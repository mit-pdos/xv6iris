(* ====================================================================== *)
(* UserFetchCert.v -- THE U-MODE INSTRUCTION FETCH, PURE.                  *)
(*                                                                        *)
(* Package P3's capstone (claude-notes/projects/user-tier-port section     *)
(* 4.2): [UserFetchPt.user_pt_fetch_instr] with its                        *)
(* [reg_interp]/[gen_heap_interp] premises replaced by                     *)
(* [UserBytes.u_mem_wf] projections, a [goodmb] conjunct added, and the    *)
(* post-state said out loud -- at the reference state                      *)
(* [UserClassifyAsm.u_state rs mm = MState rs mm dev0_state], in the same  *)
(* style as [base_exec_total_u] / [rvc_exec_total_u].                       *)
(*                                                                        *)
(* Under whole-cycle stepping the composer consumed the two interpretation *)
(* authorities only to LEARN what memory held; under per-node stepping the *)
(* hart HOLDS those bytes, so the same facts are pure and the composer is  *)
(* a [Prop].  What the resources used to carry has to be said explicitly:  *)
(* the file the fetch LANDS on (a filling walk writes the TLB), the tree   *)
(* it lands on (the Svadu write-back), and that the bytes moved only the   *)
(* way [user_pt_inv_bytes]'s closing wand allows ([u_mem_step]).            *)
(*                                                                        *)
(* Layout: section 1 the 4-byte fetch READ, certified; section 2 the fetch *)
(* composer's two shells; section 3 the [u_mem_wf] projections the walk    *)
(* and the read need; section 4 the byte-level ADUE absorption; section 5  *)
(* what the write-back does NOT touch and the fetched word; section 6 the  *)
(* [translateAddr] probes at the fetch, certified; section 7               *)
(* [u_fetch_pure] itself.                                                  *)
(*                                                                        *)
(* ONLY THE 4-ALIGNED FETCH IS HERE.  The 2-aligned split fetch (a         *)
(* compressed instruction at an odd halfword, and the 2+2 straddle that    *)
(* translates TWICE) has its exec facts in [UserFetch]                     *)
(* ([exec_fetch_rvc_2] / [exec_fetch_base_2] / the two fault arms) and its  *)
(* composer in [UserFetchPt.user_pt_fetch_instr_2], but NO [goodmb] twin   *)
(* of either exists yet: section 2 certifies [fetch_bytes] and [fetch]     *)
(* at width 4 only.  A [u_fetch_pure_2] needs those two twins first;       *)
(* everything else it wants (the walk certificate, the [u_mem_wf]          *)
(* projections, the landing algebra) is width-independent and is already   *)
(* here -- it would run the section-7 script TWICE, threading the second   *)
(* translation's [u_mem_step] through [u_mem_step_trans].                   *)
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
(* [SmodeCore.ram_fetch_pmp] -- the RAM window's PMP grant -- is the one
   thing section 7 needs from the S-mode core. *)
Require Import SmodeCore.
(* the tier's PURE pair convention: [u_state], [u_exec_pins], [Du_r]/[Du_w].
   [UserClassifyAsm] is Iris-free; nothing below is an [iProp]. *)
Require Import UserFrame UserExec UserClassify UserClassifyAsm.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 1. THE FETCH READ, certified, WIDTH-GENERIC.                           *)
(*                                                                        *)
(* [UserMem.exec_checked_mem_read_ram_{2,4}_U] / [exec_mem_read_fetch_    *)
(* {2,4}_U]'s twins.  Stated ONCE over an arbitrary width [k], exactly as  *)
(* [UserMemPt]'s [GenRead] does for the DATA read, and instantiated at 4   *)
(* (the 4-aligned fetch) and at 2 (the 2-aligned split fetch, whose two    *)
(* halfword reads are what [u_fetch_pure_2] stands on).                    *)
(*                                                                        *)
(* THE WIDTH-TYPED READ IS A PREMISE, NOT A LEMMA APPLIED INSIDE.          *)
(* [read_ram]'s value index is [mword (8*k)] and resists abstraction       *)
(* inside [sail_mem_read]'s cast (the reason [UserMemPt] section 5 closes  *)
(* over two width-TYPED bricks), but a CERTIFICATE never scrutinises the   *)
(* value -- so taking [Hread_plain] as a hypothesis keeps everything here  *)
(* generic and costs each caller one already-proved brick                  *)
(* ([exec_read_ram_plain_2] / [_4]).                                       *)
(* ===================================================================== *)

(* the PMA check at the fetch access type, both halves, width-generic *)
Lemma exec_pmaCheck_ram_fetch_g (k : Z) (addr : mword 64)
    (pbmt : page_based_mem_type) (region : PMA_Region) (s : mstate) :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k
    = Some region ->
  is_aligned_paddr (Physaddr addr) k = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (pmaCheck (Physaddr addr) k (InstructionFetch tt) pbmt false) s
    = Some (Ok pma_ok_aligned, s).
Proof.
  intros Hmatch Halign Hexec.
  destruct region as [rbase rsize rattr rdtree].
  pma_ok_peel Hmatch Hexec (exec_is_mag_applicable_fetch k s) Halign.
Qed.

Lemma goodmb_pmaCheck_ram_fetch_g (Dr Dw : register -> bool) (k : Z)
    (addr : mword 64) (pbmt : page_based_mem_type) (region : PMA_Region)
    (roc : bool) (s : mstate) (mm : pamap) :
  Dr pma_regions = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k
    = Some region ->
  is_aligned_paddr (Physaddr addr) k = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  goodmb Dr Dw (pmaCheck (Physaddr addr) k (InstructionFetch tt) pbmt roc) s mm
    = true.
Proof.
  intros HD Hmatch Halign Hfield.
  destruct region as [rbase rsize rattr rdtree].
  assert (Hrg : goodmb Dr Dw (Defs.read_reg pma_regions : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HD).
  unfold pmaCheck. apply goodmb_cer.
  gmm_lift Hrg (exec_read_reg pma_regions s).
  rewrite Hmatch. cbn [PMA_Region_attributes] in Hfield |- *. cbn match.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
  cbn match beta.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
  rewrite Hfield. cbn [Riscv.rv64d.not negb].
  gmm_lift (goodmb_mag_pma_check_aligned Dr Dw (override_PMA rattr pbmt)
              (InstructionFetch tt) (Physaddr addr) k false s mm
              (goodmb_returnm Dr Dw false s mm)
              (exec_is_mag_applicable_fetch k s) Halign)
           (exec_mag_pma_check_aligned (override_PMA rattr pbmt)
              (InstructionFetch tt) (Physaddr addr) k false s
              (exec_is_mag_applicable_fetch k s) Halign).
  cbn match beta. reflexivity.
Qed.

(* kept for compatibility with the width-4 call sites *)
Lemma goodmb_pmaCheck_ram_fetch (Dr Dw : register -> bool) (addr : mword 64)
    (pbmt : page_based_mem_type) (region : PMA_Region) (roc : bool)
    (s : mstate) (mm : pamap) :
  Dr pma_regions = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  goodmb Dr Dw (pmaCheck (Physaddr addr) 4 (InstructionFetch tt) pbmt roc) s mm
    = true.
Proof. exact (goodmb_pmaCheck_ram_fetch_g Dr Dw 4 addr pbmt region roc s mm). Qed.

(* the PMP grant at the fetch access type (the X bit), width-generic *)
Lemma goodmb_pmpCheck_user_grant_fetch (Dr Dw : register -> bool)
    (a : mword 64) (width : Z) (s : mstate) (mm : pamap) :
  Dr pmpcfg_n = true -> Dr pmpaddr_n = true ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X
    (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  goodmb Dr Dw (pmpCheck (Physaddr a) width (InstructionFetch tt) User) s mm = true.
Proof.
  intros HDc HDa HA Hord Hrange HX.
  apply (goodmb_pmpCheck_grant Dr Dw a width (InstructionFetch tt) User s mm
           HDc HDa HA Hord Hrange).
  - unfold pmpCheckRWX. cbn match. rewrite HX. apply exec_returnm.
  - unfold pmpCheckRWX. cbn match. apply goodmb_returnm.
Qed.

Section FetchReadGen.
  Context (Dr Dw : register -> bool).
  Context (k : Z) (Hk : 0 < k).
  Context (pbmt : page_based_mem_type) (addr : mword 64) (region : PMA_Region).
  Context (w : mword (8 * k)) (s : mstate) (mm : pamap).

  Hypothesis HDc : Dr pmpcfg_n = true.
  Hypothesis HDa : Dr pmpaddr_n = true.
  Hypothesis HDp : Dr pma_regions = true.
  Hypothesis HDh : Dr htif_tohost_base = true.
  Hypothesis HDms : Dr mstatus = true.
  Hypothesis HDcp : Dr cur_privilege = true.
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64)
    (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 k)) = PMP_Match.
  Hypothesis HX : eq_vec (_get_Pmpcfg_ent_X
    (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs))
    (Physaddr addr) k = Some region.
  Hypothesis Halign : is_aligned_paddr (Physaddr addr) k = true.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr addr) k) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr addr) k) s = Some (false, s).
  Hypothesis Hhtif : register_lookup htif_tohost_base s.(sregs) = None.
  Hypothesis Hdev : dev_addr addr = false.
  Hypothesis Hown : bytes_owned mm addr (Z.to_N k) = true.
  Hypothesis Hread_plain :
    exec (read_ram Read_plain (Physaddr addr) k false) s
      = Some ((w, default_meta), s).

  Let Hh : exec (within_htif_readable (Physaddr addr) k) s = Some (false, s)
    := within_htif_false addr k s Hhtif.

  Lemma frg_exec_mmio :
    exec (within_mmio_readable (Physaddr addr) k) s = Some (false, s).
  Proof.
    unfold within_mmio_readable. cbn [get_config_rvfi].
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity.
  Qed.

  Lemma frg_exec_cp :
    exec (check_pma_with_pmp_priority (InstructionFetch tt) pbmt User
            (Physaddr addr) k false) s = Some (Ok pma_ok_aligned, s).
  Proof.
    unfold check_pma_with_pmp_priority.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_pmaCheck_ram_fetch_g k addr pbmt region s Hmatch Halign Hexec)).
    cbn match. apply exec_returnM.
  Qed.

  Lemma frg_good_cp :
    goodmb Dr Dw (check_pma_with_pmp_priority (InstructionFetch tt) pbmt User
                    (Physaddr addr) k false) s mm = true.
  Proof.
    exact (goodmb_check_pma_with_pmp_priority Dr Dw _ _ User _ _ false _ s mm
             (goodmb_pmaCheck_ram_fetch_g Dr Dw k addr pbmt region false s mm
                HDp Hmatch Halign Hexec)
             (exec_pmaCheck_ram_fetch_g k addr pbmt region s Hmatch Halign Hexec)).
  Qed.

  Lemma goodmb_checked_mem_read_ram_g_U :
    goodmb Dr Dw (checked_mem_read (InstructionFetch tt) pbmt User
             (Physaddr addr) k false false false false) s mm = true.
  Proof.
    unfold checked_mem_read. apply goodmb_cer.
    erewrite gm_liftR_seq; [ | apply frg_good_cp | apply frg_exec_cp ].
    cbn beta. cbn match.
    erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
    cbn match beta.
    rewrite pma_ok_aligned_splittable. rewrite pma_ok_aligned_granule.
    gmm_lift (goodmb_split_misaligned_unsplit Dr Dw addr k 0 s mm)
             (exec_split_misaligned_unsplit addr k 0 s). cbn beta.
    cbn match beta. rewrite misaligned_order_1. cbn match zeta beta.
    assert (Hrkf : exec (read_kind_of_flags false false false) s
                   = Some (rv64d_types.Read_plain, s))
      by (unfold read_kind_of_flags; apply exec_returnM).
    assert (Hrkg : goodmb Dr Dw (read_kind_of_flags false false false) s mm = true)
      by (unfold read_kind_of_flags; apply goodmb_returnm).
    gmm_lift Hrkg Hrkf. cbn beta.
    assert (Havi : add_vec_int addr (0 * k) = addr)
      by (assert (H0 : (0 * k)%Z = 0) by lia; rewrite H0; apply avi0).
    match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?bb) _] =>
      assert (Hu : execR (Defs.untilMT vs m0 c bb) s = Some (inr (w, true, 0), s));
      [ | assert (Hug : goodmb Dr Dw (Defs.untilMT vs m0 c bb) s mm = true) ] end.
    { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
      change (bits_of_physaddr (Physaddr addr)) with addr.
      rewrite Havi.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_pmpCheck_user_grant addr k s HA Hord Hrange HX)).
      cbn beta. cbn match.
      match goal with |- context[Defs.bind (Defs.bind0 ?aa ?bb) _] =>
        assert (Hseq : execR (Defs.bind0 aa bb) s = Some (inr false, s)) end.
      { rewrite execR_bind0. rewrite execR_returnR. cbn match.
        rewrite execR_liftR. rewrite frg_exec_mmio. reflexivity. }
      rewrite (execR_bind_Some _ _ _ _ _ Hseq). cbn beta. cbn match.
      match goal with
        |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk ?ad ?wd ?mt)) ?k1) _] =>
        assert (Hrdr : execR (Defs.bind (Defs.liftR (read_ram rk ad wd mt)) k1) s
                       = Some (inr w, s)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _ Hread_plain).
        cbn beta match. apply execR_returnR_fwd. }
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
        rewrite Havi.
        gmm_lift (goodmb_pmpCheck_user_grant_fetch Dr Dw addr k s mm
                    HDc HDa HA Hord Hrange HX)
                 (exec_pmpCheck_user_grant addr k s HA Hord Hrange HX).
        cbn beta. cbn match.
        match goal with |- context[Defs.bind (Defs.bind0 ?aa ?bb) _] =>
          assert (Hseqg : goodmb Dr Dw (Defs.bind0 aa bb) s mm = true);
          [ | assert (Hseq : execR (Defs.bind0 aa bb) s = Some (inr false, s)) ] end.
        { erewrite gm_bind0R; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
          apply goodmb_liftR.
          exact (goodmb_within_mmio_readable Dr Dw addr k s mm HDh Hhtif Hc Hsig). }
        { rewrite execR_bind0. rewrite execR_returnR. cbn match.
          rewrite execR_liftR. rewrite frg_exec_mmio. reflexivity. }
        erewrite (gm_bindR Dr Dw _ _ s s mm false Hseqg Hseq). cbn beta. cbn match.
        match goal with
          |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk ?ad ?wd ?mt)) ?k1) _] =>
          assert (Hrdg : goodmb Dr Dw
                    (Defs.bind (Defs.liftR (read_ram rk ad wd mt)) k1) s mm = true);
          [ | assert (Hrd : execR (Defs.bind (Defs.liftR (read_ram rk ad wd mt)) k1) s
                            = Some (inr w, s)) ] end.
        { erewrite gm_liftR_seq;
            [ | exact (goodmb_read_ram_of_exec Dr Dw Read_plain k addr false
                         (w, default_meta) s s mm eq_refl Hdev Hown Hread_plain)
              | exact Hread_plain ].
          cbn beta match. apply goodmb_returnm. }
        { rewrite (execR_liftR_seq _ _ _ _ _ Hread_plain).
          cbn beta match. apply execR_returnR_fwd. }
        erewrite (gm_bindR Dr Dw _ _ s s mm w Hrdg Hrd). cbn beta zeta.
        change (update_subrange_vec_dec (zeros' (8 * 1 * k))
                  (8 * (0 + 1) * k - 1) (8 * 0 * k) (autocast w))
          with (update_subrange_vec_dec (zeros' (8 * k)) (8 * k - 1) 0
                  (autocast (T := mword) w)).
        rewrite (usvd_zeros_full_gen (8 * k) w ltac:(lia)).
        apply goodmb_returnm.
      - rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
        change (bits_of_physaddr (Physaddr addr)) with addr.
        rewrite Havi.
        rewrite (execR_liftR_seq _ _ _ _ _
                   (exec_pmpCheck_user_grant addr k s HA Hord Hrange HX)).
        cbn beta. cbn match.
        match goal with |- context[Defs.bind (Defs.bind0 ?aa ?bb) _] =>
          assert (Hseq : execR (Defs.bind0 aa bb) s = Some (inr false, s)) end.
        { rewrite execR_bind0. rewrite execR_returnR. cbn match.
          rewrite execR_liftR. rewrite frg_exec_mmio. reflexivity. }
        rewrite (execR_bind_Some _ _ _ _ _ Hseq). cbn beta. cbn match.
        match goal with
          |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk ?ad ?wd ?mt)) ?k1) _] =>
          assert (Hrd : execR (Defs.bind (Defs.liftR (read_ram rk ad wd mt)) k1) s
                        = Some (inr w, s)) end.
        { rewrite (execR_liftR_seq _ _ _ _ _ Hread_plain).
          cbn beta match. apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hrd). cbn beta zeta.
        change (update_subrange_vec_dec (zeros' (8 * 1 * k))
                  (8 * (0 + 1) * k - 1) (8 * 0 * k) (autocast w))
          with (update_subrange_vec_dec (zeros' (8 * k)) (8 * k - 1) 0
                  (autocast (T := mword) w)).
        rewrite (usvd_zeros_full_gen (8 * k) w ltac:(lia)).
        apply execR_returnR_fwd.
      - reflexivity.
      - apply execR_returnR_fwd. }
    erewrite (gm_bindR Dr Dw _ _ s s mm (w, true, 0) Hug Hu). cbn beta zeta.
    rewrite autocast_id. apply goodmb_returnm.
  Qed.

  Lemma goodmb_mem_read_fetch_g_U :
    register_lookup cur_privilege s.(sregs) = User ->
    exec (checked_mem_read (InstructionFetch tt) pbmt User
            (Physaddr addr) k false false false false) s
      = Some (Ok (w, default_meta), s) ->
    goodmb Dr Dw (mem_read (InstructionFetch tt) pbmt (Physaddr addr) k
             false false false) s mm = true.
  Proof.
    intros Hpriv Hchk.
    unfold mem_read.
    gmm_rr mstatus HDms.
    gmm_rr cur_privilege HDcp.
    assert (Heffg : goodb Dr (effectivePrivilege (InstructionFetch tt)
                               (register_lookup mstatus s.(sregs))
                               (register_lookup cur_privilege s.(sregs))) s = true).
    { unfold effectivePrivilege.
      replace (generic_neq (InstructionFetch tt) (InstructionFetch tt)) with false
        by (vm_compute; reflexivity).
      reflexivity. }
    gmm_peel (goodmb_of_goodb Dr Dw _ s mm Heffg)
             (exec_effectivePrivilege_fetch (register_lookup mstatus s.(sregs))
                (register_lookup cur_privilege s.(sregs)) s).
    rewrite Hpriv.
    unfold mem_read_priv.
    assert (Hmrg : goodmb Dr Dw (mem_read_priv_meta (InstructionFetch tt) pbmt User
                     (Physaddr addr) k false false false false) s mm = true).
    { unfold mem_read_priv_meta. cbn [orb andb].
      gmm_peel goodmb_checked_mem_read_ram_g_U Hchk. cbn match.
      unfold mem_read_callback. apply goodmb_returnm. }
    assert (Hmr : exec (mem_read_priv_meta (InstructionFetch tt) pbmt User
                    (Physaddr addr) k false false false false) s
                  = Some (Ok (w, default_meta), s)).
    { unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_bind_Some _ _ _ _ _ Hchk). cbn match.
      unfold mem_read_callback. apply exec_returnM. }
    gmm_peel Hmrg Hmr. cbn [MemoryOpResult_drop_meta]. apply goodmb_returnm.
  Qed.

End FetchReadGen.

(* --- the two instances.  Their argument lists are the pre-generalisation
       ones, so no call site of the width-4 pair moved. --- *)

Lemma goodmb_checked_mem_read_ram_4_U (Dr Dw : register -> bool)
    (pbmt : page_based_mem_type) (addr : mword 64) (region : PMA_Region)
    (w : bv 32) (s : mstate) (mm : pamap) :
  Dr pmpcfg_n = true -> Dr pmpaddr_n = true -> Dr pma_regions = true ->
  Dr htif_tohost_base = true -> Dr mstatus = true -> Dr cur_privilege = true ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64)
    (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X
    (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs))
    (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  register_lookup htif_tohost_base s.(sregs) = None ->
  dev_addr addr = false ->
  bytes_owned mm addr 4 = true ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  goodmb Dr Dw (checked_mem_read (InstructionFetch tt) pbmt User
           (Physaddr addr) 4 false false false false) s mm = true.
Proof.
  intros HDc HDa HDp HDh HDms HDcp HA Hord Hrange HX Hmatch Halign Hexec
    Hc Hsig Hhtif Hdev Hown Hbytes.
  assert (Hk4 : 0 < 4) by lia.
  pose proof (exec_read_ram_plain_4 addr w s Hdev Hbytes) as Hrp.
  apply (goodmb_checked_mem_read_ram_g_U Dr Dw 4 Hk4 pbmt addr region w s mm);
    assumption.
Qed.

Lemma goodmb_mem_read_fetch_4_U (Dr Dw : register -> bool)
    (pbmt : page_based_mem_type) (addr : mword 64) (region : PMA_Region)
    (w : bv 32) (s : mstate) (mm : pamap) :
  Dr pmpcfg_n = true -> Dr pmpaddr_n = true -> Dr pma_regions = true ->
  Dr htif_tohost_base = true -> Dr mstatus = true -> Dr cur_privilege = true ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64)
    (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X
    (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs))
    (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  register_lookup htif_tohost_base s.(sregs) = None ->
  dev_addr addr = false ->
  bytes_owned mm addr 4 = true ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s.(sregs) = User ->
  goodmb Dr Dw (mem_read (InstructionFetch tt) pbmt (Physaddr addr) 4
           false false false) s mm = true.
Proof.
  intros HDc HDa HDp HDh HDms HDcp HA Hord Hrange HX Hmatch Halign Hexec
    Hc Hsig Hhtif Hdev Hown Hbytes Hpriv.
  assert (Hk4 : 0 < 4) by lia.
  pose proof (exec_read_ram_plain_4 addr w s Hdev Hbytes) as Hrp.
  pose proof (exec_checked_mem_read_ram_4_U pbmt addr region w s
                HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig
                (within_htif_false addr 4 s Hhtif) Hdev Hbytes) as Hchk.
  apply (goodmb_mem_read_fetch_g_U Dr Dw 4 Hk4 pbmt addr region w s mm);
    assumption.
Qed.

(* --- and the width-2 pair, which is what the 2-aligned split fetch needs --- *)

Lemma goodmb_checked_mem_read_ram_2_U (Dr Dw : register -> bool)
    (pbmt : page_based_mem_type) (addr : mword 64) (region : PMA_Region)
    (w : bv 16) (s : mstate) (mm : pamap) :
  Dr pmpcfg_n = true -> Dr pmpaddr_n = true -> Dr pma_regions = true ->
  Dr htif_tohost_base = true -> Dr mstatus = true -> Dr cur_privilege = true ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64)
    (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 2)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X
    (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs))
    (Physaddr addr) 2 = Some region ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (within_clint (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 2) s = Some (false, s) ->
  register_lookup htif_tohost_base s.(sregs) = None ->
  dev_addr addr = false ->
  bytes_owned mm addr 2 = true ->
  (forall j : nat, (N.of_nat j < 2)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  goodmb Dr Dw (checked_mem_read (InstructionFetch tt) pbmt User
           (Physaddr addr) 2 false false false false) s mm = true.
Proof.
  intros HDc HDa HDp HDh HDms HDcp HA Hord Hrange HX Hmatch Halign Hexec
    Hc Hsig Hhtif Hdev Hown Hbytes.
  assert (Hk2 : 0 < 2) by lia.
  pose proof (exec_read_ram_plain_2 addr w s Hdev Hbytes) as Hrp.
  apply (goodmb_checked_mem_read_ram_g_U Dr Dw 2 Hk2 pbmt addr region w s mm);
    assumption.
Qed.

Lemma goodmb_mem_read_fetch_2_U (Dr Dw : register -> bool)
    (pbmt : page_based_mem_type) (addr : mword 64) (region : PMA_Region)
    (w : bv 16) (s : mstate) (mm : pamap) :
  Dr pmpcfg_n = true -> Dr pmpaddr_n = true -> Dr pma_regions = true ->
  Dr htif_tohost_base = true -> Dr mstatus = true -> Dr cur_privilege = true ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64)
    (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 2)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X
    (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs))
    (Physaddr addr) 2 = Some region ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (within_clint (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 2) s = Some (false, s) ->
  register_lookup htif_tohost_base s.(sregs) = None ->
  dev_addr addr = false ->
  bytes_owned mm addr 2 = true ->
  (forall j : nat, (N.of_nat j < 2)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s.(sregs) = User ->
  goodmb Dr Dw (mem_read (InstructionFetch tt) pbmt (Physaddr addr) 2
           false false false) s mm = true.
Proof.
  intros HDc HDa HDp HDh HDms HDcp HA Hord Hrange HX Hmatch Halign Hexec
    Hc Hsig Hhtif Hdev Hown Hbytes Hpriv.
  assert (Hk2 : 0 < 2) by lia.
  pose proof (exec_read_ram_plain_2 addr w s Hdev Hbytes) as Hrp.
  pose proof (exec_checked_mem_read_ram_2_U pbmt addr region w s
                HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig
                (within_htif_false addr 2 s Hhtif) Hdev Hbytes) as Hchk.
  apply (goodmb_mem_read_fetch_g_U Dr Dw 2 Hk2 pbmt addr region w s mm);
    assumption.
Qed.

(* ===================================================================== *)
(* 2. THE FETCH SHELLS ([UserFetch.exec_fetch_bytes_ok] /                 *)
(*    [exec_fetch_ok_4]'s twins).                                         *)
(*                                                                        *)
(* Both are pure plumbing over the two calls that matter -- the           *)
(* translation and the instruction read -- so both take those as exec     *)
(* fact PLUS certificate and add only [Dr PC] and the [Ziccif] probe.      *)
(* ===================================================================== *)

Lemma goodmb_currentlyEnabled_Ziccif (Dr Dw : register -> bool) (s : mstate)
    (mm : pamap) :
  goodmb Dr Dw (currentlyEnabled Ext_Ziccif) s mm = true.
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  vm_compute. reflexivity.
Qed.

Lemma goodmb_fetch_bytes_ok (Dr Dw : register -> bool) (width : Z)
    (fs gs pa : mword 64) (w : mword (8 * width)) (s s' : mstate) (mm : pamap) :
  exec (translateAddr (Virtaddr gs) (InstructionFetch tt)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  goodmb Dr Dw (translateAddr (Virtaddr gs) (InstructionFetch tt)) s mm = true ->
  exec (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) width false false false) s'
    = Some (Ok w, s') ->
  goodmb Dr Dw (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) width
           false false false) s' mm = true ->
  goodmb Dr Dw (fetch_bytes fs gs width) s mm = true.
Proof.
  intros Htr Htrg Hmr Hmrg.
  unfold fetch_bytes. apply goodmb_cer.
  change (ext_fetch_check_pc fs gs) with (@None unit). cbv iota beta.
  match goal with |- context[Defs.bind (Defs.bind0 ?a ?b) _] =>
    assert (Htrs : execR (Defs.bind0 a b) s
                   = Some (inr (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)), s'));
    [ | assert (Htrsg : goodmb Dr Dw (Defs.bind0 a b) s mm = true) ] end.
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
    rewrite execR_liftR. rewrite Htr. cbn match. reflexivity. }
  { erewrite gm_bind0R; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
    apply goodmb_liftR. exact Htrg. }
  erewrite (gm_bindR Dr Dw _ _ s s' mm _ Htrsg Htrs). cbv iota beta.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
  cbv iota beta.
  erewrite gm_bindR;
    [ | apply goodmb_liftR; exact Hmrg
      | rewrite execR_liftR; rewrite Hmr; cbn match; reflexivity ].
  cbv iota beta. apply goodmb_returnm.
Qed.

Section FetchOk4Cert.
  Context (Dr Dw : register -> bool).
  Context (s s' : mstate) (mm : pamap) (pc pa : mword 64) (w : mword 32).
  Hypothesis HDpc : Dr PC = true.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Hvalign : is_aligned_vaddr (Virtaddr pc) 4 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr pc) (InstructionFetch tt)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Htrg : goodmb Dr Dw (translateAddr (Virtaddr pc) (InstructionFetch tt))
                      s mm = true.
  Hypothesis Hmr : exec (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 4
                           false false false) s' = Some (Ok w, s').
  Hypothesis Hmrg : goodmb Dr Dw (mem_read (InstructionFetch tt) PBMT_PMA
                      (Physaddr pa) 4 false false false) s' mm = true.

  Let HrdPC : exec (Defs.read_reg PC) s = Some (pc, s).
  Proof. rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. Qed.

  Let HrdPCg : goodmb Dr Dw (Defs.read_reg PC : M _) s mm = true.
  Proof. rewrite goodmb_read_reg. exact HDpc. Qed.

  Lemma goodmb_fetch_ok_4 : goodmb Dr Dw (fetch tt) s mm = true.
  Proof using Dr Dw s s' mm pc pa w HDpc HpcPC Hvalign Htr Htrg Hmr Hmrg.
    destruct (align4_low_bits pc Hvalign) as [Hbit0 Hbit1].
    unfold fetch. apply goodmb_cer.
    change (get_config_rvfi tt) with false. cbv iota beta.
    gmm_lift HrdPCg HrdPC.
    gmm_lift HrdPCg HrdPC.
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    match goal with |- context[Defs.bind ?A ?K] =>
      assert (Halg : goodmb Dr Dw A s mm = true);
      [ | assert (Hale : execR A s = Some (inr false, s)) ] end.
    { erewrite gm_bind0R; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
      unfold Defs.or_boolM.
      erewrite gm_liftR_nest; [ | exact HrdPCg | exact HrdPC ].
      rewrite Hbit0. rewrite bindR_ret. cbv iota beta.
      unfold Defs.and_boolM.
      erewrite gm_liftR_nest; [ | exact HrdPCg | exact HrdPC ].
      rewrite Hbit1. rewrite bindR_ret. cbv iota beta. reflexivity. }
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      unfold Defs.or_boolM.
      rewrite (execR_bind_Some _ _ _ false s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0.
          apply execR_returnR_fwd. }
      cbv iota beta.
      unfold Defs.and_boolM.
      rewrite (execR_bind_Some _ _ _ false s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1.
          apply execR_returnR_fwd. }
      cbv iota beta. reflexivity. }
    erewrite (gm_bindR Dr Dw _ _ s s mm false Halg Hale). cbv iota beta.
    match goal with |- context[Defs.bind ?A ?K] =>
      assert (Hzg : goodmb Dr Dw A s mm = true);
      [ | assert (Hze : execR A s = Some (inr true, s)) ] end.
    { unfold Defs.and_boolM.
      erewrite gm_liftR_nest; [ | exact HrdPCg | exact HrdPC ].
      rewrite Hvalign. rewrite bindR_ret. cbv iota beta.
      apply goodmb_liftR. apply goodmb_currentlyEnabled_Ziccif. }
    { unfold Defs.and_boolM.
      rewrite (execR_bind_Some _ _ _ true s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign.
          apply execR_returnR_fwd. }
      cbv iota beta.
      rewrite execR_liftR. rewrite exec_currentlyEnabled_Ziccif.
      cbn match. reflexivity. }
    erewrite (gm_bindR Dr Dw _ _ s s mm true Hzg Hze). cbv iota beta.
    gmm_lift HrdPCg HrdPC.
    gmm_lift HrdPCg HrdPC.
    erewrite gm_liftR_seq;
      [ | exact (goodmb_fetch_bytes_ok Dr Dw 4 pc pc pa w s s' mm
                   Htr Htrg Hmr Hmrg)
        | exact (exec_fetch_bytes_ok 4 pc pc pa w s s' Htr Hmr) ].
    cbv iota beta.
    destruct (isRVC (subrange_vec_dec (autocast (T := mword) w : mword 32) 15 0));
      reflexivity.
  Qed.

End FetchOk4Cert.

(* ===================================================================== *)
(* 3. THE [u_mem_wf] PROJECTIONS THE WALK ASKS FOR.                       *)
(*                                                                        *)
(* [PtWalkCert.goodmb_ptree_translateAddr] and its exec twin want, per     *)
(* slot, a [pt_slot_mem] and a [bytes_owned].  Both are projections of     *)
(* [UserBytes.u_mem_wf] once the slot is known to be ONE OF THE TREE'S --  *)
(* which is what [ptree_maps] says, and what this section turns into the   *)
(* [pt_maps 2 t] membership [u_mem_wf_read] / [u_mem_wf_owned] consume.    *)
(* ===================================================================== *)

Lemma mword9_uint_range (x : mword 9) : (0 <= uint x < 512)%Z.
Proof.
  pose proof (bv_unsigned_in_range _ x) as Hr.
  unfold uint, get_word, MachineWord.MachineWord.word_to_N.
  rewrite Z2N.id; [| exact (proj1 Hr)].
  change (bv_modulus (MachineWord.MachineWord.Z_idx 9)) with 512%Z in Hr.
  exact Hr.
Qed.

Lemma mword9_uint_id (x : mword 9) : (mword_of_int (uint x) : mword 9) = x.
Proof.
  pose proof (bv_unsigned_in_range _ x) as Hr.
  unfold uint, get_word, MachineWord.MachineWord.word_to_N,
         SailStdpp.Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z2N.id; [| exact (proj1 Hr)].
  apply Z_to_bv_bv_unsigned.
Qed.

(* a node's OWN slot, as a byte map of that node's page *)
Lemma pt_page_maps_slot (t : ptree) (i : mword 9) :
  word_bytes (u_pte_addr (pt_base t) i) (pt_ents t i) ∈ pt_page_maps t.
Proof.
  pose proof (pt_page_map_mem t (uint i) (mword9_uint_range i)) as Hm.
  rewrite mword9_uint_id in Hm. exact Hm.
Qed.

(* the three slots a successful walk of [vpn] reads, as members of the
   whole tree's byte-map list *)
Lemma ptree_maps_slot2 (t : ptree) (vpn : mword 27) (p2 p1 p0 : mword 64) :
  ptree_maps t vpn p2 p1 p0 ->
  word_bytes (u_pte_addr (pt_base t) (vpn_idx 2 vpn)) p2 ∈ pt_maps 2 t.
Proof.
  intros (c1 & c0 & _ & _ & He2 & _). rewrite <- He2.
  apply pt_maps_page. apply pt_page_maps_slot.
Qed.

Lemma ptree_maps_slot1 (t : ptree) (vpn : mword 27) (p2 p1 p0 : mword 64) :
  ptree_maps t vpn p2 p1 p0 ->
  word_bytes (pt_addr1 p2 vpn) p1 ∈ pt_maps 2 t.
Proof.
  intros (c1 & c0 & Hk1 & Hk0 & He2 & He1 & He0 & Hb1 & Hb0 & _).
  unfold pt_addr1. rewrite Hb1. rewrite <- He1.
  apply (pt_maps_kid 1 t c1 (uint (vpn_idx 2 vpn)));
    [ apply mword9_uint_range
    | rewrite mword9_uint_id; exact Hk1
    | apply pt_maps_page; apply pt_page_maps_slot ].
Qed.

Lemma ptree_maps_slot0 (t : ptree) (vpn : mword 27) (p2 p1 p0 : mword 64) :
  ptree_maps t vpn p2 p1 p0 ->
  word_bytes (pt_addr0 p1 vpn) p0 ∈ pt_maps 2 t.
Proof.
  intros (c1 & c0 & Hk1 & Hk0 & He2 & He1 & He0 & Hb1 & Hb0 & _).
  unfold pt_addr0. rewrite Hb0. rewrite <- He0.
  apply (pt_maps_kid 1 t c1 (uint (vpn_idx 2 vpn)));
    [ apply mword9_uint_range | rewrite mword9_uint_id; exact Hk1 |].
  apply (pt_maps_kid 0 c1 c0 (uint (vpn_idx 1 vpn)));
    [ apply mword9_uint_range | rewrite mword9_uint_id; exact Hk0 |].
  rewrite pt_maps_O. apply pt_page_maps_slot.
Qed.

(* ...and a member of that list, at a slot ADDRESS (so its alignment is
   the slot geometry's), is a [pt_slot_mem] of the reference state *)
Lemma u_slot_mem_at (P : uptd) (t : ptree) (mm : pamap) (rs : regstate)
    (b : mword 44) (i : mword 9) (q : mword 64) :
  u_mem_wf P t mm ->
  word_bytes (u_pte_addr b i) q ∈ pt_maps 2 t ->
  pt_slot_mem (MState rs mm dev0_state) (u_pte_addr b i) q.
Proof.
  intros Hwf Hin.
  pose proof (u_mem_wf_sub P t mm _ q Hwf Hin) as Hsub.
  assert (Hlk : forall j : nat, (N.of_nat j < 8)%N ->
            mm !! pa_add (u_pte_addr b i) j = Some (nth_byte q j)).
  { intros j Hj. apply (lookup_weaken (word_bytes (u_pte_addr b i) q) mm);
      [ apply word_bytes_lookup; lia | exact Hsub ]. }
  assert (Hram : forall j : nat, (N.of_nat j < 8)%N ->
            addr_is_ram (pa_add (u_pte_addr b i) j)).
  { intros j Hj. destruct Hwf as (md & _ & _ & _ & _ & Hr & _).
    apply Hr. apply elem_of_dom. exists (nth_byte q j). exact (Hlk j Hj). }
  split_and!.
  - exact Hlk.
  - rewrite <- (pa_add_0 (u_pte_addr b i)). apply Hram. lia.
  - apply Hram. lia.
  - exact (pte_addr_at_aligned8 b i).
Qed.

Lemma u_slot_owned (P : uptd) (t : ptree) (mm : pamap) (a : Arch.pa) (q : mword 64) :
  u_mem_wf P t mm -> word_bytes a q ∈ pt_maps 2 t -> bytes_owned mm a 8 = true.
Proof. intros Hwf Hin. exact (u_mem_wf_owned P t mm a q Hwf Hin). Qed.

(* ===================================================================== *)
(* 4. THE ADUE ABSORPTION AT THE BYTE LEVEL.                              *)
(*                                                                        *)
(* [UserBytes.u_mem_step]'s third conjunct asks for                        *)
(* [mm' = ptree_bytes 2 t' ∪ md'], and on the Svadu write-back arm [mm']  *)
(* is [write_bytes mm <the leaf slot> 8 q].  Nothing in [UserBytes] says   *)
(* that writing the slot IS setting the leaf in the tree; this section is  *)
(* that, and it is map algebra rather than page-table reasoning.           *)
(* (FOLD BACK into [UserBytes.v] beside [u_mem_step].)                     *)
(* ===================================================================== *)

(* A WRITE IS A LEFT-BIASED UNION WITH THE WORD.  [write_bytes] folds the
   same eight inserts [word_bytes] lists, so the two agree. *)
Lemma foldr_ins_union (a : Arch.pa) {wd : N} (v : bv wd) (js : list nat)
    (m : pamap) :
  foldr (fun j acc => <[pa_add a j := nth_byte v j]> acc) m js
  = (list_to_map ((fun j : nat => (pa_add a j, nth_byte v j)) <$> js) : pamap) ∪ m.
Proof.
  induction js as [| j js IH]; cbn [foldr fmap list_fmap].
  - change (list_to_map [] : pamap) with (∅ : pamap).
    first [ by rewrite map_empty_union
          | by rewrite (left_id_L (∅ : pamap) union)
          | by rewrite left_id_L
          | symmetry; apply map_empty_union ].
  - rewrite IH.
    first [ apply insert_union_l | symmetry; apply insert_union_l ].
Qed.

Lemma write_bytes_word (m : pamap) (a : Arch.pa) (v : bv 64) :
  write_bytes m a 8 v = word_bytes a v ∪ m.
Proof. unfold write_bytes, word_bytes. apply foldr_ins_union. Qed.

Lemma write_bytes_union_l (A B : pamap) (a : Arch.pa) (v : bv 64) :
  write_bytes (A ∪ B) a 8 v = write_bytes A a 8 v ∪ B.
Proof.
  rewrite !write_bytes_word.
  first [ (rewrite assoc_L; reflexivity)
        | (rewrite <- assoc_L; reflexivity)
        | (symmetry; rewrite assoc_L; reflexivity)
        | (symmetry; rewrite <- assoc_L; reflexivity)
        | apply map_union_assoc ].
Qed.

(* [maps_disj] passes to either half of an append *)
Lemma maps_disj_app_l (l1 l2 : list pamap) : maps_disj (l1 ++ l2) -> maps_disj l1.
Proof.
  induction l1 as [| m l1 IH]; intros Hd; [done |].
  destruct Hd as [Hhd Htl]. split; [| by apply IH].
  intros m' Hm'. apply Hhd. rewrite elem_of_app. by left.
Qed.

Lemma maps_disj_app_r (l1 l2 : list pamap) : maps_disj (l1 ++ l2) -> maps_disj l2.
Proof.
  induction l1 as [| m l1 IH]; intros Hd; [done |].
  destruct Hd as [_ Htl]. by apply IH.
Qed.

Lemma maps_disj_app_cross (l1 l2 : list pamap) :
  maps_disj (l1 ++ l2) ->
  forall m1 m2, m1 ∈ l1 -> m2 ∈ l2 -> m1 ##ₘ m2.
Proof.
  induction l1 as [| m l1 IH]; intros Hd m1 m2 H1 H2;
    [ by apply elem_of_nil in H1 |].
  destruct Hd as [Hhd Htl].
  apply elem_of_cons in H1 as [-> | H1].
  - apply Hhd. rewrite elem_of_app. by right.
  - exact (IH Htl m1 m2 H1 H2).
Qed.

(* ...and the union of an append splits *)
Lemma union_list_app (l1 l2 : list pamap) : ⋃ (l1 ++ l2) = (⋃ l1) ∪ (⋃ l2).
Proof.
  induction l1 as [| m l1 IH]; cbn [app].
  - rewrite union_list_nil.
    first [ by rewrite map_empty_union
          | by rewrite (left_id_L (∅ : pamap) union)
          | symmetry; apply map_empty_union ].
  - rewrite !union_list_cons. rewrite IH.
    first [ apply map_union_assoc | symmetry; apply map_union_assoc
          | (rewrite assoc_L; reflexivity)
          | (rewrite <- assoc_L; reflexivity) ].
Qed.

(* ---------------------------------------------------------------------- *)
(* 4a. ONE ELEMENT OF A DISJOINT LIST, REPLACED BY A SAME-DOMAIN MAP.       *)
(* This is the shape every level of the tree surgery has, and the only      *)
(* thing that has to be proved about unions.                                *)
(* ---------------------------------------------------------------------- *)
Definition maps_upd_at (X Y : pamap) (l l' : list pamap) : Prop :=
  exists l1 l2, l = (l1 ++ X :: l2)%list /\ l' = (l1 ++ Y :: l2)%list.

(* a left-biased union absorbs a same-domain map underneath it.  Stated over
   [is_Some] and NOT over [dom]: naming [gset Arch.pa] in this file
   re-elaborates the key type's [Countable] instance, which is the section-8
   trap; [is_Some] mentions no instance at all. *)
Lemma map_union_absorb_dom (X Y Z : pamap) :
  (forall a, is_Some (X !! a) -> is_Some (Y !! a)) -> Y ∪ (X ∪ Z) = Y ∪ Z.
Proof.
  intros Hd. apply map_eq. intros x.
  destruct (Y !! x) as [b|] eqn:HY.
  - rewrite (lookup_union_Some_l Y (X ∪ Z) x b HY).
    rewrite (lookup_union_Some_l Y Z x b HY). reflexivity.
  - assert (HX : X !! x = None).
    { destruct (X !! x) as [c|] eqn:HXc; [| reflexivity ].
      exfalso. destruct (Hd x (mk_is_Some _ _ HXc)) as [bb Hbb]. congruence. }
    rewrite (lookup_union_r Y (X ∪ Z) x HY).
    rewrite (lookup_union_r Y Z x HY).
    rewrite (lookup_union_r X Z x HX). reflexivity.
Qed.

Lemma union_list_upd_at (X Y : pamap) (l l' : list pamap) :
  maps_disj l -> maps_upd_at X Y l l' ->
  (forall a, is_Some (X !! a) -> is_Some (Y !! a)) ->
  (forall a, is_Some (Y !! a) -> is_Some (X !! a)) ->
  ⋃ l' = Y ∪ ⋃ l.
Proof.
  intros Hd (l1 & l2 & -> & ->) Hdom Hdom'.
  assert (HX1 : X ##ₘ ⋃ l1).
  { apply symmetry, map_disjoint_union_list_l, Forall_forall.
    intros m Hm. apply elem_of_list_In in Hm.
    revert Hd. clear -Hm. revert Hm. induction l1 as [| m0 l1 IH]; intros Hm Hd;
      [ by apply elem_of_nil in Hm |].
    destruct Hd as [Hhd Htl]. apply elem_of_cons in Hm as [-> | Hm].
    - apply Hhd. rewrite elem_of_app. right. apply elem_of_cons. by left.
    - exact (IH Hm Htl). }
  assert (HY1 : Y ##ₘ ⋃ l1).
  { apply map_disjoint_spec. intros i x y Hy Hu.
    destruct (Hdom' i (mk_is_Some _ _ Hy)) as [z Hz].
    exact (proj1 (map_disjoint_spec X (⋃ l1)) HX1 i z y Hz Hu). }
  rewrite !union_list_app. rewrite !union_list_cons.
  rewrite (map_union_assoc (⋃ l1) Y (⋃ l2)).
  rewrite (map_union_comm (⋃ l1) Y (symmetry HY1)).
  rewrite <- (map_union_assoc Y (⋃ l1) (⋃ l2)).
  rewrite (map_union_assoc (⋃ l1) X (⋃ l2)).
  rewrite (map_union_comm (⋃ l1) X (symmetry HX1)).
  rewrite <- (map_union_assoc X (⋃ l1) (⋃ l2)).
  by rewrite (map_union_absorb_dom X Y (⋃ l1 ∪ ⋃ l2) Hdom).
Qed.

Lemma maps_upd_at_app_l (X Y : pamap) (k l l' : list pamap) :
  maps_upd_at X Y l l' -> maps_upd_at X Y (k ++ l) (k ++ l').
Proof.
  intros (l1 & l2 & -> & ->). exists (k ++ l1)%list, l2.
  by rewrite <- !app_assoc.
Qed.

Lemma maps_upd_at_app_r (X Y : pamap) (k l l' : list pamap) :
  maps_upd_at X Y l l' -> maps_upd_at X Y (l ++ k) (l' ++ k).
Proof.
  intros (l1 & l2 & -> & ->). exists l1, (l2 ++ k)%list.
  by rewrite <- !app_assoc.
Qed.

(* the two ways a one-index change reaches a list of maps: through an
   [fmap] (a node's own 512 slots) and through a [concat] of [fmap]
   (a node's 512 children) *)
Lemma fmap_agree_off {A} (K : list A) (f g : A -> pamap) :
  (forall i, i ∈ K -> g i = f i) -> (g <$> K) = (f <$> K).
Proof.
  induction K as [| a K IH]; intros Hfg; [reflexivity |].
  cbn [fmap list_fmap]. rewrite (Hfg a (elem_of_list_here a K)).
  rewrite IH; [ reflexivity |].
  intros i Hi. apply Hfg. by apply elem_of_list_further.
Qed.

Lemma fmap_agree_off_l {A} (K : list A) (h h' : A -> list pamap) :
  (forall i, i ∈ K -> h' i = h i) -> (h' <$> K) = (h <$> K).
Proof.
  induction K as [| a K IH]; intros Hfg; [reflexivity |].
  cbn [fmap list_fmap]. rewrite (Hfg a (elem_of_list_here a K)).
  rewrite IH; [ reflexivity |].
  intros i Hi. apply Hfg. by apply elem_of_list_further.
Qed.

Lemma nodup_split {A} `{EqDecision A} (L L1 L2 : list A) (i0 : A) :
  base.NoDup L -> L = (L1 ++ i0 :: L2)%list ->
  (forall i, i ∈ L1 -> i <> i0) /\ (forall i, i ∈ L2 -> i <> i0).
Proof.
  intros Hnd ->.
  apply stdpp.list_relations.NoDup_app in Hnd as (H1 & Hcross & H2).
  apply (proj1 (stdpp.list_relations.NoDup_cons i0 L2)) in H2 as [Hni H2].
  split.
  - intros i Hi Heq. rewrite Heq in Hi.
    exact (Hcross i0 Hi (elem_of_list_here _ _)).
  - intros i Hi Heq. rewrite Heq in Hi. exact (Hni Hi).
Qed.

Lemma fmap_upd_at {A} `{EqDecision A} (L : list A) (f g : A -> pamap) (i0 : A) :
  base.NoDup L -> i0 ∈ L ->
  (forall i, i ∈ L -> i <> i0 -> g i = f i) ->
  maps_upd_at (f i0) (g i0) (f <$> L) (g <$> L).
Proof.
  intros Hnd Hin Hfg.
  apply elem_of_list_split in Hin as (L1 & L2 & ->).
  destruct (nodup_split (L1 ++ i0 :: L2)%list L1 L2 i0 Hnd eq_refl) as [Hn1 Hn2].
  exists (f <$> L1), (f <$> L2).
  rewrite !fmap_app. cbn [fmap list_fmap]. split; [reflexivity |].
  rewrite (fmap_agree_off L1 f g
             (fun i Hi => Hfg i ltac:(rewrite elem_of_app; by left) (Hn1 i Hi))).
  by rewrite (fmap_agree_off L2 f g
                (fun i Hi => Hfg i
                   ltac:(rewrite elem_of_app; right; by apply elem_of_list_further)
                   (Hn2 i Hi))).
Qed.

Lemma concat_upd_at {A} `{EqDecision A} (L : list A) (h h' : A -> list pamap)
    (i0 : A) (X Y : pamap) :
  base.NoDup L -> i0 ∈ L ->
  (forall i, i ∈ L -> i <> i0 -> h' i = h i) ->
  maps_upd_at X Y (h i0) (h' i0) ->
  maps_upd_at X Y (concat (h <$> L)) (concat (h' <$> L)).
Proof.
  intros Hnd Hin Hfg Hupd.
  apply elem_of_list_split in Hin as (L1 & L2 & ->).
  destruct (nodup_split (L1 ++ i0 :: L2)%list L1 L2 i0 Hnd eq_refl) as [Hn1 Hn2].
  rewrite !fmap_app. cbn [fmap list_fmap]. rewrite !concat_app.
  cbn [concat].
  rewrite (fmap_agree_off_l L1 h h'
             (fun i Hi => Hfg i ltac:(rewrite elem_of_app; by left) (Hn1 i Hi))).
  rewrite (fmap_agree_off_l L2 h h'
             (fun i Hi => Hfg i
                ltac:(rewrite elem_of_app; right; by apply elem_of_list_further)
                (Hn2 i Hi))).
  apply maps_upd_at_app_l. by apply maps_upd_at_app_r.
Qed.

(* ---------------------------------------------------------------------- *)
(* 4b. THE TREE SURGERY.  [ptree_set_leaf] is [pt_upd_kid] twice and        *)
(* [pt_upd_ent] once, and each of the three replaces exactly one element of *)
(* the byte-map list.                                                       *)
(* ---------------------------------------------------------------------- *)
Lemma uint_mword9 (j : Z) : (0 <= j < 512)%Z -> uint (mword_of_int j : mword 9) = j.
Proof.
  intro Hj.
  pose proof (bv_unsigned_in_range _ (mword_of_int j : mword 9)) as Hr.
  unfold uint, get_word, MachineWord.MachineWord.word_to_N.
  rewrite Z2N.id; [| exact (proj1 Hr)].
  unfold SailStdpp.Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_small; [reflexivity |].
  change (bv_modulus (MachineWord.MachineWord.Z_idx 9)) with 512%Z. exact Hj.
Qed.

Lemma mword9_of_int_ne (j : Z) (i : mword 9) :
  (0 <= j < 512)%Z -> j <> uint i -> (mword_of_int j : mword 9) <> i.
Proof.
  intros Hj Hne Heq. apply Hne.
  rewrite <- (uint_mword9 j Hj). by rewrite Heq.
Qed.

Lemma seqZ_512_nodup : base.NoDup (seqZ 0 512).
Proof. apply NoDup_seqZ. Qed.

Lemma seqZ_512_mem (i : mword 9) : uint i ∈ seqZ 0 512.
Proof. apply elem_of_seqZ. pose proof (mword9_uint_range i). lia. Qed.


(* the projections of an updated node, as small equations -- NEVER let a
   [cbn] near a goal that mentions [pt_page_maps]: its body carries
   [seqZ 0 512] and a whitelisted [cbn] still fires the iota that computes
   the 512-element list *)
Lemma pt_base_upd_ent (t : ptree) (i : mword 9) (q : mword 64) :
  pt_base (pt_upd_ent t i q) = pt_base t.
Proof. reflexivity. Qed.

Lemma pt_ents_upd_ent_same (t : ptree) (i : mword 9) (q : mword 64) :
  pt_ents (pt_upd_ent t i q) i = q.
Proof.
  unfold pt_upd_ent. cbn [pt_ents].
  destruct (decide (i = i)) as [_ | Hc]; [ reflexivity | congruence ].
Qed.

Lemma pt_ents_upd_ent_ne (t : ptree) (i i' : mword 9) (q : mword 64) :
  i' <> i -> pt_ents (pt_upd_ent t i q) i' = pt_ents t i'.
Proof.
  intros Hne. unfold pt_upd_ent. cbn [pt_ents].
  destruct (decide (i' = i)) as [Hc | _]; [ congruence | reflexivity ].
Qed.

Lemma pt_kids_upd_kid_same (t : ptree) (i : mword 9) (c : option ptree) :
  pt_kids (pt_upd_kid t i c) i = c.
Proof.
  unfold pt_upd_kid. cbn [pt_kids].
  destruct (decide (i = i)) as [_ | Hc]; [ reflexivity | congruence ].
Qed.

Lemma pt_kids_upd_kid_ne (t : ptree) (i i' : mword 9) (c : option ptree) :
  i' <> i -> pt_kids (pt_upd_kid t i c) i' = pt_kids t i'.
Proof.
  intros Hne. unfold pt_upd_kid. cbn [pt_kids].
  destruct (decide (i' = i)) as [Hc | _]; [ congruence | reflexivity ].
Qed.

Lemma moi_ne (j k : Z) : (0 <= j < 512)%Z -> (0 <= k < 512)%Z -> k <> j ->
  (mword_of_int k : mword 9) <> mword_of_int j.
Proof.
  intros Hj Hk Hne Hc. apply Hne.
  rewrite <- (uint_mword9 k Hk). rewrite Hc. by apply uint_mword9.
Qed.

(* A NODE'S OWN PAGE, with one slot word replaced.  Indexed by the Z the
   [seqZ] carries -- [mword_of_int (uint i)] is only PROPOSITIONALLY [i], so
   a statement at [i] would not match the list the [fmap] builds.  And BOTH
   endpoints are spelled as the [fmap]'s OWN function applied to the index,
   so [apply] never has to decide [decide (x = x)] by conversion -- which on
   a symbolic [mword 9] does not come back. *)
Lemma pt_page_maps_upd_ent (t : ptree) (j : Z) (q : mword 64) :
  (0 <= j < 512)%Z ->
  maps_upd_at
    (word_bytes (u_pte_addr (pt_base t) (mword_of_int j))
                (pt_ents t (mword_of_int j)))
    (word_bytes (u_pte_addr (pt_base (pt_upd_ent t (mword_of_int j) q))
                            (mword_of_int j))
                (pt_ents (pt_upd_ent t (mword_of_int j) q) (mword_of_int j)))
    (pt_page_maps t) (pt_page_maps (pt_upd_ent t (mword_of_int j) q)).
Proof.
  intros Hj. unfold pt_page_maps.
  apply (fmap_upd_at (seqZ 0 512)
           (fun i0 : Z => word_bytes (u_pte_addr (pt_base t) (mword_of_int i0))
                            (pt_ents t (mword_of_int i0)))
           (fun i0 : Z =>
              word_bytes (u_pte_addr (pt_base (pt_upd_ent t (mword_of_int j) q))
                                     (mword_of_int i0))
                (pt_ents (pt_upd_ent t (mword_of_int j) q) (mword_of_int i0)))
           j).
  - apply seqZ_512_nodup.
  - apply elem_of_seqZ. lia.
  - intros k Hk Hne. cbn beta. apply elem_of_seqZ in Hk.
    rewrite pt_base_upd_ent.
    rewrite (pt_ents_upd_ent_ne t (mword_of_int j) (mword_of_int k) q
               (moi_ne j k Hj ltac:(lia) Hne)).
    reflexivity.
Qed.

Lemma pt_maps_upd_ent (lvl : nat) (t : ptree) (j : Z) (q : mword 64) :
  (0 <= j < 512)%Z ->
  maps_upd_at
    (word_bytes (u_pte_addr (pt_base t) (mword_of_int j))
                (pt_ents t (mword_of_int j)))
    (word_bytes (u_pte_addr (pt_base (pt_upd_ent t (mword_of_int j) q))
                            (mword_of_int j))
                (pt_ents (pt_upd_ent t (mword_of_int j) q) (mword_of_int j)))
    (pt_maps lvl t) (pt_maps lvl (pt_upd_ent t (mword_of_int j) q)).
Proof.
  intros Hj. destruct lvl as [| lvl].
  - rewrite !pt_maps_O. by apply pt_page_maps_upd_ent.
  - rewrite !pt_maps_S.
    apply maps_upd_at_app_r. by apply pt_page_maps_upd_ent.
Qed.

Lemma pt_maps_upd_kid (lvl : nat) (t c c' : ptree) (j : Z) (X Y : pamap) :
  (0 <= j < 512)%Z ->
  pt_kids t (mword_of_int j) = Some c ->
  maps_upd_at X Y (pt_maps lvl c) (pt_maps lvl c') ->
  maps_upd_at X Y (pt_maps (S lvl) t)
    (pt_maps (S lvl) (pt_upd_kid t (mword_of_int j) (Some c'))).
Proof.
  intros Hj Hk Hupd. rewrite !pt_maps_S.
  apply maps_upd_at_app_l.
  apply (concat_upd_at (seqZ 0 512)
           (fun i0 : Z => match pt_kids t (mword_of_int i0) with
                          | Some c0 => pt_maps lvl c0 | None => [] end)
           (fun i0 : Z =>
              match pt_kids (pt_upd_kid t (mword_of_int j) (Some c'))
                            (mword_of_int i0) with
              | Some c0 => pt_maps lvl c0 | None => [] end)
           j).
  - apply seqZ_512_nodup.
  - apply elem_of_seqZ. lia.
  - intros k Hk2 Hne. cbn beta. apply elem_of_seqZ in Hk2.
    rewrite (pt_kids_upd_kid_ne t (mword_of_int j) (mword_of_int k) (Some c')
               (moi_ne j k Hj ltac:(lia) Hne)).
    reflexivity.
  - cbn beta. rewrite pt_kids_upd_kid_same. by rewrite Hk.
Qed.

(* the two byte maps of one slot have the same keys, whatever the words *)
Lemma word_bytes_is_Some (a : Arch.pa) (w w' : bv 64) (x : Arch.pa) :
  is_Some (word_bytes a w !! x) -> is_Some (word_bytes a w' !! x).
Proof.
  intros [b Hb].
  destruct (word_bytes_dom_elim a w x ltac:(apply elem_of_dom; by exists b))
    as (j & Hj & ->).
  exists (nth_byte w' j). by apply word_bytes_lookup.
Qed.

(* ---------------------------------------------------------------------- *)
(* 4c. THE ABSORPTION.  Writing the leaf slot IS setting the leaf.          *)
(* ---------------------------------------------------------------------- *)
Lemma ptree_bytes_set_leaf (t : ptree) (vpn : mword 27) (p2 p1 p0 q : mword 64) :
  maps_disj (pt_maps 2 t) ->
  ptree_maps t vpn p2 p1 p0 ->
  ptree_bytes 2 (ptree_set_leaf t vpn q)
  = write_bytes (ptree_bytes 2 t) (pt_addr0 p1 vpn) 8 q.
Proof.
  intros Hdisj (c1 & c0 & Hk1 & Hk0 & He2 & He1 & He0 & Hb1 & Hb0 & _).
  (* the three indices, as the [Z]s the slot lists carry *)
  pose proof (mword9_uint_range (vpn_idx 2 vpn)) as Hr2.
  pose proof (mword9_uint_range (vpn_idx 1 vpn)) as Hr1.
  pose proof (mword9_uint_range (vpn_idx 0 vpn)) as Hr0.
  (* the leaf page, updated *)
  pose proof (pt_maps_upd_ent 0 c0 (uint (vpn_idx 0 vpn)) q Hr0) as H0.
  rewrite mword9_uint_id in H0.
  (* ...through the mid node, then through the root *)
  pose proof (pt_maps_upd_kid 0 c1 c0 (pt_upd_ent c0 (vpn_idx 0 vpn) q)
                (uint (vpn_idx 1 vpn)) _ _ Hr1
                ltac:(rewrite mword9_uint_id; exact Hk0) H0) as H1.
  rewrite mword9_uint_id in H1.
  pose proof (pt_maps_upd_kid 1 t c1
                (pt_upd_kid c1 (vpn_idx 1 vpn)
                   (Some (pt_upd_ent c0 (vpn_idx 0 vpn) q)))
                (uint (vpn_idx 2 vpn)) _ _ Hr2
                ltac:(rewrite mword9_uint_id; exact Hk1) H1) as H2.
  rewrite mword9_uint_id in H2.
  (* the tree the model lands on IS that update *)
  assert (Hsl : ptree_set_leaf t vpn q
                = pt_upd_kid t (vpn_idx 2 vpn)
                    (Some (pt_upd_kid c1 (vpn_idx 1 vpn)
                             (Some (pt_upd_ent c0 (vpn_idx 0 vpn) q))))).
  { unfold ptree_set_leaf. rewrite Hk1. by rewrite Hk0. }
  rewrite Hsl.
  (* the endpoints, in the caller's spelling *)
  rewrite pt_base_upd_ent in H2. rewrite pt_ents_upd_ent_same in H2.
  unfold ptree_bytes.
  rewrite (union_list_upd_at _ _ (pt_maps 2 t) _ Hdisj H2
             (fun x Hx => word_bytes_is_Some _ _ q x Hx)
             (fun x Hx => word_bytes_is_Some _ q _ x Hx)).
  rewrite write_bytes_word.
  unfold pt_addr0. by rewrite Hb0.
Qed.

(* ---------------------------------------------------------------------- *)
(* 4d. ...AND SO THE WRITE-BACK IS A [u_mem_step].                          *)
(* ---------------------------------------------------------------------- *)
Lemma pt_same_shape_upd_ent (lvl : nat) (t : ptree) (i : mword 9) (q : mword 64) :
  pt_same_shape lvl t (pt_upd_ent t i q).
Proof.
  destruct lvl as [| lvl]; split; [ reflexivity | done | reflexivity |].
  intros k. cbn [pt_kids pt_upd_ent].
  destruct (pt_kids t k) as [c|]; [ apply pt_same_shape_refl | done ].
Qed.

Lemma pt_same_shape_upd_kid (lvl : nat) (t c c' : ptree) (i : mword 9) :
  pt_kids t i = Some c -> pt_same_shape lvl c c' ->
  pt_same_shape (S lvl) t (pt_upd_kid t i (Some c')).
Proof.
  intros Hk Hs. split; [ reflexivity |].
  intros k. destruct (decide (k = i)) as [-> | Hne].
  - rewrite pt_kids_upd_kid_same. rewrite Hk. exact Hs.
  - rewrite (pt_kids_upd_kid_ne t i k (Some c') Hne).
    destruct (pt_kids t k) as [c0|]; [ apply pt_same_shape_refl | done ].
Qed.

Lemma pt_same_shape_set_leaf (t : ptree) (vpn : mword 27) (p2 p1 p0 q : mword 64) :
  ptree_maps t vpn p2 p1 p0 -> pt_same_shape 2 t (ptree_set_leaf t vpn q).
Proof.
  intros (c1 & c0 & Hk1 & Hk0 & _).
  assert (Hsl : ptree_set_leaf t vpn q
                = pt_upd_kid t (vpn_idx 2 vpn)
                    (Some (pt_upd_kid c1 (vpn_idx 1 vpn)
                             (Some (pt_upd_ent c0 (vpn_idx 0 vpn) q))))).
  { unfold ptree_set_leaf. rewrite Hk1. by rewrite Hk0. }
  rewrite Hsl.
  apply (pt_same_shape_upd_kid 1 t c1 _ (vpn_idx 2 vpn) Hk1).
  apply (pt_same_shape_upd_kid 0 c1 c0 _ (vpn_idx 1 vpn) Hk0).
  apply pt_same_shape_upd_ent.
Qed.

Lemma u_mem_step_writeback (P : uptd) (t : ptree) (mm : pamap)
    (vpn : mword 27) (p2 p1 p0 q : mword 64) :
  u_mem_wf P t mm ->
  ptree_maps t vpn p2 p1 p0 ->
  upt_tree_spec (ud_root P) (ud_tfp P) (ud_um P) (ptree_set_leaf t vpn q) ->
  u_mem_step P t (ptree_set_leaf t vpn q) mm
    (write_bytes mm (pt_addr0 p1 vpn) 8 q).
Proof.
  intros Hwf Hmaps Hspec'.
  pose proof (pt_same_shape_set_leaf t vpn p2 p1 p0 q Hmaps) as Hshape.
  destruct Hwf as (md & Hdisj & Hdj & Hmm & Hdm & Hram & Hrest).
  (* the slot's OLD bytes live in the tree half, hence are disjoint from the
     data half; the NEW ones have the same keys, so they are too *)
  assert (Hwdj : word_bytes (pt_addr0 p1 vpn) q ##ₘ md).
  { apply map_disjoint_spec. intros x b1 b2 H1 H2.
    destruct (word_bytes_is_Some (pt_addr0 p1 vpn) q p0 x (mk_is_Some _ _ H1))
      as [b0 Hb0].
    pose proof (maps_disj_subseteq (pt_maps 2 t)
                  (word_bytes (pt_addr0 p1 vpn) p0) Hdisj
                  (ptree_maps_slot0 t vpn p2 p1 p0 Hmaps)) as Hsubt.
    pose proof (lookup_weaken _ _ x b0 Hb0 Hsubt) as Hbt.
    exact (proj1 (map_disjoint_spec (ptree_bytes 2 t) md) Hdj x b0 b2 Hbt H2). }
  assert (Heq : ptree_bytes 2 (ptree_set_leaf t vpn q)
                = word_bytes (pt_addr0 p1 vpn) q ∪ ptree_bytes 2 t).
  { rewrite (ptree_bytes_set_leaf t vpn p2 p1 p0 q Hdisj Hmaps).
    apply write_bytes_word. }
  split_and!; [ exact Hshape | exact Hspec' |].
  exists md. split_and!.
  - rewrite Heq. apply map_disjoint_union_l. by split.
  - rewrite Hmm. rewrite write_bytes_union_l. rewrite write_bytes_word.
    rewrite Heq. reflexivity.
  - exact Hdm.
Qed.

(* ===================================================================== *)
(* 5. WHAT THE WRITE-BACK DOES *NOT* TOUCH, and the fetched word.         *)
(* ===================================================================== *)

(* the DATA half is untouched by a page-table write: that is the whole      *)
(* content of the [ptree_bytes ##ₘ md] conjunct of [u_mem_wf], and it is    *)
(* what lets the instruction read be justified at the POST-translate state. *)
Lemma u_writeback_data (P : uptd) (t : ptree) (mm : pamap) (vpn : mword 27)
    (p2 p1 p0 q : mword 64) (x : Arch.pa) :
  u_mem_wf P t mm -> ptree_maps t vpn p2 p1 p0 -> u_data_pa P x ->
  write_bytes mm (pt_addr0 p1 vpn) 8 q !! x = mm !! x.
Proof.
  intros Hwf Hmaps Hx.
  pose proof Hwf as Hwf0.
  destruct Hwf as (md & Hdisj & Hdj & Hmm & Hdm & _).
  rewrite write_bytes_word.
  destruct (word_bytes (pt_addr0 p1 vpn) q !! x) as [b|] eqn:Hw;
    [| by rewrite (lookup_union_r _ mm x Hw) ].
  exfalso.
  destruct (word_bytes_is_Some (pt_addr0 p1 vpn) q p0 x (mk_is_Some _ _ Hw))
    as [b0 Hb0].
  pose proof (maps_disj_subseteq (pt_maps 2 t)
                (word_bytes (pt_addr0 p1 vpn) p0) Hdisj
                (ptree_maps_slot0 t vpn p2 p1 p0 Hmaps)) as Hsubt.
  pose proof (lookup_weaken _ _ x b0 Hb0 Hsubt) as Hbt.
  destruct (proj1 (Hdm x) Hx) as [bd Hbd].
  exact (proj1 (map_disjoint_spec (ptree_bytes 2 t) md) Hdj x b0 bd Hbt Hbd).
Qed.

(* THE WINDOW IS OWNED, at any width the page divides.  Factored out of
   [u_fetch_bytes] because the 2-ALIGNED split fetch reads HALFWORDS: the
   coverage argument is width-generic (it is [udata_cov] under
   [UserBytes.u_walk_pa_window_wf]) and only the byte-list assembly at the
   end is not. *)
Lemma u_fetch_win_in (P : uptd) (t : ptree) (mm : pamap) (k : Z)
    (w va : mword 64) :
  0 < k -> (k | 4096) ->
  u_mem_wf P t mm ->
  ud_um P !! svpn_of va = Some w ->
  is_aligned_vaddr (Virtaddr va) k = true ->
  forall j : nat, (j < Z.to_nat k)%nat ->
    is_Some (mm !! pa_add (u_walk_pa w va) j).
Proof.
  intros Hk Hdvd Hwf Hl Hal j Hj.
  pose proof Hwf as (md & Hdisj & Hdj & Hmm & Hdm & Hram & _ & Hwfm & _).
  assert (Hd : u_data_pa P (pa_add (u_walk_pa w va) j)).
  { rewrite (u_walk_pa_window_wf k w va j Hk Hdvd Hal Hj).
    exact (u_data_pa_cov P (svpn_of va) w (add_vec_int va (Z.of_nat j)) Hwfm Hl). }
  destruct (proj1 (Hdm _) Hd) as [bd Hbd].
  exists bd. rewrite Hmm.
  destruct (ptree_bytes 2 t !! pa_add (u_walk_pa w va) j) as [c|] eqn:Ht.
  - exfalso.
    exact (proj1 (map_disjoint_spec (ptree_bytes 2 t) md) Hdj _ c bd Ht Hbd).
  - by rewrite (lookup_union_r _ md _ Ht).
Qed.

(* the TWO instruction bytes of a halfword fetch are in the owned map *)
Lemma nth_byte_assemble2 (bs : list (bv 8)) (j : nat) :
  length bs = 2%nat -> (j < 2)%nat ->
  nth_byte (Z_to_bv 16 (assemble_bytes bs) : mword 16) j = bs !!! j.
Proof. intros Hlen Hj. apply nth_byte_assemble_len; lia. Qed.

Lemma u_fetch_bytes_2 (P : uptd) (t : ptree) (mm : pamap) (w va : mword 64) :
  u_mem_wf P t mm ->
  ud_um P !! svpn_of va = Some w ->
  is_aligned_vaddr (Virtaddr va) 2 = true ->
  exists ih : mword 16,
    forall j : nat, (N.of_nat j < 2)%N ->
      mm !! pa_add (u_walk_pa w va) j = Some (nth_byte ih j).
Proof.
  intros Hwf Hl Hal.
  assert (Hin : forall j : nat, (j < 2)%nat ->
            is_Some (mm !! pa_add (u_walk_pa w va) j))
    by (intros j Hj;
        exact (u_fetch_win_in P t mm 2 w va ltac:(lia) (Z.divide_factor_l 2 2048)
                 Hwf Hl Hal j ltac:(lia))).
  destruct (Hin 0%nat ltac:(lia)) as [b0 Hb0].
  destruct (Hin 1%nat ltac:(lia)) as [b1 Hb1].
  exists (Z_to_bv 16 (assemble_bytes [b0; b1]) : mword 16).
  intros j HjN.
  assert (Hj : (j < 2)%nat) by lia.
  rewrite (nth_byte_assemble2 [b0; b1] j eq_refl Hj).
  destruct j as [ | [ | ] ]; try lia;
    cbn [lookup_total list_lookup_total];
    [ exact Hb0 | exact Hb1 ].
Qed.

(* the four instruction bytes are in the owned map, with SOME value *)
Lemma u_fetch_bytes (P : uptd) (t : ptree) (mm : pamap) (w va : mword 64) :
  u_mem_wf P t mm ->
  ud_um P !! svpn_of va = Some w ->
  is_aligned_vaddr (Virtaddr va) 4 = true ->
  exists iw : mword 32,
    forall j : nat, (N.of_nat j < 4)%N ->
      mm !! pa_add (u_walk_pa w va) j = Some (nth_byte iw j).
Proof.
  intros Hwf Hl Hal.
  set (pa := u_walk_pa w va).
  assert (Hin : forall j : nat, (j < 4)%nat -> is_Some (mm !! pa_add pa j))
    by (intros j Hj;
        exact (u_fetch_win_in P t mm 4 w va ltac:(lia) (Z.divide_factor_l 4 1024)
                 Hwf Hl Hal j ltac:(lia))).
  destruct (Hin 0%nat ltac:(lia)) as [b0 Hb0].
  destruct (Hin 1%nat ltac:(lia)) as [b1 Hb1].
  destruct (Hin 2%nat ltac:(lia)) as [b2 Hb2].
  destruct (Hin 3%nat ltac:(lia)) as [b3 Hb3].
  exists (Z_to_bv 32 (assemble_bytes [b0; b1; b2; b3]) : mword 32).
  intros j HjN.
  assert (Hj : (j < 4)%nat) by lia.
  rewrite (nth_byte_assemble4 [b0; b1; b2; b3] j eq_refl Hj).
  destruct j as [ | [ | [ | [ | ] ] ] ]; try lia;
    cbn [lookup_total list_lookup_total];
    [ exact Hb0 | exact Hb1 | exact Hb2 | exact Hb3 ].
Qed.

(* ===================================================================== *)
(* 6. THE THREE [translateAddr] INGREDIENTS AT THE FETCH, certified.       *)
(* ===================================================================== *)

Lemma goodb_read_reg_D (Db : register -> bool) {E} (r : register) (s : mstate) :
  Db r = true -> goodb Db (Defs.read_reg r : Defs.monad E _) s = true.
Proof. intros HD. unfold Defs.read_reg. cbn [goodb]. by rewrite HD. Qed.

Lemma goodb_effectivePrivilege_fetch (Db : register -> bool) (m : mword 64)
    (p : Privilege) (s : mstate) :
  goodb Db (effectivePrivilege (InstructionFetch tt) m p) s = true.
Proof.
  unfold effectivePrivilege.
  replace (generic_neq (InstructionFetch tt) (InstructionFetch tt)) with false
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma goodb_is_shadow_stack_fetch (Db : register -> bool) (s : mstate) :
  goodb Db (is_shadow_stack_access (InstructionFetch tt)) s = true.
Proof. unfold is_shadow_stack_access. cbn match. reflexivity. Qed.

Lemma goodb_architecture_Supervisor (Db : register -> bool) (s : mstate) :
  Db mstatus = true ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  goodb Db (architecture Supervisor) s = true.
Proof.
  intros HD HSXL. unfold architecture. cbn match.
  match goal with |- goodb _ (Defs.bind ?L _) _ = true =>
    assert (Hin : exec L s
                  = Some (_get_Mstatus_SXL (register_lookup mstatus s.(sregs)), s));
    [ | assert (Hing : goodb Db L s = true) ] end.
  { rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)). apply exec_returnM. }
  { rewrite (goodb_bind Db _ _ s _ (goodb_read_reg_D Db mstatus s HD)
               (exec_read_reg mstatus s)). reflexivity. }
  rewrite (goodb_bind Db _ _ s _ Hing Hin).
  unfold architecture_bits_backwards. rewrite HSXL.
  replace (eq_vec ('b"10") ('b"01")) with false by (vm_compute; reflexivity).
  cbn match.
  replace (eq_vec ('b"10") ('b"10")) with true by (vm_compute; reflexivity).
  cbn match. reflexivity.
Qed.

Lemma goodb_translationMode_U (Db : register -> bool) (satp0 : mword 64) (s : mstate) :
  Db mstatus = true -> Db satp = true ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  goodb Db (translationMode User) s = true.
Proof.
  intros HDms HDsatp HSXL Hsatp Hmode.
  unfold translationMode.
  change (generic_eq User Machine) with false. cbn match.
  rewrite (goodb_bind Db _ _ s RV64
             (goodb_architecture_Supervisor Db s HDms HSXL)
             (exec_architecture_Supervisor s HSXL)).
  assert (Hae : exec (Defs.assert_exp' (Z.geb xlen 64) "sys/vmem.sail:254.25-254.26") s
                = Some (eq_refl, s)).
  { replace (Z.geb xlen 64) with true by (vm_compute; reflexivity).
    unfold Defs.assert_exp'. cbn match. apply exec_returnm. }
  assert (Haeg : goodb Db (Defs.assert_exp' (Z.geb xlen 64)
                             "sys/vmem.sail:254.25-254.26" : M _) s = true).
  { unfold Defs.assert_exp'.
    replace (Z.geb xlen 64) with true by (vm_compute; reflexivity).
    cbn match. reflexivity. }
  match goal with |- goodb _ (Defs.bind ?L _) _ = true =>
    assert (Hmb : exec L s = Some (_get_Satp64_Mode (Mk_Satp64 satp0), s));
    [ | assert (Hmbg : goodb Db L s = true) ] end.
  { rewrite (exec_bind_Some _ _ _ _ _ Hae).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
    rewrite Hsatp. apply exec_returnm. }
  { rewrite (goodb_bind Db _ _ s _ Haeg Hae).
    rewrite (goodb_bind Db _ _ s _ (goodb_read_reg_D Db satp s HDsatp)
               (exec_read_reg satp s)). reflexivity. }
  rewrite (goodb_bind Db _ _ s _ Hmbg Hmb).
  rewrite Hmode.
  replace (satpMode_of_bits RV64 ('b"1000" : mword 4)) with (Some Sv39)
    by (vm_compute; reflexivity).
  cbn match. reflexivity.
Qed.

(* THE LEAF'S PERMISSION CHECK, certified at an ABSTRACT leaf word.
   [check_PTE_permission] is not register-free in general: on the
   R=0,W=1,X=0 encoding it reads [menvcfg] and then ASSERTS on
   menvcfg.SSE, which no abstract state decides, and its leading
   [assert_exp (W -> (R || !X))] is an error node on W=1,R=0,X=1.  At a
   leaf the fetch is PERMITTED on, [pte_check_ok] rules both out -- read
   at [dstateM] (menvcfg = 0) each would make [exec] answer something
   other than [PTE_Check_Success] -- and what is left reads nothing, so
   the certificate holds at EVERY footprint.  That is the shape
   [PtWalkCert.goodmb_ptree_translateAddr]'s [Hgchk] premise wants.
   (Its natural home is beside [uleaf_ok] in [UserPtTree.v].) *)
Lemma goodb_check_PTE_permission_fetch (w' : mword 64) (mxr do_sum : bool)
    (Db : register -> bool) (s : mstate) :
  pte_check_ok (InstructionFetch tt) User mxr do_sum w' ->
  goodb Db (check_PTE_permission (InstructionFetch tt) User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec w' 7 0)) (ext_bits_of_PTE w') tt) s = true.
Proof.
  unfold pte_check_ok. intro Hchk.
  pose proof (Hchk dstateM) as Hc0.
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
(* 7. [u_fetch_pure] -- THE PURE FETCH COMPOSER.                          *)
(*                                                                        *)
(* [UserFetchPt.user_pt_fetch_instr] with its [reg_interp] /               *)
(* [gen_heap_interp] / [utlb_inv_pt] / [udata_own] premises replaced by    *)
(* [UserClassifyAsm.u_exec_pins] + [UserBytes.u_mem_wf], a [goodmb]        *)
(* conjunct added, and the post-state said out loud.  Stated at the        *)
(* tier's reference state [u_state rsf mm] (section 9 of the worklist), so *)
(* the successor state is LITERALLY [u_state rsf' mm'] -- which is what    *)
(* [base_exec_total_u] / [rvc_exec_total_u] are stated over, so the caller *)
(* feeds this straight into them with no state algebra in between.         *)
(*                                                                        *)
(* THE FIVE CONJUNCTS, and who consumes each:                              *)
(*   - the [exec] fact, with [UserFetch.exec_fetch_ok_4]'s own             *)
(*     if-isRVC shape: [HartRunFull.run_fetch_base] / [run_fetch_rvc].     *)
(*   - the certificate at [Du_r]/[Du_w] and at the map the hart holds:     *)
(*     [HartMemRun.swp_hmrun_of_exec], for the fetch node.                 *)
(*   - the landing FILE ([rsf] itself, or ONE [tlb] write): every other    *)
(*     ambient pin -- [post_fetch_cfg], [u_hw_pins], [u_cfg_pins],         *)
(*     [u_pt_pins] -- transports across it by [irrelevant_register_set],   *)
(*     which is what lets the caller rebuild [u_exec_pins P t' rsf'].      *)
(*   - [tlb_ok_pt] at the NEW tree: [u_exec_pins]' fourth conjunct.        *)
(*   - [u_mem_step]: [UserBytes.u_mem_step_wf] gives [u_mem_wf P t' mm'],  *)
(*     and [UserClassifyAsm.u_landing_map] turns                            *)
(*     [swp_hmrun_of_exec]'s existential post map into [mm'].              *)
(*                                                                        *)
(* The three [translateAddr] outcomes are handled ONCE, in [Hland]: a TLB  *)
(* hit changes nothing, a fill writes [tlb] and keeps the tree, and the    *)
(* Svadu write-back does both and moves the tree by [ptree_set_leaf]       *)
(* ([u_mem_step_writeback] + [UptTree.upt_tree_spec_set_leaf] +            *)
(* [PtTree.tlb_ok_pt_fill_self] / [tlb_ok_pt_set_leaf]).  Nothing after    *)
(* [Hland] looks at which arm ran.                                         *)
(* ===================================================================== *)

(* ---------------------------------------------------------------------- *)
(* 7a. THE FETCH WALK, ONCE -- factored out because the 2-ALIGNED split     *)
(* fetch runs it TWICE (at [va], and at [va+2] when the low halfword is     *)
(* not compressed, possibly onto another page).                            *)
(*                                                                        *)
(* The landing is stated as [u_tlb_only], NOT as the one-walk disjunction   *)
(* "[rsf] or ONE [register_set tlb]": that shape does not compose, because  *)
(* collapsing two nested [register_set tlb]s needs functional              *)
(* extensionality (see [UserClassifyAsm.u_tlb_only]).  The one-walk caller  *)
(* below still gets the disjunction, from [Hland] directly.                 *)
(*                                                                        *)
(* The three cfg pins are taken SEPARATELY rather than as                   *)
(* [post_fetch_cfg]: at the second halfword the pc is still [va], so        *)
(* [post_fetch_cfg _ (va+2) _] is not available, while the three registers  *)
(* it would supply are unchanged.                                          *)
(* ---------------------------------------------------------------------- *)
Lemma u_walk_fetch_pure (P : uptd) (t : ptree) (mm : pamap) (rsf : regstate)
    (w va : mword 64) :
  ud_um P !! svpn_of va = Some w ->
  uleaf_ok (InstructionFetch tt) w ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                        (Z.sub 39 1) 0)) = false ->
  register_lookup cur_privilege rsf = User ->
  _get_Mstatus_SXL (register_lookup mstatus rsf) = 'b"10" ->
  register_lookup menvcfg rsf = MENVCFG_S ->
  u_exec_pins P t rsf ->
  u_mem_wf P t mm ->
  exists (rsf' : regstate) (mm' : pamap) (t' : ptree),
    exec (translateAddr (Virtaddr va) (InstructionFetch tt)) (u_state rsf mm)
      = Some (Ok (Physaddr (u_walk_pa w va), PBMT_PMA, init_ext_ptw),
              u_state rsf' mm') /\
    goodmb Du_r Du_w (translateAddr (Virtaddr va) (InstructionFetch tt))
      (u_state rsf mm) mm = true /\
    (rsf' = rsf \/ exists tv, rsf' = register_set tlb tv rsf) /\
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf') /\
    u_mem_step P t t' mm mm'.
Proof.
  intros Hl Hleaf Hcanon Lcp Lsxl Lmenv Hpins Hwf.
  destruct Hpins as (Hhw & Hcfgp & Hpt & Htlbok).
  destruct Hhw as (Hmisa & Hmseccfg & Hsenv & Hhtif & Hall & Help).
  destruct Hpt as ((usatp & Hsatpok & Hsatp) & HA & Hord & HXp & HWp & HRp & Hcovp).
  destruct Hsatpok as (Hmode & Hasid & Hppn & Hpmaw_of).
  pose proof Hwf as (md & Hdisj & Hdj & Hmm & Hdm & Hram & Hacc & Hwfm & Hspec).
  pose proof Hspec as (Hbase & _).
  destruct (upt_spec_maps (ud_root P) (ud_tfp P) (ud_um P) t (svpn_of va) w
              Hspec (or_intror (or_intror Hl)))
    as (p2 & p1 & a0 & d0 & Hmaps).
  pose proof Hmaps as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ &
                       Hv2 & Hn2 & Hv1 & Hn1 & Hv0 & Hl0 & Hnap & Hpb0).
  (* the leaf's per-variant classification *)
  assert (Hvar : forall a d : mword 1,
            pte_valid (pte_set_ad w a d) /\ pte_leaf (pte_set_ad w a d) /\
            pte_no_napot (pte_set_ad w a d) /\ pte_pbmt0 (pte_set_ad w a d))
    by exact (upt_variant (ud_tfp P) (ud_um P) (svpn_of va) w Hwfm
                (or_intror (or_intror Hl))).
  (* the three slots, as reads and as ownership *)
  assert (Hsm2 : pt_slot_mem (u_state rsf mm) (pt_addr2 t (svpn_of va)) p2)
    by exact (u_slot_mem_at P t mm rsf (pt_base t) (vpn_idx 2 (svpn_of va)) p2 Hwf
                (ptree_maps_slot2 t (svpn_of va) p2 p1 _ Hmaps)).
  assert (Hsm1 : pt_slot_mem (u_state rsf mm) (pt_addr1 p2 (svpn_of va)) p1)
    by exact (u_slot_mem_at P t mm rsf (u_next_base p2) (vpn_idx 1 (svpn_of va)) p1 Hwf
                (ptree_maps_slot1 t (svpn_of va) p2 p1 _ Hmaps)).
  assert (Hsm0 : pt_slot_mem (u_state rsf mm) (pt_addr0 p1 (svpn_of va))
                   (pte_set_ad w a0 d0))
    by exact (u_slot_mem_at P t mm rsf (u_next_base p1) (vpn_idx 0 (svpn_of va)) _ Hwf
                (ptree_maps_slot0 t (svpn_of va) p2 p1 _ Hmaps)).
  assert (Hown2 : bytes_owned mm (pt_addr2 t (svpn_of va)) 8 = true)
    by exact (u_slot_owned P t mm _ p2 Hwf (ptree_maps_slot2 t (svpn_of va) p2 p1 _ Hmaps)).
  assert (Hown1 : bytes_owned mm (pt_addr1 p2 (svpn_of va)) 8 = true)
    by exact (u_slot_owned P t mm _ p1 Hwf (ptree_maps_slot1 t (svpn_of va) p2 p1 _ Hmaps)).
  assert (Hown0 : bytes_owned mm (pt_addr0 p1 (svpn_of va)) 8 = true)
    by exact (u_slot_owned P t mm _ _ Hwf (ptree_maps_slot0 t (svpn_of va) p2 p1 _ Hmaps)).
  (* the three read-only probes of [translateAddr]'s front matter *)
  assert (Htm : exec (translationMode User) (u_state rsf mm)
                = Some (Sv39, u_state rsf mm))
    by exact (exec_translationMode_U_sv39 usatp (u_state rsf mm) Lsxl Hsatp Hmode).
  assert (Htmg : goodb Du_r (translationMode User) (u_state rsf mm) = true)
    by exact (goodb_translationMode_U Du_r usatp (u_state rsf mm)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                Lsxl Hsatp Hmode).
  assert (Heff : exec (effectivePrivilege (InstructionFetch tt)
                        (register_lookup mstatus (u_state rsf mm).(sregs)) User)
                   (u_state rsf mm) = Some (User, u_state rsf mm))
    by exact (exec_effectivePrivilege_fetch _ User (u_state rsf mm)).
  assert (Hssx : exec (is_shadow_stack_access (InstructionFetch tt)) (u_state rsf mm)
                 = Some (false, u_state rsf mm))
    by exact (exec_is_shadow_stack_fetch (u_state rsf mm)).
  (* the PMA grants *)
  assert (Hpmar : pma_allows_pte_read
                    (register_lookup pma_regions (u_state rsf mm).(sregs)))
    by exact (pma_allows_all_pte_read _ Hall).
  assert (Hpmaw : pma_allows_pte_write
                    (register_lookup pma_regions (u_state rsf mm).(sregs)))
    by exact (Hpmaw_of _ Hall).
  (* the leaf's permission check and the three validity tests, certified *)
  assert (Hgchk : forall (a d : mword 1) (mxr do_sum : bool)
                    (Db : register -> bool) (s0 : mstate),
            goodb Db (check_PTE_permission (InstructionFetch tt) User mxr do_sum
                        (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
                        (ext_bits_of_PTE (pte_set_ad w a d)) tt) s0 = true).
  { intros a d mxr do_sum Db s0.
    exact (goodb_check_PTE_permission_fetch (pte_set_ad w a d) mxr do_sum Db s0
             (Hleaf a d mxr do_sum)). }
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
  destruct (KptTree.ptree_translateAddr_cases (InstructionFetch tt) User
              (ud_root P) va w (u_walk_pa w va) usatp t (register_lookup tlb rsf)
              p2 p1 a0 d0 (u_state rsf mm)
              Hleaf Hcanon eq_refl (fun a d => proj2 (proj2 (proj2 (Hvar a d))))
              Hbase Hmaps Htlbok Hsm2 Hsm1 Hsm0
              Hmisa Lmenv Hhtif Lcp Htm Heff Hssx Hsatp Hppn Hasid eq_refl
              HA Hord HRp HWp Hcovp Hpmar Hpmaw)
    as (sf & Htr & Harms).
  assert (Htrg : goodmb Du_r Du_w
                   (translateAddr (Virtaddr va) (InstructionFetch tt))
                   (u_state rsf mm) mm = true).
  { apply (goodmb_ptree_translateAddr Du_r Du_w (InstructionFetch tt) User
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity)
             (ud_root P) t va w (u_walk_pa w va) usatp (register_lookup tlb rsf)
             p2 p1 a0 d0 (u_state rsf mm) mm
             Hleaf Hgchk Hcanon eq_refl
             (fun a d => proj2 (proj2 (proj2 (Hvar a d))))
             Hbase Hmaps Htlbok Hg2 Hg1 Hg0 Hsm2 Hsm1 Hsm0 Hown2 Hown1 Hown0
             Hmisa Lmenv Hhtif Lcp Htm Htmg Heff
             (goodb_effectivePrivilege_fetch Du_r
                (register_lookup mstatus (u_state rsf mm).(sregs)) User (u_state rsf mm))
             Hssx (goodb_is_shadow_stack_fetch Du_r (u_state rsf mm))
             Hsatp Hppn Hasid eq_refl HA Hord HRp HWp Hcovp Hpmar Hpmaw). }
  (* WHERE THE TRANSLATION LANDED: the three arms, each with its tree, its
     file and its [u_mem_step].  Nothing after this point looks at which. *)
  assert (Hland : exists (rsf' : regstate) (mm' : pamap) (t' : ptree),
            sf = u_state rsf' mm' /\
            (rsf' = rsf \/ exists tv, rsf' = register_set tlb tv rsf) /\
            tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf') /\
            u_mem_step P t t' mm mm').
  { destruct Harms as [-> | [-> | (a1 & d1 & ->)]].
    - exists rsf, mm, t. split_and!;
        [ reflexivity | left; reflexivity | exact Htlbok
        | exact (u_mem_step_refl P t mm Hwf) ].
    - eexists _, mm, t. split_and!.
      + reflexivity.
      + right. eexists. reflexivity.
      + rewrite register_lookup_set.
        exact (tlb_ok_pt_fill_self (mword_of_int 0) t (register_lookup tlb rsf)
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
                 (register_lookup tlb rsf) (svpn_of va) p2 p1 _
                 (ptree_set_leaf_maps_self t (svpn_of va) p2 p1
                    (pte_set_ad w a0 d0) _ Hmaps Hv' Hl' Hn' Hp')
                 (tlb_ok_pt_set_leaf (mword_of_int 0) t (register_lookup tlb rsf)
                    (svpn_of va) p2 p1 (pte_set_ad w a0 d0) a1 d1
                    Hmaps Hv' Hl' Hn' Hp' Htlbok)).
      + exact (u_mem_step_writeback P t mm (svpn_of va) p2 p1
                 (pte_set_ad w a0 d0) _ Hwf Hmaps Hspec'). }
  destruct Hland as (rsf' & mm' & t' & Hsf & Hfile & Htlbok' & Hstep).
  exists rsf', mm', t'. split_and!;
    [ rewrite <- Hsf; exact Htr | exact Htrg | exact Hfile | exact Htlbok'
    | exact Hstep ].
Qed.


(* ---------------------------------------------------------------------- *)
(* 7b. THE PHYSICAL GRANT FOR THE INSTRUCTION READ, width-generic.          *)
(*                                                                        *)
(* Everything [exec_mem_read_fetch_k_U] / [goodmb_mem_read_fetch_k_U] want *)
(* EXCEPT the byte values, which the caller gets from [u_fetch_bytes_k].    *)
(* Used three times: once at width 4 by [u_fetch_pure], and twice at width  *)
(* 2 by the split fetch (the low halfword at [va], the high one at [va+2]). *)
(*                                                                        *)
(* The whole bundle is stated at the POST-walk file [rsf'] and transported  *)
(* from [rsf] by [u_tlb_only]: a filling walk writes [tlb] and nothing the  *)
(* read consults.  The [bytes_owned] conjunct alone is at the PRE map [mm], *)
(* because that is the map the certificate is carried over.                 *)
(* ---------------------------------------------------------------------- *)
Lemma u_fetch_read_ok (P : uptd) (t t' : ptree) (mm mm' : pamap)
    (rsf rsf' : regstate) (k : Z) (w va : mword 64) :
  0 < k -> (k | 4096) -> k <= 16 ->
  uint (to_bits 64 k) = k ->
  is_aligned_vaddr (Virtaddr va) k = true ->
  ud_um P !! svpn_of va = Some w ->
  register_lookup cur_privilege rsf = User ->
  u_exec_pins P t rsf ->
  u_mem_wf P t mm ->
  u_mem_wf P t' mm' ->
  u_tlb_only rsf rsf' ->
  exists region : PMA_Region,
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n rsf') 0)) = TOR /\
    zopz0zKzJ_u (zeros' 64)
      (vec_access_dec (register_lookup pmpaddr_n rsf') 0) = false /\
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n rsf') 0)) 4)
      (uint (u_walk_pa w va)) (uint (to_bits 64 k)) = PMP_Match /\
    eq_vec (_get_Pmpcfg_ent_X
      (vec_access_dec (register_lookup pmpcfg_n rsf') 0)) ('b"1") = true /\
    matching_pma_region (register_lookup pma_regions rsf')
      (Physaddr (u_walk_pa w va)) k = Some region /\
    is_aligned_paddr (Physaddr (u_walk_pa w va)) k = true /\
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true /\
    exec (within_clint (Physaddr (u_walk_pa w va)) k) (u_state rsf' mm')
      = Some (false, u_state rsf' mm') /\
    exec (within_sig (Physaddr (u_walk_pa w va)) k) (u_state rsf' mm')
      = Some (false, u_state rsf' mm') /\
    register_lookup htif_tohost_base rsf' = None /\
    dev_addr (u_walk_pa w va) = false /\
    bytes_owned mm (u_walk_pa w va) (Z.to_N k) = true /\
    register_lookup cur_privilege rsf' = User.
Proof.
  intros Hk Hdvd Hk16 Huintk Hal Hl Lcp Hpins Hwf Hwf' Tr.
  pose proof Hpins as (Hhw & _ & Hpt & _).
  pose proof Hhw as (Hmisa & Hmseccfg & Hsenv & Hhtif & Hall & Help).
  pose proof Hpt as ((usatp & Hsatpok & Hsatp) & HA & Hord & HXp & HWp & HRp & Hcovp).
  (* the window is owned at the PRE map, and is RAM at the POST map *)
  assert (Hown : bytes_owned mm (u_walk_pa w va) (Z.to_N k) = true).
  { apply bytes_owned_of_dom. intros j Hj. apply elem_of_dom.
    exact (u_fetch_win_in P t mm k w va Hk Hdvd Hwf Hl Hal j ltac:(lia)). }
  assert (Hramj : forall j : nat, (j < Z.to_nat k)%nat ->
            addr_is_ram (pa_add (u_walk_pa w va) j)).
  { intros j Hj. pose proof Hwf' as (mdx & _ & _ & _ & _ & Hr & _).
    apply Hr. apply elem_of_dom.
    exact (u_fetch_win_in P t' mm' k w va Hk Hdvd Hwf' Hl Hal j Hj). }
  assert (Hram0 : addr_is_ram (u_walk_pa w va))
    by (rewrite <- (pa_add_0 (u_walk_pa w va)); apply Hramj; lia).
  assert (Hramk : addr_is_ram (pa_add (u_walk_pa w va) (Z.to_nat k - 1)))
    by (apply Hramj; lia).
  (* the ambient pins survive the TLB write *)
  assert (HA' : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n rsf') 0)) = TOR)
    by (rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA).
  assert (Hord' : zopz0zKzJ_u (zeros' 64)
      (vec_access_dec (register_lookup pmpaddr_n rsf') 0) = false)
    by (rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord).
  assert (HX' : eq_vec (_get_Pmpcfg_ent_X
      (vec_access_dec (register_lookup pmpcfg_n rsf') 0)) ('b"1") = true)
    by (rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HXp).
  assert (Hcovp' : (ram_base + ram_size
      <= uint (vec_access_dec (register_lookup pmpaddr_n rsf') 0) * 4)%Z)
    by (rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hcovp).
  assert (Hall' : pma_allows_all (register_lookup pma_regions rsf'))
    by (rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall).
  assert (Hhtif' : register_lookup htif_tohost_base rsf' = None)
    by (rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif).
  assert (Lcp' : register_lookup cur_privilege rsf' = User)
    by (rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Lcp).
  (* [Z.of_nat (Z.to_nat k - 1)] is the access's LAST byte offset.  Named,
     not an inline [ltac:(lia)]: nat subtraction is truncated, so lia needs
     [1 <= Z.to_nat k] spelled out and otherwise reports the useless
     "Cannot find witness". *)
  assert (Hk1 : (1 <= Z.to_nat k)%nat) by lia.
  assert (Hkk : Z.of_nat (Z.to_nat k - 1) = k - 1).
  { rewrite Nat2Z.inj_sub by exact Hk1. rewrite Z2Nat.id by lia. reflexivity. }
  destruct (pma_all_ram Hall' (u_walk_pa w va) k
              (pma_access_ram_at _ _ (Z.to_nat k - 1) Hkk Hram0 Hramk
                 (pma_width_le k 16 Hk Hk16 eq_refl)))
    as (region & Hpmam & Hexecp & _).
  exists region. split_and!.
  - exact HA'.
  - exact Hord'.
  - exact (ram_fetch_pmp (u_walk_pa w va) _ k (Z.to_nat k - 1) Hk Hk16
             Huintk ltac:(lia) Hram0 Hramk Hcovp').
  - exact HX'.
  - exact Hpmam.
  - exact (pa_aligned_div _ va k Hk Hdvd Hal).
  - exact Hexecp.
  - exact (within_clint_false (u_walk_pa w va) k (u_state rsf' mm')
             (addr_is_ram_not_in_clint _ Hram0) ltac:(lia)).
  - exact (within_sig_false (u_walk_pa w va) k (u_state rsf' mm')
             (addr_is_ram_not_in_sig _ Hram0) ltac:(lia)).
  - exact Hhtif'.
  - exact (addr_is_ram_not_dev _ Hram0).
  - exact Hown.
  - exact Lcp'.
Qed.
Lemma u_fetch_pure (P : uptd) (t : ptree) (mm : pamap) (rsf : regstate)
    (w va : mword 64) (mi : bool) :
  ud_um P !! svpn_of va = Some w ->
  uleaf_ok (InstructionFetch tt) w ->
  is_aligned_vaddr (Virtaddr va) 4 = true ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                        (Z.sub 39 1) 0)) = false ->
  post_fetch_cfg (u_state rsf mm) va mi ->
  u_exec_pins P t rsf ->
  u_mem_wf P t mm ->
  exists (iw : mword 32) (rsf' : regstate) (mm' : pamap) (t' : ptree),
    exec (fetch tt) (u_state rsf mm)
      = Some ((if isRVC (subrange_vec_dec (autocast (T := mword) iw : mword 32) 15 0)
               then F_RVC (subrange_vec_dec (autocast (T := mword) iw : mword 32) 15 0)
               else F_Base (autocast (T := mword) iw)), u_state rsf' mm') /\
    goodmb Du_r Du_w (fetch tt) (u_state rsf mm) mm = true /\
    (rsf' = rsf \/ exists tv, rsf' = register_set tlb tv rsf) /\
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf') /\
    u_mem_step P t t' mm mm'.
Proof.
  intros Hl Hleaf Hal Hcanon Hcfg Hpins Hwf.
  pose proof Hcfg as (Lpc & Lcp & Lms & Lmenv & _ & _).
  pose proof Lms as (Lsxl & _).
  pose proof Hpins as (Hhw & Hcfgp & Hpt & Htlbok).
  pose proof Hhw as (Hmisa & Hmseccfg & Hsenv & Hhtif & Hall & Help).
  pose proof Hpt as ((usatp & Hsatpok & Hsatp) & HA & Hord & HXp & HWp & HRp & Hcovp).
  (* THE WALK, once -- section 7a.  Everything below is the instruction READ
     at the state it landed on, and the [fetch] shell over the two. *)
  destruct (u_walk_fetch_pure P t mm rsf w va Hl Hleaf Hcanon Lcp Lsxl Lmenv
              Hpins Hwf)
    as (rsf' & mm' & t' & Htr & Htrg & Hfile & Htlbok' & Hstep).
  (* THE INSTRUCTION READ, at the state the walk landed on.  The four
     bytes are in the OWNED map at BOTH ends: at [mm'] with the values the
     machine reads, and at [mm] -- the map the certificate is stated over
     -- as ownership.  [u_mem_step] is what carries the first. *)
  assert (Hwf' : u_mem_wf P t' mm')
    by exact (u_mem_step_wf P t t' mm mm' Hwf Hstep).
  destruct (u_fetch_bytes P t' mm' w va Hwf' Hl Hal) as (iw & Hbytes).
  (* THE PHYSICAL GRANT -- section 7b, at width 4. *)
  destruct (u_fetch_read_ok P t t' mm mm' rsf rsf' 4 w va
              ltac:(lia) (Z.divide_factor_l 4 1024) ltac:(lia)
              ltac:(vm_compute; reflexivity) Hal Hl Lcp Hpins Hwf Hwf'
              (u_tlb_only_land rsf rsf' Hfile))
    as (region & HA' & Hord' & Hrange & HX' & Hpmam & Halp & Hexecp &
        Hclint & Hsigw & Hhtif' & Hdevp & Hown4 & Lcp').
  assert (Hmr : exec (mem_read (InstructionFetch tt) PBMT_PMA
                        (Physaddr (u_walk_pa w va)) 4 false false false)
                  (u_state rsf' mm') = Some (Ok iw, u_state rsf' mm'))
    by exact (exec_mem_read_fetch_4_U PBMT_PMA (u_walk_pa w va) region iw
                (u_state rsf' mm') HA' Hord' Hrange HX' Hpmam Halp Hexecp
                Hclint Hsigw
                (within_htif_false (u_walk_pa w va) 4 (u_state rsf' mm') Hhtif')
                Hdevp Hbytes Lcp').
  assert (Hmrg : goodmb Du_r Du_w (mem_read (InstructionFetch tt) PBMT_PMA
                          (Physaddr (u_walk_pa w va)) 4 false false false)
                   (u_state rsf' mm') mm = true)
    by exact (goodmb_mem_read_fetch_4_U Du_r Du_w PBMT_PMA (u_walk_pa w va)
                region iw (u_state rsf' mm') mm
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                HA' Hord' Hrange HX' Hpmam Halp Hexecp Hclint Hsigw Hhtif'
                Hdevp Hown4 Hbytes Lcp').
  (* ...and the fetch on top of the two *)
  exists iw, rsf', mm', t'. split_and!.
  - exact (exec_fetch_ok_4 (u_state rsf mm) (u_state rsf' mm') va
             (u_walk_pa w va) iw Lpc Hal Htr Hmr).
  - exact (goodmb_fetch_ok_4 Du_r Du_w (u_state rsf mm) (u_state rsf' mm') mm
             va (u_walk_pa w va) iw ltac:(vm_compute; reflexivity)
             Lpc Hal Htr Htrg Hmr Hmrg).
  - exact Hfile.
  - exact Htlbok'.
  - exact Hstep.
Qed.
