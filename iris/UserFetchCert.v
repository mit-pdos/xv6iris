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
(* and the read need; section 4 [u_fetch_pure].                            *)
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
Require Import UptTree UserPtTree UserBits UserMem UserFetch.
Require Import UserBytes PtWalkCert.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 1. THE 4-BYTE FETCH READ, certified.                                   *)
(*                                                                        *)
(* [UserMem.exec_checked_mem_read_ram_4_U] / [exec_mem_read_fetch_4_U]'s   *)
(* twins.  Same shape as [PtWalkCert] section 1e's PTE read, one width     *)
(* down and at the fetch access type: the PMA arm is [PMA_executable] and  *)
(* the PMP grant is [pmpCheck ... (InstructionFetch tt) User].             *)
(* ===================================================================== *)

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
              (InstructionFetch tt) (Physaddr addr) 4 false s mm
              (goodmb_returnm Dr Dw false s mm)
              (exec_is_mag_applicable_fetch 4 s) Halign)
           (exec_mag_pma_check_aligned (override_PMA rattr pbmt)
              (InstructionFetch tt) (Physaddr addr) 4 false s
              (exec_is_mag_applicable_fetch 4 s) Halign).
  cbn match beta. reflexivity.
Qed.

Section FetchRead.
  Context (Dr Dw : register -> bool).
  Context (pbmt : page_based_mem_type) (addr : mword 64) (region : PMA_Region).
  Context (w : bv 32) (s : mstate) (mm : pamap).

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
    (uint addr) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HX : eq_vec (_get_Pmpcfg_ent_X
    (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs))
    (Physaddr addr) 4 = Some region.
  Hypothesis Halign : is_aligned_paddr (Physaddr addr) 4 = true.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hhtif : register_lookup htif_tohost_base s.(sregs) = None.
  Hypothesis Hdev : dev_addr addr = false.
  Hypothesis Hown : bytes_owned mm addr 4 = true.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N ->
    s.(mem) !! (pa_add addr j) = Some (nth_byte w j).

  Let Hh : exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s)
    := within_htif_false addr 4 s Hhtif.

  Lemma fr_exec_cp :
    exec (check_pma_with_pmp_priority (InstructionFetch tt) pbmt User
            (Physaddr addr) 4 false) s = Some (Ok pma_ok_aligned, s).
  Proof.
    unfold check_pma_with_pmp_priority.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_pmaCheck_ram addr pbmt region s Hmatch Halign Hexec)).
    cbn match. apply exec_returnM.
  Qed.

  Lemma fr_good_cp :
    goodmb Dr Dw (check_pma_with_pmp_priority (InstructionFetch tt) pbmt User
                    (Physaddr addr) 4 false) s mm = true.
  Proof.
    exact (goodmb_check_pma_with_pmp_priority Dr Dw _ _ User _ _ false _ s mm
             (goodmb_pmaCheck_ram_fetch Dr Dw addr pbmt region false s mm
                HDp Hmatch Halign Hexec)
             (exec_pmaCheck_ram addr pbmt region s Hmatch Halign Hexec)).
  Qed.

  Lemma fr_exec_mmio :
    exec (within_mmio_readable (Physaddr addr) 4) s = Some (false, s).
  Proof.
    unfold within_mmio_readable. cbn [get_config_rvfi].
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity.
  Qed.

  Lemma goodmb_checked_mem_read_ram_4_U :
    goodmb Dr Dw (checked_mem_read (InstructionFetch tt) pbmt User
             (Physaddr addr) 4 false false false false) s mm = true.
  Proof.
    assert (Hrkf : exec (read_kind_of_flags false false false) s
                   = Some (rv64d_types.Read_plain, s))
      by (unfold read_kind_of_flags; apply exec_returnM).
    unfold checked_mem_read. apply goodmb_cer.
    erewrite gm_liftR_seq; [ | apply fr_good_cp | apply fr_exec_cp ].
    cbn beta. cbn match.
    erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
    cbn match beta.
    rewrite pma_ok_aligned_splittable; rewrite pma_ok_aligned_granule.
    gmm_lift (goodmb_split_misaligned_unsplit Dr Dw addr 4 0 s mm)
             (exec_split_misaligned_unsplit addr 4 0 s). cbn beta.
    cbn match beta. rewrite misaligned_order_1. cbn match zeta beta.
    gmm_lift (goodmb_returnm Dr Dw (E := exception) rv64d_types.Read_plain s mm) Hrkf.
    cbn beta.
    match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?b) _] =>
      assert (Hu : execR (Defs.untilMT vs m0 c b) s = Some (inr (w, true, 0), s));
      [ | assert (Hug : goodmb Dr Dw (Defs.untilMT vs m0 c b) s mm = true) ] end.
    { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
      change (bits_of_physaddr (Physaddr addr)) with addr.
      assert (Havi : add_vec_int addr (0 * 4) = addr)
        by (change (0 * 4)%Z with 0%Z; apply avi0).
      rewrite Havi.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_pmpCheck_user_grant addr 4 s HA Hord Hrange HX)). cbn beta.
      cbn match.
      match goal with |- context[Defs.bind (Defs.bind0 ?a ?b) _] =>
        assert (Hseq : execR (Defs.bind0 a b) s = Some (inr false, s)) end.
      { rewrite execR_bind0. rewrite execR_returnR. cbn match.
        rewrite execR_liftR. rewrite fr_exec_mmio. reflexivity. }
      rewrite (execR_bind_Some _ _ _ _ _ Hseq). cbn beta. cbn match.
      match goal with
        |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk ?pa ?wd ?mt)) ?k1) _] =>
        assert (Hrd : execR (Defs.bind (Defs.liftR (read_ram rk pa wd mt)) k1) s
                      = Some (inr w, s)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_ram_plain_4 addr w s Hdev Hbytes)).
        cbn beta match. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hrd). cbn beta zeta.
      rewrite autocast_id. rewrite usvd_zeros_full_32. apply execR_returnR_fwd. }
    { eapply gm_untilMT_1; [ reflexivity | | | | ].
      - gmm_liftT ltac:(apply goodmb_assert_exp'_true)
                  ltac:(apply exec_assert_exp'_true). cbn beta.
        change (bits_of_physaddr (Physaddr addr)) with addr.
        assert (Havi : add_vec_int addr (0 * 4) = addr)
          by (change (0 * 4)%Z with 0%Z; apply avi0).
        rewrite Havi.
        gmm_lift (goodmb_pmpCheck_grant Dr Dw addr 4 (InstructionFetch tt) User s mm
                    HDc HDa HA Hord Hrange
                    ltac:(unfold pmpCheckRWX; cbn match; rewrite HX; apply exec_returnm)
                    ltac:(unfold pmpCheckRWX; cbn match; apply goodmb_returnm))
                 (exec_pmpCheck_user_grant addr 4 s HA Hord Hrange HX).
        cbn beta. cbn match.
        match goal with |- context[Defs.bind (Defs.bind0 ?a ?b) _] =>
          assert (Hseqg : goodmb Dr Dw (Defs.bind0 a b) s mm = true);
          [ | assert (Hseq : execR (Defs.bind0 a b) s = Some (inr false, s)) ] end.
        { erewrite gm_bind0R; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
          apply goodmb_liftR.
          exact (goodmb_within_mmio_readable Dr Dw addr 4 s mm HDh Hhtif Hc Hsig). }
        { rewrite execR_bind0. rewrite execR_returnR. cbn match.
          rewrite execR_liftR. rewrite fr_exec_mmio. reflexivity. }
        erewrite (gm_bindR Dr Dw _ _ s s mm false Hseqg Hseq). cbn beta. cbn match.
        match goal with
          |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk ?pa ?wd ?mt)) ?k1) _] =>
          assert (Hrdg : goodmb Dr Dw
                    (Defs.bind (Defs.liftR (read_ram rk pa wd mt)) k1) s mm = true);
          [ | assert (Hrd : execR (Defs.bind (Defs.liftR (read_ram rk pa wd mt)) k1) s
                            = Some (inr w, s)) ] end.
        { erewrite gm_liftR_seq;
            [ | exact (goodmb_read_ram Dr Dw rv64d_types.Read_plain 4 addr false s mm
                         eq_refl Hdev Hown
                         (read_bytes_ne s.(mem) addr (Z.to_N 4) w Hbytes))
              | exact (exec_read_ram_plain_4 addr w s Hdev Hbytes) ].
          cbn beta match. apply goodmb_returnm. }
        { rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_ram_plain_4 addr w s Hdev Hbytes)).
          cbn beta match. apply execR_returnR_fwd. }
        erewrite (gm_bindR Dr Dw _ _ s s mm w Hrdg Hrd). cbn beta zeta.
        rewrite autocast_id. rewrite usvd_zeros_full_32. apply goodmb_returnm.
      - rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
        change (bits_of_physaddr (Physaddr addr)) with addr.
        assert (Havi : add_vec_int addr (0 * 4) = addr)
          by (change (0 * 4)%Z with 0%Z; apply avi0).
        rewrite Havi.
        rewrite (execR_liftR_seq _ _ _ _ _
                   (exec_pmpCheck_user_grant addr 4 s HA Hord Hrange HX)). cbn beta.
        cbn match.
        match goal with |- context[Defs.bind (Defs.bind0 ?a ?b) _] =>
          assert (Hseq : execR (Defs.bind0 a b) s = Some (inr false, s)) end.
        { rewrite execR_bind0. rewrite execR_returnR. cbn match.
          rewrite execR_liftR. rewrite fr_exec_mmio. reflexivity. }
        rewrite (execR_bind_Some _ _ _ _ _ Hseq). cbn beta. cbn match.
        match goal with
          |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk ?pa ?wd ?mt)) ?k1) _] =>
          assert (Hrd : execR (Defs.bind (Defs.liftR (read_ram rk pa wd mt)) k1) s
                        = Some (inr w, s)) end.
        { rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_ram_plain_4 addr w s Hdev Hbytes)).
          cbn beta match. apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hrd). cbn beta zeta.
        rewrite autocast_id. rewrite usvd_zeros_full_32. apply execR_returnR_fwd.
      - reflexivity.
      - apply execR_returnR_fwd. }
    erewrite (gm_bindR Dr Dw _ _ s s mm (w, true, 0) Hug Hu). cbn beta zeta.
    rewrite autocast_id. apply goodmb_returnm.
  Qed.

  Lemma goodmb_mem_read_fetch_4_U :
    register_lookup cur_privilege s.(sregs) = User ->
    goodmb Dr Dw (mem_read (InstructionFetch tt) pbmt (Physaddr addr) 4
             false false false) s mm = true.
  Proof.
    intros Hpriv.
    assert (Hchk : exec (checked_mem_read (InstructionFetch tt) pbmt User
                     (Physaddr addr) 4 false false false false) s
                   = Some (Ok (w, default_meta), s))
      by (apply exec_checked_mem_read_ram_4_U with (region := region);
          first [ exact HA | exact Hord | exact Hrange | exact HX | exact Hmatch
                | exact Halign | exact Hexec | exact Hc | exact Hsig | exact Hh
                | exact Hdev | exact Hbytes ]).
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
                     (Physaddr addr) 4 false false false false) s mm = true).
    { unfold mem_read_priv_meta. cbn [orb andb].
      gmm_peel goodmb_checked_mem_read_ram_4_U Hchk. cbn match.
      unfold mem_read_callback. apply goodmb_returnm. }
    assert (Hmr : exec (mem_read_priv_meta (InstructionFetch tt) pbmt User
                    (Physaddr addr) 4 false false false false) s
                  = Some (Ok (w, default_meta), s)).
    { unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_bind_Some _ _ _ _ _ Hchk). cbn match.
      unfold mem_read_callback. apply exec_returnM. }
    gmm_peel Hmrg Hmr. cbn [MemoryOpResult_drop_meta]. apply goodmb_returnm.
  Qed.

End FetchRead.

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
  u_mem_wf P t mm -> ptree_maps t vpn p2 p1 p0 -> x ∈ ud_data P ->
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
  pose proof Hwf as (md & Hdisj & Hdj & Hmm & Hdm & Hram & Hcov & _).
  set (pa := u_walk_pa w va).
  assert (Hin : forall j : nat, (j < 4)%nat -> is_Some (mm !! pa_add pa j)).
  { intros j Hj.
    assert (Hd : pa_add pa j ∈ ud_data P).
    { unfold pa. rewrite (u_walk_pa_window w va j Hal Hj).
      exact (Hcov (svpn_of va) w (add_vec_int va (Z.of_nat j)) Hl). }
    destruct (proj1 (Hdm _) Hd) as [bd Hbd].
    exists bd. rewrite Hmm.
    destruct (ptree_bytes 2 t !! pa_add pa j) as [c|] eqn:Ht.
    - exfalso.
      exact (proj1 (map_disjoint_spec (ptree_bytes 2 t) md) Hdj _ c bd Ht Hbd).
    - by rewrite (lookup_union_r _ md _ Ht). }
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
