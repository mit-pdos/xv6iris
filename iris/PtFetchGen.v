(* PtFetchGen.v -- pa-GENERIC fetch compositors: the four S-mode fetch
   geometries of SmodeCore's [exec_fetch_*_S_gen], with the translated
   OUTPUT page an explicit [pa] instead of the kernel identity.  Used by
   the trampoline-page fetches (kernel and user tables both map the
   trampoline va to the kernel-text page). *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import SmodeCore.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

Lemma exec_fetch_F_Base_4_S_gen_pa
      (va pa : mword 64) (w : mword 32) (s s1 : mstate) (region : PMA_Region) :
  register_lookup PC s.(sregs) = va ->
  is_aligned_vaddr (Virtaddr va) 4 = true ->
  exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s1) ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr pa) 4 = Some region ->
  is_aligned_paddr (Physaddr pa) 4 = true ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
  exec (within_clint (Physaddr pa) 4) s1 = Some (false, s1) ->
  exec (within_sig (Physaddr pa) 4) s1 = Some (false, s1) ->
  exec (within_htif_readable (Physaddr pa) 4) s1 = Some (false, s1) ->
  dev_addr pa = false ->
  (forall j : nat, (N.of_nat j < 4)%N -> s1.(mem) !! (pa_add pa j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s1.(sregs) = Supervisor ->
  isRVC (subrange_vec_dec w 15 0) = false ->
  exec (fetch tt) s = Some (F_Base w, s1).
Proof.
  intros HpcPC Hvalign Htr iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHdev iHbytes iHpriv HnotRVC.
  destruct (align4_low_bits va Hvalign) as [Hbit0 Hbit1].
  assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
  { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
  assert (Hfb4 : exec (fetch_bytes va va 4) s = Some (@FetchBytes_Success 4 w, s1)).
  { unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
    assert (Htrstep1 : execR (Defs.bind0 (Defs.returnR (FetchBytes_Result 4) tt)
        (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
        = Some (inr (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)), s1)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite Htr. cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Htrstep1).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pa, PBMT_PMA) s1)).
    cbv iota beta.
    assert (Hmrdstep1 : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 4 false false false) : Defs.monadR (FetchBytes_Result 4) _ (result (mword (8 * 4)) (physaddr * ExceptionType))) s1 = Some (inr (Ok w), s1)).
    { rewrite execR_liftR. rewrite (exec_mem_read_fetch_4_S PBMT_PMA pa region w s1 iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHdev iHbytes iHpriv). cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hmrdstep1).
    cbv iota beta. rewrite autocast_mword_id.
    rewrite execR_returnR_fwd. cbn match. reflexivity. }
  unfold fetch.
  rewrite exec_catch_early_return.
  change (get_config_rvfi tt) with false. cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
  rewrite (execR_bind_Some _ _ _ false s).
  2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      unfold or_boolM.
      rewrite (execR_bind_Some _ _ _ false s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
      cbv iota beta.
      unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ false s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
      cbv iota beta. reflexivity. }
  cbv iota beta.
  rewrite (execR_bind_Some _ _ _ true s).
  2:{ unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ true s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign. apply execR_returnR_fwd. }
      cbv iota beta.
      rewrite execR_liftR. rewrite exec_currentlyEnabled_Ziccif. cbn match. reflexivity. }
  cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ Hfb4).
  cbv iota beta.
  match goal with
  | |- context [isRVC ?x] =>
      replace (isRVC x) with false by (symmetry; exact HnotRVC)
  end.
  cbv iota beta.
  rewrite execR_returnR_fwd. cbn match. reflexivity.
Qed.

Lemma exec_fetch_RVC_4_S_gen_pa
      (va pa : mword 64) (w : mword 32) (s s1 : mstate) (region : PMA_Region) :
  register_lookup PC s.(sregs) = va ->
  is_aligned_vaddr (Virtaddr va) 4 = true ->
  exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s1) ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr pa) 4 = Some region ->
  is_aligned_paddr (Physaddr pa) 4 = true ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
  exec (within_clint (Physaddr pa) 4) s1 = Some (false, s1) ->
  exec (within_sig (Physaddr pa) 4) s1 = Some (false, s1) ->
  exec (within_htif_readable (Physaddr pa) 4) s1 = Some (false, s1) ->
  dev_addr pa = false ->
  (forall j : nat, (N.of_nat j < 4)%N -> s1.(mem) !! (pa_add pa j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s1.(sregs) = Supervisor ->
  isRVC (subrange_vec_dec w 15 0) = true ->
  exec (fetch tt) s = Some (F_RVC (subrange_vec_dec w 15 0), s1).
Proof.
  intros HpcPC Hvalign Htr iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHdev iHbytes iHpriv HisRVC.
  destruct (align4_low_bits va Hvalign) as [Hbit0 Hbit1].
  assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
  { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
  assert (Hfb4 : exec (fetch_bytes va va 4) s = Some (@FetchBytes_Success 4 w, s1)).
  { unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
    assert (Htrstep2 : execR (Defs.bind0 (Defs.returnR (FetchBytes_Result 4) tt)
        (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
        = Some (inr (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)), s1)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite Htr. cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Htrstep2).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pa, PBMT_PMA) s1)).
    cbv iota beta.
    assert (Hmrdstep2 : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 4 false false false) : Defs.monadR (FetchBytes_Result 4) _ (result (mword (8 * 4)) (physaddr * ExceptionType))) s1 = Some (inr (Ok w), s1)).
    { rewrite execR_liftR. rewrite (exec_mem_read_fetch_4_S PBMT_PMA pa region w s1 iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHdev iHbytes iHpriv). cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hmrdstep2).
    cbv iota beta. rewrite autocast_mword_id.
    rewrite execR_returnR_fwd. cbn match. reflexivity. }
  unfold fetch.
  rewrite exec_catch_early_return.
  change (get_config_rvfi tt) with false. cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
  rewrite (execR_bind_Some _ _ _ false s).
  2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      unfold or_boolM.
      rewrite (execR_bind_Some _ _ _ false s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
      cbv iota beta.
      unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ false s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
      cbv iota beta. reflexivity. }
  cbv iota beta.
  rewrite (execR_bind_Some _ _ _ true s).
  2:{ unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ true s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign. apply execR_returnR_fwd. }
      cbv iota beta.
      rewrite execR_liftR. rewrite exec_currentlyEnabled_Ziccif. cbn match. reflexivity. }
  cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ Hfb4).
  cbv iota beta.
  match goal with
  | |- context [isRVC ?x] =>
      replace (isRVC x) with true by (symmetry; exact HisRVC)
  end.
  cbv iota beta.
  rewrite execR_returnR_fwd. cbn match. reflexivity.
Qed.

Lemma exec_fetch_RVC_2_S_gen_pa
      (va pa : mword 64) (h : mword 16) (s s1 : mstate) (region : PMA_Region) :
  register_lookup PC s.(sregs) = va ->
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  neq_vec (access_vec_dec va 0) ('b"0") = false ->
  neq_vec (access_vec_dec va 1) ('b"0") = true ->
  is_aligned_vaddr (Virtaddr va) 4 = false ->
  exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s1) ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 2)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr pa) 2 = Some region ->
  is_aligned_paddr (Physaddr pa) 2 = true ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
  exec (within_clint (Physaddr pa) 2) s1 = Some (false, s1) ->
  exec (within_sig (Physaddr pa) 2) s1 = Some (false, s1) ->
  exec (within_htif_readable (Physaddr pa) 2) s1 = Some (false, s1) ->
  dev_addr pa = false ->
  (forall j : nat, (N.of_nat j < 2)%N -> s1.(mem) !! (pa_add pa j) = Some (nth_byte h j)) ->
  register_lookup cur_privilege s1.(sregs) = Supervisor ->
  isRVC h = true ->
  exec (fetch tt) s = Some (F_RVC h, s1).
Proof.
  intros HpcPC HmisaC Hbit0 Hbit1 Hvalign4 Htr iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHdev iHbytes iHpriv HisRVC.
  assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
  { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
  assert (Hfb2 : exec (fetch_bytes va va 2) s = Some (@FetchBytes_Success 2 h, s1)).
  { unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
    assert (Htrstep3 : execR (Defs.bind0 (Defs.returnR (FetchBytes_Result 2) tt)
        (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
        = Some (inr (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)), s1)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite Htr. cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Htrstep3).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pa, PBMT_PMA) s1)).
    cbv iota beta.
    assert (Hmrdstep3 : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 2 false false false) : Defs.monadR (FetchBytes_Result 2) _ (result (mword (8 * 2)) (physaddr * ExceptionType))) s1 = Some (inr (Ok h), s1)).
    { rewrite execR_liftR. rewrite (exec_mem_read_fetch_2_S PBMT_PMA pa region h s1 iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHdev iHbytes iHpriv). cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hmrdstep3).
    cbv iota beta. rewrite autocast_mword_id_16.
    rewrite execR_returnR_fwd. cbn match. reflexivity. }
  unfold fetch.
  rewrite exec_catch_early_return.
  change (get_config_rvfi tt) with false. cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
  rewrite (execR_bind_Some _ _ _ false s).
  2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      unfold or_boolM.
      rewrite (execR_bind_Some _ _ _ false s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
      cbv iota beta.
      unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ true s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
      cbv iota beta.
      rewrite (execR_bind_Some _ _ _ true s).
      2:{ rewrite execR_liftR. rewrite (exec_currentlyEnabled_Zca s HmisaC). cbn match.
          apply execR_returnR_fwd. }
      cbv iota beta. reflexivity. }
  cbv iota beta.
  rewrite (execR_bind_Some _ _ _ false s).
  2:{ unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ false s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign4. apply execR_returnR_fwd. }
      cbv iota beta. reflexivity. }
  cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ Hfb2).
  cbv iota beta.
  match goal with
  | |- context [isRVC ?x] =>
      replace (isRVC x) with true by (symmetry; exact HisRVC)
  end.
  cbv iota beta.
  rewrite execR_returnR_fwd. cbn match. reflexivity.
Qed.

Lemma exec_fetch_F_Base_2_S_gen_pa
      (va pa : mword 64) (w : mword 32) (s s1 s2 : mstate) (regl regh : PMA_Region) :
  let ilo : mword 16 := subrange_vec_dec w 15 0 in
  let ihi : mword 16 := subrange_vec_dec w 31 16 in
  let vah : mword 64 := add_vec_int va 2 in
  let pah : mword 64 := add_vec_int pa 2 in
  register_lookup PC s.(sregs) = va ->
  register_lookup PC s1.(sregs) = va ->
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  neq_vec (access_vec_dec va 0) ('b"0") = false ->
  neq_vec (access_vec_dec va 1) ('b"0") = true ->
  is_aligned_vaddr (Virtaddr va) 4 = false ->
  (* the two abstract halfword translations, threading s -> s1 -> s2 *)
  exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s1) ->
  exec (translateAddr (Virtaddr vah) (InstructionFetch tt)) s1
    = Some (Ok (Physaddr pah, PBMT_PMA, init_ext_ptw), s2) ->
  (* low halfword mem-read facts, at s1 *)
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 2)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr pa) 2 = Some regl ->
  is_aligned_paddr (Physaddr pa) 2 = true ->
  (override_PMA (PMA_Region_attributes regl) PBMT_PMA).(PMA_executable) = true ->
  exec (within_clint (Physaddr pa) 2) s1 = Some (false, s1) ->
  exec (within_sig (Physaddr pa) 2) s1 = Some (false, s1) ->
  exec (within_htif_readable (Physaddr pa) 2) s1 = Some (false, s1) ->
  dev_addr pa = false ->
  (forall j : nat, (N.of_nat j < 2)%N -> s1.(mem) !! (pa_add pa j) = Some (nth_byte ilo j)) ->
  register_lookup cur_privilege s1.(sregs) = Supervisor ->
  (* high halfword mem-read facts, at s2 *)
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s2.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s2.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s2.(sregs)) 0)) 4)
    (uint pah) (uint (to_bits 64 2)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s2.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s2.(sregs)) (Physaddr pah) 2 = Some regh ->
  is_aligned_paddr (Physaddr pah) 2 = true ->
  (override_PMA (PMA_Region_attributes regh) PBMT_PMA).(PMA_executable) = true ->
  exec (within_clint (Physaddr pah) 2) s2 = Some (false, s2) ->
  exec (within_sig (Physaddr pah) 2) s2 = Some (false, s2) ->
  exec (within_htif_readable (Physaddr pah) 2) s2 = Some (false, s2) ->
  dev_addr pah = false ->
  (forall j : nat, (N.of_nat j < 2)%N -> s2.(mem) !! (pa_add pah j) = Some (nth_byte ihi j)) ->
  register_lookup cur_privilege s2.(sregs) = Supervisor ->
  isRVC ilo = false ->
  concat_vec ihi ilo = w ->
  exec (fetch tt) s = Some (F_Base w, s2).
Proof.
  intros ilo ihi vah pah HpcPC HpcPC1 HmisaC Hbit0 Hbit1 Hvalign4 Htrl Htrh
         iHAL iHordL iHrangeL iHXL iHmatchL iHalignL iHexecL iHcL iHsigL iHhL iHdevL iHbytesL iHprivL
         iHAH iHordH iHrangeH iHXH iHmatchH iHalignH iHexecH iHcH iHsigH iHhH iHdevH iHbytesH iHprivH
         HnotRVC Hconcat.
  assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
  { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
  assert (HrdPC1 : exec (Defs.read_reg PC) s1 = Some (va, s1)).
  { rewrite (exec_read_reg PC s1). rewrite HpcPC1. reflexivity. }
  (* first halfword: fetch_bytes at [s] that lands in [s1] *)
  assert (Hfb2l : exec (fetch_bytes va va 2) s = Some (@FetchBytes_Success 2 ilo, s1)).
  { unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
    assert (Htrstep4 : execR (Defs.bind0 (Defs.returnR (FetchBytes_Result 2) tt)
        (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
        = Some (inr (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)), s1)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite Htrl. cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Htrstep4).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pa, PBMT_PMA) s1)).
    cbv iota beta.
    assert (Hmrdstep4 : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 2 false false false) : Defs.monadR (FetchBytes_Result 2) _ (result (mword (8 * 2)) (physaddr * ExceptionType))) s1 = Some (inr (Ok ilo), s1)).
    { rewrite execR_liftR. rewrite (exec_mem_read_fetch_2_S PBMT_PMA pa regl ilo s1 iHAL iHordL iHrangeL iHXL iHmatchL iHalignL iHexecL iHcL iHsigL iHhL iHdevL iHbytesL iHprivL). cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hmrdstep4).
    cbv iota beta. rewrite autocast_mword_id_16.
    rewrite execR_returnR_fwd. cbn match. reflexivity. }
  (* second halfword: fetch_bytes at [s1] that lands in [s2] *)
  assert (Hfb2h : exec (fetch_bytes va vah 2) s1 = Some (@FetchBytes_Success 2 ihi, s2)).
  { unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc va vah) with (@None unit). cbv iota beta.
    assert (Htrstep5 : execR (Defs.bind0 (Defs.returnR (FetchBytes_Result 2) tt)
        (Defs.liftR (translateAddr (Virtaddr vah) (InstructionFetch tt)))) s1
        = Some (inr (Ok (Physaddr pah, PBMT_PMA, init_ext_ptw)), s2)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s1)).
      rewrite execR_liftR. rewrite Htrh. cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Htrstep5).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pah, PBMT_PMA) s2)).
    cbv iota beta.
    assert (Hmrdstep5 : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pah) 2 false false false) : Defs.monadR (FetchBytes_Result 2) _ (result (mword (8 * 2)) (physaddr * ExceptionType))) s2 = Some (inr (Ok ihi), s2)).
    { rewrite execR_liftR. rewrite (exec_mem_read_fetch_2_S PBMT_PMA pah regh ihi s2 iHAH iHordH iHrangeH iHXH iHmatchH iHalignH iHexecH iHcH iHsigH iHhH iHdevH iHbytesH iHprivH). cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hmrdstep5).
    cbv iota beta. rewrite autocast_mword_id_16.
    rewrite execR_returnR_fwd. cbn match. reflexivity. }
  (* assemble the outer fetch: PC read at s pre-checks + low read; PC read at s1
     before the high read *)
  unfold fetch.
  rewrite exec_catch_early_return.
  change (get_config_rvfi tt) with false. cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
  rewrite (execR_bind_Some _ _ _ false s).
  2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      unfold or_boolM.
      rewrite (execR_bind_Some _ _ _ false s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
      cbv iota beta.
      unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ true s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
      cbv iota beta.
      rewrite (execR_bind_Some _ _ _ true s).
      2:{ rewrite execR_liftR. rewrite (exec_currentlyEnabled_Zca s HmisaC). cbn match.
          apply execR_returnR_fwd. }
      cbv iota beta. reflexivity. }
  cbv iota beta.
  rewrite (execR_bind_Some _ _ _ false s).
  2:{ unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ false s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign4. apply execR_returnR_fwd. }
      cbv iota beta. reflexivity. }
  cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ Hfb2l).
  cbv iota beta.
  match goal with
  | |- context [isRVC ?x] =>
      replace (isRVC x) with false by (symmetry; exact HnotRVC)
  end.
  cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC1).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC1).
  rewrite (execR_liftR_seq _ _ _ _ _ Hfb2h).
  cbv iota beta. rewrite execR_returnR_fwd. cbn match.
  do 3 f_equal; first [ exact Hconcat | reflexivity ].
Qed.
