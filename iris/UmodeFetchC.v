(* UmodeFetchC.v -- User-mode COMPRESSED (RVC) instruction fetch through
   the Sv39 TLB-hit path.

   The two F_RVC flavours of the fetch, mirroring UmodeFetch's 4-byte
   F_Base tower:
     - [exec_fetch_F_RVC_4_U_gen]: pc 4-aligned.  The Ziccif branch
       fetches a full 4-byte window and F_RVC is the LOW HALFWORD --
       the code map must still cover pa..pa+3.
     - [exec_fetch_F_RVC_2_U_gen]: pc == 2 (mod 4).  The alignment-fault
       check reads Zca (enabled: misa.C = 1), the Ziccif branch is
       skipped, and a single 2-byte fetch_bytes runs through the same
       translate-hit chain.
   Plus the width-2 U-mode read stack they need
   ([exec_checked_mem_read_ram_2_U], [exec_mem_read_fetch_2_U]) -- clones
   of UmodeFetch's width-4 stack over RiscvFetchExec's width-2 PMA/RAM
   primitives.                                                            *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import UmodeFetch.
Require Import WpGpr.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The width-2 U-mode read stack.                                      *)
(* ===================================================================== *)

Lemma exec_checked_mem_read_ram_2_U (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 16) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 2)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2 = Some region ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (within_clint (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 2) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 2)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (InstructionFetch tt) pbmt User (Physaddr addr) 2 false false false false)
       s = Some (Ok (w, default_meta), s).
Proof.
  intros HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hdev Hbytes.
  unfold checked_mem_read.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmpCheck_user_grant addr 2 s HA Hord Hrange HX)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_2 addr pbmt region s Hmatch Halign Hexec)).
      cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_readable (Physaddr addr) 2) s = Some (false, s))).
  2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (read_kind_of_flags _ _ _) s = Some (rv64d_types.Read_plain, s))).
  2:{ unfold read_kind_of_flags. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_plain_2 addr w s Hdev Hbytes)).
  apply exec_returnM.
Qed.

Lemma exec_mem_read_fetch_2_U (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 16) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 2)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2 = Some region ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (within_clint (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 2) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 2)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (mem_read (InstructionFetch tt) pbmt (Physaddr addr) 2 false false false)
       s = Some (Ok w, s).
Proof.
  intros HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hdev Hbytes Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_fetch _ _ s)).
  rewrite Hpriv.
  unfold mem_read_priv.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (mem_read_priv_meta _ _ _ _ 2 _ _ _ _) s = Some (Ok (w, default_meta), s))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (checked_mem_read _ _ _ _ 2 _ _ _ _) s = Some (Ok (w, default_meta), s))).
      2:{ cbn match. apply exec_checked_mem_read_ram_2_U with (region := region); assumption. }
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

(* ===================================================================== *)
(* §1b The U-mode 2-aligned (pc == 2 mod 4) 32-bit F_Base split fetch.     *)
(*   The high half can fault alone (reported at va+2); each halfword        *)
(*   translates INDEPENDENTLY (s -> s1 -> s2).  Clone of the S-mode         *)
(*   [exec_fetch_F_Base_2_S_gen] (SmodeCore.v) via the S->U copy-generalize:*)
(*   the two physical addresses [pal]/[pah] are ABSTRACT (user mappings are *)
(*   not the identity) and privilege is [User].                            *)
(* ===================================================================== *)

Lemma exec_fetch_F_Base_2_U_gen
      (va pal pah : mword 64) (w : mword 32) (s s1 s2 : mstate) (regl regh : PMA_Region) :
  let ilo : mword 16 := subrange_vec_dec w 15 0 in
  let ihi : mword 16 := subrange_vec_dec w 31 16 in
  let vah : mword 64 := add_vec_int va 2 in
  register_lookup PC s.(sregs) = va ->
  register_lookup PC s1.(sregs) = va ->
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  neq_vec (access_vec_dec va 0) ('b"0") = false ->
  neq_vec (access_vec_dec va 1) ('b"0") = true ->
  is_aligned_vaddr (Virtaddr va) 4 = false ->
  (* the two abstract halfword translations, threading s -> s1 -> s2 *)
  exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Ok (Physaddr pal, PBMT_PMA, init_ext_ptw), s1) ->
  exec (translateAddr (Virtaddr vah) (InstructionFetch tt)) s1
    = Some (Ok (Physaddr pah, PBMT_PMA, init_ext_ptw), s2) ->
  (* low halfword mem-read facts, at s1 (physical pal) *)
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
    (uint pal) (uint (to_bits 64 2)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr pal) 2 = Some regl ->
  is_aligned_paddr (Physaddr pal) 2 = true ->
  (override_PMA (PMA_Region_attributes regl) PBMT_PMA).(PMA_executable) = true ->
  exec (within_clint (Physaddr pal) 2) s1 = Some (false, s1) ->
  exec (within_sig (Physaddr pal) 2) s1 = Some (false, s1) ->
  exec (within_htif_readable (Physaddr pal) 2) s1 = Some (false, s1) ->
  dev_addr pal = false ->
  (forall j : nat, (N.of_nat j < 2)%N -> s1.(mem) !! (pa_add pal j) = Some (nth_byte ilo j)) ->
  register_lookup cur_privilege s1.(sregs) = User ->
  (* high halfword mem-read facts, at s2 (physical pah) *)
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
  register_lookup cur_privilege s2.(sregs) = User ->
  isRVC ilo = false ->
  concat_vec ihi ilo = w ->
  exec (fetch tt) s = Some (F_Base w, s2).
Proof.
  intros ilo ihi vah HpcPC HpcPC1 HmisaC Hbit0 Hbit1 Hvalign4 Htrl Htrh
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
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.bind0 (Defs.returnR _ tt)
              (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
           = Some (inr (Ok (Physaddr pal, PBMT_PMA, init_ext_ptw)), s1))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite execR_liftR. rewrite Htrl. cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pal, PBMT_PMA) s1)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pal) 2 false false false)) s1
           = Some (inr (Ok ilo), s1))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch_2_U PBMT_PMA pal regl ilo s1
                   iHAL iHordL iHrangeL iHXL iHmatchL iHalignL iHexecL iHcL iHsigL iHhL iHdevL iHbytesL iHprivL).
        cbn match. reflexivity. }
    cbv iota beta. rewrite autocast_mword_id_16.
    rewrite execR_returnR_fwd. cbn match. reflexivity. }
  (* second halfword: fetch_bytes at [s1] that lands in [s2] *)
  assert (Hfb2h : exec (fetch_bytes va vah 2) s1 = Some (@FetchBytes_Success 2 ihi, s2)).
  { unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc va vah) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.bind0 (Defs.returnR _ tt)
              (Defs.liftR (translateAddr (Virtaddr vah) (InstructionFetch tt)))) s1
           = Some (inr (Ok (Physaddr pah, PBMT_PMA, init_ext_ptw)), s2))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s1)).
        rewrite execR_liftR. rewrite Htrh. cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pah, PBMT_PMA) s2)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pah) 2 false false false)) s2
           = Some (inr (Ok ihi), s2))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch_2_U PBMT_PMA pah regh ihi s2
                   iHAH iHordH iHrangeH iHXH iHmatchH iHalignH iHexecH iHcH iHsigH iHhH iHdevH iHbytesH iHprivH).
        cbn match. reflexivity. }
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
  cbv iota beta. rewrite HnotRVC. cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC1).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC1).
  rewrite (execR_liftR_seq _ _ _ _ _ Hfb2h).
  cbv iota beta. rewrite execR_returnR_fwd. cbn match.
  rewrite Hconcat. reflexivity.
Qed.

(* ===================================================================== *)
(* §1c The U-mode 2-aligned (pc == 2 mod 4) 32-bit F_Base fetch whose      *)
(*   HIGH halfword FAULTS.  The low halfword at [va] translates + reads OK  *)
(*   (state-preserving hit, s -> s), but the high halfword at [va+2] fails  *)
(*   its INDEPENDENT translate (unmapped / no-perm), so [fetch_bytes] on    *)
(*   the second granule short-circuits to [FetchBytes_Exception e] and the  *)
(*   outer [fetch] reports [F_Error (e, va+2)] -- the fault is credited to   *)
(*   the HIGH granule (PC + 2), model line rv64d.v ~41523.  Sibling of the  *)
(*   success twin [exec_fetch_F_Base_2_U_gen]: the low-half block is copied  *)
(*   verbatim, the high-half success is replaced by a state-preserving      *)
(*   translate FAULT (mirroring [exec_fetch_u_pagefault_4]).                *)
(* ===================================================================== *)

Lemma exec_fetch_F_Base_2_U_highfault_gen
      (va pal : mword 64) (ilo : mword 16) (e : ExceptionType)
      (s s1 : mstate) (regl : PMA_Region) :
  let vah : mword 64 := add_vec_int va 2 in
  register_lookup PC s.(sregs) = va ->
  register_lookup PC s1.(sregs) = va ->
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  neq_vec (access_vec_dec va 0) ('b"0") = false ->
  neq_vec (access_vec_dec va 1) ('b"0") = true ->
  is_aligned_vaddr (Virtaddr va) 4 = false ->
  (* the low halfword translate OK (s -> s1) *)
  exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Ok (Physaddr pal, PBMT_PMA, init_ext_ptw), s1) ->
  (* low halfword mem-read facts, at s1 (physical pal) *)
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
    (uint pal) (uint (to_bits 64 2)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr pal) 2 = Some regl ->
  is_aligned_paddr (Physaddr pal) 2 = true ->
  (override_PMA (PMA_Region_attributes regl) PBMT_PMA).(PMA_executable) = true ->
  exec (within_clint (Physaddr pal) 2) s1 = Some (false, s1) ->
  exec (within_sig (Physaddr pal) 2) s1 = Some (false, s1) ->
  exec (within_htif_readable (Physaddr pal) 2) s1 = Some (false, s1) ->
  dev_addr pal = false ->
  (forall j : nat, (N.of_nat j < 2)%N -> s1.(mem) !! (pa_add pal j) = Some (nth_byte ilo j)) ->
  register_lookup cur_privilege s1.(sregs) = User ->
  (* the high halfword translate FAULTS at s1 (state-preserving) *)
  exec (translateAddr (Virtaddr vah) (InstructionFetch tt)) s1
    = Some (Err (e, tt), s1) ->
  isRVC ilo = false ->
  exec (fetch tt) s = Some (F_Error (e, vah), s1).
Proof.
  intros vah HpcPC HpcPC1 HmisaC Hbit0 Hbit1 Hvalign4 Htrl
         iHAL iHordL iHrangeL iHXL iHmatchL iHalignL iHexecL iHcL iHsigL iHhL iHdevL iHbytesL iHprivL
         Htrh_fault HnotRVC.
  assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
  { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
  assert (HrdPC1 : exec (Defs.read_reg PC) s1 = Some (va, s1)).
  { rewrite (exec_read_reg PC s1). rewrite HpcPC1. reflexivity. }
  (* first halfword: fetch_bytes at [s] that lands in [s1] -- copied verbatim
     from the success twin *)
  assert (Hfb2l : exec (fetch_bytes va va 2) s = Some (@FetchBytes_Success 2 ilo, s1)).
  { unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.bind0 (Defs.returnR _ tt)
              (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
           = Some (inr (Ok (Physaddr pal, PBMT_PMA, init_ext_ptw)), s1))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite execR_liftR. rewrite Htrl. cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pal, PBMT_PMA) s1)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pal) 2 false false false)) s1
           = Some (inr (Ok ilo), s1))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch_2_U PBMT_PMA pal regl ilo s1
                   iHAL iHordL iHrangeL iHXL iHmatchL iHalignL iHexecL iHcL iHsigL iHhL iHdevL iHbytesL iHprivL).
        cbn match. reflexivity. }
    cbv iota beta. rewrite autocast_mword_id_16.
    rewrite execR_returnR_fwd. cbn match. reflexivity. }
  (* second halfword: fetch_bytes at [s1] whose translate FAULTS (s1 -> s1) *)
  assert (Hfb2h : exec (fetch_bytes va vah 2) s1 = Some (@FetchBytes_Exception 2 e, s1)).
  { unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc va vah) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.bind0 (Defs.returnR _ tt)
              (Defs.liftR (translateAddr (Virtaddr vah) (InstructionFetch tt)))) s1
           = Some (inr (Err (e, tt)), s1))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s1)).
        rewrite execR_liftR. rewrite Htrh_fault. cbn match. reflexivity. }
    cbv iota beta.
    unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
  (* assemble the outer fetch: identical to the success twin up to the high
     [fetch_bytes], then the [FetchBytes_Exception] arm reports the fault at
     PC + 2 = vah. *)
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
  cbv iota beta. rewrite HnotRVC. cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC1).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC1).
  rewrite (execR_liftR_seq _ _ _ _ _ Hfb2h).
  cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC1).
  rewrite execR_returnR_fwd. cbn match. reflexivity.
Qed.

(* ===================================================================== *)
(* §2 The 4-aligned RVC fetch: identical window to the F_Base fetch --     *)
(*    only the isRVC discriminant flips, and F_RVC carries the LOW half.   *)
(* ===================================================================== *)

Lemma exec_fetch_F_RVC_4_U_gen
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
  register_lookup cur_privilege s1.(sregs) = User ->
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
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.bind0 (Defs.returnR _ tt)
              (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
           = Some (inr (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)), s1))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite execR_liftR. rewrite Htr. cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pa, PBMT_PMA) s1)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 4 false false false)) s1
           = Some (inr (Ok w), s1))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch_4_U PBMT_PMA pa region w s1
                   iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHdev iHbytes iHpriv).
        cbn match. reflexivity. }
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
  cbv iota beta. rewrite HisRVC. cbv iota beta.
  rewrite execR_returnR_fwd. cbn match. reflexivity.
Qed.

(* ===================================================================== *)
(* §3 The 2-mod-4 RVC fetch: the alignment-fault check now READS Zca       *)
(*    (misa.C = 1 keeps bit 1 legal), the Ziccif branch short-circuits on   *)
(*    the failed 4-alignment, and one 2-byte fetch_bytes runs through the   *)
(*    translate-hit chain.                                                  *)
(* ===================================================================== *)

Lemma exec_fetch_F_RVC_2_U_gen
      (va pa : mword 64) (h : mword 16) (s s1 : mstate) (region : PMA_Region) :
  register_lookup PC s.(sregs) = va ->
  neq_vec (access_vec_dec va 0) ('b"0") = false ->
  neq_vec (access_vec_dec va 1) ('b"0") = true ->
  is_aligned_vaddr (Virtaddr va) 4 = false ->
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
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
  register_lookup cur_privilege s1.(sregs) = User ->
  isRVC h = true ->
  exec (fetch tt) s = Some (F_RVC h, s1).
Proof.
  intros HpcPC Hbit0 Hbit1 Hvalign HmisaC Htr iHA iHord iHrange iHX iHmatch
         iHalign iHexec iHc iHsig iHh iHdev iHbytes iHpriv HisRVC.
  assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
  { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
  assert (Hfb2 : exec (fetch_bytes va va 2) s = Some (@FetchBytes_Success 2 h, s1)).
  { unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.bind0 (Defs.returnR _ tt)
              (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
           = Some (inr (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)), s1))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite execR_liftR. rewrite Htr. cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pa, PBMT_PMA) s1)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 2 false false false)) s1
           = Some (inr (Ok h), s1))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch_2_U PBMT_PMA pa region h s1
                   iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHdev iHbytes iHpriv).
        cbn match. reflexivity. }
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
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign. apply execR_returnR_fwd. }
      cbv iota beta. reflexivity. }
  cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ Hfb2).
  cbv iota beta. rewrite HisRVC. cbv iota beta.
  rewrite execR_returnR_fwd. cbn match. reflexivity.
Qed.

(* ===================================================================== *)
(* §4 The RVC step dispatch for a DIRECT result (no ExecuteAs hop):        *)
(*    C_NOP/C_NTL/ZCMOP retire directly, C_ILLEGAL is directly illegal,    *)
(*    C_NOT/C_ZEXT_B compute directly.  Twin of SmodeCore's               *)
(*    [exec_hart_active_progress_RVC_gen], with the base-gen's            *)
(*    non-ExecuteAs side condition.                                       *)
(* ===================================================================== *)

Lemma exec_hart_active_progress_RVC_direct_gen
    (priv : Privilege) (s s_f s_x : mstate) (h : mword 16) (instr : instruction)
    (pc : mword 64) (resf : ExecutionResult) :
  register_lookup cur_privilege s.(sregs) = priv ->
  exec (dispatchInterrupt priv) s = Some (None, s) ->
  exec (fetch tt) s = Some (F_RVC h, s_f) ->
  exec (ext_decode_compressed h) s_f = Some (instr, s_f) ->
  eq_vec (register_lookup elp s_f.(sregs))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  register_lookup PC s_f.(sregs) = pc ->
  exec (currentlyEnabled Ext_Zca) s_f = Some (true, s_f) ->
  exec (execute instr) (set_reg s_f nextPC (add_vec_int pc 2)) = Some (resf, s_x) ->
  (match resf with ExecuteAs _ => False | _ => True end) ->
  exec (run_hart_active 0) s = Some (Step_Execute (resf, zero_extend' 32 h), s_x).
Proof.
  intros Hpriv Hdisp Hfetch Hdec Hlpad HpcF Hzca Hexec Hnotexec.
  unfold run_hart_active.
  rewrite exec_catch_early_return.
  rewrite execR_bind execR_liftR exec_read_reg Hpriv. cbn match.
  rewrite execR_bind execR_liftR Hdisp. cbn match.
  rewrite execR_bind. rewrite execR_bind0 execR_returnR. cbn match.
  rewrite execR_liftR Hfetch. cbn match. cbn match.
  unfold ext_fetch_hook. cbn match. cbn beta iota.
  rewrite execR_bind execR_liftR Hdec. cbn match.
  unfold get_config_print_instr. cbn match.
  rewrite execR_bind. rewrite execR_bind0 execR_returnR. cbn match.
  rewrite execR_liftR exec_is_landing_pad Hlpad. cbn match.
  rewrite execR_bind execR_liftR Hzca. cbn match.
  rewrite execR_bind execR_liftR (exec_read_reg PC) HpcF. cbn match.
  rewrite execR_bind. rewrite execR_bind0 execR_liftR (exec_write_reg nextPC). cbn match.
  rewrite execR_liftR Hexec. cbn match.
  destruct resf; try contradiction; cbn match;
    rewrite execR_bind execR_returnR; cbn match;
    rewrite execR_returnR; cbn match; reflexivity.
Qed.

(* ===================================================================== *)
(* §5 The expansion layer: every retiring compressed instruction executes  *)
(*    as [ExecuteAs] of its base expansion (pure -- state untouched), and   *)
(*    the hint/illegal families produce their result directly.             *)
(* ===================================================================== *)

Ltac cexp := intros; reflexivity.

Lemma exec_execute_C_ADDI (imm : mword 6) (rsd : regidx) s :
  exec (execute (C_ADDI (imm, rsd))) s
    = Some (ExecuteAs (ITYPE (sign_extend' 12 imm, rsd, rsd, ADDI)), s).
Proof. cexp. Qed.

Lemma exec_execute_C_LI (imm : mword 6) (rd : regidx) s :
  exec (execute (C_LI (imm, rd))) s
    = Some (ExecuteAs (ITYPE (sign_extend' 12 imm, zreg, rd, ADDI)), s).
Proof. cexp. Qed.

Lemma exec_execute_C_ADDI16SP (imm : mword 6) s :
  exec (execute (C_ADDI16SP imm)) s
    = Some (ExecuteAs (ITYPE (sign_extend' 12 (concat_vec imm (Ox"0" : mword 4)), sp, sp, ADDI)), s).
Proof. cexp. Qed.

Lemma exec_execute_C_ADDI4SPN (rdc : cregidx) (nzimm : mword 8) s :
  exec (execute (C_ADDI4SPN (rdc, nzimm))) s
    = Some (ExecuteAs (ITYPE (concat_vec ('b"00" : mword 2) (concat_vec nzimm ('b"00" : mword 2)),
                              sp, creg2reg_idx rdc, ADDI)), s).
Proof. cexp. Qed.

Lemma exec_execute_C_ANDI (imm : mword 6) (rsd : cregidx) s :
  exec (execute (C_ANDI (imm, rsd))) s
    = Some (ExecuteAs (ITYPE (sign_extend' 12 imm, creg2reg_idx rsd, creg2reg_idx rsd, ANDI)), s).
Proof. cexp. Qed.

Lemma exec_execute_C_LUI (imm : mword 6) (rd : regidx) s :
  exec (execute (C_LUI (imm, rd))) s
    = Some (ExecuteAs (UTYPE (sign_extend' 20 imm, rd, LUI)), s).
Proof. cexp. Qed.

Lemma exec_execute_C_MV (rd rs2 : regidx) s :
  exec (execute (C_MV (rd, rs2))) s
    = Some (ExecuteAs (RTYPE (rs2, zreg, rd, ADD)), s).
Proof. cexp. Qed.

Lemma exec_execute_C_ADD (rsd rs2 : regidx) s :
  exec (execute (C_ADD (rsd, rs2))) s
    = Some (ExecuteAs (RTYPE (rs2, rsd, rsd, ADD)), s).
Proof. cexp. Qed.

Lemma exec_execute_C_AND (rsd rs2 : cregidx) s :
  exec (execute (C_AND (rsd, rs2))) s
    = Some (ExecuteAs (RTYPE (creg2reg_idx rs2, creg2reg_idx rsd, creg2reg_idx rsd, AND)), s).
Proof. cexp. Qed.

Lemma exec_execute_C_OR (rsd rs2 : cregidx) s :
  exec (execute (C_OR (rsd, rs2))) s
    = Some (ExecuteAs (RTYPE (creg2reg_idx rs2, creg2reg_idx rsd, creg2reg_idx rsd, OR)), s).
Proof. cexp. Qed.

Lemma exec_execute_C_XOR (rsd rs2 : cregidx) s :
  exec (execute (C_XOR (rsd, rs2))) s
    = Some (ExecuteAs (RTYPE (creg2reg_idx rs2, creg2reg_idx rsd, creg2reg_idx rsd, XOR)), s).
Proof. cexp. Qed.

Lemma exec_execute_C_SUB (rsd rs2 : cregidx) s :
  exec (execute (C_SUB (rsd, rs2))) s
    = Some (ExecuteAs (RTYPE (creg2reg_idx rs2, creg2reg_idx rsd, creg2reg_idx rsd, SUB)), s).
Proof. cexp. Qed.

Lemma exec_execute_C_ADDW (rsd rs2 : cregidx) s :
  exec (execute (C_ADDW (rsd, rs2))) s
    = Some (ExecuteAs (RTYPEW (creg2reg_idx rs2, creg2reg_idx rsd, creg2reg_idx rsd, ADDW)), s).
Proof. cexp. Qed.

Lemma exec_execute_C_SUBW (rsd rs2 : cregidx) s :
  exec (execute (C_SUBW (rsd, rs2))) s
    = Some (ExecuteAs (RTYPEW (creg2reg_idx rs2, creg2reg_idx rsd, creg2reg_idx rsd, SUBW)), s).
Proof. cexp. Qed.

Lemma exec_execute_C_SLLI (shamt : mword 6) (rsd : regidx) s :
  exec (execute (C_SLLI (shamt, rsd))) s
    = Some (ExecuteAs (SHIFTIOP (shamt, rsd, rsd, SLLI)), s).
Proof. cexp. Qed.

Lemma exec_execute_C_SRLI (shamt : mword 6) (rsd : cregidx) s :
  exec (execute (C_SRLI (shamt, rsd))) s
    = Some (ExecuteAs (SHIFTIOP (shamt, creg2reg_idx rsd, creg2reg_idx rsd, SRLI)), s).
Proof. cexp. Qed.

Lemma exec_execute_C_SRAI (shamt : mword 6) (rsd : cregidx) s :
  exec (execute (C_SRAI (shamt, rsd))) s
    = Some (ExecuteAs (SHIFTIOP (shamt, creg2reg_idx rsd, creg2reg_idx rsd, SRAI)), s).
Proof. cexp. Qed.

Lemma exec_execute_C_ADDIW (imm : mword 6) (rsd : regidx) s :
  exec (execute (C_ADDIW (imm, rsd))) s
    = Some (ExecuteAs (ADDIW (sign_extend' 12 imm, rsd, rsd)), s).
Proof. cexp. Qed.

Lemma exec_execute_C_J (imm : mword 11) s :
  exec (execute (C_J imm)) s
    = Some (ExecuteAs (JAL (sign_extend' 21 (concat_vec imm ('b"0" : mword 1)), zreg)), s).
Proof. cexp. Qed.

Lemma exec_execute_C_JR (rs1 : regidx) s :
  exec (execute (C_JR rs1)) s
    = Some (ExecuteAs (JALR (zeros' 12, rs1, zreg)), s).
Proof. cexp. Qed.

Lemma exec_execute_C_JALR (rs1 : regidx) s :
  exec (execute (C_JALR rs1)) s
    = Some (ExecuteAs (JALR (zeros' 12, rs1, ra)), s).
Proof. cexp. Qed.

Lemma exec_execute_C_BEQZ (imm : mword 8) (rs : cregidx) s :
  exec (execute (C_BEQZ (imm, rs))) s
    = Some (ExecuteAs (BTYPE (sign_extend' 13 (concat_vec imm ('b"0" : mword 1)), zreg, creg2reg_idx rs, BEQ)), s).
Proof. cexp. Qed.

Lemma exec_execute_C_BNEZ (imm : mword 8) (rs : cregidx) s :
  exec (execute (C_BNEZ (imm, rs))) s
    = Some (ExecuteAs (BTYPE (sign_extend' 13 (concat_vec imm ('b"0" : mword 1)), zreg, creg2reg_idx rs, BNE)), s).
Proof. cexp. Qed.

Lemma exec_execute_C_EBREAK s :
  exec (execute (C_EBREAK tt)) s = Some (ExecuteAs (EBREAK tt), s).
Proof. cexp. Qed.

(* direct results: hints retire, C_ILLEGAL is illegal *)
Lemma exec_execute_C_NOP (imm : mword 6) s :
  exec (execute (C_NOP imm)) s = Some (RETIRE_SUCCESS, s).
Proof. cexp. Qed.

Lemma exec_execute_C_NTL (n : ntl_type) s :
  exec (execute (C_NTL n)) s = Some (RETIRE_SUCCESS, s).
Proof. cexp. Qed.

Lemma exec_execute_ZCMOP (mop : mword 3) s :
  exec (execute (ZCMOP mop)) s = Some (RETIRE_SUCCESS, s).
Proof. cexp. Qed.

Lemma exec_execute_C_ILLEGAL (hw : mword 16) s :
  exec (execute (C_ILLEGAL hw)) s = Some (Illegal_Instruction tt, s).
Proof. cexp. Qed.

(* ===================================================================== *)
(* §6 Register-file execute facts for the DIRECT compressed computes      *)
(*    (C_NOT / C_ZEXT_B run rX/wX inline, no ExecuteAs) and the ZIMOP     *)
(*    may-be-operations (write rd := 0 and retire; register-generic, so   *)
(*    the 32-bit forms ride the base single-source compute arm).          *)
(* ===================================================================== *)

(* the 5-bit register index a compressed register field denotes (x8..x15) *)
Definition creg_bits (c : mword 3) : mword 5 :=
  zero_extend' 5 (concat_vec ('b"1" : mword 1) c).

Lemma exec_execute_C_NOT_gpr (c : mword 3) s :
  exec (execute (C_NOT (Cregidx c))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint (creg_bits c)) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint (creg_bits c))))
                 (regval_into_reg
                    (not_vec (if Z.eqb (uint (creg_bits c)) 0 then zero_reg
                              else register_lookup
                                     (R_bitvector_64 (gpr_of_Z (uint (creg_bits c))))
                                     s.(sregs))))).
Proof.
  change (execute (C_NOT (Cregidx c))) with (execute_C_NOT (Cregidx c)).
  unfold execute_C_NOT. cbv beta zeta iota.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr (creg_bits c) s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr (creg_bits c) _ s)).
  apply exec_returnM.
Qed.

Lemma exec_execute_C_ZEXT_B_gpr (c : mword 3) s :
  exec (execute (C_ZEXT_B (Cregidx c))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint (creg_bits c)) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint (creg_bits c))))
                 (regval_into_reg
                    (zero_extend' 64 (subrange_vec_dec
                       (if Z.eqb (uint (creg_bits c)) 0 then zero_reg
                        else register_lookup
                               (R_bitvector_64 (gpr_of_Z (uint (creg_bits c))))
                               s.(sregs)) 7 0)))).
Proof.
  change (execute (C_ZEXT_B (Cregidx c))) with (execute_C_ZEXT_B (Cregidx c)).
  unfold execute_C_ZEXT_B. cbv beta zeta iota.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr (creg_bits c) s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr (creg_bits c) _ s)).
  apply exec_returnM.
Qed.

(* the ZIMOP mop.r family in the base compute1 shape: rd := 0, retire.
   Register-generic (forall rs1'/rd'), F := const zero.                  *)
Lemma exec_execute_ZIMOP_MOP_R_gpr (mop : mword 5) (rs1 rd : mword 5) s :
  exec (execute (ZIMOP_MOP_R (mop, Regidx rs1, Regidx rd))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg
                    ((fun _ : mword 64 => zeros' 64)
                       (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup
                               (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))))).
Proof.
  change (execute (ZIMOP_MOP_R (mop, Regidx rs1, Regidx rd)))
    with (execute_ZIMOP_MOP_R mop (Regidx rs1) (Regidx rd)).
  unfold execute_ZIMOP_MOP_R. cbv beta.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  apply exec_returnM.
Qed.

Lemma exec_execute_ZIMOP_MOP_RR_gpr (mop : mword 3) (rs2 rs1 rd : mword 5) s :
  exec (execute (ZIMOP_MOP_RR (mop, Regidx rs2, Regidx rs1, Regidx rd))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg
                    ((fun _ : mword 64 => zeros' 64)
                       (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup
                               (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))))).
Proof.
  change (execute (ZIMOP_MOP_RR (mop, Regidx rs2, Regidx rs1, Regidx rd)))
    with (execute_ZIMOP_MOP_RR mop (Regidx rs2) (Regidx rs1) (Regidx rd)).
  unfold execute_ZIMOP_MOP_RR. cbv beta.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  apply exec_returnM.
Qed.

(* ===================================================================== *)
(* §7 The register-generic RTYPEW execute fact: execute_RTYPEW is         *)
(*    op-generic (one uniform rX/rX/wX chain with a pure match), so ONE   *)
(*    lemma covers ADDW/SUBW/SLLW/SRLW/SRAW -- for the base RTYPEW arm    *)
(*    and the C_ADDW/C_SUBW expansions.                                   *)
(* ===================================================================== *)

Definition gpr_rtypew_val (op : ropw) (v1 v2 : mword 64) : mword 64 :=
  sign_extend' 64
    (match op with
     | ADDW => add_vec (subrange_vec_dec v1 31 0) (subrange_vec_dec v2 31 0)
     | SUBW => sub_vec (subrange_vec_dec v1 31 0) (subrange_vec_dec v2 31 0)
     | SLLW => shift_bits_left (subrange_vec_dec v1 31 0)
                 (subrange_vec_dec (subrange_vec_dec v2 31 0) 4 0)
     | SRLW => shift_bits_right (subrange_vec_dec v1 31 0)
                 (subrange_vec_dec (subrange_vec_dec v2 31 0) 4 0)
     | SRAW => shift_bits_right_arith (subrange_vec_dec v1 31 0)
                 (subrange_vec_dec (subrange_vec_dec v2 31 0) 4 0)
     end).

Lemma exec_execute_RTYPEW_gpr (op : ropw) (rs2 rs1 rd : mword 5) s :
  exec (execute (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, op))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg
                    (gpr_rtypew_val op
                       (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup
                               (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                       (if Z.eqb (uint rs2) 0 then zero_reg
                        else register_lookup
                               (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))))).
Proof.
  change (execute (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, op)))
    with (execute_RTYPEW (Regidx rs2) (Regidx rs1) (Regidx rd) op).
  unfold execute_RTYPEW. cbv beta zeta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  unfold gpr_rtypew_val.
  destruct op; apply exec_returnM.
Qed.

(* ===================================================================== *)
(* §8 Register-generic execute facts for the remaining M-extension and    *)
(*    W-compute families.  All are pure rX/rX/wX (or rX/wX) chains; the   *)
(*    division-by-zero and signed-overflow cases are PURE ifs folded into *)
(*    the value functions.  Two-source facts are in the RTYPE nonzero-rd  *)
(*    shape (for the generic two-source arm); SHIFTIWOP is in the         *)
(*    single-source compute1 if-shape.                                    *)
(* ===================================================================== *)

Definition gpr_mulw_val (v1 v2 : mword 64) : mword 64 :=
  sign_extend' 64 (to_bits_truncate 32
    (Z.mul (sint (subrange_vec_dec v1 31 0)) (sint (subrange_vec_dec v2 31 0)))).

Definition gpr_div_val (is_unsigned : bool) (v1 v2 : mword 64) : mword 64 :=
  let rs1_int := if is_unsigned then uint v1 else sint v1 in
  let rs2_int := if is_unsigned then uint v2 else sint v2 in
  let quotient := if Z.eqb rs2_int 0 then Z.opp 1 else Z.quot rs1_int rs2_int in
  let quotient :=
    if andb (not is_unsigned) (Z.geb quotient (pow2 (Z.sub xlen 1)))
    then Z.opp (pow2 (Z.sub xlen 1)) else quotient in
  to_bits_truncate 64 quotient.

Definition gpr_divw_val (is_unsigned : bool) (v1 v2 : mword 64) : mword 64 :=
  let rs1_int := if is_unsigned then uint (subrange_vec_dec v1 31 0)
                 else sint (subrange_vec_dec v1 31 0) in
  let rs2_int := if is_unsigned then uint (subrange_vec_dec v2 31 0)
                 else sint (subrange_vec_dec v2 31 0) in
  let quotient := if Z.eqb rs2_int 0 then Z.opp 1 else Z.quot rs1_int rs2_int in
  let quotient :=
    if andb (not is_unsigned) (Z.geb quotient (pow2 31))
    then Z.opp (pow2 31) else quotient in
  sign_extend' 64 (to_bits_truncate 32 quotient).

Definition gpr_rem_val (is_unsigned : bool) (v1 v2 : mword 64) : mword 64 :=
  let rs1_int := if is_unsigned then uint v1 else sint v1 in
  let rs2_int := if is_unsigned then uint v2 else sint v2 in
  let remainder := if Z.eqb rs2_int 0 then rs1_int else Z.rem rs1_int rs2_int in
  to_bits_truncate 64 remainder.

Definition gpr_remw_val (is_unsigned : bool) (v1 v2 : mword 64) : mword 64 :=
  let rs1_int := if is_unsigned then uint (subrange_vec_dec v1 31 0)
                 else sint (subrange_vec_dec v1 31 0) in
  let rs2_int := if is_unsigned then uint (subrange_vec_dec v2 31 0)
                 else sint (subrange_vec_dec v2 31 0) in
  let remainder := if Z.eqb rs2_int 0 then rs1_int else Z.rem rs1_int rs2_int in
  sign_extend' 64 (to_bits_truncate 32 remainder).

Definition gpr_shiftiwop_val (op : sopw) (shamt : mword 5) (v1 : mword 64) : mword 64 :=
  sign_extend' 64
    (match op with
     | SLLIW => shift_bits_left (subrange_vec_dec v1 31 0) shamt
     | SRLIW => shift_bits_right (subrange_vec_dec v1 31 0) shamt
     | SRAIW => shift_bits_right_arith (subrange_vec_dec v1 31 0) shamt
     end).

Ltac gpr2_chain rs1 rs2 rd s :=
  cbv beta zeta;
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s));
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s));
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).

Lemma exec_execute_MULW_gpr (rs2 rs1 rd : mword 5) s :
  uint rd <> 0 ->
  exec (execute (MULW (Regidx rs2, Regidx rs1, Regidx rd))) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
            (regval_into_reg
               (gpr_mulw_val
                  (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                  (if Z.eqb (uint rs2) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))))).
Proof.
  intro Hrd.
  change (execute (MULW (Regidx rs2, Regidx rs1, Regidx rd)))
    with (execute_MULW (Regidx rs2) (Regidx rs1) (Regidx rd)).
  unfold execute_MULW, gpr_mulw_val. gpr2_chain rs1 rs2 rd s.
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  apply exec_returnM.
Qed.

Lemma exec_execute_DIV_gpr (u : bool) (rs2 rs1 rd : mword 5) s :
  uint rd <> 0 ->
  exec (execute (DIV (Regidx rs2, Regidx rs1, Regidx rd, u))) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
            (regval_into_reg
               (gpr_div_val u
                  (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                  (if Z.eqb (uint rs2) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))))).
Proof.
  intro Hrd.
  change (execute (DIV (Regidx rs2, Regidx rs1, Regidx rd, u)))
    with (execute_DIV (Regidx rs2) (Regidx rs1) (Regidx rd) u).
  unfold execute_DIV, gpr_div_val. gpr2_chain rs1 rs2 rd s.
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  apply exec_returnM.
Qed.

Lemma exec_execute_DIVW_gpr (u : bool) (rs2 rs1 rd : mword 5) s :
  uint rd <> 0 ->
  exec (execute (DIVW (Regidx rs2, Regidx rs1, Regidx rd, u))) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
            (regval_into_reg
               (gpr_divw_val u
                  (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                  (if Z.eqb (uint rs2) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))))).
Proof.
  intro Hrd.
  change (execute (DIVW (Regidx rs2, Regidx rs1, Regidx rd, u)))
    with (execute_DIVW (Regidx rs2) (Regidx rs1) (Regidx rd) u).
  unfold execute_DIVW, gpr_divw_val. gpr2_chain rs1 rs2 rd s.
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  apply exec_returnM.
Qed.

Lemma exec_execute_REM_gpr (u : bool) (rs2 rs1 rd : mword 5) s :
  uint rd <> 0 ->
  exec (execute (REM (Regidx rs2, Regidx rs1, Regidx rd, u))) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
            (regval_into_reg
               (gpr_rem_val u
                  (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                  (if Z.eqb (uint rs2) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))))).
Proof.
  intro Hrd.
  change (execute (REM (Regidx rs2, Regidx rs1, Regidx rd, u)))
    with (execute_REM (Regidx rs2) (Regidx rs1) (Regidx rd) u).
  unfold execute_REM, gpr_rem_val. gpr2_chain rs1 rs2 rd s.
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  apply exec_returnM.
Qed.

Lemma exec_execute_REMW_gpr (u : bool) (rs2 rs1 rd : mword 5) s :
  uint rd <> 0 ->
  exec (execute (REMW (Regidx rs2, Regidx rs1, Regidx rd, u))) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
            (regval_into_reg
               (gpr_remw_val u
                  (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                  (if Z.eqb (uint rs2) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))))).
Proof.
  intro Hrd.
  change (execute (REMW (Regidx rs2, Regidx rs1, Regidx rd, u)))
    with (execute_REMW (Regidx rs2) (Regidx rs1) (Regidx rd) u).
  unfold execute_REMW, gpr_remw_val. gpr2_chain rs1 rs2 rd s.
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  apply exec_returnM.
Qed.

(* single-source, in the compute1 if-shape: SLLIW/SRLIW/SRAIW instances
   ride ustep_compute1 with mk := fun rs1 rd => SHIFTIWOP (shamt, .., op) *)
Lemma exec_execute_SHIFTIWOP_gpr (op : sopw) (shamt : mword 5) (rs1 rd : mword 5) s :
  exec (execute (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, op))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg
                    (gpr_shiftiwop_val op shamt
                       (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup
                               (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))))).
Proof.
  change (execute (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, op)))
    with (execute_SHIFTIWOP shamt (Regidx rs1) (Regidx rd) op).
  unfold execute_SHIFTIWOP, gpr_shiftiwop_val. cbv beta zeta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  destruct op; apply exec_returnM.
Qed.

(* ===================================================================== *)
(* §9 EBREAK in User mode: the software-breakpoint Trap execution result  *)
(*    (twin of UmodeEcall's exec_execute_ECALL_U; tval = the pc).         *)
(* ===================================================================== *)

Lemma exec_execute_EBREAK_U (pc0 : mword 64) (s : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  register_lookup PC s.(sregs) = pc0 ->
  exec (execute (EBREAK tt)) s
    = Some (rv64d_types.Trap
              (User, make_sync_exception (E_Breakpoint Brk_Software) pc0, pc0), s).
Proof.
  intros Hpriv Hpc.
  change (execute (EBREAK tt)) with (execute_EBREAK tt).
  unfold execute_EBREAK.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
  rewrite Hpc. cbn beta.
  unfold trap.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv. cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
  rewrite Hpc. cbn beta.
  apply exec_returnm.
Qed.

(* ===================================================================== *)
(* §10 Illegal-in-User execute facts for the privileged families: SRET /  *)
(*     MRET / WFI (wfi-in-U disabled by config) / SFENCE_VMA /            *)
(*     SFENCE_W_INVAL / SFENCE_INVAL_IR, all conditioned only on          *)
(*     cur_privilege = User (state untouched).  These feed the            *)
(*     privilege-conditioned illegal arm.                                 *)
(* ===================================================================== *)

Lemma exec_execute_SRET_illegal_U (s : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (execute (SRET tt)) s = Some (Illegal_Instruction tt, s).
Proof.
  intro Hpriv.
  change (execute (SRET tt)) with (execute_SRET tt).
  unfold execute_SRET.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM true s)).
  cbn beta iota. apply exec_returnM.
Qed.

Lemma exec_execute_MRET_illegal_U (s : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (execute (MRET tt)) s = Some (Illegal_Instruction tt, s).
Proof.
  intro Hpriv.
  change (execute (MRET tt)) with (execute_MRET tt).
  unfold execute_MRET.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  replace (generic_neq User Machine) with true by (vm_compute; reflexivity).
  cbn match. apply exec_returnM.
Qed.

Lemma exec_execute_WFI_illegal_U (s : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (execute (WFI tt)) s = Some (Illegal_Instruction tt, s).
Proof.
  intro Hpriv.
  change (execute (WFI tt)) with (execute_WFI tt).
  unfold execute_WFI.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv. cbn match.
  change plat_wfi_available_to_usermode with false. cbn match.
  apply exec_returnM.
Qed.

Lemma exec_execute_SFENCE_W_INVAL_illegal_U (s : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (execute (SFENCE_W_INVAL tt)) s = Some (Illegal_Instruction tt, s).
Proof.
  intro Hpriv.
  change (execute (SFENCE_W_INVAL tt)) with (execute_SFENCE_W_INVAL tt).
  unfold execute_SFENCE_W_INVAL.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  replace (generic_eq User User) with true by (vm_compute; reflexivity).
  cbn match. apply exec_returnM.
Qed.

Lemma exec_execute_SFENCE_INVAL_IR_illegal_U (s : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (execute (SFENCE_INVAL_IR tt)) s = Some (Illegal_Instruction tt, s).
Proof.
  intro Hpriv.
  change (execute (SFENCE_INVAL_IR tt)) with (execute_SFENCE_INVAL_IR tt).
  unfold execute_SFENCE_INVAL_IR.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  replace (generic_eq User User) with true by (vm_compute; reflexivity).
  cbn match. apply exec_returnM.
Qed.

Lemma exec_execute_SFENCE_VMA_illegal_U (rs1 rs2 : mword 5) (s : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (execute (SFENCE_VMA (Regidx rs1, Regidx rs2))) s
    = Some (Illegal_Instruction tt, s).
Proof.
  intro Hpriv.
  change (execute (SFENCE_VMA (Regidx rs1, Regidx rs2)))
    with (execute_SFENCE_VMA (Regidx rs1) (Regidx rs2)).
  unfold execute_SFENCE_VMA.
  match goal with
  |- exec (Defs.bind ?m1 _) _ = _ =>
    assert (H1 : exists o1, exec m1 s = Some (o1, s))
  end.
  { destruct (generic_neq (Regidx rs1) zreg).
    - eexists. rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
      apply exec_returnM.
    - eexists. apply exec_returnM. }
  destruct H1 as [o1 H1].
  rewrite (exec_bind_Some _ _ _ _ _ H1). cbn beta.
  match goal with
  |- exec (Defs.bind ?m2 _) _ = _ =>
    assert (H2 : exists o2, exec m2 s = Some (o2, s))
  end.
  { destruct (generic_neq (Regidx rs2) zreg).
    - eexists. rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
      apply exec_returnM.
    - eexists. apply exec_returnM. }
  destruct H2 as [o2 H2].
  rewrite (exec_bind_Some _ _ _ _ _ H2). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv. cbn match. apply exec_returnM.
Qed.
