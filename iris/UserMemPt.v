(* UserMemPt.v -- the U-mode DATA-memory machinery over the ptree user
   table: physical loads and stores against the owned data pages
   ([udata_own]), composed with the U-mode translation absorption
   (UserPtTree.v).  This is the layer the LOAD/STORE step arms consume.

   The whole development is GENERIC in the access width [k] (a positive
   divisor of the page size, at most 8): §5's Section closes over [k]
   and the two width-TYPED plain-RAM bricks (the only places the
   dependent value type [mword (8*k)] resists abstraction -- the
   [cast_N] inside [sail_mem_read]); §6 instantiates the composers at
   the four RV64 access widths with the concrete bricks.

   Layers:
     §1 the width-generic page-window lemma;
     §2 the U-mode PMP TOR entry-0 grants (width-generic already);
     §3 the width-generic pma checks for data reads and writes;
     §4 the per-width plain-RAM bricks (read_1 and write_1/2/4 local;
        read_2/4 from RiscvFetchExec, read_8 from WpLoad, write_8 from
        WpMmodeLeafBase);
     §5 THE GENERIC SECTION: physical read/write chains at User, the
        ghost side (word out of the existential bytes; store update),
        and the invariant-level composers;
     §6 the width instances (the names the memory arms consume).        *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import SmodePte.
Require Import CommonWalk.
Require Import SmodeCore.
Require Import UptTree.
Require Import UserPtTree.
Require Import UserBits.
Require Import WpMmodeLeafBase.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import MemAccessGen.
Require Import HartMemRun HartMemAsm PtWalkCert.
Local Open Scope Z_scope.
Import Defs.


(* ===================================================================== *)
(* section 0  THE [goodmb] TWINS (the <exec, goodmb> pair convention,     *)
(*            claude-notes/projects/user-tier-port.md section 9).          *)
(*                                                                        *)
(* Every [exec_X] below has a [goodmb_X] immediately after it with the     *)
(* SAME binders and hypotheses, plus the FOOTPRINT ones -- one            *)
(* [Dr r = true] per register the stretch READS, one [Dw r = true] per     *)
(* register it WRITES, and, for a memory node, the two pure obligations    *)
(* [dev_addr pa = false] and [bytes_owned mm pa n = true] (both            *)
(* projections of [UserBytes.u_mem_wf] at the caller).  [Dr]/[Dw] are      *)
(* abstract, so nothing here depends on the tier's frame sets              *)
(* ([HartMemRun.goodmb_mono] specialises them), and [mm] is ARBITRARY --   *)
(* a data access really does touch memory, so the register-only [mm := 0]  *)
(* shortcut of [HartMemRun] section 4b is not available and                *)
(* [HartMemAsm]'s general-map combinators are what carry it.               *)
(*                                                                        *)
(* THE ASSEMBLY IS THE EXEC PROOF, NODE FOR NODE, with [exec_bind_Some] /  *)
(* [execR_liftR_seq] / [execR_untilMT_1] replaced by [HartMemAsm]'s        *)
(* [gm_bind] / [gm_liftR_seq] / [PtWalkCert.gm_untilMT_1] and each head's  *)
(* [exec] fact PAIRED with its own certificate.  The bricks the walk       *)
(* layer already proved ([PtWalkCert]: the privilege-generic PMP grant,    *)
(* [check_pma_with_pmp_priority], the MMIO window tests, the one-          *)
(* iteration split loop) are REUSED, not restated.                        *)
(*                                                                        *)
(* Three of the twins below are the twins of lemmas that live one file     *)
(* DOWN ([UserPtTree.exec_effectivePrivilege_mprv0],                       *)
(* [MemAccessGen.exec_mem_write_ea_g] and the two RAM bricks); they are    *)
(* here rather than there because an additive change to those files costs  *)
(* their rebuild cone.  FOLD THEM BACK beside their exec twins at the      *)
(* milestone.                                                             *)
(* ===================================================================== *)
(* --- 0. the RAM read brick, keyed on the EXEC fact.  [HartMemAsm.
   goodmb_read_ram] asks for [read_bytes <> None]; every caller in this tier
   holds the read's own [exec] fact instead, and at a SYMBOLIC width the two
   are not interchangeable by hand -- [read_bytes]' value index is
   [8 * Z.to_N k] while the model's is [MachineWord.Z_idx (8 * k)], the same
   number spelled two ways.  Reading the non-[None] out of the exec fact
   sidesteps the index entirely. --- *)
Lemma read_bytes_ne_of_exec_read_ram (rk : read_kind) (width : Z)
    (addr : SailStdpp.Values.mword 64) (meta : bool)
    (r : (SailStdpp.Values.mword (8 * width) * unit)%type) (s s' : mstate) :
  rk_ram_ok rk = true ->
  dev_addr addr = false ->
  exec (read_ram rk (Physaddr addr) width meta) s = Some (r, s') ->
  read_bytes s.(mem) addr (Z.to_N width) <> None.
Proof.
  intros Hrk Hdev He Hnone.
  unfold read_ram in He. cbn match in He.
  destruct rk; try discriminate Hrk;
    (rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)) in He;
     cbn beta zeta in He;
     unfold Defs.sail_mem_read in He; cbn beta zeta in He;
     unfold Defs.bind in He; cbn [Interface.iMon_bind] in He;
     erewrite exec_MemRead in He; [ | exact Hdev ];
     match type of He with
     | context [ read_bytes ?m ?a ?n ] =>
         replace (read_bytes m a n) with (@None (bv (8 * n))) in He
           by (symmetry; exact Hnone)
     end;
     cbn match in He; discriminate He).
Qed.

Lemma goodmb_read_ram_of_exec (Dr Dw : register -> bool) (rk : read_kind)
    (width : Z) (addr : SailStdpp.Values.mword 64) (meta : bool)
    (r : (SailStdpp.Values.mword (8 * width) * unit)%type) (s s' : mstate) mm :
  rk_ram_ok rk = true ->
  dev_addr addr = false ->
  bytes_owned mm addr (Z.to_N width) = true ->
  exec (read_ram rk (Physaddr addr) width meta) s = Some (r, s') ->
  goodmb Dr Dw (read_ram rk (Physaddr addr) width meta) s mm = true.
Proof.
  intros Hrk Hdev Hfp He.
  exact (goodmb_read_ram Dr Dw rk width addr meta s mm Hrk Hdev Hfp
           (read_bytes_ne_of_exec_read_ram rk width addr meta r s s' Hrk Hdev He)).
Qed.


(* --- 0b. the privilege brick (twin of [UserPtTree.exec_effectivePrivilege_
   mprv0]; FOLD BACK beside it at the milestone) --- *)
Lemma goodmb_effectivePrivilege_mprv0 (Dr Dw : register -> bool)
    (acc : MemoryAccessType mem_payload) (m : mword 64) (pr : Privilege) s mm :
  eq_vec (_get_Mstatus_MPRV m) ('b"1") = false ->
  goodmb Dr Dw (effectivePrivilege acc m pr) s mm = true.
Proof.
  intro H. unfold effectivePrivilege. rewrite H. rewrite andb_false_r.
  apply goodmb_returnm.
Qed.


(* ===================================================================== *)
(* §1 The width-generic page window (bounds in UserBits.v).                *)
(* ===================================================================== *)

Lemma u_walk_pa_window_div (k : Z) (pte0 : mword 64) (va : mword 64) (j : nat) :
  0 < k -> (k | 4096) ->
  is_aligned_vaddr (Virtaddr va) k = true ->
  (j < Z.to_nat k)%nat ->
  pa_add (u_walk_pa pte0 va) j = u_walk_pa pte0 (add_vec_int va (Z.of_nat j)).
Proof.
  intros Hk Hdvd Hal Hj.
  pose proof (off_bound_div va k Hk Hdvd Hal) as Hb.
  exact (pa_window _ va j ltac:(lia)).
Qed.

(* ===================================================================== *)
(* §2 The U-mode PMP TOR entry-0 grants for data accesses.                 *)
(* ===================================================================== *)

Lemma exec_pmpCheck_user_grant_load (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (Load Data) User) s = Some (None, s).
Proof.
  intros HA Hord Hrange HR.
  unfold pmpCheck. rewrite exec_catch_early_return.
  replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity). cbn zeta.
  rewrite execR_bind0.
  match goal with |- context[foreach_ZM_up ?F ?T ?S ?V ?B] =>
    assert (Hfe : execR (foreach_ZM_up F T S V B) s = Some (inl None, s)) end.
  { unfold foreach_ZM_up. cbn [foreach_ZM_up'].
    rewrite execR_bind.
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_pmpReadAddrReg_val 0 s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_pmpMatchAddr_TOR_match a (to_bits 64 width)
                  (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                  (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)
                  (zeros' 64) s HA Hord Hrange)). cbn beta.
    cbn match.
    unfold or_boolM.
    rewrite execR_bind.
    rewrite (execR_liftR_seq _ _ _ _ _
               (_ : exec (pmpCheckRWX (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                            (Load Data)) s = Some (true, s))).
    2:{ unfold pmpCheckRWX. cbn match. rewrite HR. apply exec_returnm. }
    cbn match. rewrite execR_returnR. cbn beta.
    cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
    unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
  rewrite Hfe. cbn match. reflexivity.
Qed.

Lemma exec_pmpCheck_user_grant_store (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (Store Data) User) s = Some (None, s).
Proof.
  intros HA Hord Hrange HW.
  unfold pmpCheck. rewrite exec_catch_early_return.
  replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity). cbn zeta.
  rewrite execR_bind0.
  match goal with |- context[foreach_ZM_up ?F ?T ?S ?V ?B] =>
    assert (Hfe : execR (foreach_ZM_up F T S V B) s = Some (inl None, s)) end.
  { unfold foreach_ZM_up. cbn [foreach_ZM_up'].
    rewrite execR_bind.
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_pmpReadAddrReg_val 0 s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_pmpMatchAddr_TOR_match a (to_bits 64 width)
                  (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                  (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)
                  (zeros' 64) s HA Hord Hrange)). cbn beta.
    cbn match.
    unfold or_boolM.
    rewrite execR_bind.
    rewrite (execR_liftR_seq _ _ _ _ _
               (_ : exec (pmpCheckRWX (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                            (Store Data)) s = Some (true, s))).
    2:{ unfold pmpCheckRWX. cbn match. rewrite HW. apply exec_returnm. }
    cbn match. rewrite execR_returnR. cbn beta.
    cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
    unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
  rewrite Hfe. cbn match. reflexivity.
Qed.

(* --- 1. the two PMP grants, off PtWalkCert's privilege-generic core --- *)
Lemma goodmb_pmpCheck_user_grant_load (Dr Dw : register -> bool)
    (a : mword 64) (width : Z) s mm :
  Dr pmpcfg_n = true -> Dr pmpaddr_n = true ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  goodmb Dr Dw (pmpCheck (Physaddr a) width (Load Data) User) s mm = true.
Proof.
  intros HDc HDa HA Hord Hrange HR.
  apply (goodmb_pmpCheck_grant Dr Dw a width (Load Data) User s mm
           HDc HDa HA Hord Hrange).
  - unfold pmpCheckRWX. cbn match. rewrite HR. apply exec_returnm.
  - unfold pmpCheckRWX. cbn match. apply goodmb_returnm.
Qed.

Lemma goodmb_pmpCheck_user_grant_store (Dr Dw : register -> bool)
    (a : mword 64) (width : Z) s mm :
  Dr pmpcfg_n = true -> Dr pmpaddr_n = true ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  goodmb Dr Dw (pmpCheck (Physaddr a) width (Store Data) User) s mm = true.
Proof.
  intros HDc HDa HA Hord Hrange HW.
  apply (goodmb_pmpCheck_grant Dr Dw a width (Store Data) User s mm
           HDc HDa HA Hord Hrange).
  - unfold pmpCheckRWX. cbn match. rewrite HW. apply exec_returnm.
  - unfold pmpCheckRWX. cbn match. apply goodmb_returnm.
Qed.


(* ===================================================================== *)
(* §3 The width-generic pma checks (the width is never scrutinized).       *)
(* ===================================================================== *)

(* --- 2. the two data PMA checks, width-generic --- *)
Lemma goodmb_pmaCheck_ram_load_g (Dr Dw : register -> bool) (k : Z)
    (addr : mword 64) (pbmt : page_based_mem_type) (region : PMA_Region) s mm :
  Dr pma_regions = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k
    = Some region ->
  is_aligned_paddr (Physaddr addr) k = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  goodmb Dr Dw (pmaCheck (Physaddr addr) k (Load Data) pbmt false) s mm = true.
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
              (Load Data) (Physaddr addr) k (Z.leb k xlen_bytes) s mm
              (goodmb_returnm Dr Dw (Z.leb k xlen_bytes) s mm)
              (exec_is_mag_applicable_load_data k s) Halign)
           (exec_mag_pma_check_aligned (override_PMA rattr pbmt)
              (Load Data) (Physaddr addr) k (Z.leb k xlen_bytes) s
              (exec_is_mag_applicable_load_data k s) Halign).
  cbn match beta. reflexivity.
Qed.

Lemma goodmb_pmaCheck_ram_store_g (Dr Dw : register -> bool) (k : Z)
    (addr : mword 64) (pbmt : page_based_mem_type) (region : PMA_Region) s mm :
  Dr pma_regions = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k
    = Some region ->
  is_aligned_paddr (Physaddr addr) k = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  goodmb Dr Dw (pmaCheck (Physaddr addr) k (Store Data) pbmt false) s mm = true.
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
              (Store Data) (Physaddr addr) k (Z.leb k xlen_bytes) s mm
              (goodmb_returnm Dr Dw (Z.leb k xlen_bytes) s mm)
              (exec_is_mag_applicable_store_data k s) Halign)
           (exec_mag_pma_check_aligned (override_PMA rattr pbmt)
              (Store Data) (Physaddr addr) k (Z.leb k xlen_bytes) s
              (exec_is_mag_applicable_store_data k s) Halign).
  cbn match beta. reflexivity.
Qed.


(* --- 3. the writable MMIO window tests (PtWalkCert has the readable pair) --- *)
Lemma goodmb_within_htif_writable (Dr Dw : register -> bool) (a : Arch.pa)
    (w : Z) s mm :
  Dr htif_tohost_base = true ->
  register_lookup htif_tohost_base s.(sregs) = None ->
  goodmb Dr Dw (within_htif_writable (Physaddr a) w) s mm = true.
Proof.
  intros HD Hn. unfold within_htif_writable.
  gmm_rr htif_tohost_base HD. rewrite Hn. cbn match. apply goodmb_returnm.
Qed.

Lemma goodmb_within_mmio_writable (Dr Dw : register -> bool) (a : Arch.pa)
    (w : Z) s mm :
  Dr htif_tohost_base = true ->
  register_lookup htif_tohost_base s.(sregs) = None ->
  exec (within_clint (Physaddr a) w) s = Some (false, s) ->
  exec (within_sig (Physaddr a) w) s = Some (false, s) ->
  goodmb Dr Dw (within_mmio_writable (Physaddr a) w) s mm = true.
Proof.
  intros HD Hn Hc Hsig. unfold within_mmio_writable. cbn [get_config_rvfi].
  erewrite gm_or_boolM; [ | apply goodmb_within_clint | exact Hc ]. cbn match.
  erewrite gm_or_boolM; [ | apply goodmb_within_sig | exact Hsig ]. cbn match.
  erewrite gm_and_boolM;
    [ | exact (goodmb_within_htif_writable Dr Dw a w s mm HD Hn)
      | exact (within_htif_writable_false a w s Hn) ].
  cbn match. reflexivity.
Qed.




(* ===================================================================== *)
(* §4 The per-width plain-RAM bricks -- the only width-TYPED pieces.       *)
(* ===================================================================== *)

Lemma is_aligned_vaddr_1 (va : mword 64) :
  is_aligned_vaddr (Virtaddr va) 1 = true.
Proof.
  unfold is_aligned_vaddr. apply Z.eqb_eq. apply Z.rem_1_r.
Qed.

Lemma run_read_ram_plain_1_pin (addr : mword 64) (w : bv 8) s :
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 1)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  run (read_ram Read_plain (Physaddr addr) 1 false) s (w, default_meta) s.
Proof.
  intros Hdev Hbytes.
  unfold read_ram. cbn match.
  apply (proj2 (run_bind _ _ _ _ _)).
  eexists _, s. split; [ apply run_returnM_fwd | ]. cbn beta zeta.
  apply (proj2 (run_bind _ _ _ _ _)).
  unfold Defs.sail_mem_read. cbn beta zeta.
  eexists _, s. split.
  - eapply run_MemRead_ram_intro.
    + exact Hdev.
    + intros j Hj. exact (Hbytes j Hj).
    + apply run_returnM_fwd.
  - cbn match beta. apply run_returnM_fwd.
Qed.

Lemma exec_read_ram_plain_1 (addr : mword 64) (w : bv 8) s :
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 1)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (read_ram Read_plain (Physaddr addr) 1 false) s = Some ((w, default_meta), s).
Proof.
  intros Hdev Hbytes.
  apply (run_to_exec _ _ _ _ (run_read_ram_plain_1_pin addr w s Hdev Hbytes)).
  unfold read_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_read. cbn beta zeta.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  rewrite exec_MemRead; last exact Hdev.
  cbn [Interface.ReadReq.pa].
  case_match eqn:Hrb.
  - cbn [Interface.iMon_bind]. cbn match beta iota. discriminate.
  - exfalso.
    refine (read_bytes_ne (mem s) addr (Z.to_N 1) w _ Hrb).
    intros j Hj.
    change (RiscvModelBytes.pa_add addr j) with (pa_add addr j).
    change (RiscvModelBytes.nth_byte w j) with (nth_byte w j).
    exact (Hbytes j Hj).
Qed.

(* its twin: the certificate does not scrutinise the value, so it is the
   width-generic [HartMemAsm.goodmb_read_ram_of_exec] at [width := 1]. *)
Lemma goodmb_read_ram_plain_1 (Dr Dw : register -> bool) (addr : mword 64)
    (w : bv 8) s mm :
  dev_addr addr = false ->
  bytes_owned mm addr 1 = true ->
  (forall j : nat, (N.of_nat j < 1)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  goodmb Dr Dw (read_ram Read_plain (Physaddr addr) 1 false) s mm = true.
Proof.
  intros Hdev Hown Hbytes.
  exact (goodmb_read_ram_of_exec Dr Dw Read_plain 1 addr false
           (w, default_meta) s s mm eq_refl Hdev Hown
           (exec_read_ram_plain_1 addr w s Hdev Hbytes)).
Qed.




(* ===================================================================== *)
(* §4b The width-free ghost window update (a store re-picks the           *)
(*     existential byte map; dom unchanged -- every address covered).     *)
(* ===================================================================== *)

Section UserMemPtGhost.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma udata_own_upd (data : gset Arch.pa) (l : list nat) (pa : Arch.pa)
        {wd : N} (v : bv wd) (m : _) :
      (forall j, j ∈ l -> pa_add pa j ∈ data) ->
      gen_heap_interp (hG := riscv_memGS) m -∗ udata_own data ==∗
      gen_heap_interp (hG := riscv_memGS)
        (foldr (fun j acc => <[pa_add pa j := nth_byte v j]> acc) m l) ∗
      udata_own data.
    Proof.
      iIntros (Hin) "Hm Hdata".
      iInduction l as [|x xs] "IH" forall (m).
      - cbn [foldr]. iModIntro. iFrame.
      - iMod ("IH" with "[] Hm Hdata") as "[Hm Hdata]".
        { iPureIntro. intros j Hj. apply Hin. apply elem_of_cons. right. exact Hj. }
        iDestruct "Hdata" as (dm) "[%Hdom Hbytes]".
        assert (Hmem : pa_add pa x ∈ dom dm).
        { rewrite Hdom. apply Hin. apply elem_of_cons. left. reflexivity. }
        apply elem_of_dom in Hmem. destruct Hmem as [b Hb].
        iDestruct (big_sepM_insert_acc _ _ _ _ Hb with "Hbytes") as "[Hab Hrest]".
        iMod (phys_update _ (pa_add pa x) b (nth_byte v x) with "Hm Hab") as "[Hm Hab]".
        iDestruct ("Hrest" $! (nth_byte v x) with "Hab") as "Hbytes".
        iModIntro.
        cbn [foldr]. iFrame "Hm".
        iExists (<[pa_add pa x := nth_byte v x]> dm).
        iFrame "Hbytes". iPureIntro.
        rewrite dom_insert_L Hdom.
        apply subseteq_union_1_L.
        apply singleton_subseteq_l.
        rewrite <- Hdom. exact (elem_of_dom_2 _ _ _ Hb).
    Qed.

End UserMemPtGhost.

(* ===================================================================== *)
(* §5 THE GENERIC DEVELOPMENT: everything above the plain bricks, over an  *)
(*    abstract access width [k].                                           *)
(* ===================================================================== *)

Section UserMemPtGeneric.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (k : Z).
  Context (Hk : 0 < k) (Hk8 : k <= 8) (Hkdvd : (k | 4096)).
  Context (Huintk : uint (to_bits 64 k) = k).
  (* the two width-TYPED plain-RAM bricks *)
  Context (Hread_plain : forall (addr : mword 64) (w : mword (8 * k)) s,
      dev_addr addr = false ->
      (forall j : nat, (N.of_nat j < Z.to_N k)%N ->
         s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
      exec (read_ram Read_plain (Physaddr addr) k false) s = Some ((w, default_meta), s)).
  Context (Hwrite_plain : forall (addr : mword 64) (data : mword (8 * k)) s,
      dev_addr addr = false ->
      exec (write_ram rv64d_types.Write_plain (Physaddr addr) k data tt) s
      = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) data) s.(mdev))).

  Lemma exec_checked_mem_read_ram_U (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (w : mword (8 * k)) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 k)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
    is_aligned_paddr (Physaddr addr) k = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
    exec (within_clint (Physaddr addr) k) s = Some (false, s) ->
    exec (within_sig (Physaddr addr) k) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr addr) k) s = Some (false, s) ->
    dev_addr addr = false ->
    (forall j : nat, (N.of_nat j < Z.to_N k)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
    exec (checked_mem_read (Load Data) pbmt User (Physaddr addr) k false false false false)
         s = Some (Ok (w, default_meta), s).
  Proof.
    intros HA Hord Hrange HR Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes.
    assert (Hcp : exec (check_pma_with_pmp_priority (Load Data) pbmt User
                          (Physaddr addr) k false) s = Some (Ok pma_ok_aligned, s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmaCheck_ram_load_g k addr pbmt region s Hmatch Halign Hread)).
      cbn match. apply exec_returnM. }
    assert (Hmmio : exec (within_mmio_readable (Physaddr addr) k) s = Some (false, s)).
    { unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
    unfold checked_mem_read. rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
    rewrite execR_bind. rewrite execR_returnR. cbn match beta.
    rewrite pma_ok_aligned_splittable. rewrite pma_ok_aligned_granule.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr k 0 s)). cbn beta.
    rewrite misaligned_order_1. cbn zeta.
    assert (Hrkf : exec (read_kind_of_flags false false false) s
                   = Some (rv64d_types.Read_plain, s))
      by (unfold read_kind_of_flags; apply exec_returnM).
    rewrite (execR_liftR_seq _ _ _ _ _ Hrkf). cbn beta.
    match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?bb) _] =>
      assert (Hu : execR (Defs.untilMT vs m0 c bb) s = Some (inr (w, true, 0), s)) end.
    { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
      change (bits_of_physaddr (Physaddr addr)) with addr.
      assert (Havi : add_vec_int addr (0 * k) = addr)
        by (assert (H0 : (0 * k)%Z = 0) by lia; rewrite H0; apply avi0).
      rewrite Havi.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_pmpCheck_user_grant_load addr k s HA Hord Hrange HR)).
      cbn beta. cbn match.
      match goal with |- context[Defs.bind (Defs.bind0 ?aa ?bb) _] =>
        assert (Hseq : execR (Defs.bind0 aa bb) s = Some (inr false, s)) end.
      { rewrite execR_bind0. rewrite execR_returnR. cbn match.
        rewrite execR_liftR. rewrite Hmmio. reflexivity. }
      rewrite (execR_bind_Some _ _ _ _ _ Hseq). cbn beta. cbn match.
      match goal with
        |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk ?ad ?wd ?mt)) ?k1) _] =>
        assert (Hrdr : execR (Defs.bind (Defs.liftR (read_ram rk ad wd mt)) k1) s
                       = Some (inr w, s)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _ (Hread_plain addr w s Hdev Hbytes)).
        cbn beta match. apply execR_returnR_fwd. }
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

  Lemma exec_mem_read_data_U (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (w : mword (8 * k)) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 k)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
    is_aligned_paddr (Physaddr addr) k = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
    exec (within_clint (Physaddr addr) k) s = Some (false, s) ->
    exec (within_sig (Physaddr addr) k) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr addr) k) s = Some (false, s) ->
    dev_addr addr = false ->
    (forall j : nat, (N.of_nat j < Z.to_N k)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
    register_lookup cur_privilege s.(sregs) = User ->
    exec (mem_read (Load Data) pbmt (Physaddr addr) k false false false)
         s = Some (Ok w, s).
  Proof.
    intros HA Hord Hrange HR Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes Hmprv Hpriv.
    unfold mem_read.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite (exec_bind_Some _ _ _ _ _
              (exec_effectivePrivilege_mprv0 (Load Data) _ _ s Hmprv)).
    rewrite Hpriv.
    unfold mem_read_priv.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (mem_read_priv_meta _ _ _ _ k _ _ _ _) s = Some (Ok (w, default_meta), s))).
    2:{ unfold mem_read_priv_meta. cbn [orb andb].
        rewrite (exec_bind_Some _ _ _ _ _
                  (_ : exec (checked_mem_read _ _ _ _ k _ _ _ _) s = Some (Ok (w, default_meta), s))).
        2:{ cbn match. apply exec_checked_mem_read_ram_U with (region := region); assumption. }
        cbn match. unfold mem_read_callback. apply exec_returnM. }
    cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
  Qed.

  Lemma exec_checked_mem_write_ram_U (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (data : mword (8 * k)) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 k)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
    is_aligned_paddr (Physaddr addr) k = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    exec (within_clint (Physaddr addr) k) s = Some (false, s) ->
    exec (within_sig (Physaddr addr) k) s = Some (false, s) ->
    exec (within_htif_writable (Physaddr addr) k) s = Some (false, s) ->
    dev_addr addr = false ->
    exec (checked_mem_write (Physaddr addr) k data (Store Data) pbmt User tt false false false) s
      = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) data) s.(mdev)).
  Proof.
    intros HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev.
    assert (Hcp : exec (check_pma_with_pmp_priority (Store Data) pbmt User
                          (Physaddr addr) k false) s = Some (Ok pma_ok_aligned, s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmaCheck_ram_store_g k addr pbmt region s Hmatch Halign Hwrite)).
      cbn match. apply exec_returnM. }
    assert (Hmmio : exec (within_mmio_writable (Physaddr addr) k) s = Some (false, s)).
    { unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
    set (sw := MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) data) s.(mdev)).
    unfold checked_mem_write. rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
    rewrite execR_bind. rewrite execR_returnR. cbn match beta.
    rewrite pma_ok_aligned_splittable. rewrite pma_ok_aligned_granule.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr k 0 s)). cbn beta.
    rewrite misaligned_order_1. cbn zeta.
    assert (Hwkf : exec (write_kind_of_flags false false false) s
                   = Some (rv64d_types.Write_plain, s))
      by (unfold write_kind_of_flags; cbn match; apply exec_returnM).
    rewrite (execR_liftR_seq _ _ _ _ _ Hwkf). cbn beta.
    match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?bb) _] =>
      assert (Hu : execR (Defs.untilMT vs m0 c bb) s = Some (inr (true, 0, true), sw)) end.
    { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
      change (bits_of_physaddr (Physaddr addr)) with addr.
      assert (Havi : add_vec_int addr (0 * k) = addr)
        by (assert (H0 : (0 * k)%Z = 0) by lia; rewrite H0; apply avi0).
      rewrite Havi.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_pmpCheck_user_grant_store addr k s HA Hord Hrange HW)).
      cbn beta. cbn match.
      rewrite execR_bind0. rewrite execR_returnR. cbn match zeta.
      rewrite (execR_liftR_seq _ _ _ _ _ Hmmio). cbn beta. cbn match.
      change (autocast (T := mword)
                (subrange_vec_dec data (8 * (0 + 1) * k - 1) (8 * 0 * k))
              : mword (8 * k))
        with (autocast (T := mword) (subrange_vec_dec data (8 * k - 1) 0)
              : mword (8 * k)).
      rewrite (subrange_full_gen_cast (8 * k) data ltac:(lia)).
      match goal with
        |- context[Defs.bind (Defs.bind (Defs.liftR (write_ram ?wk ?ad ?wd ?dt ?mt)) ?k1) _] =>
        assert (Hwrr : execR (Defs.bind (Defs.liftR (write_ram wk ad wd dt mt)) k1) s
                       = Some (inr true, sw)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _ (Hwrite_plain addr data s Hdev)).
        cbn beta. cbn [andb]. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hwrr). cbn beta zeta.
      apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
    rewrite execR_returnR. reflexivity.
  Qed.

  Lemma exec_mem_write_value_U (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (data : mword (8 * k)) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 k)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
    is_aligned_paddr (Physaddr addr) k = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    exec (within_clint (Physaddr addr) k) s = Some (false, s) ->
    exec (within_sig (Physaddr addr) k) s = Some (false, s) ->
    exec (within_htif_writable (Physaddr addr) k) s = Some (false, s) ->
    dev_addr addr = false ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
    register_lookup cur_privilege s.(sregs) = User ->
    exec (mem_write_value (Physaddr addr) k data (Store Data) pbmt false false false) s
      = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) data) s.(mdev)).
  Proof.
    intros HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev Hmprv Hpriv.
    unfold mem_write_value, mem_write_value_meta.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite (exec_bind_Some _ _ _ _ _
              (exec_effectivePrivilege_mprv0 (Store Data) _ _ s Hmprv)).
    rewrite Hpriv.
    unfold mem_write_value_priv_meta. cbn [orb andb].
    rewrite (exec_bind_Some _ _ _ _ _
              (exec_checked_mem_write_ram_U pbmt addr region data s
                 HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev)).
    cbn match. unfold mem_write_callback. apply exec_returnm.
  Qed.

  (* a k-window of a mapped page, out of the existential bytes *)
  Lemma udata_read_word_g (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (σ' : mstate) :
    um !! svpn_of va = Some w ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) k = true ->
    gen_heap_interp σ'.(mem) -∗ udata_own data -∗
    ⌜exists dv : mword (8 * k),
       (forall j : nat, (N.of_nat j < Z.to_N k)%N ->
          σ'.(mem) !! pa_add (u_walk_pa w va) j = Some (nth_byte dv j))
       /\ addr_is_ram (u_walk_pa w va)
       /\ addr_is_ram (pa_add (u_walk_pa w va) (Z.to_nat k - 1))⌝.
  Proof.
    iIntros (Hl Hcov Hal) "Hmem Hdata".
    iDestruct "Hdata" as (dm) "[%Hdom Hbytes]".
    set (pa := u_walk_pa w va).
    assert (Hin : forall j : nat, (j < Z.to_nat k)%nat -> pa_add pa j ∈ dom dm).
    { intros j Hj. rewrite Hdom.
      unfold pa. rewrite (u_walk_pa_window_div k _ _ _ Hk Hkdvd Hal Hj).
      exact (Hcov (svpn_of va) w (add_vec_int va (Z.of_nat j)) Hl). }
    assert (Hex : forall j : nat, (j < Z.to_nat k)%nat ->
              exists b, dm !! pa_add pa j = Some b).
    { intros j Hj. apply elem_of_dom. apply Hin. exact Hj. }
    destruct (bytes_list_of_lookups (fun j => dm !! pa_add pa j) (Z.to_nat k) Hex)
      as (bs & Hlen & Hbs).
    set (dv := (Z_to_bv _ (assemble_bytes bs) : mword (8 * k))).
    assert (Hnb : forall j : nat, (j < Z.to_nat k)%nat -> nth_byte dv j = bs !!! j).
    { intros j Hj. apply nth_byte_assemble_len; [ | lia ].
      rewrite Hlen.
      assert (HZN : Z.of_N (MachineWord.MachineWord.Z_idx (8 * k)) = 8 * k).
      { unfold MachineWord.MachineWord.Z_idx. apply Z2N.id. lia. }
      rewrite HZN. lia. }
    iAssert (⌜forall (a : Arch.pa) (b : bv 8), dm !! a = Some b ->
               σ'.(mem) !! a = Some b /\ addr_is_ram a⌝)%I as %Hmm.
    { iIntros (a b Hab).
      iDestruct (big_sepM_lookup_acc _ _ _ _ Hab with "Hbytes") as "[Hab Hrest]".
      iDestruct (phys_valid with "Hmem Hab") as %Hv.
      iDestruct (phys_ram with "Hab") as %Hr.
      iPureIntro. exact (conj Hv Hr). }
    iPureIntro.
    exists dv.
    split; [ | split ].
    - intros j HjN.
      assert (Hj : (j < Z.to_nat k)%nat) by lia.
      rewrite (Hnb j Hj).
      exact (proj1 (Hmm _ _ (Hbs j Hj))).
    - rewrite <- (pa_add_0 pa).
      exact (proj2 (Hmm _ _ (Hbs 0%nat ltac:(lia)))).
    - exact (proj2 (Hmm _ _ (Hbs (Z.to_nat k - 1)%nat ltac:(lia)))).
  Qed.

  (* a k-window STORE into the existential bytes *)
  Lemma udata_own_store_g (data : gset Arch.pa) (pa : Arch.pa)
      (v : mword (8 * k)) (m : _) :
    (forall j : nat, (j < Z.to_nat k)%nat -> pa_add pa j ∈ data) ->
    gen_heap_interp (hG := riscv_memGS) m -∗ udata_own data ==∗
    gen_heap_interp (hG := riscv_memGS) (write_bytes m pa (Z.to_N k) v) ∗ udata_own data.
  Proof.
    intros Hin.
    unfold write_bytes.
    rewrite Z_N_nat.
    apply (udata_own_upd data (seq 0 (Z.to_nat k)) pa v m).
    intros j Hj. apply Hin.
    apply elem_of_seq in Hj. lia.
  Qed.


  Lemma user_pt_load_data_g (uroot tfp : mword 44)
        (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
        (w va : mword 64) (σ : mstate) :
      um !! svpn_of va = Some w ->
      uleaf_ok (Load Data) w ->
      udata_cov um data ->
      is_aligned_vaddr (Virtaddr va) k = true ->
      neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
      register_lookup misa σ.(sregs) = MISA_C ->
      register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
      register_lookup htif_tohost_base σ.(sregs) = None ->
      register_lookup cur_privilege σ.(sregs) = User ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1") = false ->
      pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
      reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
      utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
      ∃ (dv : mword (8 * k)) (σ' : mstate),
        ⌜exec (translateAddr (Virtaddr va) (Load Data)) σ
          = Some (Ok (Physaddr (u_walk_pa w va), PBMT_PMA, init_ext_ptw), σ')⌝ ∗
        ⌜exec (mem_read (Load Data) PBMT_PMA (Physaddr (u_walk_pa w va)) k false false false) σ'
          = Some (Ok dv, σ')⌝ ∗
        ⌜σ'.(mdev) = σ.(mdev)⌝ ∗
        ⌜(σ'.(sregs) = σ.(sregs) \/
          exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type⌝ ∗
        reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗
        utlb_inv_pt uroot tfp um ∗ udata_own data.
    Proof.
      intros Hl Hchk Hcov Hal Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall.
      iIntros "Hri Hgh Hinv Hdata".
      iDestruct (utlb_inv_pt_pmp_facts uroot tfp um σ with "Hri Hinv")
        as %(HA & Hord & HX & HR & HW & Hcovp).
      iMod (utlb_inv_pt_translateAddr_u (Load Data) uroot tfp um w va
              (u_walk_pa w va) σ Hl Hchk Hcanon eq_refl
              Hmisa Hmenv Hhtif Hcp HSXL
              (exec_effectivePrivilege_mprv0 (Load Data)
                 (register_lookup mstatus σ.(sregs)) User σ Hmprv)
              (exec_is_shadow_stack_u_acc (Load Data) σ
                 (or_intror (or_introl eq_refl))) Hall
              with "Hri Hgh Hinv")
        as (σ') "(%Htr & %Hmdev & %Hsregs & Hri & Hgh & Hinv)".
      assert (Tr : forall r : register, register_beq r tlb = false ->
                register_lookup r σ'.(sregs) = register_lookup r σ.(sregs)).
      { intros r Hne.
        destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
          [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
      iDestruct (udata_read_word_g um data w va σ' Hl Hcov Hal with "Hgh Hdata")
        as %(dv & Hbytes & Hram0 & Hram7).
      iModIntro.
      iExists dv, σ'.
      iSplit; [ iPureIntro; exact Htr | ].
      iSplit; [ iPureIntro | ].
      { set (pa := u_walk_pa w va) in *.
        destruct (pma_all_ram (ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
                   : pma_allows_all (register_lookup pma_regions σ'.(sregs))) pa k
                  (pma_access_ram_at pa k (Z.to_nat k - 1) ltac:(clear -Hk; lia)
                     Hram0 Hram7 (pma_width_le k 8 Hk Hk8 eq_refl)))
          as (region & Hpmam & _ & Hrd & _).
        pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
        pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
        assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                  (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
                  (uint pa) (uint (to_bits 64 k)) = PMP_Match).
        { rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)).
          exact (ram_fetch_pmp pa _ k (Z.to_nat k - 1) Hk Hk8
                   Huintk ltac:(lia)
                   Hram0 Hram7 Hcovp). }
        exact (exec_mem_read_data_U PBMT_PMA pa region dv σ'
                 (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
                 (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
                 Hrange
                 (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HR))
                 Hpmam
                 (pa_aligned_div _ va k Hk Hkdvd Hal) Hrd
                 (within_clint_false pa k σ' Hnc Hk)
                 (within_sig_false pa k σ' Hns Hk)
                 (within_htif_false pa k σ'
                    (ltac:(rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif)))
                 (addr_is_ram_not_dev _ Hram0)
                 Hbytes
                 (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
                 (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))). }
      iSplit; [ iPureIntro; exact Hmdev | ].
      iSplit; [ iPureIntro; exact Hsregs | ].
      iFrame "Hri Hgh Hinv Hdata".
    Qed.

  Lemma user_pt_store_data_g (uroot tfp : mword 44)
        (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
        (w va : mword 64) (v : mword (8 * k)) (σ : mstate) :
      um !! svpn_of va = Some w ->
      uleaf_ok (Store Data) w ->
      udata_cov um data ->
      is_aligned_vaddr (Virtaddr va) k = true ->
      neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
      register_lookup misa σ.(sregs) = MISA_C ->
      register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
      register_lookup htif_tohost_base σ.(sregs) = None ->
      register_lookup cur_privilege σ.(sregs) = User ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1") = false ->
      pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
      reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
      utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
      ∃ σ' : mstate,
        ⌜exec (translateAddr (Virtaddr va) (Store Data)) σ
          = Some (Ok (Physaddr (u_walk_pa w va), PBMT_PMA, init_ext_ptw), σ')⌝ ∗
        ⌜exec (mem_write_value (Physaddr (u_walk_pa w va)) k v (Store Data)
                 PBMT_PMA false false false) σ'
          = Some (Ok true,
                  MState σ'.(sregs) (write_bytes σ'.(mem) (u_walk_pa w va) (Z.to_N k) v) σ'.(mdev))⌝ ∗
        (* the effective-address announcement, which the vmem layer now needs
           separately (mem_write_ea runs the PMA/PMP check itself) *)
        ⌜exec (mem_write_ea (Physaddr (u_walk_pa w va)) k (Store Data) PBMT_PMA
                 false false false) σ' = Some (Ok tt, σ')⌝ ∗
        ⌜σ'.(mdev) = σ.(mdev)⌝ ∗
        ⌜(σ'.(sregs) = σ.(sregs) \/
          exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type⌝ ∗
        reg_interp σ'.(sregs) ∗
        gen_heap_interp (write_bytes σ'.(mem) (u_walk_pa w va) (Z.to_N k) v) ∗
        utlb_inv_pt uroot tfp um ∗ udata_own data.
    Proof.
      intros Hl Hchk Hcov Hal Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall.
      iIntros "Hri Hgh Hinv Hdata".
      iDestruct (utlb_inv_pt_pmp_facts uroot tfp um σ with "Hri Hinv")
        as %(HA & Hord & HX & HR & HW & Hcovp).
      iMod (utlb_inv_pt_translateAddr_u (Store Data) uroot tfp um w va
              (u_walk_pa w va) σ Hl Hchk Hcanon eq_refl
              Hmisa Hmenv Hhtif Hcp HSXL
              (exec_effectivePrivilege_mprv0 (Store Data)
                 (register_lookup mstatus σ.(sregs)) User σ Hmprv)
              (exec_is_shadow_stack_u_acc (Store Data) σ
                 (or_intror (or_intror (or_introl eq_refl)))) Hall
              with "Hri Hgh Hinv")
        as (σ') "(%Htr & %Hmdev & %Hsregs & Hri & Hgh & Hinv)".
      assert (Tr : forall r : register, register_beq r tlb = false ->
                register_lookup r σ'.(sregs) = register_lookup r σ.(sregs)).
      { intros r Hne.
        destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
          [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
      (* RAM/window facts for the write, from the (pre-write) bytes *)
      iDestruct (udata_read_word_g um data w va σ' Hl Hcov Hal with "Hgh Hdata")
        as %(dv0 & _ & Hram0 & Hram7).
      set (pa := u_walk_pa w va) in *.
      (* the physical write fact at σ' *)
      assert (Hwr : exec (mem_write_value (Physaddr pa) k v (Store Data)
                            PBMT_PMA false false false) σ'
                    = Some (Ok true,
                            MState σ'.(sregs) (write_bytes σ'.(mem) pa (Z.to_N k) v) σ'.(mdev))).
      { destruct (pma_all_ram (ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
                   : pma_allows_all (register_lookup pma_regions σ'.(sregs))) pa k
                  (pma_access_ram_at pa k (Z.to_nat k - 1) ltac:(clear -Hk; lia)
                     Hram0 Hram7 (pma_width_le k 8 Hk Hk8 eq_refl)))
          as (region & Hpmam & _ & _ & Hwrb).
        pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
        pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
        assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                  (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
                  (uint pa) (uint (to_bits 64 k)) = PMP_Match).
        { rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)).
          exact (ram_fetch_pmp pa _ k (Z.to_nat k - 1) Hk Hk8
                   Huintk ltac:(lia)
                   Hram0 Hram7 Hcovp). }
        exact (exec_mem_write_value_U PBMT_PMA pa region v σ'
                 (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
                 (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
                 Hrange
                 (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW))
                 Hpmam
                 (pa_aligned_div _ va k Hk Hkdvd Hal) (proj1 Hwrb)
                 (within_clint_false pa k σ' Hnc Hk)
                 (within_sig_false pa k σ' Hns Hk)
                 (within_htif_writable_false pa k σ'
                    (ltac:(rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif)))
                 (addr_is_ram_not_dev _ Hram0)
                 (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
                 (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))). }
      (* the effective-address announcement: same PMA/PMP facts as the write *)
      assert (Hea : exec (mem_write_ea (Physaddr pa) k (Store Data) PBMT_PMA
                            false false false) σ' = Some (Ok tt, σ')).
      { destruct (pma_all_ram (ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
                   : pma_allows_all (register_lookup pma_regions σ'.(sregs))) pa k
                  (pma_access_ram_at pa k (Z.to_nat k - 1) ltac:(clear -Hk; lia)
                     Hram0 Hram7 (pma_width_le k 8 Hk Hk8 eq_refl)))
          as (region & Hpmam & _ & _ & Hwrb).
        assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                  (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
                  (uint pa) (uint (to_bits 64 k)) = PMP_Match).
        { rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)).
          exact (ram_fetch_pmp pa _ k (Z.to_nat k - 1) Hk Hk8
                   Huintk ltac:(lia)
                   Hram0 Hram7 Hcovp). }
        apply (exec_mem_write_ea_g k pa (Store Data) PBMT_PMA User σ').
        - rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)). rewrite Hcp.
          apply exec_effectivePrivilege_mprv0.
          rewrite (Tr mstatus ltac:(vm_compute; reflexivity)). exact Hmprv.
        - unfold check_pma_with_pmp_priority.
          rewrite (exec_bind_Some _ _ _ _ _
                     (exec_pmaCheck_ram_store_g k pa PBMT_PMA region σ' Hpmam
                        (pa_aligned_div _ va k Hk Hkdvd Hal) (proj1 Hwrb))).
          cbn match. apply exec_returnM.
        - exact (exec_pmpCheck_user_grant_store pa k σ'
                   (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
                   (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
                   Hrange
                   (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW))). }
      (* ghost update of the written window *)
      iMod (udata_own_store_g data pa v σ'.(mem)
              (fun j Hj => ltac:(
                 rewrite (u_walk_pa_window_div k w va j Hk Hkdvd Hal Hj);
                 exact (Hcov (svpn_of va) w (add_vec_int va (Z.of_nat j)) Hl)))
              with "Hgh Hdata") as "[Hgh Hdata]".
      iModIntro.
      iExists σ'.
      iSplit; [ iPureIntro; exact Htr | ].
      iSplit; [ iPureIntro; exact Hwr | ].
      iSplit; [ iPureIntro; exact Hea | ].
      iSplit; [ iPureIntro; exact Hmdev | ].
      iSplit; [ iPureIntro; exact Hsregs | ].
      iFrame "Hri Hgh Hinv Hdata".
    Qed.

End UserMemPtGeneric.

(* ===================================================================== *)
(* section 5b  THE [goodmb] TWINS OF section 5's FOUR PHYSICAL COMPOSERS. *)
(*                                                                        *)
(* Their own section rather than section 5's, for two reasons: they need   *)
(* their own [Dr]/[Dw] and footprint context, and they must NOT be         *)
(* generalised over the two width-TYPED RAM bricks section 5 closes over   *)
(* -- the certificate never scrutinises the value, so                      *)
(* [HartMemAsm.goodmb_read_ram] / [goodmb_write_ram] serve every width at  *)
(* once and the bricks are not needed here at all.                        *)
(* ===================================================================== *)
(* --- 4. the checked physical read, width-generic --- *)
Section GenRead.
  Context (Dr Dw : register -> bool).
  Context (k : Z) (Hk : 0 < k) (Hk8 : k <= 8).
  Context (pbmt : page_based_mem_type) (addr : mword 64) (region : PMA_Region).
  Context (w : mword (8 * k)) (s : mstate) (mm : PtBytes.pamap).

  Hypothesis HDc : Dr pmpcfg_n = true.
  Hypothesis HDa : Dr pmpaddr_n = true.
  Hypothesis HDp : Dr pma_regions = true.
  Hypothesis HDh : Dr htif_tohost_base = true.
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64)
    (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 k)) = PMP_Match.
  Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R
    (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs))
    (Physaddr addr) k = Some region.
  Hypothesis Halign : is_aligned_paddr (Physaddr addr) k = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr addr) k) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr addr) k) s = Some (false, s).
  Hypothesis Hh : register_lookup htif_tohost_base s.(sregs) = None.
  Hypothesis Hdev : dev_addr addr = false.
  Hypothesis Hown : bytes_owned mm addr (Z.to_N k) = true.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < Z.to_N k)%N ->
    s.(mem) !! (pa_add addr j) = Some (nth_byte w j).
  Hypothesis Hread_plain :
    exec (read_ram Read_plain (Physaddr addr) k false) s = Some ((w, default_meta), s).

  Lemma gr_mmio : exec (within_mmio_readable (Physaddr addr) k) s = Some (false, s).
  Proof.
    unfold within_mmio_readable. cbn [get_config_rvfi].
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ (within_htif_false addr k s Hh)).
    cbn match. reflexivity.
  Qed.

  Lemma gr_exec_cp : exec (check_pma_with_pmp_priority (Load Data) pbmt User
                             (Physaddr addr) k false) s = Some (Ok pma_ok_aligned, s).
  Proof.
    unfold check_pma_with_pmp_priority.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_pmaCheck_ram_load_g k addr pbmt region s Hmatch Halign Hread)).
    cbn match. apply exec_returnM.
  Qed.

  Lemma gr_good_cp : goodmb Dr Dw (check_pma_with_pmp_priority (Load Data) pbmt User
                             (Physaddr addr) k false) s mm = true.
  Proof.
    exact (goodmb_check_pma_with_pmp_priority Dr Dw _ _ User _ _ false _ s mm
             (goodmb_pmaCheck_ram_load_g Dr Dw k addr pbmt region s mm
                HDp Hmatch Halign Hread)
             (exec_pmaCheck_ram_load_g k addr pbmt region s Hmatch Halign Hread)).
  Qed.

  Lemma goodmb_checked_mem_read_ram_U :
    goodmb Dr Dw (checked_mem_read (Load Data) pbmt User (Physaddr addr) k
                    false false false false) s mm = true.
  Proof.
    unfold checked_mem_read. apply goodmb_cer.
    erewrite gm_liftR_seq; [ | apply gr_good_cp | apply gr_exec_cp ].
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
                 (exec_pmpCheck_user_grant_load addr k s HA Hord Hrange HR)).
      cbn beta. cbn match.
      match goal with |- context[Defs.bind (Defs.bind0 ?aa ?bb) _] =>
        assert (Hseq : execR (Defs.bind0 aa bb) s = Some (inr false, s)) end.
      { rewrite execR_bind0. rewrite execR_returnR. cbn match.
        rewrite execR_liftR. rewrite gr_mmio. reflexivity. }
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
        gmm_lift (goodmb_pmpCheck_user_grant_load Dr Dw addr k s mm
                    HDc HDa HA Hord Hrange HR)
                 (exec_pmpCheck_user_grant_load addr k s HA Hord Hrange HR).
        cbn beta. cbn match.
        match goal with |- context[Defs.bind (Defs.bind0 ?aa ?bb) _] =>
          assert (Hseqg : goodmb Dr Dw (Defs.bind0 aa bb) s mm = true);
          [ | assert (Hseq : execR (Defs.bind0 aa bb) s = Some (inr false, s)) ] end.
        { erewrite gm_bind0R; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
          apply goodmb_liftR.
          exact (goodmb_within_mmio_readable Dr Dw addr k s mm HDh Hh Hc Hsig). }
        { rewrite execR_bind0. rewrite execR_returnR. cbn match.
          rewrite execR_liftR. rewrite gr_mmio. reflexivity. }
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
                   (exec_pmpCheck_user_grant_load addr k s HA Hord Hrange HR)).
        cbn beta. cbn match.
        match goal with |- context[Defs.bind (Defs.bind0 ?aa ?bb) _] =>
          assert (Hseq : execR (Defs.bind0 aa bb) s = Some (inr false, s)) end.
        { rewrite execR_bind0. rewrite execR_returnR. cbn match.
          rewrite execR_liftR. rewrite gr_mmio. reflexivity. }
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
    erewrite (gm_bindR Dr Dw _ _ s s mm (w, true, 0) Hug Hu).
    cbn beta zeta. kill_autocast. apply goodmb_returnm.
  Qed.

End GenRead.


(* --- 5. the U-mode data read, one level up --- *)
Section GenRead2.
  Context (Dr Dw : register -> bool).
  Context (k : Z) (pbmt : page_based_mem_type) (addr : mword 64)
          (w : mword (8 * k)) (s : mstate) (mm : PtBytes.pamap).

  Lemma goodmb_mem_read_data_U :
    Dr mstatus = true -> Dr cur_privilege = true ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
    register_lookup cur_privilege s.(sregs) = User ->
    goodmb Dr Dw (checked_mem_read (Load Data) pbmt User (Physaddr addr) k
                    false false false false) s mm = true ->
    exec (checked_mem_read (Load Data) pbmt User (Physaddr addr) k
            false false false false) s = Some (Ok (w, default_meta), s) ->
    goodmb Dr Dw (mem_read (Load Data) pbmt (Physaddr addr) k false false false)
      s mm = true.
  Proof.
    intros HDm HDp Hmprv Hpriv Hchkg Hchke.
    unfold mem_read.
    gmm_rr mstatus HDm.
    gmm_rr cur_privilege HDp.
    erewrite gm_bind;
      [ | exact (goodmb_effectivePrivilege_mprv0 Dr Dw (Load Data)
                   (register_lookup mstatus s.(sregs))
                   (register_lookup cur_privilege s.(sregs)) s mm Hmprv)
        | exact (exec_effectivePrivilege_mprv0 (Load Data)
                   (register_lookup mstatus s.(sregs))
                   (register_lookup cur_privilege s.(sregs)) s Hmprv) ].
    rewrite Hpriv.
    unfold mem_read_priv, mem_read_priv_meta. cbn [orb andb].
    gmm_peel Hchkg Hchke. cbn match.
    unfold mem_read_callback. cbn [MemoryOpResult_drop_meta].
    apply goodmb_returnm.
  Qed.

End GenRead2.


(* --- 6. the checked physical write, width-generic --- *)
Section GenWrite.
  Context (Dr Dw : register -> bool).
  Context (k : Z) (Hk : 0 < k) (Hk8 : k <= 8).
  Context (pbmt : page_based_mem_type) (addr : mword 64) (region : PMA_Region).
  Context (data : mword (8 * k)) (s : mstate) (mm : PtBytes.pamap).

  Hypothesis HDc : Dr pmpcfg_n = true.
  Hypothesis HDa : Dr pmpaddr_n = true.
  Hypothesis HDp : Dr pma_regions = true.
  Hypothesis HDh : Dr htif_tohost_base = true.
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64)
    (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 k)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W
    (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs))
    (Physaddr addr) k = Some region.
  Hypothesis Halign : is_aligned_paddr (Physaddr addr) k = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr addr) k) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr addr) k) s = Some (false, s).
  Hypothesis Hh : register_lookup htif_tohost_base s.(sregs) = None.
  Hypothesis Hdev : dev_addr addr = false.
  Hypothesis Hown : bytes_owned mm addr (Z.to_N k) = true.
  Hypothesis Hwrite_plain : forall (d : mword (8 * k)),
    exec (write_ram rv64d_types.Write_plain (Physaddr addr) k d tt) s
    = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) d) s.(mdev)).

  Lemma gw_mmio : exec (within_mmio_writable (Physaddr addr) k) s = Some (false, s).
  Proof.
    unfold within_mmio_writable. cbn [get_config_rvfi].
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ (within_htif_writable_false addr k s Hh)).
    cbn match. reflexivity.
  Qed.

  Lemma gw_exec_cp : exec (check_pma_with_pmp_priority (Store Data) pbmt User
                             (Physaddr addr) k false) s = Some (Ok pma_ok_aligned, s).
  Proof.
    unfold check_pma_with_pmp_priority.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_pmaCheck_ram_store_g k addr pbmt region s Hmatch Halign Hwrite)).
    cbn match. apply exec_returnM.
  Qed.

  Lemma gw_good_cp : goodmb Dr Dw (check_pma_with_pmp_priority (Store Data) pbmt User
                             (Physaddr addr) k false) s mm = true.
  Proof.
    exact (goodmb_check_pma_with_pmp_priority Dr Dw _ _ User _ _ false _ s mm
             (goodmb_pmaCheck_ram_store_g Dr Dw k addr pbmt region s mm
                HDp Hmatch Halign Hwrite)
             (exec_pmaCheck_ram_store_g k addr pbmt region s Hmatch Halign Hwrite)).
  Qed.

  Lemma goodmb_checked_mem_write_ram_U :
    goodmb Dr Dw (checked_mem_write (Physaddr addr) k data (Store Data) pbmt User
                    tt false false false) s mm = true.
  Proof.
    set (sw := MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) data) s.(mdev)).
    unfold checked_mem_write. apply goodmb_cer.
    erewrite gm_liftR_seq; [ | apply gw_good_cp | apply gw_exec_cp ].
    cbn beta. cbn match.
    erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
    cbn match beta.
    rewrite pma_ok_aligned_splittable. rewrite pma_ok_aligned_granule.
    gmm_lift (goodmb_split_misaligned_unsplit Dr Dw addr k 0 s mm)
             (exec_split_misaligned_unsplit addr k 0 s). cbn beta.
    cbn match beta. rewrite misaligned_order_1. cbn match zeta beta.
    assert (Hwkf : exec (write_kind_of_flags false false false) s
                   = Some (rv64d_types.Write_plain, s))
      by (unfold write_kind_of_flags; cbn match; apply exec_returnM).
    assert (Hwkg : goodmb Dr Dw (write_kind_of_flags false false false) s mm = true)
      by (unfold write_kind_of_flags; cbn match; apply goodmb_returnm).
    gmm_lift Hwkg Hwkf. cbn beta.
    assert (Havi : add_vec_int addr (0 * k) = addr)
      by (assert (H0 : (0 * k)%Z = 0) by lia; rewrite H0; apply avi0).
    match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?bb) _] =>
      assert (Hu : execR (Defs.untilMT vs m0 c bb) s = Some (inr (true, 0, true), sw));
      [ | assert (Hug : goodmb Dr Dw (Defs.untilMT vs m0 c bb) s mm = true) ] end.
    { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
      change (bits_of_physaddr (Physaddr addr)) with addr.
      rewrite Havi.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_pmpCheck_user_grant_store addr k s HA Hord Hrange HW)).
      cbn beta. cbn match.
      rewrite execR_bind0. rewrite execR_returnR. cbn match zeta.
      rewrite (execR_liftR_seq _ _ _ _ _ gw_mmio). cbn beta. cbn match.
      change (autocast (T := mword)
                (subrange_vec_dec data (8 * (0 + 1) * k - 1) (8 * 0 * k))
              : mword (8 * k))
        with (autocast (T := mword) (subrange_vec_dec data (8 * k - 1) 0)
              : mword (8 * k)).
      rewrite (subrange_full_gen_cast (8 * k) data ltac:(lia)).
      match goal with
        |- context[Defs.bind (Defs.bind (Defs.liftR (write_ram ?wk ?ad ?wd ?dt ?mt)) ?k1) _] =>
        assert (Hwrr : execR (Defs.bind (Defs.liftR (write_ram wk ad wd dt mt)) k1) s
                       = Some (inr true, sw)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _ (Hwrite_plain data)).
        cbn beta. cbn [andb]. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hwrr). cbn beta zeta.
      apply execR_returnR_fwd. }
    { eapply gm_untilMT_1; [ reflexivity | | | | ].
      - gmm_liftT ltac:(apply goodmb_assert_exp'_true)
                  ltac:(apply exec_assert_exp'_true). cbn beta.
        change (bits_of_physaddr (Physaddr addr)) with addr.
        rewrite Havi.
        gmm_lift (goodmb_pmpCheck_user_grant_store Dr Dw addr k s mm
                    HDc HDa HA Hord Hrange HW)
                 (exec_pmpCheck_user_grant_store addr k s HA Hord Hrange HW).
        cbn beta. cbn match.
        erewrite gm_bind0R; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
        cbn match zeta.
        gmm_lift (goodmb_within_mmio_writable Dr Dw addr k s mm HDh Hh Hc Hsig)
                 gw_mmio. cbn beta. cbn match.
        change (autocast (T := mword)
                  (subrange_vec_dec data (8 * (0 + 1) * k - 1) (8 * 0 * k))
                : mword (8 * k))
          with (autocast (T := mword) (subrange_vec_dec data (8 * k - 1) 0)
                : mword (8 * k)).
        rewrite (subrange_full_gen_cast (8 * k) data ltac:(lia)).
        match goal with
          |- context[Defs.bind (Defs.bind (Defs.liftR (write_ram ?wk ?ad ?wd ?dt ?mt)) ?k1) _] =>
          assert (Hwrg : goodmb Dr Dw
                    (Defs.bind (Defs.liftR (write_ram wk ad wd dt mt)) k1) s mm = true);
          [ | assert (Hwrr : execR (Defs.bind (Defs.liftR (write_ram wk ad wd dt mt)) k1) s
                             = Some (inr true, sw)) ] end.
        { erewrite gm_liftR_seq;
            [ | exact (goodmb_write_ram Dr Dw rv64d_types.Write_plain k addr data
                         s mm eq_refl Hdev Hown)
              | exact (Hwrite_plain data) ].
          cbn beta. cbn [andb]. apply goodmb_returnm. }
        { rewrite (execR_liftR_seq _ _ _ _ _ (Hwrite_plain data)).
          cbn beta. cbn [andb]. apply execR_returnR_fwd. }
        erewrite (gm_bindR Dr Dw _ _ s sw mm true Hwrg Hwrr). cbn beta zeta.
        apply goodmb_returnm.
      - rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
        change (bits_of_physaddr (Physaddr addr)) with addr.
        rewrite Havi.
        rewrite (execR_liftR_seq _ _ _ _ _
                   (exec_pmpCheck_user_grant_store addr k s HA Hord Hrange HW)).
        cbn beta. cbn match.
        rewrite execR_bind0. rewrite execR_returnR. cbn match zeta.
        rewrite (execR_liftR_seq _ _ _ _ _ gw_mmio). cbn beta. cbn match.
        change (autocast (T := mword)
                  (subrange_vec_dec data (8 * (0 + 1) * k - 1) (8 * 0 * k))
                : mword (8 * k))
          with (autocast (T := mword) (subrange_vec_dec data (8 * k - 1) 0)
                : mword (8 * k)).
        rewrite (subrange_full_gen_cast (8 * k) data ltac:(lia)).
        match goal with
          |- context[Defs.bind (Defs.bind (Defs.liftR (write_ram ?wk ?ad ?wd ?dt ?mt)) ?k1) _] =>
          assert (Hwrr : execR (Defs.bind (Defs.liftR (write_ram wk ad wd dt mt)) k1) s
                         = Some (inr true, sw)) end.
        { rewrite (execR_liftR_seq _ _ _ _ _ (Hwrite_plain data)).
          cbn beta. cbn [andb]. apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hwrr). cbn beta zeta.
        apply execR_returnR_fwd.
      - reflexivity.
      - apply execR_returnR_fwd. }
    erewrite (gm_bindR Dr Dw _ _ s sw mm (true, 0, true) Hug Hu).
    cbn beta zeta. apply goodmb_returnm.
  Qed.

End GenWrite.


(* --- 7. the effective-address announcement (twin of
   [MemAccessGen.exec_mem_write_ea_g]; FOLD BACK beside it) --- *)
Lemma goodmb_mem_write_ea_g (Dr Dw : register -> bool) (width : Z)
    (addr : mword 64) (acc : MemoryAccessType mem_payload)
    (pbmt : page_based_mem_type) (ep : Privilege) s mm :
  0 < width ->
  Dr mstatus = true -> Dr cur_privilege = true ->
  goodmb Dr Dw (effectivePrivilege acc (register_lookup mstatus s.(sregs))
                  (register_lookup cur_privilege s.(sregs))) s mm = true ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  goodmb Dr Dw (check_pma_with_pmp_priority acc pbmt ep (Physaddr addr) width false)
    s mm = true ->
  exec (check_pma_with_pmp_priority acc pbmt ep (Physaddr addr) width false) s
    = Some (Ok pma_ok_aligned, s) ->
  goodmb Dr Dw (pmpCheck (Physaddr addr) width acc ep) s mm = true ->
  exec (pmpCheck (Physaddr addr) width acc ep) s = Some (None, s) ->
  goodmb Dr Dw (mem_write_ea (Physaddr addr) width acc pbmt false false false)
    s mm = true.
Proof.
  intros Hw HDm HDp Heffg Heff Hcpg Hcp Hpmpg Hpmpchk.
  assert (Hms : goodmb Dr Dw (Defs.read_reg mstatus : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDm).
  assert (Hpv : goodmb Dr Dw (Defs.read_reg cur_privilege : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDp).
  assert (Hwkf : exec (write_kind_of_flags false false false) s
                 = Some (rv64d_types.Write_plain, s))
    by (unfold write_kind_of_flags; cbn match; apply exec_returnM).
  assert (Hwkg : goodmb Dr Dw (write_kind_of_flags false false false) s mm = true)
    by (unfold write_kind_of_flags; cbn match; apply goodmb_returnm).
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
  match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?bb) _] =>
    assert (Hu : execR (Defs.untilMT vs m0 c bb) s = Some (inr (true, 0), s));
    [ | assert (Hug : goodmb Dr Dw (Defs.untilMT vs m0 c bb) s mm = true) ] end.
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


(* --- 8. the U-mode data write, one level up --- *)
Section GenWrite2.
  Context (Dr Dw : register -> bool).
  Context (k : Z) (pbmt : page_based_mem_type) (addr : mword 64)
          (data : mword (8 * k)) (s : mstate) (mm : PtBytes.pamap).

  Lemma goodmb_mem_write_value_U :
    Dr mstatus = true -> Dr cur_privilege = true ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
    register_lookup cur_privilege s.(sregs) = User ->
    goodmb Dr Dw (checked_mem_write (Physaddr addr) k data (Store Data) pbmt User
                    tt false false false) s mm = true ->
    exec (checked_mem_write (Physaddr addr) k data (Store Data) pbmt User
            tt false false false) s
      = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) data) s.(mdev)) ->
    goodmb Dr Dw (mem_write_value (Physaddr addr) k data (Store Data) pbmt
                    false false false) s mm = true.
  Proof.
    intros HDm HDp Hmprv Hpriv Hchkg Hchke.
    unfold mem_write_value, mem_write_value_meta.
    gmm_rr mstatus HDm.
    gmm_rr cur_privilege HDp.
    erewrite gm_bind;
      [ | exact (goodmb_effectivePrivilege_mprv0 Dr Dw (Store Data)
                   (register_lookup mstatus s.(sregs))
                   (register_lookup cur_privilege s.(sregs)) s mm Hmprv)
        | exact (exec_effectivePrivilege_mprv0 (Store Data)
                   (register_lookup mstatus s.(sregs))
                   (register_lookup cur_privilege s.(sregs)) s Hmprv) ].
    rewrite Hpriv.
    unfold mem_write_value_priv_meta. cbn [orb andb].
    gmm_peel Hchkg Hchke. cbn match.
    unfold mem_write_callback. apply goodmb_returnm.
  Qed.

End GenWrite2.

(* ===================================================================== *)
(* §6 The width instances -- the names the memory arms consume.            *)
(* ===================================================================== *)

Section UserMemPtInstances.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.









End UserMemPtInstances.

(* ===================================================================== *)
(* §7 AMO (width 4, AMOSWAP -- MemAmo4's kernel scope): the U-mode PMP    *)
(*    grant and the bundle composer.  The AMO's single translation serves *)
(*    both the read and the write, so the composer returns the old value  *)
(*    plus a ∀-value PURE write fact at the moved state; the arm computes *)
(*    the stored value from the old one and absorbs the write into        *)
(*    [udata_own] with [udata_own_store_4].                               *)
(* ===================================================================== *)


Section UserMemPtAmo.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


End UserMemPtAmo.
