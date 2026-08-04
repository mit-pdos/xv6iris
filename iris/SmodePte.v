(* SmodePte.v -- S-mode PMP grants, the checked 8-byte PTE read, TLB
   lookup/consistency helpers, factored out of SmodeCore.v so the 4KB
   page-walk layer (Pt4kWalk.v) can sit BELOW SmodeCore.  All lemmas are
   verbatim moves; proofs here rely on the ssreflect rewrite (iris env),
   matching their original home.  *)
From Stdlib Require Import ZArith FunctionalExtensionality.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep.
Require Import WpLoad ExecCommon.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 1. S-mode PMP: the TOR entry-0 grant (from SmodeCore).                 *)
(* ===================================================================== *)

Lemma exec_pmpMatchAddr_TOR_match (addr width : mword 64) (ent : mword 8)
    (pmpaddr prev : mword 64) s :
  pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent) = TOR ->
  zopz0zKzJ_u prev pmpaddr = false ->
  pmpRangeMatch (Z.mul (uint prev) 4) (Z.mul (uint pmpaddr) 4) (uint addr) (uint width) = PMP_Match ->
  exec (pmpMatchAddr (Physaddr addr) width ent pmpaddr prev) s = Some (PMP_Match, s).
Proof.
  intros HA Hord Hrange. unfold pmpMatchAddr. cbn zeta.
  rewrite HA. cbn match. rewrite Hord. rewrite Hrange. apply exec_returnm.
Qed.

Lemma exec_pmpReadAddrReg_val (n : Z) s :
  exec (pmpReadAddrReg n) s
    = Some (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) n, s).
Proof.
  unfold pmpReadAddrReg. cbn zeta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpaddr_n s)). cbn beta.
  replace (andb (Z.geb sys_pmp_grain 2)
             (eq_vec (access_vec_dec (_get_Pmpcfg_ent_A
                (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) n)) 1) ('b"1")))
    with false by (vm_compute; reflexivity).
  replace (andb (Z.geb sys_pmp_grain 1)
             (eq_vec (access_vec_dec (_get_Pmpcfg_ent_A
                (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) n)) 1) ('b"0")))
    with false by (vm_compute; reflexivity).
  cbn match. apply exec_returnm.
Qed.

Lemma exec_pmpCheck_supervisor_grant (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (InstructionFetch tt) Supervisor) s = Some (None, s).
Proof.
  intros HA Hord Hrange HX.
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
                            (InstructionFetch tt)) s = Some (true, s))).
    2:{ unfold pmpCheckRWX. cbn match. rewrite HX. apply exec_returnm. }
    cbn match. rewrite execR_returnR. cbn beta.
    cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
    unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
  rewrite Hfe. cbn match. reflexivity.
Qed.

Lemma exec_pmpCheck_supervisor_grant_load (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (Load PageTableEntry) Supervisor) s = Some (None, s).
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
                            (Load PageTableEntry)) s = Some (true, s))).
    2:{ unfold pmpCheckRWX. cbn match. rewrite HR. apply exec_returnm. }
    cbn match. rewrite execR_returnR. cbn beta.
    cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
    unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
  rewrite Hfe. cbn match. reflexivity.
Qed.


(* The TOR-entry-0 facts of the page walk's 8-byte PTE read (R instead of X). *)

(* ===================================================================== *)
(* 4. S-mode fetch memory reads (widths 2 and 4) + the 8-byte PTE read.    *)
(* ===================================================================== *)

Lemma exec_translationMode_S_sv39 (satp0 : mword 64) s :
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  exec (translationMode Supervisor) s = Some (Sv39, s).
Proof.
  intros HSXL Hsatp Hmode.
  unfold translationMode.
  replace (generic_eq Supervisor Machine) with false by (vm_compute; reflexivity).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_architecture_Supervisor s HSXL)).
  cbn match.
  change (xlen >=? 64) with true.
  match goal with |- exec (Defs.bind ?ARM _) s = _ =>
    assert (HARM : exec ARM s = Some (_get_Satp64_Mode (Mk_Satp64 satp0), s)) end.
  { assert (Hae : exec (Defs.assert_exp' true "sys/vmem.sail:254.25-254.26") s
                  = Some (eq_refl, s)).
    { unfold assert_exp'. cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hae).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
    rewrite Hsatp. apply exec_returnm. }
  rewrite (exec_bind_Some _ _ _ _ _ HARM).
  rewrite Hmode.
  replace (satpMode_of_bits RV64 ('b"1000" : mword 4)) with (Some Sv39)
    by (vm_compute; reflexivity).
  cbn match. apply exec_returnm.
Qed.

(* ===================================================================== *)
(* 2. TLB vector / hash helpers + generic consistency (from SmodeCore).  *)
(* ===================================================================== *)

(* list_update at a valid index is stdpp's insert (local copy; also in
   WpGprCsrwC, which imports us transitively -- keep them independent). *)
Lemma tlb_list_update_insert {A} (xs : list A) (k : nat) (x : A) :
  (k < length xs)%nat -> list_update xs k x = <[k := x]> xs.
Proof. intros Hk. symmetry. apply insert_take_drop. exact Hk. Qed.

(* vec_access_dec over vec_update_dec on a 64-entry vector, at ANY index j
   (including the out-of-range ones, where both sides read the same dummy). *)
Lemma vec64_access_update {T} `{Inhabited T} (v : vec T (2 ^ 6)) (m j : Z) (t : T) :
  0 <= m < 64 ->
  vec_access_dec (vec_update_dec v m t) j
  = (if Z.eqb j m then t else vec_access_dec v j).
Proof.
  intros Hm. destruct v as [xs Hlen].
  assert (Hl : length xs = 64%nat) by (rewrite Hlen; reflexivity).
  unfold vec_update_dec.
  destruct (sumbool_of_bool (0 <=? m <? 2 ^ 6)) as [He|He].
  2:{ exfalso.
      assert (Ht : ((0 <=? m) && (m <? 2 ^ 6))%bool = true)
        by (apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
      rewrite Ht in He. discriminate He. }
  unfold vec_access_dec. cbn [projT1].
  unfold update_list_dec, update_list_inc, access_list_dec, access_list_inc, length_list.
  rewrite !Hl.
  change (Z.of_nat 64 - 1) with 63.
  set (k := Z.to_nat (63 - m)).
  assert (Hk : (k < length xs)%nat) by (unfold k; rewrite Hl; lia).
  rewrite (tlb_list_update_insert xs k t Hk).
  rewrite length_insert. rewrite Hl.
  change (Z.of_nat 64 - 1) with 63.
  destruct (Z.ltb (63 - j) 0) eqn:Hg.
  - (* out of range below: both dummy; j > 63 > m *)
    apply Z.ltb_lt in Hg.
    replace (Z.eqb j m) with false by (symmetry; apply Z.eqb_neq; lia).
    reflexivity.
  - apply Z.ltb_ge in Hg.
    destruct (Z.eqb j m) eqn:Hjm.
    + apply Z.eqb_eq in Hjm. subst j.
      rewrite nth_lookup.
      replace (Z.to_nat (63 - m)) with k by reflexivity.
      rewrite (list_lookup_insert xs k t Hk). reflexivity.
    + apply Z.eqb_neq in Hjm.
      rewrite nth_lookup.
      rewrite list_lookup_insert_ne.
      2:{ unfold k. lia. }
      rewrite <- nth_lookup. reflexivity.
Qed.

(* the direct-mapped hash always lands in range. *)
Lemma tlb_hash_range (vpn : mword 27) : 0 <= tlb_hash (__id 39) vpn < 2 ^ 6.
Proof.
  unfold tlb_hash.
  match goal with |- 0 <= uint ?x < _ =>
    pose proof (uint_range x ltac:(vm_compute; discriminate)) as Hr end.
  match type of Hr with 0 <= _ <= 2 ^ ?a - 1 =>
    replace (2 ^ a - 1) with 63 in Hr by (vm_compute; reflexivity) end.
  change (2 ^ 6) with 64. lia.
Qed.

(* ---- [tlb]-register set laws: a TLB fill writes only the [tlb] cell, so     *)
(* nested/idempotent [set_reg .. tlb ..] collapse.  Used to flatten the         *)
(* possibly-double-filled fetch state to a single [set_reg σ tlb tlbvec2].      *)
Lemma register_set_tlb_id (rs : regstate) :
  register_set tlb (register_lookup tlb rs) rs = rs.
Proof.
  destruct rs. unfold register_set, register_lookup. cbn.
  f_equal. apply functional_extensionality. intros r'.
  destruct (register_vector_64_option_TLB_Entry_beq r' tlb) eqn:E.
  - apply register_vector_64_option_TLB_Entry_beq_iff in E. subst r'. reflexivity.
  - reflexivity.
Qed.

Lemma register_set_tlb_overwrite (rs : regstate) (a b : type_of_register tlb) :
  register_set tlb b (register_set tlb a rs) = register_set tlb b rs.
Proof.
  destruct rs. unfold register_set. cbn.
  f_equal. apply functional_extensionality. intros r'.
  destruct (register_vector_64_option_TLB_Entry_beq r' tlb); reflexivity.
Qed.

Lemma set_reg_tlb_id (s : mstate) :
  set_reg s tlb (register_lookup tlb s.(sregs)) = s.
Proof. destruct s. unfold set_reg. cbn. rewrite register_set_tlb_id. reflexivity. Qed.

Lemma set_reg_tlb_overwrite (s : mstate) (a b : type_of_register tlb) :
  set_reg (set_reg s tlb a) tlb b = set_reg s tlb b.
Proof. destruct s. unfold set_reg. cbn. rewrite register_set_tlb_overwrite. reflexivity. Qed.

(* ===================================================================== *)
(* Local RAM-geometry lemmas needed to DERIVE the S-mode fetch geometry    *)
(* from an owned instruction points-to (addr_is_ram), instead of taking it *)
(* as fetch-geometry premises.  (Local copies of the                       *)
(* WpSmodeGpr/WpGprRvcTor lemmas, which live downstream of this file; the   *)
(* others -- ram_canonical/ram_svpn2/ram_mask/ram_mvpn/svpn_of_unsigned -- *)
(* are already in RiscvExtras.)                                            *)
(* ===================================================================== *)

Lemma pmpRangeMatch_full (b e a w : Z) :
  b <= a -> 0 < w -> a + w <= e ->
  pmpRangeMatch b e a w = PMP_Match.
Proof.
  intros Hb Hw He. unfold pmpRangeMatch.
  replace (Z.leb (Z.add a w) b) with false by (symmetry; apply Z.leb_gt; lia).
  replace (Z.leb e a) with false by (symmetry; apply Z.leb_gt; lia).
  cbn [orb].
  replace (Z.leb b a) with true by (symmetry; apply Z.leb_le; lia).
  replace (Z.leb (Z.add a w) e) with true by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.

(* Width-general PMP TOR-entry-0 RAM grant: the W-byte access at [a] fully
   inside [0, pmpaddr0*4) matches (W = 4 / 2 for fetch, 8 for the PTE read). *)
Lemma ram_pmp_match_w (a pmpaddr0 : mword 64) (w : Z) :
  0 < w ->
  uint (to_bits 64 w) = w ->
  ram_base <= uint a ->
  uint a + w <= ram_base + ram_size ->
  ram_base + ram_size <= uint pmpaddr0 * 4 ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint pmpaddr0) 4)
    (uint a) (uint (to_bits 64 w)) = PMP_Match.
Proof.
  intros Hw0 Hwv Hlo Hfit Hcov.
  assert (Hz : uint (zeros' 64 : mword 64) = 0) by (vm_compute; reflexivity).
  rewrite Hz. rewrite Z.mul_0_l. rewrite Hwv.
  apply pmpRangeMatch_full; unfold ram_base, ram_size in *; lia.
Qed.

(* [uint_pa_add] lives in RiscvExtras.v (one home): the offset-[j] byte of an
   access is at [uint a + j] whenever the sum does not wrap. *)

(* ===================================================================== *)
(* 3. The 8-byte checked PTE read + TLB lookup miss (from SmodeCore).    *)
(* ===================================================================== *)

Lemma exec_read_pte_S (addr : mword 64) (region : PMA_Region) (w : bv 64) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 8)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
  exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 8) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (read_pte (Physaddr addr) 8) s = Some (Ok w, s).
Proof.
  intros HA Hord Hrange HR Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes.
  assert (Hchk : exec (checked_mem_read (Load PageTableEntry) PBMT_PMA Supervisor (Physaddr addr) 8 false false false false)
                   s = Some (Ok (w, default_meta), s)).
  { unfold checked_mem_read.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
    2:{ unfold phys_access_check.
        rewrite (exec_bind_Some _ _ _ _ _
                   (exec_pmpCheck_supervisor_grant_load addr 8 s HA Hord Hrange HR)).
        cbn match.
        rewrite (exec_bind_Some _ _ _ _ _
                   (_ : exec (pmaCheck (Physaddr addr) 8 (Load PageTableEntry) PBMT_PMA false) s
                        = Some (None, s))).
        2:{ unfold pmaCheck.
            rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
            rewrite Hmatch.
            destruct region as [rbase rsize rattr rdtree].
            cbn [PMA_Region_attributes] in Hread |- *.
            rewrite Halign. cbn [Riscv.rv64d.not negb].
            rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
            cbn match beta.
            change (assert_exp' true "sys/mem.sail:105.61-105.62" >>=
                    (fun _ : true = true => returnM (PMA_supports_pte_read (override_PMA rattr PBMT_PMA))))
              with (returnM (PMA_supports_pte_read (override_PMA rattr PBMT_PMA)) : M bool).
            rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
            rewrite Hread. cbn match.
            apply exec_returnM. }
        cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (within_mmio_readable (Physaddr addr) 8) s = Some (false, s))).
    2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
        rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
        rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
        rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (read_kind_of_flags _ _ _) s = Some (rv64d_types.Read_plain, s))).
    2:{ unfold read_kind_of_flags. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_plain_8 addr w s Hdev Hbytes)).
    apply exec_returnM. }
  unfold read_pte, mem_read_priv.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (mem_read_priv_meta _ _ _ _ 8 _ _ _ _) s = Some (Ok (w, default_meta), s))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_bind_Some _ _ _ _ _ Hchk).
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

Lemma exec_lookup_TLB_miss (vpn : mword 27) (asid : mword 16) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
  register_lookup tlb s.(sregs) = tlbvec ->
  vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None ->
  exec (lookup_TLB 39 asid vpn) s = Some (None, s).
Proof.
  intros Htlb Hvec.
  unfold lookup_TLB.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
  rewrite Htlb. rewrite Hvec. apply exec_returnm.
Qed.

(* Hash-collision MISS: the fetch's slot holds a NON-matching entry (e.g.  *)
(* the UART 4KB leaf, or -- under the eventual all-4KB kernel -- a          *)
(* different RAM page's leaf).  The model's [match_TLB_Entry] rejects it,   *)
(* so [lookup_TLB] returns a miss just as for an empty slot, and the walk   *)
(* proceeds identically, overwriting the slot with the fresh entry.         *)
Lemma exec_lookup_TLB_nomatch_s (vpn : mword 27) (asid : mword 16) (ent' : TLB_Entry)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
  register_lookup tlb s.(sregs) = tlbvec ->
  vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent' ->
  match_TLB_Entry ent' asid (sign_extend' (57 - 12) vpn) = false ->
  exec (lookup_TLB 39 asid vpn) s = Some (None, s).
Proof.
  intros Htlb Hvec Hnm.
  unfold lookup_TLB.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
  rewrite Htlb. rewrite Hvec. rewrite Hnm. apply exec_returnm.
Qed.

