(* MemData4.v -- mode-neutral width-4 DATA memory leaf lemmas.

   The width-4 physical read/write core, factored out of the per-mode
   (S/M/U) leaf files: the pmaCheck grants, the checked_mem_read /
   checked_mem_write / mem_read / mem_write_value chains, and the
   register-generic vmem_read / vmem_write / execute_{LOAD,STORE} tower.

   Everything here is privilege-GENERIC: the only place the access
   privilege enters is the pmpCheck grant, which each caller supplies as a
   hypothesis (Supervisor / User / Machine grant).  The address translation
   and effective-address transform are likewise abstracted as hypotheses
   (Htr / Htea), so the same tower serves every mode.  State-preserving
   form (no A/D write-back): the translate hypothesis returns the same
   state, which holds whenever the PTE A/D bits are already set. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import WpGpr WpLoad.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Pure width-4 leaf helpers (mode-neutral).                             *)
(* ===================================================================== *)

Lemma avi0_mul4 (a : mword 64) : add_vec_int a (0 * 4) = a.
Proof. change (0 * 4) with 0. apply avi0. Qed.

Lemma exec_split_misaligned_aligned_4 (vaddr : virtaddr) s :
  is_aligned_vaddr vaddr 4 = true ->
  exec (split_misaligned vaddr 4) s = Some ((1, 4), s).
Proof. intro H. unfold split_misaligned. rewrite H. cbn [orb]. apply exec_returnm. Qed.

Lemma data2_id_4 (v : mword 32) :
  update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v = v.
Proof.
  apply bv_eq. unfold update_subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.update_slice, MachineWord.MachineWord.slice.
  erewrite bv_concat_unsigned by (cbn; lia).
  erewrite bv_concat_unsigned by (cbn; lia).
  rewrite !bv_unsigned_N_0.
  rewrite Z.shiftl_0_l. rewrite Z.shiftl_0_r. rewrite Z.lor_0_r. rewrite Z.lor_0_l.
  reflexivity.
Qed.

Lemma exec_pmaCheck_ram_load_4 (addr : mword 64) (pbmt : page_based_mem_type)
      (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (pmaCheck (Physaddr addr) 4 (Load Data) pbmt false) s = Some (None, s).
Proof.
  intros Hmatch Halign Hread.
  unfold pmaCheck.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hread |- *.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
  cbn match beta.
  change (assert_exp' true "sys/mem.sail:103.61-103.62" >>=
          (fun _ : true = true => returnM (PMA_readable (override_PMA rattr pbmt))))
    with (returnM (PMA_readable (override_PMA rattr pbmt)) : M bool).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite Hread. cbn match.
  apply exec_returnM.
Qed.

Lemma exec_pmaCheck_ram_store_4 (addr : mword 64) (pbmt : page_based_mem_type)
      (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (pmaCheck (Physaddr addr) 4 (Store Data) pbmt false) s = Some (None, s).
Proof.
  intros Hmatch Halign Hwrite.
  unfold pmaCheck.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hwrite |- *.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
  cbn match beta.
  change (assert_exp' true "sys/mem.sail:106.61-106.62" >>=
          (fun _ : true = true => returnM (PMA_writable (override_PMA rattr pbmt))))
    with (returnM (PMA_writable (override_PMA rattr pbmt)) : M bool).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite Hwrite. cbn match.
  apply exec_returnM.
Qed.

Lemma exec_write_ram_plain_4 (addr : mword 64) (data : bv 32) s :
  dev_addr addr = false ->
  exec (write_ram rv64d_types.Write_plain (Physaddr addr) 4 data tt) s
  = Some (true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev)).
Proof.
  intros Hdev.
  unfold write_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_write. cbn beta zeta iota match.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  cbn match.
  rewrite exec_MemWrite; last exact Hdev.
  reflexivity.
Qed.

Lemma exec_mem_write_ea_4 (addr : mword 64) s :
  exec (mem_write_ea (Physaddr addr) 4 false false false) s = Some (Ok tt, s).
Proof.
  unfold mem_write_ea. cbn [orb andb].
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (write_kind_of_flags false false false) s = Some (rv64d_types.Write_plain, s))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
  apply exec_returnM.
Qed.

(* ===================================================================== *)
(* effectivePrivilege below Machine (MPRV clear): identity.  Generic.    *)
(* ===================================================================== *)

Lemma exec_effectivePrivilege_load_nm (m : mword 64) (pr : Privilege) s :
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  exec (effectivePrivilege (Load Data) m pr) s = Some (pr, s).
Proof.
  intro H. unfold effectivePrivilege. cbn [generic_neq generic_eq].
  rewrite H. cbn [andb]. apply exec_returnm.
Qed.

Lemma exec_effectivePrivilege_store_nm (m : mword 64) (pr : Privilege) s :
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  exec (effectivePrivilege (Store Data) m pr) s = Some (pr, s).
Proof.
  intro H. unfold effectivePrivilege. cbn [generic_neq generic_eq].
  rewrite H. cbn [andb]. apply exec_returnm.
Qed.

(* ===================================================================== *)
(* Privilege-generic checked_mem_read / mem_read at width 4 (Load Data). *)
(* The pmpCheck grant is supplied by the caller (Hpmp), which is the      *)
(* only privilege-dependent step.                                         *)
(* ===================================================================== *)

Lemma exec_checked_mem_read_ram_load_4 (p : Privilege) (pbmt : page_based_mem_type)
      (addr : mword 64) (region : PMA_Region) (w : bv 32) s :
  exec (pmpCheck (Physaddr addr) 4 (Load Data) p) s = Some (None, s) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (Load Data) pbmt p (Physaddr addr) 4 false false false false)
       s = Some (Ok (w, default_meta), s).
Proof.
  intros Hpmp Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes.
  unfold checked_mem_read.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ Hpmp). cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_load_4 addr pbmt region s Hmatch Halign Hread)).
      cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_readable (Physaddr addr) 4) s = Some (false, s))).
  2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (read_kind_of_flags _ _ _) s = Some (rv64d_types.Read_plain, s))).
  2:{ unfold read_kind_of_flags. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_plain_4 addr w s Hdev Hbytes)).
  apply exec_returnM.
Qed.

Lemma exec_mem_read_load_4 (p : Privilege) (pbmt : page_based_mem_type)
      (addr : mword 64) (region : PMA_Region) (w : bv 32) (m : mword 64) s :
  exec (pmpCheck (Physaddr addr) 4 (Load Data) p) s = Some (None, s) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = p ->
  exec (mem_read (Load Data) pbmt (Physaddr addr) 4 false false false)
       s = Some (Ok w, s).
Proof.
  intros Hpmp Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes Hms Hmprv Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv. rewrite Hms.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_load_nm m p s Hmprv)).
  unfold mem_read_priv.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (mem_read_priv_meta _ _ _ _ 4 _ _ _ _) s = Some (Ok (w, default_meta), s))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (checked_mem_read _ _ _ _ 4 _ _ _ _) s = Some (Ok (w, default_meta), s))).
      2:{ cbn match. apply exec_checked_mem_read_ram_load_4 with (p := p) (region := region); assumption. }
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

(* ===================================================================== *)
(* Privilege-generic checked_mem_write / mem_write_value at width 4.      *)
(* ===================================================================== *)

Lemma exec_checked_mem_write_ram_4 (p : Privilege) (pbmt : page_based_mem_type)
      (addr : mword 64) (region : PMA_Region) (data : bv 32) s :
  exec (pmpCheck (Physaddr addr) 4 (Store Data) p) s = Some (None, s) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  exec (checked_mem_write (Physaddr addr) 4 data (Store Data) pbmt p tt false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev)).
Proof.
  intros Hpmp Hmatch Halign Hwrite Hc Hsig Hh Hdev.
  unfold checked_mem_write.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ Hpmp). cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_store_4 addr pbmt region s Hmatch Halign Hwrite)).
      cbn match. apply exec_returnM. }
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_writable (Physaddr addr) 4) s = Some (false, s))).
  2:{ unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (write_kind_of_flags false false false) s = Some (rv64d_types.Write_plain, s))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_write_ram_plain_4 addr data s Hdev)).
  apply exec_returnM.
Qed.

Lemma exec_mem_write_value_4 (p : Privilege) (pbmt : page_based_mem_type)
      (addr : mword 64) (region : PMA_Region) (data : bv 32) (m : mword 64) s :
  exec (pmpCheck (Physaddr addr) 4 (Store Data) p) s = Some (None, s) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = p ->
  exec (mem_write_value (Physaddr addr) 4 data (Store Data) pbmt false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev)).
Proof.
  intros Hpmp Hmatch Halign Hwrite Hc Hsig Hh Hdev Hms Hmprv Hpriv.
  unfold mem_write_value, mem_write_value_meta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv. rewrite Hms.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_store_nm m p s Hmprv)).
  unfold mem_write_value_priv_meta. cbn [orb andb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_checked_mem_write_ram_4 p pbmt addr region data s Hpmp Hmatch Halign Hwrite Hc Hsig Hh Hdev)).
  cbn match. unfold mem_write_callback. apply exec_returnm.
Qed.

(* ===================================================================== *)
(* Generic width-4 LOAD tower (state-preserving, privilege- and          *)
(* sign-generic).  Translate (Htr) and effective-address transform       *)
(* (Htea) are abstracted, so any mode instantiates by supplying its own.  *)
(* ===================================================================== *)

Section GenVMemReadAddr4.
  Variable p : Privilege.
  Variable a : mword 64.
  Variable v : bv 32.
  Variable region : PMA_Region.
  Variable s : mstate.
  Variable pa : mword 64.
  Let data2 : mword (4*1*8) :=
    update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = p.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (Load Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis Hpmp : exec (pmpCheck (Physaddr pa) 4 (Load Data) p) s = Some (None, s).
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hdev : dev_addr pa = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

  Lemma exec_vmem_read_addr_4 :
    exec (vmem_read_addr (Virtaddr a) 4 (Load Data) false false false) s
      = Some (Ok data2, s).
  Proof.
    unfold vmem_read_addr.
    rewrite exec_catch_early_return.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    assert (Hinner : execR (returnR (result (mword (4 * 8)) ExecutionResult) tt >>
                            liftR (split_misaligned (Virtaddr a) 4)) s = Some (inr (1, 4), s)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_4 (Virtaddr a) s Halign). reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hinner).
    rewrite misaligned_order_1.
    match goal with
    | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
      assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (data2, true, 0), s))
    end.
    { eapply execR_untilMT_1.
      - reflexivity.
      - cbn match.
        assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _ Hass).
        rewrite (execR_liftR_seq _ _ _ _ _ Htr).
        cbn [bits_of_virtaddr] in *. cbn match.
        match goal with
        | |- execR (Defs.bind ?mrm ?post) s = _ =>
          assert (Hmrm : execR mrm s = Some (inr data2, s))
        end.
        { rewrite (execR_liftR_seq _ _ _ _ _
            (exec_mem_read_load_4 p PBMT_PMA pa region v (register_lookup mstatus s.(sregs)) s
               Hpmp Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes eq_refl Hmprv Hcp)).
          cbn match.
          rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
          rewrite autocast_id. apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hmrm).
        cbn. apply execR_returnR_fwd.
      - apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu).
    cbn. rewrite autocast_id. reflexivity.
  Qed.
End GenVMemReadAddr4.

(* ===================================================================== *)
(* Generic width-4 LOAD tower, WALK form: the data translate CHANGES      *)
(* state s -> s' (a cold-TLB walk that fills the entry).  Everything after *)
(* the translate is tlb-insensitive, so the read runs at s' and the tower  *)
(* returns [Ok data2] at s'.  Twin of [exec_vmem_read_addr_4].            *)
(* ===================================================================== *)
Section GenVMemReadAddr4Walk.
  Variable p : Privilege.
  Variable a : mword 64.
  Variable v : bv 32.
  Variable region : PMA_Region.
  Variable s s' : mstate.
  Variable pa : mword 64.
  Let data2 : mword (4*1*8) :=
    update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (Load Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hcp : register_lookup cur_privilege s'.(sregs) = p.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis Hpmp : exec (pmpCheck (Physaddr pa) 4 (Load Data) p) s' = Some (None, s').
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s'.(mem) !! (pa_add pa j) = Some (nth_byte v j).

  Lemma exec_vmem_read_addr_4_walk :
    exec (vmem_read_addr (Virtaddr a) 4 (Load Data) false false false) s
      = Some (Ok data2, s').
  Proof.
    unfold vmem_read_addr.
    rewrite exec_catch_early_return.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    assert (Hinner : execR (returnR (result (mword (4 * 8)) ExecutionResult) tt >>
                            liftR (split_misaligned (Virtaddr a) 4)) s = Some (inr (1, 4), s)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_4 (Virtaddr a) s Halign). reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hinner).
    rewrite misaligned_order_1.
    match goal with
    | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
      assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (data2, true, 0), s'))
    end.
    { eapply execR_untilMT_1.
      - reflexivity.
      - cbn match.
        assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _ Hass).
        rewrite (execR_liftR_seq _ _ _ _ _ Htr).
        cbn [bits_of_virtaddr] in *. cbn match.
        match goal with
        | |- execR (Defs.bind ?mrm ?post) s' = _ =>
          assert (Hmrm : execR mrm s' = Some (inr data2, s'))
        end.
        { rewrite (execR_liftR_seq _ _ _ _ _
            (exec_mem_read_load_4 p PBMT_PMA pa region v (register_lookup mstatus s'.(sregs)) s'
               Hpmp Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes eq_refl Hmprv Hcp)).
          cbn match.
          rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s')).
          rewrite autocast_id. apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hmrm).
        cbn. apply execR_returnR_fwd.
      - apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu).
    cbn. rewrite autocast_id. reflexivity.
  Qed.
End GenVMemReadAddr4Walk.

Section GenVMemRead4.
  Variable p : Privilege.
  Variable rs1 : mword 5.
  Variable offset : mword 64.
  Variable a : mword 64.
  Variable v : bv 32.
  Variable region : PMA_Region.
  Variable s : mstate.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Variable pa : mword 64.
  Let data2 : mword (4*1*8) :=
    update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Load Data)) s = Some (Virtaddr a, s).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = p.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (Load Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis Hpmp : exec (pmpCheck (Physaddr pa) 4 (Load Data) p) s = Some (None, s).
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hdev : dev_addr pa = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

  Lemma exec_vmem_read_4_gpr :
    exec (vmem_read (Regidx rs1) offset 4 (Load Data) false false false) s = Some (Ok data2, s).
  Proof.
    unfold vmem_read. rewrite exec_catch_early_return.
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Load Data) 4) s
                   = Some (Ext_DataAddr_OK (Virtaddr a), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Load Data) 4 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Htea).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a) s)).
    rewrite execR_liftR.
    rewrite (exec_vmem_read_addr_4 p a v region s pa Halign Hcp Hmprv Htr Hpmp Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes).
    reflexivity.
  Qed.
End GenVMemRead4.

Section GenVMemRead4Walk.
  Variable p : Privilege.
  Variable rs1 : mword 5.
  Variable offset : mword 64.
  Variable a : mword 64.
  Variable v : bv 32.
  Variable region : PMA_Region.
  Variable s s' : mstate.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Variable pa : mword 64.
  Let data2 : mword (4*1*8) :=
    update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Load Data)) s = Some (Virtaddr a, s).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (Load Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hcp : register_lookup cur_privilege s'.(sregs) = p.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis Hpmp : exec (pmpCheck (Physaddr pa) 4 (Load Data) p) s' = Some (None, s').
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s'.(mem) !! (pa_add pa j) = Some (nth_byte v j).

  Lemma exec_vmem_read_4_gpr_walk :
    exec (vmem_read (Regidx rs1) offset 4 (Load Data) false false false) s = Some (Ok data2, s').
  Proof.
    unfold vmem_read. rewrite exec_catch_early_return.
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Load Data) 4) s
                   = Some (Ext_DataAddr_OK (Virtaddr a), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Load Data) 4 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Htea).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a) s)).
    rewrite execR_liftR.
    rewrite (exec_vmem_read_addr_4_walk p a v region s s' pa Halign Htr Hcp Hmprv Hpmp Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes).
    reflexivity.
  Qed.
End GenVMemRead4Walk.

Section GenExecLoad4.
  Variable p : Privilege.
  Variable is_unsigned : bool.
  Variable rs1 rd : mword 5.
  Variable imm : mword 12.
  Variable a : mword 64.
  Variable v : bv 32.
  Variable region : PMA_Region.
  Variable s : mstate.
  Let offset := sign_extend' 64 imm.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Variable pa : mword 64.
  Let data2 : mword (4*1*8) :=
    update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v.
  Hypothesis Hrd : uint rd <> 0.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Load Data)) s = Some (Virtaddr a, s).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = p.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (Load Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis Hpmp : exec (pmpCheck (Physaddr pa) 4 (Load Data) p) s = Some (None, s).
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hdev : dev_addr pa = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

  Lemma exec_execute_LOAD_4_gpr :
    exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4))) s
      = Some (RETIRE_SUCCESS,
              set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (extend_value is_unsigned data2))).
  Proof.
    change (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4)))
      with (execute_LOAD imm (Regidx rs1) (Regidx rd) is_unsigned 4).
    unfold execute_LOAD.
    replace (4 <=? xlen_bytes) with true by (vm_compute; reflexivity).
    assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _
      (exec_vmem_read_4_gpr p rs1 offset a v region s pa Htea Halign Hcp Hmprv Htr Hpmp Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes)).
    cbn match.
    assert (Hw : exec (wX_bits (Regidx rd) (extend_value is_unsigned data2)) s
                 = Some (tt, set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg (extend_value is_unsigned data2)))).
    { rewrite (exec_wX_bits_gpr rd (extend_value is_unsigned data2) s).
      rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity. }
    rewrite (exec_bind0_Some _ _ _ _ _ Hw).
    apply exec_returnM.
  Qed.
End GenExecLoad4.

Section GenExecLoad4Walk.
  Variable p : Privilege.
  Variable is_unsigned : bool.
  Variable rs1 rd : mword 5.
  Variable imm : mword 12.
  Variable a : mword 64.
  Variable v : bv 32.
  Variable region : PMA_Region.
  Variable s s' : mstate.
  Let offset := sign_extend' 64 imm.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Variable pa : mword 64.
  Let data2 : mword (4*1*8) :=
    update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v.
  Hypothesis Hrd : uint rd <> 0.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Load Data)) s = Some (Virtaddr a, s).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (Load Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hcp : register_lookup cur_privilege s'.(sregs) = p.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis Hpmp : exec (pmpCheck (Physaddr pa) 4 (Load Data) p) s' = Some (None, s').
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s'.(mem) !! (pa_add pa j) = Some (nth_byte v j).

  Lemma exec_execute_LOAD_4_gpr_walk :
    exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4))) s
      = Some (RETIRE_SUCCESS,
              set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (extend_value is_unsigned data2))).
  Proof.
    change (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4)))
      with (execute_LOAD imm (Regidx rs1) (Regidx rd) is_unsigned 4).
    unfold execute_LOAD.
    replace (4 <=? xlen_bytes) with true by (vm_compute; reflexivity).
    assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _
      (exec_vmem_read_4_gpr_walk p rs1 offset a v region s s' pa Htea Halign Htr Hcp Hmprv Hpmp Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes)).
    cbn match.
    assert (Hw : exec (wX_bits (Regidx rd) (extend_value is_unsigned data2)) s'
                 = Some (tt, set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg (extend_value is_unsigned data2)))).
    { rewrite (exec_wX_bits_gpr rd (extend_value is_unsigned data2) s').
      rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity. }
    rewrite (exec_bind0_Some _ _ _ _ _ Hw).
    apply exec_returnM.
  Qed.
End GenExecLoad4Walk.

(* ===================================================================== *)
(* Generic width-4 STORE tower (state-preserving, privilege-generic).     *)
(* ===================================================================== *)

Section GenVMemWriteAddr4.
  Variable p : Privilege.
  Variable a : mword 64.
  Variable data : bv 32.
  Variable region : PMA_Region.
  Variable s : mstate.
  Variable pa : mword 64.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = p.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis Hpmp : exec (pmpCheck (Physaddr pa) 4 (Store Data) p) s = Some (None, s).
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_vmem_write_addr_4 :
    exec (vmem_write_addr (Virtaddr a) 4 data (Store Data) false false false) s
      = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) pa 4 data) s.(mdev)).
  Proof.
    unfold vmem_write_addr.
    rewrite exec_catch_early_return.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    assert (Hinner : execR (returnR (result bool ExecutionResult) tt >>
                            liftR (split_misaligned (Virtaddr a) 4)) s = Some (inr (1, 4), s)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_4 (Virtaddr a) s Halign). reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hinner).
    rewrite misaligned_order_1.
    match goal with
    | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
      assert (Hu : execR (Defs.untilMT vs m c b) s
                   = Some (inr (true, 0%Z, true), MState s.(sregs) (write_bytes s.(mem) pa 4 data) s.(mdev)))
    end.
    { eapply execR_untilMT_1.
      - reflexivity.
      - cbn match.
        assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _ Hass).
        rewrite (execR_liftR_seq _ _ _ _ _ Htr).
        cbn [bits_of_virtaddr] in *. cbn match.
        assert (Hsc : exec (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51") s
                      = Some (tt, s)) by reflexivity.
        assert (Hscm : execR (Defs.liftR (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51")
                              : Defs.monadR (result bool ExecutionResult) exception unit) s = Some (inr tt, s))
          by (rewrite execR_liftR; rewrite Hsc; reflexivity).
        match goal with
        | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
            assert (Hwrloop : execR (Defs.bind0 (Defs.liftR asrt) Nbody) s
                             = Some (inr true, MState s.(sregs) (write_bytes s.(mem) pa 4 data) s.(mdev)))
        end.
        { match goal with
          | |- execR (Defs.bind0 _ ?Nbody) s = _ => set (NN := Nbody)
          end.
          rewrite (execR_bind0_Some _ _ _ _ Hscm).
          unfold NN; clear NN.
          match goal with
          | |- execR (match _ as x in bool return @?P x with | true => _ | false => ?B end) ?ss = ?R =>
              change (execR B ss = R)
          end.
          rewrite (execR_liftR_seq _ _ _ _ _ (exec_mem_write_ea_4 pa s)).
          cbn match.
          match goal with
          | |- context [ mem_write_value ?pp 4 ?D (Store Data) ?pb false false false ] =>
              replace D with data
          end.
          2: { symmetry.
               change (4*(0+1)*8-1) with 31. change (4*0*8) with 0. change (4*8) with 32.
               change (31 - 0 + 1) with 32. rewrite autocast_id.
               unfold subrange_vec_dec. change (31 - 0 + 1) with 32. rewrite autocast_id.
               unfold to_word_idx, to_word, get_word, MachineWord.slice.
               rewrite MachineWord.cast_idx_refl.
               apply bv_eq. rewrite bv_extract_unsigned.
               change (Z.of_N (MachineWord.Z_idx 0)) with 0. rewrite Z.shiftr_0_r.
               apply bv_wrap_bv_unsigned. }
          rewrite (execR_liftR_seq _ _ _ _ _
            (exec_mem_write_value_4 p PBMT_PMA pa region data
               (register_lookup mstatus s.(sregs)) s Hpmp Hmatch Hpalign Hwrite Hc Hsig Hh Hdev eq_refl Hmprv Hcp)).
          cbn match.
          apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hwrloop).
        cbn.
        apply execR_returnR_fwd.
      - apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu).
    cbn. reflexivity.
  Qed.
End GenVMemWriteAddr4.

Section GenVMemWrite4.
  Variable p : Privilege.
  Variable rs1 : mword 5.
  Variable offset : mword 64.
  Variable a : mword 64.
  Variable data : bv 32.
  Variable region : PMA_Region.
  Variable s : mstate.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Variable pa : mword 64.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Store Data)) s = Some (Virtaddr a, s).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = p.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis Hpmp : exec (pmpCheck (Physaddr pa) 4 (Store Data) p) s = Some (None, s).
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_vmem_write_4_gpr :
    exec (vmem_write (Regidx rs1) offset 4 data (Store Data) false false false) s
      = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) pa 4 data) s.(mdev)).
  Proof.
    unfold vmem_write. rewrite exec_catch_early_return.
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Store Data) 4) s
                   = Some (Ext_DataAddr_OK (Virtaddr a), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) 4 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Htea).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a) s)).
    rewrite execR_liftR.
    rewrite (exec_vmem_write_addr_4 p a data region s pa Halign Hcp Hmprv Htr Hpmp Hmatch Hpalign Hwrite Hc Hsig Hh Hdev).
    reflexivity.
  Qed.
End GenVMemWrite4.

Section GenExecStore4.
  Variable p : Privilege.
  Variable rs2 rs1 : mword 5.
  Variable imm : mword 12.
  Variable a : mword 64.
  Variable region : PMA_Region.
  Variable s : mstate.
  Let offset := sign_extend' 64 imm.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Variable pa : mword 64.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Store Data)) s = Some (Virtaddr a, s).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = p.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis Hpmp : exec (pmpCheck (Physaddr pa) 4 (Store Data) p) s = Some (None, s).
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_execute_STORE_4_gpr :
    exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s
      = Some (RETIRE_SUCCESS,
              MState s.(sregs) (write_bytes s.(mem) pa 4
                (autocast (T := mword) (subrange_vec_dec vrs2 (Z.sub (Z.mul 4 8) 1) 0) : mword 32)) s.(mdev)).
  Proof.
    change (execute (STORE (imm, Regidx rs2, Regidx rs1, 4)))
      with (execute_STORE imm (Regidx rs2) (Regidx rs1) 4).
    unfold execute_STORE.
    replace (4 <=? xlen_bytes) with true by (vm_compute; reflexivity).
    assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:320.28-320.29" : M (true = true)) s
                   = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _
      (exec_vmem_write_4_gpr p rs1 offset a _ region s pa Htea Halign Hcp Hmprv Htr Hpmp Hmatch Hpalign Hwrite Hc Hsig Hh Hdev)).
    cbn match.
    apply exec_returnM.
  Qed.
End GenExecStore4.

(* ===================================================================== *)
(* Generic width-4 STORE tower, DATA-TLB-MISS form.  The translate walks   *)
(* and fills, moving s -> s'; the store body then writes at s'.            *)
(* ===================================================================== *)

Section GenVMemWriteAddr4Walk.
  Variable p : Privilege.
  Variable a : mword 64.
  Variable data : bv 32.
  Variable region : PMA_Region.
  Variable s s' : mstate.
  Variable pa : mword 64.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hcp : register_lookup cur_privilege s'.(sregs) = p.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis Hpmp : exec (pmpCheck (Physaddr pa) 4 (Store Data) p) s' = Some (None, s').
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_vmem_write_addr_4_walk :
    exec (vmem_write_addr (Virtaddr a) 4 data (Store Data) false false false) s
      = Some (Ok true, MState s'.(sregs) (write_bytes s'.(mem) pa 4 data) s'.(mdev)).
  Proof.
    unfold vmem_write_addr.
    rewrite exec_catch_early_return.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    assert (Hinner : execR (returnR (result bool ExecutionResult) tt >>
                            liftR (split_misaligned (Virtaddr a) 4)) s = Some (inr (1, 4), s)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_4 (Virtaddr a) s Halign). reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hinner).
    rewrite misaligned_order_1.
    match goal with
    | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
      assert (Hu : execR (Defs.untilMT vs m c b) s
                   = Some (inr (true, 0%Z, true), MState s'.(sregs) (write_bytes s'.(mem) pa 4 data) s'.(mdev)))
    end.
    { eapply execR_untilMT_1.
      - reflexivity.
      - cbn match.
        assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _ Hass).
        rewrite (execR_liftR_seq _ _ _ _ _ Htr).
        cbn [bits_of_virtaddr] in *. cbn match.
        assert (Hsc : exec (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51") s'
                      = Some (tt, s')) by reflexivity.
        assert (Hscm : execR (Defs.liftR (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51")
                              : Defs.monadR (result bool ExecutionResult) exception unit) s' = Some (inr tt, s'))
          by (rewrite execR_liftR; rewrite Hsc; reflexivity).
        match goal with
        | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
            assert (Hwrloop : execR (Defs.bind0 (Defs.liftR asrt) Nbody) s'
                             = Some (inr true, MState s'.(sregs) (write_bytes s'.(mem) pa 4 data) s'.(mdev)))
        end.
        { match goal with
          | |- execR (Defs.bind0 _ ?Nbody) s' = _ => set (NN := Nbody)
          end.
          rewrite (execR_bind0_Some _ _ _ _ Hscm).
          unfold NN; clear NN.
          match goal with
          | |- execR (match _ as x in bool return @?P x with | true => _ | false => ?B end) ?ss = ?R =>
              change (execR B ss = R)
          end.
          rewrite (execR_liftR_seq _ _ _ _ _ (exec_mem_write_ea_4 pa s')).
          cbn match.
          match goal with
          | |- context [ mem_write_value ?pp 4 ?D (Store Data) ?pb false false false ] =>
              replace D with data
          end.
          2: { symmetry.
               change (4*(0+1)*8-1) with 31. change (4*0*8) with 0. change (4*8) with 32.
               change (31 - 0 + 1) with 32. rewrite autocast_id.
               unfold subrange_vec_dec. change (31 - 0 + 1) with 32. rewrite autocast_id.
               unfold to_word_idx, to_word, get_word, MachineWord.slice.
               rewrite MachineWord.cast_idx_refl.
               apply bv_eq. rewrite bv_extract_unsigned.
               change (Z.of_N (MachineWord.Z_idx 0)) with 0. rewrite Z.shiftr_0_r.
               apply bv_wrap_bv_unsigned. }
          rewrite (execR_liftR_seq _ _ _ _ _
            (exec_mem_write_value_4 p PBMT_PMA pa region data
               (register_lookup mstatus s'.(sregs)) s' Hpmp Hmatch Hpalign Hwrite Hc Hsig Hh Hdev eq_refl Hmprv Hcp)).
          cbn match.
          apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hwrloop).
        cbn.
        apply execR_returnR_fwd.
      - apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu).
    cbn. reflexivity.
  Qed.
End GenVMemWriteAddr4Walk.

Section GenVMemWrite4Walk.
  Variable p : Privilege.
  Variable rs1 : mword 5.
  Variable offset : mword 64.
  Variable a : mword 64.
  Variable data : bv 32.
  Variable region : PMA_Region.
  Variable s s' : mstate.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Variable pa : mword 64.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Store Data)) s = Some (Virtaddr a, s).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hcp : register_lookup cur_privilege s'.(sregs) = p.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis Hpmp : exec (pmpCheck (Physaddr pa) 4 (Store Data) p) s' = Some (None, s').
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_vmem_write_4_gpr_walk :
    exec (vmem_write (Regidx rs1) offset 4 data (Store Data) false false false) s
      = Some (Ok true, MState s'.(sregs) (write_bytes s'.(mem) pa 4 data) s'.(mdev)).
  Proof.
    unfold vmem_write. rewrite exec_catch_early_return.
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Store Data) 4) s
                   = Some (Ext_DataAddr_OK (Virtaddr a), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) 4 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Htea).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a) s)).
    rewrite execR_liftR.
    rewrite (exec_vmem_write_addr_4_walk p a data region s s' pa Halign Htr Hcp Hmprv Hpmp Hmatch Hpalign Hwrite Hc Hsig Hh Hdev).
    reflexivity.
  Qed.
End GenVMemWrite4Walk.

Section GenExecStore4Walk.
  Variable p : Privilege.
  Variable rs2 rs1 : mword 5.
  Variable imm : mword 12.
  Variable a : mword 64.
  Variable region : PMA_Region.
  Variable s s' : mstate.
  Let offset := sign_extend' 64 imm.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Variable pa : mword 64.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Store Data)) s = Some (Virtaddr a, s).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hcp : register_lookup cur_privilege s'.(sregs) = p.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis Hpmp : exec (pmpCheck (Physaddr pa) 4 (Store Data) p) s' = Some (None, s').
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_execute_STORE_4_gpr_walk :
    exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s
      = Some (RETIRE_SUCCESS,
              MState s'.(sregs) (write_bytes s'.(mem) pa 4
                (autocast (T := mword) (subrange_vec_dec vrs2 (Z.sub (Z.mul 4 8) 1) 0) : mword 32)) s'.(mdev)).
  Proof.
    change (execute (STORE (imm, Regidx rs2, Regidx rs1, 4)))
      with (execute_STORE imm (Regidx rs2) (Regidx rs1) 4).
    unfold execute_STORE.
    replace (4 <=? xlen_bytes) with true by (vm_compute; reflexivity).
    assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:320.28-320.29" : M (true = true)) s
                   = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _
      (exec_vmem_write_4_gpr_walk p rs1 offset a _ region s s' pa Htea Halign Htr Hcp Hmprv Hpmp Hmatch Hpalign Hwrite Hc Hsig Hh Hdev)).
    cbn match.
    apply exec_returnM.
  Qed.
End GenExecStore4Walk.
