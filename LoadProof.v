(* ====================================================================== *)
(* LoadProof.v -- DEV: proving the 8-byte execute_LOAD reduction            *)
(* (the `Hexecload_gen` frontier of forward_exec_ld).                       *)
(* Built bottom-up; inspected interactively with coqtop (fast: .vo load ~1s)*)
(*                                                                         *)
(* PROVEN LEAVES (this file, compiles green):                               *)
(*   - rX_x2 / run_rX_x2 / exec_rX_x2 / exec_rX_bits_x2  (read sp)          *)
(*   - exec_ext_data_get_addr_x2  (vaddr = X(sp)+offset)                    *)
(*   - exec_effectivePrivilege_load  (= Machine, given MPRV=0)             *)
(*   - exec_split_misaligned_aligned (= (1,8) for 8-aligned vaddr)         *)
(*   - misaligned_order_1           (= (0,0,step))                          *)
(*                                                                         *)
(* REMAINING FRONTIER (heavy; see notes at end):                            *)
(*   - get_pmlen (Load Data) Machine = 0   (needs PMM-config bits = 0)      *)
(*   - transform_effective_address = identity (assemble above + Bare +     *)
(*     pm_transform_PA at pmlen=0); get_transformed_data_addr              *)
(*   - translateAddr (Load Data) identity   (Load-access twin of fetch's)  *)
(*   - 8-byte mem_read / checked_mem_read / read_ram (= read_bytes _ 8)     *)
(*   - untilMT one-iteration reduction (Acc (Zwf 0), like currentlyEnabled) *)
(*     + update_subrange_vec_dec dependent width (mword 8*1*8 = mword 64)   *)
(*   - assemble vmem_read_addr -> vmem_read (double catch_early_return/MR)  *)
(*     -> execute_LOAD; then wire into forward_exec_ld (memory ownership).  *)
(* ====================================================================== *)
From Stdlib Require Import Lia.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import RiscvModelBytes.
Require Import RiscvAddTryStep.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.

Local Open Scope Z_scope.
Import Defs.

(* NOTE: extend_value false data (width 8) = sign_extend' 64 data; we carry  *)
(* it verbatim in the conclusion (no need to simplify to `data`).            *)

(* ---------------------------------------------------------------------- *)
(* bv/MachineWord identity lemmas. mword n = bv (Z_idx n) and to_word/      *)
(* get_word are the identity, so these reduce to stdpp bv facts: cbv        *)
(* through the coercions, then bv lemmas.                                   *)
(* ---------------------------------------------------------------------- *)
Lemma zero_extend'_id (a : mword 64) : zero_extend' 64 a = a.
Proof.
  cbv [zero_extend' Operators_mwords.zero_extend Operators_mwords.extz_vec to_word get_word
       MachineWord.MachineWord.zero_extend].
  apply bv_eq. rewrite bv_zero_extend_unsigned. reflexivity. lia.
Qed.

Lemma autocast_id (m : Z) (x : mword m) : autocast x = x.
Proof. apply autocast_refl. Qed.

(* ---------------------------------------------------------------------- *)
(* should_inc_minstret is state-pure: its result is fully determined by    *)
(* the mcountinhibit and minstretcfg cells.  Owning those two CSRs thus     *)
(* discharges the `should_inc` exec-condition (no `forall s0` needed).      *)
(* ---------------------------------------------------------------------- *)
Lemma exec_should_inc_M (mc : mword 32) (mcfg : mword 64) s :
  register_lookup mcountinhibit s.(sregs) = mc ->
  register_lookup minstretcfg s.(sregs) = mcfg ->
  exec (should_inc_minstret Machine) s
    = Some (andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                 (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")), s).
Proof.
  intros Hmc Hmcfg. unfold should_inc_minstret.
  assert (HA : exec ((read_reg mcountinhibit : M (mword 32)) >>=
                     (fun w__0 => returnM (eq_vec (_get_Counterin_IR w__0) ('b"0")))) s
               = Some (eq_vec (_get_Counterin_IR mc) ('b"0"), s)).
  { rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mcountinhibit s)). rewrite Hmc. apply exec_returnm. }
  rewrite (exec_and_boolM_Some _ _ _ _ _ HA).
  destruct (eq_vec (_get_Counterin_IR mc) ('b"0")) eqn:Ea; cbn [andb].
  - rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg minstretcfg s)). rewrite Hmcfg. apply exec_returnm.
  - reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* MMIO-range discharge: an access whose base address is RAM (outside the  *)
(* CLINT/SIG ranges) is not "within" them.  Owning a memory byte at that    *)
(* address (via the RAM-constrained `↦ₘ`, lemma `mem_ram`) supplies         *)
(* `not_in_clint`/`not_in_sig`.  within_htif depends on the                 *)
(* `htif_tohost_base` register, discharged by owning it `= None`.           *)
(* ---------------------------------------------------------------------- *)
Lemma within_clint_false (a : Arch.pa) (w : Z) s :
  not_in_clint a -> (0 < w)%Z -> exec (within_clint (Physaddr a) w) s = Some (false, s).
Proof.
  intros Hnc Hw. unfold within_clint, plat_have_clint, __id. cbn [Riscv.rv64d.not negb].
  assert (Hf : (uint plat_clint_base <=? uint a) &&
               (uint a + w <=? uint plat_clint_base + uint plat_clint_size) = false).
  { destruct Hnc as [H|H]; [apply andb_false_intro1|apply andb_false_intro2]; apply Z.leb_gt; lia. }
  rewrite Hf. apply exec_returnm.
Qed.

Lemma within_sig_false (a : Arch.pa) (w : Z) s :
  not_in_sig a -> (0 < w)%Z -> exec (within_sig (Physaddr a) w) s = Some (false, s).
Proof.
  intros Hns Hw. unfold within_sig, plat_have_sig, __id. cbn [Riscv.rv64d.not negb].
  assert (Hf : (uint plat_sig_base <=? uint a) &&
               (uint a + w <=? uint plat_sig_base + uint plat_sig_size) = false).
  { destruct Hns as [H|H]; [apply andb_false_intro1|apply andb_false_intro2]; apply Z.leb_gt; lia. }
  rewrite Hf. apply exec_returnm.
Qed.

Lemma within_htif_false (a : Arch.pa) (w : Z) s :
  register_lookup htif_tohost_base s.(sregs) = None ->
  exec (within_htif_readable (Physaddr a) w) s = Some (false, s).
Proof.
  intro Hn. unfold within_htif_readable, within_htif_writable.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg htif_tohost_base s)).
  rewrite Hn. cbn match. apply exec_returnm.
Qed.

(* add_vec_int a 0 = a : the j=0 byte of an access sits at the access base. *)
Lemma avi0 (a : mword 64) : add_vec_int a 0 = a.
Proof.
  unfold add_vec_int, add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
         SailStdpp.Values.with_word, mword_of_int,
         MachineWord.MachineWord.add, MachineWord.MachineWord.Z_to_word.
  apply bv_eq. rewrite bv_add_unsigned Z_to_bv_unsigned.
  rewrite bv_wrap_0 Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma pa_add_0 (a : Arch.pa) : pa_add a 0 = a.
Proof. unfold pa_add. change (Z.of_nat 0) with 0%Z. apply avi0. Qed.

(* ---------------------------------------------------------------------- *)
(* Leaf 2: rX / rX_bits read leaf for x2 (sp), mirroring run_rX_x10.        *)
(* ---------------------------------------------------------------------- *)
Lemma rX_x2 : rX (Regno 2) = Defs.read_reg (R_bitvector_64 x2).
Proof. reflexivity. Qed.

Lemma run_rX_x2 s :
  run (rX (Regno 2)) s (register_lookup (R_bitvector_64 x2) s.(sregs)) s.
Proof. rewrite rX_x2. split; reflexivity. Qed.

Lemma exec_rX_x2 s :
  exec (rX (Regno 2)) s = Some (register_lookup (R_bitvector_64 x2) s.(sregs), s).
Proof. reflexivity. Qed.

Lemma exec_rX_bits_x2 (i : mword 5) s :
  uint i = 2 ->
  exec (rX_bits (Regidx i)) s = Some (register_lookup (R_bitvector_64 x2) s.(sregs), s).
Proof. intro H. unfold rX_bits; cbn match. rewrite H. apply exec_rX_x2. Qed.

(* ---------------------------------------------------------------------- *)
(* Leaf 3: ext_data_get_addr base offset acc w = read base, return OK vaddr *)
(* ---------------------------------------------------------------------- *)
Lemma exec_ext_data_get_addr_x2 (i : mword 5) (offset : mword 64) acc w s :
  uint i = 2 ->
  exec (ext_data_get_addr (Regidx i) offset acc w) s
  = Some (Ext_DataAddr_OK (Virtaddr (add_vec (register_lookup (R_bitvector_64 x2) s.(sregs)) offset)), s).
Proof.
  intro H. unfold ext_data_get_addr.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_x2 i s H)).
  apply exec_returnm.
Qed.

(* ---------------------------------------------------------------------- *)
(* Leaf 4: effectivePrivilege (Load Data) m Machine = Machine, given MPRV=0 *)
(* (a boot-config condition, analogous to the MIE/elp conditions).          *)
(* ---------------------------------------------------------------------- *)
Lemma exec_effectivePrivilege_load (m : mword 64) s :
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  exec (effectivePrivilege (Load Data) m Machine) s = Some (Machine, s).
Proof.
  intro H. unfold effectivePrivilege.
  cbn [generic_neq generic_eq].
  rewrite H. cbn [andb]. apply exec_returnm.
Qed.

(* ---------------------------------------------------------------------- *)
(* Leaf 5: split_misaligned vaddr 8 = (1,8) for an 8-aligned vaddr;         *)
(* misaligned_order 1 = (0,0,step).                                         *)
(* ---------------------------------------------------------------------- *)
Lemma exec_split_misaligned_aligned (vaddr : virtaddr) s :
  is_aligned_vaddr vaddr 8 = true ->
  exec (split_misaligned vaddr 8) s = Some ((1, 8), s).
Proof.
  intro H. unfold split_misaligned. rewrite H. cbn [orb]. apply exec_returnm.
Qed.

Lemma misaligned_order_1 : misaligned_order 1 = (0, 0, if sys_misaligned_order_decreasing then -1 else 1).
Proof. unfold misaligned_order. destruct sys_misaligned_order_decreasing; reflexivity. Qed.

(* ====================================================================== *)
(* 8-byte data-load memory path -- doubleword analogues of the 4-byte      *)
(* fetch lemmas in RiscvAddTryStep.v (read_ram/pmaCheck/checked/mem_read). *)
(* Differences: width 8, access = Load Data, PMA_readable (not executable).*)
(* ====================================================================== *)

(* read_ram: pin the 8-byte value from the owned bytes (mirror _4_pin). *)
Lemma run_read_ram_plain_8_pin (addr : mword 64) (w : bv 64) s :
  (forall j : nat, (N.of_nat j < 8)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  run (read_ram Read_plain (Physaddr addr) 8 false) s (w, default_meta) s.
Proof.
  intro Hbytes.
  unfold read_ram. cbn match.
  apply (proj2 (run_bind _ _ _ _ _)).
  eexists _, s. split; [ apply run_returnM_fwd | ]. cbn beta zeta.
  apply (proj2 (run_bind _ _ _ _ _)).
  unfold Defs.sail_mem_read. cbn beta zeta.
  eexists _, s. split.
  - cbn match beta. exists w. split.
    + intros j Hj. exact (Hbytes j Hj).
    + apply run_returnM_fwd.
  - cbn match beta. apply run_returnM_fwd.
Qed.

Lemma exec_read_ram_plain_8 (addr : mword 64) (w : bv 64) s :
  (forall j : nat, (N.of_nat j < 8)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (read_ram Read_plain (Physaddr addr) 8 false) s = Some ((w, default_meta), s).
Proof.
  intro Hbytes.
  apply (run_to_exec _ _ _ _ (run_read_ram_plain_8_pin addr w s Hbytes)).
  unfold read_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_read. cbn beta zeta.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  rewrite exec_MemRead.
  cbn [Interface.ReadReq.pa].
  case_match eqn:Hrb.
  - cbn [Interface.iMon_bind]. cbn match beta iota. discriminate.
  - exfalso.
    refine (read_bytes_ne (mem s) addr (Z.to_N 8) w _ Hrb).
    intros j Hj.
    change (RiscvModelBytes.pa_add addr j) with (pa_add addr j).
    change (RiscvModelBytes.nth_byte w j) with (nth_byte w j).
    exact (Hbytes j Hj).
Qed.

(* pmaCheck for Load Data: returns None when the region is readable+aligned. *)
Lemma exec_pmaCheck_ram_load (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8
    = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (pmaCheck (Physaddr addr) 8 (Load Data) pbmt false) s = Some (None, s).
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
  (* Load Data arm: assert_exp' true >>= fun _ => returnM PMA_readable  ≡  returnM PMA_readable *)
  change (assert_exp' true "sys/mem.sail:103.61-103.62" >>=
          (fun _ : true = true => returnM (PMA_readable (override_PMA rattr pbmt))))
    with (returnM (PMA_readable (override_PMA rattr pbmt)) : M bool).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite Hread. cbn match.
  apply exec_returnM.
Qed.

(* checked_mem_read for Load Data, width 8. *)
Lemma exec_checked_mem_read_ram_load (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 64) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i))
             = OFF) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8
    = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 8) s = Some (false, s) ->
  (forall j : nat, (N.of_nat j < 8)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (Load Data) pbmt Machine (Physaddr addr) 8 false false false false)
       s = Some (Ok (w, default_meta), s).
Proof.
  intros Hpmp Hmatch Halign Hread Hc Hsig Hh Hbytes.
  unfold checked_mem_read.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_machine_none _ _ _ s Hpmp)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_load addr pbmt region s Hmatch Halign Hread)).
      cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_readable (Physaddr addr) 8) s = Some (false, s))).
  2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (read_kind_of_flags _ _ _) s = Some (Read_plain, s))).
  2:{ unfold read_kind_of_flags. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_plain_8 addr w s Hbytes)).
  apply exec_returnM.
Qed.

(* mem_read for Load Data in Machine mode, width 8 (needs MPRV=0). *)
Lemma exec_mem_read_load (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 64) (m : mword 64) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i))
             = OFF) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8
    = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 8) s = Some (false, s) ->
  (forall j : nat, (N.of_nat j < 8)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (mem_read (Load Data) pbmt (Physaddr addr) 8 false false false)
       s = Some (Ok w, s).
Proof.
  intros Hpmp Hmatch Halign Hread Hc Hsig Hh Hbytes Hms Hmprv Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite Hms.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_load m s Hmprv)).
  unfold mem_read_priv.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (mem_read_priv_meta _ _ _ _ 8 _ _ _ _) s = Some (Ok (w, default_meta), s))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (checked_mem_read _ _ _ _ 8 _ _ _ _) s = Some (Ok (w, default_meta), s))).
      2:{ cbn match. apply exec_checked_mem_read_ram_load with (region := region); assumption. }
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

(* ====================================================================== *)
(* translateAddr (Load Data) = identity in Machine mode (MPRV off).        *)
(* Mirrors exec_translateAddr_identity (fetch).                            *)
(* ====================================================================== *)
Lemma exec_is_shadow_stack_load s :
  exec (is_shadow_stack_access (Load Data)) s = Some (false, s).
Proof. unfold is_shadow_stack_access. cbn match. apply exec_returnM. Qed.

Lemma exec_translateAddr_identity_load (a : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false ->
  exec (translateAddr (Virtaddr a) (Load Data)) s
    = Some (Ok (Physaddr (zero_extend' 64 (bits_of_virtaddr (Virtaddr a))),
                PBMT_PMA, init_ext_ptw), s).
Proof.
  intros Hcp Hmprv.
  unfold translateAddr.
  rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_load _ s Hmprv)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_M s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_load s)).
  unfold Defs.bind0.
  replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity).
  rewrite execR_bind.
  cbn match. reflexivity.
Qed.

(* ====================================================================== *)
(* untilMT one-iteration: measure 1, body reaches a state where cond=true. *)
(* The loop's Acc (Zwf 0) recursion is unfolded by destructing Zwf_guarded *)
(* (same technique as currentlyEnabled), so it is axiom-free.              *)
(* ====================================================================== *)
Lemma execR_untilMT_1 {R Vars} (vars vars' : Vars) (measure : Vars -> Z)
   (cond : Vars -> Defs.monadR R exception bool) (body : Vars -> Defs.monadR R exception Vars) s s' :
  measure vars = 1 ->
  execR (body vars) s = Some (inr vars', s') ->
  execR (cond vars') s' = Some (inr true, s') ->
  execR (Defs.untilMT vars measure cond body) s = Some (inr vars', s').
Proof.
  intros Hm Hb Hc. unfold Defs.untilMT.
  destruct (Defs.Zwf_guarded (measure vars)).
  cbn [Defs.untilMT'].
  destruct (Z_ge_dec (measure vars) 0) as [Hge|Hge]; [| exfalso; rewrite Hm in Hge; lia ].
  rewrite (execR_bind_Some _ _ _ _ _ Hb).
  rewrite (execR_bind_Some _ _ _ _ _ Hc).
  cbn match.
  apply execR_returnR_fwd.
Qed.

Section S.
Variable a : mword 64.
Variable v : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let pa := zero_extend' 64 (add_vec_int a (0 * 8)).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 8 = true.
Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmp : forall i, pmpAddrMatchType_encdec_backwards
   (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i)) = OFF.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Let data2 : mword (8*1*8) :=
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.

Lemma exec_vmem_read_addr_8 :
  exec (vmem_read_addr (Virtaddr a) 8 (Load Data) false false false) s
    = Some (Ok data2, s).
Proof.
  unfold vmem_read_addr.
  rewrite exec_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR (returnR (result (mword (8 * 8)) ExecutionResult) tt >>
                          liftR (split_misaligned (Virtaddr a) 8)) s = Some (inr (1, 8), s)).
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
    rewrite execR_liftR. rewrite (exec_split_misaligned_aligned (Virtaddr a) s Halign). reflexivity. }
  rewrite (execR_bind_Some _ _ _ _ _ Hinner).
  rewrite misaligned_order_1.
  match goal with
  | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (data2, true, 0), s))
  end.
  { eapply execR_untilMT_1.
    - (* measure *) reflexivity.
    - (* body *)
      cbn match.
      assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
      rewrite (execR_liftR_seq _ _ _ _ _ Hass).
      rewrite (execR_liftR_seq _ _ _ _ _
        (exec_translateAddr_identity_load (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0*8)) s Hpriv Hmprv)).
      cbn [bits_of_virtaddr]. cbn match.
      match goal with
      | |- execR (Defs.bind ?mrm ?post) s = _ =>
        assert (Hmrm : execR mrm s = Some (inr data2, s))
      end.
      { rewrite (execR_liftR_seq _ _ _ _ _
          (exec_mem_read_load PBMT_PMA pa region v (register_lookup mstatus s.(sregs)) s
             Hpmp Hmatch Hpalign Hread Hc Hsig Hh Hbytes eq_refl Hmprv Hpriv)).
        cbn match.
        rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite autocast_id. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hmrm).
      cbn. apply execR_returnR_fwd.
    - (* cond *) apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu).
  cbn. rewrite autocast_id. reflexivity.
Qed.
End S.

Lemma exec_is_pmm_applicable_load s :
  exec (is_pmm_applicable (Load Data) Machine) s = Some (true, s).
Proof.
  unfold is_pmm_applicable.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Load Data) (InstructionFetch tt)) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Load Data) (Load PageTableEntry)) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Load Data) (Store PageTableEntry)) with true by (vm_compute; reflexivity). cbn match.
  match goal with
  | |- context [ and_boolM ?orb _ ] => assert (Hor : exec orb s = Some (true, s))
  end.
  { rewrite (exec_or_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
    replace (generic_eq Machine Machine) with true by (vm_compute; reflexivity). reflexivity. }
  rewrite (exec_and_boolM_Some _ _ _ _ _ Hor).
  cbn match.
  rewrite (exec_returnM _ s).
  replace (xlen =? 64) with true by (vm_compute; reflexivity). reflexivity.
Qed.

Lemma exec_get_pmlen_load s :
  pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled ->
  exec (get_pmlen (Load Data) Machine) s = Some (0, s).
Proof.
  intro Hpmm. unfold get_pmlen.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_is_pmm_applicable_load s)).
  cbn match.
  assert (Hgp : exec (get_pmm Machine) s
          = Some (pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))), s)).
  { unfold get_pmm. rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mseccfg s)). apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hgp).
  rewrite Hpmm.
  apply exec_returnM.
Qed.

Lemma exec_transform_effective_address_load (ea : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled ->
  exec (transform_effective_address (Virtaddr ea) (Load Data)) s
    = Some (pm_transform_PA (Virtaddr ea) 0, s).
Proof.
  intros Hcp Hmprv Hpmm. unfold transform_effective_address.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_load _ s Hmprv)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_get_pmlen_load s Hpmm)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_translationMode_M s)).
  replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity). cbn match.
  apply exec_returnM.
Qed.

Section VR.
Variable i : mword 5.
Variable offset : mword 64.
Variable v : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let ea := add_vec (register_lookup (R_bitvector_64 x2) s.(sregs)) offset.
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Let data2 : mword (8*1*8) :=
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.
Hypothesis Hi : uint i = 2.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Hpmp : forall j, pmpAddrMatchType_encdec_backwards
   (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) j)) = OFF.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_vmem_read_8 :
  exec (vmem_read (Regidx i) offset 8 (Load Data) false false false) s = Some (Ok data2, s).
Proof.
  unfold vmem_read. rewrite exec_catch_early_return.
  assert (Hgta : exec (get_transformed_data_addr (Regidx i) offset (Load Data) 8) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_x2 i offset (Load Data) 8 s Hi)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_load ea s Hcp Hmprv Hpmm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
  rewrite execR_liftR.
  rewrite (exec_vmem_read_addr_8 a8 v region s Halign Hcp Hmprv Hpmp Hmatch Hpalign Hread Hc Hsig Hh Hbytes).
  reflexivity.
Qed.
End VR.
