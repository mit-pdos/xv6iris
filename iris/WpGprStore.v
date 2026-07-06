From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.MachineWord SailStdpp.Values.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpGpr.
Require Import MinstretInv InstrBytes.
From iris.base_logic.lib Require Import invariants.
From iris.bi.lib Require Import fractional.
Local Open Scope Z_scope.
Import Defs.

(* ---- write_bytes spec (stated over the mstate mem field, so the gmap
   key instance matches write_bytes' definition) ---- *)

(* off-window: write_bytes leaves untouched addresses alone. *)
Lemma write_bytes_lookup_ne {w} (s : mstate) (pa : Arch.pa) (n : N) (v : bv w) (a : Arch.pa) :
  (forall j : nat, (N.of_nat j < n)%N -> a <> pa_add pa j) ->
  write_bytes s.(mem) pa n v !! a = s.(mem) !! a.
Proof.
  intro Hne. unfold write_bytes. generalize (mem s). intro mm.
  assert (Hgen : forall l : list nat, (forall j, In j l -> a <> pa_add pa j) ->
            foldr (fun j acc => <[pa_add pa j := nth_byte v j]> acc) mm l !! a = mm !! a).
  { induction l as [|x xs IH]; intro Hl; simpl; [reflexivity|].
    rewrite lookup_insert_ne.
    - apply IH. intros j Hj. apply Hl. right. exact Hj.
    - intro Heq. apply (Hl x (or_introl eq_refl)). symmetry. exact Heq. }
  apply Hgen. intros j Hj%in_seq. apply Hne. lia.
Qed.

(* in-window: with distinct window addresses, byte j reads back as nth_byte v j. *)
Lemma write_bytes_lookup_in {w} (s : mstate) (pa : Arch.pa) (n : N) (v : bv w) (j : nat) :
  (N.of_nat j < n)%N ->
  (forall a b : nat, (N.of_nat a < n)%N -> (N.of_nat b < n)%N ->
     pa_add pa a = pa_add pa b -> a = b) ->
  write_bytes s.(mem) pa n v !! pa_add pa j = Some (nth_byte v j).
Proof.
  intros Hj Hinj. unfold write_bytes. generalize (mem s). intro mm.
  assert (Hgen : forall l : list nat, In j l -> (forall i, In i l -> (N.of_nat i < n)%N) ->
            foldr (fun i acc => <[pa_add pa i := nth_byte v i]> acc) mm l !! pa_add pa j
              = Some (nth_byte v j)).
  { induction l as [|x xs IH]; intros Hin Hb; simpl; [destruct Hin|].
    destruct (decide (x = j)) as [->|Hxj].
    - rewrite lookup_insert. reflexivity.
    - rewrite lookup_insert_ne.
      + apply IH; [destruct Hin as [->|?]; [contradiction|assumption]
                  | intros i Hi; apply Hb; right; exact Hi].
      + intro Heq. apply Hxj.
        apply (Hinj x j); [apply Hb; left; reflexivity | exact Hj | exact Heq]. }
  apply Hgen; [apply in_seq; lia | intros i Hi%in_seq; lia].
Qed.

(* ---- write leaf: write_ram rv64d_types.Write_plain stores all 8 bytes via write_bytes ---- *)
Lemma exec_write_ram_plain_8 (addr : mword 64) (data : bv 64) s :
  exec (write_ram rv64d_types.Write_plain (Physaddr addr) 8 data tt) s
  = Some (true, MState s.(sregs) (write_bytes s.(mem) addr 8 data)).
Proof.
  unfold write_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_write. cbn beta zeta iota match.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  cbn match.
  reflexivity.
Qed.

Lemma within_htif_writable_false (a : Arch.pa) (w : Z) s :
  register_lookup htif_tohost_base s.(sregs) = None ->
  exec (within_htif_writable (Physaddr a) w) s = Some (false, s).
Proof.
  intro Hn. unfold within_htif_writable.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg htif_tohost_base s)).
  rewrite Hn. cbn match. apply exec_returnm.
Qed.

Lemma exec_pmaCheck_ram_store (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (pmaCheck (Physaddr addr) 8 (Store Data) pbmt false) s = Some (None, s).
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

Lemma exec_checked_mem_write_ram_store (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 64) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i)) = OFF) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 8) s = Some (false, s) ->
  exec (checked_mem_write (Physaddr addr) 8 data (Store Data) pbmt Machine tt false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 8 data)).
Proof.
  intros Hpmp Hmatch Halign Hwrite Hc Hsig Hh.
  unfold checked_mem_write.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_machine_none _ _ _ s Hpmp)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_store addr pbmt region s Hmatch Halign Hwrite)).
      cbn match. apply exec_returnM. }
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_writable (Physaddr addr) 8) s = Some (false, s))).
  2:{ unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (write_kind_of_flags false false false) s = Some (rv64d_types.Write_plain, s))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_write_ram_plain_8 addr data s)).
  apply exec_returnM.
Qed.

Lemma exec_effectivePrivilege_store (m : mword 64) s :
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  exec (effectivePrivilege (Store Data) m Machine) s = Some (Machine, s).
Proof.
  intro H. unfold effectivePrivilege. cbn [generic_neq generic_eq].
  rewrite H. cbn [andb]. apply exec_returnm.
Qed.

Lemma exec_is_shadow_stack_store s :
  exec (is_shadow_stack_access (Store Data)) s = Some (false, s).
Proof. unfold is_shadow_stack_access. cbn match. apply exec_returnM. Qed.

Lemma exec_translateAddr_identity_store (a : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false ->
  exec (translateAddr (Virtaddr a) (Store Data)) s
    = Some (Ok (Physaddr (zero_extend' 64 (bits_of_virtaddr (Virtaddr a))), PBMT_PMA, init_ext_ptw), s).
Proof.
  intros Hcp Hmprv.
  unfold translateAddr.
  rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_store _ s Hmprv)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_M s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_store s)).
  unfold Defs.bind0.
  replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity).
  rewrite execR_bind. cbn match. reflexivity.
Qed.

Lemma exec_mem_write_ea (addr : mword 64) s :
  exec (mem_write_ea (Physaddr addr) 8 false false false) s = Some (Ok tt, s).
Proof.
  unfold mem_write_ea. cbn [orb andb].
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (write_kind_of_flags false false false) s = Some (rv64d_types.Write_plain, s))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
  apply exec_returnM.
Qed.

Lemma exec_mem_write_value_8 (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 64) (m : mword 64) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i)) = OFF) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 8) s = Some (false, s) ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (mem_write_value (Physaddr addr) 8 data (Store Data) pbmt false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 8 data)).
Proof.
  intros Hpmp Hmatch Halign Hwrite Hc Hsig Hh Hms Hmprv Hpriv.
  unfold mem_write_value, mem_write_value_meta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv. rewrite Hms.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_store m s Hmprv)).
  unfold mem_write_value_priv_meta. cbn [orb andb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_checked_mem_write_ram_store pbmt addr region data s Hpmp Hmatch Halign Hwrite Hc Hsig Hh)).
  cbn match. unfold mem_write_callback. apply exec_returnm.
Qed.


Lemma match_false_branch {T : Type} (A B : T) :
  match false return T with | true => A | false => B end = B.
Proof. reflexivity. Qed.

Lemma execR_match_false {R X} (A B : Defs.monadR R exception X) s :
  execR (match false return (Defs.monadR R exception X) with | true => A | false => B end) s
  = execR B s.
Proof. reflexivity. Qed.


(* match-reduction helper for the translateAddr Ok-triple (last component unit). *)
Lemma match_ok_triple_branch {A1 A2 B T} (x1 : A1) (x2 : A2)
    (f : A1 -> A2 -> T) (g : B -> T) :
  match (Ok (x1, x2, tt) : result (A1 * A2 * unit) B) return T with
  | Ok (y1, y2, _) => f y1 y2
  | Err e => g e
  end = f x1 x2.
Proof. reflexivity. Qed.

Section SW.
Variable a : mword 64.
Variable data : bv 64.
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
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 8) s = Some (false, s).

Lemma exec_vmem_write_addr_8 :
  exec (vmem_write_addr (Virtaddr a) 8 data (Store Data) false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) pa 8 data)).
Proof.
  unfold vmem_write_addr.
  rewrite exec_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR (returnR (result bool ExecutionResult) tt >>
                          liftR (split_misaligned (Virtaddr a) 8)) s = Some (inr (1, 8), s)).
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
    rewrite execR_liftR. rewrite (exec_split_misaligned_aligned (Virtaddr a) s Halign). reflexivity. }
  rewrite (execR_bind_Some _ _ _ _ _ Hinner).
  rewrite misaligned_order_1.
  match goal with
  | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s
                 = Some (inr (true, 0%Z, true), MState s.(sregs) (write_bytes s.(mem) pa 8 data)))
  end.
  { eapply execR_untilMT_1.
    - reflexivity.
    - (* body, vars = (false, 0, true) *)
      cbn match.
      assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
      rewrite (execR_liftR_seq _ _ _ _ _ Hass).
      rewrite (execR_liftR_seq _ _ _ _ _
        (exec_translateAddr_identity_store (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0*8)) s Hpriv Hmprv)).
      cbn [bits_of_virtaddr]. cbn match.
      (* SC dummy assert (Bool.eqb false (is_store_conditional (Store Data)) = true) *)
      assert (Hsc : exec (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51") s
                    = Some (tt, s)) by reflexivity.
      assert (Hscm : execR (Defs.liftR (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51")
                            : Defs.monadR (result bool ExecutionResult) exception unit) s = Some (inr tt, s))
        by (rewrite execR_liftR; rewrite Hsc; reflexivity).
      (* Isolate the SC-assert >> if-expression as Hinner; proving it in a
         nested goal keeps the outer goal from definitionally reducing the
         if's else branch through mem_write_value (the over-reduction trap). *)
      match goal with
      | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
          assert (Hwrloop : execR (Defs.bind0 (Defs.liftR asrt) Nbody) s
                           = Some (inr true, MState s.(sregs) (write_bytes s.(mem) pa 8 data)))
      end.
      { (* peel the SC assert, keeping the if-expression opaque via [set] so
           the bind0 rewrite cannot reduce its else branch *)
        match goal with
        | |- execR (Defs.bind0 _ ?Nbody) s = _ => set (NN := Nbody)
        end.
        rewrite (execR_bind0_Some _ _ _ _ Hscm).
        unfold NN; clear NN.
        (* strip [if (andb false _) then THEN else ELSE] -> ELSE by conversion *)
        match goal with
        | |- execR (match _ as x in bool return @?P x with | true => _ | false => ?B end) ?ss = ?R =>
            change (execR B ss = R)
        end.
        (* ELSE: mem_write_ea -> Ok tt *)
        rewrite (execR_liftR_seq _ _ _ _ _ (exec_mem_write_ea (zero_extend' 64 (add_vec_int a (0*8))) s)).
        cbn match.
        (* autocast (subrange data 63 0) = data : capture the value arg from the
           goal (so it carries the mword (8*8) type) and rewrite it to data *)
        match goal with
        | |- context [ mem_write_value ?pp 8 ?D (Store Data) ?pb false false false ] =>
            replace D with data
        end.
        2: { symmetry.
             change (8*(0+1)*8-1) with 63. change (8*0*8) with 0. change (8*8) with 64.
             change (63 - 0 + 1) with 64. rewrite autocast_id.
             unfold subrange_vec_dec. change (63 - 0 + 1) with 64. rewrite autocast_id.
             unfold to_word_idx, to_word, get_word, MachineWord.slice.
             rewrite MachineWord.cast_idx_refl.
             apply bv_eq. rewrite bv_extract_unsigned.
             change (Z.of_N (MachineWord.Z_idx 0)) with 0. rewrite Z.shiftr_0_r.
             apply bv_wrap_bv_unsigned. }
        (* mem_write_value -> Ok true, write_bytes state *)
        rewrite (execR_liftR_seq _ _ _ _ _
          (exec_mem_write_value_8 PBMT_PMA (zero_extend' 64 (add_vec_int a (0*8))) region data
             (register_lookup mstatus s.(sregs)) s Hpmp Hmatch Hpalign Hwrite Hc Hsig Hh eq_refl Hmprv Hpriv)).
        cbn match.
        apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hwrloop).
      cbn.
      apply execR_returnR_fwd.
    - apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu).
  cbn. reflexivity.
Qed.
End SW.

(* ---- store-side transform_effective_address (mirror of the load) ---- *)
Lemma exec_is_pmm_applicable_store s :
  exec (is_pmm_applicable (Store Data) Machine) s = Some (true, s).
Proof.
  unfold is_pmm_applicable.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Store Data) (InstructionFetch tt)) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Store Data) (Load PageTableEntry)) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Store Data) (Store PageTableEntry)) with true by (vm_compute; reflexivity). cbn match.
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

Lemma exec_get_pmlen_store s :
  pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled ->
  exec (get_pmlen (Store Data) Machine) s = Some (0, s).
Proof.
  intro Hpmm. unfold get_pmlen.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_is_pmm_applicable_store s)).
  cbn match.
  assert (Hgp : exec (get_pmm Machine) s
          = Some (pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))), s)).
  { unfold get_pmm. rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mseccfg s)). apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hgp).
  rewrite Hpmm.
  apply exec_returnM.
Qed.

Lemma exec_transform_effective_address_store (ea : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled ->
  exec (transform_effective_address (Virtaddr ea) (Store Data)) s
    = Some (pm_transform_PA (Virtaddr ea) 0, s).
Proof.
  intros Hcp Hmprv Hpmm. unfold transform_effective_address.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_store _ s Hmprv)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_get_pmlen_store s Hpmm)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_translationMode_M s)).
  replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity). cbn match.
  apply exec_returnM.
Qed.

(* register-generic 8-byte vmem_write: base address from ANY rs1 (incl. x0 ->
   zero_reg), value [data]. *)
Section VWg.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable data : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Hpmp : forall j, pmpAddrMatchType_encdec_backwards
   (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) j)) = OFF.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 8) s = Some (false, s).

Lemma exec_vmem_write_8_gpr :
  exec (vmem_write (Regidx rs1) offset 8 data (Store Data) false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) pa 8 data)).
Proof.
  unfold vmem_write. rewrite exec_catch_early_return.
  assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Store Data) 8) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) 8 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_store ea s Hcp Hmprv Hpmm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
  rewrite execR_liftR.
  rewrite (exec_vmem_write_addr_8 a8 data region s Halign Hcp Hmprv Hpmp Hmatch Hpalign Hwrite Hc Hsig Hh).
  reflexivity.
Qed.
End VWg.

(* the stored value [autocast (subrange v (8*8-1) 0)] is just [v] (full-width). *)
Lemma autocast_subrange_id (d : bv 64) :
  @autocast mword ((8*8-1) - 0 + 1) (8*8) _ (@subrange_vec_dec 64 d (8*8-1) 0) = d.
Proof.
  change (8*8-1) with 63. change (8*8) with 64. change (63 - 0 + 1) with 64.
  rewrite autocast_id.
  unfold subrange_vec_dec. change (63 - 0 + 1) with 64. rewrite autocast_id.
  unfold to_word_idx, to_word, get_word, MachineWord.slice.
  rewrite MachineWord.cast_idx_refl.
  apply bv_eq. rewrite bv_extract_unsigned.
  change (Z.of_N (MachineWord.Z_idx 0)) with 0. rewrite Z.shiftr_0_r.
  apply bv_wrap_bv_unsigned.
Qed.

(* register-generic 8-byte STORE execute: base from rs1, value from rs2 (ANY
   rs1/rs2, incl. x0 -> zero_reg for both the base and the stored value). *)
Section ExecStoreG.
Variable rs2 rs1 : mword 5.
Variable imm : mword 12.
Variable region : PMA_Region.
Variable s : mstate.
Let offset := sign_extend' 64 imm.
Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Hpmp : forall j, pmpAddrMatchType_encdec_backwards
   (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) j)) = OFF.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 8) s = Some (false, s).

Lemma exec_execute_STORE_8_gpr :
  exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s
    = Some (RETIRE_SUCCESS, MState s.(sregs) (write_bytes s.(mem) pa 8 vrs2)).
Proof.
  change (execute (STORE (imm, Regidx rs2, Regidx rs1, 8)))
    with (execute_STORE imm (Regidx rs2) (Regidx rs1) 8).
  unfold execute_STORE.
  replace (8 <=? xlen_bytes) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:320.28-320.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
    (exec_vmem_write_8_gpr rs1 offset _ region s Hcp Hmprv Hpmm Halign Hpmp Hmatch Hpalign Hwrite Hc Hsig Hh)).
  cbn match.
  rewrite (exec_returnM _ _).
  rewrite autocast_subrange_id.
  reflexivity.
Qed.
End ExecStoreG.

(* ====================================================================== *)
(* Memory ghost-state update: turn the 8 owned target bytes from their     *)
(* old contents into the stored value's bytes, matching [write_bytes].     *)
(* ====================================================================== *)
Section MemUpdate.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context {dqc : dfrac}.

  (* single-byte update (no [mem_update] exists in RiscvPtsto). *)
  Lemma mem_update (mm : _) (a : Arch.pa) (v v' : bv 8) :
    gen_heap_interp (hG:=riscv_memGS) mm -∗ a ↦ₘ v ==∗ gen_heap_interp (hG:=riscv_memGS) (<[a := v']> mm) ∗ a ↦ₘ v'.
  Proof.
    (* [mem_pointsto] is [Typeclasses Opaque] (sealed in RiscvPtsto); unfold it
       here so the raw [pointsto ∗ ⌜addr_is_ram⌝] conjunction can be destructed. *)
    rewrite /mem_pointsto. iIntros "Hm [Ha %Hram]".
    iMod (gen_heap_update with "Hm Ha") as "[Hm Ha]".
    iModIntro. iFrame "Hm Ha". iPureIntro. exact Hram.
  Qed.

  (* window update over an arbitrary index list (write_bytes is a foldr). *)
  Lemma upd_window (mm : _) (pa : Arch.pa) (vnew vold : bv 64)
      (l : list nat) :
    gen_heap_interp (hG:=riscv_memGS) mm -∗ ([∗ list] j ∈ l, (pa_add pa j) ↦ₘ nth_byte vold j) ==∗
    gen_heap_interp (hG:=riscv_memGS) (foldr (fun j acc => <[pa_add pa j := nth_byte vnew j]> acc) mm l)
      ∗ ([∗ list] j ∈ l, (pa_add pa j) ↦ₘ nth_byte vnew j).
  Proof.
    iInduction l as [|x xs IH] "IH"; simpl.
    - iIntros "Hm _". iModIntro. iFrame.
    - iIntros "Hm [Ha Hrest]".
      iMod ("IH" with "Hm Hrest") as "[Hm Hrest]".
      iMod (mem_update _ (pa_add pa x) (nth_byte vold x) (nth_byte vnew x) with "Hm Ha") as "[Hm Ha]".
      iModIntro. iFrame "Ha Hrest Hm".
  Qed.

  Lemma upd_window_8 (mm : _) (pa : Arch.pa) (vnew vold : bv 64) :
    gen_heap_interp (hG:=riscv_memGS) mm -∗ ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte vold j) ==∗
    gen_heap_interp (hG:=riscv_memGS) (write_bytes mm pa 8 vnew)
      ∗ ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte vnew j).
  Proof. unfold write_bytes. change (N.to_nat 8) with 8%nat. apply upd_window. Qed.
End MemUpdate.

(* ====================================================================== *)
(* The register-GENERIC store WP: ONE lemma for `sd rs2, imm(rs1)` for ANY  *)
(* rs1/rs2, GPRs held as the single [gpr_file] resource (UNCHANGED), and    *)
(* the 8 target bytes updated from their old contents to rs2's bytes.        *)
(* ====================================================================== *)
Section WpStoreGpr.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* reg_pointsto fractional instances + mmode_config_split_half /
     mmode_config_combine_half now live in InstrBytes.v (shared). *)

  (* [instr]/[mmode_config]-formulated register-generic 8-byte STORE WP -- the
     write-dual of [wp_ld_gpr].  STORE reads TWO sources: rs1 (base address) and
     rs2 (data), each borrowed off [gpr_file] independently (so rs1 = rs2 is
     fine), and WRITES the 8 target bytes from their old contents [vold] to rs2's
     bytes.  The caller supplies the OLD (full-owned) target bytes and the store's
     alignment; the config the translation / PMP checks read is recovered from the
     KEPT half of [mmode_config] + [hw_config].  No register is written ([gpr_file]
     is handed back UNCHANGED). *)
  Lemma wp_store_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc : bool) (rs1 rs2 : mword 5)
      (imm : mword 12) (m : gmap regidx (mword 64)) (vold : bv 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    let offset := sign_extend' 64 imm in
    let ea := add_vec (m !!! Regidx rs1) offset in
    ↑minstretN ⊆ E ->
    (* the 8-byte DATA access needs the stronger all-OFF form: an 8-byte
       window can partially overlap a TOR/NA4 boundary (partial match faults
       even in M-mode), so unlocked-ness alone does not suffice.  The fetch
       side uses [pmp_all_off_allows_all]. *)
    pmp_all_off pmpcfg0 ->
    is_aligned_paddr (Physaddr ea) 8 = true ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add ea j) ↦ₘ nth_byte vold j) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file m -∗
      ([∗ list] j ∈ seq 0 8, (pa_add ea j) ↦ₘ nth_byte (m !!! Regidx rs2) j) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros offset ea HN Hpmp Halign.
    iIntros "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA)".
    destruct (Hpma_all ea 8) as (region & Hmatch & _ & _ & Hwrite).
    iApply (wp_instr E Φ pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 8)) pmpcfg0
              HN (pmp_all_off_allows_all _ Hpmp) with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k")   as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms_k")     as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hpmpc_k")   as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hmseccfg")  as %Lsec.
    iDestruct (reg_valid_dq with "Hreg Hpma")      as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif")     as %Lhtif.
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))).
    (* read rs1 (base) -- borrow, read, return *)
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hr1c") as %Lrs1v.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    (* read rs2 (data) -- independent borrow; rs1 = rs2 is fine *)
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hr2c") as %Lrs2v.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    iAssert (⌜addr_is_ram ea⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    (* base register at the execute state, uniform over rs1 (x0 -> zero_reg). *)
    assert (Hbase : (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                    = m !!! Regidx rs1)
      by exact Lrs1v.
    (* data register at the execute state, uniform over rs2 (x0 -> zero_reg). *)
    assert (Hdata : (if Z.eqb (uint rs2) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s_pc.(sregs))
                    = m !!! Regidx rs2)
      by exact Lrs2v.
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmsp : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsecp : register_lookup mseccfg s_pc.(sregs) = mseccfg0)
      by (unfold s_pc; tmig; exact Lsec).
    assert (Lpmpcp : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmap : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtifp : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    pose proof (within_clint_false ea 8 s_pc (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false ea 8 s_pc (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_writable_false ea 8 s_pc Lhtifp) as Hwh.
    (* [ea]/[pa] the model computes coincide with [ea] once the identity
       zero-extends / +0 are stripped; bridge each PMP/translation goal. *)
    assert (Ha8 : zero_extend' 64 (subrange_vec_dec
              (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                       offset) (xlen - 0 - 1) 0) = ea).
    { rewrite Hbase. rewrite zero_extend'_id. rewrite subrange_id. reflexivity. }
    assert (Hpa : zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec
              (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                       offset) (xlen - 0 - 1) 0)) (0 * 8)) = ea).
    { rewrite Hbase. rewrite !zero_extend'_id. rewrite subrange_id.
      change (0 * 8) with 0. rewrite avi0. reflexivity. }
    pose (s_x := MState s_pc.(sregs) (write_bytes s_pc.(mem) ea 8 (m !!! Regidx rs2))).
    assert (Hexec_spc :
      exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s_pc
      = Some (RETIRE_SUCCESS, s_x)).
    { rewrite (exec_execute_STORE_8_gpr rs2 rs1 imm region s_pc Lprivp
                ltac:(rewrite Lmsp; exact HMPRV) ltac:(rewrite Lsecp; exact Hseccfg1)
                ltac:(rewrite Ha8; unfold is_aligned_vaddr; unfold is_aligned_paddr in Halign; exact Halign)
                ltac:(intro j; rewrite Lpmpcp; exact (proj1 (Hpmp j)))
                ltac:(rewrite Lpmap Hpa; exact Hmatch) ltac:(rewrite Hpa; exact Halign)
                Hwrite ltac:(rewrite Hpa; apply Hwc) ltac:(rewrite Hpa; apply Hws)
                ltac:(rewrite Hpa; apply Hwh)).
      subst s_x. rewrite Hpa Hdata. reflexivity. }
    (* write the 8 target bytes: from [vold] to rs2's value, updating the heap. *)
    iMod (upd_window_8 σ.(mem) ea (m !!! Regidx rs2) vold
            with "Hmem Hbytes") as "[Hmem Hbytes]".
    iModIntro.
    iExists s_x.
    iSplitR.
    { iPureIntro. rewrite Hpceq. exact Hexec_spc. }
    iSplitL "Hreg Hmem".
    { unfold s_x, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc (if is_rvc then 2 else 4)).
    { unfold s_x, s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k". iPureIntro. exact (conj HmIE (conj HMPRV HSXL)). }
    iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] [Hfmap] Hbytes").
    iSplitR.
    { iPureIntro. exact Hdom. }
    iExact "Hfmap".
  Qed.
End WpStoreGpr.

(* ====================================================================== *)
(* Demonstration: ONE lemma [wp_store_gpr] serves many (rs2,rs1) pairs.    *)
(* Only the register operands differ between `sd ra, imm(sp)` and          *)
(* `sd a0, imm(a1)`.                                                        *)
(* ====================================================================== *)
Section WpStoreGprDemo.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  (* `sd ra, imm(sp)` : rs2=ra(x1), rs1=sp(x2). *)
  Definition wp_store_ra_sp (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) (imm : mword 12) :=
    wp_store_gpr E Φ pc false (mword_of_int 2) (mword_of_int 1) imm.
  (* `sd a0, imm(a1)` : rs2=a0(x10), rs1=a1(x11).  SAME lemma, different regs. *)
  Definition wp_store_a0_a1 (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) (imm : mword 12) :=
    wp_store_gpr E Φ pc false (mword_of_int 11) (mword_of_int 10) imm.

  Goal gpr_of_Z (uint (mword_of_int 1 : mword 5)) = x1
    /\ gpr_of_Z (uint (mword_of_int 2 : mword 5)) = x2
    /\ gpr_of_Z (uint (mword_of_int 10 : mword 5)) = x10
    /\ gpr_of_Z (uint (mword_of_int 11 : mword 5)) = x11.
  Proof. repeat split; vm_compute; reflexivity. Qed.
End WpStoreGprDemo.
