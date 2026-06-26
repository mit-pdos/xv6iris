From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.MachineWord SailStdpp.Values.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpEntry WpGpr WpGprLoad.
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

(* register-generic 8-byte vmem_write: base address from ANY rs1, value [data]. *)
Section VWg.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable data : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let ea := add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Hypothesis Hrs1 : uint rs1 <> 0.
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
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) 8 s Hrs1)).
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

(* register-generic 8-byte STORE execute: base from rs1, value from rs2. *)
Section ExecStoreG.
Variable rs2 rs1 : mword 5.
Variable imm : mword 12.
Variable region : PMA_Region.
Variable s : mstate.
Let offset := sign_extend' 64 imm.
Let vrs2 := register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
Let ea := add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Hypothesis Hrs1 : uint rs1 <> 0.
Hypothesis Hrs2 : uint rs2 <> 0.
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
  rewrite (proj2 (Z.eqb_neq (uint rs2) 0) Hrs2). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
    (exec_vmem_write_8_gpr rs1 offset _ region s Hrs1 Hcp Hmprv Hpmm Halign Hpmp Hmatch Hpalign Hwrite Hc Hsig Hh)).
  cbn match.
  rewrite (exec_returnM _ _).
  rewrite autocast_subrange_id.
  reflexivity.
Qed.
End ExecStoreG.

(* exec-level register-generic STORE step (32-bit, F_Base): ANY rs1/rs2.
   The execute post-state [s_x] is parameterised (its sregs equal the
   pre-execute regs; only memory changed), so this is reusable for the WP. *)
Section ForwardSDg.
  Context (s s_x : mstate) (w : mword 32) (pc : mword 64) (imm : mword 12)
          (rs1 rs2 : mword 5) (b : bool).
  Definition sAsg : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pcg : mstate := set_reg sAsg nextPC (add_vec_int pc 4).
  Hypothesis Hsx_sregs : s_x.(sregs) = s_pcg.(sregs).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hdec_gen : forall s0 : mstate,
    register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 8), s0).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hexec_spc :
    exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s_pcg
    = Some (RETIRE_SUCCESS, s_x).

  Definition sTsg : mstate := set_reg s_x PC (register_lookup nextPC s_x.(sregs)).
  Definition sFsg : mstate :=
    if b then set_reg sTsg minstret (add_vec_int (register_lookup minstret sTsg.(sregs)) 1)
         else sTsg.

  Lemma forward_exec_sd_gpr :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    register_lookup (R_bitvector_64 mideleg) s.(sregs) = zeros' 64 ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFsg).
  Proof using All.
    intros Lpc Lpriv Lhs Lmideleg LmIE Lelp.
    assert (LpcA  : register_lookup PC sAsg.(sregs) = pc).
    { unfold sAsg. trans_mi. exact Lpc. }
    assert (LprivA: register_lookup cur_privilege sAsg.(sregs) = Machine).
    { unfold sAsg. trans_mi. exact Lpriv. }
    assert (LhsA  : register_lookup hart_state sAsg.(sregs) = HART_ACTIVE tt).
    { unfold sAsg. trans_mi. exact Lhs. }
    assert (LmidA : register_lookup (R_bitvector_64 mideleg) sAsg.(sregs) = zeros' 64).
    { unfold sAsg. trans_mi. exact Lmideleg. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE
              (register_lookup (R_bitvector_64 mstatus) sAsg.(sregs))) ('b"1") = false).
    { unfold sAsg. trans_mi. exact LmIE. }
    assert (LelpA : eq_vec (register_lookup elp sAsg.(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAsg. trans_mi. exact Lelp. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAsg = Some (None, sAsg)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAsg _ (exec_currentlyEnabled_S sAsg) LmidA LmIEA). }
    assert (HfetchA : exec (fetch tt) sAsg = Some (F_Base w, sAsg)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sAsg
              = Some (STORE (imm, Regidx rs2, Regidx rs1, 8), sAsg))
      by (apply Hdec_gen; exact LprivA).
    assert (Hha : exec (run_hart_active 0) sAsg
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), s_x)).
    { exact (exec_hart_active_progress sAsg sAsg s_x sAsg w
               (STORE (imm, Regidx rs2, Regidx rs1, 8)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA Hexec_spc I). }
    apply (exec_riscv_step_ADD s s_x w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - rewrite Hsx_sregs. unfold s_pcg, sAsg. trans_mi. trans_mi. exact Lhs.
    - rewrite Hsx_sregs. unfold s_pcg, sAsg. trans_mi. rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.

  Variable mst0 : mword 64.
  Hypothesis Lmst_s : register_lookup minstret s.(sregs) = mst0.

  Definition base_upd_sg : mstate := set_reg s_x PC (add_vec_int pc 4).
  Definition sFcsg : mstate :=
    if b then set_reg base_upd_sg minstret (add_vec_int mst0 1) else base_upd_sg.

  Lemma sFs_eq : sFsg = sFcsg.
  Proof.
    assert (Enpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
    { rewrite Hsx_sregs. unfold s_pcg, sAsg. rewrite register_lookup_set. reflexivity. }
    assert (Emst : register_lookup minstret s_x.(sregs) = mst0).
    { rewrite Hsx_sregs. unfold s_pcg, sAsg, set_reg; cbn [sregs]. tmig. tmig. exact Lmst_s. }
    unfold sFsg, sTsg, sFcsg, base_upd_sg. rewrite Enpc. destruct b; [|reflexivity].
    assert (Emst2 : register_lookup minstret (set_reg s_x PC (add_vec_int pc 4)).(sregs) = mst0).
    { unfold set_reg; cbn [sregs]. tmig. exact Emst. }
    rewrite Emst2. reflexivity.
  Qed.
End ForwardSDg.

(* ====================================================================== *)
(* Memory ghost-state update: turn the 8 owned target bytes from their     *)
(* old contents into the stored value's bytes, matching [write_bytes].     *)
(* ====================================================================== *)
Section MemUpdate.
  Context `{!riscvGS Σ}.

  (* single-byte update (no [mem_update] exists in RiscvPtsto). *)
  Lemma mem_update (mm : _) (a : Arch.pa) (v v' : bv 8) :
    gen_heap_interp (hG:=riscv_memGS) mm -∗ a ↦ₘ v ==∗ gen_heap_interp (hG:=riscv_memGS) (<[a := v']> mm) ∗ a ↦ₘ v'.
  Proof.
    iIntros "Hm [Ha %Hram]".
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

  Lemma wp_store_gpr (pc : mword 64) (w_s : mword 32) (imm_s : mword 12)
      (rs1 rs2 : mword 5) (m : gmap register_bitvector_64 (mword 64))
      (vrs1 vrs2 : mword 64) (b1 : bool) (vold : bv 64)
      (npc0a mst0a mstatus0a : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (mseccfg0 : mword 64) (pmpcfg0 : type_of_register pmpcfg_n)
      (pmar0 : list PMA_Region) (mi0a : bool) (elp0a : mword 1)
      E (Φ : mval -> iProp Σ) :
    let offset := sign_extend' 64 imm_s in
    let ea := add_vec vrs1 offset in
    let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
    let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)) in
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some vrs1 ->
    m !! gpr_of_Z (uint rs2) = Some vrs2 ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w_s 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w_s) s0 = Some (STORE (imm_s, Regidx rs2, Regidx rs1, 8), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0a) ('b"1") = false ->
    eq_vec elp0a (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0a) ('b"1") = false ->
    pmm_mode_backwards (_get_Seccfg_PMM mseccfg0) = PMM_Disabled ->
    is_aligned_vaddr (Virtaddr a8) 8 = true ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ nextPC ↦ᵣ npc0a -∗
    (R_bool minstret_increment) ↦ᵣ mi0a -∗ minstret ↦ᵣ mst0a -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0a -∗
    elp ↦ᵣ elp0a -∗ mseccfg ↦ᵣ mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗
    mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte vold j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w_s j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        gpr_file m -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0a 1 else mst0a) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0a -∗
        elp ↦ᵣ elp0a -∗ mseccfg ↦ᵣ mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗
        mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte vrs2 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w_s j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros offset ea a8 pa Hrs1 Hrs2 Hmrs1 Hmrs2 Hpmaall Hpmpf Halignf Hbit0f Hbit1f
      Hvalignf HnotRVCf Hds Hb1 HmIE Help HMPRV Hpmm Halign Hpalign.
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    destruct (Hpmaall pa 8) as (region & Hmatch & _ & _ & Hwrite).
    iIntros "Hpc Hfile Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytes Hcont".
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hsec")   as %Lsec.
    iDestruct (reg_valid with "Hreg Hpmpc")  as %Lpmpc.
    iDestruct (reg_valid with "Hreg Hpma")   as %Lpma.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hhtif")  as %Lhtif.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmrs1 with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (reg_valid with "Hreg Hr1c") as %Lrs1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmrs2 with "Hfile") as "[Hr2c Hfb2]".
    iDestruct (reg_valid with "Hreg Hr2c") as %Lrs2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    iDestruct (fetch_from_pts_minstret pc w_s region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    set (s_pc := set_reg (set_reg s (R_bool minstret_increment) b1) nextPC (add_vec_int pc 4)).
    assert (Lrs1p : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs) = vrs1).
    { unfold s_pc. gpr_trans. trans_mi. exact Lrs1. }
    assert (Lrs2p : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s_pc.(sregs) = vrs2).
    { unfold s_pc. gpr_trans. trans_mi. exact Lrs2. }
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine).
    { unfold s_pc; trans_mi; trans_mi; exact Lpriv. }
    assert (Lmsp : register_lookup mstatus s_pc.(sregs) = mstatus0a).
    { unfold s_pc; trans_mi; trans_mi; exact Lms. }
    assert (Lsecp : register_lookup mseccfg s_pc.(sregs) = mseccfg0).
    { unfold s_pc; trans_mi; trans_mi; exact Lsec. }
    assert (Lpmpcp : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0).
    { unfold s_pc; trans_mi; trans_mi; exact Lpmpc. }
    assert (Lpmap : register_lookup pma_regions s_pc.(sregs) = pmar0).
    { unfold s_pc; trans_mi; trans_mi; exact Lpma. }
    assert (Lhtifp : register_lookup htif_tohost_base s_pc.(sregs) = None).
    { unfold s_pc; trans_mi; trans_mi; exact Lhtif. }
    pose proof (within_clint_false pa 8 s_pc (proj1 Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 8 s_pc (proj2 Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_writable_false pa 8 s_pc Lhtifp) as Hwh.
    pose (s_x := MState s_pc.(sregs) (write_bytes s_pc.(mem) pa 8 vrs2)).
    assert (Hexec_spc :
      exec (execute (STORE (imm_s, Regidx rs2, Regidx rs1, 8))) s_pc
      = Some (RETIRE_SUCCESS, s_x)).
    { rewrite (exec_execute_STORE_8_gpr rs2 rs1 imm_s region s_pc Hrs1 Hrs2 Lprivp
                ltac:(rewrite Lmsp; exact HMPRV) ltac:(rewrite Lsecp; exact Hpmm)
                ltac:(rewrite Lrs1p; exact Halign) ltac:(intro j; rewrite Lpmpcp; exact (Hpmpf j))
                ltac:(rewrite Lpmap Lrs1p; exact Hmatch) ltac:(rewrite Lrs1p; exact Hpalign)
                Hwrite ltac:(rewrite Lrs1p; apply Hwc) ltac:(rewrite Lrs1p; apply Hws)
                ltac:(rewrite Lrs1p; apply Hwh)).
      subst s_x. do 3 f_equal. rewrite Lrs1p Lrs2p. reflexivity. }
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFcsg s_x pc b1 mst0a). iSplitR.
    { iPureIntro.
      assert (Hsxs : s_x.(sregs) = (s_pcg s pc b1).(sregs)) by reflexivity.
      rewrite <- (sFs_eq s s_x w_s pc b1 Hsxs Hfetch_at Hsi_s mst0a Lmst).
      apply (forward_exec_sd_gpr s s_x w_s pc imm_s rs1 rs2 b1 Hsxs Hfetch_at Hds Hsi_s Hexec_spc
               Lpc Lpriv Lhs Lmdl).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iMod (upd_window_8 s.(mem) pa vrs2 vold with "Hmem Hbytes") as "[Hmem Hbytes]".
    unfold sFcsg, base_upd_sg. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0a 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro.
      unfold s_x, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytes").
    - iMod "Hclose" as "_". iModIntro.
      unfold s_x, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytes").
  Qed.
End WpStoreGpr.

(* ====================================================================== *)
(* Demonstration: ONE lemma [wp_store_gpr] serves many (rs2,rs1) pairs.    *)
(* Only the register operands differ between `sd ra, 8(sp)` and            *)
(* `sd a0, _(a1)`.                                                          *)
(* ====================================================================== *)
Section WpStoreGprDemo.
  Context `{!riscvGS Σ}.
  (* `sd ra, imm(sp)` : rs2=ra(x1), rs1=sp(x2). *)
  Definition wp_store_ra_sp (pc : mword 64) (w : mword 32) (imm : mword 12) :=
    wp_store_gpr pc w imm (mword_of_int 2) (mword_of_int 1).
  (* `sd a0, imm(a1)` : rs2=a0(x10), rs1=a1(x11).  SAME lemma, different regs. *)
  Definition wp_store_a0_a1 (pc : mword 64) (w : mword 32) (imm : mword 12) :=
    wp_store_gpr pc w imm (mword_of_int 11) (mword_of_int 10).

  Goal gpr_of_Z (uint (mword_of_int 1 : mword 5)) = x1
    /\ gpr_of_Z (uint (mword_of_int 2 : mword 5)) = x2
    /\ gpr_of_Z (uint (mword_of_int 10 : mword 5)) = x10
    /\ gpr_of_Z (uint (mword_of_int 11 : mword 5)) = x11
    /\ uint (mword_of_int 1 : mword 5) <> 0
    /\ uint (mword_of_int 2 : mword 5) <> 0.
  Proof. repeat split; vm_compute; first [ reflexivity | discriminate ]. Qed.
End WpStoreGprDemo.
