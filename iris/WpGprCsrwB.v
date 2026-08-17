From Stdlib Require Import ZArith.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec ExecCommon WpGpr.
Require Import RegFile.
Require Import InstrBytes.
Require Import WpInstr.   (* wp_instr / mm_cycle, split out of InstrBytes *)
Local Open Scope Z_scope.
Require Import WpGprCsrwCommon.
Require Import RiscvExtras.   (* satp_ppn_mask_id: the PPN mask is a no-op here *)
Require Import MinstretInv.   (* exec_clint_dispatch_false: writing stimecmp refreshes mip *)
Require Import HartSwp HartLift HartRegNode HartSpan HartSpanChar HartMCycle
        HartMFrame HartGoodb WpDecodeBridge WpMmodeJump WpMmodeCsrSwp.
Require Import WpGprCsrrCommon.   (* drive_csr_term *)

(* ===================================================================== *)
(* MONADIC-LEGALIZE REDUCTION LAYER.  Each legalize_* chains             *)
(* currentlyEnabled/hartSupports calls; reduce them to closed bools via  *)
(* the Acc-recursion recipe, keeping the legalized value SYMBOLIC.       *)
(* First target: mideleg (0x303, _S) — shortest legalize (Sscofpmf+S^3). *)
(* ===================================================================== *)

Lemma exec_hartSupports_Sscofpmf s : exec (hartSupports Ext_Sscofpmf) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Sscofpmf) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

Lemma exec_hartSupports_Zihpm s : exec (hartSupports Ext_Zihpm) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zihpm) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

(* currentlyEnabled Sscofpmf = hartSupports Sscofpmf && (hartSupports Zihpm && cE Zicsr) = true *)
Lemma exec_currentlyEnabled_Sscofpmf s :
  exec (currentlyEnabled Ext_Sscofpmf) s = Some (true, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Sscofpmf) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Sscofpmf s)). cbn match.
  match goal with |- context[_rec_currentlyEnabled Ext_Zihpm ?k ?acc] =>
    destruct acc; cbn [_rec_currentlyEnabled]; unfold Defs.assert_exp';
    replace (Z.geb k 0) with true by reflexivity; cbn match;
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)); cbn match
  end.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Zihpm s)). cbn match.
  match goal with |- context[_rec_currentlyEnabled Ext_Zicsr ?k ?acc] =>
    destruct acc; cbn [_rec_currentlyEnabled]; unfold Defs.assert_exp';
    replace (Z.geb k 0) with true by reflexivity; cbn match;
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)); cbn match
  end.
  apply exec_hartSupports_Zicsr.
Qed.

(* The SYMBOLIC legalized mideleg value (S-mode enabled, Sscofpmf enabled).

   The written value is now MASKED by the platform's delegatable-interrupt set
   ([plat_mideleg_delegatable_bits] = 0x2222, i.e. SSI/STI/SEI/LCOFI) before the
   per-extension gates are applied, instead of being merged into the OLD value
   with the M-mode bits cleared -- so the old value plays no part any more (the
   model calls its first parameter [_o]).  With S and Sscofpmf both enabled every
   gate writes a field back with its own value, so this is the mask plus a tower
   of identity updates; it is kept in the model's shape rather than simplified,
   as before. *)
Definition mideleg_legalized (_o v : mword 64) : mword 64 :=
  let v := Mk_Minterrupts (and_vec v plat_mideleg_delegatable_bits) in
  _update_Minterrupts_SSI
    (_update_Minterrupts_STI
       (_update_Minterrupts_SEI
          (_update_Minterrupts_LCOFI v (_get_Minterrupts_LCOFI v))
          (_get_Minterrupts_SEI v))
       (_get_Minterrupts_STI v))
    (_get_Minterrupts_SSI v).

Lemma exec_legalize_mideleg (o v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (legalize_mideleg o v) s = Some (mideleg_legalized o v, s).
Proof.
  intro HS. unfold legalize_mideleg, mideleg_legalized.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Sscofpmf s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_S s)). rewrite HS. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_S s)). rewrite HS. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_S s)). rewrite HS. cbn match.
  apply exec_returnM.
Qed.

Definition csr_mideleg : mword 12 := mword_of_int 0x303.

(* the walker's view of the write: the pruned term, so the goal never carries
   the 4096-way dispatch (see WpGprCsrwA's [write_CSR_menvcfg_red] note -- the
   RHS is READ OFF the pruned goal, never hand-associated). *)
Lemma write_CSR_mideleg_red (v : mword 64) :
  write_CSR csr_mideleg v
  = Defs.bind (Defs.read_reg mideleg)
      (fun o : mword 64 =>
         Defs.bind (legalize_mideleg o v)
           (fun c : mword 64 =>
              Defs.bind (Defs.bind0 (Defs.write_reg mideleg c)
                           (Defs.read_reg mideleg))
                (fun c2 : mword 64 => returnM (Ok c2)))).
Proof.
  unfold write_CSR, csr_mideleg. drive_csr_term. reflexivity.
Qed.

Lemma goodb_legalize_mideleg (o v : mword 64) :
  goodb D_m (legalize_mideleg o v) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

Lemma exec_write_CSR_mideleg (v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (write_CSR csr_mideleg v) s
    = Some (Ok (mideleg_legalized (register_lookup mideleg s.(sregs)) v),
            set_reg s mideleg (mideleg_legalized (register_lookup mideleg s.(sregs)) v)).
Proof.
  intro HS. unfold write_CSR.
  skip_csr_false_clauses.
  (* reached the 0x303 clause *)
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_legalize_mideleg (register_lookup mideleg s.(sregs)) v s HS)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mideleg _ s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg _)).
  rewrite register_lookup_set.
  apply exec_returnM.
Qed.

Lemma exec_csr_id_write_callback_mideleg (d : mword 64) s :
  exec (csr_id_write_callback csr_mideleg d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_mideleg d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_execute_csrw_mideleg (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_mideleg (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS,
            set_reg s mideleg
              (mideleg_legalized (register_lookup mideleg s.(sregs))
                 (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hrs1 Hpriv HS.
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_execute_csrw_gpr csr_mideleg rs1 s _
           (mideleg_legalized (register_lookup mideleg s.(sregs))
              ((if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))))).
  
  - exact Hpriv.
  - apply (exec_check_CSR_result_csrw_S csr_mideleg s HS);
      [ vm_compute; reflexivity | vm_compute; reflexivity | csr_dispatch_eq | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_mideleg; exact HS.
  - apply exec_csr_id_write_callback_mideleg.
Qed.
(* ====================================================================== *)
(* mideleg (0x303, Ext_S, legalize_mideleg) — MONADIC legalize; symbolic.  *)
(* WRITTEN register coincides with the interrupt-zero frame (coercion).    *)
(* ====================================================================== *)


(* ===================================================================== *)
(* sie (0x104, _S): legalize_sie is PURE; write_CSR threads read mie +    *)
(* read mideleg + write mie + readback.  Writes mie (no frame collision). *)
(* ===================================================================== *)
Definition csr_sie : mword 12 := mword_of_int 0x104.

Definition sie_new_mie (mie0 mdl0 v : mword 64) : mword 64 := legalize_sie mie0 mdl0 v.

Lemma exec_write_CSR_sie (v : mword 64) s :
  exec (write_CSR csr_sie v) s
    = Some (Ok (lower_mie (sie_new_mie (register_lookup mie s.(sregs)) (register_lookup mideleg s.(sregs)) v)
                          (register_lookup mideleg s.(sregs))),
            set_reg s mie (sie_new_mie (register_lookup mie s.(sregs)) (register_lookup mideleg s.(sregs)) v)).
Proof.
  unfold write_CSR, sie_new_mie.
  skip_csr_false_clauses.
  (* reached the 0x104 clause *)
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mie _ s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie (set_reg s mie _))).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg (set_reg s mie _))).
  rewrite register_lookup_set.
  rewrite irrelevant_register_set; [|vm_compute; reflexivity].
  apply exec_returnM.
Qed.

(* sie's write has NO legalization sub-monad: the value is the pure
   [legalize_sie] of the two cells it reads, so the whole write is one walk. *)
Lemma write_CSR_sie_red (v : mword 64) :
  write_CSR csr_sie v
  = Defs.bind (Defs.read_reg mie)
      (fun o : mword 64 =>
         Defs.bind (Defs.read_reg mideleg)
           (fun d : mword 64 =>
              Defs.bind (Defs.bind0 (Defs.write_reg mie (legalize_sie o d v))
                           (Defs.read_reg mie))
                (fun m2 : mword 64 =>
                   Defs.bind (Defs.read_reg mideleg)
                     (fun d2 : mword 64 => returnM (Ok (lower_mie m2 d2)))))).
Proof. unfold write_CSR, csr_sie. drive_csr_term. reflexivity. Qed.

Lemma hfrun_write_CSR_sie (D Drw : gset register) (rs : regstate)
    (v : mword 64) :
  (mie : register) ∈ D -> (mie : register) ∈ Drw ->
  (mideleg : register) ∈ D ->
  hfrun 8 D Drw rs (write_CSR csr_sie v)
  = Some (Ok (lower_mie (sie_new_mie (register_lookup mie rs)
                           (register_lookup mideleg rs) v)
                (register_lookup mideleg rs)),
          register_set mie (sie_new_mie (register_lookup mie rs)
                              (register_lookup mideleg rs) v) rs).
Proof.
  intros HD HW HDd. rewrite write_CSR_sie_red /sie_new_mie.
  cbn beta iota zeta delta [Defs.bind Defs.bind0 Interface.iMon_bind
    Defs.read_reg Defs.write_reg Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD).
  cbn beta iota zeta delta [Defs.bind Defs.bind0 Interface.iMon_bind
    Defs.read_reg Defs.write_reg Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HDd).
  cbn beta iota zeta delta [Defs.bind Defs.bind0 Interface.iMon_bind
    Defs.read_reg Defs.write_reg Defs.returnm returnM].
  rewrite hfrun_write (bool_decide_eq_true_2 _ HW).
  cbn beta iota zeta delta [Defs.bind Defs.bind0 Interface.iMon_bind
    Defs.read_reg Defs.write_reg Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD) register_lookup_set.
  cbn beta iota zeta delta [Defs.bind Defs.bind0 Interface.iMon_bind
    Defs.read_reg Defs.write_reg Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HDd).
  rewrite (irrelevant_register_set mideleg mie _ _
             ltac:(vm_compute; reflexivity)).
  cbn beta iota zeta delta [Defs.returnm returnM].
  apply hfrun_ret.
Qed.

Lemma exec_csr_id_write_callback_sie (d : mword 64) s :
  exec (csr_id_write_callback csr_sie d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_sie d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_execute_csrw_sie (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_sie (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS,
            set_reg s mie
              (sie_new_mie (register_lookup mie s.(sregs)) (register_lookup mideleg s.(sregs))
                 (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hrs1 Hpriv HS.
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_execute_csrw_gpr csr_sie rs1 s _
           (lower_mie (sie_new_mie (register_lookup mie s.(sregs)) (register_lookup mideleg s.(sregs))
                         ((if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))))
                      (register_lookup mideleg s.(sregs)))).
  
  - exact Hpriv.
  - apply (exec_check_CSR_result_csrw_S csr_sie s HS);
      [ vm_compute; reflexivity | vm_compute; reflexivity | csr_dispatch_eq | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_sie.
  - apply exec_csr_id_write_callback_sie.
Qed.

(* ---- sie forward/clean/wp: writes mie; value reads mie + mideleg ---- *)


(* ===================================================================== *)
(* satp (0x180): architecture(Supervisor) + legalize_satp mode case-split *)
(* ===================================================================== *)
Lemma exec_hartSupports_Sv48 s : exec (hartSupports Ext_Sv48) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Sv48) 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  replace (andb true (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

Lemma exec_hartSupports_Sv57 s : exec (hartSupports Ext_Sv57) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Sv57) 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  replace (andb true (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

(* discharge an inner `_rec_currentlyEnabled Ext_S k a` (concrete k) to misa.S *)
Ltac crush_rec_cE_S s :=
  match goal with |- context[_rec_currentlyEnabled Ext_S ?k ?a] =>
    let H := fresh "HrecS" in
    assert (H : exec (_rec_currentlyEnabled Ext_S k a) s
                = Some (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1"), s));
    [ destruct a; cbn [_rec_currentlyEnabled]; unfold Defs.assert_exp';
      match goal with |- context[Z.geb ?kk 0] => replace (Z.geb kk 0) with true by reflexivity end;
      cbn match; rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)); cbn match;
      rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_S s)); cbn match;
      rewrite (exec_and_boolM_Some _ _ s
                 (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) s);
      [ destruct (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) eqn:?;
        [ match goal with |- context[_rec_currentlyEnabled Ext_Zicsr ?k2 ?a2] =>
            exact (exec_rec_cE_Zicsr_any k2 a2 s ltac:(reflexivity)) end
        | reflexivity ]
      | rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa s)); apply exec_returnM ]
    | rewrite H ]
  end.

Lemma exec_currentlyEnabled_Svbare s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (currentlyEnabled Ext_Svbare) s = Some (true, s).
Proof.
  intro HS. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Svbare) 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  crush_rec_cE_S s. rewrite HS. reflexivity.
Qed.

Lemma exec_currentlyEnabled_Sv39w s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (currentlyEnabled Ext_Sv39) s = Some (true, s).
Proof.
  intro HS. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Sv39) 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Sv39 s)). cbn match.
  crush_rec_cE_S s. rewrite HS. reflexivity.
Qed.

Lemma exec_currentlyEnabled_Sv48w s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (currentlyEnabled Ext_Sv48) s = Some (true, s).
Proof.
  intro HS. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Sv48) 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Sv48 s)). cbn match.
  crush_rec_cE_S s. rewrite HS. reflexivity.
Qed.

Lemma exec_currentlyEnabled_Sv57w s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (currentlyEnabled Ext_Sv57) s = Some (true, s).
Proof.
  intro HS. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Sv57) 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Sv57 s)). cbn match.
  crush_rec_cE_S s. rewrite HS. reflexivity.
Qed.

(* [exec_architecture_Supervisor] is a privilege-generic model fact, not a
   CSRW one -- it lives in ExecCommon.v so the page-table files can reach
   it without importing this whole family. *)

Definition csr_satp : mword 12 := mword_of_int 0x180.

Definition satp_legalized (prev value : mword 64) : mword 64 :=
  match satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64 value)) with
  | Some Bare => Mk_Satp64 value
  | Some Sv39 => Mk_Satp64 value
  | Some Sv48 => Mk_Satp64 value
  | Some Sv57 => Mk_Satp64 value
  | Some Sv32 => prev
  | None => prev
  end.

Lemma exec_legalize_satp_rv64 (prev value : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (legalize_satp RV64 prev value) s = Some (satp_legalized prev value, s).
Proof.
  intro HS. unfold legalize_satp, satp_legalized.
  (* the PPN mask (min (physaddr_bits - pagesize_bits) 44 = 44 here) writes the
     field back with its own value, so it drops out and the mode dispatch is on
     the written value exactly as before *)
  cbn zeta.
  rewrite satp_ppn_mask_id.
  destruct (satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64 value))) as [sv|] eqn:Hm.
  - destruct sv.
    + rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Svbare s HS)). cbn match. apply exec_returnM.
    + apply exec_returnM.
    + rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Sv39w s HS)). cbn match. apply exec_returnM.
    + rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Sv48w s HS)). cbn match. apply exec_returnM.
    + rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Sv57w s HS)). cbn match. apply exec_returnM.
  - apply exec_returnM.
Qed.

Lemma exec_write_CSR_satp (v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  exec (write_CSR csr_satp v) s
    = Some (Ok (satp_legalized (register_lookup satp s.(sregs)) v),
            set_reg s satp (satp_legalized (register_lookup satp s.(sregs)) v)).
Proof.
  intros HS HSXL. unfold write_CSR.
  skip_csr_false_clauses.
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_architecture_Supervisor s HSXL)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_legalize_satp_rv64 (register_lookup satp s.(sregs)) v s HS)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg satp _ s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp _)).
  rewrite register_lookup_set.
  apply exec_returnM.
Qed.

(* the walker's view.  [architecture Supervisor] reads mstatus, whose value is
   the kernel's and NOT the reference state's, so it is walked rather than
   goodb-transported; [legalize_satp] reads only misa, so it IS transported. *)
Lemma write_CSR_satp_red (v : mword 64) :
  write_CSR csr_satp v
  = Defs.bind (architecture Supervisor)
      (fun a : Architecture =>
         Defs.bind (Defs.read_reg satp)
           (fun o : mword 64 =>
              Defs.bind (legalize_satp a o v)
                (fun c : mword 64 =>
                   Defs.bind (Defs.bind0 (Defs.write_reg satp c)
                                (Defs.read_reg satp))
                     (fun c2 : mword 64 => returnM (Ok c2))))).
Proof. unfold write_CSR, csr_satp. drive_csr_term. reflexivity. Qed.

Lemma hfrun_architecture_Supervisor (D Drw : gset register) (rs : regstate) :
  (mstatus : register) ∈ D ->
  _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
  hfrun 4 D Drw rs (architecture Supervisor) = Some (RV64, rs).
Proof.
  intros HD HSXL. unfold architecture. cbn match.
  cbn beta iota zeta delta [Defs.bind Interface.iMon_bind Defs.read_reg
    Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD).
  cbn beta iota zeta delta [Defs.bind Interface.iMon_bind Defs.returnm returnM].
  unfold architecture_bits_backwards. rewrite HSXL.
  replace (eq_vec ('b"10") ('b"01")) with false by (vm_compute; reflexivity).
  cbn match.
  replace (eq_vec ('b"10") ('b"10")) with true by (vm_compute; reflexivity).
  cbn match. apply hfrun_ret.
Qed.

(* [goodb] cannot be computed at a symbolic [value]: the body branches on the
   satp MODE, which is a field OF that value.  Split the branch first (as the
   exec proof does) and each arm is closed. *)
Lemma goodb_legalize_satp_rv64 (prev value : mword 64) :
  goodb D_m (legalize_satp RV64 prev value) dstateM = true.
Proof.
  unfold legalize_satp. cbn zeta. rewrite satp_ppn_mask_id.
  destruct (satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64 value)))
    as [sv|]; [destruct sv|]; vm_compute; reflexivity.
Qed.

Lemma exec_csr_id_write_callback_satp (d : mword 64) s :
  exec (csr_id_write_callback csr_satp d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_satp d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_is_CSR_accessible_satp s :
  exec (is_CSR_accessible csr_satp Machine CSRWrite) s = Some (true, s).
Proof.
  unfold is_CSR_accessible.
  skip_csr_false_clauses.
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  unfold satp_accessible. cbn match. apply exec_hartSupports_S.
Qed.

(* THE SUPERVISOR ARM, AND WHY IT IS ONE LEMMA FOR BOTH ACCESS TYPES.

   satp is the only CSR this kernel touches whose accessibility is not a
   constant: [satp_accessible Supervisor] READS mstatus and answers
   TVM = 0, so it cannot go through [exec_check_CSR_result_read_extS] (or
   any other "is_CSR_accessible csr p acc = currentlyEnabled _" shortcut)
   the way sepc / scause / stval / sie do.  This is the whole of that
   difference, stated once.

   [acc] IS A PARAMETER because the 0x180 dispatch arm of
   [is_CSR_accessible] passes only the privilege on -- the access type is
   dead there.  So the SAME lemma serves the csrw leaf (UserretDefs.v,
   satp restore on the userret path) and the csrr leaf (WpSconfCsr.v,
   prepare_return's [csrr a4,satp]); there is no read/write asymmetry to
   duplicate.  The TVM premise is discharged from [sconf]'s
   [sconf_ms_facts] at the Iris layer, whose last conjunct is exactly it. *)
Lemma exec_is_CSR_accessible_satp_S (acc : CSRAccessType) s :
  eq_vec (_get_Mstatus_TVM (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  exec (is_CSR_accessible csr_satp Supervisor acc) s = Some (true, s).
Proof.
  intro HTVM.
  unfold is_CSR_accessible.
  skip_csr_false_clauses.
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  unfold satp_accessible. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (mword1_zero_of_ne_one _ HTVM).
  replace (eq_vec ('b"0" : mword 1) ('b"0")) with true by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

Lemma exec_execute_csrw_satp (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  exec (execute_CSRReg csr_satp (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS,
            set_reg s satp
              (satp_legalized (register_lookup satp s.(sregs))
                 (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hrs1 Hpriv HS HSXL.
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_execute_csrw_gpr csr_satp rs1 s _
           (satp_legalized (register_lookup satp s.(sregs))
              ((if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))))).
  
  - exact Hpriv.
  - apply (exec_check_CSR_result_csrw_pure csr_satp s);
      [ vm_compute; reflexivity
      | vm_compute; reflexivity
      | apply exec_is_CSR_accessible_satp
      | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_satp; assumption.
  - apply exec_csr_id_write_callback_satp.
Qed.

(* ---- satp forward/clean/wp: writes satp; reads mstatus (MIE + SXL) ---- *)


(* ===================================================================== *)
(* pmpaddr0 (0x3b0): NO currentlyEnabled — pure pmpWriteAddrReg threading  *)
(* + pmpReadAddrReg readback. Config: usable=16, grain=0 (no mask).        *)
(* ===================================================================== *)
Definition csr_pmpaddr0 : mword 12 := mword_of_int 0x3b0.

Definition pmp0_newaddr (cfg : vec (mword 8) 64) (addr : vec (mword 64) 64) (v : mword 64)
  : vec (mword 64) 64 :=
  vec_update_dec addr 0
    (pmpWriteAddr (pmpLocked (vec_access_dec cfg 0)) (pmpTORLocked (vec_access_dec cfg (Z.add 0 1)))
       (vec_access_dec addr 0) v).

Lemma exec_pmpWriteAddrReg_0 (v : mword 64) s :
  exec (pmpWriteAddrReg 0 v) s
    = Some (tt, set_reg s pmpaddr_n
              (pmp0_newaddr (register_lookup pmpcfg_n s.(sregs))
                 (register_lookup pmpaddr_n s.(sregs)) v)).
Proof.
  unfold pmpWriteAddrReg.
  replace (Z.ltb 0 sys_pmp_usable_count) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpaddr_n s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)).
  replace (Z.ltb (Z.add 0 1) 64) with true by (vm_compute; reflexivity). cbn match.
  match goal with |- exec (Defs.bind ?L _) s = _ =>
    assert (Hin : exec L s
                  = Some (pmpTORLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) (Z.add 0 1)), s)) end.
  { rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)). apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hin).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpaddr_n s)).
  unfold pmp0_newaddr. apply exec_write_reg.
Qed.

Lemma exec_pmpReadAddrReg_0 s :
  exec (pmpReadAddrReg 0) s = Some (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0, s).
Proof.
  unfold pmpReadAddrReg.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpaddr_n s)).
  replace (Z.geb sys_pmp_grain 2) with false by (vm_compute; reflexivity).
  replace (Z.geb sys_pmp_grain 1) with false by (vm_compute; reflexivity).
  cbn match. apply exec_returnM.
Qed.

(* readback + Ok-wrap, proved while pmpReadAddrReg is still FOLDED *)
Lemma exec_pmpReadAddrReg_0_ok s :
  exec (Defs.bind (pmpReadAddrReg 0) (fun w => returnM (Ok w) : M (result (mword 64) unit))) s
    = Some (Ok (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0), s).
Proof.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpReadAddrReg_0 s)). apply exec_returnM.
Qed.

Lemma hfrun_pmpWriteAddrReg_0 (D Drw : gset register) (rs : regstate)
    (v : mword 64) :
  (pmpaddr_n : register) ∈ D -> (pmpaddr_n : register) ∈ Drw ->
  (pmpcfg_n : register) ∈ D ->
  hfrun 8 D Drw rs (pmpWriteAddrReg 0 v)
  = Some (tt, register_set pmpaddr_n
                (pmp0_newaddr (register_lookup pmpcfg_n rs)
                   (register_lookup pmpaddr_n rs) v) rs).
Proof.
  intros HDa HWa HDc. unfold pmpWriteAddrReg, pmp0_newaddr.
  replace (Z.ltb 0 sys_pmp_usable_count) with true
    by (vm_compute; reflexivity). cbn match.
  replace (Z.ltb (Z.add 0 1) 64) with true by (vm_compute; reflexivity).
  cbn beta iota zeta delta [Defs.bind Defs.bind0 Interface.iMon_bind
    Defs.read_reg Defs.write_reg Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HDa).
  cbn beta iota zeta delta [Defs.bind Defs.bind0 Interface.iMon_bind
    Defs.read_reg Defs.write_reg Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HDc).
  cbn beta iota zeta delta [Defs.bind Defs.bind0 Interface.iMon_bind
    Defs.read_reg Defs.write_reg Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HDc).
  cbn beta iota zeta delta [Defs.bind Defs.bind0 Interface.iMon_bind
    Defs.read_reg Defs.write_reg Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HDa).
  cbn beta iota zeta delta [Defs.bind Defs.bind0 Interface.iMon_bind
    Defs.read_reg Defs.write_reg Defs.returnm returnM].
  rewrite hfrun_write (bool_decide_eq_true_2 _ HWa).
  apply hfrun_ret.
Qed.

Lemma hfrun_pmpReadAddrReg_0 (D Drw : gset register) (rs : regstate) :
  (pmpaddr_n : register) ∈ D -> (pmpcfg_n : register) ∈ D ->
  hfrun 6 D Drw rs (pmpReadAddrReg 0)
  = Some (vec_access_dec (register_lookup pmpaddr_n rs) 0, rs).
Proof.
  intros HDa HDc. unfold pmpReadAddrReg.
  cbn beta iota zeta delta [Defs.bind Interface.iMon_bind Defs.read_reg
    Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HDc).
  cbn beta iota zeta delta [Defs.bind Interface.iMon_bind Defs.read_reg
    Defs.returnm returnM].
  rewrite hfrun_read (bool_decide_eq_true_2 _ HDa).
  replace (Z.geb sys_pmp_grain 2) with false by (vm_compute; reflexivity).
  replace (Z.geb sys_pmp_grain 1) with false by (vm_compute; reflexivity).
  cbn beta iota zeta match delta [Defs.returnm returnM].
  apply hfrun_ret.
Qed.

Lemma write_CSR_pmpaddr0_red (v : mword 64) :
  write_CSR csr_pmpaddr0 v
  = Defs.bind (Defs.bind0 (pmpWriteAddrReg 0 v) (pmpReadAddrReg 0))
      (fun w : mword 64 => returnM (Ok w)).
Proof.
  unfold write_CSR, csr_pmpaddr0. drive_csr_term.
  replace (uint (concat_vec ('b"00" : mword 2)
                   (subrange_vec_dec (mword_of_int 944 : mword 12) 3 0))) with 0
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma hfrun_write_CSR_pmpaddr0 (D Drw : gset register) (rs : regstate)
    (v : mword 64) :
  (pmpaddr_n : register) ∈ D -> (pmpaddr_n : register) ∈ Drw ->
  (pmpcfg_n : register) ∈ D ->
  hfrun 15 D Drw rs (write_CSR csr_pmpaddr0 v)
  = Some (Ok (vec_access_dec
                (pmp0_newaddr (register_lookup pmpcfg_n rs)
                   (register_lookup pmpaddr_n rs) v) 0),
          register_set pmpaddr_n
            (pmp0_newaddr (register_lookup pmpcfg_n rs)
               (register_lookup pmpaddr_n rs) v) rs).
Proof.
  intros HDa HWa HDc. rewrite write_CSR_pmpaddr0_red.
  set (na := pmp0_newaddr (register_lookup pmpcfg_n rs)
               (register_lookup pmpaddr_n rs) v).
  set (rs' := register_set pmpaddr_n na rs).
  assert (Hin : hfrun 14 D Drw rs
                  (Defs.bind0 (pmpWriteAddrReg 0 v) (pmpReadAddrReg 0))
                = Some (vec_access_dec na 0, rs')).
  { apply (hfrun_bind0 8 6 D Drw rs rs' rs' _ _ (vec_access_dec na 0)).
    - apply (hfrun_pmpWriteAddrReg_0 D Drw rs v HDa HWa HDc).
    - rewrite (hfrun_pmpReadAddrReg_0 D Drw rs' HDa HDc).
      subst rs'. by rewrite register_lookup_set. }
  apply (hfrun_bind 14 1 D Drw rs rs' rs' _ _ (vec_access_dec na 0) _ Hin).
  apply hfrun_ret.
Qed.

Lemma exec_write_CSR_pmpaddr0 (v : mword 64) s :
  exec (write_CSR csr_pmpaddr0 v) s
    = Some (Ok (vec_access_dec
                  (register_lookup pmpaddr_n
                     (set_reg s pmpaddr_n (pmp0_newaddr (register_lookup pmpcfg_n s.(sregs))
                        (register_lookup pmpaddr_n s.(sregs)) v)).(sregs)) 0),
            set_reg s pmpaddr_n (pmp0_newaddr (register_lookup pmpcfg_n s.(sregs))
              (register_lookup pmpaddr_n s.(sregs)) v)).
Proof.
  unfold write_CSR.
  skip_csr_false_clauses.
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  cbn zeta.
  replace (uint (concat_vec ('b"00") (subrange_vec_dec csr_pmpaddr0 3 0))) with 0
    by (vm_compute; reflexivity).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_pmpWriteAddrReg_0 v s)).
  exact (exec_pmpReadAddrReg_0_ok
           (set_reg s pmpaddr_n (pmp0_newaddr (register_lookup pmpcfg_n s.(sregs))
              (register_lookup pmpaddr_n s.(sregs)) v))).
Qed.

Lemma exec_csr_id_write_callback_pmpaddr0 (d : mword 64) s :
  exec (csr_id_write_callback csr_pmpaddr0 d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_pmpaddr0 d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_execute_csrw_pmpaddr0 (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (execute_CSRReg csr_pmpaddr0 (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS,
            set_reg s pmpaddr_n
              (pmp0_newaddr (register_lookup pmpcfg_n s.(sregs))
                 (register_lookup pmpaddr_n s.(sregs))
                 (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hrs1 Hpriv.
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_execute_csrw_gpr csr_pmpaddr0 rs1 s _
           (vec_access_dec
              (register_lookup pmpaddr_n
                 (set_reg s pmpaddr_n (pmp0_newaddr (register_lookup pmpcfg_n s.(sregs))
                    (register_lookup pmpaddr_n s.(sregs))
                    ((if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))))).(sregs)) 0)).
  
  - exact Hpriv.
  - apply (exec_check_CSR_result_csrw_pure csr_pmpaddr0 s);
      [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_pmpaddr0.
  - apply exec_csr_id_write_callback_pmpaddr0.
Qed.

(* ---- pmpaddr0 forward/clean/wp: writes vec pmpaddr_n; reads pmpcfg_n ---- *)


(* ===================================================================== *)
(* stimecmp (0x14D): Sstc-gated; legalize = update_subrange 63 0 (pure)  *)
(* ===================================================================== *)
Definition csr_stimecmp : mword 12 := mword_of_int 0x14d.

Definition stimecmp_legalized (prev v : mword 64) : mword 64 :=
  update_subrange_vec_dec prev (Z.sub xlen 1) 0 v.

Lemma exec_is_stimecmp_accessible_M s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (is_stimecmp_accessible Machine) s = Some (true, s).
Proof.
  intro HS. unfold is_stimecmp_accessible.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_currentlyEnabled_S s)). rewrite HS. cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_currentlyEnabled_Sstc s)). cbn match.
  apply exec_returnM.
Qed.

Lemma exec_is_CSR_accessible_stimecmp s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (is_CSR_accessible csr_stimecmp Machine CSRWrite) s = Some (true, s).
Proof.
  intro HS. unfold is_CSR_accessible.
  skip_csr_false_clauses.
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  apply (exec_is_stimecmp_accessible_M s HS).
Qed.

(* Writing stimecmp REFRESHES THE TIMER-PENDING BITS: the CSR write runs
   [clint_dispatch false] between the register write and the read-back, setting
   mip.MTIP from (mtimecmp <=u mtime) and -- under Sstc with menvcfg.STCE --
   mip.STIP from (stimecmp <=u mtime).  So the post-state gains an mip write and
   this contract is existential in that value; mip lives in the value-agnostic
   [clock_inv], so the WP consumers re-establish the invariant with whatever
   comes out.  [set] holds [clint_dispatch] opaque across the CSR-clause peel:
   the [cbn match] that resolves the address dispatch would otherwise inline it
   into a raw monad-bind fixpoint that no [rewrite] can fold back. *)
Lemma exec_write_CSR_stimecmp (v : mword 64) s :
  exists mp : mword 64,
  exec (write_CSR csr_stimecmp v) s
    = Some (Ok (subrange_vec_dec (stimecmp_legalized (register_lookup stimecmp s.(sregs)) v) (Z.sub xlen 1) 0),
            set_reg (set_reg s stimecmp (stimecmp_legalized (register_lookup stimecmp s.(sregs)) v)) mip mp).
Proof.
  destruct (MinstretInv.exec_clint_dispatch_false
              (set_reg s stimecmp (stimecmp_legalized (register_lookup stimecmp s.(sregs)) v)))
    as [mp Hcd].
  exists mp.
  unfold stimecmp_legalized in Hcd |- *.
  unfold write_CSR.
  (* [remember], not [set]: the clause peel's rewrites zeta-expand a let-bound
     body, and the moment [clint_dispatch] is exposed the surrounding [exec]
     reduces it into a raw monad-bind fixpoint that no [rewrite] can fold back.
     A body-less variable cannot be expanded.  (It abstracts [Hcd] too, so
     [Hcd] below is already stated at [CD].) *)
  remember (clint_dispatch false) as CD eqn:HCD.
  skip_csr_false_clauses.
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg stimecmp s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg stimecmp _ s)).
  (* the peel left the remaining two binds delta-unfolded into the raw monad
     fixpoint; [reflexivity] folds them back *)
  match goal with |- exec ?M ?st = _ =>
    assert (HM : M = Defs.bind (Defs.bind0 CD (Defs.read_reg stimecmp))
                       (fun w : mword 64 => returnM (Ok (subrange_vec_dec w (Z.sub xlen 1) 0))))
      by reflexivity end.
  rewrite HM.
  match goal with |- exec (Defs.bind ?A _) ?st = _ =>
    assert (Hin : exec A st = Some (register_lookup stimecmp st.(sregs), set_reg st mip mp)) end.
  { rewrite (exec_bind0_Some _ _ _ _ _ Hcd).
    rewrite (exec_read_reg stimecmp _).
    rewrite sregs_set_reg.
    rewrite irrelevant_register_set; [ reflexivity | vm_compute; reflexivity ]. }
  rewrite (exec_bind_Some _ _ _ _ _ Hin).
  rewrite sregs_set_reg. rewrite register_lookup_set.
  apply exec_returnM.
Qed.

Lemma exec_csr_id_write_callback_stimecmp (d : mword 64) s :
  exec (csr_id_write_callback csr_stimecmp d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_stimecmp d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_execute_csrw_stimecmp (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exists mp : mword 64,
  exec (execute_CSRReg csr_stimecmp (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS,
            set_reg (set_reg s stimecmp
              (stimecmp_legalized (register_lookup stimecmp s.(sregs))
                 (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))) mip mp).
Proof.
  intros Hrs1 Hpriv HS.
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  destruct (exec_write_CSR_stimecmp
              (if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) s)
    as [mp Hw].
  exists mp.
  apply (exec_execute_csrw_gpr csr_stimecmp rs1 s _
           (subrange_vec_dec (stimecmp_legalized (register_lookup stimecmp s.(sregs))
              ((if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))) (Z.sub xlen 1) 0)).
  - exact Hpriv.
  - apply (exec_check_CSR_result_csrw csr_stimecmp s).
    apply exec_check_CSR_csrw;
      [ vm_compute; reflexivity
      | vm_compute; reflexivity
      | apply (exec_is_CSR_accessible_stimecmp s HS)
      | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - exact Hw.
  - apply exec_csr_id_write_callback_stimecmp.
Qed.

(* ===================================================================== *)
(* stvec (0x105): Ext_S-gated; legalize = legalize_tvec at the platform's *)
(* stvec parameters.  The S-mode accessibility/execute instances are in   *)
(* WpSconfCsr.v (no M-mode code writes stvec).                            *)
(* ===================================================================== *)
Definition csr_stvec : mword 12 := mword_of_int 0x105.

(* [legalize_tvec] with direct AND vectored mode both supported and both
   base alignments = 2 -- which is what the platform hands [set_stvec] -- is
   the IDENTITY on any value whose MODE field is not the reserved encoding:
   neither the mode fixup nor the base masking fires.  The previous value
   [o] is read only on the reserved arm. *)
Lemma exec_legalize_tvec_stvec (o v : mword 64) s :
  trapVectorMode_forwards (_get_Mtvec_Mode v) <> TV_Reserved ->
  exec (legalize_tvec o v plat_stvec_direct_mode_supported 2
          plat_stvec_vectored_mode_supported plat_stvec_vectored_base_alignment_exp) s
    = Some (v, s).
Proof.
  intro Hm. unfold legalize_tvec, Mk_Mtvec.
  unfold plat_stvec_direct_mode_supported, plat_stvec_vectored_mode_supported,
    plat_stvec_vectored_base_alignment_exp.
  destruct (trapVectorMode_forwards (_get_Mtvec_Mode v)) eqn:Hmode;
    [ | | contradiction ].
  - rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM v s)). rewrite Hmode.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM 2 s)). apply exec_returnM.
  - rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM v s)). rewrite Hmode.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM 2 s)). apply exec_returnM.
Qed.

(* [set_stvec] is a helper the write_CSR dispatch CALLS, so the whole
   read/legalize/write/read-back chain is peeled HERE: at the dispatch the
   term is left-nested ([set_stvec v >>= ...]) and the inner binds are not
   directly under an [exec]. *)
Lemma exec_set_stvec (v : mword 64) s :
  trapVectorMode_forwards (_get_Mtvec_Mode v) <> TV_Reserved ->
  exec (set_stvec v) s = Some (v, set_reg s stvec v).
Proof.
  intro Hm. unfold set_stvec.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg stvec s)).
  rewrite (exec_bind_Some _ _ _ _ _
             (exec_legalize_tvec_stvec (register_lookup stvec s.(sregs)) v s Hm)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg stvec v s)).
  rewrite (exec_read_reg stvec (set_reg s stvec v)).
  rewrite register_lookup_set. reflexivity.
Qed.

Lemma exec_write_CSR_stvec (v : mword 64) s :
  trapVectorMode_forwards (_get_Mtvec_Mode v) <> TV_Reserved ->
  exec (write_CSR csr_stvec v) s = Some (Ok v, set_reg s stvec v).
Proof.
  intro Hm. unfold write_CSR.
  skip_csr_false_clauses.
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_set_stvec v s Hm)).
  apply exec_returnM.
Qed.

Lemma exec_csr_id_write_callback_stvec (d : mword 64) s :
  exec (csr_id_write_callback csr_stvec d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_stvec d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

(* ====================================================================== *)
(* NEW-STYLE register-generic CSR-WRITE WPs (csrw csr, rs1 = csrrw x0,csr,rs1) *)
(* on the [instr] / [mmode_config] / [gpr_file] layer, built on [wp_instr]. *)
(* Dual of [wp_csrr_mhartid_gpr]: reads rs1 off the [gpr_file] and WRITES    *)
(* the CSR cell, which is threaded as an extra points-to premise (old value  *)
(* in, new/legalized value out).  Reuses the representation-independent      *)
(* execute helpers [exec_execute_csrw_*] verbatim.  A HALF of [mmode_config] *)
(* is kept to recover cur_privilege = Machine (and, where the execute        *)
(* legalizes with misa.S/misa.U or mstatus.SXL, those facts from hw_config / *)
(* the kept mstatus) at the execute state; the halves are recombined for the *)
(* continuation.                                                             *)
(* ====================================================================== *)



Section WpCsrwGprNewB.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  (* ------------------------------------------------------------------ *)
  (* mideleg: [write_CSR]'s menvcfg shape exactly -- read the cell, run a    *)
  (* READ-ONLY legalization, write it back, read it again.  So the           *)
  (* legalization goes through [goodb] (it reads only misa, whose value       *)
  (* [hw_config] pins) and the enclosing read/write are peeled at the frame.  *)
  (* ------------------------------------------------------------------ *)
  Lemma hval_legalize_mideleg (D Drw : gset register) (rs : regstate)
      (o v : mword 64) :
    (cur_privilege : register) ∈ D -> (mseccfg : register) ∈ D ->
    (misa : register) ∈ D ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup mseccfg rs = mword_of_int 0 ->
    register_lookup misa rs = MISA_C ->
    hval D Drw rs (legalize_mideleg o v) (mideleg_legalized o v) rs.
  Proof.
    intros HD1 HD2 HD3 Hp Hs Hm.
    exact (hval_of_goodb D_m D Drw _ dstateM rs (mideleg_legalized o v)
             (dm_sub D HD1 HD2 HD3)
             (agree_m (MState rs ∅ dev0_state) Hp Hs Hm)
             (goodb_legalize_mideleg o v)
             (exec_legalize_mideleg o v dstateM
                ltac:(vm_compute; reflexivity))).
  Qed.

  Lemma swp_write_CSR_mideleg (dq : dfrac) (mideleg0 v : mword 64) :
    cw_fresh mideleg ->
    gen_cert -∗
    (hreg_frame (cw_rs mideleg mideleg0) (cw_Drw mideleg) -∗
     hreg_frame_ro (cw_Df dq) (cw_rs mideleg mideleg0) cw_Dro -∗
     swp (write_CSR csr_mideleg v)
       (fun x => ⌜x = Ok (mideleg_legalized mideleg0 v)⌝ ∗
          hreg_frame (cw_rs mideleg (mideleg_legalized mideleg0 v))
            (cw_Drw mideleg) ∗
          hreg_frame_ro (cw_Df dq)
            (cw_rs mideleg (mideleg_legalized mideleg0 v)) cw_Dro)).
  Proof.
    intros Hfresh. iIntros "#Hcert Hrw Hro".
    rewrite write_CSR_mideleg_red.
    iApply (swp_bind_use (Defs.read_reg mideleg) _
              (fun o => ⌜o = mideleg0⌝ ∗
                 hreg_frame (cw_rs mideleg mideleg0) (cw_Drw mideleg) ∗
                 hreg_frame_ro (cw_Df dq) (cw_rs mideleg mideleg0) cw_Dro)%I _
              with "[Hrw Hro] [-]").
    { iApply (swp_mono with "[] [-]");
        [| iApply (swp_read_reg_pinned (cw_Drw mideleg) cw_Dro (cw_Df dq)
                     (cw_rs mideleg mideleg0) mideleg (cw_disj mideleg Hfresh)
                     (cw_in_r mideleg) with "Hcert Hrw Hro") ].
      iIntros (o) "(-> & Hrw & Hro)".
      rewrite (cw_rs_r mideleg mideleg0). by iFrame. }
    iIntros (o) "(-> & Hrw & Hro)".
    iApply (swp_bind_use (legalize_mideleg mideleg0 v) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_span (cw_Drw mideleg) cw_Dro (cw_Df dq)
                (cw_rs mideleg mideleg0) (cw_rs mideleg mideleg0) _ _
                (cw_disj mideleg Hfresh)
                (hval_legalize_mideleg (cw_Drw mideleg ∪ cw_Dro)
                   (cw_Drw mideleg) (cw_rs mideleg mideleg0) mideleg0 v
                   (cw_in_priv mideleg) (cw_in_sec mideleg)
                   (cw_in_misa mideleg)
                   (cw_rs_priv mideleg mideleg0 Hfresh)
                   (cw_rs_sec mideleg mideleg0 Hfresh)
                   (cw_rs_misa mideleg mideleg0 Hfresh))
                with "Hcert Hrw Hro"). }
    iIntros (c) "(-> & Hrw & Hro)".
    iApply (swp_bind_use _ _
              (fun c2 => ⌜c2 = mideleg_legalized mideleg0 v⌝ ∗
                 hreg_frame (cw_rs mideleg (mideleg_legalized mideleg0 v))
                   (cw_Drw mideleg) ∗
                 hreg_frame_ro (cw_Df dq)
                   (cw_rs mideleg (mideleg_legalized mideleg0 v)) cw_Dro)%I _
              with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ => hreg_frame
                   (cw_rs mideleg (mideleg_legalized mideleg0 v))
                   (cw_Drw mideleg) ∗
                   hreg_frame_ro (cw_Df dq)
                     (cw_rs mideleg (mideleg_legalized mideleg0 v)) cw_Dro)%I _
                with "[Hrw Hro] [-]").
      { iApply (swp_mono with "[] [-]");
          [| iApply (swp_write_reg_owned (cw_Drw mideleg) cw_Dro (cw_Df dq)
                       (cw_rs mideleg mideleg0) mideleg _
                       (cw_disj mideleg Hfresh) (cw_w_r mideleg)
                       with "Hcert Hrw Hro") ].
        iIntros (u) "[Hrw Hro]".
        iDestruct (cw_rw_ext mideleg _ _
                     (reg_agree_l _ _ _ _
                        (cw_set_agree mideleg mideleg0 _ Hfresh)) with "Hrw")
          as "Hrw".
        iDestruct (cw_ro_ext dq _ _
                     (reg_agree_r _ _ _ _
                        (cw_set_agree mideleg mideleg0 _ Hfresh)) with "Hro")
          as "Hro".
        by iFrame. }
      iIntros (u) "[Hrw Hro]".
      iApply (swp_mono with "[] [-]");
        [| iApply (swp_read_reg_pinned (cw_Drw mideleg) cw_Dro (cw_Df dq)
                     (cw_rs mideleg (mideleg_legalized mideleg0 v)) mideleg
                     (cw_disj mideleg Hfresh) (cw_in_r mideleg)
                     with "Hcert Hrw Hro") ].
      iIntros (c2) "(-> & Hrw & Hro)".
      rewrite (cw_rs_r mideleg (mideleg_legalized mideleg0 v)). by iFrame. }
    iIntros (c2) "(-> & Hrw & Hro)".
    iApply swp_ret. iSplitR; [done|]. iFrame.
  Qed.

  (* ---- mideleg ---- *)
  Lemma wp_csrw_mideleg_gpr (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (mideleg0 : type_of_register mideleg)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    mideleg ↦ᵣ mideleg0 -∗
    instr pc false (CSRReg (csr_mideleg, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      mideleg ↦ᵣ mideleg_legalized mideleg0 (m !!! Regidx rs1) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrs1) "Hmm Hpmpc Hpc Hf Hcsr Hinstr Hcont".
    assert (Hfresh : cw_fresh mideleg)
      by (rewrite /cw_fresh; split_and!; vm_compute; reflexivity).
    assert (Hchk : exec (check_CSR_result csr_mideleg Machine CSRWrite) dstateM
                   = Some (CSR_Check_OK tt, dstateM))
      by (vm_compute; reflexivity).
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & %Hmisaval & %Hsecval & _)".
    subst misa0 mseccfg0.
    iApply (wp_instr pc (add_vec_int pc 4) false
              (CSRReg (csr_mideleg, Regidx rs1, zreg, CSRRW)) m m pmpcfg0
              (mmode_config (DfracOwn (q/2)) ∗
               pmpcfg_n ↦ᵣ{DfracOwn (q/2)} pmpcfg0 ∗
               mideleg ↦ᵣ mideleg_legalized mideleg0 (m !!! Regidx rs1))%I
              Hpmp Hstat
              with "Hmm_wp Hpmpc_wp Hpc Hf Hinstr
                    [Hhs_k Hpriv_k Hmst_k Hpmpc_k Hcsr] [Hcont]").
    - iIntros "Hf HPC HnPC".
      iDestruct (cw_frames_in (DfracOwn (q/2)) mideleg mideleg0 Hfresh
                   with "Hcsr Hpriv_k Hmseccfg Hmisa") as "[Hrw Hro]".
      iApply (swp_mono with "[HPC HnPC Hhs_k Hmst_k Hpmpc_k] [Hf Hrw Hro]");
        [| iApply (swp_execute_CSRReg_csrw (cw_Drw mideleg) cw_Dro
                     (cw_Df (DfracOwn (q/2))) (cw_rs mideleg mideleg0)
                     (cw_rs mideleg
                        (mideleg_legalized mideleg0 (m !!! Regidx rs1))) m
                     csr_mideleg rs1 _ (cw_disj mideleg Hfresh)
                     (cw_in_priv mideleg) (cw_in_sec mideleg)
                     (cw_in_misa mideleg)
                     (cw_rs_priv mideleg mideleg0 Hfresh)
                     (cw_rs_sec mideleg mideleg0 Hfresh)
                     (cw_rs_misa mideleg mideleg0 Hfresh)
                     ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)
                     Hchk
                     ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)
                     with "Hcert Hf Hrw Hro [Hcert]") ].
      + iIntros (e) "(-> & Hf & Hrw & Hro)".
        iDestruct (cw_frames_out (DfracOwn (q/2)) mideleg _ Hfresh
                     with "[$Hrw $Hro]") as "(Hcsr & Hpriv_k & _ & _)".
        iSplitR; [done|]. iFrame "Hf HPC HnPC".
        iSplitL "Hhs_k Hpriv_k Hmst_k".
        { iFrame "Hhw Hhs_k Hpriv_k Hmst_k". }
        iFrame "Hpmpc_k Hcsr".
      + iApply (swp_write_CSR_mideleg (DfracOwn (q/2)) mideleg0
                  (m !!! Regidx rs1) Hfresh with "Hcert").
    - iNext. iIntros "Hmm' Hpmpc' Hpc' Hf' (Hmm_k' & Hpmpc_k' & Hcsr')".
      iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
      iCombine "Hpmpc' Hpmpc_k'" as "Hpmpc''".
      iApply ("Hcont" with "Hmm'' Hpmpc'' Hpc' Hf' Hcsr'").
  Qed.


  (* ---- sie (Ext_S): writes mie; value reads old mie + old mideleg ---- *)
  Lemma wp_csrw_sie_gpr (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (mie0 mideleg0 : type_of_register mie)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    mie ↦ᵣ mie0 -∗
    mideleg ↦ᵣ mideleg0 -∗
    instr pc false (CSRReg (csr_sie, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      mie ↦ᵣ sie_new_mie mie0 mideleg0 (m !!! Regidx rs1) -∗
      mideleg ↦ᵣ mideleg0 -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrs1) "Hmm Hpmpc Hpc Hf Hmie Hmdl Hinstr Hcont".
    assert (Hok : cw2_ok mie mideleg).
    { rewrite /cw2_ok /cw_fresh. split_and!;
        first [ vm_compute; reflexivity | intros HX; discriminate HX ]. }
    pose proof Hok as (Hfresh & _ & _).
    assert (Hchk : exec (check_CSR_result csr_sie Machine CSRWrite) dstateM
                   = Some (CSR_Check_OK tt, dstateM))
      by (vm_compute; reflexivity).
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & %Hmisaval & %Hsecval & _)".
    subst misa0 mseccfg0.
    iApply (wp_instr pc (add_vec_int pc 4) false
              (CSRReg (csr_sie, Regidx rs1, zreg, CSRRW)) m m pmpcfg0
              (mmode_config (DfracOwn (q/2)) ∗
               pmpcfg_n ↦ᵣ{DfracOwn (q/2)} pmpcfg0 ∗
               mie ↦ᵣ sie_new_mie mie0 mideleg0 (m !!! Regidx rs1) ∗
               mideleg ↦ᵣ mideleg0)%I
              Hpmp Hstat
              with "Hmm_wp Hpmpc_wp Hpc Hf Hinstr
                    [Hhs_k Hpriv_k Hmst_k Hpmpc_k Hmie Hmdl] [Hcont]").
    - iIntros "Hf HPC HnPC".
      iDestruct (cw2_frames_in (DfracOwn (q/2)) (DfracOwn 1) mie mie0
                   mideleg mideleg0 Hok
                   with "Hmie Hmdl Hpriv_k Hmseccfg Hmisa") as "[Hrw Hro]".
      iApply (swp_mono with "[HPC HnPC Hhs_k Hmst_k Hpmpc_k] [Hf Hrw Hro]");
        [| iApply (swp_execute_CSRReg_csrw (cw_Drw mie) (cw2_Dro mideleg)
                     (cw2_Df (DfracOwn (q/2)) (DfracOwn 1) mideleg)
                     (cw2_rs mie mie0 mideleg mideleg0)
                     (cw2_rs mie (sie_new_mie mie0 mideleg0 (m !!! Regidx rs1))
                        mideleg mideleg0) m
                     csr_sie rs1 _ (cw2_disj mie mideleg Hok)
                     (cw2_in_priv mie mideleg) (cw2_in_sec mie mideleg)
                     (cw2_in_misa mie mideleg)
                     (cw2_rs_priv mie mie0 mideleg mideleg0 Hok)
                     (cw2_rs_sec mie mie0 mideleg mideleg0 Hok)
                     (cw2_rs_misa mie mie0 mideleg mideleg0 Hok)
                     ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)
                     Hchk
                     ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)
                     with "Hcert Hf Hrw Hro [Hcert]") ].
      + iIntros (e) "(-> & Hf & Hrw & Hro)".
        iDestruct (cw2_frames_out (DfracOwn (q/2)) (DfracOwn 1) mie _
                     mideleg mideleg0 Hok with "[$Hrw $Hro]")
          as "(Hmie & Hmdl & Hpriv_k & _ & _)".
        iSplitR; [done|]. iFrame "Hf HPC HnPC".
        iSplitL "Hhs_k Hpriv_k Hmst_k".
        { iFrame "Hhw Hhs_k Hpriv_k Hmst_k". }
        iFrame "Hpmpc_k Hmie Hmdl".
      + iIntros "Hrw Hro".
        iApply (swp_mono with "[] [-]");
          [| iApply (swp_hfrun 8 (cw_Drw mie) (cw2_Dro mideleg)
                       (cw2_Df (DfracOwn (q/2)) (DfracOwn 1) mideleg)
                       (cw2_rs mie mie0 mideleg mideleg0) _ _ _
                       (cw2_disj mie mideleg Hok)
                       (hfrun_write_CSR_sie
                          (cw_Drw mie ∪ cw2_Dro mideleg) (cw_Drw mie)
                          (cw2_rs mie mie0 mideleg mideleg0)
                          (m !!! Regidx rs1)
                          (cw2_in_r mie mideleg) (cw2_w_r mie mideleg)
                          (cw2_in_r2 mie mideleg))
                       with "Hcert Hrw Hro") ].
        iIntros (x) "(-> & Hrw & Hro)".
        rewrite (cw2_rs_r mie mie0 mideleg mideleg0 Hok)
          (cw2_rs_r2 mie mie0 mideleg mideleg0).
        iDestruct (cw2_rw_ext mie _ _
                     (reg_agree_l _ _ _ _
                        (cw2_set_agree mie mie0 _ mideleg mideleg0 Hok))
                     with "Hrw") as "Hrw".
        iDestruct (cw2_ro_ext (DfracOwn (q/2)) (DfracOwn 1) mideleg _ _
                     (reg_agree_r _ _ _ _
                        (cw2_set_agree mie mie0 _ mideleg mideleg0 Hok))
                     with "Hro") as "Hro".
        iSplitR; [done|]. iFrame.
    - iNext. iIntros "Hmm' Hpmpc' Hpc' Hf' (Hmm_k' & Hpmpc_k' & Hmie' & Hmdl')".
      iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
      iCombine "Hpmpc' Hpmpc_k'" as "Hpmpc''".
      iApply ("Hcont" with "Hmm'' Hpmpc'' Hpc' Hf' Hmie' Hmdl'").
  Qed.

  (* ------------------------------------------------------------------ *)
  (* satp's write, on the ONE-EXTRA-CELL footprint: [architecture           *)
  (* Supervisor] reads mstatus, and mstatus's value is the kernel's rather   *)
  (* than the reference state's, so it is WALKED (with the SXL fact the      *)
  (* leaf already holds) instead of goodb-transported.  The legalization     *)
  (* reads only misa and so IS transported.                                 *)
  (* ------------------------------------------------------------------ *)
  Lemma hval_legalize_satp (D Drw : gset register) (rs : regstate)
      (o v : mword 64) :
    (cur_privilege : register) ∈ D -> (mseccfg : register) ∈ D ->
    (misa : register) ∈ D ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup mseccfg rs = mword_of_int 0 ->
    register_lookup misa rs = MISA_C ->
    hval D Drw rs (legalize_satp RV64 o v) (satp_legalized o v) rs.
  Proof.
    intros HD1 HD2 HD3 Hp Hs Hm.
    exact (hval_of_goodb D_m D Drw _ dstateM rs (satp_legalized o v)
             (dm_sub D HD1 HD2 HD3)
             (agree_m (MState rs ∅ dev0_state) Hp Hs Hm)
             (goodb_legalize_satp_rv64 o v)
             (exec_legalize_satp_rv64 o v dstateM
                ltac:(vm_compute; reflexivity))).
  Qed.

  Lemma swp_write_CSR_satp (dq dq2 : dfrac) (satp0 ms0 v : mword 64) :
    cw2_ok satp mstatus ->
    _get_Mstatus_SXL ms0 = 'b"10" ->
    gen_cert -∗
    (hreg_frame (cw2_rs satp satp0 mstatus ms0) (cw_Drw satp) -∗
     hreg_frame_ro (cw2_Df dq dq2 mstatus) (cw2_rs satp satp0 mstatus ms0)
       (cw2_Dro mstatus) -∗
     swp (write_CSR csr_satp v)
       (fun x => ⌜x = Ok (satp_legalized satp0 v)⌝ ∗
          hreg_frame (cw2_rs satp (satp_legalized satp0 v) mstatus ms0)
            (cw_Drw satp) ∗
          hreg_frame_ro (cw2_Df dq dq2 mstatus)
            (cw2_rs satp (satp_legalized satp0 v) mstatus ms0)
            (cw2_Dro mstatus))).
  Proof.
    intros Hok HSXL. iIntros "#Hcert Hrw Hro".
    rewrite write_CSR_satp_red.
    (* 1. the architecture read, walked *)
    iApply (swp_bind_use (architecture Supervisor) _
              (fun a => ⌜a = RV64⌝ ∗
                 hreg_frame (cw2_rs satp satp0 mstatus ms0) (cw_Drw satp) ∗
                 hreg_frame_ro (cw2_Df dq dq2 mstatus)
                   (cw2_rs satp satp0 mstatus ms0) (cw2_Dro mstatus))%I _
              with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 4 (cw_Drw satp) (cw2_Dro mstatus)
                (cw2_Df dq dq2 mstatus) (cw2_rs satp satp0 mstatus ms0) _ _ _
                (cw2_disj satp mstatus Hok)
                (hfrun_architecture_Supervisor
                   (cw_Drw satp ∪ cw2_Dro mstatus) (cw_Drw satp)
                   (cw2_rs satp satp0 mstatus ms0)
                   (cw2_in_r2 satp mstatus)
                   ltac:(rewrite (cw2_rs_r2 satp satp0 mstatus ms0);
                         exact HSXL))
                with "Hcert Hrw Hro"). }
    iIntros (a) "(-> & Hrw & Hro)".
    (* 2. the satp read, at the frame *)
    iApply (swp_bind_use (Defs.read_reg satp) _
              (fun o => ⌜o = satp0⌝ ∗
                 hreg_frame (cw2_rs satp satp0 mstatus ms0) (cw_Drw satp) ∗
                 hreg_frame_ro (cw2_Df dq dq2 mstatus)
                   (cw2_rs satp satp0 mstatus ms0) (cw2_Dro mstatus))%I _
              with "[Hrw Hro] [-]").
    { iApply (swp_mono with "[] [-]");
        [| iApply (swp_read_reg_pinned (cw_Drw satp) (cw2_Dro mstatus)
                     (cw2_Df dq dq2 mstatus) (cw2_rs satp satp0 mstatus ms0)
                     satp (cw2_disj satp mstatus Hok)
                     (cw2_in_r satp mstatus) with "Hcert Hrw Hro") ].
      iIntros (o) "(-> & Hrw & Hro)".
      rewrite (cw2_rs_r satp satp0 mstatus ms0 Hok). by iFrame. }
    iIntros (o) "(-> & Hrw & Hro)".
    (* 3. the legalization, goodb-transported *)
    iApply (swp_bind_use (legalize_satp RV64 satp0 v) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_span (cw_Drw satp) (cw2_Dro mstatus)
                (cw2_Df dq dq2 mstatus) (cw2_rs satp satp0 mstatus ms0)
                (cw2_rs satp satp0 mstatus ms0) _ _
                (cw2_disj satp mstatus Hok)
                (hval_legalize_satp (cw_Drw satp ∪ cw2_Dro mstatus)
                   (cw_Drw satp) (cw2_rs satp satp0 mstatus ms0) satp0 v
                   (cw2_in_priv satp mstatus) (cw2_in_sec satp mstatus)
                   (cw2_in_misa satp mstatus)
                   (cw2_rs_priv satp satp0 mstatus ms0 Hok)
                   (cw2_rs_sec satp satp0 mstatus ms0 Hok)
                   (cw2_rs_misa satp satp0 mstatus ms0 Hok))
                with "Hcert Hrw Hro"). }
    iIntros (c) "(-> & Hrw & Hro)".
    (* 4. the write and the readback *)
    iApply (swp_bind_use _ _
              (fun c2 => ⌜c2 = satp_legalized satp0 v⌝ ∗
                 hreg_frame (cw2_rs satp (satp_legalized satp0 v) mstatus ms0)
                   (cw_Drw satp) ∗
                 hreg_frame_ro (cw2_Df dq dq2 mstatus)
                   (cw2_rs satp (satp_legalized satp0 v) mstatus ms0)
                   (cw2_Dro mstatus))%I _
              with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ => hreg_frame
                   (cw2_rs satp (satp_legalized satp0 v) mstatus ms0)
                   (cw_Drw satp) ∗
                   hreg_frame_ro (cw2_Df dq dq2 mstatus)
                     (cw2_rs satp (satp_legalized satp0 v) mstatus ms0)
                     (cw2_Dro mstatus))%I _
                with "[Hrw Hro] [-]").
      { iApply (swp_mono with "[] [-]");
          [| iApply (swp_write_reg_owned (cw_Drw satp) (cw2_Dro mstatus)
                       (cw2_Df dq dq2 mstatus)
                       (cw2_rs satp satp0 mstatus ms0) satp _
                       (cw2_disj satp mstatus Hok) (cw2_w_r satp mstatus)
                       with "Hcert Hrw Hro") ].
        iIntros (u) "[Hrw Hro]".
        iDestruct (cw2_rw_ext satp _ _
                     (reg_agree_l _ _ _ _
                        (cw2_set_agree satp satp0 _ mstatus ms0 Hok))
                     with "Hrw") as "Hrw".
        iDestruct (cw2_ro_ext dq dq2 mstatus _ _
                     (reg_agree_r _ _ _ _
                        (cw2_set_agree satp satp0 _ mstatus ms0 Hok))
                     with "Hro") as "Hro".
        by iFrame. }
      iIntros (u) "[Hrw Hro]".
      iApply (swp_mono with "[] [-]");
        [| iApply (swp_read_reg_pinned (cw_Drw satp) (cw2_Dro mstatus)
                     (cw2_Df dq dq2 mstatus)
                     (cw2_rs satp (satp_legalized satp0 v) mstatus ms0) satp
                     (cw2_disj satp mstatus Hok) (cw2_in_r satp mstatus)
                     with "Hcert Hrw Hro") ].
      iIntros (c2) "(-> & Hrw & Hro)".
      rewrite (cw2_rs_r satp (satp_legalized satp0 v) mstatus ms0 Hok).
      by iFrame. }
    iIntros (c2) "(-> & Hrw & Hro)".
    iApply swp_ret. iSplitR; [done|]. iFrame.
  Qed.

  (* ---- satp (Ext_S, mstatus.SXL=SXLEN64): the SXL fact is drawn from the
     kept-half [mstatus] (mstatus.SXL is part of the mmode_config mstatus). ---- *)
  Lemma wp_csrw_satp_gpr (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (satp0 : type_of_register satp)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    satp ↦ᵣ satp0 -∗
    instr pc false (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      satp ↦ᵣ satp_legalized satp0 (m !!! Regidx rs1) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrs1) "Hmm Hpmpc Hpc Hf Hcsr Hinstr Hcont".
    assert (Hok : cw2_ok satp mstatus).
    { rewrite /cw2_ok /cw_fresh. split_and!;
        first [ vm_compute; reflexivity | intros HX; discriminate HX ]. }
    pose proof Hok as (Hfresh & _ & _).
    assert (Hchk : exec (check_CSR_result csr_satp Machine CSRWrite) dstateM
                   = Some (CSR_Check_OK tt, dstateM))
      by (vm_compute; reflexivity).
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL & %HKF)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & %Hmisaval & %Hsecval & _)".
    subst misa0 mseccfg0.
    iApply (wp_instr pc (add_vec_int pc 4) false
              (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW)) m m pmpcfg0
              (mmode_config (DfracOwn (q/2)) ∗
               pmpcfg_n ↦ᵣ{DfracOwn (q/2)} pmpcfg0 ∗
               satp ↦ᵣ satp_legalized satp0 (m !!! Regidx rs1))%I
              Hpmp Hstat
              with "Hmm_wp Hpmpc_wp Hpc Hf Hinstr
                    [Hhs_k Hpriv_k Hms_k Hpmpc_k Hcsr] [Hcont]").
    - iIntros "Hf HPC HnPC".
      iDestruct (cw2_frames_in (DfracOwn (q/2)) (DfracOwn (q/2)) satp satp0
                   mstatus ms0 Hok
                   with "Hcsr Hms_k Hpriv_k Hmseccfg Hmisa") as "[Hrw Hro]".
      iApply (swp_mono with "[HPC HnPC Hhs_k Hpmpc_k] [Hf Hrw Hro]");
        [| iApply (swp_execute_CSRReg_csrw (cw_Drw satp) (cw2_Dro mstatus)
                     (cw2_Df (DfracOwn (q/2)) (DfracOwn (q/2)) mstatus)
                     (cw2_rs satp satp0 mstatus ms0)
                     (cw2_rs satp (satp_legalized satp0 (m !!! Regidx rs1))
                        mstatus ms0) m
                     csr_satp rs1 _ (cw2_disj satp mstatus Hok)
                     (cw2_in_priv satp mstatus) (cw2_in_sec satp mstatus)
                     (cw2_in_misa satp mstatus)
                     (cw2_rs_priv satp satp0 mstatus ms0 Hok)
                     (cw2_rs_sec satp satp0 mstatus ms0 Hok)
                     (cw2_rs_misa satp satp0 mstatus ms0 Hok)
                     ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)
                     Hchk
                     ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)
                     with "Hcert Hf Hrw Hro [Hcert]") ].
      + iIntros (e) "(-> & Hf & Hrw & Hro)".
        iDestruct (cw2_frames_out (DfracOwn (q/2)) (DfracOwn (q/2)) satp _
                     mstatus ms0 Hok with "[$Hrw $Hro]")
          as "(Hcsr & Hms_k & Hpriv_k & _ & _)".
        iSplitR; [done|]. iFrame "Hf HPC HnPC".
        iSplitL "Hhs_k Hpriv_k Hms_k".
        { iFrame "Hhw Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k".
          iPureIntro. exact (conj HmIE (conj HMPRV (conj HSXL HKF))). }
        iFrame "Hpmpc_k Hcsr".
      + iApply (swp_write_CSR_satp (DfracOwn (q/2)) (DfracOwn (q/2)) satp0 ms0
                  (m !!! Regidx rs1) Hok HSXL with "Hcert").
    - iNext. iIntros "Hmm' Hpmpc' Hpc' Hf' (Hmm_k' & Hpmpc_k' & Hcsr')".
      iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
      iCombine "Hpmpc' Hpmpc_k'" as "Hpmpc''".
      iApply ("Hcont" with "Hmm'' Hpmpc'' Hpc' Hf' Hcsr'").
  Qed.

  (* ---- pmpaddr0 (pure): writes pmpaddr_n; value reads old pmpaddr_n AND
     pmpcfg_n.  pmpcfg_n is held (read-only) by [wp_instr] at the split
     fraction; we recover its value at the execute state via a kept half. ---- *)
  Lemma wp_csrw_pmpaddr0_gpr (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (pmpaddr0 : type_of_register pmpaddr_n)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    pmpaddr_n ↦ᵣ pmpaddr0 -∗
    instr pc false (CSRReg (csr_pmpaddr0, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      pmpaddr_n ↦ᵣ pmp0_newaddr pmpcfg0 pmpaddr0 (m !!! Regidx rs1) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrs1) "Hmm Hpmpc Hpc Hf Hcsr Hinstr Hcont".
    assert (Hok : cw2_ok pmpaddr_n pmpcfg_n).
    { rewrite /cw2_ok /cw_fresh. split_and!;
        first [ vm_compute; reflexivity | intros HX; discriminate HX ]. }
    pose proof Hok as (Hfresh & _ & _).
    assert (Hchk : exec (check_CSR_result csr_pmpaddr0 Machine CSRWrite)
                        dstateM = Some (CSR_Check_OK tt, dstateM))
      by (vm_compute; reflexivity).
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & %Hmisaval & %Hsecval & _)".
    subst misa0 mseccfg0.
    iApply (wp_instr pc (add_vec_int pc 4) false
              (CSRReg (csr_pmpaddr0, Regidx rs1, zreg, CSRRW)) m m pmpcfg0
              (mmode_config (DfracOwn (q/2)) ∗
               pmpcfg_n ↦ᵣ{DfracOwn (q/2)} pmpcfg0 ∗
               pmpaddr_n ↦ᵣ pmp0_newaddr pmpcfg0 pmpaddr0
                            (m !!! Regidx rs1))%I
              Hpmp Hstat
              with "Hmm_wp Hpmpc_wp Hpc Hf Hinstr
                    [Hhs_k Hpriv_k Hmst_k Hpmpc_k Hcsr] [Hcont]").
    - iIntros "Hf HPC HnPC".
      iDestruct (cw2_frames_in (DfracOwn (q/2)) (DfracOwn (q/2))
                   pmpaddr_n pmpaddr0 pmpcfg_n pmpcfg0 Hok
                   with "Hcsr Hpmpc_k Hpriv_k Hmseccfg Hmisa") as "[Hrw Hro]".
      iApply (swp_mono with "[HPC HnPC Hhs_k Hmst_k] [Hf Hrw Hro]");
        [| iApply (swp_execute_CSRReg_csrw (cw_Drw pmpaddr_n)
                     (cw2_Dro pmpcfg_n)
                     (cw2_Df (DfracOwn (q/2)) (DfracOwn (q/2)) pmpcfg_n)
                     (cw2_rs pmpaddr_n pmpaddr0 pmpcfg_n pmpcfg0)
                     (cw2_rs pmpaddr_n
                        (pmp0_newaddr pmpcfg0 pmpaddr0 (m !!! Regidx rs1))
                        pmpcfg_n pmpcfg0) m
                     csr_pmpaddr0 rs1 _ (cw2_disj pmpaddr_n pmpcfg_n Hok)
                     (cw2_in_priv pmpaddr_n pmpcfg_n)
                     (cw2_in_sec pmpaddr_n pmpcfg_n)
                     (cw2_in_misa pmpaddr_n pmpcfg_n)
                     (cw2_rs_priv pmpaddr_n pmpaddr0 pmpcfg_n pmpcfg0 Hok)
                     (cw2_rs_sec pmpaddr_n pmpaddr0 pmpcfg_n pmpcfg0 Hok)
                     (cw2_rs_misa pmpaddr_n pmpaddr0 pmpcfg_n pmpcfg0 Hok)
                     ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)
                     Hchk
                     ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)
                     with "Hcert Hf Hrw Hro [Hcert]") ].
      + iIntros (e) "(-> & Hf & Hrw & Hro)".
        iDestruct (cw2_frames_out (DfracOwn (q/2)) (DfracOwn (q/2))
                     pmpaddr_n _ pmpcfg_n pmpcfg0 Hok with "[$Hrw $Hro]")
          as "(Hcsr & Hpmpc_k & Hpriv_k & _ & _)".
        iSplitR; [done|]. iFrame "Hf HPC HnPC".
        iSplitL "Hhs_k Hpriv_k Hmst_k".
        { iFrame "Hhw Hhs_k Hpriv_k Hmst_k". }
        iFrame "Hpmpc_k Hcsr".
      + (* the write is ONE walk: [pmpWriteAddrReg] / [pmpReadAddrReg] read
           pmpcfg_n and pmpaddr_n and write pmpaddr_n, all in the footprint *)
        iIntros "Hrw Hro".
        iApply (swp_mono with "[] [-]");
          [| iApply (swp_hfrun 15 (cw_Drw pmpaddr_n) (cw2_Dro pmpcfg_n)
                       (cw2_Df (DfracOwn (q/2)) (DfracOwn (q/2)) pmpcfg_n)
                       (cw2_rs pmpaddr_n pmpaddr0 pmpcfg_n pmpcfg0) _ _ _
                       (cw2_disj pmpaddr_n pmpcfg_n Hok)
                       (hfrun_write_CSR_pmpaddr0
                          (cw_Drw pmpaddr_n ∪ cw2_Dro pmpcfg_n)
                          (cw_Drw pmpaddr_n)
                          (cw2_rs pmpaddr_n pmpaddr0 pmpcfg_n pmpcfg0)
                          (m !!! Regidx rs1)
                          (cw2_in_r pmpaddr_n pmpcfg_n)
                          (cw2_w_r pmpaddr_n pmpcfg_n)
                          (cw2_in_r2 pmpaddr_n pmpcfg_n))
                       with "Hcert Hrw Hro") ].
        iIntros (x) "(-> & Hrw & Hro)".
        rewrite (cw2_rs_r pmpaddr_n pmpaddr0 pmpcfg_n pmpcfg0 Hok)
          (cw2_rs_r2 pmpaddr_n pmpaddr0 pmpcfg_n pmpcfg0).
        iDestruct (cw2_rw_ext pmpaddr_n _ _
                     (reg_agree_l _ _ _ _
                        (cw2_set_agree pmpaddr_n pmpaddr0 _ pmpcfg_n pmpcfg0
                           Hok)) with "Hrw") as "Hrw".
        iDestruct (cw2_ro_ext (DfracOwn (q/2)) (DfracOwn (q/2)) pmpcfg_n _ _
                     (reg_agree_r _ _ _ _
                        (cw2_set_agree pmpaddr_n pmpaddr0 _ pmpcfg_n pmpcfg0
                           Hok)) with "Hro") as "Hro".
        iSplitR; [done|]. iFrame.
    - iNext. iIntros "Hmm' Hpmpc' Hpc' Hf' (Hmm_k' & Hpmpc_k' & Hcsr')".
      iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
      iCombine "Hpmpc' Hpmpc_k'" as "Hpmpc''".
      iApply ("Hcont" with "Hmm'' Hpmpc'' Hpc' Hf' Hcsr'").
  Qed.

End WpCsrwGprNewB.
