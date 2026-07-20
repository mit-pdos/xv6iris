(* WpLeafCommon.v — small helper lemmas shared by the WpGpr* leaf files,
   moved verbatim out of WpEntry.v so the leaves need not depend on the
   (slow-to-compile) WpEntry.v.  WpEntry.v re-imports this file. *)
From Stdlib Require Import ZArith.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec.
From iris.base_logic.lib Require Import invariants.

Definition h_lui : mword 16 := mword_of_int 0x6505.

(* and_boolM of two true-reducing computations (no cbn -> no driving into cE Zca). *)
Lemma exec_returnM_true (b : bool) s : b = true -> exec (returnM b) s = Some (true, s).
Proof. intro H. rewrite exec_returnm. rewrite H. reflexivity. Qed.
Lemma exec_andM_true (l r : M bool) s :
  exec l s = Some (true, s) -> exec r s = Some (true, s) ->
  exec (Defs.and_boolM l r) s = Some (true, s).
Proof. intros Hl Hr. rewrite (exec_and_boolM_Some _ _ _ _ _ Hl). exact Hr. Qed.


(* HEAD-position guarded if-elimination, for walking a deep nested-if decision
   tree (e.g. [read_CSR]/[write_CSR]'s ~90-way CSR-address dispatch).  The
   obvious idiom
     [repeat (match goal with |- context[if ?g then _ else _] =>
              replace g with false by (vm_compute; reflexivity) end; cbn match)]
   is O(#clauses^2): every iteration re-scans the whole (huge) goal for [context]
   and then [cbn match]-traverses it.  Rewriting at the HEAD instead
     [repeat (erewrite exec_if_false_g by (vm_compute; reflexivity))]
   peels one guard per step with no goal-wide scan and no [cbn match], leaving the
   goal in the same shape (the matching [if g then _ else _] at head).  See the
   "Build-perf note" in README.md. *)
Lemma exec_if_false_g {X} (g : bool) (A B : M X) s :
  g = false -> exec (if g then A else B) s = exec B s.
Proof. intros ->. reflexivity. Qed.

(* Batched head-peels for the ~90-way read_CSR/write_CSR nested-if dispatch:
   one [erewrite] per 16 (resp. 4) false guards instead of per clause, so the
   O(tail)-sized retyping that dominates the clause walk (Ltac profiling:
   68% of WpGprCsrwB) happens ~3 times per lemma instead of ~28.  Use via
   [skip_csr_false_clauses]; the 1-clause [exec_if_false_g] stays as the
   fallback (and for the final clauses before the TRUE guard, where the
   batched side conditions fail and the erewrite backtracks cheaply). *)
Lemma exec_if_false_g16 {X} (g1 : bool) (g2 : bool) (g3 : bool) (g4 : bool) (g5 : bool) (g6 : bool) (g7 : bool) (g8 : bool) (g9 : bool) (g10 : bool) (g11 : bool) (g12 : bool) (g13 : bool) (g14 : bool) (g15 : bool) (g16 : bool) (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 B : M X) s :
  g1 = false -> g2 = false -> g3 = false -> g4 = false -> g5 = false -> g6 = false -> g7 = false -> g8 = false -> g9 = false -> g10 = false -> g11 = false -> g12 = false -> g13 = false -> g14 = false -> g15 = false -> g16 = false ->
  exec (if g1 then A1 else (if g2 then A2 else (if g3 then A3 else (if g4 then A4 else (if g5 then A5 else (if g6 then A6 else (if g7 then A7 else (if g8 then A8 else (if g9 then A9 else (if g10 then A10 else (if g11 then A11 else (if g12 then A12 else (if g13 then A13 else (if g14 then A14 else (if g15 then A15 else (if g16 then A16 else (B))))))))))))))))) s = exec B s.
Proof. intros -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> ->. reflexivity. Qed.

Lemma exec_if_false_g4 {X} (g1 : bool) (g2 : bool) (g3 : bool) (g4 : bool) (A1 A2 A3 A4 B : M X) s :
  g1 = false -> g2 = false -> g3 = false -> g4 = false ->
  exec (if g1 then A1 else (if g2 then A2 else (if g3 then A3 else (if g4 then A4 else (B))))) s = exec B s.
Proof. intros -> -> -> ->. reflexivity. Qed.

Ltac skip_csr_false_clauses :=
  repeat (erewrite exec_if_false_g16 by (vm_compute; reflexivity));
  repeat (erewrite exec_if_false_g4 by (vm_compute; reflexivity));
  repeat (erewrite exec_if_false_g by (vm_compute; reflexivity)).

Definition imm_clui : mword 6 :=
  concat_vec (subrange_vec_dec h_lui 12 12) (subrange_vec_dec h_lui 6 2).

(* write any GPR (given the reflexivity equation for its concrete index). *)
Lemma exec_wX_bits_at (i : mword 5) (r : register_bitvector_64) s (v : mword 64) :
  wX (Regno (uint i)) v
    = Defs.bind0 (Defs.write_reg (R_bitvector_64 r) (regval_into_reg v)) (returnM tt) ->
  exec (wX_bits (Regidx i) v) s = Some (tt, set_reg s (R_bitvector_64 r) (regval_into_reg v)).
Proof.
  intro Heq. unfold wX_bits. rewrite Heq.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg (R_bitvector_64 r) _ s)).
  apply exec_returnm.
Qed.


Lemma exec_set_next_pc (target : mword 64) s :
  exec (set_next_pc target) s = Some (tt, set_reg s nextPC target).
Proof.
  unfold set_next_pc. cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg nextPC target s)).
  apply exec_returnm.
Qed.

Lemma exec_jump_to (target : mword 64) s :
  eq_vec (access_vec_dec target 0) ('b"0") = true ->
  bit_to_bool (access_vec_dec target 1) = false ->
  exec (jump_to target) s = Some (RETIRE_SUCCESS, set_reg s nextPC target).
Proof.
  intros Halign Hbit1.
  unfold jump_to. rewrite exec_catch_early_return.
  change (ext_control_check_pc target) with (@None unit). cbv iota beta.
  (* outer bind: w1 = false (target[1]=0 short-circuits and_boolM) *)
  rewrite (execR_bind_Some _ _ _ false s).
  2:{ unfold Defs.bind0.
      (* INNER = bind (bind (returnR())(fun _ => liftR assert)) (fun _ => and_boolM..) *)
      erewrite execR_bind_Some.
      2:{ erewrite execR_bind_Some.
          2:{ apply execR_returnR_fwd. }
          rewrite execR_liftR. unfold assert_exp. rewrite Halign. cbn match.
          rewrite exec_returnm. reflexivity. }
      unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ (bit_to_bool (access_vec_dec target 1)) s).
      2:{ apply execR_returnR_fwd. }
      rewrite Hbit1. cbv iota beta. apply execR_returnR_fwd. }
  cbv iota beta.
  (* K false = liftR (set_next_pc target) >> returnR RETIRE_SUCCESS *)
  unfold Defs.bind0.
  rewrite (execR_bind_Some _ _ _ tt (set_reg s nextPC target)).
  2:{ rewrite execR_liftR. rewrite exec_set_next_pc. reflexivity. }
  rewrite (execR_returnR_fwd RETIRE_SUCCESS (set_reg s nextPC target)).
  reflexivity.
Qed.

(* the compressed-extension jump: with Ext_Zca enabled the model accepts a
   merely 2-aligned target (bit 0 = 0), so bit 1 need not be 0. *)
Lemma exec_jump_to_zca (target : mword 64) s :
  eq_vec (access_vec_dec target 0) ('b"0") = true ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  exec (jump_to target) s = Some (RETIRE_SUCCESS, set_reg s nextPC target).
Proof.
  intros Halign Hzca.
  unfold jump_to. rewrite exec_catch_early_return.
  change (ext_control_check_pc target) with (@None unit). cbv iota beta.
  rewrite (execR_bind_Some _ _ _ false s).
  2:{ unfold Defs.bind0.
      erewrite execR_bind_Some.
      2:{ erewrite execR_bind_Some.
          2:{ apply execR_returnR_fwd. }
          rewrite execR_liftR. unfold assert_exp. rewrite Halign. cbn match.
          rewrite exec_returnm. reflexivity. }
      unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ (bit_to_bool (access_vec_dec target 1)) s).
      2:{ apply execR_returnR_fwd. }
      destruct (bit_to_bool (access_vec_dec target 1)).
      - cbv iota beta.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite execR_liftR. rewrite Hzca. reflexivity. }
        cbv iota beta. apply execR_returnR_fwd.
      - cbv iota beta. apply execR_returnR_fwd. }
  cbv iota beta.
  unfold Defs.bind0.
  rewrite (execR_bind_Some _ _ _ tt (set_reg s nextPC target)).
  2:{ rewrite execR_liftR. rewrite exec_set_next_pc. reflexivity. }
  rewrite (execR_returnR_fwd RETIRE_SUCCESS (set_reg s nextPC target)).
  reflexivity.
Qed.

Lemma exec_execute_JAL (imm : mword 21) (rd : regidx) s s_w :
  eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
  bit_to_bool (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 1) = false ->
  exec (wX_bits rd (register_lookup nextPC s.(sregs)))
       (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))) = Some (tt, s_w) ->
  exec (execute_JAL imm rd) s = Some (RETIRE_SUCCESS, s_w).
Proof.
  intros Halign Hbit1 Hwx.
  unfold execute_JAL, get_next_pc.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg nextPC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_jump_to _ s Halign Hbit1)).
  cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _ Hwx).
  apply exec_returnm.
Qed.

Definition mulop_mul : mul_op :=
  {| mul_op_result_part := Low; mul_op_signed_rs1 := Signed; mul_op_signed_rs2 := Signed |}.

Lemma exec_execute_ITYPE_ADDI (imm : mword 12) (rs1 rd : regidx) (a : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) ->
  exec (wX_bits rd (add_vec a (sign_extend' 64 imm))) s = Some (tt, s') ->
  exec (execute (ITYPE (imm, rs1, rd, ADDI))) s = Some (RETIRE_SUCCESS, s').
Proof.
  intros Ha Hw.
  change (execute (ITYPE (imm, rs1, rd, ADDI))) with (execute_ITYPE imm rs1 rd ADDI).
  unfold execute_ITYPE. cbn match.
  rewrite (exec_bind_Some _ _ _ (add_vec a (sign_extend' 64 imm)) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ Ha). apply exec_returnm. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw). apply exec_returnm.
Qed.

Definition w_csrr : mword 32 := mword_of_int 0xf14025f3.
Definition csr_csrr : mword 12 := subrange_vec_dec w_csrr 31 20.
Definition i_rs1_csrr : mword 5 :=
  autocast (subrange_vec_dec (subrange_vec_dec w_csrr 19 15) (regidx_bit_width - 1) 0).
Definition i_rd_csrr : mword 5 :=
  autocast (subrange_vec_dec (subrange_vec_dec w_csrr 11 7) (regidx_bit_width - 1) 0).

Lemma exec_check_CSR_csrr s : exec (check_CSR csr_csrr Machine CSRRead) s = Some (true, s).
Proof.
  assert (H : check_CSR csr_csrr Machine CSRRead = returnM true) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_csr_id_read_callback_csrr s d :
  exec (csr_id_read_callback csr_csrr d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_csrr d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_rX_bits_x0 (i : mword 5) s :
  uint i = 0 -> exec (rX_bits (Regidx i)) s = Some (zero_reg, s).
Proof.
  intro H. unfold rX_bits; cbn match. rewrite H. unfold rX.
  replace (Z.eqb 0 0) with true by reflexivity. cbn match. apply exec_returnM.
Qed.

(* [is_CSR_accessible csr priv acc = RHS] goals (RHS an opaque gate term like
   [currentlyEnabled Ext_U] or [Defs.and_boolM (currentlyEnabled Ext_X) ...]):
   do NOT use [vm_compute; reflexivity] here.  [currentlyEnabled]/[hartSupports]
   are defined via a well-founded (Acc/Zwf_guarded) fixpoint whose proof term
   vm_compute cannot reduce cheaply (~0.7-1s EACH for LHS via vm_compute AND
   again for the kernel's Qed-time conversion check in reflexivity, since both
   sides mention the same recursor). [is_CSR_accessible]'s dispatch on the
   concrete [csr] is a plain (non-well-founded) if-chain on [eq_vec]/
   [subrange_vec_dec]/[access_vec_dec] guards, so a TARGETED unfold that
   evaluates only those guard primitives -- never touching [currentlyEnabled]/
   [hartSupports]/[and_boolM]/[or_boolM], which stay folded and un-normalized
   on both sides -- selects the matching clause and lands on a goal that's
   syntactically [RHS = RHS], closed by a free [reflexivity]. Measured
   ~1.7s -> ~0.02s per call. *)
Ltac csr_dispatch_eq :=
  unfold is_CSR_accessible;
  cbv delta [eq_vec get_word MachineWord.MachineWord.eqb bool_decide] iota zeta beta;
  reflexivity.

Lemma exec_check_CSR_result_csrr s :
  exec (check_CSR_result csr_csrr Machine CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  unfold check_CSR_result.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_check_CSR_csrr s)).
  exact (exec_returnM (CSR_Check_OK tt) s).
Qed.

Lemma exec_read_CSR_csrr s :
  exec (read_CSR csr_csrr) s = Some (register_lookup mhartid s.(sregs), s).
Proof. exact (exec_read_reg (R_bitvector_64 mhartid) s). Qed.

(* wX to x0 is a no-op (write discarded).  Twin of [exec_rX_bits_x0]. *)
Lemma exec_wX_bits_x0 (i : mword 5) (v : mword 64) s :
  uint i = 0 -> exec (wX_bits (Regidx i) v) s = Some (tt, s).
Proof.
  intro H. unfold wX_bits, wX. rewrite H.
  cbv zeta. replace (Z.eqb 0 0) with true by reflexivity.
  cbn match. apply exec_returnM.
Qed.

(* JAL with rd = x0 (zreg): the jump retires with NO link write, so the only
   state change is nextPC := target.  Instantiate the rd-generic [exec_execute_JAL]
   at rd := zreg and discharge the wX obligation with the x0-no-op fact. *)
