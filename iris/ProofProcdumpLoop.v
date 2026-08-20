(* ProofProcdumpLoop.v -- procdump's SCAN LOOP: the block +0x56 .. +0x8c and
   the fuel induction over the 64 [proc] slots.

   The loop is entered at its HEAD (+0x6e) with the cursor s1 = [pd_cur j];
   control leaves it only through the [beq s1,s2] at +0x6a, which is taken
   exactly when the NEXT index is [NPROC].  So the lemma below takes the
   epilogue's continuation as a PREMISE (fdalloc's rule, as in ProofKkill) and
   the induction is an ordinary Coq induction on a [fuel] bounding
   [NPROC - j] -- the IH then keeps its leading [forall j M].

   THREE JOINS, AND THEY ARE WHY THE PROOF IS SHAPED THIS WAY.

   * +0x56 (PRINT) is reached from the "???" arm (+0x78 taken) and from the
     table arm (+0x88 taken).  Both arrive with a2 holding a pointer to a
     NUL-terminated string owned PERSISTENTLY, which is all printk needs, so
     the whole two-call print block is proved ONCE as an intuitionistic
     [wp_next] assertion parameterised by (sptr, ss).
   * +0x66 (ADVANCE) is reached from the UNUSED skip (+0x74 taken) and from
     the end of the print block, so it too is a single assertion.
   * both assertions take the exit continuation as a wand premise, because it
     is linear; the fuel IH is intuitionistic and needs no such treatment.

   The five-way case analysis on [p->state] is the one place where a symbolic
   index would be nice and is not available: [c.beqz] gives [state <> 0] and
   the [bltu s6,a5] fall-through gives [uint state <= 5], so the state is one
   of five 64-bit literals.  The three shift/add instructions between +0x7c and
   +0x84 are handled at a SYMBOLIC [k] by the single pure lemma
   [pdl_table_addr] (five concrete [vm_compute]s in a two-hypothesis context),
   which is what lets the table arm's WP script be written once. *)
From Stdlib Require Import ZArith Lia List String Ascii.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import dfrac.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import RiscvExtras.
Require Import InstrBytes KernelText KernelDataInv.
Require Import CalleeSaved.
Require Import WpMmodeLeafBase.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import IntrDefs WpNext.
Require Import CpuOwn.
Require Import WpLock.
Require Import DiskPtsto WpUart.
Require Import ProcGeom.
Require Import PrintkFmt.
Require Import SpecPrintk.
Require Import SpecProcdump.
Require Import ProcdumpAux.
Require Import CodeProcdump.
From Kernel Require KernelInstrs KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Local Open Scope Z_scope.
(* a failing tactic in a whole-function WP over the proc resources otherwise
   spends tens of minutes FORMATTING the goal -- see durable-notes. *)
Set Printing Depth 40.

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.
Local Ltac regne := reg_ne_side.

(* ===================================================================== *)
(* 1.  THE NUMERIC SIDE CONDITIONS, mword-free (durable-notes: [lia]      *)
(*     misbehaves in a context full of [bv_unsigned]).                    *)
(* ===================================================================== *)

Lemma pdl_no_fuel (j : nat) : (NPROC - j <= 0)%nat -> (j < NPROC)%nat -> False.
Proof. unfold NPROC. lia. Qed.

Lemma pdl_fuel_le (j fuel : nat) :
  (NPROC - j <= S fuel)%nat -> (NPROC - S j <= fuel)%nat.
Proof. unfold NPROC. lia. Qed.

Lemma pdl_j_le (j : nat) : (j < NPROC)%nat -> (j <= NPROC)%nat.
Proof. lia. Qed.

Lemma pdl_sj_le (j : nat) : (j < NPROC)%nat -> (S j <= NPROC)%nat.
Proof. unfold NPROC. lia. Qed.

Lemma pdl_seq_suffix (j : nat) :
  (j < NPROC)%nat -> seq j (NPROC - j) = j :: seq (S j) (NPROC - S j).
Proof.
  intro Hj. replace (NPROC - j)%nat with (S (NPROC - S j))%nat
    by (unfold NPROC in *; lia).
  reflexivity.
Qed.

Lemma pdl_seq_prefix (j : nat) : seq 0 (S j) = (seq 0 j ++ [j])%list.
Proof. rewrite seq_S. reflexivity. Qed.

Lemma pdl_suffix_done (j : nat) : (S j = NPROC)%nat -> (NPROC - S j = 0)%nat.
Proof. lia. Qed.

(* ===================================================================== *)
(* 2.  THE STATE'S FIVE VALUES                                            *)
(* ===================================================================== *)

Lemma pdl_state_five (v : mword 64) :
  eq_vec v (zero_reg : mword 64) = false ->
  zopz0zI_u (mword_of_int 5 : mword 64) v = false ->
  exists k : nat, (1 <= k <= 5)%nat /\ v = (mword_of_int (Z.of_nat k) : mword 64).
Proof.
  intros Hnz Hle.
  unfold zopz0zI_u in Hle. apply Z.ltb_ge in Hle.
  rewrite !uint_unsigned in Hle.
  assert (H5 : bv_unsigned (mword_of_int 5 : mword 64) = 5)
    by (vm_compute; reflexivity).
  rewrite H5 in Hle.
  assert (Hz : bv_unsigned v <> 0).
  { intro Hc. apply eq_vec_false_iff in Hnz. apply Hnz.
    apply bv_eq. rewrite Hc. vm_compute; reflexivity. }
  pose proof (bv_unsigned_in_range _ v) as Hr.
  assert (Hcases : bv_unsigned v = 1 \/ bv_unsigned v = 2 \/ bv_unsigned v = 3
                   \/ bv_unsigned v = 4 \/ bv_unsigned v = 5) by lia.
  destruct Hcases as [H|[H|[H|[H|H]]]].
  - exists 1%nat. split; [lia|]. apply bv_eq. rewrite H. vm_compute; reflexivity.
  - exists 2%nat. split; [lia|]. apply bv_eq. rewrite H. vm_compute; reflexivity.
  - exists 3%nat. split; [lia|]. apply bv_eq. rewrite H. vm_compute; reflexivity.
  - exists 4%nat. split; [lia|]. apply bv_eq. rewrite H. vm_compute; reflexivity.
  - exists 5%nat. split; [lia|]. apply bv_eq. rewrite H. vm_compute; reflexivity.
Qed.

Lemma pdl_state_lt6 (k : nat) : (1 <= k <= 5)%nat -> (k < 6)%nat.
Proof. lia. Qed.

(* [slli a4,a5,32; srli a5,a4,29; c.add a5,a5,s7], then [c.ld a2,0(a5)]'s
   own zero displacement, at a SYMBOLIC state index.  Five concrete
   [vm_compute]s here rather than five copies of the WP script. *)
Lemma pdl_table_addr (k : nat) : (1 <= k <= 5)%nat ->
  add_vec
    (add_vec
       (shift_bits_right
          (shift_bits_left (mword_of_int (Z.of_nat k) : mword 64)
             (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))
          (subrange_vec_dec (mword_of_int 29 : mword 6) (Z.sub log2_xlen 1) 0))
       (mword_of_int pd_states_a : mword 64))
    (sign_extend' 64 (mword_of_int 0 : mword 12))
  = (mword_of_int (pd_states_a + 8 * Z.of_nat k) : mword 64).
Proof.
  intro Hk.
  destruct k as [|[|[|[|[|[|k']]]]]]; try lia;
    (apply bv_eq; vm_compute; reflexivity).
Qed.

(* ===================================================================== *)
(* 3.  THE REGISTER INVARIANTS UNDER ONE WRITE / ONE CALL                 *)
(* ===================================================================== *)

Lemma pdl_get_sp (M : regfile) (spv : mword 64) (j : nat) :
  pd_regs_loop M spv j -> M !!! Regidx (mword_of_int 2 : mword 5) = spv.
Proof. intros (H & _). exact H. Qed.
Lemma pdl_get_s1 (M : regfile) (spv : mword 64) (j : nat) :
  pd_regs_loop M spv j -> M !!! Regidx (mword_of_int 9 : mword 5) = pd_cur j.
Proof. intros (_ & H & _). exact H. Qed.
Lemma pdl_get_s2 (M : regfile) (spv : mword 64) (j : nat) :
  pd_regs_loop M spv j -> M !!! Regidx (mword_of_int 18 : mword 5) = pd_cur NPROC.
Proof. intros (_ & _ & H & _). exact H. Qed.
Lemma pdl_get_s3 (M : regfile) (spv : mword 64) (j : nat) :
  pd_regs_loop M spv j ->
  M !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int pd_qqq_a : mword 64).
Proof. intros (_ & _ & _ & H & _). exact H. Qed.
Lemma pdl_get_s4 (M : regfile) (spv : mword 64) (j : nat) :
  pd_regs_loop M spv j ->
  M !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int pd_nl_a : mword 64).
Proof. intros (_ & _ & _ & _ & H & _). exact H. Qed.
Lemma pdl_get_s5 (M : regfile) (spv : mword 64) (j : nat) :
  pd_regs_loop M spv j ->
  M !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int pd_fmt_a : mword 64).
Proof. intros (_ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma pdl_get_s6 (M : regfile) (spv : mword 64) (j : nat) :
  pd_regs_loop M spv j ->
  M !!! Regidx (mword_of_int 22 : mword 5) = (mword_of_int 5 : mword 64).
Proof. intros (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma pdl_get_s7 (M : regfile) (spv : mword 64) (j : nat) :
  pd_regs_loop M spv j ->
  M !!! Regidx (mword_of_int 23 : mword 5) = (mword_of_int pd_states_a : mword 64).
Proof. intros (_ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

(* a CALLER-SAVED write touches neither invariant *)
Lemma pdl_loop_upd (M : regfile) (r : mword 5) (v : mword 64)
    (spv : mword 64) (j : nat) :
  is_cs_idx r = false ->
  pd_regs_loop M spv j -> pd_regs_loop (<[Regidx r := v]> M) spv j.
Proof.
  intros Hr (H2 & H9 & H18 & H19 & H20 & H21 & H22 & H23).
  unfold pd_regs_loop, pdR in *.
  split_and!;
    (rewrite upd_ne;
      [ assumption
      | apply not_eq_sym; apply (is_cs_idx_true_neq r);
        [ exact Hr | vm_compute; reflexivity ] ]).
Qed.

Lemma pdl_hi_upd (m0 M : regfile) (r : mword 5) (v : mword 64) :
  is_cs_idx r = false ->
  pd_regs_hi m0 M -> pd_regs_hi m0 (<[Regidx r := v]> M).
Proof.
  intros Hr (H24 & H25 & H26 & H27).
  unfold pd_regs_hi, pdR in *.
  split_and!;
    (rewrite upd_ne;
      [ assumption
      | apply not_eq_sym; apply (is_cs_idx_true_neq r);
        [ exact Hr | vm_compute; reflexivity ] ]).
Qed.

(* the ONE callee-saved write the loop makes: [addi s1,s1,360] *)
Lemma pdl_loop_s1 (M : regfile) (v : mword 64) (spv : mword 64) (j : nat) :
  v = pd_cur (S j) -> pd_regs_loop M spv j ->
  pd_regs_loop (<[Regidx (mword_of_int 9 : mword 5) := v]> M) spv (S j).
Proof.
  intros Hv (H2 & H9 & H18 & H19 & H20 & H21 & H22 & H23).
  unfold pd_regs_loop, pdR in *.
  split_and!.
  - rewrite upd_ne; [assumption | regne].
  - rewrite upd_eq. exact Hv.
  - rewrite upd_ne; [assumption | regne].
  - rewrite upd_ne; [assumption | regne].
  - rewrite upd_ne; [assumption | regne].
  - rewrite upd_ne; [assumption | regne].
  - rewrite upd_ne; [assumption | regne].
  - rewrite upd_ne; [assumption | regne].
Qed.

Lemma pdl_hi_s1 (m0 M : regfile) (v : mword 64) :
  pd_regs_hi m0 M ->
  pd_regs_hi m0 (<[Regidx (mword_of_int 9 : mword 5) := v]> M).
Proof.
  intros (H24 & H25 & H26 & H27). unfold pd_regs_hi, pdR in *.
  split_and!; (rewrite upd_ne; [assumption | regne]).
Qed.

(* ... and what a printk call gives back *)
Lemma pdl_loop_cs (M M' : regfile) (spv : mword 64) (j : nat) :
  callee_saved M M' -> pd_regs_loop M spv j -> pd_regs_loop M' spv j.
Proof.
  intros Hcs (H2 & H9 & H18 & H19 & H20 & H21 & H22 & H23).
  unfold pd_regs_loop, pdR in *.
  split_and!.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 2 : mword 5)
               ltac:(vm_compute; reflexivity)); exact H2.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 9 : mword 5)
               ltac:(vm_compute; reflexivity)); exact H9.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 18 : mword 5)
               ltac:(vm_compute; reflexivity)); exact H18.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 19 : mword 5)
               ltac:(vm_compute; reflexivity)); exact H19.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5)
               ltac:(vm_compute; reflexivity)); exact H20.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 21 : mword 5)
               ltac:(vm_compute; reflexivity)); exact H21.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 22 : mword 5)
               ltac:(vm_compute; reflexivity)); exact H22.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 23 : mword 5)
               ltac:(vm_compute; reflexivity)); exact H23.
Qed.

(* ===================================================================== *)
(* 4.  THE RESOURCE PLUMBING                                              *)
(* ===================================================================== *)

Section ProcdumpLoopRes.
  Context `{!riscvGS Σ}.

  Lemma pdl_slot_mk (pa : mword 64) (dqs dqp dqn : dfrac)
      (st pid : mword 32) (nm : string) :
    nonul nm = true ->
    p_state pa ↦₄{dqs} st -∗ p_pid pa ↦₄{dqp} pid -∗
    p_name pa 0 ↦ₛ{dqn} nm -∗ proc_dump_slot pa.
  Proof.
    intro Hnm. iIntros "H1 H2 H3". rewrite /proc_dump_slot.
    iExists dqs, dqp, dqn, st, pid, nm.
    iSplit; [iPureIntro; exact Hnm|]. iFrame.
  Qed.

  Lemma pdl_prefix_step (j : nat) :
    ([∗ list] k ∈ seq 0 j, proc_dump_slot (proc_addr k)) -∗
    proc_dump_slot (proc_addr j) -∗
    ([∗ list] k ∈ seq 0 (S j), proc_dump_slot (proc_addr k)).
  Proof.
    iIntros "Hp Hs".
    rewrite (pdl_seq_prefix j) big_sepL_app big_sepL_singleton.
    iSplitL "Hp"; [iExact "Hp" | iExact "Hs"].
  Qed.

  Context `{GEN : GenId}.

  Lemma pdl_pkastr (CIDx : CpuId) (v : mword 64) (dq : dfrac) (s : string) :
    nonul s = true -> eq_vec v (zero_reg : mword 64) = false ->
    v ↦ₛ{dq} s -∗ pk_desc_res v (PkAStr dq s).
  Proof.
    intros H1 H2. iIntros "H". unfold pk_desc_res; cbn match.
    iSplit; [iPureIntro; exact H1|].
    iSplit; [iPureIntro; exact H2|]. iExact "H".
  Qed.

  Lemma pdl_descs_mk (CIDx : CpuId) (m : regfile)
      (sptr nmp : mword 64) (ss nm : string) (dqn : dfrac) :
    pk_vararg m 1%nat = sptr -> pk_vararg m 2%nat = nmp ->
    nonul ss = true -> eq_vec sptr (zero_reg : mword 64) = false ->
    nonul nm = true -> eq_vec nmp (zero_reg : mword 64) = false ->
    sptr ↦ₛ□ ss -∗ nmp ↦ₛ{dqn} nm -∗
    ([∗ list] i ↦ d ∈ [PkANum; PkAStr DfracDiscarded ss; PkAStr dqn nm],
       pk_desc_res (pk_vararg m i) d).
  Proof.
    intros H1 H2 Hss Hsz Hnm Hnz. iIntros "#Hs Hn".
    rewrite !big_sepL_cons big_sepL_nil H1 H2.
    iSplitR.
    { unfold pk_desc_res; cbn match. done. }
    iSplitR "Hn".
    { iApply (pdl_pkastr CIDx sptr DfracDiscarded ss Hss Hsz with "Hs"). }
    iSplitL "Hn"; [| done].
    iApply (pdl_pkastr CIDx nmp dqn nm Hnm Hnz with "Hn").
  Qed.

  Lemma pdl_descs_take (CIDx : CpuId) (m : regfile)
      (sptr nmp : mword 64) (ss nm : string) (dqn : dfrac) :
    pk_vararg m 1%nat = sptr -> pk_vararg m 2%nat = nmp ->
    ([∗ list] i ↦ d ∈ [PkANum; PkAStr DfracDiscarded ss; PkAStr dqn nm],
       pk_desc_res (pk_vararg m i) d) -∗
    nmp ↦ₛ{dqn} nm.
  Proof.
    intros H1 H2. iIntros "H".
    rewrite !big_sepL_cons big_sepL_nil H1 H2.
    unfold pk_desc_res; cbn match.
    iDestruct "H" as "(_ & _ & (_ & _ & $) & _)".
  Qed.

End ProcdumpLoopRes.

(* ===================================================================== *)
(* 5.  THE SCAN                                                           *)
(* ===================================================================== *)

Section ProofProcdumpLoop.
  Context `{!riscvGS Σ, !xv6G Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rsp := (mword_of_int 2 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).

  (* ---- THE BLOCK STATEMENTS, NAMED (claude-notes/optimization.md, RULE
     ONE) -- [Hloop]/[Hadv]/[Hprint] are each stated below as a
     [wp_next]-wrapped [iAssert] whose continuation body is tens of lines
     of ∀/wands; spelled out in place, EVERY proofmode step of the walk
     re-embeds that whole statement in the proof term (the cost is
     |Δ| times the number of steps).  Naming the inner body turns each
     into a constant applied to its arguments in the context.

     They are TRANSPARENT ON PURPOSE and only the part AFTER
     [fun CIDx : CpuId =>] is named: the [wp_next]/[□]/[∀ fuel] at each
     use site stay syntactically visible, which is what lets
     [iSpecialize]/[iApply] unify through them without an extra
     [iEval (rewrite /...)], and what lets [iInduction fuel] leave
     [pdl_loop_body]'s own induction hypothesis folded.  [GEN]/[CID0] are
     bound by [wp_pd_loop] itself, not by the section, so unlike the
     dirlink/dirlookup/namex families these definitions take them as
     explicit parameters. *)

  Definition pdl_loop_body `{GEN : GenId} (CID0 : CpuId)
      (spv p : mword 64) (m0 : regfile) (K' : nat) (eb b : bool)
      (lks : gset string) (fuel : nat) (CIDf : CpuId) : iProp Σ :=
    (∀ (j : nat) (M : regfile),
       ⌜ (NPROC - j <= fuel)%nat ⌝ -∗
       ⌜ (j < NPROC)%nat ⌝ -∗
       ⌜ pd_regs_loop M spv j /\ pd_regs_hi m0 M ⌝ -∗
       wp_next (CID0 := CID0) b p (fun (CIDq : CpuId) =>
         ∀ (Mx : regfile),
           ⌜ Mx !!! pdR 2 = spv /\ pd_regs_hi m0 Mx ⌝ -∗
           sie_cap_gpr KT1 Mx K' b p -∗
           cpu_own 0%nat eb p b lks -∗
           pc_is (mword_of_int (KernelSyms.procdump + 0x8e)) -∗
           procdump_view -∗
           WP (Loop : expr riscv_lang)) -∗
       sie_cap_gpr KT1 M K' b p -∗
       cpu_own 0%nat eb p b lks -∗
       pc_is (mword_of_int (KernelSyms.procdump + 0x6e)) -∗
       ([∗ list] k ∈ seq 0 j, proc_dump_slot (proc_addr k)) -∗
       ([∗ list] k ∈ seq j (NPROC - j), proc_dump_slot (proc_addr k)) -∗
       WP (Loop : expr riscv_lang))%I.

  Definition pdl_adv_body `{GEN : GenId} (CID0 : CpuId)
      (spv p : mword 64) (m0 : regfile) (K' : nat) (eb b : bool)
      (lks : gset string) (j : nat) (CIDa : CpuId) : iProp Σ :=
    (∀ (Ma : regfile),
       ⌜ pd_regs_loop Ma spv j /\ pd_regs_hi m0 Ma ⌝ -∗
       wp_next (CID0 := CID0) b p (fun (CIDq : CpuId) =>
         ∀ (Mx : regfile),
           ⌜ Mx !!! pdR 2 = spv /\ pd_regs_hi m0 Mx ⌝ -∗
           sie_cap_gpr KT1 Mx K' b p -∗
           cpu_own 0%nat eb p b lks -∗
           pc_is (mword_of_int (KernelSyms.procdump + 0x8e)) -∗
           procdump_view -∗
           WP (Loop : expr riscv_lang)) -∗
       sie_cap_gpr KT1 Ma K' b p -∗
       cpu_own 0%nat eb p b lks -∗
       pc_is (mword_of_int (KernelSyms.procdump + 0x66)) -∗
       ([∗ list] k ∈ seq 0 (S j), proc_dump_slot (proc_addr k)) -∗
       ([∗ list] k ∈ seq (S j) (NPROC - S j), proc_dump_slot (proc_addr k)) -∗
       WP (Loop : expr riscv_lang))%I.

  Definition pdl_print_body `{GEN : GenId} (CID0 : CpuId)
      (spv p : mword 64) (m0 : regfile) (K' : nat) (eb b : bool)
      (lks : gset string) (j : nat) (CIDp : CpuId) : iProp Σ :=
    (∀ (Mp : regfile) (sptr : mword 64) (ss nm2 : string)
       (dq1 dq2 dq3 : dfrac) (st2 pid2 : mword 32),
       ⌜ pd_regs_loop Mp spv j /\ pd_regs_hi m0 Mp ⌝ -∗
       ⌜ Mp !!! Regidx Ra2 = sptr /\ Mp !!! Regidx Ra3 = pd_cur j ⌝ -∗
       ⌜ nonul ss = true /\ eq_vec sptr (zero_reg : mword 64) = false
         /\ nonul nm2 = true ⌝ -∗
       sptr ↦ₛ□ ss -∗
       wp_next (CID0 := CID0) b p (fun (CIDq : CpuId) =>
         ∀ (Mx : regfile),
           ⌜ Mx !!! pdR 2 = spv /\ pd_regs_hi m0 Mx ⌝ -∗
           sie_cap_gpr KT1 Mx K' b p -∗
           cpu_own 0%nat eb p b lks -∗
           pc_is (mword_of_int (KernelSyms.procdump + 0x8e)) -∗
           procdump_view -∗
           WP (Loop : expr riscv_lang)) -∗
       sie_cap_gpr KT1 Mp K' b p -∗
       cpu_own 0%nat eb p b lks -∗
       pc_is (mword_of_int (KernelSyms.procdump + 0x56)) -∗
       p_state (proc_addr j) ↦₄{dq1} st2 -∗
       p_pid (proc_addr j) ↦₄{dq2} pid2 -∗
       p_name (proc_addr j) 0 ↦ₛ{dq3} nm2 -∗
       ([∗ list] k ∈ seq 0 j, proc_dump_slot (proc_addr k)) -∗
       ([∗ list] k ∈ seq (S j) (NPROC - S j), proc_dump_slot (proc_addr k)) -∗
       WP (Loop : expr riscv_lang))%I.

  Lemma wp_pd_loop `{GEN : GenId} `{CID0 : CpuId}
      (γpr : gname) (γd : uart_names) (γv : disk_names)
      (m0 : regfile) (spv p : mword 64) (K' : nat) (eb b : bool)
      (lks : gset string) :
    printk_gen_contract (kt := KT1) γpr γd γv ->
    (48 <= K')%nat ->
    (* procdump's own cone touches no lock directly -- printk (rank "pr") is
       the only callee, and it is the whole order premise. *)
    locks_below lks "pr" ->
    kernel_text -∗ kernel_data -∗ printk_env γpr γd γv -∗
    (* THE EXIT CONTINUATION, at the epilogue entry, taken as a PREMISE *)
    wp_next (CID0 := CID0) b p (fun (CIDq : CpuId) =>
      ∀ (Mx : regfile),
        ⌜ Mx !!! pdR 2 = spv /\ pd_regs_hi m0 Mx ⌝ -∗
        sie_cap_gpr KT1 Mx K' b p -∗
        cpu_own 0%nat eb p b lks -∗
        pc_is (mword_of_int (KernelSyms.procdump + 0x8e)) -∗
        procdump_view -∗
        WP (Loop : expr riscv_lang)) -∗
    ∀ (j : nat) (M : regfile),
      ⌜ (j < NPROC)%nat ⌝ -∗ ⌜ pd_regs_loop M spv j /\ pd_regs_hi m0 M ⌝ -∗
      sie_cap_gpr KT1 M K' b p -∗
      cpu_own 0%nat eb p b lks -∗
      pc_is (mword_of_int (KernelSyms.procdump + 0x6e)) -∗
      ([∗ list] k ∈ seq 0 j, proc_dump_slot (proc_addr k)) -∗
      ([∗ list] k ∈ seq j (NPROC - j), proc_dump_slot (proc_addr k)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    intros Hpk HK Hfresh.
    iIntros "#Hkt #Hkd #Hpenv Hqexit".
    iAssert (∀ (fuel : nat),
      wp_next (CID0 := CID0) b p (fun (CIDf : CpuId) =>
        pdl_loop_body CID0 spv p m0 K' eb b lks fuel CIDf))%I
      with "[]" as "Hloop".
    { iIntros (fuel). iInduction fuel as [|fuel IHf] "IHf".
      { iIntros (CIDf Hsf j M) "%Hfuel %Hj %Hregs Hqx Hcg Hown Hpc Hpre Hsuf".
        exfalso. exact (pdl_no_fuel j Hfuel Hj). }
      iIntros (CIDf Hsf j M) "%Hfuel %Hj %Hregs Hqx Hcg Hown Hpc Hpre Hsuf".
      destruct Hregs as [Hrl Hrh].
      pose proof (pdl_j_le j Hj) as HjLe.
      (* ---- the slot at [j], out of the head of the remaining suffix ---- *)
      iEval (rewrite (pdl_seq_suffix j Hj)) in "Hsuf".
      iEval (rewrite big_sepL_cons) in "Hsuf".
      iDestruct "Hsuf" as "[Hslot Hsuf]".
      iDestruct "Hslot" as (dqs dqp dqn st pid nm) "(%Hnm & Hst & Hpid & Hnmc)".
      iPoseProof (pdi_56 with "Hkt") as "Hi56".
      iPoseProof (pdi_5a with "Hkt") as "Hi5a".
      iPoseProof (pdi_5c with "Hkt") as "Hi5c".
      iPoseProof (pdi_60 with "Hkt") as "Hi60".
      iPoseProof (pdi_62 with "Hkt") as "Hi62".
      iPoseProof (pdi_66 with "Hkt") as "Hi66".
      iPoseProof (pdi_6a with "Hkt") as "Hi6a".
      iPoseProof (pdi_6e with "Hkt") as "Hi6e".
      iPoseProof (pdi_70 with "Hkt") as "Hi70".
      iPoseProof (pdi_74 with "Hkt") as "Hi74".
      iPoseProof (pdi_76 with "Hkt") as "Hi76".
      iPoseProof (pdi_78 with "Hkt") as "Hi78".
      iPoseProof (pdi_7c with "Hkt") as "Hi7c".
      iPoseProof (pdi_80 with "Hkt") as "Hi80".
      iPoseProof (pdi_84 with "Hkt") as "Hi84".
      iPoseProof (pdi_86 with "Hkt") as "Hi86".
      iPoseProof (pdi_88 with "Hkt") as "Hi88".
      (* ================================================================ *)
      (* THE ADVANCE JOIN, +0x66 .. +0x6a                                  *)
      (* ================================================================ *)
      iAssert (□ wp_next (CID0 := CIDf) b p (fun (CIDa : CpuId) =>
        pdl_adv_body CID0 spv p m0 K' eb b lks j CIDa))%I
        with "[]" as "#Hadv".
      { iModIntro. iIntros (CIDa Hsa Ma) "%Hra Hqx2 Hcg Hown Hpc Hpre2 Hsuf2".
        destruct Hra as [Hral Hrah].
        (* ---- +0x66 addi s1,s1,360 ---- *)
        assert (Hrg66 : rget (CID := CIDa) Ma Rs1 = Ma !!! Regidx Rs1)
          by (rgne; reflexivity).
        iApply (wp_addi4_s_sconf (CID := CIDa)
                  (mword_of_int (KernelSyms.procdump + 0x66)) Rs1 Rs1
                  (mword_of_int 360 : mword 12) Ma K' b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi66").
        iIntros (CIDb Hsb) "Hcg Hpc".
        iEval (rewrite Hrg66) in "Hcg".
        set (Ma66 := <[Regidx Rs1 := regval_into_reg
                        (add_vec (Ma !!! Regidx Rs1)
                           (sign_extend' 64 (mword_of_int 360 : mword 12)))]> Ma).
        assert (Hval66 : add_vec (Ma !!! Regidx Rs1)
                           (sign_extend' 64 (mword_of_int 360 : mword 12))
                         = pd_cur (S j)).
        { rewrite (pdl_get_s1 Ma spv j Hral). apply pd_cur_succ. }
        assert (Hral66 : pd_regs_loop Ma66 spv (S j))
          by (rewrite /Ma66; apply (pdl_loop_s1 Ma _ spv j Hval66 Hral)).
        assert (Hrah66 : pd_regs_hi m0 Ma66)
          by (rewrite /Ma66; apply (pdl_hi_s1 m0 Ma _ Hrah)).
        assert (Hpp6a : add_vec_int
                          (mword_of_int (KernelSyms.procdump + 0x66) : mword 64) 4
                        = mword_of_int (KernelSyms.procdump + 0x6a)) by pcw.
        iEval (rewrite Hpp6a) in "Hpc".
        (* ---- +0x6a beq s1,s2 ---- *)
        assert (Hrg6a1 : rget (CID := CIDb) Ma66 Rs1 = Ma66 !!! Regidx Rs1)
          by (rgne; reflexivity).
        assert (Hrg6a2 : rget (CID := CIDb) Ma66 Rs2 = Ma66 !!! Regidx Rs2)
          by (rgne; reflexivity).
        assert (Hs1v : Ma66 !!! Regidx Rs1 = pd_cur (S j))
          by exact (pdl_get_s1 Ma66 spv (S j) Hral66).
        assert (Hs2v : Ma66 !!! Regidx Rs2 = pd_cur NPROC)
          by exact (pdl_get_s2 Ma66 spv (S j) Hral66).
        destruct (Nat.eq_dec (S j) NPROC) as [Heq | Hne].
        - (* the scan is over: TAKEN to +0x8e *)
          assert (Hcmp : eq_vec (rget (CID := CIDb) Ma66 Rs1)
                                (rget (CID := CIDb) Ma66 Rs2) = true).
          { rewrite Hrg6a1 Hrg6a2 Hs1v Hs2v Heq. apply pd_cur_eq_end_eq. }
          iApply (wp_beq_taken_s_sconf (CID := CIDb)
                    (mword_of_int (KernelSyms.procdump + 0x6a))
                    (mword_of_int 36 : mword 13) Rs2 Rs1 Ma66 K' b
                    ltac:(nz) ltac:(nz) Hcmp ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi6a").
          iApply bi.later_intro. iIntros (CIDc Hsc) "Hcg Hpc".
          assert (Htgt8e : add_vec
                             (mword_of_int (KernelSyms.procdump + 0x6a) : mword 64)
                             (sign_extend' 64 (mword_of_int 36 : mword 13))
                           = mword_of_int (KernelSyms.procdump + 0x8e)) by pcw.
          iEval (rewrite Htgt8e) in "Hpc".
         iDestruct (cpu_own_transport CIDa CIDc 0%nat eb p b 
                       ltac:(wp_next_chain) with "Hown") as "Hown".
          iSpecialize ("Hqx2" $! CIDc with "[%]"); [wp_next_chain|].
          iApply ("Hqx2" $! Ma66 with "[%] Hcg Hown Hpc [Hpre2]").
          + split; [exact (pdl_get_sp Ma66 spv (S j) Hral66) | exact Hrah66].
          + rewrite /procdump_view -Heq. iExact "Hpre2".
        - (* more slots: FALL to +0x6e *)
          assert (HSjLt : (S j < NPROC)%nat).
          { pose proof (pdl_sj_le j Hj) as Hle. lia. }
          assert (Hcmp : eq_vec (rget (CID := CIDb) Ma66 Rs1)
                                (rget (CID := CIDb) Ma66 Rs2) = false).
          { rewrite Hrg6a1 Hrg6a2 Hs1v Hs2v. apply (pd_cur_eq_end_lt (S j) HSjLt). }
          iApply (wp_beq_fall_s_sconf (CID := CIDb)
                    (mword_of_int (KernelSyms.procdump + 0x6a))
                    (mword_of_int 36 : mword 13) Rs2 Rs1 Ma66 K' b
                    ltac:(nz) ltac:(nz) Hcmp with "Hcg Hpc Hi6a").
          iIntros (CIDc Hsc) "Hcg Hpc".
          assert (Hpp6e : add_vec_int
                            (mword_of_int (KernelSyms.procdump + 0x6a) : mword 64) 4
                          = mword_of_int (KernelSyms.procdump + 0x6e)) by pcw.
          iEval (rewrite Hpp6e) in "Hpc".
          iDestruct (cpu_own_transport CIDa CIDc 0%nat eb p b 
                       ltac:(wp_next_chain) with "Hown") as "Hown".
          iSpecialize ("IHf" $! CIDc with "[%]"); [wp_next_chain|].
          iApply ("IHf" $! (S j) Ma66 with "[%] [%] [%] Hqx2 Hcg Hown Hpc Hpre2 Hsuf2").
          + exact (pdl_fuel_le j fuel Hfuel).
          + exact HSjLt.
          + split; [exact Hral66 | exact Hrah66]. }
      (* ================================================================ *)
      (* THE PRINT JOIN, +0x56 .. +0x64                                    *)
      (* ================================================================ *)
      iAssert (□ wp_next (CID0 := CIDf) b p (fun (CIDp : CpuId) =>
        pdl_print_body CID0 spv p m0 K' eb b lks j CIDp))%I
        with "[]" as "#Hprint".
      { iModIntro.
        iIntros (CIDp Hsp Mp sptr ss nm2 dq1 dq2 dq3 st2 pid2)
          "%Hrp %Hav %Hstr #Hss Hqx2 Hcg Hown Hpc Hst2 Hpid2 Hnmc2 Hpre2 Hsuf2".
        destruct Hrp as [Hrpl Hrph].
        destruct Hav as [Ha2v Ha3v].
        destruct Hstr as (Hssn & Hssz & Hnm2).
        (* ---- +0x56 lw a1,-296(a3) : a1 := p->pid ---- *)
        assert (Hpa56 : add_vec (rget (CID := CIDp) Mp Ra3)
                          (sign_extend' 64 (mword_of_int 3800 : mword 12))
                        = p_pid (proc_addr j)).
        { rgne. rewrite Ha3v. apply pd_cur_pid. }
        iEval (rewrite -Hpa56) in "Hpid2".
        iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (CID := CIDp)
                  (mword_of_int (KernelSyms.procdump + 0x56)) Ra1 Ra3
                  (mword_of_int 3800 : mword 12) Mp K' pid2 b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi56 Hpid2").
        iIntros (CIDq1 Hsq1) "Hcg Hpc Hpid2".
        iEval (rewrite Hpa56) in "Hpid2".
        set (P56 := <[Regidx Ra1 := regval_into_reg
                       (sign_extend' 64 (pid2 : mword 32))]> Mp).
        assert (Hrl56 : pd_regs_loop P56 spv j)
          by (rewrite /P56; apply pdl_loop_upd;
              [vm_compute; reflexivity | exact Hrpl]).
        assert (Hrh56 : pd_regs_hi m0 P56)
          by (rewrite /P56; apply pdl_hi_upd;
              [vm_compute; reflexivity | exact Hrph]).
        assert (Ha2_56 : P56 !!! Regidx Ra2 = sptr)
          by (rewrite /P56 upd_ne; [exact Ha2v | nz]).
        assert (Ha3_56 : P56 !!! Regidx Ra3 = pd_cur j)
          by (rewrite /P56 upd_ne; [exact Ha3v | nz]).
        assert (Hpp5a : add_vec_int
                          (mword_of_int (KernelSyms.procdump + 0x56) : mword 64) 4
                        = mword_of_int (KernelSyms.procdump + 0x5a)) by pcw.
        iEval (rewrite Hpp5a) in "Hpc".
        (* ---- +0x5a c.mv a0,s5 ---- *)
        assert (Hrg5a : rget (CID := CIDq1) P56 Rs5 = P56 !!! Regidx Rs5)
          by (rgne; reflexivity).
        iApply (wp_cmv_s_sconf (CID := CIDq1)
                  (mword_of_int (KernelSyms.procdump + 0x5a)) Ra0 Rs5 P56 K' b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi5a").
        iIntros (CIDq2 Hsq2) "Hcg Hpc".
        iEval (rewrite Hrg5a) in "Hcg".
        set (P5a := <[Regidx Ra0 := regval_into_reg
                       (add_vec zero_reg (P56 !!! Regidx Rs5))]> P56).
        assert (Ha0_5a : P5a !!! Regidx Ra0 = (mword_of_int pd_fmt_a : mword 64)).
        { rewrite /P5a upd_eq add_vec_zero_l.
          exact (pdl_get_s5 P56 spv j Hrl56). }
        assert (Hrl5a : pd_regs_loop P5a spv j)
          by (rewrite /P5a; apply pdl_loop_upd;
              [vm_compute; reflexivity | exact Hrl56]).
        assert (Hrh5a : pd_regs_hi m0 P5a)
          by (rewrite /P5a; apply pdl_hi_upd;
              [vm_compute; reflexivity | exact Hrh56]).
        assert (Ha2_5a : P5a !!! Regidx Ra2 = sptr)
          by (rewrite /P5a upd_ne; [exact Ha2_56 | nz]).
        assert (Ha3_5a : P5a !!! Regidx Ra3 = pd_cur j)
          by (rewrite /P5a upd_ne; [exact Ha3_56 | nz]).
        assert (Hpp5c : add_vec_int
                          (mword_of_int (KernelSyms.procdump + 0x5a) : mword 64) 2
                        = mword_of_int (KernelSyms.procdump + 0x5c)) by pcw.
        iEval (rewrite Hpp5c) in "Hpc".
        (* ---- +0x5c jal ra,printk ---- *)
        iApply (wp_jal_s_sconf (CID := CIDq2)
                  (mword_of_int (KernelSyms.procdump + 0x5c)) Rra
                  (mword_of_int 2089374 : mword 21) P5a K' b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi5c").
        iIntros (CIDq3 Hsq3) "Hcg Hpc".
        set (P5c := <[Regidx Rra := regval_into_reg
                       (add_vec_int
                          (mword_of_int (KernelSyms.procdump + 0x5c) : mword 64) 4)]> P5a).
        assert (Htgtpk1 : add_vec
                            (mword_of_int (KernelSyms.procdump + 0x5c) : mword 64)
                            (sign_extend' 64 (mword_of_int 2089374 : mword 21))
                          = mword_of_int KernelSyms.printk) by pcw.
        iEval (rewrite Htgtpk1) in "Hpc".
        assert (Hra_5c : P5c !!! Regidx Rra
                         = add_vec_int
                             (mword_of_int (KernelSyms.procdump + 0x5c) : mword 64) 4)
          by (rewrite /P5c; apply upd_eq).
        assert (Ha0_5c : P5c !!! Regidx Ra0 = (mword_of_int pd_fmt_a : mword 64))
          by (rewrite /P5c upd_ne; [exact Ha0_5a | nz]).
        assert (Ha2_5c : P5c !!! Regidx Ra2 = sptr)
          by (rewrite /P5c upd_ne; [exact Ha2_5a | nz]).
        assert (Ha3_5c : P5c !!! Regidx Ra3 = pd_cur j)
          by (rewrite /P5c upd_ne; [exact Ha3_5a | nz]).
        assert (Hrl5c : pd_regs_loop P5c spv j)
          by (rewrite /P5c; apply pdl_loop_upd;
              [vm_compute; reflexivity | exact Hrl5a]).
        assert (Hrh5c : pd_regs_hi m0 P5c)
          by (rewrite /P5c; apply pdl_hi_upd;
              [vm_compute; reflexivity | exact Hrh5a]).
        (* the name cell, in the spelling a3 has *)
        iEval (rewrite -(pd_cur_name j)) in "Hnmc2".
        iPoseProof (pd_fmt_str with "Hkd") as "Hfmt".
        iDestruct (cpu_own_transport CIDp CIDq3 0%nat eb p b 
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        iApply (Hpk CIDq3 P5c K' eb p DfracDiscarded pd_fmt
                  [PkANum; PkAStr DfracDiscarded ss; PkAStr dq3 nm2] b lks
                  ltac:(lia) pd_fmt_len pd_fmt_nonul
                  ltac:(rewrite pd_fmt_kinds; reflexivity)
                  ltac:(cbn [length]; lia)
                  Hfresh
                  with "Hcg Hkt Hkd Hpc Hown Hpenv [Hfmt] [Hnmc2]").
        all: try lkbelow.
        { rewrite Ha0_5c. iExact "Hfmt". }
        { iApply (pdl_descs_mk CIDq3 P5c sptr (pd_cur j) ss nm2 dq3
                    Ha2_5c Ha3_5c Hssn Hssz Hnm2 (pd_cur_nonzero j HjLe)
                    with "Hss Hnmc2"). }
        iIntros (CIDq4 Hsq4 mP1) "Hcg Hpc %Hcsp1 Hown _ Hdescs".
        destruct Hcsp1 as [Hcs1 Hra1].
        iDestruct (pdl_descs_take CIDq4 P5c sptr (pd_cur j) ss nm2 dq3
                     Ha2_5c Ha3_5c with "Hdescs") as "Hnmc2".
        assert (Hpc60 : ret_pc (P5c !!! Regidx Rra : mword 64)
                        = mword_of_int (KernelSyms.procdump + 0x60))
          by (rewrite Hra_5c; pcw).
        iEval (rewrite Hpc60) in "Hpc".
        assert (HrlP1 : pd_regs_loop mP1 spv j)
          by exact (pdl_loop_cs P5c mP1 spv j Hcs1 Hrl5c).
        assert (HrhP1 : pd_regs_hi m0 mP1)
          by exact (pd_regs_hi_trans m0 P5c mP1 Hrh5c (pd_regs_hi_of_cs _ _ Hcs1)).
        (* ---- +0x60 c.mv a0,s4 ---- *)
        assert (Hrg60 : rget (CID := CIDq4) mP1 Rs4 = mP1 !!! Regidx Rs4)
          by (rgne; reflexivity).
        iApply (wp_cmv_s_sconf (CID := CIDq4)
                  (mword_of_int (KernelSyms.procdump + 0x60)) Ra0 Rs4 mP1 K' b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi60").
        iIntros (CIDq5 Hsq5) "Hcg Hpc".
        iEval (rewrite Hrg60) in "Hcg".
        set (P60 := <[Regidx Ra0 := regval_into_reg
                       (add_vec zero_reg (mP1 !!! Regidx Rs4))]> mP1).
        assert (Ha0_60 : P60 !!! Regidx Ra0 = (mword_of_int pd_nl_a : mword 64)).
        { rewrite /P60 upd_eq add_vec_zero_l.
          exact (pdl_get_s4 mP1 spv j HrlP1). }
        assert (Hrl60 : pd_regs_loop P60 spv j)
          by (rewrite /P60; apply pdl_loop_upd;
              [vm_compute; reflexivity | exact HrlP1]).
        assert (Hrh60 : pd_regs_hi m0 P60)
          by (rewrite /P60; apply pdl_hi_upd;
              [vm_compute; reflexivity | exact HrhP1]).
        assert (Hpp62 : add_vec_int
                          (mword_of_int (KernelSyms.procdump + 0x60) : mword 64) 2
                        = mword_of_int (KernelSyms.procdump + 0x62)) by pcw.
        iEval (rewrite Hpp62) in "Hpc".
        (* ---- +0x62 jal ra,printk ---- *)
        iApply (wp_jal_s_sconf (CID := CIDq5)
                  (mword_of_int (KernelSyms.procdump + 0x62)) Rra
                  (mword_of_int 2089368 : mword 21) P60 K' b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi62").
        iIntros (CIDq6 Hsq6) "Hcg Hpc".
        set (P62 := <[Regidx Rra := regval_into_reg
                       (add_vec_int
                          (mword_of_int (KernelSyms.procdump + 0x62) : mword 64) 4)]> P60).
        assert (Htgtpk2 : add_vec
                            (mword_of_int (KernelSyms.procdump + 0x62) : mword 64)
                            (sign_extend' 64 (mword_of_int 2089368 : mword 21))
                          = mword_of_int KernelSyms.printk) by pcw.
        iEval (rewrite Htgtpk2) in "Hpc".
        assert (Hra_62 : P62 !!! Regidx Rra
                         = add_vec_int
                             (mword_of_int (KernelSyms.procdump + 0x62) : mword 64) 4)
          by (rewrite /P62; apply upd_eq).
        assert (Ha0_62 : P62 !!! Regidx Ra0 = (mword_of_int pd_nl_a : mword 64))
          by (rewrite /P62 upd_ne; [exact Ha0_60 | nz]).
        assert (Hrl62 : pd_regs_loop P62 spv j)
          by (rewrite /P62; apply pdl_loop_upd;
              [vm_compute; reflexivity | exact Hrl60]).
        assert (Hrh62 : pd_regs_hi m0 P62)
          by (rewrite /P62; apply pdl_hi_upd;
              [vm_compute; reflexivity | exact Hrh60]).
        iPoseProof (pd_nl_str with "Hkd") as "Hnlstr".
        iDestruct (cpu_own_transport CIDq4 CIDq6 0%nat eb p b
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        iApply (Hpk CIDq6 P62 K' eb p DfracDiscarded pd_nl [] b lks
                  ltac:(lia) pd_nl_len pd_nl_nonul
                  ltac:(rewrite pd_nl_kinds; reflexivity)
                  ltac:(cbn [length]; lia)
                  Hfresh
                  with "Hcg Hkt Hkd Hpc Hown Hpenv [Hnlstr] []").
        all: try lkbelow.
        { rewrite Ha0_62. iExact "Hnlstr". }
        { done. }
        iIntros (CIDq7 Hsq7 mP2) "Hcg Hpc %Hcsp2 Hown _ _".
        destruct Hcsp2 as [Hcs2 Hra2].
        assert (Hpc66 : ret_pc (P62 !!! Regidx Rra : mword 64)
                        = mword_of_int (KernelSyms.procdump + 0x66))
          by (rewrite Hra_62; pcw).
        iEval (rewrite Hpc66) in "Hpc".
        assert (HrlP2 : pd_regs_loop mP2 spv j)
          by exact (pdl_loop_cs P62 mP2 spv j Hcs2 Hrl62).
        assert (HrhP2 : pd_regs_hi m0 mP2)
          by exact (pd_regs_hi_trans m0 P62 mP2 Hrh62 (pd_regs_hi_of_cs _ _ Hcs2)).
        (* ---- reassemble the slot and hand over to the ADVANCE ---- *)
        iEval (rewrite (pd_cur_name j)) in "Hnmc2".
        iDestruct (pdl_slot_mk (proc_addr j) dq1 dq2 dq3 st2 pid2 nm2 Hnm2
                     with "Hst2 Hpid2 Hnmc2") as "Hslot2".
        iDestruct (pdl_prefix_step j with "Hpre2 Hslot2") as "Hpre2".
        iSpecialize ("Hadv" $! CIDq7 with "[%]"); [wp_next_chain|].
        iApply ("Hadv" $! mP2 with "[%] Hqx2 Hcg Hown Hpc Hpre2 Hsuf2").
        split; [exact HrlP2 | exact HrhP2]. }
      (* ================================================================ *)
      (* THE HEAD, +0x6e .. +0x8c                                          *)
      (* ================================================================ *)
      (* ---- +0x6e c.mv a3,s1 ---- *)
      assert (Hrg6e : rget (CID := CIDf) M Rs1 = M !!! Regidx Rs1)
        by (rgne; reflexivity).
      iApply (wp_cmv_s_sconf (CID := CIDf)
                (mword_of_int (KernelSyms.procdump + 0x6e)) Ra3 Rs1 M K' b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi6e").
      iIntros (CID1 Hs1) "Hcg Hpc".
      iEval (rewrite Hrg6e) in "Hcg".
      set (H6e := <[Regidx Ra3 := regval_into_reg
                     (add_vec zero_reg (M !!! Regidx Rs1))]> M).
      assert (Ha3_6e : H6e !!! Regidx Ra3 = pd_cur j).
      { rewrite /H6e upd_eq add_vec_zero_l. exact (pdl_get_s1 M spv j Hrl). }
      assert (Hrl6e : pd_regs_loop H6e spv j)
        by (rewrite /H6e; apply pdl_loop_upd;
            [vm_compute; reflexivity | exact Hrl]).
      assert (Hrh6e : pd_regs_hi m0 H6e)
        by (rewrite /H6e; apply pdl_hi_upd;
            [vm_compute; reflexivity | exact Hrh]).
      assert (Hpp70 : add_vec_int
                        (mword_of_int (KernelSyms.procdump + 0x6e) : mword 64) 2
                      = mword_of_int (KernelSyms.procdump + 0x70)) by pcw.
      iEval (rewrite Hpp70) in "Hpc".
      (* ---- +0x70 lw a5,-320(s1) : a5 := p->state ---- *)
      assert (Hpa70 : add_vec (rget (CID := CID1) H6e Rs1)
                        (sign_extend' 64 (mword_of_int 3776 : mword 12))
                      = p_state (proc_addr j)).
      { rgne. rewrite (pdl_get_s1 H6e spv j Hrl6e). apply pd_cur_state. }
      iEval (rewrite -Hpa70) in "Hst".
      iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (CID := CID1)
                (mword_of_int (KernelSyms.procdump + 0x70)) Ra5 Rs1
                (mword_of_int 3776 : mword 12) H6e K' st b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi70 Hst").
      iIntros (CID2 Hs2) "Hcg Hpc Hst".
      iEval (rewrite Hpa70) in "Hst".
      set (H70 := <[Regidx Ra5 := regval_into_reg
                     (sign_extend' 64 (st : mword 32))]> H6e).
      assert (Ha5_70 : H70 !!! Regidx Ra5 = (sign_extend' 64 (st : mword 32) : mword 64))
        by (rewrite /H70; apply upd_eq).
      assert (Ha3_70 : H70 !!! Regidx Ra3 = pd_cur j)
        by (rewrite /H70 upd_ne; [exact Ha3_6e | nz]).
      assert (Hrl70 : pd_regs_loop H70 spv j)
        by (rewrite /H70; apply pdl_loop_upd;
            [vm_compute; reflexivity | exact Hrl6e]).
      assert (Hrh70 : pd_regs_hi m0 H70)
        by (rewrite /H70; apply pdl_hi_upd;
            [vm_compute; reflexivity | exact Hrh6e]).
      assert (Hpp74 : add_vec_int
                        (mword_of_int (KernelSyms.procdump + 0x70) : mword 64) 4
                      = mword_of_int (KernelSyms.procdump + 0x74)) by pcw.
      iEval (rewrite Hpp74) in "Hpc".
      (* ---- +0x74 c.beqz a5 : UNUSED slots are skipped ---- *)
      assert (Hrg74 : rget (CID := CID2) H70 Ra5 = H70 !!! Regidx Ra5)
        by (rgne; reflexivity).
      destruct (eq_vec (H70 !!! Regidx Ra5) (zero_reg : mword 64)) eqn:Hzst.
      { (* state = UNUSED: TAKEN to +0x66 *)
        assert (Hcmp74 : eq_vec (rget (CID := CID2) H70 Ra5) (zero_reg : mword 64) = true)
          by (rewrite Hrg74; exact Hzst).
        iApply (wp_cbeqz_taken_s_sconf (CID := CID2)
                  (mword_of_int (KernelSyms.procdump + 0x74))
                  (mword_of_int 249 : mword 8) (Cregidx (mword_of_int 7)) Ra5 H70 K' b
                  ltac:(vm_compute; reflexivity) ltac:(nz) Hcmp74
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi74").
        iApply bi.later_intro. iIntros (CID3 Hs3) "Hcg Hpc".
        assert (Htgt66 : add_vec
                           (mword_of_int (KernelSyms.procdump + 0x74) : mword 64)
                           (sign_extend' 64
                              (sign_extend' 13
                                 (concat_vec (mword_of_int 249 : mword 8) ('b"0"))))
                         = mword_of_int (KernelSyms.procdump + 0x66)) by pcw.
        iEval (rewrite Htgt66) in "Hpc".
        iDestruct (pdl_slot_mk (proc_addr j) dqs dqp dqn st pid nm Hnm
                     with "Hst Hpid Hnmc") as "Hslot".
        iDestruct (pdl_prefix_step j with "Hpre Hslot") as "Hpre".
        iDestruct (cpu_own_transport CIDf CID3 0%nat eb p b
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        iSpecialize ("Hadv" $! CID3 with "[%]"); [wp_next_chain|].
        iApply ("Hadv" $! H70 with "[%] Hqx Hcg Hown Hpc Hpre Hsuf").
        split; [exact Hrl70 | exact Hrh70]. }
      (* state <> UNUSED *)
      assert (Hcmp74 : eq_vec (rget (CID := CID2) H70 Ra5) (zero_reg : mword 64) = false)
        by (rewrite Hrg74; exact Hzst).
      iApply (wp_cbeqz_fall_s_sconf (CID := CID2)
                (mword_of_int (KernelSyms.procdump + 0x74))
                (mword_of_int 249 : mword 8) (Cregidx (mword_of_int 7)) Ra5 H70 K' b
                ltac:(vm_compute; reflexivity) ltac:(nz) Hcmp74
                with "Hcg Hpc Hi74").
      iIntros (CID3 Hs3) "Hcg Hpc".
      assert (Hpp76 : add_vec_int
                        (mword_of_int (KernelSyms.procdump + 0x74) : mword 64) 2
                      = mword_of_int (KernelSyms.procdump + 0x76)) by pcw.
      iEval (rewrite Hpp76) in "Hpc".
      (* ---- +0x76 c.mv a2,s3 : a2 := "???" ---- *)
      assert (Hrg76 : rget (CID := CID3) H70 Rs3 = H70 !!! Regidx Rs3)
        by (rgne; reflexivity).
      iApply (wp_cmv_s_sconf (CID := CID3)
                (mword_of_int (KernelSyms.procdump + 0x76)) Ra2 Rs3 H70 K' b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi76").
      iIntros (CID4 Hs4) "Hcg Hpc".
      iEval (rewrite Hrg76) in "Hcg".
      set (H76 := <[Regidx Ra2 := regval_into_reg
                     (add_vec zero_reg (H70 !!! Regidx Rs3))]> H70).
      assert (Ha2_76 : H76 !!! Regidx Ra2 = (mword_of_int pd_qqq_a : mword 64)).
      { rewrite /H76 upd_eq add_vec_zero_l. exact (pdl_get_s3 H70 spv j Hrl70). }
      assert (Ha3_76 : H76 !!! Regidx Ra3 = pd_cur j)
        by (rewrite /H76 upd_ne; [exact Ha3_70 | nz]).
      assert (Ha5_76 : H76 !!! Regidx Ra5 = (sign_extend' 64 (st : mword 32) : mword 64))
        by (rewrite /H76 upd_ne; [exact Ha5_70 | nz]).
      assert (Hrl76 : pd_regs_loop H76 spv j)
        by (rewrite /H76; apply pdl_loop_upd;
            [vm_compute; reflexivity | exact Hrl70]).
      assert (Hrh76 : pd_regs_hi m0 H76)
        by (rewrite /H76; apply pdl_hi_upd;
            [vm_compute; reflexivity | exact Hrh70]).
      assert (Hpp78 : add_vec_int
                        (mword_of_int (KernelSyms.procdump + 0x76) : mword 64) 2
                      = mword_of_int (KernelSyms.procdump + 0x78)) by pcw.
      iEval (rewrite Hpp78) in "Hpc".
      (* ---- +0x78 bltu s6,a5 : out-of-range states print "???" ---- *)
      assert (Hrg78a : rget (CID := CID4) H76 Rs6 = H76 !!! Regidx Rs6)
        by (rgne; reflexivity).
      assert (Hrg78b : rget (CID := CID4) H76 Ra5 = H76 !!! Regidx Ra5)
        by (rgne; reflexivity).
      destruct (zopz0zI_u (H76 !!! Regidx Rs6) (H76 !!! Regidx Ra5)) eqn:Hbl.
      { (* 5 <u state : TAKEN to +0x56 with "???" *)
        assert (Hcmp78 : zopz0zI_u (rget (CID := CID4) H76 Rs6)
                                   (rget (CID := CID4) H76 Ra5) = true)
          by (rewrite Hrg78a Hrg78b; exact Hbl).
        iApply (wp_bltu_taken_s_sconf (CID := CID4)
                  (mword_of_int (KernelSyms.procdump + 0x78))
                  (mword_of_int 8158 : mword 13) Ra5 Rs6 H76 K' b
                  ltac:(nz) ltac:(nz) Hcmp78 ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi78").
        iApply bi.later_intro. iIntros (CID5 Hs5) "Hcg Hpc".
        assert (Htgt56 : add_vec
                           (mword_of_int (KernelSyms.procdump + 0x78) : mword 64)
                           (sign_extend' 64 (mword_of_int 8158 : mword 13))
                         = mword_of_int (KernelSyms.procdump + 0x56)) by pcw.
        iEval (rewrite Htgt56) in "Hpc".
        iPoseProof (pd_qqq_str with "Hkd") as "Hqqq".
        iDestruct (cpu_own_transport CIDf CID5 0%nat eb p b
                     ltac:(wp_next_chain) with "Hown") as "Hown".
        iSpecialize ("Hprint" $! CID5 with "[%]"); [wp_next_chain|].
        iApply ("Hprint" $! H76 (mword_of_int pd_qqq_a : mword 64) pd_qqq nm
                  dqs dqp dqn st pid
                  with "[%] [%] [%] Hqqq Hqx Hcg Hown Hpc Hst Hpid Hnmc Hpre Hsuf").
        - split; [exact Hrl76 | exact Hrh76].
        - split; [exact Ha2_76 | exact Ha3_76].
        - split; [exact pd_qqq_nonul |].
          split; [exact pd_qqq_p_nonzero | exact Hnm]. }
      (* state in 1..5 : the table arm *)
      assert (Hcmp78 : zopz0zI_u (rget (CID := CID4) H76 Rs6)
                                 (rget (CID := CID4) H76 Ra5) = false)
        by (rewrite Hrg78a Hrg78b; exact Hbl).
      assert (Hbl5 : zopz0zI_u (mword_of_int 5 : mword 64) (H76 !!! Regidx Ra5) = false).
      { rewrite -(pdl_get_s6 H76 spv j Hrl76). exact Hbl. }
      assert (Hnz5 : eq_vec (H76 !!! Regidx Ra5) (zero_reg : mword 64) = false)
        by (rewrite Ha5_76 -Ha5_70; exact Hzst).
      destruct (pdl_state_five (H76 !!! Regidx Ra5) Hnz5 Hbl5) as [k [Hk Hkv]].
      pose proof (pdl_state_lt6 k Hk) as Hk6.
      iApply (wp_bltu_fall_s_sconf (CID := CID4)
                (mword_of_int (KernelSyms.procdump + 0x78))
                (mword_of_int 8158 : mword 13) Ra5 Rs6 H76 K' b
                ltac:(nz) ltac:(nz) Hcmp78 with "Hcg Hpc Hi78").
      iIntros (CID5 Hs5) "Hcg Hpc".
      assert (Hpp7c : add_vec_int
                        (mword_of_int (KernelSyms.procdump + 0x78) : mword 64) 4
                      = mword_of_int (KernelSyms.procdump + 0x7c)) by pcw.
      iEval (rewrite Hpp7c) in "Hpc".
      (* ---- +0x7c slli a4,a5,32 ---- *)
      assert (Hrg7c : rget (CID := CID5) H76 Ra5 = H76 !!! Regidx Ra5)
        by (rgne; reflexivity).
      iApply (wp_slli_s_sconf (CID := CID5)
                (mword_of_int (KernelSyms.procdump + 0x7c)) Ra4 Ra5
                (mword_of_int 32 : mword 6)
                (shift_bits_left (rget (CID := CID5) H76 Ra5)
                   (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))
                H76 K' b
                ltac:(nz) ltac:(rdok) eq_refl with "Hcg Hpc Hi7c").
      iIntros (CID6 Hs6) "Hcg Hpc".
      iEval (rewrite Hrg7c) in "Hcg".
      set (H7c := <[Regidx Ra4 := regval_into_reg
                     (shift_bits_left (H76 !!! Regidx Ra5)
                        (subrange_vec_dec (mword_of_int 32 : mword 6)
                           (Z.sub log2_xlen 1) 0))]> H76).
      assert (Ha4_7c : H7c !!! Regidx Ra4
                       = shift_bits_left (mword_of_int (Z.of_nat k) : mword 64)
                           (subrange_vec_dec (mword_of_int 32 : mword 6)
                              (Z.sub log2_xlen 1) 0)).
      { rewrite /H7c upd_eq Hkv. reflexivity. }
      assert (Ha3_7c : H7c !!! Regidx Ra3 = pd_cur j)
        by (rewrite /H7c upd_ne; [exact Ha3_76 | nz]).
      assert (Hrl7c : pd_regs_loop H7c spv j)
        by (rewrite /H7c; apply pdl_loop_upd;
            [vm_compute; reflexivity | exact Hrl76]).
      assert (Hrh7c : pd_regs_hi m0 H7c)
        by (rewrite /H7c; apply pdl_hi_upd;
            [vm_compute; reflexivity | exact Hrh76]).
      assert (Hpp80 : add_vec_int
                        (mword_of_int (KernelSyms.procdump + 0x7c) : mword 64) 4
                      = mword_of_int (KernelSyms.procdump + 0x80)) by pcw.
      iEval (rewrite Hpp80) in "Hpc".
      (* ---- +0x80 srli a5,a4,29 ---- *)
      assert (Hrg80 : rget (CID := CID6) H7c Ra4 = H7c !!! Regidx Ra4)
        by (rgne; reflexivity).
      iApply (wp_srli4_s_sconf (CID := CID6)
                (mword_of_int (KernelSyms.procdump + 0x80)) Ra5 Ra4
                (mword_of_int 29 : mword 6) H7c K' b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi80").
      iIntros (CID7 Hs7) "Hcg Hpc".
      iEval (rewrite Hrg80) in "Hcg".
      set (H80 := <[Regidx Ra5 := regval_into_reg
                     (shift_bits_right (H7c !!! Regidx Ra4)
                        (subrange_vec_dec (mword_of_int 29 : mword 6)
                           (Z.sub log2_xlen 1) 0))]> H7c).
      assert (Ha5_80 : H80 !!! Regidx Ra5
                       = shift_bits_right
                           (shift_bits_left (mword_of_int (Z.of_nat k) : mword 64)
                              (subrange_vec_dec (mword_of_int 32 : mword 6)
                                 (Z.sub log2_xlen 1) 0))
                           (subrange_vec_dec (mword_of_int 29 : mword 6)
                              (Z.sub log2_xlen 1) 0)).
      { rewrite /H80 upd_eq Ha4_7c. reflexivity. }
      assert (Ha3_80 : H80 !!! Regidx Ra3 = pd_cur j)
        by (rewrite /H80 upd_ne; [exact Ha3_7c | nz]).
      assert (Hrl80 : pd_regs_loop H80 spv j)
        by (rewrite /H80; apply pdl_loop_upd;
            [vm_compute; reflexivity | exact Hrl7c]).
      assert (Hrh80 : pd_regs_hi m0 H80)
        by (rewrite /H80; apply pdl_hi_upd;
            [vm_compute; reflexivity | exact Hrh7c]).
      assert (Hpp84 : add_vec_int
                        (mword_of_int (KernelSyms.procdump + 0x80) : mword 64) 4
                      = mword_of_int (KernelSyms.procdump + 0x84)) by pcw.
      iEval (rewrite Hpp84) in "Hpc".
      (* ---- +0x84 c.add a5,a5,s7 ---- *)
      assert (Hrg84a : rget (CID := CID7) H80 Ra5 = H80 !!! Regidx Ra5)
        by (rgne; reflexivity).
      assert (Hrg84b : rget (CID := CID7) H80 Rs7 = H80 !!! Regidx Rs7)
        by (rgne; reflexivity).
      iApply (wp_cadd_s_sconf (CID := CID7)
                (mword_of_int (KernelSyms.procdump + 0x84)) Ra5 Rs7 H80 K' b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi84").
      iIntros (CID8 Hs8) "Hcg Hpc".
      iEval (rewrite Hrg84a) in "Hcg". iEval (rewrite Hrg84b) in "Hcg".
      set (H84 := <[Regidx Ra5 := regval_into_reg
                     (add_vec (H80 !!! Regidx Ra5) (H80 !!! Regidx Rs7))]> H80).
      assert (Ha3_84 : H84 !!! Regidx Ra3 = pd_cur j)
        by (rewrite /H84 upd_ne; [exact Ha3_80 | nz]).
      assert (Hrl84 : pd_regs_loop H84 spv j)
        by (rewrite /H84; apply pdl_loop_upd;
            [vm_compute; reflexivity | exact Hrl80]).
      assert (Hrh84 : pd_regs_hi m0 H84)
        by (rewrite /H84; apply pdl_hi_upd;
            [vm_compute; reflexivity | exact Hrh80]).
      assert (Hpp86 : add_vec_int
                        (mword_of_int (KernelSyms.procdump + 0x84) : mword 64) 2
                      = mword_of_int (KernelSyms.procdump + 0x86)) by pcw.
      iEval (rewrite Hpp86) in "Hpc".
      (* ---- +0x86 c.ld a2,0(a5) : a2 := states[state] ---- *)
      iPoseProof (pd_states_word k Hk6 with "Hkd") as "Htbl".
      assert (Hpa86 : add_vec (rget (CID := CID8) H84 Ra5)
                        (sign_extend' 64 (mword_of_int 0 : mword 12))
                      = (mword_of_int (pd_states_a + 8 * Z.of_nat k) : mword 64)).
      { rgne. rewrite /H84 upd_eq Ha5_80 (pdl_get_s7 H80 spv j Hrl80).
        exact (pdl_table_addr k Hk). }
      iEval (rewrite -Hpa86) in "Htbl".
      iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (CID := CID8)
                (mword_of_int (KernelSyms.procdump + 0x86)) Ra2 Ra5
                (mword_of_int 0 : mword 12) H84 K' (pd_state_p k) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi86 Htbl").
      iIntros (CID9 Hs9) "Hcg Hpc _".
      set (H86 := <[Regidx Ra2 := regval_into_reg (pd_state_p k)]> H84).
      assert (Ha2_86 : H86 !!! Regidx Ra2 = pd_state_p k)
        by (rewrite /H86; apply upd_eq).
      assert (Ha3_86 : H86 !!! Regidx Ra3 = pd_cur j)
        by (rewrite /H86 upd_ne; [exact Ha3_84 | nz]).
      assert (Hrl86 : pd_regs_loop H86 spv j)
        by (rewrite /H86; apply pdl_loop_upd;
            [vm_compute; reflexivity | exact Hrl84]).
      assert (Hrh86 : pd_regs_hi m0 H86)
        by (rewrite /H86; apply pdl_hi_upd;
            [vm_compute; reflexivity | exact Hrh84]).
      assert (Hpp88 : add_vec_int
                        (mword_of_int (KernelSyms.procdump + 0x86) : mword 64) 2
                      = mword_of_int (KernelSyms.procdump + 0x88)) by pcw.
      iEval (rewrite Hpp88) in "Hpc".
      (* ---- +0x88 c.bnez a2 : every entry 1..5 is non-null, so ALWAYS taken --- *)
      assert (Hrg88 : rget (CID := CID9) H86 Ra2 = H86 !!! Regidx Ra2)
        by (rgne; reflexivity).
      assert (Hcmp88 : neq_vec (rget (CID := CID9) H86 Ra2) (zero_reg : mword 64) = true).
      { rewrite Hrg88 Ha2_86. unfold neq_vec.
        rewrite (pd_state_p_nonzero k Hk6). reflexivity. }
      iApply (wp_cbnez_taken_s_sconf (CID := CID9)
                (mword_of_int (KernelSyms.procdump + 0x88))
                (mword_of_int 231 : mword 8) (Cregidx (mword_of_int 4)) Ra2 H86 K' b
                ltac:(vm_compute; reflexivity) ltac:(nz) Hcmp88
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi88").
      iApply bi.later_intro. iIntros (CID10 Hs10) "Hcg Hpc".
      assert (Htgt56b : add_vec
                          (mword_of_int (KernelSyms.procdump + 0x88) : mword 64)
                          (sign_extend' 64
                             (sign_extend' 13
                                (concat_vec (mword_of_int 231 : mword 8) ('b"0"))))
                        = mword_of_int (KernelSyms.procdump + 0x56)) by pcw.
      iEval (rewrite Htgt56b) in "Hpc".
      iPoseProof (pd_state_str k Hk6 with "Hkd") as "Hsstr".
      iDestruct (cpu_own_transport CIDf CID10 0%nat eb p b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iSpecialize ("Hprint" $! CID10 with "[%]"); [wp_next_chain|].
      iApply ("Hprint" $! H86 (pd_state_p k) (pd_state_name k) nm
                dqs dqp dqn st pid
                with "[%] [%] [%] Hsstr Hqx Hcg Hown Hpc Hst Hpid Hnmc Hpre Hsuf").
      - split; [exact Hrl86 | exact Hrh86].
      - split; [exact Ha2_86 | exact Ha3_86].
      - split; [exact (pd_state_nonul k Hk6) |].
        split; [exact (pd_state_p_nonzero k Hk6) | exact Hnm]. }
    (* ---------------------------------------------------------------- *)
    iIntros (j M) "%Hj %Hregs Hcg Hown Hpc Hpre Hsuf".
    iSpecialize ("Hloop" $! (NPROC - j)%nat).
    iSpecialize ("Hloop" $! CID0 with "[%]"); [by intros|].
    iApply ("Hloop" $! j M with "[%] [%] [%] Hqexit Hcg Hown Hpc Hpre Hsuf");
      [reflexivity | exact Hj | exact Hregs].
  Qed.

End ProofProcdumpLoop.
