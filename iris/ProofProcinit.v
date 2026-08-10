(* ProofProcinit.v -- the whole-function WP for xv6's procinit() over the
   SIE-agnostic sconf world.

     void procinit(void) {
       initlock(&pid_lock, "nextpid");
       initlock(&wait_lock, "wait_lock");
       for (p = proc; p < &proc[NPROC]; p++) {
         initlock(&p->lock, "proc");
         p->state  = UNUSED;
         p->kstack = KSTACK((int)(p - proc));
       }
     }

   Three parts.

   (1) The prologue: an 8-slot frame (ra, s0..s6 -- every slot is used), the
   two standalone initlock calls, and then the loop's SIX live registers, all
   of them constants the compiler hoisted out of the body:

     s1 = p (the cursor)      s2 = 0x4fa4fa4fa4fa4fa5 (the /360 magic)
     s3 = 0x3FFFFFF000 (TRAMPOLINE)                    s4 = &proc[NPROC]
     s5 = proc (the base, for p - proc)                s6 = &"proc"

   (2) The loop, proved -- like iinit's over initsleeplock -- by ordinary Coq
   fuel induction on the number of processes left, NOT iLoeb (the packaged
   sconf leaves strip the step's later).  The cursor is [SpecProcinit.pacur],
   so the [bne s1,s4] back edge becomes the index test [S j =? NPROC]
   ([ArrCursor.acur_neq]) and [addi s1,s1,360] becomes [S j]
   ([ProcGeom.proc_addr_succ]).

   (3) The KSTACK address, shared verbatim with proc_mapstacks: gcc divides
   [p - proc] by 360 with a multiply by the modular inverse of 45, and
   KstackArith.v is that arithmetic.  The helper lemmas at the top of this
   file are the four steps of the chain instantiated at procinit's registers,
   stated OUTSIDE the Iris section so their [lia]s run without an mword in
   context (durable-notes.md).

   The fd-slot supply is routed ONCE, before the loop: [proc_seal_list] turns
   the [proc_dormant_nofd] blocks the caller handed over into real
   [proc_dormant]s ([ProcInv.proc_dormant_seal]).  Nothing about the
   distribution is per-iteration -- procinit's code never touches an fd -- so
   keeping it out of the loop invariant costs nothing and says the true
   thing. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import KernelText KernelDataInv.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import WpLock.
Require Import ArrCursor.
Require Import ProcGeom.
Require Import FdSlots.
Require Import FileInv.
Require Import ProcInv.
Require Import KvmMap.
Require Import KstackArith.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl WpSconfVc.
Require Import SpecInitlock.
Require Import CodeProcinit.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecProcinit.
Local Open Scope Z_scope.
Import Defs.

(* A failing tactic in a whole-function WP over [proc_dormant] otherwise
   prints a goal that takes tens of minutes to format (durable-notes). *)
Set Printing Depth 40.

(* ===================================================================== *)
(*  The KSTACK chain at procinit's registers -- Iris-free, so every [lia] *)
(*  here runs with no mword in context.                                   *)
(* ===================================================================== *)

(* +0x84 [sub a5,s1,s5]: the cursor minus the base IS 360*j.  The two
   operands are the loop's [proc_addr j] and the hoisted [proc]. *)
Lemma pi_sub_base (j : nat) : (j < NPROC)%nat ->
  sub_vec (proc_addr j) (mword_of_int KernelSyms.proc : mword 64)
  = (mword_of_int (360 * Z.of_nat j) : mword 64).
Proof.
  intro Hj. unfold NPROC in Hj.
  assert (Hnn : (0 <= 360 * Z.of_nat j)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hle : (360 * Z.of_nat j <= 360 * 64)%Z)
    by (apply Z.mul_le_mono_nonneg_l; lia).
  rewrite proc_addr_acur. unfold pacur, acur, proc_size.
  rewrite (subvec_moi (KernelSyms.proc + 360 * Z.of_nat j) KernelSyms.proc
             ltac:(unfold KernelSyms.proc; lia)
             ltac:(lia)
             ltac:(unfold KernelSyms.proc; lia)).
  f_equal. lia.
Qed.

(* +0x88 [srai a5,a5,3]: 360*j >>s 3 = 45*j. *)
Lemma pi_srai (j : nat) : (j < NPROC)%nat ->
  shift_bits_right_arith (mword_of_int (360 * Z.of_nat j) : mword 64)
    (subrange_vec_dec (mword_of_int 3 : mword 6) 5 0)
  = (mword_of_int (45 * Z.of_nat j) : mword 64).
Proof.
  intro Hj. unfold NPROC in Hj.
  assert (Hle : (360 * Z.of_nat j <= 360 * 64)%Z)
    by (apply Z.mul_le_mono_nonneg_l; lia).
  rewrite (srai3 (360 * Z.of_nat j)
             ltac:(split; [apply Z.mul_nonneg_nonneg; lia | lia])).
  replace (360 * Z.of_nat j)%Z with (45 * Z.of_nat j * 8)%Z by ring.
  rewrite Z.div_mul; [reflexivity | lia].
Qed.

(* +0x8e [slli a5,a5,13]: j << 13 = 8192*j. *)
Lemma pi_slli (j : nat) : (j < NPROC)%nat ->
  shift_bits_left (mword_of_int (Z.of_nat j) : mword 64)
    (subrange_vec_dec (mword_of_int 13 : mword 6) 5 0)
  = (mword_of_int (8192 * Z.of_nat j) : mword 64).
Proof.
  intro Hj. unfold NPROC in Hj.
  rewrite (slli13 (Z.of_nat j) ltac:(lia)
             ltac:(assert (Z.of_nat j * 8192 <= 64 * 8192)%Z
                     by (apply Z.mul_le_mono_nonneg_r; lia); lia)).
  replace (8192 * Z.of_nat j)%Z with (Z.of_nat j * 8192)%Z by ring.
  reflexivity.
Qed.

(* +0x94 [sub a5,s3,a5]: TRAMPOLINE - 8192*(j+1) IS KSTACK(j). *)
Lemma pi_sub_tramp (j : nat) : (j < NPROC)%nat ->
  sub_vec (mword_of_int 0x3FFFFFF000 : mword 64)
          (mword_of_int (8192 * (Z.of_nat j + 1)) : mword 64)
  = kstack_va j.
Proof.
  intro Hj. unfold NPROC in Hj. unfold kstack_va.
  assert (Hle : (8192 * (Z.of_nat j + 1) <= 8192 * 64)%Z)
    by (apply Z.mul_le_mono_nonneg_l; lia).
  apply subvec_moi; [apply Z.mul_nonneg_nonneg; lia | lia | lia].
Qed.

(* The two field addresses the loop body stores through, in the form the
   [sw]/[c.sd] displacement gives them. *)
Lemma pi_state_addr (pa : mword 64) :
  add_vec pa (sign_extend' 64 (mword_of_int 24 : mword 12)) = p_state pa.
Proof.
  unfold p_state, state_off.
  assert (H : sign_extend' 64 (mword_of_int 24 : mword 12) = (mword_of_int 24 : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H. reflexivity.
Qed.

Lemma pi_kstack_addr (pa : mword 64) :
  add_vec pa (sign_extend' 64 (mword_of_int 64 : mword 12)) = p_kstack pa.
Proof.
  unfold p_kstack.
  assert (H : sign_extend' 64 (mword_of_int 64 : mword 12) = (mword_of_int 64 : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H. reflexivity.
Qed.

Module ProcinitProof (Initlock : INITLOCK) : PROCINIT.

Section ProofProcinit.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{!lockG Σ}.
  Context `{!fileG Σ}.
  Context `{!fdslotG Σ, !irefNameG Σ, !irefslotG Σ}.
  (* NOTE: no shared [Context `{GEN : GenId} `{CID : CpuId}] here -- the epilogue/loop
     lemmas below apply EACH OTHER at a hart that a [wp_next] crossing may
     have migrated to, so each needs its OWN implicit per-lemma [CID]
     binder (shadowing what a section Context would give); see the porting
     guide's "Two things a DECOMPOSED proof needs". *)


  (* the register indices the loop keeps live *)
  Notation s0i := (mword_of_int 8 : mword 5).
  Notation s1i := (mword_of_int 9 : mword 5).
  Notation s2i := (mword_of_int 18 : mword 5).
  Notation s3i := (mword_of_int 19 : mword 5).
  Notation s4i := (mword_of_int 20 : mword 5).
  Notation s5i := (mword_of_int 21 : mword 5).
  Notation s6i := (mword_of_int 22 : mword 5).
  Notation rai := (mword_of_int 1 : mword 5).
  Notation a0i := (mword_of_int 10 : mword 5).
  Notation a1i := (mword_of_int 11 : mword 5).
  Notation a4i := (mword_of_int 14 : mword 5).
  Notation a5i := (mword_of_int 15 : mword 5).

  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.
  (* peel ONE update layer at a time; unfolding a whole set-chain first is
     quadratic in the depth (claude-notes/optimization.md). *)
  Ltac peel_reg_step :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ].
  Ltac peel_reg := peel_reg_step; reflexivity.

  (* the three hoisted constants, named *)
  Definition pi_magic : mword 64 := mword_of_int 0x4fa4fa4fa4fa4fa5.
  Definition pi_tramp : mword 64 := mword_of_int 0x3FFFFFF000.

  (* ================================================================= *)
  (*  Routing the fd-slot supply (once, before the loop).               *)
  (* ================================================================= *)
  (* A process whose block has already been given its NOFILE units: what
     the loop actually consumes.  Everything else is exactly [proc_raw]. *)
  Definition proc_seal (pa : mword 64) : iProp Σ :=
    (∃ (vst : mword 32) (vks : mword 64),
       lk_raw pa ∗
       p_state pa ↦₄ vst ∗
       p_kstack pa ↦₈ vks ∗
       proc_dormant pa UNUSED)%I.

  (* Stated over an arbitrary LIST so the induction is a plain cons peel --
     the list's elements never matter, only how many there are. *)
  Lemma proc_seal_list (l : list nat) :
    ([∗ list] i ∈ l, proc_raw (proc_addr i)) -∗
    fd_slots (length l * (NOFILE + FDSPARE)) -∗
    iref_slots (length l * (1 + IREFSPARE)) -∗
    [∗ list] i ∈ l, proc_seal (proc_addr i).
  Proof.
    induction l as [|x l IH]; iIntros "Hraw Hsl Hir"; [done|].
    iDestruct "Hraw" as "[Hx Hraw]".
    cbn [length].
    replace (S (length l) * (NOFILE + FDSPARE))%nat
      with ((NOFILE + FDSPARE) + length l * (NOFILE + FDSPARE))%nat by lia.
    replace (S (length l) * (1 + IREFSPARE))%nat
      with ((1 + IREFSPARE) + length l * (1 + IREFSPARE))%nat by lia.
    iDestruct (fd_slots_split with "Hsl") as "[Hs1 Hsl]".
    iDestruct (iref_slots_split with "Hir") as "[Hi1 Hir]".
    iSplitL "Hx Hs1 Hi1".
    - iDestruct "Hx" as (vst vks) "(Hlk & Hst & Hks & Hdorm)".
      iExists vst, vks. iFrame "Hlk Hst Hks".
      iApply (proc_dormant_seal with "Hdorm Hs1 Hi1").
    - iApply (IH with "Hraw Hsl Hir").
  Qed.

  (* ================================================================= *)
  (*  The epilogue (+0xa2..+0xb4): restore ra/s0..s6, give the 8-slot    *)
  (*  frame back, ret.  Payload-free -- the caller's postcondition        *)
  (*  resources ride in the framed [-] -- and factored out because it is  *)
  (*  60 lines of frame arithmetic.                                      *)
  (* ================================================================= *)
  (* [CID0] is its OWN binder here: this "post-resume half" gets applied at
     whichever hart the loop's own leaf steps actually migrated to, not
     necessarily the entry hart of [wp_procinit_sconf]. *)
  Lemma piepi `{GEN : GenId} `{CID0 : CpuId} (m Me : regfile) (K : nat)
      (b : bool) (p : mword 64) :
    let sp0 := m !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
    let ret_tgt := ret_pc (m !!! Regidx rai) in
    (8 <= K)%nat ->
    Me !!! Regidx csp_rs1 = spr ->
    (forall c : mword 5, is_cs_idx c = true ->
       c <> s0i -> c <> s1i -> c <> s2i -> c <> s3i -> c <> s4i -> c <> s5i ->
       c <> s6i -> c <> csp_rs1 ->
       Me !!! Regidx c = m !!! Regidx c) ->
    kernel_text -∗
    sie_cap_gpr Me (K - 8) b p -∗
    pc_is (mword_of_int (KernelSyms.procinit + 0xa2)) -∗
    (pa_stk sp0 1) ↦₈ (m !!! Regidx rai : mword 64) -∗
    (pa_stk sp0 2) ↦₈ (m !!! Regidx s0i : mword 64) -∗
    (pa_stk sp0 3) ↦₈ (m !!! Regidx s1i : mword 64) -∗
    (pa_stk sp0 4) ↦₈ (m !!! Regidx s2i : mword 64) -∗
    (pa_stk sp0 5) ↦₈ (m !!! Regidx s3i : mword 64) -∗
    (pa_stk sp0 6) ↦₈ (m !!! Regidx s4i : mword 64) -∗
    (pa_stk sp0 7) ↦₈ (m !!! Regidx s5i : mword 64) -∗
    (pa_stk sp0 8) ↦₈ (m !!! Regidx s6i : mword 64) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mr,
      sie_cap_gpr mr K b p -∗
      pc_is ret_tgt -∗ ⌜ callee_saved m mr ⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 spr ret_tgt HK8 HMesp HMecs.
    assert (Hspr8 : spr = pa_stk sp0 8).
    { unfold spr, pa_stk, add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb7 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 7).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb8 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 8).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iIntros "#Htext Hcg Hpc Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hc7 Hc8 Hcont".
    iPoseProof (pii_a2 with "Htext") as "Hia2".
    iPoseProof (pii_a4 with "Htext") as "Hia4".
    iPoseProof (pii_a6 with "Htext") as "Hia6".
    iPoseProof (pii_a8 with "Htext") as "Hia8".
    iPoseProof (pii_aa with "Htext") as "Hiaa".
    iPoseProof (pii_ac with "Htext") as "Hiac".
    iPoseProof (pii_ae with "Htext") as "Hiae".
    iPoseProof (pii_b0 with "Htext") as "Hib0".
    iPoseProof (pii_b2 with "Htext") as "Hib2".
    iPoseProof (pii_b4 with "Htext") as "Hib4".
    (* +0xa2 c.ldsp ra,56(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.procinit + 0xa2)) (mword_of_int 7 : mword 6) rai
              Me (K - 8)%nat (m !!! Regidx rai) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hia2 [Hc1] [-]").
    { iEval (rewrite HMesp Hb1). iExact "Hc1". }
    iIntros (CID1 Hs1) "Hcg Hpc Hc1".
    iEval (rewrite HMesp Hb1) in "Hc1".
    set (E1 := <[Regidx rai := regval_into_reg (m !!! Regidx rai)]> Me).
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spr) by (rewrite /E1 upd_ne; [exact HMesp | reg_neq]).
    assert (Hpa4 : add_vec_int (mword_of_int (KernelSyms.procinit + 0xa2) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0xa4)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa4) in "Hpc".
    (* +0xa4 c.ldsp s0,48(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.procinit + 0xa4)) (mword_of_int 6 : mword 6) s0i
              E1 (K - 8)%nat (m !!! Regidx s0i) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hia4 [Hc2] [-]").
    { iEval (rewrite HE1sp Hb2). iExact "Hc2". }
    iIntros (CID2 Hs2) "Hcg Hpc Hc2".
    iEval (rewrite HE1sp Hb2) in "Hc2".
    set (E2 := <[Regidx s0i := regval_into_reg (m !!! Regidx s0i)]> E1).
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spr) by (rewrite /E2 upd_ne; [exact HE1sp | reg_neq]).
    assert (Hpa6 : add_vec_int (mword_of_int (KernelSyms.procinit + 0xa4) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0xa6)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa6) in "Hpc".
    (* +0xa6 c.ldsp s1,40(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.procinit + 0xa6)) (mword_of_int 5 : mword 6) s1i
              E2 (K - 8)%nat (m !!! Regidx s1i) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hia6 [Hc3] [-]").
    { iEval (rewrite HE2sp Hb3). iExact "Hc3". }
    iIntros (CID3 Hs3) "Hcg Hpc Hc3".
    iEval (rewrite HE2sp Hb3) in "Hc3".
    set (E3 := <[Regidx s1i := regval_into_reg (m !!! Regidx s1i)]> E2).
    assert (HE3sp : E3 !!! Regidx csp_rs1 = spr) by (rewrite /E3 upd_ne; [exact HE2sp | reg_neq]).
    assert (Hpa8 : add_vec_int (mword_of_int (KernelSyms.procinit + 0xa6) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0xa8)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa8) in "Hpc".
    (* +0xa8 c.ldsp s2,32(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.procinit + 0xa8)) (mword_of_int 4 : mword 6) s2i
              E3 (K - 8)%nat (m !!! Regidx s2i) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hia8 [Hc4] [-]").
    { iEval (rewrite HE3sp Hb4). iExact "Hc4". }
    iIntros (CID4 Hs4) "Hcg Hpc Hc4".
    iEval (rewrite HE3sp Hb4) in "Hc4".
    set (E4 := <[Regidx s2i := regval_into_reg (m !!! Regidx s2i)]> E3).
    assert (HE4sp : E4 !!! Regidx csp_rs1 = spr) by (rewrite /E4 upd_ne; [exact HE3sp | reg_neq]).
    assert (Hpaa : add_vec_int (mword_of_int (KernelSyms.procinit + 0xa8) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0xaa)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpaa) in "Hpc".
    (* +0xaa c.ldsp s3,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.procinit + 0xaa)) (mword_of_int 3 : mword 6) s3i
              E4 (K - 8)%nat (m !!! Regidx s3i) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hiaa [Hc5] [-]").
    { iEval (rewrite HE4sp Hb5). iExact "Hc5". }
    iIntros (CID5 Hs5) "Hcg Hpc Hc5".
    iEval (rewrite HE4sp Hb5) in "Hc5".
    set (E5 := <[Regidx s3i := regval_into_reg (m !!! Regidx s3i)]> E4).
    assert (HE5sp : E5 !!! Regidx csp_rs1 = spr) by (rewrite /E5 upd_ne; [exact HE4sp | reg_neq]).
    assert (Hpac : add_vec_int (mword_of_int (KernelSyms.procinit + 0xaa) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0xac)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpac) in "Hpc".
    (* +0xac c.ldsp s4,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.procinit + 0xac)) (mword_of_int 2 : mword 6) s4i
              E5 (K - 8)%nat (m !!! Regidx s4i) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hiac [Hc6] [-]").
    { iEval (rewrite HE5sp Hb6). iExact "Hc6". }
    iIntros (CID6 Hs6) "Hcg Hpc Hc6".
    iEval (rewrite HE5sp Hb6) in "Hc6".
    set (E6 := <[Regidx s4i := regval_into_reg (m !!! Regidx s4i)]> E5).
    assert (HE6sp : E6 !!! Regidx csp_rs1 = spr) by (rewrite /E6 upd_ne; [exact HE5sp | reg_neq]).
    assert (Hpae : add_vec_int (mword_of_int (KernelSyms.procinit + 0xac) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0xae)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpae) in "Hpc".
    (* +0xae c.ldsp s5,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.procinit + 0xae)) (mword_of_int 1 : mword 6) s5i
              E6 (K - 8)%nat (m !!! Regidx s5i) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hiae [Hc7] [-]").
    { iEval (rewrite HE6sp Hb7). iExact "Hc7". }
    iIntros (CID7 Hs7) "Hcg Hpc Hc7".
    iEval (rewrite HE6sp Hb7) in "Hc7".
    set (E7 := <[Regidx s5i := regval_into_reg (m !!! Regidx s5i)]> E6).
    assert (HE7sp : E7 !!! Regidx csp_rs1 = spr) by (rewrite /E7 upd_ne; [exact HE6sp | reg_neq]).
    assert (Hpb0 : add_vec_int (mword_of_int (KernelSyms.procinit + 0xae) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0xb0)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpb0) in "Hpc".
    (* +0xb0 c.ldsp s6,0(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.procinit + 0xb0)) (mword_of_int 0 : mword 6) s6i
              E7 (K - 8)%nat (m !!! Regidx s6i) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hib0 [Hc8] [-]").
    { iEval (rewrite HE7sp Hb8). iExact "Hc8". }
    iIntros (CID8 Hs8) "Hcg Hpc Hc8".
    iEval (rewrite HE7sp Hb8) in "Hc8".
    set (E8 := <[Regidx s6i := regval_into_reg (m !!! Regidx s6i)]> E7).
    assert (HE8sp : E8 !!! Regidx csp_rs1 = spr) by (rewrite /E8 upd_ne; [exact HE7sp | reg_neq]).
    assert (Hpb2 : add_vec_int (mword_of_int (KernelSyms.procinit + 0xb0) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0xb2)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpb2) in "Hpc".
    (* +0xb2 c.addi16sp sp,64 -- the frame trade back (pop 8) *)
    set (E9 := <[Regidx csp_rs1 := regval_into_reg (add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> E8).
    assert (HE9sp : E9 !!! Regidx csp_rs1 = sp0).
    { rewrite /E9 upd_eq. rewrite HE8sp.
      unfold spr. rewrite pa_stk_off2.
      replace (mword_of_int (bv_wrap 64 (uint (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)) : mword 64) + uint (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)) : mword 64))) : mword 64) with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      change (add_vec sp0 (mword_of_int 0)) with (add_vec_int sp0 0). apply avi0. }
    assert (Hwv : add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))) = sp0).
    { rewrite -HE9sp /E9 upd_eq. reflexivity. }
    assert (Hpop : E8 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)))) 8).
    { rewrite Hwv HE8sp Hspr8. reflexivity. }
    iAssert (stack_own sp0 8) with "[Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hc7 Hc8]" as "Hframe8".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hc1"; [iExists _; iExact "Hc1"|].
      iSplitL "Hc2"; [iExists _; iExact "Hc2"|].
      iSplitL "Hc3"; [iExists _; iExact "Hc3"|].
      iSplitL "Hc4"; [iExists _; iExact "Hc4"|].
      iSplitL "Hc5"; [iExists _; iExact "Hc5"|].
      iSplitL "Hc6"; [iExists _; iExact "Hc6"|].
      iSplitL "Hc7"; [iExists _; iExact "Hc7"|].
      iSplitL "Hc8"; [iExists _; iExact "Hc8"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe8".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.procinit + 0xb2)) (mword_of_int 4 : mword 6) E8 (K - 8)%nat 8 b Hpop
              with "Hcg Hpc Hib2 Hframe8 [-]").
    iIntros (CID9 Hs9) "Hcg Hpc".
    assert (Hnk : ((K - 8) + 8)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> E8) with E9.
    assert (Hpb4 : add_vec_int (mword_of_int (KernelSyms.procinit + 0xb2) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0xb4)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpb4) in "Hpc".
    (* +0xb4 c.ret *)
    assert (HE9ra : E9 !!! Regidx rai = m !!! Regidx rai).
    { rewrite /E9 upd_ne; [| reg_neq]. rewrite /E8 upd_ne; [| reg_neq].
      rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_ne; [| reg_neq].
      rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq].
      rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq].
      rewrite /E1 upd_eq; reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.procinit + 0xb4)) rai E9 K b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hib4 [-]").
    iIntros (CID10 Hs10) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (E9 !!! Regidx rai) = ret_tgt) by (rewrite HE9ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    iSpecialize ("Hcont" $! CID10 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E9 with "Hcg Hpc [%]").
    (* callee_saved m E9 *)
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
              c <> s0i -> c <> s1i -> c <> s2i -> c <> s3i -> c <> s4i -> c <> s5i ->
              c <> s6i -> c <> csp_rs1 ->
              E9 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N8 N9 N18 N19 N20 N21 N22 Nsp.
      pose proof (is_cs_idx_true_neq rai c ltac:(vm_compute; reflexivity) Hc) as Nra.
      rewrite /E9 upd_ne; [| congruence].
      rewrite /E8 upd_ne; [| congruence].
      rewrite /E7 upd_ne; [| congruence].
      rewrite /E6 upd_ne; [| congruence].
      rewrite /E5 upd_ne; [| congruence].
      rewrite /E4 upd_ne; [| congruence].
      rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      apply HMecs; assumption. }
    assert (Hcs_s0 : E9 !!! Regidx s0i = m !!! Regidx s0i).
    { rewrite /E9 upd_ne; [| reg_neq]. rewrite /E8 upd_ne; [| reg_neq].
      rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_ne; [| reg_neq].
      rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq].
      rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_eq; reflexivity. }
    assert (Hcs_s1 : E9 !!! Regidx s1i = m !!! Regidx s1i).
    { rewrite /E9 upd_ne; [| reg_neq]. rewrite /E8 upd_ne; [| reg_neq].
      rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_ne; [| reg_neq].
      rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq].
      rewrite /E3 upd_eq; reflexivity. }
    assert (Hcs_s2 : E9 !!! Regidx s2i = m !!! Regidx s2i).
    { rewrite /E9 upd_ne; [| reg_neq]. rewrite /E8 upd_ne; [| reg_neq].
      rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_ne; [| reg_neq].
      rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_eq; reflexivity. }
    assert (Hcs_s3 : E9 !!! Regidx s3i = m !!! Regidx s3i).
    { rewrite /E9 upd_ne; [| reg_neq]. rewrite /E8 upd_ne; [| reg_neq].
      rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_ne; [| reg_neq].
      rewrite /E5 upd_eq; reflexivity. }
    assert (Hcs_s4 : E9 !!! Regidx s4i = m !!! Regidx s4i).
    { rewrite /E9 upd_ne; [| reg_neq]. rewrite /E8 upd_ne; [| reg_neq].
      rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_eq; reflexivity. }
    assert (Hcs_s5 : E9 !!! Regidx s5i = m !!! Regidx s5i).
    { rewrite /E9 upd_ne; [| reg_neq]. rewrite /E8 upd_ne; [| reg_neq].
      rewrite /E7 upd_eq; reflexivity. }
    assert (Hcs_s6 : E9 !!! Regidx s6i = m !!! Regidx s6i).
    { rewrite /E9 upd_ne; [| reg_neq]. rewrite /E8 upd_eq; reflexivity. }
    unfold callee_saved.
    split. { exact HE9sp. }
    split. { exact Hcs_s0. }
    split. { exact Hcs_s1. }
    split. { exact Hcs_s2. }
    split. { exact Hcs_s3. }
    split. { exact Hcs_s4. }
    split. { exact Hcs_s5. }
    split. { exact Hcs_s6. }
    repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate].
  Qed.

  (* ================================================================= *)
  (*  THE LOOP (+0x78 entry): fuel induction on the processes left.  Its
      OWN top-level lemma with its OWN [CID] binder (shadowing what a
      section Context would give): [CID] rides the SAME [forall] as the
      per-iteration state ([j], [M], ...) so [induction fuel] auto-
      generalizes it, and each iteration re-anchors the caller's
      continuation to the hart THIS iteration's leaves migrated to with
      [wp_next_shift] before recursing or handing off to [piepi].       *)
  (* ================================================================= *)
  Lemma procinit_loop `{GEN : GenId} `{CID : CpuId} (m : regfile)
      (K : nat) (b : bool) (p : mword 64) (fuel : nat) :
    let sp0 := (m !!! Regidx csp_rs1 : mword 64) in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
    let ret_tgt := ret_pc (m !!! Regidx rai : mword 64) in
    let name_proc := (mword_of_int proc_str : mword 64) in
    forall (j : nat) (M : regfile),
    (10 <= K)%nat ->
    (NPROC - j <= fuel)%nat ->
    (j < NPROC)%nat ->
    M !!! Regidx s1i = proc_addr j ->
    M !!! Regidx s2i = pi_magic ->
    M !!! Regidx s3i = pi_tramp ->
    M !!! Regidx s4i = pacur NPROC ->
    M !!! Regidx s5i = (mword_of_int KernelSyms.proc : mword 64) ->
    M !!! Regidx s6i = name_proc ->
    M !!! Regidx csp_rs1 = spr ->
    (forall c : mword 5, is_cs_idx c = true ->
       c <> s0i -> c <> s1i -> c <> s2i -> c <> s3i -> c <> s4i -> c <> s5i ->
       c <> s6i -> c <> csp_rs1 ->
       M !!! Regidx c = m !!! Regidx c) ->
    sie_cap_gpr M (K - 8) b p -∗
    kernel_text -∗
    name_proc ↦ₛ□ "proc"%string -∗
    pc_is (mword_of_int (KernelSyms.procinit + 0x78)) -∗
    ([∗ list] i ∈ seq 0 j, proc_ready i) -∗
    ([∗ list] i ∈ seq j (NPROC - j), proc_seal (proc_addr i)) -∗
    (pa_stk sp0 1) ↦₈ (m !!! Regidx rai : mword 64) -∗
    (pa_stk sp0 2) ↦₈ (m !!! Regidx s0i : mword 64) -∗
    (pa_stk sp0 3) ↦₈ (m !!! Regidx s1i : mword 64) -∗
    (pa_stk sp0 4) ↦₈ (m !!! Regidx s2i : mword 64) -∗
    (pa_stk sp0 5) ↦₈ (m !!! Regidx s3i : mword 64) -∗
    (pa_stk sp0 6) ↦₈ (m !!! Regidx s4i : mword 64) -∗
    (pa_stk sp0 7) ↦₈ (m !!! Regidx s5i : mword 64) -∗
    (pa_stk sp0 8) ↦₈ (m !!! Regidx s6i : mword 64) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mr, sie_cap_gpr mr K b p -∗ pc_is ret_tgt -∗ ⌜ callee_saved m mr ⌝ -∗
        ([∗ list] i ∈ seq 0 NPROC, proc_ready i) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 spr ret_tgt name_proc.
    revert CID.
    induction fuel as [|fuel IHf];
      intros CID j M HK Hlen Hj HMs1 HMs2 HMs3 HMs4 HMs5 HMs6 HMsp HMcs.
    { exfalso. lia. }
    iIntros "Hcg #Htext #Hstr_proc Hpc Hdone Hrest Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hc7 Hc8 Hpost".
    assert (Hj64 : (j < 64)%nat) by (unfold NPROC in Hj; lia).
    (* peel the head process off the remaining list *)
    assert (Hsplit : (NPROC - j)%nat = S (NPROC - S j)) by lia.
    iEval (rewrite Hsplit) in "Hrest".
    iEval (cbn [seq]) in "Hrest".
    iDestruct "Hrest" as "[Hp0 Hrest]".
    iDestruct "Hp0" as (vst vks) "(Hlk & Hst & Hks & Hdorm)".
    iDestruct "Hlk" as (vlock vname vcpu) "(Hlkw & Hlkn & Hlkc)".
    iPoseProof (pii_78 with "Htext") as "Hi78".
    iPoseProof (pii_7a with "Htext") as "Hi7a".
    iPoseProof (pii_7c with "Htext") as "Hi7c".
    iPoseProof (pii_80 with "Htext") as "Hi80".
    iPoseProof (pii_84 with "Htext") as "Hi84".
    iPoseProof (pii_88 with "Htext") as "Hi88".
    iPoseProof (pii_8a with "Htext") as "Hi8a".
    iPoseProof (pii_8e with "Htext") as "Hi8e".
    iPoseProof (pii_90 with "Htext") as "Hi90".
    iPoseProof (pii_92 with "Htext") as "Hi92".
    iPoseProof (pii_94 with "Htext") as "Hi94".
    iPoseProof (pii_98 with "Htext") as "Hi98".
    iPoseProof (pii_9a with "Htext") as "Hi9a".
    iPoseProof (pii_9e with "Htext") as "Hi9e".
    (* +0x78 c.mv a1,s6 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.procinit + 0x78)) a1i s6i
              M (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi78 [-]").
    iIntros (CID51 Hs51) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (M1 := <[Regidx a1i := regval_into_reg (add_vec zero_reg (M !!! Regidx s6i))]> M).
    assert (HM1a1 : M1 !!! Regidx a1i = name_proc).
    { rewrite /M1 upd_eq. rewrite HMs6. apply add_vec_zero_l. }
    assert (Hp7a : add_vec_int (mword_of_int (KernelSyms.procinit + 0x78) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0x7a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp7a) in "Hpc".
    (* +0x7a c.mv a0,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.procinit + 0x7a)) a0i s1i
              M1 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi7a [-]").
    iIntros (CID52 Hs52) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (M2 := <[Regidx a0i := regval_into_reg (add_vec zero_reg (M1 !!! Regidx s1i))]> M1).
    assert (HM1s1 : M1 !!! Regidx s1i = proc_addr j)
      by (rewrite /M1 upd_ne; [exact HMs1 | reg_neq]).
    assert (HM2a0 : M2 !!! Regidx a0i = proc_addr j).
    { rewrite /M2 upd_eq. rewrite HM1s1. apply add_vec_zero_l. }
    assert (HM2a1 : M2 !!! Regidx a1i = name_proc)
      by (rewrite /M2 upd_ne; [exact HM1a1 | reg_neq]).
    assert (Hp7c : add_vec_int (mword_of_int (KernelSyms.procinit + 0x7a) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0x7c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp7c) in "Hpc".
    (* +0x7c jal ra,initlock *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.procinit + 0x7c)) rai (mword_of_int 0x1ff2f0 : mword 21)
              M2 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi7c [-]").
    iIntros (CID53 Hs53) "Hcg Hpc".
    set (M3 := <[Regidx rai := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.procinit + 0x7c) : mword 64) 4)]> M2).
    assert (Htgt3 : add_vec (mword_of_int (KernelSyms.procinit + 0x7c) : mword 64) (sign_extend' 64 (mword_of_int 0x1ff2f0 : mword 21)) = mword_of_int KernelSyms.initlock)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt3) in "Hpc".
    assert (HM3a0 : M3 !!! Regidx a0i = proc_addr j) by (rewrite /M3 upd_ne; [exact HM2a0 | reg_neq]).
    assert (HM3a1 : M3 !!! Regidx a1i = name_proc) by (rewrite /M3 upd_ne; [exact HM2a1 | reg_neq]).
    assert (HM3s1 : M3 !!! Regidx s1i = proc_addr j).
    { rewrite /M3 upd_ne; [| reg_neq]. rewrite /M2 upd_ne; [exact HM1s1 | reg_neq]. }
    assert (HM3s2 : M3 !!! Regidx s2i = pi_magic).
    { rewrite /M3 upd_ne; [| reg_neq]. rewrite /M2 upd_ne; [| reg_neq].
      rewrite /M1 upd_ne; [exact HMs2 | reg_neq]. }
    assert (HM3s3 : M3 !!! Regidx s3i = pi_tramp).
    { rewrite /M3 upd_ne; [| reg_neq]. rewrite /M2 upd_ne; [| reg_neq].
      rewrite /M1 upd_ne; [exact HMs3 | reg_neq]. }
    assert (HM3s4 : M3 !!! Regidx s4i = pacur NPROC).
    { rewrite /M3 upd_ne; [| reg_neq]. rewrite /M2 upd_ne; [| reg_neq].
      rewrite /M1 upd_ne; [exact HMs4 | reg_neq]. }
    assert (HM3s5 : M3 !!! Regidx s5i = (mword_of_int KernelSyms.proc : mword 64)).
    { rewrite /M3 upd_ne; [| reg_neq]. rewrite /M2 upd_ne; [| reg_neq].
      rewrite /M1 upd_ne; [exact HMs5 | reg_neq]. }
    assert (HM3s6 : M3 !!! Regidx s6i = name_proc).
    { rewrite /M3 upd_ne; [| reg_neq]. rewrite /M2 upd_ne; [| reg_neq].
      rewrite /M1 upd_ne; [exact HMs6 | reg_neq]. }
    assert (HM3sp : M3 !!! Regidx csp_rs1 = spr).
    { rewrite /M3 upd_ne; [| reg_neq]. rewrite /M2 upd_ne; [| reg_neq].
      rewrite /M1 upd_ne; [exact HMsp | reg_neq]. }
    assert (HM3cs : forall c : mword 5, is_cs_idx c = true ->
              c <> s0i -> c <> s1i -> c <> s2i -> c <> s3i -> c <> s4i -> c <> s5i ->
              c <> s6i -> c <> csp_rs1 -> M3 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N8 N9 N18 N19 N20 N21 N22 Nsp.
      pose proof (is_cs_idx_true_neq rai c ltac:(vm_compute; reflexivity) Hc) as Nra.
      pose proof (is_cs_idx_true_neq a0i c ltac:(vm_compute; reflexivity) Hc) as Na0.
      pose proof (is_cs_idx_true_neq a1i c ltac:(vm_compute; reflexivity) Hc) as Na1.
      rewrite /M3 upd_ne; [| congruence]. rewrite /M2 upd_ne; [| congruence].
      rewrite /M1 upd_ne; [| congruence]. apply HMcs; assumption. }
    assert (HM3ra : M3 !!! Regidx rai = mword_of_int (KernelSyms.procinit + 0x80)).
    { rewrite /M3 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    (* ---- initlock(&p->lock, "proc") ---- *)
    iApply (Initlock.wp_initlock_sconf M3 vlock vname vcpu "proc"%string (K - 8) b p
              ltac:(lia)
              with "Hcg Htext Hpc [] [Hlkw] [Hlkn] [Hlkc]").
    { iEval (rewrite HM3a1). iExact "Hstr_proc". }
    { iEval (rewrite HM3a0). iExact "Hlkw". }
    { iEval (rewrite HM3a0). iExact "Hlkn". }
    { iEval (rewrite HM3a0). iExact "Hlkc". }
    iIntros (CID54 Hs54 mil) "Hcg Hpc %Hilcs Hlkw Hlkn Hlkc".
    iEval (rewrite HM3a0) in "Hlkw".
    iEval (rewrite HM3a0 HM3a1) in "Hlkn".
    iMod (lock_name_intro with "Hstr_proc Hlkn") as "#Hnm_p".
    iEval (rewrite HM3a0) in "Hlkc".
    iAssert (lk_fresh (proc_addr j) "proc"%string) with "[Hlkw Hlkc]" as "Hlkfresh".
    { rewrite /lk_fresh. iFrame "Hlkw Hnm_p Hlkc". }
    assert (Hpcil : ret_pc (M3 !!! Regidx rai) = mword_of_int (KernelSyms.procinit + 0x80)).
    { rewrite HM3ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcil) in "Hpc".
    pose proof Hilcs as Hilcs_full.
    assert (Hils1 : mil !!! Regidx s1i = proc_addr j)
      by (rewrite (callee_saved_lookup Hilcs_full s1i ltac:(vm_compute; reflexivity)); exact HM3s1).
    assert (Hils2 : mil !!! Regidx s2i = pi_magic)
      by (rewrite (callee_saved_lookup Hilcs_full s2i ltac:(vm_compute; reflexivity)); exact HM3s2).
    assert (Hils3 : mil !!! Regidx s3i = pi_tramp)
      by (rewrite (callee_saved_lookup Hilcs_full s3i ltac:(vm_compute; reflexivity)); exact HM3s3).
    assert (Hils4 : mil !!! Regidx s4i = pacur NPROC)
      by (rewrite (callee_saved_lookup Hilcs_full s4i ltac:(vm_compute; reflexivity)); exact HM3s4).
    assert (Hils5 : mil !!! Regidx s5i = (mword_of_int KernelSyms.proc : mword 64))
      by (rewrite (callee_saved_lookup Hilcs_full s5i ltac:(vm_compute; reflexivity)); exact HM3s5).
    assert (Hils6 : mil !!! Regidx s6i = name_proc)
      by (rewrite (callee_saved_lookup Hilcs_full s6i ltac:(vm_compute; reflexivity)); exact HM3s6).
    assert (Hilsp : mil !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hilcs_full csp_rs1 ltac:(vm_compute; reflexivity)); exact HM3sp).
    assert (Hilcs' : forall c : mword 5, is_cs_idx c = true ->
              c <> s0i -> c <> s1i -> c <> s2i -> c <> s3i -> c <> s4i -> c <> s5i ->
              c <> s6i -> c <> csp_rs1 -> mil !!! Regidx c = m !!! Regidx c).
    { intros c Hc N8 N9 N18 N19 N20 N21 N22 Nsp.
      rewrite (callee_saved_lookup Hilcs_full c Hc). apply HM3cs; assumption. }
    (* +0x80 sw zero,24(s1) -- p->state = UNUSED.  The store leaf spells its
       address [rget mil s1i]; bridge it at THIS hart before applying. *)
    assert (Hils1r : rget (CID:=CID54) mil s1i = proc_addr j) by (rgne; exact Hils1).
    iApply (wp_sw_zero_s_sconf (mword_of_int (KernelSyms.procinit + 0x80)) s1i (mword_of_int 24 : mword 12)
              mil (K - 8)%nat vst b with "Hcg Hpc Hi80 [Hst] [-]").
    { iEval (rewrite Hils1r pi_state_addr). iExact "Hst". }
    iIntros (CID55 Hs55) "Hcg Hpc Hst".
    iEval (rewrite Hils1r pi_state_addr) in "Hst".
    assert (Hp84 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x80) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0x84)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp84) in "Hpc".
    (* +0x84 sub a5,s1,s5 -- 360*j *)
    iApply (wp_sub_s_sconf (CID:=CID55) (mword_of_int (KernelSyms.procinit + 0x84)) a5i s1i s5i
              (mword_of_int (360 * Z.of_nat j))
              mil (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rgne; rewrite Hils1 Hils5; exact (pi_sub_base j Hj))
              with "Hcg Hpc Hi84 [-]").
    iIntros (CID56 Hs56) "Hcg Hpc".
    set (N1 := <[Regidx a5i := regval_into_reg (mword_of_int (360 * Z.of_nat j))]> mil).
    assert (HN1a5 : N1 !!! Regidx a5i = (mword_of_int (360 * Z.of_nat j) : mword 64))
      by (rewrite /N1 upd_eq; reflexivity).
    assert (Hp88 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x84) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0x88)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp88) in "Hpc".
    (* +0x88 srai a5,a5,3 -- 45*j *)
    iApply (wp_srai_s_sconf (mword_of_int (KernelSyms.procinit + 0x88)) a5i (mword_of_int 3 : mword 6)
              N1 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi88 [-]").
    iIntros (CID57 Hs57) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (N2 := <[Regidx a5i := regval_into_reg (shift_bits_right_arith (N1 !!! Regidx a5i) (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0))]> N1).
    assert (HN2a5 : N2 !!! Regidx a5i = (mword_of_int (45 * Z.of_nat j) : mword 64)).
    { rewrite /N2 upd_eq. rewrite HN1a5. exact (pi_srai j Hj). }
    assert (Hp8a : add_vec_int (mword_of_int (KernelSyms.procinit + 0x88) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0x8a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp8a) in "Hpc".
    (* +0x8a mul a5,a5,s2 -- j (the modular inverse of 45) *)
    assert (HN2s2 : N2 !!! Regidx s2i = pi_magic) by (rewrite /N2 upd_ne; [| reg_neq]; rewrite /N1 upd_ne; [exact Hils2 | reg_neq]).
    iApply (wp_mul_s_sconf (CID:=CID57) (mword_of_int (KernelSyms.procinit + 0x8a)) a5i a5i s2i
              (mword_of_int (Z.of_nat j))
              N2 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rgne; rewrite HN2a5 HN2s2; unfold pi_magic; exact (kstack_mul_step j Hj64))
              with "Hcg Hpc Hi8a [-]").
    iIntros (CID58 Hs58) "Hcg Hpc".
    set (N3 := <[Regidx a5i := regval_into_reg (mword_of_int (Z.of_nat j))]> N2).
    assert (HN3a5 : N3 !!! Regidx a5i = (mword_of_int (Z.of_nat j) : mword 64))
      by (rewrite /N3 upd_eq; reflexivity).
    assert (Hp8e : add_vec_int (mword_of_int (KernelSyms.procinit + 0x8a) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0x8e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp8e) in "Hpc".
    (* +0x8e slli a5,a5,13 -- 8192*j *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.procinit + 0x8e)) (Regidx a5i) a5i (mword_of_int 13 : mword 6)
              N3 (K - 8)%nat b ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi8e [-]").
    iIntros (CID59 Hs59) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (N4 := <[Regidx a5i := regval_into_reg (shift_bits_left (N3 !!! Regidx a5i) (subrange_vec_dec (mword_of_int 13 : mword 6) (Z.sub log2_xlen 1) 0))]> N3).
    assert (HN4a5 : N4 !!! Regidx a5i = (mword_of_int (8192 * Z.of_nat j) : mword 64)).
    { rewrite /N4 upd_eq. rewrite HN3a5. exact (pi_slli j Hj). }
    assert (Hp90 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x8e) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0x90)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp90) in "Hpc".
    (* +0x90 c.lui a4,0x2 -- 8192 *)
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.procinit + 0x90)) a4i (sign_extend' 20 (mword_of_int 2 : mword 6)) (mword_of_int 8192 : mword 64)
              N4 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi90 [-]").
    iIntros (CID60 Hs60) "Hcg Hpc".
    set (N5 := <[Regidx a4i := regval_into_reg (mword_of_int 8192 : mword 64)]> N4).
    assert (HN5a4 : N5 !!! Regidx a4i = (mword_of_int 8192 : mword 64)) by (rewrite /N5 upd_eq; reflexivity).
    assert (HN5a5 : N5 !!! Regidx a5i = (mword_of_int (8192 * Z.of_nat j) : mword 64))
      by (rewrite /N5 upd_ne; [exact HN4a5 | reg_neq]).
    assert (Hp92 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x90) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0x92)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp92) in "Hpc".
    (* +0x92 addw a5,a5,a4 -- 8192*(j+1) *)
    iApply (wp_addw_s_sconf (mword_of_int (KernelSyms.procinit + 0x92)) a5i a4i
              N5 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi92 [-]").
    iIntros (CID61 Hs61) "Hcg Hpc".
    iEval (rgne) in "Hcg". iEval (rgne) in "Hcg".
    set (N6 := <[Regidx a5i := regval_into_reg
        (sign_extend' 64 (add_vec (subrange_vec_dec (N5 !!! Regidx a5i) 31 0 : mword 32)
                                  (subrange_vec_dec (N5 !!! Regidx a4i) 31 0 : mword 32)))]> N5).
    assert (HN6a5 : N6 !!! Regidx a5i = (mword_of_int (8192 * (Z.of_nat j + 1)) : mword 64)).
    { rewrite /N6 upd_eq. rewrite HN5a5 HN5a4. exact (addw_step j Hj64). }
    assert (Hp94 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x92) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0x94)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp94) in "Hpc".
    (* +0x94 sub a5,s3,a5 -- KSTACK(j) *)
    assert (HN6s3 : N6 !!! Regidx s3i = pi_tramp).
    { rewrite /N6 upd_ne; [| reg_neq]. rewrite /N5 upd_ne; [| reg_neq].
      rewrite /N4 upd_ne; [| reg_neq]. rewrite /N3 upd_ne; [| reg_neq].
      rewrite /N2 upd_ne; [| reg_neq]. rewrite /N1 upd_ne; [exact Hils3 | reg_neq]. }
    iApply (wp_sub_s_sconf (CID:=CID61) (mword_of_int (KernelSyms.procinit + 0x94)) a5i s3i a5i
              (kstack_va j)
              N6 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rgne; rewrite HN6s3 HN6a5; unfold pi_tramp; exact (pi_sub_tramp j Hj))
              with "Hcg Hpc Hi94 [-]").
    iIntros (CID62 Hs62) "Hcg Hpc".
    set (N7 := <[Regidx a5i := regval_into_reg (kstack_va j)]> N6).
    assert (HN7a5 : N7 !!! Regidx a5i = kstack_va j) by (rewrite /N7 upd_eq; reflexivity).
    assert (HN7s1 : N7 !!! Regidx s1i = proc_addr j).
    { rewrite /N7 upd_ne; [| reg_neq]. rewrite /N6 upd_ne; [| reg_neq].
      rewrite /N5 upd_ne; [| reg_neq]. rewrite /N4 upd_ne; [| reg_neq].
      rewrite /N3 upd_ne; [| reg_neq]. rewrite /N2 upd_ne; [| reg_neq].
      rewrite /N1 upd_ne; [exact Hils1 | reg_neq]. }
    assert (Hp98 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x94) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0x98)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp98) in "Hpc".
    (* +0x98 c.sd a5,64(s1) -- p->kstack = KSTACK(j).  Both the address and
       the stored value are [rget]-spelled; bridge them at THIS hart. *)
    assert (HN7s1r : rget (CID:=CID62) N7 s1i = proc_addr j) by (rgne; exact HN7s1).
    assert (HN7a5r : rget (CID:=CID62) N7 a5i = kstack_va j) by (rgne; exact HN7a5).
    iApply (wp_csd_s_sconf (mword_of_int (KernelSyms.procinit + 0x98)) a5i s1i (mword_of_int 64 : mword 12)
              N7 (K - 8)%nat vks b with "Hcg Hpc Hi98 [Hks] [-]").
    { iEval (rewrite HN7s1r pi_kstack_addr). iExact "Hks". }
    iIntros (CID63 Hs63) "Hcg Hpc Hks".
    iEval (rewrite HN7s1r pi_kstack_addr HN7a5r) in "Hks".
    assert (Hp9a : add_vec_int (mword_of_int (KernelSyms.procinit + 0x98) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0x9a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp9a) in "Hpc".
    (* the freshly initialized process joins the accumulator *)
    iAssert (proc_ready j) with "[Hlkfresh Hst Hks Hdorm]" as "Hrdy".
    { rewrite /proc_ready. iFrame "Hlkfresh Hst Hks Hdorm". }
    iAssert ([∗ list] i ∈ seq 0 (S j), proc_ready i)%I with "[Hdone Hrdy]" as "Hdone".
    { rewrite seq_S. rewrite big_sepL_app. iFrame "Hdone".
      rewrite Nat.add_0_l. cbn [seq]. by iFrame "Hrdy". }
    (* +0x9a addi s1,s1,360 -- bump the cursor to process j+1 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.procinit + 0x9a)) s1i s1i (mword_of_int 0x168 : mword 12)
              N7 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi9a [-]").
    iIntros (CID64 Hs64) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (N8 := <[Regidx s1i := regval_into_reg (add_vec (N7 !!! Regidx s1i) (sign_extend' 64 (mword_of_int 0x168 : mword 12)))]> N7).
    assert (HN8s1 : N8 !!! Regidx s1i = proc_addr (S j)).
    { rewrite /N8 upd_eq. rewrite HN7s1.
      change (mword_of_int 0x168 : mword 12) with (mword_of_int proc_size : mword 12).
      apply proc_addr_succ. }
    assert (HN8s2 : N8 !!! Regidx s2i = pi_magic).
    { rewrite /N8 upd_ne; [| reg_neq]. exact HN2s2. }
    assert (HN8s3 : N8 !!! Regidx s3i = pi_tramp).
    { rewrite /N8 upd_ne; [| reg_neq]. rewrite /N7 upd_ne; [exact HN6s3 | reg_neq]. }
    assert (HN8s4 : N8 !!! Regidx s4i = pacur NPROC).
    { rewrite /N8 upd_ne; [| reg_neq]. rewrite /N7 upd_ne; [| reg_neq].
      rewrite /N6 upd_ne; [| reg_neq]. rewrite /N5 upd_ne; [| reg_neq].
      rewrite /N4 upd_ne; [| reg_neq]. rewrite /N3 upd_ne; [| reg_neq].
      rewrite /N2 upd_ne; [| reg_neq]. rewrite /N1 upd_ne; [exact Hils4 | reg_neq]. }
    assert (HN8s5 : N8 !!! Regidx s5i = (mword_of_int KernelSyms.proc : mword 64)).
    { rewrite /N8 upd_ne; [| reg_neq]. rewrite /N7 upd_ne; [| reg_neq].
      rewrite /N6 upd_ne; [| reg_neq]. rewrite /N5 upd_ne; [| reg_neq].
      rewrite /N4 upd_ne; [| reg_neq]. rewrite /N3 upd_ne; [| reg_neq].
      rewrite /N2 upd_ne; [| reg_neq]. rewrite /N1 upd_ne; [exact Hils5 | reg_neq]. }
    assert (HN8s6 : N8 !!! Regidx s6i = name_proc).
    { rewrite /N8 upd_ne; [| reg_neq]. rewrite /N7 upd_ne; [| reg_neq].
      rewrite /N6 upd_ne; [| reg_neq]. rewrite /N5 upd_ne; [| reg_neq].
      rewrite /N4 upd_ne; [| reg_neq]. rewrite /N3 upd_ne; [| reg_neq].
      rewrite /N2 upd_ne; [| reg_neq]. rewrite /N1 upd_ne; [exact Hils6 | reg_neq]. }
    assert (HN8sp : N8 !!! Regidx csp_rs1 = spr).
    { rewrite /N8 upd_ne; [| reg_neq]. rewrite /N7 upd_ne; [| reg_neq].
      rewrite /N6 upd_ne; [| reg_neq]. rewrite /N5 upd_ne; [| reg_neq].
      rewrite /N4 upd_ne; [| reg_neq]. rewrite /N3 upd_ne; [| reg_neq].
      rewrite /N2 upd_ne; [| reg_neq]. rewrite /N1 upd_ne; [exact Hilsp | reg_neq]. }
    assert (HN8cs : forall c : mword 5, is_cs_idx c = true ->
              c <> s0i -> c <> s1i -> c <> s2i -> c <> s3i -> c <> s4i -> c <> s5i ->
              c <> s6i -> c <> csp_rs1 -> N8 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N8n N9 N18 N19 N20 N21 N22 Nsp.
      pose proof (is_cs_idx_true_neq a4i c ltac:(vm_compute; reflexivity) Hc) as Na4.
      pose proof (is_cs_idx_true_neq a5i c ltac:(vm_compute; reflexivity) Hc) as Na5.
      rewrite /N8 upd_ne; [| congruence]. rewrite /N7 upd_ne; [| congruence].
      rewrite /N6 upd_ne; [| congruence]. rewrite /N5 upd_ne; [| congruence].
      rewrite /N4 upd_ne; [| congruence]. rewrite /N3 upd_ne; [| congruence].
      rewrite /N2 upd_ne; [| congruence]. rewrite /N1 upd_ne; [| congruence].
      apply Hilcs'; assumption. }
    assert (Hp9e : add_vec_int (mword_of_int (KernelSyms.procinit + 0x9a) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0x9e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp9e) in "Hpc".
    (* +0x9e bne s1,s4 -- back edge unless the cursor reached &proc[NPROC] *)
    assert (Hcmp : neq_vec (rget (CID:=CID64) N8 s1i) (rget (CID:=CID64) N8 s4i)
                   = negb (Nat.eqb (S j) NPROC)).
    { rgne. rgne. rewrite HN8s1 HN8s4. rewrite proc_addr_acur. unfold pacur.
      apply (acur_neq KernelSyms.proc proc_size (S j) NPROC
               proc_base_nonneg proc_size_pos proc_end_fits).
      lia. }
    (* [decide], NOT [Nat.eqb_spec]: destructing the reflect would abstract
       [S j =? NPROC] out of [Hcmp] too. *)
    destruct (decide (S j = NPROC)) as [Hend | Hne].
    - (* the last process: bne FALLS -> straight into the epilogue *)
      assert (Hfall : neq_vec (rget (CID:=CID64) N8 s1i) (rget (CID:=CID64) N8 s4i) = false).
      { rewrite Hcmp. rewrite (proj2 (Nat.eqb_eq (S j) NPROC) Hend). reflexivity. }
      iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.procinit + 0x9e)) (mword_of_int 8154 : mword 13) s4i s1i
                N8 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hfall
                with "Hcg Hpc Hi9e [-]").
      iIntros (CID65 Hs65) "Hcg Hpc".
      assert (Hpa2 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x9e) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0xa2)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpa2) in "Hpc".
      assert (Hnone : (NPROC - S j)%nat = 0%nat) by lia.
      iEval (rewrite Hnone) in "Hrest". iEval (cbn [seq]) in "Hrest".
      iEval (rewrite Hend) in "Hdone".
      (* re-anchor the caller's continuation to the hart this iteration's own
         leaves + initlock migrated to, THEN hand it to [piepi] -- which is
         itself [wp_next]-wrapped, so [[-]] leaves exactly that obligation. *)
      assert (Hshift : b = false \/ p = zero_reg -> (CID65 : CPU) = (CID : CPU)) by wp_next_chain.
      iDestruct (wp_next_shift Hshift with "Hpost") as "Hpost".
      iApply (piepi m N8 K b p ltac:(lia) HN8sp HN8cs
                with "Htext Hcg Hpc Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hc7 Hc8 [-]").
      iIntros (CIDg Hsg mr) "Hcg Hpc %Hcs".
      iSpecialize ("Hpost" $! CIDg with "[%]"); [wp_next_chain|].
      iApply ("Hpost" $! mr with "Hcg Hpc [//] Hdone").
    - (* more processes: bne TAKEN -> back edge to +0x78 at cursor S j *)
      assert (Htgt78 : add_vec (mword_of_int (KernelSyms.procinit + 0x9e) : mword 64) (sign_extend' 64 (mword_of_int 8154 : mword 13)) = mword_of_int (KernelSyms.procinit + 0x78))
        by (apply bv_eq; vm_compute; reflexivity).
      assert (Htaken : neq_vec (rget (CID:=CID64) N8 s1i) (rget (CID:=CID64) N8 s4i) = true).
      { rewrite Hcmp. rewrite (proj2 (Nat.eqb_neq (S j) NPROC) Hne). reflexivity. }
      iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.procinit + 0x9e)) (mword_of_int 8154 : mword 13) s4i s1i
                N8 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Htaken
                ltac:(rewrite Htgt78; vm_compute; reflexivity)
                with "Hcg Hpc Hi9e [-]").
      iNext. iIntros (CID66 Hs66) "Hcg Hpc".
      iEval (rewrite Htgt78) in "Hpc".
      (* recurse at the hart THIS iteration ended on: re-anchor [Hpost] there
         first, exactly as the exit arm does. *)
      assert (Hshift2 : b = false \/ p = zero_reg -> (CID66 : CPU) = (CID : CPU)) by wp_next_chain.
      iDestruct (wp_next_shift Hshift2 with "Hpost") as "Hpost".
      iApply (IHf CID66 (S j) N8 HK ltac:(lia) ltac:(lia)
                HN8s1 HN8s2 HN8s3 HN8s4 HN8s5 HN8s6 HN8sp HN8cs
                with "Hcg Htext Hstr_proc Hpc Hdone Hrest Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hc7 Hc8 Hpost").
  Qed.

  (* ================================================================= *)
  (*  procinit's whole-function WP.                                     *)
  (* ================================================================= *)
  Lemma wp_procinit_sconf `{GEN : GenId} `{CID : CpuId} (m : regfile) (K : nat)
      (b : bool) (p : mword 64)
    : wp_procinit_sconf_body m K b p.
  Proof.
    cbv beta delta [wp_procinit_sconf_body].
    intros pcE ret_tgt HK.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))).
    pose (name_nextpid := (mword_of_int nextpid_str : mword 64)).
    pose (name_waitlock := (mword_of_int waitlock_str : mword 64)).
    pose (name_proc := (mword_of_int proc_str : mword 64)).
    iIntros "Hcg #Htext #Hkdata Hpc Hpid Hwait Hraws Hslots Hirslots Hcont".
    (* ---- the three string literals, read out of the data image ---- *)
    assert (Hnextpid : forall j bt, cstring_bytes "nextpid"%string !! j = Some bt ->
                        KernelData.kernel_data !! (nextpid_str + Z.of_nat j)%Z = Some bt).
    { intros j bt Hj.
      do 8 (destruct j as [|j];
            [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
      vm_compute in Hj; discriminate. }
    iPoseProof (kernel_data_string nextpid_str "nextpid"%string name_nextpid eq_refl ltac:(unfold text_end, nextpid_str; lia) Hnextpid
                  with "Hkdata") as "#Hstr_nextpid".
    assert (Hwaitlock : forall j bt, cstring_bytes "wait_lock"%string !! j = Some bt ->
                         KernelData.kernel_data !! (waitlock_str + Z.of_nat j)%Z = Some bt).
    { intros j bt Hj.
      do 10 (destruct j as [|j];
             [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
      vm_compute in Hj; discriminate. }
    iPoseProof (kernel_data_string waitlock_str "wait_lock"%string name_waitlock eq_refl ltac:(unfold text_end, waitlock_str; lia) Hwaitlock
                  with "Hkdata") as "#Hstr_waitlock".
    assert (Hprocstr : forall j bt, cstring_bytes "proc"%string !! j = Some bt ->
                        KernelData.kernel_data !! (proc_str + Z.of_nat j)%Z = Some bt).
    { intros j bt Hj.
      do 5 (destruct j as [|j];
            [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
      vm_compute in Hj; discriminate. }
    iPoseProof (kernel_data_string proc_str "proc"%string name_proc eq_refl ltac:(unfold text_end, proc_str; lia) Hprocstr
                  with "Hkdata") as "#Hstr_proc".
    (* ---- route both supplies, once ---- *)
    iDestruct (proc_seal_list (seq 0 NPROC) with "Hraws [Hslots] [Hirslots]") as "Hseals".
    { rewrite length_seq. iExact "Hslots". }
    { rewrite length_seq. iExact "Hirslots". }
    (* ---- the frame geometry ---- *)
    assert (Hspr8 : spr = pa_stk sp0 8).
    { unfold spr, pa_stk, add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb7 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 7).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb8 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 8).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (pii_00 with "Htext") as "Hi00".
    iPoseProof (pii_02 with "Htext") as "Hi02".
    iPoseProof (pii_04 with "Htext") as "Hi04".
    iPoseProof (pii_06 with "Htext") as "Hi06".
    iPoseProof (pii_08 with "Htext") as "Hi08".
    iPoseProof (pii_0a with "Htext") as "Hi0a".
    iPoseProof (pii_0c with "Htext") as "Hi0c".
    iPoseProof (pii_0e with "Htext") as "Hi0e".
    iPoseProof (pii_10 with "Htext") as "Hi10".
    iPoseProof (pii_12 with "Htext") as "Hi12".
    (* ===== PROLOGUE: 8-slot frame push + save ra/s0..s6 ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))]> m).
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 60 : mword 6) m K 8 b ltac:(lia) Hspr8
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID11 Hs11) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & _)".
    iDestruct "S1" as (vra0) "Hc1". iDestruct "S2" as (vs00) "Hc2".
    iDestruct "S3" as (vs10) "Hc3". iDestruct "S4" as (vs20) "Hc4".
    iDestruct "S5" as (vs30) "Hc5". iDestruct "S6" as (vs40) "Hc6".
    iDestruct "S7" as (vs50) "Hc7". iDestruct "S8" as (vs60) "Hc8".
    assert (Hp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0x02)) by (unfold pcE; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    (* the saved values are the ORIGINAL ra/s0..s6 *)
    assert (Hra_v : R1 !!! Regidx rai = m !!! Regidx rai) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (Hs0_v : R1 !!! Regidx s0i = m !!! Regidx s0i) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (Hs1_v : R1 !!! Regidx s1i = m !!! Regidx s1i) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (Hs2_v : R1 !!! Regidx s2i = m !!! Regidx s2i) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (Hs3_v : R1 !!! Regidx s3i = m !!! Regidx s3i) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (Hs4_v : R1 !!! Regidx s4i = m !!! Regidx s4i) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (Hs5_v : R1 !!! Regidx s5i = m !!! Regidx s5i) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (Hs6_v : R1 !!! Regidx s6i = m !!! Regidx s6i) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    (* +0x02 c.sdsp ra,56(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.procinit + 0x02)) (mword_of_int 7 : mword 6) rai
              R1 (K - 8)%nat vra0 b with "Hcg Hpc Hi02 [Hc1] [-]").
    { iEval (rewrite HspR1 Hb1). iExact "Hc1". }
    iIntros (CID12 Hs12) "Hcg Hpc Hc1".
    iEval (rgne) in "Hc1". iEval (rewrite HspR1 Hb1 Hra_v) in "Hc1".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    (* +0x04 c.sdsp s0,48(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.procinit + 0x04)) (mword_of_int 6 : mword 6) s0i
              R1 (K - 8)%nat vs00 b with "Hcg Hpc Hi04 [Hc2] [-]").
    { iEval (rewrite HspR1 Hb2). iExact "Hc2". }
    iIntros (CID13 Hs13) "Hcg Hpc Hc2".
    iEval (rgne) in "Hc2". iEval (rewrite HspR1 Hb2 Hs0_v) in "Hc2".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    (* +0x06 c.sdsp s1,40(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.procinit + 0x06)) (mword_of_int 5 : mword 6) s1i
              R1 (K - 8)%nat vs10 b with "Hcg Hpc Hi06 [Hc3] [-]").
    { iEval (rewrite HspR1 Hb3). iExact "Hc3". }
    iIntros (CID14 Hs14) "Hcg Hpc Hc3".
    iEval (rgne) in "Hc3". iEval (rewrite HspR1 Hb3 Hs1_v) in "Hc3".
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    (* +0x08 c.sdsp s2,32(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.procinit + 0x08)) (mword_of_int 4 : mword 6) s2i
              R1 (K - 8)%nat vs20 b with "Hcg Hpc Hi08 [Hc4] [-]").
    { iEval (rewrite HspR1 Hb4). iExact "Hc4". }
    iIntros (CID15 Hs15) "Hcg Hpc Hc4".
    iEval (rgne) in "Hc4". iEval (rewrite HspR1 Hb4 Hs2_v) in "Hc4".
    assert (Hp0a : add_vec_int (mword_of_int (KernelSyms.procinit + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0a) in "Hpc".
    (* +0x0a c.sdsp s3,24(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.procinit + 0x0a)) (mword_of_int 3 : mword 6) s3i
              R1 (K - 8)%nat vs30 b with "Hcg Hpc Hi0a [Hc5] [-]").
    { iEval (rewrite HspR1 Hb5). iExact "Hc5". }
    iIntros (CID16 Hs16) "Hcg Hpc Hc5".
    iEval (rgne) in "Hc5". iEval (rewrite HspR1 Hb5 Hs3_v) in "Hc5".
    assert (Hp0c : add_vec_int (mword_of_int (KernelSyms.procinit + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0c) in "Hpc".
    (* +0x0c c.sdsp s4,16(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.procinit + 0x0c)) (mword_of_int 2 : mword 6) s4i
              R1 (K - 8)%nat vs40 b with "Hcg Hpc Hi0c [Hc6] [-]").
    { iEval (rewrite HspR1 Hb6). iExact "Hc6". }
    iIntros (CID17 Hs17) "Hcg Hpc Hc6".
    iEval (rgne) in "Hc6". iEval (rewrite HspR1 Hb6 Hs4_v) in "Hc6".
    assert (Hp0e : add_vec_int (mword_of_int (KernelSyms.procinit + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0e) in "Hpc".
    (* +0x0e c.sdsp s5,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.procinit + 0x0e)) (mword_of_int 1 : mword 6) s5i
              R1 (K - 8)%nat vs50 b with "Hcg Hpc Hi0e [Hc7] [-]").
    { iEval (rewrite HspR1 Hb7). iExact "Hc7". }
    iIntros (CID18 Hs18) "Hcg Hpc Hc7".
    iEval (rgne) in "Hc7". iEval (rewrite HspR1 Hb7 Hs5_v) in "Hc7".
    assert (Hp10 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    (* +0x10 c.sdsp s6,0(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.procinit + 0x10)) (mword_of_int 0 : mword 6) s6i
              R1 (K - 8)%nat vs60 b with "Hcg Hpc Hi10 [Hc8] [-]").
    { iEval (rewrite HspR1 Hb8). iExact "Hc8". }
    iIntros (CID19 Hs19) "Hcg Hpc Hc8".
    iEval (rgne) in "Hc8". iEval (rewrite HspR1 Hb8 Hs6_v) in "Hc8".
    assert (Hp12 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp12) in "Hpc".
    (* +0x12 c.addi4spn s0,sp,64 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.procinit + 0x12)) (Cregidx (mword_of_int 0)) (mword_of_int 16 : mword 8) s0i
              R1 (K - 8)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12 [-]").
    iIntros (CID20 Hs20) "Hcg Hpc".
    set (R2 := <[Regidx s0i := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))))]> R1).
    assert (Hp14 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp14) in "Hpc".
    (* ===== initlock(&pid_lock, "nextpid") : +0x14 .. +0x24 ===== *)
    iPoseProof (pii_14 with "Htext") as "Hi14".
    iPoseProof (pii_18 with "Htext") as "Hi18".
    iPoseProof (pii_1c with "Htext") as "Hi1c".
    iPoseProof (pii_20 with "Htext") as "Hi20".
    iPoseProof (pii_24 with "Htext") as "Hi24".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.procinit + 0x14)) a1i (mword_of_int 6 : mword 20)
              R2 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [-]").
    iIntros (CID21 Hs21) "Hcg Hpc".
    set (R3 := <[Regidx a1i := regval_into_reg (add_vec (mword_of_int (KernelSyms.procinit + 0x14) : mword 64) (auipc_off (mword_of_int 6 : mword 20)))]> R2).
    assert (Hp18 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x14) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp18) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.procinit + 0x18)) a1i a1i (mword_of_int 0x930 : mword 12)
              R3 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18 [-]").
    iIntros (CID22 Hs22) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R4 := <[Regidx a1i := regval_into_reg (add_vec (R3 !!! Regidx a1i) (sign_extend' 64 (mword_of_int 2352 : mword 12)))]> R3).
    assert (HR4a1 : R4 !!! Regidx a1i = name_nextpid).
    { rewrite /R4 upd_eq. rewrite /R3 upd_eq. unfold name_nextpid, nextpid_str.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hp1c : add_vec_int (mword_of_int (KernelSyms.procinit + 0x18) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1c) in "Hpc".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.procinit + 0x1c)) a0i (mword_of_int 0x11 : mword 20)
              R4 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c [-]").
    iIntros (CID23 Hs23) "Hcg Hpc".
    set (R5 := <[Regidx a0i := regval_into_reg (add_vec (mword_of_int (KernelSyms.procinit + 0x1c) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> R4).
    assert (Hp20 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x1c) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp20) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.procinit + 0x20)) a0i a0i (mword_of_int 0xb10 : mword 12)
              R5 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi20 [-]").
    iIntros (CID24 Hs24) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R6 := <[Regidx a0i := regval_into_reg (add_vec (R5 !!! Regidx a0i) (sign_extend' 64 (mword_of_int 2832 : mword 12)))]> R5).
    assert (HR6a0 : R6 !!! Regidx a0i = pid_lock_addr).
    { rewrite /R6 upd_eq. rewrite /R5 upd_eq. unfold pid_lock_addr, KernelSyms.pid_lock.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HR6a1 : R6 !!! Regidx a1i = name_nextpid).
    { rewrite /R6 upd_ne; [| reg_neq]. rewrite /R5 upd_ne; [exact HR4a1 | reg_neq]. }
    assert (HR6sp : R6 !!! Regidx csp_rs1 = spr).
    { rewrite /R6 upd_ne; [| reg_neq]. rewrite /R5 upd_ne; [| reg_neq].
      rewrite /R4 upd_ne; [| reg_neq]. rewrite /R3 upd_ne; [| reg_neq].
      rewrite /R2 upd_ne; [exact HspR1 | reg_neq]. }
    assert (Hp24 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x20) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp24) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.procinit + 0x24)) rai (mword_of_int 0x1ff348 : mword 21)
              R6 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi24 [-]").
    iIntros (CID25 Hs25) "Hcg Hpc".
    set (R7 := <[Regidx rai := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.procinit + 0x24) : mword 64) 4)]> R6).
    assert (Htgt1 : add_vec (mword_of_int (KernelSyms.procinit + 0x24) : mword 64) (sign_extend' 64 (mword_of_int 0x1ff348 : mword 21)) = mword_of_int KernelSyms.initlock)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt1) in "Hpc".
    assert (HR7a0 : R7 !!! Regidx a0i = pid_lock_addr) by (rewrite /R7 upd_ne; [exact HR6a0 | reg_neq]).
    assert (HR7a1 : R7 !!! Regidx a1i = name_nextpid) by (rewrite /R7 upd_ne; [exact HR6a1 | reg_neq]).
    assert (HR7sp : R7 !!! Regidx csp_rs1 = spr) by (rewrite /R7 upd_ne; [exact HR6sp | reg_neq]).
    assert (HR7ra : R7 !!! Regidx rai = mword_of_int (KernelSyms.procinit + 0x28)).
    { rewrite /R7 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    (* the callee-saved registers procinit has not written yet (tp, s1..s11) *)
    assert (HR7cs : forall c : mword 5, is_cs_idx c = true ->
              c <> s0i -> c <> csp_rs1 -> R7 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N8 Nsp.
      pose proof (is_cs_idx_true_neq rai c ltac:(vm_compute; reflexivity) Hc) as Nra.
      pose proof (is_cs_idx_true_neq a0i c ltac:(vm_compute; reflexivity) Hc) as Na0.
      pose proof (is_cs_idx_true_neq a1i c ltac:(vm_compute; reflexivity) Hc) as Na1.
      rewrite /R7 upd_ne; [| congruence]. rewrite /R6 upd_ne; [| congruence].
      rewrite /R5 upd_ne; [| congruence]. rewrite /R4 upd_ne; [| congruence].
      rewrite /R3 upd_ne; [| congruence]. rewrite /R2 upd_ne; [| congruence].
      rewrite /R1 upd_ne; [reflexivity | congruence]. }
    iDestruct "Hpid" as (vlk1 vnm1 vcp1) "(Hpl & Hpn & Hpc0)".
    iApply (Initlock.wp_initlock_sconf R7 vlk1 vnm1 vcp1 "nextpid"%string (K - 8) b p
              ltac:(lia)
              with "Hcg Htext Hpc [] [Hpl] [Hpn] [Hpc0]").
    { iEval (rewrite HR7a1). iExact "Hstr_nextpid". }
    { iEval (rewrite HR7a0). iExact "Hpl". }
    { iEval (rewrite HR7a0). iExact "Hpn". }
    { iEval (rewrite HR7a0). iExact "Hpc0". }
    iIntros (CID26 Hs26 mil1) "Hcg Hpc %Hil1cs Hpl Hpn Hpcpu".
    iEval (rewrite HR7a0) in "Hpl".
    iEval (rewrite HR7a0 HR7a1) in "Hpn".
    iMod (lock_name_intro with "Hstr_nextpid Hpn") as "#Hnm_pid".
    iEval (rewrite HR7a0) in "Hpcpu".
    iAssert (lk_fresh pid_lock_addr "nextpid"%string) with "[Hpl Hpcpu]" as "Hpidfresh".
    { rewrite /lk_fresh. iFrame "Hpl Hnm_pid Hpcpu". }
    assert (Hpcil1 : ret_pc (R7 !!! Regidx rai) = mword_of_int (KernelSyms.procinit + 0x28)).
    { rewrite HR7ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcil1) in "Hpc".
    pose proof Hil1cs as Hil1cs_full.
    assert (Hil1sp : mil1 !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hil1cs_full csp_rs1 ltac:(vm_compute; reflexivity)); exact HR7sp).
    assert (Hil1cs' : forall c : mword 5, is_cs_idx c = true ->
              c <> s0i -> c <> csp_rs1 -> mil1 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N8 Nsp.
      rewrite (callee_saved_lookup Hil1cs_full c Hc). apply HR7cs; assumption. }
    (* ===== initlock(&wait_lock, "wait_lock") : +0x28 .. +0x38 ===== *)
    iPoseProof (pii_28 with "Htext") as "Hi28".
    iPoseProof (pii_2c with "Htext") as "Hi2c".
    iPoseProof (pii_30 with "Htext") as "Hi30".
    iPoseProof (pii_34 with "Htext") as "Hi34".
    iPoseProof (pii_38 with "Htext") as "Hi38".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.procinit + 0x28)) a1i (mword_of_int 6 : mword 20)
              mil1 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi28 [-]").
    iIntros (CID27 Hs27) "Hcg Hpc".
    set (T1 := <[Regidx a1i := regval_into_reg (add_vec (mword_of_int (KernelSyms.procinit + 0x28) : mword 64) (auipc_off (mword_of_int 6 : mword 20)))]> mil1).
    assert (Hp2c : add_vec_int (mword_of_int (KernelSyms.procinit + 0x28) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2c) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.procinit + 0x2c)) a1i a1i (mword_of_int 0x924 : mword 12)
              T1 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2c [-]").
    iIntros (CID28 Hs28) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T2 := <[Regidx a1i := regval_into_reg (add_vec (T1 !!! Regidx a1i) (sign_extend' 64 (mword_of_int 2340 : mword 12)))]> T1).
    assert (HT2a1 : T2 !!! Regidx a1i = name_waitlock).
    { rewrite /T2 upd_eq. rewrite /T1 upd_eq. unfold name_waitlock, waitlock_str.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hp30 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x2c) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp30) in "Hpc".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.procinit + 0x30)) a0i (mword_of_int 0x11 : mword 20)
              T2 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi30 [-]").
    iIntros (CID29 Hs29) "Hcg Hpc".
    set (T3 := <[Regidx a0i := regval_into_reg (add_vec (mword_of_int (KernelSyms.procinit + 0x30) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> T2).
    assert (Hp34 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x30) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp34) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.procinit + 0x34)) a0i a0i (mword_of_int 0xb14 : mword 12)
              T3 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi34 [-]").
    iIntros (CID30 Hs30) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T4 := <[Regidx a0i := regval_into_reg (add_vec (T3 !!! Regidx a0i) (sign_extend' 64 (mword_of_int 2836 : mword 12)))]> T3).
    assert (HT4a0 : T4 !!! Regidx a0i = wait_lock_addr).
    { rewrite /T4 upd_eq. rewrite /T3 upd_eq. unfold wait_lock_addr, KernelSyms.wait_lock.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HT4a1 : T4 !!! Regidx a1i = name_waitlock).
    { rewrite /T4 upd_ne; [| reg_neq]. rewrite /T3 upd_ne; [exact HT2a1 | reg_neq]. }
    assert (HT4sp : T4 !!! Regidx csp_rs1 = spr).
    { rewrite /T4 upd_ne; [| reg_neq]. rewrite /T3 upd_ne; [| reg_neq].
      rewrite /T2 upd_ne; [| reg_neq]. rewrite /T1 upd_ne; [exact Hil1sp | reg_neq]. }
    assert (Hp38 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x34) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp38) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.procinit + 0x38)) rai (mword_of_int 0x1ff334 : mword 21)
              T4 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi38 [-]").
    iIntros (CID31 Hs31) "Hcg Hpc".
    set (T5 := <[Regidx rai := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.procinit + 0x38) : mword 64) 4)]> T4).
    assert (Htgt2 : add_vec (mword_of_int (KernelSyms.procinit + 0x38) : mword 64) (sign_extend' 64 (mword_of_int 0x1ff334 : mword 21)) = mword_of_int KernelSyms.initlock)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt2) in "Hpc".
    assert (HT5a0 : T5 !!! Regidx a0i = wait_lock_addr) by (rewrite /T5 upd_ne; [exact HT4a0 | reg_neq]).
    assert (HT5a1 : T5 !!! Regidx a1i = name_waitlock) by (rewrite /T5 upd_ne; [exact HT4a1 | reg_neq]).
    assert (HT5sp : T5 !!! Regidx csp_rs1 = spr) by (rewrite /T5 upd_ne; [exact HT4sp | reg_neq]).
    assert (HT5ra : T5 !!! Regidx rai = mword_of_int (KernelSyms.procinit + 0x3c)).
    { rewrite /T5 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HT5cs : forall c : mword 5, is_cs_idx c = true ->
              c <> s0i -> c <> csp_rs1 -> T5 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N8 Nsp.
      pose proof (is_cs_idx_true_neq rai c ltac:(vm_compute; reflexivity) Hc) as Nra.
      pose proof (is_cs_idx_true_neq a0i c ltac:(vm_compute; reflexivity) Hc) as Na0.
      pose proof (is_cs_idx_true_neq a1i c ltac:(vm_compute; reflexivity) Hc) as Na1.
      rewrite /T5 upd_ne; [| congruence]. rewrite /T4 upd_ne; [| congruence].
      rewrite /T3 upd_ne; [| congruence]. rewrite /T2 upd_ne; [| congruence].
      rewrite /T1 upd_ne; [| congruence]. apply Hil1cs'; assumption. }
    iDestruct "Hwait" as (vlk2 vnm2 vcp2) "(Hwl & Hwn & Hwc)".
    iApply (Initlock.wp_initlock_sconf T5 vlk2 vnm2 vcp2 "wait_lock"%string (K - 8) b p
              ltac:(lia)
              with "Hcg Htext Hpc [] [Hwl] [Hwn] [Hwc]").
    { iEval (rewrite HT5a1). iExact "Hstr_waitlock". }
    { iEval (rewrite HT5a0). iExact "Hwl". }
    { iEval (rewrite HT5a0). iExact "Hwn". }
    { iEval (rewrite HT5a0). iExact "Hwc". }
    iIntros (CID32 Hs32 mil2) "Hcg Hpc %Hil2cs Hwl Hwn Hwc".
    iEval (rewrite HT5a0) in "Hwl".
    iEval (rewrite HT5a0 HT5a1) in "Hwn".
    iMod (lock_name_intro with "Hstr_waitlock Hwn") as "#Hnm_wait".
    iEval (rewrite HT5a0) in "Hwc".
    iAssert (lk_fresh wait_lock_addr "wait_lock"%string) with "[Hwl Hwc]" as "Hwaitfresh".
    { rewrite /lk_fresh. iFrame "Hwl Hnm_wait Hwc". }
    assert (Hpcil2 : ret_pc (T5 !!! Regidx rai) = mword_of_int (KernelSyms.procinit + 0x3c)).
    { rewrite HT5ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcil2) in "Hpc".
    pose proof Hil2cs as Hil2cs_full.
    assert (Hil2sp : mil2 !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hil2cs_full csp_rs1 ltac:(vm_compute; reflexivity)); exact HT5sp).
    assert (Hil2cs' : forall c : mword 5, is_cs_idx c = true ->
              c <> s0i -> c <> csp_rs1 -> mil2 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N8 Nsp.
      rewrite (callee_saved_lookup Hil2cs_full c Hc). apply HT5cs; assumption. }
    (* ===== loop setup: the six hoisted constants, +0x3c .. +0x74 ===== *)
    iPoseProof (pii_3c with "Htext") as "Hi3c".
    iPoseProof (pii_40 with "Htext") as "Hi40".
    iPoseProof (pii_44 with "Htext") as "Hi44".
    iPoseProof (pii_48 with "Htext") as "Hi48".
    iPoseProof (pii_4c with "Htext") as "Hi4c".
    iPoseProof (pii_4e with "Htext") as "Hi4e".
    iPoseProof (pii_52 with "Htext") as "Hi52".
    iPoseProof (pii_56 with "Htext") as "Hi56".
    iPoseProof (pii_58 with "Htext") as "Hi58".
    iPoseProof (pii_5c with "Htext") as "Hi5c".
    iPoseProof (pii_60 with "Htext") as "Hi60".
    iPoseProof (pii_64 with "Htext") as "Hi64".
    iPoseProof (pii_66 with "Htext") as "Hi66".
    iPoseProof (pii_68 with "Htext") as "Hi68".
    iPoseProof (pii_6c with "Htext") as "Hi6c".
    iPoseProof (pii_6e with "Htext") as "Hi6e".
    iPoseProof (pii_70 with "Htext") as "Hi70".
    iPoseProof (pii_74 with "Htext") as "Hi74".
    (* +0x3c/+0x40 s1 := proc *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.procinit + 0x3c)) s1i (mword_of_int 0x11 : mword 20)
              mil2 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3c [-]").
    iIntros (CID33 Hs33) "Hcg Hpc".
    set (U1 := <[Regidx s1i := regval_into_reg (add_vec (mword_of_int (KernelSyms.procinit + 0x3c) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> mil2).
    assert (Hp40 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x3c) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp40) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.procinit + 0x40)) s1i s1i (mword_of_int 0xf20 : mword 12)
              U1 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi40 [-]").
    iIntros (CID34 Hs34) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (U2 := <[Regidx s1i := regval_into_reg (add_vec (U1 !!! Regidx s1i) (sign_extend' 64 (mword_of_int 3872 : mword 12)))]> U1).
    assert (HU2s1 : U2 !!! Regidx s1i = (mword_of_int KernelSyms.proc : mword 64)).
    { rewrite /U2 upd_eq. rewrite /U1 upd_eq. unfold KernelSyms.proc.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hp44 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x40) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp44) in "Hpc".
    (* +0x44/+0x48 s6 := &"proc" *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.procinit + 0x44)) s6i (mword_of_int 6 : mword 20)
              U2 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi44 [-]").
    iIntros (CID35 Hs35) "Hcg Hpc".
    set (U3 := <[Regidx s6i := regval_into_reg (add_vec (mword_of_int (KernelSyms.procinit + 0x44) : mword 64) (auipc_off (mword_of_int 6 : mword 20)))]> U2).
    assert (Hp48 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x44) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp48) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.procinit + 0x48)) s6i s6i (mword_of_int 0x918 : mword 12)
              U3 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi48 [-]").
    iIntros (CID36 Hs36) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (U4 := <[Regidx s6i := regval_into_reg (add_vec (U3 !!! Regidx s6i) (sign_extend' 64 (mword_of_int 2328 : mword 12)))]> U3).
    assert (HU4s6 : U4 !!! Regidx s6i = name_proc).
    { rewrite /U4 upd_eq. rewrite /U3 upd_eq. unfold name_proc, proc_str.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HU4s1 : U4 !!! Regidx s1i = (mword_of_int KernelSyms.proc : mword 64)).
    { rewrite /U4 upd_ne; [| reg_neq]. rewrite /U3 upd_ne; [exact HU2s1 | reg_neq]. }
    assert (Hp4c : add_vec_int (mword_of_int (KernelSyms.procinit + 0x48) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp4c) in "Hpc".
    (* +0x4c c.mv s5,s1 -- keep the base for [p - proc] *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.procinit + 0x4c)) s5i s1i
              U4 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4c [-]").
    iIntros (CID37 Hs37) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (U5 := <[Regidx s5i := regval_into_reg (add_vec zero_reg (U4 !!! Regidx s1i))]> U4).
    assert (HU5s5 : U5 !!! Regidx s5i = (mword_of_int KernelSyms.proc : mword 64)).
    { rewrite /U5 upd_eq. rewrite HU4s1. apply add_vec_zero_l. }
    assert (Hp4e : add_vec_int (mword_of_int (KernelSyms.procinit + 0x4c) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp4e) in "Hpc".
    (* +0x4e .. +0x66 : s2 := 0x4fa4fa4fa4fa4fa5 (via a5) *)
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.procinit + 0x4e)) a5i (mword_of_int 165 : mword 20) (luival (mword_of_int 165 : mword 20))
              U5 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity)
              with "Hcg Hpc Hi4e [-]").
    iIntros (CID38 Hs38) "Hcg Hpc".
    set (U6 := <[Regidx a5i := regval_into_reg (luival (mword_of_int 165 : mword 20))]> U5).
    assert (Hp52 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x4e) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp52) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.procinit + 0x52)) a5i a5i (mword_of_int 0xfa5 : mword 12)
              U6 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi52 [-]").
    iIntros (CID39 Hs39) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (U7 := <[Regidx a5i := regval_into_reg (add_vec (U6 !!! Regidx a5i) (sign_extend' 64 (mword_of_int 0xfa5 : mword 12)))]> U6).
    assert (Hp56 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x52) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp56) in "Hpc".
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.procinit + 0x56)) (Regidx a5i) a5i (mword_of_int 12 : mword 6)
              U7 (K - 8)%nat b ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi56 [-]").
    iIntros (CID40 Hs40) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (U8 := <[Regidx a5i := regval_into_reg (shift_bits_left (U7 !!! Regidx a5i) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> U7).
    assert (Hp58 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x56) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp58) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.procinit + 0x58)) a5i a5i (mword_of_int 0xfa5 : mword 12)
              U8 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi58 [-]").
    iIntros (CID41 Hs41) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (U9 := <[Regidx a5i := regval_into_reg (add_vec (U8 !!! Regidx a5i) (sign_extend' 64 (mword_of_int 0xfa5 : mword 12)))]> U8).
    assert (Hp5c : add_vec_int (mword_of_int (KernelSyms.procinit + 0x58) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5c) in "Hpc".
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.procinit + 0x5c)) s2i (mword_of_int 0x4fa50 : mword 20) (luival (mword_of_int 0x4fa50 : mword 20))
              U9 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity)
              with "Hcg Hpc Hi5c [-]").
    iIntros (CID42 Hs42) "Hcg Hpc".
    set (U10 := <[Regidx s2i := regval_into_reg (luival (mword_of_int 0x4fa50 : mword 20))]> U9).
    assert (Hp60 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x5c) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp60) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.procinit + 0x60)) s2i s2i (mword_of_int 0xa4f : mword 12)
              U10 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi60 [-]").
    iIntros (CID43 Hs43) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (U11 := <[Regidx s2i := regval_into_reg (add_vec (U10 !!! Regidx s2i) (sign_extend' 64 (mword_of_int 0xa4f : mword 12)))]> U10).
    assert (Hp64 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x60) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0x64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp64) in "Hpc".
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.procinit + 0x64)) (Regidx s2i) s2i (mword_of_int 32 : mword 6)
              U11 (K - 8)%nat b ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi64 [-]").
    iIntros (CID44 Hs44) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (U12 := <[Regidx s2i := regval_into_reg (shift_bits_left (U11 !!! Regidx s2i) (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))]> U11).
    assert (Hp66 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x64) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0x66)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp66) in "Hpc".
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.procinit + 0x66)) s2i a5i
              U12 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi66 [-]").
    iIntros (CID45 Hs45) "Hcg Hpc".
    iEval (rgne) in "Hcg". iEval (rgne) in "Hcg".
    set (U13 := <[Regidx s2i := regval_into_reg (add_vec (U12 !!! Regidx s2i) (U12 !!! Regidx a5i))]> U12).
    assert (HU13s2 : U13 !!! Regidx s2i = pi_magic).
    { rewrite /U13 upd_eq. unfold pi_magic. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp68 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x66) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0x68)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp68) in "Hpc".
    (* +0x68 .. +0x6e : s3 := TRAMPOLINE *)
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.procinit + 0x68)) s3i (mword_of_int 0x4000 : mword 20) (luival (mword_of_int 0x4000 : mword 20))
              U13 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity)
              with "Hcg Hpc Hi68 [-]").
    iIntros (CID46 Hs46) "Hcg Hpc".
    set (U14 := <[Regidx s3i := regval_into_reg (luival (mword_of_int 0x4000 : mword 20))]> U13).
    assert (Hp6c : add_vec_int (mword_of_int (KernelSyms.procinit + 0x68) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0x6c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6c) in "Hpc".
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.procinit + 0x6c)) s3i (mword_of_int 63 : mword 6)
              U14 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6c [-]").
    iIntros (CID47 Hs47) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (U15 := <[Regidx s3i := regval_into_reg (add_vec (U14 !!! Regidx s3i) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> U14).
    assert (Hp6e : add_vec_int (mword_of_int (KernelSyms.procinit + 0x6c) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0x6e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6e) in "Hpc".
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.procinit + 0x6e)) (Regidx s3i) s3i (mword_of_int 12 : mword 6)
              U15 (K - 8)%nat b ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6e [-]").
    iIntros (CID48 Hs48) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (U16 := <[Regidx s3i := regval_into_reg (shift_bits_left (U15 !!! Regidx s3i) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> U15).
    assert (HU16s3 : U16 !!! Regidx s3i = pi_tramp).
    { rewrite /U16 upd_eq. unfold pi_tramp. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp70 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x6e) : mword 64) 2 = mword_of_int (KernelSyms.procinit + 0x70)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp70) in "Hpc".
    (* +0x70/+0x74 : s4 := &proc[NPROC] (the linker put it at tickslock) *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.procinit + 0x70)) s4i (mword_of_int 0x17 : mword 20)
              U16 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi70 [-]").
    iIntros (CID49 Hs49) "Hcg Hpc".
    set (U17 := <[Regidx s4i := regval_into_reg (add_vec (mword_of_int (KernelSyms.procinit + 0x70) : mword 64) (auipc_off (mword_of_int 0x17 : mword 20)))]> U16).
    assert (Hp74 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x70) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0x74)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp74) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.procinit + 0x74)) s4i s4i (mword_of_int 0x8ec : mword 12)
              U17 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi74 [-]").
    iIntros (CID50 Hs50) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (U18 := <[Regidx s4i := regval_into_reg (add_vec (U17 !!! Regidx s4i) (sign_extend' 64 (mword_of_int 2284 : mword 12)))]> U17).
    assert (HU18s4 : U18 !!! Regidx s4i = pacur NPROC).
    { rewrite /U18 upd_eq. rewrite /U17 upd_eq. rewrite proc_end_is_tickslock.
      unfold KernelSyms.tickslock. apply bv_eq; vm_compute; reflexivity. }
    (* ---- the loop-entry register facts ----
       Each constant was established at the layer that wrote it; here it is
       carried up through the [upd_ne] layers above.  [peel_reg_step] cannot
       do this for a WRITTEN register (it stops at the [upd_eq]), so the
       chains are spelled out -- one line per instruction that wrote a
       different register. *)
    assert (HU2s1p : U2 !!! Regidx s1i = proc_addr 0).
    { rewrite HU2s1. unfold proc_addr, proc_base, proc_size.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HU18s2 : U18 !!! Regidx s2i = pi_magic).
    { rewrite /U18 upd_ne; [| reg_neq]. rewrite /U17 upd_ne; [| reg_neq].
      rewrite /U16 upd_ne; [| reg_neq]. rewrite /U15 upd_ne; [| reg_neq].
      rewrite /U14 upd_ne; [| reg_neq]. exact HU13s2. }
    assert (HU18s3 : U18 !!! Regidx s3i = pi_tramp).
    { rewrite /U18 upd_ne; [| reg_neq]. rewrite /U17 upd_ne; [| reg_neq].
      exact HU16s3. }
    assert (HU18s5 : U18 !!! Regidx s5i = (mword_of_int KernelSyms.proc : mword 64)).
    { rewrite /U18 upd_ne; [| reg_neq]. rewrite /U17 upd_ne; [| reg_neq].
      rewrite /U16 upd_ne; [| reg_neq]. rewrite /U15 upd_ne; [| reg_neq].
      rewrite /U14 upd_ne; [| reg_neq]. rewrite /U13 upd_ne; [| reg_neq].
      rewrite /U12 upd_ne; [| reg_neq]. rewrite /U11 upd_ne; [| reg_neq].
      rewrite /U10 upd_ne; [| reg_neq]. rewrite /U9 upd_ne; [| reg_neq].
      rewrite /U8 upd_ne; [| reg_neq]. rewrite /U7 upd_ne; [| reg_neq].
      rewrite /U6 upd_ne; [| reg_neq]. exact HU5s5. }
    assert (HU18s6 : U18 !!! Regidx s6i = name_proc).
    { rewrite /U18 upd_ne; [| reg_neq]. rewrite /U17 upd_ne; [| reg_neq].
      rewrite /U16 upd_ne; [| reg_neq]. rewrite /U15 upd_ne; [| reg_neq].
      rewrite /U14 upd_ne; [| reg_neq]. rewrite /U13 upd_ne; [| reg_neq].
      rewrite /U12 upd_ne; [| reg_neq]. rewrite /U11 upd_ne; [| reg_neq].
      rewrite /U10 upd_ne; [| reg_neq]. rewrite /U9 upd_ne; [| reg_neq].
      rewrite /U8 upd_ne; [| reg_neq]. rewrite /U7 upd_ne; [| reg_neq].
      rewrite /U6 upd_ne; [| reg_neq]. rewrite /U5 upd_ne; [| reg_neq].
      exact HU4s6. }
    assert (HU18s1 : U18 !!! Regidx s1i = proc_addr 0).
    { rewrite /U18 upd_ne; [| reg_neq]. rewrite /U17 upd_ne; [| reg_neq].
      rewrite /U16 upd_ne; [| reg_neq]. rewrite /U15 upd_ne; [| reg_neq].
      rewrite /U14 upd_ne; [| reg_neq]. rewrite /U13 upd_ne; [| reg_neq].
      rewrite /U12 upd_ne; [| reg_neq]. rewrite /U11 upd_ne; [| reg_neq].
      rewrite /U10 upd_ne; [| reg_neq]. rewrite /U9 upd_ne; [| reg_neq].
      rewrite /U8 upd_ne; [| reg_neq]. rewrite /U7 upd_ne; [| reg_neq].
      rewrite /U6 upd_ne; [| reg_neq]. rewrite /U5 upd_ne; [| reg_neq].
      rewrite /U4 upd_ne; [| reg_neq]. rewrite /U3 upd_ne; [| reg_neq].
      exact HU2s1p. }
    assert (HU18sp : U18 !!! Regidx csp_rs1 = spr) by (peel_reg_step; exact Hil2sp).
    assert (HU18cs : forall c : mword 5, is_cs_idx c = true ->
              c <> s0i -> c <> s1i -> c <> s2i -> c <> s3i -> c <> s4i -> c <> s5i ->
              c <> s6i -> c <> csp_rs1 -> U18 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N8 N9 N18 N19 N20 N21 N22 Nsp.
      pose proof (is_cs_idx_true_neq a5i c ltac:(vm_compute; reflexivity) Hc) as Na5.
      rewrite /U18 upd_ne; [| congruence]. rewrite /U17 upd_ne; [| congruence].
      rewrite /U16 upd_ne; [| congruence]. rewrite /U15 upd_ne; [| congruence].
      rewrite /U14 upd_ne; [| congruence]. rewrite /U13 upd_ne; [| congruence].
      rewrite /U12 upd_ne; [| congruence]. rewrite /U11 upd_ne; [| congruence].
      rewrite /U10 upd_ne; [| congruence]. rewrite /U9 upd_ne; [| congruence].
      rewrite /U8 upd_ne; [| congruence]. rewrite /U7 upd_ne; [| congruence].
      rewrite /U6 upd_ne; [| congruence]. rewrite /U5 upd_ne; [| congruence].
      rewrite /U4 upd_ne; [| congruence]. rewrite /U3 upd_ne; [| congruence].
      rewrite /U2 upd_ne; [| congruence]. rewrite /U1 upd_ne; [| congruence].
      apply Hil2cs'; assumption. }
    assert (Hp78 : add_vec_int (mword_of_int (KernelSyms.procinit + 0x74) : mword 64) 4 = mword_of_int (KernelSyms.procinit + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp78) in "Hpc".
    (* fold the two standalone locks into the shape the loop hands on --
       [wp_next]-wrapped, since the ORIGINAL "Hcont" is generic in [b] and its
       [wp_next] stays deferred until the loop's exit arm resolves it. *)
    iAssert (wp_next (CID0 := CID) b p (fun (CID' : CpuId) =>
              ∀ mr, sie_cap_gpr mr K b p -∗ pc_is ret_tgt -∗ ⌜ callee_saved m mr ⌝ -∗
              ([∗ list] i ∈ seq 0 NPROC, proc_ready i) -∗
              WP (Loop : expr riscv_lang)))%I
      with "[Hcont Hpidfresh Hwaitfresh]" as "Hpost".
    { iIntros (CID' Hs' mr) "Hcg Hpc %Hcs Hready".
      iSpecialize ("Hcont" $! CID' with "[%]"); [exact Hs'|].
      iApply ("Hcont" $! mr with "Hcg Hpc [//] Hpidfresh Hwaitfresh Hready"). }
    (* enter the loop at cursor 0 with NPROC units of fuel, at the hart the
       loop-setup leaves migrated to; [Hpost] is still anchored at
       wp_procinit_sconf's own entry hart, so shift it there once. *)
    assert (Hshift0 : b = false \/ p = zero_reg -> (CID50 : CPU) = (CID : CPU)) by wp_next_chain.
    iDestruct (wp_next_shift Hshift0 with "Hpost") as "Hpost".
    iApply (procinit_loop m K b p NPROC 0%nat U18 HK ltac:(lia)
              ltac:(unfold NPROC; lia)
              HU18s1 HU18s2 HU18s3 HU18s4 HU18s5 HU18s6 HU18sp HU18cs
              with "Hcg Htext Hstr_proc Hpc [] [Hseals] Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hc7 Hc8 Hpost").
    { cbn [seq]. done. }
    { rewrite Nat.sub_0_r. iExact "Hseals". }
  Qed.

End ProofProcinit.

End ProcinitProof.
