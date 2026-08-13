(* ProofFreerange.v -- the whole-function WP for xv6's freerange() over the
   SIE-agnostic sconf world.  freerange(pa_start, pa_end) rounds pa_start up to
   a page boundary and calls kfree() on every full page in
   [PGROUNDUP(pa_start), pa_end).  It is the hard loop of the kinit cone: a
   BOUNDED loop over kfree, proved by ordinary Coq fuel induction on the list of
   remaining pages (no iLoeb -- the packaged leaves strip the later).

   The loop threads: [sconf]/[sie_cap]/[intr_count] (net-zero -- kfree's
   acquire/release pair restores the level), the three per-CPU scratch cells
   (returned by the strengthened [Kfree.wp_kfree_sconf]), a DEEP [stack_own] slice
   lent to kfree (kfree wants 14 below its sp), and a big-sep of [page_own] over
   the pages to be freed.

   EXPLICIT-CPUID: this function calls no acquire/release itself (kfree's own
   critical section is entirely behind SpecKfree's contract, which threads
   [cpu_own]/[b] net-zero across the call, exactly like a callee), so it is
   [b]-GENERIC start to finish and every plain instruction threads a fresh
   hart.  [Hcnt] (cpu_own) needs [cpu_own_transport] around each kfree call,
   same as the other two files.  The LOOP additionally needs the "decomposed
   proof" recipe from the porting guide: [frepi] (the shared epilogue) is
   pulled out of the section's ambient hart with its own `{CID0 : CpuId}`
   binder, and the fuel induction ("Hloop") carries the entry hart as part of
   the SAME universal as the fuel/map/page-list state, so [iInduction]
   auto-generalizes it; the back-edge recursion and both exits re-anchor the
   caller's ["Hcont"] from the OLD entry hart to the NEW one with
   [WpSconfVc.wp_next_shift] (a wp_next-shaped analogue of
   [cpu_own_transport], needed because [wp_next]'s own conditional equality
   is stated relative to a fixed entry hart).

   Neither freerange's own entry nor kfree's contract states a raw-map tp
   premise any more (SpecFreerange.v / SpecKfree.v both dropped it, unlike
   SpecRelease/SpecUvmcreate) -- so the [Htp]/tp-preservation chain the
   original proof threaded through the loop invariant and into the kfree call
   is gone outright, along with the tp conjunct in every callee_saved
   proof. *)
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
Require Import IntrDefs.
Require Import WpNext.
Require Import StackOwn CalleeSaved.
Require Import KernelText.
Require Import WpLock.
Require Import KallocInv.
Require Import CpuOwn.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpSconfVc.
Require Import SpecKfree.
Require Import CodeFreerange.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecFreerange.
Require Import SpecPanic.
Local Open Scope Z_scope.
Import Defs.


Module FreerangeProof (Kfree : KFREE) : FREERANGE.

Section ProofFreerange.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ================================================================= *)
  (*  §2  The page-run predicate and freerange's whole-function WP.     *)
  (* ================================================================= *)


  Lemma avail_inc_n_comm (on : option nat) (k : nat) :
    avail_inc_n (avail_inc on) k = avail_inc (avail_inc_n on k).
  Proof. induction k as [|k IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

  Lemma avail_inc_n_Some0 (k : nat) : avail_inc_n (Some 0%nat) k = Some k.
  Proof. induction k as [|k IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

  (* [prun pa_end s1 ps]: [ps] is exactly the list of full pages to free when the
     loop register [s1] currently holds [p + PGSIZE].  The list terminates the
     moment [s1 >u pa_end] (no full page left); each entry is [s1 - PGSIZE],
     page-valid, and the residual [prun] threads [s1 += PGSIZE]. *)

  (* [>=u] is the negation of [<u]: ties the bgeu back-edge to the bltu entry. *)
  Lemma zge_negb_zlt (a b : mword 64) : zopz0zKzJ_u a b = negb (zopz0zI_u a b).
  Proof.
    unfold zopz0zKzJ_u, zopz0zI_u.
    rewrite Z.geb_leb. rewrite Z.ltb_antisym. rewrite negb_involutive. reflexivity.
  Qed.

  (* freerange's epilogue (0x3e..0x46): restore ra/s0/s1, frame trade back (move_up
     6), ret.  Factored as a top-level lemma so its call sites can hand it
     ["Hcont"] re-anchored at whichever hart they reached (a DECOMPOSED
     helper: its own fresh `{CID0 : CpuId}` binder, per the porting guide,
     rather than the section's ambient one, which callers have long since
     migrated away from). *)
  Lemma frepi `{CID0 : CpuId}
      (m Me : regfile) (K ncnt : nat) (eb b : bool) (pcur : mword 64) (C : iProp Σ)
      (γl : gname) (γk : gname * gname) (onf : option nat) :
    let sp0 := m !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))) in
    let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
    (6 <= K)%nat ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    Me !!! Regidx csp_rs1 = spr ->
    (forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> csp_rs1 -> Me !!! Regidx c = m !!! Regidx c) ->
    kernel_text -∗
    sie_cap_gpr Me (K - 6) b pcur -∗
    cpu_own ncnt eb pcur C b -∗
    pc_is (mword_of_int (KernelSyms.freerange + 0x3e)) -∗
    (pa_stk sp0 1) ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) -∗
    (pa_stk sp0 2) ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5) : mword 64) -∗
    (pa_stk sp0 3) ↦₈ (m !!! Regidx (mword_of_int 9 : mword 5) : mword 64) -∗
    (∃ v : mword 64, (pa_stk sp0 4) ↦₈ v) -∗
    (∃ v : mword 64, (pa_stk sp0 5) ↦₈ v) -∗
    (∃ v : mword 64, (pa_stk sp0 6) ↦₈ v) -∗
    panic_wp_any -∗
    kalloc_avail γk onf -∗
    wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
      ∀ mr,
      sie_cap_gpr mr K b pcur -∗
      cpu_own ncnt eb pcur C b -∗
      pc_is ret_tgt -∗ ⌜ callee_saved m mr ⌝ -∗
      kalloc_avail γk onf -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 spr ret_tgt HK6 Hretm HMesp HMecs.
    assert (Hspr6 : spr = pa_stk sp0 6).
    { unfold spr, pa_stk, add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iIntros "#Htext Hcg Hcnt Hpc Hs1c Hs2c Hs3c Hf4 Hf5 Hf6 #Hqcpu Havail Hcont".
    iPoseProof (fri_3e with "Htext") as "Hi3e".
    iPoseProof (fri_40 with "Htext") as "Hi40".
    iPoseProof (fri_42 with "Htext") as "Hi42".
    iPoseProof (fri_44 with "Htext") as "Hi44".
    iPoseProof (fri_46 with "Htext") as "Hi46".
    (* +0x3e c.ldsp ra,40(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.freerange + 0x3e)) (mword_of_int 5 : mword 6) (mword_of_int 1 : mword 5)
              Me (K - 6)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3e [Hs1c]").
    { iEval (rewrite HMesp Hb1). iExact "Hs1c". }
    iIntros (CIDf1 Hsf1) "Hcg Hpc Hs1c".
    iEval (rewrite HMesp Hb1) in "Hs1c".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> Me).
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spr) by (rewrite /E1 upd_ne; [exact HMesp | vm_compute; discriminate]).
    assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.freerange + 0x3e) : mword 64) 2 = mword_of_int (KernelSyms.freerange + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp40) in "Hpc".
    (* +0x40 c.ldsp s0,32(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.freerange + 0x40)) (mword_of_int 4 : mword 6) (mword_of_int 8 : mword 5)
              E1 (K - 6)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi40 [Hs2c]").
    { iEval (rewrite HE1sp Hb2). iExact "Hs2c". }
    iIntros (CIDf2 Hsf2) "Hcg Hpc Hs2c".
    iEval (rewrite HE1sp Hb2) in "Hs2c".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spr) by (rewrite /E2 upd_ne; [exact HE1sp | vm_compute; discriminate]).
    assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.freerange + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.freerange + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp42) in "Hpc".
    (* +0x42 c.ldsp s1,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.freerange + 0x42)) (mword_of_int 3 : mword 6) (mword_of_int 9 : mword 5)
              E2 (K - 6)%nat (m !!! Regidx (mword_of_int 9 : mword 5)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi42 [Hs3c]").
    { iEval (rewrite HE2sp Hb3). iExact "Hs3c". }
    iIntros (CIDf3 Hsf3) "Hcg Hpc Hs3c".
    iEval (rewrite HE2sp Hb3) in "Hs3c".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    assert (HE3sp : E3 !!! Regidx csp_rs1 = spr) by (rewrite /E3 upd_ne; [exact HE2sp | vm_compute; discriminate]).
    assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.freerange + 0x42) : mword 64) 2 = mword_of_int (KernelSyms.freerange + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp44) in "Hpc".
    (* +0x44 c.addi16sp sp,48 -- frame trade back (pop 6) *)
    iDestruct "Hf4" as (v4) "Hs4c". iDestruct "Hf5" as (v5) "Hs5c". iDestruct "Hf6" as (v6) "Hs6c".
    set (E4 := <[Regidx csp_rs1 := regval_into_reg (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E3).
    assert (HE4sp : E4 !!! Regidx csp_rs1 = sp0).
    { rewrite /E4 upd_eq. rewrite HE3sp.
      unfold spr. rewrite pa_stk_off2.
      replace (mword_of_int (bv_wrap 64 (uint (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)) : mword 64) + uint (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)) : mword 64))) : mword 64) with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      change (add_vec sp0 (mword_of_int 0)) with (add_vec_int sp0 0). apply avi0. }
    assert (Hup : E3 !!! Regidx csp_rs1 = pa_stk (E4 !!! Regidx csp_rs1) 6).
    { rewrite HE3sp HE4sp Hspr6. reflexivity. }
    assert (Hwv : add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0).
    { rewrite -HE4sp /E4 upd_eq. reflexivity. }
    assert (Hpop : E3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6).
    { rewrite Hwv Hup HE4sp. reflexivity. }
    iAssert (stack_own sp0 6) with "[Hs1c Hs2c Hs3c Hs4c Hs5c Hs6c]" as "Hframe6".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hs1c"; [iExists _; iExact "Hs1c"|].
      iSplitL "Hs2c"; [iExists _; iExact "Hs2c"|].
      iSplitL "Hs3c"; [iExists _; iExact "Hs3c"|].
      iSplitL "Hs4c"; [iExists _; iExact "Hs4c"|].
      iSplitL "Hs5c"; [iExists _; iExact "Hs5c"|].
      iSplitL "Hs6c"; [iExists _; iExact "Hs6c"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe6".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.freerange + 0x44)) (mword_of_int 3 : mword 6) E3 (K - 6)%nat 6 b Hpop
              with "Hcg Hpc Hi44 Hframe6").
    iIntros (CIDf4 Hsf4) "Hcg Hpc".
    assert (Hnk : ((K - 6) + 6)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E3) with E4.
    assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.freerange + 0x44) : mword 64) 2 = mword_of_int (KernelSyms.freerange + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp46) in "Hpc".
    (* +0x46 c.ret *)
    assert (HE4ra : E4 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_eq; reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.freerange + 0x46)) (mword_of_int 1 : mword 5) E4 K b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi46").
    iIntros (CIDf5 Hsf5) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (E4 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
      by (rewrite HE4ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* [Hcnt] entered at CID0 and every one of the five plain epilogue
       instructions has moved to a fresh hart, so [Hcont] (specialized at the
       last one, [CIDf5]) wants it there. *)
    iDestruct (cpu_own_transport CID0 CIDf5 ncnt eb pcur C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CIDf5 with "[]"); [ iPureIntro; wp_next_chain | ].
    iApply ("Hcont" $! E4 with "Hcg Hcnt Hpc [%] Havail").
    (* callee_saved m E4 *)
    assert (Hthread : forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 1 -> c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> csp_rs1 -> E4 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N1 N8 N9 Nsp.
      rewrite /E4 upd_ne; [| congruence].
      rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      apply HMecs; assumption. }
    unfold callee_saved.
    split. { rewrite HE4sp. reflexivity. }
    split. { rewrite /E4 upd_ne; [| vm_compute; discriminate].
             rewrite /E3 upd_ne; [| vm_compute; discriminate].
             rewrite /E2 upd_eq; reflexivity. }
    split. { rewrite /E4 upd_ne; [| vm_compute; discriminate].
             rewrite /E3 upd_eq; reflexivity. }
    repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate].
  Qed.

  Lemma wp_freerange_sconf
      (γl : gname) (γk : gname * gname) (lk fl : mword 64)
      (m : regfile)
      (ps : list (mword 64)) (K ncnt : nat) (eb : bool) (pcur : mword 64) (C : iProp Σ) (b : bool)
    : wp_freerange_sconf_body γl γk lk fl m ps K ncnt eb pcur C b.
  Proof.
    cbv beta delta [wp_freerange_sconf_body].
    intros pcE pa_start pa_end ret_tgt s1entry
      HK Hncnt Hlk Hfl Hprun.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))).
    iIntros "Hcg Hcnt #Htext Hpc #Hkmem Hpages #Hqcpu Havail Hcont".
    assert (Hspr6 : spr = pa_stk sp0 6).
    { unfold spr, pa_stk, add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* the six frame-slot address bridges (spr-relative store offset -> pa_stk sp0 k) *)
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (fri_00 with "Htext") as "Hi00".
    iPoseProof (fri_02 with "Htext") as "Hi02".
    iPoseProof (fri_04 with "Htext") as "Hi04".
    iPoseProof (fri_06 with "Htext") as "Hi06".
    iPoseProof (fri_08 with "Htext") as "Hi08".
    iPoseProof (fri_0a with "Htext") as "Hi0a".
    iPoseProof (fri_0c with "Htext") as "Hi0c".
    iPoseProof (fri_10 with "Htext") as "Hi10".
    iPoseProof (fri_14 with "Htext") as "Hi14".
    iPoseProof (fri_16 with "Htext") as "Hi16".
    iPoseProof (fri_18 with "Htext") as "Hi18".
    iPoseProof (fri_1a with "Htext") as "Hi1a".
    iPoseProof (fri_1e with "Htext") as "Hi1e".
    iPoseProof (fri_20 with "Htext") as "Hi20".
    iPoseProof (fri_22 with "Htext") as "Hi22".
    iPoseProof (fri_24 with "Htext") as "Hi24".
    iPoseProof (fri_26 with "Htext") as "Hi26".
    iPoseProof (fri_28 with "Htext") as "Hi28".
    (* ===== PROLOGUE (generic b): 6-slot frame push + save ra/s0/s1 ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    assert (Hpush : add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))) = pa_stk sp0 6)
      by (exact Hspr6).
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 61 : mword 6) m K 6 b ltac:(lia) Hpush
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & _)".
    iDestruct "S1" as (vra0) "Hra". iDestruct "S2" as (vs00) "Hs0".
    iDestruct "S3" as (vs10) "Hs1". iDestruct "S4" as (vs20) "Hslot4".
    iDestruct "S5" as (vs30) "Hslot5". iDestruct "S6" as (vs40) "Hslot6".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.freerange + 0x02)) by (unfold pcE; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,40(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.freerange + 0x02)) (mword_of_int 5 : mword 6) (mword_of_int 1 : mword 5)
              R1 (K - 6)%nat vra0 b with "Hcg Hpc Hi02 [Hra]").
    { iEval (rewrite HspR1 Hb1). iExact "Hra". }
    iIntros (CID2 Hs2) "Hcg Hpc Hra".
    iEval (rewrite HspR1 Hb1) in "Hra".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.freerange + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.freerange + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,32(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.freerange + 0x04)) (mword_of_int 4 : mword 6) (mword_of_int 8 : mword 5)
              R1 (K - 6)%nat vs00 b with "Hcg Hpc Hi04 [Hs0]").
    { iEval (rewrite HspR1 Hb2). iExact "Hs0". }
    iIntros (CID3 Hs3) "Hcg Hpc Hs0".
    iEval (rewrite HspR1 Hb2) in "Hs0".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.freerange + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.freerange + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,24(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.freerange + 0x06)) (mword_of_int 3 : mword 6) (mword_of_int 9 : mword 5)
              R1 (K - 6)%nat vs10 b with "Hcg Hpc Hi06 [Hs1]").
    { iEval (rewrite HspR1 Hb3). iExact "Hs1". }
    iIntros (CID4 Hs4) "Hcg Hpc Hs1".
    iEval (rewrite HspR1 Hb3) in "Hs1".
    (* the saved values are the ORIGINAL ra/s0/s1 (unchanged before these stores) *)
    assert (Hra_v : R1 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0_v : R1 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1_v : R1 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rgne; rewrite Hra_v) in "Hra". iEval (rgne; rewrite Hs0_v) in "Hs0". iEval (rgne; rewrite Hs1_v) in "Hs1".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.freerange + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.freerange + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.addi4spn s0,sp,48 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.freerange + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 12 : mword 8) (mword_of_int 8 : mword 5)
              R1 (K - 6)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> R1).
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.freerange + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.freerange + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* ===== PGROUNDUP (0x0a..0x18): compute s1entry, a5=PGSIZE, a4=negmask ===== *)
    (* +0x0a c.lui a5,0x1 : a5 := 0x1000 *)
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.freerange + 0x0a)) (mword_of_int 15 : mword 5) (sign_extend' 20 (mword_of_int 1 : mword 6)) PGSIZEv
              R2 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(unfold PGSIZEv; vm_compute; reflexivity)
              with "Hcg Hpc Hi0a").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (R3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg PGSIZEv]> R2).
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.freerange + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.freerange + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    assert (HR3a5 : R3 !!! Regidx (mword_of_int 15 : mword 5) = PGSIZEv) by (rewrite /R3 upd_eq; reflexivity).
    (* +0x0c addi a4,a5,-1 : a4 := 0xfff *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.freerange + 0x0c)) (mword_of_int 14 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 4095 : mword 12)
              R3 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c").
    iIntros (CID7 Hs7) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R4 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (R3 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 4095 : mword 12)))]> R3).
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.freerange + 0x0c) : mword 64) 4 = mword_of_int (KernelSyms.freerange + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    assert (HR4a0 : R4 !!! Regidx (mword_of_int 10 : mword 5) = pa_start).
    { rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HR4a4 : R4 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 4095).
    { rewrite /R4 upd_eq. rewrite HR3a5. unfold PGSIZEv. apply bv_eq; vm_compute; reflexivity. }
    (* +0x10 add s1,a0,a4 : s1 := pa_start + 0xfff *)
    iApply (wp_add_s_sconf (mword_of_int (KernelSyms.freerange + 0x10)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 14 : mword 5)
              (add_vec pa_start (mword_of_int 4095 : mword 64)) R4 (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rgne; rewrite HR4a0 HR4a4; reflexivity)
              with "Hcg Hpc Hi10").
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (R5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec pa_start (mword_of_int 4095 : mword 64))]> R4).
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.freerange + 0x10) : mword 64) 4 = mword_of_int (KernelSyms.freerange + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 c.lui a4,0xfffff : a4 := negmask *)
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.freerange + 0x14)) (mword_of_int 14 : mword 5) (sign_extend' 20 (mword_of_int 63 : mword 6)) negPGSIZEv
              R5 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(unfold negPGSIZEv; vm_compute; reflexivity)
              with "Hcg Hpc Hi14").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (R6 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg negPGSIZEv]> R5).
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.freerange + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.freerange + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    assert (HR6s1 : R6 !!! Regidx (mword_of_int 9 : mword 5) = add_vec pa_start (mword_of_int 4095 : mword 64)).
    { rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_eq; reflexivity. }
    assert (HR6a4 : R6 !!! Regidx (mword_of_int 14 : mword 5) = negPGSIZEv) by (rewrite /R6 upd_eq; reflexivity).
    (* +0x16 c.and s1,s1,a4 : s1 := PGROUNDUP(pa_start) *)
    iApply (wp_cand_s_sconf (mword_of_int (KernelSyms.freerange + 0x16)) (mword_of_int 9 : mword 5) (mword_of_int 14 : mword 5)
              R6 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16").
    iIntros (CID10 Hs10) "Hcg Hpc".
    iEval (rgne; rgne) in "Hcg".
    set (R7 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (and_vec (R6 !!! Regidx (mword_of_int 9 : mword 5)) (R6 !!! Regidx (mword_of_int 14 : mword 5)))]> R6).
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.freerange + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.freerange + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    assert (HR7s1 : R7 !!! Regidx (mword_of_int 9 : mword 5) = and_vec (add_vec pa_start (mword_of_int 4095 : mword 64)) negPGSIZEv).
    { rewrite /R7 upd_eq. rewrite HR6s1 HR6a4. reflexivity. }
    assert (HR7a5 : R7 !!! Regidx (mword_of_int 15 : mword 5) = PGSIZEv).
    { rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate]. exact HR3a5. }
    (* +0x18 c.add s1,s1,a5 : s1 := s1entry = PGROUNDUP(pa_start) + PGSIZE *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.freerange + 0x18)) (mword_of_int 9 : mword 5) (mword_of_int 15 : mword 5)
              R7 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18").
    iIntros (CID11 Hs11) "Hcg Hpc".
    iEval (rgne; rgne) in "Hcg".
    set (R8 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec (R7 !!! Regidx (mword_of_int 9 : mword 5)) (R7 !!! Regidx (mword_of_int 15 : mword 5)))]> R7).
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.freerange + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.freerange + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    assert (HR8s1 : R8 !!! Regidx (mword_of_int 9 : mword 5) = s1entry).
    { rewrite /R8 upd_eq. rewrite HR7s1 HR7a5. reflexivity. }
    assert (HR8a1 : R8 !!! Regidx (mword_of_int 11 : mword 5) = pa_end).
    { rewrite /R8 upd_ne; [| vm_compute; discriminate].
      rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    (* register bookkeeping shared by both branches: sp preserved, a4/a5, s2/s3/s4 orig *)
    assert (HR8sp : R8 !!! Regidx csp_rs1 = spr).
    { rewrite /R8 upd_ne; [| vm_compute; discriminate].
      rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate]. exact HspR1. }
    (* a general "callee-saved-except-{s0,s1,sp} through R8" helper (used at the epilogue) *)
    assert (HR8cs : forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> csp_rs1 -> R8 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N8 N9 Nsp.
      pose proof (is_cs_idx_true_neq (mword_of_int 14 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N14.
      pose proof (is_cs_idx_true_neq (mword_of_int 15 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as N15.
      rewrite /R8 upd_ne; [| congruence].
      rewrite /R7 upd_ne; [| congruence].
      rewrite /R6 upd_ne; [| congruence].
      rewrite /R5 upd_ne; [| congruence].
      rewrite /R4 upd_ne; [| congruence].
      rewrite /R3 upd_ne; [| congruence].
      rewrite /R2 upd_ne; [| congruence].
      rewrite /R1 upd_ne; [reflexivity | congruence]. }
    (* the eleven plain prologue instructions have each moved to a fresh
       hart, so ["Hcont"] -- still wp_next-wrapped, entered at the section's
       ambient hart -- must be re-anchored to CID11 before either branch
       below can use it (both eventually call a helper taking a wp_next
       argument at ITS OWN entry hart). *)
    assert (Hshift11 : b = false \/ pcur = zero_reg -> (CID11 : CPU) = (CID : CPU)) by wp_next_chain.
    iDestruct (wp_next_shift Hshift11 with "Hcont") as "Hcont".
    (* ===================================================================== *)
    (* +0x1a bltu a1,s1,+0x3e : split on whether any full page fits.          *)
    (* ===================================================================== *)
    destruct ps as [| p0 rest] eqn:Hpseq.
    - (* ---- SKIP: no full page fits; bltu TAKEN straight to the epilogue ---- *)
      simpl in Hprun.
      assert (Htgt3e : add_vec (mword_of_int (KernelSyms.freerange + 0x1a) : mword 64) (sign_extend' 64 (mword_of_int 36 : mword 13)) = mword_of_int (KernelSyms.freerange + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_bltu_taken_s_sconf (mword_of_int (KernelSyms.freerange + 0x1a)) (mword_of_int 36 : mword 13) (mword_of_int 9 : mword 5) (mword_of_int 11 : mword 5)
                R8 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgne; rgne; rewrite HR8a1 HR8s1; exact Hprun)
                ltac:(rewrite Htgt3e; vm_compute; reflexivity)
                with "Hcg Hpc Hi1a").
      iNext. iIntros (CID12 Hs12) "Hcg Hpc".
      iEval (rewrite Htgt3e) in "Hpc".
      (* [Hcnt]/["Hcont"] were last anchored at CID11 (the prologue's own
         shift point); the taken branch moved one hart further, to CID12. *)
      assert (Hshift12 : b = false \/ pcur = zero_reg -> (CID12 : CPU) = (CID11 : CPU)) by wp_next_chain.
      iDestruct (wp_next_shift Hshift12 with "Hcont") as "Hcont".
      iDestruct (cpu_own_transport CID CID12 ncnt eb pcur C b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iApply (frepi (CID0 := CID12) m R8 K ncnt eb b pcur C γl γk (Some 0%nat) ltac:(lia) ltac:(apply ret_pc_aligned) HR8sp HR8cs
                with "Htext Hcg Hcnt Hpc Hra Hs0 Hs1 [Hslot4] [Hslot5] [Hslot6] Hqcpu Havail Hcont").
      { iExists vs20; iExact "Hslot4". }
      { iExists vs30; iExact "Hslot5". }
      { iExists vs40; iExact "Hslot6". }
    - (* ---- LOOP: at least one full page fits; enter the loop ---- *)
      destruct Hprun as (Hfits0 & Hp0eq & Hpv0 & Hprest0).
      (* +0x1a bltu a1,s1 : falls through into the loop setup *)
      iApply (wp_bltu_fall_s_sconf (mword_of_int (KernelSyms.freerange + 0x1a)) (mword_of_int 36 : mword 13) (mword_of_int 9 : mword 5) (mword_of_int 11 : mword 5)
                R8 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgne; rgne; rewrite HR8a1 HR8s1; exact Hfits0)
                with "Hcg Hpc Hi1a").
      iIntros (CID12 Hs12) "Hcg Hpc".
      assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.freerange + 0x1a) : mword 64) 4 = mword_of_int (KernelSyms.freerange + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1e) in "Hpc".
      (* the saved s2/s3/s4 are the ORIGINAL callee values (untouched before 0x1e) *)
      assert (HR8s2 : R8 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5)) by (apply HR8cs; vm_compute; first [reflexivity | discriminate]).
      assert (HR8s3 : R8 !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5)) by (apply HR8cs; vm_compute; first [reflexivity | discriminate]).
      assert (HR8s4 : R8 !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5)) by (apply HR8cs; vm_compute; first [reflexivity | discriminate]).
      (* +0x1e c.sdsp s2,16(sp) *)
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.freerange + 0x1e)) (mword_of_int 2 : mword 6) (mword_of_int 18 : mword 5)
                R8 (K - 6)%nat vs20 b with "Hcg Hpc Hi1e [Hslot4]").
      { iEval (rewrite HR8sp Hb4). iExact "Hslot4". }
      iIntros (CID13 Hs13) "Hcg Hpc Hslot4".
      iEval (rgne; rewrite HR8sp Hb4 HR8s2) in "Hslot4".
      assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.freerange + 0x1e) : mword 64) 2 = mword_of_int (KernelSyms.freerange + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp20) in "Hpc".
      (* +0x20 c.sdsp s3,8(sp) *)
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.freerange + 0x20)) (mword_of_int 1 : mword 6) (mword_of_int 19 : mword 5)
                R8 (K - 6)%nat vs30 b with "Hcg Hpc Hi20 [Hslot5]").
      { iEval (rewrite HR8sp Hb5). iExact "Hslot5". }
      iIntros (CID14 Hs14) "Hcg Hpc Hslot5".
      iEval (rgne; rewrite HR8sp Hb5 HR8s3) in "Hslot5".
      assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.freerange + 0x20) : mword 64) 2 = mword_of_int (KernelSyms.freerange + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp22) in "Hpc".
      (* +0x22 c.sdsp s4,0(sp) *)
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.freerange + 0x22)) (mword_of_int 0 : mword 6) (mword_of_int 20 : mword 5)
                R8 (K - 6)%nat vs40 b with "Hcg Hpc Hi22 [Hslot6]").
      { iEval (rewrite HR8sp Hb6). iExact "Hslot6". }
      iIntros (CID15 Hs15) "Hcg Hpc Hslot6".
      iEval (rgne; rewrite HR8sp Hb6 HR8s4) in "Hslot6".
      assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.freerange + 0x22) : mword 64) 2 = mword_of_int (KernelSyms.freerange + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp24) in "Hpc".
      (* +0x24 c.mv s2,a1 : s2 := pa_end *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.freerange + 0x24)) (mword_of_int 18 : mword 5) (mword_of_int 11 : mword 5)
                R8 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi24").
      iIntros (CID16 Hs16) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (R9 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec zero_reg (R8 !!! Regidx (mword_of_int 11 : mword 5)))]> R8).
      assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.freerange + 0x24) : mword 64) 2 = mword_of_int (KernelSyms.freerange + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp26) in "Hpc".
      (* +0x26 c.mv s4,a4 : s4 := negmask *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.freerange + 0x26)) (mword_of_int 20 : mword 5) (mword_of_int 14 : mword 5)
                R9 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi26").
      iIntros (CID17 Hs17) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (R10 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (add_vec zero_reg (R9 !!! Regidx (mword_of_int 14 : mword 5)))]> R9).
      assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.freerange + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.freerange + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp28) in "Hpc".
      (* +0x28 c.mv s3,a5 : s3 := PGSIZE *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.freerange + 0x28)) (mword_of_int 19 : mword 5) (mword_of_int 15 : mword 5)
                R10 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi28").
      iIntros (CID18 Hs18) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (R11 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (add_vec zero_reg (R10 !!! Regidx (mword_of_int 15 : mword 5)))]> R10).
      assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.freerange + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.freerange + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2a) in "Hpc".
      (* register values entering the loop body *)
      assert (HR11s2 : R11 !!! Regidx (mword_of_int 18 : mword 5) = pa_end).
      { rewrite /R11 upd_ne; [| vm_compute; discriminate].
        rewrite /R10 upd_ne; [| vm_compute; discriminate].
        rewrite /R9 upd_eq. rewrite HR8a1. apply add_vec_zero_l. }
      assert (HR11s3 : R11 !!! Regidx (mword_of_int 19 : mword 5) = PGSIZEv).
      { rewrite /R11 upd_eq.
        rewrite /R10 upd_ne; [| vm_compute; discriminate].
        rewrite /R9 upd_ne; [| vm_compute; discriminate].
        rewrite /R8 upd_ne; [| vm_compute; discriminate].
        rewrite HR7a5. apply add_vec_zero_l. }
      assert (HR11s4 : R11 !!! Regidx (mword_of_int 20 : mword 5) = negPGSIZEv).
      { rewrite /R11 upd_ne; [| vm_compute; discriminate].
        rewrite /R10 upd_eq.
        rewrite /R9 upd_ne; [| vm_compute; discriminate].
        rewrite /R8 upd_ne; [| vm_compute; discriminate].
        rewrite /R7 upd_ne; [| vm_compute; discriminate].
        rewrite HR6a4. apply add_vec_zero_l. }
      assert (HR11sp : R11 !!! Regidx csp_rs1 = spr).
      { rewrite /R11 upd_ne; [| vm_compute; discriminate].
        rewrite /R10 upd_ne; [| vm_compute; discriminate].
        rewrite /R9 upd_ne; [| vm_compute; discriminate]. exact HR8sp. }
      assert (HR11s1 : R11 !!! Regidx (mword_of_int 9 : mword 5) = s1entry).
      { rewrite /R11 upd_ne; [| vm_compute; discriminate].
        rewrite /R10 upd_ne; [| vm_compute; discriminate].
        rewrite /R9 upd_ne; [| vm_compute; discriminate]. exact HR8s1. }
      (* the surviving callee-saved (s5..s11) tracked across the loop *)
      assert (HR11cs : forall c : mword 5, is_cs_idx c = true ->
                c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> csp_rs1 ->
                c <> mword_of_int 18 -> c <> mword_of_int 19 -> c <> mword_of_int 20 ->
                R11 !!! Regidx c = m !!! Regidx c).
      { intros c Hc N8 N9 Nsp N18 N19 N20.
        rewrite /R11 upd_ne; [| congruence].
        rewrite /R10 upd_ne; [| congruence].
        rewrite /R9 upd_ne; [| congruence].
        apply HR8cs; assumption. }
      (* the seven plain instructions since the shift point (0x1a..0x28) have
         moved further; re-anchor once more, to the loop's own entry hart. *)
      assert (Hshift18 : b = false \/ pcur = zero_reg -> (CID18 : CPU) = (CID11 : CPU)) by wp_next_chain.
      iDestruct (wp_next_shift Hshift18 with "Hcont") as "Hcont".
      (* ================================================================= *)
      (* THE LOOP.  Fuel induction over the remaining page list.           *)
      (* ================================================================= *)
      iAssert (∀ (fuel : nat) `(CID0 : CpuId) (M : regfile) (qs : list (mword 64)) (on : option nat),
        ⌜(length qs <= fuel)%nat⌝ -∗
        ⌜ M !!! Regidx (mword_of_int 18 : mword 5) = pa_end
          /\ M !!! Regidx (mword_of_int 19 : mword 5) = PGSIZEv
          /\ M !!! Regidx (mword_of_int 20 : mword 5) = negPGSIZEv
          /\ M !!! Regidx csp_rs1 = spr
          /\ (forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> csp_rs1 -> c <> mword_of_int 18 -> c <> mword_of_int 19 -> c <> mword_of_int 20 -> M !!! Regidx c = m !!! Regidx c)
          /\ prun pa_end (M !!! Regidx (mword_of_int 9 : mword 5)) qs
          /\ qs <> []
          /\ avail_inc_n on (length qs) = Some (length (p0 :: rest)) ⌝ -∗
        sie_cap_gpr (CID:=CID0) M (K - 6) b pcur -∗
        cpu_own (CID:=CID0) ncnt eb pcur C b -∗
        pc_is (CID:=CID0) (mword_of_int (KernelSyms.freerange + 0x2a)) -∗
        ([∗ list] p ∈ qs, page_own p) -∗
        kalloc_avail γk on -∗
        (pa_stk sp0 1) ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) -∗
        (pa_stk sp0 2) ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5) : mword 64) -∗
        (pa_stk sp0 3) ↦₈ (m !!! Regidx (mword_of_int 9 : mword 5) : mword 64) -∗
        (pa_stk sp0 4) ↦₈ (m !!! Regidx (mword_of_int 18 : mword 5) : mword 64) -∗
        (pa_stk sp0 5) ↦₈ (m !!! Regidx (mword_of_int 19 : mword 5) : mword 64) -∗
        (pa_stk sp0 6) ↦₈ (m !!! Regidx (mword_of_int 20 : mword 5) : mword 64) -∗
        wp_next (CID0 := CID0) b pcur (fun (CID : CpuId) =>
          ∀ mr, sie_cap_gpr mr K b pcur -∗
          cpu_own ncnt eb pcur C b -∗
          pc_is ret_tgt -∗ ⌜ callee_saved m mr ⌝ -∗
          kalloc_avail γk (Some (length (p0 :: rest))) -∗
          WP (Loop : expr riscv_lang)) -∗
        WP (Loop : expr riscv_lang))%I
        with "[]" as "Hloop".
      { iIntros (fuel). iInduction fuel as [|fuel IHf] "IHf".
        { iIntros (CID0 M qs on) "%Hlen %Hinv Hcg Hcnt Hpc Hpages Havail Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hcont".
          destruct Hinv as (_ & _ & _ & _ & _ & _ & Hne & _).
          destruct qs; [contradiction | simpl in Hlen; lia]. }
        iIntros (CID0 M qs on) "%Hlen %Hinv Hcg Hcnt Hpc Hpages Havail Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hcont".
        destruct Hinv as (Hms2 & Hms3 & Hms4 & Hmsp & Hmcs & Hprunq & Hqne & Hcount).
        destruct qs as [| pc0 rest0]; [contradiction |].
        destruct Hprunq as (Hfitsq & Hpc0eqq & Hpvq & Hprestq).
        iDestruct "Hpages" as "[Hpage Hpages]".
        iPoseProof (fri_2a with "Htext") as "Hi2a".
        iPoseProof (fri_2e with "Htext") as "Hi2e".
        iPoseProof (fri_32 with "Htext") as "Hi32".
        iPoseProof (fri_34 with "Htext") as "Hi34".
        (* +0x2a add a0,s1,s4 : a0 := p = s1 - PGSIZE *)
        iApply (wp_add_s_sconf (mword_of_int (KernelSyms.freerange + 0x2a)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 20 : mword 5)
                  (add_vec (M !!! Regidx (mword_of_int 9 : mword 5)) (M !!! Regidx (mword_of_int 20 : mword 5))) M (K - 6)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(rgne; rgne; reflexivity)
                  with "Hcg Hpc Hi2a").
        iIntros (CIDb1 Hsb1) "Hcg Hpc".
        set (M1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (M !!! Regidx (mword_of_int 9 : mword 5)) (M !!! Regidx (mword_of_int 20 : mword 5)))]> M).
        assert (HM1a0 : M1 !!! Regidx (mword_of_int 10 : mword 5) = pc0).
        { rewrite /M1 upd_eq. rewrite Hms4. rewrite -Hpc0eqq. reflexivity. }
        assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.freerange + 0x2a) : mword 64) 4 = mword_of_int (KernelSyms.freerange + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp2e) in "Hpc".
        (* +0x2e jal ra,kfree *)
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.freerange + 0x2e)) (mword_of_int 1 : mword 5) (mword_of_int 2096998 : mword 21)
                  M1 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi2e").
        iIntros (CIDb2 Hsb2) "Hcg Hpc".
        set (M2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.freerange + 0x2e) : mword 64) 4)]> M1).
        assert (Htgtkf : add_vec (mword_of_int (KernelSyms.freerange + 0x2e) : mword 64) (sign_extend' 64 (mword_of_int 2096998 : mword 21)) = mword_of_int KernelSyms.kfree) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgtkf) in "Hpc".
        assert (HM2a0 : M2 !!! Regidx (mword_of_int 10 : mword 5) = pc0).
        { rewrite /M2 upd_ne; [exact HM1a0 | vm_compute; discriminate]. }
        assert (HM2sp : M2 !!! Regidx csp_rs1 = spr).
        { rewrite /M2 upd_ne; [| vm_compute; discriminate].
          rewrite /M1 upd_ne; [exact Hmsp | vm_compute; discriminate]. }
        assert (HM2ra : M2 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.freerange + 0x2e) : mword 64) 4) by (rewrite /M2; apply upd_eq).
        (* [Hcnt] entered this iteration at [CID0]; the two plain
           instructions above moved it to [CIDb2], where kfree wants it. *)
        iDestruct (cpu_own_transport CID0 CIDb2 ncnt eb pcur C b ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        (* ---- kfree(p) ---- *)
        iApply (Kfree.wp_kfree_sconf γl γk lk fl M2 on ncnt eb pcur C (K - 6) b
                  ltac:(lia)
                  Hlk Hfl
                  ltac:(lia)
                  with "Hcg Hcnt Htext Hpc Hkmem [Hpage] Havail Hqcpu").
        { rewrite /kfree_pre. iSplitR; [iPureIntro; rewrite HM2a0; exact Hpvq | rewrite HM2a0; iExact "Hpage"]. }
        iIntros (CIDkf Hskf mkf) "Hcg Hcnt Hpc %Hkfcs Havail".
        assert (Hkfret : ret_pc (M2 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.freerange + 0x32)).
        { rewrite HM2ra. apply bv_eq; vm_compute; reflexivity. }
        iEval (rewrite Hkfret) in "Hpc".
        pose proof Hkfcs as Hkfcs_full. unfold callee_saved in Hkfcs.
        destruct Hkfcs as (Hqsp & Hqs0 & Hqs1 & Hqs2 & Hqs3 & Hqs4 & Hqs5 & Hqs6 & Hqs7 & Hqs8 & Hqs9 & Hqs10 & Hqs11).
        (* +0x32 c.add s1,s1,s3 : s1 += PGSIZE *)
        iPoseProof (fri_32 with "Htext") as "Hi32'".
        iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.freerange + 0x32)) (mword_of_int 9 : mword 5) (mword_of_int 19 : mword 5)
                  mkf (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi32").
        iIntros (CIDb3 Hsb3) "Hcg Hpc".
        iEval (rgne; rgne) in "Hcg".
        set (M3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec (mkf !!! Regidx (mword_of_int 9 : mword 5)) (mkf !!! Regidx (mword_of_int 19 : mword 5)))]> mkf).
        assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.freerange + 0x32) : mword 64) 2 = mword_of_int (KernelSyms.freerange + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp34) in "Hpc".
        (* mkf preserves the loop registers (callee-saved through kfree) *)
        assert (Hkf_s1 : mkf !!! Regidx (mword_of_int 9 : mword 5) = M !!! Regidx (mword_of_int 9 : mword 5)).
        { rewrite Hqs1. rewrite /M2 upd_ne; [| vm_compute; discriminate].
          rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]. }
        assert (Hkf_s2 : mkf !!! Regidx (mword_of_int 18 : mword 5) = pa_end).
        { rewrite Hqs2. rewrite /M2 upd_ne; [| vm_compute; discriminate].
          rewrite /M1 upd_ne; [exact Hms2 | vm_compute; discriminate]. }
        assert (Hkf_s3 : mkf !!! Regidx (mword_of_int 19 : mword 5) = PGSIZEv).
        { rewrite Hqs3. rewrite /M2 upd_ne; [| vm_compute; discriminate].
          rewrite /M1 upd_ne; [exact Hms3 | vm_compute; discriminate]. }
        assert (Hkf_s4 : mkf !!! Regidx (mword_of_int 20 : mword 5) = negPGSIZEv).
        { rewrite Hqs4. rewrite /M2 upd_ne; [| vm_compute; discriminate].
          rewrite /M1 upd_ne; [exact Hms4 | vm_compute; discriminate]. }
        assert (Hkf_sp : mkf !!! Regidx csp_rs1 = spr) by (rewrite Hqsp; exact HM2sp).
        assert (HM3s1 : M3 !!! Regidx (mword_of_int 9 : mword 5) = add_vec (M !!! Regidx (mword_of_int 9 : mword 5)) PGSIZEv).
        { rewrite /M3 upd_eq. rewrite Hkf_s1 Hkf_s3. reflexivity. }
        assert (HM3s2 : M3 !!! Regidx (mword_of_int 18 : mword 5) = pa_end).
        { rewrite /M3 upd_ne; [exact Hkf_s2 | vm_compute; discriminate]. }
        assert (HM3s3 : M3 !!! Regidx (mword_of_int 19 : mword 5) = PGSIZEv).
        { rewrite /M3 upd_ne; [exact Hkf_s3 | vm_compute; discriminate]. }
        assert (HM3s4 : M3 !!! Regidx (mword_of_int 20 : mword 5) = negPGSIZEv).
        { rewrite /M3 upd_ne; [exact Hkf_s4 | vm_compute; discriminate]. }
        assert (HM3sp : M3 !!! Regidx csp_rs1 = spr).
        { rewrite /M3 upd_ne; [exact Hkf_sp | vm_compute; discriminate]. }
        (* the tail callee-saved (s5..s11) still equal m through this iteration *)
        assert (HM3cs : forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> csp_rs1 -> c <> mword_of_int 18 -> c <> mword_of_int 19 -> c <> mword_of_int 20 -> M3 !!! Regidx c = m !!! Regidx c).
        { intros c Hc N8 N9 Nsp N18 N19 N20.
          pose proof (is_cs_idx_true_neq (mword_of_int 1 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Nra.
          pose proof (is_cs_idx_true_neq (mword_of_int 10 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na0.
          rewrite /M3 upd_ne; [| congruence].
          rewrite (callee_saved_lookup Hkfcs_full c Hc).
          rewrite /M2 upd_ne; [| congruence].
          rewrite /M1 upd_ne; [| congruence].
          apply Hmcs; assumption. }
        (* the bgeu test: s2 >=u s1  <->  another page still fits (rest nonempty) *)
        destruct rest0 as [| q0 rest0'].
        + (* rest empty: bgeu FALLS -> exit to 0x38, restore s2/s3/s4, then epilogue *)
          simpl in Hprestq.
          assert (Hbfall : zopz0zKzJ_u (M3 !!! Regidx (mword_of_int 18 : mword 5)) (M3 !!! Regidx (mword_of_int 9 : mword 5)) = false).
          { rewrite zge_negb_zlt. rewrite HM3s2 HM3s1. rewrite Hprestq. reflexivity. }
          iApply (wp_bgeu_fall_s_sconf (mword_of_int (KernelSyms.freerange + 0x34)) (mword_of_int 8182 : mword 13) (mword_of_int 9 : mword 5) (mword_of_int 18 : mword 5)
                    M3 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hbfall
                    with "Hcg Hpc Hi34").
          iIntros (CIDb4 Hsb4) "Hcg Hpc".
          assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.freerange + 0x34) : mword 64) 4 = mword_of_int (KernelSyms.freerange + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp38) in "Hpc".
          iPoseProof (fri_38 with "Htext") as "Hi38".
          iPoseProof (fri_3a with "Htext") as "Hi3a".
          iPoseProof (fri_3c with "Htext") as "Hi3c".
          (* +0x38 c.ldsp s2,16(sp) : restore s2 = m!!!18 *)
          iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.freerange + 0x38)) (mword_of_int 2 : mword 6) (mword_of_int 18 : mword 5)
                    M3 (K - 6)%nat (m !!! Regidx (mword_of_int 18 : mword 5)) b (dqm:=DfracOwn 1)
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc Hi38 [Hc4]").
          { iEval (rewrite HM3sp Hb4). iExact "Hc4". }
          iIntros (CIDb5 Hsb5) "Hcg Hpc Hc4".
          iEval (rewrite HM3sp Hb4) in "Hc4".
          set (N1 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> M3).
          assert (HN1sp : N1 !!! Regidx csp_rs1 = spr) by (rewrite /N1 upd_ne; [exact HM3sp | vm_compute; discriminate]).
          assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.freerange + 0x38) : mword 64) 2 = mword_of_int (KernelSyms.freerange + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp3a) in "Hpc".
          (* +0x3a c.ldsp s3,8(sp) : restore s3 = m!!!19 *)
          iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.freerange + 0x3a)) (mword_of_int 1 : mword 6) (mword_of_int 19 : mword 5)
                    N1 (K - 6)%nat (m !!! Regidx (mword_of_int 19 : mword 5)) b (dqm:=DfracOwn 1)
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc Hi3a [Hc5]").
          { iEval (rewrite HN1sp Hb5). iExact "Hc5". }
          iIntros (CIDb6 Hsb6) "Hcg Hpc Hc5".
          iEval (rewrite HN1sp Hb5) in "Hc5".
          set (N2 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 19 : mword 5))]> N1).
          assert (HN2sp : N2 !!! Regidx csp_rs1 = spr) by (rewrite /N2 upd_ne; [exact HN1sp | vm_compute; discriminate]).
          assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.freerange + 0x3a) : mword 64) 2 = mword_of_int (KernelSyms.freerange + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp3c) in "Hpc".
          (* +0x3c c.ldsp s4,0(sp) : restore s4 = m!!!20 *)
          iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.freerange + 0x3c)) (mword_of_int 0 : mword 6) (mword_of_int 20 : mword 5)
                    N2 (K - 6)%nat (m !!! Regidx (mword_of_int 20 : mword 5)) b (dqm:=DfracOwn 1)
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc Hi3c [Hc6]").
          { iEval (rewrite HN2sp Hb6). iExact "Hc6". }
          iIntros (CIDb7 Hsb7) "Hcg Hpc Hc6".
          iEval (rewrite HN2sp Hb6) in "Hc6".
          set (N3 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 20 : mword 5))]> N2).
          assert (HN3sp : N3 !!! Regidx csp_rs1 = spr) by (rewrite /N3 upd_ne; [exact HN2sp | vm_compute; discriminate]).
          assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.freerange + 0x3c) : mword 64) 2 = mword_of_int (KernelSyms.freerange + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp3e) in "Hpc".
          (* the restored map satisfies the epilogue's callee-saved-except side condition *)
          assert (HN3cs : forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> csp_rs1 -> N3 !!! Regidx c = m !!! Regidx c).
          { intros c Hc N8 N9 Nsp.
            destruct (decide (c = mword_of_int 18)) as [->|Hn18].
            { rewrite /N3 upd_ne; [| vm_compute; discriminate].
              rewrite /N2 upd_ne; [| vm_compute; discriminate].
              rewrite /N1 upd_eq; reflexivity. }
            destruct (decide (c = mword_of_int 19)) as [->|Hn19].
            { rewrite /N3 upd_ne; [| vm_compute; discriminate].
              rewrite /N2 upd_eq; reflexivity. }
            destruct (decide (c = mword_of_int 20)) as [->|Hn20].
            { rewrite /N3 upd_eq; reflexivity. }
            rewrite /N3 upd_ne; [| congruence].
            rewrite /N2 upd_ne; [| congruence].
            rewrite /N1 upd_ne; [| congruence].
            apply HM3cs; assumption. }
          (* the token after the last free is [avail_inc on] = [Some (length ps)] *)
          simpl in Hcount.
          iEval (rewrite Hcount) in "Havail".
          (* re-anchor ["Hcont"] and transport ["Hcnt"] from this iteration's
             entry [CID0] (via kfree's exit [CIDkf]) to the exit hart [CIDb7]. *)
          assert (Hshiftexit : b = false \/ pcur = zero_reg -> (CIDb7 : CPU) = (CID0 : CPU)) by wp_next_chain.
          iDestruct (wp_next_shift Hshiftexit with "Hcont") as "Hcont".
          iDestruct (cpu_own_transport CIDkf CIDb7 ncnt eb pcur C b ltac:(wp_next_chain)
                       with "Hcnt") as "Hcnt".
          iApply (frepi (CID0 := CIDb7) m N3 K ncnt eb b pcur C γl γk (Some (length (p0 :: rest))) ltac:(lia)
                    ltac:(apply ret_pc_aligned) HN3sp HN3cs
                    with "Htext Hcg Hcnt Hpc Hc1 Hc2 Hc3 [Hc4] [Hc5] [Hc6] Hqcpu Havail Hcont").
          { iExists _; iExact "Hc4". }
          { iExists _; iExact "Hc5". }
          { iExists _; iExact "Hc6". }
        + (* rest nonempty: bgeu TAKEN -> back-edge to 0x2a, recurse with rest0 *)
          assert (Hbtaken : zopz0zKzJ_u (M3 !!! Regidx (mword_of_int 18 : mword 5)) (M3 !!! Regidx (mword_of_int 9 : mword 5)) = true).
          { rewrite zge_negb_zlt. rewrite HM3s2 HM3s1.
            destruct Hprestq as (Hfitsq' & _ & _ & _). rewrite Hfitsq'. reflexivity. }
          assert (Htgt2a : add_vec (mword_of_int (KernelSyms.freerange + 0x34) : mword 64) (sign_extend' 64 (mword_of_int 8182 : mword 13)) = mword_of_int (KernelSyms.freerange + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
          iApply (wp_bgeu_taken_s_sconf (mword_of_int (KernelSyms.freerange + 0x34)) (mword_of_int 8182 : mword 13) (mword_of_int 9 : mword 5) (mword_of_int 18 : mword 5)
                    M3 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hbtaken
                    ltac:(rewrite Htgt2a; vm_compute; reflexivity)
                    with "Hcg Hpc Hi34").
          iNext. iIntros (CIDb4 Hsb4) "Hcg Hpc".
          iEval (rewrite Htgt2a) in "Hpc".
          assert (Hshiftrec : b = false \/ pcur = zero_reg -> (CIDb4 : CPU) = (CID0 : CPU)) by wp_next_chain.
          iDestruct (wp_next_shift Hshiftrec with "Hcont") as "Hcont".
          iDestruct (cpu_own_transport CIDkf CIDb4 ncnt eb pcur C b ltac:(wp_next_chain)
                       with "Hcnt") as "Hcnt".
          iApply ("IHf" $! CIDb4 M3 (q0 :: rest0') (avail_inc on) with "[] [] Hcg Hcnt Hpc Hpages Havail Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hcont").
          { iPureIntro. simpl in Hlen |- *. lia. }
          { iPureIntro. rewrite HM3s2 HM3s3 HM3s4 HM3sp HM3s1.
            split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
            split; [reflexivity|]. split; [exact HM3cs|].
            split; [exact Hprestq|]. split; [discriminate|].
            rewrite avail_inc_n_comm; exact Hcount. } }
      (* [Hcnt] entered at the section's ambient hart; the eighteen plain
         instructions since (prologue + loop setup) have each moved it, so
         the loop's own entry hart [CID18] wants it re-transported. *)
      iDestruct (cpu_own_transport CID CID18 ncnt eb pcur C b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      (* apply the loop at the entry (fuel = length of the page list) *)
      iApply ("Hloop" $! (length (p0 :: rest)) CID18 R11 (p0 :: rest) (Some 0%nat) with "[] [] Hcg Hcnt Hpc Hpages Havail Hra Hs0 Hs1 Hslot4 Hslot5 Hslot6 Hcont").
      { iPureIntro. lia. }
      { iPureIntro. rewrite HR11s2 HR11s3 HR11s4 HR11sp HR11s1.
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [exact HR11cs|].
        split; [simpl; split; [exact Hfits0 | split; [exact Hp0eq | split; [exact Hpv0 | exact Hprest0]]]|].
        split; [discriminate|].
        rewrite avail_inc_n_Some0; reflexivity. }
  Qed.

End ProofFreerange.

End FreerangeProof.
