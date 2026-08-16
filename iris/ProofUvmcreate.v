(* ProofUvmcreate.v -- whole-function proof of uvmcreate (kernel/vm.c):
   a 4-slot frame, one kalloc, the null test, memset(p,0,4096), and the
   epilogue.  Straight-line under the counted budget: the null arm is dead.

   The body is the same shape as kvmmake's prologue (ProofKvmmake's
   [wp_kmk_prologue_node]) -- kalloc + memset + [zero_page_to_node] -- with
   the frame pop and the [beqz] fall-through added, since here it IS the
   whole function. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad list_numbers bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore RegFile InstrBytes WpMmodeLeafBase KernelText.
Require Import IntrDefs HartTp WpNext WpSmodeIntr WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpLock.
Require Import CalleeSaved StackOwn.
Require Import CpuOwn.
Require Import KallocInv.
Require Import KMap.            (* mem_page_to_phys *)
Require Import PtBuild KptPt KptTree KvmSpec.
Require Import WpMemsetPage.    (* bytes_choose *)
Require Import CodeUvmcreate.
Require Import SpecKalloc SpecMemset SpecUvmcreate.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
Local Open Scope Z_scope.
Import Defs.

(* clean-context (mword-free) stack-slot arithmetic, so [lia] never sees a bv *)
Lemma uvc_cap_bounds (K : nat) : (18 <= K)%nat ->
  (4 <= K)%nat /\ (2 <= K - 4)%nat /\ (14 <= K - 4)%nat.
Proof. lia. Qed.

(* mword-free too: [uvc_htail]'s frame-pop accounting, kept out of the
   [bitvector.tactics] zify hook the same way. *)
Lemma uvc_nk4 (K : nat) : (4 <= K)%nat -> ((K - 4) + 4)%nat = K.
Proof. lia. Qed.

(* Z-only (bv-free) node-page range arithmetic, so [lia] never sees a bv --
   the heavy-import context breaks lia's zify hook otherwise. *)
(* The lower bound is [PageGeom.kmem_lo] -- kalloc's own [page_in_range]
   floor, which IS the dumped `end` symbol -- rather than a transcribed
   address: its body is a [Z] literal computed from [KernelSyms.end_], so
   [unfold kmem_lo] leaves [lia] a number to work with. *)
Lemma uvc_kdata_bound_arith (z : Z) :
  (z mod 4096 = 0)%Z -> (kmem_lo <= z)%Z -> (z < 0x88000000)%Z ->
  (ram_base <= z)%Z /\ (z + 4096 <= ram_base + ram_size)%Z.
Proof.
  intros Hm Hlo Hhi. apply Z.mod_divide in Hm; [| lia]. destruct Hm as [k Hk].
  unfold kmem_lo in Hlo. unfold ram_base, ram_size. lia.
Qed.

Lemma uvc_kda_arith (z : Z) : (kmem_lo <= z)%Z -> (text_end <= z)%Z.
Proof. unfold text_end, kmem_lo. lia. Qed.


Module UvmcreateProof (AK : KALLOC) (MS : MEMSET) : UVMCREATE.

Section ProofUvmcreate.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.
  Ltac peel_reg_step :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ].
  Ltac peel_reg := peel_reg_step; reflexivity.

  (* ===================================================================== *)
  (*  THE SHARED EPILOGUE, +0x1a .. +0x24.  Both arms of the [beqz a0] in    *)
  (*  [wp_uvmcreate_sconf] leave through it, so it is proved ONCE, as its    *)
  (*  OWN lemma -- NOT a nested [iAssert] -- because it is applied from two  *)
  (*  call sites that have migrated through two INDEPENDENT chains of       *)
  (*  [wp_next]-introduced harts by the time they get there.  [sie_cap_gpr] *)
  (*  / [cpu_own] / [pc_is] / [uvmcreate_post] are all implicitly hart-      *)
  (*  indexed ([Context `{CID:CpuId}]); a nested [iAssert]'s STATEMENT is a  *)
  (*  single fixed [iProp Σ] term with no argument list of its own, so it   *)
  (*  cannot re-bind a fresh per-call [CID] the way a LEMMA can.  Rebinding *)
  (*  `{CID0 : CpuId}` HERE shadows the section's own [CID] for this lemma  *)
  (*  only (durable-notes / sched-hart-generic.md; worked example:          *)
  (*  ProofStrlen.v's [sl_tail]), so callers never annotate it explicitly:  *)
  (*  it unifies automatically from whichever [sie_cap_gpr]-typed hypothesis*)
  (*  the "with" clause supplies at each call site. *)
  Local Lemma uvc_htail `{CID0 : CpuId}
      (γa : gname) (mm : regfile) (lvl K : nat) (eb : bool) (p : mword 64)
      (on : option nat) (b : bool) (lks : gset string)
      (Mt : regfile) (rv sp0 : mword 64) (v4 : bv 64) :
    (4 <= K)%nat ->
    Mt !!! Regidx csp_rs1 = add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) ->
    Mt !!! Regidx (mword_of_int 9 : mword 5) = rv ->
    (forall r : mword 5, is_cs_idx r = true ->
       r <> csp_rs1 -> r <> mword_of_int 8 -> r <> mword_of_int 9 ->
       Mt !!! Regidx r = mm !!! Regidx r) ->
    mm !!! Regidx csp_rs1 = sp0 ->
    sie_cap_gpr Mt (K - 4)%nat b p -∗
    cpu_own lvl eb p b lks -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.uvmcreate + 0x1a)) -∗
    pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1 : mword 5)) -∗
    pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8 : mword 5)) -∗
    pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9 : mword 5)) -∗
    pa_stk sp0 4 ↦₈ v4 -∗
    uvmcreate_post γa on (mm !!! Regidx (mword_of_int 4)) rv -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mr : regfile,
      sie_cap_gpr mr K b p -∗
      cpu_own lvl eb p b lks -∗
      pc_is (ret_pc (mm !!! Regidx (mword_of_int 1 : mword 5))) -∗
      ⌜ callee_saved mm mr ⌝ -∗
      uvmcreate_post γa on (mm !!! Regidx (mword_of_int 4)) (mr !!! Regidx (mword_of_int 10)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hc4 Htsp Hts1 Htrest Hmmsp.
    set (spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    (* the three saved-slot addresses, purely arithmetic in [sp0] -- the
       SAME facts the outer proof computed once from its own [sp0]/[spr],
       re-derived here since [uvc_htail] no longer shares that closure. *)
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iIntros "Hcg Hcnt #Htext Hpc Hc1 Hc2 Hc3 Hc4 Hpost Hcont".
    iPoseProof (uvci_1a with "Htext") as "Hj1a".
    iPoseProof (uvci_1c with "Htext") as "Hj1c".
    iPoseProof (uvci_1e with "Htext") as "Hj1e".
    iPoseProof (uvci_20 with "Htext") as "Hj20".
    iPoseProof (uvci_22 with "Htext") as "Hj22".
    iPoseProof (uvci_24 with "Htext") as "Hj24".
    (* +0x1a mv a0,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmcreate + 0x1a)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              Mt (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hj1a").
    iIntros (CID6 Hs6) "Hcg Hpc".
    (* [wval] is let-bound OUTSIDE the leaf's [wp_next] lambda, so it is
       fixed at the hart ambient WHEN THIS LEMMA WAS APPLIED (CID0, this
       lemma's own binder), NOT the freshly-bound CID6. *)
    set (E0 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (rget (CID := CID0) Mt (mword_of_int 9 : mword 5)))]> Mt).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (rget (CID := CID0) Mt (mword_of_int 9 : mword 5)))]> Mt) with E0.
    assert (Hp1c : add_vec_int (mword_of_int (KernelSyms.uvmcreate + 0x1a) : mword 64) 2 = mword_of_int (KernelSyms.uvmcreate + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1c) in "Hpc".
    assert (HE0sp : E0 !!! Regidx csp_rs1 = spr) by (rewrite /E0; rewrite upd_ne; [| reg_neq]; exact Htsp).
    (* +0x1c ld ra,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmcreate + 0x1c)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              E0 (K - 4)%nat (mm !!! Regidx (mword_of_int 1 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hj1c [Hc1]").
    { iEval (rewrite HE0sp Hb1). iExact "Hc1". }
    iIntros (CID7 Hs7) "Hcg Hpc Hc1". iEval (rewrite HE0sp Hb1) in "Hc1".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 1 : mword 5))]> E0).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 1 : mword 5))]> E0) with E1.
    assert (Hp1e : add_vec_int (mword_of_int (KernelSyms.uvmcreate + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.uvmcreate + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1e) in "Hpc".
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spr) by (rewrite /E1; rewrite upd_ne; [| reg_neq]; exact HE0sp).
    (* +0x1e ld s0,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmcreate + 0x1e)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              E1 (K - 4)%nat (mm !!! Regidx (mword_of_int 8 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hj1e [Hc2]").
    { iEval (rewrite HE1sp Hb2). iExact "Hc2". }
    iIntros (CID8 Hs8) "Hcg Hpc Hc2". iEval (rewrite HE1sp Hb2) in "Hc2".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 8 : mword 5))]> E1) with E2.
    assert (Hp20 : add_vec_int (mword_of_int (KernelSyms.uvmcreate + 0x1e) : mword 64) 2 = mword_of_int (KernelSyms.uvmcreate + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp20) in "Hpc".
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spr) by (rewrite /E2; rewrite upd_ne; [| reg_neq]; exact HE1sp).
    (* +0x20 ld s1,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmcreate + 0x20)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              E2 (K - 4)%nat (mm !!! Regidx (mword_of_int 9 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hj20 [Hc3]").
    { iEval (rewrite HE2sp Hb3). iExact "Hc3". }
    iIntros (CID9 Hs9) "Hcg Hpc Hc3". iEval (rewrite HE2sp Hb3) in "Hc3".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 9 : mword 5))]> E2) with E3.
    assert (Hp22 : add_vec_int (mword_of_int (KernelSyms.uvmcreate + 0x20) : mword 64) 2 = mword_of_int (KernelSyms.uvmcreate + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp22) in "Hpc".
    assert (HE3sp : E3 !!! Regidx csp_rs1 = spr) by (rewrite /E3; rewrite upd_ne; [| reg_neq]; exact HE2sp).
    (* +0x22 addi sp,sp,32 -- the frame pop *)
    assert (Hwv : add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HE3sp. apply frame_cancel_32. }
    assert (Hpop : E3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HE3sp. reflexivity. }
    iAssert (stack_own sp0 4) with "[Hc1 Hc2 Hc3 Hc4]" as "Hframe".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hc1". { iExists (mm !!! Regidx (mword_of_int 1)). iExact "Hc1". }
      iSplitL "Hc2". { iExists (mm !!! Regidx (mword_of_int 8)). iExact "Hc2". }
      iSplitL "Hc3". { iExists (mm !!! Regidx (mword_of_int 9)). iExact "Hc3". }
      iSplitL "Hc4". { iExists v4. iExact "Hc4". }
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.uvmcreate + 0x22)) (mword_of_int 2 : mword 6)
              E3 (K - 4)%nat 4 b Hpop with "Hcg Hpc Hj22 Hframe").
    iIntros (CID10 Hs10) "Hcg Hpc".
    set (E4 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3).
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3) with E4.
    assert (Hnk : ((K - 4) + 4)%nat = K) by (apply uvc_nk4; exact Hc4).
    iEval (rewrite Hnk) in "Hcg".
    assert (Hp24 : add_vec_int (mword_of_int (KernelSyms.uvmcreate + 0x22) : mword 64) 2 = mword_of_int (KernelSyms.uvmcreate + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp24) in "Hpc".
    (* +0x24 ret *)
    assert (HE4ra : E4 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)) by peel_reg.
    (* the leaf's target is [rget E4 ra] (a VARIABLE-index read) -- [rgne]
       bridges it to the plain-map [HE4ra] fact above exactly as at
       cpuid's/mycpu's c.ret sites. *)
    assert (Hrt : ret_pc (rget E4 (mword_of_int 1 : mword 5)) = ret_pc (mm !!! Regidx (mword_of_int 1 : mword 5)))
      by (rgne; rewrite HE4ra; reflexivity).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.uvmcreate + 0x24)) (mword_of_int 1 : mword 5) E4 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hj24").
    iIntros (CID11 Hs11) "Hcg Hpc". iEval (rewrite Hrt) in "Hpc".
    (* [Hts1] is about [Mt !!! Regidx 9]; the leaf's write is [rget Mt 9]
       (same [CID0] annotation as [E0] above -- this is the SAME [wval],
       just re-derived here) -- bridge with [rgne] before chasing the
       E-chain down to it. *)
    assert (HMts1 : rget (CID := CID0) Mt (mword_of_int 9 : mword 5) = rv) by (rgne; exact Hts1).
    assert (HE4a0 : E4 !!! Regidx (mword_of_int 10 : mword 5) = rv).
    { rewrite /E4. rewrite upd_ne; [| reg_neq]. rewrite /E3. rewrite upd_ne; [| reg_neq].
      rewrite /E2. rewrite upd_ne; [| reg_neq]. rewrite /E1. rewrite upd_ne; [| reg_neq].
      rewrite /E0 upd_eq. rewrite add_vec_zero_l. exact HMts1. }
    assert (Hthr : forall r : mword 5, is_cs_idx r = true ->
                     r <> csp_rs1 -> r <> mword_of_int 8 -> r <> mword_of_int 9 ->
                     E4 !!! Regidx r = mm !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /E4 upd_ne; [| congruence].
      rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      rewrite /E0 upd_ne; [| congruence].
      exact (Htrest r Hr Ncsp N8 N9). }
    iSpecialize ("Hcont" $! CID11 with "[%]"); [wp_next_chain|].
    (* [cpu_own] was obtained at this lemma's OWN entry hart [CID0] and is
       never rebound by any of the six plain leaves above (none of them
       mention [cpu_own]); the continuation needs it at [CID11].
       [cpu_own_transport] bridges exactly this: at [b = true] the payload
       isn't hart-indexed at all (pure conversion), at [b = false] the
       chained [Hs6]..[Hs11] equalities (composed by [wp_next_chain]) show
       the hart never moved. *)
    iDestruct (cpu_own_transport CID0 CID11 lvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply ("Hcont" $! E4 with "Hcg Hcnt Hpc [%] [Hpost]").
    - unfold callee_saved.
      (* A1 (sp), A2 (s0) and A3 (s1) are NOT covered by [Hthr] (it
         explicitly excludes csp_rs1/8/9 -- those three are exactly the
         registers this shared tail itself reloads/restores), so they are
         discharged from the E-chain directly; the remaining nine
         (s2..s11) are untouched by any leaf here and go via [Hthr]. *)
      split. { rewrite /E4 upd_eq. rewrite Hwv. symmetry. exact Hmmsp. }
      split. { rewrite /E4. rewrite upd_ne; [| reg_neq]. rewrite /E3. rewrite upd_ne; [| reg_neq]. rewrite /E2 upd_eq. reflexivity. }
      split. { rewrite /E4. rewrite upd_ne; [| reg_neq]. rewrite /E3 upd_eq. reflexivity. }
      repeat (split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|]).
      apply Hthr; vm_compute; first [reflexivity | discriminate].
    - iEval (rewrite HE4a0). iExact "Hpost".
  Qed.

  Lemma wp_uvmcreate_sconf (γa : gname)
      (mm : regfile) (lvl K : nat) (eb : bool) (p : mword 64)
      (on : option nat) (b : bool) (lks : gset string)
    : wp_uvmcreate_sconf_body γa mm lvl K eb p on b lks.
  Proof.
    cbv beta delta [wp_uvmcreate_sconf_body].
    intros ret_tgt Hlvl HK Hcid Hbelow.
    pose proof (uvc_cap_bounds K HK) as (Hc4 & Hc2 & Hc14).
    set (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iIntros "Hcg Hcnt #Htext Hpc Henv Hcont".
    (* [ret_tgt] is a LET-bound local (from [intros] on the spec body's own
       [let ret_tgt := ... in]), not a plain hypothesis -- [rewrite /ret_tgt]
       is a no-op on it (durable-notes.md).  [uvc_htail]'s own continuation
       is stated at the unfolded [ret_pc (mm !!! Regidx 1)] directly (it has
       no [ret_tgt] local of its own), so [Hcont] must be re-spelled that way
       ONCE here for [iApply (uvc_htail ...  with "... Hcont")] to unify
       syntactically at either call site below -- [iSpecialize]/[iApply]'s
       hypothesis matching does not zeta-reduce a local [let] the way [exact]
       does. *)
    assert (Hrettgt : ret_tgt = ret_pc (mm !!! Regidx (mword_of_int 1 : mword 5))) by reflexivity.
    iEval (rewrite Hrettgt) in "Hcont".
    (* frame-cell address facts *)
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hsprstk : pa_stk sp0 4 = spr).
    { rewrite /pa_stk /spr /sp0 /add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (uvci_00 with "Htext") as "Hi00".
    iPoseProof (uvci_02 with "Htext") as "Hi02".
    iPoseProof (uvci_04 with "Htext") as "Hi04".
    iPoseProof (uvci_06 with "Htext") as "Hi06".
    iPoseProof (uvci_08 with "Htext") as "Hi08".
    iPoseProof (uvci_0a with "Htext") as "Hi0a".
    iPoseProof (uvci_0e with "Htext") as "Hi0e".
    iPoseProof (uvci_10 with "Htext") as "Hi10".
    iPoseProof (uvci_12 with "Htext") as "Hi12".
    iPoseProof (uvci_14 with "Htext") as "Hi14".
    iPoseProof (uvci_16 with "Htext") as "Hi16".
    iPoseProof (uvci_1a with "Htext") as "Hi1a".
    iPoseProof (uvci_1c with "Htext") as "Hi1c".
    iPoseProof (uvci_1e with "Htext") as "Hi1e".
    iPoseProof (uvci_20 with "Htext") as "Hi20".
    iPoseProof (uvci_22 with "Htext") as "Hi22".
    iPoseProof (uvci_24 with "Htext") as "Hi24".
    (* +0x00 addi sp,sp,-32 *)
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (mm !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf (mword_of_int KernelSyms.uvmcreate) (mword_of_int 32 : mword 6) mm K 4 b Hc4 Hpush
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    set (W1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> mm).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (v1) "Hc1". iDestruct "S2" as (v2) "Hc2".
    iDestruct "S3" as (v3) "Hc3". iDestruct "S4" as (v4) "Hc4".
    assert (HspW1 : W1 !!! Regidx csp_rs1 = spr) by (rewrite /W1; rewrite upd_eq; reflexivity).
    assert (Hp02 : add_vec_int (mword_of_int KernelSyms.uvmcreate : mword 64) 2 = mword_of_int (KernelSyms.uvmcreate + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    (* +0x02 sd ra,24(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmcreate + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              W1 (K - 4)%nat v1 b with "Hcg Hpc Hi02 [Hc1]").
    { iEval (rewrite HspW1 Hb1). iExact "Hc1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hc1". iEval (rewrite HspW1 Hb1) in "Hc1".
    (* the stored value is [rget W1 _] (a leaf whose source register is a
       VARIABLE index) -- [rgne] bridges it to the plain map fact, exactly
       as at the c.sdsp sites in ProofCpuid.v/ProofMycpu.v.  MUST be
       annotated [(CID := CID1)]: the leaf's [storeval] is LET-BOUND OUTSIDE
       its [wp_next] lambda, so it is fixed at the hart ambient WHEN THE
       LEAF WAS APPLIED (CID1, right after the push), not at CID2 (this
       leaf's OWN resuming hart, bound by the [iIntros] just above) -- a
       bare unannotated [rget] here would default to CID2 (the most
       recently introduced [CpuId] in scope) and silently fail to match
       "Hc1"'s actual content. *)
    assert (HW1r1 : rget (CID := CID1) W1 (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1))
      by (rgne; rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r1) in "Hc1".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.uvmcreate + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.uvmcreate + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    (* +0x04 sd s0,16(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmcreate + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              W1 (K - 4)%nat v2 b with "Hcg Hpc Hi04 [Hc2]").
    { iEval (rewrite HspW1 Hb2). iExact "Hc2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hc2". iEval (rewrite HspW1 Hb2) in "Hc2".
    (* annotated [(CID := CID2)]: ambient hart when THIS csdsp was applied. *)
    assert (HW1r8 : rget (CID := CID2) W1 (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8))
      by (rgne; rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r8) in "Hc2".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.uvmcreate + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.uvmcreate + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    (* +0x06 sd s1,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmcreate + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              W1 (K - 4)%nat v3 b with "Hcg Hpc Hi06 [Hc3]").
    { iEval (rewrite HspW1 Hb3). iExact "Hc3". }
    iIntros (CID4 Hs4) "Hcg Hpc Hc3". iEval (rewrite HspW1 Hb3) in "Hc3".
    (* annotated [(CID := CID3)]: ambient hart when THIS csdsp was applied. *)
    assert (HW1r9 : rget (CID := CID3) W1 (mword_of_int 9 : mword 5) = mm !!! Regidx (mword_of_int 9))
      by (rgne; rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r9) in "Hc3".
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.uvmcreate + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.uvmcreate + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    (* +0x08 addi s0,sp,32 (value unused; s0 reloaded at the epilogue) *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.uvmcreate + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              W1 (K - 4)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (W2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> W1).
    assert (Hp0a : add_vec_int (mword_of_int (KernelSyms.uvmcreate + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.uvmcreate + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0a) in "Hpc".
    (* +0x0a jal kalloc *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uvmcreate + 0x0a)) (mword_of_int 1 : mword 5) (mword_of_int 2095434 : mword 21)
              W2 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0a").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (J := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uvmcreate + 0x0a) : mword 64) 4)]> W2).
    assert (Htgtk : add_vec (mword_of_int (KernelSyms.uvmcreate + 0x0a) : mword 64) (sign_extend' 64 (mword_of_int 2095434 : mword 21)) = mword_of_int KernelSyms.kalloc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtk) in "Hpc".
    iDestruct "Henv" as (γk) "(#Hlock & Havail)".
    assert (HJ4 : J !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4)).
    { rewrite /J /W2 /W1. repeat (rewrite upd_ne; [| reg_neq]). reflexivity. }
    assert (HJsp : J !!! Regidx csp_rs1 = spr).
    { rewrite /J /W2. repeat (rewrite upd_ne; [| reg_neq]). exact HspW1. }
    (* NOTE: kalloc's entry-side tp premise is GONE from the new contract
       (tp_pin makes it true by construction), so the old [HcidJ] argument
       is simply dropped at the call below -- [HJ4] is now unused (kept
       for documentation) rather than deleted, since nothing else in the
       proof reads it either. *)
    (* ---- THE CALL.  [Hcnt : cpu_own lvl eb p C b] was introduced at this
       function's ENTRY hart [CID]; the six plain instructions above each
       ran through a FRESH, universally quantified hart (CID1..CID6), so
       kalloc wants it at CID6.  [cpu_own_transport] moves it there, one
       line, no case split on [b] -- exactly the ProofKvmmap.v pattern. ---- *)
    iDestruct (cpu_own_transport CID CID6 lvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (AK.wp_kalloc_sconf γa γk (mword_of_int (KernelSyms.kmem + 24))
              J on lvl eb p (K - 4)%nat b
              _ Hc14
              ltac:(reflexivity)
              Hlvl
              Hbelow
              with "Hcg Hcnt Htext Hpc Hlock Havail").
    all: try lkbelow.
    iIntros (CID7 Hs7 mr0) "Hcg Hcnt Hpc %Hkcs0 Hkpost".
    assert (Hret0e : ret_pc (J !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.uvmcreate + 0x0e)).
    { rewrite /J upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret0e) in "Hpc".
    set (root0 := mr0 !!! Regidx (mword_of_int 10 : mword 5)).
    assert (Hmr0sp : mr0 !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hkcs0 csp_rs1 ltac:(vm_compute; reflexivity)). exact HJsp. }
    (* +0x0e mv s1,a0 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmcreate + 0x0e)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              mr0 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e").
    iIntros (CID8 Hs8) "Hcg Hpc".
    (* [wval] in [wp_cmv_s_sconf] is LET-BOUND OUTSIDE its [wp_next] lambda,
       so it is fixed at the hart ambient WHEN THE LEAF WAS APPLIED (CID7,
       right after kalloc's own continuation), not at CID8 (bound just
       above) -- [set] must be given that SAME annotation or it will not
       match "Hcg"'s actual content (a bare [rget] here would silently pick
       CID8 instead), and every later [iApply] against [M1] would then fail
       to unify. *)
    set (M1 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (rget (CID := CID7) mr0 (mword_of_int 10 : mword 5)))]> mr0).
    assert (Hp10 : add_vec_int (mword_of_int (KernelSyms.uvmcreate + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.uvmcreate + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    (* the mv's source is [rget mr0 a0] (a VARIABLE-index read) -- bridge to
       the plain [root0] definition with [rgne].  Same CID7 annotation. *)
    assert (Hmr0a0 : rget (CID := CID7) mr0 (mword_of_int 10 : mword 5) = root0) by (rgne; reflexivity).
    (* +0x10 beqz a0 -- THE failure test: kalloc may have returned null *)
    assert (HM1a0 : M1 !!! Regidx (mword_of_int 10 : mword 5) = root0)
      by (rewrite /M1; rewrite upd_ne; [reflexivity | reg_neq]).
    assert (HM1a0' : rget M1 (mword_of_int 10 : mword 5) = root0) by (rgne; exact HM1a0).
    assert (HM1s1 : M1 !!! Regidx (mword_of_int 9 : mword 5) = root0)
      by (rewrite /M1 upd_eq; rewrite Hmr0a0; rewrite add_vec_zero_l; reflexivity).
    assert (HM1sp : M1 !!! Regidx csp_rs1 = spr)
      by (rewrite /M1; rewrite upd_ne; [exact Hmr0sp | reg_neq]).
    assert (HM1rest : forall r : mword 5, is_cs_idx r = true ->
                        r <> csp_rs1 -> r <> mword_of_int 8 -> r <> mword_of_int 9 ->
                        M1 !!! Regidx r = mm !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /M1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hkcs0 r Hr).
      rewrite /J upd_ne; [| congruence].
      rewrite /W2 upd_ne; [| congruence].
      rewrite /W1 upd_ne; [| congruence]. reflexivity. }
    assert (Hnz : (zero_reg : mword 64) = nullp) by (apply bv_eq; vm_compute; reflexivity).
    iDestruct "Hkpost" as "[(%Hnull & %Hz & Havail2) | (%Hpv & Hpage & Havail2)]".
    { (* OUT OF MEMORY: the branch is taken straight to the epilogue *)
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.uvmcreate + 0x10)) (mword_of_int 5 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
                M1 (K - 4)%nat b
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite HM1a0'; apply eq_vec_true_iff; rewrite Hnz; exact Hnull)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi10").
      iNext. iIntros (CID9 Hs9) "Hcg Hpc".
      assert (Htgt1a : add_vec (mword_of_int (KernelSyms.uvmcreate + 0x10) : mword 64)
                         (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 5 : mword 8) ('b"0"))))
                       = mword_of_int (KernelSyms.uvmcreate + 0x1a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt1a) in "Hpc".
      (* [Hcnt] was last rebound at CID7 (kalloc's own continuation); the
         mv and the taken cbeqz above moved the hart on to CID9 without
         either mentioning [cpu_own] -- transport it across both hops. *)
      iDestruct (cpu_own_transport CID7 CID9 lvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iApply (uvc_htail γa mm lvl K eb p on b lks M1 root0 sp0 v4
                Hc4 HM1sp HM1s1 HM1rest ltac:(reflexivity)
                with "Hcg Hcnt Htext Hpc Hc1 Hc2 Hc3 Hc4 [Havail2]").
      { rewrite /uvmcreate_post. iLeft.
        iSplit; [iPureIntro; rewrite Hnull; symmetry; exact Hnz|].
        iSplit; [iPureIntro; exact Hz|].
        iExists γk. iFrame "Hlock Havail2". }
      (* [uvc_htail]'s OWN [wp_next b K] obligation (the [-]-framed slot
         above) is at ITS ambient hart (CID9 here), which is NOT [Hcont]'s
         hart -- [Hcont]'s [wp_next] is fixed at the OUTER entry hart
         [CID].  Re-derive it at the fresh hart the same way [uvc_htail]
         discharges its OWN continuation: [iIntros] the fresh hart plus the
         crossing equality, chase [Hcont] there with [iSpecialize], done. *)
      iIntros (CIDx Hsx).
      iSpecialize ("Hcont" $! CIDx with "[%]"); [wp_next_chain|].
      iExact "Hcont".
    }
    iAssert (kalloc_env γa (avail_sub on 1))
      with "[Havail2]" as "Henv".
    { iExists γk. rewrite avail_sub_S avail_sub_0. iFrame "Hlock Havail2". }
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.uvmcreate + 0x10)) (mword_of_int 5 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
              M1 (K - 4)%nat b
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite HM1a0'; apply eq_vec_false_iff; rewrite Hnz;
                    exact (page_valid_ne_null _ Hpv))
              with "Hcg Hpc Hi10").
    iIntros (CID9 Hs9) "Hcg Hpc".
    assert (Hp12 : add_vec_int (mword_of_int (KernelSyms.uvmcreate + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.uvmcreate + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp12) in "Hpc".
    (* +0x12 lui a2,0x1 *)
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.uvmcreate + 0x12)) (mword_of_int 12 : mword 5) (sign_extend' 20 (mword_of_int 1 : mword 6)) (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))
              M1 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi12").
    iIntros (CID10 Hs10) "Hcg Hpc".
    set (M2 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))]> M1).
    assert (Hp14 : add_vec_int (mword_of_int (KernelSyms.uvmcreate + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.uvmcreate + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp14) in "Hpc".
    (* +0x14 li a1,0 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.uvmcreate + 0x14)) (mword_of_int 11 : mword 5) (mword_of_int 0 : mword 6) (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
              M2 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi14").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (M3 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))]> M2).
    assert (Hp16 : add_vec_int (mword_of_int (KernelSyms.uvmcreate + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.uvmcreate + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp16) in "Hpc".
    (* +0x16 jal memset *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uvmcreate + 0x16)) (mword_of_int 1 : mword 5) (mword_of_int 2095832 : mword 21)
              M3 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi16").
    iIntros (CID12 Hs12) "Hcg Hpc".
    set (M4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.uvmcreate + 0x16) : mword 64) 4)]> M3).
    assert (Htgtm : add_vec (mword_of_int (KernelSyms.uvmcreate + 0x16) : mword 64) (sign_extend' 64 (mword_of_int 2095832 : mword 21)) = mword_of_int KernelSyms.memset) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtm) in "Hpc".
    (* memset(root, 0, 4096): bridge page_own to the per-byte buffer.
       memset's OWN a1/a2 premises stay plain [!!!] lookups (concrete
       indices local to memset's own contract, not a variable-index read
       through [rget]), so [HM4a1]/[HM4a2] are unchanged from before. *)
    assert (HM4a0 : M4 !!! Regidx (mword_of_int 10 : mword 5) = root0).
    { rewrite /M4 /M3 /M2 /M1. repeat (rewrite upd_ne; [| reg_neq]). reflexivity. }
    assert (HM4a1 : M4 !!! Regidx (mword_of_int 11 : mword 5) = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))).
    { rewrite /M4. rewrite upd_ne; [| reg_neq]. rewrite /M3 upd_eq. reflexivity. }
    assert (HM4a2 : M4 !!! Regidx (mword_of_int 12 : mword 5) = mword_of_int (Z.of_nat 4096)).
    { rewrite /M4 /M3. repeat (rewrite upd_ne; [| reg_neq]). rewrite /M2 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite /page_own /byte_any) in "Hpage".
    iDestruct (bytes_choose 4096 0 (fun j b => ((pa_add root0 j) ↦ₘ b)%I) with "Hpage") as (olds) "Hbuf".
    iApply (MS.wp_memset_sconf M4 (K - 4)%nat 4096 (M4 !!! Regidx (mword_of_int 11 : mword 5)) olds b p
              Hc2 ltac:(vm_compute; reflexivity) ltac:(reflexivity) HM4a2
              with "Hcg Htext Hpc [Hbuf]").
    { iApply (big_sepL_impl with "Hbuf"). iIntros "!>" (k j _) "H". rewrite HM4a0. iExact "H". }
    iIntros (CID13 Hs13 mfin) "Hcg Hpc Hbytes %Hmcs".
    assert (Hret1a : ret_pc (M4 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.uvmcreate + 0x1a)).
    { rewrite /M4 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret1a) in "Hpc".
    (* the written buffer is all-zero bytes *)
    assert (Hcb : nth_byte (autocast (T := mword) (subrange_vec_dec (M4 !!! Regidx (mword_of_int 11 : mword 5)) (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0 = (mword_of_int 0 : mword 8)).
    { rewrite HM4a1. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hcb HM4a0) in "Hbytes".
    (* page geometry: alignment + range *)
    pose proof Hpv as Hpv'. destruct Hpv' as [Hpal [Hplo Hphi]].
    unfold page_aligned, PGSIZE in Hpal. unfold page_in_range, kmem_lo, kmem_hi in Hplo, Hphi.
    rewrite uint_unsigned in Hpal, Hplo, Hphi.
    set (bppn := autocast (T := mword) (subrange_vec_dec root0 55 12) : mword 44).
    assert (Hpbase : zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12)) = root0).
    { unfold bppn. apply walk_alloc_page_base.
      - rewrite uint_unsigned. exact Hpal.
      - rewrite uint_unsigned. apply (Z.lt_trans _ 0x88000000); [exact Hphi | apply Z.ltb_lt; vm_compute; reflexivity]. }
    (* physical-tier bytes + node claim from the static kdata claims *)
    iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhwc Hcg]".
    iDestruct "Hhwc" as (hwmisa0 hwmseccfg0 hwpmar0 hwelp0)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & #Hkmapb)".
    iDestruct (mem_page_to_phys root0 (DfracOwn 1) (mword_of_int 0 : mword 8)
                 ltac:(intros j Hj; apply kdata_svpn_class; apply page_in_range_addr_is_kdata; [exact Hpv | exact Hj])
                 with "Hkmapb Hbytes") as "Hbytes".
    iEval (rewrite -Hpbase) in "Hbytes".
    assert (Hbppn4k : bv_unsigned bppn * 4096 = bv_unsigned root0).
    { rewrite <- (page_base_unsigned bppn). rewrite Hpbase. reflexivity. }
    assert (Hnpv : page_valid (page_base bppn)).
    { unfold page_base. rewrite Hpbase. exact Hpv. }
    iDestruct (pt_node_claim_from_static bppn Hnpv with "Hkmapb") as "#Hbclaim".
    iDestruct (zero_page_to_node 2 (DfracOwn 1) bppn with "Hbclaim Hbytes") as "Hptree".
    (* register facts through memset *)
    assert (Hfsp : mfin !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hmcs csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /M4 /M3 /M2 /M1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmr0sp. }
    assert (Hfs1 : mfin !!! Regidx (mword_of_int 9 : mword 5) = zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12))).
    { rewrite (callee_saved_lookup Hmcs (mword_of_int 9) ltac:(vm_compute; reflexivity)).
      rewrite /M4 /M3 /M2. repeat (rewrite upd_ne; [| reg_neq]). rewrite /M1 upd_eq.
      (* M1's insert is [rget mr0 a0] now, not [mr0 !!! Regidx a0] --
         [Hmr0a0] is the bridge (established above, at the mv leaf). *)
      rewrite Hmr0a0. rewrite add_vec_zero_l. rewrite Hpbase. reflexivity. }
    (* ---------------- the shared epilogue does the rest ---------------- *)
    assert (Hfrest : forall r : mword 5, is_cs_idx r = true ->
                       r <> csp_rs1 -> r <> mword_of_int 8 -> r <> mword_of_int 9 ->
                       mfin !!! Regidx r = mm !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N11 : r <> mword_of_int 11) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N12 : r <> mword_of_int 12) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite (callee_saved_lookup Hmcs r Hr).
      rewrite /M4 upd_ne; [| congruence].
      rewrite /M3 upd_ne; [| congruence].
      rewrite /M2 upd_ne; [| congruence].
      rewrite /M1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hkcs0 r Hr).
      rewrite /J upd_ne; [| congruence].
      rewrite /W2 upd_ne; [| congruence].
      rewrite /W1 upd_ne; [| congruence]. reflexivity. }
    (* [Hcnt] was last rebound at CID7 (kalloc's own continuation); memset's
       OWN contract does not thread [cpu_own] at all (SpecMemset.v), so it
       rode UNCHANGED, still at CID7, across the fall-through, lui, li, jal,
       and the memset call itself -- transport it in one hop to CID13, the
       hart memset's own [wp_next] resumed on. *)
    iDestruct (cpu_own_transport CID7 CID13 lvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (uvc_htail γa mm lvl K eb p on b lks mfin (zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12))) sp0 v4
              Hc4 Hfsp Hfs1 Hfrest ltac:(reflexivity)
              with "Hcg Hcnt Htext Hpc Hc1 Hc2 Hc3 Hc4 [Hptree Henv]").
    { rewrite /uvmcreate_post. iRight. iExists bppn.
      iSplit; [done|].
      iSplit; [iPureIntro; rewrite Hpbase; exact Hpv|].
      iFrame "Hptree Henv". }
    (* same re-derivation as the taken branch: [uvc_htail]'s [wp_next]
       obligation here is at CID13, not [Hcont]'s (outer-entry-hart) one. *)
    iIntros (CIDy Hsy).
    iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain|].
    iExact "Hcont".
  Qed.

End ProofUvmcreate.

End UvmcreateProof.
