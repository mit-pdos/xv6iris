(* ProofProcFreepagetable.v -- proc_freepagetable() over the SIE-agnostic
   sconf world.

     void proc_freepagetable(pagetable_t pagetable, uint64 sz)
     {
       uvmunmap(pagetable, TRAMPOLINE, 1, 0);
       uvmunmap(pagetable, TRAPFRAME,  1, 0);
       uvmfree(pagetable, sz);
     }

   Spec of record: SpecProcFreepagetable.v.  Thirty instructions, a 32-byte
   four-slot frame, three calls and NO branches at all -- the simplest
   whole-function shape in the tree.  What it is really about is the ghost
   walk down BarePt.v's fixed-leaf axis:

     proc_pt P                                    [proc_pt_uptg]
       -> uptg (upt_fixed_both tfp) root um
       -> uptg {[tf_vpn := pte_tf tfp]} root um   +0x1c, UVMUNMAP_FIXED
       -> uptg empty root um = bare_pt root um    +0x2e, UVMUNMAP_FIXED
       -> (nothing)                               +0x36, UVMFREE

   [upt_fixed_both_del_tramp] and [upt_fixed_tf_del_tf] are the two map
   equalities that make each arrow a rewrite.

   TWO THINGS TO KNOW ABOUT THE REGISTER PLUMBING.

   1. THE FIRST CALL NEVER RELOADS a0.  gcc knows a0 still holds the
      pagetable at +0x1c (nothing since entry has written it), so only the
      SECOND call does [c.mv a0,s1].  The proof therefore has to carry
      [Ra0 = page_base uroot] through five register writes rather than
      re-establishing it.

   2. BOTH [va]s ARE BUILT, NOT LOADED: lui / addi -1 / slli.  So the only
      real arithmetic obligations are the two closed equalities saying that
      what lands in a1 IS [TRAMPOLINE] (resp. [TRAPFRAME]) -- [pf_tramp_va]
      and [pf_tf_va] -- plus their [svpn_of]s.  All of it is
      [vm_compute]-closed and hoisted out of the WP (the inline-ltac rule). *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore.
Require Import WpMmodeLeafBase.
Require Import RegFile.
Require Import CalleeSaved StackOwn.
Require Import IntrDefs WpSmodeIntr.
Require Import WpNext.
Require Import WpLock.
Require Import KallocInv.
Require Import PtBuild.
Require Import TrampPt KptExecMap.
Require Import UptTree UserPtTree.
Require Import CpuOwn.
Require Import ProcPtOwn.
Require Import BarePt.
Require Import CodeProcFreepagetable.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import SpecUvmunmap SpecUvmfree.
Require Import SpecProcFreepagetable.
Require Import KernelRvcDecode.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §0  The pure vocabulary.  All [mword]-free where it can be (the        *)
(*     zify-hook rule: [lia] in an mword-laden context fails with         *)
(*     "Cannot find witness").                                            *)
(* ===================================================================== *)

(* the two constants the code BUILDS.  [PF_TRAMP]/[PF_TF] are spelled the
   way the instruction sequence leaves them so the WP can close by
   [vm_compute]. *)
Definition pf_tramp_word : mword 64 := mword_of_int 274877902848.   (* 2^38 - 4096 *)
Definition pf_tf_word    : mword 64 := mword_of_int 274877898752.   (* 2^38 - 8192 *)

(* the run-index bound behind uvmfree's domain premise, as a closed [Z]
   fact *)
Lemma pf_z_vpn_lt (v sz : Z) : 0 <= v -> v * 4096 < sz -> v < (sz + 4095) / 4096.
Proof.
  intros H0 Hlt.
  assert (H1 : (v + 1) * 4096 <= sz + 4095) by lia.
  assert (Hle : v + 1 <= (sz + 4095) / 4096)
    by (apply Z.div_le_lower_bound; lia).
  lia.
Qed.

(* every numeric step of the bridge below, as ONE closed [Z] fact.  In an
   mword-laden context [lia] fails with "Cannot find witness" (the zify
   hook tries to decompose the bitvector terms), so the arithmetic has to
   be done where no mword is in scope and fed back by name. *)
Lemma pf_z_idx (a szz : Z) :
  0 <= a -> a < 134217728 -> 0 <= szz -> a * 4096 < szz ->
  (Z.to_nat a < Z.to_nat ((szz + 4095) / 4096))%nat
  /\ (0 + Z.of_nat (Z.to_nat a) < 134217728)%Z
  /\ (0 + Z.of_nat (Z.to_nat a) = a)%Z.
Proof.
  intros H0 Ha27 Hs Hlt.
  assert (Hid : Z.of_nat (Z.to_nat a) = a) by (apply Z2Nat.id; exact H0).
  assert (Hdiv : 0 <= (szz + 4095) / 4096) by (apply Z.div_pos; lia).
  assert (Hup : a < (szz + 4095) / 4096) by (apply pf_z_vpn_lt; assumption).
  split_and!.
  - apply Nat2Z.inj_lt. rewrite Hid. rewrite (Z2Nat.id _ Hdiv). exact Hup.
  - (* [a < 2^27] is NOT derivable from [a * 4096 < szz]: that only gives
       [a < 2^52].  It is the [mword 27] range of the vpn, passed in. *)
    rewrite Hid. exact Ha27.
  - rewrite Hid. lia.
Qed.

(* [um_below sz um] IS uvmfree's domain premise, one level up.  Every vpn
   the table still maps sits strictly below PGROUNDUP(sz)/PGSIZE, i.e.
   inside the run uvmfree is about to clear.  This is the whole reason the
   contract asks for [um_below] and nothing else about the map -- and the
   caller has it already, from [ProcInv.proc_priv]'s p->sz invariant. *)
Lemma pf_um_below_dom (sz : mword 64) (um : gmap (mword 27) (mword 64)) :
  um_below sz um ->
  dom um ⊆ vpn_run (svpn_of (mword_of_int 0 : mword 64)) (uvm_np sz).
Proof.
  intros Hbel v Hv.
  apply elem_of_dom in Hv. destruct Hv as (w & Hw).
  pose proof (Hbel v w Hw) as Hlt.
  pose proof (bv_unsigned_in_range 27 v) as [Hv0 Hvhi].
  pose proof (bv_unsigned_in_range 64 sz) as [Hs0 _].
  assert (HM : bv_modulus 27 = 134217728) by (vm_compute; reflexivity).
  rewrite HM in Hvhi.
  destruct (pf_z_idx (bv_unsigned v) (bv_unsigned sz) Hv0 Hvhi Hs0 Hlt)
    as (Hidx & Hbnd & Hval).
  assert (Hz0 : svpn_of (mword_of_int 0 : mword 64) = (mword_of_int 0 : mword 27))
    by (apply bv_eq; vm_compute; reflexivity).
  assert (Hzu : bv_unsigned (mword_of_int 0 : mword 27) = 0%Z)
    by (vm_compute; reflexivity).
  apply elem_of_vpn_run.
  exists (Z.to_nat (bv_unsigned v)).
  split.
  - rewrite /uvm_np uint_unsigned. exact Hidx.
  - rewrite Hz0. apply bv_eq. symmetry.
    rewrite (vpn_at_unsigned (mword_of_int 0 : mword 27)
               (Z.to_nat (bv_unsigned v)) ltac:(rewrite Hzu; exact Hbnd)).
    rewrite Hzu. exact Hval.
Qed.

(* the two [va]s the code builds, and their vpns.  Closed, so the WP never
   runs a [vm_compute] under an [ltac:]. *)
Lemma pf_tramp_svpn : svpn_of pf_tramp_word = tramp_vpn.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma pf_tf_svpn : svpn_of pf_tf_word = tf_vpn.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma pf_tramp_align :
  subrange_vec_dec pf_tramp_word 11 0 = (zeros' 12 : mword 12).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma pf_tf_align :
  subrange_vec_dec pf_tf_word 11 0 = (zeros' 12 : mword 12).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma pf_tramp_range : (uint pf_tramp_word + 4096 <= 2 ^ 38)%Z.
Proof. vm_compute; discriminate. Qed.

Lemma pf_tf_range : (uint pf_tf_word + 4096 <= 2 ^ 38)%Z.
Proof. vm_compute; discriminate. Qed.

(* ===================================================================== *)
(* THE WHOLE FUNCTION.                                                    *)
(* ===================================================================== *)

Module ProcFreepagetableProof (UvmunmapFixed : UVMUNMAP_FIXED) (Uvmfree : UVMFREE)
  : PROC_FREEPAGETABLE.

Section ProofProcFreepagetable.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).

  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  (* discharge an [upd_ne] side goal in a callee-saved transport: either the
     written register is not callee-saved at all (so [is_cs_idx c = true]
     refutes it) or it is one of the four this function writes, and the
     corresponding [c <> k] hypothesis is in context.  [vm_compute in Hc]
     does NOT work -- [c] is a variable there. *)
  (* [Hc] is the [is_cs_idx c = true] hypothesis; SUBST first, then compute --
     [vm_compute in Hc] on a variable [c] does nothing. *)
  (* [congruence] MUST come before the [vm_compute] branch: at every layer
     whose written register IS one of the four ([csp_rs1]/[Rs0]/[Rs1]/[Rs2]),
     [Hc] stays TRUE post-subst, so leading with [vm_compute in Hc;
     discriminate] pays for that branch's FAILURE -- and a failed [vm_compute]
     grows with the surrounding proof term, ~1 s a layer near the prologue and
     ~10 s a layer by the epilogue (measured on the analogous [ppt_thr] peel,
     proc-pagetable-ownership.md). [congruence] closes those layers instantly
     from [H2]/[H8]/[H9]/[H18] (post-subst one of them reads [k <> k]); it
     only falls through to [vm_compute] for a genuinely non-callee-saved
     write, where it fails fast on a syntactic mismatch. The two [pf_thr]
     peel sites this hits hardest (:902, the deepest -- 27.68 s; :505, the
     shallowest -- 10.05 s) both drop off this file's expensive-sentence
     list entirely; file total 53.77 s -> 27.42 s (1.96x). *)
  Ltac thr_side Hc :=
    intros Hx; injection Hx as Hx2; subst;
    (* the [k <> k] case by NAME-FREE [exact], not [congruence]: a
       whole-context closer inside a per-layer peel is the ~4 s-per-call trap
       in claude-notes/optimization.md.  [congruence] stays last only so no
       call site can lose completeness. *)
    first [ lazymatch goal with H : ?a <> ?a |- _ => exact (H eq_refl) end
          | vm_compute in Hc; discriminate
          | congruence ].

  (* the callee-saved registers proc_freepagetable itself writes *)
  Definition pf_thr (mm m : regfile) : Prop :=
    forall c : mword 5, is_cs_idx c = true ->
      c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
      m !!! Regidx c = mm !!! Regidx c.

  Lemma wp_proc_freepagetable_sconf
      (γa : gname) (mm : regfile)
      (P : uptd) (K : nat) (eb : bool) (p : mword 64)
      (C : iProp Σ) (ilvl : nat) (b : bool) (lks : gset string)
    : wp_proc_freepagetable_sconf_body γa mm P K eb p C ilvl b lks.
  Proof.
    cbv beta delta [wp_proc_freepagetable_sconf_body].
    intros pcE sz ret_tgt HK Hilvl Hroot Hbnd Hbelow Hlkbelow.
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iIntros "Hcg Hcpu #Htext Hpc Hpt #Henv Hcont".

    (* the three callee stack budgets, discharged once (never inline) *)
    assert (HKuu : (22 <= K - 4)%nat) by lia.
    assert (HKuf : (36 <= K - 4)%nat) by lia.
    (* uvmfree's domain premise, from the contract's [um_below] *)
    assert (Hdom : dom P.(ud_um)
                   ⊆ vpn_run (svpn_of (mword_of_int 0 : mword 64)) (uvm_np sz))
      by exact (pf_um_below_dom sz P.(ud_um) Hbelow).

    (* ================================================================= *)
    (* §A  PROLOGUE: the 32-byte ra/s0/s1/s2 frame.                       *)
    (* ================================================================= *)
    iPoseProof (pfi_00 with "Htext") as "Hi00".
    iPoseProof (pfi_02 with "Htext") as "Hi02".
    iPoseProof (pfi_04 with "Htext") as "Hi04".
    iPoseProof (pfi_06 with "Htext") as "Hi06".
    iPoseProof (pfi_08 with "Htext") as "Hi08".
    iPoseProof (pfi_0a with "Htext") as "Hi0a".
    iPoseProof (pfi_0c with "Htext") as "Hi0c".
    iPoseProof (pfi_0e with "Htext") as "Hi0e".
    assert (Hspm : mm !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (mm !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) mm K 4 b
              ltac:(lia) Hpush with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> mm).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> mm) with A0.
    assert (HA0sp : A0 !!! Regidx csp_rs1 = spd) by (rewrite /A0 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & _)".
    iDestruct "S1c" as (vr24) "Hr24".
    iDestruct "S2c" as (vr16) "Hr16".
    iDestruct "S3c" as (vr8) "Hr8".
    iDestruct "S4c" as (vr0) "Hr0".
    assert (Hb1 : pa_stk sp0 1
                  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2
                  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : pa_stk sp0 3
                  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : pa_stk sp0 4
                  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.proc_freepagetable + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    (* +0x02 c.sdsp ra,24(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x02)) (mword_of_int 3 : mword 6) Rra
              A0 (K - 4)%nat vr24 b with "Hcg Hpc Hi02 [Hr24]").
    { iEval (rewrite HA0sp -Hb1). iExact "Hr24". }
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    iEval (rgne) in "Hr24".
    assert (Hpc04 : add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.proc_freepagetable + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    (* +0x04 c.sdsp s0,16(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x04)) (mword_of_int 2 : mword 6) Rs0
              A0 (K - 4)%nat vr16 b with "Hcg Hpc Hi04 [Hr16]").
    { iEval (rewrite HA0sp -Hb2). iExact "Hr16". }
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    iEval (rgne) in "Hr16".
    assert (Hpc06 : add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.proc_freepagetable + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    (* +0x06 c.sdsp s1,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x06)) (mword_of_int 1 : mword 6) Rs1
              A0 (K - 4)%nat vr8 b with "Hcg Hpc Hi06 [Hr8]").
    { iEval (rewrite HA0sp -Hb3). iExact "Hr8". }
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    iEval (rgne) in "Hr8".
    assert (Hpc08 : add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.proc_freepagetable + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    (* +0x08 c.sdsp s2,0(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x08)) (mword_of_int 0 : mword 6) Rs2
              A0 (K - 4)%nat vr0 b with "Hcg Hpc Hi08 [Hr0]").
    { iEval (rewrite HA0sp -Hb4). iExact "Hr0". }
    iIntros (CID5 Hs5) "Hcg Hpc Hr0".
    iEval (rgne) in "Hr0".
    assert (Hpc0a : add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.proc_freepagetable + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    (* normalize the four saved cells to the epilogue's reload shape *)
    assert (HA0ra : A0 !!! Regidx Rra = mm !!! Regidx Rra)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    assert (HA0s0 : A0 !!! Regidx Rs0 = mm !!! Regidx Rs0)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    assert (HA0s1 : A0 !!! Regidx Rs1 = mm !!! Regidx Rs1)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    assert (HA0s2 : A0 !!! Regidx Rs2 = mm !!! Regidx Rs2)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HA0sp HA0ra) in "Hr24".
    iEval (rewrite HA0sp HA0s0) in "Hr16".
    iEval (rewrite HA0sp HA0s1) in "Hr8".
    iEval (rewrite HA0sp HA0s2) in "Hr0".
    (* +0x0a c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x0a)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 A0 (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok)
              with "Hcg Hpc Hi0a").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (A1 := <[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0).
    change (<[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0) with A1.
    assert (Hpc0c : add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.proc_freepagetable + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    assert (HA1a0 : A1 !!! Regidx Ra0 = page_base P.(ud_root)).
    { rewrite /A1 upd_ne; [| reg_neq]. rewrite /A0 upd_ne; [| reg_neq]. exact Hroot. }
    (* +0x0c c.mv s1,a0 : s1 := pagetable *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x0c)) Rs1 Ra0 A1 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c").
    iIntros (CID7 Hs7) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    iEval (rewrite HA1a0 add_vec_zero_l) in "Hcg".
    set (A2 := <[Regidx Rs1 := regval_into_reg (page_base P.(ud_root))]> A1).
    change (<[Regidx Rs1 := regval_into_reg (page_base P.(ud_root))]> A1) with A2.
    assert (Hpc0e : add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.proc_freepagetable + 0x0e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0e) in "Hpc".
    assert (HA2a1 : A2 !!! Regidx Ra1 = sz).
    { rewrite /A2 upd_ne; [| reg_neq]. rewrite /A1 upd_ne; [| reg_neq].
      rewrite /A0 upd_ne; [| reg_neq]. reflexivity. }
    (* +0x0e c.mv s2,a1 : s2 := sz *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x0e)) Rs2 Ra1 A2 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e").
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    iEval (rewrite HA2a1 add_vec_zero_l) in "Hcg".
    set (A3 := <[Regidx Rs2 := regval_into_reg sz]> A2).
    change (<[Regidx Rs2 := regval_into_reg sz]> A2) with A3.
    assert (Hpc10 : add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.proc_freepagetable + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    (* the four facts that survive the whole body *)
    assert (HA3sp : A3 !!! Regidx csp_rs1 = spd).
    { rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
      rewrite /A1 upd_ne; [| reg_neq]. exact HA0sp. }
    assert (HA3s1 : A3 !!! Regidx Rs1 = page_base P.(ud_root)).
    { rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_eq. reflexivity. }
    assert (HA3s2 : A3 !!! Regidx Rs2 = sz) by (rewrite /A3 upd_eq; reflexivity).
    assert (HA3a0 : A3 !!! Regidx Ra0 = page_base P.(ud_root)).
    { rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq]. exact HA1a0. }
    assert (HA3thr : pf_thr mm A3).
    { intros c Hc H2 H8 H9 H18.
      rewrite /A3 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H18; reflexivity].
      rewrite /A2 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H9; reflexivity].
      rewrite /A1 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H8; reflexivity].
      rewrite /A0 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H2; reflexivity].
      reflexivity. }

    (* ================================================================= *)
    (* §B  CALL 1: uvmunmap(pagetable, TRAMPOLINE, 1, 0).                 *)
    (*     a0 is NOT reloaded -- it still holds the pagetable from entry.  *)
    (* ================================================================= *)
    iPoseProof (pfi_10 with "Htext") as "Hi10".
    iPoseProof (pfi_12 with "Htext") as "Hi12".
    iPoseProof (pfi_14 with "Htext") as "Hi14".
    iPoseProof (pfi_18 with "Htext") as "Hi18".
    iPoseProof (pfi_1a with "Htext") as "Hi1a".
    iPoseProof (pfi_1c with "Htext") as "Hi1c".
    (* +0x10 c.li a3,0 : do_free = 0 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x10)) Ra3
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64) A3 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi10").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (B0 := <[Regidx Ra3 := regval_into_reg (mword_of_int 0 : mword 64)]> A3).
    assert (Hpc12 : add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.proc_freepagetable + 0x12))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    (* +0x12 c.li a2,1 : npages = 1 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x12)) Ra2
              (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64) B0 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi12").
    iIntros (CID10 Hs10) "Hcg Hpc".
    set (B1 := <[Regidx Ra2 := regval_into_reg (mword_of_int 1 : mword 64)]> B0).
    assert (Hpc14 : add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.proc_freepagetable + 0x14))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    (* +0x14 lui a1,0x4000 *)
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x14)) Ra1
              (mword_of_int 16384 : mword 20) (luival (mword_of_int 16384 : mword 20))
              B1 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(reflexivity) with "Hcg Hpc Hi14").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (B2 := <[Regidx Ra1 := regval_into_reg (luival (mword_of_int 16384 : mword 20))]> B1).
    assert (Hpc18 : add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x14) : mword 64) 4 = mword_of_int (KernelSyms.proc_freepagetable + 0x18))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc18) in "Hpc".
    (* +0x18 c.addi a1,a1,-1 *)
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x18)) Ra1 (mword_of_int 63 : mword 6)
              B2 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18").
    iIntros (CID12 Hs12) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B3 := <[Regidx Ra1 := regval_into_reg
        (add_vec (B2 !!! Regidx Ra1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> B2).
    assert (Hpc1a : add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.proc_freepagetable + 0x1a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1a) in "Hpc".
    (* +0x1a c.slli a1,a1,0xc -> a1 = TRAMPOLINE *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x1a)) (Regidx Ra1) Ra1
              (mword_of_int 12 : mword 6) B3 (K - 4)%nat b eq_refl
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi1a").
    iIntros (CID13 Hs13) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B4 := <[Regidx Ra1 := regval_into_reg
        (shift_bits_left (B3 !!! Regidx Ra1)
           (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> B3).
    assert (Hpc1c : add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x1a) : mword 64) 2 = mword_of_int (KernelSyms.proc_freepagetable + 0x1c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1c) in "Hpc".
    (* +0x1c jal ra,uvmunmap *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x1c)) Rra
              (mword_of_int 2094882 : mword 21) B4 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1c").
    iIntros (CID14 Hs14) "Hcg Hpc".
    set (B5 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x1c) : mword 64) 4)]> B4).
    assert (Htgt1 : add_vec (mword_of_int (KernelSyms.proc_freepagetable + 0x1c) : mword 64)
                      (sign_extend' 64 (mword_of_int 2094882 : mword 21))
                    = mword_of_int KernelSyms.uvmunmap)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt1) in "Hpc".
    (* the argument column *)
    assert (HB5a0 : B5 !!! Regidx Ra0 = page_base P.(ud_root)).
    { rewrite /B5 /B4 /B3 /B2 /B1 /B0. repeat (rewrite upd_ne; [| reg_neq]). exact HA3a0. }
    assert (HB5a1 : B5 !!! Regidx Ra1 = pf_tramp_word).
    { rewrite /B5. rewrite upd_ne; [| reg_neq]. rewrite /B4 upd_eq.
      rewrite /B3 upd_eq. rewrite /B2 upd_eq. rewrite /pf_tramp_word.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HB5a2 : B5 !!! Regidx Ra2 = (mword_of_int 1 : mword 64)).
    { rewrite /B5 /B4 /B3 /B2. repeat (rewrite upd_ne; [| reg_neq]).
      rewrite /B1 upd_eq. reflexivity. }
    assert (HB5a3 : B5 !!! Regidx Ra3 = (mword_of_int 0 : mword 64)).
    { rewrite /B5 /B4 /B3 /B2 /B1. repeat (rewrite upd_ne; [| reg_neq]).
      rewrite /B0 upd_eq. reflexivity. }
    assert (HB5sp : B5 !!! Regidx csp_rs1 = spd).
    { rewrite /B5 /B4 /B3 /B2 /B1 /B0. repeat (rewrite upd_ne; [| reg_neq]). exact HA3sp. }
    assert (HB5s1 : B5 !!! Regidx Rs1 = page_base P.(ud_root)).
    { rewrite /B5 /B4 /B3 /B2 /B1 /B0. repeat (rewrite upd_ne; [| reg_neq]). exact HA3s1. }
    assert (HB5s2 : B5 !!! Regidx Rs2 = sz).
    { rewrite /B5 /B4 /B3 /B2 /B1 /B0. repeat (rewrite upd_ne; [| reg_neq]). exact HA3s2. }
    assert (HB5thr : pf_thr mm B5).
    { intros c Hc H2 H8 H9 H18. rewrite /pf_thr in HA3thr.
      rewrite /B5 /B4 /B3 /B2 /B1 /B0.
      (* the peel goes all the way through A3..A0 as well, since those are
         local definitions -- so the residual goal is already reflexive. *)
      repeat (rewrite upd_ne; [| thr_side Hc]).
      first [ reflexivity | apply HA3thr; assumption ]. }
    assert (HB5ra : B5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x1c) : mword 64) 4)
      by (rewrite /B5 upd_eq; reflexivity).
    (* ---- the table, at the fixed-leaf altitude ---- *)
    iDestruct (proc_pt_uptg P with "Hpt") as "Hpt".
    iDestruct (cpu_own_transport CID CID14 ilvl eb p C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (UvmunmapFixed.wp_uvmunmap_fixed_sconf γa B5
              (upt_fixed_both P.(ud_tfp)) P.(ud_root) P.(ud_um) tramp_vpn
              (K - 4)%nat eb p C ilvl b
              _ HKuu Hilvl HB5a0
              ltac:(rewrite HB5a1; exact pf_tramp_align)
              HB5a2 HB5a3
              ltac:(rewrite HB5a1; exact pf_tramp_svpn)
              (or_introl eq_refl)
              ltac:(rewrite HB5a1; exact pf_tramp_range)
              with "Hcg Hcpu Htext Hpc Hpt Henv").
    iIntros (CID15 Hs15 mr1) "Hcg Hcpu Hpc %Hcs1 Hpt".
    iEval (rewrite (upt_fixed_both_del_tramp P.(ud_tfp))) in "Hpt".
    assert (Hret20 : ret_pc (B5 !!! Regidx Rra) = mword_of_int (KernelSyms.proc_freepagetable + 0x20)).
    { rewrite HB5ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret20) in "Hpc".

    (* ================================================================= *)
    (* §C  CALL 2: uvmunmap(pagetable, TRAPFRAME, 1, 0).                  *)
    (*     a0 WAS clobbered by call 1, so this one reloads it from s1.     *)
    (* ================================================================= *)
    iPoseProof (pfi_20 with "Htext") as "Hi20".
    iPoseProof (pfi_22 with "Htext") as "Hi22".
    iPoseProof (pfi_24 with "Htext") as "Hi24".
    iPoseProof (pfi_28 with "Htext") as "Hi28".
    iPoseProof (pfi_2a with "Htext") as "Hi2a".
    iPoseProof (pfi_2c with "Htext") as "Hi2c".
    iPoseProof (pfi_2e with "Htext") as "Hi2e".
    assert (Hm1sp : mr1 !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hcs1 csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HB5sp. }
    assert (Hm1s1 : mr1 !!! Regidx Rs1 = page_base P.(ud_root)).
    { rewrite (callee_saved_lookup Hcs1 Rs1 ltac:(vm_compute; reflexivity)).
      exact HB5s1. }
    assert (Hm1s2 : mr1 !!! Regidx Rs2 = sz).
    { rewrite (callee_saved_lookup Hcs1 Rs2 ltac:(vm_compute; reflexivity)).
      exact HB5s2. }
    assert (Hm1thr : pf_thr mm mr1).
    { intros c Hc H2 H8 H9 H18.
      rewrite (callee_saved_lookup Hcs1 c Hc). apply HB5thr; assumption. }
    (* +0x20 c.li a3,0 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x20)) Ra3
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64) mr1 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi20").
    iIntros (CID16 Hs16) "Hcg Hpc".
    set (C0 := <[Regidx Ra3 := regval_into_reg (mword_of_int 0 : mword 64)]> mr1).
    assert (Hpc22 : add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x20) : mword 64) 2 = mword_of_int (KernelSyms.proc_freepagetable + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc22) in "Hpc".
    (* +0x22 c.li a2,1 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x22)) Ra2
              (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64) C0 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi22").
    iIntros (CID17 Hs17) "Hcg Hpc".
    set (C1 := <[Regidx Ra2 := regval_into_reg (mword_of_int 1 : mword 64)]> C0).
    assert (Hpc24 : add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x22) : mword 64) 2 = mword_of_int (KernelSyms.proc_freepagetable + 0x24))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc24) in "Hpc".
    (* +0x24 lui a1,0x2000 *)
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x24)) Ra1
              (mword_of_int 8192 : mword 20) (luival (mword_of_int 8192 : mword 20))
              C1 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(reflexivity) with "Hcg Hpc Hi24").
    iIntros (CID18 Hs18) "Hcg Hpc".
    set (C2 := <[Regidx Ra1 := regval_into_reg (luival (mword_of_int 8192 : mword 20))]> C1).
    assert (Hpc28 : add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x24) : mword 64) 4 = mword_of_int (KernelSyms.proc_freepagetable + 0x28))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    (* +0x28 c.addi a1,a1,-1 *)
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x28)) Ra1 (mword_of_int 63 : mword 6)
              C2 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi28").
    iIntros (CID19 Hs19) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (C3 := <[Regidx Ra1 := regval_into_reg
        (add_vec (C2 !!! Regidx Ra1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> C2).
    assert (Hpc2a : add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.proc_freepagetable + 0x2a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    (* +0x2a c.slli a1,a1,0xd -> a1 = TRAPFRAME *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x2a)) (Regidx Ra1) Ra1
              (mword_of_int 13 : mword 6) C3 (K - 4)%nat b eq_refl
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi2a").
    iIntros (CID20 Hs20) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (C4 := <[Regidx Ra1 := regval_into_reg
        (shift_bits_left (C3 !!! Regidx Ra1)
           (subrange_vec_dec (mword_of_int 13 : mword 6) (Z.sub log2_xlen 1) 0))]> C3).
    assert (Hpc2c : add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x2a) : mword 64) 2 = mword_of_int (KernelSyms.proc_freepagetable + 0x2c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2c) in "Hpc".
    assert (HC4s1 : C4 !!! Regidx Rs1 = page_base P.(ud_root)).
    { rewrite /C4 /C3 /C2 /C1 /C0. repeat (rewrite upd_ne; [| reg_neq]). exact Hm1s1. }
    (* +0x2c c.mv a0,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x2c)) Ra0 Rs1 C4 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2c").
    iIntros (CID21 Hs21) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    iEval (rewrite HC4s1 add_vec_zero_l) in "Hcg".
    set (C5 := <[Regidx Ra0 := regval_into_reg (page_base P.(ud_root))]> C4).
    assert (Hpc2e : add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.proc_freepagetable + 0x2e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2e) in "Hpc".
    (* +0x2e jal ra,uvmunmap *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x2e)) Rra
              (mword_of_int 2094864 : mword 21) C5 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi2e").
    iIntros (CID22 Hs22) "Hcg Hpc".
    set (C6 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x2e) : mword 64) 4)]> C5).
    assert (Htgt2 : add_vec (mword_of_int (KernelSyms.proc_freepagetable + 0x2e) : mword 64)
                      (sign_extend' 64 (mword_of_int 2094864 : mword 21))
                    = mword_of_int KernelSyms.uvmunmap)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt2) in "Hpc".
    assert (HC6a0 : C6 !!! Regidx Ra0 = page_base P.(ud_root)).
    { rewrite /C6. rewrite upd_ne; [| reg_neq]. rewrite /C5 upd_eq. reflexivity. }
    assert (HC6a1 : C6 !!! Regidx Ra1 = pf_tf_word).
    { rewrite /C6 /C5. repeat (rewrite upd_ne; [| reg_neq]). rewrite /C4 upd_eq.
      rewrite /C3 upd_eq. rewrite /C2 upd_eq. rewrite /pf_tf_word.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HC6a2 : C6 !!! Regidx Ra2 = (mword_of_int 1 : mword 64)).
    { rewrite /C6 /C5 /C4 /C3 /C2. repeat (rewrite upd_ne; [| reg_neq]).
      rewrite /C1 upd_eq. reflexivity. }
    assert (HC6a3 : C6 !!! Regidx Ra3 = (mword_of_int 0 : mword 64)).
    { rewrite /C6 /C5 /C4 /C3 /C2 /C1. repeat (rewrite upd_ne; [| reg_neq]).
      rewrite /C0 upd_eq. reflexivity. }
    assert (HC6sp : C6 !!! Regidx csp_rs1 = spd).
    { rewrite /C6 /C5 /C4 /C3 /C2 /C1 /C0. repeat (rewrite upd_ne; [| reg_neq]).
      exact Hm1sp. }
    assert (HC6s1 : C6 !!! Regidx Rs1 = page_base P.(ud_root)).
    { rewrite /C6 /C5 /C4 /C3 /C2 /C1 /C0. repeat (rewrite upd_ne; [| reg_neq]).
      exact Hm1s1. }
    assert (HC6s2 : C6 !!! Regidx Rs2 = sz).
    { rewrite /C6 /C5 /C4 /C3 /C2 /C1 /C0. repeat (rewrite upd_ne; [| reg_neq]).
      exact Hm1s2. }
    assert (HC6thr : pf_thr mm C6).
    { intros c Hc H2 H8 H9 H18. rewrite /pf_thr in Hm1thr.
      rewrite /C6 /C5 /C4 /C3 /C2 /C1 /C0.
      repeat (rewrite upd_ne; [| thr_side Hc]).
      first [ reflexivity | apply Hm1thr; assumption ]. }
    assert (HC6ra : C6 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x2e) : mword 64) 4)
      by (rewrite /C6 upd_eq; reflexivity).
    iDestruct (cpu_own_transport CID15 CID22 ilvl eb p C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (UvmunmapFixed.wp_uvmunmap_fixed_sconf γa C6
              {[tf_vpn := pte_tf P.(ud_tfp)]} P.(ud_root) P.(ud_um) tf_vpn
              (K - 4)%nat eb p C ilvl b
              _ HKuu Hilvl HC6a0
              ltac:(rewrite HC6a1; exact pf_tf_align)
              HC6a2 HC6a3
              ltac:(rewrite HC6a1; exact pf_tf_svpn)
              (or_intror eq_refl)
              ltac:(rewrite HC6a1; exact pf_tf_range)
              with "Hcg Hcpu Htext Hpc Hpt Henv").
    iIntros (CID23 Hs23 mr2) "Hcg Hcpu Hpc %Hcs2 Hpt".
    (* the table is BARE now: no trampoline, no trapframe, just the user map *)
    iEval (rewrite (upt_fixed_tf_del_tf P.(ud_tfp)) -/(bare_pt P.(ud_root) P.(ud_um)))
      in "Hpt".
    assert (Hret32 : ret_pc (C6 !!! Regidx Rra) = mword_of_int (KernelSyms.proc_freepagetable + 0x32)).
    { rewrite HC6ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret32) in "Hpc".

    (* ================================================================= *)
    (* §D  CALL 3: uvmfree(pagetable, sz).                                *)
    (* ================================================================= *)
    iPoseProof (pfi_32 with "Htext") as "Hi32".
    iPoseProof (pfi_34 with "Htext") as "Hi34".
    iPoseProof (pfi_36 with "Htext") as "Hi36".
    assert (Hm2sp : mr2 !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hcs2 csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HC6sp. }
    assert (Hm2s1 : mr2 !!! Regidx Rs1 = page_base P.(ud_root)).
    { rewrite (callee_saved_lookup Hcs2 Rs1 ltac:(vm_compute; reflexivity)).
      exact HC6s1. }
    assert (Hm2s2 : mr2 !!! Regidx Rs2 = sz).
    { rewrite (callee_saved_lookup Hcs2 Rs2 ltac:(vm_compute; reflexivity)).
      exact HC6s2. }
    assert (Hm2thr : pf_thr mm mr2).
    { intros c Hc H2 H8 H9 H18.
      rewrite (callee_saved_lookup Hcs2 c Hc). apply HC6thr; assumption. }
    (* +0x32 c.mv a1,s2 : a1 := sz *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x32)) Ra1 Rs2 mr2 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi32").
    iIntros (CID24 Hs24) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    iEval (rewrite Hm2s2 add_vec_zero_l) in "Hcg".
    set (D0 := <[Regidx Ra1 := regval_into_reg sz]> mr2).
    assert (Hpc34 : add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x32) : mword 64) 2 = mword_of_int (KernelSyms.proc_freepagetable + 0x34))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc34) in "Hpc".
    assert (HD0s1 : D0 !!! Regidx Rs1 = page_base P.(ud_root))
      by (rewrite /D0 upd_ne; [exact Hm2s1 | reg_neq]).
    (* +0x34 c.mv a0,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x34)) Ra0 Rs1 D0 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi34").
    iIntros (CID25 Hs25) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    iEval (rewrite HD0s1 add_vec_zero_l) in "Hcg".
    set (D1 := <[Regidx Ra0 := regval_into_reg (page_base P.(ud_root))]> D0).
    assert (Hpc36 : add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x34) : mword 64) 2 = mword_of_int (KernelSyms.proc_freepagetable + 0x36))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc36) in "Hpc".
    (* +0x36 jal ra,uvmfree *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x36)) Rra
              (mword_of_int 2095324 : mword 21) D1 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi36").
    iIntros (CID26 Hs26) "Hcg Hpc".
    set (D2 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x36) : mword 64) 4)]> D1).
    assert (Htgt3 : add_vec (mword_of_int (KernelSyms.proc_freepagetable + 0x36) : mword 64)
                      (sign_extend' 64 (mword_of_int 2095324 : mword 21))
                    = mword_of_int KernelSyms.uvmfree)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt3) in "Hpc".
    assert (HD2a0 : D2 !!! Regidx Ra0 = page_base P.(ud_root)).
    { rewrite /D2. rewrite upd_ne; [| reg_neq]. rewrite /D1 upd_eq. reflexivity. }
    assert (HD2a1 : D2 !!! Regidx Ra1 = sz).
    { rewrite /D2 /D1. repeat (rewrite upd_ne; [| reg_neq]). rewrite /D0 upd_eq.
      reflexivity. }
    assert (HD2sp : D2 !!! Regidx csp_rs1 = spd).
    { rewrite /D2 /D1 /D0. repeat (rewrite upd_ne; [| reg_neq]). exact Hm2sp. }
    assert (HD2thr : pf_thr mm D2).
    { intros c Hc H2 H8 H9 H18. rewrite /pf_thr in Hm2thr.
      rewrite /D2 /D1 /D0.
      repeat (rewrite upd_ne; [| thr_side Hc]).
      first [ reflexivity | apply Hm2thr; assumption ]. }
    assert (HD2ra : D2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x36) : mword 64) 4)
      by (rewrite /D2 upd_eq; reflexivity).
    iDestruct (cpu_own_transport CID23 CID26 ilvl eb p C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (Uvmfree.wp_uvmfree_sconf γa D2 P.(ud_root) P.(ud_um)
              (K - 4)%nat eb p C ilvl b
              _ HKuf Hilvl HD2a0
              ltac:(rewrite HD2a1; exact Hbnd)
              ltac:(rewrite HD2a1; exact Hdom)
              with "Hcg Hcpu Htext Hpc Hpt Henv").
    all: try lkbelow.
    iIntros (CID27 Hs27 mr3) "Hcg Hcpu Hpc %Hcs3".
    assert (Hret3a : ret_pc (D2 !!! Regidx Rra) = mword_of_int (KernelSyms.proc_freepagetable + 0x3a)).
    { rewrite HD2ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret3a) in "Hpc".

    (* ================================================================= *)
    (* §E  EPILOGUE (+0x3a .. +0x44).                                     *)
    (* ================================================================= *)
    iPoseProof (pfi_3a with "Htext") as "Hi3a".
    iPoseProof (pfi_3c with "Htext") as "Hi3c".
    iPoseProof (pfi_3e with "Htext") as "Hi3e".
    iPoseProof (pfi_40 with "Htext") as "Hi40".
    iPoseProof (pfi_42 with "Htext") as "Hi42".
    iPoseProof (pfi_44 with "Htext") as "Hi44".
    assert (Hm3sp : mr3 !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hcs3 csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HD2sp. }
    assert (Hm3thr : pf_thr mm mr3).
    { intros c Hc H2 H8 H9 H18.
      rewrite (callee_saved_lookup Hcs3 c Hc). apply HD2thr; assumption. }
    (* +0x3a c.ldsp ra,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x3a)) (mword_of_int 3 : mword 6) Rra
              mr3 (K - 4)%nat (mm !!! Regidx Rra) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3a [Hr24]").
    { iEval (rewrite Hm3sp). iExact "Hr24". }
    iIntros (CID28 Hs28) "Hcg Hpc Hr24". iEval (rewrite Hm3sp) in "Hr24".
    set (E0 := <[Regidx Rra := regval_into_reg (mm !!! Regidx Rra)]> mr3).
    change (<[Regidx Rra := regval_into_reg (mm !!! Regidx Rra)]> mr3) with E0.
    assert (HE0sp : E0 !!! Regidx csp_rs1 = spd)
      by (rewrite /E0 upd_ne; [exact Hm3sp | reg_neq]).
    assert (Hpc3c : add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x3a) : mword 64) 2
                    = mword_of_int (KernelSyms.proc_freepagetable + 0x3c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc3c) in "Hpc".
    (* +0x3c c.ldsp s0,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x3c)) (mword_of_int 2 : mword 6) Rs0
              E0 (K - 4)%nat (mm !!! Regidx Rs0) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3c [Hr16]").
    { iEval (rewrite HE0sp). iExact "Hr16". }
    iIntros (CID29 Hs29) "Hcg Hpc Hr16". iEval (rewrite HE0sp) in "Hr16".
    set (E1 := <[Regidx Rs0 := regval_into_reg (mm !!! Regidx Rs0)]> E0).
    change (<[Regidx Rs0 := regval_into_reg (mm !!! Regidx Rs0)]> E0) with E1.
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spd)
      by (rewrite /E1 upd_ne; [exact HE0sp | reg_neq]).
    assert (Hpc3e : add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x3c) : mword 64) 2
                    = mword_of_int (KernelSyms.proc_freepagetable + 0x3e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc3e) in "Hpc".
    (* +0x3e c.ldsp s1,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x3e)) (mword_of_int 1 : mword 6) Rs1
              E1 (K - 4)%nat (mm !!! Regidx Rs1) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3e [Hr8]").
    { iEval (rewrite HE1sp). iExact "Hr8". }
    iIntros (CID30 Hs30) "Hcg Hpc Hr8". iEval (rewrite HE1sp) in "Hr8".
    set (E2 := <[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> E1).
    change (<[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> E1) with E2.
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spd)
      by (rewrite /E2 upd_ne; [exact HE1sp | reg_neq]).
    assert (Hpc40 : add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x3e) : mword 64) 2
                    = mword_of_int (KernelSyms.proc_freepagetable + 0x40))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc40) in "Hpc".
    (* +0x40 c.ldsp s2,0(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x40)) (mword_of_int 0 : mword 6) Rs2
              E2 (K - 4)%nat (mm !!! Regidx Rs2) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi40 [Hr0]").
    { iEval (rewrite HE2sp). iExact "Hr0". }
    iIntros (CID31 Hs31) "Hcg Hpc Hr0". iEval (rewrite HE2sp) in "Hr0".
    set (E3 := <[Regidx Rs2 := regval_into_reg (mm !!! Regidx Rs2)]> E2).
    change (<[Regidx Rs2 := regval_into_reg (mm !!! Regidx Rs2)]> E2) with E3.
    assert (HE3sp : E3 !!! Regidx csp_rs1 = spd)
      by (rewrite /E3 upd_ne; [exact HE2sp | reg_neq]).
    assert (Hpc42 : add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x40) : mword 64) 2
                    = mword_of_int (KernelSyms.proc_freepagetable + 0x42))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc42) in "Hpc".
    (* +0x42 c.addi16sp sp,32 -- the frame pop *)
    set (E4 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3).
    assert (Hsp0up : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))
                     = sp0).
    { rewrite /spd /sp0 po_addv_assoc.
      assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))
                    = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite HAB. apply avi0. }
    assert (Hwv : add_vec (E3 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0)
      by (rewrite HE3sp; exact Hsp0up).
    assert (Hpop : E3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E3 !!! Regidx csp_rs1)
                               (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HE3sp. symmetry. exact Hspd4. }
    iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hr0]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24". { iExists _. iEval (rewrite Hb1). iExact "Hr24". }
      iSplitL "Hr16". { iExists _. iEval (rewrite Hb2). iExact "Hr16". }
      iSplitL "Hr8".  { iExists _. iEval (rewrite Hb3). iExact "Hr8". }
      iSplitL "Hr0".  { iExists _. iEval (rewrite Hb4). iExact "Hr0". }
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x42))
              (mword_of_int 2 : mword 6) E3 (K - 4)%nat 4 b Hpop
              with "Hcg Hpc Hi42 Hframe4").
    iIntros (CID32 Hs32) "Hcg Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3) with E4.
    assert (Hnk : ((K - 4) + 4)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpc44 : add_vec_int (mword_of_int (KernelSyms.proc_freepagetable + 0x42) : mword 64) 2
                    = mword_of_int (KernelSyms.proc_freepagetable + 0x44))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc44) in "Hpc".
    (* +0x44 c.ret *)
    assert (HE4ra : E4 !!! Regidx Rra = mm !!! Regidx Rra).
    { rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
      rewrite /E2 upd_ne; [| reg_neq]. rewrite /E1 upd_ne; [| reg_neq].
      rewrite /E0 upd_eq. reflexivity. }
    assert (HE4sp : E4 !!! Regidx csp_rs1 = mm !!! Regidx csp_rs1)
      by (rewrite /E4 upd_eq; exact Hwv).
    assert (HE4s0 : E4 !!! Regidx Rs0 = mm !!! Regidx Rs0).
    { rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
      rewrite /E2 upd_ne; [| reg_neq]. rewrite /E1 upd_eq. reflexivity. }
    assert (HE4s1 : E4 !!! Regidx Rs1 = mm !!! Regidx Rs1).
    { rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
      rewrite /E2 upd_eq. reflexivity. }
    assert (HE4s2 : E4 !!! Regidx Rs2 = mm !!! Regidx Rs2).
    { rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_eq. reflexivity. }
    assert (HE4thr : pf_thr mm E4).
    { intros c Hc H2 H8 H9 H18. rewrite /pf_thr in Hm3thr.
      rewrite /E4 /E3 /E2 /E1 /E0.
      repeat (rewrite upd_ne; [| thr_side Hc]).
      first [ reflexivity | apply Hm3thr; assumption ]. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.proc_freepagetable + 0x44)) Rra E4 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi44").
    iIntros (CID33 Hs33) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (E4 !!! Regidx Rra) = ret_tgt) by (rewrite HE4ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    iDestruct (cpu_own_transport CID27 CID33 ilvl eb p C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iSpecialize ("Hcont" $! CID33 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E4 with "Hcg Hcpu Hpc [%]").
    unfold callee_saved. split_and!;
        first [ exact HE4sp | exact HE4s0 | exact HE4s1 | exact HE4s2
              | apply HE4thr; vm_compute; first [reflexivity | discriminate] ].
  Qed.

End ProofProcFreepagetable.

End ProcFreepagetableProof.
