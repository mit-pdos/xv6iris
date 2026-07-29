(* ProofVirtioDiskRwB.v -- virtio_disk_rw, phases P2.3 .. P6.

   The continuation of ProofVirtioDiskRw.v.  That file proves the four
   Qed-sealed phase lemmas up to and including [wp_vdrw_alloc3] (the
   three-iteration descriptor allocator); this file picks up the seams it
   leaves and carries the function to its return.

     P2.3 the s1/s4/s5/s8 set-up, the outer sleep-retry iLoeb, and the
          partial-free failure tail                        +0x036..+0x0b0
     P3   descriptor / header / status / info.b formatting  +0x0b0..+0x162
     P4   ring write, fence, and THE PUBLISH                +0x162..+0x186
     P5   QUEUE_NOTIFY + the completion-wait iLoeb          +0x186..+0x1b0
     P6   payoff withdrawal, free_chain, release, epilogue  +0x1b0..+0x212

   It is a SEPARATE FILE (rather than more of ProofVirtioDiskRw.v) purely
   for build latency: the parent file already costs ~6 minutes to check, and
   every phase added to it would re-pay that.  The functor is re-opened over
   the same four callee module types and instantiates the parent's functor
   internally, so the phase lemmas compose exactly as if they were one file.

   P3/P4/P5/P6 follow in the C/D/E/F files.
   The whole function is composed and sealed in ProofVirtioDiskRwF.v
   ([Module VirtioDiskRwProof … : VIRTIODISKRW]) and instantiated in
   LinkVirtioDiskRw.v.  Everything here is Qed-closed.
 *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map mono_nat.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved KernelText.
Require Import WpLock.
Require Import ProcGeom.
Require Import IntrDefs WpSmodeIntr.
Require Import CpuOwn SchedCtx FdSlots.
Require Import WpAuipc.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpUart.
Require Import VirtioQueue DiskPtsto VirtioProto DiskInv.
Require Import SpecPanic.
Require Import SpecAcquire SpecRelease SpecSleep SpecFreeDesc.
Require Import WpVirtioDiskRwDecode.
Require Import SpecVirtioDiskRw.
Require Import ProofVirtioDiskRw.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(* §0  Pure helpers for P2.3.                                            *)
(* ===================================================================== *)

(* [c.li s1,8] / [c.li s4,3] / [c.li s8,-1] *)
Lemma vdrwb_li8 :
  add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6)))
  = (mword_of_int 8 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma vdrwb_li3 :
  add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 3 : mword 6)))
  = (mword_of_int (Z.of_nat 3) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma vdrwb_li1 :
  add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))
  = (mword_of_int (Z.of_nat 1) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma vdrwb_lim1 :
  add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))
  = (mword_of_int (-1) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* clearing a descriptor's free bit preserves "index [i] is not free" *)
Lemma fr_upd_false_pres (fr : nat -> bool) (k i : nat) :
  fr i = false -> fr_upd fr k false i = false.
Proof.
  intro H. destruct (decide (i = k)) as [->|Hne];
    [ apply fr_upd_eq | rewrite (fr_upd_ne fr k i false Hne); exact H ].
Qed.

(* the three [bge] outcomes of the partial-free tail: [s2] is 0, 1 or 2. *)
Lemma vdrwb_bge0 :
  zopz0zKzJ_s (zero_reg : mword 64) (mword_of_int (Z.of_nat 0) : mword 64) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma vdrwb_bge1 :
  zopz0zKzJ_s (zero_reg : mword 64) (mword_of_int (Z.of_nat 1) : mword 64) = false.
Proof. vm_compute; reflexivity. Qed.
Lemma vdrwb_bge2 :
  zopz0zKzJ_s (zero_reg : mword 64) (mword_of_int (Z.of_nat 2) : mword 64) = false.
Proof. vm_compute; reflexivity. Qed.
Lemma vdrwb_bge11 :
  zopz0zKzJ_s (mword_of_int (Z.of_nat 1) : mword 64)
              (mword_of_int (Z.of_nat 1) : mword 64) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma vdrwb_bge12 :
  zopz0zKzJ_s (mword_of_int (Z.of_nat 1) : mword 64)
              (mword_of_int (Z.of_nat 2) : mword 64) = false.
Proof. vm_compute; reflexivity. Qed.

(* free_desc's argument bound, read off the word the [lw] loaded *)
Lemma vdrwb_uint_small (i : nat) : (i < 8)%nat ->
  uint (sign_extend' 64 (mword_of_int (Z.of_nat i) : mword 32) : mword 64) = Z.of_nat i.
Proof.
  intro Hi. do 8 (destruct i as [|i]; [ vm_compute; reflexivity |]).
  exfalso. clear -Hi. lia.
Qed.

(* the [lw a0,-96(s0)] / [lw a0,-92(s0)] displacements *)
Lemma vdrwb_sext_4000 :
  sign_extend' 64 (mword_of_int 4000 : mword 12) = (mword_of_int (- 96) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma vdrwb_sext_4004 :
  sign_extend' 64 (mword_of_int 4004 : mword 12) = (mword_of_int (- 92) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* the sleep/free_desc stack budgets, mword-free *)
Lemma vdrwb_K20 (K : nat) : (K_virtio_disk_rw <= K)%nat -> (K_free_desc <= K - 12)%nat.
Proof. unfold K_virtio_disk_rw, K_free_desc. lia. Qed.
Lemma vdrwb_lvl1 : (Z.of_nat 1 + 1 < 2 ^ 31)%Z.
Proof. lia. Qed.

(* THE conjunct the P2/P3/P4 seam has to carry: a triple whose three members
   are still marked FREE cannot meet any RECORDED triple, because every
   recorded member is marked not-free. *)
Lemma vdrwb_tri_disj (fr : nat -> bool) (tr : gmap nat (nat * nat * nat))
    (h m2 t : nat) :
  (forall p T i, tr !! p = Some T -> i ∈ tri_set T -> fr i = false) ->
  fr h = true -> fr m2 = true -> fr t = true ->
  forall p T, tr !! p = Some T -> tri_set T ## tri_set (h, m2, t).
Proof.
  intros Hfree Hh Hm Ht p T Hp.
  apply elem_of_disjoint. intros x Hx1 Hx2.
  pose proof (Hfree p T x Hp Hx1) as Hfx.
  unfold tri_set in Hx2. cbn in Hx2.
  rewrite !elem_of_union !elem_of_singleton in Hx2.
  destruct Hx2 as [[-> | ->] | ->]; congruence.
Qed.

Section VdrwbDefs.
  Context `{!riscvGS Σ, !diskGhostG Σ}.

  (* [free_bundles] only reads [fr] below 8, so a pointwise agreement there
     is all a re-fold needs.  The partial-free tail re-marks the descriptors
     it gives back, producing [fr_upd (fr_upd fr h false) h true], which is
     that -- but not syntactically [fr]. *)
  Lemma free_bundles_ext (pd : Arch.pa) (fr fr' : nat -> bool) :
    (forall i, (i < 8)%nat -> fr i = fr' i) ->
    free_bundles pd fr ⊣⊢ free_bundles pd fr'.
  Proof.
    intro Hext. rewrite /free_bundles. apply big_sepL_proper.
    intros k y Hk. apply lookup_seq in Hk as [-> Hlt].
    rewrite (Hext (0 + k)%nat ltac:(lia)). reflexivity.
  Qed.

  (* THE P2/P3 SEAM: [disk_res] with its existentials named and the free
     bundle at whatever the allocator left behind. *)
  Definition vdrw_body (γ : disk_names) (pd pav : mword 64)
      (np nr : nat) (fl pk : gmap nat dclaim)
      (tr : gmap nat (nat * nat * nat)) (fr : nat -> bool) : iProp Σ :=
    (⌜dom fl = set_seq nr (np - nr)⌝ ∗
     ⌜forall p, p ∈ dom pk -> (p < nr)%nat⌝ ∗
     ⌜dom tr = dom fl ∪ dom pk⌝ ∗
     ⌜forall p v, (fl ∪ pk) !! p = Some v -> tr !! p = Some (dc_tri v)⌝ ∗
     ⌜forall p T, tr !! p = Some T -> tri_ok T⌝ ∗
     ⌜forall p q Tp Tq, p <> q -> tr !! p = Some Tp -> tr !! q = Some Tq ->
        tri_set Tp ## tri_set Tq⌝ ∗
     ⌜forall p T i, tr !! p = Some T -> i ∈ tri_set T -> fr i = false⌝ ∗
     disk_pub γ np ∗
     disk_done_lb γ nr ∗
     ghost_map_auth (dn_claim γ) 1 (fl ∪ pk) ∗
     d_used_idx ↦₂ wrap16 nr ∗
     ([∗ map] p ↦ v ∈ fl, flight_res γ p v) ∗
     ([∗ map] p ↦ v ∈ pk, parked_res γ pav p v) ∗
     free_bundles pd fr ∗
     ring_slots_res pav (mod8 (dom fl)))%I.

  Lemma vdrw_body_close (γ : disk_names) (pd pav pu : mword 64)
      (np nr : nat) (fl pk : gmap nat dclaim)
      (tr : gmap nat (nat * nat * nat)) (fr : nat -> bool) :
    vdrw_body γ pd pav np nr fl pk tr fr -∗ disk_res γ pd pav pu.
  Proof.
    iIntros "H". rewrite /disk_res.
    iExists np, nr, fl, pk, tr, fr. iExact "H".
  Qed.

  Lemma vdrw_body_open (γ : disk_names) (pd pav pu : mword 64) :
    disk_res γ pd pav pu -∗
    ∃ (np nr : nat) (fl pk : gmap nat dclaim)
      (tr : gmap nat (nat * nat * nat)) (fr : nat -> bool),
      vdrw_body γ pd pav np nr fl pk tr fr.
  Proof.
    iIntros "H". rewrite /disk_res.
    iDestruct "H" as (np nr fl pk tr fr) "H".
    iExists np, nr, fl, pk, tr, fr. iExact "H".
  Qed.

  (* re-joining the [int idx[3]] straddle into the two frame slots *)
  Lemma vdrw_idx_join (sp0 : Arch.pa) (v0 v1 v2 : mword 32) :
    is_aligned_paddr (Physaddr (pa_stk sp0 11)) 8 = true ->
    is_aligned_paddr (Physaddr (pa_stk sp0 12)) 8 = true ->
    vdrw_idx sp0 v0 v1 v2 -∗ vdrw_scratch sp0.
  Proof.
    intros Hal11 Hal12. iIntros "(Hx0 & Hx1 & Hx2 & Hxp)".
    iDestruct "Hxp" as (vp) "Hxp".
    iDestruct (word_pointsto_join4 (pa_stk sp0 12) (DfracOwn 1) v0 v1 Hal12
                 with "Hx0 Hx1") as "H12".
    iDestruct (word_pointsto_join4 (pa_stk sp0 11) (DfracOwn 1) v2 vp Hal11
                 with "Hx2 Hxp") as "H11".
    rewrite /vdrw_scratch. iExists (word_of_words v2 vp), (word_of_words v0 v1).
    iFrame "H11 H12".
  Qed.

End VdrwbDefs.

(* the window bound and the ring-slot freshness, WITHOUT the [nr <= np]
   hypothesis: [disk_res] does not carry it (it follows from the protocol,
   which the lock holder cannot see), and both facts are vacuous when the
   subtraction underflows. *)
Lemma disk_window_le' {A : Type} (np nr : nat) (fl pk : gmap nat A)
    (tr : gmap nat (nat * nat * nat)) (T0 : nat * nat * nat) :
  dom fl = set_seq nr (np - nr) ->
  (forall p, p ∈ dom pk -> (p < nr)%nat) ->
  dom tr = dom fl ∪ dom pk ->
  (forall p T, tr !! p = Some T -> tri_ok T) ->
  (forall p q Tp Tq, p <> q -> tr !! p = Some Tp -> tr !! q = Some Tq ->
     tri_set Tp ## tri_set Tq) ->
  tri_ok T0 ->
  (forall p T, tr !! p = Some T -> tri_set T ## tri_set T0) ->
  (np - nr <= 1)%nat.
Proof.
  intros Hfl Hpk Htr Hok Hdisj HT0 Hdisj0.
  destruct (Nat.le_gt_cases nr np) as [Hle|Hgt].
  - exact (disk_window_le np nr fl pk tr T0 Hle Hfl Hpk Htr Hok Hdisj HT0 Hdisj0).
  - lia.
Qed.

Lemma mod8_set_seq_fresh' (nr np : nat) :
  (np - nr <= 1)%nat -> (np `mod` 8)%nat ∉ mod8 (set_seq nr (np - nr)).
Proof.
  intro Hw. destruct (Nat.le_gt_cases nr np) as [Hle|Hgt].
  - exact (mod8_set_seq_fresh nr np Hle Hw).
  - replace (np - nr)%nat with 0%nat by lia.
    rewrite /mod8 /set_seq set_map_empty. apply not_elem_of_empty.
Qed.

(* ===================================================================== *)

Module VirtioDiskRwRest (Acquire : ACQUIRE) (Release : RELEASE)
                        (Sleep : SLEEP) (FreeDesc : FREEDESC).

Module P1 := VirtioDiskRwPhases Acquire Release Sleep FreeDesc.

Section ProofVirtioDiskRwB.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !diskGhostG Σ, !uartGhostG Σ}.
  Context `{CID : CpuId}.

  Notation VRW := KernelSyms.virtio_disk_rw.

  Notation Rra := (mword_of_int 1  : mword 5).
  Notation Rtp := (mword_of_int 4  : mword 5).
  Notation Rs0 := (mword_of_int 8  : mword 5).
  Notation Rs1 := (mword_of_int 9  : mword 5).
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
  Notation Rs8 := (mword_of_int 24 : mword 5).

  Local Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  Local Ltac regne :=
    first [ congruence
          | apply vdrw_cs_ne; [ assumption | vm_compute; reflexivity ] ].

  (* =================================================================== *)
  (* P2.3a  ONE [free_desc] call of the partial-free tail.                *)
  (*                                                                     *)
  (*     off+0  lw   a0, imm(s0)      -- idx[k]                          *)
  (*     off+4  jal  ra, free_desc                                       *)
  (*                                                                     *)
  (* The bundle surgery is the whole content: [free_bundles_split] peels  *)
  (* descriptor [i]'s (cleared) cell out, [free_slot_res] is taken apart  *)
  (* so free_desc gets its four descriptor words, and the pieces it       *)
  (* returns -- the cell at 1 and the four zeroed words -- rebuild the    *)
  (* slot at [fr_upd fr i true].                                         *)
  (* =================================================================== *)
  Lemma wp_vdrw_free_at (γ : gname) (Φ : mval -> iProp Σ) (γs : list gname)
      (pd : mword 64) (i : nat) (fr : nat -> bool)
      (M : regfile) (av : nat) (eb : bool) (pme : mword 64) (C : iProp Σ)
      (idxa : Arch.pa) (off : Z) (imm : mword 12) (jimm : mword 21) :
    (K_free_desc <= av)%nat ->
    (i < 8)%nat ->
    fr i = false ->
    length γs = NPROC ->
    M !!! Regidx Rtp = cid_word ->
    add_vec (M !!! Regidx Rs0) (sign_extend' 64 imm) = (idxa : mword 64) ->
    add_vec_int (mword_of_int (VRW + off) : mword 64) 4
      = (mword_of_int (VRW + off + 4) : mword 64) ->
    add_vec (mword_of_int (VRW + off + 4) : mword 64) (sign_extend' 64 jimm)
      = mword_of_int KernelSyms.free_desc ->
    eq_vec (access_vec_dec (add_vec (mword_of_int (VRW + off + 4) : mword 64)
                              (sign_extend' 64 jimm)) 0) ('b"0") = true ->
    ret_pc (add_vec_int (mword_of_int (VRW + off + 4) : mword 64) 4)
      = (mword_of_int (VRW + off + 8) : mword 64) ->
    sie_cap_gpr γ M av -∗
    cpu_own γ 1 eb pme C -∗
    kernel_text -∗ pc_is (mword_of_int (VRW + off) : mword 64) -∗
    panic_wp -∗ procs_inv γ Φ γs -∗
    d_desc_ptr ↦₈□ pd -∗
    instr (mword_of_int (VRW + off) : mword 64) false
          (LOAD (imm, Regidx Rs0, Regidx Ra0, false, 4)) -∗
    instr (mword_of_int (VRW + off + 4) : mword 64) false (JAL (jimm, Regidx Rra)) -∗
    idxa ↦₄ (mword_of_int (Z.of_nat i) : mword 32) -∗
    free_bundles pd fr -∗ free_slot_res pd i -∗
    ( ∀ Mf : regfile,
        ⌜forall r : mword 5, is_cs_idx r = true -> Mf !!! Regidx r = M !!! Regidx r⌝ -∗
        sie_cap_gpr γ Mf av -∗
        cpu_own γ 1 eb pme C -∗
        pc_is (mword_of_int (VRW + off + 8) : mword 64) -∗
        idxa ↦₄ (mword_of_int (Z.of_nat i) : mword 32) -∗
        free_bundles pd (fr_upd fr i true) -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hav Hi8 Hfri Hlen Htp Haddr Hp4 Hjt Hjal Hret.
    iIntros "Hcg Hown #Htext Hpc #Hpanic #Hpinv #Hdp Hi0 Hi4 Hidx Hbun Hslot Hcont".
    (* ---- lw a0, imm(s0) ---- *)
    iApply (wp_lw_s_sconf γ Φ (mword_of_int (VRW + off) : mword 64) Ra0 Rs0 imm M av
              (mword_of_int (Z.of_nat i) : mword 32) (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0 [Hidx] [-]").
    { iEval (rewrite Haddr). iExact "Hidx". }
    iIntros "Hcg Hpc Hidx".
    iEval (rewrite Haddr) in "Hidx".
    set (N1 := <[Regidx Ra0 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.of_nat i) : mword 32))]> M).
    change (<[Regidx Ra0 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.of_nat i) : mword 32))]> M) with N1.
    iEval (rewrite Hp4) in "Hpc".
    (* ---- jal ra, free_desc ---- *)
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (VRW + off + 4) : mword 64) Rra jimm N1 av
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hjal
              with "Hcg Hpc Hi4 [-]").
    iIntros "Hcg Hpc".
    set (N2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (VRW + off + 4) : mword 64) 4)]> N1).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (VRW + off + 4) : mword 64) 4)]> N1) with N2.
    iEval (rewrite Hjt) in "Hpc".
    (* the register facts free_desc's spec wants *)
    assert (HN2a0 : uint (N2 !!! Regidx Ra0 : mword 64) = Z.of_nat i).
    { rewrite /N2 upd_ne; [| reg_neq]. rewrite /N1 upd_eq.
      exact (vdrwb_uint_small i Hi8). }
    assert (HN2tp : N2 !!! Regidx Rtp = cid_word).
    { rewrite /N2 upd_ne; [| reg_neq]. rewrite /N1 upd_ne; [| reg_neq]. exact Htp. }
    assert (HN2ra : N2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (VRW + off + 4) : mword 64) 4)
      by (rewrite /N2; apply upd_eq).
    (* peel descriptor [i]'s (already cleared) free cell out of the bundle *)
    iEval (rewrite (free_bundles_split pd fr i Hi8)) in "Hbun".
    iDestruct "Hbun" as "[[Hcell _] Hrest]".
    iEval (rewrite Hfri) in "Hcell".
    (* take the slot apart: free_desc wants the four descriptor words *)
    iDestruct "Hslot" as "(Hde & Hops & Hst & Hib)".
    iDestruct "Hde" as (va vl vf vn) "(Hd0 & Hd8 & Hd12 & Hd14)".
    iApply (FreeDesc.wp_free_desc_sconf γ Φ γs pd i N2 av 1%nat eb pme C va vl vf vn
              Hav Hi8 HN2a0 ltac:(intro r; apply rf_to_gmap_dom) Hlen HN2tp vdrwb_lvl1
              with "Hcg Hown Htext Hpc Hpanic Hpinv Hdp Hcell Hd0 Hd8 Hd12 Hd14 [-]").
    iIntros (Mf) "%Hf Hcg Hown _ Hpc Hcell Hd0 Hd8 Hd12 Hd14".
    destruct Hf as (Hcs & _).
    iEval (rewrite HN2ra Hret) in "Hpc".
    iApply ("Hcont" $! Mf with "[%] Hcg Hown Hpc Hidx [Hcell Hrest Hops Hst Hib Hd0 Hd8 Hd12 Hd14]").
    { intros r Hr.
      rewrite (callee_saved_lookup Hcs r Hr).
      rewrite /N2 upd_ne; [| apply not_eq_sym, is_cs_idx_true_neq;
                             [vm_compute; reflexivity | exact Hr]].
      rewrite /N1 upd_ne; [reflexivity |].
      apply not_eq_sym, is_cs_idx_true_neq; [vm_compute; reflexivity | exact Hr]. }
    rewrite (free_bundles_split pd (fr_upd fr i true) i Hi8).
    rewrite fr_upd_eq.
    rewrite -(free_bundles_but_upd pd fr i true).
    iFrame "Hrest Hcell Hops Hst Hib".
    iExists (zero_reg : mword 64), (mword_of_int 0 : mword 32),
            (mword_of_int 0 : mword 16), (mword_of_int 0 : mword 16).
    iFrame "Hd0 Hd8 Hd12 Hd14".
  Qed.

  (* =================================================================== *)
  (* P2.3b  The outer sleep-retry loop.                                  *)
  (* =================================================================== *)

  (* what the loop hands out when all three descriptors are in hand *)
  Definition vdrw_p2_exit (γ γk : gname) (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γd : disk_names)
      (pd pav pu : mword 64) (K : nat) (eb : bool) (C : iProp Σ)
      (sp0 b : Arch.pa) (wr sector : mword 64) (m0 : regfile) : iProp Σ :=
    (∀ (M : regfile) (np nr : nat) (fl pk : gmap nat dclaim)
       (tr : gmap nat (nat * nat * nat)) (fr : nat -> bool) (h m2 t : nat),
       ⌜vdrw_regs M sp0 b wr sector /\ vdrw_hi M m0⌝ -∗
       ⌜tri_ok (h, m2, t) /\ fr h = true /\ fr m2 = true /\ fr t = true⌝ -∗
       (* the publisher's own triple is disjoint from every RECORDED one.
          Only P2.3 can state this: it holds [disk_res] at the ORIGINAL [fr],
          where the three bits are still set, and the body's sixth conjunct
          ("every recorded triple member is not free") then refutes any
          overlap.  Downstream the body is exported at the CLEARED [fr], for
          which that conjunct says nothing at h/m2/t -- so the fact is no
          longer derivable and has to travel. *)
       ⌜forall p T, tr !! p = Some T -> tri_set T ## tri_set (h, m2, t)⌝ -∗
       ⌜is_aligned_paddr (Physaddr (pa_stk sp0 11)) 8 = true
        /\ is_aligned_paddr (Physaddr (pa_stk sp0 12)) 8 = true⌝ -∗
       sie_cap_gpr γ M (K - 12)%nat -∗
       cpu_own γ 1 eb (proc_addr j) C -∗
       trap_csrs_pay 0 eb -∗
       pc_is (mword_of_int (VRW + 0x0b0) : mword 64) -∗
       own_ctx (p_context (proc_addr j)) -∗
       ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) (proc_addr j) -∗
       locked γk cpu_id -∗
       vdrw_body γd pd pav np nr fl pk tr
         (fr_upd (fr_upd (fr_upd fr h false) m2 false) t false) -∗
       free_slot_res pd h -∗ free_slot_res pd m2 -∗ free_slot_res pd t -∗
       vdrw_idx sp0 (mword_of_int (Z.of_nat h)) (mword_of_int (Z.of_nat m2))
                    (mword_of_int (Z.of_nat t)) -∗
       WP (Loop : expr riscv_lang) {{ Φ }})%I.

  (* the loop head at +0x0a8 *)
  Definition vdrw_p2_loop (γ γk : gname) (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γd : disk_names)
      (pd pav pu : mword 64) (K : nat) (eb : bool) (C : iProp Σ)
      (sp0 b : Arch.pa) (wr sector : mword 64) (m0 : regfile) : iProp Σ :=
    (∀ M : regfile,
       ⌜vdrw_regs M sp0 b wr sector
        /\ M !!! Regidx Rs1 = (mword_of_int 8 : mword 64)
        /\ M !!! Regidx Rs4 = (mword_of_int (Z.of_nat 3) : mword 64)
        /\ M !!! Regidx Rs5 = (disk_base : mword 64)
        /\ vdrw_hi M m0⌝ -∗
       sie_cap_gpr γ M (K - 12)%nat -∗
       cpu_own γ 1 eb (proc_addr j) C -∗
       trap_csrs_pay 0 eb -∗
       pc_is (mword_of_int (VRW + 0x0a8) : mword 64) -∗
       own_ctx (p_context (proc_addr j)) -∗
       ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) (proc_addr j) -∗
       locked γk cpu_id -∗
       disk_res γd pd pav pu -∗
       vdrw_scratch sp0 -∗
       vdrw_p2_exit γ γk Φ γs j γd pd pav pu K eb C sp0 b wr sector m0 -∗
       WP (Loop : expr riscv_lang) {{ Φ }})%I.

  Lemma wp_vdrw_p2 (γ γk : gname) (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname) (γd : disk_names)
      (pd pav pu : mword 64) (M0 : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (sp0 b : Arch.pa) (wr sector : mword 64) (m0 : regfile) :
    (K_virtio_disk_rw <= K)%nat ->
    (j < NPROC)%nat -> γs !! j = Some γl -> length γs = NPROC ->
    vdrw_regs M0 sp0 b wr sector -> vdrw_hi M0 m0 ->
    sie_cap_gpr γ M0 (K - 12)%nat -∗
    cpu_own γ 1 eb (proc_addr j) C -∗
    trap_csrs_pay 0 eb -∗
    kernel_text -∗ pc_is (mword_of_int (VRW + 0x036) : mword 64) -∗
    panic_wp -∗ procs_inv γ Φ γs -∗
    own_ctx (p_context (proc_addr j)) -∗
    ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) (proc_addr j) -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    locked γk cpu_id -∗
    disk_res γd pd pav pu -∗
    vdrw_scratch sp0 -∗
    vdrw_p2_exit γ γk Φ γs j γd pd pav pu K eb C sp0 b wr sector m0 -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros HK Hj Hjl Hlen Hregs Hhi0.
    iIntros "Hcg Hown Hpay #Htext Hpc #Hpanic #Hpinv Hctx Hsched
             #Hgeom #Hlk Htok HR Hscr Hexit".
    iPoseProof (rwi_036 with "Htext") as "Hi036".
    iPoseProof (rwi_038 with "Htext") as "Hi038".
    iPoseProof (rwi_03c with "Htext") as "Hi03c".
    iPoseProof (rwi_040 with "Htext") as "Hi040".
    iPoseProof (rwi_042 with "Htext") as "Hi042".
    iPoseProof (rwi_044 with "Htext") as "Hi044".
    (* ---- +0x036  c.li s1,8 ---- *)
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (VRW + 0x036) : mword 64) Rs1
              (mword_of_int 8 : mword 6) (mword_of_int 8 : mword 64) M0 (K - 12)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              vdrwb_li8 with "Hcg Hpc Hi036 [-]").
    iIntros "Hcg Hpc".
    set (A1 := <[Regidx Rs1 := regval_into_reg (mword_of_int 8 : mword 64)]> M0).
    change (<[Regidx Rs1 := regval_into_reg (mword_of_int 8 : mword 64)]> M0) with A1.
    assert (Hp038 : add_vec_int (mword_of_int (VRW + 0x036) : mword 64) 2
                    = mword_of_int (VRW + 0x038)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp038) in "Hpc".
    (* ---- +0x038 / +0x03c  s5 := &disk ---- *)
    iApply (wp_auipc_s_sconf γ Φ (mword_of_int (VRW + 0x038) : mword 64) Rs5
              (mword_of_int 30 : mword 20) A1 (K - 12)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi038 [-]").
    iIntros "Hcg Hpc".
    set (A2 := <[Regidx Rs5 := regval_into_reg
                  (add_vec (mword_of_int (VRW + 0x038) : mword 64)
                           (auipc_off (mword_of_int 30 : mword 20)))]> A1).
    change (<[Regidx Rs5 := regval_into_reg
                  (add_vec (mword_of_int (VRW + 0x038) : mword 64)
                           (auipc_off (mword_of_int 30 : mword 20)))]> A1) with A2.
    assert (Hp03c : add_vec_int (mword_of_int (VRW + 0x038) : mword 64) 4
                    = mword_of_int (VRW + 0x03c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp03c) in "Hpc".
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (VRW + 0x03c) : mword 64) Rs5 Rs5
              (mword_of_int 3216 : mword 12) A2 (K - 12)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi03c [-]").
    iIntros "Hcg Hpc".
    set (A3 := <[Regidx Rs5 := regval_into_reg
                  (add_vec (A2 !!! Regidx Rs5)
                     (sign_extend' 64 (mword_of_int 3216 : mword 12)))]> A2).
    change (<[Regidx Rs5 := regval_into_reg
                  (add_vec (A2 !!! Regidx Rs5)
                     (sign_extend' 64 (mword_of_int 3216 : mword 12)))]> A2) with A3.
    assert (HA3s5 : A3 !!! Regidx Rs5 = (disk_base : mword 64)).
    { rewrite /A3 upd_eq /A2 upd_eq.
      unfold disk_base. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp040 : add_vec_int (mword_of_int (VRW + 0x03c) : mword 64) 4
                    = mword_of_int (VRW + 0x040)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp040) in "Hpc".
    (* ---- +0x040  c.li s4,3 ---- *)
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (VRW + 0x040) : mword 64) Rs4
              (mword_of_int 3 : mword 6) (mword_of_int (Z.of_nat 3) : mword 64)
              A3 (K - 12)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              vdrwb_li3 with "Hcg Hpc Hi040 [-]").
    iIntros "Hcg Hpc".
    set (A4 := <[Regidx Rs4 := regval_into_reg
                  (mword_of_int (Z.of_nat 3) : mword 64)]> A3).
    change (<[Regidx Rs4 := regval_into_reg
                  (mword_of_int (Z.of_nat 3) : mword 64)]> A3) with A4.
    assert (Hp042 : add_vec_int (mword_of_int (VRW + 0x040) : mword 64) 2
                    = mword_of_int (VRW + 0x042)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp042) in "Hpc".
    (* ---- +0x042  c.li s8,-1 ---- *)
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (VRW + 0x042) : mword 64) Rs8
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              A4 (K - 12)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              vdrwb_lim1 with "Hcg Hpc Hi042 [-]").
    iIntros "Hcg Hpc".
    set (A5 := <[Regidx Rs8 := regval_into_reg (mword_of_int (-1) : mword 64)]> A4).
    change (<[Regidx Rs8 := regval_into_reg (mword_of_int (-1) : mword 64)]> A4) with A5.
    assert (Hp044 : add_vec_int (mword_of_int (VRW + 0x042) : mword 64) 2
                    = mword_of_int (VRW + 0x044)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp044) in "Hpc".
    (* the four loop-invariant registers, at A5 *)
    assert (HA5s1 : A5 !!! Regidx Rs1 = (mword_of_int 8 : mword 64)).
    { rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
      rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
      rewrite /A1; apply upd_eq. }
    assert (HA5s4 : A5 !!! Regidx Rs4 = (mword_of_int (Z.of_nat 3) : mword 64)).
    { rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4; apply upd_eq. }
    assert (HA5s5 : A5 !!! Regidx Rs5 = (disk_base : mword 64)).
    { rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq]. exact HA3s5. }
    assert (HA5regs : vdrw_regs A5 sp0 b wr sector).
    { unfold vdrw_regs in Hregs |- *.
      destruct Hregs as (Hsp & Hs0 & Hs3 & Hs6 & Hs7 & Htp).
      split_and!.
      - rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
        rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
        rewrite /A1 upd_ne; [| reg_neq]. exact Hsp.
      - rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
        rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
        rewrite /A1 upd_ne; [| reg_neq]. exact Hs0.
      - rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
        rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
        rewrite /A1 upd_ne; [| reg_neq]. exact Hs3.
      - rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
        rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
        rewrite /A1 upd_ne; [| reg_neq]. exact Hs6.
      - rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
        rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
        rewrite /A1 upd_ne; [| reg_neq]. exact Hs7.
      - rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
        rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
        rewrite /A1 upd_ne; [| reg_neq]. exact Htp. }
    (* ================= THE LOOP (iLoeb) ================= *)
    iAssert (vdrw_p2_loop γ γk Φ γs j γd pd pav pu K eb C sp0 b wr sector m0)
      with "[]" as "Hloop".
    { iLöb as "IH". rewrite /vdrw_p2_loop.
      iIntros (M) "%Hinv Hcg Hown Hpay Hpc Hctx Hsched Htok HR Hscr Hexit".
      destruct Hinv as (Hregs' & Hs1 & Hs4 & Hs5 & Hhi).
      iPoseProof (rwi_07a with "Htext") as "Hi07a".
      iPoseProof (rwi_07e with "Htext") as "Hi07e".
      iPoseProof (rwi_082 with "Htext") as "Hi082".
      iPoseProof (rwi_086 with "Htext") as "Hi086".
      iPoseProof (rwi_088 with "Htext") as "Hi088".
      iPoseProof (rwi_08c with "Htext") as "Hi08c".
      iPoseProof (rwi_090 with "Htext") as "Hi090".
      iPoseProof (rwi_094 with "Htext") as "Hi094".
      iPoseProof (rwi_098 with "Htext") as "Hi098".
      iPoseProof (rwi_09c with "Htext") as "Hi09c".
      iPoseProof (rwi_0a0 with "Htext") as "Hi0a0".
      iPoseProof (rwi_0a4 with "Htext") as "Hi0a4".
      iDestruct "Hgeom" as "#Hgeom'".
      iDestruct "Hgeom'" as "(Hdp & _)".
      destruct Hregs' as (Hsp & Hs0 & Hs3 & Hs6 & Hs7 & Htp).
      (* open the lock's resource *)
      iDestruct (vdrw_body_open γd pd pav pu with "HR") as (np nr fl pk tr fr) "Hbody".
      iDestruct "Hbody" as "(%Hdfl & %Hdpk & %Hdtr & %Hcoh & %Htok1 & %Htok2 & %Htok3 &
                             Hpub & Hlb & Hcl & Huidx & Hflight & Hparked &
                             Hbun & Hring)".
      (* ---- the three-descriptor allocator ---- *)
      iApply (P1.wp_vdrw_alloc3 γ Φ pd sp0 fr (K - 12)%nat M
                Hs0 Hs5 Hs1 Hs4 with "Hcg Htext Hpc Hbun Hscr [-]").
      (* the [iNext] here is what pays the Loeb later: [wp_vdrw_alloc3]'s
         continuation is guarded, and stripping it also strips "IH". *)
      iNext.
      (* [cpu_own]/[trap_csrs_pay] are opaque Definitions, so only the
         scheduler valid-context needs re-wrapping. *)
      iAssert (▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) (proc_addr j))%I
        with "[Hsched]" as "Hsched".
      { iNext. iExact "Hsched". }
      iIntros (M1) "%Hcs1 %Hal Hcg Hout".
      rewrite /P1.vdrw_alloc_out. iDestruct "Hout" as "[Hok|Hfail]".
      { (* ============ all three won: hand the seam to P3 ============ *)
        iDestruct "Hok" as (h m2 t) "[%Hfacts [Hpc [Hidx [Hbh [Hbm [Hbt Hbun]]]]]]".
        destruct Hfacts as (Hh8 & Hm8 & Ht8 & Hhm & Hht & Hmt & Hfrh & Hfrm & Hfrt).
        iApply ("Hexit" $! M1 np nr fl pk tr fr h m2 t with
                  "[%] [%] [%] [%] Hcg Hown Hpay Hpc Hctx Hsched Htok
                   [Hpub Hlb Hcl Huidx Hflight Hparked Hbun Hring] Hbh Hbm Hbt Hidx").
        - split;
            [| exact (vdrw_hi_frame1 M M1 m0 Rs2 ltac:(vm_compute; reflexivity) Hcs1 Hhi)].
          unfold vdrw_regs. split_and!.
          + rewrite (Hcs1 csp_rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hsp.
          + rewrite (Hcs1 Rs0 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hs0.
          + rewrite (Hcs1 Rs3 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hs3.
          + rewrite (Hcs1 Rs6 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hs6.
          + rewrite (Hcs1 Rs7 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hs7.
          + rewrite (Hcs1 Rtp ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Htp.
        - unfold tri_ok. cbn. split_and!; assumption.
        - exact (vdrwb_tri_disj fr tr h m2 t Htok3 Hfrh Hfrm Hfrt).
        - exact Hal.
        - rewrite /vdrw_body. iFrame "Hpub Hlb Hcl Huidx Hflight Hparked Hbun Hring".
          iPureIntro. split_and!; try assumption.
          intros p T i HpT Hi.
          apply fr_upd_false_pres, fr_upd_false_pres, fr_upd_false_pres.
          exact (Htok3 p T i HpT Hi). }
      (* ============ the partial-free failure tail ============ *)
      iDestruct "Hfail" as "[Hpc Hfail]".
      (* the register facts that survive the allocator *)
      assert (Hsp1 : M1 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite (Hcs1 csp_rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Hsp).
      assert (Hs01 : M1 !!! Regidx Rs0 = (sp0 : mword 64))
        by (rewrite (Hcs1 Rs0 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Hs0).
      assert (Hs31 : M1 !!! Regidx Rs3 = (b : mword 64))
        by (rewrite (Hcs1 Rs3 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Hs3).
      assert (Hs61 : M1 !!! Regidx Rs6 = wr)
        by (rewrite (Hcs1 Rs6 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Hs6).
      assert (Hs71 : M1 !!! Regidx Rs7 = sector)
        by (rewrite (Hcs1 Rs7 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Hs7).
      assert (Htp1 : M1 !!! Regidx Rtp = cid_word)
        by (rewrite (Hcs1 Rtp ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Htp).
      assert (Hs11 : M1 !!! Regidx Rs1 = (mword_of_int 8 : mword 64))
        by (rewrite (Hcs1 Rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Hs1).
      assert (Hs41 : M1 !!! Regidx Rs4 = (mword_of_int (Z.of_nat 3) : mword 64))
        by (rewrite (Hcs1 Rs4 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Hs4).
      assert (Hs51 : M1 !!! Regidx Rs5 = (disk_base : mword 64))
        by (rewrite (Hcs1 Rs5 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Hs5).
      destruct Hal as [Hal11 Hal12].
      (* the addresses of idx[0] and idx[1], off the frame pointer *)
      assert (Hidx0a : add_vec (M1 !!! Regidx Rs0)
                         (sign_extend' 64 (mword_of_int 4000 : mword 12))
                       = (pa_stk sp0 12 : mword 64))
        by (rewrite Hs01; apply vdrw_idx0_addr).
      assert (Hidx1s : add_vec (sp0 : mword 64)
                         (sign_extend' 64 (mword_of_int 4004 : mword 12))
                       = (pa_add (pa_stk sp0 12) 4 : mword 64)).
      { rewrite vdrwb_sext_4004 (vdrw_pa_add_moi (pa_stk sp0 12) 4).
        unfold pa_stk, add_vec_int. rewrite vdrw_av2.
        apply f_equal. apply bv_eq; vm_compute; reflexivity. }
      (* the common continuation: after the frees, the bundle is whole again *)
      iAssert ( ∀ (Mz : regfile),
                  ⌜forall r : mword 5, is_cs_idx r = true ->
                     Mz !!! Regidx r = M1 !!! Regidx r⌝ -∗
                  sie_cap_gpr γ Mz (K - 12)%nat -∗
                  cpu_own γ 1 eb (proc_addr j) C -∗
                  trap_csrs_pay 0 eb -∗
                  pc_is (mword_of_int (VRW + 0x094) : mword 64) -∗
                  own_ctx (p_context (proc_addr j)) -∗
                  ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) (proc_addr j) -∗
                  locked γk cpu_id -∗
                  free_bundles pd fr -∗
                  vdrw_scratch sp0 -∗
                  vdrw_p2_exit γ γk Φ γs j γd pd pav pu K eb C sp0 b wr sector m0 -∗
                  WP (Loop : expr riscv_lang) {{ Φ }})%I
        with "[Hpub Hlb Hcl Huidx Hflight Hparked Hring IH]" as "Hsleep".
      { iIntros (Mz) "%Hcsz Hcg Hown Hpay Hpc Hctx Hsched Htok Hbun Hscr Hexit".
        assert (Hhiz : vdrw_hi Mz m0)
          by (exact (vdrw_hi_frame M1 Mz m0 Hcsz
                       (vdrw_hi_frame1 M M1 m0 Rs2 ltac:(vm_compute; reflexivity)
                          Hcs1 Hhi))).
        (* the register facts at Mz *)
        assert (Hspz : Mz !!! Regidx csp_rs1 = pa_stk sp0 12)
          by (rewrite (Hcsz csp_rs1 ltac:(vm_compute; reflexivity)); exact Hsp1).
        assert (Hs0z : Mz !!! Regidx Rs0 = (sp0 : mword 64))
          by (rewrite (Hcsz Rs0 ltac:(vm_compute; reflexivity)); exact Hs01).
        assert (Hs3z : Mz !!! Regidx Rs3 = (b : mword 64))
          by (rewrite (Hcsz Rs3 ltac:(vm_compute; reflexivity)); exact Hs31).
        assert (Hs6z : Mz !!! Regidx Rs6 = wr)
          by (rewrite (Hcsz Rs6 ltac:(vm_compute; reflexivity)); exact Hs61).
        assert (Hs7z : Mz !!! Regidx Rs7 = sector)
          by (rewrite (Hcsz Rs7 ltac:(vm_compute; reflexivity)); exact Hs71).
        assert (Htpz : Mz !!! Regidx Rtp = cid_word)
          by (rewrite (Hcsz Rtp ltac:(vm_compute; reflexivity)); exact Htp1).
        assert (Hs1z : Mz !!! Regidx Rs1 = (mword_of_int 8 : mword 64))
          by (rewrite (Hcsz Rs1 ltac:(vm_compute; reflexivity)); exact Hs11).
        assert (Hs4z : Mz !!! Regidx Rs4 = (mword_of_int (Z.of_nat 3) : mword 64))
          by (rewrite (Hcsz Rs4 ltac:(vm_compute; reflexivity)); exact Hs41).
        assert (Hs5z : Mz !!! Regidx Rs5 = (disk_base : mword 64))
          by (rewrite (Hcsz Rs5 ltac:(vm_compute; reflexivity)); exact Hs51).
        (* ---- +0x094 / +0x098  a1 := &disk.vdisk_lock ---- *)
        iApply (wp_auipc_s_sconf γ Φ (mword_of_int (VRW + 0x094) : mword 64) Ra1
                  (mword_of_int 30 : mword 20) Mz (K - 12)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  with "Hcg Hpc Hi094 [-]").
        iIntros "Hcg Hpc".
        set (B1 := <[Regidx Ra1 := regval_into_reg
                      (add_vec (mword_of_int (VRW + 0x094) : mword 64)
                               (auipc_off (mword_of_int 30 : mword 20)))]> Mz).
        change (<[Regidx Ra1 := regval_into_reg
                      (add_vec (mword_of_int (VRW + 0x094) : mword 64)
                               (auipc_off (mword_of_int 30 : mword 20)))]> Mz) with B1.
        assert (Hp098 : add_vec_int (mword_of_int (VRW + 0x094) : mword 64) 4
                        = mword_of_int (VRW + 0x098))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp098) in "Hpc".
        iApply (wp_addi4_s_sconf γ Φ (mword_of_int (VRW + 0x098) : mword 64) Ra1 Ra1
                  (mword_of_int 3420 : mword 12) B1 (K - 12)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  with "Hcg Hpc Hi098 [-]").
        iIntros "Hcg Hpc".
        set (B2 := <[Regidx Ra1 := regval_into_reg
                      (add_vec (B1 !!! Regidx Ra1)
                         (sign_extend' 64 (mword_of_int 3420 : mword 12)))]> B1).
        change (<[Regidx Ra1 := regval_into_reg
                      (add_vec (B1 !!! Regidx Ra1)
                         (sign_extend' 64 (mword_of_int 3420 : mword 12)))]> B1) with B2.
        assert (HB2a1 : B2 !!! Regidx Ra1 = (d_lock : mword 64)).
        { rewrite /B2 upd_eq /B1 upd_eq.
          unfold d_lock, disk_base, pa_add, add_vec_int.
          apply bv_eq; vm_compute; reflexivity. }
        assert (Hp09c : add_vec_int (mword_of_int (VRW + 0x098) : mword 64) 4
                        = mword_of_int (VRW + 0x09c))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp09c) in "Hpc".
        (* ---- +0x09c / +0x0a0  a0 := &disk.free[0] ---- *)
        iApply (wp_auipc_s_sconf γ Φ (mword_of_int (VRW + 0x09c) : mword 64) Ra0
                  (mword_of_int 30 : mword 20) B2 (K - 12)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  with "Hcg Hpc Hi09c [-]").
        iIntros "Hcg Hpc".
        set (B3 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (mword_of_int (VRW + 0x09c) : mword 64)
                               (auipc_off (mword_of_int 30 : mword 20)))]> B2).
        change (<[Regidx Ra0 := regval_into_reg
                      (add_vec (mword_of_int (VRW + 0x09c) : mword 64)
                               (auipc_off (mword_of_int 30 : mword 20)))]> B2) with B3.
        assert (Hp0a0 : add_vec_int (mword_of_int (VRW + 0x09c) : mword 64) 4
                        = mword_of_int (VRW + 0x0a0))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp0a0) in "Hpc".
        iApply (wp_addi4_s_sconf γ Φ (mword_of_int (VRW + 0x0a0) : mword 64) Ra0 Ra0
                  (mword_of_int 3140 : mword 12) B3 (K - 12)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  with "Hcg Hpc Hi0a0 [-]").
        iIntros "Hcg Hpc".
        set (B4 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (B3 !!! Regidx Ra0)
                         (sign_extend' 64 (mword_of_int 3140 : mword 12)))]> B3).
        change (<[Regidx Ra0 := regval_into_reg
                      (add_vec (B3 !!! Regidx Ra0)
                         (sign_extend' 64 (mword_of_int 3140 : mword 12)))]> B3) with B4.
        assert (Hp0a4 : add_vec_int (mword_of_int (VRW + 0x0a0) : mword 64) 4
                        = mword_of_int (VRW + 0x0a4))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp0a4) in "Hpc".
        (* ---- +0x0a4  jal sleep ---- *)
        iApply (wp_jal_s_sconf γ Φ (mword_of_int (VRW + 0x0a4) : mword 64) Rra
                  (mword_of_int 2082578 : mword 21) B4 (K - 12)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi0a4 [-]").
        iIntros "Hcg Hpc".
        set (B5 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (VRW + 0x0a4) : mword 64) 4)]> B4).
        change (<[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (VRW + 0x0a4) : mword 64) 4)]> B4) with B5.
        assert (Hjsl : add_vec (mword_of_int (VRW + 0x0a4) : mword 64)
                         (sign_extend' 64 (mword_of_int 2082578 : mword 21))
                       = mword_of_int KernelSyms.sleep)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjsl) in "Hpc".
        assert (HB5tp : B5 !!! Regidx Rtp = cid_word).
        { rewrite /B5 upd_ne; [| reg_neq]. rewrite /B4 upd_ne; [| reg_neq].
          rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_ne; [| reg_neq].
          rewrite /B1 upd_ne; [| reg_neq]. exact Htpz. }
        assert (HB5a1 : add_vec (B5 !!! Regidx Ra1)
                          (sign_extend' 64 (mword_of_int 0 : mword 12))
                        = (d_lock : mword 64)).
        { rewrite /B5 upd_ne; [| reg_neq]. rewrite /B4 upd_ne; [| reg_neq].
          rewrite /B3 upd_ne; [| reg_neq]. rewrite HB2a1. apply vdrw_addv_sext0. }
        assert (HB5ra : B5 !!! Regidx Rra
                        = add_vec_int (mword_of_int (VRW + 0x0a4) : mword 64) 4)
          by (rewrite /B5; apply upd_eq).
        (* re-close the lock's resource: the bundle is whole again *)
        iAssert (disk_res γd pd pav pu)
          with "[Hpub Hlb Hcl Huidx Hflight Hparked Hbun Hring]" as "HR".
        { iApply (vdrw_body_close γd pd pav pu np nr fl pk tr fr).
          rewrite /vdrw_body.
          iFrame "Hpub Hlb Hcl Huidx Hflight Hparked Hbun Hring".
          iPureIntro. split_and!; assumption. }
        iApply (Sleep.wp_sleep_sconf γ Φ γs j γl γk d_lock "virtio_disk"%string
                  (disk_res γd pd pav pu) B5 (K - 12)%nat eb C
                  HB5tp Hj Hjl HB5a1 (vdrw_K22 K HK)
                  with "Hcg Hown Hpay Htext Hpc Hpinv Hlk Htok HR Hpanic Hctx Hsched [-]").
        iIntros (Mf) "%Hcsf Hcg Hown Hpay Hpc Htok HR Hctx Hsched".
        assert (Hret : ret_pc (B5 !!! Regidx Rra) = mword_of_int (VRW + 0x0a8))
          by (rewrite HB5ra; apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hret) in "Hpc".
        (* ---- the back edge ---- *)
        iApply ("IH" $! Mf with "[%] Hcg Hown Hpay Hpc Hctx Hsched Htok HR Hscr Hexit").
        unfold vdrw_regs. split_and!.
        - rewrite (proj1 Hcsf).
          rewrite /B5 upd_ne; [| reg_neq]. rewrite /B4 upd_ne; [| reg_neq].
          rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_ne; [| reg_neq].
          rewrite /B1 upd_ne; [| reg_neq]. exact Hspz.
        - rewrite (callee_saved_lookup Hcsf Rs0 ltac:(vm_compute; reflexivity)).
          rewrite /B5 upd_ne; [| reg_neq]. rewrite /B4 upd_ne; [| reg_neq].
          rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_ne; [| reg_neq].
          rewrite /B1 upd_ne; [| reg_neq]. exact Hs0z.
        - rewrite (callee_saved_lookup Hcsf Rs3 ltac:(vm_compute; reflexivity)).
          rewrite /B5 upd_ne; [| reg_neq]. rewrite /B4 upd_ne; [| reg_neq].
          rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_ne; [| reg_neq].
          rewrite /B1 upd_ne; [| reg_neq]. exact Hs3z.
        - rewrite (callee_saved_lookup Hcsf Rs6 ltac:(vm_compute; reflexivity)).
          rewrite /B5 upd_ne; [| reg_neq]. rewrite /B4 upd_ne; [| reg_neq].
          rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_ne; [| reg_neq].
          rewrite /B1 upd_ne; [| reg_neq]. exact Hs6z.
        - rewrite (callee_saved_lookup Hcsf Rs7 ltac:(vm_compute; reflexivity)).
          rewrite /B5 upd_ne; [| reg_neq]. rewrite /B4 upd_ne; [| reg_neq].
          rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_ne; [| reg_neq].
          rewrite /B1 upd_ne; [| reg_neq]. exact Hs7z.
        - rewrite (callee_saved_lookup Hcsf Rtp ltac:(vm_compute; reflexivity)).
          exact HB5tp.
        - rewrite (callee_saved_lookup Hcsf Rs1 ltac:(vm_compute; reflexivity)).
          rewrite /B5 upd_ne; [| reg_neq]. rewrite /B4 upd_ne; [| reg_neq].
          rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_ne; [| reg_neq].
          rewrite /B1 upd_ne; [| reg_neq]. exact Hs1z.
        - rewrite (callee_saved_lookup Hcsf Rs4 ltac:(vm_compute; reflexivity)).
          rewrite /B5 upd_ne; [| reg_neq]. rewrite /B4 upd_ne; [| reg_neq].
          rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_ne; [| reg_neq].
          rewrite /B1 upd_ne; [| reg_neq]. exact Hs4z.
        - rewrite (callee_saved_lookup Hcsf Rs5 ltac:(vm_compute; reflexivity)).
          rewrite /B5 upd_ne; [| reg_neq]. rewrite /B4 upd_ne; [| reg_neq].
          rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_ne; [| reg_neq].
          rewrite /B1 upd_ne; [| reg_neq]. exact Hs5z.
        - exact (vdrw_hi_cs B5 Mf m0 Hcsf ltac:(vdrw_hi_peel; exact Hhiz)). }
      (* ---- +0x07a  bge x0,s2 : nothing allocated? ---- *)
      rewrite /P1.vdrw_alloc_fail.
      iDestruct "Hfail" as "[H0|[H1|H2]]".
      - (* ---------------- s2 = 0: no descriptor to give back ------------- *)
        iDestruct "H0" as "(%Hs2 & Hbun & Hidx)".
        iApply (wp_bge_x0_taken_s_sconf γ Φ (mword_of_int (VRW + 0x07a) : mword 64)
                  (mword_of_int 26 : mword 13) Rs2 M1 (K - 12)%nat
                  ltac:(vm_compute; discriminate)
                  ltac:(rewrite Hs2; exact vdrwb_bge0)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi07a [-]").
        iNext. iIntros "Hcg Hpc".
        assert (Hb094 : add_vec (mword_of_int (VRW + 0x07a) : mword 64)
                          (sign_extend' 64 (mword_of_int 26 : mword 13))
                        = mword_of_int (VRW + 0x094))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hb094) in "Hpc".
        iDestruct "Hidx" as (v0 v1 v2) "Hidx".
        iApply ("Hsleep" $! M1 with
                  "[%] Hcg Hown Hpay Hpc Hctx Hsched Htok Hbun
                   [Hidx] Hexit").
        { intros r Hr. reflexivity. }
        iApply (vdrw_idx_join sp0 v0 v1 v2 Hal11 Hal12 with "Hidx").
      - (* ---------------- s2 = 1: one descriptor to give back ------------ *)
        iDestruct "H1" as (h) "(%Hh & Hbun & Hbh & Hidx)".
        destruct Hh as (Hh8 & Hfrh & Hs2).
        iApply (wp_bge_x0_fall_s_sconf γ Φ (mword_of_int (VRW + 0x07a) : mword 64)
                  (mword_of_int 26 : mword 13) Rs2 M1 (K - 12)%nat
                  ltac:(vm_compute; discriminate)
                  ltac:(rewrite Hs2; exact vdrwb_bge1)
                  with "Hcg Hpc Hi07a [-]").
        iIntros "Hcg Hpc".
        assert (Hp07e : add_vec_int (mword_of_int (VRW + 0x07a) : mword 64) 4
                        = mword_of_int (VRW + 0x07e))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp07e) in "Hpc".
        iDestruct "Hidx" as (v1 v2) "Hidx".
        iDestruct "Hidx" as "(Hx0 & Hx1 & Hx2 & Hxp)".
        iApply (wp_vdrw_free_at γ Φ γs pd h (fr_upd fr h false) M1 (K - 12)%nat
                  eb (proc_addr j) C (pa_stk sp0 12) 0x07e
                  (mword_of_int 4000 : mword 12) (mword_of_int 2096448 : mword 21)
                  (vdrwb_K20 K HK) Hh8 (fr_upd_eq fr h false) Hlen Htp1 Hidx0a
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hown Htext Hpc Hpanic Hpinv Hdp Hi07e Hi082 Hx0 Hbun Hbh [-]").
        iIntros (M2) "%Hcs2 Hcg Hown Hpc Hx0 Hbun".
        (* +0x086  c.li a5,1 *)
        iApply (wp_cli_s_sconf γ Φ (mword_of_int (VRW + 0x086) : mword 64) Ra5
                  (mword_of_int 1 : mword 6) (mword_of_int (Z.of_nat 1) : mword 64)
                  M2 (K - 12)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  vdrwb_li1 with "Hcg Hpc Hi086 [-]").
        iIntros "Hcg Hpc".
        set (F1 := <[Regidx Ra5 := regval_into_reg
                      (mword_of_int (Z.of_nat 1) : mword 64)]> M2).
        change (<[Regidx Ra5 := regval_into_reg
                      (mword_of_int (Z.of_nat 1) : mword 64)]> M2) with F1.
        assert (Hp088 : add_vec_int (mword_of_int (VRW + 0x086) : mword 64) 2
                        = mword_of_int (VRW + 0x088))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp088) in "Hpc".
        assert (HF1a5 : F1 !!! Regidx Ra5 = (mword_of_int (Z.of_nat 1) : mword 64))
          by (rewrite /F1; apply upd_eq).
        assert (HF1s2 : F1 !!! Regidx Rs2 = (mword_of_int (Z.of_nat 1) : mword 64)).
        { rewrite /F1 upd_ne; [| reg_neq].
          rewrite (Hcs2 Rs2 ltac:(vm_compute; reflexivity)). exact Hs2. }
        (* +0x088  bge a5,s2 : 1 >= 1, TAKEN *)
        iApply (wp_bge_taken_s_sconf γ Φ (mword_of_int (VRW + 0x088) : mword 64)
                  (mword_of_int 12 : mword 13) Rs2 Ra5 F1 (K - 12)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rewrite HF1a5 HF1s2; exact vdrwb_bge11)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi088 [-]").
        iNext. iIntros "Hcg Hpc".
        assert (Hb094' : add_vec (mword_of_int (VRW + 0x088) : mword 64)
                           (sign_extend' 64 (mword_of_int 12 : mword 13))
                         = mword_of_int (VRW + 0x094))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hb094') in "Hpc".
        iApply ("Hsleep" $! F1 with
                  "[%] Hcg Hown Hpay Hpc Hctx Hsched Htok [Hbun] [Hx0 Hx1 Hx2 Hxp] Hexit").
        { intros r Hr. rewrite /F1 upd_ne;
            [| apply not_eq_sym, is_cs_idx_true_neq;
               [vm_compute; reflexivity | exact Hr]].
          exact (Hcs2 r Hr). }
        { iApply (free_bundles_ext pd (fr_upd (fr_upd fr h false) h true) fr).
          { intros i _. destruct (Nat.eq_dec i h) as [->|Hne].
            - rewrite fr_upd_eq. symmetry. exact Hfrh.
            - rewrite (fr_upd_ne _ h i true Hne) (fr_upd_ne _ h i false Hne). reflexivity. }
          iExact "Hbun". }
        iApply (vdrw_idx_join sp0 (mword_of_int (Z.of_nat h)) v1 v2 Hal11 Hal12).
        rewrite /vdrw_idx. iFrame "Hx0 Hx1 Hx2 Hxp".
      - (* ---------------- s2 = 2: two descriptors to give back ----------- *)
        iDestruct "H2" as (h m2) "(%Hh & Hbun & Hbh & Hbm & Hidx)".
        destruct Hh as (Hh8 & Hm8 & Hhm & Hfrh & Hfrm & Hs2).
        iApply (wp_bge_x0_fall_s_sconf γ Φ (mword_of_int (VRW + 0x07a) : mword 64)
                  (mword_of_int 26 : mword 13) Rs2 M1 (K - 12)%nat
                  ltac:(vm_compute; discriminate)
                  ltac:(rewrite Hs2; exact vdrwb_bge2)
                  with "Hcg Hpc Hi07a [-]").
        iIntros "Hcg Hpc".
        assert (Hp07e : add_vec_int (mword_of_int (VRW + 0x07a) : mword 64) 4
                        = mword_of_int (VRW + 0x07e))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp07e) in "Hpc".
        iDestruct "Hidx" as (v2) "Hidx".
        iDestruct "Hidx" as "(Hx0 & Hx1 & Hx2 & Hxp)".
        (* the first free: descriptor h, whose cell the allocator cleared *)
        assert (Hfrh' : fr_upd (fr_upd fr h false) m2 false h = false)
          by (rewrite (fr_upd_ne _ m2 h false Hhm); apply fr_upd_eq).
        iApply (wp_vdrw_free_at γ Φ γs pd h
                  (fr_upd (fr_upd fr h false) m2 false) M1 (K - 12)%nat
                  eb (proc_addr j) C (pa_stk sp0 12) 0x07e
                  (mword_of_int 4000 : mword 12) (mword_of_int 2096448 : mword 21)
                  (vdrwb_K20 K HK) Hh8 Hfrh' Hlen Htp1 Hidx0a
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hown Htext Hpc Hpanic Hpinv Hdp Hi07e Hi082 Hx0 Hbun Hbh [-]").
        iIntros (M2) "%Hcs2 Hcg Hown Hpc Hx0 Hbun".
        (* +0x086  c.li a5,1 *)
        iApply (wp_cli_s_sconf γ Φ (mword_of_int (VRW + 0x086) : mword 64) Ra5
                  (mword_of_int 1 : mword 6) (mword_of_int (Z.of_nat 1) : mword 64)
                  M2 (K - 12)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  vdrwb_li1 with "Hcg Hpc Hi086 [-]").
        iIntros "Hcg Hpc".
        set (G1 := <[Regidx Ra5 := regval_into_reg
                      (mword_of_int (Z.of_nat 1) : mword 64)]> M2).
        change (<[Regidx Ra5 := regval_into_reg
                      (mword_of_int (Z.of_nat 1) : mword 64)]> M2) with G1.
        assert (Hp088 : add_vec_int (mword_of_int (VRW + 0x086) : mword 64) 2
                        = mword_of_int (VRW + 0x088))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp088) in "Hpc".
        assert (HG1a5 : G1 !!! Regidx Ra5 = (mword_of_int (Z.of_nat 1) : mword 64))
          by (rewrite /G1; apply upd_eq).
        assert (HG1s2 : G1 !!! Regidx Rs2 = (mword_of_int (Z.of_nat 2) : mword 64)).
        { rewrite /G1 upd_ne; [| reg_neq].
          rewrite (Hcs2 Rs2 ltac:(vm_compute; reflexivity)). exact Hs2. }
        assert (HG1s0 : G1 !!! Regidx Rs0 = (sp0 : mword 64)).
        { rewrite /G1 upd_ne; [| reg_neq].
          rewrite (Hcs2 Rs0 ltac:(vm_compute; reflexivity)). exact Hs01. }
        assert (HG1tp : G1 !!! Regidx Rtp = cid_word).
        { rewrite /G1 upd_ne; [| reg_neq].
          rewrite (Hcs2 Rtp ltac:(vm_compute; reflexivity)). exact Htp1. }
        (* +0x088  bge a5,s2 : 1 >= 2 is false, FALL THROUGH *)
        iApply (wp_bge_fall_s_sconf γ Φ (mword_of_int (VRW + 0x088) : mword 64)
                  (mword_of_int 12 : mword 13) Rs2 Ra5 G1 (K - 12)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rewrite HG1a5 HG1s2; exact vdrwb_bge12)
                  with "Hcg Hpc Hi088 [-]").
        iIntros "Hcg Hpc".
        assert (Hp08c : add_vec_int (mword_of_int (VRW + 0x088) : mword 64) 4
                        = mword_of_int (VRW + 0x08c))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp08c) in "Hpc".
        (* the second free: descriptor m2 *)
        assert (Hidx1a' : add_vec (G1 !!! Regidx Rs0)
                            (sign_extend' 64 (mword_of_int 4004 : mword 12))
                          = (pa_add (pa_stk sp0 12) 4 : mword 64))
          by (rewrite HG1s0; exact Hidx1s).
        assert (Hfrm' : fr_upd (fr_upd (fr_upd fr h false) m2 false) h true m2 = false).
        { rewrite (fr_upd_ne _ h m2 true (not_eq_sym Hhm)). apply fr_upd_eq. }
        iApply (wp_vdrw_free_at γ Φ γs pd m2
                  (fr_upd (fr_upd (fr_upd fr h false) m2 false) h true) G1 (K - 12)%nat
                  eb (proc_addr j) C (pa_add (pa_stk sp0 12) 4) 0x08c
                  (mword_of_int 4004 : mword 12) (mword_of_int 2096434 : mword 21)
                  (vdrwb_K20 K HK) Hm8 Hfrm' Hlen HG1tp Hidx1a'
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hown Htext Hpc Hpanic Hpinv Hdp Hi08c Hi090 Hx1 Hbun Hbm [-]").
        iIntros (M3) "%Hcs3 Hcg Hown Hpc Hx1 Hbun".
        iApply ("Hsleep" $! M3 with
                  "[%] Hcg Hown Hpay Hpc Hctx Hsched Htok [Hbun] [Hx0 Hx1 Hx2 Hxp] Hexit").
        { intros r Hr. rewrite (Hcs3 r Hr).
          rewrite /G1 upd_ne;
            [| apply not_eq_sym, is_cs_idx_true_neq;
               [vm_compute; reflexivity | exact Hr]].
          exact (Hcs2 r Hr). }
        { iApply (free_bundles_ext pd
                    (fr_upd (fr_upd (fr_upd (fr_upd fr h false) m2 false) h true) m2 true)
                    fr).
          { intros i _. destruct (Nat.eq_dec i m2) as [->|Hnem].
            - rewrite fr_upd_eq. symmetry. exact Hfrm.
            - rewrite (fr_upd_ne _ m2 i true Hnem).
              destruct (Nat.eq_dec i h) as [->|Hneh].
              + rewrite fr_upd_eq. symmetry. exact Hfrh.
              + rewrite (fr_upd_ne _ h i true Hneh) (fr_upd_ne _ m2 i false Hnem)
                        (fr_upd_ne _ h i false Hneh). reflexivity. }
          iExact "Hbun". }
        iApply (vdrw_idx_join sp0 (mword_of_int (Z.of_nat h))
                  (mword_of_int (Z.of_nat m2)) v2 Hal11 Hal12).
        rewrite /vdrw_idx. iFrame "Hx0 Hx1 Hx2 Hxp". }
    (* ---- +0x044  c.j -> +0x0a8 : enter the loop ---- *)
    iApply (wp_cj_s_sconf γ Φ (mword_of_int (VRW + 0x044) : mword 64)
              (sign_extend' 21 (concat_vec (mword_of_int 50 : mword 11) ('b"0")))
              A5 (K - 12)%nat ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi044 [-]").
    iNext. iIntros "Hcg Hpc".
    assert (Hj0a8 : add_vec (mword_of_int (VRW + 0x044) : mword 64)
                      (sign_extend' 64 (sign_extend' 21
                         (concat_vec (mword_of_int 50 : mword 11) ('b"0"))))
                    = mword_of_int (VRW + 0x0a8))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hj0a8) in "Hpc".
    iApply ("Hloop" $! A5 with "[%] Hcg Hown Hpay Hpc Hctx Hsched Htok HR Hscr Hexit").
    split_and!; [ exact HA5regs | exact HA5s1 | exact HA5s4 | exact HA5s5
                | vdrw_hi_peel; exact Hhi0 ].
  Qed.

End ProofVirtioDiskRwB.
End VirtioDiskRwRest.
