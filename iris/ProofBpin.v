(* ProofBpin.v -- bpin over the SIE-agnostic sconf world.

     void bpin(struct buf *b) { acquire(&bcache.lock); b->refcnt++; release; }

   Straight-line, so the whole proof is about what happens to the bcache
   resource across the three instructions in the critical section.  Two things
   make the unchecked [refcnt++] provable, and both come from BioInv.v:

   * the count cannot overflow.  That is NOT a fact about the cache -- no
     unconditional increment preserves a bound -- it comes from the caller's
     [bslot]: the resource stores one slot per outstanding reference and the
     supply is fixed at BSLOTS, so [bslots_no_overflow] bounds the count and
     its successor far below what an [int] holds.  The caller's slot is
     absorbed into the slot's own store, which is what keeps the invariant
     re-established.

   * the minted reference's dev/blockno FRACTION comes out of the resource's
     retained share, never out of a caller's (unlike filedup, bpin's caller
     may hold no reference at all -- pinning at refcnt == 0 is legal).  So the
     two arms differ only in where the fraction is cut:

       M !! k = None       the slot holds the whole bcache half; cut it in
                           two, mint at 1/4 and retain 1/4 (tie 1/4+1/4=1/2)
       M !! k = Some(qt,n)  the slot retains qr with qt+qr = 1/2; halve qr,
                           mint at qr/2 and retain qr/2 (the retainder never
                           dies, which is what keeps every future pin legal)

   The two arms are joined BEFORE the load, as one
   [∃ cw, brefcnt k ↦₄ cw ∗ (brefcnt k ↦₄ incr32 cw ==∗ bcache_res ∗ bref)]:
   the three instructions and the whole release/epilogue tail are then proved
   once, over an abstract count word. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvModelBytes.
Require Import RiscvExtras.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import DiskPtsto.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import BufOwn BcacheInv BioInv.
Require Import CodeBpin.
Require Import SpecAcquire SpecRelease.
Require Import SpecBpin.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(*  Pure fraction arithmetic (stated over Qp variables, so no solver    *)
(*  ever runs inside the WP context).                                   *)
(* ------------------------------------------------------------------ *)

Local Lemma bp_quarter_half : ((1/4) + (1/4))%Qp = (1/2)%Qp.
Proof. compute_done. Qed.

Local Lemma bp_half_le_one : ((1/2) ≤ 1)%Qp.
Proof. compute_done. Qed.

Local Lemma bp_quarter_valid : ✓ (1/4)%Qp.
Proof. apply frac_valid. compute_done. Qed.

Local Lemma bp_div2_le (q : Qp) : (q/2 ≤ q)%Qp.
Proof. pose proof (Qp.le_add_l (q/2) (q/2)) as H. rewrite Qp.div_2 in H. exact H. Qed.

(* the minted fraction is legal: the entry's total only ever grows toward the
   1/2 the bcache resource started with. *)
Local Lemma bp_incr_valid (qt qr : Qp) :
  (qt + qr)%Qp = (1/2)%Qp -> ✓ (qt + qr/2)%Qp.
Proof.
  intro Htie. apply frac_valid.
  etrans; [| exact bp_half_le_one].
  rewrite -Htie. apply Qp.add_le_mono; [reflexivity | apply bp_div2_le].
Qed.

(* and the slot's cell tie survives the mint *)
Local Lemma bp_incr_tie (qt qr : Qp) :
  (qt + qr)%Qp = (1/2)%Qp -> ((qt + qr/2) + qr/2)%Qp = (1/2)%Qp.
Proof. intro Htie. rewrite -Qp.add_assoc Qp.div_2. exact Htie. Qed.

Module BpinProof (Acquire : ACQUIRE) (Release : RELEASE) : BPIN.

Section ProofBpin.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !bioG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Notation Rra  := (mword_of_int 1 : mword 5).
  Notation Rs0  := (mword_of_int 8 : mword 5).
  Notation Rs1  := (mword_of_int 9 : mword 5).
  Notation Ra0  := (mword_of_int 10 : mword 5).
  Notation Ra5  := (mword_of_int 15 : mword 5).
  Notation Rtp  := (mword_of_int 4 : mword 5).

  Local Ltac regne := reg_ne_side.

  (* the value the [c.addiw a5,a5,1] leaves for the store, as a function of
     the loaded word -- what joins the two arms of the critical section. *)
  Local Definition incr32 (cw : mword 32) : mword 32 :=
    trunc32 (sign_extend' 64 (subrange_vec_dec
      (add_vec (sign_extend' 64 cw)
               (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0)).

  Local Lemma incr32_pos (z : Z) :
    (0 <= z)%Z -> (z + 1 < 2 ^ 31)%Z ->
    incr32 (mword_of_int z : mword 32) = (mword_of_int (z + 1) : mword 32).
  Proof. intros H0 H1. rewrite /incr32. by apply moi32_storeval_succ. Qed.

  Lemma wp_bpin_sconf (bn : bio_names) (V : bio_view Σ) (k : nat)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64) (K : nat) (b : bool) (lks : gset string)
    : wp_bpin_sconf_body bn V k m n eb p K b lks.
  Proof.
    cbv beta delta [wp_bpin_sconf_body].
    intros pcE ret_tgt HK Hnoffpos Hk Ha0 Hbelow.
    pose proof (locks_below_not_elem _ _ Hbelow) as Hfresh.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt #Htext Hpc #Hctx Hbslot Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbeq.
    iDestruct (bio_ctx_lock with "Hctx") as "#Hlock".
    set (spr := add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iPoseProof (bpi_00 with "Htext") as "Hi00".
    iPoseProof (bpi_02 with "Htext") as "Hi02".
    iPoseProof (bpi_04 with "Htext") as "Hi04".
    iPoseProof (bpi_06 with "Htext") as "Hi06".
    iPoseProof (bpi_08 with "Htext") as "Hi08".
    iPoseProof (bpi_0a with "Htext") as "Hi0a".
    iPoseProof (bpi_0c with "Htext") as "Hi0c".
    iPoseProof (bpi_10 with "Htext") as "Hi10".
    iPoseProof (bpi_14 with "Htext") as "Hi14".
    (* ===== PROLOGUE ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m K 4 b
              ltac:(lia) Hpush with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (vr24) "Hr24". iDestruct "S2" as (vr16) "Hr16".
    iDestruct "S3" as (vr8)  "Hr8".  iDestruct "S4" as (vg4)  "Hg4".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".  iEval (rewrite -Hb4) in "Hg4".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.bpin + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.bpin + 0x02)) (mword_of_int 3 : mword 6) Rra
              R1 (K - 4)%nat vr24 b with "Hcg Hpc Hi02 Hr24").
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.bpin + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.bpin + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.bpin + 0x04)) (mword_of_int 2 : mword 6) Rs0
              R1 (K - 4)%nat vr16 b with "Hcg Hpc Hi04 Hr16").
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.bpin + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.bpin + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.bpin + 0x06)) (mword_of_int 1 : mword 6) Rs1
              R1 (K - 4)%nat vr8 b with "Hcg Hpc Hi06 Hr8").
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.bpin + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.bpin + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.bpin + 0x08)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 R1 (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.bpin + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.bpin + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.mv s1,a0 : the cursor register takes the argument *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.bpin + 0x0a)) Rs1 Ra0
              R2 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (R3 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (R2 !!! Regidx Ra0))]> R2).
    assert (HR3s1 : R3 !!! Regidx Rs1 = bnode k).
    { rewrite /R3 upd_eq. rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite Ha0. apply add_vec_zero_l. }
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.bpin + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.bpin + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c/+0x10 a0 := &bcache *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.bpin + 0x0c)) Ra0 (mword_of_int 0x15 : mword 20)
              R3 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (R4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.bpin + 0x0c) : mword 64)
                     (auipc_off (mword_of_int 0x15 : mword 20)))]> R3).
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.bpin + 0x0c) : mword 64) 4 = mword_of_int (KernelSyms.bpin + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.bpin + 0x10)) Ra0 Ra0 (mword_of_int 0x50a : mword 12)
              R4 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10").
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (R5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (R4 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 1290 : mword 12)))]> R4).
    assert (HR5a0 : R5 !!! Regidx Ra0 = bcache_addr).
    { rewrite /R5 upd_eq /R4 upd_eq. rewrite /bcache_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.bpin + 0x10) : mword 64) 4 = mword_of_int (KernelSyms.bpin + 0x14))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* ===== +0x14 jal ra,acquire ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.bpin + 0x14)) Rra (mword_of_int 0x1fdebc : mword 21)
              R5 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi14").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (mA := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.bpin + 0x14) : mword 64) 4)]> R5).
    assert (Htgtacq : add_vec (mword_of_int (KernelSyms.bpin + 0x14) : mword 64)
                        (sign_extend' 64 (mword_of_int 0x1fdebc : mword 21))
                      = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtacq) in "Hpc".
    assert (HmAsp : mA !!! Regidx csp_rs1 = spr).
    { rewrite /mA upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      exact HspR1. }
    assert (HmAa0 : mA !!! Regidx Ra0 = bcache_addr).
    { rewrite /mA upd_ne; [| vm_compute; discriminate]. exact HR5a0. }
    assert (HmAs1 : mA !!! Regidx Rs1 = bnode k).
    { rewrite /mA upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate]. exact HR3s1. }
    assert (HmAra : mA !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.bpin + 0x14) : mword 64) 4)
      by (rewrite /mA; apply upd_eq).
    iDestruct (cpu_own_transport CID CID9 n eb p b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Acquire.wp_acquire_sconf (bn_lk bn) "bcache"%string (bcache_res bn V) mA
              n eb p (K - 4)%nat b lks
              Hnoffpos ltac:(lia) Hbelow
              with "Hcg Hcnt Htext Hpc [Hlock]").
    all: try lkbelow.
    { iEval (rewrite HmAa0). iExact "Hlock". }
    iIntros (CID10 Hs10 ms macq) "%Hmsfacts Hcg Hpc %Hacqpins Htok HRres Hcnt Hpay".
    assert (Hpc18 : ret_pc (mA !!! Regidx Rra) = mword_of_int (KernelSyms.bpin + 0x18)).
    { rewrite HmAra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc18) in "Hpc".
    pose proof Hacqpins as Hacqpins_cs.
    assert (Hmsp : macq !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hacqpins_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HmAsp).
    assert (Hms1 : macq !!! Regidx Rs1 = bnode k)
      by (rewrite (callee_saved_lookup Hacqpins_cs (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HmAs1).
    (* ===== the critical section ===== *)
    (* the refcnt cell, at the address the [c.lw]/[c.sw] compute *)
    assert (Hs64 : sign_extend' 64 (mword_of_int 64 : mword 12) = (mword_of_int 64 : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    (* BOTH arms, joined: an abstract count word plus the wand that closes the
       resource back up around its successor. *)
    iAssert (∃ cw : mword 32,
               brefcnt k ↦₄ cw ∗
               (brefcnt k ↦₄ (incr32 cw) ==∗
                  bcache_res bn V ∗ ∃ (q : Qp) (dev bno : mword 32), bref bn k q dev bno))%I
      with "[HRres Hbslot]" as (cw) "[Hcell Hclose]".
    { iDestruct "HRres" as (Mg ord devs bnos)
        "(Hauth & Hsauth & %Hdom & %Hord & %Hinj & %Hdev & Hlru & Hpool & Hslots)".
      iDestruct (bio_slots_acc bn Mg devs bnos k Hk with "Hslots") as "[Hslot Hback]".
      destruct (Mg !! k) as [[qt cnt]|] eqn:HMk.
      - (* ---- busy buffer: halve the retained share ---- *)
        iEval (rewrite /bio_slot_res HMk) in "Hslot".
        iDestruct "Hslot" as "(%Hcnt & Hcell & Hfd & Hqr)".
        iDestruct "Hqr" as (qr) "(%Htie & Hdev & Hbno)".
        iDestruct (bslots_no_overflow with "Hsauth Hfd") as %[Hn1 Hn2].
        iExists (mword_of_int (Z.pos cnt) : mword 32). iFrame "Hcell".
        iIntros "Hcell".
        assert (Hinc : incr32 (mword_of_int (Z.pos cnt) : mword 32)
                       = (mword_of_int (Z.pos (Pos.succ cnt)) : mword 32)).
        { rewrite (incr32_pos (Z.pos cnt) ltac:(lia)
                     ltac:(pose proof Hn2 as Hx; rewrite Pos2Z.inj_succ in Hx; lia)).
          f_equal. rewrite Pos2Z.inj_succ. lia. }
        iEval (rewrite Hinc) in "Hcell".
        iMod (bio_incr_step bn Mg k qt cnt (qr/2)%Qp HMk (bp_incr_valid qt qr Htie)
                with "Hauth") as "[Hauth Htok]".
        iAssert (b_dev (bpa k) ↦₄{DfracOwn (qr/2)} (devs k) ∗
                 b_dev (bpa k) ↦₄{DfracOwn (qr/2)} (devs k))%I
          with "[Hdev]" as "[Hdev1 Hdev2]".
        { rewrite -word4_pointsto_frac_split Qp.div_2. iExact "Hdev". }
        iAssert (b_blockno (bpa k) ↦₄{DfracOwn (qr/2)} (bnos k) ∗
                 b_blockno (bpa k) ↦₄{DfracOwn (qr/2)} (bnos k))%I
          with "[Hbno]" as "[Hbno1 Hbno2]".
        { rewrite -word4_pointsto_frac_split Qp.div_2. iExact "Hbno". }
        assert (Hsucc : Pos.to_nat (Pos.succ cnt) = (Pos.to_nat cnt + 1)%nat)
          by (rewrite Pos2Nat.inj_succ; lia).
        iEval (rewrite /bslot) in "Hbslot".
        iAssert (bio_slot_res bn (<[k := ((qt + qr/2)%Qp, Pos.succ cnt)]> Mg) k (devs k) (bnos k))
          with "[Hcell Hfd Hbslot Hdev1 Hbno1]" as "Hslot".
        { rewrite /bio_slot_res lookup_insert.
          iSplitR. { iPureIntro. rewrite Pos2Z.inj_succ. rewrite Pos2Z.inj_succ in Hn2. lia. }
          iFrame "Hcell".
          iSplitL "Hfd Hbslot".
          { rewrite Hsucc bslots_op. iFrame "Hfd Hbslot". }
          iExists (qr/2)%Qp. iSplitR.
          { iPureIntro. exact (bp_incr_tie qt qr Htie). }
          iFrame "Hdev1 Hbno1". }
        iDestruct ("Hback" $! (<[k := ((qt + qr/2)%Qp, Pos.succ cnt)]> Mg) devs bnos
                     with "[%] Hslot") as "Hslots".
        { intros j Hj. split_and!;
            [ rewrite lookup_insert_ne; [reflexivity | congruence] | reflexivity | reflexivity ]. }
        iModIntro. iSplitR "Htok Hdev2 Hbno2".
        + iExists (<[k := ((qt + qr/2)%Qp, Pos.succ cnt)]> Mg), ord, devs, bnos.
          iFrame "Hauth Hsauth".
          iSplitR.
          { iPureIntro. intros j Hj.
            destruct (decide (j = k)) as [->|Hne]; [exact Hk|].
            apply Hdom. by rewrite lookup_insert_ne in Hj. }
          iSplitR; [iPureIntro; exact Hord|].
          iSplitR; [iPureIntro; exact Hinj|].
          iSplitR; [iPureIntro; exact Hdev|].
          iFrame "Hlru Hpool Hslots".
        + iExists (qr/2)%Qp, (devs k), (bnos k). rewrite /bref. iFrame "Htok Hdev2 Hbno2".
      - (* ---- free buffer: the first reference, cut 1/4 off the bcache half ---- *)
        iEval (rewrite /bio_slot_res HMk) in "Hslot".
        iDestruct "Hslot" as "(Hcell & Hdev & Hbno)".
        iExists (mword_of_int 0 : mword 32). iFrame "Hcell".
        iIntros "Hcell".
        assert (Hinc : incr32 (mword_of_int 0 : mword 32) = (mword_of_int 1 : mword 32)).
        { rewrite (incr32_pos 0 ltac:(lia) ltac:(vm_compute; reflexivity)). reflexivity. }
        iEval (rewrite Hinc) in "Hcell".
        iMod (bio_first_ref_step bn Mg k (1/4)%Qp HMk bp_quarter_valid
                with "Hauth") as "[Hauth Htok]".
        iAssert (b_dev (bpa k) ↦₄{DfracOwn (1/4)} (devs k) ∗
                 b_dev (bpa k) ↦₄{DfracOwn (1/4)} (devs k))%I
          with "[Hdev]" as "[Hdev1 Hdev2]".
        { rewrite -word4_pointsto_frac_split bp_quarter_half. iExact "Hdev". }
        iAssert (b_blockno (bpa k) ↦₄{DfracOwn (1/4)} (bnos k) ∗
                 b_blockno (bpa k) ↦₄{DfracOwn (1/4)} (bnos k))%I
          with "[Hbno]" as "[Hbno1 Hbno2]".
        { rewrite -word4_pointsto_frac_split bp_quarter_half. iExact "Hbno". }
        iEval (rewrite /bslot) in "Hbslot".
        iAssert (bio_slot_res bn (<[k := ((1/4)%Qp, 1%positive)]> Mg) k (devs k) (bnos k))
          with "[Hcell Hbslot Hdev1 Hbno1]" as "Hslot".
        { rewrite /bio_slot_res lookup_insert.
          iSplitR. { iPureIntro. vm_compute. reflexivity. }
          iFrame "Hcell".
          iSplitL "Hbslot". { change (Pos.to_nat 1) with 1%nat. iFrame "Hbslot". }
          iExists (1/4)%Qp. iSplitR; [iPureIntro; exact bp_quarter_half|].
          iFrame "Hdev1 Hbno1". }
        iDestruct ("Hback" $! (<[k := ((1/4)%Qp, 1%positive)]> Mg) devs bnos
                     with "[%] Hslot") as "Hslots".
        { intros j Hj. split_and!;
            [ rewrite lookup_insert_ne; [reflexivity | congruence] | reflexivity | reflexivity ]. }
        iModIntro. iSplitR "Htok Hdev2 Hbno2".
        + iExists (<[k := ((1/4)%Qp, 1%positive)]> Mg), ord, devs, bnos.
          iFrame "Hauth Hsauth".
          iSplitR.
          { iPureIntro. intros j Hj.
            destruct (decide (j = k)) as [->|Hne]; [exact Hk|].
            apply Hdom. by rewrite lookup_insert_ne in Hj. }
          iSplitR; [iPureIntro; exact Hord|].
          iSplitR; [iPureIntro; exact Hinj|].
          iSplitR; [iPureIntro; exact Hdev|].
          iFrame "Hlru Hpool Hslots".
        + iExists (1/4)%Qp, (devs k), (bnos k). rewrite /bref. iFrame "Htok Hdev2 Hbno2". }
    iPoseProof (bpi_18 with "Htext") as "Hi18".
    iPoseProof (bpi_1a with "Htext") as "Hi1a".
    iPoseProof (bpi_1c with "Htext") as "Hi1c".
    iPoseProof (bpi_1e with "Htext") as "Hi1e".
    iPoseProof (bpi_22 with "Htext") as "Hi22".
    iPoseProof (bpi_26 with "Htext") as "Hi26".
    (* +0x18 c.lw a5,64(s1) *)
    assert (Hpa : add_vec (rget macq Rs1) (sign_extend' 64 (mword_of_int 64 : mword 12))
                  = brefcnt k).
    { rgne. rewrite Hms1 Hs64. rewrite /brefcnt /bpa /pa_add /add_vec_int. reflexivity. }
    iEval (rewrite -Hpa) in "Hcell".
    iApply (wp_clw_s_sconf (mword_of_int (KernelSyms.bpin + 0x18)) Ra5 Rs1 (mword_of_int 64 : mword 12)
              macq (trap_res b + (K - 4))%nat (cw : mword 32) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18 Hcell").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hcell".
    iEval (rewrite Hpa) in "Hcell".
    set (D1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (cw : mword 32))]> macq).
    assert (HD1a5 : D1 !!! Regidx Ra5 = sign_extend' 64 (cw : mword 32))
      by (rewrite /D1; apply upd_eq).
    assert (HD1s1 : D1 !!! Regidx Rs1 = bnode k)
      by (rewrite /D1 upd_ne; [exact Hms1 | vm_compute; discriminate]).
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.bpin + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.bpin + 0x1a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a c.addiw a5,a5,1 *)
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.bpin + 0x1a)) Ra5 (mword_of_int 1 : mword 6)
              D1 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (D2 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (subrange_vec_dec
                     (add_vec (D1 !!! Regidx Ra5)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> D1).
    assert (HD2s1 : D2 !!! Regidx Rs1 = bnode k)
      by (rewrite /D2 upd_ne; [exact HD1s1 | vm_compute; discriminate]).
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.bpin + 0x1a) : mword 64) 2 = mword_of_int (KernelSyms.bpin + 0x1c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* +0x1c c.sw a5,64(s1) : b->refcnt = refcnt+1 *)
    assert (Hpa2 : add_vec (rget D2 Rs1) (sign_extend' 64 (mword_of_int 64 : mword 12))
                   = brefcnt k).
    { rgne. rewrite HD2s1 Hs64. rewrite /brefcnt /bpa /pa_add /add_vec_int. reflexivity. }
    iEval (rewrite -Hpa2) in "Hcell".
    iApply (wp_csw_s_sconf (mword_of_int (KernelSyms.bpin + 0x1c)) Ra5 Rs1 (mword_of_int 64 : mword 12)
              D2 (trap_res b + (K - 4))%nat (cw : mword 32) false
              with "Hcg Hpc Hi1c Hcell").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hcell".
    iEval (rewrite Hpa2) in "Hcell".
    iEval (rgne) in "Hcell".
    assert (Hstv : trunc32 (D2 !!! Regidx Ra5) = incr32 (cw : mword 32)).
    { rewrite /D2 upd_eq. unfold regval_into_reg. rewrite HD1a5. reflexivity. }
    iEval (rewrite Hstv) in "Hcell".
    iMod ("Hclose" with "Hcell") as "[HRres Href]".
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.bpin + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.bpin + 0x1e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e/+0x22 a0 := &bcache ; +0x26 jal release *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.bpin + 0x1e)) Ra0 (mword_of_int 0x15 : mword 20)
              D2 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (D3 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.bpin + 0x1e) : mword 64)
                     (auipc_off (mword_of_int 0x15 : mword 20)))]> D2).
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.bpin + 0x1e) : mword 64) 4 = mword_of_int (KernelSyms.bpin + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.bpin + 0x22)) Ra0 Ra0 (mword_of_int 0x4f8 : mword 12)
              D3 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (D4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (D3 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 1272 : mword 12)))]> D3).
    assert (HD4a0 : D4 !!! Regidx Ra0 = bcache_addr).
    { rewrite /D4 upd_eq /D3 upd_eq. rewrite /bcache_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.bpin + 0x22) : mword 64) 4 = mword_of_int (KernelSyms.bpin + 0x26))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.bpin + 0x26)) Rra (mword_of_int 0x1fdf32 : mword 21)
              D4 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi26").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (D5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.bpin + 0x26) : mword 64) 4)]> D4).
    assert (Htgtrel : add_vec (mword_of_int (KernelSyms.bpin + 0x26) : mword 64)
                        (sign_extend' 64 (mword_of_int 0x1fdf32 : mword 21))
                      = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtrel) in "Hpc".
    assert (HD5a0 : D5 !!! Regidx Ra0 = bcache_addr)
      by (rewrite /D5 upd_ne; [exact HD4a0 | vm_compute; discriminate]).
    assert (HD5thr : forall c : mword 5, is_cs_idx c = true ->
                       D5 !!! Regidx c = macq !!! Regidx c).
    { intros c Hcs.
      rewrite /D5 upd_ne; [| regne].
      rewrite /D4 upd_ne; [| regne].
      rewrite /D3 upd_ne; [| regne].
      rewrite /D2 upd_ne; [| regne].
      rewrite /D1 upd_ne; [reflexivity | regne]. }
    assert (HD5sp : D5 !!! Regidx csp_rs1 = spr)
      by (rewrite (HD5thr csp_rs1 ltac:(vm_compute; reflexivity)); exact Hmsp).
    assert (HD5ra : D5 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.bpin + 0x26) : mword 64) 4)
      by (rewrite /D5; apply upd_eq).
    (* the acquire handed the window index out as [trap_res b + N]; release
       wants it as [trap_res outb + N] with [outb = match n with O => eb
       | S _ => false end].  Those are the same bool -- [cpu_own] forces
       it -- so this is a pure re-spelling, and it is what makes the
       acquire/release pair compose back to [N]. *)
    iEval (rewrite -Hbeq) in "Hcg".
    iApply (Release.wp_release_sconf (bn_lk bn) bcache_addr "bcache"%string (bcache_res bn V) D5
              n eb p (K - 4)%nat
              ({["bcache"]} ∪ lks)
              ltac:(rewrite HD5a0; apply bv_eq; vm_compute; reflexivity)
              ltac:(lia)
              with "Hcg Htext Hpc [Hlock] Htok HRres Hcnt Hpay").
    { iExact "Hlock". }
    iIntros (CID11 Hs11 mr) "Hcg Hpc %Hrelpins Hcnt".
    (* bpin is BALANCED: the set release hands back collapses to the entry
       [lks] -- [Hfresh] is what makes the singleton insert/delete cancel. *)
    assert (Hsetback : ({["bcache"]} ∪ lks) ∖ {["bcache"]} = lks)
      by (apply locks_add_del_below; lkbelow).
    iEval (rewrite Hsetback) in "Hcnt".
    rewrite Hbeq in Hs11.
    iEval (rewrite Hbeq) in "Hcg". iEval (rewrite Hbeq) in "Hcnt".
    assert (Hpc2a : ret_pc (D5 !!! Regidx Rra) = mword_of_int (KernelSyms.bpin + 0x2a)).
    { rewrite HD5ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc2a) in "Hpc".
    pose proof Hrelpins as Hrelpins_cs.
    (* ===== EPILOGUE ===== *)
    iPoseProof (bpi_2a with "Htext") as "Hi2a".
    iPoseProof (bpi_2c with "Htext") as "Hi2c".
    iPoseProof (bpi_2e with "Htext") as "Hi2e".
    iPoseProof (bpi_30 with "Htext") as "Hi30".
    iPoseProof (bpi_32 with "Htext") as "Hi32".
    assert (Hmrsp : mr !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hrelpins_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HD5sp).
    iEval (rewrite HspR1) in "Hr24". iEval (rewrite HspR1) in "Hr16".
    iEval (rewrite HspR1) in "Hr8".  iEval (rewrite HspR1) in "Hg4".
    (* +0x2a c.ldsp ra,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.bpin + 0x2a)) (mword_of_int 3 : mword 6) Rra
              mr (K - 4)%nat (R1 !!! Regidx Rra) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2a [Hr24]").
    { iEval (rewrite Hmrsp). iExact "Hr24". }
    iIntros (CID12 Hs12) "Hcg Hpc Hr24".
    iEval (rewrite Hmrsp) in "Hr24".
    set (P1 := <[Regidx Rra := regval_into_reg (R1 !!! Regidx Rra)]> mr).
    assert (HP1sp : P1 !!! Regidx csp_rs1 = spr)
      by (rewrite /P1 upd_ne; [exact Hmrsp | vm_compute; discriminate]).
    assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.bpin + 0x2a) : mword 64) 2 = mword_of_int (KernelSyms.bpin + 0x2c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.bpin + 0x2c)) (mword_of_int 2 : mword 6) Rs0
              P1 (K - 4)%nat (R1 !!! Regidx Rs0) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2c [Hr16]").
    { iEval (rewrite HP1sp). iExact "Hr16". }
    iIntros (CID13 Hs13) "Hcg Hpc Hr16".
    iEval (rewrite HP1sp) in "Hr16".
    set (P2 := <[Regidx Rs0 := regval_into_reg (R1 !!! Regidx Rs0)]> P1).
    assert (HP2sp : P2 !!! Regidx csp_rs1 = spr)
      by (rewrite /P2 upd_ne; [exact HP1sp | vm_compute; discriminate]).
    assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.bpin + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.bpin + 0x2e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.bpin + 0x2e)) (mword_of_int 1 : mword 6) Rs1
              P2 (K - 4)%nat (R1 !!! Regidx Rs1) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2e [Hr8]").
    { iEval (rewrite HP2sp). iExact "Hr8". }
    iIntros (CID14 Hs14) "Hcg Hpc Hr8".
    iEval (rewrite HP2sp) in "Hr8".
    set (P3 := <[Regidx Rs1 := regval_into_reg (R1 !!! Regidx Rs1)]> P2).
    assert (HP3sp : P3 !!! Regidx csp_rs1 = spr)
      by (rewrite /P3 upd_ne; [exact HP2sp | vm_compute; discriminate]).
    assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.bpin + 0x2e) : mword 64) 2 = mword_of_int (KernelSyms.bpin + 0x30))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    set (P4 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P3 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P3).
    assert (Hwv : add_vec (P3 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HP3sp. unfold spr, sp0. apply frame_cancel_32. }
    assert (Hpop : P3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (P3 !!! Regidx csp_rs1)
                               (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HP3sp. unfold spr, sp0, pa_stk, add_vec_int.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hg4]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24"; [iEval (rewrite -Hb1 HspR1); iExists _; iExact "Hr24"|].
      iSplitL "Hr16"; [iEval (rewrite -Hb2 HspR1); iExists _; iExact "Hr16"|].
      iSplitL "Hr8";  [iEval (rewrite -Hb3 HspR1); iExists _; iExact "Hr8"|].
      iSplitL "Hg4";  [iEval (rewrite -Hb4 HspR1); iExists _; iExact "Hg4"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.bpin + 0x30)) (mword_of_int 2 : mword 6)
              P3 (K - 4)%nat 4 b Hpop with "Hcg Hpc Hi30 Hframe4").
    iIntros (CID15 Hs15) "Hcg Hpc".
    assert (Hnk : ((K - 4) + 4)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg
      (add_vec (P3 !!! Regidx csp_rs1)
         (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P3) with P4.
    assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.bpin + 0x30) : mword 64) 2 = mword_of_int (KernelSyms.bpin + 0x32))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    assert (HP4ra : P4 !!! Regidx Rra = m !!! Regidx Rra).
    { rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_ne; [| vm_compute; discriminate].
      rewrite /P1 upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.bpin + 0x32)) Rra P4 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi32").
    iIntros (CID16 Hs16) "Hcg Hpc".
    assert (Hretf : ret_pc (P4 !!! Regidx Rra) = ret_tgt) by (rewrite HP4ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* callee_saved m P4 *)
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> mword_of_int 8 -> c <> mword_of_int 9 ->
              P4 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9.
      rewrite /P4 upd_ne; [| regne].
      rewrite /P3 upd_ne; [| regne].
      rewrite /P2 upd_ne; [| regne].
      rewrite /P1 upd_ne; [| regne].
      rewrite (callee_saved_lookup Hrelpins_cs c Hcs).
      rewrite (HD5thr c Hcs).
      rewrite (callee_saved_lookup Hacqpins_cs c Hcs).
      rewrite /mA upd_ne; [| regne].
      rewrite /R5 upd_ne; [| regne].
      rewrite /R4 upd_ne; [| regne].
      rewrite /R3 upd_ne; [| regne].
      rewrite /R2 upd_ne; [| regne].
      rewrite /R1 upd_ne; [reflexivity | regne]. }
    iDestruct (cpu_own_transport CID11 CID16 n eb p b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CID16 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! P4 with "Hcg Hcnt Hpc [%] Href").
    unfold callee_saved.
    assert (Hc2 : P4 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1).
    { rewrite /P4 upd_eq. rewrite HP3sp. unfold regval_into_reg, spr, sp0.
      apply frame_cancel_32. }
    assert (Hc8 : P4 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5)).
    { rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (Hc9 : P4 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5)).
    { rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    repeat split;
      first [ exact Hc2 | exact Hc8 | exact Hc9
            | apply Hthread; vm_compute; first [reflexivity | discriminate] ].
  Qed.

End ProofBpin.

End BpinProof.
