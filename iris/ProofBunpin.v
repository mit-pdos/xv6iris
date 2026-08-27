(* ProofBunpin.v -- bunpin over the SIE-agnostic sconf world.

     void bunpin(struct buf *b) { acquire(&bcache.lock); b->refcnt--; release; }

   bpin's mirror image, and the same twenty instructions with [c.addiw a5,-1]
   in place of [c.addiw a5,1].  What the caller brings is the reference itself,
   and that is what makes the DECREMENT safe with no run-time check:

   * [bref_tok_lookup] puts the buffer in the authority's domain with a
     [positive] count, so the loaded word is that count and the store cannot
     underflow past zero -- the C code's unguarded [--] is faithful precisely
     because a reference exists.

   * the reference's dev/blockno fraction rejoins the resource's retained
     share, and the Arc algebra's sole-reference law decides which of the two
     arms applies:

       count = 1        the reference held the WHOLE outstanding fraction
                        ([bref_tok_lookup]), so the returned q plus the
                        retained qr is exactly the 1/2 a free slot holds; the
                        entry disappears and the refcnt word is 0
       count = n+1      strict inclusion gives q < qt, hence qt - q = qr', and
                        the retainder grows to qr + q (tie qr'+(qr+q) = 1/2)

     The caller's [bslot] comes back out of the slot's own store in both arms
     (one unit per outstanding reference), which is the conservation law that
     keeps the count a faithful int.

   As in ProofBpin the two arms are joined BEFORE the load, as one
   [∃ cw, brefcnt k ↦₄ cw ∗ (brefcnt k ↦₄ decr32 cw ==∗ bcache_res ∗ bslot)],
   so the instruction stream is proved once over an abstract count word.

   EXPLICIT-CPUID NOTE (same shape as ProofFiledup.v): the prologue (through
   [jal acquire]) and the epilogue (from release's return through [ret]) run
   at bunpin's own GENERIC [b], each plain instruction threading a FRESH hart
   and [cpu_own] moved across each stretch with ONE [cpu_own_transport] call.
   The critical section (acquire's return through release's call) runs at the
   LITERAL [false] SIE state acquire hands back, so [rewrite wp_next_off]
   collapses each of its steps with no hart threading.  [SpecRelease.v]'s
   entry-side tp premise is gone (HartTp.v -- the map's tp slot is ignored),
   so the map is handed to release as-is; release's derived exit index is
   absorbed by [sie_b_agree]'s [Houtb], read once at function entry. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants own.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvModelBytes.
Require Import RegFile.
Require Import HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import WpPushOffBridges.
Require Import IntrDefs.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import CpuOwn.
Require Import BufOwn BcacheInv BioInv.
Require Import CodeBpin.
Require Import SpecAcquire SpecRelease.
Require Import SpecBunpin.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(*  Pure fraction arithmetic (over Qp variables, so no solver ever runs *)
(*  inside the WP context).                                             *)
(* ------------------------------------------------------------------ *)

(* the last reference held the whole outstanding share, so the slot's cells
   are whole again. *)
Local Lemma bu_last_tie (qt qr : Qp) :
  (qt + qr)%Qp = (1/2)%Qp -> (qr + qt)%Qp = (1/2)%Qp.
Proof. intro H. by rewrite Qp.add_comm. Qed.

(* a survivor decrement: what leaves the entry joins the retainder. *)
Local Lemma bu_decr_tie (qt qr q qr' : Qp) :
  (qt + qr)%Qp = (1/2)%Qp -> qt = (q + qr')%Qp -> (qr' + (qr + q))%Qp = (1/2)%Qp.
Proof.
  intros Htie Hsub. rewrite -Htie Hsub.
  rewrite (Qp.add_comm qr q) Qp.add_assoc (Qp.add_comm qr' q). reflexivity.
Qed.

Module BunpinProof (Acquire : ACQUIRE) (Release : RELEASE) : BUNPIN.

Section ProofBunpin.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.


  Notation Rra  := (mword_of_int 1 : mword 5).
  Notation Rs0  := (mword_of_int 8 : mword 5).
  Notation Rs1  := (mword_of_int 9 : mword 5).
  Notation Ra0  := (mword_of_int 10 : mword 5).
  Notation Ra5  := (mword_of_int 15 : mword 5).
  Notation Rtp  := (mword_of_int 4 : mword 5).

  Local Ltac regne := reg_ne_side.

  (* [b] (from [sie_cap_gpr]'s arm) and [n],[eb] (from [cpu_own]'s count) are
     two independent presentations of the same SIE state; see
     ProofFiledup.v's identical helper for the full comment. *)
  Local Lemma sie_b_agree (m : regfile) (n K0 : nat) (eb b : bool) (p : mword 64) (lks : gset string) :
    sie_cap_gpr KT1 m K0 b p -∗ cpu_own n eb p b lks -∗
    ⌜ b = match n with O => eb | S _ => false end ⌝.
  Proof.
    iIntros "Hcg Hcnt". destruct b.
    - iDestruct "Hcnt" as "%Hb". destruct Hb as (-> & -> & _). done.
    - destruct n as [|n']; [ | done ].
      iDestruct "Hcnt" as "[_ Hint]".
      iDestruct "Hcg" as "(_ & _ & (_ & _ & Harm & _) & _)".
      iDestruct (ghost_var_agree with "Harm Hint") as %Heq.
      destruct eb; [ exfalso | done ].
      apply (f_equal (@bv_unsigned _)) in Heq. vm_compute in Heq. discriminate.
  Qed.

  (* the value [c.addiw a5,a5,-1] leaves for the store, as a function of the
     loaded word -- what joins the two arms of the critical section. *)
  Local Definition decr32 (cw : mword 32) : mword 32 :=
    trunc32 (sign_extend' 64 (subrange_vec_dec
      (add_vec (sign_extend' 64 cw)
               (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0)).

  (* on a POSITIVE count the borrow never happens: the stored word is the
     literal predecessor (pop_off's [c->noff--] arithmetic, at a [positive]). *)
  Local Lemma decr32_pos (cnt : positive) :
    (Z.pos cnt < 2 ^ 31)%Z ->
    decr32 (mword_of_int (Z.pos cnt) : mword 32) = (mword_of_int (Z.pos cnt - 1) : mword 32).
  Proof.
    intro Hb.
    pose (j := (Pos.to_nat cnt - 1)%nat).
    assert (Hj : Pos.to_nat cnt = S j)
      by (unfold j; pose proof (Pos2Nat.is_pos cnt); lia).
    assert (Hz : Z.pos cnt = Z.of_nat (S j))
      by (rewrite -Hj positive_nat_Z; reflexivity).
    assert (Hb' : (Z.of_nat (S j) < 2 ^ 31)%Z) by (rewrite -Hz; exact Hb).
    assert (Hnv : (mword_of_int (Z.pos cnt) : mword 32) = noff_val (S j))
      by (unfold noff_val; rewrite Hz; reflexivity).
    rewrite /decr32 Hnv (pop_nv1_pred j Hb') trunc32_sext /noff_val.
    assert (Heq : Z.of_nat j = (Z.pos cnt - 1)%Z) by lia.
    rewrite Heq. reflexivity.
  Qed.

  Lemma wp_bunpin_sconf (bn : bio_names) (V : bio_view Σ) (k : nat)
      (q : Qp) (dev bno : mword 32)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64) (K : nat) (b : bool) (lks : gset string)
    : wp_bunpin_sconf_body bn V k q dev bno m n eb p K b lks.
  Proof.
    cbv beta delta [wp_bunpin_sconf_body].
    intros pcE ret_tgt HK HnZ Hk Ha0 Hbelow.
    pose proof (locks_below_not_elem _ _ Hbelow) as Hfresh.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt #Htext Hpc #Hctx Href Hcont".
    iDestruct (sie_b_agree m n K eb b p lks with "Hcg Hcnt") as %Houtb.
    iDestruct (bio_ctx_lock with "Hctx") as "#Hlock".
    set (spr := add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    (* ===== PROLOGUE (generic [b]) ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m K 4 b
              ltac:(lia) Hpush with "Hcg Hpc []").
    { iApply (bui_00 with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
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
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.bunpin + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.bunpin + 0x02)) (mword_of_int 3 : mword 6) Rra
              R1 (K - 4)%nat vr24 b with "Hcg Hpc [] Hr24").
    { iApply (bui_02 with "Htext"). }
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    iEval (rgne) in "Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.bunpin + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.bunpin + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.bunpin + 0x04)) (mword_of_int 2 : mword 6) Rs0
              R1 (K - 4)%nat vr16 b with "Hcg Hpc [] Hr16").
    { iApply (bui_04 with "Htext"). }
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    iEval (rgne) in "Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.bunpin + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.bunpin + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.bunpin + 0x06)) (mword_of_int 1 : mword 6) Rs1
              R1 (K - 4)%nat vr8 b with "Hcg Hpc [] Hr8").
    { iApply (bui_06 with "Htext"). }
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    iEval (rgne) in "Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.bunpin + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.bunpin + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.bunpin + 0x08)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 R1 (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (bui_08 with "Htext"). }
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.bunpin + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.bunpin + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.mv s1,a0 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.bunpin + 0x0a)) Rs1 Ra0
              R2 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (bui_0a with "Htext"). }
    iIntros (CID6 Hs6) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R3 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (R2 !!! Regidx Ra0))]> R2).
    assert (HR3s1 : R3 !!! Regidx Rs1 = bnode k).
    { rewrite /R3 upd_eq. rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite Ha0. apply add_vec_zero_l. }
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.bunpin + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.bunpin + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c/+0x10 a0 := &bcache *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.bunpin + 0x0c)) Ra0 (mword_of_int 0x15 : mword 20)
              R3 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (bui_0c with "Htext"). }
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (R4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.bunpin + 0x0c) : mword 64)
                     (auipc_off (mword_of_int 0x15 : mword 20)))]> R3).
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.bunpin + 0x0c) : mword 64) 4 = mword_of_int (KernelSyms.bunpin + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.bunpin + 0x10)) Ra0 Ra0 (mword_of_int 0x4c6 : mword 12)
              R4 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (bui_10 with "Htext"). }
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (R4 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 1222 : mword 12)))]> R4).
    assert (HR5a0 : R5 !!! Regidx Ra0 = bcache_addr).
    { rewrite /R5 upd_eq /R4 upd_eq. rewrite /bcache_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.bunpin + 0x10) : mword 64) 4 = mword_of_int (KernelSyms.bunpin + 0x14))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* ===== +0x14 jal ra,acquire ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.bunpin + 0x14)) Rra (mword_of_int 0x1fde78 : mword 21)
              R5 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (bui_14 with "Htext"). }
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (mA := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.bunpin + 0x14) : mword 64) 4)]> R5).
    assert (Htgtacq : add_vec (mword_of_int (KernelSyms.bunpin + 0x14) : mword 64)
                        (sign_extend' 64 (mword_of_int 0x1fde78 : mword 21))
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
    assert (HmAra : mA !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.bunpin + 0x14) : mword 64) 4)
      by (rewrite /mA; apply upd_eq).
    (* [Hcnt] was introduced at the entry hart; nine plain instructions have
       moved us to CID9. *)
    iDestruct (cpu_own_transport CID CID9 n eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Acquire.wp_acquire_sconf KT1 (bn_lk bn) "bcache"%string (λ ξ : CtxId, bcache_res (XI := ξ) bn V) mA
              n eb p (K - 4)%nat b lks
              HnZ ltac:(lia) Hbelow
              with "Hcg Hcnt Htext Hpc [Hlock]").
    all: try lkbelow.
    { iEval (rewrite HmAa0). iExact "Hlock". }
    iIntros (CIDacq Hsacq ms macq) "%Hmsfacts Hcg Hpc %Hacqpins Htok HRres _ Hcnt Hpay".
    assert (Hpc18 : ret_pc (mA !!! Regidx Rra) = mword_of_int (KernelSyms.bunpin + 0x18)).
    { rewrite HmAra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc18) in "Hpc".
    pose proof Hacqpins as Hacqpins_cs.
    assert (Hmsp : macq !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hacqpins_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HmAsp).
    assert (Hms1 : macq !!! Regidx Rs1 = bnode k)
      by (rewrite (callee_saved_lookup Hacqpins_cs (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HmAs1).
    (* ===== the critical section (literal [false], no hart threading) ===== *)
    assert (Hs64 : sign_extend' 64 (mword_of_int 64 : mword 12) = (mword_of_int 64 : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iAssert (∃ cw : mword 32,
               brefcnt k ↦₄ cw ∗
               (brefcnt k ↦₄ (decr32 cw) ==∗ bcache_res bn V ∗ bslot))%I
      with "[HRres Href]" as (cw) "[Hcell Hclose]".
    { iDestruct "HRres" as (Mg ord devs bnos)
        "(Hauth & Hsauth & %Hdom & %Hord & %Hinj & %Hdev & Hlru & Hpool & Hslots)".
      iDestruct "Href" as "(Hrtok & Hrdev & Hrbno)".
      iDestruct (bref_tok_lookup with "Hauth Hrtok")
        as %(qt & cnt & HMk & Hsole & _ & Hltn).
      iDestruct (bio_slots_acc bn Mg devs bnos k Hk with "Hslots") as "[Hslot Hback]".
      iEval (rewrite /bio_slot_res HMk) in "Hslot".
      iDestruct "Hslot" as "(%Hcnt & Hcell & Hfd & Hqr)".
      iDestruct "Hqr" as (qr) "(%Htie & Hdev & Hbno)".
      iDestruct (ctx_word4_pointsto_agree with "Hrdev Hdev") as %->.
      iDestruct (ctx_word4_pointsto_agree with "Hrbno Hbno") as %->.
      iExists (mword_of_int (Z.pos cnt) : mword 32). iFrame "Hcell".
      iIntros "Hcell".
      iEval (rewrite (decr32_pos cnt Hcnt)) in "Hcell".
      destruct (decide (cnt = 1%positive)) as [->|Hne].
      - (* ---- the last reference: the entry disappears ---- *)
        assert (Hq : q = qt) by (apply Hsole; reflexivity). subst qt.
        iMod (bio_last_ref_step bn Mg k q HMk with "Hauth Hrtok") as "Hauth".
        assert (Hz0 : (Z.pos 1 - 1)%Z = 0%Z) by reflexivity.
        iEval (rewrite Hz0) in "Hcell".
        iAssert (b_dev (bpa k) ↦₄{DfracOwn (1/2)} (devs k))%I
          with "[Hrdev Hdev]" as "Hdev".
        { rewrite -(bu_last_tie q qr Htie) ctx_word4_pointsto_frac_split.
          iFrame "Hdev Hrdev". }
        iAssert (b_blockno (bpa k) ↦₄{DfracOwn (1/2)} (bnos k))%I
          with "[Hrbno Hbno]" as "Hbno".
        { rewrite -(bu_last_tie q qr Htie) ctx_word4_pointsto_frac_split.
          iFrame "Hbno Hrbno". }
        assert (Hdel : delete k Mg !! k = None) by apply lookup_delete.
        iAssert (bio_slot_res bn (delete k Mg) k (devs k) (bnos k))
          with "[Hcell Hdev Hbno]" as "Hslot".
        { rewrite /bio_slot_res Hdel. iFrame "Hcell Hdev Hbno". }
        iDestruct ("Hback" $! (delete k Mg) devs bnos with "[%] Hslot") as "Hslots".
        { intros j Hj. split_and!;
            [ rewrite lookup_delete_ne; [reflexivity | congruence] | reflexivity | reflexivity ]. }
        iModIntro. iSplitR "Hfd".
        + iExists (delete k Mg), ord, devs, bnos.
          iFrame "Hauth Hsauth".
          iSplitR.
          { iPureIntro. intros j Hj. apply Hdom.
            destruct (decide (j = k)) as [->|Hne].
            - rewrite Hdel in Hj. by destruct Hj as [x Hx].
            - rewrite lookup_delete_ne in Hj; [exact Hj | congruence]. }
          iSplitR; [iPureIntro; exact Hord|].
          iSplitR; [iPureIntro; exact Hinj|].
          iSplitR; [iPureIntro; exact Hdev|].
          iFrame "Hlru Hpool Hslots".
        + rewrite /bslot. change (Pos.to_nat 1) with 1%nat. iFrame "Hfd".
      - (* ---- survivors: the fraction returns to the retainder ---- *)
        assert (Hex : exists c', cnt = Pos.succ c').
        { exists (Pos.pred cnt). symmetry. by apply Pos.succ_pred. }
        destruct Hex as [cnt' Hcnt']. subst cnt.
        assert (Hlt : (q < qt)%Qp) by (apply Hltn; apply Pos.succ_not_1).
        assert (Hsub : exists qr', (qt - q)%Qp = Some qr').
        { apply Qp.lt_sum in Hlt as [r Hr]. exists r. by apply Qp.sub_Some. }
        destruct Hsub as [qr' Hsub].
        assert (Hsub' : qt = (q + qr')%Qp) by (by apply Qp.sub_Some).
        iMod (bio_decr_step bn Mg k q qt cnt' qr' HMk Hsub with "Hauth Hrtok") as "Hauth".
        assert (Hzp : (Z.pos (Pos.succ cnt') - 1)%Z = Z.pos cnt')
          by (rewrite Pos2Z.inj_succ; lia).
        iEval (rewrite Hzp) in "Hcell".
        iAssert (b_dev (bpa k) ↦₄{DfracOwn (qr + q)} (devs k))%I
          with "[Hrdev Hdev]" as "Hdev".
        { rewrite ctx_word4_pointsto_frac_split. iFrame "Hdev Hrdev". }
        iAssert (b_blockno (bpa k) ↦₄{DfracOwn (qr + q)} (bnos k))%I
          with "[Hrbno Hbno]" as "Hbno".
        { rewrite ctx_word4_pointsto_frac_split. iFrame "Hbno Hrbno". }
        assert (Hsucc : Pos.to_nat (Pos.succ cnt') = (Pos.to_nat cnt' + 1)%nat)
          by (rewrite Pos2Nat.inj_succ; lia).
        iEval (rewrite Hsucc bslots_op) in "Hfd".
        iDestruct "Hfd" as "[Hfd Hout]".
        iAssert (bio_slot_res bn (<[k := (qr', cnt')]> Mg) k (devs k) (bnos k))
          with "[Hcell Hfd Hdev Hbno]" as "Hslot".
        { rewrite /bio_slot_res lookup_insert.
          iSplitR. { iPureIntro. rewrite Pos2Z.inj_succ in Hcnt. lia. }
          iFrame "Hcell Hfd".
          iExists (qr + q)%Qp. iSplitR.
          { iPureIntro. exact (bu_decr_tie qt qr q qr' Htie Hsub'). }
          iFrame "Hdev Hbno". }
        iDestruct ("Hback" $! (<[k := (qr', cnt')]> Mg) devs bnos with "[%] Hslot") as "Hslots".
        { intros j Hj. split_and!;
            [ rewrite lookup_insert_ne; [reflexivity | congruence] | reflexivity | reflexivity ]. }
        iModIntro. iSplitR "Hout".
        + iExists (<[k := (qr', cnt')]> Mg), ord, devs, bnos.
          iFrame "Hauth Hsauth".
          iSplitR.
          { iPureIntro. intros j Hj.
            destruct (decide (j = k)) as [->|Hne2]; [exact Hk|].
            apply Hdom. by rewrite lookup_insert_ne in Hj. }
          iSplitR; [iPureIntro; exact Hord|].
          iSplitR; [iPureIntro; exact Hinj|].
          iSplitR; [iPureIntro; exact Hdev|].
          iFrame "Hlru Hpool Hslots".
        + rewrite /bslot. iFrame "Hout". }
    (* +0x18 c.lw a5,64(s1) *)
    assert (Hpa : add_vec (rget macq Rs1) (sign_extend' 64 (mword_of_int 64 : mword 12))
                  = brefcnt k).
    { rewrite (rget_ne macq Rs1 ltac:(vm_compute; discriminate)) Hms1 Hs64.
      rewrite /brefcnt /bpa /pa_add /add_vec_int. reflexivity. }
    iEval (rewrite -Hpa) in "Hcell".
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.bunpin + 0x18)) Ra5 Rs1 (mword_of_int 64 : mword 12)
              macq (trap_res b + (K - 4))%nat (cw : mword 32) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hcell").
    { iApply (bui_18 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hcell".
    iEval (rewrite Hpa) in "Hcell".
    set (D1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (cw : mword 32))]> macq).
    assert (HD1a5 : D1 !!! Regidx Ra5 = sign_extend' 64 (cw : mword 32))
      by (rewrite /D1; apply upd_eq).
    assert (HD1s1 : D1 !!! Regidx Rs1 = bnode k)
      by (rewrite /D1 upd_ne; [exact Hms1 | vm_compute; discriminate]).
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.bunpin + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.bunpin + 0x1a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a c.addiw a5,a5,-1 *)
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.bunpin + 0x1a)) Ra5 (mword_of_int 63 : mword 6)
              D1 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (bui_1a with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D2 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (subrange_vec_dec
                     (add_vec (D1 !!! Regidx Ra5)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))]> D1).
    assert (HD2s1 : D2 !!! Regidx Rs1 = bnode k)
      by (rewrite /D2 upd_ne; [exact HD1s1 | vm_compute; discriminate]).
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.bunpin + 0x1a) : mword 64) 2 = mword_of_int (KernelSyms.bunpin + 0x1c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* +0x1c c.sw a5,64(s1) : b->refcnt = refcnt-1 *)
    assert (Hpa2 : add_vec (rget D2 Rs1) (sign_extend' 64 (mword_of_int 64 : mword 12))
                   = brefcnt k).
    { rewrite (rget_ne D2 Rs1 ltac:(vm_compute; discriminate)) HD2s1 Hs64.
      rewrite /brefcnt /bpa /pa_add /add_vec_int. reflexivity. }
    iEval (rewrite -Hpa2) in "Hcell".
    iApply (wp_csw_s_sconf (mword_of_int (KernelSyms.bunpin + 0x1c)) Ra5 Rs1 (mword_of_int 64 : mword 12)
              D2 (trap_res b + (K - 4))%nat (cw : mword 32) false
              with "Hcg Hpc [] Hcell").
    { iApply (bui_1c with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hcell".
    iEval (rewrite Hpa2) in "Hcell".
    assert (Hstv : trunc32 (rget D2 Ra5) = decr32 (cw : mword 32)).
    { rewrite (rget_ne D2 Ra5 ltac:(vm_compute; discriminate)).
      rewrite /D2 upd_eq. unfold regval_into_reg. rewrite HD1a5. reflexivity. }
    iEval (rewrite Hstv) in "Hcell".
    iMod ("Hclose" with "Hcell") as "[HRres Hbslot]".
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.bunpin + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.bunpin + 0x1e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e/+0x22 a0 := &bcache ; +0x26 jal release *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.bunpin + 0x1e)) Ra0 (mword_of_int 0x15 : mword 20)
              D2 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (bui_1e with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (D3 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.bunpin + 0x1e) : mword 64)
                     (auipc_off (mword_of_int 0x15 : mword 20)))]> D2).
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.bunpin + 0x1e) : mword 64) 4 = mword_of_int (KernelSyms.bunpin + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.bunpin + 0x22)) Ra0 Ra0 (mword_of_int 0x4b4 : mword 12)
              D3 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (bui_22 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (D3 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 1204 : mword 12)))]> D3).
    assert (HD4a0 : D4 !!! Regidx Ra0 = bcache_addr).
    { rewrite /D4 upd_eq /D3 upd_eq. rewrite /bcache_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.bunpin + 0x22) : mword 64) 4 = mword_of_int (KernelSyms.bunpin + 0x26))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.bunpin + 0x26)) Rra (mword_of_int 0x1fdeee : mword 21)
              D4 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (bui_26 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (D5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.bunpin + 0x26) : mword 64) 4)]> D4).
    assert (Htgtrel : add_vec (mword_of_int (KernelSyms.bunpin + 0x26) : mword 64)
                        (sign_extend' 64 (mword_of_int 0x1fdeee : mword 21))
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
    assert (HD5ra : D5 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.bunpin + 0x26) : mword 64) 4)
      by (rewrite /D5; apply upd_eq).
    (* ===== +0x26 lands us in release; bunpin's own derived index [Houtb]
       absorbs release's [outb]. ===== *)
    (* the acquire handed the window index out as [trap_res b + N]; release
       wants it as [trap_res outb + N] with [outb = match n with O => eb
       | S _ => false end].  Those are the same bool -- [cpu_own] forces
       it -- so this is a pure re-spelling, and it is what makes the
       acquire/release pair compose back to [N]. *)
    iEval (rewrite Houtb) in "Hcg".
    iApply (Release.wp_release_sconf KT1 (bn_lk bn) bcache_addr "bcache"%string (λ ξ : CtxId, bcache_res (XI := ξ) bn V) D5
              n eb p (K - 4)%nat
              ({["bcache"]} ∪ lks)
              ltac:(rewrite HD5a0; apply bv_eq; vm_compute; reflexivity)
              ltac:(lia)
              with "Hcg Htext Hpc [Hlock] Htok HRres Hcnt Hpay").
    { iExact "Hlock". }
    iIntros (CIDr Hsr mr) "Hcg Hpc %Hrelpins Hcnt".
    (* bunpin is BALANCED: the set release hands back collapses to the entry
       [lks] -- [Hfresh] is what makes the singleton insert/delete cancel. *)
    assert (Hsetback : ({["bcache"]} ∪ lks) ∖ {["bcache"]} = lks)
      by (apply locks_add_del_below; lkbelow).
    iEval (rewrite Hsetback) in "Hcnt".
    iEval (rewrite <- Houtb) in "Hcg". iEval (rewrite <- Houtb) in "Hcnt".
    rewrite <- Houtb in Hsr.
    pose proof Hrelpins as Hrelpins_cs.
    assert (Hpc2a : ret_pc (D5 !!! Regidx Rra) = mword_of_int (KernelSyms.bunpin + 0x2a)).
    { rewrite HD5ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc2a) in "Hpc".
    (* ===== EPILOGUE (generic [b], via [Houtb]) ===== *)
    assert (Hmrsp : mr !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hrelpins_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HD5sp).
    iEval (rewrite HspR1) in "Hr24". iEval (rewrite HspR1) in "Hr16".
    iEval (rewrite HspR1) in "Hr8".  iEval (rewrite HspR1) in "Hg4".
    (* +0x2a c.ldsp ra,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.bunpin + 0x2a)) (mword_of_int 3 : mword 6) Rra
              mr (K - 4)%nat (R1 !!! Regidx Rra) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hr24]").
    { iApply (bui_2a with "Htext"). }
    { iEval (rewrite Hmrsp). iExact "Hr24". }
    iIntros (CIDe1 Hse1) "Hcg Hpc Hr24".
    iEval (rewrite Hmrsp) in "Hr24".
    set (P1 := <[Regidx Rra := regval_into_reg (R1 !!! Regidx Rra)]> mr).
    assert (HP1sp : P1 !!! Regidx csp_rs1 = spr)
      by (rewrite /P1 upd_ne; [exact Hmrsp | vm_compute; discriminate]).
    assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.bunpin + 0x2a) : mword 64) 2 = mword_of_int (KernelSyms.bunpin + 0x2c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.bunpin + 0x2c)) (mword_of_int 2 : mword 6) Rs0
              P1 (K - 4)%nat (R1 !!! Regidx Rs0) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hr16]").
    { iApply (bui_2c with "Htext"). }
    { iEval (rewrite HP1sp). iExact "Hr16". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hr16".
    iEval (rewrite HP1sp) in "Hr16".
    set (P2 := <[Regidx Rs0 := regval_into_reg (R1 !!! Regidx Rs0)]> P1).
    assert (HP2sp : P2 !!! Regidx csp_rs1 = spr)
      by (rewrite /P2 upd_ne; [exact HP1sp | vm_compute; discriminate]).
    assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.bunpin + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.bunpin + 0x2e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.bunpin + 0x2e)) (mword_of_int 1 : mword 6) Rs1
              P2 (K - 4)%nat (R1 !!! Regidx Rs1) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hr8]").
    { iApply (bui_2e with "Htext"). }
    { iEval (rewrite HP2sp). iExact "Hr8". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hr8".
    iEval (rewrite HP2sp) in "Hr8".
    set (P3 := <[Regidx Rs1 := regval_into_reg (R1 !!! Regidx Rs1)]> P2).
    assert (HP3sp : P3 !!! Regidx csp_rs1 = spr)
      by (rewrite /P3 upd_ne; [exact HP2sp | vm_compute; discriminate]).
    assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.bunpin + 0x2e) : mword 64) 2 = mword_of_int (KernelSyms.bunpin + 0x30))
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
    iAssert (stack_own (KTR := KT1) sp0 4) with "[Hr24 Hr16 Hr8 Hg4]" as "Hframe4".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hr24"; [iEval (rewrite -Hb1 HspR1); iExists _; iExact "Hr24"|].
      iSplitL "Hr16"; [iEval (rewrite -Hb2 HspR1); iExists _; iExact "Hr16"|].
      iSplitL "Hr8";  [iEval (rewrite -Hb3 HspR1); iExists _; iExact "Hr8"|].
      iSplitL "Hg4";  [iEval (rewrite -Hb4 HspR1); iExists _; iExact "Hg4"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.bunpin + 0x30)) (mword_of_int 2 : mword 6)
              P3 (K - 4)%nat 4 b Hpop with "Hcg Hpc [] Hframe4").
    { iApply (bui_30 with "Htext"). }
    iIntros (CIDe4 Hse4) "Hcg Hpc".
    assert (Hnk : ((K - 4) + 4)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg
      (add_vec (P3 !!! Regidx csp_rs1)
         (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P3) with P4.
    assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.bunpin + 0x30) : mword 64) 2 = mword_of_int (KernelSyms.bunpin + 0x32))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    assert (HP4ra : P4 !!! Regidx Rra = m !!! Regidx Rra).
    { rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_ne; [| vm_compute; discriminate].
      rewrite /P1 upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.bunpin + 0x32)) Rra P4 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc []").
    { iApply (bui_32 with "Htext"). }
    iIntros (CIDe5 Hse5) "Hcg Hpc".
    assert (Hretf : ret_pc (P4 !!! Regidx Rra) = ret_tgt) by (rewrite HP4ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* [cpu_own] was delivered at CIDr by release's own [wp_next]; five more
       plain instructions have moved us to CIDe5. *)
    iDestruct (cpu_own_transport CIDr CIDe5 n eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CIDe5 with "[]"); [ iPureIntro; wp_next_chain | ].
    iApply ("Hcont" $! P4 with "Hcg Hcnt Hpc [%] Hbslot").
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

End ProofBunpin.

End BunpinProof.
