(* ProofBrelse.v -- brelse over the SIE-agnostic sconf world.

     void brelse(struct buf *b) {
       if (!holdingsleep(&b->lock)) panic("brelse");
       releasesleep(&b->lock);
       acquire(&bcache.lock);
       b->refcnt--;
       if (b->refcnt == 0) { <unlink b>; <splice b after head> }
       release(&bcache.lock);
     }

   Four things carry the whole proof.

   * THE PARK, and it happens FIRST.  A blocked waiter's acquiresleep can
     return the moment the sleeplock frees, so the buffer's traveling content
     has to be back in the per-buffer escrow BEFORE releasesleep runs -- not at
     the refcnt decrement, which happens later and under a different lock.  So
     the very first frame store ([sd ra,24(sp)]) is proved with a mask-carrying
     store leaf ([wp_store_s_sconf_au], WpSconfMem.v) and [buf_escrow] opened
     around exactly that instruction: [BioInv.escrow_swap_park] deposits the
     valid/dev/buf_own bundle TOGETHER WITH the handle's payload (the disk
     cell and [bio_pay], re-packaged as the escrow's [buf_pay] at v = true --
     the blockno is covered, so the [decide] resolves left) and withdraws the
     chain's own reference plus the checkout token [bown].  Nothing physical
     happens to the buffer at that instruction; the swap is pure ghost
     bookkeeping that has to be atomic.  The body is NOT timeless (the view's
     [bv_clean]/[bv_dirty] are opaque), so the swap runs under the [iInv]'s
     [▷] and only the withdrawn bundle -- all timeless -- is stripped.

   * the panic arm is DEAD.  [bio_locked] carries the sleeplock's exclusive
     token and the lock's pid field, and the caller's own [p_pid] cell agrees
     with it, so holdingsleep's HOLDER variant returns 1.

   * the token withdrawn by the park is exactly what releasesleep's [R] is,
     and the reference withdrawn by the park is exactly what the decrement
     burns.  The two arms of the decrement differ only in where the fraction
     goes ([BioInv.bio_decr_step] / [bio_last_ref_step], as in bunpin) -- and
     in whether the LRU splice runs.

   * THE SPLICE.  On the zero arm the buffer is first UNLINKED from wherever
     it sits in the cycle and then spliced in after the head.  Both halves are
     BcacheInv.v's ([bcache_lru_unlink] and [bcache_lru_splice], the latter the
     very lemma binit's loop uses).  The
     order [ord] the bcache resource carries goes from [o1 ++ k :: o2] to
     [k :: (o1 ++ o2)], still a permutation of [seq 0 NBUF] by
     [Permutation_middle].

   The release/epilogue tail is reached from both arms, so it is factored as
   [brelse_tail] over an ARBITRARY arrival map (design/kernel-proofs.md's
   "a block the control flow re-joins" shape). *)
Set Printing Depth 40.
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
Require Import RiscvExtras.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import WpPushOffBridges.
Require Import KptGhost.
Require Import MinstretInv.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import CpuOwn.
Require Import FdSlots.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import KernelText.
Require Import InstrBytes.
Require Import DiskPtsto.
Require Import BufOwn BcacheInv BioInv.
Require Import CodeBrelse.
Require Import SpecHoldingsleep SpecReleasesleep.
Require Import SpecAcquire SpecRelease.
Require Import SpecBrelse.
From Kernel Require KernelSyms.
Require Import IrefSlots.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(*  Pure fraction arithmetic (over Qp variables, so no solver ever runs *)
(*  inside the WP context).                                             *)
(* ------------------------------------------------------------------ *)

(* the last reference held the whole outstanding share, so the slot's cells
   are whole again. *)
Local Lemma br_last_tie (qt qr : Qp) :
  (qt + qr)%Qp = (1/2)%Qp -> (qr + qt)%Qp = (1/2)%Qp.
Proof. intro H. by rewrite Qp.add_comm. Qed.

(* a survivor decrement: what leaves the entry joins the retainder. *)
Local Lemma br_decr_tie (qt qr q qr' : Qp) :
  (qt + qr)%Qp = (1/2)%Qp -> qt = (q + qr')%Qp -> (qr' + (qr + q))%Qp = (1/2)%Qp.
Proof.
  intros Htie Hsub. rewrite -Htie Hsub.
  rewrite (Qp.add_comm qr q) Qp.add_assoc (Qp.add_comm qr' q). reflexivity.
Qed.

Module BrelseProof (Hsl : HOLDINGSLEEP) (Rsl : RELEASESLEEP)
                   (Aq : ACQUIRE) (Rl : RELEASE) : BRELSE.

Section ProofBrelse.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Notation Rra  := (mword_of_int 1 : mword 5).
  Notation Rs0  := (mword_of_int 8 : mword 5).
  Notation Rs1  := (mword_of_int 9 : mword 5).
  Notation Ra0  := (mword_of_int 10 : mword 5).
  Notation Ra4  := (mword_of_int 14 : mword 5).
  Notation Ra5  := (mword_of_int 15 : mword 5).
  Notation Rs2  := (mword_of_int 18 : mword 5).
  Notation Rtp  := (mword_of_int 4 : mword 5).

  Local Ltac regne := reg_ne_side.

  (* Peel every [rget m k] in sight down to a raw [m !!! Regidx k].  Every
     register index brelse names is a concrete non-tp literal, so [rgne]'s
     side condition always closes and the loop terminates when no [rget] is
     left.  This is the consumer-side bridge the guide describes; it is
     wanted at both ends of every load/store leaf (the address AND the
     stored value are separate [rget]s at different indices). *)
  Local Ltac rgpeel := repeat rgne.


  (* ---------------------------------------------------------------- *)
  (*  The mask-carrying [c.sdsp] leaf: the escrow is opened around this  *)
  (*  ONE frame store.  A ~15-line wrapper over [wp_store_s_sconf_au],   *)
  (*  exactly as WpSconfLock.v's lock leaves are (durable-notes).        *)
  (*                                                                     *)
  (*  Its own [CID0] binder (the section's [CID] is the ENTRY hart, and   *)
  (*  the park runs several leaves later), and the stored value is        *)
  (*  [rget m0 rs2], NOT [m0 !!! Regidx rs2]: [rs2] is a VARIABLE index,  *)
  (*  so a raw read could name the register file's junk tp slot.  The     *)
  (*  base is [sp], a concrete non-tp index, so it stays a raw lookup     *)
  (*  (exactly as [wp_csdsp_s_sconf] spells it).                          *)
  (* ---------------------------------------------------------------- *)
  Local Lemma wp_csdsp_au_s_sconf `{CID0 : CpuId} 
      (pc : mword 64) (uimm : mword 6) (rs2 : mword 5) `{!SrcOk rs2}
      (m0 : regfile) (av : nat) (Ψ : iProp Σ) (Em : coPset)
      (b : bool) (pme : mword 64) :
    ↑kptN ⊆ Em ->
    sie_cap_gpr m0 av b pme -∗
    pc_is pc -∗
    instr pc true (STORE (zero_extend' 12 (concat_vec uimm ('b"000")), Regidx rs2, sp, 8)) -∗
    (|={⊤ ∖ ↑minstretN, Em}=> ∃ vold : mword 64,
       add_vec (m0 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) ↦₈ vold ∗
       (add_vec (m0 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000")))
          ↦₈ (rget m0 rs2) ={Em, ⊤ ∖ ↑minstretN}=∗ Ψ)) -∗
    wp_next b pme (fun (CID : CpuId) =>
      sie_cap_gpr m0 av b pme -∗
      pc_is (add_vec_int pc 2) -∗
      Ψ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intro HkptEm.
    (* the class, consumed at [rs2] -- see [IntrDefs.SrcOk].  This wrapper
       applies a converted leaf at a VARIABLE register and carries no tp fact
       of its own, so the class has to be stated here; it is implicit, so this
       lemma's own call sites (which pass concrete registers) do not move.  The
       [assert] is the wiring check: it names the register the premise reads. *)
    assert (Hsv2_all : forall hh : CpuId, rget (CID := hh) m0 rs2 = rget (CID := CID0) m0 rs2)
      by (intros hh; exact (src_ok_rget_indep m0 rs2 hh CID0)).
    assert (Hsp : rget (CID := CID0) m0 csp_rs1 = m0 !!! Regidx csp_rs1).
    { apply rget_ne. intro He. injection He as He2. vm_compute in He2. congruence. }
    rewrite <- sext9_12_64.
    change sp with (Regidx csp_rs1).
    iIntros "Hcg Hpc Hinstr HAU Hcont".
    iApply (wp_store_s_sconf_au (CID := CID0) (p := pme) 8 true pc rs2 csp_rs1
              (zero_extend' 12 (concat_vec uimm ('b"000"))) m0 av
              (rget m0 rs2) Ψ Em b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 512; reflexivity)
              ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_8 (store_ext_8 (rget (CID := CID0) m0 rs2)) HkptEm
              with "Hcg Hpc Hinstr [HAU] Hcont").
    rewrite Hsp. iExact "HAU".
  Qed.

  (* the escrow, in the raw [inv] shape [iInv] recognizes *)
  Local Lemma buf_escrow_inv (bn : bio_names) (V : bio_view Σ) (k : nat) :
    buf_escrow bn V k -∗ inv bioN (buf_escrow_body bn V k).
  Proof. iIntros "H". iExact "H". Qed.

  (* ---------------------------------------------------------------- *)
  (*  The [c.addiw a5,a5,-1] value, as a function of the loaded word    *)
  (* ---------------------------------------------------------------- *)

  Local Definition decr32 (cw : mword 32) : mword 32 :=
    trunc32 (sign_extend' 64 (subrange_vec_dec
      (add_vec (sign_extend' 64 cw)
               (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0)).

  (* the 64-bit register value the branch reads is the sign extension of it *)
  Local Lemma decr64_sext (cw : mword 32) :
    sign_extend' 64 (subrange_vec_dec
      (add_vec (sign_extend' 64 cw)
               (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0)
    = sign_extend' 64 (decr32 cw).
  Proof. rewrite /decr32 trunc32_sext. reflexivity. Qed.

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

  (* ================================================================== *)
  (*  THE TAIL: release(&bcache.lock) + the epilogue, reached from both  *)
  (*  arms of the [c.bnez].                                             *)
  (* ================================================================== *)

  (* Its OWN [CID0] binder: the tail starts at the hart [acquire] came back
     on, which the section's [CID] cannot name.  Entry is at the DISABLED
     index (the bcache lock is held, so the level is 1); the exit index is
     [eb] -- release's own level-0 exit arm, which pop_off restores to the
     saved base enable.  The level is fixed at 1 (brelse's only call site),
     so no [nn] binder survives. *)
  Local Lemma brelse_tail `{CID0 : CpuId}  (bn : bio_names)
      (V : bio_view Σ)
      (m M : regfile) (K : nat) (eb : bool) (p : mword 64) (C : iProp Σ) :
    (K_brelse <= K)%nat ->
    M !!! Regidx csp_rs1
      = add_vec (m !!! Regidx csp_rs1)
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) ->
    (forall c : mword 5, is_cs_idx c = true ->
       c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
       M !!! Regidx c = m !!! Regidx c) ->
    sie_cap_gpr M (trap_res eb + (K - 4))%nat false p -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.brelse + 0x60) : mword 64) -∗
    is_lock (bn_lk bn) bcache_addr "bcache"%string (bcache_res bn V) -∗
    locked (bn_lk bn) cpu_id -∗
    bcache_res bn V -∗
    cpu_own 1%nat eb p C false -∗
    arm_pay 0%nat eb p -∗
    pa_stk (m !!! Regidx csp_rs1) 1 ↦₈ (m !!! Regidx Rra) -∗
    pa_stk (m !!! Regidx csp_rs1) 2 ↦₈ (m !!! Regidx Rs0) -∗
    pa_stk (m !!! Regidx csp_rs1) 3 ↦₈ (m !!! Regidx Rs1) -∗
    pa_stk (m !!! Regidx csp_rs1) 4 ↦₈ (m !!! Regidx Rs2) -∗
    wp_next eb p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr mf K eb p -∗
        cpu_own 0%nat eb p C eb -∗
        pc_is (ret_pc (m !!! Regidx Rra)) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK HMsp HMthr.
    assert (HK26 : (26 <= K)%nat) by (unfold K_brelse in HK; exact HK).
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec (m !!! Regidx csp_rs1 : mword 64)
                  (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iIntros "Hcg #Htext Hpc #Hlock Htok HRres Hcnt Hpay Hr24 Hr16 Hr8 Hg4 Hcont".
    iPoseProof (bri_60 with "Htext") as "Hi60".
    iPoseProof (bri_64 with "Htext") as "Hi64".
    iPoseProof (bri_68 with "Htext") as "Hi68".
    (* +0x60 / +0x64 : a0 := &bcache.  The lock is held, so the whole stretch
       up to [release] runs at the DISABLED index and [wp_next_off] collapses
       the hart back at every leaf -- which is what keeps [Htok] / [Hpay],
       both pinned at THIS hart, usable across it. *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.brelse + 0x60)) Ra0 (mword_of_int 21 : mword 20)
              M (trap_res eb + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi60 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (T1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.brelse + 0x60) : mword 64)
                     (auipc_off (mword_of_int 21 : mword 20)))]> M).
    assert (Hpp64 : add_vec_int (mword_of_int (KernelSyms.brelse + 0x60) : mword 64) 4 = mword_of_int (KernelSyms.brelse + 0x64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp64) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.brelse + 0x64)) Ra0 Ra0 (mword_of_int 1332 : mword 12)
              T1 (trap_res eb + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi64 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (T1 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 1332 : mword 12)))]> T1).
    assert (HT2a0 : T2 !!! Regidx Ra0 = bcache_addr).
    { rewrite /T2 upd_eq /T1 upd_eq. rewrite /bcache_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp68 : add_vec_int (mword_of_int (KernelSyms.brelse + 0x64) : mword 64) 4 = mword_of_int (KernelSyms.brelse + 0x68))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp68) in "Hpc".
    (* +0x68 jal ra,release *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.brelse + 0x68)) Rra (mword_of_int 2088820 : mword 21)
              T2 (trap_res eb + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi68 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (T3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.brelse + 0x68) : mword 64) 4)]> T2).
    assert (Htgtrel : add_vec (mword_of_int (KernelSyms.brelse + 0x68) : mword 64)
                        (sign_extend' 64 (mword_of_int 2088820 : mword 21))
                      = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtrel) in "Hpc".
    assert (HT3thr : forall c : mword 5, is_cs_idx c = true ->
                       T3 !!! Regidx c = M !!! Regidx c).
    { intros c Hcs.
      rewrite /T3 upd_ne; [| regne].
      rewrite /T2 upd_ne; [| regne].
      rewrite /T1 upd_ne; [reflexivity | regne]. }
    assert (HT3a0 : T3 !!! Regidx Ra0 = bcache_addr)
      by (rewrite /T3 upd_ne; [exact HT2a0 | vm_compute; discriminate]).
    assert (HT3sp : T3 !!! Regidx csp_rs1 = spr)
      by (rewrite (HT3thr csp_rs1 ltac:(vm_compute; reflexivity)); exact HMsp).
    assert (HT3ra : T3 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.brelse + 0x68) : mword 64) 4)
      by (rewrite /T3; apply upd_eq).
    iApply (Rl.wp_release_sconf (bn_lk bn) bcache_addr "bcache"%string (bcache_res bn V) T3
              0%nat eb p C (K - 4)%nat
              ltac:(rewrite HT3a0; apply bv_eq; vm_compute; reflexivity)
              ltac:(lia)
              with "Hcg Htext Hpc [Hlock] Htok HRres Hcnt Hpay [-]").
    { iExact "Hlock". }
    iIntros (CIDr Hsr mr) "Hcg Hpc %Hrelpins Hcnt".
    assert (Hpc6c : ret_pc (T3 !!! Regidx Rra) = mword_of_int (KernelSyms.brelse + 0x6c)).
    { rewrite HT3ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc6c) in "Hpc".
    pose proof Hrelpins as Hrelpins_cs.
    (* ===== EPILOGUE ===== *)
    iPoseProof (bri_6c with "Htext") as "Hi6c".
    iPoseProof (bri_6e with "Htext") as "Hi6e".
    iPoseProof (bri_70 with "Htext") as "Hi70".
    iPoseProof (bri_72 with "Htext") as "Hi72".
    iPoseProof (bri_74 with "Htext") as "Hi74".
    iPoseProof (bri_76 with "Htext") as "Hi76".
    assert (Hmrsp : mr !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hrelpins_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HT3sp).
    assert (Hb1 : add_vec spr
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ===== the epilogue, at release's exit index [eb] ===== *)
    (* +0x6c c.ldsp ra,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.brelse + 0x6c)) (mword_of_int 3 : mword 6) Rra
              mr (K - 4)%nat (m !!! Regidx Rra) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6c [Hr24] [-]").
    { iEval (rewrite Hmrsp Hb1). iExact "Hr24". }
    iIntros (CIDe1 Hse1) "Hcg Hpc Hr24".
    iEval (rewrite Hmrsp Hb1) in "Hr24".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra)]> mr).
    assert (HP1sp : P1 !!! Regidx csp_rs1 = spr)
      by (rewrite /P1 upd_ne; [exact Hmrsp | vm_compute; discriminate]).
    assert (Hpp6e : add_vec_int (mword_of_int (KernelSyms.brelse + 0x6c) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x6e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp6e) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.brelse + 0x6e)) (mword_of_int 2 : mword 6) Rs0
              P1 (K - 4)%nat (m !!! Regidx Rs0) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6e [Hr16] [-]").
    { iEval (rewrite HP1sp Hb2). iExact "Hr16". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hr16".
    iEval (rewrite HP1sp Hb2) in "Hr16".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0)]> P1).
    assert (HP2sp : P2 !!! Regidx csp_rs1 = spr)
      by (rewrite /P2 upd_ne; [exact HP1sp | vm_compute; discriminate]).
    assert (Hpp70 : add_vec_int (mword_of_int (KernelSyms.brelse + 0x6e) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x70))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp70) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.brelse + 0x70)) (mword_of_int 1 : mword 6) Rs1
              P2 (K - 4)%nat (m !!! Regidx Rs1) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi70 [Hr8] [-]").
    { iEval (rewrite HP2sp Hb3). iExact "Hr8". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hr8".
    iEval (rewrite HP2sp Hb3) in "Hr8".
    set (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1)]> P2).
    assert (HP3sp : P3 !!! Regidx csp_rs1 = spr)
      by (rewrite /P3 upd_ne; [exact HP2sp | vm_compute; discriminate]).
    assert (Hpp72 : add_vec_int (mword_of_int (KernelSyms.brelse + 0x70) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x72))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp72) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.brelse + 0x72)) (mword_of_int 0 : mword 6) Rs2
              P3 (K - 4)%nat (m !!! Regidx Rs2) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi72 [Hg4] [-]").
    { iEval (rewrite HP3sp Hb4). iExact "Hg4". }
    iIntros (CIDe4 Hse4) "Hcg Hpc Hg4".
    iEval (rewrite HP3sp Hb4) in "Hg4".
    set (P4 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> P3).
    assert (HP4sp : P4 !!! Regidx csp_rs1 = spr)
      by (rewrite /P4 upd_ne; [exact HP3sp | vm_compute; discriminate]).
    assert (Hpp74 : add_vec_int (mword_of_int (KernelSyms.brelse + 0x72) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x74))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp74) in "Hpc".
    set (P5 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P4 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P4).
    assert (Hwv : add_vec (P4 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HP4sp. unfold spr, sp0. apply frame_cancel_32. }
    assert (Hpop : P4 !!! Regidx csp_rs1
                   = pa_stk (add_vec (P4 !!! Regidx csp_rs1)
                               (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HP4sp. unfold spr, sp0, pa_stk, add_vec_int.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hg4]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24"; [iExists _; iExact "Hr24"|].
      iSplitL "Hr16"; [iExists _; iExact "Hr16"|].
      iSplitL "Hr8";  [iExists _; iExact "Hr8"|].
      iSplitL "Hg4";  [iExists _; iExact "Hg4"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.brelse + 0x74)) (mword_of_int 2 : mword 6)
              P4 (K - 4)%nat 4 eb Hpop with "Hcg Hpc Hi74 Hframe4 [-]").
    iIntros (CIDe5 Hse5) "Hcg Hpc".
    assert (Hnk : ((K - 4) + 4)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg
      (add_vec (P4 !!! Regidx csp_rs1)
         (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P4) with P5.
    assert (Hpp76 : add_vec_int (mword_of_int (KernelSyms.brelse + 0x74) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x76))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp76) in "Hpc".
    assert (HP5ra : P5 !!! Regidx Rra = m !!! Regidx Rra).
    { rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_ne; [| vm_compute; discriminate].
      rewrite /P1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.brelse + 0x76)) Rra P5 K eb
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi76 [-]").
    iIntros (CIDe6 Hse6) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    iEval (rewrite HP5ra) in "Hpc".
    (* [cpu_own] is the one resource a leaf's [wp_next] does NOT re-deliver:
       release handed it back at [CIDr], the six epilogue leaves moved on. *)
    iDestruct (cpu_own_transport CIDr CIDe6 0%nat eb p C eb ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CIDe6 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! P5 with "[%] Hcg Hcnt Hpc").
    (* callee_saved m P5 *)
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              P5 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /P5 upd_ne; [| regne].
      rewrite /P4 upd_ne; [| regne].
      rewrite /P3 upd_ne; [| regne].
      rewrite /P2 upd_ne; [| regne].
      rewrite /P1 upd_ne; [| regne].
      rewrite (callee_saved_lookup Hrelpins_cs c Hcs).
      rewrite (HT3thr c Hcs).
      exact (HMthr c Hcs N2 N8 N9 N18). }
    unfold callee_saved.
    assert (Hc2 : P5 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1).
    { rewrite /P5 upd_eq. rewrite HP4sp. unfold regval_into_reg, spr, sp0.
      apply frame_cancel_32. }
    assert (Hc8 : P5 !!! Regidx Rs0 = m !!! Regidx Rs0).
    { rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_eq. reflexivity. }
    assert (Hc9 : P5 !!! Regidx Rs1 = m !!! Regidx Rs1).
    { rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_eq. reflexivity. }
    assert (Hc18 : P5 !!! Regidx Rs2 = m !!! Regidx Rs2).
    { rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_eq. reflexivity. }
    repeat split;
      first [ exact Hc2 | exact Hc8 | exact Hc9 | exact Hc18
            | apply Hthread; vm_compute; first [reflexivity | discriminate] ].
  Qed.

  (* ================================================================== *)
  (*  THE WHOLE FUNCTION                                                 *)
  (* ================================================================== *)

  Lemma wp_brelse_sconf 
      (γs : list gname)
      (bn : bio_names) (V : bio_view Σ) (k : nat)
      (pidv dev bno : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (bs bsd : list (bv 8)) (d : bool) (b : bool)
    : wp_brelse_sconf_body γs bn V k pidv dev bno dq m K eb p C bs bsd d b.
  Proof.
    cbv beta delta [wp_brelse_sconf_body].
    intros pcE ret_tgt HK Hk Ha0.
    assert (HK26 : (26 <= K)%nat) by (unfold K_brelse in HK; exact HK).
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt #Htext Hpc #Hpanic #Hbio Hppid Hprocs Hlocked Hcont".
    (* brelse enters at level 0, so the saved base enable IS the live SIE
       state: [eb = b].  Substituting makes release's exit index (which is
       [eb]) literally [b], so one [wp_next_chain] composes across the whole
       acquire/release boundary.  See the porting guide's "Derive the SIE
       index rather than stating it". *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Heb. cbn in Heb. subst eb.
    iDestruct (bio_ctx_lock with "Hbio") as "#Hlock".
    iDestruct (bio_ctx_buf bn V k Hk with "Hbio") as "[#Hslk #Hesc0]".
    iDestruct (buf_escrow_inv with "Hesc0") as "#Hesc".
    iDestruct "Hlocked"
      as "(_ & %Hcov & %Hdv & Hstok & Hpid & Hvalid & Hbdev & Hbuf & Hdb & Hbpay)".
    (* the payload the park deposits: the handle's disk cell and [bio_pay],
       re-packaged at the escrow's [buf_pay] shape.  The blockno is covered
       (bio_held's second conjunct), so the [decide] resolves LEFT and the
       valid bit is [true]. *)
    iAssert (buf_pay bn V k true dev bno bs) with "[Hdb Hbpay]" as "Hbpayload".
    { rewrite /buf_pay. case_decide as Hc; [|contradiction].
      iSplitR; [iPureIntro; exact Hdv|].
      iExists bsd, d. iFrame "Hdb Hbpay". }
    set (spr := add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iPoseProof (bri_00 with "Htext") as "Hi00".
    iPoseProof (bri_02 with "Htext") as "Hi02".
    iPoseProof (bri_04 with "Htext") as "Hi04".
    iPoseProof (bri_06 with "Htext") as "Hi06".
    iPoseProof (bri_08 with "Htext") as "Hi08".
    iPoseProof (bri_0a with "Htext") as "Hi0a".
    iPoseProof (bri_0c with "Htext") as "Hi0c".
    iPoseProof (bri_0e with "Htext") as "Hi0e".
    iPoseProof (bri_12 with "Htext") as "Hi12".
    iPoseProof (bri_14 with "Htext") as "Hi14".
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
              ltac:(lia) Hpush with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    assert (HR1ra : R1 !!! Regidx Rra = m !!! Regidx Rra)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1s0 : R1 !!! Regidx Rs0 = m !!! Regidx Rs0)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1s1 : R1 !!! Regidx Rs1 = m !!! Regidx Rs1)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1s2 : R1 !!! Regidx Rs2 = m !!! Regidx Rs2)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
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
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* ===== +0x02 sd ra,24(sp) -- THE PARK ===== *)
    iApply (wp_csdsp_au_s_sconf (mword_of_int (KernelSyms.brelse + 0x02)) (mword_of_int 3 : mword 6) Rra
              R1 (K - 4)%nat
              ((add_vec (R1 !!! Regidx csp_rs1)
                  (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                 ↦₈ (R1 !!! Regidx Rra)) ∗
               (∃ q : Qp, bref_tok bn k q ∗
                  b_dev (bpa k) ↦₄{DfracOwn q} dev ∗
                  b_blockno (bpa k) ↦₄{DfracOwn q} bno ∗ bown bn k))%I
              (⊤ ∖ ↑minstretN ∖ ↑bioN) b p
              ltac:(solve_ndisj)
              with "Hcg Hpc Hi02 [Hr24 Hvalid Hbdev Hbuf Hbpayload] [-]").
    (* The escrow body is NOT timeless any more: the parked arm's [buf_pay]
       carries the view's opaque payload ([bv_clean] / [bv_dirty]), so the
       [▷] the [iInv] hands out cannot be stripped up front.  It does not
       have to be: run the swap UNDER the later ([iNext] strips the body's
       [▷] and weakens the non-later inputs), give the invariant back its
       [▷ body] as usual, and strip the later off the WITHDRAWN bundle --
       which is a reference fragment, two word cells and a lock token, all
       timeless -- with one [iMod] inside the accessor's own fupd. *)
    { iInv "Hesc" as "Hbody" "Hclose".
      (* [escrow_swap_park_now] does the [iNext] AND the withdrawn bundle's
         later-strip inside BioInv, where the context is five hypotheses
         wide.  Done here it was 34 s in one [iMod] -- the cost is the
         CONTEXT, not the bundle (optimization.md). *)
      iMod (escrow_swap_park_now _ bn V k true dev bno bs
              with "Hbody Hvalid Hbdev Hbuf Hbpayload") as "[Hbody Hpark]".
      iModIntro. iExists vr24. iFrame "Hr24".
      iIntros "Hcell". iEval (rgpeel) in "Hcell".
      iMod ("Hclose" with "[Hbody]") as "_". { iNext. iExact "Hbody". }
      iModIntro. iFrame "Hcell Hpark". }
    iIntros (CID2 Hs2) "Hcg Hpc [Hr24 Hpark]".
    iDestruct "Hpark" as (q) "(Hrtok & Hrdev & Hrbno & Hbown)".
    iEval (rewrite Hb1 HR1ra) in "Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.brelse + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.brelse + 0x04)) (mword_of_int 2 : mword 6) Rs0
              R1 (K - 4)%nat vr16 b with "Hcg Hpc Hi04 Hr16 [-]").
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    iEval (rgpeel) in "Hr16".
    iEval (rewrite Hb2 HR1s0) in "Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.brelse + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.brelse + 0x06)) (mword_of_int 1 : mword 6) Rs1
              R1 (K - 4)%nat vr8 b with "Hcg Hpc Hi06 Hr8 [-]").
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    iEval (rgpeel) in "Hr8".
    iEval (rewrite Hb3 HR1s1) in "Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.brelse + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.brelse + 0x08)) (mword_of_int 0 : mword 6) Rs2
              R1 (K - 4)%nat vg4 b with "Hcg Hpc Hi08 Hg4 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc Hg4".
    iEval (rgpeel) in "Hg4".
    iEval (rewrite Hb4 HR1s2) in "Hg4".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.brelse + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.brelse + 0x0a)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 R1 (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.brelse + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c c.mv s1,a0 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.brelse + 0x0c)) Rs1 Ra0
              R2 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c [-]").
    iIntros (CID7 Hs7) "Hcg Hpc".
    iEval (rgpeel) in "Hcg".
    set (R3 :=<[Regidx Rs1 := regval_into_reg (add_vec zero_reg (R2 !!! Regidx Ra0))]> R2).
    assert (HR3s1 : R3 !!! Regidx Rs1 = bnode k).
    { rewrite /R3 upd_eq. rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite Ha0. apply add_vec_zero_l. }
    assert (HR3a0 : R3 !!! Regidx Ra0 = bnode k).
    { rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [exact Ha0 | vm_compute; discriminate]. }
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.brelse + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x0e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e addi s2,a0,16 : s2 := &b->lock *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.brelse + 0x0e)) Rs2 Ra0 (mword_of_int 16 : mword 12)
              R3 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e [-]").
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (rgpeel) in "Hcg".
    set (R4 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (R3 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 16 : mword 12)))]> R3).
    assert (HR4s2 : R4 !!! Regidx Rs2 = buf_lock (bnode k)).
    { rewrite /R4 upd_eq. rewrite HR3a0. reflexivity. }
    assert (HR4s1 : R4 !!! Regidx Rs1 = bnode k)
      by (rewrite /R4 upd_ne; [exact HR3s1 | vm_compute; discriminate]).
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.brelse + 0x0e) : mword 64) 4 = mword_of_int (KernelSyms.brelse + 0x12))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* +0x12 c.mv a0,s2 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.brelse + 0x12)) Ra0 Rs2
              R4 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12 [-]").
    iIntros (CID9 Hs9) "Hcg Hpc".
    iEval (rgpeel) in "Hcg".
    set (R5 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (R4 !!! Regidx Rs2))]> R4).
    assert (HR5a0 : R5 !!! Regidx Ra0 = buf_lock (bnode k)).
    { rewrite /R5 upd_eq. rewrite HR4s2. apply add_vec_zero_l. }
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.brelse + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x14))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* ===== +0x14 jal ra,holdingsleep ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.brelse + 0x14)) Rra (mword_of_int 4920 : mword 21)
              R5 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi14 [-]").
    iIntros (CID10 Hs10) "Hcg Hpc".
    set (mA := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.brelse + 0x14) : mword 64) 4)]> R5).
    assert (Htgthsl : add_vec (mword_of_int (KernelSyms.brelse + 0x14) : mword 64)
                        (sign_extend' 64 (mword_of_int 4920 : mword 21))
                      = mword_of_int KernelSyms.holdingsleep)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgthsl) in "Hpc".
    assert (HmAthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              mA !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /mA upd_ne; [| regne].
      rewrite /R5 upd_ne; [| regne].
      rewrite /R4 upd_ne; [| regne].
      rewrite /R3 upd_ne; [| regne].
      rewrite /R2 upd_ne; [| regne].
      rewrite /R1 upd_ne; [reflexivity | regne]. }
    assert (HmAsp : mA !!! Regidx csp_rs1 = spr).
    { rewrite /mA upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      exact HspR1. }
    assert (HmAa0 : mA !!! Regidx Ra0 = buf_lock (bnode k))
      by (rewrite /mA upd_ne; [exact HR5a0 | vm_compute; discriminate]).
    assert (HmAs1 : mA !!! Regidx Rs1 = bnode k).
    { rewrite /mA upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate]. exact HR4s1. }
    assert (HmAs2 : mA !!! Regidx Rs2 = buf_lock (bnode k)).
    { rewrite /mA upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate]. exact HR4s2. }
    assert (HmAra : mA !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.brelse + 0x14) : mword 64) 4)
      by (rewrite /mA; apply upd_eq).
    iDestruct (cpu_own_transport CID CID10 0%nat b p C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Hsl.wp_holdingsleep_sconf (fst (bn_slk bn k)) (snd (bn_slk bn k))
              "buffer"%string (bown bn k) mA p pidv (K - 4)%nat b C b
              ltac:(lia)
              with "Hcg Hcnt Htext Hpc [] Hstok [Hpid] Hpanic Hppid [-]").
    { iEval (rewrite HmAa0). iExact "Hslk". }
    { iEval (rewrite HmAa0). iExact "Hpid". }
    iIntros (CID11 Hs11 mH) "%Hhs Hcg Hcnt Hpc Hstok Hpid Hppid".
    destruct Hhs as [Hcs1 Hha0].
    iEval (rewrite HmAa0) in "Hpid".
    assert (Hpc18 : ret_pc (mA !!! Regidx Rra) = mword_of_int (KernelSyms.brelse + 0x18)).
    { rewrite HmAra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc18) in "Hpc".
    pose proof Hcs1 as Hcs1_cs.
    assert (HmHsp : mH !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HmAsp).
    assert (HmHs1 : mH !!! Regidx Rs1 = bnode k)
      by (rewrite (callee_saved_lookup Hcs1_cs (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HmAs1).
    assert (HmHs2 : mH !!! Regidx Rs2 = buf_lock (bnode k))
      by (rewrite (callee_saved_lookup Hcs1_cs (mword_of_int 18) ltac:(vm_compute; reflexivity)); exact HmAs2).
    assert (HmHthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              mH !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N18.
      rewrite (callee_saved_lookup Hcs1_cs c Hcs). exact (HmAthr c Hcs N2 N8 N9 N18). }
    (* ===== +0x18 c.beqz a0 : a0 = 1, the panic arm is dead ===== *)
    iPoseProof (bri_18 with "Htext") as "Hi18".
    iPoseProof (bri_1a with "Htext") as "Hi1a".
    iPoseProof (bri_1c with "Htext") as "Hi1c".
    assert (Hbeqz : eq_vec (mH !!! Regidx Ra0) zero_reg = false)
      by (rewrite Hha0; vm_compute; reflexivity).
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.brelse + 0x18)) (mword_of_int 48 : mword 8)
              (Cregidx (mword_of_int 2)) Ra0 mH (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rgne; exact Hbeqz)
              with "Hcg Hpc Hi18 [-]").
    iIntros (CID12 Hs12) "Hcg Hpc".
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.brelse + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x1a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a c.mv a0,s2 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.brelse + 0x1a)) Ra0 Rs2
              mH (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a [-]").
    iIntros (CID13 Hs13) "Hcg Hpc".
    iEval (rgpeel) in "Hcg".
    set (H1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mH !!! Regidx Rs2))]> mH).
    assert (HH1a0 : H1 !!! Regidx Ra0 = buf_lock (bnode k)).
    { rewrite /H1 upd_eq. rewrite HmHs2. apply add_vec_zero_l. }
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.brelse + 0x1a) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x1c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* ===== +0x1c jal ra,releasesleep ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.brelse + 0x1c)) Rra (mword_of_int 4856 : mword 21)
              H1 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi1c [-]").
    iIntros (CID14 Hs14) "Hcg Hpc".
    set (H2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.brelse + 0x1c) : mword 64) 4)]> H1).
    assert (Htgtrsl : add_vec (mword_of_int (KernelSyms.brelse + 0x1c) : mword 64)
                        (sign_extend' 64 (mword_of_int 4856 : mword 21))
                      = mword_of_int KernelSyms.releasesleep)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtrsl) in "Hpc".
    assert (HH2thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              H2 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /H2 upd_ne; [| regne].
      rewrite /H1 upd_ne; [| regne]. exact (HmHthr c Hcs N2 N8 N9 N18). }
    assert (HH2sp : H2 !!! Regidx csp_rs1 = spr).
    { rewrite /H2 upd_ne; [| vm_compute; discriminate].
      rewrite /H1 upd_ne; [exact HmHsp | vm_compute; discriminate]. }
    assert (HH2s1 : H2 !!! Regidx Rs1 = bnode k).
    { rewrite /H2 upd_ne; [| vm_compute; discriminate].
      rewrite /H1 upd_ne; [exact HmHs1 | vm_compute; discriminate]. }
    assert (HH2a0 : H2 !!! Regidx Ra0 = buf_lock (bnode k))
      by (rewrite /H2 upd_ne; [exact HH1a0 | vm_compute; discriminate]).
    assert (HH2ra : H2 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.brelse + 0x1c) : mword 64) 4)
      by (rewrite /H2; apply upd_eq).
    iDestruct (cpu_own_transport CID11 CID14 0%nat b p C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Rsl.wp_releasesleep_sconf γs (fst (bn_slk bn k)) (snd (bn_slk bn k))
              "buffer"%string (bown bn k) H2 pidv p (K - 4)%nat b C b
              ltac:(lia)
              with "Hcg Hcnt Htext Hpc [] Hstok [Hpid] Hbown Hpanic Hprocs [-]").
    { iEval (rewrite HH2a0). iExact "Hslk". }
    { iEval (rewrite HH2a0). iExact "Hpid". }
    iIntros (CID15 Hs15 mR) "%Hcs2 Hcg Hcnt Hpc".
    assert (Hpc20 : ret_pc (H2 !!! Regidx Rra) = mword_of_int (KernelSyms.brelse + 0x20)).
    { rewrite HH2ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc20) in "Hpc".
    pose proof Hcs2 as Hcs2_cs.
    assert (HmRsp : mR !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hcs2_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HH2sp).
    assert (HmRs1 : mR !!! Regidx Rs1 = bnode k)
      by (rewrite (callee_saved_lookup Hcs2_cs (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HH2s1).
    assert (HmRthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              mR !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N18.
      rewrite (callee_saved_lookup Hcs2_cs c Hcs). exact (HH2thr c Hcs N2 N8 N9 N18). }
    (* ===== +0x20 / +0x24 : a0 := &bcache ; +0x28 jal acquire ===== *)
    iPoseProof (bri_20 with "Htext") as "Hi20".
    iPoseProof (bri_24 with "Htext") as "Hi24".
    iPoseProof (bri_28 with "Htext") as "Hi28".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.brelse + 0x20)) Ra0 (mword_of_int 21 : mword 20)
              mR (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi20 [-]").
    iIntros (CID16 Hs16) "Hcg Hpc".
    set (U1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.brelse + 0x20) : mword 64)
                     (auipc_off (mword_of_int 21 : mword 20)))]> mR).
    assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.brelse + 0x20) : mword 64) 4 = mword_of_int (KernelSyms.brelse + 0x24))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.brelse + 0x24)) Ra0 Ra0 (mword_of_int 1396 : mword 12)
              U1 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24 [-]").
    iIntros (CID17 Hs17) "Hcg Hpc".
    iEval (rgpeel) in "Hcg".
    set (U2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (U1 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 1396 : mword 12)))]> U1).
    assert (HU2a0 : U2 !!! Regidx Ra0 = bcache_addr).
    { rewrite /U2 upd_eq /U1 upd_eq. rewrite /bcache_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.brelse + 0x24) : mword 64) 4 = mword_of_int (KernelSyms.brelse + 0x28))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.brelse + 0x28)) Rra (mword_of_int 2088748 : mword 21)
              U2 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi28 [-]").
    iIntros (CID18 Hs18) "Hcg Hpc".
    set (U3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.brelse + 0x28) : mword 64) 4)]> U2).
    assert (Htgtacq : add_vec (mword_of_int (KernelSyms.brelse + 0x28) : mword 64)
                        (sign_extend' 64 (mword_of_int 2088748 : mword 21))
                      = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtacq) in "Hpc".
    assert (HU3thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              U3 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /U3 upd_ne; [| regne].
      rewrite /U2 upd_ne; [| regne].
      rewrite /U1 upd_ne; [| regne]. exact (HmRthr c Hcs N2 N8 N9 N18). }
    assert (HU3sp : U3 !!! Regidx csp_rs1 = spr).
    { rewrite /U3 upd_ne; [| vm_compute; discriminate].
      rewrite /U2 upd_ne; [| vm_compute; discriminate].
      rewrite /U1 upd_ne; [exact HmRsp | vm_compute; discriminate]. }
    assert (HU3s1 : U3 !!! Regidx Rs1 = bnode k).
    { rewrite /U3 upd_ne; [| vm_compute; discriminate].
      rewrite /U2 upd_ne; [| vm_compute; discriminate].
      rewrite /U1 upd_ne; [exact HmRs1 | vm_compute; discriminate]. }
    assert (HU3a0 : U3 !!! Regidx Ra0 = bcache_addr)
      by (rewrite /U3 upd_ne; [exact HU2a0 | vm_compute; discriminate]).
    assert (HU3ra : U3 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.brelse + 0x28) : mword 64) 4)
      by (rewrite /U3; apply upd_eq).
    iDestruct (cpu_own_transport CID15 CID18 0%nat b p C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Aq.wp_acquire_sconf (bn_lk bn) "bcache"%string (bcache_res bn V) U3
              0%nat b p C (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(lia)
              with "Hcg Hcnt Htext Hpc [Hlock] Hpanic [-]").
    { iEval (rewrite HU3a0). iExact "Hlock". }
    (* acquire returns with interrupts OFF ([sie_cap_gpr _ _ false _]), so the
       whole critical section below runs at the literal [false] index and
       [wp_next_off] pins the hart at [CIDa] -- which is what keeps [Htok]
       ([locked _ cpu_id]) and [Hpay] usable across every leaf. *)
    iIntros (CIDa Hsa ms mQ) "%Hmsfacts Hcg Hpc %Hacqpins Htok HRres Hcnt Hpay".
    assert (Hpc2c : ret_pc (U3 !!! Regidx Rra) = mword_of_int (KernelSyms.brelse + 0x2c)).
    { rewrite HU3ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc2c) in "Hpc".
    pose proof Hacqpins as Hacqpins_cs.
    assert (HmQsp : mQ !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hacqpins_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HU3sp).
    assert (HmQs1 : mQ !!! Regidx Rs1 = bnode k)
      by (rewrite (callee_saved_lookup Hacqpins_cs (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HU3s1).
    assert (HmQthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              mQ !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N18.
      rewrite (callee_saved_lookup Hacqpins_cs c Hcs). exact (HU3thr c Hcs N2 N8 N9 N18). }
    (* ===== the critical section ===== *)
    assert (Hs64 : sign_extend' 64 (mword_of_int 64 : mword 12) = (mword_of_int 64 : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iPoseProof (bri_2c with "Htext") as "Hi2c".
    iPoseProof (bri_2e with "Htext") as "Hi2e".
    iPoseProof (bri_30 with "Htext") as "Hi30".
    iPoseProof (bri_32 with "Htext") as "Hi32".
    iDestruct "HRres" as (Mg ord devs bnos)
      "(Hauth & Hsauth & %Hdom & %Hord & %Hinj & %Hdev & Hlru & Hpool & Hslots)".
    iDestruct (bref_tok_lookup with "Hauth Hrtok")
      as %(qt & cnt & HMk & Hsole & _ & Hltn).
    iDestruct (bio_slots_acc bn Mg devs bnos k Hk with "Hslots") as "[Hslot Hback]".
    iEval (rewrite /bio_slot_res HMk) in "Hslot".
    iDestruct "Hslot" as "(%Hcnt & Hcell & Hfd & Hqr)".
    iDestruct "Hqr" as (qr) "(%Htie & Hdev & Hbno)".
    iDestruct (word4_pointsto_agree with "Hrdev Hdev") as %->.
    iDestruct (word4_pointsto_agree with "Hrbno Hbno") as %->.
    (* the three instructions of the decrement, run in both arms *)
    assert (Hpa : add_vec (rget mQ Rs1) (sign_extend' 64 (mword_of_int 64 : mword 12))
                  = brefcnt k).
    { rgne. rewrite HmQs1 Hs64. rewrite /brefcnt /bpa /pa_add /add_vec_int. reflexivity. }
    destruct (decide (cnt = 1%positive)) as [->|Hne].
    (* ================= the LAST reference: unlink + splice ============ *)
    - assert (Hq : q = qt) by (apply Hsole; reflexivity). subst qt.
      iEval (rewrite -Hpa) in "Hcell".
      iApply (wp_clw_s_sconf (mword_of_int (KernelSyms.brelse + 0x2c)) Ra5 Rs1 (mword_of_int 64 : mword 12)
                mQ (trap_res b + (K - 4))%nat (mword_of_int (Z.pos 1) : mword 32) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi2c Hcell [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hcell".
      iEval (rewrite Hpa) in "Hcell".
      set (D1 := <[Regidx Ra5 := regval_into_reg
                    (sign_extend' 64 (mword_of_int (Z.pos 1) : mword 32))]> mQ).
      assert (HD1a5 : D1 !!! Regidx Ra5 = sign_extend' 64 (mword_of_int (Z.pos 1) : mword 32))
        by (rewrite /D1; apply upd_eq).
      assert (HD1s1 : D1 !!! Regidx Rs1 = bnode k)
        by (rewrite /D1 upd_ne; [exact HmQs1 | vm_compute; discriminate]).
      assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.brelse + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x2e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2e) in "Hpc".
      iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.brelse + 0x2e)) Ra5 (mword_of_int 63 : mword 6)
                D1 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi2e [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      iEval (rgpeel) in "Hcg".
      set (D2 := <[Regidx Ra5 := regval_into_reg
                    (sign_extend' 64 (subrange_vec_dec
                       (add_vec (D1 !!! Regidx Ra5)
                          (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))]> D1).
      assert (HD2s1 : D2 !!! Regidx Rs1 = bnode k)
        by (rewrite /D2 upd_ne; [exact HD1s1 | vm_compute; discriminate]).
      assert (HD2a5 : D2 !!! Regidx Ra5
                      = sign_extend' 64 (mword_of_int 0 : mword 32)).
      { rewrite /D2 upd_eq. unfold regval_into_reg. rewrite HD1a5.
        rewrite decr64_sext. rewrite (decr32_pos 1%positive Hcnt). reflexivity. }
      assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.brelse + 0x2e) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x30))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp30) in "Hpc".
      assert (Hpa2 : add_vec (rget D2 Rs1) (sign_extend' 64 (mword_of_int 64 : mword 12))
                     = brefcnt k).
      { rgne. rewrite HD2s1 Hs64. rewrite /brefcnt /bpa /pa_add /add_vec_int. reflexivity. }
      iEval (rewrite -Hpa2) in "Hcell".
      iApply (wp_csw_s_sconf (mword_of_int (KernelSyms.brelse + 0x30)) Ra5 Rs1 (mword_of_int 64 : mword 12)
                D2 (trap_res b + (K - 4))%nat (mword_of_int (Z.pos 1) : mword 32) false
                with "Hcg Hpc Hi30 Hcell [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hcell".
      iEval (rewrite Hpa2) in "Hcell".
      iEval (rgpeel) in "Hcell".
      assert (Hstv : trunc32 (D2 !!! Regidx Ra5) = (mword_of_int 0 : mword 32)).
      { rewrite HD2a5. apply trunc32_sext. }
      iEval (rewrite Hstv) in "Hcell".
      (* the ghost step: the entry disappears, the retainder is whole again *)
      iMod (bio_last_ref_step bn Mg k q HMk with "Hauth Hrtok") as "Hauth".
      iAssert (b_dev (bpa k) ↦₄{DfracOwn (1/2)} (devs k))%I
        with "[Hrdev Hdev]" as "Hdev".
      { rewrite -(br_last_tie q qr Htie) word4_pointsto_frac_split.
        iFrame "Hdev Hrdev". }
      iAssert (b_blockno (bpa k) ↦₄{DfracOwn (1/2)} (bnos k))%I
        with "[Hrbno Hbno]" as "Hbno".
      { rewrite -(br_last_tie q qr Htie) word4_pointsto_frac_split.
        iFrame "Hbno Hrbno". }
      assert (Hdel : delete k Mg !! k = None) by apply lookup_delete.
      iAssert (bio_slot_res bn (delete k Mg) k (devs k) (bnos k))
        with "[Hcell Hdev Hbno]" as "Hslot".
      { rewrite /bio_slot_res Hdel. iFrame "Hcell Hdev Hbno". }
      iDestruct ("Hback" $! (delete k Mg) devs bnos with "[%] Hslot") as "Hslots".
      { intros j Hj. split_and!;
          [ rewrite lookup_delete_ne; [reflexivity | congruence] | reflexivity | reflexivity ]. }
      assert (Hdom' : forall j, is_Some (delete k Mg !! j) -> (j < NBUF)%nat).
      { intros j Hj. apply Hdom.
        destruct (decide (j = k)) as [->|Hnk].
        - rewrite Hdel in Hj. by destruct Hj as [x Hx].
        - rewrite lookup_delete_ne in Hj; [exact Hj | congruence]. }
      iEval (change (Pos.to_nat 1) with 1%nat) in "Hfd".
      (* ===== +0x32 c.bnez a5 : NOT taken, the splice runs ===== *)
      assert (Hbnez : neq_vec (D2 !!! Regidx Ra5) zero_reg = false)
        by (rewrite HD2a5; exact brc_word_zero_neqv).
      iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.brelse + 0x32)) (mword_of_int 23 : mword 8)
                (Cregidx (mword_of_int 7)) Ra5 D2 (trap_res b + (K - 4))%nat false
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; exact Hbnez)
                with "Hcg Hpc Hi32 [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.brelse + 0x32) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x34))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp34) in "Hpc".
      (* ---- locate k in the LRU order and unlink it ---- *)
      assert (Hkord : k ∈ ord).
      { rewrite Hord. apply elem_of_seq. lia. }
      apply elem_of_list_split in Hkord as (o1 & o2 & Hordeq).
      iEval (rewrite Hordeq map_app) in "Hlru".
      iEval (cbn [List.map]) in "Hlru".
      iDestruct (bcache_lru_unlink bhead (bnode k) (map bnode o1) (map bnode o2)
                   with "Hlru") as "(Hbp & Hbn & Hpn & Hsp & Hrelink)".
      iPoseProof (bri_34 with "Htext") as "Hi34".
      iPoseProof (bri_36 with "Htext") as "Hi36".
      iPoseProof (bri_38 with "Htext") as "Hi38".
      iPoseProof (bri_3a with "Htext") as "Hi3a".
      iPoseProof (bri_3c with "Htext") as "Hi3c".
      (* +0x34 c.ld a4,80(s1) : a4 := b->next *)
      iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.brelse + 0x34)) Ra4 Rs1 (mword_of_int 80 : mword 12)
                D2 (trap_res b + (K - 4))%nat (List.hd bhead (map bnode o2)) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi34 [Hbn] [-]").
      { iEval (rgpeel; rewrite HD2s1). iExact "Hbn". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hbn".
      iEval (rgpeel; rewrite HD2s1) in "Hbn".
      set (E1 := <[Regidx Ra4 := regval_into_reg (List.hd bhead (map bnode o2))]> D2).
      assert (HE1s1 : E1 !!! Regidx Rs1 = bnode k)
        by (rewrite /E1 upd_ne; [exact HD2s1 | vm_compute; discriminate]).
      assert (HE1a4 : E1 !!! Regidx Ra4 = List.hd bhead (map bnode o2))
        by (rewrite /E1; apply upd_eq).
      assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.brelse + 0x34) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x36))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp36) in "Hpc".
      (* +0x36 c.ld a5,72(s1) : a5 := b->prev *)
      iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.brelse + 0x36)) Ra5 Rs1 (mword_of_int 72 : mword 12)
                E1 (trap_res b + (K - 4))%nat (List.last (map bnode o1) bhead) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi36 [Hbp] [-]").
      { iEval (rgpeel; rewrite HE1s1). iExact "Hbp". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hbp".
      iEval (rgpeel; rewrite HE1s1) in "Hbp".
      set (E2 := <[Regidx Ra5 := regval_into_reg (List.last (map bnode o1) bhead)]> E1).
      assert (HE2s1 : E2 !!! Regidx Rs1 = bnode k)
        by (rewrite /E2 upd_ne; [exact HE1s1 | vm_compute; discriminate]).
      assert (HE2a4 : E2 !!! Regidx Ra4 = List.hd bhead (map bnode o2))
        by (rewrite /E2 upd_ne; [exact HE1a4 | vm_compute; discriminate]).
      assert (HE2a5 : E2 !!! Regidx Ra5 = List.last (map bnode o1) bhead)
        by (rewrite /E2; apply upd_eq).
      assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.brelse + 0x36) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x38))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp38) in "Hpc".
      (* +0x38 c.sd a5,72(a4) : b->next->prev = b->prev *)
      iApply (wp_csd_s_sconf (mword_of_int (KernelSyms.brelse + 0x38)) Ra5 Ra4 (mword_of_int 72 : mword 12)
                E2 (trap_res b + (K - 4))%nat (bnode k) false with "Hcg Hpc Hi38 [Hsp] [-]").
      { iEval (rgpeel; rewrite HE2a4). iExact "Hsp". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hsp".
      iEval (rgpeel) in "Hsp".
      iEval (rewrite HE2a4 HE2a5) in "Hsp".
      assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.brelse + 0x38) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x3a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3a) in "Hpc".
      (* +0x3a c.ld a4,80(s1) : a4 := b->next, again *)
      iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.brelse + 0x3a)) Ra4 Rs1 (mword_of_int 80 : mword 12)
                E2 (trap_res b + (K - 4))%nat (List.hd bhead (map bnode o2)) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi3a [Hbn] [-]").
      { iEval (rgpeel; rewrite HE2s1). iExact "Hbn". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hbn".
      iEval (rgpeel; rewrite HE2s1) in "Hbn".
      set (E3 := <[Regidx Ra4 := regval_into_reg (List.hd bhead (map bnode o2))]> E2).
      assert (HE3s1 : E3 !!! Regidx Rs1 = bnode k)
        by (rewrite /E3 upd_ne; [exact HE2s1 | vm_compute; discriminate]).
      assert (HE3a4 : E3 !!! Regidx Ra4 = List.hd bhead (map bnode o2))
        by (rewrite /E3; apply upd_eq).
      assert (HE3a5 : E3 !!! Regidx Ra5 = List.last (map bnode o1) bhead)
        by (rewrite /E3 upd_ne; [exact HE2a5 | vm_compute; discriminate]).
      assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.brelse + 0x3a) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x3c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3c) in "Hpc".
      (* +0x3c c.sd a4,80(a5) : b->prev->next = b->next *)
      iApply (wp_csd_s_sconf (mword_of_int (KernelSyms.brelse + 0x3c)) Ra4 Ra5 (mword_of_int 80 : mword 12)
                E3 (trap_res b + (K - 4))%nat (bnode k) false with "Hcg Hpc Hi3c [Hpn] [-]").
      { iEval (rgpeel; rewrite HE3a5). iExact "Hpn". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hpn".
      iEval (rgpeel) in "Hpn".
      iEval (rewrite HE3a5 HE3a4) in "Hpn".
      iDestruct ("Hrelink" with "Hpn Hsp") as "Hlru".
      (* ---- reinsert after the head ---- *)
      iDestruct (bcache_lru_splice bhead (map bnode o1 ++ map bnode o2)%list with "Hlru")
        as "(Hhn & Hhp & Hsplice)".
      iPoseProof (bri_3e with "Htext") as "Hi3e".
      iPoseProof (bri_42 with "Htext") as "Hi42".
      iPoseProof (bri_46 with "Htext") as "Hi46".
      iPoseProof (bri_4a with "Htext") as "Hi4a".
      iPoseProof (bri_4c with "Htext") as "Hi4c".
      iPoseProof (bri_50 with "Htext") as "Hi50".
      iPoseProof (bri_54 with "Htext") as "Hi54".
      iPoseProof (bri_56 with "Htext") as "Hi56".
      iPoseProof (bri_5a with "Htext") as "Hi5a".
      iPoseProof (bri_5c with "Htext") as "Hi5c".
      assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.brelse + 0x3c) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x3e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3e) in "Hpc".
      (* +0x3e / +0x42 : a5 := bcache + 0x8000 *)
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.brelse + 0x3e)) Ra5 (mword_of_int 29 : mword 20)
                E3 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi3e [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      set (E4 := <[Regidx Ra5 := regval_into_reg
                    (add_vec (mword_of_int (KernelSyms.brelse + 0x3e) : mword 64)
                       (auipc_off (mword_of_int 29 : mword 20)))]> E3).
      assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.brelse + 0x3e) : mword 64) 4 = mword_of_int (KernelSyms.brelse + 0x42))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.brelse + 0x42)) Ra5 Ra5 (mword_of_int 1366 : mword 12)
                E4 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi42 [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      iEval (rgpeel) in "Hcg".
      set (E5 := <[Regidx Ra5 := regval_into_reg
                    (add_vec (E4 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 1366 : mword 12)))]> E4).
      assert (HE5hn : add_vec (E5 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 696 : mword 12))
                      = bnext bhead).
      { rewrite /E5 upd_eq /E4 upd_eq. apply bv_eq; vm_compute; reflexivity. }
      assert (HE5s1 : E5 !!! Regidx Rs1 = bnode k).
      { rewrite /E5 upd_ne; [| vm_compute; discriminate].
        rewrite /E4 upd_ne; [exact HE3s1 | vm_compute; discriminate]. }
      assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.brelse + 0x42) : mword 64) 4 = mword_of_int (KernelSyms.brelse + 0x46))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp46) in "Hpc".
      (* +0x46 ld a4,696(a5) : a4 := bcache.head.next *)
      iApply (wp_ld_s_sconf (mword_of_int (KernelSyms.brelse + 0x46)) Ra4 Ra5 (mword_of_int 696 : mword 12)
                E5 (trap_res b + (K - 4))%nat (List.hd bhead (map bnode o1 ++ map bnode o2)%list) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi46 [Hhn] [-]").
      { iEval (rgpeel; rewrite HE5hn). iExact "Hhn". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hhn".
      iEval (rgpeel; rewrite HE5hn) in "Hhn".
      set (E6 := <[Regidx Ra4 := regval_into_reg
                    (List.hd bhead (map bnode o1 ++ map bnode o2)%list)]> E5).
      assert (HE6s1 : E6 !!! Regidx Rs1 = bnode k)
        by (rewrite /E6 upd_ne; [exact HE5s1 | vm_compute; discriminate]).
      assert (HE6a4 : E6 !!! Regidx Ra4 = List.hd bhead (map bnode o1 ++ map bnode o2)%list)
        by (rewrite /E6; apply upd_eq).
      assert (HE6hn : add_vec (E6 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 696 : mword 12))
                      = bnext bhead).
      { rewrite /E6 upd_ne; [exact HE5hn | vm_compute; discriminate]. }
      assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.brelse + 0x46) : mword 64) 4 = mword_of_int (KernelSyms.brelse + 0x4a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4a) in "Hpc".
      (* +0x4a c.sd a4,80(s1) : b->next = bcache.head.next *)
      iApply (wp_csd_s_sconf (mword_of_int (KernelSyms.brelse + 0x4a)) Ra4 Rs1 (mword_of_int 80 : mword 12)
                E6 (trap_res b + (K - 4))%nat (List.hd bhead (map bnode o2)) false
                with "Hcg Hpc Hi4a [Hbn] [-]").
      { iEval (rgpeel; rewrite HE6s1). iExact "Hbn". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hbn".
      iEval (rgpeel) in "Hbn".
      iEval (rewrite HE6s1 HE6a4) in "Hbn".
      assert (Hpp4c : add_vec_int (mword_of_int (KernelSyms.brelse + 0x4a) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x4c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4c) in "Hpc".
      (* +0x4c / +0x50 : a4 := &bcache.head *)
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.brelse + 0x4c)) Ra4 (mword_of_int 29 : mword 20)
                E6 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi4c [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      set (E7 := <[Regidx Ra4 := regval_into_reg
                    (add_vec (mword_of_int (KernelSyms.brelse + 0x4c) : mword 64)
                       (auipc_off (mword_of_int 29 : mword 20)))]> E6).
      assert (Hpp50 : add_vec_int (mword_of_int (KernelSyms.brelse + 0x4c) : mword 64) 4 = mword_of_int (KernelSyms.brelse + 0x50))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp50) in "Hpc".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.brelse + 0x50)) Ra4 Ra4 (mword_of_int 1968 : mword 12)
                E7 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi50 [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      iEval (rgpeel) in "Hcg".
      set (E8 := <[Regidx Ra4 := regval_into_reg
                    (add_vec (E7 !!! Regidx Ra4) (sign_extend' 64 (mword_of_int 1968 : mword 12)))]> E7).
      assert (HE8a4 : E8 !!! Regidx Ra4 = bhead).
      { rewrite /E8 upd_eq /E7 upd_eq. apply bv_eq; vm_compute; reflexivity. }
      assert (HE8s1 : E8 !!! Regidx Rs1 = bnode k).
      { rewrite /E8 upd_ne; [| vm_compute; discriminate].
        rewrite /E7 upd_ne; [exact HE6s1 | vm_compute; discriminate]. }
      assert (HE8hn : add_vec (E8 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 696 : mword 12))
                      = bnext bhead).
      { rewrite /E8 upd_ne; [| vm_compute; discriminate].
        rewrite /E7 upd_ne; [exact HE6hn | vm_compute; discriminate]. }
      assert (Hpp54 : add_vec_int (mword_of_int (KernelSyms.brelse + 0x50) : mword 64) 4 = mword_of_int (KernelSyms.brelse + 0x54))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp54) in "Hpc".
      (* +0x54 c.sd a4,72(s1) : b->prev = &bcache.head *)
      iApply (wp_csd_s_sconf (mword_of_int (KernelSyms.brelse + 0x54)) Ra4 Rs1 (mword_of_int 72 : mword 12)
                E8 (trap_res b + (K - 4))%nat (List.last (map bnode o1) bhead) false
                with "Hcg Hpc Hi54 [Hbp] [-]").
      { iEval (rgpeel; rewrite HE8s1). iExact "Hbp". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hbp".
      iEval (rgpeel) in "Hbp".
      iEval (rewrite HE8s1 HE8a4) in "Hbp".
      assert (Hpp56 : add_vec_int (mword_of_int (KernelSyms.brelse + 0x54) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x56))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp56) in "Hpc".
      (* +0x56 ld a4,696(a5) : a4 := bcache.head.next, again *)
      iApply (wp_ld_s_sconf (mword_of_int (KernelSyms.brelse + 0x56)) Ra4 Ra5 (mword_of_int 696 : mword 12)
                E8 (trap_res b + (K - 4))%nat (List.hd bhead (map bnode o1 ++ map bnode o2)%list) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi56 [Hhn] [-]").
      { iEval (rgpeel; rewrite HE8hn). iExact "Hhn". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hhn".
      iEval (rgpeel; rewrite HE8hn) in "Hhn".
      set (E9 := <[Regidx Ra4 := regval_into_reg
                    (List.hd bhead (map bnode o1 ++ map bnode o2)%list)]> E8).
      assert (HE9s1 : E9 !!! Regidx Rs1 = bnode k)
        by (rewrite /E9 upd_ne; [exact HE8s1 | vm_compute; discriminate]).
      assert (HE9a4 : E9 !!! Regidx Ra4 = List.hd bhead (map bnode o1 ++ map bnode o2)%list)
        by (rewrite /E9; apply upd_eq).
      assert (HE9hn : add_vec (E9 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 696 : mword 12))
                      = bnext bhead)
        by (rewrite /E9 upd_ne; [exact HE8hn | vm_compute; discriminate]).
      assert (Hpp5a : add_vec_int (mword_of_int (KernelSyms.brelse + 0x56) : mword 64) 4 = mword_of_int (KernelSyms.brelse + 0x5a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp5a) in "Hpc".
      (* +0x5a c.sd s1,72(a4) : bcache.head.next->prev = b *)
      iApply (wp_csd_s_sconf (mword_of_int (KernelSyms.brelse + 0x5a)) Rs1 Ra4 (mword_of_int 72 : mword 12)
                E9 (trap_res b + (K - 4))%nat bhead false with "Hcg Hpc Hi5a [Hhp] [-]").
      { iEval (rgpeel; rewrite HE9a4). iExact "Hhp". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hhp".
      iEval (rgpeel) in "Hhp".
      iEval (rewrite HE9a4 HE9s1) in "Hhp".
      assert (Hpp5c : add_vec_int (mword_of_int (KernelSyms.brelse + 0x5a) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x5c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp5c) in "Hpc".
      (* +0x5c sd s1,696(a5) : bcache.head.next = b *)
      iApply (wp_sd_s_sconf (mword_of_int (KernelSyms.brelse + 0x5c)) Rs1 Ra5 (mword_of_int 696 : mword 12)
                E9 (trap_res b + (K - 4))%nat (List.hd bhead (map bnode o1 ++ map bnode o2)%list) false
                with "Hcg Hpc Hi5c [Hhn] [-]").
      { iEval (rgpeel; rewrite HE9hn). iExact "Hhn". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hhn".
      iEval (rgpeel) in "Hhn".
      iEval (rewrite HE9hn HE9s1) in "Hhn".
      iDestruct ("Hsplice" $! (bnode k) with "Hhn Hhp Hbn Hbp") as "Hlru".
      (* ---- the new order, still a permutation of [seq 0 NBUF] ---- *)
      assert (Hord' : (k :: (o1 ++ o2))%list ≡ₚ seq 0 NBUF).
      { rewrite -Hord Hordeq.
        first [ apply Permutation_middle | symmetry; apply Permutation_middle ]. }
      assert (Hmapeq : map bnode (k :: (o1 ++ o2))%list
                       = (bnode k :: (map bnode o1 ++ map bnode o2))%list)
        by (cbn [List.map]; rewrite map_app; reflexivity).
      iEval (rewrite -Hmapeq) in "Hlru".
      assert (Hpp60 : add_vec_int (mword_of_int (KernelSyms.brelse + 0x5c) : mword 64) 4 = mword_of_int (KernelSyms.brelse + 0x60))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp60) in "Hpc".
      (* ---- rebuild the bcache resource and run the tail ---- *)
      iAssert (bcache_res bn V) with "[Hauth Hsauth Hlru Hpool Hslots]" as "HRres".
      { iExists (delete k Mg), (k :: (o1 ++ o2))%list, devs, bnos.
        iFrame "Hauth Hsauth".
        iSplitR; [iPureIntro; exact Hdom'|].
        iSplitR; [iPureIntro; exact Hord'|].
        iSplitR; [iPureIntro; exact Hinj|].
          iSplitR; [iPureIntro; exact Hdev|].
        iFrame "Hlru Hpool Hslots". }
      assert (HE9sp : E9 !!! Regidx csp_rs1 = spr).
      { rewrite /E9 upd_ne; [| vm_compute; discriminate].
        rewrite /E8 upd_ne; [| vm_compute; discriminate].
        rewrite /E7 upd_ne; [| vm_compute; discriminate].
        rewrite /E6 upd_ne; [| vm_compute; discriminate].
        rewrite /E5 upd_ne; [| vm_compute; discriminate].
        rewrite /E4 upd_ne; [| vm_compute; discriminate].
        rewrite /E3 upd_ne; [| vm_compute; discriminate].
        rewrite /E2 upd_ne; [| vm_compute; discriminate].
        rewrite /E1 upd_ne; [| vm_compute; discriminate].
        rewrite /D2 upd_ne; [| vm_compute; discriminate].
        rewrite /D1 upd_ne; [exact HmQsp | vm_compute; discriminate]. }
      assert (HE9thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
                E9 !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N9 N18.
        rewrite /E9 upd_ne; [| regne].
        rewrite /E8 upd_ne; [| regne].
        rewrite /E7 upd_ne; [| regne].
        rewrite /E6 upd_ne; [| regne].
        rewrite /E5 upd_ne; [| regne].
        rewrite /E4 upd_ne; [| regne].
        rewrite /E3 upd_ne; [| regne].
        rewrite /E2 upd_ne; [| regne].
        rewrite /E1 upd_ne; [| regne].
        rewrite /D2 upd_ne; [| regne].
        rewrite /D1 upd_ne; [| regne]. exact (HmQthr c Hcs N2 N8 N9 N18). }
      iApply (brelse_tail (CID0 := CIDa)  bn V m E9 K b p C HK HE9sp HE9thr
                with "Hcg Htext Hpc Hlock Htok HRres Hcnt Hpay Hr24 Hr16 Hr8 Hg4 [-]").
      iIntros (CIDf Hsf mf) "%Hcsf Hcg Hcnt Hpc".
      iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "[%] Hcg Hcnt Hpc Hppid [Hfd]").
      { exact Hcsf. }
      { rewrite /bslot. iExact "Hfd". }
    (* ================= a SURVIVING reference: no splice ============== *)
    - assert (Hex : exists c', cnt = Pos.succ c').
      { exists (Pos.pred cnt). symmetry. by apply Pos.succ_pred. }
      destruct Hex as [cnt' Hcnt']. subst cnt.
      assert (Hlt : (q < qt)%Qp) by (apply Hltn; apply Pos.succ_not_1).
      assert (Hsub : exists qr', (qt - q)%Qp = Some qr').
      { apply Qp.lt_sum in Hlt as [r Hr]. exists r. by apply Qp.sub_Some. }
      destruct Hsub as [qr' Hsub].
      assert (Hsub' : qt = (q + qr')%Qp) by (by apply Qp.sub_Some).
      iEval (rewrite -Hpa) in "Hcell".
      iApply (wp_clw_s_sconf (mword_of_int (KernelSyms.brelse + 0x2c)) Ra5 Rs1 (mword_of_int 64 : mword 12)
                mQ (trap_res b + (K - 4))%nat (mword_of_int (Z.pos (Pos.succ cnt')) : mword 32) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi2c Hcell [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hcell".
      iEval (rewrite Hpa) in "Hcell".
      set (D1 := <[Regidx Ra5 := regval_into_reg
                    (sign_extend' 64 (mword_of_int (Z.pos (Pos.succ cnt')) : mword 32))]> mQ).
      assert (HD1a5 : D1 !!! Regidx Ra5
                      = sign_extend' 64 (mword_of_int (Z.pos (Pos.succ cnt')) : mword 32))
        by (rewrite /D1; apply upd_eq).
      assert (HD1s1 : D1 !!! Regidx Rs1 = bnode k)
        by (rewrite /D1 upd_ne; [exact HmQs1 | vm_compute; discriminate]).
      assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.brelse + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x2e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2e) in "Hpc".
      iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.brelse + 0x2e)) Ra5 (mword_of_int 63 : mword 6)
                D1 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi2e [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      iEval (rgpeel) in "Hcg".
      set (D2 := <[Regidx Ra5 := regval_into_reg
                    (sign_extend' 64 (subrange_vec_dec
                       (add_vec (D1 !!! Regidx Ra5)
                          (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))]> D1).
      assert (HD2s1 : D2 !!! Regidx Rs1 = bnode k)
        by (rewrite /D2 upd_ne; [exact HD1s1 | vm_compute; discriminate]).
      assert (Hzp : (Z.pos (Pos.succ cnt') - 1)%Z = Z.pos cnt')
        by (rewrite Pos2Z.inj_succ; lia).
      assert (HD2a5 : D2 !!! Regidx Ra5
                      = sign_extend' 64 (mword_of_int (Z.pos cnt') : mword 32)).
      { rewrite /D2 upd_eq. unfold regval_into_reg. rewrite HD1a5.
        rewrite decr64_sext. rewrite (decr32_pos (Pos.succ cnt') Hcnt). by rewrite Hzp. }
      assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.brelse + 0x2e) : mword 64) 2 = mword_of_int (KernelSyms.brelse + 0x30))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp30) in "Hpc".
      assert (Hpa2 : add_vec (rget D2 Rs1) (sign_extend' 64 (mword_of_int 64 : mword 12))
                     = brefcnt k).
      { rgne. rewrite HD2s1 Hs64. rewrite /brefcnt /bpa /pa_add /add_vec_int. reflexivity. }
      iEval (rewrite -Hpa2) in "Hcell".
      iApply (wp_csw_s_sconf (mword_of_int (KernelSyms.brelse + 0x30)) Ra5 Rs1 (mword_of_int 64 : mword 12)
                D2 (trap_res b + (K - 4))%nat (mword_of_int (Z.pos (Pos.succ cnt')) : mword 32) false
                with "Hcg Hpc Hi30 Hcell [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hcell".
      iEval (rewrite Hpa2) in "Hcell".
      iEval (rgpeel) in "Hcell".
      assert (Hstv : trunc32 (D2 !!! Regidx Ra5) = (mword_of_int (Z.pos cnt') : mword 32)).
      { rewrite HD2a5. apply trunc32_sext. }
      iEval (rewrite Hstv) in "Hcell".
      (* the ghost step: the departing fraction rejoins the retainder *)
      iMod (bio_decr_step bn Mg k q qt cnt' qr' HMk Hsub with "Hauth Hrtok") as "Hauth".
      iAssert (b_dev (bpa k) ↦₄{DfracOwn (qr + q)} (devs k))%I
        with "[Hrdev Hdev]" as "Hdev".
      { rewrite word4_pointsto_frac_split. iFrame "Hdev Hrdev". }
      iAssert (b_blockno (bpa k) ↦₄{DfracOwn (qr + q)} (bnos k))%I
        with "[Hrbno Hbno]" as "Hbno".
      { rewrite word4_pointsto_frac_split. iFrame "Hbno Hrbno". }
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
        { iPureIntro. exact (br_decr_tie qt qr q qr' Htie Hsub'). }
        iFrame "Hdev Hbno". }
      iDestruct ("Hback" $! (<[k := (qr', cnt')]> Mg) devs bnos with "[%] Hslot") as "Hslots".
      { intros j Hj. split_and!;
          [ rewrite lookup_insert_ne; [reflexivity | congruence] | reflexivity | reflexivity ]. }
      iAssert (bcache_res bn V) with "[Hauth Hsauth Hlru Hpool Hslots]" as "HRres".
      { iExists (<[k := (qr', cnt')]> Mg), ord, devs, bnos.
        iFrame "Hauth Hsauth".
        iSplitR.
        { iPureIntro. intros j Hj.
          destruct (decide (j = k)) as [->|Hnk]; [exact Hk|].
          apply Hdom. by rewrite lookup_insert_ne in Hj. }
        iSplitR; [iPureIntro; exact Hord|].
        iSplitR; [iPureIntro; exact Hinj|].
          iSplitR; [iPureIntro; exact Hdev|].
        iFrame "Hlru Hpool Hslots". }
      (* ===== +0x32 c.bnez a5 : TAKEN, straight to the release ===== *)
      assert (Hbnez : neq_vec (D2 !!! Regidx Ra5) zero_reg = true).
      { rewrite HD2a5. apply brc_word_nonzero_neqv.
        rewrite Pos2Z.inj_succ in Hcnt. lia. }
      iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.brelse + 0x32)) (mword_of_int 23 : mword 8)
                (Cregidx (mword_of_int 7)) Ra5 D2 (trap_res b + (K - 4))%nat false
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; exact Hbnez)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi32 [-]").
      iApply bi.later_intro.
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      assert (Htgt60 : add_vec (mword_of_int (KernelSyms.brelse + 0x32) : mword 64)
                         (sign_extend' 64 (sign_extend' 13
                            (concat_vec (mword_of_int 23 : mword 8) ('b"0"))))
                       = mword_of_int (KernelSyms.brelse + 0x60))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt60) in "Hpc".
      assert (HD2sp : D2 !!! Regidx csp_rs1 = spr).
      { rewrite /D2 upd_ne; [| vm_compute; discriminate].
        rewrite /D1 upd_ne; [exact HmQsp | vm_compute; discriminate]. }
      assert (HD2thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
                D2 !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N9 N18.
        rewrite /D2 upd_ne; [| regne].
        rewrite /D1 upd_ne; [| regne]. exact (HmQthr c Hcs N2 N8 N9 N18). }
      iApply (brelse_tail (CID0 := CIDa)  bn V m D2 K b p C HK HD2sp HD2thr
                with "Hcg Htext Hpc Hlock Htok HRres Hcnt Hpay Hr24 Hr16 Hr8 Hg4 [-]").
      iIntros (CIDf Hsf mf) "%Hcsf Hcg Hcnt Hpc".
      iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "[%] Hcg Hcnt Hpc Hppid [Hout]").
      { exact Hcsf. }
      { rewrite /bslot. iExact "Hout". }
  Qed.

End ProofBrelse.

End BrelseProof.
