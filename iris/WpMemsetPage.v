(* WpMemsetPage.v -- a PAGE-LEVEL S-mode WP for the kernel's [memset], tailored
   to zero/fill a whole 4096-byte page for kalloc/kfree.

   [wp_memset_page] wraps [wp_memset_s_full_kt] (WpMemsetInstr.v): it DERIVES all
   of that lemma's ~30 per-byte side conditions (Sv39 canonicality, the identity
   translation, the gigapage svpn masks, the per-byte PMP TOR match, the pointer
   arithmetic) from the single fact that the page base [p] is RAM-resident and
   4096-aligned ([page_valid p]), and bridges [page_own p] to memset's per-byte
   buffer.  This is the last blocker for both the kalloc and kfree instruction
   proofs. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpGpr WpGprRvc WpGprLoad.
Require Import SmodeCore WpSmodeGpr WpEntryNew WpMemsetS.
Require Import WpMemsetInstr.
Require Import CalleeSaved.
Require Import WpLock KallocInv.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  Pure helpers: [add_vec] arithmetic, the address correspondence, and    *)
(*  the page-level geometry.                                               *)
(* ===================================================================== *)

Lemma add_vec_unsigned (x y : mword 64) :
  bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y).
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  rewrite bv_add_unsigned. reflexivity.
Qed.

Lemma moi_unsigned (k : Z) : bv_unsigned (mword_of_int k : mword 64) = bv_wrap 64 k.
Proof.
  unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned. reflexivity.
Qed.

(* [ms_a8]/[ms_pa] are the store's translated (identity) byte address; on
   64-bit both are the identity, and [ms_addr p j] is definitionally [pa_add p
   j].  Hence memset's per-byte address [ms_pa (ms_addr p j)] is exactly the
   [pa_add p j] that [page_own] tiles. *)
Lemma ms_a8_id (cur : mword 64) : ms_a8 cur = cur.
Proof.
  unfold ms_a8.
  assert (H0 : sign_extend' 64 (mword_of_int 0 : mword 12) = (mword_of_int 0 : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H0.
  assert (Hc : add_vec cur (mword_of_int 0 : mword 64) = cur) by (exact (avi0 cur)).
  rewrite Hc. rewrite subrange_id. rewrite sign_extend'_id. reflexivity.
Qed.

Lemma ms_pa_id (cur : mword 64) : ms_pa cur = cur.
Proof.
  unfold ms_pa. change (0 * 1)%Z with 0%Z.
  rewrite avi0. rewrite zero_extend'_id. apply ms_a8_id.
Qed.

Lemma ms_addr_pa_add (p : mword 64) (j : nat) : ms_addr p j = pa_add p j.
Proof. unfold ms_addr, pa_add, add_vec_int. reflexivity. Qed.

Lemma ms_pa_ms_addr (p : mword 64) (j : nat) : ms_pa (ms_addr p j) = pa_add p j.
Proof. rewrite ms_pa_id. apply ms_addr_pa_add. Qed.

Lemma ms_a8_ms_addr (p : mword 64) (j : nat) : ms_a8 (ms_addr p j) = pa_add p j.
Proof. rewrite ms_a8_id. apply ms_addr_pa_add. Qed.

(* the c.addi increment [ms_incr1] is just [1]. *)
Lemma ms_incr1_one : ms_incr1 = (mword_of_int 1 : mword 64).
Proof. unfold ms_incr1. apply bv_eq; vm_compute; reflexivity. Qed.

(* pointer arithmetic: the c.addi advances the byte offset by one (any j). *)
Lemma ms_incr_step (p : mword 64) (j : nat) :
  add_vec (ms_addr p j) ms_incr1 = ms_addr p (S j).
Proof.
  rewrite ms_incr1_one. rewrite !ms_addr_pa_add. unfold pa_add, add_vec_int.
  apply bv_eq. rewrite !add_vec_unsigned. rewrite !moi_unsigned.
  rewrite Nat2Z.inj_succ.
  rewrite !bv_wrap_add_idemp_r. rewrite !bv_wrap_add_idemp_l.
  f_equal. lia.
Qed.

(* memset's frame alloc (c.addi16sp sp,-16 ; encoded imm 48 = -16 in 6-bit)
   and dealloc (c.addi16sp sp,+16 ; imm 16) cancel, so sp is net-preserved. *)
Lemma add_vec_frame_cancel (X : mword 64) :
  add_vec (add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = X.
Proof.
  apply bv_eq. rewrite !add_vec_unsigned. rewrite bv_wrap_add_idemp_l.
  assert (HA : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)) : mword 64)
             = 18446744073709551600) by (vm_compute; reflexivity).
  assert (HB : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)) : mword 64)
             = 16) by (vm_compute; reflexivity).
  rewrite HA HB. rewrite <- Z.add_assoc.
  replace (18446744073709551600 + 16) with (bv_modulus 64) by (vm_compute; reflexivity).
  rewrite bv_wrap_add_modulus_1. apply bv_wrap_bv_unsigned.
Qed.

(* ---- page validity gives RAM residency for the base and every byte ---- *)

Lemma page_valid_ram (p : mword 64) : page_valid p -> addr_is_ram p.
Proof.
  intros [_ [Hlo Hhi]]. unfold addr_is_ram, kmem_lo, kmem_hi in *.
  unfold ram_base, ram_size. lia.
Qed.

Lemma uint_pa_add_page (p : mword 64) (j : nat) :
  page_valid p -> (j < 4096)%nat -> uint (pa_add p j) = uint p + Z.of_nat j.
Proof.
  intros Hpv Hj. pose proof (page_valid_ram p Hpv) as Hr.
  apply uint_pa_add.
  destruct Hr as [_ Hhi]. unfold ram_base, ram_size in Hhi. lia.
Qed.

Lemma page_valid_ram_j (p : mword 64) (j : nat) :
  page_valid p -> (j < 4096)%nat -> addr_is_ram (pa_add p j).
Proof.
  intros Hpv Hj. pose proof Hpv as [_ [Hlo Hhi]].
  unfold kmem_lo, kmem_hi in *.
  unfold addr_is_ram. rewrite (uint_pa_add_page p j Hpv Hj).
  unfold ram_base, ram_size. lia.
Qed.

(* STEP 3 (the crux): adding an in-page offset [j < 4096] to a 4096-aligned RAM
   base leaves the Sv39 VPN unchanged, because it only touches bits [11:0]. *)
Lemma svpn_pa_add_same (p : mword 64) (j : nat) :
  page_valid p -> (j < 4096)%nat -> svpn_of (pa_add p j) = svpn_of p.
Proof.
  intros Hpv Hj.
  pose proof (page_valid_ram p Hpv) as Hrp.
  pose proof (page_valid_ram_j p j Hpv Hj) as Hrj.
  apply bv_eq.
  rewrite (svpn_of_unsigned _ Hrj) (svpn_of_unsigned _ Hrp).
  rewrite (uint_pa_add_page p j Hpv Hj).
  destruct Hpv as [Hal _]. unfold page_aligned, PGSIZE in Hal.
  rewrite (Z.shiftr_div_pow2 (uint p + Z.of_nat j) 12 ltac:(lia))
          (Z.shiftr_div_pow2 (uint p) 12 ltac:(lia)).
  change (2 ^ 12) with 4096.
  apply Z.mod_divide in Hal; [| lia]. destruct Hal as [q Hq]. rewrite Hq.
  rewrite (Z.div_add_l q 4096 (Z.of_nat j) ltac:(lia)).
  rewrite (Z.div_small (Z.of_nat j) 4096 ltac:(lia)).
  rewrite Z.add_0_r.
  rewrite (Z.div_mul q 4096 ltac:(lia)). reflexivity.
Qed.

(* the end pointer [p + 4096] compared against [p + (j+1)]: no 2^64 wraparound
   inside a valid page, so equality of the compared pointers is equality of the
   byte offsets. *)
Lemma ms_cmp_page (p : mword 64) (j : nat) :
  page_valid p -> (j < 4096)%nat ->
  neq_vec (ms_addr p (S j)) (add_vec (mword_of_int 4096 : mword 64) p)
    = negb (Nat.eqb (S j) 4096).
Proof.
  intros Hpv Hj.
  pose proof Hpv as [_ [Hplo Hphi]]. unfold kmem_lo, kmem_hi in *.
  assert (Hup : bv_unsigned p = uint p) by (rewrite uint_unsigned; reflexivity).
  assert (HxL : bv_unsigned (ms_addr p (S j)) = uint p + Z.of_nat (S j)).
  { rewrite ms_addr_pa_add. unfold pa_add, add_vec_int.
    rewrite add_vec_unsigned moi_unsigned. rewrite Hup.
    rewrite (bv_wrap_small 64 (Z.of_nat (S j)) ltac:(unfold bv_modulus; simpl; lia)).
    apply bv_wrap_small. unfold bv_modulus; simpl. lia. }
  assert (HeL : bv_unsigned (add_vec (mword_of_int 4096 : mword 64) p) = uint p + 4096).
  { rewrite add_vec_unsigned moi_unsigned. rewrite Hup.
    rewrite (bv_wrap_small 64 4096 ltac:(unfold bv_modulus; simpl; lia)).
    rewrite (Z.add_comm 4096 (uint p)).
    apply bv_wrap_small. unfold bv_modulus; simpl. lia. }
  unfold neq_vec. f_equal.
  destruct (Nat.eqb_spec (S j) 4096) as [He | Hne].
  - apply eq_vec_true_iff. apply bv_eq. rewrite HxL HeL He. reflexivity.
  - apply eq_vec_false_iff. intro Hc. apply (f_equal bv_unsigned) in Hc.
    rewrite HxL HeL in Hc. lia.
Qed.

Section WpMemsetPage.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  (* Choice: a big-sep of per-element existentials over a [seq] yields a single
     witness FUNCTION indexed by the element.  (Elements of a [seq] are
     distinct, so the pointwise function-update introduces no collision.) *)
  Lemma bytes_choose (n : nat) :
    forall (start : nat) (P : nat -> bv 8 -> iProp Σ),
    ([∗ list] k ∈ seq start n, ∃ b : bv 8, P k b) ⊢
    ∃ f : nat -> bv 8, [∗ list] k ∈ seq start n, P k (f k).
  Proof.
    induction n as [|n IH]; intros start P.
    - iIntros "_". iExists (fun _ => bv_0 8). done.
    - cbn [seq]. rewrite big_sepL_cons.
      iIntros "[Hh Ht]". iDestruct "Hh" as (b) "Hh".
      iDestruct (IH (S start) P with "Ht") as (f) "Ht".
      iExists (fun k => if Nat.eq_dec k start then b else f k).
      rewrite big_sepL_cons. iSplitL "Hh".
      + destruct (Nat.eq_dec start start) as [_|Hne]; [ iExact "Hh" | done ].
      + iApply (big_sepL_impl with "Ht"). iIntros "!>" (k y Hy) "H".
        destruct (Nat.eq_dec y start) as [He|_].
        * exfalso. apply elem_of_list_lookup_2 in Hy. apply elem_of_seq in Hy. lia.
        * iExact "H".
  Qed.

  (* =================================================================== *)
  (*  THE PAGE-LEVEL memset WP.  memset(p, cval, 4096) fills a whole valid *)
  (*  page, consuming and returning [page_own p].  All of                  *)
  (*  wp_memset_s_full_kt's ~30 per-byte side conditions are DERIVED from   *)
  (*  [page_valid p]; the ~15 standard S-mode config facts are kept.        *)
  (* =================================================================== *)
  Lemma wp_memset_page (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (m0 : gmap regidx (mword 64)) (cval : mword 64) (vra vs0 : bv 64)
      (γ : gname) {dq : dfrac} :
    let ra_idx : mword 5 := mword_of_int 1 in
    let s0_idx : mword 5 := mword_of_int 8 in
    let a0_idx : mword 5 := mword_of_int 10 in
    let a1_idx : mword 5 := mword_of_int 11 in
    let a2_idx : mword 5 := mword_of_int 12 in
    let pcE := mword_of_int KernelSyms.memset in
    let imm_entry : mword 6 := mword_of_int 48 in
    let sp' := add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry)) in
    let ra0 := m0 !!! Regidx ra_idx in
    let s00 := m0 !!! Regidx s0_idx in
    let p := m0 !!! Regidx a0_idx in
    let ea_ra := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let pa_ra := ea_ra in
    let ea_s0 := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let pa_s0 := ea_s0 in
    let ret_tgt := update_vec_dec (add_vec ra0 (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    (* the page being filled: RAM-resident, 4096-aligned, in [end, PHYSTOP) *)
    page_valid p ->
    (* argument setup by the caller before the [jal memset] *)
    m0 !!! Regidx a1_idx = cval ->
    m0 !!! Regidx a2_idx = (mword_of_int 4096 : mword 64) ->
    (* standard S-mode config side conditions (unchanged from the callee) *)
    ↑minstretN ⊆ E ->
    (* the caller's return target's low bit is clear (a 2-aligned target is
       fine: memset returns via [exec_jump_to_zca], Zca always enabled) *)
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    smode_config γ dq -∗
    tlb_inv root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m0 -∗
    pa_ra ↦₈ vra -∗
    pa_s0 ↦₈ vs0 -∗
    page_own p -∗
    ( ∀ mfin,
      smode_config γ dq -∗
      tlb_inv root_ppn -∗
      pc_is ret_tgt -∗
      pa_ra ↦₈ ra0 -∗
      pa_s0 ↦₈ s00 -∗
      page_own p -∗
      gpr_file mfin -∗
      ⌜ callee_saved m0 mfin ⌝ -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ra_idx s0_idx a0_idx a1_idx a2_idx pcE imm_entry sp' ra0 s00 p
      ea_ra pa_ra ea_s0 pa_s0 ret_tgt
      Hpv Hcval Ha2 HN Hret0.
    iIntros "Hsm Htlbinv
             #Htext Hpc Hfile Hbra Hbs0 Hpage Hcont".
    (* --- bridge [page_own p] to memset's per-byte buffer --- *)
    iEval (rewrite /page_own /byte_any) in "Hpage".
    iDestruct (bytes_choose 4096 0 (fun j b => ((pa_add p j) ↦ₘ b)%I) with "Hpage")
      as (olds) "Hpage".
    iAssert ([∗ list] j ∈ seq 0 4096, (ms_pa (ms_addr p j)) ↦ₘ olds j)%I
      with "[Hpage]" as "Hbuf".
    { iApply (big_sepL_impl with "Hpage"). iIntros "!>" (k j _) "H".
      rewrite ms_pa_ms_addr. iExact "H". }
    (* --- apply the whole-function memset WP, discharging all geometry --- *)
    pose proof (page_valid_ram p Hpv) as Hramp.
    iApply (wp_memset_s_full root_ppn E Φ m0 4096
              (add_vec (mword_of_int 4096 : mword 64) p) (svpn_of p) olds vra vs0
              γ (dq:=dq)
              HN ltac:(lia)
              add_vec_frame_cancel
              (* Hbexec_add : the add computes a4 := 4096 + p *)
              ltac:(intros s_pc Hnpc Hva Hvb;
                    cbn [execute];
                    rewrite (exec_execute_RTYPE_ADD_gpr (mword_of_int 10) (mword_of_int 12) (mword_of_int 14) s_pc);
                    replace (Z.eqb (uint (mword_of_int 14 : mword 5)) 0) with false by (vm_compute; reflexivity);
                    unfold gpr_rd_val;
                    rewrite Hva Hvb;
                    match goal with
                    | |- context [ ?mm !!! Regidx (mword_of_int 12) ] =>
                        let HA := fresh "HA" in
                        assert (HA : mm !!! Regidx (mword_of_int 12) = (mword_of_int 4096));
                        [ rewrite lookup_total_insert; rewrite lookup_total_insert;
                          rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
                          rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
                          rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
                          rewrite Ha2; apply bv_eq; vm_compute; reflexivity
                        | rewrite HA ]
                    end;
                    match goal with
                    | |- context [ ?mm !!! Regidx (mword_of_int 10) ] =>
                        let HB := fresh "HB" in
                        assert (HB : mm !!! Regidx (mword_of_int 10) = p);
                        [ rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
                          rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
                          rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
                          rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
                          rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
                          reflexivity
                        | rewrite HB ]
                    end;
                    reflexivity)
              (* Hn0 : a2 = 4096 <> 0 *)
              ltac:(rewrite Ha2; vm_compute; reflexivity)
              Hret0
              (* Hbne / HpcL0 : constant target geometry *)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              (* svpn structural facts, over svpn_of p *)
              (ram_mask p Hramp) (ram_svpn2 p Hramp) (ram_mvpn p Hramp)
              (WpSmodeGpr.ram_mppn p Hramp)
              (* the four per-byte geometry premises *)
              ltac:(intros j Hj; rewrite ms_a8_ms_addr;
                    exact (ram_canonical (pa_add p j) (page_valid_ram_j p j Hpv Hj)))
              ltac:(intros j Hj; rewrite ms_a8_ms_addr;
                    exact (svpn_pa_add_same p j Hpv Hj))
              ltac:(intros j Hj; rewrite ms_a8_ms_addr;
                    rewrite <- (svpn_pa_add_same p j Hpv Hj);
                    exact (ram_ident root_ppn (pa_add p j) (page_valid_ram_j p j Hpv Hj)))
              (* Hincr / Hcmp : pointer arithmetic *)
              ltac:(intros j; exact (ms_incr_step p j))
              ltac:(intros j Hj; exact (ms_cmp_page p j Hpv Hj))
              with "Hsm Htlbinv
                    Htext Hpc Hfile Hbra Hbs0 Hbuf [Hcont]").
    (* --- continuation: rebuild [page_own p] and re-expose gpr_file --- *)
    iIntros (mfin) "Hsm Htlbinv Hpc Hbra Hbs0 Hbuf Hfile %Hcs".
    iApply ("Hcont" $! mfin with "Hsm Htlbinv Hpc Hbra Hbs0 [Hbuf] Hfile [%]").
    - (* page_own p from the returned all-cbyte buffer *)
      iEval (rewrite /page_own /byte_any).
      iApply (big_sepL_impl with "Hbuf"). iIntros "!>" (k j _) "H".
      iEval (rewrite ms_pa_ms_addr) in "H". iExists _. iExact "H".
    - (* the final register file: callee_saved passes straight through *)
      exact Hcs.
  Qed.

End WpMemsetPage.
