(* ProofMemset.v: the memset byte-fill loop over the SIE-agnostic v2
   bundle.  memset runs OUTSIDE the interrupt-disabled region (kfree
   calls it before acquire, kalloc after release), so it must be
   SIE-agnostic — interrupts absorbed by the funnel during the fill.
   It threads the [sie_cap_gpr] bundle (sconf + sie_cap + gpr_file, NO
   intr_count: the fill never touches the disable nesting).  Fuel
   induction over the remaining byte count (the packaged bne-taken leaf
   hands the step's later out, stripped by iNext against the fuel IH —
   bounded loop, not iLöb). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import HartTp WpNext.
Require Import WpGpr WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import IntrDefs.
Require Import IntrDefs.
Require Import VcGen.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpMemsetS.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecMemsetParts.
Import Defs.


(* the epilogue +16 cancels a pa_stk 2 re-anchor (closed offsets). *)
Local Lemma po_up_cancel16 (X : mword 64) :
  pa_stk (add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2 = X.
Proof.
  unfold pa_stk, add_vec_int.
  rewrite pa_stk_off2.
  assert (Hz : bv_wrap 64 (uint (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)) : mword 64)
                           + uint (mword_of_int (- (8 * Z.of_nat 2)) : mword 64)) = 0%Z)
    by (vm_compute; reflexivity).
  rewrite Hz.
  change (add_vec X (mword_of_int 0)) with (add_vec_int X 0).
  apply avi0.
Qed.

Module MemsetProof : MEMSET_PARTS.

Section ProofMemset.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  (* [rget m k] at a NON-tp index is the plain map lookup ([rget_ne]) -- the
     one-line bridge from a leaf's [rget] to the register-map facts a
     whole-function proof already has.  Written name-free (durable-notes: an
     Ltac body cannot mention a hypothesis by literal name). *)
  Local Ltac rgne :=
    rewrite rget_ne;
    [ | let H1 := fresh in let H2 := fresh in
        intro H1; injection H1 as H2; vm_compute in H2; congruence ].

  (* the memset store leaf's [pa = add_vec cur (sext 0)] equals the
     buffer's [ms_pa cur] (both are just cur). *)
  Local Lemma ms_pa_sb_pa (cur : mword 64) :
    ms_pa cur = add_vec cur (sign_extend' 64 (mword_of_int 0 : mword 12)).
  Proof.
    unfold ms_pa, ms_a8.
    change (0 * 1)%Z with 0%Z. rewrite avi0. rewrite zero_extend'_id.
    rewrite subrange_id. rewrite sign_extend'_id. reflexivity.
  Qed.

  Local Lemma trunc8_nth0 (v : mword 64) : trunc8 v = nth_byte (trunc8 v) 0.
  Proof.
    apply bv_eq. rewrite nth_byte_unsigned.
    change (Z.of_N (8 * N.of_nat 0)) with 0%Z. rewrite Z.shiftr_0_r.
    symmetry. apply Z.mod_small.
    pose proof (bv_unsigned_in_range _ (trunc8 v)) as [Hlo Hhi].
    split; [ exact Hlo |].
    eapply Z.lt_le_trans; [ exact Hhi |].
    unfold bv_modulus. change (2 ^ Z.of_N 8)%Z with 256%Z.
    change (2 ^ 8)%Z with 256%Z. apply Z.le_refl.
  Qed.

  (* STILL BLOCKED, one layer deeper than before.  The landed premise
     [Regidx ra5 <> Regidx Rtp] fixes ra5's leg (it is WRITTEN each
     iteration -- [c.addi a5,a5,1] -- and its [rd_ok] premise carries the
     tp exclusion, and its READ through [rget] in the [sb]/[bne] leaves now
     bridges to the plain-map facts [Hcur]/[Hm'a5] via [rget_ne Hra5tp], as
     the development below shows).  But [ra1] and [ra4] are READ-ONLY every
     iteration -- [ra1] as the [sb] leaf's STORE VALUE ([storeval := trunc8
     (rget m ra1)], used in this lemma's OWN postcondition to show the
     written byte is [cbyte]), [ra4] as the [bne] comparison's other
     operand ([neq_vec (rget m' ra1(*rs1=ra5*)) (rget m' ra4)]) -- and nothing in
     [wp_memset_loop_sconf_body] excludes [ra1 = Rtp] or [ra4 = Rtp].  Both
     premises given for them, [Hm4 : m !!! Regidx ra4 = e] and
     [Hm1 : m !!! Regidx ra1 = cval], are PLAIN map facts; bridging either to
     the leaf's [rget]-spelled premise needs [rget_ne], whose side condition
     is exactly [Regidx ra4 <> Regidx Rtp] / [Regidx ra1 <> Regidx Rtp] --
     NOT derivable from [Hra1]/[Hra4]/[Hra4ne]/[Hra1ne]/[Hra5sp]/[Hra5tp]
     (none of those relate ra1 or ra4 to Rtp at all).  Confirmed empirically:
     the very first leaf (sb) already needs [Hm1] bridged this way to
     discharge its OWN postcondition ([Hb0]'s written byte = [cbyte]), and
     the development below reaches exactly that point and stops.  This is a
     second gap in the ALREADY-PORTED SpecMemsetParts.v contract (missing
     two more conjuncts, [Regidx ra1 <> Regidx Rtp] and [Regidx ra4 <>
     Regidx Rtp]), not a mechanical-porting issue -- reported rather than
     forced through.  The STATEMENT is updated to match the new (still
     unprovable) contract; the PROOF is developed as far as it correctly
     goes -- through the [b]-generic recursion restructuring ([revert CID]
     before [induction], matching the header comment's pattern) and the
     [sb] leaf's precondition (ra5-only, now provable) -- and stops at the
     confirmed blocker rather than admitting anything. *)
  Lemma wp_memset_loop_sconf (Φ : mval -> iProp Σ)
      (N : nat) (p e cval : mword 64) (ra1 ra4 ra5 : mword 5) (imm_bne : mword 13)
      (olds : nat -> bv 8) (n : nat) (b : bool) (pcur : mword 64)
    : wp_memset_loop_sconf_body Φ N p e cval ra1 ra4 ra5 imm_bne olds n b pcur.
  Proof.
    cbv beta delta [wp_memset_loop_sconf_body].
    intros pc0 pc4 pc6 cbyte Hra1 Hra4 Hra5 Hback Hal0
      Hincr Hcmp Hra4ne Hra1ne Hra5sp Hra5tp Hext0 Hext4 Hext6.
    (* [b]-generic recursion: IH must be applicable at ANY landing hart
       (the taken-bne step can migrate), so CID has to be part of what the
       induction generalizes -- a plain [induction rem] here would fix IH at
       THIS invocation's own (now-shadowed) [CID], and the recursive call
       could then never be applied at the hart the taken-branch lands on. *)
    intros rem. revert CID.
    induction rem as [|rem' IH]; intros CID off m Hoff Hrem Hcur Hm4 Hm1;
      [ exfalso; lia | ].
    iIntros "Hcg #Htext Hpc Hbuf Hcont".
    iPoseProof (Hext0 with "Htext") as "Hi0".
    iPoseProof (Hext4 with "Htext") as "Hi4".
    iPoseProof (Hext6 with "Htext") as "Hi6".
    (* off < N, and the current byte is offset off *)
    assert (HoffN : (off < N)%nat) by lia.
    (* peel the head byte of the pending buffer *)
    rewrite (seq_cons off rem').
    rewrite big_sepL_cons.
    iDestruct "Hbuf" as "[Hb0 Hbuf]".
    assert (Hcur' : rget m ra5 = ms_addr p off) by (rewrite (rget_ne m ra5 Hra5tp); exact Hcur).
    (* --- 0xce0: sb a1, 0(a5) : fill byte [off] --- *)
    iApply (wp_sb_s_sconf Φ pc0 ra1 ra5 (mword_of_int 0) m n (olds off) b
              with "Hcg Hpc Hi0 [Hb0]").
    { rewrite Hcur'. rewrite -ms_pa_sb_pa. iExact "Hb0". }
    iIntros (CID1 Hs1) "Hcg Hpc Hb0".
    (* the postcondition needs [rget m ra1 = cval] (the byte the store
       actually wrote is [trunc8 (rget m ra1)]); bridging [Hm1 : m !!!
       Regidx ra1 = cval] to it needs [rget_ne], whose side condition
       [Regidx ra1 <> Regidx Rtp] is exactly the missing fact -- see the
       comment above.  STOP here, left open rather than admitted. *)
    assert (Hm1' : rget m ra1 = cval).
    rewrite rget_ne; [exact Hm1|].
    (* remaining goal: [Regidx ra1 <> Regidx Rtp] -- NOT derivable from
       Hra1/Hra4/Hra5/Hra4ne/Hra1ne/Hra5sp/Hra5tp. *)
  Abort.

  Lemma wp_memset_suffix_sconf (Φ : mval -> iProp Σ)
      (M : regfile) (n : nat) (ra0e s00e : mword 64) (b : bool) (pcur : mword 64)
    : wp_memset_suffix_sconf_body Φ M n ra0e s00e b pcur.
  Proof.
    cbv beta delta [wp_memset_suffix_sconf_body].
    intros spd sp0up ret_tgt.
    set (M4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg ra0e]> M).
    set (M5 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg s00e]> M4).
    set (M6 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (M5 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> M5).
    iIntros "Hcg Hi28 Hi2a Hi2c Hi2e Hpc Hp8 Hp0 Hcont".
    (* ---- 0x28: c.ldsp ra,8(sp) ---- *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (MS + 0x1e)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              M n ra0e b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi28 Hp8 [-]").
    iIntros (CID1 Hs1) "Hcg Hpc Hp8".
    assert (Hpc2a : add_vec_int (mword_of_int (MS + 0x1e) : mword 64) 2 = mword_of_int (MS + 0x20))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg ra0e]> M) with M4.
    (* ---- 0x2a: c.ldsp s0,0(sp) ---- *)
    assert (Hsp4 : M4 !!! Regidx csp_rs1 = spd)
      by (rewrite /M4 upd_ne; [reflexivity | vm_compute; discriminate]).
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (MS + 0x20)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              M4 n s00e b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2a [Hp0] [-]").
    { iEval (rewrite Hsp4). iExact "Hp0". }
    iIntros (CID2 Hs2) "Hcg Hpc Hp0".
    assert (Hpc2c : add_vec_int (mword_of_int (MS + 0x20) : mword 64) 2 = mword_of_int (MS + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2c) in "Hpc".
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg s00e]> M4) with M5.
    (* ---- 0x2c: c.addi sp,16 -- the frame trade back ---- *)
    assert (Hsp5 : M5 !!! Regidx csp_rs1 = spd)
      by (rewrite /M5 upd_ne; [exact Hsp4 | vm_compute; discriminate]).
    assert (Hupc : pa_stk sp0up 2 = spd).
    { unfold sp0up. apply po_up_cancel16. }
    assert (Hwv : add_vec (M5 !!! Regidx csp_rs1)
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0up).
    { rewrite Hsp5. reflexivity. }
    assert (Hpop : M5 !!! Regidx csp_rs1
                   = pa_stk (add_vec (M5 !!! Regidx csp_rs1)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
    { rewrite Hwv Hupc. exact Hsp5. }
    assert (Hb1u : pa_stk sp0up 1
                    = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { unfold sp0up, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2u : pa_stk sp0up 2
                    = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))).
    { unfold sp0up, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iApply (wp_caddi_sp_pop_s_sconf Φ (mword_of_int (MS + 0x22)) (mword_of_int 16 : mword 6) M5
              n 2 b Hpop
              with "Hcg Hpc Hi2c [Hp8 Hp0] [-]").
    { iEval (rewrite Hwv).
      iApply (stack_own_2_intro with "[Hp8] [Hp0]").
      - iEval (rewrite Hb1u). iExact "Hp8".
      - iEval (rewrite Hb2u -Hsp4). iExact "Hp0". }
    iIntros (CID3 Hs3) "Hcg Hpc".
    assert (Hpc2e : add_vec_int (mword_of_int (MS + 0x22) : mword 64) 2 = mword_of_int (MS + 0x24))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2e) in "Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (M5 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> M5) with M6.
    (* ---- 0x2e: c.ret ---- *)
    assert (HM6ra : M6 !!! Regidx (mword_of_int 1 : mword 5) = ra0e).
    { rewrite /M6 upd_ne; [| vm_compute; discriminate].
      rewrite /M5 upd_ne; [| vm_compute; discriminate].
      rewrite /M4. apply upd_eq. }
    iApply (wp_cret_s_sconf Φ (mword_of_int (MS + 0x24)) (mword_of_int 1 : mword 5) M6 (n + 2)%nat b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi2e [-]").
    iIntros (CID4 Hs4) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hra_final : ret_pc (M6 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
      by (rewrite HM6ra; reflexivity).
    iEval (rewrite Hra_final) in "Hpc".
    iSpecialize ("Hcont" $! CID4 with "[]"); [iPureIntro; wp_next_chain|].
    iApply ("Hcont" $! M6 with "Hcg Hpc [%]").
    rewrite /M6 /M5 /M4 Hsp5. reflexivity.
  Qed.


  (* =================================================================== *)
  (*  memset HEAD over sconf (memset+0x00..+0x06): the 2-slot frame alloc  *)
  (*  (c.addi sp,-16, a push trading 2 off the avail count), the two       *)
  (*  c.sdsp saves into the freed frame cells, and c.addi4spn s0.  Stops   *)
  (*  at the c.beqz on the count, handing the two full frame cells         *)
  (*  (ra0/s0) out to whichever arm of it runs.                            *)
  (* =================================================================== *)
  Lemma wp_memset_head_sconf (Φ : mval -> iProp Σ)
      (m0 : regfile) (n : nat) (imm_entry : mword 6) (nzimm_s0 : mword 8) (b : bool) (pcur : mword 64)
    : wp_memset_head_sconf_body Φ m0 n imm_entry nzimm_s0 b pcur.
  Proof.
    cbv beta delta [wp_memset_head_sconf_body].
    intros ra_idx s0_idx pcE sp0 sp' pa_ra pa_s0 ra0 s00 m1 m2 Hn2 Hsp'.
    iIntros "Hcg Hpc Hi00 Hi02 Hi04 Hi06 Hcont".
    assert (Hcsp1 : m1 !!! Regidx csp_rs1 = sp') by (apply upd_eq).
    (* ---- 0x00: c.addi sp,-16 -- the frame push ---- *)
    iApply (wp_caddi_sp_push_s_sconf Φ pcE imm_entry m0 n 2 b Hn2 Hsp'
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (MS + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iDestruct (stack_own_2_elim with "Hframe") as (vr8 vs0) "[Hbra Hbs0]".
    assert (Hpa1 : add_vec (m1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hcsp1 Hsp'. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpa2 : add_vec (m1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite Hcsp1 Hsp'. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa1) in "Hbra".
    iEval (rewrite -Hpa2) in "Hbs0".
    (* ---- 0x02: c.sdsp ra,8(sp) ---- *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (MS + 0x02)) (mword_of_int 1 : mword 6) ra_idx m1 (n - 2)%nat vr8 b
              with "Hcg Hpc Hi02 Hbra [-]").
    iIntros (CID2 Hs2) "Hcg Hpc Hbra".
    assert (Hpp04 : add_vec_int (mword_of_int (MS + 0x02) : mword 64) 2 = mword_of_int (MS + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- 0x04: c.sdsp s0,0(sp) ---- *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (MS + 0x04)) (mword_of_int 0 : mword 6) s0_idx m1 (n - 2)%nat vs0 b
              with "Hcg Hpc Hi04 Hbs0 [-]").
    iIntros (CID3 Hs3) "Hcg Hpc Hbs0".
    assert (Hpp06 : add_vec_int (mword_of_int (MS + 0x04) : mword 64) 2 = mword_of_int (MS + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* the saved values: ra0/s00 *)
    assert (Hra0v : m1 !!! Regidx ra_idx = ra0)
      by (unfold m1, ra0; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs00v : m1 !!! Regidx s0_idx = s00)
      by (unfold m1, s00; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    (* ---- 0x06: c.addi4spn s0,sp,16 ---- *)
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (MS + 0x06)) (Cregidx (mword_of_int 0)) nzimm_s0 s0_idx m1 (n - 2)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06 [-]").
    iIntros (CID4 Hs4) "Hcg Hpc".
    assert (Hpp08 : add_vec_int (mword_of_int (MS + 0x06) : mword 64) 2 = add_vec_int (pcE : mword 64) 8) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    change (<[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1) with m2.
    (* frame cells hold ra0/s00 at pa_ra/pa_s0 (via Hcsp1: m1!!!csp = sp') *)
    iEval (rgne) in "Hbra". iEval (rewrite Hcsp1 Hra0v) in "Hbra".
    iEval (rgne) in "Hbs0". iEval (rewrite Hcsp1 Hs00v) in "Hbs0".
    iApply ("Hcont" $! CID4 with "[%] Hcg Hpc Hbra Hbs0").
    wp_next_chain.
  Qed.

  (* =================================================================== *)
  (*  memset SKIP over sconf (memset+0x08, taken): a zero count jumps      *)
  (*  straight to the epilogue -- nothing written, no register moved.      *)
  (* =================================================================== *)
  Lemma wp_memset_skip_sconf (Φ : mval -> iProp Σ)
      (M : regfile) (n : nat) (imm8_beqz : mword 8) (b : bool) (pcur : mword 64)
    : wp_memset_skip_sconf_body Φ M n imm8_beqz b pcur.
  Proof.
    cbv beta delta [wp_memset_skip_sconf_body].
    intros a2_idx pcE Hz Htgt.
    iIntros "Hcg Hpc Hi08 Hcont".
    assert (Hal : eq_vec (access_vec_dec
                    (add_vec (add_vec_int (pcE : mword 64) 8)
                       (sign_extend' 64 (sign_extend' 13 (concat_vec imm8_beqz ('b"0"))))) 0) ('b"0") = true)
      by (rewrite Htgt; vm_compute; reflexivity).
    assert (Hz' : eq_vec (rget M a2_idx) zero_reg = true) by (rgne; exact Hz).
    iApply (wp_cbeqz_taken_s_sconf Φ (add_vec_int pcE 8) imm8_beqz (Cregidx (mword_of_int 4)) a2_idx M n b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hz' Hal
              with "Hcg Hpc Hi08 [-]").
    iNext.
    iIntros (CID1 Hs1) "Hcg Hpc".
    iEval (rewrite Htgt) in "Hpc".
    iApply ("Hcont" $! CID1 with "[%] Hcg Hpc").
    wp_next_chain.
  Qed.

  (* =================================================================== *)
  (*  memset SETUP over sconf (memset+0x08..+0x10): the nonzero-count      *)
  (*  c.beqz fall-through, the (unsigned int) count truncation, the a5     *)
  (*  cursor and the a4 end-pointer setup.  Ends at the loop top.          *)
  (* =================================================================== *)
  Lemma wp_memset_setup_sconf (Φ : mval -> iProp Σ)
      (M : regfile) (n : nat) (shamt_l shamt_r : mword 6) (imm8_beqz : mword 8)
      (wval_add : mword 64) (b : bool) (pcur : mword 64)
    : wp_memset_setup_sconf_body Φ M n shamt_l shamt_r imm8_beqz wval_add b pcur.
  Proof.
    cbv beta delta [wp_memset_setup_sconf_body].
    intros a0_idx a2_idx a4_idx a5_idx pcE m3 m4 m5 m6 Hn0 Hvalue_add.
    iIntros "Hcg Hpc Hi08 Hi0a Hi0c Hi0e Hi10 Hcont".
    assert (Hn0' : eq_vec (rget M a2_idx) zero_reg = false) by (rgne; exact Hn0).
    (* ---- 0x08: c.beqz a2,cea : n<>0, fall through ---- *)
    iApply (wp_cbeqz_fall_s_sconf Φ (add_vec_int pcE 8) imm8_beqz (Cregidx (mword_of_int 4)) a2_idx M n b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hn0'
              with "Hcg Hpc Hi08 [-]").
    iIntros (CID1 Hs1) "Hcg Hpc".
    assert (Hpp0a : add_vec_int (add_vec_int (pcE : mword 64) 8) 2 = mword_of_int (MS + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* ---- 0x0a: c.mv a5,a0 ---- *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (MS + 0x0a)) a5_idx a0_idx M n b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a [-]").
    iIntros (CID2 Hs2) "Hcg Hpc".
    assert (Hpp0c : add_vec_int (mword_of_int (MS + 0x0a) : mword 64) 2 = mword_of_int (MS + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    change (<[Regidx a5_idx := regval_into_reg (add_vec zero_reg (rget M a0_idx))]> M) with m3.
    (* ---- 0x0c: c.slli a2,shamt_l ---- *)
    iApply (wp_cslli_s_sconf Φ (mword_of_int (MS + 0x0c)) (Regidx a2_idx) a2_idx shamt_l m3 n b
              eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c [-]").
    iIntros (CID3 Hs3) "Hcg Hpc".
    assert (Hpp0e : add_vec_int (mword_of_int (MS + 0x0c) : mword 64) 2 = mword_of_int (MS + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    change (<[Regidx a2_idx := regval_into_reg (shift_bits_left (rget m3 a2_idx) (subrange_vec_dec shamt_l (Z.sub log2_xlen 1) 0))]> m3) with m4.
    (* ---- 0x0e: c.srli a2,shamt_r ---- *)
    iApply (wp_csrli_s_sconf Φ (mword_of_int (MS + 0x0e)) (Cregidx (mword_of_int 4)) a2_idx shamt_r m4 n b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e [-]").
    iIntros (CID4 Hs4) "Hcg Hpc".
    assert (Hpp10 : add_vec_int (mword_of_int (MS + 0x0e) : mword 64) 2 = mword_of_int (MS + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    change (<[Regidx a2_idx := regval_into_reg (shift_bits_right (rget m4 a2_idx) (subrange_vec_dec shamt_r (Z.sub log2_xlen 1) 0))]> m4) with m5.
    (* ---- 0x10: add a4,a2,a0 (end pointer) ---- *)
    assert (Hvalue_add' : add_vec (rget m5 a2_idx) (rget m5 a0_idx) = wval_add).
    { rewrite (rget_ne m5 a2_idx ltac:(vm_compute; discriminate)).
      rewrite (rget_ne m5 a0_idx ltac:(vm_compute; discriminate)).
      exact Hvalue_add. }
    iApply (wp_add_s_sconf Φ (mword_of_int (MS + 0x10)) a4_idx a2_idx a0_idx wval_add m5 n b
              ltac:(vm_compute; discriminate) ltac:(rdok) Hvalue_add'
              with "Hcg Hpc Hi10 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc".
    assert (Hpp14 : add_vec_int (mword_of_int (MS + 0x10) : mword 64) 4 = add_vec_int (pcE : mword 64) 20) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    change (<[Regidx a4_idx := regval_into_reg wval_add]> m5) with m6.
    iApply ("Hcont" $! CID5 with "[%] Hcg Hpc").
    wp_next_chain.
  Qed.

End ProofMemset.

End MemsetProof.
