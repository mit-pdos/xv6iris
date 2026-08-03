(* ProofCpuid.v: whole-function WP for xv6's cpuid() in S-mode, over the
   SIE-agnostic sie_cap bundle.  cpuid() @ 0x800018d0 reads the thread pointer
   [tp] and returns it as an [int] (sign-extension of tp's low 32 bits):

     0x800018d0 <cpuid>:
       +0x00  1141   c.addi   sp,sp,-16     frame alloc
       +0x02  e406   c.sdsp   ra,8(sp)
       +0x04  e022   c.sdsp   s0,0(sp)
       +0x06  0800   c.addi4spn s0,sp,16
       +0x08  8512   c.mv     a0,tp         a0 = tp
       +0x0a  2501   c.addiw  a0,0          sext.w a0
       +0x0c  60a2   c.ldsp   ra,8(sp)
       +0x0e  6402   c.ldsp   s0,0(sp)
       +0x10  0141   c.addi   sp,sp,16      frame free
       +0x12  8082   c.ret

   This is a simpler [mycpu] (ProofMycpu.v): the SAME 16-byte frame and the
   SAME [c.mv;sext.w tp] read, but no cpus[] indexing (no slli/auipc/addi/add).
   Structure mirrors ProofMycpu.v leaf-by-leaf; instruction decodes for the
   shared frame ops come from KernelRvcDecode, and the two a0-flavoured decodes
   ([c.mv a0,tp], [c.addiw a0,0]) are proven here.

   INTERRUPTS OFF.  The contract (SpecCpuid.v) is stated at [b = false]
   because the [tp] read happens MID-function: see the comment there.  Every
   leaf is therefore applied at [false], and each [wp_next false] obligation
   collapses with [rewrite wp_next_off] -- the hart never moves, so the proof
   reads as it did before the explicit-CPUID refactor.  The [c.mv a0,tp] read
   itself is [rget m2 tp_idx], which is THIS hart's id by [rget_tp] (HartTp.v):
   there is no special tp leaf. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile WpMmodeLeafBase.
Require Import SmodeCore.
Require Import HartTp WpNext IntrDefs.
Require Import StackOwn CalleeSaved.
Require Import KernelRvcDecode.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecCpuid.
Require Import CodeCpuid.
Import Defs.



(* the [sext.w a0] result, applied to a0 = [add_vec zero_reg tp] with imm 0,
   truncates to exactly [subrange tp 31 0] -- i.e. it bridges the model's
   ADDIW value to [cpuid_ret]'s definition. *)
Lemma cpuid_addiw_bridge (X : mword 64) :
  add_vec (add_vec zero_reg X) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))) = X.
Proof.
  assert (add_vec_unsigned : forall x y : mword 64,
            bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y)).
  { intros x y. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned. reflexivity. }
  apply bv_eq. rewrite !add_vec_unsigned.
  assert (HZ : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)) : mword 64) = 0)
    by (vm_compute; reflexivity).
  assert (HZR : bv_unsigned (zero_reg : mword 64) = 0) by (vm_compute; reflexivity).
  rewrite HZ HZR. rewrite Z.add_0_r Z.add_0_l.
  rewrite bv_wrap_bv_unsigned. apply bv_wrap_bv_unsigned.
Qed.

(* [rget m k] at a NON-tp index is the plain map lookup ([rget_ne]) -- the
   one-line bridge from a leaf's [rget] to the register-map facts a
   whole-function proof already has.  Written name-free (durable-notes: an
   Ltac body cannot mention a hypothesis by literal name). *)
Local Ltac rgne :=
  rewrite rget_ne;
  [ | let H1 := fresh in let H2 := fresh in
      intro H1; injection H1 as H2; vm_compute in H2; congruence ].

Module CpuidProof : CPUID.

Section ProofCpuid.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.











  (* =================================================================== *)
  (*  THE CAPSTONE: a WP for the entire cpuid(), entry through return.    *)
  (*  Registers: ra=x1 sp=x2 tp=x4 s0=x8 a0=x10.  On exit                 *)
  (*  a0 = cpuid_ret tp, ra/sp/s0 restored (callee-saved).                *)
  (* =================================================================== *)
  Lemma wp_cpuid_sconf (Φ : mval -> iProp Σ)
      (m0 : regfile) (n : nat) (p : mword 64)
    : wp_cpuid_sconf_body Φ m0 n p.
  Proof.
    cbv beta delta [wp_cpuid_sconf_body].
    intros ra_idx tp_idx a0_idx pcE ra0 ret_tgt cret Hn.
    (* THE tp READ, once: [tp] is pinned to the hart, so a read at index 4 is
       this hart's id at EVERY register map ([rget_tp]).  That is why the
       contract may name the entry map's [rget m0 tp_idx] for a value the
       [c.mv] reads out of [m2] four instructions later -- at [b = false] the
       hart cannot have moved in between. *)
    assert (Htp : forall mm : regfile, rget mm tp_idx = cid_word)
      by (intros mm; exact (rget_tp mm)).
    (* the per-instruction register-map chain (private to the proof) *)
    set (s0_idx := (mword_of_int 8 : mword 5)).
    set (imm_entry := (mword_of_int 48 : mword 6)).
    set (imm_dealloc := (mword_of_int 16 : mword 6)).
    set (nzimm_s0 := (mword_of_int 4 : mword 8)).
    set (sp0 := m0 !!! Regidx csp_rs1).
    set (sp' := add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry))).
    set (s00 := m0 !!! Regidx s0_idx).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg sp']> m0).
    set (m2 := <[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1).
    set (m3 := <[Regidx a0_idx := regval_into_reg (add_vec zero_reg (rget m2 tp_idx))]> m2).
    set (m4 := <[Regidx a0_idx := regval_into_reg (sign_extend' 64 (subrange_vec_dec (add_vec (rget m3 a0_idx) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> m3).
    set (m5 := <[Regidx ra_idx := regval_into_reg ra0]> m4).
    set (m6 := <[Regidx s0_idx := regval_into_reg s00]> m5).
    set (m7 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m6 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)))]> m6).
    iIntros "Hcg #Htext Hpc Hcont".
    iPoseProof (ci_00 with "Htext") as "Hi00".
    iPoseProof (ci_02 with "Htext") as "Hi02".
    iPoseProof (ci_04 with "Htext") as "Hi04".
    iPoseProof (ci_06 with "Htext") as "Hi06".
    iPoseProof (ci_08 with "Htext") as "Hi08".
    iPoseProof (ci_0a with "Htext") as "Hi0a".
    iPoseProof (ci_0c with "Htext") as "Hi0c".
    iPoseProof (ci_0e with "Htext") as "Hi0e".
    iPoseProof (ci_10 with "Htext") as "Hi10".
    iPoseProof (ci_12 with "Htext") as "Hi12".
    (* the sp geometry: sp' = pa_stk sp0 2; frame slot addresses *)
    assert (Hcsp1 : m1 !!! Regidx csp_rs1 = sp') by (apply upd_eq).
    assert (Hpush : sp' = pa_stk (m0 !!! Regidx csp_rs1) 2).
    { unfold sp', pa_stk, add_vec_int, imm_entry.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x00: c.addi sp,-16 -- the frame push ---- *)
    iApply (wp_caddi_sp_push_s_sconf Φ pcE imm_entry m0 n 2 false Hn Hpush
              with "Hcg Hpc Hi00 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hframe Hpc".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.cpuid + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iDestruct (stack_own_2_elim with "Hframe") as (vr24 vs16) "[Hbra Hbs0]".
    (* the two frame cells at csdsp's own address spelling *)
    assert (Hpa1 : add_vec (m1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hcsp1. unfold sp', sp0, pa_stk, add_vec_int, imm_entry. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpa2 : add_vec (m1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite Hcsp1. unfold sp', sp0, pa_stk, add_vec_int, imm_entry. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa1) in "Hbra".
    iEval (rewrite -Hpa2) in "Hbs0".
    (* ---- 0x02: c.sdsp ra,8(sp) ---- *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.cpuid + 0x02)) (mword_of_int 1 : mword 6) ra_idx m1 (n - 2)%nat vr24 false
              with "Hcg Hpc Hi02 Hbra [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hbra".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.cpuid + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.cpuid + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- 0x04: c.sdsp s0,0(sp) ---- *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.cpuid + 0x04)) (mword_of_int 0 : mword 6) s0_idx m1 (n - 2)%nat vs16 false
              with "Hcg Hpc Hi04 Hbs0 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hbs0".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.cpuid + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.cpuid + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* ---- 0x06: c.addi4spn s0,sp,4 ---- *)
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (KernelSyms.cpuid + 0x06)) (Cregidx (mword_of_int 0)) nzimm_s0 s0_idx m1 (n - 2)%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.cpuid + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.cpuid + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    change (<[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1) with m2.
    (* ---- 0x08: c.mv a0,tp -- THE tp READ.  The leaf's value is [rget m2
       tp_idx], which is this hart's id; nothing special is needed for it. ---- *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.cpuid + 0x08)) a0_idx tp_idx m2 (n - 2)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.cpuid + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.cpuid + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    change (<[Regidx a0_idx := regval_into_reg (add_vec zero_reg (rget m2 tp_idx))]> m2) with m3.
    (* ---- 0x0a: c.addiw a0,0 (sext.w a0) ---- *)
    iApply (wp_caddiw_s_sconf Φ (mword_of_int (KernelSyms.cpuid + 0x0a)) a0_idx (mword_of_int 0 : mword 6) m3 (n - 2)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.cpuid + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.cpuid + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    change (<[Regidx a0_idx := regval_into_reg (sign_extend' 64 (subrange_vec_dec (add_vec (rget m3 a0_idx) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> m3) with m4.
    (* ---- 0x0c: c.ldsp ra,8(sp) ---- *)
    assert (Hm4sp : m4 !!! Regidx csp_rs1 = sp').
    { unfold m4, m3, m2;
      repeat (rewrite upd_ne; [| vm_compute; discriminate]);
      unfold m1; rewrite upd_eq; reflexivity. }
    assert (Hpa1' : add_vec (m4 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hm4sp. rewrite -Hcsp1. exact Hpa1. }
    assert (Hpa2' : add_vec (m4 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite Hm4sp. rewrite -Hcsp1. exact Hpa2. }
    (* the c.sdsp'd values are [rget m1 _] (the leaf reads at a VARIABLE
       index); neither ra nor s0 is tp, so [rgne] is the whole bridge. *)
    assert (Hra0v : rget m1 ra_idx = ra0)
      by (rgne; unfold m1; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs00v : rget m1 s0_idx = s00)
      by (rgne; unfold m1; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hpa1 -Hpa1' Hra0v) in "Hbra".
    iEval (rewrite Hpa2 -Hpa2' Hs00v) in "Hbs0".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.cpuid + 0x0c)) (mword_of_int 1 : mword 6) ra_idx m4 (n - 2)%nat ra0 false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c Hbra [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hbra".
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.cpuid + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.cpuid + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    change (<[Regidx ra_idx := regval_into_reg ra0]> m4) with m5.
    (* ---- 0x0e: c.ldsp s0,0(sp) ---- *)
    assert (Hm5sp : m5 !!! Regidx csp_rs1 = m4 !!! Regidx csp_rs1)
      by (unfold m5; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite -Hm5sp) in "Hbs0".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.cpuid + 0x0e)) (mword_of_int 0 : mword 6) s0_idx m5 (n - 2)%nat s00 false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e Hbs0 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hbs0".
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.cpuid + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.cpuid + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    change (<[Regidx s0_idx := regval_into_reg s00]> m5) with m6.
    (* ---- 0x10: c.addi sp,16 -- the frame pop ---- *)
    assert (Hm6sp : m6 !!! Regidx csp_rs1 = sp').
    { unfold m6, m5; repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      exact Hm4sp. }
    assert (Hwv : add_vec (m6 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)) = sp0).
    { rewrite Hm6sp. unfold sp', imm_dealloc, imm_entry, sp0. apply frame_cancel_16. }
    assert (Hpop : m6 !!! Regidx csp_rs1
                   = pa_stk (add_vec (m6 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc))) 2).
    { rewrite Hwv Hm6sp. exact Hpush. }
    iEval (rewrite Hpa1') in "Hbra".
    iEval (rewrite Hm5sp Hpa2') in "Hbs0".
    iDestruct (stack_own_2_intro sp0 with "Hbra Hbs0") as "Hframe".
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf Φ (mword_of_int (KernelSyms.cpuid + 0x10)) imm_dealloc m6
              (n - 2)%nat 2 false Hpop
              with "Hcg Hpc Hi10 Hframe [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hnk : ((n - 2) + 2)%nat = n) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.cpuid + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.cpuid + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (m6 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)))]> m6) with m7.
    (* ---- 0x12: c.ret ---- *)
    assert (Hm7ra : m7 !!! Regidx ra_idx = ra0).
    { unfold m7, m6; repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      unfold m5. rewrite upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf Φ (mword_of_int (KernelSyms.cpuid + 0x12)) ra_idx m7 n false
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi12 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hra_final : ret_pc (rget m7 ra_idx) = ret_tgt)
      by (rgne; rewrite Hm7ra; reflexivity).
    iEval (rewrite Hra_final) in "Hpc".
    iApply ("Hcont" $! m7 with "Hcg Hpc [%]").
    split.
    - assert (Hm7w : m7 = apply_writes
        [ (csp_rs1, regval_into_reg (add_vec (m6 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc))));
          (s0_idx,  regval_into_reg s00);
          (ra_idx,  regval_into_reg ra0);
          (a0_idx,  regval_into_reg (sign_extend' 64 (subrange_vec_dec (add_vec (rget m3 a0_idx) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0)));
          (a0_idx,  regval_into_reg (add_vec zero_reg (rget m2 tp_idx)));
          (s0_idx,  regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0))));
          (csp_rs1, regval_into_reg sp') ] m0) by reflexivity.
      rewrite Hm7w. apply callee_saved_apply_writes.
      repeat constructor.
      rewrite (outer_write_cons_eq (mword_of_int 2) csp_rs1);
        [ | vm_compute; reflexivity ].
      unfold regval_into_reg.
      rewrite Hm6sp.
      change (m0 !!! Regidx (mword_of_int 2)) with (m0 !!! Regidx csp_rs1).
      unfold sp', imm_dealloc, imm_entry.
      apply frame_cancel_16.
    - (* a0 = cpuid_ret tp.  Stated at the zeta-expanded form and closed by
         [exact], since [cret] is a spec-body [let] the peel cannot unfold. *)
      assert (Hcret : m7 !!! Regidx a0_idx = cpuid_ret (rget m0 tp_idx)).
      { rewrite /m7 /m6 /m5 /m4 /m3 /m2 /m1 /s00 /ra0.
        repeat first [ rewrite upd_eq
                     | rewrite upd_ne; [| vm_compute; discriminate]
                     | rewrite Htp
                     | rgne ].
        unfold cpuid_ret.
        rewrite cpuid_addiw_bridge. reflexivity. }
      exact Hcret.
  Qed.

  (* jal-callable form: writes ra := P+4, runs cpuid, returns to P+4. *)
  Lemma wp_call_cpuid_sconf_cs (Φ : mval -> iProp Σ)
      (P : mword 64) (jimm : mword 21)
      (m : regfile) (n : nat) (p : mword 64)
    : wp_call_cpuid_sconf_cs_body Φ P jimm m n p.
  Proof.
    cbv beta delta [wp_call_cpuid_sconf_cs_body].
    intros ra_idx tp_idx a0_idx m0 pcE ra0 ret_tgt cret Htarget Halpce Hn.
    iIntros "Hcg #Htext Hpc Hjal Hcont".
    iApply (wp_jal_s_sconf Φ P (mword_of_int 1) jimm m n false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rewrite Htarget; exact Halpce)
              with "Hcg Hpc Hjal [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rewrite Htarget) in "Hpc".
    iApply (wp_cpuid_sconf Φ m0 n p Hn
              with "Hcg Htext Hpc [-]").
    iIntros (m') "Hcg Hpc %Hcs".
    iApply ("Hcont" $! m' with "Hcg Hpc [%]").
    destruct Hcs as [Hcs Ha0].
    split.
    - eapply callee_saved_trans; [ | exact Hcs ].
      assert (Hm0w : m0 = apply_writes
        [ ((mword_of_int 1 : mword 5), regval_into_reg (add_vec_int P 4)) ] m) by reflexivity.
      rewrite Hm0w. apply callee_saved_apply_writes. repeat constructor.
    - (* the jal's ra write does not move tp, and BOTH tp reads are this
         hart's id anyway ([rget_tp]) -- no register-map fact is needed. *)
      rewrite Ha0. f_equal.
  Qed.

End ProofCpuid.

End CpuidProof.
