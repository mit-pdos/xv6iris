(* WpTimerinit.v -- the xv6 kernel [timerinit()] (21 instructions at
   0x8000001c .. 0x80000056, KernelInstrs indices 9..29), proved as ONE WP
   theorem [wp_timerinit] by composing ONLY the new-style register-generic
   [wp_*_gpr] WPs, at a GENERIC fraction [q] of [mmode_config]/[pmpcfg_n]
   (timerinit runs inside start()'s csrw-mstatus -> mret window where the
   caller holds q = 1/2).

   The trace (ground truth: kernel-rocq/KernelInstrs.v):
     9  0x8000001c 0x1141     c.addi  sp, -16          [RVC, 4-aligned]
     10 0x8000001e 0xe406     c.sdsp  ra, 8(sp)        [RVC, 8-byte STORE]
     11 0x80000020 0xe022     c.sdsp  s0, 0(sp)        [RVC, 8-byte STORE]
     12 0x80000022 0x0800     c.addi4spn s0, sp, 16    [RVC]
     13 0x80000024 0x30a027f3 csrr    a5, menvcfg      [F_Base, 4-aligned]
     14 0x80000028 0x577d     c.li    a4, -1           [RVC]
     15 0x8000002a 0x177e     c.slli  a4, 63           [RVC]
     16 0x8000002c 0x8fd9     c.or    a5, a4           [RVC]
     17 0x8000002e 0x30a79073 csrw    menvcfg, a5      [F_Base, 2-aligned]
     18 0x80000032 0x306027f3 csrr    a5, mcounteren   [F_Base, 2-aligned]
     19 0x80000036 0x0027e793 ori     a5, a5, 2        [F_Base, 2-aligned]
     20 0x8000003a 0x30679073 csrw    mcounteren, a5   [F_Base, 2-aligned]
     21 0x8000003e 0xc01027f3 csrr    a5, time         [F_Base, 2-aligned]
     22 0x80000042 0x000f4737 lui     a4, 0xf4         [F_Base, 2-aligned]
     23 0x80000046 0x24070713 addi    a4, a4, 576      [F_Base, 2-aligned]
     24 0x8000004a 0x97ba     c.add   a5, a4           [RVC]
     25 0x8000004c 0x14d79073 csrw    stimecmp, a5     [F_Base, 4-aligned]
     26 0x80000050 0x60a2     c.ldsp  ra, 8(sp)        [RVC, 8-byte LOAD]
     27 0x80000052 0x6402     c.ldsp  s0, 0(sp)        [RVC, 8-byte LOAD]
     28 0x80000054 0x0141     c.addi  sp, 16           [RVC]
     29 0x80000056 0x8082     c.ret  (c.jr ra)         [RVC]

   The two stores / two loads run AFTER start()'s pmpcfg0 write, so their PMP
   data checks go through the TOR-entry-0 path ([wp_csdsp_gpr_tor] /
   [wp_cldsp_gpr_tor] from WpGprRvcTor.v) with the [pmp_tor0_grants]
   premises; every fetch uses [pmp_allows_all].

   [kernel_text] / [kernel_window_pc] / the [instr_bytes_*] constructors are
   REUSED from WpEntryNew.v (they close over its Section's `{!riscvGS Σ}`
   context, so they are directly applicable here). *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec RiscvExtras WpGpr.
Require Import WpMmodeShiftiop.
Require Import WpMmodeLeafBase.
Require Import WpMmodeUtype.
Require Import WpMmodeItype.
Require Import WpMmodeRtype.
Require Import WpMmodeJalr.
Require Import WpMmodeLoad.
Require Import WpMmodeStore.
Require Import WpGprCsrrA WpGprCsrrB WpGprCsrwA WpGprCsrwB.
Require Import WpGprCsrwStimecmp.
Require Import InstrBytes.
Require Import KernelText.
Require Import StackOwn.
Require Import RegFile.
From iris.base_logic.lib Require Import invariants.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Require Import CodeTimerinitAux.
Require Import MbootVocab.
(* [mw_prep] / [zn_norm] / [bv_eq_testbit], for [ti_mcen1_TM] below.  Safe at
   this altitude: MstatusBits.v has no intra-[iris] requires at all. *)
Require Import MstatusBits.
Require Import TsoCtx.
(* ===================================================================== *)
(* Symbolic values of the run (functions of the entry state).             *)
(* ===================================================================== *)

(* sp after the prologue c.addi (= sp0 - 16). *)
Definition ti_sp1 (sp0 : mword 64) : mword 64 := add_vec sp0 (sign_extend' 64 i9).
(* the two stack-slot effective addresses (exactly the c.sdsp/c.ldsp ea forms). *)
Definition ti_ea_ra (sp0 : mword 64) : mword 64 :=
  add_vec (ti_sp1 sp0) (sign_extend' 64 (zero_extend' 12 (concat_vec u10 ('b"000")))).
Definition ti_ea_s0 (sp0 : mword 64) : mword 64 :=
  add_vec (ti_sp1 sp0) (sign_extend' 64 (zero_extend' 12 (concat_vec u11 ('b"000")))).
(* The bridges to [MbootVocab]: the three of these the boot CONTRACT names,
   restated over its own vocabulary so [SpecEntry] does not have to be written
   in the decoded-immediate spelling ([i9], [u10], [u11]) that only this proof
   cares about.  Note the contract's argument is start()'s [sp0], so its slot
   addresses sit at a DOUBLE frame drop -- start()'s, then timerinit's. *)
Lemma ti_sp1_mb (sp0 : mword 64) : ti_sp1 sp0 = mb_frame sp0.
Proof.
  unfold ti_sp1, mb_frame.
  apply (f_equal (add_vec sp0)). apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma ti_ea_ra_mb (sp0 : mword 64) : ti_ea_ra (ti_sp1 sp0) = mb_ti_ra sp0.
Proof.
  unfold ti_ea_ra, mb_ti_ra. rewrite !ti_sp1_mb.
  apply (f_equal (add_vec (mb_frame (mb_frame sp0)))).
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma ti_ea_s0_mb (sp0 : mword 64) : ti_ea_s0 (ti_sp1 sp0) = mb_ti_s0 sp0.
Proof.
  unfold ti_ea_s0, mb_ti_s0. rewrite !ti_sp1_mb.
  (* u11 is 0, so the displacement is the identity *)
  replace (sign_extend' 64 (zero_extend' 12 (concat_vec u11 ('b"000"))) : mword 64)
    with (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
    by (apply bv_eq; vm_compute; reflexivity).
  apply addv_sext0.
Qed.

(* s0 after c.addi4spn (= sp1 + 16 = sp0). *)
Definition ti_s0v (sp0 : mword 64) : mword 64 :=
  add_vec (ti_sp1 sp0) (sign_extend' 64 (caddi4spn_imm nz12)).
(* the c.li/c.slli-built constant 1<<63, the menvcfg STCE|... OR mask result,
   the mcounteren TM-or, the lui/addi-built 1000000 interval, the deadline. *)
Definition ti_bit63 : mword 64 := mword_of_int 0x8000000000000000.
Definition ti_menv1 (menv0 : mword 64) : mword 64 := or_vec menv0 ti_bit63.
Definition ti_mcen1 (mcen0 : mword 32) : mword 64 :=
  or_vec (zero_extend' 64 mcen0) (sign_extend' 64 i19).
(* THE TM BIT IS SET IN THE mcounteren timerinit WRITES, at ANY entry value.
   [i19 = 2] is the TM bit, the [ori] sets it, and the CSR's legalization masks
   with [sys_mcounteren_writable_bits] = all ones, so it survives.  This is the
   one fact [TimerCap.timer_cap_intro] wants of timerinit's output, and it can
   only be stated where the written value is still concrete -- which is here.
   The S-mode side needs it because [timer_cap] is what clockintr runs under,
   hence one of the credentials kerneltrap's cone closes over
   (claude-notes/completed/kerneltrap.md).

   THE PROOF IS A WIDTH-CROSSING TOWER (64 -> 32 -> 1) AND [tb1] DOES NOT CLOSE
   IT.  [MstatusBits]' [tb_rw] is tuned for [update_slice] towers; this one is
   [bv_extract] / [bv_and] / [bv_or], so the rewrite chain is driven linearly
   and by hand.  The closing move is the point: at the leaf exactly ONE bit is
   symbolic (mcen0's bit 1), so case-splitting it makes both branches closed
   and [vm_compute] finishes -- and the subterm must be taken from what the
   [context] match RETURNS, because rebuilding it from the pattern elaborates
   [@bv_unsigned] at a different (convertible, not equal) width index and then
   [destruct] abstracts nothing.  Measured at 0.25 s. *)
Lemma ti_mcen1_TM (mcen0 : mword 32) :
  eq_vec (_get_Counteren_TM (legalize_mcounteren mcen0 (ti_mcen1 mcen0)))
         ('b"1" : mword 1) = true.
Proof.
  apply eq_vec_true_iff.
  unfold ti_mcen1, i19, _get_Counteren_TM, legalize_mcounteren, Mk_Counteren,
         sys_mcounteren_writable_bits, and_vec, or_vec, word_binop,
         zero_extend', sign_extend', zero_extend, sign_extend, extz_vec, exts_vec.
  mw_prep.
  unfold with_word', with_word, MachineWord.and, MachineWord.or,
         MachineWord.zero_extend, MachineWord.sign_extend.
  zn_norm.
  apply (bv_eq_testbit 1); intros k Hk;
    assert (k = 0) as Hk0; [ lia | subst k ].
  rewrite bv_extract_unsigned bv_and_unsigned bv_extract_unsigned
          bv_or_unsigned bv_zero_extend_unsigned' bv_sign_extend_unsigned.
  rewrite bv_wrap_spec_low; [| lia].
  rewrite Z.shiftr_spec; [| lia].
  rewrite Z.land_spec.
  rewrite bv_wrap_spec_low; [| lia].
  rewrite Z.shiftr_spec; [| lia].
  rewrite Z.lor_spec.
  rewrite (bv_wrap_spec_low 64); [| lia].
  match goal with
  | |- context [ orb ?t _ ] => destruct t
  end; vm_compute; reflexivity.
Qed.

Definition ti_interval : mword 64 := mword_of_int 1000000.
Definition ti_deadline (mtime0 : mword 64) : mword 64 := add_vec mtime0 ti_interval.


Lemma ti_sp_restore (sp0 : mword 64) :
  add_vec (ti_sp1 sp0) (sign_extend' 64 i28) = sp0.
Proof.
  unfold ti_sp1. rewrite add_vec_assoc.
  replace (add_vec (sign_extend' 64 i9) (sign_extend' 64 i28))
    with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
  exact (avi0 sp0).
Qed.

(* ===================================================================== *)
(* The gpr-file after each register write, as nested-insert abbreviations *)
(* over the abstract entry file [m] (WpEntryNew [m_jal] style).           *)
(* ===================================================================== *)
Definition ti_m1 (m : regfile) (sp0 : mword 64) :=
  <[Regidx csp_rs1 := regval_into_reg (ti_sp1 sp0)]> m.
Definition ti_m12 (m : regfile) (sp0 : mword 64) :=
  <[Regidx ti_s0 := regval_into_reg (ti_s0v sp0)]> (ti_m1 m sp0).
Definition ti_m13 (m : regfile) (sp0 menv0 : mword 64) :=
  <[Regidx ti_a5 := regval_into_reg menv0]> (ti_m12 m sp0).
Definition ti_m14 (m : regfile) (sp0 menv0 : mword 64) :=
  <[Regidx ti_a4 := regval_into_reg (cli_wval i14)]> (ti_m13 m sp0 menv0).
Definition ti_m15 (m : regfile) (sp0 menv0 : mword 64) :=
  <[Regidx ti_a4 := regval_into_reg ti_bit63]> (ti_m14 m sp0 menv0).
Definition ti_m16 (m : regfile) (sp0 menv0 : mword 64) :=
  <[Regidx ti_a5 := regval_into_reg (ti_menv1 menv0)]> (ti_m15 m sp0 menv0).
Definition ti_m18 (m : regfile) (sp0 menv0 : mword 64) (mcen0 : mword 32) :=
  <[Regidx ti_a5 := regval_into_reg (zero_extend' 64 mcen0)]> (ti_m16 m sp0 menv0).
Definition ti_m19 (m : regfile) (sp0 menv0 : mword 64) (mcen0 : mword 32) :=
  <[Regidx ti_a5 := regval_into_reg (ti_mcen1 mcen0)]> (ti_m18 m sp0 menv0 mcen0).
Definition ti_m21 (m : regfile) (sp0 menv0 : mword 64) (mcen0 : mword 32) (mtime0 : mword 64) :=
  <[Regidx ti_a5 := regval_into_reg mtime0]> (ti_m19 m sp0 menv0 mcen0).
Definition ti_m22 (m : regfile) (sp0 menv0 : mword 64) (mcen0 : mword 32) (mtime0 : mword 64) :=
  <[Regidx ti_a4 := regval_into_reg (luival i22)]> (ti_m21 m sp0 menv0 mcen0 mtime0).
Definition ti_m23 (m : regfile) (sp0 menv0 : mword 64) (mcen0 : mword 32) (mtime0 : mword 64) :=
  <[Regidx ti_a4 := regval_into_reg ti_interval]> (ti_m22 m sp0 menv0 mcen0 mtime0).
Definition ti_m24 (m : regfile) (sp0 menv0 : mword 64) (mcen0 : mword 32) (mtime0 : mword 64) :=
  <[Regidx ti_a5 := regval_into_reg (ti_deadline mtime0)]> (ti_m23 m sp0 menv0 mcen0 mtime0).
Definition ti_m26 (m : regfile) (sp0 menv0 : mword 64) (mcen0 : mword 32) (mtime0 ra0 : mword 64) :=
  <[Regidx ti_ra := regval_into_reg ra0]> (ti_m24 m sp0 menv0 mcen0 mtime0).
Definition ti_m27 (m : regfile) (sp0 menv0 : mword 64) (mcen0 : mword 32) (mtime0 ra0 s00 : mword 64) :=
  <[Regidx ti_s0 := regval_into_reg s00]> (ti_m26 m sp0 menv0 mcen0 mtime0 ra0).
(* the FINAL file: sp/ra/s0 restored (sp1+16 = sp0), a4 = the interval
   1000000, a5 = the stimecmp deadline (mtime0 + 1000000). *)
Definition ti_mout (m : regfile) (sp0 menv0 : mword 64) (mcen0 : mword 32) (mtime0 ra0 s00 : mword 64) :=
  <[Regidx csp_rs1 := regval_into_reg sp0]> (ti_m27 m sp0 menv0 mcen0 mtime0 ra0 s00).

(* concrete-register-key disequality (both keys literal). *)
Local Ltac ti_reg_neq :=
  let H := fresh in intro H;
  apply (f_equal (fun r : regidx => uint (regidx_bits r))) in H;
  vm_compute in H; discriminate H.

(* drive a total lookup over the insert chain; bottoms out at a premise. *)
Local Ltac ti_look :=
  repeat first [ rewrite upd_eq
               | rewrite upd_ne; [ | ti_reg_neq ] ];
  first [ reflexivity | assumption ].

Local Ltac ti_unfold :=
  unfold ti_mout, ti_m27, ti_m26, ti_m24, ti_m23, ti_m22, ti_m21, ti_m19,
         ti_m18, ti_m16, ti_m15, ti_m14, ti_m13, ti_m12, ti_m1.

(* timerinit obeys the callee-saved ABI: it spills+reloads ra/s0, restores sp,
   and clobbers only the caller-saved temporaries a4/a5 -- every callee-saved
   register (sp, tp, s0, s1, s2..s11) holds its entry value on return. *)

(* ===================================================================== *)
(* THE THEOREM: the whole timerinit() body, one Qed, at a generic         *)
(* fraction [q] of the M-mode config.                                     *)
(* ===================================================================== *)
Section WpTimerinitThm.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* [wp_timerinit]: the whole-function spec over the [stack_own_phys] abstraction. *)
  Lemma wp_timerinit (q : Qp)
      (m : regfile) (sp0 ra0 s00 : mword 64)
      (menv0 stimecmp0 : mword 64) (mcen0 : mword 32)
      (pmpcfg1 : type_of_register pmpcfg_n) (pmpaddrs : type_of_register pmpaddr_n)
      (n : nat) :
    (2 ≤ n)%nat ->
    (* fetch side: all PMP entries unlocked (post-pmpcfg0-write config). *)
    pmp_allows_all pmpcfg1 ->
    (* data side: TOR entry 0 grants both 8-byte stack slots. *)
    pmp_tor0_grants pmpcfg1 pmpaddrs (ti_ea_ra sp0) 8 ->
    pmp_tor0_grants pmpcfg1 pmpaddrs (ti_ea_s0 sp0) 8 ->
    (* entry register file: sp/ra/s0 (ra0 stays SYMBOLIC -- the caller's
       return address; timerinit spills and reloads it). *)
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx ti_ra = ra0 ->
    m !!! Regidx ti_s0 = s00 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg1 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
    pc_is ti_pc9 -∗
    gpr_file m -∗
    menvcfg ↦ᵣ menv0 -∗
    mcounteren ↦ᵣ mcen0 -∗
    stimecmp ↦ᵣ stimecmp0 -∗
    (* timerinit's 16-byte ra/s0 frame as the bottom two slots of
       [stack_own_phys sp0 n] (any depth n >= 2). *)
    stack_own_phys sp0 n -∗
    kernel_text -∗
    (* [mtime] lives in [clock_inv] and advances with the nondeterministic
       clock tick, so the continuation is ∀-quantified over the value [tv]
       the rdtime (csrr time) read -- the stimecmp deadline is relative to
       THAT read. *)
    ( ∀ tv : mword 64,
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg1 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
      pc_is (ret_pc ra0) -∗
      gpr_file (ti_mout m sp0 menv0 mcen0 tv ra0 s00) -∗
      menvcfg ↦ᵣ menvcfg_legalized menv0 (ti_menv1 menv0) -∗
      mcounteren ↦ᵣ legalize_mcounteren mcen0 (ti_mcen1 mcen0) -∗
      stimecmp ↦ᵣ stimecmp_legalized stimecmp0 (ti_deadline tv) -∗
      stack_own_phys sp0 n -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn2 Hpmp Htor_ra Htor_s0 Hsp Hra Hs0.
    iIntros "Hmm Hpmpc Hpaddr Hpc Hfile Hmenv Hmcen Hstc Hstk #Htext Hcont".
    iDestruct (stack_own_phys_split_1 sp0 2 n ltac:(lia) with "Hstk") as "[Htop Hdeep]".
    iDestruct (stack_own_phys_2_elim with "Htop") as (vold_ra vold_s0) "[Hstkra Hstks0]".
    assert (Hpra : ti_ea_ra sp0 = pa_stk sp0 1).
    { unfold ti_ea_ra, ti_sp1, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hps0 : ti_ea_s0 sp0 = pa_stk sp0 2).
    { unfold ti_ea_s0, ti_sp1, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpra) in "Hstkra".
    iEval (rewrite -Hps0) in "Hstks0".
    (* register-nonzero side conditions *)
    assert (Hnz_sp : uint csp_rs1 <> 0) by (vm_compute; discriminate).
    assert (Hnz_ra : uint ti_ra <> 0) by (vm_compute; discriminate).
    assert (Hnz_s0 : uint ti_s0 <> 0) by (vm_compute; discriminate).
    assert (Hnz_a4 : uint ti_a4 <> 0) by (vm_compute; discriminate).
    assert (Hnz_a5 : uint ti_a5 <> 0) by (vm_compute; discriminate).
    (* compressed-register bridges *)
    assert (Hcreg12  : creg2reg_idx ti_cs0 = Regidx ti_s0) by (vm_compute; reflexivity).
    assert (Hcreg16d : creg2reg_idx ti_ca5 = Regidx ti_a5) by (vm_compute; reflexivity).
    assert (Hcreg16s : creg2reg_idx ti_ca4 = Regidx ti_a4) by (vm_compute; reflexivity).
    (* PC steps *)
    assert (P0  : add_vec_int ti_pc9  2 = ti_pc10) by (vm_compute; reflexivity).
    assert (P1  : add_vec_int ti_pc10 2 = ti_pc11) by (vm_compute; reflexivity).
    assert (P2  : add_vec_int ti_pc11 2 = ti_pc12) by (vm_compute; reflexivity).
    assert (P3  : add_vec_int ti_pc12 2 = ti_pc13) by (vm_compute; reflexivity).
    assert (P4  : add_vec_int ti_pc13 4 = ti_pc14) by (vm_compute; reflexivity).
    assert (P5  : add_vec_int ti_pc14 2 = ti_pc15) by (vm_compute; reflexivity).
    assert (P6  : add_vec_int ti_pc15 2 = ti_pc16) by (vm_compute; reflexivity).
    assert (P7  : add_vec_int ti_pc16 2 = ti_pc17) by (vm_compute; reflexivity).
    assert (P8  : add_vec_int ti_pc17 4 = ti_pc18) by (vm_compute; reflexivity).
    assert (P9  : add_vec_int ti_pc18 4 = ti_pc19) by (vm_compute; reflexivity).
    assert (P10 : add_vec_int ti_pc19 4 = ti_pc20) by (vm_compute; reflexivity).
    assert (P11 : add_vec_int ti_pc20 4 = ti_pc21) by (vm_compute; reflexivity).
    assert (P12 : add_vec_int ti_pc21 4 = ti_pc22) by (vm_compute; reflexivity).
    assert (P13 : add_vec_int ti_pc22 4 = ti_pc23) by (vm_compute; reflexivity).
    assert (P14 : add_vec_int ti_pc23 4 = ti_pc24) by (vm_compute; reflexivity).
    assert (P15 : add_vec_int ti_pc24 2 = ti_pc25) by (vm_compute; reflexivity).
    assert (P16 : add_vec_int ti_pc25 4 = ti_pc26) by (vm_compute; reflexivity).
    assert (P17 : add_vec_int ti_pc26 2 = ti_pc27) by (vm_compute; reflexivity).
    assert (P18 : add_vec_int ti_pc27 2 = ti_pc28) by (vm_compute; reflexivity).
    assert (P19 : add_vec_int ti_pc28 2 = ti_pc29) by (vm_compute; reflexivity).
    (* closed-value bridges *)
    assert (Hb63 : shift_bits_left (cli_wval i14)
                     (subrange_vec_dec sh15 (Z.sub log2_xlen 1) 0) = ti_bit63)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hival : add_vec (luival i22) (sign_extend' 64 i23) = ti_interval)
      by (apply bv_eq; vm_compute; reflexivity).
    pose proof (ti_sp_restore sp0) as Hspres.

    (* ---- 9. c.addi sp, -16 ---- *)
    iApply (wp_addi_gpr ti_pc9 true csp_rs1 csp_rs1 (sign_extend' 12 i9) m pmpcfg1 q
              Hpmp ltac:(boot_static) Hnz_sp
              with "Hmm Hpmpc Hpc Hfile []").
    { iApply (ti_instr9 with "Htext"). }
    iEval (change (if true then 2%Z else 4%Z) with 2%Z). iEval (rewrite P0). iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (rewrite sext6_12_64 Hsp) in "Hfile".
    iEval (change (<[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 i9))]> m)
             with (ti_m1 m sp0)) in "Hfile".

    (* ---- 10. c.sdsp ra, 8(sp) ---- *)
    assert (Lsp1 : ti_m1 m sp0 !!! Regidx csp_rs1 = ti_sp1 sp0)
      by (ti_unfold; ti_look).
    assert (Lra1 : ti_m1 m sp0 !!! Regidx ti_ra = ra0)
      by (ti_unfold; ti_look).
    assert (Ls01 : ti_m1 m sp0 !!! Regidx ti_s0 = s00)
      by (ti_unfold; ti_look).
    assert (Hea_ra1 : add_vec (ti_m1 m sp0 !!! Regidx csp_rs1)
              (sign_extend' 64 (zero_extend' 12 (concat_vec u10 ('b"000")))) = ti_ea_ra sp0)
      by (rewrite Lsp1; reflexivity).
    assert (Htor10 : pmp_tor0_grants pmpcfg1 pmpaddrs
              (add_vec (ti_m1 m sp0 !!! Regidx csp_rs1)
                 (sign_extend' 64 (zero_extend' 12 (concat_vec u10 ('b"000"))))) 8)
      by (rewrite Hea_ra1; exact Htor_ra).
    iApply (wp_csdsp_gpr_tor ti_pc10 u10 ti_ra (ti_m1 m sp0) vold_ra pmpcfg1 pmpaddrs q
              Hpmp ltac:(boot_static) Htor10
              with "Hmm Hpmpc Hpaddr Hpc Hfile [] [Hstkra]").
    { iApply (ti_instr10 with "Htext"). }
    { rewrite Hea_ra1. iExact "Hstkra". }
    iEval (rewrite P1 Hea_ra1 Lra1). iIntros "Hmm Hpmpc Hpaddr Hpc Hfile Hstkra".

    (* ---- 11. c.sdsp s0, 0(sp) ---- *)
    assert (Hea_s01 : add_vec (ti_m1 m sp0 !!! Regidx csp_rs1)
              (sign_extend' 64 (zero_extend' 12 (concat_vec u11 ('b"000")))) = ti_ea_s0 sp0)
      by (rewrite Lsp1; reflexivity).
    assert (Htor11 : pmp_tor0_grants pmpcfg1 pmpaddrs
              (add_vec (ti_m1 m sp0 !!! Regidx csp_rs1)
                 (sign_extend' 64 (zero_extend' 12 (concat_vec u11 ('b"000"))))) 8)
      by (rewrite Hea_s01; exact Htor_s0).
    iApply (wp_csdsp_gpr_tor ti_pc11 u11 ti_s0 (ti_m1 m sp0) vold_s0 pmpcfg1 pmpaddrs q
              Hpmp ltac:(boot_static) Htor11
              with "Hmm Hpmpc Hpaddr Hpc Hfile [] [Hstks0]").
    { iApply (ti_instr11 with "Htext"). }
    { rewrite Hea_s01. iExact "Hstks0". }
    iEval (rewrite P2 Hea_s01 Ls01). iIntros "Hmm Hpmpc Hpaddr Hpc Hfile Hstks0".

    (* ---- 12. c.addi4spn s0, sp, 16 ---- *)
    iApply (wp_addi_gpr ti_pc12 true csp_rs1 ti_s0 (caddi4spn_imm nz12) (ti_m1 m sp0) pmpcfg1 q
              Hpmp ltac:(boot_static) Hnz_s0
              with "Hmm Hpmpc Hpc Hfile []").
    { iApply (ti_instr12 with "Htext"). }
    iEval (change (if true then 2%Z else 4%Z) with 2%Z). iEval (rewrite P3 Lsp1). iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx ti_s0 := regval_into_reg
                      (add_vec (ti_sp1 sp0) (sign_extend' 64 (caddi4spn_imm nz12)))]> (ti_m1 m sp0))
             with (ti_m12 m sp0)) in "Hfile".

    (* ---- 13. csrr a5, menvcfg ---- *)
    iApply (wp_csrr_menvcfg_gpr ti_pc13 ti_a5 menv0 (ti_m12 m sp0) pmpcfg1 q
              Hpmp ltac:(boot_static) Hnz_a5
              with "Hmm Hpmpc Hpc Hfile Hmenv []").
    { iApply (ti_instr13 with "Htext"). }
    iEval (rewrite P4). iIntros "Hmm Hpmpc Hpc Hfile Hmenv".
    iEval (change (<[Regidx ti_a5 := regval_into_reg menv0]> (ti_m12 m sp0))
             with (ti_m13 m sp0 menv0)) in "Hfile".

    (* ---- 14. c.li a4, -1 ---- *)
    iDestruct (gpr_file_x0 (ti_m13 m sp0 menv0) cli_rs1 ltac:(vm_compute; reflexivity)
                 with "Hfile") as "[%Hx0_14 Hfile]".
    iApply (wp_addi_gpr ti_pc14 true cli_rs1 ti_a4 (sign_extend' 12 i14) (ti_m13 m sp0 menv0) pmpcfg1 q
              Hpmp ltac:(boot_static) Hnz_a4
              with "Hmm Hpmpc Hpc Hfile []").
    { iApply (ti_instr14 with "Htext"). }
    iEval (change (if true then 2%Z else 4%Z) with 2%Z). iEval (rewrite P5 Hx0_14 add_vec_zero_l sext6_12_64). iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg (cli_wval i14)]> (ti_m13 m sp0 menv0))
             with (ti_m14 m sp0 menv0)) in "Hfile".

    (* ---- 15. c.slli a4, 63 ---- *)
    assert (L15a4 : ti_m14 m sp0 menv0 !!! Regidx ti_a4 = cli_wval i14)
      by (ti_unfold; ti_look).
    iApply (wp_slli_gpr ti_pc15 true ti_a4 ti_a4 sh15 (ti_m14 m sp0 menv0) pmpcfg1 q
              Hpmp ltac:(boot_static) Hnz_a4
              with "Hmm Hpmpc Hpc Hfile []").
    { iApply (ti_instr15 with "Htext"). }
    iEval (change (if true then 2%Z else 4%Z) with 2%Z). iEval (rewrite P6 L15a4 Hb63). iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg ti_bit63]> (ti_m14 m sp0 menv0))
             with (ti_m15 m sp0 menv0)) in "Hfile".

    (* ---- 16. c.or a5, a4 ---- *)
    assert (L16a5 : ti_m15 m sp0 menv0 !!! Regidx ti_a5 = menv0)
      by (ti_unfold; ti_look).
    assert (L16a4 : ti_m15 m sp0 menv0 !!! Regidx ti_a4 = ti_bit63)
      by (ti_unfold; ti_look).
    iApply (wp_or_gpr ti_pc16 true ti_a4 ti_a5 ti_a5 (ti_m15 m sp0 menv0) pmpcfg1 q
              Hpmp ltac:(boot_static) Hnz_a5
              with "Hmm Hpmpc Hpc Hfile []").
    { iApply (ti_instr16 with "Htext"). }
    iEval (change (if true then 2%Z else 4%Z) with 2%Z). iEval (rewrite P7 L16a5 L16a4). iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (or_vec menv0 ti_bit63)]> (ti_m15 m sp0 menv0))
             with (ti_m16 m sp0 menv0)) in "Hfile".

    (* ---- 17. csrw menvcfg, a5 ---- *)
    assert (L17a5 : ti_m16 m sp0 menv0 !!! Regidx ti_a5 = ti_menv1 menv0)
      by (ti_unfold; ti_look).
    iApply (wp_csrw_menvcfg_gpr ti_pc17 ti_a5 (ti_m16 m sp0 menv0) menv0 pmpcfg1 q
              Hpmp ltac:(boot_static) Hnz_a5
              with "Hmm Hpmpc Hpc Hfile Hmenv []").
    { iApply (ti_instr17 with "Htext"). }
    iEval (rewrite P8 L17a5). iIntros "Hmm Hpmpc Hpc Hfile Hmenv".

    (* ---- 18. csrr a5, mcounteren ---- *)
    iApply (wp_csrr_mcounteren_gpr ti_pc18 ti_a5 mcen0 (ti_m16 m sp0 menv0) pmpcfg1 q
              Hpmp ltac:(boot_static) Hnz_a5
              with "Hmm Hpmpc Hpc Hfile Hmcen []").
    { iApply (ti_instr18 with "Htext"). }
    iEval (rewrite P9). iIntros "Hmm Hpmpc Hpc Hfile Hmcen".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (zero_extend' 64 mcen0)]> (ti_m16 m sp0 menv0))
             with (ti_m18 m sp0 menv0 mcen0)) in "Hfile".

    (* ---- 19. ori a5, a5, 2 ---- *)
    assert (L19a5 : ti_m18 m sp0 menv0 mcen0 !!! Regidx ti_a5 = zero_extend' 64 mcen0)
      by (ti_unfold; ti_look).
    iApply (wp_ori_gpr ti_pc19 ti_a5 ti_a5 i19 (ti_m18 m sp0 menv0 mcen0) pmpcfg1 q
              Hpmp ltac:(boot_static) Hnz_a5
              with "Hmm Hpmpc Hpc Hfile []").
    { iApply (ti_instr19 with "Htext"). }
    iEval (rewrite P10 L19a5). iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg
                      (or_vec (zero_extend' 64 mcen0) (sign_extend' 64 i19))]>
                     (ti_m18 m sp0 menv0 mcen0))
             with (ti_m19 m sp0 menv0 mcen0)) in "Hfile".

    (* ---- 20. csrw mcounteren, a5 ---- *)
    assert (L20a5 : ti_m19 m sp0 menv0 mcen0 !!! Regidx ti_a5 = ti_mcen1 mcen0)
      by (ti_unfold; ti_look).
    iApply (wp_csrw_mcounteren_gpr ti_pc20 ti_a5 (ti_m19 m sp0 menv0 mcen0) mcen0 pmpcfg1 q
              Hpmp ltac:(boot_static) Hnz_a5
              with "Hmm Hpmpc Hpc Hfile Hmcen []").
    { iApply (ti_instr20 with "Htext"). }
    iEval (rewrite P11 L20a5). iIntros "Hmm Hpmpc Hpc Hfile Hmcen".

    (* ---- 21. csrr a5, time ---- *)
    iApply (wp_csrr_time_gpr ti_pc21 ti_a5 (ti_m19 m sp0 menv0 mcen0) pmpcfg1 q
              Hpmp ltac:(boot_static) Hnz_a5
              with "Hmm Hpmpc Hpc Hfile []").
    { iApply (ti_instr21 with "Htext"). }
    iEval (rewrite P12). iIntros (tv) "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg tv]> (ti_m19 m sp0 menv0 mcen0))
             with (ti_m21 m sp0 menv0 mcen0 tv)) in "Hfile".

    (* ---- 22. lui a4, 0xf4 ---- *)
    iApply (wp_lui_gpr ti_pc22 false ti_a4 i22 (ti_m21 m sp0 menv0 mcen0 tv) pmpcfg1 q
              Hpmp ltac:(boot_static) Hnz_a4
              with "Hmm Hpmpc Hpc Hfile []").
    { iApply (ti_instr22 with "Htext"). }
    iEval (change (if false then 2%Z else 4%Z) with 4%Z). iEval (rewrite P13). iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg (luival i22)]>
                     (ti_m21 m sp0 menv0 mcen0 tv))
             with (ti_m22 m sp0 menv0 mcen0 tv)) in "Hfile".

    (* ---- 23. addi a4, a4, 576 ---- *)
    assert (L23a4 : ti_m22 m sp0 menv0 mcen0 tv !!! Regidx ti_a4 = luival i22)
      by (ti_unfold; ti_look).
    iApply (wp_addi_gpr ti_pc23 false ti_a4 ti_a4 i23 (ti_m22 m sp0 menv0 mcen0 tv) pmpcfg1 q
              Hpmp ltac:(boot_static) Hnz_a4
              with "Hmm Hpmpc Hpc Hfile []").
    { iApply (ti_instr23 with "Htext"). }
    iEval (change (if false then 2%Z else 4%Z) with 4%Z). iEval (rewrite P14 L23a4 Hival). iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg ti_interval]>
                     (ti_m22 m sp0 menv0 mcen0 tv))
             with (ti_m23 m sp0 menv0 mcen0 tv)) in "Hfile".

    (* ---- 24. c.add a5, a4 ---- *)
    assert (L24a5 : ti_m23 m sp0 menv0 mcen0 tv !!! Regidx ti_a5 = tv)
      by (ti_unfold; ti_look).
    assert (L24a4 : ti_m23 m sp0 menv0 mcen0 tv !!! Regidx ti_a4 = ti_interval)
      by (ti_unfold; ti_look).
    iApply (wp_add_gpr ti_pc24 true ti_a4 ti_a5 ti_a5 (ti_m23 m sp0 menv0 mcen0 tv) pmpcfg1 q
              Hpmp ltac:(boot_static) Hnz_a5
              with "Hmm Hpmpc Hpc Hfile []").
    { iApply (ti_instr24 with "Htext"). }
    iEval (change (if true then 2%Z else 4%Z) with 2%Z). iEval (rewrite P15 L24a5 L24a4). iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (add_vec tv ti_interval)]>
                     (ti_m23 m sp0 menv0 mcen0 tv))
             with (ti_m24 m sp0 menv0 mcen0 tv)) in "Hfile".

    (* ---- 25. csrw stimecmp, a5 ---- *)
    assert (L25a5 : ti_m24 m sp0 menv0 mcen0 tv !!! Regidx ti_a5 = ti_deadline tv)
      by (ti_unfold; ti_look).
    iApply (wp_csrw_stimecmp_gpr ti_pc25 ti_a5 (ti_m24 m sp0 menv0 mcen0 tv) stimecmp0 pmpcfg1 q
              Hpmp ltac:(boot_static) Hnz_a5
              with "Hmm Hpmpc Hpc Hfile Hstc []").
    { iApply (ti_instr25 with "Htext"). }
    iEval (rewrite P16 L25a5). iIntros "Hmm Hpmpc Hpc Hfile Hstc".

    (* ---- 26. c.ldsp ra, 8(sp) ---- *)
    assert (L26sp : ti_m24 m sp0 menv0 mcen0 tv !!! Regidx csp_rs1 = ti_sp1 sp0)
      by (ti_unfold; ti_look).
    assert (Hea_ra26 : add_vec (ti_m24 m sp0 menv0 mcen0 tv !!! Regidx csp_rs1)
              (sign_extend' 64 (zero_extend' 12 (concat_vec u10 ('b"000")))) = ti_ea_ra sp0)
      by (rewrite L26sp; reflexivity).
    assert (Htor26 : pmp_tor0_grants pmpcfg1 pmpaddrs
              (add_vec (ti_m24 m sp0 menv0 mcen0 tv !!! Regidx csp_rs1)
                 (sign_extend' 64 (zero_extend' 12 (concat_vec u10 ('b"000"))))) 8)
      by (rewrite Hea_ra26; exact Htor_ra).
    iApply (wp_cldsp_gpr_tor ti_pc26 u10 ti_ra (ti_m24 m sp0 menv0 mcen0 tv) ra0
              pmpcfg1 pmpaddrs q Hpmp ltac:(boot_static) Htor26 Hnz_ra
              with "Hmm Hpmpc Hpaddr Hpc Hfile [] [Hstkra]").
    { iApply (ti_instr26 with "Htext"). }
    { rewrite Hea_ra26. iExact "Hstkra". }
    iEval (rewrite P17 Hea_ra26). iIntros "Hmm Hpmpc Hpaddr Hpc Hfile Hstkra".
    iEval (change (<[Regidx ti_ra := regval_into_reg ra0]> (ti_m24 m sp0 menv0 mcen0 tv))
             with (ti_m26 m sp0 menv0 mcen0 tv ra0)) in "Hfile".

    (* ---- 27. c.ldsp s0, 0(sp) ---- *)
    assert (L27sp : ti_m26 m sp0 menv0 mcen0 tv ra0 !!! Regidx csp_rs1 = ti_sp1 sp0)
      by (ti_unfold; ti_look).
    assert (Hea_s027 : add_vec (ti_m26 m sp0 menv0 mcen0 tv ra0 !!! Regidx csp_rs1)
              (sign_extend' 64 (zero_extend' 12 (concat_vec u11 ('b"000")))) = ti_ea_s0 sp0)
      by (rewrite L27sp; reflexivity).
    assert (Htor27 : pmp_tor0_grants pmpcfg1 pmpaddrs
              (add_vec (ti_m26 m sp0 menv0 mcen0 tv ra0 !!! Regidx csp_rs1)
                 (sign_extend' 64 (zero_extend' 12 (concat_vec u11 ('b"000"))))) 8)
      by (rewrite Hea_s027; exact Htor_s0).
    iApply (wp_cldsp_gpr_tor ti_pc27 u11 ti_s0 (ti_m26 m sp0 menv0 mcen0 tv ra0) s00
              pmpcfg1 pmpaddrs q Hpmp ltac:(boot_static) Htor27 Hnz_s0
              with "Hmm Hpmpc Hpaddr Hpc Hfile [] [Hstks0]").
    { iApply (ti_instr27 with "Htext"). }
    { rewrite Hea_s027. iExact "Hstks0". }
    iEval (rewrite P18 Hea_s027). iIntros "Hmm Hpmpc Hpaddr Hpc Hfile Hstks0".
    iEval (change (<[Regidx ti_s0 := regval_into_reg s00]> (ti_m26 m sp0 menv0 mcen0 tv ra0))
             with (ti_m27 m sp0 menv0 mcen0 tv ra0 s00)) in "Hfile".

    (* ---- 28. c.addi sp, 16 ---- *)
    assert (L28sp : ti_m27 m sp0 menv0 mcen0 tv ra0 s00 !!! Regidx csp_rs1 = ti_sp1 sp0)
      by (ti_unfold; ti_look).
    iApply (wp_addi_gpr ti_pc28 true csp_rs1 csp_rs1 (sign_extend' 12 i28)
              (ti_m27 m sp0 menv0 mcen0 tv ra0 s00) pmpcfg1 q
              Hpmp ltac:(boot_static) Hnz_sp
              with "Hmm Hpmpc Hpc Hfile []").
    { iApply (ti_instr28 with "Htext"). }
    iEval (change (if true then 2%Z else 4%Z) with 2%Z). iEval (rewrite sext6_12_64 P19 L28sp Hspres). iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx csp_rs1 := regval_into_reg sp0]>
                     (ti_m27 m sp0 menv0 mcen0 tv ra0 s00))
             with (ti_mout m sp0 menv0 mcen0 tv ra0 s00)) in "Hfile".

    (* ---- 29. c.ret ---- *)
    assert (L29ra : ti_mout m sp0 menv0 mcen0 tv ra0 s00 !!! Regidx ti_ra = ra0)
      by (ti_unfold; ti_look).
    iApply (wp_cret_gpr_zca ti_pc29 ti_ra (ti_mout m sp0 menv0 mcen0 tv ra0 s00) pmpcfg1 q
              Hpmp ltac:(boot_static) Hnz_ra
              with "Hmm Hpmpc Hpc Hfile []").
    { iApply (ti_instr29 with "Htext"). }
    iEval (rewrite L29ra). iIntros "Hmm Hpmpc Hpc Hfile".

    (* re-bundle timerinit's two frame slots back into [stack_own_phys sp0 n]
       and hand everything to the caller's continuation. *)
    iEval (rewrite Hpra) in "Hstkra".
    iEval (rewrite Hps0) in "Hstks0".
    iDestruct (stack_own_phys_2_intro with "Hstkra Hstks0") as "Htop".
    iDestruct (stack_own_phys_split_2 sp0 2 n ltac:(lia) with "[$Htop $Hdeep]") as "Hstk".
    iApply ("Hcont" $! tv with "Hmm Hpmpc Hpaddr Hpc Hfile Hmenv Hmcen Hstc Hstk").
  Qed.

End WpTimerinitThm.
