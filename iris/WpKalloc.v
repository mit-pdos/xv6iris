(* WpKalloc.v -- instruction-level proof of the kernel's [kalloc] (0x80000b20)
   and [kfree] (0x80000a38) against the allocator spec in KallocInv.v.

   kalloc/kfree are whole-function S-mode proofs in the mould of [wp_release]
   (WpRelease.v) and [wp_acquire_lock] (WpAcquireLock.v): they thread the S-mode
   machine configuration (mstatus/pmp/pte/tlb) through every instruction and
   CALL the sub-functions acquire / release / memset via [jal], discharging each
   callee's whole-function WP.  The novel content is the free-list manipulation,
   which is discharged by KallocInv's transfer lemmas [kmem_res_pop] /
   [kmem_res_push] together with [page_head8_word_at] / [run_page_page_own]. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
From iris.base_logic.lib Require Import ghost_var.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import MinstretInv InstrBytes.
Require Import WpEntryNew WpAuipc.
Require Import WpGpr WpGprAddi WpGprRvc WpGprLui.
Require Import SmodeCore WpSmodeGpr WpMemsetS WpKernelvecNew WpPushOff.
Require Import WpMycpu WpPushOffTop WpAcquireMem.
Require Import WpLock WpPopOff.
Require Import WpAcquireLock WpRelease WpMemsetPage WpHoldingInv.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KallocInv WpKallocDecode WpFreelistMem.
Require Import RiscvExec.
Require Export WpSmodeToBeDeleted WpSmodeAddiw WpSmodeShiftiop WpSmodeRtype WpSmodeItype WpSmodeUtype.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Section Kalloc.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Notation AK := KernelSyms.kalloc.
  Notation AQ := KernelSyms.acquire.
  Notation PO := KernelSyms.push_off.

  (* ===== [smode_config] leaf wrappers kalloc's body needs ===== *)



  Lemma wp_sd_s_ram_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 64) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    ea ↦₈ vold -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗ ea ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_sd_s_ram root_ppn E Φ pc rs2 rs1 imm m vold mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_ld_s_ram_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (v : bv 64) {dq dqm : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    ea ↦₈{ dqm } v -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      ea ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN Hrd.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_ld_s_ram root_ppn E Φ pc rd rs1 imm m v mstatus0 mie_v mdv0 menvcfg0 (dq:=dq) (dqm:=dqm)
              HN Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_cbeqz_fall_s_config_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm8 : mword 8) (rs : cregidx) (rd1 : mword 5)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    creg2reg_idx rs = Regidx rd1 ->
    uint rd1 <> 0 ->
    eq_vec (m !!! Regidx rd1) zero_reg = false ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BEQ)) -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hrs Hrd1 Hcmp) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_cbeqz_fall_s_config root_ppn E Φ pc imm8 rs rd1 m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrs Hrd1 Hcmp
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.

  Lemma wp_gpr_write_s_config_base_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rsa rsb : mword 5) (i : instruction) (wval : mword 64)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    (forall s_pc : mstate,
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4 ->
       (if Z.eqb (uint rsa) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsa))) s_pc.(sregs)) = m !!! Regidx rsa ->
       (if Z.eqb (uint rsb) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsb))) s_pc.(sregs)) = m !!! Regidx rsb ->
       exec (execute i) s_pc
       = Some (RETIRE_SUCCESS,
               set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval))) ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false i -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hrd Hbexec) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_gpr_write_s_config_base root_ppn E Φ pc rd rsa rsb i wval m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd Hbexec
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.

  (* ============================================================= *)
  (* kalloc: whole-function S-mode WP.  COMPLETE (Qed, no admits).  *)
  (* Single full-[stack_own] lemma: pre and post are [stack_own     *)
  (* sp0 n] (n >= 14).  kalloc peels its own 4-slot frame and lends  *)
  (* the deep tail [stack_own spr (n-4)] to acquire / release /      *)
  (* memset in turn, each returning it intact (no stack leak).       *)
  (* ============================================================= *)
  Lemma wp_kalloc (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (γ : gname)
      (m : gmap regidx (mword 64))
      (qcpuold : bv 64)
      (qnoff qintena_old : mword 32) (a0f fl : mword 64)
      (γc : gname) (bsie : mword 1)
      (n : nat)
      :
    let pcE : mword 64 := mword_of_int AK in
    let sp0 := m !!! Regidx csp_rs1 in
    let spr := add_vec (m !!! Regidx csp_rs1 : mword 64) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    let a_r24 := add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) in
    let a_r16 := add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let a_r8  := add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    let R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m in
    let R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1 in
    let R3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (mword_of_int (AK + 0x0a) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> R2 in
    let R4 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (R3 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0x7fe : mword 12)))]> R3 in
    let mA := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (AK + 0x12) : mword 64) 4)]> R4 in
    let lkA := mA !!! Regidx (mword_of_int 10 : mword 5) in
    let sp0A := mA !!! Regidx csp_rs1 in
    let spdA := add_vec sp0A (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    let q_r24 := add_vec spdA (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) in
    let q_r16 := add_vec spdA (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let q_r8  := add_vec spdA (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let pspdA := add_vec spdA (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    let q_p24 := add_vec pspdA (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) in
    let q_p16 := add_vec pspdA (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let q_p8  := add_vec pspdA (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let q_p0  := add_vec pspdA (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let pspm10A := add_vec pspdA (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) in
    let q_fra := add_vec pspm10A (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let q_fs0 := add_vec pspm10A (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let q_noff := add_vec a0f (sign_extend' 64 (mword_of_int 120 : mword 12)) in
    let q_intena := add_vec a0f (sign_extend' 64 (mword_of_int 124 : mword 12)) in
    let q_cpu := add_vec lkA (sign_extend' 64 (mword_of_int 16 : mword 12)) in
    let q_storeval32 := (zeros' 32 : mword 32) in
    let q_noff_a5 := sign_extend' 64 (subrange_vec_dec
        (add_vec (sign_extend' 64 qnoff) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0) in
    let q_noff_store := (autocast (T := mword) (subrange_vec_dec q_noff_a5 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    let q_ret_tgt := update_vec_dec (add_vec (mA !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    (14 <= n)%nat ->
    ↑minstretN ⊆ E ->
    ↑lockN ⊆ E ->
    eq_vec (qcpuold : mword 64) (mycpu_ret (mA !!! Regidx (mword_of_int 4 : mword 5))) = false ->
    eq_vec (access_vec_dec q_ret_tgt 0) ('b"0") = true ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    fl = mword_of_int (KernelSyms.kmem + 24) ->
    a0f = mycpu_ret (mA !!! Regidx (mword_of_int 4 : mword 5)) ->
    zopz0zKzJ_s zero_reg (sign_extend' 64 q_noff_store) = false ->
    eq_vec (sign_extend' 64
       (if eq_vec (sign_extend' 64 qnoff) zero_reg then q_storeval32 else qintena_old)) zero_reg = true ->
    smode_config γc (DfracOwn 1) -∗
    ghost_var γc (1/2) bsie -∗
    tlb_inv root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m -∗
    stack_own sp0 n -∗
    q_noff ↦₄ qnoff -∗
    q_intena ↦₄ qintena_old -∗
    is_lock γ lkA (kmem_res fl) -∗
    q_cpu ↦₈ qcpuold -∗
    ( ∀ (mr : gmap regidx (mword 64)),
      smode_config γc (DfracOwn 1) -∗
      ghost_var γc (1/2) bsie -∗
      tlb_inv root_ppn -∗
      pc_is ret_tgt -∗
      gpr_file mr -∗
      kalloc_post (mr !!! Regidx (mword_of_int 10 : mword 5)) -∗
      stack_own sp0 n -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros pcE sp0 spr a_r24 a_r16 a_r8 ret_tgt
      R1 R2 R3 R4 mA lkA sp0A spdA q_r24 q_r16 q_r8 pspdA q_p24 q_p16 q_p8 q_p0
      pspm10A q_fra q_fs0 q_noff q_intena q_cpu
      q_storeval32 q_noff_a5 q_noff_store q_ret_tgt
      Hn HN HNl Hcpune Hret0 Hretm Hfl Ha0fcpu Hnoffpos Hintena0.
    iIntros "Hcfg Htoken Htlbinv #Htext Hpc Hfile Hstk Hnoff Hint #Hlock Hcpu Hcont".
    assert (HmAsp : mA !!! Regidx csp_rs1 = spr).
    { rewrite /mA lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R4 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R2 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R1 lookup_total_insert. reflexivity. }
    (* peel kalloc's own 4-slot frame [spr, sp0); slots 1..3 hold ra/s0/s1,
       slot 4 is padding.  The deep tail [stack_own spr (n-4)] is lent to
       acquire / release / memset in turn and returned intact (no leak). *)
    iDestruct (stack_own_split_1 sp0 4 n ltac:(lia) with "Hstk") as "[Htop Hdeep]".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Htop".
    iDestruct "Htop" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (vr24) "Hr24". iDestruct "S2" as (vr16) "Hr16".
    iDestruct "S3" as (vr8)  "Hr8".  iDestruct "S4" as (vg4)  "Hg4".
    assert (Hb1 : add_vec (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hsprstk : pa_stk sp0 4 = spr).
    { rewrite /pa_stk /spr /sp0 /add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".  iEval (rewrite -Hb4) in "Hg4".
    iEval (rewrite Hsprstk) in "Hdeep".
    (* unbundle the ambient S-mode config: raw cells + folded facts + the SIE
       ghost half (Hgc); the caller's token Htoken is returned at the end. *)
    iPoseProof (kai_00 with "Htext") as "Hi00".
    iPoseProof (kai_02 with "Htext") as "Hi02".
    iPoseProof (kai_04 with "Htext") as "Hi04".
    iPoseProof (kai_06 with "Htext") as "Hi06".
    iPoseProof (kai_08 with "Htext") as "Hi08".
    iPoseProof (kai_0a with "Htext") as "Hi0a".
    iPoseProof (kai_0e with "Htext") as "Hi0e".
    (* +0x00 c.addi16sp sp,-32 *)
    iApply (wp_caddi_gpr_s_config_scfg root_ppn γc E Φ pcE csp_rs1 (mword_of_int 32 : mword 6) m
              (dq:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi00 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr)
      by (rewrite /R1; apply lookup_total_insert).
    assert (Hpp02 : add_vec_int pcE 2 = mword_of_int (AK + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,24(sp) *)
    iApply (wp_csdsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (AK + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              R1 vr24 (dq:=DfracOwn 1)
              HN
              with "Hcfg Htlbinv Hpc Hfile Hi02 [Hr24] [-]").
    { iEval (rewrite HspR1). iExact "Hr24". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (AK + 0x02) : mword 64) 2 = mword_of_int (AK + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,16(sp) *)
    iApply (wp_csdsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (AK + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              R1 vr16 (dq:=DfracOwn 1)
              HN
              with "Hcfg Htlbinv Hpc Hfile Hi04 [Hr16] [-]").
    { iEval (rewrite HspR1). iExact "Hr16". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (AK + 0x04) : mword 64) 2 = mword_of_int (AK + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,8(sp) *)
    iApply (wp_csdsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (AK + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              R1 vr8 (dq:=DfracOwn 1)
              HN
              with "Hcfg Htlbinv Hpc Hfile Hi06 [Hr8] [-]").
    { iEval (rewrite HspR1). iExact "Hr8". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (AK + 0x06) : mword 64) 2 = mword_of_int (AK + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_gpr_s_config_scfg root_ppn γc E Φ (mword_of_int (AK + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              R1 (dq:=DfracOwn 1)
              HN
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi08 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    assert (Hpp0a : add_vec_int (mword_of_int (AK + 0x08) : mword 64) 2 = mword_of_int (AK + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a auipc a0,0x11 *)
    iApply (wp_auipc_s_scfg root_ppn γc E Φ (mword_of_int (AK + 0x0a)) (mword_of_int 10 : mword 5) (mword_of_int 0x11 : mword 20)
              R2 (dq:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi0a [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    assert (Hpp0e : add_vec_int (mword_of_int (AK + 0x0a) : mword 64) 4 = mword_of_int (AK + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e addi a0,a0,2046  (a0 := &kmem) *)
    iApply (wp_addi4_s_scfg root_ppn γc E Φ (mword_of_int (AK + 0x0e)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 0x7fe : mword 12)
              R3 (dq:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi0e [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    assert (Hpp12 : add_vec_int (mword_of_int (AK + 0x0e) : mword 64) 4 = mword_of_int (AK + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* ---- a0 = &kmem now (R4 !!! a0) ---- *)
    iPoseProof (kai_12 with "Htext") as "Hi12".
    (* +0x12 jal ra,acquire : link ra := +0x16, jump to acquire's entry *)
    iApply (wp_jal_gpr_s_zca root_ppn γc E Φ (mword_of_int (AK + 0x12)) (mword_of_int 1 : mword 5) (mword_of_int 0xc8 : mword 21)
              R4 1%Qp
              HN ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi12 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    assert (Htgta : add_vec (mword_of_int (AK + 0x12) : mword 64) (sign_extend' 64 (mword_of_int 0xc8 : mword 21)) = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgta) in "Hpc".
    (* ---- acquire(&kmem): CSL acquire, returns [locked γ ∗ kmem_res fl] ---- *)
    (* re-bundle the ambient config; pass smode_config + the SIE token *)
    iApply (wp_acquire_lock root_ppn E Φ γ (kmem_res fl) mA
              qcpuold (n - 4)%nat qnoff qintena_old a0f γc bsie
              HN HNl ltac:(lia) (eq_sym Ha0fcpu) Hcpune Hret0
              with "Hcfg Htoken Htlbinv Htext Hpc Hfile
                    [Hdeep] Hnoff Hint Hlock Hcpu [-]").
    { iEval (rewrite HmAsp). iExact "Hdeep". }
    iIntros (mfin) "Hcfg Htoken Htlbinv Hpc Htok HRres Hfile %Hpins
             Hdeep Hnoff Hint Hcpu".
    iEval (rewrite HmAsp) in "Hdeep".
    (* re-open the config for kalloc's own post-acquire leaves (fresh existential,
       rebound to the same names after clearing the consumed pre-acquire ones) *)
    (* ---- acquire returned: [locked γ ∗ kmem_res fl] held, pc = +0x16 ---- *)
    unfold callee_saved in Hpins.
    destruct Hpins as (Hmsp & Hmtp & Hms0 & Hms1 & Hms2 & _ & _ & _ & _ & _ & _ & _ & _ & _).
    assert (Hmara : mA !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (AK + 0x12) : mword 64) 4)
      by (rewrite /mA; apply lookup_total_insert).
    assert (Hpc16 : update_vec_dec (add_vec (mA !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (AK + 0x16)).
    { rewrite Hmara. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc16) in "Hpc".
    iPoseProof (kai_16 with "Htext") as "Hi16".
    iPoseProof (kai_1a with "Htext") as "Hi1a".
    iPoseProof (kai_1e with "Htext") as "Hi1e".
    (* +0x16 auipc s1,0x12 *)
    iApply (wp_auipc_s_scfg root_ppn γc E Φ (mword_of_int (AK + 0x16)) (mword_of_int 9 : mword 5) (mword_of_int 0x12 : mword 20)
              mfin (dq:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi16 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (R6 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec (mword_of_int (AK + 0x16) : mword 64) (auipc_off (mword_of_int 0x12 : mword 20)))]> mfin).
    assert (Hs1R6 : R6 !!! Regidx (mword_of_int 9 : mword 5) = add_vec (mword_of_int (AK + 0x16) : mword 64) (auipc_off (mword_of_int 0x12 : mword 20)))
      by (rewrite /R6; apply lookup_total_insert).
    assert (Hpp1a : add_vec_int (mword_of_int (AK + 0x16) : mword 64) 4 = mword_of_int (AK + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a ld s1,-2038(s1) : s1 := *(kmem.freelist) = head *)
    iDestruct "HRres" as (head pages) "[Hflw Hchain]".
    assert (Hldaddr : add_vec (R6 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 0x80a : mword 12)) = fl).
    { rewrite Hs1R6 Hfl. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_ld_s_ram_scfg root_ppn γc E Φ (mword_of_int (AK + 0x1a)) (mword_of_int 9 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 0x80a : mword 12)
              R6 head (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi1a [Hflw] [-]").
    { iEval (rewrite -Hldaddr) in "Hflw". rewrite /word_at. iExact "Hflw". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hflw".
    iEval (rewrite Hldaddr) in "Hflw".
    set (R7 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg head]> R6).
    assert (Hs1R7 : R7 !!! Regidx (mword_of_int 9 : mword 5) = head) by (rewrite /R7; apply lookup_total_insert).
    assert (Hpp1e : add_vec_int (mword_of_int (AK + 0x1a) : mword 64) 4 = mword_of_int (AK + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e c.beqz s1,+0x4c : head=nullp -> empty; else pop *)
    destruct pages as [|p ps].
    - (* ---- EMPTY list: head = nullp, branch taken to +0x4c ---- *)
      iDestruct "Hchain" as %Hhead.
      iApply (wp_cbeqz_taken_s_zca_scfg root_ppn γc E Φ (mword_of_int (AK + 0x1e)) (mword_of_int 23 : mword 8) (Cregidx (mword_of_int 1)) (mword_of_int 9 : mword 5)
                R7 (dq:=DfracOwn 1)
                HN
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs1R7 Hhead; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi1e [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      (* ---- pc = +0x4c ; EMPTY: reclose kmem_res, release, join at +0x40, return null ---- *)
      iAssert (kmem_res fl) with "[Hflw]" as "HRres".
      { iApply (kmem_res_close fl head []). rewrite /word_at.
        iSplitL "Hflw"; [ iExact "Hflw" | iPureIntro; exact Hhead ]. }
      iPoseProof (kai_4c with "Htext") as "Hi4c".
      iPoseProof (kai_50 with "Htext") as "Hi50".
      iPoseProof (kai_54 with "Htext") as "Hi54".
      (* +0x4c auipc a0,0x11 *)
      iApply (wp_auipc_s_scfg root_ppn γc E Φ (mword_of_int (AK + 0x4c)) (mword_of_int 10 : mword 5) (mword_of_int 0x11 : mword 20)
                R7 (dq:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi4c [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (E1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (mword_of_int (AK + 0x4c) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> R7).
      assert (Hpp50 : add_vec_int (mword_of_int (AK + 0x4c) : mword 64) 4 = mword_of_int (AK + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp50) in "Hpc".
      (* +0x50 addi a0,a0,1980  (a0 := &kmem) *)
      iApply (wp_addi4_s_scfg root_ppn γc E Φ (mword_of_int (AK + 0x50)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 0x7bc : mword 12)
                E1 (dq:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi50 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (E2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (E1 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0x7bc : mword 12)))]> E1).
      assert (Ha0kmem2 : E2 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int KernelSyms.kmem).
      { rewrite /E2 lookup_total_insert /E1 lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
      assert (Hpp54 : add_vec_int (mword_of_int (AK + 0x50) : mword 64) 4 = mword_of_int (AK + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp54) in "Hpc".
      (* +0x54 jal ra,release *)
      iApply (wp_jal_gpr_s_zca root_ppn γc E Φ (mword_of_int (AK + 0x54)) (mword_of_int 1 : mword 5) (mword_of_int 0x10e : mword 21)
                E2 1%Qp
                HN ltac:(vm_compute; discriminate)
                ltac:(vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi54 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (E3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (AK + 0x54) : mword 64) 4)]> E2).
      assert (Htgtr2 : add_vec (mword_of_int (AK + 0x54) : mword 64) (sign_extend' 64 (mword_of_int 0x10e : mword 21)) = mword_of_int KernelSyms.release)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtr2) in "Hpc".
      (* register-agreement facts (m := E3) *)
      assert (HE3csp : E3 !!! Regidx csp_rs1 = mA !!! Regidx csp_rs1).
      { rewrite /E3 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /E2 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /E1 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R7 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R6 lookup_total_insert_ne; [| vm_compute; discriminate].
        exact Hmsp. }
      assert (HE3tp : E3 !!! Regidx (mword_of_int 4 : mword 5) = mA !!! Regidx (mword_of_int 4 : mword 5)).
      { rewrite /E3 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /E2 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /E1 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R7 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R6 lookup_total_insert_ne; [| vm_compute; discriminate].
        exact Hmtp. }
      assert (HE3a0 : E3 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int KernelSyms.kmem).
      { rewrite /E3 lookup_total_insert_ne; [| vm_compute; discriminate]. exact Ha0kmem2. }
      assert (HE3ra : E3 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (AK + 0x54) : mword 64) 4)
        by (rewrite /E3; apply lookup_total_insert).
      assert (HlkAkmem : lkA = mword_of_int KernelSyms.kmem).
      { rewrite /lkA /mA lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R4 lookup_total_insert /R3 lookup_total_insert.
        apply bv_eq; vm_compute; reflexivity. }
      assert (Hacpu : add_vec (E3 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 16 : mword 12)) = q_cpu).
      { rewrite HE3a0 /q_cpu HlkAkmem. reflexivity. }
      assert (Hanoff : add_vec (mycpu_ret (E3 !!! Regidx (mword_of_int 4 : mword 5))) (sign_extend' 64 (mword_of_int 120 : mword 12)) = q_noff).
      { rewrite HE3tp /q_noff Ha0fcpu. reflexivity. }
      assert (Haint : add_vec (mycpu_ret (E3 !!! Regidx (mword_of_int 4 : mword 5))) (sign_extend' 64 (mword_of_int 124 : mword 12)) = q_intena).
      { rewrite HE3tp /q_intena Ha0fcpu. reflexivity. }
      iApply (wp_release root_ppn E Φ γ γc bsie lkA (kmem_res fl) E3
                (mycpu_ret (mA !!! Regidx (mword_of_int 4 : mword 5)))
                q_noff_store
                (if eq_vec (sign_extend' 64 qnoff) zero_reg then q_storeval32 else qintena_old)
                (n - 4)%nat
                (dqi:=DfracOwn 1)
                ltac:(lia) HN HNl
                ltac:(rewrite HE3a0 HlkAkmem; apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite HE3tp; apply eq_vec_true_iff; reflexivity)
                Hnoffpos Hintena0
                ltac:(rewrite HE3ra; vm_compute; reflexivity)
                with "Hcfg Htoken Htlbinv Htext Hpc Hfile
                      Hlock Htok HRres [Hcpu] [Hnoff] [Hint] [Hdeep] [-]").
      { iEval (rewrite Hacpu). iExact "Hcpu". }
      { iEval (rewrite Hanoff). iExact "Hnoff". }
      { iEval (rewrite Haint). iExact "Hint". }
      { iEval (rewrite HE3csp HmAsp). iExact "Hdeep". }
      iIntros (mr) "Hcfg Htoken Htlbinv Hpc Hfile %Hpins2 Hcpu2 Hnoff2 Hint2 Hdeep".
      iEval (rewrite HE3csp HmAsp) in "Hdeep".
      assert (Hpc58 : update_vec_dec (add_vec (E3 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (AK + 0x58)).
      { rewrite HE3ra. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hpc58) in "Hpc".
      unfold callee_saved in Hpins2.
      destruct Hpins2 as (Hmrcsp & Hmrtp & Hmrs0 & Hmrs1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
      assert (HE3s1 : E3 !!! Regidx (mword_of_int 9 : mword 5) = nullp).
      { rewrite /E3 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /E2 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /E1 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hs1R7. exact Hhead. }
      (* ---- shared epilogue (+0x40..+0x4a): a0:=s1, restore ra/s0/s1, ret ---- *)
      iPoseProof (kai_58 with "Htext") as "Hi58".
      iPoseProof (kai_40 with "Htext") as "Hi40".
      iPoseProof (kai_42 with "Htext") as "Hi42".
      iPoseProof (kai_44 with "Htext") as "Hi44".
      iPoseProof (kai_46 with "Htext") as "Hi46".
      iPoseProof (kai_48 with "Htext") as "Hi48".
      iPoseProof (kai_4a with "Htext") as "Hi4a".
      (* +0x58 c.j +0x40 *)
      iApply (wp_cj_s_scfg root_ppn γc E Φ (mword_of_int (AK + 0x58))
                (sign_extend' 21 (concat_vec (mword_of_int 2036 : mword 11) ('b"0")))
                mr (dq:=DfracOwn 1)
                HN
                ltac:(vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi58 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Htgtj : add_vec (mword_of_int (AK + 0x58) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2036 : mword 11) ('b"0")))) = mword_of_int (AK + 0x40))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtj) in "Hpc".
      (* +0x40 c.mv a0,s1  (a0 := s1 = nullp) *)
      iApply (wp_cmv_gpr_s_config_scfg root_ppn γc E Φ (mword_of_int (AK + 0x40)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                mr (dq:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi40 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (P41 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (mr !!! Regidx (mword_of_int 9 : mword 5)))]> mr).
      assert (HspP41 : P41 !!! Regidx csp_rs1 = spr).
      { rewrite /P41 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmrcsp HE3csp. exact HmAsp. }
      assert (Hpp42 : add_vec_int (mword_of_int (AK + 0x40) : mword 64) 2 = mword_of_int (AK + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      (* kalloc's own saved ra/s0/s1 sit at [spr]-relative slots *)
      iEval (rewrite HspR1) in "Hr24".
      iEval (rewrite HspR1) in "Hr16".
      iEval (rewrite HspR1) in "Hr8".
      (* +0x42 c.ldsp ra,24(sp) *)
      iApply (wp_cldsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (AK + 0x42)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
                P41 (R1 !!! Regidx (mword_of_int 1 : mword 5))
                (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi42 [Hr24]").
      { iEval (rewrite HspP41). iExact "Hr24". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hr24".
      iEval (rewrite HspP41) in "Hr24".
      set (P42 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 1 : mword 5))]> P41).
      assert (HspP42 : P42 !!! Regidx csp_rs1 = spr) by (rewrite /P42 lookup_total_insert_ne; [ exact HspP41 | vm_compute; discriminate ]).
      assert (Hpp44 : add_vec_int (mword_of_int (AK + 0x42) : mword 64) 2 = mword_of_int (AK + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp44) in "Hpc".
      (* +0x44 c.ldsp s0,16(sp) *)
      iApply (wp_cldsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (AK + 0x44)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
                P42 (R1 !!! Regidx (mword_of_int 8 : mword 5))
                (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi44 [Hr16]").
      { iEval (rewrite HspP42). iExact "Hr16". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hr16".
      iEval (rewrite HspP42) in "Hr16".
      set (P43 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 8 : mword 5))]> P42).
      assert (HspP43 : P43 !!! Regidx csp_rs1 = spr) by (rewrite /P43 lookup_total_insert_ne; [ exact HspP42 | vm_compute; discriminate ]).
      assert (Hpp46 : add_vec_int (mword_of_int (AK + 0x44) : mword 64) 2 = mword_of_int (AK + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp46) in "Hpc".
      (* +0x46 c.ldsp s1,8(sp) *)
      iApply (wp_cldsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (AK + 0x46)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
                P43 (R1 !!! Regidx (mword_of_int 9 : mword 5))
                (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi46 [Hr8]").
      { iEval (rewrite HspP43). iExact "Hr8". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hr8".
      iEval (rewrite HspP43) in "Hr8".
      set (P44 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 9 : mword 5))]> P43).
      assert (HspP44 : P44 !!! Regidx csp_rs1 = spr) by (rewrite /P44 lookup_total_insert_ne; [ exact HspP43 | vm_compute; discriminate ]).
      assert (Hpp48 : add_vec_int (mword_of_int (AK + 0x46) : mword 64) 2 = mword_of_int (AK + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp48) in "Hpc".
      (* +0x48 c.addi16sp sp,32 *)
      iApply (wp_caddi16sp_gpr_s root_ppn γc E Φ (mword_of_int (AK + 0x48)) (mword_of_int 2 : mword 6) P44
                1%Qp HN
                with "Hcfg Htlbinv Hpc Hfile Hi48 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (P45 := <[Regidx csp_rs1 := regval_into_reg (add_vec (P44 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P44).
      assert (Hpp4a : add_vec_int (mword_of_int (AK + 0x48) : mword 64) 2 = mword_of_int (AK + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4a) in "Hpc".
      (* +0x4a c.ret *)
      assert (HP45ra : P45 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
      { rewrite /P45 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P44 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P43 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P42 lookup_total_insert.
        rewrite /R1 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
      assert (HP45a0 : P45 !!! Regidx (mword_of_int 10 : mword 5) = nullp).
      { rewrite /P45 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P44 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P43 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P42 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P41 lookup_total_insert.
        rewrite Hmrs1 HE3s1. apply add_vec_zero_l. }
      iApply (wp_cret_s_zca_scfg root_ppn γc E Φ (mword_of_int (AK + 0x4a)) (mword_of_int 1) P45
                (dq:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate)
                ltac:(rewrite HP45ra; exact Hretm)
                with "Hcfg Htlbinv Hpc Hfile Hi4a [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      iEval (rewrite HP45ra) in "Hpc".
      (* rebundle kalloc's own 4-slot frame with the returned deep tail into
         the FULL [stack_own sp0 n] handed back to the caller. *)
      iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hg4]" as "Htop".
      { rewrite stack_own_slots. cbn [seq].
        iSplitL "Hr24"; [iEval (rewrite -Hb1); iExists _; iExact "Hr24"|].
        iSplitL "Hr16"; [iEval (rewrite -Hb2); iExists _; iExact "Hr16"|].
        iSplitL "Hr8";  [iEval (rewrite -Hb3); iExists _; iExact "Hr8"|].
        iSplitL "Hg4";  [iEval (rewrite -Hb4); iExists _; iExact "Hg4"|].
        done. }
      iEval (rewrite -Hsprstk) in "Hdeep".
      iDestruct (stack_own_split_2 sp0 4 n ltac:(lia) with "[$Htop $Hdeep]") as "Hstk".
      iApply ("Hcont" $! P45 with "Hcfg Htoken Htlbinv Hpc Hfile [] Hstk").
      { rewrite /kalloc_post. iLeft. iPureIntro. exact HP45a0. }
    - (* ---- NONEMPTY: head = p, page_valid p, p <> nullp, fall through to +0x20 ---- *)
      iDestruct "Hchain" as "(-> & %Hpv & Hrun)".
      iDestruct "Hrun" as (nxt) "[Hrun Hchain]".
      iApply (wp_cbeqz_fall_s_config_scfg root_ppn γc E Φ (mword_of_int (AK + 0x1e)) (mword_of_int 23 : mword 8) (Cregidx (mword_of_int 1)) (mword_of_int 9 : mword 5)
                R7 (dq:=DfracOwn 1)
                HN
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs1R7; apply eq_vec_false_iff; intro Hpz;
                      apply (page_valid_ne_null p Hpv); rewrite Hpz; apply bv_eq; vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi1e [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      (* pc = +0x20 ; run_page p nxt = word_at p nxt ∗ page_rest p *)
      iEval (rewrite /run_page) in "Hrun".
      iDestruct "Hrun" as "[Hpnext Hprest]".
      iPoseProof (kai_20 with "Htext") as "Hi20".
      iPoseProof (kai_22 with "Htext") as "Hi22".
      iPoseProof (kai_26 with "Htext") as "Hi26".
      (* +0x20 c.ld a5,0(s1) : a5 := *p = nxt *)
      assert (Hpaddr : add_vec (R7 !!! Regidx (mword_of_int 9 : mword 5))
                 (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")))) = p).
      { replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000"))) : mword 64)
          with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
        rewrite Hs1R7. apply kv_addv_zero. }
      iApply (wp_cld_s_ram_scfg root_ppn γc E Φ (mword_of_int (AK + 0x20)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
                (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")))
                R7 nxt (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi20 [Hpnext] [-]").
      { iEval (rewrite Hpaddr). rewrite /word_at. iExact "Hpnext". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hpnext".
      iEval (rewrite Hpaddr) in "Hpnext".
      set (R8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg nxt]> R7).
      assert (Hpp22 : add_vec_int (mword_of_int (AK + 0x20) : mword 64) 2 = mword_of_int (AK + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp22) in "Hpc".
      (* +0x22 auipc a4,0x11 *)
      iApply (wp_auipc_s_scfg root_ppn γc E Φ (mword_of_int (AK + 0x22)) (mword_of_int 14 : mword 5) (mword_of_int 0x11 : mword 20)
                R8 (dq:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi22 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (R9 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (mword_of_int (AK + 0x22) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> R8).
      assert (Ha4R9 : R9 !!! Regidx (mword_of_int 14 : mword 5) = add_vec (mword_of_int (AK + 0x22) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))
        by (rewrite /R9; apply lookup_total_insert).
      assert (Ha5R9 : R9 !!! Regidx (mword_of_int 15 : mword 5) = nxt).
      { rewrite /R9 lookup_total_insert_ne; [| vm_compute; discriminate]. rewrite /R8; apply lookup_total_insert. }
      assert (Hpp26 : add_vec_int (mword_of_int (AK + 0x22) : mword 64) 4 = mword_of_int (AK + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp26) in "Hpc".
      (* +0x26 sd a5,2046(a4) : kmem.freelist := nxt *)
      assert (Hstaddr : add_vec (R9 !!! Regidx (mword_of_int 14 : mword 5)) (sign_extend' 64 (mword_of_int 0x7fe : mword 12)) = fl).
      { rewrite Ha4R9 Hfl. apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_sd_s_ram_scfg root_ppn γc E Φ (mword_of_int (AK + 0x26)) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 0x7fe : mword 12)
                R9 p (dq:=DfracOwn 1)
                HN
                with "Hcfg Htlbinv Hpc Hfile Hi26 [Hflw] [-]").
      { iEval (rewrite -Hstaddr) in "Hflw". rewrite /word_at. iExact "Hflw". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hflw".
      rewrite Ha5R9. iEval (rewrite Hstaddr) in "Hflw".
      (* reclose kmem_res fl on the new head nxt, and reassemble page_own p *)
      iAssert (kmem_res fl) with "[Hflw Hchain]" as "HRres".
      { iApply (kmem_res_close fl nxt ps). rewrite /word_at. iFrame "Hflw Hchain". }
      iAssert (page_own p) with "[Hpnext Hprest]" as "Hpage".
      { iApply (run_page_page_own p nxt). rewrite /run_page /word_at. iFrame "Hpnext Hprest". }
      assert (Hpp2a : add_vec_int (mword_of_int (AK + 0x26) : mword 64) 4 = mword_of_int (AK + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2a) in "Hpc".
      iPoseProof (kai_2a with "Htext") as "Hi2a".
      iPoseProof (kai_2e with "Htext") as "Hi2e".
      (* +0x2a auipc a0,0x11 *)
      iApply (wp_auipc_s_scfg root_ppn γc E Φ (mword_of_int (AK + 0x2a)) (mword_of_int 10 : mword 5) (mword_of_int 0x11 : mword 20)
                R9 (dq:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi2a [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (R10 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (mword_of_int (AK + 0x2a) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> R9).
      assert (Hpp2e : add_vec_int (mword_of_int (AK + 0x2a) : mword 64) 4 = mword_of_int (AK + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2e) in "Hpc".
      (* +0x2e addi a0,a0,2014  (a0 := &kmem) *)
      iApply (wp_addi4_s_scfg root_ppn γc E Φ (mword_of_int (AK + 0x2e)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 0x7de : mword 12)
                R10 (dq:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi2e [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (R11 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (R10 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0x7de : mword 12)))]> R10).
      assert (Ha0kmem : R11 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int KernelSyms.kmem).
      { rewrite /R11 lookup_total_insert /R10 lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
      assert (Hpp32 : add_vec_int (mword_of_int (AK + 0x2e) : mword 64) 4 = mword_of_int (AK + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp32) in "Hpc".
      iPoseProof (kai_32 with "Htext") as "Hi32".
      (* +0x32 jal ra,release : link ra := +0x36, jump to release's entry *)
      iApply (wp_jal_gpr_s_zca root_ppn γc E Φ (mword_of_int (AK + 0x32)) (mword_of_int 1 : mword 5) (mword_of_int 0x130 : mword 21)
                R11 1%Qp
                HN ltac:(vm_compute; discriminate)
                ltac:(vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi32 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (R12 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (AK + 0x32) : mword 64) 4)]> R11).
      assert (Htgtr : add_vec (mword_of_int (AK + 0x32) : mword 64) (sign_extend' 64 (mword_of_int 0x130 : mword 21)) = mword_of_int KernelSyms.release)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtr) in "Hpc".
      (* pc = release entry, a0 = &kmem, ra = +0x36 ; hold locked γ ∗ kmem_res fl. *)
      (* ---- register-agreement facts across the R6..R12 chain (m := R12) ---- *)
      assert (HR12csp : R12 !!! Regidx csp_rs1 = mA !!! Regidx csp_rs1).
      { rewrite /R12 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R11 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R10 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R9 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R8 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R7 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R6 lookup_total_insert_ne; [| vm_compute; discriminate].
        exact Hmsp. }
      assert (HR12tp : R12 !!! Regidx (mword_of_int 4 : mword 5) = mA !!! Regidx (mword_of_int 4 : mword 5)).
      { rewrite /R12 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R11 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R10 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R9 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R8 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R7 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R6 lookup_total_insert_ne; [| vm_compute; discriminate].
        exact Hmtp. }
      assert (HR12a0 : R12 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int KernelSyms.kmem).
      { rewrite /R12 lookup_total_insert_ne; [| vm_compute; discriminate]. exact Ha0kmem. }
      assert (HR12ra : R12 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (AK + 0x32) : mword 64) 4)
        by (rewrite /R12; apply lookup_total_insert).
      assert (HlkAkmem : lkA = mword_of_int KernelSyms.kmem).
      { rewrite /lkA /mA lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R4 lookup_total_insert /R3 lookup_total_insert.
        apply bv_eq; vm_compute; reflexivity. }
      (* ---- release's window addresses reduce to kalloc's q_* slots ---- *)
      assert (Hacpu : add_vec (R12 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 16 : mword 12)) = q_cpu).
      { rewrite HR12a0 /q_cpu HlkAkmem. reflexivity. }
      assert (Hanoff : add_vec (mycpu_ret (R12 !!! Regidx (mword_of_int 4 : mword 5))) (sign_extend' 64 (mword_of_int 120 : mword 12)) = q_noff).
      { rewrite HR12tp /q_noff Ha0fcpu. reflexivity. }
      assert (Haint : add_vec (mycpu_ret (R12 !!! Regidx (mword_of_int 4 : mword 5))) (sign_extend' 64 (mword_of_int 124 : mword 12)) = q_intena).
      { rewrite HR12tp /q_intena Ha0fcpu. reflexivity. }
      iApply (wp_release root_ppn E Φ γ γc bsie lkA (kmem_res fl) R12
                (mycpu_ret (mA !!! Regidx (mword_of_int 4 : mword 5)))
                q_noff_store
                (if eq_vec (sign_extend' 64 qnoff) zero_reg then q_storeval32 else qintena_old)
                (n - 4)%nat
                (dqi:=DfracOwn 1)
                ltac:(lia) HN HNl
                ltac:(rewrite HR12a0 HlkAkmem; apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite HR12tp; apply eq_vec_true_iff; reflexivity)
                Hnoffpos Hintena0
                ltac:(rewrite HR12ra; vm_compute; reflexivity)
                with "Hcfg Htoken Htlbinv Htext Hpc Hfile
                      Hlock Htok HRres [Hcpu] [Hnoff] [Hint] [Hdeep] [-]").
      { iEval (rewrite Hacpu). iExact "Hcpu". }
      { iEval (rewrite Hanoff). iExact "Hnoff". }
      { iEval (rewrite Haint). iExact "Hint". }
      { iEval (rewrite HR12csp HmAsp). iExact "Hdeep". }
      iIntros (mr) "Hcfg Htoken Htlbinv Hpc Hfile %Hpins2 Hcpu2 Hnoff2 Hint2 Hdeep".
      iEval (rewrite HR12csp HmAsp) in "Hdeep".
      (* pc = ret_tgt = +0x36 ; lock released, still hold [page_own p]. *)
      assert (Hpc36 : update_vec_dec (add_vec (R12 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (AK + 0x36)).
      { rewrite HR12ra. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hpc36) in "Hpc".
      iPoseProof (kai_36 with "Htext") as "Hi36".
      iPoseProof (kai_38 with "Htext") as "Hi38".
      iPoseProof (kai_3a with "Htext") as "Hi3a".
      (* ---- set up the memset(p, 5, 4096) arguments a0/a1/a2 ---- *)
      (* +0x36 c.lui a2,0x1  (a2 := 4096) *)
      unshelve iApply (wp_gpr_write_s_config_scfg root_ppn γc E Φ (mword_of_int (AK + 0x36)) (mword_of_int 12 : mword 5) (mword_of_int 0 : mword 5) (mword_of_int 0 : mword 5)
                (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI))
                (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))
                mr (dq:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate)
                _
                with "Hcfg Htlbinv Hpc Hfile Hi36 [-]").
      { intros s_pc _ _ _.
        rewrite (exec_execute_UTYPE_LUI_gpr (mword_of_int 12) (sign_extend' 20 (mword_of_int 1 : mword 6)) s_pc).
        replace (Z.eqb (uint (mword_of_int 12 : mword 5)) 0) with false by (vm_compute; reflexivity).
        reflexivity. }
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (Mlui := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))]> mr).
      assert (Hpp38 : add_vec_int (mword_of_int (AK + 0x36) : mword 64) 2 = mword_of_int (AK + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp38) in "Hpc".
      (* +0x38 c.li a1,5  (a1 := 5) *)
      unshelve iApply (wp_gpr_write_s_config_scfg root_ppn γc E Φ (mword_of_int (AK + 0x38)) (mword_of_int 11 : mword 5) (mword_of_int 0 : mword 5) (mword_of_int 0 : mword 5)
                (ITYPE (sign_extend' 12 (mword_of_int 5 : mword 6), zreg, Regidx (mword_of_int 11), ADDI))
                (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 5 : mword 6))))
                Mlui (dq:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate)
                _
                with "Hcfg Htlbinv Hpc Hfile Hi38 [-]").
      { intros s_pc _ _ _.
        change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
        rewrite (exec_execute_ITYPE_ADDI_gpr (zero_extend' 5 ('b"00")) (mword_of_int 11) (sign_extend' 12 (mword_of_int 5 : mword 6)) s_pc).
        replace (Z.eqb (uint (mword_of_int 11 : mword 5)) 0) with false by (vm_compute; reflexivity).
        unfold gpr_addi_val.
        replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true by (vm_compute; reflexivity).
        reflexivity. }
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (Mli := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 5 : mword 6))))]> Mlui).
      assert (Hpp3a : add_vec_int (mword_of_int (AK + 0x38) : mword 64) 2 = mword_of_int (AK + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3a) in "Hpc".
      (* +0x3a c.mv a0,s1  (a0 := s1 = p) *)
      iApply (wp_cmv_gpr_s_config_scfg root_ppn γc E Φ (mword_of_int (AK + 0x3a)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                Mli (dq:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi3a [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Hpp3c : add_vec_int (mword_of_int (AK + 0x3a) : mword 64) 2 = mword_of_int (AK + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3c) in "Hpc".
      set (M3a := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (Mli !!! Regidx (mword_of_int 9 : mword 5)))]> Mli).
      unfold callee_saved in Hpins2.
      destruct Hpins2 as (Hmrcsp & Hmrtp & Hmrs0 & Hmrs1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
      assert (HR12s1 : R12 !!! Regidx (mword_of_int 9 : mword 5) = p).
      { rewrite /R12 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R11 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R10 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R9 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R8 lookup_total_insert_ne; [| vm_compute; discriminate].
        exact Hs1R7. }
      iPoseProof (kai_3c with "Htext") as "Hi3c".
      (* +0x3c jal ra,memset : link ra := +0x40, jump to memset entry *)
      iApply (wp_jal_gpr_s_zca root_ppn γc E Φ (mword_of_int (AK + 0x3c)) (mword_of_int 1 : mword 5) (mword_of_int 0x15e : mword 21)
                M3a 1%Qp
                HN ltac:(vm_compute; discriminate)
                ltac:(vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi3c [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (Mms := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (AK + 0x3c) : mword 64) 4)]> M3a).
      assert (Htgtms : add_vec (mword_of_int (AK + 0x3c) : mword 64) (sign_extend' 64 (mword_of_int 0x15e : mword 21)) = mword_of_int KernelSyms.memset)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtms) in "Hpc".
      (* ---- Mms register lookups ---- *)
      assert (HMmsa0 : Mms !!! Regidx (mword_of_int 10 : mword 5) = p).
      { rewrite /Mms lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /M3a lookup_total_insert.
        rewrite /Mli lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Mlui lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmrs1 HR12s1. apply add_vec_zero_l. }
      assert (HMmss1 : Mms !!! Regidx (mword_of_int 9 : mword 5) = p).
      { rewrite /Mms lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /M3a lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Mli lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Mlui lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmrs1. exact HR12s1. }
      assert (HMmsa1 : Mms !!! Regidx (mword_of_int 11 : mword 5) = (mword_of_int 5 : mword 64)).
      { rewrite /Mms lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /M3a lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Mli lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
      assert (HMmsa2 : Mms !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int 4096 : mword 64)).
      { rewrite /Mms lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /M3a lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Mli lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Mlui lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
      assert (HMmsra : Mms !!! Regidx (mword_of_int 1 : mword 5) = mword_of_int (AK + 0x40)).
      { rewrite /Mms lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
      assert (HMmssp : Mms !!! Regidx csp_rs1 = mA !!! Regidx csp_rs1).
      { rewrite /Mms lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /M3a lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Mli lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Mlui lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmrcsp. exact HR12csp. }
      (* +0x3c memset(p, 5, 4096) : fills the page, returns [page_own p] + gpr_file.
         memset's stack frame is the deep tail [stack_own spr (n-4)] (spr = its
         entry sp, via HMmssp/HmAsp), returned intact. *)
      iApply (wp_memset_page root_ppn E Φ Mms (mword_of_int 5 : mword 64) (n - 4)%nat
                γc (dq:=DfracOwn 1)
                ltac:(lia)
                ltac:(rewrite HMmsa0; exact Hpv)
                HMmsa1 HMmsa2
                HN
                ltac:(rewrite HMmsra; vm_compute; reflexivity)
                with "Hcfg Htlbinv Htext Hpc Hfile [Hdeep] [Hpage] [-]").
      { iEval (rewrite HMmssp HmAsp). iExact "Hdeep". }
      { iEval (rewrite HMmsa0). iExact "Hpage". }
      iIntros (mfp) "Hcfg Htlbinv Hpc Hstk Hpage Hfile %Hpinsf".
      iEval (rewrite HMmsa0) in "Hpage".
      iEval (rewrite HMmssp HmAsp) in "Hstk". iRename "Hstk" into "Hdeep".
      unfold callee_saved in Hpinsf.
    destruct Hpinsf as (Hfsp & Hftp & Hfs0 & Hfs1 & Hfs2 & _ & _ & _ & _ & _ & _ & _ & _ & _).
      assert (Hpc40 : update_vec_dec (add_vec (Mms !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (AK + 0x40)).
      { rewrite HMmsra. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hpc40) in "Hpc".
      assert (Hmfsp : mfp !!! Regidx csp_rs1 = spr).
      { rewrite Hfsp HMmssp. exact HmAsp. }
      (* ---- shared epilogue (+0x40..+0x4a), returning a0 = p ---- *)
      iPoseProof (kai_40 with "Htext") as "Hi40".
      iPoseProof (kai_42 with "Htext") as "Hi42".
      iPoseProof (kai_44 with "Htext") as "Hi44".
      iPoseProof (kai_46 with "Htext") as "Hi46".
      iPoseProof (kai_48 with "Htext") as "Hi48".
      iPoseProof (kai_4a with "Htext") as "Hi4a".
      (* +0x40 c.mv a0,s1  (a0 := s1 = p) *)
      iApply (wp_cmv_gpr_s_config_scfg root_ppn γc E Φ (mword_of_int (AK + 0x40)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                mfp (dq:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi40 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (Q41 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (mfp !!! Regidx (mword_of_int 9 : mword 5)))]> mfp).
      assert (HspQ41 : Q41 !!! Regidx csp_rs1 = spr).
      { rewrite /Q41 lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hmfsp. }
      assert (Hpp42 : add_vec_int (mword_of_int (AK + 0x40) : mword 64) 2 = mword_of_int (AK + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      iEval (rewrite HspR1) in "Hr24".
      iEval (rewrite HspR1) in "Hr16".
      iEval (rewrite HspR1) in "Hr8".
      (* +0x42 c.ldsp ra,24(sp) *)
      iApply (wp_cldsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (AK + 0x42)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
                Q41 (R1 !!! Regidx (mword_of_int 1 : mword 5))
                (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi42 [Hr24]").
      { iEval (rewrite HspQ41). iExact "Hr24". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hr24".
      iEval (rewrite HspQ41) in "Hr24".
      set (Q42 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 1 : mword 5))]> Q41).
      assert (HspQ42 : Q42 !!! Regidx csp_rs1 = spr) by (rewrite /Q42 lookup_total_insert_ne; [ exact HspQ41 | vm_compute; discriminate ]).
      assert (Hpp44 : add_vec_int (mword_of_int (AK + 0x42) : mword 64) 2 = mword_of_int (AK + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp44) in "Hpc".
      (* +0x44 c.ldsp s0,16(sp) *)
      iApply (wp_cldsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (AK + 0x44)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
                Q42 (R1 !!! Regidx (mword_of_int 8 : mword 5))
                (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi44 [Hr16]").
      { iEval (rewrite HspQ42). iExact "Hr16". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hr16".
      iEval (rewrite HspQ42) in "Hr16".
      set (Q43 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 8 : mword 5))]> Q42).
      assert (HspQ43 : Q43 !!! Regidx csp_rs1 = spr) by (rewrite /Q43 lookup_total_insert_ne; [ exact HspQ42 | vm_compute; discriminate ]).
      assert (Hpp46 : add_vec_int (mword_of_int (AK + 0x44) : mword 64) 2 = mword_of_int (AK + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp46) in "Hpc".
      (* +0x46 c.ldsp s1,8(sp) *)
      iApply (wp_cldsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (AK + 0x46)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
                Q43 (R1 !!! Regidx (mword_of_int 9 : mword 5))
                (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi46 [Hr8]").
      { iEval (rewrite HspQ43). iExact "Hr8". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hr8".
      iEval (rewrite HspQ43) in "Hr8".
      set (Q44 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 9 : mword 5))]> Q43).
      assert (HspQ44 : Q44 !!! Regidx csp_rs1 = spr) by (rewrite /Q44 lookup_total_insert_ne; [ exact HspQ43 | vm_compute; discriminate ]).
      assert (Hpp48 : add_vec_int (mword_of_int (AK + 0x46) : mword 64) 2 = mword_of_int (AK + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp48) in "Hpc".
      (* +0x48 c.addi16sp sp,32 *)
      iApply (wp_caddi16sp_gpr_s root_ppn γc E Φ (mword_of_int (AK + 0x48)) (mword_of_int 2 : mword 6) Q44
                1%Qp HN
                with "Hcfg Htlbinv Hpc Hfile Hi48 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      set (Q45 := <[Regidx csp_rs1 := regval_into_reg (add_vec (Q44 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q44).
      assert (Hpp4a : add_vec_int (mword_of_int (AK + 0x48) : mword 64) 2 = mword_of_int (AK + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4a) in "Hpc".
      (* +0x4a c.ret *)
      assert (HQ45ra : Q45 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
      { rewrite /Q45 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q44 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q43 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q42 lookup_total_insert.
        rewrite /R1 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
      assert (HQ45a0 : Q45 !!! Regidx (mword_of_int 10 : mword 5) = p).
      { rewrite /Q45 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q44 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q43 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q42 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q41 lookup_total_insert.
        rewrite Hfs1 HMmss1. apply add_vec_zero_l. }
      iApply (wp_cret_s_zca_scfg root_ppn γc E Φ (mword_of_int (AK + 0x4a)) (mword_of_int 1) Q45
                (dq:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate)
                ltac:(rewrite HQ45ra; exact Hretm)
                with "Hcfg Htlbinv Hpc Hfile Hi4a [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      iEval (rewrite HQ45ra) in "Hpc".
      (* rebundle kalloc's own 4-slot frame with the returned deep tail into
         the FULL [stack_own sp0 n] handed back to the caller. *)
      iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hg4]" as "Htop".
      { rewrite stack_own_slots. cbn [seq].
        iSplitL "Hr24"; [iEval (rewrite -Hb1); iExists _; iExact "Hr24"|].
        iSplitL "Hr16"; [iEval (rewrite -Hb2); iExists _; iExact "Hr16"|].
        iSplitL "Hr8";  [iEval (rewrite -Hb3); iExists _; iExact "Hr8"|].
        iSplitL "Hg4";  [iEval (rewrite -Hb4); iExists _; iExact "Hg4"|].
        done. }
      iEval (rewrite -Hsprstk) in "Hdeep".
      iDestruct (stack_own_split_2 sp0 4 n ltac:(lia) with "[$Htop $Hdeep]") as "Hstk".
      iApply ("Hcont" $! Q45 with "Hcfg Htoken Htlbinv Hpc Hfile [Hpage] Hstk").
      { rewrite /kalloc_post HQ45a0. iRight. iFrame "Hpage". iPureIntro. exact Hpv. }
  Qed.

End Kalloc.
