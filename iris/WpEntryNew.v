(* WpEntryNew.v -- the xv6 kernel [_entry] boot sequence (8 instructions at
   0x80000000) up to and including the [jal] into [start()], proved as ONE WP
   theorem [wp_entry] by composing ONLY the new-style [wp_*_gpr] WP lemmas.

   The eight instructions (ground truth from the ELF dump):
     0x80000000 AUIPC   sp := pc + (imm_auipc<<12)          [4-aligned, F_Base]
     0x80000004 LOAD    sp := mem[sp + sext(imm_ld)]        [4-aligned, F_Base]
     0x80000008 C.LUI   a0 := 0x1000                        [RVC]
     0x8000000a CSRRS   a1 := mhartid                       [2-aligned, F_Base]
     0x8000000e C.ADDI  a1 := a1 + 1                        [RVC]
     0x80000010 MUL     a0 := a0 * a1                       [4-aligned, F_Base]
     0x80000014 C.ADD   sp := sp + a0                       [RVC]
     0x80000016 JAL     ra := pc+4; PC := start (0x80000058) [2-aligned, F_Base]

   All decoded-field / word Definitions (imm_auipc, i_auipc, imm_ld, i_ld,
   imm_clui, rd_clui, csr_csrr, i_rd_csrr, imm_caddi, rsd_caddi, i_mul_*,
   rsd_cadd, rs2_cadd, imm_jal, i_jal, mulop_mul) are REUSED from WpDecode.v /
   WpEntry.v -- not redefined here.

   The chain applies, in order:
     wp_auipc_gpr → wp_ld_gpr → wp_clui_gpr → wp_csrr_mhartid_gpr
       → wp_caddi_gpr → wp_mul_gpr → wp_cadd_gpr → wp_jal_gpr
   threading pc_is / gpr_file / mmode_config / pmpcfg_n through each
   continuation.  The two 2-aligned full instructions (csrr@0xa, jal@0x16)
   now go through the SAME [instr]/[wp_instr]-based WPs as the 4-aligned
   ones: [instr]/[instr_bytes] dispatch on alignment (InstrBytes.v), so
   [wp_csrr_mhartid_gpr] / [wp_jal_gpr] work at any 2-aligned PC. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpDecode WpEntry WpGpr.
Require Import WpAuipc WpGprAuipc WpGprLoad WpGprMul WpGprCsrr WpGprJal WpGprRvc WpGprLui WpGprAddi WpGprLogic.
Require Import MinstretInv InstrBytes.
From iris.base_logic.lib Require Import invariants.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* Moved here from WpDecode.v via the late KernelBoot.v (this file is now their
   only user): the one-shot decodes of _entry's two 32-bit prefix instructions. *)
Lemma decode_auipc s :
  priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode w_auipc) s = Some (UTYPE (imm_auipc, Regidx i_auipc, AUIPC), s).
Proof. intro Hpriv. unfold imm_auipc, i_auipc. decode_any s Hpriv. Qed.
Lemma decode_ld s :
  priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode w_ld) s = Some (LOAD (imm_ld, Regidx i_ld, Regidx i_ld, false, 8), s).
Proof. intro Hpriv. unfold imm_ld, i_ld. decode_any s Hpriv. Qed.

Section WpEntryNew.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* PCs of the eight instructions. *)
  Definition pc_e0 : mword 64 := mword_of_int (KernelSyms._entry).  (* AUIPC  *)
  Definition pc_e1 : mword 64 := mword_of_int (KernelSyms._entry + 0x4).  (* LOAD   *)
  Definition pc_e2 : mword 64 := mword_of_int (KernelSyms._entry + 0x8).  (* C.LUI  *)
  Definition pc_e3 : mword 64 := mword_of_int (KernelSyms._entry + 0xa).  (* CSRRS  *)
  Definition pc_e4 : mword 64 := mword_of_int (KernelSyms._entry + 0xe).  (* C.ADDI *)
  Definition pc_e5 : mword 64 := mword_of_int (KernelSyms._entry + 0x10).  (* MUL    *)
  Definition pc_e6 : mword 64 := mword_of_int (KernelSyms._entry + 0x14).  (* C.ADD  *)
  Definition pc_e7 : mword 64 := mword_of_int (KernelSyms._entry + 0x16).  (* JAL    *)
  Definition pc_start : mword 64 := mword_of_int (KernelSyms.start). (* start() *)

  (* The value AUIPC writes to sp (= pc0 + (imm_auipc<<12) = 0x8000a000). *)
  Definition entry_sp1 : mword 64 := add_vec pc_e0 (auipc_off imm_auipc).

  (* The load effective address: sp (just set by AUIPC) + sext(imm_ld). *)
  Definition entry_ld_ea : mword 64 := add_vec entry_sp1 (sign_extend' 64 imm_ld).

  (* ---- pure address / register arithmetic, all by vm_compute ---- *)
  Lemma pc_e0_e1 : add_vec_int pc_e0 4 = pc_e1.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pc_e1_e2 : add_vec_int pc_e1 4 = pc_e2.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pc_e2_e3 : add_vec_int pc_e2 2 = pc_e3.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pc_e3_e4 : add_vec_int pc_e3 4 = pc_e4.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pc_e4_e5 : add_vec_int pc_e4 2 = pc_e5.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pc_e5_e6 : add_vec_int pc_e5 4 = pc_e6.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pc_e6_e7 : add_vec_int pc_e6 2 = pc_e7.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pc_e7_start : add_vec pc_e7 (sign_extend' 64 imm_jal) = pc_start.
  Proof. vm_compute. reflexivity. Qed.
  Lemma jal_aligned :
    is_aligned_paddr (Physaddr (add_vec pc_e7 (sign_extend' 64 imm_jal))) 4 = true.
  Proof. vm_compute. reflexivity. Qed.

  (* i_ld and i_auipc are the same architectural register (x2/sp). *)
  Lemma reg_ld_auipc : (Regidx i_ld : regidx) = Regidx i_auipc.
  Proof. vm_compute. reflexivity. Qed.

  (* ================================================================= *)
  (*  The kernel TEXT image + per-instruction [instr] constructors.    *)
  (* ================================================================= *)

  (* The image is the dumper's PER-BYTE map [KernelInstrs.kernel_bytes] (byte
     address -> byte value), each byte resident at its physical address.  The
     code points-to facts are DfracDiscarded (`↦ₘ□`), hence persistent and
     duplicable: a fetch window can be extracted while [kernel_text] stays
     intact — no borrow/return. *)
  Definition kernel_text : iProp Σ :=
    ([∗ map] a↦b ∈ KernelInstrs.kernel_bytes, (mword_of_int a : Arch.pa) ↦ₘ□ b)%I.

  Global Instance kernel_text_persistent : Persistent kernel_text.
  Proof. apply _. Qed.

  (* Keep typeclass resolution (Frame/IntoWand/... in iApply/iIntros/iFrame)
     from unfolding [kernel_text] into its 23K-entry [big_sepM] over
     [kernel_bytes] -- otherwise every chunk's [iApply (... with "Htext")]
     pays a huge TC search (cf. the [kernel_bytes] opacity fix).  Unification
     can still see through it where a proof genuinely needs the [big_sepM]. *)
  Global Typeclasses Opaque kernel_text.

  (* THE window extractor: for the instruction word [w] of width [W] bytes at
     byte address [A], its fetch window (in the per-opcode WPs' form,
     [pa_add (fetch_pa pc) j ↦ₘ□ nth_byte w j]) is recovered from [kernel_text]
     by looking up the [W] consecutive bytes [A .. A+W-1].  The byte-equality
     side condition [Hbytes] (each stored byte = the j-th byte of [w]) is
     discharged at the call site by [vm_compute] over the concrete image. *)
  Lemma kernel_window {wd : Z} (A : Z) (w : mword wd) (W : nat) :
    (forall j, (j < W)%nat ->
       KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte w j)) ->
    kernel_text -∗
    ([∗ list] j ∈ seq 0 W, (pa_add (fetch_pa (mword_of_int A)) j) ↦ₘ□ nth_byte w j).
  Proof.
    iIntros (Hbytes) "#Ht". iApply big_sepL_intro. iIntros "!>" (k j Hk).
    apply lookup_seq in Hk. destruct Hk as [-> Hlt]. simpl.
    rewrite pa_add_fetch_mword.
    iApply (big_sepM_lookup _ _ (A + Z.of_nat k)%Z (nth_byte w k) with "Ht").
    apply Hbytes. exact Hlt.
  Qed.

  (* [pa_add] over a literal address, without the [fetch_pa] wrapper (the
     [instr_bytes] footprints are phrased directly over the instruction
     address; virtual = physical in M-mode). *)
  Lemma pa_add_mword (A : Z) (j : nat) :
    pa_add (mword_of_int A : Arch.pa) j = mword_of_int (A + Z.of_nat j).
  Proof. unfold pa_add. apply avi_mword. Qed.

  (* [kernel_window] in [instr_bytes]' address form: the [W]-byte window of
     the word [w] at the literal byte address [A] = [pc], as [pa_add pc j]. *)
  Lemma kernel_window_pc {wd : Z} (A : Z) (w : mword wd) (W : nat) (pc : mword 64) :
    pc = mword_of_int A ->
    (forall j, (j < W)%nat ->
       KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte w j)) ->
    kernel_text -∗
    ([∗ list] j ∈ seq 0 W, (pa_add pc j) ↦ₘ□ nth_byte w j).
  Proof.
    iIntros (-> Hbytes) "#Ht". iApply big_sepL_intro. iIntros "!>" (k j Hk).
    apply lookup_seq in Hk. destruct Hk as [-> Hlt]. simpl.
    rewrite pa_add_mword.
    iApply (big_sepM_lookup _ _ (A + Z.of_nat k)%Z (nth_byte w k) with "Ht").
    apply Hbytes. exact Hlt.
  Qed.

  (* ---- generic [instr_bytes] introduction (base / 4-aligned RVC / RVC) ---- *)
  Lemma instr_bytes_base (pc : mword 64) (w : mword 32) :
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    ([∗ list] j ∈ seq 0 4, (pa_add pc j) ↦ₘ□ nth_byte w j) -∗
    instr_bytes pc (F_Base w).
  Proof.
    iIntros (H2 Hn) "Hw". rewrite /instr_bytes. iEval (cbv beta iota).
    iSplitR; [iPureIntro; exact H2|].
    iSplitR; [iPureIntro; exact Hn|].
    iExact "Hw".
  Qed.

  Lemma instr_bytes_rvc4 (pc : mword 64) (h : mword 16) (w : mword 32) :
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC h = true ->
    subrange_vec_dec w 15 0 = h ->
    ([∗ list] j ∈ seq 0 4, (pa_add pc j) ↦ₘ□ nth_byte w j) -∗
    instr_bytes pc (F_RVC h).
  Proof.
    iIntros (H2 H4 Hr Hs) "Hw". rewrite /instr_bytes. iEval (cbv beta iota).
    rewrite H4.
    iSplitR; [iPureIntro; exact H2|].
    iSplitR; [iPureIntro; exact Hr|].
    iExists w. iSplitR; [iPureIntro; exact Hs|]. iExact "Hw".
  Qed.

  Lemma instr_bytes_rvc2 (pc : mword 64) (h : mword 16) :
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC h = true ->
    ([∗ list] j ∈ seq 0 2, (pa_add pc j) ↦ₘ□ nth_byte h j) -∗
    instr_bytes pc (F_RVC h).
  Proof.
    iIntros (H2 H4 Hr) "Hw". rewrite /instr_bytes. iEval (cbv beta iota).
    rewrite H4.
    iSplitR; [iPureIntro; exact H2|].
    iSplitR; [iPureIntro; exact Hr|].
    iExact "Hw".
  Qed.

  (* The two cross-boundary 4-byte RVC fetch windows (low 16 = the RVC instr,
     high 16 = the next instruction's low 16 bits, as a 4-aligned fetch reads
     them), taken literally from the image. *)
  Definition w_lui4 : mword 32 := mword_of_int 0x25f36505.  (* c.lui | csrr-lo *)
  Definition w_add4 : mword 32 := mword_of_int 0x00ef912a.  (* c.add | jal-lo  *)

  (* ---- the eight [_entry] instructions, each recovered from the image.
     Every constructor is [kernel_text -∗ instr ...]; only MUL's decoder
     additionally needs misa.M = 1, which it reads off [hw_config]. *)

  Lemma entry_instr_auipc :
    kernel_text -∗ instr pc_e0 false (UTYPE (imm_auipc, Regidx i_auipc, AUIPC)).
  Proof.
    assert (Hlpad : is_lpad_instruction (UTYPE (imm_auipc, Regidx i_auipc, AUIPC)) = false)
      by (vm_compute; reflexivity).
    assert (H2al : is_aligned_vaddr (Virtaddr pc_e0) 2 = true) by (vm_compute; reflexivity).
    assert (Hnrvc : isRVC (subrange_vec_dec w_auipc 15 0) = false) by (vm_compute; reflexivity).
    assert (Hbytes : forall j, (j < 4)%nat ->
        KernelInstrs.kernel_bytes !! ((KernelSyms._entry) + Z.of_nat j)%Z = Some (nth_byte w_auipc j)).
    { intros j Hj;
        do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia. }
    iIntros "#Ht". rewrite /instr.
    iSplitR; [iPureIntro; exact Hlpad|].
    iExists (F_Base w_auipc).
    iSplitR; [iPureIntro; reflexivity|].
    iSplitL "".
    - iApply (instr_bytes_base pc_e0 w_auipc H2al Hnrvc).
      iApply (kernel_window_pc (KernelSyms._entry) w_auipc 4 pc_e0 eq_refl Hbytes with "Ht").
    - iIntros (σ) "_". iPureIntro. intros Hpriv _ _.
      exact (decode_auipc σ Hpriv).
  Qed.

  Lemma entry_instr_ld :
    kernel_text -∗ instr pc_e1 false (LOAD (imm_ld, Regidx i_ld, Regidx i_ld, false, 8)).
  Proof.
    assert (Hlpad : is_lpad_instruction (LOAD (imm_ld, Regidx i_ld, Regidx i_ld, false, 8)) = false)
      by (vm_compute; reflexivity).
    assert (H2al : is_aligned_vaddr (Virtaddr pc_e1) 2 = true) by (vm_compute; reflexivity).
    assert (Hnrvc : isRVC (subrange_vec_dec w_ld 15 0) = false) by (vm_compute; reflexivity).
    assert (Hbytes : forall j, (j < 4)%nat ->
        KernelInstrs.kernel_bytes !! ((KernelSyms._entry + 0x4) + Z.of_nat j)%Z = Some (nth_byte w_ld j)).
    { intros j Hj;
        do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia. }
    iIntros "#Ht". rewrite /instr.
    iSplitR; [iPureIntro; exact Hlpad|].
    iExists (F_Base w_ld).
    iSplitR; [iPureIntro; reflexivity|].
    iSplitL "".
    - iApply (instr_bytes_base pc_e1 w_ld H2al Hnrvc).
      iApply (kernel_window_pc (KernelSyms._entry + 0x4) w_ld 4 pc_e1 eq_refl Hbytes with "Ht").
    - iIntros (σ) "_". iPureIntro. intros Hpriv _ _.
      exact (decode_ld σ Hpriv).
  Qed.

  Lemma entry_instr_clui :
    kernel_text -∗ instr pc_e2 true (UTYPE (sign_extend' 20 imm_clui, rd_clui, LUI)).
  Proof.
    assert (Hlpad : is_lpad_instruction (UTYPE (sign_extend' 20 imm_clui, rd_clui, LUI)) = false)
      by (vm_compute; reflexivity).
    assert (H2al : is_aligned_vaddr (Virtaddr pc_e2) 2 = true) by (vm_compute; reflexivity).
    assert (H4al : is_aligned_vaddr (Virtaddr pc_e2) 4 = true) by (vm_compute; reflexivity).
    assert (Hrvc : isRVC h_lui = true) by (vm_compute; reflexivity).
    assert (Hsub : subrange_vec_dec w_lui4 15 0 = h_lui)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hbytes : forall j, (j < 4)%nat ->
        KernelInstrs.kernel_bytes !! ((KernelSyms._entry + 0x8) + Z.of_nat j)%Z = Some (nth_byte w_lui4 j)).
    { intros j Hj;
        do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia. }
    iIntros "#Ht". rewrite /instr.
    iSplitR; [iPureIntro; exact Hlpad|].
    iExists (F_RVC h_lui).
    iSplitR; [iPureIntro; reflexivity|].
    iSplitL "".
    - iApply (instr_bytes_rvc4 pc_e2 h_lui w_lui4 H2al H4al Hrvc Hsub).
      iApply (kernel_window_pc (KernelSyms._entry + 0x8) w_lui4 4 pc_e2 eq_refl Hbytes with "Ht").
    - iIntros (σ) "_". iPureIntro. intros _ HmisaC _. cbn [fetch_is_rvc].
      exists (C_LUI (imm_clui, rd_clui)).
      split; [exact (decode_C_lui σ HmisaC) |].
      split; [vm_compute; reflexivity |].
      intro s. exact (exec_execute_C_LUI imm_clui rd_clui s).
  Qed.

  Lemma entry_instr_csrr :
    kernel_text -∗ instr pc_e3 false (CSRReg (csr_csrr, zreg, Regidx i_rd_csrr, CSRRS)).
  Proof.
    assert (Hlpad : is_lpad_instruction (CSRReg (csr_csrr, zreg, Regidx i_rd_csrr, CSRRS)) = false)
      by (vm_compute; reflexivity).
    assert (H2al : is_aligned_vaddr (Virtaddr pc_e3) 2 = true) by (vm_compute; reflexivity).
    assert (Hnrvc : isRVC (subrange_vec_dec w_csrr 15 0) = false) by (vm_compute; reflexivity).
    assert (Hz : zreg = Regidx i_rs1_csrr) by (vm_compute; reflexivity).
    assert (Hbytes : forall j, (j < 4)%nat ->
        KernelInstrs.kernel_bytes !! ((KernelSyms._entry + 0xa) + Z.of_nat j)%Z = Some (nth_byte w_csrr j)).
    { intros j Hj;
        do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia. }
    iIntros "#Ht". rewrite /instr.
    iSplitR; [iPureIntro; exact Hlpad|].
    iExists (F_Base w_csrr).
    iSplitR; [iPureIntro; reflexivity|].
    iSplitL "".
    - iApply (instr_bytes_base pc_e3 w_csrr H2al Hnrvc).
      iApply (kernel_window_pc (KernelSyms._entry + 0xa) w_csrr 4 pc_e3 eq_refl Hbytes with "Ht").
    - iIntros (σ) "_". iPureIntro. intros Hpriv _ _.
      rewrite Hz. exact (decode_csrr σ Hpriv).
  Qed.

  Lemma entry_instr_caddi :
    kernel_text -∗ instr pc_e4 true (ITYPE (sign_extend' 12 imm_caddi, rsd_caddi, rsd_caddi, ADDI)).
  Proof.
    assert (Hlpad : is_lpad_instruction (ITYPE (sign_extend' 12 imm_caddi, rsd_caddi, rsd_caddi, ADDI)) = false)
      by (vm_compute; reflexivity).
    assert (H2al : is_aligned_vaddr (Virtaddr pc_e4) 2 = true) by (vm_compute; reflexivity).
    assert (H4al : is_aligned_vaddr (Virtaddr pc_e4) 4 = false) by (vm_compute; reflexivity).
    assert (Hrvc : isRVC h_addi = true) by (vm_compute; reflexivity).
    assert (Hbytes : forall j, (j < 2)%nat ->
        KernelInstrs.kernel_bytes !! ((KernelSyms._entry + 0xe) + Z.of_nat j)%Z = Some (nth_byte h_addi j)).
    { intros j Hj;
        do 2 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia. }
    iIntros "#Ht". rewrite /instr.
    iSplitR; [iPureIntro; exact Hlpad|].
    iExists (F_RVC h_addi).
    iSplitR; [iPureIntro; reflexivity|].
    iSplitL "".
    - iApply (instr_bytes_rvc2 pc_e4 h_addi H2al H4al Hrvc).
      iApply (kernel_window_pc (KernelSyms._entry + 0xe) h_addi 2 pc_e4 eq_refl Hbytes with "Ht").
    - iIntros (σ) "_". iPureIntro. intros _ HmisaC _. cbn [fetch_is_rvc].
      exists (C_ADDI (imm_caddi, rsd_caddi)).
      split; [exact (decode_C_ADDI σ HmisaC) |].
      split; [vm_compute; reflexivity |].
      intro s. exact (exec_execute_C_ADDI imm_caddi rsd_caddi s).
  Qed.

  Lemma entry_instr_mul :
    hw_config -∗ kernel_text -∗
    instr pc_e5 false (MUL (Regidx i_mul_rs2, Regidx i_mul_rs1, Regidx i_mul_rd, mulop_mul)).
  Proof.
    assert (Hlpad : is_lpad_instruction
        (MUL (Regidx i_mul_rs2, Regidx i_mul_rs1, Regidx i_mul_rd, mulop_mul)) = false)
      by (vm_compute; reflexivity).
    assert (H2al : is_aligned_vaddr (Virtaddr pc_e5) 2 = true) by (vm_compute; reflexivity).
    assert (Hnrvc : isRVC (subrange_vec_dec w_mul 15 0) = false) by (vm_compute; reflexivity).
    assert (Hbytes : forall j, (j < 4)%nat ->
        KernelInstrs.kernel_bytes !! ((KernelSyms._entry + 0x10) + Z.of_nat j)%Z = Some (nth_byte w_mul j)).
    { intros j Hj;
        do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia. }
    iIntros "#Hhw #Ht".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & _ & %HmisaS & %HmisaC0 & %HmisaU & %HmisaM & _)".
    rewrite /instr.
    iSplitR; [iPureIntro; exact Hlpad|].
    iExists (F_Base w_mul).
    iSplitR; [iPureIntro; reflexivity|].
    iSplitL "".
    - iApply (instr_bytes_base pc_e5 w_mul H2al Hnrvc).
      iApply (kernel_window_pc (KernelSyms._entry + 0x10) w_mul 4 pc_e5 eq_refl Hbytes with "Ht").
    - iIntros (σ) "Hsi".
      iDestruct (state_interp_reg_dq σ misa DfracDiscarded misa0
                   with "Hsi Hmisa") as %Lmisa.
      iPureIntro. intros Hpriv _ _.
      assert (HmisaMs : eq_vec (_get_Misa_M (register_lookup misa σ.(sregs))) ('b"1") = true)
        by (rewrite Lmisa; exact HmisaM).
      exact (decode_mul σ Hpriv HmisaMs).
  Qed.

  Lemma entry_instr_cadd :
    kernel_text -∗ instr pc_e6 true (RTYPE (rs2_cadd, rsd_cadd, rsd_cadd, ADD)).
  Proof.
    assert (Hlpad : is_lpad_instruction (RTYPE (rs2_cadd, rsd_cadd, rsd_cadd, ADD)) = false)
      by (vm_compute; reflexivity).
    assert (H2al : is_aligned_vaddr (Virtaddr pc_e6) 2 = true) by (vm_compute; reflexivity).
    assert (H4al : is_aligned_vaddr (Virtaddr pc_e6) 4 = true) by (vm_compute; reflexivity).
    assert (Hrvc : isRVC h_add = true) by (vm_compute; reflexivity).
    assert (Hsub : subrange_vec_dec w_add4 15 0 = h_add)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hbytes : forall j, (j < 4)%nat ->
        KernelInstrs.kernel_bytes !! ((KernelSyms._entry + 0x14) + Z.of_nat j)%Z = Some (nth_byte w_add4 j)).
    { intros j Hj;
        do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia. }
    iIntros "#Ht". rewrite /instr.
    iSplitR; [iPureIntro; exact Hlpad|].
    iExists (F_RVC h_add).
    iSplitR; [iPureIntro; reflexivity|].
    iSplitL "".
    - iApply (instr_bytes_rvc4 pc_e6 h_add w_add4 H2al H4al Hrvc Hsub).
      iApply (kernel_window_pc (KernelSyms._entry + 0x14) w_add4 4 pc_e6 eq_refl Hbytes with "Ht").
    - iIntros (σ) "_". iPureIntro. intros _ HmisaC _. cbn [fetch_is_rvc].
      exists (C_ADD (rsd_cadd, rs2_cadd)).
      split; [exact (decode_C_ADD σ HmisaC) |].
      split; [vm_compute; reflexivity |].
      intro s. exact (exec_execute_C_ADD rsd_cadd rs2_cadd s).
  Qed.

  Lemma entry_instr_jal :
    kernel_text -∗ instr pc_e7 false (JAL (imm_jal, Regidx i_jal)).
  Proof.
    assert (Hlpad : is_lpad_instruction (JAL (imm_jal, Regidx i_jal)) = false)
      by (vm_compute; reflexivity).
    assert (H2al : is_aligned_vaddr (Virtaddr pc_e7) 2 = true) by (vm_compute; reflexivity).
    assert (Hnrvc : isRVC (subrange_vec_dec w_jal 15 0) = false) by (vm_compute; reflexivity).
    assert (Hbytes : forall j, (j < 4)%nat ->
        KernelInstrs.kernel_bytes !! ((KernelSyms._entry + 0x16) + Z.of_nat j)%Z = Some (nth_byte w_jal j)).
    { intros j Hj;
        do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia. }
    iIntros "#Ht". rewrite /instr.
    iSplitR; [iPureIntro; exact Hlpad|].
    iExists (F_Base w_jal).
    iSplitR; [iPureIntro; reflexivity|].
    iSplitL "".
    - iApply (instr_bytes_base pc_e7 w_jal H2al Hnrvc).
      iApply (kernel_window_pc (KernelSyms._entry + 0x16) w_jal 4 pc_e7 eq_refl Hbytes with "Ht").
    - iIntros (σ) "_". iPureIntro. intros Hpriv _ _.
      exact (decode_jal σ Hpriv).
  Qed.

  (* The final gpr_file after the eight writes, in terms of the abstract initial
     map [m], the loaded stack pointer [v_stack0], and the abstract [mhartid_in].
     Each nested insert is exactly the continuation map handed back by the
     corresponding WP.  (a1's C.ADDI and a0's MUL and sp's C.ADD read their
     inputs off the threaded map, so their written values are left as symbolic
     [!!!] reads over the running map -- exactly what the WPs produce.) *)
  Definition m_auipc (m : gmap regidx (mword 64)) : gmap regidx (mword 64) :=
    <[Regidx i_auipc := regval_into_reg entry_sp1]> m.
  Definition m_ld (m : gmap regidx (mword 64)) (v_stack0 : bv 64)
      : gmap regidx (mword 64) :=
    <[Regidx i_ld := regval_into_reg v_stack0]> (m_auipc m).
  Definition m_clui (m : gmap regidx (mword 64)) (v_stack0 : bv 64)
      : gmap regidx (mword 64) :=
    <[Regidx (regidx_bits rd_clui) :=
        regval_into_reg (WpGprLui.luival (sign_extend' 20 imm_clui))]> (m_ld m v_stack0).
  Definition m_csrr (m : gmap regidx (mword 64)) (v_stack0 : bv 64)
      (mhartid_in : mword 64) : gmap regidx (mword 64) :=
    <[Regidx i_rd_csrr := regval_into_reg mhartid_in]> (m_clui m v_stack0).
  Definition m_caddi (m : gmap regidx (mword 64)) (v_stack0 : bv 64)
      (mhartid_in : mword 64) : gmap regidx (mword 64) :=
    <[Regidx (regidx_bits rsd_caddi) :=
        regval_into_reg
          (add_vec (m_csrr m v_stack0 mhartid_in !!! Regidx (regidx_bits rsd_caddi))
             (sign_extend' 64 imm_caddi))]> (m_csrr m v_stack0 mhartid_in).
  Definition m_mul (m : gmap regidx (mword 64)) (v_stack0 : bv 64)
      (mhartid_in : mword 64) : gmap regidx (mword 64) :=
    <[Regidx i_mul_rd :=
        regval_into_reg
          (mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
             (mulop_mul.(mul_op_signed_rs2))
             (m_caddi m v_stack0 mhartid_in !!! Regidx i_mul_rs1)
             (m_caddi m v_stack0 mhartid_in !!! Regidx i_mul_rs2)
             (mulop_mul.(mul_op_result_part)))]> (m_caddi m v_stack0 mhartid_in).
  Definition m_cadd (m : gmap regidx (mword 64)) (v_stack0 : bv 64)
      (mhartid_in : mword 64) : gmap regidx (mword 64) :=
    <[Regidx (regidx_bits rsd_cadd) :=
        regval_into_reg
          (add_vec (m_mul m v_stack0 mhartid_in !!! Regidx (regidx_bits rsd_cadd))
             (m_mul m v_stack0 mhartid_in !!! Regidx (regidx_bits rs2_cadd)))]>
      (m_mul m v_stack0 mhartid_in).
  Definition m_jal (m : gmap regidx (mword 64)) (v_stack0 : bv 64)
      (mhartid_in : mword 64) : gmap regidx (mword 64) :=
    <[Regidx i_jal := regval_into_reg (add_vec_int pc_e7 4)]>
      (m_cadd m v_stack0 mhartid_in).

  (* ================================================================= *)
  (*  THE THEOREM: the whole [_entry] boot chain, one Qed.             *)
  (* ================================================================= *)
  Lemma wp_entry E (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64)) (v_stack0 : bv 64) (mhartid_in : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    (* [pmp_all_off] (not just unlocked): the chain contains an 8-byte load
       (`ld sp, ..`), whose PMP check needs the all-OFF form -- see the note
       on [pmp_all_off] in RiscvFetchExec.v.  It holds of the boot-time
       all-zero pmpcfg by vm_compute. *)
    pmp_all_off pmpcfg0 ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc_e0 -∗
    gpr_file m -∗
    mhartid ↦ᵣ mhartid_in -∗
    (* the stack0 pointer word sitting at the load effective address *)
    entry_ld_ea ↦₈{ dq } v_stack0 -∗
    (* the kernel text image: the eight decoded [instr] facts are derived from
       it inside the proof via the [entry_instr_*] constructors ([kernel_text]
       is persistent, so one copy feeds all eight) *)
    kernel_text -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is pc_start -∗
      gpr_file (m_jal m v_stack0 mhartid_in) -∗
      mhartid ↦ᵣ mhartid_in -∗
      entry_ld_ea ↦₈{ dq } v_stack0 -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp)
      "Hmm Hpmpc Hpc Hfile Hmh Hbytes #Htext Hcont".
    pose proof (pmp_all_off_allows_all _ Hpmp) as HpmpU.
    (* derive the eight [instr] facts off the (persistent) text image; MUL's
       decoder additionally needs misa.M = 1, read off [mmode_config]'s
       persistent [hw_config], which is split out and put back. *)
    iDestruct "Hmm" as "(#Hhw & Hmmrest)".
    iPoseProof (entry_instr_auipc with "Htext") as "Hi0".
    iPoseProof (entry_instr_ld    with "Htext") as "Hi1".
    iPoseProof (entry_instr_clui  with "Htext") as "Hi2".
    iPoseProof (entry_instr_csrr  with "Htext") as "Hi3".
    iPoseProof (entry_instr_caddi with "Htext") as "Hi4".
    iPoseProof (entry_instr_mul   with "Hhw Htext") as "Hi5".
    iPoseProof (entry_instr_cadd  with "Htext") as "Hi6".
    iPoseProof (entry_instr_jal   with "Htext") as "Hi7".
    iAssert (mmode_config (DfracOwn 1)) with "[Hmmrest]" as "Hmm".
    { rewrite /mmode_config. iFrame "Hhw". iExact "Hmmrest". }
    (* register-nonzero side conditions (all targets are sp/a0/a1/ra <> x0) *)
    assert (Hrd0 : uint i_auipc <> 0) by (vm_compute; discriminate).
    assert (Hrd1 : uint i_ld <> 0) by (vm_compute; discriminate).
    assert (Hrd2 : uint (regidx_bits rd_clui) <> 0) by (vm_compute; discriminate).
    assert (Hrd3 : uint i_rd_csrr <> 0) by (vm_compute; discriminate).
    assert (Hrd4 : uint (regidx_bits rsd_caddi) <> 0) by (vm_compute; discriminate).
    assert (Hrd5 : uint i_mul_rd <> 0) by (vm_compute; discriminate).
    assert (Hrd6 : uint (regidx_bits rsd_cadd) <> 0) by (vm_compute; discriminate).
    assert (Hrd7 : uint i_jal <> 0) by (vm_compute; discriminate).

    (* ---- 1. AUIPC @ pc_e0: sp := entry_sp1 ---- *)
    iApply (wp_auipc_gpr E Φ pc_e0 i_auipc imm_auipc m pmpcfg0 1%Qp HN HpmpU Hrd0
              with "Hmm Hpmpc Hpc Hfile Hi0").
    iEval (rewrite pc_e0_e1).
    iIntros "Hmm Hpmpc Hpc Hfile".
    (* fold the AUIPC continuation map into [m_auipc m] *)
    iEval (change (<[Regidx i_auipc := regval_into_reg (add_vec pc_e0 (auipc_off imm_auipc))]> m)
             with (m_auipc m)) in "Hfile".

    (* ---- 2. LOAD @ pc_e1: sp := mem[sp + sext(imm_ld)] = v_stack0 ---- *)
    (* the load reads rs1 = i_ld = i_auipc = sp, whose value in [m_auipc m] is
       entry_sp1, so the effective address is entry_ld_ea. *)
    assert (Hea : add_vec (m_auipc m !!! Regidx i_ld) (sign_extend' 64 imm_ld)
                  = entry_ld_ea).
    { unfold entry_ld_ea, entry_sp1, m_auipc.
      rewrite reg_ld_auipc.
      rewrite lookup_total_insert. reflexivity. }
    iApply (wp_ld_gpr E Φ pc_e1 false i_ld i_ld imm_ld (m_auipc m) v_stack0 pmpcfg0 1%Qp
              (dq := dq) HN Hpmp Hrd1 with "Hmm Hpmpc Hpc Hfile Hi1 [Hbytes]").
    { rewrite Hea. iExact "Hbytes". }
    iEval (rewrite pc_e1_e2).
    iIntros "Hmm Hpmpc Hpc Hfile Hbytes".
    iEval (rewrite Hea) in "Hbytes".
    iEval (change (<[Regidx i_ld := regval_into_reg v_stack0]> (m_auipc m))
             with (m_ld m v_stack0)) in "Hfile".

    (* ---- 3. C.LUI @ pc_e2: a0 := 0x1000 ---- *)
    iApply (wp_lui_gpr E Φ pc_e2 true (regidx_bits rd_clui) (sign_extend' 20 imm_clui)
              (m_ld m v_stack0) pmpcfg0 1%Qp HN HpmpU Hrd2
              with "Hmm Hpmpc Hpc Hfile Hi2").
    iEval (change (if true then 2%Z else 4%Z) with 2%Z).
    iEval (rewrite pc_e2_e3).
    iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx (regidx_bits rd_clui) :=
                      regval_into_reg (WpGprLui.luival (sign_extend' 20 imm_clui))]> (m_ld m v_stack0))
             with (m_clui m v_stack0)) in "Hfile".

    (* ---- 4. CSRRS @ pc_e3 (2-aligned): a1 := mhartid ---- *)
    iApply (wp_csrr_mhartid_gpr E Φ pc_e3 i_rd_csrr mhartid_in
              (m_clui m v_stack0) pmpcfg0 1%Qp HN HpmpU Hrd3
              with "Hmm Hpmpc Hpc Hfile Hmh Hi3").
    iEval (rewrite pc_e3_e4).
    iIntros "Hmm Hpmpc Hpc Hfile Hmh".
    iEval (change (<[Regidx i_rd_csrr := regval_into_reg mhartid_in]> (m_clui m v_stack0))
             with (m_csrr m v_stack0 mhartid_in)) in "Hfile".

    (* ---- 5. C.ADDI @ pc_e4: a1 := a1 + 1 ---- *)
    iApply (wp_addi_gpr E Φ pc_e4 true (regidx_bits rsd_caddi) (regidx_bits rsd_caddi)
              (sign_extend' 12 imm_caddi)
              (m_csrr m v_stack0 mhartid_in) pmpcfg0 1%Qp HN HpmpU Hrd4
              with "Hmm Hpmpc Hpc Hfile Hi4").
    iEval (change (if true then 2%Z else 4%Z) with 2%Z).
    iEval (rewrite pc_e4_e5).
    iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (rewrite sext6_12_64) in "Hfile".
    iEval (change (<[Regidx (regidx_bits rsd_caddi) :=
             regval_into_reg
               (add_vec (m_csrr m v_stack0 mhartid_in !!! Regidx (regidx_bits rsd_caddi))
                  (sign_extend' 64 imm_caddi))]> (m_csrr m v_stack0 mhartid_in))
             with (m_caddi m v_stack0 mhartid_in)) in "Hfile".

    (* ---- 6. MUL @ pc_e5: a0 := a0 * a1 ---- *)
    iApply (wp_mul_gpr E Φ pc_e5 i_mul_rs2 i_mul_rs1 i_mul_rd
              (m_caddi m v_stack0 mhartid_in) pmpcfg0 HN HpmpU Hrd5
              with "Hmm Hpmpc Hpc Hfile Hi5").
    iEval (rewrite pc_e5_e6).
    iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx i_mul_rd :=
             regval_into_reg
               (mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
                  (mulop_mul.(mul_op_signed_rs2))
                  (m_caddi m v_stack0 mhartid_in !!! Regidx i_mul_rs1)
                  (m_caddi m v_stack0 mhartid_in !!! Regidx i_mul_rs2)
                  (mulop_mul.(mul_op_result_part)))]> (m_caddi m v_stack0 mhartid_in))
             with (m_mul m v_stack0 mhartid_in)) in "Hfile".

    (* ---- 7. C.ADD @ pc_e6: sp := sp + a0 ---- *)
    iApply (wp_add_gpr E Φ pc_e6 true (regidx_bits rs2_cadd) (regidx_bits rsd_cadd)
              (regidx_bits rsd_cadd)
              (m_mul m v_stack0 mhartid_in) pmpcfg0 1%Qp HN HpmpU Hrd6
              with "Hmm Hpmpc Hpc Hfile Hi6").
    iEval (change (if true then 2%Z else 4%Z) with 2%Z).
    iEval (rewrite pc_e6_e7).
    iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx (regidx_bits rsd_cadd) :=
             regval_into_reg
               (add_vec (m_mul m v_stack0 mhartid_in !!! Regidx (regidx_bits rsd_cadd))
                  (m_mul m v_stack0 mhartid_in !!! Regidx (regidx_bits rs2_cadd)))]>
             (m_mul m v_stack0 mhartid_in))
             with (m_cadd m v_stack0 mhartid_in)) in "Hfile".

    (* ---- 8. JAL @ pc_e7 (2-aligned): ra := pc+4; PC := start ---- *)
    iApply (wp_jal_gpr E Φ pc_e7 i_jal imm_jal
              (m_cadd m v_stack0 mhartid_in) pmpcfg0 1%Qp HN HpmpU Hrd7 jal_aligned
              with "Hmm Hpmpc Hpc Hfile Hi7").
    iEval (rewrite pc_e7_start).
    iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx i_jal := regval_into_reg (add_vec_int pc_e7 4)]>
             (m_cadd m v_stack0 mhartid_in))
             with (m_jal m v_stack0 mhartid_in)) in "Hfile".

    (* hand everything to the caller's continuation *)
    iApply ("Hcont" with "Hmm Hpmpc Hpc Hfile Hmh Hbytes").
  Qed.

End WpEntryNew.
