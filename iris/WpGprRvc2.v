(* WpGprRvc2.v -- the SECOND batch of "2-aligned-fetch" ALU WPs (addi / ori /
   lui), ported to the NEW [wp_instr] / [mmode_config] / [gpr_file] layer.

   These are NOT compressed instructions: they are ordinary 32-bit F_Base ops
   (decoded via [ext_decode]) whose PC lands at an address with [addr % 4 = 2]
   (e.g. addi/ori in the start()/timerinit chain).  The new [instr]/[wp_instr]
   layer (InstrBytes.v) only exposes the 4-aligned F_Base fetch, so this file
   builds a 2-aligned analog:
     - [instr_bytes_2 pc w]  : ownership of the 4 bytes of [w] at pc..pc+3,
       together with the (pure, computable) 2-aligned fetch geometry;
     - [instr_2 pc i]        : some 32-bit word decoding to [i] lives at [pc]
       (via [instr_bytes_2]) and [i] is not a landing pad;
     - [wp_instr_2]          : the [instr_2]-driven decode/execute step, stated
       exactly like [wp_instr] but using the 2-aligned fetch.  Because the
       fetched result is still an F_Base [w], the caller's execute obligation is
       identical to the 4-aligned case (nextPC := PC+4, single [execute i]).

   With [wp_instr_2] in hand, [wp_addi_gpr_2] / [wp_ori_gpr_2] / [wp_lui_gpr_2]
   are the [pc_is]/[gpr_file]/[mmode_config] siblings of [wp_addi_gpr]
   (WpGprAddi) / [wp_ori_gpr] (WpGprLogic) / [wp_lui_gpr] (WpGprLui), differing
   ONLY in the fetch alignment (2- vs 4-aligned).  The execute helpers
   [gpr_addi_val] / [exec_execute_ITYPE_ADDI_gpr] / [gpr_ori_val] /
   [exec_execute_ITYPE_ORI_gpr] / [luival] / [exec_execute_UTYPE_LUI_gpr] are
   reused verbatim from those base files. *)
From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpEntry WpGpr WpGprAddi WpGprLogic WpGprLui.
Require Import MinstretInv InstrBytes.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.

Section WpInstr2.
  Context `{!riscvGS Σ}.

  (* [instr_bytes_2 pc w]: the four bytes of the 32-bit word [w] live at
     pc..pc+3 (in duplicable [↦ₘ□]), TOGETHER with the purely-geometric side
     conditions the 2-aligned F_Base fetch reduction needs.  [pc] is 2-aligned
     but NOT 4-aligned (so the fetch reads two halfwords, at pc and pc+2), the
     low 16 bits of [w] are not a compressed opcode, and the byte-split /
     address-offset facts relate the two halfword reads back to [w].  All of
     these are computable for a concrete pc/w, so a client discharges them by
     [vm_compute]. *)
  Definition instr_bytes_2 (pc : mword 64) (w : mword 32) : iProp Σ :=
    (⌜ is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ⌝ ∗
     ⌜ is_aligned_paddr (Physaddr (fetch_pa (add_vec_int pc 2))) 2 = true ⌝ ∗
     ⌜ neq_vec (access_vec_dec pc 0) ('b"0") = false ⌝ ∗
     ⌜ neq_vec (access_vec_dec pc 1) ('b"0") = true ⌝ ∗
     ⌜ is_aligned_vaddr (Virtaddr pc) 4 = false ⌝ ∗
     ⌜ isRVC (subrange_vec_dec w 15 0) = false ⌝ ∗
     ⌜ concat_vec (subrange_vec_dec w 31 16) (subrange_vec_dec w 15 0) = w ⌝ ∗
     ⌜ forall j : nat, (N.of_nat j < 2)%N ->
          pa_add (fetch_pa (add_vec_int pc 2)) j = pa_add (fetch_pa pc) (2 + j) ⌝ ∗
     ⌜ forall j : nat, (N.of_nat j < 2)%N ->
          nth_byte (subrange_vec_dec w 15 0 : mword 16) j = nth_byte w j ⌝ ∗
     ⌜ forall j : nat, (N.of_nat j < 2)%N ->
          nth_byte (subrange_vec_dec w 31 16 : mword 16) j = nth_byte w (2 + j) ⌝ ∗
     [∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ□ nth_byte w j)%I.

  (* fetch_from_instr_bytes_2: the 2-aligned analog of [fetch_from_instr_bytes]
     (InstrBytes.v).  Given the state interpretation, ownership of PC and the
     read-only fetch config CSRs, and [instr_bytes_2 pc w], executing [fetch]
     at [σ] yields [F_Base w], leaving [σ] unchanged.  Delegates to the pure
     2-aligned reduction [exec_fetch_F_Base_2] (WpEntry.v), reading the byte
     footprint out of the state via [mem_valid] and the RAM/MMIO checks out of
     [mem_ram], exactly as the 4-aligned [fetch_from_instr_bytes] does. *)
  Lemma fetch_from_instr_bytes_2
      (σ : mstate) ns κs nt (pc : mword 64) (w : mword 32)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (misa0 : mword 64) {dqp dqc dqa dqh dqm : dfrac} :
    pmp_allows_all pmpcfg0 ->
    pma_allows_all pmar0 ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    state_interp σ ns κs nt -∗
    PC ↦ᵣ pc -∗
    cur_privilege ↦ᵣ{ dqp } Machine -∗
    pmpcfg_n ↦ᵣ{ dqc } pmpcfg0 -∗
    pma_regions ↦ᵣ{ dqa } pmar0 -∗
    htif_tohost_base ↦ᵣ{ dqh } None -∗
    misa ↦ᵣ{ dqm } misa0 -∗
    instr_bytes_2 pc w -∗
    ⌜ exec (fetch tt) σ = Some (F_Base w, σ) ⌝.
  Proof.
    iIntros (Hpmp0 Hpma0 HmisaC) "[Hreg Hmem] Hpc Hpriv Hpmpc Hpma Hhtif Hmisa Hbytes".
    iDestruct "Hbytes" as "(%Halignl & %Halignh & %Hbit0 & %Hbit1 & %Hvalign &
                            %HnotRVC & %Hconcat & %Haddr & %Hlo & %Hhi & Hbytes)".
    iDestruct (reg_valid    with "Hreg Hpc")   as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hpmp : forall i, pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) i)) = OFF)
      by (rewrite Lpmpc; exact Hpmp0).
    assert (Hoff : fetch_pa (add_vec_int pc 2) = pa_add (fetch_pa pc) 2).
    { specialize (Haddr 0%nat ltac:(lia)). rewrite pa_add_0 in Haddr. exact Haddr. }
    (* the four bytes of [w] are in [σ.(mem)] at [fetch_pa pc + j] *)
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
               σ.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte w j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 4)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram (fetch_pa pc)⌝)%I as %Hraml.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (fetch_pa (add_vec_int pc 2))⌝)%I as %Hramh.
    { iDestruct (big_sepL_lookup _ _ 2%nat 2%nat with "Hbytes") as "Hb2".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb2") as %Hr2. rewrite Hoff. iPureIntro. exact Hr2. }
    iPureIntro.
    destruct Hraml as [Hncl Hnsl]. destruct Hramh as [Hnch Hnsh].
    destruct (Hpma0 (fetch_pa pc) 2) as (regl & Hml0 & Hxl & _ & _).
    destruct (Hpma0 (fetch_pa (add_vec_int pc 2)) 2) as (regh & Hmh0 & Hxh & _ & _).
    assert (Hml : matching_pma_region (register_lookup pma_regions σ.(sregs))
              (Physaddr (fetch_pa pc)) 2 = Some regl) by (rewrite Lpma; exact Hml0).
    assert (Hmh : matching_pma_region (register_lookup pma_regions σ.(sregs))
              (Physaddr (fetch_pa (add_vec_int pc 2))) 2 = Some regh) by (rewrite Lpma; exact Hmh0).
    assert (HmisaC' : eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Lmisa; exact HmisaC).
    assert (Hbl : forall j : nat, (N.of_nat j < 2)%N ->
              σ.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte (subrange_vec_dec w 15 0 : mword 16) j)).
    { intros j Hj. rewrite Hlo; [|exact Hj]. apply Hbytesf. lia. }
    assert (Hbh : forall j : nat, (N.of_nat j < 2)%N ->
              σ.(mem) !! (pa_add (fetch_pa (add_vec_int pc 2)) j) = Some (nth_byte (subrange_vec_dec w 31 16 : mword 16) j)).
    { intros j Hj. rewrite Hhi; [|exact Hj]. rewrite (Haddr j Hj). apply Hbytesf. lia. }
    exact (exec_fetch_F_Base_2 pc regl regh w σ Lpc Lpriv Hpmp Hml Hmh Halignl Halignh
             Hxl Hxh
             (within_clint_false (fetch_pa pc) 2 σ Hncl ltac:(lia))
             (within_sig_false  (fetch_pa pc) 2 σ Hnsl ltac:(lia))
             (within_htif_false (fetch_pa pc) 2 σ Lhtif)
             (within_clint_false (fetch_pa (add_vec_int pc 2)) 2 σ Hnch ltac:(lia))
             (within_sig_false  (fetch_pa (add_vec_int pc 2)) 2 σ Hnsh ltac:(lia))
             (within_htif_false (fetch_pa (add_vec_int pc 2)) 2 σ Lhtif)
             Hbl Hbh Hbit0 Hbit1 Hvalign HmisaC' HnotRVC Hconcat).
  Qed.

  (* [instr_2 pc i]: the (32-bit, 2-aligned) instruction at [pc] is [i].  Some
     word [w] lives there (with its byte footprint + 2-aligned geometry, via
     [instr_bytes_2]) whose [ext_decode] is [i], and [i] is not a landing-pad
     instruction (so it takes the ordinary execute path).  This is the 2-aligned
     F_Base analog of [instr pc false i] (InstrBytes.v). *)
  Definition instr_2 (pc : mword 64) (i : instruction) : iProp Σ :=
    (⌜ is_lpad_instruction i = false ⌝ ∗
     ∃ w : mword 32,
       instr_bytes_2 pc w ∗
       (∀ σ ns κs nt, state_interp σ ns κs nt -∗
          ⌜ exec (ext_decode w) σ = Some (i, σ) ⌝))%I.

  (* instr_lift_2: lift [instr_2 pc i] to the pure fetch/decode facts a
     decode/execute WP step consumes (2-aligned F_Base flavour of [instr_lift]). *)
  Lemma instr_lift_2
      (σ : mstate) ns κs nt (pc : mword 64) (i : instruction)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (misa0 : mword 64) {dqp dqc dqa dqh dqm : dfrac} :
    pmp_allows_all pmpcfg0 ->
    pma_allows_all pmar0 ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    state_interp σ ns κs nt -∗
    PC ↦ᵣ pc -∗
    cur_privilege ↦ᵣ{ dqp } Machine -∗
    pmpcfg_n ↦ᵣ{ dqc } pmpcfg0 -∗
    pma_regions ↦ᵣ{ dqa } pmar0 -∗
    htif_tohost_base ↦ᵣ{ dqh } None -∗
    misa ↦ᵣ{ dqm } misa0 -∗
    instr_2 pc i -∗
    ⌜ ∃ w : word,
        exec (fetch tt) σ = Some (F_Base w, σ) /\
        exec (ext_decode w) σ = Some (i, σ) /\
        is_lpad_instruction i = false ⌝.
  Proof.
    iIntros (Hpmp Hpma HmisaC) "Hsi Hpc Hpriv Hpmpc Hpma Hhtif Hmisa Hinstr".
    iDestruct "Hinstr" as "[%Hnlpad Hr]".
    iDestruct "Hr" as (w) "[Hbytes Hdec]".
    iDestruct (fetch_from_instr_bytes_2 σ ns κs nt pc w pmpcfg0 pmar0 misa0
                 Hpmp Hpma HmisaC
                 with "Hsi Hpc Hpriv Hpmpc Hpma Hhtif Hmisa Hbytes") as %Hfetch.
    iDestruct ("Hdec" $! σ ns κs nt with "Hsi") as %Hdec.
    iPureIntro. exists w. split; [exact Hfetch | split; [exact Hdec | exact Hnlpad]].
  Qed.

  (* wp_instr_2: the [instr_2]-driven decode/execute step -- the 2-aligned
     F_Base analog of [wp_instr] (InstrBytes.v).  Because the fetched result is
     an F_Base [w], the run_hart_active path is the base one (nextPC := PC+4,
     single [execute i]); the caller's execute obligation is IDENTICAL to the
     [is_rvc = false] branch of [wp_instr].  Built on
     [wp_exec_step_decode_execute_inv]. *)
  Lemma wp_instr_2 E Φ (pc : mword 64) (i : instruction)
      (pmpcfg0 : type_of_register pmpcfg_n) {dq : dfrac} :
    ↑minstretN ⊆ E →
    pmp_allows_all pmpcfg0 ->
    mmode_config dq -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    instr_2 pc i -∗
    (∀ σ ns κs nt (Hpceq : register_lookup PC σ.(sregs) = pc),
       state_interp σ ns κs nt ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs)) 4))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         state_interp s_exec ns κs nt ∗
         (mmode_config dq -∗
          pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp) "Hmm Hpmpc Hpc Hinstr H".
    iDestruct "Hmm" as "(#Hhw & #Hinv & Hhs & Hpriv & Hmst)".
    iDestruct "Hmst" as (mstatus0) "(Hmstatus & %HmIE & %HMPRV & %HSXL)".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    iApply (wp_exec_step_decode_execute_inv E Φ HN with "Hinv Hhs").
    iIntros (σ ns κs nt) "Hsi".
    iDestruct (instr_lift_2 σ ns κs nt pc i pmpcfg0 pmar0 misa0
                 Hpmp Hpma_all HmisaC
                 with "Hsi Hpc Hpriv Hpmpc Hpma Hhtif Hmisa Hinstr") as %Hlift.
    iDestruct (dispatchInterrupt_none_from_regs σ ns κs nt misa0 mstatus0 HmisaS HmIE
                 with "Hsi Hmisa Hmstatus") as %Hdisp.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σ.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Help_σ.
    iDestruct (reg_valid    with "Hreg Hpc")   as %Lpc.
    iMod ("H" $! σ ns κs nt Lpc with "[$Hreg $Hmem]")
      as (s_exec) "(%Hexec & [Hreg' Hmem'] & Hcont)".
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    iAssert (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
             PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
             WP (Loop : expr riscv_lang) @ E {{ Φ }})%I
      with "[Hcont Hpriv Hmstatus Hpmpc]" as "Hcont'".
    { iIntros "Hhs' Hpc'". iApply ("Hcont" with "[- Hpc' Hpmpc] Hpmpc Hpc'").
      iFrame "Hinv Hhs' Hpriv".
      iSplitR "Hmstatus".
      - iExists misa0, mseccfg0, pmar0, elp0.
        iFrame "Hmisa Hmseccfg Hpma Hhtif Help %".
      - iExists mstatus0. iFrame "Hmstatus".
        iSplitR; [ iPureIntro; exact HmIE | ]. iSplitR; iPureIntro; [ exact HMPRV | exact HSXL ]. }
    destruct Hlift as (w & Hfetch & Hdec & Hnlpad).
    iModIntro. iExists (F_Base w), i, s_exec.
    iSplitR; [iPureIntro; exact Hpriv_σ |].
    iSplitR; [iPureIntro; exact Hdisp |].
    iSplitR; [iPureIntro; exact Hfetch |].
    iSplitR; [iPureIntro; exact Hdec |].
    iSplitR; [iPureIntro; rewrite Help_σ; exact Help_np |].
    iSplitL "".
    { iSplitR; [iPureIntro; exact Hnlpad |]. iPureIntro. exact Hexec. }
    rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont'".
  Qed.

End WpInstr2.

(* ====================================================================== *)
(* The register-GENERIC 2-aligned ALU WPs, on the new layer.               *)
(* ====================================================================== *)
Section WpGprRvc2.
  Context `{!riscvGS Σ}.

  (* addi rd, rs1, imm  (2-aligned fetch) *)
  Lemma wp_addi_gpr_2 E (Φ : mval -> iProp Σ) (pc : mword 64) (rs1 rd : mword 5)
      (imm : mword 12) (m : gmap regidx (mword 64))
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr_2 pc (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_2 E Φ pc (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) pmpcfg0
              HN Hpmp with "Hmm Hpmpc Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int pc 4)) with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    assert (Hav : gpr_addi_val rs1 imm (set_reg σ nextPC (add_vec_int pc 4))
                  = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
    { unfold gpr_addi_val. rewrite Hrv. reflexivity. }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int pc 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      rewrite (exec_execute_ITYPE_ADDI_gpr rs1 rd imm (set_reg σ nextPC (add_vec_int pc 4))).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      rewrite Hav. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (add_vec (m !!! Regidx rs1)
                   (sign_extend' 64 imm)))).(sregs)
             = add_vec_int pc 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hmm' Hpmpc' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* ori rd, rs1, imm  (2-aligned fetch) *)
  Lemma wp_ori_gpr_2 E (Φ : mval -> iProp Σ) (pc : mword 64) (rs1 rd : mword 5)
      (imm : mword 12) (m : gmap regidx (mword 64))
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr_2 pc (ITYPE (imm, Regidx rs1, Regidx rd, ORI)) -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (or_vec (m !!! Regidx rs1) (sign_extend' 64 imm))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_2 E Φ pc (ITYPE (imm, Regidx rs1, Regidx rd, ORI)) pmpcfg0
              HN Hpmp with "Hmm Hpmpc Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int pc 4)) with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    assert (Hav : gpr_ori_val rs1 imm (set_reg σ nextPC (add_vec_int pc 4))
                  = or_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
    { unfold gpr_ori_val. rewrite Hrv. reflexivity. }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (or_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (or_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int pc 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (or_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      rewrite (exec_execute_ITYPE_ORI_gpr rs1 rd imm (set_reg σ nextPC (add_vec_int pc 4))).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      rewrite Hav. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (or_vec (m !!! Regidx rs1)
                   (sign_extend' 64 imm)))).(sregs)
             = add_vec_int pc 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hmm' Hpmpc' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* lui rd, imm  (2-aligned fetch); no source register *)
  Lemma wp_lui_gpr_2 E (Φ : mval -> iProp Σ) (pc : mword 64) (rd : mword 5)
      (imm : mword 20) (m : gmap regidx (mword 64))
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr_2 pc (UTYPE (imm, Regidx rd, LUI)) -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (luival imm)]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_2 E Φ pc (UTYPE (imm, Regidx rd, LUI)) pmpcfg0
              HN Hpmp with "Hmm Hpmpc Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (luival imm))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (luival imm))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int pc 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (luival imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      rewrite (exec_execute_UTYPE_LUI_gpr rd imm (set_reg σ nextPC (add_vec_int pc 4))).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (luival imm))).(sregs)
             = add_vec_int pc 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hmm' Hpmpc' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

End WpGprRvc2.

(* Demonstration: ONE lemma each serves many (rd,rs1) pairs (2-aligned fetch). *)
Section WpGprRvc2Demo.
  Context `{!riscvGS Σ}.
  Definition wp_addi_x5_x6_2 E (Φ : mval -> iProp Σ) (pc : mword 64) (imm : mword 12) :=
    wp_addi_gpr_2 E Φ pc (mword_of_int 6) (mword_of_int 5) imm.   (* addi x5, x6, imm *)
  Definition wp_ori_x5_x6_2 E (Φ : mval -> iProp Σ) (pc : mword 64) (imm : mword 12) :=
    wp_ori_gpr_2 E Φ pc (mword_of_int 6) (mword_of_int 5) imm.    (* ori  x5, x6, imm *)
  Definition wp_lui_x5_2 E (Φ : mval -> iProp Σ) (pc : mword 64) (imm : mword 20) :=
    wp_lui_gpr_2 E Φ pc (mword_of_int 5) imm.                     (* lui  x5, imm *)
  Goal gpr_of_Z (uint (mword_of_int 6 : mword 5)) = x6
    /\ gpr_of_Z (uint (mword_of_int 5 : mword 5)) = x5
    /\ uint (mword_of_int 5 : mword 5) <> 0.
  Proof. repeat split; vm_compute; first [ reflexivity | discriminate ]. Qed.
End WpGprRvc2Demo.
