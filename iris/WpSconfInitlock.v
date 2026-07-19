(* WpSconfInitlock.v -- initlock over the SIE-agnostic sconf world.

   The sconf mirror of [wp_initlock_r] (WpInitlock.v): a straight-line
   function with NO locking (no push_off/acquire), so it does NOT thread
   [intr_count] at all.  It owns the spinlock's three struct fields
   (locked : 4B @ +0, name : 8B @ +8, cpu : 8B @ +16) as raw memory and
   returns them initialised.  sp moves only at the prologue/epilogue
   (2-slot frame), traded through [sie_cap_move_down]/[sie_cap_move_up] 2.

   The [locked := 0] store is a plain 4-byte zero store over a PLAINLY-
   owned word (the lock is not yet an invariant) -- for that we build the
   local leaf [wp_sw_zero_s_sconf], the width-4 sibling of
   [wp_sd_zero_s_sconf] (WpSconfMem.v).  The decode facts + [initlock_sp_
   cancel] are reused from the smode file WpInitlock.v, exactly as
   WpSconfKfree reuses WpKfree's [kfi_*]. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import WpLoad.
Require Import WpGpr InstrBytes WpMmodeLeafBase.
Require Import SmodePte PtTreeAdue.
Require Import SmodeCore WpSmodeGpr.
Require Import KptTree SmodeCorePt WpSmodePtLeaves WpSmodePtMem.
Require Import StackOwn CalleeSaved.
Require Import KernelText.
Require Import IntrDefs WpIntrInv WpSmodeIntr.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpInitlock.
Require Import SRegime.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.
Import Defs.

(* helper copies (Local in WpSconfMem.v / WpSmodePtMem.v). *)
Local Lemma avi0_mul4 (a : mword 64) : add_vec_int a (0 * 4) = a.
Proof. change (0 * 4)%Z with 0%Z. apply avi0. Qed.

Section WpSconfInitlock.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  Local Lemma upd_window_bw {k : N} (mm : _) (pa : Arch.pa) (vnew vold : bv k)
      (l : list nat) :
    gen_heap_interp (hG:=riscv_memGS) mm -∗ ([∗ list] j ∈ l, (pa_add pa j) ↦ₘ nth_byte vold j) ==∗
    gen_heap_interp (hG:=riscv_memGS) (foldr (fun j acc => <[pa_add pa j := nth_byte vnew j]> acc) mm l)
      ∗ ([∗ list] j ∈ l, (pa_add pa j) ↦ₘ nth_byte vnew j).
  Proof.
    iInduction l as [|x xs IH] "IH"; simpl.
    - iIntros "Hm _". iModIntro. iFrame.
    - iIntros "Hm [Ha Hrest]".
      iMod ("IH" with "Hm Hrest") as "[Hm Hrest]".
      iMod (mem_update _ (pa_add pa x) (nth_byte vold x) (nth_byte vnew x) with "Hm Ha") as "[Hm Ha]".
      iModIntro. iFrame "Ha Hrest Hm".
  Qed.

  Local Lemma upd_window_4 (mm : _) (pa : Arch.pa) (vnew vold : bv 32) :
    gen_heap_interp (hG:=riscv_memGS) mm -∗ ([∗ list] j ∈ seq 0 4, (pa_add pa j) ↦ₘ nth_byte vold j) ==∗
    gen_heap_interp (hG:=riscv_memGS) (write_bytes mm pa 4 vnew)
      ∗ ([∗ list] j ∈ seq 0 4, (pa_add pa j) ↦ₘ nth_byte vnew j).
  Proof. unfold write_bytes. change (N.to_nat 4) with 4%nat. apply upd_window_bw. Qed.

  (* ================================================================== *)
  (* the plain 4-byte zero store [sw zero, imm(rs1)] over a PLAINLY-     *)
  (* owned word.  Width-4 sibling of [wp_sd_zero_s_sconf]; cloned from   *)
  (* the width-4 store [wp_sw_s_sconf] with rs2 hardwired to x0 and the  *)
  (* stored value pinned to the model's [mword_of_int 0].                *)
  (* ================================================================== *)
  Local Lemma wp_sw_zero_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 32) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let storeval := (mword_of_int 0 : mword 32) in
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4)) -∗
    pa ↦₄ vold -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      sie_cap γ root_ppn m -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      pa ↦₄ storeval -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa storeval.
    iIntros "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr (Virtaddr pa) 4 = true) by exact Hpalign4.
    iApply (wp_instr_s_sconf γ root_ppn m Φ pc false
              (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4))
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Htlbinv [%Hdom Hfmap] Hnpc Hsi".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 4) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct "Htlbinv" as (satp1 tlbvec1 t1)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hpmawimpl & Ht & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc0 & Hpa0 & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hpc0")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpa0")  as %Lpmpaddr.
    iAssert (tlb_inv_pt root_ppn) with "[Hsatp Htlb Ht Hpc0 Hpa0]" as "Htlbinv".
    { iExists satp1, tlbvec1, t1. iFrame "Hsatp Htlb Ht".
      iSplit; [iPureIntro; exact Hmode |].
      iSplit; [iPureIntro; exact Hasid |].
      iSplit; [iPureIntro; exact Hppn |].
      iSplit; [iPureIntro; exact Htlbok |].
      iSplit; [iPureIntro; exact Hspec |].
      iSplit; [iPureIntro; exact Hpmawimpl |].
      iExists pmpcfg0, pmpaddr00. iFrame "Hpc0 Hpa0". iPureIntro. tauto. }
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hrampa3.
    { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb3") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 4 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 3 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 3) with 3. lia. }
      pose proof (uint_pa_add pa 3 Hnw) as Heq.
      destruct Hrampa3 as [_ Hhi3]. rewrite Heq in Hhi3. change (Z.of_nat 3) with 3 in Hhi3.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 4 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp1)
      by (unfold s_pc; tmig; exact Lsatp).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00)
      by (unfold s_pc; tmig; exact Lpmpaddr).
    assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C)
      by (rewrite Lmisa_pc; exact Hmisa_val0).
    assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S)
      by (rewrite Lmenv_pc; exact Hmenvval0).
    assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10")
      by (rewrite Lms_pc; exact HSXL).
    assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs)))
      by (rewrite Lpma_pc; exact Hpma_all).
    iMod (tlb_inv_pt_translateAddr_store root_ppn pa s_pc
            Hrampa Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_store s_pc)
            Lpma_pc' with "Hreg Hmem Htlbinv")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & Hreg & Hmem & Htlbinv)".
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = ms0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpmpc_tr : register_lookup pmpcfg_n s_tr.(sregs) = pmpcfg0)
      by (rewrite (Hprestr pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc_pc).
    assert (Lpmpaddr_tr : register_lookup pmpaddr_n s_tr.(sregs) = pmpaddr00)
      by (rewrite (Hprestr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr_pc).
    assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
      by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
    assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
      by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
    pose proof (within_clint_false pa 4 s_tr (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 4 s_tr (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_writable_false pa 4 s_tr Lhtif_tr) as Hwh.
    assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr pa)))) (Store Data)) s_pc
                     = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_tr)).
    { replace ((bits_of_virtaddr (Virtaddr pa))) with pa
        by (cbn [bits_of_virtaddr]; reflexivity).
      exact Htr0. }
    assert (Hstore : exec (execute (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4))) s_pc
                    = Some (RETIRE_SUCCESS,
                            MState s_tr.(sregs)
                              (write_bytes s_tr.(mem) pa 4 storeval)
                              s_tr.(mdev))).
    { assert (Htea : exec (transform_effective_address
            (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                           (sign_extend' 64 imm))) (Store Data)) s_pc
          = Some (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                           (sign_extend' 64 imm)), s_pc)).
      { apply (exec_transform_effective_address_mode (Store Data) Sv39 _ s_pc Lpriv_pc
                 (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
                    ltac:(rewrite Lms_pc; exact HMPRV))
                 (exec_get_pmlen_store_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                    ltac:(rewrite Lmenv_pc; exact Hpmm))
                 (exec_translationMode_S_sv39 satp1 s_pc
                    ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode)). }
      pose proof (exec_execute_STORE_4_gpr_S_walk_pt (mword_of_int 0 : mword 5) rs1 imm region_st s_pc s_tr
               Htea
               ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               ltac:(rewrite Lpmpc_tr; exact HA0) ltac:(rewrite Lpmpaddr_tr; exact Hord0)
               ltac:(rewrite Lpmpaddr_tr Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_tr; exact HW)
               ltac:(rewrite Lpma_tr Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_st0)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
               Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)
               ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact (addr_is_ram_not_dev _ Hrampa))) as H0.
      rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id in H0.
      rewrite H0. do 3 f_equal;
      first [ reflexivity | f_equal; apply bv_eq; vm_compute; reflexivity ]. }
    iMod (upd_window_4 s_tr.(mem) pa storeval vold with "Hmem Hbytes") as "[Hmem Hbytes]".
    iModIntro.
    iExists (MState s_tr.(sregs) (write_bytes s_tr.(mem) pa 4 storeval) s_tr.(mdev)).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hstore. }
    iSplitL "Hreg Hmem Hdev".
    { cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (MState s_tr.(sregs) (write_bytes s_tr.(mem) pa 4 storeval) s_tr.(mdev)).(sregs)
             = add_vec_int pc 4).
    { cbn [sregs].
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (pa ↦₄ storeval)%I with "[Hbytes]" as "Hbw".
    { rewrite /word4_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
    iApply ("Hcont" with "Hhs' [Hpriv Hms Hhalf Hmiex Hmenv] Hcap Htlbinv
                          [$Hpc' $Hnpc] [Hfmap] Hbw").
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf".
      { iExists ms0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iSplitR; [iPureIntro; exact Hdom |].
    iExact "Hfmap".
  Qed.

  Notation IL := KernelSyms.initlock.

  (* ============================================================= *)
  (* initlock: whole-function WP over the sconf world.  Owns the     *)
  (* spinlock's three struct fields as raw memory and returns them   *)
  (* initialised; makes no sub-calls (a pure prologue / three        *)
  (* stores / epilogue).  NO [intr_count] -- it does no locking.     *)
  (* ============================================================= *)
  Lemma wp_initlock_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64))
      (vlock : bv 32) (vname vcpu : bv 64)
      (K : nat) :
    let pcE : mword 64 := mword_of_int IL in
    let lk := m !!! Regidx (mword_of_int 10 : mword 5) in
    let name := m !!! Regidx (mword_of_int 11 : mword 5) in
    let sp0 := m !!! Regidx csp_rs1 in
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    let c_name := add_vec lk (sign_extend' 64 (mword_of_int 8 : mword 12)) in
    let c_cpu := add_vec lk (sign_extend' 64 (mword_of_int 0x10 : mword 12)) in
    (2 <= K)%nat ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗
    tlb_inv_pt root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m -∗
    lk ↦₄ vlock -∗
    c_name ↦₈ vname -∗
    c_cpu ↦₈ vcpu -∗
    stack_own (pa_stk sp0 kv_frame_slots) K -∗
    ( ∀ mr,
      sconf γ -∗
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      sie_cap γ root_ppn mr -∗
      tlb_inv_pt root_ppn -∗
      pc_is ret_tgt -∗ gpr_file mr -∗
      ⌜ callee_saved m mr ⌝ -∗
      lk ↦₄ (mword_of_int 0 : mword 32) -∗
      c_name ↦₈ name -∗
      c_cpu ↦₈ (zero_reg : mword 64) -∗
      stack_own (pa_stk sp0 kv_frame_slots) K -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pcE lk name sp0 ret_tgt c_name c_cpu HK Hretm.
    set (spr := add_vec (m !!! Regidx csp_rs1 : mword 64) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    iIntros "Hsc Hhs Hcap Htlbinv #Htext Hpc Hfile Hlock Hname Hcpu Hdeep Hcont".
    (* split off the top-2 of the deep custody for the frame trade *)
    iDestruct (stack_own_split_1 (pa_stk sp0 kv_frame_slots) 2 K ltac:(lia) with "Hdeep") as "[Hd2 Hdeep]".
    iPoseProof (ini_00 with "Htext") as "Hi00".
    iPoseProof (ini_02 with "Htext") as "Hi02".
    iPoseProof (ini_04 with "Htext") as "Hi04".
    iPoseProof (ini_06 with "Htext") as "Hi06".
    iPoseProof (ini_08 with "Htext") as "Hi08".
    iPoseProof (ini_0a with "Htext") as "Hi0a".
    iPoseProof (ini_0e with "Htext") as "Hi0e".
    iPoseProof (ini_12 with "Htext") as "Hi12".
    iPoseProof (ini_14 with "Htext") as "Hi14".
    iPoseProof (ini_16 with "Htext") as "Hi16".
    iPoseProof (ini_18 with "Htext") as "Hi18".
    (* ===== PROLOGUE: 2-slot frame trade + saves ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m).
    assert (Hsp1 : R1 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 2).
    { rewrite /R1 lookup_total_insert. unfold regval_into_reg, pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    (* +0x00 c.addi sp,-16 -- the frame trade (move_down 2) *)
    iApply (wp_caddi_sp_s_sconf γ root_ppn Φ pcE (mword_of_int 48 : mword 6) m (stack_own sp0 2)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi00 [Hd2] [-]").
    { iIntros "Hcap".
      iDestruct (sie_cap_move_down γ root_ppn m R1 2 Hsp1 with "Hd2 Hcap") as "[Hcap Hframe]".
      iFrame "Hcap Hframe". }
    iIntros "Hhs Hsc Hcap Hframe Htlbinv Hpc Hfile".
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 lookup_total_insert; reflexivity).
    (* frame cells at [pa_stk sp0 1..2] *)
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & _)".
    iDestruct "S1" as (vra0) "Hras". iDestruct "S2" as (vs00) "Hs0s".
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hras". iEval (rewrite -Hb2) in "Hs0s".
    assert (Hpp02 : add_vec_int pcE 2 = mword_of_int (IL + 0x02)) by (unfold pcE; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,8(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (IL + 0x02)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              R1 vra0 with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi02 [Hras] [-]").
    { iEval (rewrite HspR1). iExact "Hras". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hras".
    iEval (rewrite HspR1) in "Hras".
    assert (Hpp04 : add_vec_int (mword_of_int (IL + 0x02) : mword 64) 2 = mword_of_int (IL + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,0(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (IL + 0x04)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              R1 vs00 with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi04 [Hs0s] [-]").
    { iEval (rewrite HspR1). iExact "Hs0s". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hs0s".
    iEval (rewrite HspR1) in "Hs0s".
    assert (Hpp06 : add_vec_int (mword_of_int (IL + 0x04) : mword 64) 2 = mword_of_int (IL + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.addi4spn s0,sp,16 *)
    iApply (wp_caddi4spn_s_sconf γ root_ppn Φ (mword_of_int (IL + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              R1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi06 [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1).
    assert (HR2a0 : R2 !!! Regidx (mword_of_int 10 : mword 5) = lk).
    { rewrite /R2 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R1 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HR2a1 : R2 !!! Regidx (mword_of_int 11 : mword 5) = name).
    { rewrite /R2 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R1 lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HspR2 : R2 !!! Regidx csp_rs1 = spr).
    { rewrite /R2 lookup_total_insert_ne; [| vm_compute; discriminate]. exact HspR1. }
    assert (Hpp08 : add_vec_int (mword_of_int (IL + 0x06) : mword 64) 2 = mword_of_int (IL + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sd a1,8(a0):  lk->name := a1 *)
    assert (Hea_name : add_vec (R2 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))) = c_name).
    { rewrite HR2a0. unfold c_name. f_equal; apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_csd_s_sconf γ root_ppn Φ (mword_of_int (IL + 0x08)) (mword_of_int 11 : mword 5) (mword_of_int 10 : mword 5)
              (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) R2 vname
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi08 [Hname] [-]").
    { iEval (rewrite Hea_name). iExact "Hname". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hname".
    iEval (rewrite Hea_name HR2a1) in "Hname".
    assert (Hpp0a : add_vec_int (mword_of_int (IL + 0x08) : mword 64) 2 = mword_of_int (IL + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a sw zero,0(a0):  lk->locked := 0 *)
    assert (Hea_lock : add_vec (R2 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = lk).
    { rewrite HR2a0. replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity). apply kv_addv_zero. }
    iApply (wp_sw_zero_s_sconf γ root_ppn Φ (mword_of_int (IL + 0x0a)) (mword_of_int 10 : mword 5)
              (mword_of_int 0 : mword 12) R2 vlock
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi0a [Hlock] [-]").
    { iEval (rewrite Hea_lock). iExact "Hlock". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hlock".
    iEval (rewrite Hea_lock) in "Hlock".
    assert (Hpp0e : add_vec_int (mword_of_int (IL + 0x0a) : mword 64) 4 = mword_of_int (IL + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e sd zero,16(a0):  lk->cpu := 0 *)
    assert (Hea_cpu : add_vec (R2 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0x10 : mword 12)) = c_cpu).
    { rewrite HR2a0. reflexivity. }
    iApply (wp_sd_zero_s_sconf γ root_ppn Φ (mword_of_int (IL + 0x0e)) (mword_of_int 10 : mword 5)
              (mword_of_int 0x10 : mword 12) R2 vcpu
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi0e [Hcpu] [-]").
    { iEval (rewrite Hea_cpu). iExact "Hcpu". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hcpu".
    iEval (rewrite Hea_cpu) in "Hcpu".
    assert (Hpp12 : add_vec_int (mword_of_int (IL + 0x0e) : mword 64) 4 = mword_of_int (IL + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* ===== EPILOGUE: restore ra/s0, frame trade back, ret ===== *)
    (* +0x12 c.ldsp ra,8(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (IL + 0x12)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              R2 (R1 !!! Regidx (mword_of_int 1 : mword 5)) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi12 [Hras] [-]").
    { iEval (rewrite HspR2). iExact "Hras". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hras".
    iEval (rewrite HspR2) in "Hras".
    set (R3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 1 : mword 5))]> R2).
    assert (HspR3 : R3 !!! Regidx csp_rs1 = spr).
    { rewrite /R3 lookup_total_insert_ne; [| vm_compute; discriminate]. exact HspR2. }
    assert (Hpp14 : add_vec_int (mword_of_int (IL + 0x12) : mword 64) 2 = mword_of_int (IL + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 c.ldsp s0,0(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (IL + 0x14)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              R3 (R1 !!! Regidx (mword_of_int 8 : mword 5)) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi14 [Hs0s] [-]").
    { iEval (rewrite HspR3). iExact "Hs0s". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hs0s".
    iEval (rewrite HspR3) in "Hs0s".
    set (R4 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 8 : mword 5))]> R3).
    assert (HspR4 : R4 !!! Regidx csp_rs1 = spr).
    { rewrite /R4 lookup_total_insert_ne; [| vm_compute; discriminate]. exact HspR3. }
    assert (Hpp16 : add_vec_int (mword_of_int (IL + 0x14) : mword 64) 2 = mword_of_int (IL + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* rebuild the 2-slot frame from the restored cells *)
    iEval (rewrite Hb1) in "Hras". iEval (rewrite Hb2) in "Hs0s".
    (* +0x16 c.addi sp,16 -- the frame trade back (move_up 2) *)
    set (R5 := <[Regidx csp_rs1 := regval_into_reg (add_vec (R4 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> R4).
    assert (HR5csp : R5 !!! Regidx csp_rs1 = sp0).
    { rewrite /R5 lookup_total_insert. rewrite HspR4. unfold regval_into_reg, spr, sp0. apply initlock_sp_cancel. }
    assert (Hup : R4 !!! Regidx csp_rs1 = pa_stk (R5 !!! Regidx csp_rs1) 2).
    { rewrite HspR4 HR5csp. unfold spr, sp0, pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_s_sconf γ root_ppn Φ (mword_of_int (IL + 0x16)) (mword_of_int 16 : mword 6) R4
              (stack_own (pa_stk sp0 kv_frame_slots) 2)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi16 [Hras Hs0s] [-]").
    { iIntros "Hcap".
      iAssert (stack_own (R5 !!! Regidx csp_rs1) 2) with "[Hras Hs0s]" as "Hframe".
      { rewrite HR5csp. rewrite stack_own_slots. cbn [seq].
        iSplitL "Hras"; [iExists _; iExact "Hras"|].
        iSplitL "Hs0s"; [iExists _; iExact "Hs0s"|].
        done. }
      iDestruct (sie_cap_move_up γ root_ppn R4 R5 2 Hup with "Hframe Hcap") as "[Hcap Hdeep2]".
      iEval (rewrite HR5csp) in "Hdeep2". iFrame "Hcap Hdeep2". }
    iIntros "Hhs Hsc Hcap Hdeep2 Htlbinv Hpc Hfile".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (R4 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> R4) with R5.
    assert (Hpp18 : add_vec_int (mword_of_int (IL + 0x16) : mword 64) 2 = mword_of_int (IL + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* recombine the returned deep-2 with the riding deep-(K-2) *)
    iDestruct (stack_own_split_2 (pa_stk sp0 kv_frame_slots) 2 K ltac:(lia) with "[$Hdeep2 $Hdeep]") as "Hdeep".
    (* +0x18 c.ret *)
    assert (HR5ra : R5 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /R5 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R4 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3 lookup_total_insert.
      unfold regval_into_reg.
      rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    assert (Hretaligned : eq_vec (access_vec_dec (update_vec_dec (add_vec (R5 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true)
      by (rewrite HR5ra; exact Hretm).
    iApply (wp_cret_s_sconf γ root_ppn Φ (mword_of_int (IL + 0x18)) (mword_of_int 1 : mword 5) R5
              ltac:(vm_compute; discriminate) Hretaligned
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi18 [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    assert (Hretf : update_vec_dec (add_vec (R5 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = ret_tgt)
      by (rewrite HR5ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    iApply ("Hcont" $! R5 with "Hsc Hhs Hcap Htlbinv Hpc Hfile [%] Hlock Hname Hcpu Hdeep").
    (* callee_saved m R5 *)
    assert (Hthread : forall c : mword 5, c <> csp_rs1 -> c <> mword_of_int 8 -> c <> mword_of_int 1 ->
                R5 !!! Regidx c = m !!! Regidx c).
    { intros c N2 N8 N1.
      rewrite /R5 lookup_total_insert_ne; [| congruence].
      rewrite /R4 lookup_total_insert_ne; [| congruence].
      rewrite /R3 lookup_total_insert_ne; [| congruence].
      rewrite /R2 lookup_total_insert_ne; [| congruence].
      rewrite /R1 lookup_total_insert_ne; [| congruence].
      reflexivity. }
    unfold callee_saved.
    split.
    { (* sp *)
      rewrite /R5 lookup_total_insert. rewrite HspR4.
      unfold regval_into_reg, spr. apply initlock_sp_cancel. }
    split.
    { (* tp *) apply Hthread; vm_compute; first [reflexivity | discriminate]. }
    split.
    { (* s0 *)
      rewrite /R5 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R4 lookup_total_insert.
      unfold regval_into_reg.
      rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate].
  Qed.

End WpSconfInitlock.
