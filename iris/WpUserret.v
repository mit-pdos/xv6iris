(* WpUserret.v -- verifying the [userret] trampoline (kernel/trampoline.S):
   the return-to-user path that switches from the kernel page table to a user
   process page table and sret's to user mode.

   userret sits in the TRAMPOLINE page: physically at KernelSyms.userret
   (0x8000609c, inside kernel text), but it EXECUTES at virtual address
   TRAMPOLINE + 0x9c = 0x3FFFFF F09C -- the same page is mapped at TRAMPOLINE
   in BOTH the kernel page table and every user page table, which is what
   makes the mid-stream satp switch coherent:

     0x9c  sfence.vma        (fetch via KERNEL PT: walk, fills slot 63)
     0xa0  csrw satp,a0      (fetch HITS slot 63; satp := user table)
     0xa4  sfence.vma        (fetch HITS the STALE kernel-PT entry -- same pa!)
                             (execute flushes the TLB; [utlb_inv] holds now)
     0xa8.. lui/c.addiw/c.slli  a0 := TRAPFRAME
     0xb0.. 27 ld/c.ld rd, off(a0)   (loads via the user PT's TRAPFRAME leaf)
     0x11a c.ld a0, 112(a0)
     0x11c sret               (SPP=0: to USER mode, pc := sepc)

   This file provides:
   - [utlb_inv]: the USER page table's TLB/PT invariant (the [tlb_inv] mirror
     for a user table): satp holds the user root, the TLB is slot-precise
     (63 = trampoline 4K entry or empty, 62 = trapframe 4K entry or empty,
     all others empty), and the four user PTEs are owned;
   - [ktramp_pte_bytes]: the KERNEL page table's trampoline-walk PTEs (the
     kernel [tlb_inv] only speaks about the kernel-text superpage, so the
     TRAMPOLINE mapping's three PTEs ride separately);
   - the unified S-mode fetch over the trampoline mapping (kernel- and
     user-table phases) and the step engines;
   - [instr] constructors for the 38 userret instructions;
   - [wp_userret]: the whole-trampoline WP through sret, ending in USER mode
     with [utlb_inv] established and the GPR file loaded from the trapframe. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpDecode WpDecodeBridge WpRvcBridge WpLeafCommon.
Require Import WpGpr WpGprLui WpGprAddi WpGprShift WpGprRvc WpGprRvcTor WpGprLoad WpLoad.
Require Import WpGprCsrwCommon WpGprCsrwB WpGprMretNew WpRelease.
Require Import WpEntryNew SmodeCore WpSmodeGpr WpSmodeSret WpKallocDecode.
Require Import TrampPt TrampTlb.
From Kernel Require Import KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 1. Constants: userret's va/pa windows and the user-PT PTE values.      *)
(* ===================================================================== *)

(* the userret instruction at trampoline-page offset [off]. *)
Definition uva (off : Z) : mword 64 := mword_of_int (TRAMPOLINE + off).
Definition upa (off : Z) : mword 64 := mword_of_int (KernelSyms.trampoline + off).

(* PTE values of the user table's trampoline/trapframe walk. *)
Definition pte_tramp : mword 64 := mk_pte tramp_ppn PTE_TRAMP.
Definition pte_tf (tfp : mword 44) : mword 64 := mk_pte tfp PTE_TF.
Definition pte_ptr (p : mword 44) : mword 64 := mk_pte p PTE_PTR.

(* the walk indices of both top-of-VA pages (VPN2=255, VPN1=511; VPN0 = 511
   for TRAMPOLINE, 510 for TRAPFRAME). *)
Local Notation idx2t := (subrange_vec_dec tramp_vpn 26 18).
Local Notation idx1t := (subrange_vec_dec tramp_vpn 17 9).
Local Notation idx0t := (subrange_vec_dec tramp_vpn 8 0).
Local Notation idx2f := (subrange_vec_dec tf_vpn 26 18).
Local Notation idx1f := (subrange_vec_dec tf_vpn 17 9).
Local Notation idx0f := (subrange_vec_dec tf_vpn 8 0).

(* the 4K TLB entries the two walks install (asid 0). *)
Definition tramp_ent (l0 : mword 44) : TLB_Entry :=
  tlb4k_entry (mword_of_int 0) tramp_vpn tramp_ppn pte_tramp (pte_addr_at l0 idx0t).
Definition tf_ent (ul0 tfp : mword 44) : TLB_Entry :=
  tlb4k_entry (mword_of_int 0) tf_vpn tfp (pte_tf tfp) (pte_addr_at ul0 idx0f).

(* ===================================================================== *)
(* 2. Iris bundles.                                                       *)
(* ===================================================================== *)

Section UserretIris.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  (* 8 owned bytes holding a PTE. *)
  Definition pte8 (a v : mword 64) (dq : dfrac) : iProp Σ :=
    ([∗ list] j ∈ seq 0 8, (pa_add a j) ↦ₘ{ dq } nth_byte v j)%I.

  (* the user table's four PTEs: root[255] -> l1, l1[511] -> l0,
     l0[511] = trampoline leaf, l0[510] = trapframe leaf. *)
  Definition upte_bytes (uroot ul1 ul0 tfp : mword 44) (dq : dfrac) : iProp Σ :=
    (pte8 (pte_addr_at uroot idx2t) (pte_ptr ul1) dq ∗
     pte8 (pte_addr_at ul1 idx1t) (pte_ptr ul0) dq ∗
     pte8 (pte_addr_at ul0 idx0t) pte_tramp dq ∗
     pte8 (pte_addr_at ul0 idx0f) (pte_tf tfp) dq)%I.

  (* the KERNEL table's trampoline-walk PTEs (kroot[255] -> kl1 -> kl0[511]).
     The kernel [tlb_inv] owns only the kernel-text superpage PTE; the
     TRAMPOLINE mapping's PTEs ride separately in the userret WP. *)
  Definition ktramp_pte_bytes (kroot kl1 kl0 : mword 44) (dq : dfrac) : iProp Σ :=
    (pte8 (pte_addr_at kroot idx2t) (pte_ptr kl1) dq ∗
     pte8 (pte_addr_at kl1 idx1t) (pte_ptr kl0) dq ∗
     pte8 (pte_addr_at kl0 idx0t) pte_tramp dq)%I.

  (* slot-precise TLB consistency for the user table: 63 = trampoline or
     empty, 62 = trapframe or empty, everything else empty. *)
  Definition utlb_consistent (ul0 tfp : mword 44)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) : Prop :=
    forall i, 0 <= i < 2 ^ 6 ->
      vec_access_dec tlbvec i = None \/
      (i = 63 /\ vec_access_dec tlbvec i = Some (tramp_ent ul0)) \/
      (i = 62 /\ vec_access_dec tlbvec i = Some (tf_ent ul0 tfp)).

  Lemma utlb_consistent_empty (ul0 tfp : mword 44)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
    (forall i, 0 <= i < 64 -> vec_access_dec tlbvec i = None) ->
    utlb_consistent ul0 tfp tlbvec.
  Proof. intros H i Hi. left. apply H. exact Hi. Qed.

  (* the two fills preserve consistency.  [tlb_hash tramp_vpn] = 63 and
     [tlb_hash tf_vpn] = 62 (direct-mapped low bits). *)
  Lemma tramp_hash : tlb_hash (__id 39) tramp_vpn = 63.
  Proof. vm_compute; reflexivity. Qed.
  Lemma tf_hash : tlb_hash (__id 39) tf_vpn = 62.
  Proof. vm_compute; reflexivity. Qed.

  Lemma utlb_consistent_fill63 (ul0 tfp : mword 44)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
    utlb_consistent ul0 tfp tlbvec ->
    utlb_consistent ul0 tfp
      (vec_update_dec tlbvec (tlb_hash (__id 39) tramp_vpn) (Some (tramp_ent ul0))).
  Proof.
    intros Hc i Hi.
    rewrite tramp_hash.
    rewrite (vec64_access_update tlbvec 63 i _ ltac:(lia)).
    destruct (Z.eqb_spec i 63) as [-> | Hne].
    - right; left. split; reflexivity.
    - apply Hc. exact Hi.
  Qed.

  Lemma utlb_consistent_fill62 (ul0 tfp : mword 44)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
    utlb_consistent ul0 tfp tlbvec ->
    utlb_consistent ul0 tfp
      (vec_update_dec tlbvec (tlb_hash (__id 39) tf_vpn) (Some (tf_ent ul0 tfp))).
  Proof.
    intros Hc i Hi.
    rewrite tf_hash.
    rewrite (vec64_access_update tlbvec 62 i _ ltac:(lia)).
    destruct (Z.eqb_spec i 62) as [-> | Hne].
    - right; right. split; reflexivity.
    - apply Hc. exact Hi.
  Qed.

  (* consistency gives [exec_translateAddr_tramp]'s slot disjunction. *)
  Lemma utlb_slot63 (ul0 tfp : mword 44) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
    utlb_consistent ul0 tfp tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) tramp_vpn) = None \/
    (exists ent, vec_access_dec tlbvec (tlb_hash (__id 39) tramp_vpn) = Some ent /\
                 match_TLB_Entry ent (mword_of_int 0) (sign_extend' (57 - 12) tramp_vpn) = false) \/
    (exists ptea, vec_access_dec tlbvec (tlb_hash (__id 39) tramp_vpn)
                  = Some (tlb4k_entry (mword_of_int 0) tramp_vpn tramp_ppn (mk_pte tramp_ppn PTE_TRAMP) ptea)).
  Proof.
    intros Hc.
    rewrite tramp_hash.
    destruct (Hc 63 ltac:(vm_compute; split; congruence)) as [Hn | [[_ He] | [Habs _]]].
    - left. exact Hn.
    - right; right. eexists. exact He.
    - lia.
  Qed.

  Lemma utlb_slot62 (ul0 tfp : mword 44) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
    utlb_consistent ul0 tfp tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) tf_vpn) = None \/
    (exists ent, vec_access_dec tlbvec (tlb_hash (__id 39) tf_vpn) = Some ent /\
                 match_TLB_Entry ent (mword_of_int 0) (sign_extend' (57 - 12) tf_vpn) = false) \/
    (exists ptea, vec_access_dec tlbvec (tlb_hash (__id 39) tf_vpn)
                  = Some (tlb4k_entry (mword_of_int 0) tf_vpn tfp (mk_pte tfp PTE_TF) ptea)).
  Proof.
    intros Hc.
    rewrite tf_hash.
    destruct (Hc 62 ltac:(vm_compute; split; congruence)) as [Hn | [[Habs _] | [_ He]]].
    - left. exact Hn.
    - lia.
    - right; right. eexists. exact He.
  Qed.

  (* the ambient PMP configuration for the user table's PTE reads (mirror of
     SmodeCore's [pmp_config], covering the FOUR user PTE addresses). *)
  Definition upmp_config (uroot ul1 ul0 tfp : mword 44) : iProp Σ :=
    (∃ (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
        (rg2 rg1 rg0t rg0f : PMA_Region),
       pmpcfg_n ↦ᵣ pmpcfg0 ∗ pmpaddr_n ↦ᵣ pmpaddr00 ∗
       ⌜ pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_addr_at uroot idx2t) ⌝ ∗
       ⌜ pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_addr_at ul1 idx1t) ⌝ ∗
       ⌜ pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_addr_at ul0 idx0t) ⌝ ∗
       ⌜ pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_addr_at ul0 idx0f) ⌝ ∗
       ⌜ forall pmar0, pma_allows_all pmar0 ->
           (matching_pma_region pmar0 (Physaddr (pte_addr_at uroot idx2t)) 8 = Some rg2 /\
            (override_PMA (PMA_Region_attributes rg2) PBMT_PMA).(PMA_supports_pte_read) = true) /\
           (matching_pma_region pmar0 (Physaddr (pte_addr_at ul1 idx1t)) 8 = Some rg1 /\
            (override_PMA (PMA_Region_attributes rg1) PBMT_PMA).(PMA_supports_pte_read) = true) /\
           (matching_pma_region pmar0 (Physaddr (pte_addr_at ul0 idx0t)) 8 = Some rg0t /\
            (override_PMA (PMA_Region_attributes rg0t) PBMT_PMA).(PMA_supports_pte_read) = true) /\
           (matching_pma_region pmar0 (Physaddr (pte_addr_at ul0 idx0f)) 8 = Some rg0f /\
            (override_PMA (PMA_Region_attributes rg0f) PBMT_PMA).(PMA_supports_pte_read) = true) ⌝ ∗
       ⌜ eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ⌝ ∗
       ⌜ eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ⌝ ∗
       ⌜ eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ⌝ ∗
       ⌜ (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ⌝)%I.

  (* ------------------------------------------------------------------- *)
  (* THE USER-PAGE-TABLE INVARIANT: the [tlb_inv] mirror for a user table. *)
  (* satp holds the user root; the TLB is [utlb_consistent]; the walk's    *)
  (* PTEs and the PMP configuration ride inside at full fraction.          *)
  (* ------------------------------------------------------------------- *)
  Definition utlb_inv (uroot ul1 ul0 tfp : mword 44) : iProp Σ :=
    (∃ (usatp : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
       satp ↦ᵣ usatp ∗
       ⌜ _get_Satp64_Mode (Mk_Satp64 usatp) = ('b"1000" : mword 4) ⌝ ∗
       ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) usatp : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
       ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) usatp : mword 64)) = uroot ⌝ ∗
       tlb ↦ᵣ tlbvec ∗ ⌜ utlb_consistent ul0 tfp tlbvec ⌝ ∗
       upte_bytes uroot ul1 ul0 tfp (DfracOwn 1) ∗
       upmp_config uroot ul1 ul0 tfp)%I.

  Lemma utlb_inv_intro (uroot ul1 ul0 tfp : mword 44) (usatp : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
    _get_Satp64_Mode (Mk_Satp64 usatp) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) usatp : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) usatp : mword 64)) = uroot ->
    utlb_consistent ul0 tfp tlbvec ->
    satp ↦ᵣ usatp -∗ tlb ↦ᵣ tlbvec -∗ upte_bytes uroot ul1 ul0 tfp (DfracOwn 1) -∗
    upmp_config uroot ul1 ul0 tfp -∗
    utlb_inv uroot ul1 ul0 tfp.
  Proof.
    intros Hmode Hasid Hppn Hc. iIntros "Hsatp Htlb Hpte Hpmp".
    iExists usatp, tlbvec. iFrame "Hsatp Htlb Hpte Hpmp". iPureIntro. tauto.
  Qed.

  Lemma utlb_inv_open (uroot ul1 ul0 tfp : mword 44) :
    utlb_inv uroot ul1 ul0 tfp -∗
    ∃ (usatp : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
      satp ↦ᵣ usatp ∗
      ⌜ _get_Satp64_Mode (Mk_Satp64 usatp) = ('b"1000" : mword 4) ⌝ ∗
      ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) usatp : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
      ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) usatp : mword 64)) = uroot ⌝ ∗
      tlb ↦ᵣ tlbvec ∗ ⌜ utlb_consistent ul0 tfp tlbvec ⌝ ∗
      upte_bytes uroot ul1 ul0 tfp (DfracOwn 1) ∗
      upmp_config uroot ul1 ul0 tfp.
  Proof. iIntros "H". iExact "H". Qed.

End UserretIris.

(* ===================================================================== *)
(* 3. The Iris-level fetch translation through the USER table: from       *)
(* [utlb_inv]'s opened pieces, any trampoline-page va translates to its   *)
(* physical home, HITTING slot 63 or WALKING the three owned PTEs (fill). *)
(* ===================================================================== *)

Section UserretFetch.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  (* mem-lookup facts for one owned PTE. *)
  Lemma pte8_facts (σ : mstate) (a v : mword 64) (dq : dfrac) :
    mstate_interp σ -∗ pte8 a v dq -∗
    ⌜ (forall j : nat, (N.of_nat j < 8)%N -> σ.(mem) !! (pa_add a j) = Some (nth_byte v j))
      /\ addr_is_ram a ⌝.
  Proof.
    iIntros "[Hreg Hmem] Hp".
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
               σ.(mem) !! (pa_add a j) = Some (nth_byte v j)⌝)%I as %Hb.
    { iIntros (j Hj).
      iDestruct (big_sepL_lookup _ _ j j with "Hp") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram a⌝)%I as %Hram.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hp") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iPureIntro. tauto.
  Qed.

  (* the leaf reductions for the two user leaves, discharged once. *)
  Lemma tramp_chk_fetch : forall (mxr do_sum : bool) s',
    exec (check_PTE_permission (InstructionFetch tt) Supervisor mxr do_sum
            (Mk_PTE_Flags (mword_of_int PTE_TRAMP)) (Mk_PTE_Ext (mword_of_int 0)) tt) s'
    = Some (PTE_Check_Success tt, s').
  Proof. intros mxr do_sum s'. destruct mxr, do_sum; vm_compute; reflexivity. Qed.

  Lemma tf_chk_load : forall (mxr do_sum : bool) s',
    exec (check_PTE_permission (Load Data) Supervisor mxr do_sum
            (Mk_PTE_Flags (mword_of_int PTE_TF)) (Mk_PTE_Ext (mword_of_int 0)) tt) s'
    = Some (PTE_Check_Success tt, s').
  Proof. intros mxr do_sum s'. destruct mxr, do_sum; vm_compute; reflexivity. Qed.

  Lemma tramp_inv_red : forall s',
    exec (pte_is_invalid (Mk_PTE_Flags (mword_of_int PTE_TRAMP)) (Mk_PTE_Ext (mword_of_int 0))) s'
    = Some (false, s').
  Proof. intro s'. vm_compute; reflexivity. Qed.

  Lemma tf_inv_red : forall s',
    exec (pte_is_invalid (Mk_PTE_Flags (mword_of_int PTE_TF)) (Mk_PTE_Ext (mword_of_int 0))) s'
    = Some (false, s').
  Proof. intro s'. vm_compute; reflexivity. Qed.

  (* THE per-va fetch translation, USER-phase.  Pure geometry facts about
     the CONCRETE va/pa pair are premises ([vm_compute] at instantiation). *)
  Lemma utramp_translate_fetch (uroot ul1 ul0 tfp : mword 44)
      (σ : mstate) (va pa : mword 64)
      (usatp mstatus0 misa0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (rg2 rg1 rg0t rg0f : PMA_Region) (pmar0 : list PMA_Region)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) {dqp dqs dqm dqe dqa dqh : dfrac} :
    pma_allows_all pmar0 ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 usatp) = ('b"1000" : mword 4) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) usatp : mword 64)) = uroot ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) usatp : mword 64)) = (mword_of_int 0 : mword 16) ->
    utlb_consistent ul0 tfp tlbvec ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_addr_at uroot idx2t) ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_addr_at ul1 idx1t) ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_addr_at ul0 idx0t) ->
    (matching_pma_region pmar0 (Physaddr (pte_addr_at uroot idx2t)) 8 = Some rg2 /\
     (override_PMA (PMA_Region_attributes rg2) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    (matching_pma_region pmar0 (Physaddr (pte_addr_at ul1 idx1t)) 8 = Some rg1 /\
     (override_PMA (PMA_Region_attributes rg1) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    (matching_pma_region pmar0 (Physaddr (pte_addr_at ul0 idx0t)) 8 = Some rg0t /\
     (override_PMA (PMA_Region_attributes rg0t) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    (* va/pa geometry (vm_compute at concrete instantiation) *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    mstate_interp σ -∗
    cur_privilege ↦ᵣ{ dqp } Supervisor -∗
    mstatus ↦ᵣ{ dqs } mstatus0 -∗
    satp ↦ᵣ usatp -∗
    tlb ↦ᵣ tlbvec -∗
    menvcfg ↦ᵣ{ dqe } menvcfg0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pmpaddr_n ↦ᵣ pmpaddr00 -∗
    pma_regions ↦ᵣ{ dqa } pmar0 -∗
    htif_tohost_base ↦ᵣ{ dqh } None -∗
    misa ↦ᵣ{ dqm } misa0 -∗
    upte_bytes uroot ul1 ul0 tfp (DfracOwn 1) -∗
    ⌜ exists tlbvec2,
        exec (translateAddr (Virtaddr va) (InstructionFetch tt)) σ
        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), set_reg σ tlb tlbvec2)
        /\ utlb_consistent ul0 tfp tlbvec2 ⌝.
  Proof.
    iIntros (Hpma0 HmisaS HSXL Hmode Hppn Hasid Hcons HPBMTE Hp2 Hp1 Hp0 Hr2 Hr1 Hr0
             Hcanon Hvpn Hident)
      "Hsi Hpriv Hms Hsatp Htlb Hmenv Hpmpc Hpmpa Hpma Hhtif Hmisa Hpte".
    iDestruct "Hpte" as "(Hpb2 & Hpb1 & Hpb0t & Hpb0f)".
    iDestruct (pte8_facts σ _ _ _ with "Hsi Hpb2") as %[Hb2 Hram2].
    iDestruct (pte8_facts σ _ _ _ with "Hsi Hpb1") as %[Hb1 Hram1].
    iDestruct (pte8_facts σ _ _ _ with "Hsi Hpb0t") as %[Hb0 Hram0].
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid    with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid    with "Hreg Hpmpa") as %Lpmpa.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iPureIntro.
    destruct Hp2 as (HA & Hord & Hrg2 & HR).
    destruct Hp1 as (_ & _ & Hrg1 & _).
    destruct Hp0 as (_ & _ & Hrg0 & _).
    destruct Hr2 as [Hm2 Hpr2]. destruct Hr1 as [Hm1 Hpr1]. destruct Hr0 as [Hm0 Hpr0].
    pose proof (addr_is_ram_not_in_clint _ Hram2) as Hnc2.
    pose proof (addr_is_ram_not_in_sig _ Hram2) as Hns2.
    pose proof (addr_is_ram_not_in_clint _ Hram1) as Hnc1.
    pose proof (addr_is_ram_not_in_sig _ Hram1) as Hns1.
    pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc0.
    pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns0.
    destruct (exec_translateAddr_tramp
                (InstructionFetch tt) tramp_vpn uroot ul1 ul0 tramp_ppn PTE_TRAMP
                rg2 rg1 rg0t menvcfg0 σ
                ltac:(unfold PTE_TRAMP; lia)
                tramp_inv_red
                ltac:(vm_compute; reflexivity)
                tramp_chk_fetch
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Lmisa; exact HmisaS)
                ltac:(rewrite Lpmpc; exact HA)
                ltac:(rewrite Lpmpa; exact Hord)
                ltac:(rewrite Lpmpc; exact HR)
                Lmenv HPBMTE
                ltac:(rewrite Lpmpa; exact Hrg2)
                ltac:(rewrite Lpma; exact Hm2)
                Hpr2
                (within_clint_false _ 8 σ Hnc2 ltac:(lia))
                (within_sig_false _ 8 σ Hns2 ltac:(lia))
                (within_htif_false _ 8 σ Lhtif)
                Hb2
                ltac:(rewrite Lpmpa; exact Hrg1)
                ltac:(rewrite Lpma; exact Hm1)
                Hpr1
                (within_clint_false _ 8 σ Hnc1 ltac:(lia))
                (within_sig_false _ 8 σ Hns1 ltac:(lia))
                (within_htif_false _ 8 σ Lhtif)
                Hb1
                ltac:(rewrite Lpmpa; exact Hrg0)
                ltac:(rewrite Lpma; exact Hm0)
                Hpr0
                (within_clint_false _ 8 σ Hnc0 ltac:(lia))
                (within_sig_false _ 8 σ Hns0 ltac:(lia))
                (within_htif_false _ 8 σ Lhtif)
                Hb0
                ltac:(unfold PTE_TRAMP; vm_compute; reflexivity)
                usatp pa va
                (exec_effectivePrivilege_fetch _ _ σ)
                (exec_is_shadow_stack_fetch σ)
                Lpriv
                ltac:(rewrite Lms; exact HSXL)
                Lsatp Hmode Hppn Hasid Hcanon Hvpn Hident
                tlbvec Ltlb
                (utlb_slot63 ul0 tfp tlbvec Hcons))
      as (s' & Htr & Hcase).
    destruct Hcase as [-> | ->].
    - exists tlbvec. split.
      + replace (set_reg σ tlb tlbvec) with σ; [exact Htr |].
        rewrite <- Ltlb. symmetry. apply set_reg_tlb_id.
      + exact Hcons.
    - eexists. split.
      + exact Htr.
      + (* the fill installs [tramp_ent ul0] at slot 63 *)
        change (tramp_tlb_ent tramp_vpn ul0 tramp_ppn PTE_TRAMP) with (tramp_ent ul0).
        apply utlb_consistent_fill63. exact Hcons.
  Qed.

End UserretFetch.

(* ===================================================================== *)
(* 4. The unified USER-phase fetch over [instr_bytes] at the PHYSICAL     *)
(* trampoline page: every 16-bit chunk translates through slot 63 (hit    *)
(* or 3-level walk + fill), and the bytes are read at [pa].               *)
(* ===================================================================== *)

Section UserretFetch2.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Lemma fetch_from_instr_bytes_u (uroot ul1 ul0 tfp : mword 44)
      (σ : mstate) (va pa : mword 64) (r : FetchResult)
      (usatp mstatus0 misa0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (rg2 rg1 rg0t rg0f : PMA_Region) (pmar0 : list PMA_Region)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) {dqp dqs dqm dqe dqa dqh : dfrac} :
    pma_allows_all pmar0 ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 usatp) = ('b"1000" : mword 4) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) usatp : mword 64)) = uroot ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) usatp : mword 64)) = (mword_of_int 0 : mword 16) ->
    utlb_consistent ul0 tfp tlbvec ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_addr_at uroot idx2t) ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_addr_at ul1 idx1t) ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_addr_at ul0 idx0t) ->
    (matching_pma_region pmar0 (Physaddr (pte_addr_at uroot idx2t)) 8 = Some rg2 /\
     (override_PMA (PMA_Region_attributes rg2) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    (matching_pma_region pmar0 (Physaddr (pte_addr_at ul1 idx1t)) 8 = Some rg1 /\
     (override_PMA (PMA_Region_attributes rg1) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    (matching_pma_region pmar0 (Physaddr (pte_addr_at ul0 idx0t)) 8 = Some rg0t /\
     (override_PMA (PMA_Region_attributes rg0t) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    (* --- va/pa geometry (all [vm_compute] at a concrete va/pa) --- *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int va 2)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub pagesize_bits 1) 0)) = add_vec_int pa 2 ->
    is_aligned_vaddr (Virtaddr va) 2 = true ->
    is_aligned_vaddr (Virtaddr pa) 4 = is_aligned_vaddr (Virtaddr va) 4 ->
    is_aligned_paddr (Physaddr pa) 2 = true ->
    is_aligned_paddr (Physaddr (add_vec_int pa 2)) 2 = true ->
    (is_aligned_vaddr (Virtaddr va) 4 = true -> is_aligned_paddr (Physaddr pa) 4 = true) ->
    addr_is_ram pa -> addr_is_ram (pa_add pa 1) ->
    addr_is_ram (pa_add pa 2) -> addr_is_ram (pa_add pa 3) ->
    mstate_interp σ -∗
    PC ↦ᵣ va -∗
    cur_privilege ↦ᵣ{ dqp } Supervisor -∗
    mstatus ↦ᵣ{ dqs } mstatus0 -∗
    satp ↦ᵣ usatp -∗
    tlb ↦ᵣ tlbvec -∗
    menvcfg ↦ᵣ{ dqe } menvcfg0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pmpaddr_n ↦ᵣ pmpaddr00 -∗
    pma_regions ↦ᵣ{ dqa } pmar0 -∗
    htif_tohost_base ↦ᵣ{ dqh } None -∗
    misa ↦ᵣ{ dqm } misa0 -∗
    upte_bytes uroot ul1 ul0 tfp (DfracOwn 1) -∗
    instr_bytes pa r -∗
    ⌜ exists tlbvec2,
        exec (fetch tt) σ = Some (r, set_reg σ tlb tlbvec2)
        /\ utlb_consistent ul0 tfp tlbvec2 ⌝.
  Proof.
    iIntros (Hpma0 HmisaS HmisaC HSXL Hmode Hppn Hasid Hcons HPBMTE HX Hcov
             Hp2 Hp1 Hp0 Hr2 Hr1 Hr0
             Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2
             Hva2 Hpa4va4 Hpa2al Hpa2al2 Hpa4al Hram0 Hram1 Hram2b Hram3b)
      "Hsi Hpc Hpriv Hms Hsatp Htlb Hmenv Hpmpc Hpmpa Hpma Hhtif Hmisa Hpte Hbytes".
    (* register lookups at σ *)
    iDestruct (state_interp_reg_dq σ cur_privilege _ _ with "Hsi Hpriv") as %Lpriv.
    iDestruct (state_interp_reg_dq σ mstatus _ _ with "Hsi Hms") as %Lms.
    iDestruct (state_interp_reg_dq σ misa _ _ with "Hsi Hmisa") as %Lmisa.
    iDestruct (state_interp_reg_dq σ menvcfg _ _ with "Hsi Hmenv") as %Lmenv.
    iDestruct (state_interp_reg_dq σ pma_regions _ _ with "Hsi Hpma") as %Lpma.
    iDestruct (state_interp_reg_dq σ htif_tohost_base _ _ with "Hsi Hhtif") as %Lhtif.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc") as %Lpc.
    iDestruct (reg_valid with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid with "Hreg Htlb") as %Ltlb.
    iDestruct (reg_valid with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid with "Hreg Hpmpa") as %Lpmpa.
    iAssert (mstate_interp σ) with "[Hreg Hmem]" as "Hsi". { iFrame. }
    (* the three fetch-walk PTE mem facts *)
    iDestruct "Hpte" as "(Hpb2 & Hpb1 & Hpb0t & Hpb0f)".
    iDestruct (pte8_facts σ _ _ _ with "Hsi Hpb2") as %[Hb2 HramP2].
    iDestruct (pte8_facts σ _ _ _ with "Hsi Hpb1") as %[Hb1 HramP1].
    iDestruct (pte8_facts σ _ _ _ with "Hsi Hpb0t") as %[Hb0 HramP0].
    iDestruct "Hsi" as "[Hreg Hmem]".
    (* the PURE per-chunk translation, applicable at ANY state agreeing with σ
       on everything but the tlb (whose value/consistency is a parameter). *)
    destruct Hp2 as (HAx & Hordx & Hrg2 & HRx).
    pose proof (conj HAx (conj Hordx (conj Hrg2 HRx))) as Hp2'.
    destruct Hr2 as [Hm2 Hpr2]. destruct Hr1 as [Hm1 Hpr1]. destruct Hr0 as [Hm0 Hpr0].
    pose proof (addr_is_ram_not_in_clint _ HramP2) as HncP2.
    pose proof (addr_is_ram_not_in_sig _ HramP2) as HnsP2.
    pose proof (addr_is_ram_not_in_clint _ HramP1) as HncP1.
    pose proof (addr_is_ram_not_in_sig _ HramP1) as HnsP1.
    pose proof (addr_is_ram_not_in_clint _ HramP0) as HncP0.
    pose proof (addr_is_ram_not_in_sig _ HramP0) as HnsP0.
    assert (Htrans : forall (s0 : mstate) (tv : vec (option TLB_Entry) (2 ^ 6))
                       (va0 pa0 : mword 64),
      s0.(mem) = σ.(mem) ->
      register_lookup cur_privilege s0.(sregs) = Supervisor ->
      register_lookup mstatus s0.(sregs) = mstatus0 ->
      register_lookup satp s0.(sregs) = usatp ->
      register_lookup menvcfg s0.(sregs) = menvcfg0 ->
      register_lookup misa s0.(sregs) = misa0 ->
      register_lookup pmpcfg_n s0.(sregs) = pmpcfg0 ->
      register_lookup pmpaddr_n s0.(sregs) = pmpaddr00 ->
      register_lookup pma_regions s0.(sregs) = pmar0 ->
      register_lookup htif_tohost_base s0.(sregs) = None ->
      register_lookup tlb s0.(sregs) = tv ->
      utlb_consistent ul0 tfp tv ->
      neq_vec (bits_of_virtaddr (Virtaddr va0))
        (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va0)) (Z.sub 39 1) 0)) = false ->
      autocast (T := mword) (subrange_vec_dec
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va0)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = tramp_vpn ->
      zero_extend' 64 (concat_vec tramp_ppn
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va0)) (Z.sub pagesize_bits 1) 0)) = pa0 ->
      exists tv2,
        exec (translateAddr (Virtaddr va0) (InstructionFetch tt)) s0
        = Some (Ok (Physaddr pa0, PBMT_PMA, init_ext_ptw), set_reg s0 tlb tv2)
        /\ utlb_consistent ul0 tfp tv2).
    { intros s0 tv va0 pa0 Hsm L0priv L0ms L0satp L0menv L0misa L0pmpc L0pmpa L0pma L0htif L0tlb
             Hcons0 Hcanon0 Hvpn0 Hident0.
      destruct (exec_translateAddr_tramp
                  (InstructionFetch tt) tramp_vpn uroot ul1 ul0 tramp_ppn PTE_TRAMP
                  rg2 rg1 rg0t menvcfg0 s0
                  ltac:(unfold PTE_TRAMP; lia)
                  tramp_inv_red
                  ltac:(vm_compute; reflexivity)
                  tramp_chk_fetch
                  ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  ltac:(rewrite L0misa; exact HmisaS)
                  ltac:(rewrite L0pmpc; exact HAx)
                  ltac:(rewrite L0pmpa; exact Hordx)
                  ltac:(rewrite L0pmpc; exact HRx)
                  L0menv HPBMTE
                  ltac:(rewrite L0pmpa; exact Hrg2)
                  ltac:(rewrite L0pma; exact Hm2)
                  Hpr2
                  (within_clint_false _ 8 s0 HncP2 ltac:(lia))
                  (within_sig_false _ 8 s0 HnsP2 ltac:(lia))
                  (within_htif_false _ 8 s0 L0htif)
                  ltac:(rewrite Hsm; exact Hb2)
                  ltac:(rewrite L0pmpa; destruct Hp1 as (_&_&HH&_); exact HH)
                  ltac:(rewrite L0pma; exact Hm1)
                  Hpr1
                  (within_clint_false _ 8 s0 HncP1 ltac:(lia))
                  (within_sig_false _ 8 s0 HnsP1 ltac:(lia))
                  (within_htif_false _ 8 s0 L0htif)
                  ltac:(rewrite Hsm; exact Hb1)
                  ltac:(rewrite L0pmpa; destruct Hp0 as (_&_&HH&_); exact HH)
                  ltac:(rewrite L0pma; exact Hm0)
                  Hpr0
                  (within_clint_false _ 8 s0 HncP0 ltac:(lia))
                  (within_sig_false _ 8 s0 HnsP0 ltac:(lia))
                  (within_htif_false _ 8 s0 L0htif)
                  ltac:(rewrite Hsm; exact Hb0)
                  ltac:(unfold PTE_TRAMP; vm_compute; reflexivity)
                  usatp pa0 va0
                  (exec_effectivePrivilege_fetch _ _ s0)
                  (exec_is_shadow_stack_fetch s0)
                  L0priv
                  ltac:(rewrite L0ms; exact HSXL)
                  L0satp Hmode Hppn Hasid Hcanon0 Hvpn0 Hident0
                  tv L0tlb
                  (utlb_slot63 ul0 tfp tv Hcons0))
        as (s' & Htr & Hcase).
      destruct Hcase as [-> | ->].
      - exists tv. split.
        + replace (set_reg s0 tlb tv) with s0; [exact Htr |].
          rewrite <- L0tlb. symmetry. apply set_reg_tlb_id.
        + exact Hcons0.
      - eexists. split.
        + exact Htr.
        + change (tramp_tlb_ent tramp_vpn ul0 tramp_ppn PTE_TRAMP) with (tramp_ent ul0).
          apply utlb_consistent_fill63. exact Hcons0. }
    (* register facts at the (possibly) filled state *)
    assert (Hreg1 : forall (tv2 : vec (option TLB_Entry) (2 ^ 6)) (rr : register),
              register_beq rr tlb = false ->
              register_lookup rr (set_reg σ tlb tv2).(sregs) = register_lookup rr σ.(sregs)).
    { intros tv2 rr Hne. unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [reflexivity | exact Hne]. }
    (* instruction-read pmp facts at any state with σ's registers *)
    pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
    pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
    iEval (rewrite /instr_bytes) in "Hbytes".
    iDestruct "Hbytes" as "[%H2alp Hbytes]".
    destruct r as [e | w | h | erx].
    - (* F_Ext_Error *) iDestruct "Hbytes" as %[].
    - (* F_Base w *)
      iDestruct "Hbytes" as "[%HnotRVC Hbytes]".
      iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
                 σ.(mem) !! (pa_add pa j) = Some (nth_byte w j)⌝)%I as %Hbf.
      { iIntros (j Hj).
        iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
        { rewrite lookup_seq_lt; [reflexivity | lia]. }
        iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
      iPureIntro.
      destruct (Hpma0 pa 4) as (rgi & Hmi & Hxi & _ & _).
      destruct (Hpma0 pa 2) as (rgl & Hml & Hxl & _ & _).
      destruct (Hpma0 (add_vec_int pa 2) 2) as (rgh & Hmh & Hxh & _ & _).
      destruct (is_aligned_vaddr (Virtaddr va) 4) eqn:Hal4.
      + (* single 4-byte read *)
        destruct (Htrans σ tlbvec va pa eq_refl Lpriv Lms Lsatp Lmenv Lmisa Lpmpc Lpmpa
                    Lpma Lhtif Ltlb Hcons Hcanon Hvpn Hident) as (tv2 & Htr & Hcons2).
        set (s1 := set_reg σ tlb tv2).
        exists tv2. split; [| exact Hcons2].
        apply (exec_fetch_F_Base_4_pa va pa w σ s1 rgi Lpc Hal4 Htr).
        * rewrite (Hreg1 tv2 pmpcfg_n ltac:(vm_compute; reflexivity)). rewrite Lpmpc. exact HAx.
        * rewrite (Hreg1 tv2 pmpaddr_n ltac:(vm_compute; reflexivity)). rewrite Lpmpa. exact Hordx.
        * rewrite (Hreg1 tv2 pmpaddr_n ltac:(vm_compute; reflexivity)). rewrite Lpmpa.
          exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 4 3
                   ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                   Hram0 Hram3b Hcov).
        * rewrite (Hreg1 tv2 pmpcfg_n ltac:(vm_compute; reflexivity)). rewrite Lpmpc. exact HX.
        * rewrite (Hreg1 tv2 pma_regions ltac:(vm_compute; reflexivity)). rewrite Lpma. exact Hmi.
        * exact (Hpa4al eq_refl).
        * exact Hxi.
        * exact (within_clint_false pa 4 s1 Hnc ltac:(lia)).
        * exact (within_sig_false pa 4 s1 Hns ltac:(lia)).
        * apply within_htif_false.
          rewrite (Hreg1 tv2 htif_tohost_base ltac:(vm_compute; reflexivity)). exact Lhtif.
        * intros j Hj. unfold s1, set_reg; cbn [mem]. exact (Hbf j Hj).
        * rewrite (Hreg1 tv2 cur_privilege ltac:(vm_compute; reflexivity)). exact Lpriv.
        * exact HnotRVC.
      + (* 2+2 read: both chunks through slot 63 *)
        destruct (align2_not4_facts va Hva2 Hal4) as (_ & Hbit0 & Hbit1).
        destruct (Htrans σ tlbvec va pa eq_refl Lpriv Lms Lsatp Lmenv Lmisa Lpmpc Lpmpa
                    Lpma Lhtif Ltlb Hcons Hcanon Hvpn Hident) as (tv2 & Htr1 & Hcons2).
        set (s1 := set_reg σ tlb tv2).
        assert (L1tlb : register_lookup tlb s1.(sregs) = tv2).
        { unfold s1, set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
        destruct (Htrans s1 tv2 (add_vec_int va 2) (add_vec_int pa 2) eq_refl
                    ltac:(rewrite (Hreg1 tv2 cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv)
                    ltac:(rewrite (Hreg1 tv2 mstatus ltac:(vm_compute; reflexivity)); exact Lms)
                    ltac:(rewrite (Hreg1 tv2 satp ltac:(vm_compute; reflexivity)); exact Lsatp)
                    ltac:(rewrite (Hreg1 tv2 menvcfg ltac:(vm_compute; reflexivity)); exact Lmenv)
                    ltac:(rewrite (Hreg1 tv2 misa ltac:(vm_compute; reflexivity)); exact Lmisa)
                    ltac:(rewrite (Hreg1 tv2 pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc)
                    ltac:(rewrite (Hreg1 tv2 pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpa)
                    ltac:(rewrite (Hreg1 tv2 pma_regions ltac:(vm_compute; reflexivity)); exact Lpma)
                    ltac:(rewrite (Hreg1 tv2 htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif)
                    L1tlb Hcons2 Hcanon2 Hvpn2 Hident2) as (tv3 & Htr2 & Hcons3).
        assert (Hcollapse : set_reg s1 tlb tv3 = set_reg σ tlb tv3)
          by (unfold s1; apply set_reg_tlb_overwrite).
        exists tv3. split; [| exact Hcons3].
        assert (Haddr : forall j : nat, (N.of_nat j < 2)%N ->
                  pa_add (add_vec_int pa 2) j = pa_add pa (2 + j)).
        { intros j _. unfold pa_add. rewrite avi_assoc. f_equal. lia. }
        apply (exec_fetch_F_Base_2_pa va pa (add_vec_int pa 2) w σ s1 (set_reg σ tlb tv3) rgl rgh
                 Lpc
                 ltac:(rewrite (Hreg1 tv2 PC ltac:(vm_compute; reflexivity)); exact Lpc)
                 ltac:(rewrite Lmisa; exact HmisaC)
                 Hbit0 Hbit1 Hal4 Htr1
                 ltac:(rewrite Hcollapse in Htr2; exact Htr2)).
        * rewrite (Hreg1 tv2 pmpcfg_n ltac:(vm_compute; reflexivity)). rewrite Lpmpc. exact HAx.
        * rewrite (Hreg1 tv2 pmpaddr_n ltac:(vm_compute; reflexivity)). rewrite Lpmpa. exact Hordx.
        * rewrite (Hreg1 tv2 pmpaddr_n ltac:(vm_compute; reflexivity)). rewrite Lpmpa.
          exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 2 1
                   ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                   Hram0 Hram1 Hcov).
        * rewrite (Hreg1 tv2 pmpcfg_n ltac:(vm_compute; reflexivity)). rewrite Lpmpc. exact HX.
        * rewrite (Hreg1 tv2 pma_regions ltac:(vm_compute; reflexivity)). rewrite Lpma. exact Hml.
        * exact Hpa2al.
        * exact Hxl.
        * exact (within_clint_false pa 2 s1 Hnc ltac:(lia)).
        * exact (within_sig_false pa 2 s1 Hns ltac:(lia)).
        * apply within_htif_false.
          rewrite (Hreg1 tv2 htif_tohost_base ltac:(vm_compute; reflexivity)). exact Lhtif.
        * intros j Hj. unfold s1, set_reg; cbn [mem].
          rewrite nth_byte_subrange_lo; [| exact Hj]. apply Hbf. lia.
        * rewrite (Hreg1 tv2 cur_privilege ltac:(vm_compute; reflexivity)). exact Lpriv.
        * rewrite (Hreg1 tv3 pmpcfg_n ltac:(vm_compute; reflexivity)). rewrite Lpmpc. exact HAx.
        * rewrite (Hreg1 tv3 pmpaddr_n ltac:(vm_compute; reflexivity)). rewrite Lpmpa. exact Hordx.
        * rewrite (Hreg1 tv3 pmpaddr_n ltac:(vm_compute; reflexivity)). rewrite Lpmpa.
          assert (Hramh1 : addr_is_ram (pa_add (add_vec_int pa 2) 1)).
          { rewrite (Haddr 1%nat ltac:(lia)). change (2 + 1)%nat with 3%nat. exact Hram3b. }
          assert (Hramh0 : addr_is_ram (add_vec_int pa 2)).
          { unfold pa_add in Hram2b. change (Z.of_nat 2) with 2 in Hram2b. exact Hram2b. }
          exact (ram_fetch_pmp (add_vec_int pa 2) (vec_access_dec pmpaddr00 0) 2 1
                   ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                   Hramh0 Hramh1 Hcov).
        * rewrite (Hreg1 tv3 pmpcfg_n ltac:(vm_compute; reflexivity)). rewrite Lpmpc. exact HX.
        * rewrite (Hreg1 tv3 pma_regions ltac:(vm_compute; reflexivity)). rewrite Lpma. exact Hmh.
        * exact Hpa2al2.
        * exact Hxh.
        * exact (within_clint_false _ 2 (set_reg σ tlb tv3)
                   (addr_is_ram_not_in_clint _ ltac:(unfold pa_add in Hram2b; change (Z.of_nat 2) with 2 in Hram2b; exact Hram2b)) ltac:(lia)).
        * exact (within_sig_false _ 2 (set_reg σ tlb tv3)
                   (addr_is_ram_not_in_sig _ ltac:(unfold pa_add in Hram2b; change (Z.of_nat 2) with 2 in Hram2b; exact Hram2b)) ltac:(lia)).
        * apply within_htif_false.
          rewrite (Hreg1 tv3 htif_tohost_base ltac:(vm_compute; reflexivity)). exact Lhtif.
        * intros j Hj. cbn [mem set_reg].
          rewrite nth_byte_subrange_hi; [| exact Hj].
          rewrite (Haddr j Hj). apply Hbf. lia.
        * rewrite (Hreg1 tv3 cur_privilege ltac:(vm_compute; reflexivity)). exact Lpriv.
        * exact HnotRVC.
        * apply concat_subranges_id.
    - (* F_RVC h *)
      iDestruct "Hbytes" as "[%HisRVC Hbytes]".
      rewrite Hpa4va4.
      destruct (is_aligned_vaddr (Virtaddr va) 4) eqn:Hal4.
      + (* 4-aligned RVC: read the full 4-byte window *)
        iDestruct "Hbytes" as (w) "[%Hsub Hbytes]".
        iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
                   σ.(mem) !! (pa_add pa j) = Some (nth_byte w j)⌝)%I as %Hbf.
        { iIntros (j Hj).
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        iPureIntro.
        destruct (Hpma0 pa 4) as (rgi & Hmi & Hxi & _ & _).
        destruct (Htrans σ tlbvec va pa eq_refl Lpriv Lms Lsatp Lmenv Lmisa Lpmpc Lpmpa
                    Lpma Lhtif Ltlb Hcons Hcanon Hvpn Hident) as (tv2 & Htr & Hcons2).
        set (s1 := set_reg σ tlb tv2).
        exists tv2. split; [| exact Hcons2].
        rewrite <- Hsub.
        apply (exec_fetch_RVC_4_pa va pa w σ s1 rgi Lpc Hal4 Htr).
        * rewrite (Hreg1 tv2 pmpcfg_n ltac:(vm_compute; reflexivity)). rewrite Lpmpc. exact HAx.
        * rewrite (Hreg1 tv2 pmpaddr_n ltac:(vm_compute; reflexivity)). rewrite Lpmpa. exact Hordx.
        * rewrite (Hreg1 tv2 pmpaddr_n ltac:(vm_compute; reflexivity)). rewrite Lpmpa.
          exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 4 3
                   ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                   Hram0 Hram3b Hcov).
        * rewrite (Hreg1 tv2 pmpcfg_n ltac:(vm_compute; reflexivity)). rewrite Lpmpc. exact HX.
        * rewrite (Hreg1 tv2 pma_regions ltac:(vm_compute; reflexivity)). rewrite Lpma. exact Hmi.
        * exact (Hpa4al eq_refl).
        * exact Hxi.
        * exact (within_clint_false pa 4 s1 Hnc ltac:(lia)).
        * exact (within_sig_false pa 4 s1 Hns ltac:(lia)).
        * apply within_htif_false.
          rewrite (Hreg1 tv2 htif_tohost_base ltac:(vm_compute; reflexivity)). exact Lhtif.
        * intros j Hj. unfold s1, set_reg; cbn [mem]. exact (Hbf j Hj).
        * rewrite (Hreg1 tv2 cur_privilege ltac:(vm_compute; reflexivity)). exact Lpriv.
        * rewrite Hsub. exact HisRVC.
      + (* 2-mod-4 RVC: single 2-byte read *)
        destruct (align2_not4_facts va Hva2 Hal4) as (_ & Hbit0 & Hbit1).
        iAssert (⌜forall j : nat, (N.of_nat j < 2)%N ->
                   σ.(mem) !! (pa_add pa j) = Some (nth_byte h j)⌝)%I as %Hbf.
        { iIntros (j Hj).
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        iPureIntro.
        destruct (Hpma0 pa 2) as (rgl & Hml & Hxl & _ & _).
        destruct (Htrans σ tlbvec va pa eq_refl Lpriv Lms Lsatp Lmenv Lmisa Lpmpc Lpmpa
                    Lpma Lhtif Ltlb Hcons Hcanon Hvpn Hident) as (tv2 & Htr & Hcons2).
        set (s1 := set_reg σ tlb tv2).
        exists tv2. split; [| exact Hcons2].
        apply (exec_fetch_RVC_2_pa va pa h σ s1 rgl Lpc
                 ltac:(rewrite Lmisa; exact HmisaC) Hbit0 Hbit1 Hal4 Htr).
        * rewrite (Hreg1 tv2 pmpcfg_n ltac:(vm_compute; reflexivity)). rewrite Lpmpc. exact HAx.
        * rewrite (Hreg1 tv2 pmpaddr_n ltac:(vm_compute; reflexivity)). rewrite Lpmpa. exact Hordx.
        * rewrite (Hreg1 tv2 pmpaddr_n ltac:(vm_compute; reflexivity)). rewrite Lpmpa.
          exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 2 1
                   ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                   Hram0 Hram1 Hcov).
        * rewrite (Hreg1 tv2 pmpcfg_n ltac:(vm_compute; reflexivity)). rewrite Lpmpc. exact HX.
        * rewrite (Hreg1 tv2 pma_regions ltac:(vm_compute; reflexivity)). rewrite Lpma. exact Hml.
        * exact Hpa2al.
        * exact Hxl.
        * exact (within_clint_false pa 2 s1 Hnc ltac:(lia)).
        * exact (within_sig_false pa 2 s1 Hns ltac:(lia)).
        * apply within_htif_false.
          rewrite (Hreg1 tv2 htif_tohost_base ltac:(vm_compute; reflexivity)). exact Lhtif.
        * intros j Hj. unfold s1, set_reg; cbn [mem]. exact (Hbf j Hj).
        * rewrite (Hreg1 tv2 cur_privilege ltac:(vm_compute; reflexivity)). exact Lpriv.
        * exact HisRVC.
    - iDestruct "Hbytes" as %[].
  Qed.

End UserretFetch2.

(* ===================================================================== *)
(* 5. wp_instr_u -- the step engine for USER-phase trampoline execution   *)
(* (the [wp_instr_s_config_tlbinv] mirror over [utlb_inv], with the       *)
(* instruction's va/pa geometry as pure premises).                        *)
(* ===================================================================== *)

Section WpInstrU.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_instr_u (uroot ul1 ul0 tfp : mword 44) E Φ
      (va pa : mword 64) (is_rvc : bool) (i : instruction)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
    ↑minstretN ⊆ E →
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* va/pa geometry ([vm_compute] at each concrete userret instruction) *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int va 2)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub pagesize_bits 1) 0)) = add_vec_int pa 2 ->
    is_aligned_vaddr (Virtaddr va) 2 = true ->
    is_aligned_vaddr (Virtaddr pa) 4 = is_aligned_vaddr (Virtaddr va) 4 ->
    is_aligned_paddr (Physaddr pa) 2 = true ->
    is_aligned_paddr (Physaddr (add_vec_int pa 2)) 2 = true ->
    (is_aligned_vaddr (Virtaddr va) 4 = true -> is_aligned_paddr (Physaddr pa) 4 = true) ->
    addr_is_ram pa -> addr_is_ram (pa_add pa 1) ->
    addr_is_ram (pa_add pa 2) -> addr_is_ram (pa_add pa 3) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    utlb_inv uroot ul1 ul0 tfp -∗
    PC ↦ᵣ va -∗
    instr pa is_rvc i -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = va)
       (usatp : mword 64) (tlbvec_f : vec (option TLB_Entry) (2 ^ 6))
       (Hmode : _get_Satp64_Mode (Mk_Satp64 usatp) = ('b"1000" : mword 4))
       (Hasid : zero_extend' 16 (satp_to_asid (autocast (T := mword) usatp : mword 64)) = (mword_of_int 0 : mword 16))
       (Hppn : autocast (T := mword) (satp_to_ppn (autocast (T := mword) usatp : mword 64)) = uroot)
       (Hconsf : utlb_consistent ul0 tfp tlbvec_f),
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       satp ↦ᵣ usatp -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       upmp_config uroot ul1 ul0 tfp -∗
       tlb ↦ᵣ tlbvec_f -∗
       upte_bytes uroot ul1 ul0 tfp (DfracOwn 1) -∗
       mstate_interp σ ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs))
                                     (if is_rvc then 2 else 4)))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
             Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2
             Hva2 Hpa4va4 Hpa2al Hpa2al2 Hpa4al Hram0 Hram1 Hram2b Hram3b)
      "#Hhw #Hinv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hutlb Hpc Hinstr H".
    iDestruct (utlb_inv_open with "Hutlb") as (usatp tlbvec)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Hcons & Hpbytes & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00 rg2 rg1 rg0t rg0f)
      "(Hpmpc & Hpmpa & %Hp2 & %Hp1 & %Hp0 & %Hpf & %Hpteregion & %HX & %HW & %HR & %Hcov)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpteregion pmar0 Hpma_all) as (Hr2 & Hr1 & Hr0t & Hr0f).
    iDestruct "Hinstr" as "[%Hnlpad Hr]".
    iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
    iApply (wp_exec_step_decode_execute_inv_priv Supervisor E Φ HN with "Hinv Hhs").
    iIntros (σ) "Hsi".
    iDestruct (fetch_from_instr_bytes_u uroot ul1 ul0 tfp σ va pa r
                 usatp mstatus0 misa0 menvcfg0 pmpcfg0 pmpaddr00 rg2 rg1 rg0t rg0f pmar0 tlbvec
                 Hpma_all HmisaS HmisaC HSXL Hmode Hppn Hasid Hcons HPBMTE HX Hcov
                 Hp2 Hp1 Hp0 Hr2 Hr1 Hr0t
                 Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2
                 Hva2 Hpa4va4 Hpa2al Hpa2al2 Hpa4al Hram0 Hram1 Hram2b Hram3b
                 with "Hsi Hpc Hpriv Hmstatus Hsatp Htlb Hmenvc Hpmpc Hpmpa Hpma Hhtif Hmisa Hpbytes Hbytes")
      as %Hfetch.
    destruct Hfetch as (tlbvec2 & Hfetcheq & Hcons2).
    iDestruct (dispatchInterrupt_none_S_from_regs σ misa0 mstatus0 mie_v mdv0
                 HmisaS Hmm HSIE
                 with "Hsi Hmisa Hmstatus Hmiec Hmdlc") as %Hdisp.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σ.
    iDestruct (reg_valid    with "Hreg Hpc")   as %Lpc.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iMod (reg_update _ tlb _ tlbvec2 with "Hreg Htlb") as "[Hreg Htlb]".
    set (σf := set_reg σ tlb tlbvec2 : mstate).
    iAssert (mstate_interp σf) with "[Hreg Hmem]" as "Hsi".
    { unfold σf, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iDestruct ("Hdec" $! σf with "Hsi") as %Hdec0.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σf.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Help_σf.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Hmisa_σf.
    iDestruct (reg_valid_dq with "Hreg Hmenvc") as %Hmenv_σf.
    specialize (Hdec0 ltac:(rewrite Hpriv_σf; reflexivity)
                      ltac:(rewrite Hmisa_σf; exact HmisaC)
                      ltac:(rewrite Hmisa_σf; exact HmisaA)
                      ltac:(rewrite Hmisa_σf; exact Hmisa_val0)
                      ltac:(unfold cfg_ok; right; split;
                            [ exact Hpriv_σf | rewrite Hmenv_σf; exact Hmenvval0 ])).
    assert (Lpc_σf : register_lookup PC σf.(sregs) = va).
    { unfold σf, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    iAssert (upmp_config uroot ul1 ul0 tfp) with "[Hpmpc Hpmpa]" as "Hpmp".
    { iExists pmpcfg0, pmpaddr00, rg2, rg1, rg0t, rg0f.
      iFrame "Hpmpc Hpmpa". iPureIntro. tauto. }
    iMod ("H" $! σf Lpc_σf usatp tlbvec2 Hmode Hasid Hppn Hcons2
            with "Hpriv Hsatp Hmstatus Hmiec Hmdlc Hmenvc Hpmp Htlb Hpbytes [$Hreg $Hmem]")
      as (s_exec) "(Hexec & [Hreg' Hmem'] & Hcont)".
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    iDestruct "Hexec" as %Hexec.
    destruct r as [e | w | h | erx].
    - iDestruct "Hbytes" as "[_ %Hbf]". done.
    - cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      iModIntro. iExists (F_Base w), i, σf, s_exec.
      iSplitR; [iPureIntro; exact Hpriv_σ |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetcheq |].
      iSplitR; [iPureIntro; exact Hdec0 |].
      iSplitR; [iPureIntro; rewrite Help_σf; exact Help_np |].
      iSplitR.
      { iSplitR; [iPureIntro; exact Hnlpad |]. iPureIntro; exact Hexec. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont".
    - cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      destruct Hdec0 as (i0 & Hdec & Hnlpad0 & Hexp).
      iModIntro. iExists (F_RVC h), i0, σf, s_exec.
      iSplitR; [iPureIntro; exact Hpriv_σ |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetcheq |].
      iSplitR; [iPureIntro; exact Hdec |].
      iSplitR; [iPureIntro; rewrite Help_σf; exact Help_np |].
      iSplitR.
      { iSplitR.
        { iPureIntro. apply exec_currentlyEnabled_Zca. rewrite Hmisa_σf. exact HmisaC. }
        iExists i. iSplit; iPureIntro; [apply Hexp | exact Hexec]. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont".
    - iDestruct "Hbytes" as "[_ %Hbf]". done.
  Qed.

End WpInstrU.

(* ===================================================================== *)
(* 6. The 38 userret instructions: decode facts + [instr] constructors.   *)
(* ===================================================================== *)

(* --- 32-bit words --- *)
Definition uw_sfence : mword 32 := mword_of_int 0x12000073.
Definition uw_csrw   : mword 32 := mword_of_int 0x18051073.
Definition uw_lui    : mword 32 := mword_of_int 0x02000537.
Definition uw_sret   : mword 32 := mword_of_int 0x10200073.

Definition uw_ld_ra : mword 32 := mword_of_int 0x02853083.
Definition uw_ld_sp : mword 32 := mword_of_int 0x03053103.
Definition uw_ld_gp : mword 32 := mword_of_int 0x03853183.
Definition uw_ld_tp : mword 32 := mword_of_int 0x04053203.
Definition uw_ld_t0 : mword 32 := mword_of_int 0x04853283.
Definition uw_ld_t1 : mword 32 := mword_of_int 0x05053303.
Definition uw_ld_t2 : mword 32 := mword_of_int 0x05853383.
Definition uw_ld_a6 : mword 32 := mword_of_int 0x0a053803.
Definition uw_ld_a7 : mword 32 := mword_of_int 0x0a853883.
Definition uw_ld_s2 : mword 32 := mword_of_int 0x0b053903.
Definition uw_ld_s3 : mword 32 := mword_of_int 0x0b853983.
Definition uw_ld_s4 : mword 32 := mword_of_int 0x0c053a03.
Definition uw_ld_s5 : mword 32 := mword_of_int 0x0c853a83.
Definition uw_ld_s6 : mword 32 := mword_of_int 0x0d053b03.
Definition uw_ld_s7 : mword 32 := mword_of_int 0x0d853b83.
Definition uw_ld_s8 : mword 32 := mword_of_int 0x0e053c03.
Definition uw_ld_s9 : mword 32 := mword_of_int 0x0e853c83.
Definition uw_ld_s10 : mword 32 := mword_of_int 0x0f053d03.
Definition uw_ld_s11 : mword 32 := mword_of_int 0x0f853d83.
Definition uw_ld_t3 : mword 32 := mword_of_int 0x10053e03.
Definition uw_ld_t4 : mword 32 := mword_of_int 0x10853e83.
Definition uw_ld_t5 : mword 32 := mword_of_int 0x11053f03.
Definition uw_ld_t6 : mword 32 := mword_of_int 0x11853f83.

(* --- compressed halves and their 4-aligned windows --- *)
Definition uh_addiw : mword 16 := mword_of_int 0x357d.
Definition uh_slli  : mword 16 := mword_of_int 0x0536.
Definition uwin_addiw : mword 32 := mword_of_int 0x0536357d.
Definition uh_cld_s0 : mword 16 := mword_of_int 0x7120.
Definition uh_cld_s1 : mword 16 := mword_of_int 0x7524.
Definition uh_cld_a1 : mword 16 := mword_of_int 0x7d2c.
Definition uh_cld_a2 : mword 16 := mword_of_int 0x6150.
Definition uh_cld_a3 : mword 16 := mword_of_int 0x6554.
Definition uh_cld_a4 : mword 16 := mword_of_int 0x6958.
Definition uh_cld_a5 : mword 16 := mword_of_int 0x6d5c.
Definition uh_cld_a0 : mword 16 := mword_of_int 0x7928.
Definition uwin_cld_s0 : mword 32 := mword_of_int 0x75247120.
Definition uwin_cld_a1 : mword 32 := mword_of_int 0x61507d2c.
Definition uwin_cld_a3 : mword 32 := mword_of_int 0x69586554.
Definition uwin_cld_a5 : mword 32 := mword_of_int 0x38036d5c.

(* --- ASTs --- *)
Definition ureg (n : Z) : regidx := Regidx (mword_of_int n).
Definition ucreg (n : Z) : cregidx := Cregidx (mword_of_int n).
Definition ai_sfence : instruction := SFENCE_VMA (zreg, zreg).
Definition ai_csrw : instruction := CSRReg (csr_satp, ureg 10, zreg, CSRRW).
Definition ai_lui : instruction := UTYPE (mword_of_int 0x2000, ureg 10, LUI).
Definition ai_addiw : instruction :=
  ADDIW (sign_extend' 12 (mword_of_int 63 : mword 6), ureg 10, ureg 10).
Definition ai_slli : instruction :=
  SHIFTIOP (mword_of_int 13, ureg 10, ureg 10, SLLI).
Definition ai_sret : instruction := SRET tt.
Definition ai_ld (rd : Z) (imm : Z) : instruction :=
  LOAD (mword_of_int imm, ureg 10, ureg rd, false, 8).
Definition ai_cld_tgt (rdc : Z) (uimm : Z) : instruction :=
  LOAD (mword_of_int (uimm * 8), ureg 10, ureg (8 + rdc), false, 8).

(* --- decode facts --- *)
Lemma udec_sfence s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_sfence) s = Some (ai_sfence, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_csrw s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_csrw) s = Some (ai_csrw, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_lui s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_lui) s = Some (ai_lui, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_sret s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_sret) s = Some (ai_sret, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_ra s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_ra) s = Some (ai_ld 1 40, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_sp s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_sp) s = Some (ai_ld 2 48, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_gp s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_gp) s = Some (ai_ld 3 56, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_tp s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_tp) s = Some (ai_ld 4 64, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_t0 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_t0) s = Some (ai_ld 5 72, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_t1 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_t1) s = Some (ai_ld 6 80, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_t2 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_t2) s = Some (ai_ld 7 88, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_a6 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_a6) s = Some (ai_ld 16 160, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_a7 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_a7) s = Some (ai_ld 17 168, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_s2 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_s2) s = Some (ai_ld 18 176, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_s3 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_s3) s = Some (ai_ld 19 184, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_s4 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_s4) s = Some (ai_ld 20 192, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_s5 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_s5) s = Some (ai_ld 21 200, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_s6 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_s6) s = Some (ai_ld 22 208, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_s7 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_s7) s = Some (ai_ld 23 216, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_s8 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_s8) s = Some (ai_ld 24 224, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_s9 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_s9) s = Some (ai_ld 25 232, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_s10 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_s10) s = Some (ai_ld 26 240, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_s11 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_s11) s = Some (ai_ld 27 248, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_t3 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_t3) s = Some (ai_ld 28 256, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_t4 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_t4) s = Some (ai_ld 29 264, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_t5 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_t5) s = Some (ai_ld 30 272, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_t6 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_t6) s = Some (ai_ld 31 280, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_addiw s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uh_addiw) s
  = Some (C_ADDIW (mword_of_int 63, ureg 10), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma udec_slli s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uh_slli) s
  = Some (C_SLLI (mword_of_int 13, ureg 10), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma udec_cld_s0 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uh_cld_s0) s
  = Some (C_LD (mword_of_int 12, ucreg 2, ucreg 0), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma udec_cld_s1 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uh_cld_s1) s
  = Some (C_LD (mword_of_int 13, ucreg 2, ucreg 1), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma udec_cld_a1 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uh_cld_a1) s
  = Some (C_LD (mword_of_int 15, ucreg 2, ucreg 3), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma udec_cld_a2 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uh_cld_a2) s
  = Some (C_LD (mword_of_int 16, ucreg 2, ucreg 4), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma udec_cld_a3 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uh_cld_a3) s
  = Some (C_LD (mword_of_int 17, ucreg 2, ucreg 5), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma udec_cld_a4 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uh_cld_a4) s
  = Some (C_LD (mword_of_int 18, ucreg 2, ucreg 6), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma udec_cld_a5 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uh_cld_a5) s
  = Some (C_LD (mword_of_int 19, ucreg 2, ucreg 7), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma udec_cld_a0 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uh_cld_a0) s
  = Some (C_LD (mword_of_int 14, ucreg 2, ucreg 2), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.


Section UserretInstrs.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Local Ltac u_mk_base A w pc ast decname :=
    let Hlpad := fresh "Hlpad" in
    let H2al := fresh "H2al" in
    let Hnrvc := fresh "Hnrvc" in
    let Hbytes := fresh "Hbytes" in
    assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
    assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
    assert (Hnrvc : isRVC (subrange_vec_dec w 15 0) = false) by (vm_compute; reflexivity);
    assert (Hbytes : forall j, (j < 4)%nat ->
        KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte w j))
      by (intros j Hj;
          do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
    iIntros "#Ht"; rewrite /instr;
    iSplitR; [iPureIntro; exact Hlpad|];
    iExists (F_Base w);
    iSplitR; [iPureIntro; reflexivity|];
    iSplitL "";
    [ iApply (instr_bytes_base pc w H2al Hnrvc);
      iApply (kernel_window_pc A w 4 pc eq_refl Hbytes with "Ht")
    | iIntros (?) "_"; iPureIntro; intros; apply decname; assumption ].

  Local Ltac u_mk_rvc4 A h w pc ast decname expname :=
    let Hlpad := fresh "Hlpad" in
    let H2al := fresh "H2al" in
    let H4al := fresh "H4al" in
    let Hrvc := fresh "Hrvc" in
    let Hsub := fresh "Hsub" in
    let Hbytes := fresh "Hbytes" in
    assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
    assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
    assert (H4al : is_aligned_vaddr (Virtaddr pc) 4 = true) by (vm_compute; reflexivity);
    assert (Hrvc : isRVC h = true) by (vm_compute; reflexivity);
    assert (Hsub : subrange_vec_dec w 15 0 = h) by (apply bv_eq; vm_compute; reflexivity);
    assert (Hbytes : forall j, (j < 4)%nat ->
        KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte w j))
      by (intros j Hj;
          do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
    iIntros "#Ht"; rewrite /instr;
    iSplitR; [iPureIntro; exact Hlpad|];
    iExists (F_RVC h);
    iSplitR; [iPureIntro; reflexivity|];
    iSplitL "";
    [ iApply (instr_bytes_rvc4 pc h w H2al H4al Hrvc Hsub);
      iApply (kernel_window_pc A w 4 pc eq_refl Hbytes with "Ht")
    | iIntros (?) "_"; iPureIntro; intros; cbn [fetch_is_rvc];
      eexists; (split; [ apply decname; assumption
                       | split; [ vm_compute; reflexivity
                                | intro; apply expname ] ]) ].

  Local Ltac u_mk_rvc2 A h pc ast decname expname :=
    let Hlpad := fresh "Hlpad" in
    let H2al := fresh "H2al" in
    let H4al := fresh "H4al" in
    let Hrvc := fresh "Hrvc" in
    let Hbytes := fresh "Hbytes" in
    assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
    assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
    assert (H4al : is_aligned_vaddr (Virtaddr pc) 4 = false) by (vm_compute; reflexivity);
    assert (Hrvc : isRVC h = true) by (vm_compute; reflexivity);
    assert (Hbytes : forall j, (j < 2)%nat ->
        KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte h j))
      by (intros j Hj;
          do 2 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
    iIntros "#Ht"; rewrite /instr;
    iSplitR; [iPureIntro; exact Hlpad|];
    iExists (F_RVC h);
    iSplitR; [iPureIntro; reflexivity|];
    iSplitL "";
    [ iApply (instr_bytes_rvc2 pc h H2al H4al Hrvc);
      iApply (kernel_window_pc A h 2 pc eq_refl Hbytes with "Ht")
    | iIntros (?) "_"; iPureIntro; intros; cbn [fetch_is_rvc];
      eexists; (split; [ apply decname; assumption
                       | split; [ vm_compute; reflexivity
                                | intro; apply expname ] ]) ].

  Lemma ui_sfence1 :
    kernel_text -∗ instr (upa 0x9c) false ai_sfence.
  Proof. u_mk_base (KernelSyms.trampoline + 0x9c) uw_sfence (upa 0x9c) ai_sfence udec_sfence. Qed.

  Lemma ui_csrw :
    kernel_text -∗ instr (upa 0xa0) false ai_csrw.
  Proof. u_mk_base (KernelSyms.trampoline + 0xa0) uw_csrw (upa 0xa0) ai_csrw udec_csrw. Qed.

  Lemma ui_sfence2 :
    kernel_text -∗ instr (upa 0xa4) false ai_sfence.
  Proof. u_mk_base (KernelSyms.trampoline + 0xa4) uw_sfence (upa 0xa4) ai_sfence udec_sfence. Qed.

  Lemma ui_lui :
    kernel_text -∗ instr (upa 0xa8) false ai_lui.
  Proof. u_mk_base (KernelSyms.trampoline + 0xa8) uw_lui (upa 0xa8) ai_lui udec_lui. Qed.

  Lemma ui_addiw :
    kernel_text -∗ instr (upa 0xac) true ai_addiw.
  Proof. u_mk_rvc4 (KernelSyms.trampoline + 0xac) uh_addiw uwin_addiw (upa 0xac) ai_addiw udec_addiw exec_execute_C_ADDIW. Qed.

  Lemma ui_slli :
    kernel_text -∗ instr (upa 0xae) true ai_slli.
  Proof. u_mk_rvc2 (KernelSyms.trampoline + 0xae) uh_slli (upa 0xae) ai_slli udec_slli exec_execute_C_SLLI. Qed.

  Lemma ui_ld_ra :
    kernel_text -∗ instr (upa 0xb0) false (ai_ld 1 40).
  Proof. u_mk_base (KernelSyms.trampoline + 0xb0) uw_ld_ra (upa 0xb0) (ai_ld 1 40) udec_ld_ra. Qed.

  Lemma ui_ld_sp :
    kernel_text -∗ instr (upa 0xb4) false (ai_ld 2 48).
  Proof. u_mk_base (KernelSyms.trampoline + 0xb4) uw_ld_sp (upa 0xb4) (ai_ld 2 48) udec_ld_sp. Qed.

  Lemma ui_ld_gp :
    kernel_text -∗ instr (upa 0xb8) false (ai_ld 3 56).
  Proof. u_mk_base (KernelSyms.trampoline + 0xb8) uw_ld_gp (upa 0xb8) (ai_ld 3 56) udec_ld_gp. Qed.

  Lemma ui_ld_tp :
    kernel_text -∗ instr (upa 0xbc) false (ai_ld 4 64).
  Proof. u_mk_base (KernelSyms.trampoline + 0xbc) uw_ld_tp (upa 0xbc) (ai_ld 4 64) udec_ld_tp. Qed.

  Lemma ui_ld_t0 :
    kernel_text -∗ instr (upa 0xc0) false (ai_ld 5 72).
  Proof. u_mk_base (KernelSyms.trampoline + 0xc0) uw_ld_t0 (upa 0xc0) (ai_ld 5 72) udec_ld_t0. Qed.

  Lemma ui_ld_t1 :
    kernel_text -∗ instr (upa 0xc4) false (ai_ld 6 80).
  Proof. u_mk_base (KernelSyms.trampoline + 0xc4) uw_ld_t1 (upa 0xc4) (ai_ld 6 80) udec_ld_t1. Qed.

  Lemma ui_ld_t2 :
    kernel_text -∗ instr (upa 0xc8) false (ai_ld 7 88).
  Proof. u_mk_base (KernelSyms.trampoline + 0xc8) uw_ld_t2 (upa 0xc8) (ai_ld 7 88) udec_ld_t2. Qed.

  Lemma ui_ld_a6 :
    kernel_text -∗ instr (upa 0xda) false (ai_ld 16 160).
  Proof. u_mk_base (KernelSyms.trampoline + 0xda) uw_ld_a6 (upa 0xda) (ai_ld 16 160) udec_ld_a6. Qed.

  Lemma ui_ld_a7 :
    kernel_text -∗ instr (upa 0xde) false (ai_ld 17 168).
  Proof. u_mk_base (KernelSyms.trampoline + 0xde) uw_ld_a7 (upa 0xde) (ai_ld 17 168) udec_ld_a7. Qed.

  Lemma ui_ld_s2 :
    kernel_text -∗ instr (upa 0xe2) false (ai_ld 18 176).
  Proof. u_mk_base (KernelSyms.trampoline + 0xe2) uw_ld_s2 (upa 0xe2) (ai_ld 18 176) udec_ld_s2. Qed.

  Lemma ui_ld_s3 :
    kernel_text -∗ instr (upa 0xe6) false (ai_ld 19 184).
  Proof. u_mk_base (KernelSyms.trampoline + 0xe6) uw_ld_s3 (upa 0xe6) (ai_ld 19 184) udec_ld_s3. Qed.

  Lemma ui_ld_s4 :
    kernel_text -∗ instr (upa 0xea) false (ai_ld 20 192).
  Proof. u_mk_base (KernelSyms.trampoline + 0xea) uw_ld_s4 (upa 0xea) (ai_ld 20 192) udec_ld_s4. Qed.

  Lemma ui_ld_s5 :
    kernel_text -∗ instr (upa 0xee) false (ai_ld 21 200).
  Proof. u_mk_base (KernelSyms.trampoline + 0xee) uw_ld_s5 (upa 0xee) (ai_ld 21 200) udec_ld_s5. Qed.

  Lemma ui_ld_s6 :
    kernel_text -∗ instr (upa 0xf2) false (ai_ld 22 208).
  Proof. u_mk_base (KernelSyms.trampoline + 0xf2) uw_ld_s6 (upa 0xf2) (ai_ld 22 208) udec_ld_s6. Qed.

  Lemma ui_ld_s7 :
    kernel_text -∗ instr (upa 0xf6) false (ai_ld 23 216).
  Proof. u_mk_base (KernelSyms.trampoline + 0xf6) uw_ld_s7 (upa 0xf6) (ai_ld 23 216) udec_ld_s7. Qed.

  Lemma ui_ld_s8 :
    kernel_text -∗ instr (upa 0xfa) false (ai_ld 24 224).
  Proof. u_mk_base (KernelSyms.trampoline + 0xfa) uw_ld_s8 (upa 0xfa) (ai_ld 24 224) udec_ld_s8. Qed.

  Lemma ui_ld_s9 :
    kernel_text -∗ instr (upa 0xfe) false (ai_ld 25 232).
  Proof. u_mk_base (KernelSyms.trampoline + 0xfe) uw_ld_s9 (upa 0xfe) (ai_ld 25 232) udec_ld_s9. Qed.

  Lemma ui_ld_s10 :
    kernel_text -∗ instr (upa 0x102) false (ai_ld 26 240).
  Proof. u_mk_base (KernelSyms.trampoline + 0x102) uw_ld_s10 (upa 0x102) (ai_ld 26 240) udec_ld_s10. Qed.

  Lemma ui_ld_s11 :
    kernel_text -∗ instr (upa 0x106) false (ai_ld 27 248).
  Proof. u_mk_base (KernelSyms.trampoline + 0x106) uw_ld_s11 (upa 0x106) (ai_ld 27 248) udec_ld_s11. Qed.

  Lemma ui_ld_t3 :
    kernel_text -∗ instr (upa 0x10a) false (ai_ld 28 256).
  Proof. u_mk_base (KernelSyms.trampoline + 0x10a) uw_ld_t3 (upa 0x10a) (ai_ld 28 256) udec_ld_t3. Qed.

  Lemma ui_ld_t4 :
    kernel_text -∗ instr (upa 0x10e) false (ai_ld 29 264).
  Proof. u_mk_base (KernelSyms.trampoline + 0x10e) uw_ld_t4 (upa 0x10e) (ai_ld 29 264) udec_ld_t4. Qed.

  Lemma ui_ld_t5 :
    kernel_text -∗ instr (upa 0x112) false (ai_ld 30 272).
  Proof. u_mk_base (KernelSyms.trampoline + 0x112) uw_ld_t5 (upa 0x112) (ai_ld 30 272) udec_ld_t5. Qed.

  Lemma ui_ld_t6 :
    kernel_text -∗ instr (upa 0x116) false (ai_ld 31 280).
  Proof. u_mk_base (KernelSyms.trampoline + 0x116) uw_ld_t6 (upa 0x116) (ai_ld 31 280) udec_ld_t6. Qed.

  Lemma ui_cld_s0 :
    kernel_text -∗ instr (upa 0xcc) true (ai_cld_tgt 0 12).
  Proof. u_mk_rvc4 (KernelSyms.trampoline + 0xcc) uh_cld_s0 uwin_cld_s0 (upa 0xcc) (ai_cld_tgt 0 12) udec_cld_s0 exec_execute_C_LD. Qed.

  Lemma ui_cld_s1 :
    kernel_text -∗ instr (upa 0xce) true (ai_cld_tgt 1 13).
  Proof. u_mk_rvc2 (KernelSyms.trampoline + 0xce) uh_cld_s1 (upa 0xce) (ai_cld_tgt 1 13) udec_cld_s1 exec_execute_C_LD. Qed.

  Lemma ui_cld_a1 :
    kernel_text -∗ instr (upa 0xd0) true (ai_cld_tgt 3 15).
  Proof. u_mk_rvc4 (KernelSyms.trampoline + 0xd0) uh_cld_a1 uwin_cld_a1 (upa 0xd0) (ai_cld_tgt 3 15) udec_cld_a1 exec_execute_C_LD. Qed.

  Lemma ui_cld_a2 :
    kernel_text -∗ instr (upa 0xd2) true (ai_cld_tgt 4 16).
  Proof. u_mk_rvc2 (KernelSyms.trampoline + 0xd2) uh_cld_a2 (upa 0xd2) (ai_cld_tgt 4 16) udec_cld_a2 exec_execute_C_LD. Qed.

  Lemma ui_cld_a3 :
    kernel_text -∗ instr (upa 0xd4) true (ai_cld_tgt 5 17).
  Proof. u_mk_rvc4 (KernelSyms.trampoline + 0xd4) uh_cld_a3 uwin_cld_a3 (upa 0xd4) (ai_cld_tgt 5 17) udec_cld_a3 exec_execute_C_LD. Qed.

  Lemma ui_cld_a4 :
    kernel_text -∗ instr (upa 0xd6) true (ai_cld_tgt 6 18).
  Proof. u_mk_rvc2 (KernelSyms.trampoline + 0xd6) uh_cld_a4 (upa 0xd6) (ai_cld_tgt 6 18) udec_cld_a4 exec_execute_C_LD. Qed.

  Lemma ui_cld_a5 :
    kernel_text -∗ instr (upa 0xd8) true (ai_cld_tgt 7 19).
  Proof. u_mk_rvc4 (KernelSyms.trampoline + 0xd8) uh_cld_a5 uwin_cld_a5 (upa 0xd8) (ai_cld_tgt 7 19) udec_cld_a5 exec_execute_C_LD. Qed.

  Lemma ui_cld_a0 :
    kernel_text -∗ instr (upa 0x11a) true (ai_cld_tgt 2 14).
  Proof. u_mk_rvc2 (KernelSyms.trampoline + 0x11a) uh_cld_a0 (upa 0x11a) (ai_cld_tgt 2 14) udec_cld_a0 exec_execute_C_LD. Qed.

  Lemma ui_sret :
    kernel_text -∗ instr (upa 0x11c) false ai_sret.
  Proof. u_mk_base (KernelSyms.trampoline + 0x11c) uw_sret (upa 0x11c) ai_sret udec_sret. Qed.


End UserretInstrs.
