(* ====================================================================== *)
(* BootChain.v -- THE PER-HART BOOT CHAIN.                                 *)
(*                                                                        *)
(* One hart's whole life, from the residue a power-on hands it to the       *)
(* [WP (LoopE gen c)] adequacy asks for, composed out of the three proven   *)
(* contracts:                                                             *)
(*                                                                        *)
(*   [SpecEntry.wp_entry_boot]  ([LinkEntry.Entry])   -- reset -> <main>    *)
(*   [BootBridge.boot_bridge]                         -- M-mode -> sconf    *)
(*   [SpecMain.wp_main_boot_sconf] / [SpecMainSecondary.                    *)
(*    wp_main_secondary_sconf]                        -- <main> -> forever  *)
(*                                                                        *)
(* NOTHING HERE IS ABOUT MORE THAN ONE HART.  Every statement is at the     *)
(* AMBIENT [CpuId], so the client (adequacy) applies it once per hart with  *)
(* [CID := c]; the resources it takes are exactly that hart's share of the  *)
(* client bundle plus the SHARED persistents, and never another hart's      *)
(* anything.                                                              *)
(*                                                                        *)
(*   §1 THE BOOT GEOMETRY -- the concrete addresses the chain runs on:      *)
(*      [_entry]'s GOT slot and the &stack0 word in it, and this hart's     *)
(*      [sp0 = &stack0 + 4096*(mhartid+1)] with every bound the M-mode      *)
(*      contract and the bridge ask about it.  All of it is CLOSED          *)
(*      arithmetic once the hart index is: [v_stack0] is the image's own    *)
(*      word and [mhartid] is pinned to the hart index by                  *)
(*      [RiscvLang.reset_regs], so each fact is eight [vm_compute]s and     *)
(*      needs no [lia] at all (which is what keeps it out of the           *)
(*      [bitvector.tactics] zify hook's way).                              *)
(*   §2 THE M-MODE HALF, COMPOSED -- [boot_entry_bridge]: this hart's       *)
(*      reset register cells plus the image plus its own .bss become        *)
(*      main's per-hart precondition ([sie_cap_gpr] + [cpu_own] + the SIE   *)
(*      spare quarter + [main_hart_raw]) and [pc_is <main>].  The memory    *)
(*      side enters as premises in the CARVE's vocabulary (BootCarve /      *)
(*      BootCarveMain produce every one of them), so the remaining boot     *)
(*      client is the cut chain plus the ghost allocations.                 *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap finite list_numbers bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvFetchExec MinstretInv.
Require Import RegFile HartTp InstrBytes WpGpr.
Require Import KMap KptPt SmodePte.
Require Import StackOwn.
Require Import WpMmodeLeafBase.
Require Import KernelText.
Require Import WpEntryNew WpTimerinit WpStartNew.
Require Import SRegime SmodeCore.
Require Import IntrDefs.
Require Import ProcGeom CpuOwn SchedCtx.
Require Import SpecMain.
Require Import BootConfig BootBridge PowerBoot.
Require Import SpecEntry LinkEntry.
From Kernel Require KernelData.
From Kernel Require KernelSyms.
Require Import RiscvExtras.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* §1  THE BOOT GEOMETRY.                                                  *)
(* ====================================================================== *)

(* [_entry]'s `la sp, stack0` is an auipc/ld pair, so the value it loads is a
   WORD OF THE IMAGE, at the pc-relative slot [entry_got]; and the word there
   is &stack0.  [WpEntryNew.entry_ld_ea] is the address the WP computes; these
   two lemmas are the only place the tree says what it IS. *)
Definition entry_got : Z := 0x8000a208.

Definition v_stack0 : mword 64 := mword_of_int KernelSyms.stack0.

Lemma entry_ld_ea_addr : entry_ld_ea = pa_of_z entry_got.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* the eight image bytes at the slot ARE &stack0's, little-endian: exactly
   [BootCarve.kernel_data_phys_word]'s one obligation. *)
Lemma entry_got_bytes (j : nat) :
  (j < 8)%nat ->
  KernelData.kernel_data !! (entry_got + Z.of_nat j) = Some (nth_byte v_stack0 j).
Proof.
  intro Hj.
  (* [vm_compute; reflexivity] does NOT close these: the two sides are
     [Some <the same bv literal>] with DIFFERENT [BvWf] proofs, and print
     identically (durable-notes' [bv_eq] trap, one [option] layer up). *)
  destruct j as [|[|[|[|[|[|[|[|j']]]]]]]]; [.. | cbn in Hj; lia];
    vm_compute; apply (f_equal Some), bv_eq; reflexivity.
Qed.

(* THE PER-HART STACK POINTER.  [_entry] computes sp = &stack0 + 4096*(hart+1)
   ([sp_of] below), and [RiscvLang.reset_regs] pins mhartid to the hart index,
   so for a concrete hart every fact about it is closed arithmetic. *)
Definition sp_of (n : nat) : Z := KernelSyms.stack0 + 4096 * (Z.of_nat n + 1).

(* the depth of the carve below sp0: the hart's own 4096-byte [stack0] slice
   is exactly [uint sp0 - 8*512, uint sp0), which is what makes the ONE range
   serve both [wp_entry_boot]'s [4 <= n] and the bridge's
   [boot_stack_slots K_main = 86 <= n]. *)
Definition boot_stack_depth : nat := 512%nat.

Lemma boot_stack_depth_entry : (4 <= boot_stack_depth)%nat.
Proof. unfold boot_stack_depth. lia. Qed.

Lemma boot_stack_depth_bridge : (boot_stack_slots K_main <= boot_stack_depth)%nat.
Proof. rewrite boot_stack_slots_main. unfold boot_stack_depth. lia. Qed.

(* [_entry]'s eight instructions write sp, a0 and a1, so the computed sp does
   not mention the initial map at all: peeling the eight-deep insert tower
   bottoms out in a CLOSED term. *)
Lemma sp0_val (m : regfile) (n : nat) :
  (n < NCPU)%nat ->
  m_jal m v_stack0 (boot_w64 (Z.of_nat n)) !!! Regidx csp_rs1
  = (mword_of_int (sp_of n) : mword 64).
Proof.
  unfold NCPU. intro Hn.
  destruct n as [|[|[|[|[|[|[|[|n']]]]]]]]; [.. | lia];
    apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma sp0_uint (n : nat) :
  (n < NCPU)%nat -> uint (mword_of_int (sp_of n) : mword 64) = sp_of n.
Proof.
  unfold NCPU. intro Hn.
  destruct n as [|[|[|[|[|[|[|[|n']]]]]]]]; [.. | lia];
    vm_compute; reflexivity.
Qed.

(* timerinit's two frame slots sit inside the TOR region start() opened
   ([0, 0xfffffffffffffc)) -- [wp_entry_boot]'s two stack-geometry premises. *)
Lemma ti_ea_ra_bound (n : nat) :
  (n < NCPU)%nat ->
  uint (ti_ea_ra (ti_sp1 (mword_of_int (sp_of n) : mword 64))) + 8
  <= 0xfffffffffffffc.
Proof.
  unfold NCPU. intro Hn.
  destruct n as [|[|[|[|[|[|[|[|n']]]]]]]]; [.. | lia];
    vm_compute; discriminate.
Qed.

Lemma ti_ea_s0_bound (n : nat) :
  (n < NCPU)%nat ->
  uint (ti_ea_s0 (ti_sp1 (mword_of_int (sp_of n) : mword 64))) + 8
  <= 0xfffffffffffffc.
Proof.
  unfold NCPU. intro Hn.
  destruct n as [|[|[|[|[|[|[|[|n']]]]]]]]; [.. | lia];
    vm_compute; discriminate.
Qed.

(* the bridge's two stack-location bounds, at [K := K_main] *)
Lemma sp_of_lo (n : nat) :
  (n < NCPU)%nat ->
  text_end + 8 * Z.of_nat (boot_stack_slots K_main) <= sp_of n.
Proof.
  unfold NCPU. intro Hn. rewrite boot_stack_slots_main.
  destruct n as [|[|[|[|[|[|[|[|n']]]]]]]]; [.. | lia];
    vm_compute; discriminate.
Qed.

Lemma sp_of_hi (n : nat) : (n < NCPU)%nat -> sp_of n <= ram_base + ram_size.
Proof.
  unfold NCPU. intro Hn.
  destruct n as [|[|[|[|[|[|[|[|n']]]]]]]]; [.. | lia];
    vm_compute; discriminate.
Qed.

(* THE tp/cid CONVENTION, at any hart: start()'s `mv tp, a1` writes mhartid,
   and [HartTp.cid_word_of] IS [mword_of_int (Z.of_nat (fin_to_nat c))]. *)
Lemma st_tpv_of_nat (n : nat) :
  (n < NCPU)%nat ->
  st_tpv (boot_w64 (Z.of_nat n)) = (mword_of_int (Z.of_nat n) : mword 64).
Proof.
  unfold NCPU. intro Hn.
  destruct n as [|[|[|[|[|[|[|[|n']]]]]]]]; [.. | lia];
    apply bv_eq; vm_compute; reflexivity.
Qed.

(* the boot menvcfg has the Zicfilp landing-pad enable clear *)
Lemma menvcfg_boot_lpe : _get_MEnvcfg_LPE (boot_w64 0) = ('b"0").
Proof. vm_compute. reflexivity. Qed.

(* ====================================================================== *)
(* §2  THE M-MODE PRECONDITION, out of one hart's reset residue.           *)
(*                                                                        *)
(* [boot_entry_pre] is the whole register side of the chain: this hart's    *)
(* [boot_D] cells (at the values [reset_regs] pins them to) plus the        *)
(* persisted static claims plus the generation certificate become EXACTLY   *)
(* what [SpecEntry.wp_entry_boot] asks for -- [mmode_config] included,      *)
(* which means allocating this hart's [minstret_inv] and freezing its       *)
(* [hw_config] cells on the way -- together with the five S-mode registers  *)
(* the M-mode contract never touches and [BootBridge.boot_bridge] wants,    *)
(* and the two PLIC wire pins the device client asks for.                   *)
(*                                                                        *)
(* Everything below the register layer (the image, the stack slice, this    *)
(* hart's cpus[] cells) is the CARVE's, and is not this lemma's business.   *)
(* ====================================================================== *)

Section BootChain.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma boot_entry_pre (E : coPset) (rs : regstate) :
    reset_regs cpu_id rs ->
    kmap_static_claims -∗
    gen_cert -∗
    boot_reg_res rs
    ={E}=∗
      (* --- [wp_entry_boot]'s own inputs --- *)
      mmode_config (DfracOwn 1) ∗
      pmpcfg_n ↦ᵣ pmpcfg_boot ∗
      pmpaddr_n ↦ᵣ register_lookup pmpaddr_n rs ∗
      pc_is (mword_of_int KernelSyms._entry) ∗
      gpr_file (boot_regfile rs) ∗
      mhartid ↦ᵣ boot_w64 (Z.of_nat (fin_to_nat cpu_id)) ∗
      mepc ↦ᵣ register_lookup mepc rs ∗
      satp ↦ᵣ register_lookup satp rs ∗
      medeleg ↦ᵣ register_lookup medeleg rs ∗
      mideleg ↦ᵣ register_lookup mideleg rs ∗
      mie ↦ᵣ register_lookup mie rs ∗
      menvcfg ↦ᵣ boot_w64 0 ∗
      mcounteren ↦ᵣ register_lookup mcounteren rs ∗
      stimecmp ↦ᵣ register_lookup stimecmp rs ∗
      (* --- the S-mode cells the M-mode boot never touches: [boot_bridge]'s
             per-hart register inputs --- *)
      tlb ↦ᵣ register_lookup tlb rs ∗
      (∃ v : mword 64, stvec ↦ᵣ v) ∗
      (∃ v : mword 64, sepc ↦ᵣ v) ∗
      (∃ v : mword 64, scause ↦ᵣ v) ∗
      (∃ v : mword 64, stval ↦ᵣ v) ∗
      (* --- the PLIC wire pins ([WireInv.wire_inv]'s, allocated across all
             harts by the client) --- *)
      sig_seip ↦ᵣ register_lookup sig_seip rs ∗
      sig_meip ↦ᵣ register_lookup sig_meip rs.
  Proof.
    intros (Hpc0 & Hnpc0 & Hpv0 & Hhs0 & Hmh0 & Hms0 & Hmisa0 & Hsec0 & Hmenv0 &
            Hhtif0 & Help0 & Hpma0 & Hpmpc0).
    iIntros "#Hcl #Hcert Hregs".
    iDestruct (boot_reg_split rs with "Hregs") as
      "(HPC & HnPC & Hpriv & Hhs & Hmh & Hms & Hmisa & Hsec & Hmenv & Hhtif & Help &
        Hpma & Hpmpc & Hpmpa & Hmepc & Hsatp & Hmede & Hmdl & Hmie & Hmcen & Hstc &
        Hmst & Hminc & Hmcy & Hmt & Hmip & Hseip & Hmeip & Htlb & Hstvec &
        Hsepc & Hscause & Hstval & Hgprs)".
    (* the pinned cells, at their pinned values *)
    iEval (rewrite Hpc0 boot_pc_entry) in "HPC".
    iEval (rewrite Hnpc0 boot_pc_entry) in "HnPC".
    iEval (rewrite Hpv0) in "Hpriv".
    iEval (rewrite Hhs0) in "Hhs".
    iEval (rewrite Hmh0) in "Hmh".
    iEval (rewrite Hms0) in "Hms".
    iEval (rewrite Hmisa0) in "Hmisa".
    iEval (rewrite Hsec0) in "Hsec".
    iEval (rewrite Hmenv0) in "Hmenv".
    iEval (rewrite Hhtif0) in "Hhtif".
    iEval (rewrite Help0) in "Help".
    iEval (rewrite Hpma0) in "Hpma".
    iEval (rewrite Hpmpc0) in "Hpmpc".
    (* this hart's two register invariants, and the frozen config bundle *)
    iMod (minstret_inv_alloc E _ _ _ _ _
            with "Hcert Hmst Hminc Hmcy Hmt Hmip") as "#Hmin".
    iMod (hw_config_intro with "Hmisa Hsec Hpma Hhtif Help Hcl") as "#Hhw".
    iModIntro.
    iSplitL "Hhs Hpriv Hms".
    { iApply (mmode_config_intro (DfracOwn 1) with "Hhw Hmin Hhs Hpriv Hms"). }
    iFrame "Hpmpc Hpmpa".
    iSplitL "HPC HnPC". { rewrite /pc_is. iFrame "HPC HnPC". }
    iSplitL "Hgprs". { iApply (boot_gpr_file rs with "Hgprs"). }
    iFrame "Hmh Hmepc Hsatp Hmede Hmdl Hmie Hmenv Hmcen Hstc Htlb".
    iSplitL "Hstvec". { iExists (register_lookup stvec rs). iExact "Hstvec". }
    iSplitL "Hsepc". { iExists (register_lookup sepc rs). iExact "Hsepc". }
    iSplitL "Hscause". { iExists (register_lookup scause rs). iExact "Hscause". }
    iSplitL "Hstval". { iExists (register_lookup stval rs). iExact "Hstval". }
    iFrame "Hseip Hmeip".
  Qed.

End BootChain.

(* ====================================================================== *)
(* §3  THE M-MODE HALF, RUN AND BRIDGED.                                   *)
(*                                                                        *)
(* [boot_entry_bridge] takes [boot_entry_pre]'s output (minus the two PLIC *)
(* wire pins -- see below), runs [SpecEntry.wp_entry_boot] over §1's        *)
(* geometry, and applies [BootBridge.boot_bridge] to its postcondition, so  *)
(* what reaches the continuation is EXACTLY the per-hart half of either     *)
(* main arm's precondition plus [pc_is <main>].                            *)
(*                                                                        *)
(* THE WIRE PINS ARE NOT TAKEN HERE, and that is forced by the control      *)
(* flow, exactly as the [cpus[h].proc] split was (M6c (2a)):                *)
(* [WireInv.wire_inv_alloc] wants ALL EIGHT harts' [sig_seip]/[sig_meip]    *)
(* cells at once, and it must run before any hart's WP -- so the client     *)
(* calls [boot_entry_pre] for every hart inside its own [={⊤}=∗], keeps the *)
(* sixteen pins for the wire invariant, and hands each hart the rest here.  *)
(* That is why [boot_entry_pre] is a separate fupd rather than folded in.   *)
(*                                                                        *)
(* THE ENTRY mstatus IS HANDLED BY THE POST'S FACT BUNDLE.  [HoKF]          *)
(* ([MstatusFacts.mstatus_kernel_facts ms0], M6c (2b)) plus                *)
(* [BootBridge.boot_csrs_from_kf] discharge the bridge's two mstatus        *)
(* premises without the client ever learning the entry value -- which it    *)
(* cannot, since the contract's post quantifies over it.                    *)
(* ====================================================================== *)

Section BootRun.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma boot_entry_bridge (Φ : mval -> iProp Σ) (rs : regstate)
      (iv : mword 32) (dq : dfrac) :
    reset_regs cpu_id rs ->
    (* THE TWO CSR PINS THE RESET MACHINE DOES NOT YET GIVE.  [boot_bridge]'s
       "no non-delegated interrupt is enabled" premise
       ([and_vec (st_mie1 mie0 mideleg0) (not_vec (st_mdl1 mideleg0)) = 0]) is
       FALSE at an arbitrary entry [mie] -- an M-mode enable bit such as MEIE
       survives start()'s `csrs sie` write while [mideleg]'s legalizer forces
       the matching delegation bit to 0.  [RiscvLang.reset_regs] pins thirteen
       registers and mie/mideleg are not among them, so these two are premises
       here rather than consequences.  Reality supplies them (a reset hart has
       every interrupt disabled and delegates nothing), which makes this the
       same shape of finding as the [nextPC] pin of M6c-pre -- see
       claude-notes/projects/crash.md, M6c (3).  (satp needs no pin: writing 0
       selects Bare whatever the old value was.) *)
    register_lookup mie rs = boot_w64 0 ->
    register_lookup mideleg rs = boot_w64 0 ->
    (* --- [boot_entry_pre]'s output, minus the two wire pins --- *)
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg_boot -∗
    pmpaddr_n ↦ᵣ register_lookup pmpaddr_n rs -∗
    pc_is (mword_of_int KernelSyms._entry) -∗
    gpr_file (boot_regfile rs) -∗
    mhartid ↦ᵣ boot_w64 (Z.of_nat (fin_to_nat cpu_id)) -∗
    mepc ↦ᵣ register_lookup mepc rs -∗
    satp ↦ᵣ register_lookup satp rs -∗
    medeleg ↦ᵣ register_lookup medeleg rs -∗
    mideleg ↦ᵣ register_lookup mideleg rs -∗
    mie ↦ᵣ register_lookup mie rs -∗
    menvcfg ↦ᵣ boot_w64 0 -∗
    mcounteren ↦ᵣ register_lookup mcounteren rs -∗
    stimecmp ↦ᵣ register_lookup stimecmp rs -∗
    tlb ↦ᵣ register_lookup tlb rs -∗
    (∃ v : mword 64, stvec ↦ᵣ v) -∗
    (∃ v : mword 64, sepc ↦ᵣ v) -∗
    (∃ v : mword 64, scause ↦ᵣ v) -∗
    (∃ v : mword 64, stval ↦ᵣ v) -∗
    (* --- the image and this hart's stack slice (the CARVE's outputs) --- *)
    kernel_text -∗
    entry_ld_ea ↦ₚ₈{ dq } v_stack0 -∗
    stack_own_phys (mword_of_int (sp_of (fin_to_nat cpu_id))) boot_stack_depth -∗
    (* --- the bridge's adequacy-minted and .bss inputs --- *)
    strans_bit strans_bit_bare -∗
    strans_bit strans_bit_bare -∗
    ghost_var sie_gname (1/2) ('b"0" : mword 1) -∗
    ghost_var sie_gname (1/4) ('b"0" : mword 1) -∗
    ghost_var sie_gname (1/4) ('b"0" : mword 1) -∗
    a_cpu_noff cid_word ↦₄ noff_val 0 -∗
    a_cpu_int cid_word ↦₄ iv -∗
    cpu_proc_half cpu_id zero_reg -∗
    cpu_ctx_free -∗
    (* --- and what main's arm then wants of this hart --- *)
    (∀ mf : regfile,
       sie_cap_gpr mf K_main false zero_reg -∗
       cpu_own 0 false zero_reg cpu_ctx_free false -∗
       ghost_var sie_gname (1/4) ('b"0" : mword 1) -∗
       main_hart_raw (register_lookup tlb rs) -∗
       pc_is (mword_of_int KernelSyms.main) -∗
       WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hreset Hmie0 Hmdl0.
    iIntros "Hmm Hpmpc Hpmpa Hpc Hfile Hmh Hmepc Hsatp Hmede Hmdl Hmie Hmenv
             Hmcen Hstc Htlb Hstvec Hsepc Hscause Hstval #Htext Hgot Hstk
             Hbit Hbit2 Hg2 Hg4a Hg4b Hnoff Hint Hproc Hctx Hcont".
    pose proof (fin_to_nat_lt cpu_id) as Hn.
    (* the two persistent halves of the config bundle, kept for the bridge *)
    iDestruct (mmode_config_persist with "Hmm") as "[[#Hhw #Hmin] Hmm]".
    (* [wp_entry_boot]'s premises live at the LET-BOUND sp0, i.e. at the
       computed register value; §1's facts are at [mword_of_int (sp_of n)]. *)
    assert (Hsp : m_jal (boot_regfile rs) v_stack0
                    (boot_w64 (Z.of_nat (fin_to_nat cpu_id))) !!! Regidx csp_rs1
                  = (mword_of_int (sp_of (fin_to_nat cpu_id)) : mword 64))
      by exact (sp0_val (boot_regfile rs) (fin_to_nat cpu_id) Hn).
    iEval (rewrite -Hsp) in "Hstk".
    assert (Hra : uint (ti_ea_ra (ti_sp1 (m_jal (boot_regfile rs) v_stack0
                    (boot_w64 (Z.of_nat (fin_to_nat cpu_id))) !!! Regidx csp_rs1)))
                  + 8 <= 0xfffffffffffffc)
      by (rewrite Hsp; exact (ti_ea_ra_bound _ Hn)).
    assert (Hs0b : uint (ti_ea_s0 (ti_sp1 (m_jal (boot_regfile rs) v_stack0
                     (boot_w64 (Z.of_nat (fin_to_nat cpu_id))) !!! Regidx csp_rs1)))
                   + 8 <= 0xfffffffffffffc)
      by (rewrite Hsp; exact (ti_ea_s0_bound _ Hn)).
    iApply (Entry.wp_entry_boot Φ (boot_regfile rs) v_stack0
              (boot_w64 (Z.of_nat (fin_to_nat cpu_id)))
              (register_lookup mepc rs) (register_lookup satp rs)
              (register_lookup medeleg rs) (register_lookup mideleg rs)
              (register_lookup mie rs) (boot_w64 0)
              (register_lookup stimecmp rs) (register_lookup mcounteren rs)
              pmpcfg_boot (register_lookup pmpaddr_n rs) boot_stack_depth
              boot_stack_depth_entry pmp_all_off_pmpcfg_boot menvcfg_boot_lpe
              Hra Hs0b
              with "Hmm Hpmpc Hpmpa Hpc Hfile Hmh Hmepc Hsatp Hmede Hmdl Hmie
                    Hmenv Hmcen Hstc Hgot Hstk Htext").
    iIntros (tv ms0 HoIE HoPRV HoSXL HoKF)
      "Hhs Hpriv Hmst Hpmpc Hpmpa Hpc Hfile Hmh Hmepc Hsatp Hmede Hmdl Hmie
       Hmenv Hmcen Hstc Hgot Hstk".
    (* the five CSR side conditions, from the post's own fact bundle *)
    destruct (boot_csrs_from_kf ms0 (boot_w64 0) (register_lookup mie rs)
                (register_lookup mideleg rs) (register_lookup satp rs)
                HoKF eq_refl Hmie0 Hmdl0)
      as (Hsie & Hmsf & Hmenvl & Hmiez & Hsatpm).
    (* back to §1's form of sp0, in BOTH resources the bridge takes at it:
       the stack slice and the register file ([st_mout ... sp0 ...]). *)
    iEval (rewrite Hsp) in "Hstk".
    iEval (rewrite Hsp) in "Hfile".
    (* the two stack-location bounds: [sp0_uint] rewrites only at ITS OWN
       elaboration of [uint]'s width index, so the facts are asserted here at
       §1's form and handed to the bridge by [exact] (conversion sees through
       [Z_idx 64] vs [64%N] where [rewrite] does not). *)
    assert (Hlo : text_end + 8 * Z.of_nat (boot_stack_slots K_main)
                  <= uint (mword_of_int (sp_of (fin_to_nat cpu_id)) : mword 64))
      by (rewrite (sp0_uint _ Hn); exact (sp_of_lo _ Hn)).
    assert (Hhi : uint (mword_of_int (sp_of (fin_to_nat cpu_id)) : mword 64)
                  <= ram_base + ram_size)
      by (rewrite (sp0_uint _ Hn); exact (sp_of_hi _ Hn)).
    iMod (boot_bridge K_main boot_stack_depth
              (m_jal (boot_regfile rs) v_stack0
                 (boot_w64 (Z.of_nat (fin_to_nat cpu_id))))
              (mword_of_int (sp_of (fin_to_nat cpu_id))) ms0
              (register_lookup satp rs) (register_lookup mideleg rs)
              (register_lookup mie rs) (boot_w64 0) tv
              (boot_w64 (Z.of_nat (fin_to_nat cpu_id)))
              (register_lookup mcounteren rs) pmpcfg_boot
              (register_lookup pmpaddr_n rs) (register_lookup tlb rs)
              (noff_val 0) iv zero_reg
              pmp_all_off_pmpcfg_boot Hsie Hmsf Hmenvl Hmiez Hsatpm
              ltac:(exact (st_tpv_of_nat _ Hn))
              boot_stack_depth_bridge
              Hlo Hhi
              eq_refl
              with "Hhw Hmin Hhs Hpriv Hmst Hpmpc Hpmpa Hfile Hsatp Hmdl Hmie
                    Hmenv Hstk Hbit Hbit2 Hg2 Hg4a Hg4b Htlb Hsepc Hscause
                    Hstval Hstvec Hnoff Hint Hproc Hctx")
      as (mf) "(Hcap & Hcpu & Hg & Hraw)".
    iApply ("Hcont" $! mf with "Hcap Hcpu Hg Hraw Hpc").
  Qed.

End BootRun.
