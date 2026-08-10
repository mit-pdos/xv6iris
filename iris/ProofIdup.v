(* ProofIdup.v -- idup(), proven instruction by instruction.

   idup is filedup's twin: the same 32-byte ra/s0/s1 frame, the same
   acquire / [ref++] / release, the same [c.mv a0,s1] return.  It is four
   bytes shorter because it has NO panic arm -- xv6 checks [f->ref < 1] in
   filedup and does not check [ip->ref < 1] here -- so the offsets after the
   load run four below filedup's.  [ProofFiledup.v] is the template and the
   two should be read together.

   THE ONE STRUCTURAL DIFFERENCE, and it is the whole point of the file:
   filedup's [f->ref] cell comes out of the FTABLE LOCK's resource, so its
   load and store are ordinary leaves.  idup's [ip->ref] cell lives in
   [IcacheInv.itable_inv] instead -- it has to, because ilock and iunlock
   read it holding no lock at all -- so both memory steps are ATOMIC-UPDATE
   leaves that open the invariant around exactly one instruction.

   That the read-modify-write is nevertheless atomic IN THE PROOF is not an
   accident of the leaves: idup holds itable.lock across all three
   instructions, and the lock's resource holds HALF the authority, so no
   other thread can move [M] between the [lw] and the [sw].  The two halves
   meet only inside the store's invariant opening -- [iref_dup_store_au] --
   which is exactly the moment the physical word changes.

   THE INCREMENT'S SAFETY comes from outside the algebra: [iref_slot], one
   unit of [IrefSlots]' fixed supply, is what proves the incremented count
   is still an [int].  See [IrefSlots.v]'s header for why no axiom may do
   that job instead.                                                       *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import RiscvFetchExec.
Require Import MemAccessGen.
Require Import RegFile.
Require Import InstrBytes.
Require Import HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import MinstretInv.
Require Import KptGhost.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import InodeInv.
Require Import DiskPtsto.
Require Import FsBlocks LogInv FsCrash.
Require Import DinodeEnc.
Require Import InodeLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import CodeIdup.
Require Import SpecPanic.
Require Import SpecAcquire SpecRelease.
Require Import SpecIdup.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  The two mask-carrying width-4 leaves.                                 *)
(*                                                                        *)
(*  Identical to [ProofBreadParts]' [wp_lw_au_s_sconf] / [wp_sw_au_s_sconf]*)
(*  -- restated rather than imported because those live in a section that  *)
(*  fixes [bioG]/[diskGhostG], and idup has no business carrying the bio   *)
(*  layer's ghost state to get at a two-line wrapper.                      *)
(* ===================================================================== *)

Section IdupAuLeaves.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {p : mword 64}.

  Lemma wp_lw_au_idup (cmp : bool)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (av : nat) (Ψ : mword 32 -> iProp Σ) (Em : coPset) (b : bool)
      {dqm : dfrac} :
    uint rd <> 0 ->
    rd_ok rd ->
    ↑kptN ⊆ Em ->
    sie_cap_gpr m av b p -∗
    pc_is pc -∗
    instr pc cmp (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    (|={⊤ ∖ ↑minstretN, Em}=> ∃ v : mword 32,
       add_vec (rget m rs1) (sign_extend' 64 imm) ↦₄{dqm} v ∗
       (add_vec (rget m rs1) (sign_extend' 64 imm) ↦₄{dqm} v
          ={Em, ⊤ ∖ ↑minstretN}=∗ Ψ v)) -∗
    ( ∀ v : mword 32,
      wp_next b p (fun (CID : CpuId) =>
        sie_cap_gpr (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) av b p -∗
        pc_is (add_vec_int pc (if cmp then 2 else 4)) -∗
        Ψ v -∗
        WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hrd Hrdok HkptEm.
    iIntros "Hcg Hpc Hinstr HAU Hcont".
    iApply (wp_load_s_sconf_au 4 cmp false pc rd rs1 imm m av
              (fun w => sign_extend' 64 w) Ψ Em b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 1024; reflexivity)
              ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_4 data2_ext_4 Hrd Hrdok HkptEm
              with "Hcg Hpc Hinstr HAU Hcont").
  Qed.

  Lemma wp_sw_au_idup (cmp : bool)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : regfile) (av : nat) (Ψ : iProp Σ) (Em : coPset) (b : bool) :
    ↑kptN ⊆ Em ->
    sie_cap_gpr m av b p -∗
    pc_is pc -∗
    instr pc cmp (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
    (|={⊤ ∖ ↑minstretN, Em}=> ∃ vold : mword 32,
       add_vec (rget m rs1) (sign_extend' 64 imm) ↦₄ vold ∗
       (add_vec (rget m rs1) (sign_extend' 64 imm)
          ↦₄ (trunc32 (rget m rs2)) ={Em, ⊤ ∖ ↑minstretN}=∗ Ψ)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m av b p -∗
      pc_is (add_vec_int pc (if cmp then 2 else 4)) -∗
      Ψ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intro HkptEm.
    iIntros "Hcg Hpc Hinstr HAU Hcont".
    iApply (wp_store_s_sconf_au 4 cmp pc rs2 rs1 imm m av
              (trunc32 (rget m rs2)) Ψ Em b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 1024; reflexivity)
              ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_4 (store_ext_4 (rget m rs2)) HkptEm
              with "Hcg Hpc Hinstr HAU Hcont").
  Qed.

End IdupAuLeaves.

Module IdupProof (Acquire : ACQUIRE) (Release : RELEASE) : IDUP.

Section ProofIdup.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !icacheG Σ, !irefslotG Σ,
            !diskGhostG Σ, !fsLogG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation Rra  := (mword_of_int 1 : mword 5).
  Notation Rs0  := (mword_of_int 8 : mword 5).
  Notation Rs1  := (mword_of_int 9 : mword 5).
  Notation Ra0  := (mword_of_int 10 : mword 5).
  Notation Ra5  := (mword_of_int 15 : mword 5).

  Local Ltac regne :=
    first [ congruence
          | apply not_eq_sym; apply is_cs_idx_true_neq;
            [vm_compute; reflexivity | assumption]
          | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption] ].

  (* [ProofFiledup.sie_b_agree], verbatim: [b] and [n]/[eb] are two
     presentations of the same SIE state, and the ghost eighth they share
     pins the relationship.  Read once at entry, it is what lets release's
     derived exit index equal idup's own (symmetric) [b]. *)
  Local Lemma sie_b_agree (m : regfile) (n K0 : nat) (eb b : bool) (p : mword 64) (C : iProp Σ) :
    sie_cap_gpr m K0 b p -∗ cpu_own n eb p C b -∗
    ⌜ b = match n with O => eb | S _ => false end ⌝.
  Proof.
    iIntros "Hcg Hcnt". destruct b.
    - iDestruct "Hcnt" as "[%Hb _]". destruct Hb as [-> ->]. done.
    - destruct n as [|n']; [ | done ].
      iDestruct "Hcnt" as "[[_ Hint] _]".
      iDestruct "Hcg" as "(_ & _ & (_ & _ & Harm) & _)".
      iDestruct (ghost_var_agree with "Harm Hint") as %Heq.
      destruct eb; [ exfalso | done ].
      apply (f_equal (@bv_unsigned _)) in Heq. vm_compute in Heq. discriminate.
  Qed.

  Lemma wp_idup_sconf
      (γl : gname) (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (nib : nat)
      (k : nat) (q : Qp) (dev inum : mword 32)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (K : nat) (b : bool)
    : wp_idup_sconf_body γl cn γfs γi cov logstart nib k q dev inum
                         m n eb p C K b.
  Proof.
    cbv beta delta [wp_idup_sconf_body].
    intros pcE ret_tgt HK HnZ Ha0.
    unfold K_idup in HK.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt #Htext Hpc #Hlock #Hinv #Hpanic Hislot Href Hcont".
    iDestruct (sie_b_agree m n K eb b p C with "Hcg Hcnt") as %Houtb.
    set (spr := add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iPoseProof (idi_00 with "Htext") as "Hi00".
    iPoseProof (idi_02 with "Htext") as "Hi02".
    iPoseProof (idi_04 with "Htext") as "Hi04".
    iPoseProof (idi_06 with "Htext") as "Hi06".
    iPoseProof (idi_08 with "Htext") as "Hi08".
    iPoseProof (idi_0a with "Htext") as "Hi0a".
    iPoseProof (idi_0c with "Htext") as "Hi0c".
    iPoseProof (idi_10 with "Htext") as "Hi10".
    iPoseProof (idi_14 with "Htext") as "Hi14".
    (* ===== PROLOGUE (generic [b]) -- filedup's, offset for offset ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m K 4 b
              ltac:(lia) Hpush with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (vr24) "Hr24". iDestruct "S2" as (vr16) "Hr16".
    iDestruct "S3" as (vr8)  "Hr8".  iDestruct "S4" as (vg4)  "Hg4".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".  iEval (rewrite -Hb4) in "Hg4".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.idup + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.idup + 0x02)) (mword_of_int 3 : mword 6) Rra
              R1 (K - 4)%nat vr24 b with "Hcg Hpc Hi02 Hr24 [-]").
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    iEval (rgne) in "Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.idup + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.idup + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.idup + 0x04)) (mword_of_int 2 : mword 6) Rs0
              R1 (K - 4)%nat vr16 b with "Hcg Hpc Hi04 Hr16 [-]").
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    iEval (rgne) in "Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.idup + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.idup + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.idup + 0x06)) (mword_of_int 1 : mword 6) Rs1
              R1 (K - 4)%nat vr8 b with "Hcg Hpc Hi06 Hr8 [-]").
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    iEval (rgne) in "Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.idup + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.idup + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.idup + 0x08)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 R1 (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.idup + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.idup + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.mv s1,a0 : the cursor register takes the argument *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.idup + 0x0a)) Rs1 Ra0
              R2 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R3 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (R2 !!! Regidx Ra0))]> R2).
    assert (HR3s1 : R3 !!! Regidx Rs1 = ientry k).
    { rewrite /R3 upd_eq. rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite Ha0. apply add_vec_zero_l. }
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.idup + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.idup + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c/+0x10 a0 := &itable  (both auipc/addi pairs resolve to the
       symbol itself: the spinlock is struct itable's first member) *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.idup + 0x0c)) Ra0 (mword_of_int 29 : mword 20)
              R3 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c [-]").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (R4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.idup + 0x0c) : mword 64)
                     (auipc_off (mword_of_int 29 : mword 20)))]> R3).
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.idup + 0x0c) : mword 64) 4 = mword_of_int (KernelSyms.idup + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.idup + 0x10)) Ra0 Ra0 (mword_of_int 1726 : mword 12)
              R4 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10 [-]").
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (R4 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 1726 : mword 12)))]> R4).
    assert (HR5a0 : R5 !!! Regidx Ra0 = itable_lock).
    { rewrite /R5 upd_eq /R4 upd_eq. rewrite /itable_lock.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.idup + 0x10) : mword 64) 4 = mword_of_int (KernelSyms.idup + 0x14))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* ===== +0x14 jal ra,acquire ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.idup + 0x14)) Rra (mword_of_int 2087502 : mword 21)
              R5 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi14 [-]").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (mA := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.idup + 0x14) : mword 64) 4)]> R5).
    assert (Htgtacq : add_vec (mword_of_int (KernelSyms.idup + 0x14) : mword 64)
                        (sign_extend' 64 (mword_of_int 2087502 : mword 21))
                      = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtacq) in "Hpc".
    assert (HmAsp : mA !!! Regidx csp_rs1 = spr).
    { rewrite /mA upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      exact HspR1. }
    assert (HmAa0 : mA !!! Regidx Ra0 = itable_lock).
    { rewrite /mA upd_ne; [| vm_compute; discriminate]. exact HR5a0. }
    assert (HmAs1 : mA !!! Regidx Rs1 = ientry k).
    { rewrite /mA upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate]. exact HR3s1. }
    assert (HmAra : mA !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.idup + 0x14) : mword 64) 4)
      by (rewrite /mA; apply upd_eq).
    iDestruct (cpu_own_transport CID CID9 n eb p C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Acquire.wp_acquire_sconf γl "itable"%string (itable_res2 cn γfs γi cov logstart nib dev) mA
              n eb p C (K - 4)%nat b
              HnZ ltac:(lia)
              with "Hcg Hcnt Htext Hpc [Hlock] Hpanic [-]").
    { iEval (rewrite HmAa0). iExact "Hlock". }
    iIntros (CIDacq Hsacq ms macq) "%Hmsfacts Hcg Hpc %Hacqpins Htok HRres Hcnt Hpay".
    assert (Hpc18 : ret_pc (mA !!! Regidx Rra) = mword_of_int (KernelSyms.idup + 0x18)).
    { rewrite HmAra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc18) in "Hpc".
    pose proof Hacqpins as Hacqpins_cs.
    assert (Hmsp : macq !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hacqpins_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HmAsp).
    assert (Hms1 : macq !!! Regidx Rs1 = ientry k)
      by (rewrite (callee_saved_lookup Hacqpins_cs (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HmAs1).
    (* ===== the critical section (literal [false], no hart threading) ===== *)
    iDestruct "HRres" as (M ci) "(Hhalf & %Hwf & %Hciwf & Hiauth & Hslots & Hpool)".
    iDestruct "Href" as "[Hrtok Hrident]".
    iDestruct (iref_lookup with "Hhalf Hrtok") as %(qt & cnt & HMk & Hqt & _ & _).
    assert (Hk : (k < NINODE)%nat) by (apply (proj1 Hwf); by eexists).
    (* [ci] records exactly the LIVE slots (§13.9's restored [dom ci = dom
       M]), so the slot's identity values are readable off [ci !! k] -- which
       is what makes [islot2]'s mismatched arms unreachable. *)
    assert (Hcik : exists di : mword 32 * mword 32, ci !! k = Some di).
    { destruct Hciwf as [Hdom _].
      assert (Hin : k ∈ dom ci)
        by (rewrite Hdom; apply elem_of_dom; by eexists).
      apply elem_of_dom in Hin. exact Hin. }
    destruct Hcik as [[cdev cinum] Hcik].
    iDestruct (islots2_acc_upd cn M ci k Hk with "Hslots") as "[Hslot Hback]".
    iEval (rewrite /islot2 HMk Hcik) in "Hslot".
    iDestruct "Hslot" as "(Hrest & Hiu & Hgid)".
    (* the iref-slot conservation law: the caller's unit plus the ones the
       table already holds for this entry are within the fixed supply, so the
       count is safely below what an int holds -- before AND after. *)
    iDestruct (iref_slots_combine with "Hiu Hislot") as "Hiu".
    assert (Hsucc : (Pos.to_nat cnt + 1)%nat = Pos.to_nat (Pos.succ cnt))
      by (rewrite Pos2Nat.inj_succ; lia).
    iEval (rewrite Hsucc) in "Hiu".
    iDestruct (iref_slots_no_overflow with "Hiauth Hiu") as %[Hno _].
    iPoseProof (idi_18 with "Htext") as "Hi18".
    iPoseProof (idi_1a with "Htext") as "Hi1a".
    iPoseProof (idi_1c with "Htext") as "Hi1c".
    iPoseProof (idi_1e with "Htext") as "Hi1e".
    iPoseProof (idi_22 with "Htext") as "Hi22".
    iPoseProof (idi_26 with "Htext") as "Hi26".
    iPoseProof (idi_2a with "Htext") as "Hi2a".
    assert (Hiw : iref_word M k = (mword_of_int (Z.pos cnt) : mword 32))
      by (rewrite /iref_word HMk; reflexivity).
    (* +0x18 c.lw a5,8(s1) -- ATOMIC-UPDATE read: the ref word is in
       [itable_inv], not in the lock's resource. *)
    assert (Hpa : add_vec (rget macq Rs1) (sign_extend' 64 (mword_of_int 8 : mword 12))
                  = i_ref (ientry k)).
    { rewrite (rget_ne macq Rs1 ltac:(vm_compute; discriminate)) Hms1. reflexivity. }
    iApply (wp_lw_au_idup true (mword_of_int (KernelSyms.idup + 0x18)) Ra5 Rs1
              (mword_of_int 8 : mword 12) macq (K - 4)%nat
              (fun v => (⌜v = iref_word M k⌝ ∗ itable_half (icn_ref cn) M)%I)
              (⊤ ∖ ↑minstretN ∖ ↑icacheN) false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(solve_ndisj)
              with "Hcg Hpc Hi18 [Hhalf] [-]").
    { rewrite Hpa.
      iMod (iref_load_locked_au (⊤ ∖ ↑minstretN) (icn_ref cn) M k ltac:(solve_ndisj) Hk
              with "Hinv Hhalf") as "[Hcell Hback]".
      iModIntro. iExists (iref_word M k). iFrame "Hcell". iIntros "Hcell".
      iMod ("Hback" with "Hcell") as "Hhalf". iModIntro. by iFrame. }
    iIntros (vld).
    iApply wp_next_off_intro. iIntros "Hcg Hpc [%Hvld Hhalf]".
    subst vld. iEval (rewrite Hiw) in "Hcg".
    set (D1 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.pos cnt) : mword 32))]> macq).
    assert (HD1a5 : D1 !!! Regidx Ra5 = sign_extend' 64 (mword_of_int (Z.pos cnt) : mword 32))
      by (rewrite /D1; apply upd_eq).
    assert (HD1s1 : D1 !!! Regidx Rs1 = ientry k)
      by (rewrite /D1 upd_ne; [exact Hms1 | vm_compute; discriminate]).
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.idup + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.idup + 0x1a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a c.addiw a5,a5,1 -- NO panic arm here, unlike filedup *)
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.idup + 0x1a)) Ra5 (mword_of_int 1 : mword 6)
              D1 (K - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D2 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (subrange_vec_dec
                     (add_vec (D1 !!! Regidx Ra5)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> D1).
    assert (HD2s1 : D2 !!! Regidx Rs1 = ientry k)
      by (rewrite /D2 upd_ne; [exact HD1s1 | vm_compute; discriminate]).
    (* the stored word IS the successor count -- the [c.addiw] arithmetic *)
    assert (Hstv : trunc32 (rget D2 Ra5) = (mword_of_int (Z.pos (Pos.succ cnt)) : mword 32)).
    { rewrite (rget_ne D2 Ra5 ltac:(vm_compute; discriminate)).
      rewrite /D2 upd_eq. unfold regval_into_reg. rewrite HD1a5.
      rewrite (moi32_storeval_succ (Z.pos cnt) ltac:(lia)
                 ltac:(pose proof Hno as Hx; rewrite Pos2Z.inj_succ in Hx; lia)).
      f_equal. rewrite Pos2Z.inj_succ. lia. }
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.idup + 0x1a) : mword 64) 2 = mword_of_int (KernelSyms.idup + 0x1c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* +0x1c c.sw a5,8(s1) : ip->ref = ref+1.  The ghost step rides along
       inside the SAME invariant opening -- that is the atomicity. *)
    assert (Hpa2 : add_vec (rget D2 Rs1) (sign_extend' 64 (mword_of_int 8 : mword 12))
                   = i_ref (ientry k)).
    { rewrite (rget_ne D2 Rs1 ltac:(vm_compute; discriminate)) HD2s1. reflexivity. }
    iApply (wp_sw_au_idup true (mword_of_int (KernelSyms.idup + 0x1c)) Ra5 Rs1
              (mword_of_int 8 : mword 12) D2 (K - 4)%nat
              (itable_half (icn_ref cn) (<[k := (qt, Pos.succ cnt)]> M) ∗
               iref_tok (icn_ref cn) k (q/2)%Qp ∗ iref_tok (icn_ref cn) k (q/2)%Qp)%I
              (⊤ ∖ ↑minstretN ∖ ↑icacheN) false
              ltac:(solve_ndisj)
              with "Hcg Hpc Hi1c [Hhalf Hrtok] [-]").
    { rewrite Hpa2 Hstv.
      iMod (iref_dup_store_au (⊤ ∖ ↑minstretN) (icn_ref cn) M k q qt cnt
              ltac:(solve_ndisj) HMk Hno with "Hinv Hhalf Hrtok") as "[Hcell Hback]".
      iModIntro. iExists (iref_word M k). iFrame "Hcell". iIntros "Hcell".
      iMod ("Hback" with "Hcell") as "(Hhalf & Ht1 & Ht2)". iModIntro. iFrame. }
    iApply wp_next_off_intro. iIntros "Hcg Hpc (Hhalf & Ht1 & Ht2)".
    (* rebuild the lock's resource at the new map *)
    iDestruct (inode_ident_split k (q/2) (q/2) dev inum) as "[Hsplit _]".
    iEval (rewrite Qp.div_2) in "Hsplit".
    iDestruct ("Hsplit" with "Hrident") as "[Hid1 Hid2]".
    iDestruct ("Hback" $! (<[k := (qt, Pos.succ cnt)]> M) ci
                 with "[%] [%] [Hrest Hiu Hgid]") as "Hslots".
    { intros j Hj. rewrite lookup_insert_ne; [reflexivity | by apply not_eq_sym]. }
    { intros j Hj. reflexivity. }
    { rewrite /islot2 lookup_insert Hcik. iFrame "Hrest Hiu Hgid". }
    iAssert (itable_res2 cn γfs γi cov logstart nib dev) with "[Hhalf Hiauth Hslots Hpool]" as "HRres".
    { iExists (<[k := (qt, Pos.succ cnt)]> M), ci. iFrame "Hhalf Hiauth Hpool".
      iSplitR; [| iSplitR; [| iExact "Hslots"]].
      2:{ (* [ci] did not move, and [M]'s domain did not either: the slot was
             already live, so §13.2/§13.9/§13.11's four clauses are
             preserved -- including the single-device one, which is about
             [ci] alone and so is literally the hypothesis. *)
        iPureIntro. destruct Hciwf as (Hdom & Hinj & Hrange & Hdev).
        split_and!; [| exact Hinj | exact Hrange | exact Hdev].
        rewrite dom_insert_L Hdom.
        assert (Hkin : k ∈ dom M) by (apply elem_of_dom; by eexists).
        set_solver. }
      iPureIntro. destruct Hwf as [Hdom Hcnt'].  split.
      - intros j Hj. destruct (decide (j = k)) as [->|Hne]; [exact Hk|].
        rewrite lookup_insert_ne in Hj; [|by apply not_eq_sym]. by apply Hdom.
      - intros j qj nj Hj. destruct (decide (j = k)) as [->|Hne].
        + rewrite lookup_insert in Hj. apply Some_inj in Hj.
          injection Hj as _ Hn. subst nj. exact Hno.
        + rewrite lookup_insert_ne in Hj; [|by apply not_eq_sym].
          by apply (Hcnt' j qj). }
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.idup + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.idup + 0x1e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e/+0x22 a0 := &itable ; +0x26 jal release *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.idup + 0x1e)) Ra0 (mword_of_int 29 : mword 20)
              D2 (K - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (D3 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.idup + 0x1e) : mword 64)
                     (auipc_off (mword_of_int 29 : mword 20)))]> D2).
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.idup + 0x1e) : mword 64) 4 = mword_of_int (KernelSyms.idup + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.idup + 0x22)) Ra0 Ra0 (mword_of_int 1708 : mword 12)
              D3 (K - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (D3 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 1708 : mword 12)))]> D3).
    assert (HD4a0 : D4 !!! Regidx Ra0 = itable_lock).
    { rewrite /D4 upd_eq /D3 upd_eq. rewrite /itable_lock.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.idup + 0x22) : mword 64) 4 = mword_of_int (KernelSyms.idup + 0x26))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.idup + 0x26)) Rra (mword_of_int 2087620 : mword 21)
              D4 (K - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi26 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (D5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.idup + 0x26) : mword 64) 4)]> D4).
    assert (Htgtrel : add_vec (mword_of_int (KernelSyms.idup + 0x26) : mword 64)
                        (sign_extend' 64 (mword_of_int 2087620 : mword 21))
                      = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtrel) in "Hpc".
    assert (HD5a0 : D5 !!! Regidx Ra0 = itable_lock)
      by (rewrite /D5 upd_ne; [exact HD4a0 | vm_compute; discriminate]).
    assert (HD5thr : forall c : mword 5, is_cs_idx c = true -> c <> mword_of_int 9 ->
                       D5 !!! Regidx c = macq !!! Regidx c).
    { intros c Hcs Hne.
      rewrite /D5 upd_ne; [| regne].
      rewrite /D4 upd_ne; [| regne].
      rewrite /D3 upd_ne; [| regne].
      rewrite /D2 upd_ne; [| regne].
      rewrite /D1 upd_ne; [reflexivity | regne]. }
    assert (HD5sp : D5 !!! Regidx csp_rs1 = spr)
      by (rewrite (HD5thr csp_rs1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)); exact Hmsp).
    assert (HD5s1 : D5 !!! Regidx Rs1 = ientry k).
    { rewrite /D5 upd_ne; [| vm_compute; discriminate].
      rewrite /D4 upd_ne; [| vm_compute; discriminate].
      rewrite /D3 upd_ne; [| vm_compute; discriminate]. exact HD2s1. }
    assert (HD5ra : D5 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.idup + 0x26) : mword 64) 4)
      by (rewrite /D5; apply upd_eq).
    iApply (Release.wp_release_sconf γl itable_lock "itable"%string (itable_res2 cn γfs γi cov logstart nib dev) D5
              n eb p C (K - 4)%nat
              ltac:(rewrite HD5a0; reflexivity)
              ltac:(lia)
              with "Hcg Htext Hpc [Hlock] Htok HRres Hcnt Hpay [-]").
    { iExact "Hlock". }
    iIntros (CIDr Hsr mr) "Hcg Hpc %Hrelpins Hcnt".
    iEval (rewrite <- Houtb) in "Hcg". iEval (rewrite <- Houtb) in "Hcnt".
    rewrite <- Houtb in Hsr.
    pose proof Hrelpins as Hrelpins_cs.
    assert (Hpc2a : ret_pc (D5 !!! Regidx Rra) = mword_of_int (KernelSyms.idup + 0x2a)).
    { rewrite HD5ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc2a) in "Hpc".
    (* ===== EPILOGUE (generic [b], via [Houtb]) ===== *)
    iPoseProof (idi_2c with "Htext") as "Hi2c".
    iPoseProof (idi_2e with "Htext") as "Hi2e".
    iPoseProof (idi_30 with "Htext") as "Hi30".
    iPoseProof (idi_32 with "Htext") as "Hi32".
    iPoseProof (idi_34 with "Htext") as "Hi34".
    assert (Hmrsp : mr !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hrelpins_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HD5sp).
    assert (Hmrs1 : mr !!! Regidx Rs1 = ientry k)
      by (rewrite (callee_saved_lookup Hrelpins_cs (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HD5s1).
    (* +0x2a c.mv a0,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.idup + 0x2a)) Ra0 Rs1
              mr (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2a [-]").
    iIntros (CIDe1 Hse1) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (P1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mr !!! Regidx Rs1))]> mr).
    assert (HP1sp : P1 !!! Regidx csp_rs1 = spr)
      by (rewrite /P1 upd_ne; [exact Hmrsp | vm_compute; discriminate]).
    assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.idup + 0x2a) : mword 64) 2 = mword_of_int (KernelSyms.idup + 0x2c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    iEval (rewrite HspR1) in "Hr24". iEval (rewrite HspR1) in "Hr16".
    iEval (rewrite HspR1) in "Hr8".  iEval (rewrite HspR1) in "Hg4".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.idup + 0x2c)) (mword_of_int 3 : mword 6) Rra
              P1 (K - 4)%nat (R1 !!! Regidx Rra) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2c [Hr24] [-]").
    { iEval (rewrite HP1sp). iExact "Hr24". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hr24".
    iEval (rewrite HP1sp) in "Hr24".
    set (P2 := <[Regidx Rra := regval_into_reg (R1 !!! Regidx Rra)]> P1).
    assert (HP2sp : P2 !!! Regidx csp_rs1 = spr)
      by (rewrite /P2 upd_ne; [exact HP1sp | vm_compute; discriminate]).
    assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.idup + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.idup + 0x2e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.idup + 0x2e)) (mword_of_int 2 : mword 6) Rs0
              P2 (K - 4)%nat (R1 !!! Regidx Rs0) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2e [Hr16] [-]").
    { iEval (rewrite HP2sp). iExact "Hr16". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hr16".
    iEval (rewrite HP2sp) in "Hr16".
    set (P3 := <[Regidx Rs0 := regval_into_reg (R1 !!! Regidx Rs0)]> P2).
    assert (HP3sp : P3 !!! Regidx csp_rs1 = spr)
      by (rewrite /P3 upd_ne; [exact HP2sp | vm_compute; discriminate]).
    assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.idup + 0x2e) : mword 64) 2 = mword_of_int (KernelSyms.idup + 0x30))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.idup + 0x30)) (mword_of_int 1 : mword 6) Rs1
              P3 (K - 4)%nat (R1 !!! Regidx Rs1) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi30 [Hr8] [-]").
    { iEval (rewrite HP3sp). iExact "Hr8". }
    iIntros (CIDe4 Hse4) "Hcg Hpc Hr8".
    iEval (rewrite HP3sp) in "Hr8".
    set (P4 := <[Regidx Rs1 := regval_into_reg (R1 !!! Regidx Rs1)]> P3).
    assert (HP4sp : P4 !!! Regidx csp_rs1 = spr)
      by (rewrite /P4 upd_ne; [exact HP3sp | vm_compute; discriminate]).
    assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.idup + 0x30) : mword 64) 2 = mword_of_int (KernelSyms.idup + 0x32))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    set (P5 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P4 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P4).
    assert (Hwv : add_vec (P4 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HP4sp. unfold spr, sp0. apply frame_cancel_32. }
    assert (Hpop : P4 !!! Regidx csp_rs1
                   = pa_stk (add_vec (P4 !!! Regidx csp_rs1)
                               (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HP4sp. unfold spr, sp0, pa_stk, add_vec_int.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hg4]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24"; [iEval (rewrite -Hb1 HspR1); iExists _; iExact "Hr24"|].
      iSplitL "Hr16"; [iEval (rewrite -Hb2 HspR1); iExists _; iExact "Hr16"|].
      iSplitL "Hr8";  [iEval (rewrite -Hb3 HspR1); iExists _; iExact "Hr8"|].
      iSplitL "Hg4";  [iEval (rewrite -Hb4 HspR1); iExists _; iExact "Hg4"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.idup + 0x32)) (mword_of_int 2 : mword 6)
              P4 (K - 4)%nat 4 b Hpop with "Hcg Hpc Hi32 Hframe4 [-]").
    iIntros (CIDe5 Hse5) "Hcg Hpc".
    assert (Hnk : ((K - 4) + 4)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg
      (add_vec (P4 !!! Regidx csp_rs1)
         (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P4) with P5.
    assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.idup + 0x32) : mword 64) 2 = mword_of_int (KernelSyms.idup + 0x34))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp34) in "Hpc".
    assert (HP5ra : P5 !!! Regidx Rra = m !!! Regidx Rra).
    { rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HP5a0 : P5 !!! Regidx Ra0 = ientry k).
    { rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_ne; [| vm_compute; discriminate].
      rewrite /P1 upd_eq. rewrite Hmrs1. apply add_vec_zero_l. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.idup + 0x34)) Rra P5 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi34 [-]").
    iIntros (CIDe6 Hse6) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (P5 !!! Regidx Rra) = ret_tgt) by (rewrite HP5ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    iDestruct (cpu_own_transport CIDr CIDe6 n eb p C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CIDe6 with "[]"); [ iPureIntro; wp_next_chain | ].
    iApply ("Hcont" $! P5 with "Hcg Hcnt Hpc [%] [Ht1 Hid1] [Ht2 Hid2]").
    3:{ rewrite /inode_ref. iFrame "Ht2 Hid2". }
    2:{ rewrite /inode_ref. iFrame "Ht1 Hid1". }
    (* callee_saved m P5, and a0 = ip *)
    split; [| exact HP5a0].
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> mword_of_int 8 -> c <> mword_of_int 9 ->
              c <> mword_of_int 1 -> c <> mword_of_int 10 ->
              P5 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N1 N10.
      rewrite /P5 upd_ne; [| regne].
      rewrite /P4 upd_ne; [| regne].
      rewrite /P3 upd_ne; [| regne].
      rewrite /P2 upd_ne; [| regne].
      rewrite /P1 upd_ne; [| regne].
      rewrite (callee_saved_lookup Hrelpins_cs c Hcs).
      rewrite (HD5thr c Hcs N9).
      rewrite (callee_saved_lookup Hacqpins_cs c Hcs).
      rewrite /mA upd_ne; [| regne].
      rewrite /R5 upd_ne; [| regne].
      rewrite /R4 upd_ne; [| regne].
      rewrite /R3 upd_ne; [| regne].
      rewrite /R2 upd_ne; [| regne].
      rewrite /R1 upd_ne; [reflexivity | regne]. }
    unfold callee_saved.
    assert (Hc2 : P5 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1).
    { rewrite /P5 upd_eq. rewrite HP4sp. unfold regval_into_reg, spr, sp0.
      apply frame_cancel_32. }
    assert (Hc8 : P5 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5)).
    { rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (Hc9 : P5 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5)).
    { rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    repeat split;
      first [ exact Hc2 | exact Hc8 | exact Hc9
            | apply Hthread; vm_compute; first [reflexivity | discriminate] ].
  Qed.

End ProofIdup.

End IdupProof.
