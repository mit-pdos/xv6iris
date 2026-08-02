(* ProofVmfault.v -- vmfault() over the SIE-agnostic sconf world.

   THE HART IS EXPLICIT AND [b] IS GENERIC.  vmfault is called both with
   interrupts on (usertrap) and inside copyin/copyout, so its contract is
   [b]-generic: every leaf hands the continuation back at a FRESH hart, and
   the shared epilogue [EPI] is itself a [wp_next (CID0 := CID) b (fun CIDe
   => ...)] -- ProofPipealloc.v's shape.  [cpu_own] is hart-indexed and only
   the four cpu_own-taking callees refresh it, so it is re-anchored with
   [cpu_own_transport] before each of those calls and at each of the five
   epilogue entry points.  The per-instruction hart binders are named after
   the pc offset the resumed hart executes ([C02], [C1cB], ...).

     uint64 vmfault(pagetable_t pagetable, uint64 va, int read) {
       struct proc *p = myproc();
       if (va >= p->sz) return 0;
       va = PGROUNDDOWN(va);
       if (ismapped(pagetable, va)) return 0;
       mem = (uint64)kalloc();            if (mem == 0) return 0;
       memset(mem, 0, PGSIZE);
       if (mappages(p->pagetable, va, PGSIZE, mem, PTE_W|PTE_U|PTE_R) != 0) {
         kfree(mem); return 0;
       }
       return mem;
     }

   Spec of record: SpecVmfault.v -- stated at the [proc_pt] altitude, so the
   whole proof is bracketed by ProcPtOwn's three dovetail lemmas
   ([proc_pt_acc_rep0] to open the table into the exact [pt_rep0] view walk /
   mappages consume, [proc_pt_rebuild] on every failure arm, [proc_pt_grow] on
   the success arm).

   TWO STRUCTURAL POINTS.

   1. THE SHRINK-WRAPPED FRAME.  All six slots of the 48-byte frame are pushed
      at +0x00 (ra/s0/s2/s3 are stored right away; slots 3 and 6 -- s1/s4 --
      only at +0x2a/+0x2c, past the [va < p->sz] test).  So the epilogue's
      [iAssert]ed continuation ([EPI], taken before the first branch) OWNS the
      four always-saved cells and takes the two shrink-wrapped ones as an
      EXISTENTIAL wand argument: the short arm hands back the junk the push
      produced, each long arm the values it has just reloaded s1/s4 from.

   2. THE FIVE-WAY JOIN at +0x1c ([mv a0,s3] then the pop).  Every exit sets s3
      to its return value, so [EPI] is parameterized by (the register file at
      +0x1c, the return value [res], the post's disjunct at [res]).  Its
      register premise is exactly what the pop cannot restore: sp = spr, s3 =
      res, and agreement with [mm] on every callee-saved register other than
      sp/s0/s2/s3 (which the epilogue reloads).  s1/s4 fall under that clause --
      the long paths reloaded them, the short path never touched them.

   The base (4-byte) [RTYPE AND] leaf this proof needs -- [wp_and_s_sconf],
   with rd <> rs1, which the compressed [c.and rd,rd,rs2] form cannot
   express -- lives in WpSconfAlu.v next to [wp_cand_s_sconf]. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore.
Require Import InstrBytes.
Require Import WpMmodeLeafBase.
Require Import RegFile HartTp WpNext.
Require Import CalleeSaved StackOwn.
Require Import IntrDefs WpSmodeIntr.
Require Import WpLock.
Require Import KallocInv.
Require Import PtTree PtBuild.
Require Import UserPtTree.
Require Import ProcGeom CpuOwn.
Require Import KvmSpec.
Require Import ProcPt ProcPtOwn.
Require Import WpVmfaultDecode.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import SpecMyproc SpecIsmapped SpecKalloc SpecMemsetPage SpecMappages SpecKfree.
Require Import SpecVmfault.
Require Import KernelRvcDecode.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* proc_pt-altitude goals are enormous; without this a one-line mistake in the
   whole-function WP prints for tens of minutes instead of erroring.  See
   claude-notes/durable-notes.md, "a failing tactic looks like a hang". *)
Set Printing Depth 40.

(* ===================================================================== *)
(* Pure bridges.                                                          *)
(* ===================================================================== *)

(* a kalloc page is page-aligned, in mappages' [subrange] spelling *)
Lemma vf_page_align12 (r : mword 64) :
  page_valid r -> subrange_vec_dec r 11 0 = (zeros' 12 : mword 12).
Proof.
  intros [Hal _]. unfold page_aligned, PGSIZE in Hal. rewrite uint_unsigned in Hal.
  assert (Hand : and_vec r (mword_of_int (-4096)) = r).
  { apply bv_eq. rewrite pgd_unsigned. rewrite Hal. apply Z.sub_0_r. }
  rewrite <- Hand. apply pgrounddown_low12.
Qed.

(* mappages' one-page run post IS the vmfault leaf insert *)
(* the [perm := 22] instance of [ProcPtOwn.uvm_run1] *)
Lemma vf_run1 (m_ad : gmap (mword 27) (mword 64)) (vpn0 : mword 27) (r : mword 64) :
  pt_insert_run m_ad vpn0 (autocast (T := mword) (subrange_vec_dec r 55 12) : mword 44) 22 1
  = <[vpn0 := vmfault_pte r]> m_ad.
Proof. exact (uvm_run1 m_ad vpn0 22 r). Qed.

(* the [mword]-free arithmetic (the zify-hook rule: keep [bv_unsigned] out of
   any goal [lia] must see) *)
Lemma vf_z_lt_maxva (x : Z) : x + 4096 <= 274877906944 -> x < 274877906944.
Proof. lia. Qed.
Lemma vf_z_run_va (x b : Z) : x + 4096 <= b -> x + Z.of_nat 1 * 4096 <= b.
Proof. lia. Qed.
Lemma vf_z_run_pa (x : Z) : x < 2281701376 -> x + Z.of_nat 1 * 4096 < 72057594037927936.
Proof. lia. Qed.

(* ===================================================================== *)
(* THE WHOLE FUNCTION.                                                    *)
(* ===================================================================== *)

Module VmfaultProof (Myproc : MYPROC) (Ismapped : ISMAPPED) (Kalloc : KALLOC)
                    (MemsetPage : MEMSETPAGE) (Mappages : MAPPAGES) (Kfree : KFREE)
  : VMFAULT.

Section ProofVmfault.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{CID : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rtp := (mword_of_int 4 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).

  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  (* peel via the upd_eq/upd_ne LEMMAS, one layer at a time (values stay
     opaque): optimization.md's [peel_reg].  No closing tactic, so the caller
     finishes with [reflexivity] / [exact H] / [apply ...]. *)
  Ltac peel_reg_step :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ].

  Lemma wp_vmfault_sconf
      (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile)
      (P : uptd) (szv : mword 64) (K lvl : nat) (eb : bool) (p : mword 64)
      (C : iProp Σ) (dqs dqp : dfrac) (b : bool)
    : wp_vmfault_sconf_body γa Φ mm P szv K lvl eb p C dqs dqp b.
  Proof.
    cbv beta delta [wp_vmfault_sconf_body].
    intros pcE va va0 ret_tgt HK Htp Hroot Hszb Hlvl.
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt #Htext Hpc Hszc Hptc Hpt Henv Hcont".
    iDestruct "Henv" as (γk) "(#Hlock & #Havail & #Hpanic)".
    set (spr := add_vec (mm !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))).
    (* the two struct-proc cell addresses, in the [ld] displacement shape *)
    assert (Hpsza : add_vec p (sign_extend' 64 (mword_of_int 72 : mword 12)) = p_sz p)
      by reflexivity.
    assert (Hppta : add_vec p (sign_extend' 64 (mword_of_int 80 : mword 12)) = p_pagetable p)
      by reflexivity.

    (* ===== PROLOGUE: 6-slot frame; ra/s0/s2/s3 saved now ============== *)
    iPoseProof (vfi_00 with "Htext") as "Hi00".
    iPoseProof (vfi_02 with "Htext") as "Hi02".
    iPoseProof (vfi_04 with "Htext") as "Hi04".
    iPoseProof (vfi_06 with "Htext") as "Hi06".
    iPoseProof (vfi_08 with "Htext") as "Hi08".
    iPoseProof (vfi_0a with "Htext") as "Hi0a".
    iPoseProof (vfi_0c with "Htext") as "Hi0c".
    iPoseProof (vfi_0e with "Htext") as "Hi0e".
    iPoseProof (vfi_10 with "Htext") as "Hi10".
    iPoseProof (vfi_14 with "Htext") as "Hi14".
    iPoseProof (vfi_16 with "Htext") as "Hi16".
    assert (Hspm : mm !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))
                    = pa_stk (mm !!! Regidx csp_rs1) 6).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi16sp_push_s_sconf Φ pcE (mword_of_int 61 : mword 6) mm K 6 b
              ltac:(lia) Hpush with "Hcg Hpc Hi00 [-]").
    iIntros (C02 Hs02) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (mm !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> mm).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> mm) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & _)".
    iDestruct "S1" as (u40) "Hk1". iDestruct "S2" as (u32) "Hk2".
    iDestruct "S3" as (u24) "Hk3". iDestruct "S4" as (u16) "Hk4".
    iDestruct "S5" as (u8)  "Hk5". iDestruct "S6" as (u0)  "Hk6".
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 3).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk sp0 4).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk sp0 5).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk sp0 6).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hsprstk : pa_stk sp0 6 = spr).
    { rewrite /pa_stk /spr /sp0 /add_vec_int. f_equal;
        try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (VF + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,40(sp) *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (VF + 0x02)) (mword_of_int 5 : mword 6) Rra
              R1 (K - 6)%nat u40 b with "Hcg Hpc Hi02 [Hk1] [-]").
    { iEval (rewrite HspR1 Hb1). iExact "Hk1". }
    iIntros (C04 Hs04) "Hcg Hpc Hk1".
    iEval (rgne) in "Hk1".
    iEval (rewrite HspR1 Hb1) in "Hk1".
    assert (HR1ra : R1 !!! Regidx Rra = mm !!! Regidx Rra)
      by (rewrite /R1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HR1ra) in "Hk1".
    assert (Hpp04 : add_vec_int (mword_of_int (VF + 0x02) : mword 64) 2 = mword_of_int (VF + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,32(sp) *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (VF + 0x04)) (mword_of_int 4 : mword 6) Rs0
              R1 (K - 6)%nat u32 b with "Hcg Hpc Hi04 [Hk2] [-]").
    { iEval (rewrite HspR1 Hb2). iExact "Hk2". }
    iIntros (C06 Hs06) "Hcg Hpc Hk2".
    iEval (rgne) in "Hk2".
    iEval (rewrite HspR1 Hb2) in "Hk2".
    assert (HR1s0 : R1 !!! Regidx Rs0 = mm !!! Regidx Rs0)
      by (rewrite /R1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HR1s0) in "Hk2".
    assert (Hpp06 : add_vec_int (mword_of_int (VF + 0x04) : mword 64) 2 = mword_of_int (VF + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s2,16(sp) *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (VF + 0x06)) (mword_of_int 2 : mword 6) Rs2
              R1 (K - 6)%nat u16 b with "Hcg Hpc Hi06 [Hk4] [-]").
    { iEval (rewrite HspR1 Hb4). iExact "Hk4". }
    iIntros (C08 Hs08) "Hcg Hpc Hk4".
    iEval (rgne) in "Hk4".
    iEval (rewrite HspR1 Hb4) in "Hk4".
    assert (HR1s2 : R1 !!! Regidx Rs2 = mm !!! Regidx Rs2)
      by (rewrite /R1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HR1s2) in "Hk4".
    assert (Hpp08 : add_vec_int (mword_of_int (VF + 0x06) : mword 64) 2 = mword_of_int (VF + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp s3,8(sp) *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (VF + 0x08)) (mword_of_int 1 : mword 6) Rs3
              R1 (K - 6)%nat u8 b with "Hcg Hpc Hi08 [Hk5] [-]").
    { iEval (rewrite HspR1 Hb5). iExact "Hk5". }
    iIntros (C0a Hs0a) "Hcg Hpc Hk5".
    iEval (rgne) in "Hk5".
    iEval (rewrite HspR1 Hb5) in "Hk5".
    assert (HR1s3 : R1 !!! Regidx Rs3 = mm !!! Regidx Rs3)
      by (rewrite /R1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HR1s3) in "Hk5".
    assert (Hpp0a : add_vec_int (mword_of_int (VF + 0x08) : mword 64) 2 = mword_of_int (VF + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.addi4spn s0,sp,48 *)
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (VF + 0x0a)) (Cregidx (mword_of_int 0))
              (mword_of_int 12 : mword 8) Rs0 R1 (K - 6)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok)
              with "Hcg Hpc Hi0a [-]").
    iIntros (C0c Hs0c) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> R1).
    assert (Hpp0c : add_vec_int (mword_of_int (VF + 0x0a) : mword 64) 2 = mword_of_int (VF + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c c.mv s3,a0   (s3 := pagetable) *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (VF + 0x0c)) Rs3 Ra0
              R2 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c [-]").
    iIntros (C0e Hs0e) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R3 := <[Regidx Rs3 := regval_into_reg (add_vec zero_reg (R2 !!! Regidx Ra0))]> R2).
    assert (HR3s3 : R3 !!! Regidx Rs3 = page_base P.(ud_root)).
    { rewrite /R3 upd_eq. rewrite add_vec_zero_l.
      rewrite /R2. rewrite upd_ne; [| reg_neq].
      rewrite /R1. rewrite upd_ne; [| reg_neq]. exact Hroot. }
    assert (Hpp0e : add_vec_int (mword_of_int (VF + 0x0c) : mword 64) 2 = mword_of_int (VF + 0x0e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e c.mv s2,a1   (s2 := va) *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (VF + 0x0e)) Rs2 Ra1
              R3 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e [-]").
    iIntros (C10 Hs10) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R4 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (R3 !!! Regidx Ra1))]> R3).
    assert (HR4s2 : R4 !!! Regidx Rs2 = va).
    { rewrite /R4 upd_eq. rewrite add_vec_zero_l.
      rewrite /R3. rewrite upd_ne; [| reg_neq].
      rewrite /R2. rewrite upd_ne; [| reg_neq].
      rewrite /R1. rewrite upd_ne; [reflexivity | reg_neq]. }
    assert (HR4s3 : R4 !!! Regidx Rs3 = page_base P.(ud_root))
      by (rewrite /R4; rewrite upd_ne; [exact HR3s3 | reg_neq]).
    assert (HR4sp : R4 !!! Regidx csp_rs1 = spr).
    { rewrite /R4 /R3 /R2.
      repeat (rewrite upd_ne; [| reg_neq]). exact HspR1. }
    assert (Hpp10 : add_vec_int (mword_of_int (VF + 0x0e) : mword 64) 2 = mword_of_int (VF + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 jal ra,myproc *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (VF + 0x10)) Rra (mword_of_int 852 : mword 21)
              R4 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi10 [-]").
    iIntros (Cmpe Hsmpe) "Hcg Hpc".
    set (R5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (VF + 0x10) : mword 64) 4)]> R4).
    assert (Htgtmp : add_vec (mword_of_int (VF + 0x10) : mword 64)
                       (sign_extend' 64 (mword_of_int 852 : mword 21))
                     = mword_of_int KernelSyms.myproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtmp) in "Hpc".
    assert (HR5sp : R5 !!! Regidx csp_rs1 = spr)
      by (rewrite /R5; rewrite upd_ne; [exact HR4sp | reg_neq]).
    assert (HR5s2 : R5 !!! Regidx Rs2 = va)
      by (rewrite /R5; rewrite upd_ne; [exact HR4s2 | reg_neq]).
    assert (HR5s3 : R5 !!! Regidx Rs3 = page_base P.(ud_root))
      by (rewrite /R5; rewrite upd_ne; [exact HR4s3 | reg_neq]).
    assert (HR5ra : R5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (VF + 0x10) : mword 64) 4)
      by (rewrite /R5 upd_eq; reflexivity).
    (* the callee-saved registers R5 shares with mm: everything but sp/s0/s2/s3 *)
    assert (HR5thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs2 -> c <> Rs3 ->
              R5 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H18 H19.
      rewrite /R5. rewrite upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /R4. rewrite upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H18; reflexivity].
      rewrite /R3. rewrite upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H19; reflexivity].
      rewrite /R2. rewrite upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H8; reflexivity].
      rewrite /R1. rewrite upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H2; reflexivity].
      reflexivity. }
    (* ---- myproc() ---- *)
    iDestruct (cpu_own_transport CID Cmpe lvl eb p C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Myproc.wp_myproc_sconf Φ R5 (K - 6)%nat lvl eb p C b
              Hlvl ltac:(lia)
              with "Hcg Hcnt Htext Hpc").
    iIntros (Cmy Hsmy msM mf) "%HmsM Hcg Hcnt Hpc %Hmp".
    destruct Hmp as (Hmpcs & Hmpa0).
    assert (Hret14 : ret_pc (R5 !!! Regidx Rra) = mword_of_int (VF + 0x14)).
    { rewrite HR5ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret14) in "Hpc".
    assert (Hmfsp : mf !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hmpcs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HR5sp. }
    assert (Hmfs2 : mf !!! Regidx Rs2 = va).
    { rewrite (callee_saved_lookup Hmpcs Rs2 ltac:(vm_compute; reflexivity)).
      exact HR5s2. }
    assert (Hmfs3 : mf !!! Regidx Rs3 = page_base P.(ud_root)).
    { rewrite (callee_saved_lookup Hmpcs Rs3 ltac:(vm_compute; reflexivity)).
      exact HR5s3. }
    assert (Hmfthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs2 -> c <> Rs3 ->
              mf !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H18 H19.
      rewrite (callee_saved_lookup Hmpcs c Hc). apply HR5thr; assumption. }
    (* ---- +0x14 c.ld a5,72(a0) : the p->sz read ---- *)
    iEval (rewrite cshape_653c) in "Hi14".
    assert (Hrgmfa0 : rget mf Ra0 = p) by (rgne; exact Hmpa0).
    iApply (wp_cld_s_sconf Φ (mword_of_int (VF + 0x14)) Ra5 Ra0
              (mword_of_int 72 : mword 12) mf (K - 6)%nat szv b (dqm:=dqs)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [Hszc] [-]").
    { iEval (rewrite Hrgmfa0 Hpsza). iExact "Hszc". }
    iIntros (C16 Hs16) "Hcg Hpc Hszc".
    iEval (rewrite Hrgmfa0 Hpsza) in "Hszc".
    set (M1 := <[Regidx Ra5 := regval_into_reg szv]> mf).
    assert (HM1a5 : M1 !!! Regidx Ra5 = szv) by (rewrite /M1 upd_eq; reflexivity).
    assert (HM1s2 : M1 !!! Regidx Rs2 = va)
      by (rewrite /M1; rewrite upd_ne; [exact Hmfs2 | reg_neq]).
    assert (HM1s3 : M1 !!! Regidx Rs3 = page_base P.(ud_root))
      by (rewrite /M1; rewrite upd_ne; [exact Hmfs3 | reg_neq]).
    assert (HM1sp : M1 !!! Regidx csp_rs1 = spr)
      by (rewrite /M1; rewrite upd_ne; [exact Hmfsp | reg_neq]).
    assert (HM1a0 : M1 !!! Regidx Ra0 = p)
      by (rewrite /M1; rewrite upd_ne; [exact Hmpa0 | reg_neq]).
    assert (HM1thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs2 -> c <> Rs3 ->
              M1 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H18 H19.
      rewrite /M1. rewrite upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      apply Hmfthr; assumption. }
    assert (Hpp16 : add_vec_int (mword_of_int (VF + 0x14) : mword 64) 2
                    = mword_of_int (VF + 0x16))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".

    (* ================================================================= *)
    (*  THE EPILOGUE / JOIN at +0x1c, taken before the first branch.      *)
    (* ================================================================= *)
    iPoseProof (vfi_1c with "Htext") as "Hi1c".
    iPoseProof (vfi_1e with "Htext") as "Hi1e".
    iPoseProof (vfi_20 with "Htext") as "Hi20".
    iPoseProof (vfi_22 with "Htext") as "Hi22".
    iPoseProof (vfi_24 with "Htext") as "Hi24".
    iPoseProof (vfi_26 with "Htext") as "Hi26".
    iPoseProof (vfi_28 with "Htext") as "Hi28".
    set (PAY := (fun res : mword 64 =>
      ((⌜res = mword_of_int 0⌝ ∗ proc_pt P)
       ∨ (∃ r : mword 64,
            ⌜res = r⌝ ∗ ⌜page_valid r⌝ ∗ ⌜(uint va < uint szv)%Z⌝ ∗
            ⌜P.(ud_um) !! svpn_of va0 = None⌝ ∗
            proc_pt (uptd_insert P (svpn_of va0) r)))%I)).
    set (EPI := (wp_next (CID0 := CID) b (fun (CIDe : CpuId) =>
        ∀ (mj : regfile) (res : mword 64),
        ⌜ mj !!! Regidx csp_rs1 = spr
          /\ mj !!! Regidx Rs3 = res
          /\ (forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs2 -> c <> Rs3 ->
                mj !!! Regidx c = mm !!! Regidx c) ⌝ -∗
        sie_cap_gpr mj (K - 6)%nat b p -∗
        cpu_own lvl eb p C b -∗
        pc_is (mword_of_int (VF + 0x1c) : mword 64) -∗
        (∃ w3 w6 : mword 64, pa_stk sp0 3 ↦₈ w3 ∗ pa_stk sp0 6 ↦₈ w6) -∗
        p_pagetable p ↦₈{dqp} page_base P.(ud_root) -∗
        PAY res -∗
        WP (Loop : expr riscv_lang) {{ Φ }}))%I).
    iAssert EPI with "[Hcont Hszc Hk1 Hk2 Hk4 Hk5]" as "Hepi".
    { rewrite /EPI.
      iIntros (CIDe Hbe mj res) "(%Hjsp & %Hjs3 & %Hjthr) Hcg Hcnt Hpc Hjunk Hptc Hpost".
      iDestruct "Hjunk" as (w3 w6) "[Hk3 Hk6]".
      (* +0x1c c.mv a0,s3 *)
      iApply (wp_cmv_s_sconf Φ (mword_of_int (VF + 0x1c)) Ra0 Rs3
                mj (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi1c [-]").
      iIntros (E1e Hse1e) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (E0 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mj !!! Regidx Rs3))]> mj).
      assert (HE0sp : E0 !!! Regidx csp_rs1 = spr)
        by (rewrite /E0; rewrite upd_ne; [exact Hjsp | reg_neq]).
      assert (Hpp1e : add_vec_int (mword_of_int (VF + 0x1c) : mword 64) 2
                      = mword_of_int (VF + 0x1e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1e) in "Hpc".
      (* +0x1e c.ldsp ra,40(sp) *)
      iApply (wp_cldsp_s_sconf Φ (mword_of_int (VF + 0x1e)) (mword_of_int 5 : mword 6) Rra
                E0 (K - 6)%nat (mm !!! Regidx Rra) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi1e [Hk1] [-]").
      { iEval (rewrite HE0sp Hb1). iExact "Hk1". }
      iIntros (E20 Hse20) "Hcg Hpc Hk1". iEval (rewrite HE0sp Hb1) in "Hk1".
      set (E1 := <[Regidx Rra := regval_into_reg (mm !!! Regidx Rra)]> E0).
      assert (HE1sp : E1 !!! Regidx csp_rs1 = spr)
        by (rewrite /E1; rewrite upd_ne; [exact HE0sp | reg_neq]).
      assert (Hpp20 : add_vec_int (mword_of_int (VF + 0x1e) : mword 64) 2
                      = mword_of_int (VF + 0x20))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp20) in "Hpc".
      (* +0x20 c.ldsp s0,32(sp) *)
      iApply (wp_cldsp_s_sconf Φ (mword_of_int (VF + 0x20)) (mword_of_int 4 : mword 6) Rs0
                E1 (K - 6)%nat (mm !!! Regidx Rs0) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi20 [Hk2] [-]").
      { iEval (rewrite HE1sp Hb2). iExact "Hk2". }
      iIntros (E22 Hse22) "Hcg Hpc Hk2". iEval (rewrite HE1sp Hb2) in "Hk2".
      set (E2 := <[Regidx Rs0 := regval_into_reg (mm !!! Regidx Rs0)]> E1).
      assert (HE2sp : E2 !!! Regidx csp_rs1 = spr)
        by (rewrite /E2; rewrite upd_ne; [exact HE1sp | reg_neq]).
      assert (Hpp22 : add_vec_int (mword_of_int (VF + 0x20) : mword 64) 2
                      = mword_of_int (VF + 0x22))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp22) in "Hpc".
      (* +0x22 c.ldsp s2,16(sp) *)
      iApply (wp_cldsp_s_sconf Φ (mword_of_int (VF + 0x22)) (mword_of_int 2 : mword 6) Rs2
                E2 (K - 6)%nat (mm !!! Regidx Rs2) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi22 [Hk4] [-]").
      { iEval (rewrite HE2sp Hb4). iExact "Hk4". }
      iIntros (E24 Hse24) "Hcg Hpc Hk4". iEval (rewrite HE2sp Hb4) in "Hk4".
      set (E3 := <[Regidx Rs2 := regval_into_reg (mm !!! Regidx Rs2)]> E2).
      assert (HE3sp : E3 !!! Regidx csp_rs1 = spr)
        by (rewrite /E3; rewrite upd_ne; [exact HE2sp | reg_neq]).
      assert (Hpp24 : add_vec_int (mword_of_int (VF + 0x22) : mword 64) 2
                      = mword_of_int (VF + 0x24))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp24) in "Hpc".
      (* +0x24 c.ldsp s3,8(sp) *)
      iApply (wp_cldsp_s_sconf Φ (mword_of_int (VF + 0x24)) (mword_of_int 1 : mword 6) Rs3
                E3 (K - 6)%nat (mm !!! Regidx Rs3) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi24 [Hk5] [-]").
      { iEval (rewrite HE3sp Hb5). iExact "Hk5". }
      iIntros (E26 Hse26) "Hcg Hpc Hk5". iEval (rewrite HE3sp Hb5) in "Hk5".
      set (E4 := <[Regidx Rs3 := regval_into_reg (mm !!! Regidx Rs3)]> E3).
      assert (HE4sp : E4 !!! Regidx csp_rs1 = spr)
        by (rewrite /E4; rewrite upd_ne; [exact HE3sp | reg_neq]).
      assert (Hpp26 : add_vec_int (mword_of_int (VF + 0x24) : mword 64) 2
                      = mword_of_int (VF + 0x26))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp26) in "Hpc".
      (* +0x26 c.addi16sp sp,48 -- trade the frame back *)
      set (E5 := <[Regidx csp_rs1 := regval_into_reg
                    (add_vec (E4 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E4).
      assert (Hwv : add_vec (E4 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0).
      { rewrite HE4sp. unfold spr, sp0. apply frame_cancel_48. }
      assert (Hpop : E4 !!! Regidx csp_rs1
                     = pa_stk (add_vec (E4 !!! Regidx csp_rs1)
                                 (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6).
      { rewrite Hwv HE4sp. symmetry. exact Hsprstk. }
      iAssert (stack_own sp0 6) with "[Hk1 Hk2 Hk3 Hk4 Hk5 Hk6]" as "Hframe6".
      { rewrite stack_own_slots. cbn [seq].
        iSplitL "Hk1"; [iExists _; iExact "Hk1" |].
        iSplitL "Hk2"; [iExists _; iExact "Hk2" |].
        iSplitL "Hk3"; [iExists _; iExact "Hk3" |].
        iSplitL "Hk4"; [iExists _; iExact "Hk4" |].
        iSplitL "Hk5"; [iExists _; iExact "Hk5" |].
        iSplitL "Hk6"; [iExists _; iExact "Hk6" |].
        done. }
      iEval (rewrite -Hwv) in "Hframe6".
      iApply (wp_caddi16sp_pop_s_sconf Φ (mword_of_int (VF + 0x26))
                (mword_of_int 3 : mword 6) E4 (K - 6)%nat 6 b Hpop
                with "Hcg Hpc Hi26 Hframe6 [-]").
      iIntros (E28 Hse28) "Hcg Hpc".
      change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E4 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E4) with E5.
      assert (Hnk : ((K - 6) + 6)%nat = K) by lia.
      iEval (rewrite Hnk) in "Hcg".
      assert (Hpp28 : add_vec_int (mword_of_int (VF + 0x26) : mword 64) 2
                      = mword_of_int (VF + 0x28))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp28) in "Hpc".
      (* +0x28 c.ret *)
      assert (HE5ra : E5 !!! Regidx Rra = mm !!! Regidx Rra).
      { rewrite /E5. rewrite upd_ne; [| reg_neq].
        rewrite /E4. rewrite upd_ne; [| reg_neq].
        rewrite /E3. rewrite upd_ne; [| reg_neq].
        rewrite /E2. rewrite upd_ne; [| reg_neq].
        rewrite /E1 upd_eq. reflexivity. }
      assert (HE5a0 : E5 !!! Regidx Ra0 = res).
      { rewrite /E5. rewrite upd_ne; [| reg_neq].
        rewrite /E4. rewrite upd_ne; [| reg_neq].
        rewrite /E3. rewrite upd_ne; [| reg_neq].
        rewrite /E2. rewrite upd_ne; [| reg_neq].
        rewrite /E1. rewrite upd_ne; [| reg_neq].
        rewrite /E0 upd_eq. rewrite add_vec_zero_l. exact Hjs3. }
      assert (HE5thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs2 -> c <> Rs3 ->
                E5 !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H18 H19.
        rewrite /E5. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; apply H2; reflexivity].
        rewrite /E4. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; apply H19; reflexivity].
        rewrite /E3. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; apply H18; reflexivity].
        rewrite /E2. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; apply H8; reflexivity].
        rewrite /E1. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
        rewrite /E0. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
        apply Hjthr; assumption. }
      iApply (wp_cret_s_sconf Φ (mword_of_int (VF + 0x28)) Rra E5 K b
                ltac:(vm_compute; discriminate) with "Hcg Hpc Hi28 [-]").
      iIntros (Eret Hseret) "Hcg Hpc". iEval (rgne) in "Hpc".
      assert (Hretf : ret_pc (E5 !!! Regidx Rra) = ret_tgt) by (rewrite HE5ra; reflexivity).
      iEval (rewrite Hretf) in "Hpc".
      iDestruct (cpu_own_transport CIDe Eret lvl eb p C b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("Hcont" $! Eret with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! E5 with "Hcg Hcnt Hpc Hszc Hptc [%] [Hpost]").
      2:{ rewrite /PAY. rewrite HE5a0.
          iDestruct "Hpost" as "[(%Hz & Hp) | Hs]".
          - iLeft. iSplitR; [iPureIntro; exact Hz | iExact "Hp"].
          - iRight. iExact "Hs". }
      { unfold callee_saved.
        assert (Hc2 : E5 !!! Regidx csp_rs1 = mm !!! Regidx csp_rs1).
        { rewrite /E5 upd_eq. exact Hwv. }
        assert (Hc8 : E5 !!! Regidx Rs0 = mm !!! Regidx Rs0).
        { rewrite /E5. rewrite upd_ne; [| reg_neq].
          rewrite /E4. rewrite upd_ne; [| reg_neq].
          rewrite /E3. rewrite upd_ne; [| reg_neq].
          rewrite /E2 upd_eq. reflexivity. }
        assert (Hc18 : E5 !!! Regidx Rs2 = mm !!! Regidx Rs2).
        { rewrite /E5. rewrite upd_ne; [| reg_neq].
          rewrite /E4. rewrite upd_ne; [| reg_neq].
          rewrite /E3 upd_eq. reflexivity. }
        assert (Hc19 : E5 !!! Regidx Rs3 = mm !!! Regidx Rs3).
        { rewrite /E5. rewrite upd_ne; [| reg_neq].
          rewrite /E4 upd_eq. reflexivity. }
        split_and!;
          first [ exact Hc2 | exact Hc8 | exact Hc18 | exact Hc19
                | apply HE5thr; vm_compute; first [reflexivity | discriminate] ]. } }

    (* ================================================================= *)
    (*  +0x16 bltu s2,a5 : the [va < p->sz] test.                        *)
    (* ================================================================= *)
    assert (Hrg1s2 : rget M1 Rs2 = M1 !!! Regidx Rs2) by (rgne; reflexivity).
    assert (Hrg1a5 : rget M1 Ra5 = M1 !!! Regidx Ra5) by (rgne; reflexivity).
    destruct (zopz0zI_u (rget M1 Rs2) (rget M1 Ra5)) eqn:Hcmp.
    2:{ (* ---- va >= p->sz: fall to +0x1a, return 0 ---- *)
      iPoseProof (vfi_1a with "Htext") as "Hi1a".
      iApply (wp_bltu_fall_s_sconf Φ (mword_of_int (VF + 0x16))
                (mword_of_int 20 : mword 13) Ra5 Rs2 M1 (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hcmp
                with "Hcg Hpc Hi16 [-]").
      iIntros (C1a Hs1a) "Hcg Hpc".
      assert (Hpp1a : add_vec_int (mword_of_int (VF + 0x16) : mword 64) 4
                      = mword_of_int (VF + 0x1a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1a) in "Hpc".
      (* +0x1a c.li s3,0 *)
      iApply (wp_cli_s_sconf Φ (mword_of_int (VF + 0x1a)) Rs3 (mword_of_int 0 : mword 6)
                (mword_of_int 0 : mword 64) M1 (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi1a [-]").
      iIntros (C1c Hs1c) "Hcg Hpc".
      set (Z1 := <[Regidx Rs3 := regval_into_reg (mword_of_int 0 : mword 64)]> M1).
      assert (Hpp1c : add_vec_int (mword_of_int (VF + 0x1a) : mword 64) 2
                      = mword_of_int (VF + 0x1c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1c) in "Hpc".
      iDestruct (cpu_own_transport Cmy C1c lvl eb p C b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("Hepi" $! C1c with "[%]"); [wp_next_chain|].
      iApply ("Hepi" $! Z1 (mword_of_int 0) with "[%] Hcg Hcnt Hpc [Hk3 Hk6] Hptc [Hpt]").
      { split_and!.
        - rewrite /Z1. rewrite upd_ne; [exact HM1sp | reg_neq].
        - rewrite /Z1 upd_eq. reflexivity.
        - intros c Hc H2 H8 H18 H19.
          rewrite /Z1. rewrite upd_ne;
            [| intros Hx; injection Hx as Hx2; subst c; apply H19; reflexivity].
          apply HM1thr; assumption. }
      { iExists u24, u0. iFrame "Hk3 Hk6". }
      { rewrite /PAY. iLeft. iSplitR; [iPureIntro; reflexivity | iExact "Hpt"]. } }

    (* ---- va < p->sz: the real work ---- *)
    assert (Hvalt : (uint va < uint szv)%Z).
    { rewrite -HM1s2 -HM1a5 -Hrg1s2 -Hrg1a5. unfold zopz0zI_u in Hcmp.
      apply Z.ltb_lt. exact Hcmp. }
    assert (Hvab : (uint va < 2 ^ 38)%Z)
      by (eapply Z.lt_le_trans; [exact Hvalt | exact Hszb]).
    pose proof (pgrounddown_bound va Hvab) as Hva0b4.
    change (2 ^ 38)%Z with 274877906944%Z in Hva0b4.
    assert (Hva0b : (uint va0 < 2 ^ 38)%Z).
    { change (2 ^ 38)%Z with 274877906944%Z. exact (vf_z_lt_maxva _ Hva0b4). }
    iPoseProof (vfi_2a with "Htext") as "Hi2a".
    iPoseProof (vfi_2c with "Htext") as "Hi2c".
    iPoseProof (vfi_2e with "Htext") as "Hi2e".
    iPoseProof (vfi_30 with "Htext") as "Hi30".
    iPoseProof (vfi_32 with "Htext") as "Hi32".
    iPoseProof (vfi_36 with "Htext") as "Hi36".
    iPoseProof (vfi_38 with "Htext") as "Hi38".
    iPoseProof (vfi_3a with "Htext") as "Hi3a".
    iApply (wp_bltu_taken_s_sconf Φ (mword_of_int (VF + 0x16))
              (mword_of_int 20 : mword 13) Ra5 Rs2 M1 (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hcmp
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi16 [-]").
    iApply bi.later_intro. iIntros (C2a Hs2a) "Hcg Hpc".
    assert (Htgt2a : add_vec (mword_of_int (VF + 0x16) : mword 64)
                       (sign_extend' 64 (mword_of_int 20 : mword 13))
                     = mword_of_int (VF + 0x2a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt2a) in "Hpc".
    (* +0x2a c.sdsp s1,24(sp) *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (VF + 0x2a)) (mword_of_int 3 : mword 6) Rs1
              M1 (K - 6)%nat u24 b with "Hcg Hpc Hi2a [Hk3] [-]").
    { iEval (rewrite HM1sp Hb3). iExact "Hk3". }
    iIntros (C2c Hs2c) "Hcg Hpc Hk3".
    iEval (rgne) in "Hk3".
    iEval (rewrite HM1sp Hb3) in "Hk3".
    assert (HM1s1 : M1 !!! Regidx Rs1 = mm !!! Regidx Rs1)
      by (apply HM1thr; vm_compute; first [reflexivity | discriminate]).
    iEval (rewrite HM1s1) in "Hk3".
    assert (Hpp2c : add_vec_int (mword_of_int (VF + 0x2a) : mword 64) 2
                    = mword_of_int (VF + 0x2c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    (* +0x2c c.sdsp s4,0(sp) *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (VF + 0x2c)) (mword_of_int 0 : mword 6) Rs4
              M1 (K - 6)%nat u0 b with "Hcg Hpc Hi2c [Hk6] [-]").
    { iEval (rewrite HM1sp Hb6). iExact "Hk6". }
    iIntros (C2e Hs2e) "Hcg Hpc Hk6".
    iEval (rgne) in "Hk6".
    iEval (rewrite HM1sp Hb6) in "Hk6".
    assert (HM1s4 : M1 !!! Regidx Rs4 = mm !!! Regidx Rs4)
      by (apply HM1thr; vm_compute; first [reflexivity | discriminate]).
    iEval (rewrite HM1s4) in "Hk6".
    assert (Hpp2e : add_vec_int (mword_of_int (VF + 0x2c) : mword 64) 2
                    = mword_of_int (VF + 0x2e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    (* +0x2e c.mv s1,a0   (s1 := p) *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (VF + 0x2e)) Rs1 Ra0
              M1 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2e [-]").
    iIntros (C30 Hs30) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (L1 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (M1 !!! Regidx Ra0))]> M1).
    assert (HL1s1 : L1 !!! Regidx Rs1 = p)
      by (rewrite /L1 upd_eq; rewrite add_vec_zero_l; exact HM1a0).
    assert (Hpp30 : add_vec_int (mword_of_int (VF + 0x2e) : mword 64) 2
                    = mword_of_int (VF + 0x30))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* +0x30 c.lui a5,0xfffff *)
    iApply (wp_clui_s_sconf Φ (mword_of_int (VF + 0x30)) Ra5
              (sign_extend' 20 (mword_of_int 63 : mword 6)) (mword_of_int (-4096) : mword 64)
              L1 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              lui_m4096
              with "Hcg Hpc Hi30 [-]").
    iIntros (C32 Hs32) "Hcg Hpc".
    set (L2 := <[Regidx Ra5 := regval_into_reg (mword_of_int (-4096) : mword 64)]> L1).
    assert (Hpp32 : add_vec_int (mword_of_int (VF + 0x30) : mword 64) 2
                    = mword_of_int (VF + 0x32))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    (* +0x32 and s4,s2,a5   (s4 := PGROUNDDOWN(va)) *)
    assert (HL2and : and_vec (rget L2 Rs2) (rget L2 Ra5) = va0).
    { rgne. rgne. rewrite /L2 upd_eq. rewrite upd_ne; [| reg_neq].
      rewrite /L1. rewrite upd_ne; [| reg_neq]. rewrite HM1s2. reflexivity. }
    iApply (wp_and_s_sconf Φ (mword_of_int (VF + 0x32)) Rs4 Rs2 Ra5 va0
              L2 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              HL2and with "Hcg Hpc Hi32 [-]").
    iIntros (C36 Hs36) "Hcg Hpc".
    set (L3 := <[Regidx Rs4 := regval_into_reg va0]> L2).
    assert (Hpp36 : add_vec_int (mword_of_int (VF + 0x32) : mword 64) 4
                    = mword_of_int (VF + 0x36))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp36) in "Hpc".
    (* +0x36 c.mv a1,s4 *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (VF + 0x36)) Ra1 Rs4
              L3 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi36 [-]").
    iIntros (C38 Hs38) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (L4 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (L3 !!! Regidx Rs4))]> L3).
    assert (Hpp38 : add_vec_int (mword_of_int (VF + 0x36) : mword 64) 2
                    = mword_of_int (VF + 0x38))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp38) in "Hpc".
    (* +0x38 c.mv a0,s3 *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (VF + 0x38)) Ra0 Rs3
              L4 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi38 [-]").
    iIntros (C3a Hs3a) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (L5 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (L4 !!! Regidx Rs3))]> L4).
    assert (Hpp3a : add_vec_int (mword_of_int (VF + 0x38) : mword 64) 2
                    = mword_of_int (VF + 0x3a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3a) in "Hpc".
    (* +0x3a jal ra,ismapped *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (VF + 0x3a)) Rra
              (mword_of_int 2097066 : mword 21) L5 (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi3a [-]").
    iIntros (Cim Hsim) "Hcg Hpc".
    set (L6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (VF + 0x3a) : mword 64) 4)]> L5).
    assert (Htgtim : add_vec (mword_of_int (VF + 0x3a) : mword 64)
                       (sign_extend' 64 (mword_of_int 2097066 : mword 21))
                     = mword_of_int KernelSyms.ismapped)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtim) in "Hpc".
    (* the register facts at ismapped's entry *)
    assert (HL6a1 : L6 !!! Regidx Ra1 = va0).
    { rewrite /L6. rewrite upd_ne; [| reg_neq].
      rewrite /L5. rewrite upd_ne; [| reg_neq].
      rewrite /L4 upd_eq. rewrite add_vec_zero_l.
      rewrite /L3 upd_eq. reflexivity. }
    assert (HL6a0 : L6 !!! Regidx Ra0 = page_base P.(ud_root)).
    { rewrite /L6. rewrite upd_ne; [| reg_neq].
      rewrite /L5 upd_eq. rewrite add_vec_zero_l.
      rewrite /L4. rewrite upd_ne; [| reg_neq].
      rewrite /L3. rewrite upd_ne; [| reg_neq].
      rewrite /L2. rewrite upd_ne; [| reg_neq].
      rewrite /L1. rewrite upd_ne; [| reg_neq]. exact HM1s3. }
    assert (HL6s1 : L6 !!! Regidx Rs1 = p).
    { rewrite /L6. rewrite upd_ne; [| reg_neq].
      rewrite /L5. rewrite upd_ne; [| reg_neq].
      rewrite /L4. rewrite upd_ne; [| reg_neq].
      rewrite /L3. rewrite upd_ne; [| reg_neq].
      rewrite /L2. rewrite upd_ne; [| reg_neq]. exact HL1s1. }
    assert (HL6s4 : L6 !!! Regidx Rs4 = va0).
    { rewrite /L6. rewrite upd_ne; [| reg_neq].
      rewrite /L5. rewrite upd_ne; [| reg_neq].
      rewrite /L4. rewrite upd_ne; [| reg_neq].
      rewrite /L3 upd_eq. reflexivity. }
    assert (HL6s3 : L6 !!! Regidx Rs3 = page_base P.(ud_root)).
    { rewrite /L6. rewrite upd_ne; [| reg_neq].
      rewrite /L5. rewrite upd_ne; [| reg_neq].
      rewrite /L4. rewrite upd_ne; [| reg_neq].
      rewrite /L3. rewrite upd_ne; [| reg_neq].
      rewrite /L2. rewrite upd_ne; [| reg_neq].
      rewrite /L1. rewrite upd_ne; [| reg_neq]. exact HM1s3. }
    assert (HL6sp : L6 !!! Regidx csp_rs1 = spr).
    { rewrite /L6 /L5 /L4 /L3 /L2 /L1.
      repeat (rewrite upd_ne; [| reg_neq]). exact HM1sp. }
    assert (HL6ra : L6 !!! Regidx Rra
                    = add_vec_int (mword_of_int (VF + 0x3a) : mword 64) 4)
      by (rewrite /L6 upd_eq; reflexivity).
    assert (HL6thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
              L6 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9 H18 H19 H20.
      rewrite /L6. rewrite upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /L5. rewrite upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /L4. rewrite upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /L3. rewrite upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H20; reflexivity].
      rewrite /L2. rewrite upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /L1. rewrite upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H9; reflexivity].
      apply HM1thr; assumption. }
    (* ---- open the table into the exact represented view ---- *)
    iDestruct (proc_pt_acc_rep0 P with "Hpt") as
      (t m_ad) "(%Hrep & %Hview & %Hbase & %Hwf & Hptree & Hown)".
    assert (HL6root : L6 !!! Regidx Ra0
                      = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))).
    { rewrite HL6a0 Hbase. reflexivity. }
    (* ---- ismapped(pagetable, va0) ---- *)
    iApply (Ismapped.wp_ismapped_sconf Φ L6 t m_ad (K - 6)%nat (DfracOwn 1) b p
              ltac:(lia) HL6root ltac:(rewrite HL6a1; exact Hva0b) Hrep
              with "Hcg Htext Hpc Hptree [-]").
    iIntros (Cir Hsir mi) "Hcg Hpc Hptree %Hics %Hiv".
    rewrite HL6a1 in Hiv.
    assert (Hret3e : ret_pc (L6 !!! Regidx Rra) = mword_of_int (VF + 0x3e)).
    { rewrite HL6ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret3e) in "Hpc".
    assert (Hmisp : mi !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hics csp_rs1 ltac:(vm_compute; reflexivity)). exact HL6sp. }
    assert (Hmis1 : mi !!! Regidx Rs1 = p).
    { rewrite (callee_saved_lookup Hics Rs1 ltac:(vm_compute; reflexivity)). exact HL6s1. }
    assert (Hmis4 : mi !!! Regidx Rs4 = va0).
    { rewrite (callee_saved_lookup Hics Rs4 ltac:(vm_compute; reflexivity)). exact HL6s4. }
    assert (Hmithr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
              mi !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9 H18 H19 H20.
      rewrite (callee_saved_lookup Hics c Hc). apply HL6thr; assumption. }
    iPoseProof (vfi_3e with "Htext") as "Hi3e".
    iPoseProof (vfi_40 with "Htext") as "Hi40".
    (* +0x3e c.li s3,0 *)
    iApply (wp_cli_s_sconf Φ (mword_of_int (VF + 0x3e)) Rs3 (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) mi (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi3e [-]").
    iIntros (C40 Hs40) "Hcg Hpc".
    set (N1 := <[Regidx Rs3 := regval_into_reg (mword_of_int 0 : mword 64)]> mi).
    assert (HN1s3 : N1 !!! Regidx Rs3 = mword_of_int 0)
      by (rewrite /N1 upd_eq; reflexivity).
    assert (HN1sp : N1 !!! Regidx csp_rs1 = spr)
      by (rewrite /N1; rewrite upd_ne; [exact Hmisp | reg_neq]).
    assert (HN1s1 : N1 !!! Regidx Rs1 = p)
      by (rewrite /N1; rewrite upd_ne; [exact Hmis1 | reg_neq]).
    assert (HN1s4 : N1 !!! Regidx Rs4 = va0)
      by (rewrite /N1; rewrite upd_ne; [exact Hmis4 | reg_neq]).
    assert (HN1a0 : N1 !!! Regidx Ra0 = mi !!! Regidx Ra0)
      by (rewrite /N1; rewrite upd_ne; [reflexivity | reg_neq]).
    assert (HN1thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
              N1 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9 H18 H19 H20.
      rewrite /N1. rewrite upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H19; reflexivity].
      apply Hmithr; assumption. }
    assert (Hpp40 : add_vec_int (mword_of_int (VF + 0x3e) : mword 64) 2
                    = mword_of_int (VF + 0x40))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp40) in "Hpc".
    (* ================================================================= *)
    (*  +0x40 c.beqz a0 : the ismapped verdict.                           *)
    (* ================================================================= *)
    destruct Hiv as [(Ha0z & Hnone) | (w & Hsome & Ha0one)].
    { (* ================= UNMAPPED: allocate ========================= *)
      iApply (wp_cbeqz_taken_s_sconf Φ (mword_of_int (VF + 0x40))
                (mword_of_int 4 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                N1 (K - 6)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HN1a0 Ha0z; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi40 [-]").
      iApply bi.later_intro. iIntros (C48 Hs48) "Hcg Hpc".
      assert (Htgt48 : add_vec (mword_of_int (VF + 0x40) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 4 : mword 8) ('b"0"))))
              = mword_of_int (VF + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt48) in "Hpc".
      iPoseProof (vfi_48 with "Htext") as "Hi48".
      iPoseProof (vfi_4c with "Htext") as "Hi4c".
      iPoseProof (vfi_4e with "Htext") as "Hi4e".
      (* +0x48 jal ra,kalloc *)
      iApply (wp_jal_s_sconf Φ (mword_of_int (VF + 0x48)) Rra
                (mword_of_int 2094406 : mword 21) N1 (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi48 [-]").
      iIntros (Cka Hska) "Hcg Hpc".
      set (A1 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (VF + 0x48) : mword 64) 4)]> N1).
      assert (Htgtka : add_vec (mword_of_int (VF + 0x48) : mword 64)
                         (sign_extend' 64 (mword_of_int 2094406 : mword 21))
                       = mword_of_int KernelSyms.kalloc)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtka) in "Hpc".
      assert (HA1ra : A1 !!! Regidx Rra
                      = add_vec_int (mword_of_int (VF + 0x48) : mword 64) 4)
        by (rewrite /A1 upd_eq; reflexivity).
      assert (HA1sp : A1 !!! Regidx csp_rs1 = spr)
        by (rewrite /A1; rewrite upd_ne; [exact HN1sp | reg_neq]).
      assert (HA1s1 : A1 !!! Regidx Rs1 = p)
        by (rewrite /A1; rewrite upd_ne; [exact HN1s1 | reg_neq]).
      assert (HA1s3 : A1 !!! Regidx Rs3 = mword_of_int 0)
        by (rewrite /A1; rewrite upd_ne; [exact HN1s3 | reg_neq]).
      assert (HA1s4 : A1 !!! Regidx Rs4 = va0)
        by (rewrite /A1; rewrite upd_ne; [exact HN1s4 | reg_neq]).
      assert (HA1thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                A1 !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H9 H18 H19 H20.
        rewrite /A1. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
        apply HN1thr; assumption. }
      iDestruct (cpu_own_transport Cmy Cka lvl eb p C b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iApply (Kalloc.wp_kalloc_sconf Φ γa γk (mword_of_int (KernelSyms.kmem + 24))
                A1 None lvl eb p C (K - 6)%nat b
                ltac:(lia) ltac:(reflexivity) Hlvl
                with "Hcg Hcnt Htext Hpc Hlock Havail Hpanic [-]").
      iIntros (Ckr Hskr mk) "Hcg Hcnt Hpc %Hkcs Hkpost".
      assert (Hret4c : ret_pc (A1 !!! Regidx Rra) = mword_of_int (VF + 0x4c)).
      { rewrite HA1ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hret4c) in "Hpc".
      assert (Hmksp : mk !!! Regidx csp_rs1 = spr).
      { rewrite (callee_saved_lookup Hkcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HA1sp. }
      assert (Hmks1 : mk !!! Regidx Rs1 = p).
      { rewrite (callee_saved_lookup Hkcs Rs1 ltac:(vm_compute; reflexivity)). exact HA1s1. }
      assert (Hmks3 : mk !!! Regidx Rs3 = mword_of_int 0).
      { rewrite (callee_saved_lookup Hkcs Rs3 ltac:(vm_compute; reflexivity)). exact HA1s3. }
      assert (Hmks4 : mk !!! Regidx Rs4 = va0).
      { rewrite (callee_saved_lookup Hkcs Rs4 ltac:(vm_compute; reflexivity)). exact HA1s4. }
      assert (Hmkthr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                mk !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H9 H18 H19 H20.
        rewrite (callee_saved_lookup Hkcs c Hc). apply HA1thr; assumption. }
      (* +0x4c c.mv s2,a0 *)
      iApply (wp_cmv_s_sconf Φ (mword_of_int (VF + 0x4c)) Rs2 Ra0
                mk (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi4c [-]").
      iIntros (C4e Hs4e) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (A2 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (mk !!! Regidx Ra0))]> mk).
      assert (HA2a0 : A2 !!! Regidx Ra0 = mk !!! Regidx Ra0)
        by (rewrite /A2; rewrite upd_ne; [reflexivity | reg_neq]).
      assert (HA2s2 : A2 !!! Regidx Rs2 = mk !!! Regidx Ra0)
        by (rewrite /A2 upd_eq; apply add_vec_zero_l).
      assert (HA2sp : A2 !!! Regidx csp_rs1 = spr)
        by (rewrite /A2; rewrite upd_ne; [exact Hmksp | reg_neq]).
      assert (HA2s1 : A2 !!! Regidx Rs1 = p)
        by (rewrite /A2; rewrite upd_ne; [exact Hmks1 | reg_neq]).
      assert (HA2s3 : A2 !!! Regidx Rs3 = mword_of_int 0)
        by (rewrite /A2; rewrite upd_ne; [exact Hmks3 | reg_neq]).
      assert (HA2s4 : A2 !!! Regidx Rs4 = va0)
        by (rewrite /A2; rewrite upd_ne; [exact Hmks4 | reg_neq]).
      assert (HA2thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                A2 !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H9 H18 H19 H20.
        rewrite /A2. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; apply H18; reflexivity].
        apply Hmkthr; assumption. }
      assert (Hpp4e : add_vec_int (mword_of_int (VF + 0x4c) : mword 64) 2
                      = mword_of_int (VF + 0x4e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4e) in "Hpc".
      iDestruct "Hkpost" as "[(%Hnull & _ & _) | (%Hpv & Hpage & _)]".
      { (* ---- kalloc returned 0: +0x7e, return 0 ---- *)
        iPoseProof (vfi_7e with "Htext") as "Hi7e".
        iPoseProof (vfi_80 with "Htext") as "Hi80".
        iPoseProof (vfi_82 with "Htext") as "Hi82".
        iApply (wp_cbeqz_taken_s_sconf Φ (mword_of_int (VF + 0x4e))
                  (mword_of_int 24 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                  A2 (K - 6)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite HA2a0 Hnull; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi4e [-]").
        iApply bi.later_intro. iIntros (C7e Hs7e) "Hcg Hpc".
        assert (Htgt7e : add_vec (mword_of_int (VF + 0x4e) : mword 64)
                  (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 24 : mword 8) ('b"0"))))
                = mword_of_int (VF + 0x7e)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt7e) in "Hpc".
        (* +0x7e c.ldsp s1,24(sp) *)
        iApply (wp_cldsp_s_sconf Φ (mword_of_int (VF + 0x7e)) (mword_of_int 3 : mword 6) Rs1
                  A2 (K - 6)%nat (mm !!! Regidx Rs1) b (dqm:=DfracOwn 1)
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi7e [Hk3] [-]").
        { iEval (rewrite HA2sp Hb3). iExact "Hk3". }
        iIntros (C80 Hs80) "Hcg Hpc Hk3". iEval (rewrite HA2sp Hb3) in "Hk3".
        set (B1 := <[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> A2).
        assert (HB1sp : B1 !!! Regidx csp_rs1 = spr)
          by (rewrite /B1; rewrite upd_ne; [exact HA2sp | reg_neq]).
        assert (Hpp80 : add_vec_int (mword_of_int (VF + 0x7e) : mword 64) 2
                        = mword_of_int (VF + 0x80))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp80) in "Hpc".
        (* +0x80 c.ldsp s4,0(sp) *)
        iApply (wp_cldsp_s_sconf Φ (mword_of_int (VF + 0x80)) (mword_of_int 0 : mword 6) Rs4
                  B1 (K - 6)%nat (mm !!! Regidx Rs4) b (dqm:=DfracOwn 1)
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi80 [Hk6] [-]").
        { iEval (rewrite HB1sp Hb6). iExact "Hk6". }
        iIntros (C82 Hs82) "Hcg Hpc Hk6". iEval (rewrite HB1sp Hb6) in "Hk6".
        set (B2 := <[Regidx Rs4 := regval_into_reg (mm !!! Regidx Rs4)]> B1).
        assert (Hpp82 : add_vec_int (mword_of_int (VF + 0x80) : mword 64) 2
                        = mword_of_int (VF + 0x82))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp82) in "Hpc".
        (* +0x82 c.j -0x66 *)
        iApply (wp_cj_s_sconf Φ (mword_of_int (VF + 0x82))
                  (sign_extend' 21 (concat_vec (mword_of_int 1997 : mword 11) ('b"0")))
                  B2 (K - 6)%nat b ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi82 [-]").
        iIntros (C1cA Hs1cA). iApply bi.later_intro. iIntros "Hcg Hpc".
        assert (Hjt82 : add_vec (mword_of_int (VF + 0x82) : mword 64)
                  (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1997 : mword 11) ('b"0"))))
                = mword_of_int (VF + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjt82) in "Hpc".
        iDestruct (proc_pt_rebuild P t m_ad Hwf Hview Hrep Hbase with "Hptree Hown") as "Hpt".
        iDestruct (cpu_own_transport Ckr C1cA lvl eb p C b ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        iSpecialize ("Hepi" $! C1cA with "[%]"); [wp_next_chain|].
        iApply ("Hepi" $! B2 (mword_of_int 0) with "[%] Hcg Hcnt Hpc [Hk3 Hk6] Hptc [Hpt]").
        { split_and!.
          - rewrite /B2. rewrite upd_ne; [exact HB1sp | reg_neq].
          - rewrite /B2. rewrite upd_ne; [| reg_neq].
            rewrite /B1. rewrite upd_ne; [exact HA2s3 | reg_neq].
          - intros c Hc H2 H8 H18 H19.
            destruct (decide (c = Rs1)) as [->|H9].
            { rewrite /B2. rewrite upd_ne; [| reg_neq]. rewrite /B1 upd_eq. reflexivity. }
            destruct (decide (c = Rs4)) as [->|H20].
            { rewrite /B2 upd_eq. reflexivity. }
            rewrite /B2. rewrite upd_ne;
              [| intros Hx; injection Hx as Hx2; subst c; apply H20; reflexivity].
            rewrite /B1. rewrite upd_ne;
              [| intros Hx; injection Hx as Hx2; subst c; apply H9; reflexivity].
            apply HA2thr; assumption. }
        { iExists _, _. iFrame "Hk3 Hk6". }
        { rewrite /PAY. iLeft. iSplitR; [iPureIntro; reflexivity | iExact "Hpt"]. } }
      (* ---- kalloc returned a page r ---- *)
      set (r := (mk !!! Regidx Ra0 : mword 64)).
      assert (Hpv' : page_valid r) by exact Hpv.
      pose proof Hpv' as Hpvd. destruct Hpvd as [Hral Hrrng].
      unfold page_in_range, kmem_lo, kmem_hi in Hrrng.
      assert (Hnz : (zero_reg : mword 64) = nullp) by (apply bv_eq; vm_compute; reflexivity).
      iPoseProof (vfi_50 with "Htext") as "Hi50".
      iPoseProof (vfi_52 with "Htext") as "Hi52".
      iPoseProof (vfi_54 with "Htext") as "Hi54".
      iPoseProof (vfi_56 with "Htext") as "Hi56".
      iApply (wp_cbeqz_fall_s_sconf Φ (mword_of_int (VF + 0x4e))
                (mword_of_int 24 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                A2 (K - 6)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HA2a0; apply eq_vec_false_iff; rewrite Hnz;
                      exact (page_valid_ne_null _ Hpv))
                with "Hcg Hpc Hi4e [-]").
      iIntros (C50 Hs50) "Hcg Hpc".
      assert (Hpp50 : add_vec_int (mword_of_int (VF + 0x4e) : mword 64) 2
                      = mword_of_int (VF + 0x50))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp50) in "Hpc".
      (* +0x50 c.mv s3,a0   (s3 := mem, the success return) *)
      iApply (wp_cmv_s_sconf Φ (mword_of_int (VF + 0x50)) Rs3 Ra0
                A2 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi50 [-]").
      iIntros (C52 Hs52) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (A3 := <[Regidx Rs3 := regval_into_reg (add_vec zero_reg (A2 !!! Regidx Ra0))]> A2).
      assert (HA3s3 : A3 !!! Regidx Rs3 = r)
        by (rewrite /A3 upd_eq; rewrite add_vec_zero_l; exact HA2a0).
      assert (HA3a0 : A3 !!! Regidx Ra0 = r)
        by (rewrite /A3; rewrite upd_ne; [exact HA2a0 | reg_neq]).
      assert (Hpp52 : add_vec_int (mword_of_int (VF + 0x50) : mword 64) 2
                      = mword_of_int (VF + 0x52))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp52) in "Hpc".
      (* +0x52 c.lui a2,1 *)
      iApply (wp_clui_s_sconf Φ (mword_of_int (VF + 0x52)) Ra2
                (sign_extend' 20 (mword_of_int 1 : mword 6)) (mword_of_int 4096 : mword 64)
                A3 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi52 [-]").
      iIntros (C54 Hs54) "Hcg Hpc".
      set (A4 := <[Regidx Ra2 := regval_into_reg (mword_of_int 4096 : mword 64)]> A3).
      assert (Hpp54 : add_vec_int (mword_of_int (VF + 0x52) : mword 64) 2
                      = mword_of_int (VF + 0x54))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp54) in "Hpc".
      (* +0x54 c.li a1,0 *)
      iApply (wp_cli_s_sconf Φ (mword_of_int (VF + 0x54)) Ra1 (mword_of_int 0 : mword 6)
                (mword_of_int 0 : mword 64) A4 (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi54 [-]").
      iIntros (C56 Hs56) "Hcg Hpc".
      set (A5 := <[Regidx Ra1 := regval_into_reg (mword_of_int 0 : mword 64)]> A4).
      assert (Hpp56 : add_vec_int (mword_of_int (VF + 0x54) : mword 64) 2
                      = mword_of_int (VF + 0x56))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp56) in "Hpc".
      (* +0x56 jal ra,memset *)
      iApply (wp_jal_s_sconf Φ (mword_of_int (VF + 0x56)) Rra
                (mword_of_int 2094802 : mword 21) A5 (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi56 [-]").
      iIntros (Cms Hsms) "Hcg Hpc".
      set (A6 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (VF + 0x56) : mword 64) 4)]> A5).
      assert (Htgtms : add_vec (mword_of_int (VF + 0x56) : mword 64)
                         (sign_extend' 64 (mword_of_int 2094802 : mword 21))
                       = mword_of_int KernelSyms.memset)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtms) in "Hpc".
      assert (HA6a0 : A6 !!! Regidx Ra0 = r).
      { rewrite /A6. rewrite upd_ne; [| reg_neq].
        rewrite /A5. rewrite upd_ne; [| reg_neq].
        rewrite /A4. rewrite upd_ne; [| reg_neq]. exact HA3a0. }
      assert (HA6a1 : A6 !!! Regidx Ra1 = mword_of_int 0).
      { rewrite /A6. rewrite upd_ne; [| reg_neq]. rewrite /A5 upd_eq. reflexivity. }
      assert (HA6a2 : A6 !!! Regidx Ra2 = mword_of_int 4096).
      { rewrite /A6. rewrite upd_ne; [| reg_neq].
        rewrite /A5. rewrite upd_ne; [| reg_neq]. rewrite /A4 upd_eq. reflexivity. }
      assert (HA6ra : A6 !!! Regidx Rra
                      = add_vec_int (mword_of_int (VF + 0x56) : mword 64) 4)
        by (rewrite /A6 upd_eq; reflexivity).
      assert (HA6sp : A6 !!! Regidx csp_rs1 = spr).
      { rewrite /A6 /A5 /A4 /A3.
        repeat (rewrite upd_ne; [| reg_neq]). exact HA2sp. }
      assert (HA6s1 : A6 !!! Regidx Rs1 = p).
      { rewrite /A6 /A5 /A4 /A3.
        repeat (rewrite upd_ne; [| reg_neq]). exact HA2s1. }
      assert (HA6s2 : A6 !!! Regidx Rs2 = r).
      { rewrite /A6 /A5 /A4 /A3.
        repeat (rewrite upd_ne; [| reg_neq]). exact HA2s2. }
      assert (HA6s3 : A6 !!! Regidx Rs3 = r).
      { rewrite /A6. rewrite upd_ne; [| reg_neq].
        rewrite /A5. rewrite upd_ne; [| reg_neq].
        rewrite /A4. rewrite upd_ne; [| reg_neq]. exact HA3s3. }
      assert (HA6s4 : A6 !!! Regidx Rs4 = va0).
      { rewrite /A6 /A5 /A4 /A3.
        repeat (rewrite upd_ne; [| reg_neq]). exact HA2s4. }
      assert (HA6thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                A6 !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H9 H18 H19 H20.
        rewrite /A6. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
        rewrite /A5. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
        rewrite /A4. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
        rewrite /A3. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; apply H19; reflexivity].
        apply HA2thr; assumption. }
      (* ---- memset(mem, 0, PGSIZE) ---- *)
      iApply (MemsetPage.wp_memset_page_sconf Φ A6 (K - 6)%nat (mword_of_int 0 : mword 64) b p
                ltac:(lia) ltac:(rewrite HA6a0; exact Hpv) HA6a1 HA6a2
                with "Hcg Htext Hpc [Hpage] [-]").
      { iEval (rewrite HA6a0). iExact "Hpage". }
      iIntros (Cse Hsse ms) "Hcg Hpc Hpage %Hmscs".
      iEval (rewrite HA6a0) in "Hpage".
      assert (Hret5a : ret_pc (A6 !!! Regidx Rra) = mword_of_int (VF + 0x5a)).
      { rewrite HA6ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hret5a) in "Hpc".
      assert (Hmssp : ms !!! Regidx csp_rs1 = spr).
      { rewrite (callee_saved_lookup Hmscs csp_rs1 ltac:(vm_compute; reflexivity)). exact HA6sp. }
      assert (Hmss1 : ms !!! Regidx Rs1 = p).
      { rewrite (callee_saved_lookup Hmscs Rs1 ltac:(vm_compute; reflexivity)). exact HA6s1. }
      assert (Hmss2 : ms !!! Regidx Rs2 = r).
      { rewrite (callee_saved_lookup Hmscs Rs2 ltac:(vm_compute; reflexivity)). exact HA6s2. }
      assert (Hmss3 : ms !!! Regidx Rs3 = r).
      { rewrite (callee_saved_lookup Hmscs Rs3 ltac:(vm_compute; reflexivity)). exact HA6s3. }
      assert (Hmss4 : ms !!! Regidx Rs4 = va0).
      { rewrite (callee_saved_lookup Hmscs Rs4 ltac:(vm_compute; reflexivity)). exact HA6s4. }
      assert (Hmsthr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                ms !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H9 H18 H19 H20.
        rewrite (callee_saved_lookup Hmscs c Hc). apply HA6thr; assumption. }
      iPoseProof (vfi_5a with "Htext") as "Hi5a".
      iPoseProof (vfi_5c with "Htext") as "Hi5c".
      iPoseProof (vfi_5e with "Htext") as "Hi5e".
      iPoseProof (vfi_60 with "Htext") as "Hi60".
      iPoseProof (vfi_62 with "Htext") as "Hi62".
      iPoseProof (vfi_64 with "Htext") as "Hi64".
      iPoseProof (vfi_68 with "Htext") as "Hi68".
      (* +0x5a c.li a4,22 *)
      iApply (wp_cli_s_sconf Φ (mword_of_int (VF + 0x5a)) Ra4 (mword_of_int 22 : mword 6)
                (mword_of_int 22 : mword 64) ms (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi5a [-]").
      iIntros (C5c Hs5c) "Hcg Hpc".
      set (G1 := <[Regidx Ra4 := regval_into_reg (mword_of_int 22 : mword 64)]> ms).
      assert (Hpp5c : add_vec_int (mword_of_int (VF + 0x5a) : mword 64) 2
                      = mword_of_int (VF + 0x5c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp5c) in "Hpc".
      (* +0x5c c.mv a3,s2 *)
      iApply (wp_cmv_s_sconf Φ (mword_of_int (VF + 0x5c)) Ra3 Rs2
                G1 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi5c [-]").
      iIntros (C5e Hs5e) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (G2 := <[Regidx Ra3 := regval_into_reg (add_vec zero_reg (G1 !!! Regidx Rs2))]> G1).
      assert (Hpp5e : add_vec_int (mword_of_int (VF + 0x5c) : mword 64) 2
                      = mword_of_int (VF + 0x5e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp5e) in "Hpc".
      (* +0x5e c.lui a2,1 *)
      iApply (wp_clui_s_sconf Φ (mword_of_int (VF + 0x5e)) Ra2
                (sign_extend' 20 (mword_of_int 1 : mword 6)) (mword_of_int 4096 : mword 64)
                G2 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi5e [-]").
      iIntros (C60 Hs60) "Hcg Hpc".
      set (G3 := <[Regidx Ra2 := regval_into_reg (mword_of_int 4096 : mword 64)]> G2).
      assert (Hpp60 : add_vec_int (mword_of_int (VF + 0x5e) : mword 64) 2
                      = mword_of_int (VF + 0x60))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp60) in "Hpc".
      (* +0x60 c.mv a1,s4 *)
      iApply (wp_cmv_s_sconf Φ (mword_of_int (VF + 0x60)) Ra1 Rs4
                G3 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi60 [-]").
      iIntros (C62 Hs62) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (G4 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (G3 !!! Regidx Rs4))]> G3).
      assert (HG4s1 : G4 !!! Regidx Rs1 = p).
      { rewrite /G4 /G3 /G2 /G1.
        repeat (rewrite upd_ne; [| reg_neq]). exact Hmss1. }
      assert (Hpp62 : add_vec_int (mword_of_int (VF + 0x60) : mword 64) 2
                      = mword_of_int (VF + 0x62))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp62) in "Hpc".
      (* +0x62 c.ld a0,80(s1)   (a0 := p->pagetable) *)
      iEval (rewrite cshape_68a8) in "Hi62".
      assert (HrgG4s1 : rget G4 Rs1 = p) by (rgne; exact HG4s1).
      iApply (wp_cld_s_sconf Φ (mword_of_int (VF + 0x62)) Ra0 Rs1
                (mword_of_int 80 : mword 12) G4 (K - 6)%nat
                (page_base P.(ud_root)) b (dqm:=dqp)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi62 [Hptc] [-]").
      { iEval (rewrite HrgG4s1 Hppta). iExact "Hptc". }
      iIntros (C64 Hs64) "Hcg Hpc Hptc".
      iEval (rewrite HrgG4s1 Hppta) in "Hptc".
      set (G5 := <[Regidx Ra0 := regval_into_reg (page_base P.(ud_root))]> G4).
      assert (Hpp64 : add_vec_int (mword_of_int (VF + 0x62) : mword 64) 2
                      = mword_of_int (VF + 0x64))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp64) in "Hpc".
      (* +0x64 jal ra,mappages *)
      iApply (wp_jal_s_sconf Φ (mword_of_int (VF + 0x64)) Rra
                (mword_of_int 2095660 : mword 21) G5 (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi64 [-]").
      iIntros (Cmg Hsmg) "Hcg Hpc".
      set (G6 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (VF + 0x64) : mword 64) 4)]> G5).
      assert (Htgtmap : add_vec (mword_of_int (VF + 0x64) : mword 64)
                          (sign_extend' 64 (mword_of_int 2095660 : mword 21))
                        = mword_of_int KernelSyms.mappages)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtmap) in "Hpc".
      (* the register facts at mappages' entry *)
      assert (HG6a0 : G6 !!! Regidx Ra0
                      = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))).
      { rewrite /G6. rewrite upd_ne; [| reg_neq].
        rewrite /G5 upd_eq. rewrite Hbase. reflexivity. }
      assert (HG6a1 : G6 !!! Regidx Ra1 = va0).
      { rewrite /G6. rewrite upd_ne; [| reg_neq].
        rewrite /G5. rewrite upd_ne; [| reg_neq].
        rewrite /G4 upd_eq. rewrite add_vec_zero_l.
        rewrite /G3. rewrite upd_ne; [| reg_neq].
        rewrite /G2. rewrite upd_ne; [| reg_neq].
        rewrite /G1. rewrite upd_ne; [| reg_neq]. exact Hmss4. }
      assert (HG6a2 : G6 !!! Regidx Ra2 = mword_of_int 4096).
      { rewrite /G6. rewrite upd_ne; [| reg_neq].
        rewrite /G5. rewrite upd_ne; [| reg_neq].
        rewrite /G4. rewrite upd_ne; [| reg_neq].
        rewrite /G3 upd_eq. reflexivity. }
      assert (HG6a3 : G6 !!! Regidx Ra3 = r).
      { rewrite /G6. rewrite upd_ne; [| reg_neq].
        rewrite /G5. rewrite upd_ne; [| reg_neq].
        rewrite /G4. rewrite upd_ne; [| reg_neq].
        rewrite /G3. rewrite upd_ne; [| reg_neq].
        rewrite /G2 upd_eq. rewrite add_vec_zero_l.
        rewrite /G1. rewrite upd_ne; [| reg_neq]. exact Hmss2. }
      assert (HG6a4 : G6 !!! Regidx Ra4 = mword_of_int 22).
      { rewrite /G6. rewrite upd_ne; [| reg_neq].
        rewrite /G5. rewrite upd_ne; [| reg_neq].
        rewrite /G4. rewrite upd_ne; [| reg_neq].
        rewrite /G3. rewrite upd_ne; [| reg_neq].
        rewrite /G2. rewrite upd_ne; [| reg_neq].
        rewrite /G1 upd_eq. reflexivity. }
      assert (HG6ra : G6 !!! Regidx Rra
                      = add_vec_int (mword_of_int (VF + 0x64) : mword 64) 4)
        by (rewrite /G6 upd_eq; reflexivity).
      assert (HG6sp : G6 !!! Regidx csp_rs1 = spr).
      { rewrite /G6 /G5 /G4 /G3 /G2 /G1.
        repeat (rewrite upd_ne; [| reg_neq]). exact Hmssp. }
      assert (HG6s1 : G6 !!! Regidx Rs1 = p).
      { rewrite /G6 /G5 /G4 /G3 /G2 /G1.
        repeat (rewrite upd_ne; [| reg_neq]). exact Hmss1. }
      assert (HG6s2 : G6 !!! Regidx Rs2 = r).
      { rewrite /G6 /G5 /G4 /G3 /G2 /G1.
        repeat (rewrite upd_ne; [| reg_neq]). exact Hmss2. }
      assert (HG6s3 : G6 !!! Regidx Rs3 = r).
      { rewrite /G6 /G5 /G4 /G3 /G2 /G1.
        repeat (rewrite upd_ne; [| reg_neq]). exact Hmss3. }
      assert (HG6s4 : G6 !!! Regidx Rs4 = va0).
      { rewrite /G6 /G5 /G4 /G3 /G2 /G1.
        repeat (rewrite upd_ne; [| reg_neq]). exact Hmss4. }
      assert (HG6thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                G6 !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H9 H18 H19 H20.
        rewrite /G6 /G5 /G4 /G3 /G2 /G1.
        repeat (rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate]).
        apply Hmsthr; assumption. }
      (* mappages' premises, all pre-established (optimization.md: never an
         inline [ltac:] over a big goal) *)
      assert (Hmpva : subrange_vec_dec (G6 !!! Regidx Ra1) 11 0 = (zeros' 12 : mword 12))
        by (rewrite HG6a1; apply pgrounddown_low12).
      assert (Hmppa : subrange_vec_dec (G6 !!! Regidx Ra3) 11 0 = (zeros' 12 : mword 12))
        by (rewrite HG6a3; exact (vf_page_align12 r Hpv)).
      assert (Hmpsz : G6 !!! Regidx Ra2 = mword_of_int (Z.of_nat 1 * 4096))
        by (rewrite HG6a2; apply bv_eq; vm_compute; reflexivity).
      assert (Hmpvab : (uint (G6 !!! Regidx Ra1) + Z.of_nat 1 * 4096 <= 2 ^ 38)%Z).
      { rewrite HG6a1. change (2 ^ 38)%Z with 274877906944%Z.
        exact (vf_z_run_va _ _ Hva0b4). }
      assert (Hmppab : (uint (G6 !!! Regidx Ra3) + Z.of_nat 1 * 4096 < 2 ^ 56)%Z).
      { rewrite HG6a3. change (2 ^ 56)%Z with 72057594037927936%Z.
        exact (vf_z_run_pa _ (proj2 Hrrng)). }
      assert (Hmpfresh : forall i, (i < 1)%nat ->
                m_ad !! vpn_at (svpn_of (G6 !!! Regidx Ra1)) i = None).
      { intros i Hi. assert (Hi0 : i = 0%nat) by lia. subst i.
        rewrite vpn_at_0. rewrite HG6a1. exact Hnone. }
      iAssert (kalloc_env γa None) as "#Henv2".
      { iExists γk. iFrame "Hlock Havail Hpanic". }
      (* ---- mappages(p->pagetable, va0, PGSIZE, mem, PTE_R|W|U) ----
         at the ambient [lvl]: mappages/walk are level-generic, and [Hlvl] is
         exactly the int-range fact their kalloc needs. *)
      iDestruct (cpu_own_transport Ckr Cmg lvl eb p C b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iApply (Mappages.wp_mappages_sconf γa Φ G6 t m_ad 1%nat 22 lvl (K - 6)%nat
                eb p C None b
                Hlvl ltac:(lia) HG6a0 Hmpva Hmppa Hmpsz ltac:(lia)
                HG6a4 vmf_perm_ok22 Hmpvab Hmppab Hrep Hmpfresh
                with "Hcg Hcnt Htext Hpc Hptree Henv2 [-]").
      iIntros (Cgr Hsgr mg t' k g) "Hcg Hcnt Hpc Hptree %Hnodes _ %Hgcs %Hbase' %Hrep' %Hmono %Hmiss %Hmpay".
      rewrite HG6a1 in Hrep'. rewrite HG6a3 in Hrep'.
      assert (Hret68 : ret_pc (G6 !!! Regidx Rra) = mword_of_int (VF + 0x68)).
      { rewrite HG6ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hret68) in "Hpc".
      assert (Hmgsp : mg !!! Regidx csp_rs1 = spr).
      { rewrite (callee_saved_lookup Hgcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HG6sp. }
      assert (Hmgs2 : mg !!! Regidx Rs2 = r).
      { rewrite (callee_saved_lookup Hgcs Rs2 ltac:(vm_compute; reflexivity)). exact HG6s2. }
      assert (Hmgs3 : mg !!! Regidx Rs3 = r).
      { rewrite (callee_saved_lookup Hgcs Rs3 ltac:(vm_compute; reflexivity)). exact HG6s3. }
      assert (Hmgthr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                mg !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H9 H18 H19 H20.
        rewrite (callee_saved_lookup Hgcs c Hc). apply HG6thr; assumption. }
      assert (Hbase'' : pt_base t' = P.(ud_root)) by (rewrite Hbase'; exact Hbase).
      destruct Hmpay as [(Hk1 & Hga0) | (Hklt & Hga0 & _)].
      { (* ============ mappages SUCCEEDED: return mem ================ *)
        subst k. rewrite vf_run1 in Hrep'.
        iPoseProof (vfi_6a with "Htext") as "Hi6a".
        iPoseProof (vfi_6c with "Htext") as "Hi6c".
        iPoseProof (vfi_6e with "Htext") as "Hi6e".
        (* +0x68 c.bnez a0 FALLS (a0 = 0) *)
        iApply (wp_cbnez_fall_s_sconf Φ (mword_of_int (VF + 0x68))
                  (mword_of_int 4 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                  mg (K - 6)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite Hga0; vm_compute; reflexivity)
                  with "Hcg Hpc Hi68 [-]").
        iIntros (C6a Hs6a) "Hcg Hpc".
        assert (Hpp6a : add_vec_int (mword_of_int (VF + 0x68) : mword 64) 2
                        = mword_of_int (VF + 0x6a))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp6a) in "Hpc".
        (* +0x6a c.ldsp s1,24(sp) *)
        iApply (wp_cldsp_s_sconf Φ (mword_of_int (VF + 0x6a)) (mword_of_int 3 : mword 6) Rs1
                  mg (K - 6)%nat (mm !!! Regidx Rs1) b (dqm:=DfracOwn 1)
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi6a [Hk3] [-]").
        { iEval (rewrite Hmgsp Hb3). iExact "Hk3". }
        iIntros (C6c Hs6c) "Hcg Hpc Hk3". iEval (rewrite Hmgsp Hb3) in "Hk3".
        set (S1 := <[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> mg).
        assert (HS1sp : S1 !!! Regidx csp_rs1 = spr)
          by (rewrite /S1; rewrite upd_ne; [exact Hmgsp | reg_neq]).
        assert (Hpp6c : add_vec_int (mword_of_int (VF + 0x6a) : mword 64) 2
                        = mword_of_int (VF + 0x6c))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp6c) in "Hpc".
        (* +0x6c c.ldsp s4,0(sp) *)
        iApply (wp_cldsp_s_sconf Φ (mword_of_int (VF + 0x6c)) (mword_of_int 0 : mword 6) Rs4
                  S1 (K - 6)%nat (mm !!! Regidx Rs4) b (dqm:=DfracOwn 1)
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi6c [Hk6] [-]").
        { iEval (rewrite HS1sp Hb6). iExact "Hk6". }
        iIntros (C6e Hs6e) "Hcg Hpc Hk6". iEval (rewrite HS1sp Hb6) in "Hk6".
        set (S2 := <[Regidx Rs4 := regval_into_reg (mm !!! Regidx Rs4)]> S1).
        assert (Hpp6e : add_vec_int (mword_of_int (VF + 0x6c) : mword 64) 2
                        = mword_of_int (VF + 0x6e))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp6e) in "Hpc".
        (* +0x6e c.j -0x52 *)
        iApply (wp_cj_s_sconf Φ (mword_of_int (VF + 0x6e))
                  (sign_extend' 21 (concat_vec (mword_of_int 2007 : mword 11) ('b"0")))
                  S2 (K - 6)%nat b ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi6e [-]").
        iIntros (C1cB Hs1cB). iApply bi.later_intro. iIntros "Hcg Hpc".
        assert (Hjt6e : add_vec (mword_of_int (VF + 0x6e) : mword 64)
                  (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2007 : mword 11) ('b"0"))))
                = mword_of_int (VF + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjt6e) in "Hpc".
        (* ---- grow the user map by the new page ---- *)
        iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhwc Hcg]".
        iDestruct "Hhwc" as (hwmisa0 hwmseccfg0 hwpmar0 hwelp0)
          "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & #Hkmapb)".
        assert (Hvpnb : (bv_unsigned (svpn_of va0) < 67108864)%Z)
          by exact (svpn_of_lt_maxva va0 Hva0b).
        iDestruct (proc_pt_grow P (svpn_of va0) r t'
                     m_ad Hwf Hview Hnone Hvpnb Hrep' Hbase'' Hpv
                     with "Hkmapb Hptree Hpage Hown") as "Hpt".
        assert (Humnone : P.(ud_um) !! svpn_of va0 = None)
          by (exact (proj2 (proj2 (proj1 (proj1 Hview (svpn_of va0)) Hnone)))).
        iDestruct (cpu_own_transport Cgr C1cB lvl eb p C b ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        iSpecialize ("Hepi" $! C1cB with "[%]"); [wp_next_chain|].
        iApply ("Hepi" $! S2 r with "[%] Hcg Hcnt Hpc [Hk3 Hk6] Hptc [Hpt]").
        { split_and!.
          - rewrite /S2. rewrite upd_ne; [exact HS1sp | reg_neq].
          - rewrite /S2. rewrite upd_ne; [| reg_neq].
            rewrite /S1. rewrite upd_ne; [exact Hmgs3 | reg_neq].
          - intros c Hc H2 H8 H18 H19.
            destruct (decide (c = Rs1)) as [->|H9].
            { rewrite /S2. rewrite upd_ne; [| reg_neq]. rewrite /S1 upd_eq. reflexivity. }
            destruct (decide (c = Rs4)) as [->|H20].
            { rewrite /S2 upd_eq. reflexivity. }
            rewrite /S2. rewrite upd_ne;
              [| intros Hx; injection Hx as Hx2; subst c; apply H20; reflexivity].
            rewrite /S1. rewrite upd_ne;
              [| intros Hx; injection Hx as Hx2; subst c; apply H9; reflexivity].
            apply Hmgthr; assumption. }
        { iExists _, _. iFrame "Hk3 Hk6". }
        { rewrite /PAY. iRight. iExists r.
          iSplitR; [iPureIntro; reflexivity |].
          iSplitR; [iPureIntro; exact Hpv |].
          iSplitR; [iPureIntro; exact Hvalt |].
          iSplitR; [iPureIntro; exact Humnone |].
          iExact "Hpt". } }
      (* ============ mappages FAILED: kfree and return 0 ============= *)
      assert (Hk0 : k = 0%nat) by lia. subst k.
      cbn [pt_insert_run] in Hrep'.
      iPoseProof (vfi_70 with "Htext") as "Hi70".
      iPoseProof (vfi_72 with "Htext") as "Hi72".
      iPoseProof (vfi_76 with "Htext") as "Hi76".
      iPoseProof (vfi_78 with "Htext") as "Hi78".
      iPoseProof (vfi_7a with "Htext") as "Hi7a".
      iPoseProof (vfi_7c with "Htext") as "Hi7c".
      (* +0x68 c.bnez a0 TAKEN (a0 = -1) *)
      iApply (wp_cbnez_taken_s_sconf Φ (mword_of_int (VF + 0x68))
                (mword_of_int 4 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                mg (K - 6)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite Hga0; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi68 [-]").
      iApply bi.later_intro. iIntros (C70 Hs70) "Hcg Hpc".
      assert (Htgt70 : add_vec (mword_of_int (VF + 0x68) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 4 : mword 8) ('b"0"))))
              = mword_of_int (VF + 0x70)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt70) in "Hpc".
      (* +0x70 c.mv a0,s2 *)
      iApply (wp_cmv_s_sconf Φ (mword_of_int (VF + 0x70)) Ra0 Rs2
                mg (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi70 [-]").
      iIntros (C72 Hs72) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (F1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mg !!! Regidx Rs2))]> mg).
      assert (Hpp72 : add_vec_int (mword_of_int (VF + 0x70) : mword 64) 2
                      = mword_of_int (VF + 0x72))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp72) in "Hpc".
      (* +0x72 jal ra,kfree *)
      iApply (wp_jal_s_sconf Φ (mword_of_int (VF + 0x72)) Rra
                (mword_of_int 2094132 : mword 21) F1 (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi72 [-]").
      iIntros (Ckf Hskf) "Hcg Hpc".
      set (F2 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (VF + 0x72) : mword 64) 4)]> F1).
      assert (Htgtkf : add_vec (mword_of_int (VF + 0x72) : mword 64)
                         (sign_extend' 64 (mword_of_int 2094132 : mword 21))
                       = mword_of_int KernelSyms.kfree)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtkf) in "Hpc".
      assert (HF2a0 : F2 !!! Regidx Ra0 = r).
      { rewrite /F2. rewrite upd_ne; [| reg_neq].
        rewrite /F1 upd_eq. rewrite add_vec_zero_l. exact Hmgs2. }
      assert (HF2ra : F2 !!! Regidx Rra
                      = add_vec_int (mword_of_int (VF + 0x72) : mword 64) 4)
        by (rewrite /F2 upd_eq; reflexivity).
      assert (HF2sp : F2 !!! Regidx csp_rs1 = spr).
      { rewrite /F2. rewrite upd_ne; [| reg_neq].
        rewrite /F1. rewrite upd_ne; [| reg_neq]. exact Hmgsp. }
      assert (HF2s3 : F2 !!! Regidx Rs3 = r).
      { rewrite /F2. rewrite upd_ne; [| reg_neq].
        rewrite /F1. rewrite upd_ne; [| reg_neq]. exact Hmgs3. }
      assert (HF2thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                F2 !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H9 H18 H19 H20.
        rewrite /F2. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
        rewrite /F1. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
        apply Hmgthr; assumption. }
      iDestruct (cpu_own_transport Cgr Ckf lvl eb p C b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iApply (Kfree.wp_kfree_sconf Φ γa γk (mword_of_int KernelSyms.kmem)
                (mword_of_int (KernelSyms.kmem + 24)) F2 None lvl eb p C (K - 6)%nat b
                ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)
                Hlvl
                with "Hcg Hcnt Htext Hpc Hlock [Hpage] Havail Hpanic [-]").
      { rewrite /kfree_pre HF2a0.
        iSplitR; [iPureIntro; exact Hpv | iExact "Hpage"]. }
      iIntros (Cfr Hsfr mfk) "Hcg Hcnt Hpc %Hfcs _".
      assert (Hret76 : ret_pc (F2 !!! Regidx Rra) = mword_of_int (VF + 0x76)).
      { rewrite HF2ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hret76) in "Hpc".
      assert (Hmfksp : mfk !!! Regidx csp_rs1 = spr).
      { rewrite (callee_saved_lookup Hfcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HF2sp. }
      assert (Hmfkthr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                mfk !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H9 H18 H19 H20.
        rewrite (callee_saved_lookup Hfcs c Hc). apply HF2thr; assumption. }
      (* +0x76 c.li s3,0 *)
      iApply (wp_cli_s_sconf Φ (mword_of_int (VF + 0x76)) Rs3 (mword_of_int 0 : mword 6)
                (mword_of_int 0 : mword 64) mfk (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi76 [-]").
      iIntros (C78 Hs78) "Hcg Hpc".
      set (F3 := <[Regidx Rs3 := regval_into_reg (mword_of_int 0 : mword 64)]> mfk).
      assert (HF3sp : F3 !!! Regidx csp_rs1 = spr)
        by (rewrite /F3; rewrite upd_ne; [exact Hmfksp | reg_neq]).
      assert (Hpp78 : add_vec_int (mword_of_int (VF + 0x76) : mword 64) 2
                      = mword_of_int (VF + 0x78))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp78) in "Hpc".
      (* +0x78 c.ldsp s1,24(sp) *)
      iApply (wp_cldsp_s_sconf Φ (mword_of_int (VF + 0x78)) (mword_of_int 3 : mword 6) Rs1
                F3 (K - 6)%nat (mm !!! Regidx Rs1) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi78 [Hk3] [-]").
      { iEval (rewrite HF3sp Hb3). iExact "Hk3". }
      iIntros (C7a Hs7a) "Hcg Hpc Hk3". iEval (rewrite HF3sp Hb3) in "Hk3".
      set (F4 := <[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> F3).
      assert (HF4sp : F4 !!! Regidx csp_rs1 = spr)
        by (rewrite /F4; rewrite upd_ne; [exact HF3sp | reg_neq]).
      assert (Hpp7a : add_vec_int (mword_of_int (VF + 0x78) : mword 64) 2
                      = mword_of_int (VF + 0x7a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp7a) in "Hpc".
      (* +0x7a c.ldsp s4,0(sp) *)
      iApply (wp_cldsp_s_sconf Φ (mword_of_int (VF + 0x7a)) (mword_of_int 0 : mword 6) Rs4
                F4 (K - 6)%nat (mm !!! Regidx Rs4) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi7a [Hk6] [-]").
      { iEval (rewrite HF4sp Hb6). iExact "Hk6". }
      iIntros (C7c Hs7c) "Hcg Hpc Hk6". iEval (rewrite HF4sp Hb6) in "Hk6".
      set (F5 := <[Regidx Rs4 := regval_into_reg (mm !!! Regidx Rs4)]> F4).
      assert (Hpp7c : add_vec_int (mword_of_int (VF + 0x7a) : mword 64) 2
                      = mword_of_int (VF + 0x7c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp7c) in "Hpc".
      (* +0x7c c.j -0x60 *)
      iApply (wp_cj_s_sconf Φ (mword_of_int (VF + 0x7c))
                (sign_extend' 21 (concat_vec (mword_of_int 2000 : mword 11) ('b"0")))
                F5 (K - 6)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi7c [-]").
      iIntros (C1cC Hs1cC). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Hjt7c : add_vec (mword_of_int (VF + 0x7c) : mword 64)
                (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2000 : mword 11) ('b"0"))))
              = mword_of_int (VF + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjt7c) in "Hpc".
      iDestruct (proc_pt_rebuild P t' m_ad Hwf Hview Hrep' Hbase'' with "Hptree Hown") as "Hpt".
      iDestruct (cpu_own_transport Cfr C1cC lvl eb p C b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("Hepi" $! C1cC with "[%]"); [wp_next_chain|].
      iApply ("Hepi" $! F5 (mword_of_int 0) with "[%] Hcg Hcnt Hpc [Hk3 Hk6] Hptc [Hpt]").
      { split_and!.
        - rewrite /F5. rewrite upd_ne; [exact HF4sp | reg_neq].
        - rewrite /F5. rewrite upd_ne; [| reg_neq].
          rewrite /F4. rewrite upd_ne; [| reg_neq].
          rewrite /F3 upd_eq. reflexivity.
        - intros c Hc H2 H8 H18 H19.
          destruct (decide (c = Rs1)) as [->|H9].
          { rewrite /F5. rewrite upd_ne; [| reg_neq]. rewrite /F4 upd_eq. reflexivity. }
          destruct (decide (c = Rs4)) as [->|H20].
          { rewrite /F5 upd_eq. reflexivity. }
          rewrite /F5. rewrite upd_ne;
            [| intros Hx; injection Hx as Hx2; subst c; apply H20; reflexivity].
          rewrite /F4. rewrite upd_ne;
            [| intros Hx; injection Hx as Hx2; subst c; apply H9; reflexivity].
          rewrite /F3. rewrite upd_ne;
            [| intros Hx; injection Hx as Hx2; subst c; apply H19; reflexivity].
          apply Hmfkthr; assumption. }
      { iExists _, _. iFrame "Hk3 Hk6". }
      { rewrite /PAY. iLeft. iSplitR; [iPureIntro; reflexivity | iExact "Hpt"]. } }

    (* ================= ALREADY MAPPED: return 0 ==================== *)
    iPoseProof (vfi_42 with "Htext") as "Hi42".
    iPoseProof (vfi_44 with "Htext") as "Hi44".
    iPoseProof (vfi_46 with "Htext") as "Hi46".
    iApply (wp_cbeqz_fall_s_sconf Φ (mword_of_int (VF + 0x40))
              (mword_of_int 4 : mword 8) (Cregidx (mword_of_int 2)) Ra0
              N1 (K - 6)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite HN1a0 Ha0one; vm_compute; reflexivity)
              with "Hcg Hpc Hi40 [-]").
    iIntros (C42 Hs42) "Hcg Hpc".
    assert (Hpp42 : add_vec_int (mword_of_int (VF + 0x40) : mword 64) 2
                    = mword_of_int (VF + 0x42))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp42) in "Hpc".
    (* +0x42 c.ldsp s1,24(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (VF + 0x42)) (mword_of_int 3 : mword 6) Rs1
              N1 (K - 6)%nat (mm !!! Regidx Rs1) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi42 [Hk3] [-]").
    { iEval (rewrite HN1sp Hb3). iExact "Hk3". }
    iIntros (C44 Hs44) "Hcg Hpc Hk3". iEval (rewrite HN1sp Hb3) in "Hk3".
    set (D1 := <[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> N1).
    assert (HD1sp : D1 !!! Regidx csp_rs1 = spr)
      by (rewrite /D1; rewrite upd_ne; [exact HN1sp | reg_neq]).
    assert (Hpp44 : add_vec_int (mword_of_int (VF + 0x42) : mword 64) 2
                    = mword_of_int (VF + 0x44))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp44) in "Hpc".
    (* +0x44 c.ldsp s4,0(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (VF + 0x44)) (mword_of_int 0 : mword 6) Rs4
              D1 (K - 6)%nat (mm !!! Regidx Rs4) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi44 [Hk6] [-]").
    { iEval (rewrite HD1sp Hb6). iExact "Hk6". }
    iIntros (C46 Hs46) "Hcg Hpc Hk6". iEval (rewrite HD1sp Hb6) in "Hk6".
    set (D2 := <[Regidx Rs4 := regval_into_reg (mm !!! Regidx Rs4)]> D1).
    assert (Hpp46 : add_vec_int (mword_of_int (VF + 0x44) : mword 64) 2
                    = mword_of_int (VF + 0x46))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp46) in "Hpc".
    (* +0x46 c.j -0x2a *)
    iApply (wp_cj_s_sconf Φ (mword_of_int (VF + 0x46))
              (sign_extend' 21 (concat_vec (mword_of_int 2027 : mword 11) ('b"0")))
              D2 (K - 6)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi46 [-]").
    iIntros (C1cD Hs1cD). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Hjt46 : add_vec (mword_of_int (VF + 0x46) : mword 64)
              (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2027 : mword 11) ('b"0"))))
            = mword_of_int (VF + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjt46) in "Hpc".
    iDestruct (proc_pt_rebuild P t m_ad Hwf Hview Hrep Hbase with "Hptree Hown") as "Hpt".
    iDestruct (cpu_own_transport Cmy C1cD lvl eb p C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iSpecialize ("Hepi" $! C1cD with "[%]"); [wp_next_chain|].
    iApply ("Hepi" $! D2 (mword_of_int 0) with "[%] Hcg Hcnt Hpc [Hk3 Hk6] Hptc [Hpt]").
    { split_and!.
      - rewrite /D2. rewrite upd_ne; [exact HD1sp | reg_neq].
      - rewrite /D2. rewrite upd_ne; [| reg_neq].
        rewrite /D1. rewrite upd_ne; [exact HN1s3 | reg_neq].
      - intros c Hc H2 H8 H18 H19.
        destruct (decide (c = Rs1)) as [->|H9].
        { rewrite /D2. rewrite upd_ne; [| reg_neq]. rewrite /D1 upd_eq. reflexivity. }
        destruct (decide (c = Rs4)) as [->|H20].
        { rewrite /D2 upd_eq. reflexivity. }
        rewrite /D2. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; apply H20; reflexivity].
        rewrite /D1. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; apply H9; reflexivity].
        apply HN1thr; assumption. }
    { iExists _, _. iFrame "Hk3 Hk6". }
    { rewrite /PAY. iLeft. iSplitR; [iPureIntro; reflexivity | iExact "Hpt"]. }
  Qed.

End ProofVmfault.

End VmfaultProof.
