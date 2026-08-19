(* ProofVmfault.v -- vmfault() over the SIE-agnostic sconf world.

   THE HART IS EXPLICIT AND [b] IS GENERIC.  vmfault is called both with
   interrupts on (usertrap) and inside copyin/copyout, so its contract is
   [b]-generic: every leaf hands the continuation back at a FRESH hart, and
   the shared epilogue [EPI] is itself a [wp_next (CID0 := CID) b (fun CIDe
   => ...)] -- ProofPipealloc.v's shape.  [cpu_own] is hart-indexed and only
   the three cpu_own-taking callees (kalloc / mappages / kfree) refresh it,
   so it is re-anchored with [cpu_own_transport] before each of those calls
   and at each of the five epilogue entry points.  The per-instruction hart
   binders are named after the pc offset the resumed hart executes ([C02],
   [C1cB], ...).

     uint64 vmfault(pagetable_t pagetable, uint64 psz, uint64 va, int read) {
       if (va >= psz) return 0;
       va = PGROUNDDOWN(va);
       if (ismapped(pagetable, va)) return 0;
       mem = (uint64)kalloc();            if (mem == 0) return 0;
       memset(mem, 0, PGSIZE);
       if (mappages(pagetable, va, PGSIZE, mem, PTE_W|PTE_U|PTE_R) != 0) {
         kfree(mem); return 0;
       }
       return mem;
     }

   xv6 `4f2fc8b` STOPPED CONFLATING THE TABLE IT IS HANDED WITH
   `myproc()->pagetable`: there is no myproc() call, no `p->sz` load (the
   size is the a1 ARGUMENT) and no `p->pagetable` load (the mappages goes
   into the a0 argument).  So this proof reads NO struct-proc cell, and the
   contract carries neither [p_sz]/[p_pagetable] nor their fractions.

   Spec of record: SpecVmfault.v -- stated at the [proc_pt] altitude, so the
   whole proof is bracketed by ProcPtOwn's three dovetail lemmas
   ([proc_pt_acc_rep0] to open the table into the exact [pt_rep0] view walk /
   mappages consume, [proc_pt_rebuild] on every failure arm, [proc_pt_grow] on
   the success arm).

   THE REGISTER ROLES, which is most of what moved in the bump:

     s4  the return value (zeroed at +0x0a, BEFORE the first branch)
     s1  the pagetable argument      (a0, saved at +0x20)
     s3  va0 = PGROUNDDOWN(va)       (+0x24)
     s2  the kalloc'd page           (+0x3e)
     a2  va -- never saved; dead after the [and]
     a1  psz -- read only by the branch at +0x0c

   TWO STRUCTURAL POINTS.

   1. LAZY SPILLS.  The 48-byte frame is pushed at +0x00 but only ra/s0/s4
      are stored there (slots 1/2/6).  s1 and s3 are spilled at +0x1c/+0x1e
      and s2 at +0x38 -- i.e. only on the paths that clobber them -- and each
      early-return path reloads exactly what it spilled before jumping to the
      join.  So the epilogue's [iAssert]ed continuation ([EPI], taken before
      the first branch) OWNS the three always-saved cells and takes the three
      lazily-spilled ones (slots 3/4/5) as an EXISTENTIAL wand argument: the
      short arm hands back the junk the push produced, each long arm the
      values it has just reloaded from.

   2. THE FIVE-WAY JOIN at +0x10 ([mv a0,s4] then the pop).  Every exit sets
      s4 to its return value, so [EPI] is parameterized by (the register file
      at +0x10, the return value [res], the post's disjunct at [res]).  Its
      register premise is exactly what the pop cannot restore: sp = spr,
      s4 = res, and agreement with [mm] on every callee-saved register other
      than sp/s0/s4 (which the epilogue reloads).  s1/s2/s3 fall under that
      clause -- the long paths reloaded them, the short path never touched
      them.

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
Require Import RiscvModelBytes RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore.
Require Import InstrBytes.
Require Import WpMmodeLeafBase.
Require Import RegFile HartTp WpNext.
Require Import CalleeSaved StackOwn.
Require Import IntrDefs WpSmodeIntr.
Require Import WpLock.
Require Import KallocInv.
Require Import PtBuild.
Require Import PtreeType.
Require Import UserPtTree.
Require Import CpuOwn.
Require Import KvmSpec.
Require Import ProcPt ProcPtOwn.
Require Import CodeVmfault.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import SpecIsmapped SpecKalloc SpecMemsetPage SpecMappages SpecKfree.
Require Import SpecVmfault.
Require Import KernelRvcDecode.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
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

Module VmfaultProof (Ismapped : ISMAPPED) (Kalloc : KALLOC)
                    (MemsetPage : MEMSETPAGE) (Mappages : MAPPAGES) (Kfree : KFREE)
  : VMFAULT.

Section ProofVmfault.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

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

  Lemma wp_vmfault_sconf_mem
      (γa : gname) (mm : regfile)
      (P : uptd) (M : gmap Z (bv 8)) (szv : mword 64) (K lvl : nat) (eb : bool)
      (p : mword 64) (b : bool) (lks : gset string)
    : wp_vmfault_sconf_mem_body γa mm P M szv K lvl eb p b lks.
  Proof.
    cbv beta delta [wp_vmfault_sconf_mem_body].
    intros pcE va va0 ret_tgt HK Htp Hroot Hsza1 Hszb Hlvl Hbelow.
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt #Htext Hpc Hpt Henv Hcont".
    iDestruct "Henv" as (γk) "(#Hlock & #Havail)".
    set (spr := add_vec (mm !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))).
    (* NO struct-proc cell addresses any more.  vmfault used to [ld] p->sz at
       +72 and p->pagetable at +80, which is why this proof carried [Hpsza] /
       [Hppta] and the [dqs] / [dqp] fractions; xv6 `4f2fc8b` replaced the
       first read with the a1 ARGUMENT ([Hsza1]) and the second with the a0
       one ([Hroot]), so both cells are gone from the code and from here. *)

    (* ===== PROLOGUE: 6-slot frame; only ra/s0/s4 saved here =========== *)
    iPoseProof (vfi_00 with "Htext") as "Hi00".
    iPoseProof (vfi_02 with "Htext") as "Hi02".
    iPoseProof (vfi_04 with "Htext") as "Hi04".
    iPoseProof (vfi_06 with "Htext") as "Hi06".
    iPoseProof (vfi_08 with "Htext") as "Hi08".
    iPoseProof (vfi_0a with "Htext") as "Hi0a".
    iPoseProof (vfi_0c with "Htext") as "Hi0c".
    assert (Hspm : mm !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))
                    = pa_stk (mm !!! Regidx csp_rs1) 6).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 61 : mword 6) mm K 6 b
              ltac:(lia) Hpush with "Hcg Hpc Hi00").
    iIntros (C02 Hs02) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (mm !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> mm).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> mm) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
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
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.vmfault + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,40(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.vmfault + 0x02)) (mword_of_int 5 : mword 6) Rra
              R1 (K - 6)%nat u40 b with "Hcg Hpc Hi02 [Hk1]").
    { iEval (rewrite HspR1 Hb1). iExact "Hk1". }
    iIntros (C04 Hs04) "Hcg Hpc Hk1".
    iEval (rgne) in "Hk1".
    iEval (rewrite HspR1 Hb1) in "Hk1".
    assert (HR1ra : R1 !!! Regidx Rra = mm !!! Regidx Rra)
      by (rewrite /R1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HR1ra) in "Hk1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.vmfault + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,32(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.vmfault + 0x04)) (mword_of_int 4 : mword 6) Rs0
              R1 (K - 6)%nat u32 b with "Hcg Hpc Hi04 [Hk2]").
    { iEval (rewrite HspR1 Hb2). iExact "Hk2". }
    iIntros (C06 Hs06) "Hcg Hpc Hk2".
    iEval (rgne) in "Hk2".
    iEval (rewrite HspR1 Hb2) in "Hk2".
    assert (HR1s0 : R1 !!! Regidx Rs0 = mm !!! Regidx Rs0)
      by (rewrite /R1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HR1s0) in "Hk2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.vmfault + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s4,0(sp) -- the ONLY callee-saved spill in the prologue *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.vmfault + 0x06)) (mword_of_int 0 : mword 6) Rs4
              R1 (K - 6)%nat u0 b with "Hcg Hpc Hi06 [Hk6]").
    { iEval (rewrite HspR1 Hb6). iExact "Hk6". }
    iIntros (C08 Hs08) "Hcg Hpc Hk6".
    iEval (rgne) in "Hk6".
    iEval (rewrite HspR1 Hb6) in "Hk6".
    assert (HR1s4 : R1 !!! Regidx Rs4 = mm !!! Regidx Rs4)
      by (rewrite /R1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HR1s4) in "Hk6".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.vmfault + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.addi4spn s0,sp,48 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.vmfault + 0x08)) (Cregidx (mword_of_int 0))
              (mword_of_int 12 : mword 8) Rs0 R1 (K - 6)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (C0a Hs0a) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> R1).
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.vmfault + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.li s4,0   (the return value, zeroed BEFORE the branch) *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.vmfault + 0x0a)) Rs4 (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) R2 (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi0a").
    iIntros (C0c Hs0c) "Hcg Hpc".
    set (R3 := <[Regidx Rs4 := regval_into_reg (mword_of_int 0 : mword 64)]> R2).
    assert (HR3sp : R3 !!! Regidx csp_rs1 = spr).
    { rewrite /R3. rewrite upd_ne; [| reg_neq].
      rewrite /R2. rewrite upd_ne; [| reg_neq]. exact HspR1. }
    assert (HR3a0 : R3 !!! Regidx Ra0 = page_base P.(ud_root)).
    { rewrite /R3. rewrite upd_ne; [| reg_neq].
      rewrite /R2. rewrite upd_ne; [| reg_neq].
      rewrite /R1. rewrite upd_ne; [| reg_neq]. exact Hroot. }
    assert (HR3a1 : R3 !!! Regidx Ra1 = szv).
    { rewrite /R3. rewrite upd_ne; [| reg_neq].
      rewrite /R2. rewrite upd_ne; [| reg_neq].
      rewrite /R1. rewrite upd_ne; [| reg_neq]. exact Hsza1. }
    assert (HR3a2 : R3 !!! Regidx Ra2 = va).
    { rewrite /R3. rewrite upd_ne; [| reg_neq].
      rewrite /R2. rewrite upd_ne; [| reg_neq].
      rewrite /R1. rewrite upd_ne; [reflexivity | reg_neq]. }
    assert (HR3s4 : R3 !!! Regidx Rs4 = mword_of_int 0)
      by (rewrite /R3 upd_eq; reflexivity).
    (* the callee-saved registers R3 shares with mm: everything but sp/s0/s4 *)
    assert (HR3thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs4 ->
              R3 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H20.
      rewrite /R3. rewrite upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H20; reflexivity].
      rewrite /R2. rewrite upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H8; reflexivity].
      rewrite /R1. rewrite upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H2; reflexivity].
      reflexivity. }
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.vmfault + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".

    (* ================================================================= *)
    (*  THE EPILOGUE / JOIN at +0x10, taken before the first branch.      *)
    (* ================================================================= *)
    iPoseProof (vfi_10 with "Htext") as "Hi10".
    iPoseProof (vfi_12 with "Htext") as "Hi12".
    iPoseProof (vfi_14 with "Htext") as "Hi14".
    iPoseProof (vfi_16 with "Htext") as "Hi16".
    iPoseProof (vfi_18 with "Htext") as "Hi18".
    iPoseProof (vfi_1a with "Htext") as "Hi1a".
    set (PAY := (fun res : mword 64 =>
      ((⌜res = mword_of_int 0⌝ ∗ proc_ptm P (uint szv) M)
       ∨ (∃ r : mword 64,
            ⌜res = r⌝ ∗ ⌜page_valid r⌝ ∗ ⌜(uint va < uint szv)%Z⌝ ∗
            ⌜P.(ud_um) !! svpn_of va0 = None⌝ ∗
            proc_ptm (uptd_insert P (svpn_of va0) r) (uint szv) M))%I)).
    set (EPI := (wp_next (CID0 := CID) b p (fun (CIDe : CpuId) =>
        ∀ (mj : regfile) (res : mword 64),
        ⌜ mj !!! Regidx csp_rs1 = spr
          /\ mj !!! Regidx Rs4 = res
          /\ (forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs4 ->
                mj !!! Regidx c = mm !!! Regidx c) ⌝ -∗
        sie_cap_gpr KT1 mj (K - 6)%nat b p -∗
        cpu_own lvl eb p b lks -∗
        pc_is (mword_of_int (KernelSyms.vmfault + 0x10) : mword 64) -∗
        (∃ w3 w4 w5 : mword 64,
           pa_stk sp0 3 ↦₈[KT1] w3 ∗ pa_stk sp0 4 ↦₈[KT1] w4 ∗ pa_stk sp0 5 ↦₈[KT1] w5) -∗
        PAY res -∗
        WP (Loop : expr riscv_lang)))%I).
    iAssert EPI with "[Hcont Hk1 Hk2 Hk6]" as "Hepi".
    { rewrite /EPI.
      iIntros (CIDe Hbe mj res) "(%Hjsp & %Hjs4 & %Hjthr) Hcg Hcnt Hpc Hjunk Hpost".
      iDestruct "Hjunk" as (w3 w4 w5) "(Hk3 & Hk4 & Hk5)".
      (* +0x10 c.mv a0,s4 *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.vmfault + 0x10)) Ra0 Rs4
                mj (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi10").
      iIntros (E12 Hse12) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (E0 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mj !!! Regidx Rs4))]> mj).
      assert (HE0sp : E0 !!! Regidx csp_rs1 = spr)
        by (rewrite /E0; rewrite upd_ne; [exact Hjsp | reg_neq]).
      assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x10) : mword 64) 2
                      = mword_of_int (KernelSyms.vmfault + 0x12))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp12) in "Hpc".
      (* +0x12 c.ldsp ra,40(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.vmfault + 0x12)) (mword_of_int 5 : mword 6) Rra
                E0 (K - 6)%nat (mm !!! Regidx Rra) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi12 [Hk1]").
      { iEval (rewrite HE0sp Hb1). iExact "Hk1". }
      iIntros (E14 Hse14) "Hcg Hpc Hk1". iEval (rewrite HE0sp Hb1) in "Hk1".
      set (E1 := <[Regidx Rra := regval_into_reg (mm !!! Regidx Rra)]> E0).
      assert (HE1sp : E1 !!! Regidx csp_rs1 = spr)
        by (rewrite /E1; rewrite upd_ne; [exact HE0sp | reg_neq]).
      assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x12) : mword 64) 2
                      = mword_of_int (KernelSyms.vmfault + 0x14))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp14) in "Hpc".
      (* +0x14 c.ldsp s0,32(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.vmfault + 0x14)) (mword_of_int 4 : mword 6) Rs0
                E1 (K - 6)%nat (mm !!! Regidx Rs0) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi14 [Hk2]").
      { iEval (rewrite HE1sp Hb2). iExact "Hk2". }
      iIntros (E16 Hse16) "Hcg Hpc Hk2". iEval (rewrite HE1sp Hb2) in "Hk2".
      set (E2 := <[Regidx Rs0 := regval_into_reg (mm !!! Regidx Rs0)]> E1).
      assert (HE2sp : E2 !!! Regidx csp_rs1 = spr)
        by (rewrite /E2; rewrite upd_ne; [exact HE1sp | reg_neq]).
      assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x14) : mword 64) 2
                      = mword_of_int (KernelSyms.vmfault + 0x16))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp16) in "Hpc".
      (* +0x16 c.ldsp s4,0(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.vmfault + 0x16)) (mword_of_int 0 : mword 6) Rs4
                E2 (K - 6)%nat (mm !!! Regidx Rs4) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi16 [Hk6]").
      { iEval (rewrite HE2sp Hb6). iExact "Hk6". }
      iIntros (E18 Hse18) "Hcg Hpc Hk6". iEval (rewrite HE2sp Hb6) in "Hk6".
      set (E3 := <[Regidx Rs4 := regval_into_reg (mm !!! Regidx Rs4)]> E2).
      assert (HE3sp : E3 !!! Regidx csp_rs1 = spr)
        by (rewrite /E3; rewrite upd_ne; [exact HE2sp | reg_neq]).
      assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x16) : mword 64) 2
                      = mword_of_int (KernelSyms.vmfault + 0x18))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp18) in "Hpc".
      (* +0x18 c.addi16sp sp,48 -- trade the frame back *)
      set (E4 := <[Regidx csp_rs1 := regval_into_reg
                    (add_vec (E3 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E3).
      assert (Hwv : add_vec (E3 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0).
      { rewrite HE3sp. unfold spr, sp0. apply frame_cancel_48. }
      assert (Hpop : E3 !!! Regidx csp_rs1
                     = pa_stk (add_vec (E3 !!! Regidx csp_rs1)
                                 (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6).
      { rewrite Hwv HE3sp. symmetry. exact Hsprstk. }
      iAssert (stack_own (KTR := KT1) sp0 6) with "[Hk1 Hk2 Hk3 Hk4 Hk5 Hk6]" as "Hframe6".
      { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
        iSplitL "Hk1"; [iExists _; iExact "Hk1" |].
        iSplitL "Hk2"; [iExists _; iExact "Hk2" |].
        iSplitL "Hk3"; [iExists _; iExact "Hk3" |].
        iSplitL "Hk4"; [iExists _; iExact "Hk4" |].
        iSplitL "Hk5"; [iExists _; iExact "Hk5" |].
        iSplitL "Hk6"; [iExists _; iExact "Hk6" |].
        done. }
      iEval (rewrite -Hwv) in "Hframe6".
      iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.vmfault + 0x18))
                (mword_of_int 3 : mword 6) E3 (K - 6)%nat 6 b Hpop
                with "Hcg Hpc Hi18 Hframe6").
      iIntros (E1a Hse1a) "Hcg Hpc".
      change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E3) with E4.
      assert (Hnk : ((K - 6) + 6)%nat = K) by lia.
      iEval (rewrite Hnk) in "Hcg".
      assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x18) : mword 64) 2
                      = mword_of_int (KernelSyms.vmfault + 0x1a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1a) in "Hpc".
      (* +0x1a c.ret *)
      assert (HE4ra : E4 !!! Regidx Rra = mm !!! Regidx Rra).
      { rewrite /E4. rewrite upd_ne; [| reg_neq].
        rewrite /E3. rewrite upd_ne; [| reg_neq].
        rewrite /E2. rewrite upd_ne; [| reg_neq].
        rewrite /E1 upd_eq. reflexivity. }
      assert (HE4a0 : E4 !!! Regidx Ra0 = res).
      { rewrite /E4. rewrite upd_ne; [| reg_neq].
        rewrite /E3. rewrite upd_ne; [| reg_neq].
        rewrite /E2. rewrite upd_ne; [| reg_neq].
        rewrite /E1. rewrite upd_ne; [| reg_neq].
        rewrite /E0 upd_eq. rewrite add_vec_zero_l. exact Hjs4. }
      assert (HE4thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs4 ->
                E4 !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H20.
        rewrite /E4. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; apply H2; reflexivity].
        rewrite /E3. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; apply H20; reflexivity].
        rewrite /E2. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; apply H8; reflexivity].
        rewrite /E1. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
        rewrite /E0. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
        apply Hjthr; assumption. }
      iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.vmfault + 0x1a)) Rra E4 K b
                ltac:(vm_compute; discriminate) with "Hcg Hpc Hi1a").
      iIntros (Eret Hseret) "Hcg Hpc". iEval (rgne) in "Hpc".
      assert (Hretf : ret_pc (E4 !!! Regidx Rra) = ret_tgt) by (rewrite HE4ra; reflexivity).
      iEval (rewrite Hretf) in "Hpc".
      iDestruct (cpu_own_transport CIDe Eret lvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("Hcont" $! Eret with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! E4 with "Hcg Hcnt Hpc [%] [Hpost]").
      2:{ rewrite /PAY. rewrite HE4a0.
          iDestruct "Hpost" as "[(%Hz & Hp) | Hs]".
          - iLeft. iSplitR; [iPureIntro; exact Hz | iExact "Hp"].
          - iRight. iExact "Hs". }
      { unfold callee_saved.
        assert (Hc2 : E4 !!! Regidx csp_rs1 = mm !!! Regidx csp_rs1).
        { rewrite /E4 upd_eq. exact Hwv. }
        assert (Hc8 : E4 !!! Regidx Rs0 = mm !!! Regidx Rs0).
        { rewrite /E4. rewrite upd_ne; [| reg_neq].
          rewrite /E3. rewrite upd_ne; [| reg_neq].
          rewrite /E2 upd_eq. reflexivity. }
        assert (Hc20 : E4 !!! Regidx Rs4 = mm !!! Regidx Rs4).
        { rewrite /E4. rewrite upd_ne; [| reg_neq].
          rewrite /E3 upd_eq. reflexivity. }
        split_and!;
          first [ exact Hc2 | exact Hc8 | exact Hc20
                | apply HE4thr; vm_compute; first [reflexivity | discriminate] ]. } }

    (* ================================================================= *)
    (*  +0x0c bltu a2,a1 : the [va < psz] test.                          *)
    (*  The size is the ARGUMENT now, so both operands are registers the  *)
    (*  caller set; no cell is read.                                     *)
    (* ================================================================= *)
    assert (Hrg3a2 : rget R3 Ra2 = R3 !!! Regidx Ra2) by (rgne; reflexivity).
    assert (Hrg3a1 : rget R3 Ra1 = R3 !!! Regidx Ra1) by (rgne; reflexivity).
    destruct (zopz0zI_u (rget R3 Ra2) (rget R3 Ra1)) eqn:Hcmp.
    2:{ (* ---- va >= psz: fall to the join at +0x10, return 0 ---- *)
      iApply (wp_bltu_fall_s_sconf (mword_of_int (KernelSyms.vmfault + 0x0c))
                (mword_of_int 16 : mword 13) Ra1 Ra2 R3 (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hcmp
                with "Hcg Hpc Hi0c").
      iIntros (C10 Hs10) "Hcg Hpc".
      assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x0c) : mword 64) 4
                      = mword_of_int (KernelSyms.vmfault + 0x10))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp10) in "Hpc".
      iDestruct (cpu_own_transport CID C10 lvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("Hepi" $! C10 with "[%]"); [wp_next_chain|].
      iApply ("Hepi" $! R3 (mword_of_int 0) with "[%] Hcg Hcnt Hpc [Hk3 Hk4 Hk5] [Hpt]").
      { split_and!.
        - exact HR3sp.
        - exact HR3s4.
        - exact HR3thr. }
      { iExists u24, u16, u8. iFrame "Hk3 Hk4 Hk5". }
      { rewrite /PAY. iLeft. iSplitR; [iPureIntro; reflexivity | iExact "Hpt"]. } }

    (* ---- va < psz: the real work, at +0x1c ---- *)
    assert (Hvalt : (uint va < uint szv)%Z).
    { rewrite -HR3a2 -HR3a1 -Hrg3a2 -Hrg3a1. unfold zopz0zI_u in Hcmp.
      apply Z.ltb_lt. exact Hcmp. }
    assert (Hvab : (uint va < 2 ^ 38)%Z)
      by (eapply Z.lt_le_trans; [exact Hvalt | exact Hszb]).
    pose proof (pgrounddown_bound va Hvab) as Hva0b4.
    change (2 ^ 38)%Z with 274877906944%Z in Hva0b4.
    assert (Hva0b : (uint va0 < 2 ^ 38)%Z).
    { change (2 ^ 38)%Z with 274877906944%Z. exact (vf_z_lt_maxva _ Hva0b4). }
    iPoseProof (vfi_1c with "Htext") as "Hi1c".
    iPoseProof (vfi_1e with "Htext") as "Hi1e".
    iPoseProof (vfi_20 with "Htext") as "Hi20".
    iPoseProof (vfi_22 with "Htext") as "Hi22".
    iPoseProof (vfi_24 with "Htext") as "Hi24".
    iPoseProof (vfi_28 with "Htext") as "Hi28".
    iPoseProof (vfi_2a with "Htext") as "Hi2a".
    iApply (wp_bltu_taken_s_sconf (mword_of_int (KernelSyms.vmfault + 0x0c))
              (mword_of_int 16 : mword 13) Ra1 Ra2 R3 (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hcmp
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0c").
    iApply bi.later_intro. iIntros (C1c Hs1c) "Hcg Hpc".
    assert (Htgt1c : add_vec (mword_of_int (KernelSyms.vmfault + 0x0c) : mword 64)
                       (sign_extend' 64 (mword_of_int 16 : mword 13))
                     = mword_of_int (KernelSyms.vmfault + 0x1c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt1c) in "Hpc".
    (* the two LAZY SPILLS: s1 and s3, only on the path that clobbers them *)
    assert (HR3s1 : R3 !!! Regidx Rs1 = mm !!! Regidx Rs1)
      by (apply HR3thr; vm_compute; first [reflexivity | discriminate]).
    assert (HR3s3 : R3 !!! Regidx Rs3 = mm !!! Regidx Rs3)
      by (apply HR3thr; vm_compute; first [reflexivity | discriminate]).
    assert (HR3s2 : R3 !!! Regidx Rs2 = mm !!! Regidx Rs2)
      by (apply HR3thr; vm_compute; first [reflexivity | discriminate]).
    (* +0x1c c.sdsp s1,24(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.vmfault + 0x1c)) (mword_of_int 3 : mword 6) Rs1
              R3 (K - 6)%nat u24 b with "Hcg Hpc Hi1c [Hk3]").
    { iEval (rewrite HR3sp Hb3). iExact "Hk3". }
    iIntros (C1e Hs1e) "Hcg Hpc Hk3".
    iEval (rgne) in "Hk3".
    iEval (rewrite HR3sp Hb3) in "Hk3".
    iEval (rewrite HR3s1) in "Hk3".
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x1c) : mword 64) 2
                    = mword_of_int (KernelSyms.vmfault + 0x1e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e c.sdsp s3,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.vmfault + 0x1e)) (mword_of_int 1 : mword 6) Rs3
              R3 (K - 6)%nat u8 b with "Hcg Hpc Hi1e [Hk5]").
    { iEval (rewrite HR3sp Hb5). iExact "Hk5". }
    iIntros (C20 Hs20) "Hcg Hpc Hk5".
    iEval (rgne) in "Hk5".
    iEval (rewrite HR3sp Hb5) in "Hk5".
    iEval (rewrite HR3s3) in "Hk5".
    assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x1e) : mword 64) 2
                    = mword_of_int (KernelSyms.vmfault + 0x20))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* +0x20 c.mv s1,a0   (s1 := the pagetable ARGUMENT) *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.vmfault + 0x20)) Rs1 Ra0
              R3 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi20").
    iIntros (C22 Hs22) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (L1 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (R3 !!! Regidx Ra0))]> R3).
    assert (HL1s1 : L1 !!! Regidx Rs1 = page_base P.(ud_root))
      by (rewrite /L1 upd_eq; rewrite add_vec_zero_l; exact HR3a0).
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x20) : mword 64) 2
                    = mword_of_int (KernelSyms.vmfault + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    (* +0x22 c.lui a5,0xfffff *)
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.vmfault + 0x22)) Ra5
              (sign_extend' 20 (mword_of_int 63 : mword 6)) (mword_of_int (-4096) : mword 64)
              L1 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              lui_m4096
              with "Hcg Hpc Hi22").
    iIntros (C24 Hs24) "Hcg Hpc".
    set (L2 := <[Regidx Ra5 := regval_into_reg (mword_of_int (-4096) : mword 64)]> L1).
    assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x22) : mword 64) 2
                    = mword_of_int (KernelSyms.vmfault + 0x24))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    (* +0x24 and s3,a2,a5   (s3 := PGROUNDDOWN(va); a2 is dead after this) *)
    assert (HL2and : and_vec (rget L2 Ra2) (rget L2 Ra5) = va0).
    { rgne. rgne. rewrite /L2 upd_eq. rewrite upd_ne; [| reg_neq].
      rewrite /L1. rewrite upd_ne; [| reg_neq]. rewrite HR3a2. reflexivity. }
    iApply (wp_and_s_sconf (mword_of_int (KernelSyms.vmfault + 0x24)) Rs3 Ra2 Ra5 va0
              L2 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              HL2and with "Hcg Hpc Hi24").
    iIntros (C28 Hs28) "Hcg Hpc".
    set (L3 := <[Regidx Rs3 := regval_into_reg va0]> L2).
    assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x24) : mword 64) 4
                    = mword_of_int (KernelSyms.vmfault + 0x28))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    (* +0x28 c.mv a1,s3  -- a0 already holds the pagetable, untouched since entry *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.vmfault + 0x28)) Ra1 Rs3
              L3 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi28").
    iIntros (C2a Hs2a) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (L4 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (L3 !!! Regidx Rs3))]> L3).
    assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x28) : mword 64) 2
                    = mword_of_int (KernelSyms.vmfault + 0x2a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2a) in "Hpc".
    (* +0x2a jal ra,ismapped *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.vmfault + 0x2a)) Rra
              (mword_of_int 2097082 : mword 21) L4 (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi2a").
    iIntros (Cim Hsim) "Hcg Hpc".
    set (L5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.vmfault + 0x2a) : mword 64) 4)]> L4).
    assert (Htgtim : add_vec (mword_of_int (KernelSyms.vmfault + 0x2a) : mword 64)
                       (sign_extend' 64 (mword_of_int 2097082 : mword 21))
                     = mword_of_int KernelSyms.ismapped)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtim) in "Hpc".
    (* the register facts at ismapped's entry *)
    assert (HL5a1 : L5 !!! Regidx Ra1 = va0).
    { rewrite /L5. rewrite upd_ne; [| reg_neq].
      rewrite /L4 upd_eq. rewrite add_vec_zero_l.
      rewrite /L3 upd_eq. reflexivity. }
    assert (HL5a0 : L5 !!! Regidx Ra0 = page_base P.(ud_root)).
    { rewrite /L5. rewrite upd_ne; [| reg_neq].
      rewrite /L4. rewrite upd_ne; [| reg_neq].
      rewrite /L3. rewrite upd_ne; [| reg_neq].
      rewrite /L2. rewrite upd_ne; [| reg_neq].
      rewrite /L1. rewrite upd_ne; [| reg_neq]. exact HR3a0. }
    assert (HL5s1 : L5 !!! Regidx Rs1 = page_base P.(ud_root)).
    { rewrite /L5. rewrite upd_ne; [| reg_neq].
      rewrite /L4. rewrite upd_ne; [| reg_neq].
      rewrite /L3. rewrite upd_ne; [| reg_neq].
      rewrite /L2. rewrite upd_ne; [| reg_neq]. exact HL1s1. }
    assert (HL5s3 : L5 !!! Regidx Rs3 = va0).
    { rewrite /L5. rewrite upd_ne; [| reg_neq].
      rewrite /L4. rewrite upd_ne; [| reg_neq].
      rewrite /L3 upd_eq. reflexivity. }
    assert (HL5s4 : L5 !!! Regidx Rs4 = mword_of_int 0).
    { rewrite /L5 /L4 /L3 /L2 /L1.
      repeat (rewrite upd_ne; [| reg_neq]). exact HR3s4. }
    assert (HL5sp : L5 !!! Regidx csp_rs1 = spr).
    { rewrite /L5 /L4 /L3 /L2 /L1.
      repeat (rewrite upd_ne; [| reg_neq]). exact HR3sp. }
    assert (HL5ra : L5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.vmfault + 0x2a) : mword 64) 4)
      by (rewrite /L5 upd_eq; reflexivity).
    (* s2 is NOT in the exclusion list here: nothing has touched it yet *)
    assert (HL5thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs3 -> c <> Rs4 ->
              L5 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9 H19 H20.
      rewrite /L5. rewrite upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /L4. rewrite upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /L3. rewrite upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H19; reflexivity].
      rewrite /L2. rewrite upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /L1. rewrite upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H9; reflexivity].
      apply HR3thr; assumption. }
    (* ---- open the table into the exact represented view ---- *)
    iDestruct (proc_ptm_acc_rep0 P (uint szv) M with "Hpt") as
      (t m_ad) "(%Hrep & %Hview & %Hbase & %Hwf & Hptree & Hown)".
    assert (HL5root : L5 !!! Regidx Ra0
                      = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))).
    { rewrite HL5a0 Hbase. reflexivity. }
    (* ---- ismapped(pagetable, va0) ---- *)
    iApply (Ismapped.wp_ismapped_sconf L5 t m_ad (K - 6)%nat (DfracOwn 1) b p
              ltac:(lia) HL5root ltac:(rewrite HL5a1; exact Hva0b) Hrep
              with "Hcg Htext Hpc Hptree").
    iIntros (Cir Hsir mi) "Hcg Hpc Hptree %Hics %Hiv".
    rewrite HL5a1 in Hiv.
    assert (Hret2e : ret_pc (L5 !!! Regidx Rra) = mword_of_int (KernelSyms.vmfault + 0x2e)).
    { rewrite HL5ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret2e) in "Hpc".
    assert (Hmisp : mi !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hics csp_rs1 ltac:(vm_compute; reflexivity)). exact HL5sp. }
    assert (Hmis1 : mi !!! Regidx Rs1 = page_base P.(ud_root)).
    { rewrite (callee_saved_lookup Hics Rs1 ltac:(vm_compute; reflexivity)). exact HL5s1. }
    assert (Hmis3 : mi !!! Regidx Rs3 = va0).
    { rewrite (callee_saved_lookup Hics Rs3 ltac:(vm_compute; reflexivity)). exact HL5s3. }
    assert (Hmithr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs3 -> c <> Rs4 ->
              mi !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9 H19 H20.
      rewrite (callee_saved_lookup Hics c Hc). apply HL5thr; assumption. }
    iPoseProof (vfi_2e with "Htext") as "Hi2e".
    iPoseProof (vfi_30 with "Htext") as "Hi30".
    (* +0x2e c.li s4,0 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.vmfault + 0x2e)) Rs4 (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) mi (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi2e").
    iIntros (C30 Hs30) "Hcg Hpc".
    set (N1 := <[Regidx Rs4 := regval_into_reg (mword_of_int 0 : mword 64)]> mi).
    assert (HN1s4 : N1 !!! Regidx Rs4 = mword_of_int 0)
      by (rewrite /N1 upd_eq; reflexivity).
    assert (HN1sp : N1 !!! Regidx csp_rs1 = spr)
      by (rewrite /N1; rewrite upd_ne; [exact Hmisp | reg_neq]).
    assert (HN1s1 : N1 !!! Regidx Rs1 = page_base P.(ud_root))
      by (rewrite /N1; rewrite upd_ne; [exact Hmis1 | reg_neq]).
    assert (HN1s3 : N1 !!! Regidx Rs3 = va0)
      by (rewrite /N1; rewrite upd_ne; [exact Hmis3 | reg_neq]).
    assert (HN1a0 : N1 !!! Regidx Ra0 = mi !!! Regidx Ra0)
      by (rewrite /N1; rewrite upd_ne; [reflexivity | reg_neq]).
    assert (HN1thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs3 -> c <> Rs4 ->
              N1 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9 H19 H20.
      rewrite /N1. rewrite upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H20; reflexivity].
      apply Hmithr; assumption. }
    assert (HN1s2 : N1 !!! Regidx Rs2 = mm !!! Regidx Rs2)
      by (apply HN1thr; vm_compute; first [reflexivity | discriminate]).
    assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x2e) : mword 64) 2
                    = mword_of_int (KernelSyms.vmfault + 0x30))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* ================================================================= *)
    (*  +0x30 c.beqz a0 : the ismapped verdict.                           *)
    (* ================================================================= *)
    destruct Hiv as [(Ha0z & Hnone) | (w & Hsome & Ha0one)].
    { (* ================= UNMAPPED: allocate ========================= *)
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.vmfault + 0x30))
                (mword_of_int 4 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                N1 (K - 6)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HN1a0 Ha0z; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi30").
      iApply bi.later_intro. iIntros (C38 Hs38) "Hcg Hpc".
      assert (Htgt38 : add_vec (mword_of_int (KernelSyms.vmfault + 0x30) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 4 : mword 8) ('b"0"))))
              = mword_of_int (KernelSyms.vmfault + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt38) in "Hpc".
      iPoseProof (vfi_38 with "Htext") as "Hi38".
      iPoseProof (vfi_3a with "Htext") as "Hi3a".
      iPoseProof (vfi_3e with "Htext") as "Hi3e".
      iPoseProof (vfi_40 with "Htext") as "Hi40".
      (* +0x38 c.sdsp s2,16(sp) -- the THIRD lazy spill *)
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.vmfault + 0x38)) (mword_of_int 2 : mword 6) Rs2
                N1 (K - 6)%nat u16 b with "Hcg Hpc Hi38 [Hk4]").
      { iEval (rewrite HN1sp Hb4). iExact "Hk4". }
      iIntros (C3a Hs3a) "Hcg Hpc Hk4".
      iEval (rgne) in "Hk4".
      iEval (rewrite HN1sp Hb4) in "Hk4".
      iEval (rewrite HN1s2) in "Hk4".
      assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x38) : mword 64) 2
                      = mword_of_int (KernelSyms.vmfault + 0x3a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3a) in "Hpc".
      (* +0x3a jal ra,kalloc *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.vmfault + 0x3a)) Rra
                (mword_of_int 2094606 : mword 21) N1 (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi3a").
      iIntros (Cka Hska) "Hcg Hpc".
      set (A1 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.vmfault + 0x3a) : mword 64) 4)]> N1).
      assert (Htgtka : add_vec (mword_of_int (KernelSyms.vmfault + 0x3a) : mword 64)
                         (sign_extend' 64 (mword_of_int 2094606 : mword 21))
                       = mword_of_int KernelSyms.kalloc)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtka) in "Hpc".
      assert (HA1ra : A1 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KernelSyms.vmfault + 0x3a) : mword 64) 4)
        by (rewrite /A1 upd_eq; reflexivity).
      assert (HA1sp : A1 !!! Regidx csp_rs1 = spr)
        by (rewrite /A1; rewrite upd_ne; [exact HN1sp | reg_neq]).
      assert (HA1s1 : A1 !!! Regidx Rs1 = page_base P.(ud_root))
        by (rewrite /A1; rewrite upd_ne; [exact HN1s1 | reg_neq]).
      assert (HA1s3 : A1 !!! Regidx Rs3 = va0)
        by (rewrite /A1; rewrite upd_ne; [exact HN1s3 | reg_neq]).
      assert (HA1s4 : A1 !!! Regidx Rs4 = mword_of_int 0)
        by (rewrite /A1; rewrite upd_ne; [exact HN1s4 | reg_neq]).
      assert (HA1thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs3 -> c <> Rs4 ->
                A1 !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H9 H19 H20.
        rewrite /A1. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
        apply HN1thr; assumption. }
      iDestruct (cpu_own_transport CID Cka lvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iApply (Kalloc.wp_kalloc_sconf KT1 γa γk (mword_of_int (KernelSyms.kmem + 24))
                A1 None lvl eb p (K - 6)%nat b _
                ltac:(lia) ltac:(reflexivity) Hlvl Hbelow
                with "Hcg Hcnt Htext Hpc Hlock Havail").
      all: try lkbelow.
      iIntros (Ckr Hskr mk) "Hcg Hcnt Hpc %Hkcs Hkpost".
      assert (Hret3e : ret_pc (A1 !!! Regidx Rra) = mword_of_int (KernelSyms.vmfault + 0x3e)).
      { rewrite HA1ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hret3e) in "Hpc".
      assert (Hmksp : mk !!! Regidx csp_rs1 = spr).
      { rewrite (callee_saved_lookup Hkcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HA1sp. }
      assert (Hmks1 : mk !!! Regidx Rs1 = page_base P.(ud_root)).
      { rewrite (callee_saved_lookup Hkcs Rs1 ltac:(vm_compute; reflexivity)). exact HA1s1. }
      assert (Hmks3 : mk !!! Regidx Rs3 = va0).
      { rewrite (callee_saved_lookup Hkcs Rs3 ltac:(vm_compute; reflexivity)). exact HA1s3. }
      assert (Hmks4 : mk !!! Regidx Rs4 = mword_of_int 0).
      { rewrite (callee_saved_lookup Hkcs Rs4 ltac:(vm_compute; reflexivity)). exact HA1s4. }
      assert (Hmkthr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs3 -> c <> Rs4 ->
                mk !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H9 H19 H20.
        rewrite (callee_saved_lookup Hkcs c Hc). apply HA1thr; assumption. }
      (* +0x3e c.mv s2,a0 *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.vmfault + 0x3e)) Rs2 Ra0
                mk (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi3e").
      iIntros (C40 Hs40) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (A2 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (mk !!! Regidx Ra0))]> mk).
      assert (HA2a0 : A2 !!! Regidx Ra0 = mk !!! Regidx Ra0)
        by (rewrite /A2; rewrite upd_ne; [reflexivity | reg_neq]).
      assert (HA2s2 : A2 !!! Regidx Rs2 = mk !!! Regidx Ra0)
        by (rewrite /A2 upd_eq; apply add_vec_zero_l).
      assert (HA2sp : A2 !!! Regidx csp_rs1 = spr)
        by (rewrite /A2; rewrite upd_ne; [exact Hmksp | reg_neq]).
      assert (HA2s1 : A2 !!! Regidx Rs1 = page_base P.(ud_root))
        by (rewrite /A2; rewrite upd_ne; [exact Hmks1 | reg_neq]).
      assert (HA2s3 : A2 !!! Regidx Rs3 = va0)
        by (rewrite /A2; rewrite upd_ne; [exact Hmks3 | reg_neq]).
      assert (HA2s4 : A2 !!! Regidx Rs4 = mword_of_int 0)
        by (rewrite /A2; rewrite upd_ne; [exact Hmks4 | reg_neq]).
      assert (HA2thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                A2 !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H9 H18 H19 H20.
        rewrite /A2. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; apply H18; reflexivity].
        apply Hmkthr; assumption. }
      assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x3e) : mword 64) 2
                      = mword_of_int (KernelSyms.vmfault + 0x40))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp40) in "Hpc".
      iDestruct "Hkpost" as "[(%Hnull & _ & _) | (%Hpv & Hpage & _)]".
      { (* ---- kalloc returned 0: +0x74, restore the three spills ---- *)
        iPoseProof (vfi_74 with "Htext") as "Hi74".
        iPoseProof (vfi_76 with "Htext") as "Hi76".
        iPoseProof (vfi_78 with "Htext") as "Hi78".
        iPoseProof (vfi_7a with "Htext") as "Hi7a".
        iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.vmfault + 0x40))
                  (mword_of_int 26 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                  A2 (K - 6)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite HA2a0 Hnull; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi40").
        iApply bi.later_intro. iIntros (C74 Hs74) "Hcg Hpc".
        assert (Htgt74 : add_vec (mword_of_int (KernelSyms.vmfault + 0x40) : mword 64)
                  (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 26 : mword 8) ('b"0"))))
                = mword_of_int (KernelSyms.vmfault + 0x74)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt74) in "Hpc".
        (* +0x74 c.ldsp s1,24(sp) *)
        iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.vmfault + 0x74)) (mword_of_int 3 : mword 6) Rs1
                  A2 (K - 6)%nat (mm !!! Regidx Rs1) b (dqm:=DfracOwn 1)
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi74 [Hk3]").
        { iEval (rewrite HA2sp Hb3). iExact "Hk3". }
        iIntros (C76 Hs76) "Hcg Hpc Hk3". iEval (rewrite HA2sp Hb3) in "Hk3".
        set (B1 := <[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> A2).
        assert (HB1sp : B1 !!! Regidx csp_rs1 = spr)
          by (rewrite /B1; rewrite upd_ne; [exact HA2sp | reg_neq]).
        assert (Hpp76 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x74) : mword 64) 2
                        = mword_of_int (KernelSyms.vmfault + 0x76))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp76) in "Hpc".
        (* +0x76 c.ldsp s2,16(sp) *)
        iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.vmfault + 0x76)) (mword_of_int 2 : mword 6) Rs2
                  B1 (K - 6)%nat (mm !!! Regidx Rs2) b (dqm:=DfracOwn 1)
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi76 [Hk4]").
        { iEval (rewrite HB1sp Hb4). iExact "Hk4". }
        iIntros (C78 Hs78) "Hcg Hpc Hk4". iEval (rewrite HB1sp Hb4) in "Hk4".
        set (B2 := <[Regidx Rs2 := regval_into_reg (mm !!! Regidx Rs2)]> B1).
        assert (HB2sp : B2 !!! Regidx csp_rs1 = spr)
          by (rewrite /B2; rewrite upd_ne; [exact HB1sp | reg_neq]).
        assert (Hpp78 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x76) : mword 64) 2
                        = mword_of_int (KernelSyms.vmfault + 0x78))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp78) in "Hpc".
        (* +0x78 c.ldsp s3,8(sp) *)
        iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.vmfault + 0x78)) (mword_of_int 1 : mword 6) Rs3
                  B2 (K - 6)%nat (mm !!! Regidx Rs3) b (dqm:=DfracOwn 1)
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi78 [Hk5]").
        { iEval (rewrite HB2sp Hb5). iExact "Hk5". }
        iIntros (C7a Hs7a) "Hcg Hpc Hk5". iEval (rewrite HB2sp Hb5) in "Hk5".
        set (B3 := <[Regidx Rs3 := regval_into_reg (mm !!! Regidx Rs3)]> B2).
        assert (Hpp7a : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x78) : mword 64) 2
                        = mword_of_int (KernelSyms.vmfault + 0x7a))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp7a) in "Hpc".
        (* +0x7a c.j -0x6a *)
        iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.vmfault + 0x7a))
                  (sign_extend' 21 (concat_vec (mword_of_int 1995 : mword 11) ('b"0")))
                  B3 (K - 6)%nat b ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi7a").
        iIntros (C10A Hs10A). iApply bi.later_intro. iIntros "Hcg Hpc".
        assert (Hjt7a : add_vec (mword_of_int (KernelSyms.vmfault + 0x7a) : mword 64)
                  (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1995 : mword 11) ('b"0"))))
                = mword_of_int (KernelSyms.vmfault + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjt7a) in "Hpc".
        iDestruct (proc_ptm_rebuild P (uint szv) M t m_ad Hwf Hview Hrep Hbase with "Hptree Hown") as "Hpt".
        iDestruct (cpu_own_transport Ckr C10A lvl eb p b ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        iSpecialize ("Hepi" $! C10A with "[%]"); [wp_next_chain|].
        iApply ("Hepi" $! B3 (mword_of_int 0) with "[%] Hcg Hcnt Hpc [Hk3 Hk4 Hk5] [Hpt]").
        { split_and!.
          - rewrite /B3. rewrite upd_ne; [exact HB2sp | reg_neq].
          - rewrite /B3. rewrite upd_ne; [| reg_neq].
            rewrite /B2. rewrite upd_ne; [| reg_neq].
            rewrite /B1. rewrite upd_ne; [exact HA2s4 | reg_neq].
          - intros c Hc H2 H8 H20.
            destruct (decide (c = Rs1)) as [->|H9].
            { rewrite /B3. rewrite upd_ne; [| reg_neq].
              rewrite /B2. rewrite upd_ne; [| reg_neq]. rewrite /B1 upd_eq. reflexivity. }
            destruct (decide (c = Rs2)) as [->|H18].
            { rewrite /B3. rewrite upd_ne; [| reg_neq]. rewrite /B2 upd_eq. reflexivity. }
            destruct (decide (c = Rs3)) as [->|H19].
            { rewrite /B3 upd_eq. reflexivity. }
            rewrite /B3. rewrite upd_ne;
              [| intros Hx; injection Hx as Hx2; subst c; apply H19; reflexivity].
            rewrite /B2. rewrite upd_ne;
              [| intros Hx; injection Hx as Hx2; subst c; apply H18; reflexivity].
            rewrite /B1. rewrite upd_ne;
              [| intros Hx; injection Hx as Hx2; subst c; apply H9; reflexivity].
            apply HA2thr; assumption. }
        { iExists _, _, _. iFrame "Hk3 Hk4 Hk5". }
        { rewrite /PAY. iLeft. iSplitR; [iPureIntro; reflexivity | iExact "Hpt"]. } }
      (* ---- kalloc returned a page r ---- *)
      set (r := (mk !!! Regidx Ra0 : mword 64)).
      assert (Hpv' : page_valid r) by exact Hpv.
      pose proof Hpv' as Hpvd. destruct Hpvd as [Hral Hrrng].
      unfold page_in_range, kmem_lo, kmem_hi in Hrrng.
      assert (Hnz : (zero_reg : mword 64) = nullp) by (apply bv_eq; vm_compute; reflexivity).
      iPoseProof (vfi_42 with "Htext") as "Hi42".
      iPoseProof (vfi_44 with "Htext") as "Hi44".
      iPoseProof (vfi_46 with "Htext") as "Hi46".
      iPoseProof (vfi_48 with "Htext") as "Hi48".
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.vmfault + 0x40))
                (mword_of_int 26 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                A2 (K - 6)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HA2a0; apply eq_vec_false_iff; rewrite Hnz;
                      exact (page_valid_ne_null _ Hpv))
                with "Hcg Hpc Hi40").
      iIntros (C42 Hs42) "Hcg Hpc".
      assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x40) : mword 64) 2
                      = mword_of_int (KernelSyms.vmfault + 0x42))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      (* +0x42 c.mv s4,a0   (s4 := mem, the success return value) *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.vmfault + 0x42)) Rs4 Ra0
                A2 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi42").
      iIntros (C44 Hs44) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (A3 := <[Regidx Rs4 := regval_into_reg (add_vec zero_reg (A2 !!! Regidx Ra0))]> A2).
      assert (HA3s4 : A3 !!! Regidx Rs4 = r)
        by (rewrite /A3 upd_eq; rewrite add_vec_zero_l; exact HA2a0).
      assert (HA3a0 : A3 !!! Regidx Ra0 = r)
        by (rewrite /A3; rewrite upd_ne; [exact HA2a0 | reg_neq]).
      assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x42) : mword 64) 2
                      = mword_of_int (KernelSyms.vmfault + 0x44))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp44) in "Hpc".
      (* +0x44 c.lui a2,1 *)
      iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.vmfault + 0x44)) Ra2
                (sign_extend' 20 (mword_of_int 1 : mword 6)) (mword_of_int 4096 : mword 64)
                A3 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi44").
      iIntros (C46 Hs46) "Hcg Hpc".
      set (A4 := <[Regidx Ra2 := regval_into_reg (mword_of_int 4096 : mword 64)]> A3).
      assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x44) : mword 64) 2
                      = mword_of_int (KernelSyms.vmfault + 0x46))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp46) in "Hpc".
      (* +0x46 c.li a1,0 *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.vmfault + 0x46)) Ra1 (mword_of_int 0 : mword 6)
                (mword_of_int 0 : mword 64) A4 (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi46").
      iIntros (C48 Hs48) "Hcg Hpc".
      set (A5 := <[Regidx Ra1 := regval_into_reg (mword_of_int 0 : mword 64)]> A4).
      assert (Hpp48 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x46) : mword 64) 2
                      = mword_of_int (KernelSyms.vmfault + 0x48))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp48) in "Hpc".
      (* +0x48 jal ra,memset *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.vmfault + 0x48)) Rra
                (mword_of_int 2095002 : mword 21) A5 (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi48").
      iIntros (Cms Hsms) "Hcg Hpc".
      set (A6 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.vmfault + 0x48) : mword 64) 4)]> A5).
      assert (Htgtms : add_vec (mword_of_int (KernelSyms.vmfault + 0x48) : mword 64)
                         (sign_extend' 64 (mword_of_int 2095002 : mword 21))
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
                      = add_vec_int (mword_of_int (KernelSyms.vmfault + 0x48) : mword 64) 4)
        by (rewrite /A6 upd_eq; reflexivity).
      assert (HA6sp : A6 !!! Regidx csp_rs1 = spr).
      { rewrite /A6 /A5 /A4 /A3.
        repeat (rewrite upd_ne; [| reg_neq]). exact HA2sp. }
      assert (HA6s1 : A6 !!! Regidx Rs1 = page_base P.(ud_root)).
      { rewrite /A6 /A5 /A4 /A3.
        repeat (rewrite upd_ne; [| reg_neq]). exact HA2s1. }
      assert (HA6s2 : A6 !!! Regidx Rs2 = r).
      { rewrite /A6 /A5 /A4 /A3.
        repeat (rewrite upd_ne; [| reg_neq]). exact HA2s2. }
      assert (HA6s3 : A6 !!! Regidx Rs3 = va0).
      { rewrite /A6 /A5 /A4 /A3.
        repeat (rewrite upd_ne; [| reg_neq]). exact HA2s3. }
      assert (HA6s4 : A6 !!! Regidx Rs4 = r).
      { rewrite /A6. rewrite upd_ne; [| reg_neq].
        rewrite /A5. rewrite upd_ne; [| reg_neq].
        rewrite /A4. rewrite upd_ne; [| reg_neq]. exact HA3s4. }
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
          [| intros Hx; injection Hx as Hx2; subst c; apply H20; reflexivity].
        apply HA2thr; assumption. }
      (* ---- memset(mem, 0, PGSIZE) ---- *)
      (* the VALUE-PRESERVING form: what the page holds after this is the
         whole of vmfault's contribution to the process's memory, and it is
         ZERO -- which is why the abstract view does not move. *)
      iApply (MemsetPage.wp_memset_page_val_sconf KT1 A6 (K - 6)%nat (mword_of_int 0 : mword 64) b p
                ltac:(lia) ltac:(rewrite HA6a0; exact Hpv) HA6a1 HA6a2
                with "Hcg Htext Hpc [Hpage]").
      { iEval (rewrite HA6a0). iExact "Hpage". }
      iIntros (Cse Hsse ms) "Hcg Hpc Hzpage %Hmscs".
      iEval (rewrite HA6a0) in "Hzpage".
      assert (Hcb : nth_byte (autocast (T := mword)
                      (subrange_vec_dec (mword_of_int 0 : mword 64)
                         (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0 = bv_0 8)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hcb) in "Hzpage".
      assert (Hret4c : ret_pc (A6 !!! Regidx Rra) = mword_of_int (KernelSyms.vmfault + 0x4c)).
      { rewrite HA6ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hret4c) in "Hpc".
      assert (Hmssp : ms !!! Regidx csp_rs1 = spr).
      { rewrite (callee_saved_lookup Hmscs csp_rs1 ltac:(vm_compute; reflexivity)). exact HA6sp. }
      assert (Hmss1 : ms !!! Regidx Rs1 = page_base P.(ud_root)).
      { rewrite (callee_saved_lookup Hmscs Rs1 ltac:(vm_compute; reflexivity)). exact HA6s1. }
      assert (Hmss2 : ms !!! Regidx Rs2 = r).
      { rewrite (callee_saved_lookup Hmscs Rs2 ltac:(vm_compute; reflexivity)). exact HA6s2. }
      assert (Hmss3 : ms !!! Regidx Rs3 = va0).
      { rewrite (callee_saved_lookup Hmscs Rs3 ltac:(vm_compute; reflexivity)). exact HA6s3. }
      assert (Hmss4 : ms !!! Regidx Rs4 = r).
      { rewrite (callee_saved_lookup Hmscs Rs4 ltac:(vm_compute; reflexivity)). exact HA6s4. }
      assert (Hmsthr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                ms !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H9 H18 H19 H20.
        rewrite (callee_saved_lookup Hmscs c Hc). apply HA6thr; assumption. }
      iPoseProof (vfi_4c with "Htext") as "Hi4c".
      iPoseProof (vfi_4e with "Htext") as "Hi4e".
      iPoseProof (vfi_50 with "Htext") as "Hi50".
      iPoseProof (vfi_52 with "Htext") as "Hi52".
      iPoseProof (vfi_54 with "Htext") as "Hi54".
      iPoseProof (vfi_56 with "Htext") as "Hi56".
      iPoseProof (vfi_5a with "Htext") as "Hi5a".
      (* +0x4c c.li a4,22 *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.vmfault + 0x4c)) Ra4 (mword_of_int 22 : mword 6)
                (mword_of_int 22 : mword 64) ms (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi4c").
      iIntros (C4e Hs4e) "Hcg Hpc".
      set (G1 := <[Regidx Ra4 := regval_into_reg (mword_of_int 22 : mword 64)]> ms).
      assert (Hpp4e : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x4c) : mword 64) 2
                      = mword_of_int (KernelSyms.vmfault + 0x4e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4e) in "Hpc".
      (* +0x4e c.mv a3,s2 *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.vmfault + 0x4e)) Ra3 Rs2
                G1 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi4e").
      iIntros (C50 Hs50) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (G2 := <[Regidx Ra3 := regval_into_reg (add_vec zero_reg (G1 !!! Regidx Rs2))]> G1).
      assert (Hpp50 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x4e) : mword 64) 2
                      = mword_of_int (KernelSyms.vmfault + 0x50))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp50) in "Hpc".
      (* +0x50 c.lui a2,1 *)
      iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.vmfault + 0x50)) Ra2
                (sign_extend' 20 (mword_of_int 1 : mword 6)) (mword_of_int 4096 : mword 64)
                G2 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi50").
      iIntros (C52 Hs52) "Hcg Hpc".
      set (G3 := <[Regidx Ra2 := regval_into_reg (mword_of_int 4096 : mword 64)]> G2).
      assert (Hpp52 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x50) : mword 64) 2
                      = mword_of_int (KernelSyms.vmfault + 0x52))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp52) in "Hpc".
      (* +0x52 c.mv a1,s3 *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.vmfault + 0x52)) Ra1 Rs3
                G3 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi52").
      iIntros (C54 Hs54) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (G4 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (G3 !!! Regidx Rs3))]> G3).
      assert (Hpp54 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x52) : mword 64) 2
                      = mword_of_int (KernelSyms.vmfault + 0x54))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp54) in "Hpc".
      (* +0x54 c.mv a0,s1   (the pagetable ARGUMENT -- not p->pagetable) *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.vmfault + 0x54)) Ra0 Rs1
                G4 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi54").
      iIntros (C56 Hs56) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (G5 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (G4 !!! Regidx Rs1))]> G4).
      assert (Hpp56 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x54) : mword 64) 2
                      = mword_of_int (KernelSyms.vmfault + 0x56))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp56) in "Hpc".
      (* +0x56 jal ra,mappages *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.vmfault + 0x56)) Rra
                (mword_of_int 2095862 : mword 21) G5 (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi56").
      iIntros (Cmg Hsmg) "Hcg Hpc".
      set (G6 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.vmfault + 0x56) : mword 64) 4)]> G5).
      assert (Htgtmap : add_vec (mword_of_int (KernelSyms.vmfault + 0x56) : mword 64)
                          (sign_extend' 64 (mword_of_int 2095862 : mword 21))
                        = mword_of_int KernelSyms.mappages)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtmap) in "Hpc".
      (* the register facts at mappages' entry *)
      assert (HG4s1 : G4 !!! Regidx Rs1 = page_base P.(ud_root)).
      { rewrite /G4 /G3 /G2 /G1.
        repeat (rewrite upd_ne; [| reg_neq]). exact Hmss1. }
      assert (HG6a0 : G6 !!! Regidx Ra0
                      = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))).
      { rewrite /G6. rewrite upd_ne; [| reg_neq].
        rewrite /G5 upd_eq. rewrite add_vec_zero_l. rewrite HG4s1.
        rewrite Hbase. reflexivity. }
      assert (HG6a1 : G6 !!! Regidx Ra1 = va0).
      { rewrite /G6. rewrite upd_ne; [| reg_neq].
        rewrite /G5. rewrite upd_ne; [| reg_neq].
        rewrite /G4 upd_eq. rewrite add_vec_zero_l.
        rewrite /G3. rewrite upd_ne; [| reg_neq].
        rewrite /G2. rewrite upd_ne; [| reg_neq].
        rewrite /G1. rewrite upd_ne; [| reg_neq]. exact Hmss3. }
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
                      = add_vec_int (mword_of_int (KernelSyms.vmfault + 0x56) : mword 64) 4)
        by (rewrite /G6 upd_eq; reflexivity).
      assert (HG6sp : G6 !!! Regidx csp_rs1 = spr).
      { rewrite /G6 /G5 /G4 /G3 /G2 /G1.
        repeat (rewrite upd_ne; [| reg_neq]). exact Hmssp. }
      assert (HG6s1 : G6 !!! Regidx Rs1 = page_base P.(ud_root)).
      { rewrite /G6 /G5 /G4 /G3 /G2 /G1.
        repeat (rewrite upd_ne; [| reg_neq]). exact Hmss1. }
      assert (HG6s2 : G6 !!! Regidx Rs2 = r).
      { rewrite /G6 /G5 /G4 /G3 /G2 /G1.
        repeat (rewrite upd_ne; [| reg_neq]). exact Hmss2. }
      assert (HG6s3 : G6 !!! Regidx Rs3 = va0).
      { rewrite /G6 /G5 /G4 /G3 /G2 /G1.
        repeat (rewrite upd_ne; [| reg_neq]). exact Hmss3. }
      assert (HG6s4 : G6 !!! Regidx Rs4 = r).
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
      { iExists γk. iFrame "Hlock Havail". }
      (* ---- mappages(pagetable, va0, PGSIZE, mem, PTE_R|W|U) ----
         at the ambient [lvl]: mappages/walk are level-generic, and [Hlvl] is
         exactly the int-range fact their kalloc needs. *)
      iDestruct (cpu_own_transport Ckr Cmg lvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iApply (Mappages.wp_mappages_sconf KT1 γa G6 t m_ad 1%nat 22 lvl (K - 6)%nat
                eb p None b _
                Hlvl ltac:(lia) HG6a0 Hmpva Hmppa Hmpsz ltac:(lia)
                HG6a4 vmf_perm_ok22 Hmpvab Hmppab Hrep Hmpfresh
                with "Hcg Hcnt Htext Hpc Hptree Henv2").
      all: try lkbelow.
      iIntros (Cgr Hsgr mg t' k g) "Hcg Hcnt Hpc Hptree %Hnodes _ %Hgcs %Hbase' %Hrep' %Hmono %Hmiss %Hmpay".
      rewrite HG6a1 in Hrep'. rewrite HG6a3 in Hrep'.
      assert (Hret5a : ret_pc (G6 !!! Regidx Rra) = mword_of_int (KernelSyms.vmfault + 0x5a)).
      { rewrite HG6ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hret5a) in "Hpc".
      assert (Hmgsp : mg !!! Regidx csp_rs1 = spr).
      { rewrite (callee_saved_lookup Hgcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HG6sp. }
      assert (Hmgs2 : mg !!! Regidx Rs2 = r).
      { rewrite (callee_saved_lookup Hgcs Rs2 ltac:(vm_compute; reflexivity)). exact HG6s2. }
      assert (Hmgs4 : mg !!! Regidx Rs4 = r).
      { rewrite (callee_saved_lookup Hgcs Rs4 ltac:(vm_compute; reflexivity)). exact HG6s4. }
      assert (Hmgthr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                mg !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H9 H18 H19 H20.
        rewrite (callee_saved_lookup Hgcs c Hc). apply HG6thr; assumption. }
      assert (Hbase'' : pt_base t' = P.(ud_root)) by (rewrite Hbase'; exact Hbase).
      destruct Hmpay as [(Hk1 & Hga0) | (Hklt & Hga0 & _)].
      { (* ============ mappages SUCCEEDED: return mem ================ *)
        subst k. rewrite vf_run1 in Hrep'.
        iPoseProof (vfi_5c with "Htext") as "Hi5c".
        iPoseProof (vfi_5e with "Htext") as "Hi5e".
        iPoseProof (vfi_60 with "Htext") as "Hi60".
        iPoseProof (vfi_62 with "Htext") as "Hi62".
        (* +0x5a c.bnez a0 FALLS (a0 = 0) *)
        iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.vmfault + 0x5a))
                  (mword_of_int 5 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                  mg (K - 6)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite Hga0; vm_compute; reflexivity)
                  with "Hcg Hpc Hi5a").
        iIntros (C5c Hs5c) "Hcg Hpc".
        assert (Hpp5c : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x5a) : mword 64) 2
                        = mword_of_int (KernelSyms.vmfault + 0x5c))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp5c) in "Hpc".
        (* +0x5c c.ldsp s1,24(sp) *)
        iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.vmfault + 0x5c)) (mword_of_int 3 : mword 6) Rs1
                  mg (K - 6)%nat (mm !!! Regidx Rs1) b (dqm:=DfracOwn 1)
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi5c [Hk3]").
        { iEval (rewrite Hmgsp Hb3). iExact "Hk3". }
        iIntros (C5e Hs5e) "Hcg Hpc Hk3". iEval (rewrite Hmgsp Hb3) in "Hk3".
        set (S1 := <[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> mg).
        assert (HS1sp : S1 !!! Regidx csp_rs1 = spr)
          by (rewrite /S1; rewrite upd_ne; [exact Hmgsp | reg_neq]).
        assert (Hpp5e : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x5c) : mword 64) 2
                        = mword_of_int (KernelSyms.vmfault + 0x5e))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp5e) in "Hpc".
        (* +0x5e c.ldsp s2,16(sp) *)
        iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.vmfault + 0x5e)) (mword_of_int 2 : mword 6) Rs2
                  S1 (K - 6)%nat (mm !!! Regidx Rs2) b (dqm:=DfracOwn 1)
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi5e [Hk4]").
        { iEval (rewrite HS1sp Hb4). iExact "Hk4". }
        iIntros (C60 Hs60) "Hcg Hpc Hk4". iEval (rewrite HS1sp Hb4) in "Hk4".
        set (S2 := <[Regidx Rs2 := regval_into_reg (mm !!! Regidx Rs2)]> S1).
        assert (HS2sp : S2 !!! Regidx csp_rs1 = spr)
          by (rewrite /S2; rewrite upd_ne; [exact HS1sp | reg_neq]).
        assert (Hpp60 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x5e) : mword 64) 2
                        = mword_of_int (KernelSyms.vmfault + 0x60))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp60) in "Hpc".
        (* +0x60 c.ldsp s3,8(sp) *)
        iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.vmfault + 0x60)) (mword_of_int 1 : mword 6) Rs3
                  S2 (K - 6)%nat (mm !!! Regidx Rs3) b (dqm:=DfracOwn 1)
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi60 [Hk5]").
        { iEval (rewrite HS2sp Hb5). iExact "Hk5". }
        iIntros (C62 Hs62) "Hcg Hpc Hk5". iEval (rewrite HS2sp Hb5) in "Hk5".
        set (S3 := <[Regidx Rs3 := regval_into_reg (mm !!! Regidx Rs3)]> S2).
        assert (Hpp62 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x60) : mword 64) 2
                        = mword_of_int (KernelSyms.vmfault + 0x62))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp62) in "Hpc".
        (* +0x62 c.j -0x52 *)
        iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.vmfault + 0x62))
                  (sign_extend' 21 (concat_vec (mword_of_int 2007 : mword 11) ('b"0")))
                  S3 (K - 6)%nat b ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi62").
        iIntros (C10B Hs10B). iApply bi.later_intro. iIntros "Hcg Hpc".
        assert (Hjt62 : add_vec (mword_of_int (KernelSyms.vmfault + 0x62) : mword 64)
                  (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2007 : mword 11) ('b"0"))))
                = mword_of_int (KernelSyms.vmfault + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjt62) in "Hpc".
        (* ---- grow the user map by the new page ---- *)
        iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhwc Hcg]".
        iDestruct "Hhwc" as (hwmisa0 hwmseccfg0 hwpmar0 hwelp0)
          "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & #Hkmapb & _)".
        assert (Hvpnb : (bv_unsigned (svpn_of va0) < 67108864)%Z)
          by exact (svpn_of_lt_maxva va0 Hva0b).
        (* the faulting va's PAGE is inside [p->sz], so every one of its vas
           was already in the process's view -- as a lazy page reading 0 *)
        assert (Hvpnv : (bv_unsigned (svpn_of va0) * 4096
                         = 4096 * (bv_unsigned va / 4096))%Z).
        { rewrite (svpn_of_unsigned_lo va0
                     ltac:(change (2 ^ 38)%Z with 274877906944%Z in Hva0b;
                           exact Hva0b)).
          rewrite Z.shiftr_div_pow2; [| lia]. change (2 ^ 12)%Z with 4096%Z.
          rewrite uint_unsigned. subst va0. rewrite pgd_unsigned.
          pose proof (Z.div_mod (bv_unsigned va) 4096 ltac:(lia)) as Hdm.
          pose proof (Z.mod_pos_bound (bv_unsigned va) 4096 ltac:(lia)) as Hmb.
          replace (bv_unsigned va - bv_unsigned va mod 4096)%Z
            with ((bv_unsigned va / 4096) * 4096)%Z by lia.
          rewrite (Z.div_mul (bv_unsigned va / 4096) 4096 ltac:(lia)). lia. }
        assert (Hlive : forall j : nat, (j < 4096)%nat ->
                  uva_live (uint szv)
                    (bv_unsigned (svpn_of va0) * 4096 + Z.of_nat j)%Z).
        { intros j Hj. rewrite Hvpnv.
          apply (uva_live_page (uint szv) (bv_unsigned va) j);
            [ exact (proj1 (bv_unsigned_in_range _ va))
            | rewrite <- uint_unsigned; exact Hvalt
            | exact Hj ]. }
        iDestruct (proc_ptm_fault P (uint szv) M (svpn_of va0) r t'
                     m_ad (fun _ : nat => bv_0 8)
                     Hwf Hview Hnone Hvpnb Hrep' Hbase'' Hpv Hlive
                     ltac:(intros j Hj; reflexivity)
                     with "Hkmapb Hptree Hzpage Hown") as "Hpt".
        assert (Humnone : P.(ud_um) !! svpn_of va0 = None)
          by (exact (proj2 (proj2 (proj1 (proj1 Hview (svpn_of va0)) Hnone)))).
        iDestruct (cpu_own_transport Cgr C10B lvl eb p b ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        iSpecialize ("Hepi" $! C10B with "[%]"); [wp_next_chain|].
        iApply ("Hepi" $! S3 r with "[%] Hcg Hcnt Hpc [Hk3 Hk4 Hk5] [Hpt]").
        { split_and!.
          - rewrite /S3. rewrite upd_ne; [exact HS2sp | reg_neq].
          - rewrite /S3. rewrite upd_ne; [| reg_neq].
            rewrite /S2. rewrite upd_ne; [| reg_neq].
            rewrite /S1. rewrite upd_ne; [exact Hmgs4 | reg_neq].
          - intros c Hc H2 H8 H20.
            destruct (decide (c = Rs1)) as [->|H9].
            { rewrite /S3. rewrite upd_ne; [| reg_neq].
              rewrite /S2. rewrite upd_ne; [| reg_neq]. rewrite /S1 upd_eq. reflexivity. }
            destruct (decide (c = Rs2)) as [->|H18].
            { rewrite /S3. rewrite upd_ne; [| reg_neq]. rewrite /S2 upd_eq. reflexivity. }
            destruct (decide (c = Rs3)) as [->|H19].
            { rewrite /S3 upd_eq. reflexivity. }
            rewrite /S3. rewrite upd_ne;
              [| intros Hx; injection Hx as Hx2; subst c; apply H19; reflexivity].
            rewrite /S2. rewrite upd_ne;
              [| intros Hx; injection Hx as Hx2; subst c; apply H18; reflexivity].
            rewrite /S1. rewrite upd_ne;
              [| intros Hx; injection Hx as Hx2; subst c; apply H9; reflexivity].
            apply Hmgthr; assumption. }
        { iExists _, _, _. iFrame "Hk3 Hk4 Hk5". }
        { rewrite /PAY. iRight. iExists r.
          iSplitR; [iPureIntro; reflexivity |].
          iSplitR; [iPureIntro; exact Hpv |].
          iSplitR; [iPureIntro; exact Hvalt |].
          iSplitR; [iPureIntro; exact Humnone |].
          iExact "Hpt". } }
      (* ============ mappages FAILED: kfree and return 0 ============= *)
      assert (Hk0 : k = 0%nat) by lia. subst k.
      cbn [pt_insert_run] in Hrep'.
      iPoseProof (vfi_64 with "Htext") as "Hi64".
      iPoseProof (vfi_66 with "Htext") as "Hi66".
      iPoseProof (vfi_6a with "Htext") as "Hi6a".
      iPoseProof (vfi_6c with "Htext") as "Hi6c".
      iPoseProof (vfi_6e with "Htext") as "Hi6e".
      iPoseProof (vfi_70 with "Htext") as "Hi70".
      iPoseProof (vfi_72 with "Htext") as "Hi72".
      (* +0x5a c.bnez a0 TAKEN (a0 = -1) *)
      iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.vmfault + 0x5a))
                (mword_of_int 5 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                mg (K - 6)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite Hga0; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi5a").
      iApply bi.later_intro. iIntros (C64 Hs64) "Hcg Hpc".
      assert (Htgt64 : add_vec (mword_of_int (KernelSyms.vmfault + 0x5a) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 5 : mword 8) ('b"0"))))
              = mword_of_int (KernelSyms.vmfault + 0x64)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt64) in "Hpc".
      (* +0x64 c.mv a0,s2 *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.vmfault + 0x64)) Ra0 Rs2
                mg (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi64").
      iIntros (C66 Hs66) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (F1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mg !!! Regidx Rs2))]> mg).
      assert (Hpp66 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x64) : mword 64) 2
                      = mword_of_int (KernelSyms.vmfault + 0x66))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp66) in "Hpc".
      (* +0x66 jal ra,kfree *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.vmfault + 0x66)) Rra
                (mword_of_int 2094330 : mword 21) F1 (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi66").
      iIntros (Ckf Hskf) "Hcg Hpc".
      set (F2 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.vmfault + 0x66) : mword 64) 4)]> F1).
      assert (Htgtkf : add_vec (mword_of_int (KernelSyms.vmfault + 0x66) : mword 64)
                         (sign_extend' 64 (mword_of_int 2094330 : mword 21))
                       = mword_of_int KernelSyms.kfree)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtkf) in "Hpc".
      assert (HF2a0 : F2 !!! Regidx Ra0 = r).
      { rewrite /F2. rewrite upd_ne; [| reg_neq].
        rewrite /F1 upd_eq. rewrite add_vec_zero_l. exact Hmgs2. }
      assert (HF2ra : F2 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KernelSyms.vmfault + 0x66) : mword 64) 4)
        by (rewrite /F2 upd_eq; reflexivity).
      assert (HF2sp : F2 !!! Regidx csp_rs1 = spr).
      { rewrite /F2. rewrite upd_ne; [| reg_neq].
        rewrite /F1. rewrite upd_ne; [| reg_neq]. exact Hmgsp. }
      assert (HF2thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                F2 !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H9 H18 H19 H20.
        rewrite /F2. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
        rewrite /F1. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
        apply Hmgthr; assumption. }
      iDestruct (cpu_own_transport Cgr Ckf lvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iApply (Kfree.wp_kfree_sconf KT1 γa γk (mword_of_int KernelSyms.kmem)
                (mword_of_int (KernelSyms.kmem + 24)) F2 None lvl eb p (K - 6)%nat b lks
                ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)
                Hlvl Hbelow
                with "Hcg Hcnt Htext Hpc Hlock [Hzpage] Havail").
      all: try lkbelow.
      { rewrite /kfree_pre HF2a0.
        iSplitR; [iPureIntro; exact Hpv |].
        (* kfree wants the page contents-existential; forget the zeros *)
        rewrite /page_own /byte_any.
        iApply (big_sepL_impl with "Hzpage"). iIntros "!>" (k x Hx) "Hj".
        iExists _. iExact "Hj". }
      iIntros (Cfr Hsfr mfk) "Hcg Hcnt Hpc %Hfcs _".
      assert (Hret6a : ret_pc (F2 !!! Regidx Rra) = mword_of_int (KernelSyms.vmfault + 0x6a)).
      { rewrite HF2ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hret6a) in "Hpc".
      assert (Hmfksp : mfk !!! Regidx csp_rs1 = spr).
      { rewrite (callee_saved_lookup Hfcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HF2sp. }
      assert (Hmfkthr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                mfk !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H9 H18 H19 H20.
        rewrite (callee_saved_lookup Hfcs c Hc). apply HF2thr; assumption. }
      (* +0x6a c.li s4,0 *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.vmfault + 0x6a)) Rs4 (mword_of_int 0 : mword 6)
                (mword_of_int 0 : mword 64) mfk (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi6a").
      iIntros (C6c Hs6c) "Hcg Hpc".
      set (F3 := <[Regidx Rs4 := regval_into_reg (mword_of_int 0 : mword 64)]> mfk).
      assert (HF3sp : F3 !!! Regidx csp_rs1 = spr)
        by (rewrite /F3; rewrite upd_ne; [exact Hmfksp | reg_neq]).
      assert (Hpp6c : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x6a) : mword 64) 2
                      = mword_of_int (KernelSyms.vmfault + 0x6c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp6c) in "Hpc".
      (* +0x6c c.ldsp s1,24(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.vmfault + 0x6c)) (mword_of_int 3 : mword 6) Rs1
                F3 (K - 6)%nat (mm !!! Regidx Rs1) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi6c [Hk3]").
      { iEval (rewrite HF3sp Hb3). iExact "Hk3". }
      iIntros (C6e Hs6e) "Hcg Hpc Hk3". iEval (rewrite HF3sp Hb3) in "Hk3".
      set (F4 := <[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> F3).
      assert (HF4sp : F4 !!! Regidx csp_rs1 = spr)
        by (rewrite /F4; rewrite upd_ne; [exact HF3sp | reg_neq]).
      assert (Hpp6e : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x6c) : mword 64) 2
                      = mword_of_int (KernelSyms.vmfault + 0x6e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp6e) in "Hpc".
      (* +0x6e c.ldsp s2,16(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.vmfault + 0x6e)) (mword_of_int 2 : mword 6) Rs2
                F4 (K - 6)%nat (mm !!! Regidx Rs2) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi6e [Hk4]").
      { iEval (rewrite HF4sp Hb4). iExact "Hk4". }
      iIntros (C70 Hs70) "Hcg Hpc Hk4". iEval (rewrite HF4sp Hb4) in "Hk4".
      set (F5 := <[Regidx Rs2 := regval_into_reg (mm !!! Regidx Rs2)]> F4).
      assert (HF5sp : F5 !!! Regidx csp_rs1 = spr)
        by (rewrite /F5; rewrite upd_ne; [exact HF4sp | reg_neq]).
      assert (Hpp70 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x6e) : mword 64) 2
                      = mword_of_int (KernelSyms.vmfault + 0x70))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp70) in "Hpc".
      (* +0x70 c.ldsp s3,8(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.vmfault + 0x70)) (mword_of_int 1 : mword 6) Rs3
                F5 (K - 6)%nat (mm !!! Regidx Rs3) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi70 [Hk5]").
      { iEval (rewrite HF5sp Hb5). iExact "Hk5". }
      iIntros (C72 Hs72) "Hcg Hpc Hk5". iEval (rewrite HF5sp Hb5) in "Hk5".
      set (F6 := <[Regidx Rs3 := regval_into_reg (mm !!! Regidx Rs3)]> F5).
      assert (Hpp72 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x70) : mword 64) 2
                      = mword_of_int (KernelSyms.vmfault + 0x72))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp72) in "Hpc".
      (* +0x72 c.j -0x62 *)
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.vmfault + 0x72))
                (sign_extend' 21 (concat_vec (mword_of_int 1999 : mword 11) ('b"0")))
                F6 (K - 6)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi72").
      iIntros (C10C Hs10C). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Hjt72 : add_vec (mword_of_int (KernelSyms.vmfault + 0x72) : mword 64)
                (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 1999 : mword 11) ('b"0"))))
              = mword_of_int (KernelSyms.vmfault + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjt72) in "Hpc".
      iDestruct (proc_ptm_rebuild P (uint szv) M t' m_ad Hwf Hview Hrep' Hbase'' with "Hptree Hown") as "Hpt".
      iDestruct (cpu_own_transport Cfr C10C lvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("Hepi" $! C10C with "[%]"); [wp_next_chain|].
      iApply ("Hepi" $! F6 (mword_of_int 0) with "[%] Hcg Hcnt Hpc [Hk3 Hk4 Hk5] [Hpt]").
      { split_and!.
        - rewrite /F6. rewrite upd_ne; [exact HF5sp | reg_neq].
        - rewrite /F6. rewrite upd_ne; [| reg_neq].
          rewrite /F5. rewrite upd_ne; [| reg_neq].
          rewrite /F4. rewrite upd_ne; [| reg_neq].
          rewrite /F3 upd_eq. reflexivity.
        - intros c Hc H2 H8 H20.
          destruct (decide (c = Rs1)) as [->|H9].
          { rewrite /F6. rewrite upd_ne; [| reg_neq].
            rewrite /F5. rewrite upd_ne; [| reg_neq]. rewrite /F4 upd_eq. reflexivity. }
          destruct (decide (c = Rs2)) as [->|H18].
          { rewrite /F6. rewrite upd_ne; [| reg_neq]. rewrite /F5 upd_eq. reflexivity. }
          destruct (decide (c = Rs3)) as [->|H19].
          { rewrite /F6 upd_eq. reflexivity. }
          rewrite /F6. rewrite upd_ne;
            [| intros Hx; injection Hx as Hx2; subst c; apply H19; reflexivity].
          rewrite /F5. rewrite upd_ne;
            [| intros Hx; injection Hx as Hx2; subst c; apply H18; reflexivity].
          rewrite /F4. rewrite upd_ne;
            [| intros Hx; injection Hx as Hx2; subst c; apply H9; reflexivity].
          rewrite /F3. rewrite upd_ne;
            [| intros Hx; injection Hx as Hx2; subst c; apply H20; reflexivity].
          apply Hmfkthr; assumption. }
      { iExists _, _, _. iFrame "Hk3 Hk4 Hk5". }
      { rewrite /PAY. iLeft. iSplitR; [iPureIntro; reflexivity | iExact "Hpt"]. } }

    (* ================= ALREADY MAPPED: return 0 ==================== *)
    iPoseProof (vfi_32 with "Htext") as "Hi32".
    iPoseProof (vfi_34 with "Htext") as "Hi34".
    iPoseProof (vfi_36 with "Htext") as "Hi36".
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.vmfault + 0x30))
              (mword_of_int 4 : mword 8) (Cregidx (mword_of_int 2)) Ra0
              N1 (K - 6)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite HN1a0 Ha0one; vm_compute; reflexivity)
              with "Hcg Hpc Hi30").
    iIntros (C32 Hs32) "Hcg Hpc".
    assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x30) : mword 64) 2
                    = mword_of_int (KernelSyms.vmfault + 0x32))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    (* +0x32 c.ldsp s1,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.vmfault + 0x32)) (mword_of_int 3 : mword 6) Rs1
              N1 (K - 6)%nat (mm !!! Regidx Rs1) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi32 [Hk3]").
    { iEval (rewrite HN1sp Hb3). iExact "Hk3". }
    iIntros (C34 Hs34) "Hcg Hpc Hk3". iEval (rewrite HN1sp Hb3) in "Hk3".
    set (D1 := <[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> N1).
    assert (HD1sp : D1 !!! Regidx csp_rs1 = spr)
      by (rewrite /D1; rewrite upd_ne; [exact HN1sp | reg_neq]).
    assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x32) : mword 64) 2
                    = mword_of_int (KernelSyms.vmfault + 0x34))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp34) in "Hpc".
    (* +0x34 c.ldsp s3,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.vmfault + 0x34)) (mword_of_int 1 : mword 6) Rs3
              D1 (K - 6)%nat (mm !!! Regidx Rs3) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi34 [Hk5]").
    { iEval (rewrite HD1sp Hb5). iExact "Hk5". }
    iIntros (C36 Hs36) "Hcg Hpc Hk5". iEval (rewrite HD1sp Hb5) in "Hk5".
    set (D2 := <[Regidx Rs3 := regval_into_reg (mm !!! Regidx Rs3)]> D1).
    assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.vmfault + 0x34) : mword 64) 2
                    = mword_of_int (KernelSyms.vmfault + 0x36))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp36) in "Hpc".
    (* +0x36 c.j -0x26 *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.vmfault + 0x36))
              (sign_extend' 21 (concat_vec (mword_of_int 2029 : mword 11) ('b"0")))
              D2 (K - 6)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi36").
    iIntros (C10D Hs10D). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Hjt36 : add_vec (mword_of_int (KernelSyms.vmfault + 0x36) : mword 64)
              (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2029 : mword 11) ('b"0"))))
            = mword_of_int (KernelSyms.vmfault + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjt36) in "Hpc".
    iDestruct (proc_ptm_rebuild P (uint szv) M t m_ad Hwf Hview Hrep Hbase with "Hptree Hown") as "Hpt".
    iDestruct (cpu_own_transport CID C10D lvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iSpecialize ("Hepi" $! C10D with "[%]"); [wp_next_chain|].
    iApply ("Hepi" $! D2 (mword_of_int 0) with "[%] Hcg Hcnt Hpc [Hk3 Hk4 Hk5] [Hpt]").
    { split_and!.
      - rewrite /D2. rewrite upd_ne; [exact HD1sp | reg_neq].
      - rewrite /D2. rewrite upd_ne; [| reg_neq].
        rewrite /D1. rewrite upd_ne; [exact HN1s4 | reg_neq].
      - intros c Hc H2 H8 H20.
        destruct (decide (c = Rs1)) as [->|H9].
        { rewrite /D2. rewrite upd_ne; [| reg_neq]. rewrite /D1 upd_eq. reflexivity. }
        destruct (decide (c = Rs3)) as [->|H19].
        { rewrite /D2 upd_eq. reflexivity. }
        rewrite /D2. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; apply H19; reflexivity].
        rewrite /D1. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; apply H9; reflexivity].
        apply HN1thr; assumption. }
    { iExists _, _, _. iFrame "Hk3 Hk4 Hk5". }
    { rewrite /PAY. iLeft. iSplitR; [iPureIntro; reflexivity | iExact "Hpt"]. }
  Qed.

  (* THE [proc_pt]-ALTITUDE COROLLARY.  vmfault's other callers -- usertrap,
     copyinstr -- say nothing about the process's memory, so they keep the
     contract that does not name it.  Opening and re-sealing is the whole
     of the derivation: [ProcPtOwn.proc_pt_ptm] IS the equivalence. *)
  Lemma wp_vmfault_sconf
      (γa : gname) (mm : regfile)
      (P : uptd) (szv : mword 64) (K lvl : nat) (eb : bool) (p : mword 64)
      (b : bool) (lks : gset string)
    : wp_vmfault_sconf_body γa mm P szv K lvl eb p b lks.
  Proof.
    cbv beta delta [wp_vmfault_sconf_body].
    intros pcE va va0 ret_tgt HK Htp Hroot Hsza1 Hszb Hlvl Hbelow.
    iIntros "Hcg Hcnt #Htext Hpc Hpt Henv Hcont".
    iEval (rewrite (proc_pt_ptm P (uint szv))) in "Hpt".
    iDestruct "Hpt" as (M) "Hpt".
    iApply (wp_vmfault_sconf_mem γa mm P M szv K lvl eb p b lks
              HK Htp Hroot Hsza1 Hszb Hlvl Hbelow
              with "Hcg Hcnt Htext Hpc Hpt Henv").
    rewrite /wp_next.
    iIntros (CIDr) "%Hch".
    iSpecialize ("Hcont" $! CIDr with "[%]"); [exact Hch |].
    iIntros (mr) "Hcg2 Hcnt2 Hpc2 %Hcs Hpost".
    iApply ("Hcont" $! mr with "Hcg2 Hcnt2 Hpc2 [%] [Hpost]"); [exact Hcs |].
    iDestruct "Hpost" as "[(%Hz & Hp) | Hs]".
    - iLeft. iSplitR; [iPureIntro; exact Hz |].
      iApply (proc_ptm_pt with "Hp").
    - iDestruct "Hs" as (r) "(%Hr & %Hv & %Hlt & %Hn & Hp)".
      iRight. iExists r.
      iSplitR; [iPureIntro; exact Hr |].
      iSplitR; [iPureIntro; exact Hv |].
      iSplitR; [iPureIntro; exact Hlt |].
      iSplitR; [iPureIntro; exact Hn |].
      iApply (proc_ptm_pt with "Hp").
  Qed.

End ProofVmfault.

End VmfaultProof.
