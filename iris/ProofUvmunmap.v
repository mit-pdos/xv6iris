(* ProofUvmunmap.v -- uvmunmap() over the SIE-agnostic sconf world.

     void uvmunmap(pagetable_t pagetable, uint64 va, uint64 npages, int do_free)
     {
       if ((va % PGSIZE) != 0) panic("uvmunmap: not aligned");
       for (a = va; a < va + npages * PGSIZE; a += PGSIZE) {
         if ((pte = walk(pagetable, a, 0)) == 0) continue;
         if (( *pte & PTE_V) == 0) continue;
         if (do_free) { uint64 pa = PTE2PA( *pte); kfree((void * )pa); }
         *pte = 0;
       }
     }

   Spec of record: SpecUvmunmap.v -- TWO of them.  The function is proved
   ONCE, over BarePt.v's fixed-leaf axis [fx : gmap (mword 27) (mword 64)]
   ([UvmunmapCore.wp_uvmunmap_gen], at [BarePt.uptg fx uroot um]), and
   sealed twice: [UVMUNMAP] at [Some P.(ud_tfp)] (= [ProcPtOwn.proc_pt],
   every existing caller, statement unchanged) and [UVMUNMAP_BARE] at
   [None] (= [BarePt.bare_pt], what uvmfree runs on, after
   proc_freepagetable's two [do_free = 0] unmaps have dropped the
   trampoline and trapframe leaves).  This costs nothing because the loop
   touches the fixed leaves in exactly ONE way -- it must know the vpn it
   clears is not one of them -- and gets that from its own range premise
   ([BarePt.uptg_fixed_user_none] discharges it at both ends).

   The loop keeps the tree OPEN across iterations (walk consumes
   [ptree_own]), so the invariant carries [ptree_own 2 (DfracOwn 1) t] plus
   the exact map view [pt_rep0 t m_i] and its [BarePt.uptg_view] relation to
   [um_del_run ... done]; the map moves by ONE deletion per iteration
   ([um_del_run _ _ (S k)] is [delete _ (um_del_run _ _ k)] by conversion).

   THREE STRUCTURAL POINTS.

   1. NO FUEL.  The measure drops by exactly one page per iteration, so plain
      [induction rem] works (unlike the copy loops).

   2. THE SHRINK-WRAPPED FRAME.  The 64-byte frame has eight slots
      (1=ra 2=s0 3=s1 4=s2 5=s3 6=s4 7=s5 8=s6, at [pa_stk sp0 k]), but s1 is
      pushed at +0x2a only when the loop runs; the [npages == 0] branch at
      +0x26 jumps to +0x78, PAST the [ld s1] at +0x76.  So the epilogue
      lemma [uu_epilogue] covers +0x78..+0x88 and takes slot 3 as an
      [∃ w, pa_stk sp0 3 ↦₈[KT1] w] argument (the vmfault join recipe).

   3. THE +0x4a JOIN.  Three arms reach the loop tail -- walk found no leaf,
      the leaf word is invalid, and the freed-and-cleared arm -- and all three
      leave the map at [um_del_run um vpn0 (S done)].  One
      [iAssert]ed [TAIL] continuation carries the whole tail (+0x4a bump,
      +0x4c exit test, and either the induction hypothesis or the close).

   The panic block +0x2e..+0x45 is DEAD: [va] page-aligned is a precondition,
   so [slli a5,a1,0x34] is zero and the [bnez] at +0x0c falls through. *)
Set Printing Depth 40.
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
Require Import InstrBytes KernelText.
Require Import WpMmodeLeafBase.
Require Import RegFile.
Require Import CalleeSaved StackOwn.
Require Import IntrDefs WpSmodeIntr.
Require Import HartTp WpNext.
Require Import WpLock.
Require Import KallocInv.
Require Import ByteCursor.
Require Import CommonWalk PtTree.
Require Import KptTree.
Require Import PtBuild.
Require Import TrampPt.
Require Import UserPtTree.
Require Import CpuOwn.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import BarePt.
Require Import CodeUvmunmap.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import SpecWalk SpecKfree.
Require Import SpecUvmunmap.
Require Import KernelRvcDecode.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

(* uvmunmap's arithmetic is all SHARED and lives at its own altitude: the
   run-cursor / PGROUNDUP [Z] facts ([z_run_iter], [z_run_end64],
   [z_run_strict], [z_lt_tramp_vpn_ne]) and the two shift bridges
   ([shl52_aligned] -- the page-alignment test -- [shl12_moi] and
   [shl12_pages_add]) are in ProcPtOwn.v; the two readings of the unsigned
   compare a [bgeu] decides are [ByteCursor.bc_geu] / [bc_ltu].  Only the
   two callee-saved transport predicates below are function-specific. *)

(* the callee-saved registers the function never touches, in its two
   flavours: inside the loop s1 is live (it holds the PTE pointer), at the
   epilogue join it has already been reloaded. *)
Definition uu_thr (mm m : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 ->
    c <> (mword_of_int 8 : mword 5) -> c <> (mword_of_int 9 : mword 5) ->
    c <> (mword_of_int 18 : mword 5) -> c <> (mword_of_int 19 : mword 5) ->
    c <> (mword_of_int 20 : mword 5) -> c <> (mword_of_int 21 : mword 5) ->
    c <> (mword_of_int 22 : mword 5) ->
    m !!! Regidx c = mm !!! Regidx c.

(* s5 holds [do_free], and the [beq s5,zero] at +0x66 is the ONE place the
   loop body branches on it: taken skips the PTE2PA/kfree block and lands
   straight on the [sd zero,0(s1)] at +0x46, which is where the freeing arm
   rejoins anyway.  So the whole [df] split is this predicate plus a
   two-way [destruct] at that branch. *)
Definition uu_s5 (df : bool) (m : regfile) : Prop :=
  if df then m !!! Regidx (mword_of_int 21 : mword 5) <> (mword_of_int 0 : mword 64)
        else m !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 0 : mword 64).

Definition uu_thr1 (mm m : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 ->
    c <> (mword_of_int 8 : mword 5) ->
    c <> (mword_of_int 18 : mword 5) -> c <> (mword_of_int 19 : mword 5) ->
    c <> (mword_of_int 20 : mword 5) -> c <> (mword_of_int 21 : mword 5) ->
    c <> (mword_of_int 22 : mword 5) ->
    m !!! Regidx c = mm !!! Regidx c.



(* ===================================================================== *)
(* THE WHOLE FUNCTION, PROVED ONCE OVER [BarePt.uptg].                    *)
(* ===================================================================== *)

Module UvmunmapCore (WalkNoalloc : WALK_NOALLOC) (Kfree : KFREE).

Section ProofUvmunmap.
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
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).

  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  Ltac slot_addr :=
    unfold pa_stk, add_vec_int; rewrite pa_stk_off2;
    apply f_equal; apply bv_eq; vm_compute; reflexivity.

  (* peel a register lookup through the insert tower via the [upd_eq]/[upd_ne]
     LEMMAS, one layer at a time (optimization.md's [peel_reg]). *)
  Ltac lkp :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | match goal with |- context [ ?M !!! _ ] => is_var M; progress unfold M end ];
    repeat rewrite add_vec_zero_l;
    first [ reflexivity | assumption ].

  (* the same peel, WITHOUT the closing step -- for the lookups whose value
     still needs a rewrite. *)
  Ltac lkp0 :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | match goal with |- context [ ?M !!! _ ] => is_var M; progress unfold M end ];
    repeat rewrite add_vec_zero_l.

  (* discharge a [uu_thr]/[uu_thr1] transport across a block of writes: peel,
     refuting each [upd_ne] side goal either because the written register is
     not callee-saved ([Hc]) or because it is one of the excluded ones. *)
  (* the [upd_ne] side goal [Regidx c <> Regidx k]: either [k] is not
     callee-saved at all (so [is_cs_idx c = true] refutes it) or it is one of
     the excluded ones, and the corresponding [c <> k] hypothesis is in
     context. *)
  Ltac thr_side :=
    first
      [ apply not_eq_sym; apply is_cs_idx_true_neq;
        [ vm_compute; reflexivity | assumption ]
      | congruence ].

  Ltac thr_peel :=
    repeat first
      [ rewrite upd_ne; [| thr_side]
      | match goal with |- context [ ?M !!! _ ] => is_var M; progress unfold M end ].

  (* ================================================================== *)
  (*  THE EPILOGUE (+0x78 .. +0x88).  Reached by the [npages == 0]        *)
  (*  branch directly and by the loop exit through the [ld s1] at +0x76,  *)
  (*  so slot 3 arrives at existential contents.                          *)
  (* ================================================================== *)
  Local Lemma uu_epilogue `{CID0 : CpuId}
      (mm mj : regfile) (K : nat) (sp0 : mword 64) (b : bool) (p : mword 64) :
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
    (8 <= K)%nat ->
    mm !!! Regidx csp_rs1 = sp0 ->
    mj !!! Regidx csp_rs1 = spr ->
    uu_thr1 mm mj ->
    sie_cap_gpr KT1 mj (K - 8) b p -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.uvmunmap + 0x78) : mword 64) -∗
    pa_stk sp0 1 ↦₈[KT1] (mm !!! Regidx Rra) -∗
    pa_stk sp0 2 ↦₈[KT1] (mm !!! Regidx Rs0) -∗
    (∃ w : mword 64, pa_stk sp0 3 ↦₈[KT1] w) -∗
    pa_stk sp0 4 ↦₈[KT1] (mm !!! Regidx Rs2) -∗
    pa_stk sp0 5 ↦₈[KT1] (mm !!! Regidx Rs3) -∗
    pa_stk sp0 6 ↦₈[KT1] (mm !!! Regidx Rs4) -∗
    pa_stk sp0 7 ↦₈[KT1] (mm !!! Regidx Rs5) -∗
    pa_stk sp0 8 ↦₈[KT1] (mm !!! Regidx Rs6) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
      sie_cap_gpr KT1 mf K b p -∗
      pc_is (ret_pc (mm !!! Regidx Rra)) -∗
      ⌜callee_saved mm mf⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros spr HK Hmmsp Hjsp Hjthr.
    iIntros "Hcg #Htext Hpc Hk1 Hk2 Hk3 Hk4 Hk5 Hk6 Hk7 Hk8 Hcont".
    iDestruct "Hk3" as (u3) "Hk3".
    iPoseProof (uui_78 with "Htext") as "Hi78".
    iPoseProof (uui_7a with "Htext") as "Hi7a".
    iPoseProof (uui_7c with "Htext") as "Hi7c".
    iPoseProof (uui_7e with "Htext") as "Hi7e".
    iPoseProof (uui_80 with "Htext") as "Hi80".
    iPoseProof (uui_82 with "Htext") as "Hi82".
    iPoseProof (uui_84 with "Htext") as "Hi84".
    iPoseProof (uui_86 with "Htext") as "Hi86".
    iPoseProof (uui_88 with "Htext") as "Hi88".
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (unfold spr; slot_addr).
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (unfold spr; slot_addr).
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (unfold spr; slot_addr).
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (unfold spr; slot_addr).
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk sp0 6) by (unfold spr; slot_addr).
    assert (Hb7 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk sp0 7) by (unfold spr; slot_addr).
    assert (Hb8 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk sp0 8) by (unfold spr; slot_addr).
    assert (Hsprstk : pa_stk sp0 8 = spr).
    { unfold spr, pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    (* --- +0x78 c.ldsp s2,32(sp) --- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x78)) (mword_of_int 4 : mword 6) Rs2
              mj (K - 8) (mm !!! Regidx Rs2) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi78 [Hk4]").
    { iEval (rewrite Hjsp Hb4). iExact "Hk4". }
    iIntros (CID1 Hs1) "Hcg Hpc Hk4". iEval (rewrite Hjsp Hb4) in "Hk4".
    set (E1 := <[Regidx Rs2 := regval_into_reg (mm !!! Regidx Rs2)]> mj).
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spr) by lkp.
    assert (Hp7a : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x78) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x7a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp7a) in "Hpc".
    (* --- +0x7a c.ldsp s3,24(sp) --- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x7a)) (mword_of_int 3 : mword 6) Rs3
              E1 (K - 8) (mm !!! Regidx Rs3) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi7a [Hk5]").
    { iEval (rewrite HE1sp Hb5). iExact "Hk5". }
    iIntros (CID2 Hs2) "Hcg Hpc Hk5". iEval (rewrite HE1sp Hb5) in "Hk5".
    set (E2 := <[Regidx Rs3 := regval_into_reg (mm !!! Regidx Rs3)]> E1).
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spr) by lkp.
    assert (Hp7c : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x7a) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x7c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp7c) in "Hpc".
    (* --- +0x7c c.ldsp s4,16(sp) --- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x7c)) (mword_of_int 2 : mword 6) Rs4
              E2 (K - 8) (mm !!! Regidx Rs4) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi7c [Hk6]").
    { iEval (rewrite HE2sp Hb6). iExact "Hk6". }
    iIntros (CID3 Hs3) "Hcg Hpc Hk6". iEval (rewrite HE2sp Hb6) in "Hk6".
    set (E3 := <[Regidx Rs4 := regval_into_reg (mm !!! Regidx Rs4)]> E2).
    assert (HE3sp : E3 !!! Regidx csp_rs1 = spr) by lkp.
    assert (Hp7e : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x7c) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x7e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp7e) in "Hpc".
    (* --- +0x7e c.ldsp s5,8(sp) --- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x7e)) (mword_of_int 1 : mword 6) Rs5
              E3 (K - 8) (mm !!! Regidx Rs5) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi7e [Hk7]").
    { iEval (rewrite HE3sp Hb7). iExact "Hk7". }
    iIntros (CID4 Hs4) "Hcg Hpc Hk7". iEval (rewrite HE3sp Hb7) in "Hk7".
    set (E4 := <[Regidx Rs5 := regval_into_reg (mm !!! Regidx Rs5)]> E3).
    assert (HE4sp : E4 !!! Regidx csp_rs1 = spr) by lkp.
    assert (Hp80 : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x7e) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x80)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp80) in "Hpc".
    (* --- +0x80 c.ldsp s6,0(sp) --- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x80)) (mword_of_int 0 : mword 6) Rs6
              E4 (K - 8) (mm !!! Regidx Rs6) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi80 [Hk8]").
    { iEval (rewrite HE4sp Hb8). iExact "Hk8". }
    iIntros (CID5 Hs5) "Hcg Hpc Hk8". iEval (rewrite HE4sp Hb8) in "Hk8".
    set (E5 := <[Regidx Rs6 := regval_into_reg (mm !!! Regidx Rs6)]> E4).
    assert (HE5sp : E5 !!! Regidx csp_rs1 = spr) by lkp.
    assert (Hp82 : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x80) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x82)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp82) in "Hpc".
    (* --- +0x82 c.ldsp ra,56(sp) --- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x82)) (mword_of_int 7 : mword 6) Rra
              E5 (K - 8) (mm !!! Regidx Rra) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi82 [Hk1]").
    { iEval (rewrite HE5sp Hb1). iExact "Hk1". }
    iIntros (CID6 Hs6) "Hcg Hpc Hk1". iEval (rewrite HE5sp Hb1) in "Hk1".
    set (E6 := <[Regidx Rra := regval_into_reg (mm !!! Regidx Rra)]> E5).
    assert (HE6sp : E6 !!! Regidx csp_rs1 = spr) by lkp.
    assert (Hp84 : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x82) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x84)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp84) in "Hpc".
    (* --- +0x84 c.ldsp s0,48(sp) --- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x84)) (mword_of_int 6 : mword 6) Rs0
              E6 (K - 8) (mm !!! Regidx Rs0) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi84 [Hk2]").
    { iEval (rewrite HE6sp Hb2). iExact "Hk2". }
    iIntros (CID7 Hs7) "Hcg Hpc Hk2". iEval (rewrite HE6sp Hb2) in "Hk2".
    set (E7 := <[Regidx Rs0 := regval_into_reg (mm !!! Regidx Rs0)]> E6).
    assert (HE7sp : E7 !!! Regidx csp_rs1 = spr) by lkp.
    assert (Hp86 : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x84) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x86)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp86) in "Hpc".
    (* --- +0x86 c.addi16sp sp,64 : trade the frame back --- *)
    set (E8 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (E7 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> E7).
    assert (Hwv : add_vec (E7 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))) = sp0).
    { rewrite HE7sp. unfold spr. apply frame_cancel_64. }
    assert (Hpop : E7 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E7 !!! Regidx csp_rs1)
                               (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)))) 8).
    { rewrite Hwv HE7sp. symmetry. exact Hsprstk. }
    iAssert (stack_own (KTR := KT1) sp0 8) with "[Hk1 Hk2 Hk3 Hk4 Hk5 Hk6 Hk7 Hk8]" as "Hframe".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hk1"; [iExists _; iExact "Hk1" |].
      iSplitL "Hk2"; [iExists _; iExact "Hk2" |].
      iSplitL "Hk3"; [iExists _; iExact "Hk3" |].
      iSplitL "Hk4"; [iExists _; iExact "Hk4" |].
      iSplitL "Hk5"; [iExists _; iExact "Hk5" |].
      iSplitL "Hk6"; [iExists _; iExact "Hk6" |].
      iSplitL "Hk7"; [iExists _; iExact "Hk7" |].
      iSplitL "Hk8"; [iExists _; iExact "Hk8" |].
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x86))
              (mword_of_int 4 : mword 6) E7 (K - 8) 8 b Hpop
              with "Hcg Hpc Hi86 Hframe").
    iIntros (CID8 Hs8) "Hcg Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
      (add_vec (E7 !!! Regidx csp_rs1)
         (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> E7) with E8.
    assert (Hnk : ((K - 8) + 8)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hp88 : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x86) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x88)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp88) in "Hpc".
    (* --- +0x88 c.ret --- *)
    assert (HE8ra : E8 !!! Regidx Rra = mm !!! Regidx Rra) by lkp.
    assert (HE8thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 ->
              c <> Rs2 -> c <> Rs3 -> c <> Rs4 -> c <> Rs5 -> c <> Rs6 ->
              E8 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H18 H19 H20 H21 H22. thr_peel. apply Hjthr; assumption. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x88)) Rra E8 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi88").
    iIntros (CID9 Hs9) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    iEval (rewrite HE8ra) in "Hpc".
    iSpecialize ("Hcont" $! CID9 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E8 with "Hcg Hpc [%]").
    unfold callee_saved. split_and!.
    - (* sp *) rewrite /E8 upd_eq. rewrite Hwv. symmetry. exact Hmmsp.
    - (* s0 *) rewrite /E8. rewrite upd_ne; [| reg_neq]. rewrite /E7 upd_eq. reflexivity.
    - (* s1 *) apply HE8thr; [vm_compute; reflexivity | vm_compute; discriminate ..].
    - (* s2 *) rewrite /E8. rewrite upd_ne; [| reg_neq]. rewrite /E7. rewrite upd_ne; [| reg_neq].
      rewrite /E6. rewrite upd_ne; [| reg_neq]. rewrite /E5. rewrite upd_ne; [| reg_neq].
      rewrite /E4. rewrite upd_ne; [| reg_neq]. rewrite /E3. rewrite upd_ne; [| reg_neq].
      rewrite /E2. rewrite upd_ne; [| reg_neq]. rewrite /E1 upd_eq. reflexivity.
    - (* s3 *) rewrite /E8. rewrite upd_ne; [| reg_neq]. rewrite /E7. rewrite upd_ne; [| reg_neq].
      rewrite /E6. rewrite upd_ne; [| reg_neq]. rewrite /E5. rewrite upd_ne; [| reg_neq].
      rewrite /E4. rewrite upd_ne; [| reg_neq]. rewrite /E3. rewrite upd_ne; [| reg_neq].
      rewrite /E2 upd_eq. reflexivity.
    - (* s4 *) rewrite /E8. rewrite upd_ne; [| reg_neq]. rewrite /E7. rewrite upd_ne; [| reg_neq].
      rewrite /E6. rewrite upd_ne; [| reg_neq]. rewrite /E5. rewrite upd_ne; [| reg_neq].
      rewrite /E4. rewrite upd_ne; [| reg_neq]. rewrite /E3 upd_eq. reflexivity.
    - (* s5 *) rewrite /E8. rewrite upd_ne; [| reg_neq]. rewrite /E7. rewrite upd_ne; [| reg_neq].
      rewrite /E6. rewrite upd_ne; [| reg_neq]. rewrite /E5. rewrite upd_ne; [| reg_neq].
      rewrite /E4 upd_eq. reflexivity.
    - (* s6 *) rewrite /E8. rewrite upd_ne; [| reg_neq]. rewrite /E7. rewrite upd_ne; [| reg_neq].
      rewrite /E6. rewrite upd_ne; [| reg_neq]. rewrite /E5 upd_eq. reflexivity.
    - (* s7 *) apply HE8thr; [vm_compute; reflexivity | vm_compute; discriminate ..].
    - (* s8 *) apply HE8thr; [vm_compute; reflexivity | vm_compute; discriminate ..].
    - (* s9 *) apply HE8thr; [vm_compute; reflexivity | vm_compute; discriminate ..].
    - (* s10 *) apply HE8thr; [vm_compute; reflexivity | vm_compute; discriminate ..].
    - (* s11 *) apply HE8thr; [vm_compute; reflexivity | vm_compute; discriminate ..].
  Qed.

  (* RULE ONE (claude-notes/optimization.md): [uu_loop]'s two block
     continuations, named so the walk's proofmode steps stop re-embedding
     ~15-20 lines of ∀/wands per step.  Transparent on purpose; the
     [wp_next]/[fun CID => ] shape stays visible at each [iAssert], only
     what follows the lambda is folded. *)
  Definition uu_tail_body
      (b : bool) (p spr va : mword 64) (uroot : mword 44)
      (done npages : nat) (df : bool) (fx um : gmap (mword 27) (mword 64))
      (K ilvl : nat) (eb : bool) (mm : regfile)
      (CIDt : CpuId) (lks : gset string) : iProp Σ :=
    (∀ (mt : regfile) (t' : ptree) (m' : gmap (mword 27) (mword 64)),
     ⌜ mt !!! Regidx csp_rs1 = spr
       /\ mt !!! Regidx Rs2 = add_vec va (mword_of_int (4096 * Z.of_nat done))
       /\ mt !!! Regidx Rs3 = add_vec va (mword_of_int (4096 * Z.of_nat npages))
       /\ mt !!! Regidx Rs4 = page_base uroot
       /\ uu_s5 df mt
       /\ mt !!! Regidx Rs6 = (mword_of_int 4096 : mword 64)
       /\ uu_thr mm mt
       /\ pt_rep0 t' m'
       /\ uptg_view (uu_fx df fx (svpn_of va) (S done))
                    (uu_um df um (svpn_of va) (S done)) m'
       /\ pt_base t' = uroot ⌝ -∗
     sie_cap_gpr KT1 mt (K - 8) b p -∗
     cpu_own ilvl eb p b lks -∗
     pc_is (mword_of_int (KernelSyms.uvmunmap + 0x4a) : mword 64) -∗
     ptree_own 2 (DfracOwn 1) t' -∗
     upt_pages_own (uu_um df um (svpn_of va) (S done)) -∗
     WP (Loop : expr riscv_lang))%I.

  Definition uu_store_body
      (b : bool) (p spr va : mword 64) (uroot : mword 44)
      (done npages : nat) (df : bool) (um : gmap (mword 27) (mword 64))
      (K ilvl : nat) (eb : bool) (mm mw : regfile) (t : ptree)
      (CIDs : CpuId) (lks : gset string) : iProp Σ :=
    (∀ ms : regfile,
     ⌜ ms !!! Regidx csp_rs1 = spr
       /\ ms !!! Regidx Rs1 = mw !!! Regidx Ra0
       /\ ms !!! Regidx Rs2 = add_vec va (mword_of_int (4096 * Z.of_nat done))
       /\ ms !!! Regidx Rs3 = add_vec va (mword_of_int (4096 * Z.of_nat npages))
       /\ ms !!! Regidx Rs4 = page_base uroot
       /\ uu_s5 df ms
       /\ ms !!! Regidx Rs6 = (mword_of_int 4096 : mword 64)
       /\ uu_thr mm ms ⌝ -∗
     sie_cap_gpr KT1 ms (K - 8) b p -∗
     cpu_own ilvl eb p b lks -∗
     pc_is (mword_of_int (KernelSyms.uvmunmap + 0x46) : mword 64) -∗
     ptree_own 2 (DfracOwn 1) t -∗
     upt_pages_own (uu_um df um (svpn_of va) (S done)) -∗
     WP (Loop : expr riscv_lang))%I.

  (* ================================================================== *)
  (*  THE LOOP (+0x50 head, +0x4a tail), by induction on the remaining    *)
  (*  page count.                                                         *)
  (* ================================================================== *)
  Local Lemma uu_loop `{CID0 : CpuId} (γa : gname)
      (mm : regfile) (fx : gmap (mword 27) (mword 64)) (uroot : mword 44)
      (um : gmap (mword 27) (mword 64)) (npages K : nat) (eb b df : bool)
      (p : mword 64) (va spr : mword 64) (ilvl : nat) (lks : gset string) :
    (22 <= K)%nat ->
    (Z.of_nat ilvl + 1 < 2 ^ 31)%Z ->
    (* the WIDE bound: the cursor stays inside the Sv39 user space and does
       not wrap.  A fixed-leaf run ends AT the top of it. *)
    (bv_unsigned va + Z.of_nat npages * 4096 <= 274877906944)%Z ->
    uptg_wf um ->
    fx_wf fx ->
    (* which side of the leaf map every vpn of the run lives on.  This
       REPLACES the old proof's derivation of [vpn < tf_vpn] from the range
       premise: at [df = true] the caller derives it exactly that way, at
       [df = false] it names the fixed leaf. *)
    (forall k : nat, (k < npages)%nat -> uu_vpn_ok df (vpn_at (svpn_of va) k)) ->
    forall (rem done : nat) (m : regfile) (t : ptree)
           (m_ad : gmap (mword 27) (mword 64)),
    (1 <= rem)%nat -> (done + rem = npages)%nat ->
    pt_rep0 t m_ad ->
    uptg_view (uu_fx df fx (svpn_of va) done)
              (uu_um df um (svpn_of va) done) m_ad ->
    pt_base t = uroot ->
    m !!! Regidx csp_rs1 = spr ->
    m !!! Regidx Rs2 = add_vec va (mword_of_int (4096 * Z.of_nat done)) ->
    m !!! Regidx Rs3 = add_vec va (mword_of_int (4096 * Z.of_nat npages)) ->
    m !!! Regidx Rs4 = page_base uroot ->
    uu_s5 df m ->
    m !!! Regidx Rs6 = (mword_of_int 4096 : mword 64) ->
    uu_thr mm m ->
    (* the loop's kfree only runs when [do_free != 0] ([destruct df] below);
       at [df = false] the run never touches a lock at all. *)
    (if df then locks_below lks "kmem" else True) ->
    sie_cap_gpr KT1 m (K - 8) b p -∗
    cpu_own ilvl eb p b lks -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.uvmunmap + 0x50) : mword 64) -∗
    ptree_own 2 (DfracOwn 1) t -∗
    upt_pages_own (uu_um df um (svpn_of va) done) -∗
    kalloc_env γa None -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mj : regfile,
      ⌜mj !!! Regidx csp_rs1 = spr⌝ -∗
      ⌜uu_thr mm mj⌝ -∗
      sie_cap_gpr KT1 mj (K - 8) b p -∗
      cpu_own ilvl eb p b lks -∗
      pc_is (mword_of_int (KernelSyms.uvmunmap + 0x76) : mword 64) -∗
      uptg (uu_fx df fx (svpn_of va) npages)
           uroot (uu_um df um (svpn_of va) npages) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hilvl Hrange Hwf Hfx Hside.
    intro rem.
    revert CID0.
    induction rem as [| rem' IH];
      intros CID0 done m t m_ad Hrem Hsum Hrep Hview Hbase
             Hsp Hs2 Hs3 Hs4 Hs5 Hs6 Hthr Hbelow;
      [ destruct (Nat.nle_succ_0 0 Hrem) |].
    iIntros "Hcg Hcnt #Htext Hpc Hptree Hown Henv Hcont".
    iDestruct "Henv" as (γk) "(#Hlock & #Havail)".
    iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhwc Hcg]".
    iDestruct "Hhwc" as (hwmisa0 hwmseccfg0 hwpmar0 hwelp0)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & #Hkmapb & _)".
    (* ---- the iteration's numeric facts ---- *)
    pose proof (bv_unsigned_in_range 64 va) as [Hva0 _].
    assert (Hdnp : (Z.of_nat done + 1 <= Z.of_nat npages)%Z) by lia.
    destruct (z_run_iter_gen (bv_unsigned va) (Z.of_nat done) (Z.of_nat npages)
                Hva0 (Nat2Z.is_nonneg done) Hdnp Hrange)
      as (Hcnn & Hc38 & Hc64).
    assert (Hcuru : bv_unsigned (add_vec va (mword_of_int (4096 * Z.of_nat done)))
                    = bv_unsigned va + 4096 * Z.of_nat done)
      by (apply pb_va_k_unsigned; exact Hc64).
    assert (Hvpne : svpn_of (add_vec va (mword_of_int (4096 * Z.of_nat done)))
                    = vpn_at (svpn_of va) done)
      by (apply svpn_of_run; exact Hc38).
    assert (Hvpnu : bv_unsigned (vpn_at (svpn_of va) done)
                    = (bv_unsigned va + 4096 * Z.of_nat done) / 4096).
    { rewrite <- Hvpne.
      rewrite (svpn_of_unsigned_lo (add_vec va (mword_of_int (4096 * Z.of_nat done)))
                 ltac:(rewrite uint_unsigned; rewrite Hcuru; exact Hc38)).
      rewrite uint_unsigned. rewrite Hcuru.
      rewrite Z.shiftr_div_pow2; [reflexivity | lia]. }
    (* THE ONE THING THE LOOP NEEDS OF THE FIXED LEAVES: which side of the
       leaf map this vpn lives on.  It used to be DERIVED here, from the
       range premise, and that is exactly what pinned uvmunmap to runs
       strictly below the trapframe.  It is a hypothesis now
       ([BarePt.uu_vpn_ok]); the user-run seals still derive it from the
       range premise, and proc_freepagetable's two calls supply the other
       side instead. *)
    assert (Hvok : uu_vpn_ok df (vpn_at (svpn_of va) done))
      by (apply Hside; lia).
    (* ---- the instruction facts ---- *)
    iPoseProof (uui_50 with "Htext") as "Hi50".
    iPoseProof (uui_52 with "Htext") as "Hi52".
    iPoseProof (uui_54 with "Htext") as "Hi54".
    iPoseProof (uui_56 with "Htext") as "Hi56".
    iPoseProof (uui_5a with "Htext") as "Hi5a".
    iPoseProof (uui_5c with "Htext") as "Hi5c".
    iPoseProof (uui_5e with "Htext") as "Hi5e".
    iPoseProof (uui_60 with "Htext") as "Hi60".
    iPoseProof (uui_64 with "Htext") as "Hi64".
    iPoseProof (uui_66 with "Htext") as "Hi66".
    iPoseProof (uui_6a with "Htext") as "Hi6a".
    iPoseProof (uui_6c with "Htext") as "Hi6c".
    iPoseProof (uui_70 with "Htext") as "Hi70".
    iPoseProof (uui_74 with "Htext") as "Hi74".
    iPoseProof (uui_46 with "Htext") as "Hi46".
    (* ================================================================ *)
    (*  THE +0x4a JOIN: the loop tail, over the post-body descriptor.     *)
    (* ================================================================ *)
    iAssert (wp_next b p (fun (CIDt : CpuId) =>
        uu_tail_body b p spr va uroot done npages df fx um K ilvl eb mm
          CIDt lks))%I with "[Hcont]" as "TAIL".
    { iIntros (CIDt Hst mt t' m').
      iIntros "(%Htsp & %Hts2 & %Hts3 & %Hts4 & %Hts5 & %Hts6 & %Htthr
                & %Htrep & %Htview & %Htbase) Hcg Hcnt Hpc Hptree Hown".
      iPoseProof (uui_4a with "Htext") as "Hi4a".
      iPoseProof (uui_4c with "Htext") as "Hi4c".
      (* --- +0x4a c.add s2,s2,s6 : a += PGSIZE --- *)
      iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x4a)) Rs2 Rs6 mt (K - 8) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi4a").
      iIntros (CIDu Hsu) "Hcg Hpc".
      iEval (repeat rgne) in "Hcg".
      set (T1 := <[Regidx Rs2 := regval_into_reg
                    (add_vec (mt !!! Regidx Rs2) (mt !!! Regidx Rs6))]> mt).
      assert (HT1s2 : T1 !!! Regidx Rs2
                      = add_vec va (mword_of_int (4096 * Z.of_nat (S done)))).
      { rewrite /T1 upd_eq. rewrite Hts2 Hts6.
        apply mappages_va_step. vm_compute; reflexivity. }
      assert (HT1s3 : T1 !!! Regidx Rs3
                      = add_vec va (mword_of_int (4096 * Z.of_nat npages))) by lkp.
      assert (HT1sp : T1 !!! Regidx csp_rs1 = spr) by lkp.
      assert (HT1s4 : T1 !!! Regidx Rs4 = page_base uroot) by lkp.
      assert (HT1s5 : uu_s5 df T1).
      { rewrite /uu_s5 in Hts5 |- *. rewrite /T1.
        destruct df; rewrite upd_ne; [exact Hts5 | reg_neq | exact Hts5 | reg_neq]. }
      assert (HT1s6 : T1 !!! Regidx Rs6 = (mword_of_int 4096 : mword 64)) by lkp.
      assert (HT1thr : uu_thr mm T1).
      { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22. thr_peel. apply Htthr; assumption. }
      (* --- +0x4c bgeu s2,s3 : the exit test --- *)
      destruct (Nat.eq_dec rem' 0) as [Hr0 | Hrne].
      { (* the run is finished: close the table and leave at +0x76 *)
        assert (Hdn : S done = npages) by lia.
        assert (Hcmp : zopz0zKzJ_u (T1 !!! Regidx Rs2) (T1 !!! Regidx Rs3) = true).
        { rewrite HT1s2 HT1s3. rewrite Hdn. apply bc_geu. apply Z.le_refl. }
        iApply (wp_bgeu_taken_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x4c))
                  (mword_of_int 42 : mword 13) Rs3 Rs2 T1 (K - 8) b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hcmp ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi4c").
        iApply bi.later_intro. iIntros (CIDv Hsv) "Hcg Hpc".
        assert (Htgt76 : add_vec (mword_of_int (KernelSyms.uvmunmap + 0x4c) : mword 64)
                  (sign_extend' 64 (mword_of_int 42 : mword 13))
                = mword_of_int (KernelSyms.uvmunmap + 0x76)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt76) in "Hpc".
        rewrite Hdn in Htview.
        iEval (rewrite Hdn) in "Hown".
        iDestruct (uptg_rebuild (uu_fx df fx (svpn_of va) npages) uroot
                     (uu_um df um (svpn_of va) npages)
                     t' m' (uu_um_wf df um (svpn_of va) npages Hwf)
                     (uu_fx_wf df fx (svpn_of va) npages Hfx)
                     Htview Htrep Htbase with "Hptree Hown") as "Hpt".
        iDestruct (cpu_own_transport CIDt CIDv ilvl eb p b ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        iSpecialize ("Hcont" $! CIDv with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! T1 with "[%] [%] Hcg Hcnt Hpc Hpt").
        - exact HT1sp.
        - exact HT1thr. }
      (* more pages to go: fall through to the loop head *)
      assert (Hsdlt : (S done < npages)%nat) by lia.
      assert (Hcmp : zopz0zKzJ_u (T1 !!! Regidx Rs2) (T1 !!! Regidx Rs3) = false).
      { rewrite HT1s2 HT1s3. apply bc_ltu.
        rewrite (pb_va_k_unsigned va (S done)
                   ltac:(exact (proj2 (proj2 (z_run_iter_gen (bv_unsigned va)
                            (Z.of_nat (S done)) (Z.of_nat npages) Hva0
                            (Nat2Z.is_nonneg (S done)) ltac:(lia) Hrange)))) ).
        rewrite (pb_va_k_unsigned va npages
                   ltac:(exact (z_run_end64_gen (bv_unsigned va) (Z.of_nat npages)
                           Hva0 (Nat2Z.is_nonneg npages) Hrange))).
        apply z_run_strict. lia. }
      iApply (wp_bgeu_fall_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x4c))
                (mword_of_int 42 : mword 13) Rs3 Rs2 T1 (K - 8) b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp with "Hcg Hpc Hi4c").
      iIntros (CIDw Hsw) "Hcg Hpc".
      assert (Hp50 : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x4c) : mword 64) 4
                     = mword_of_int (KernelSyms.uvmunmap + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp50) in "Hpc".
      iAssert (kalloc_env γa None) as "Henv2".
      { iExists γk. iFrame "Hlock Havail". }
      iDestruct (cpu_own_transport CIDt CIDw ilvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iDestruct (wp_next_shift (CIDa := CID0) (CIDb := CIDw) ltac:(wp_next_chain)
                   with "Hcont") as "Hcont".
      iApply (IH CIDw (S done) T1 t' m' ltac:(lia) ltac:(lia) Htrep Htview Htbase
                HT1sp HT1s2 HT1s3 HT1s4 HT1s5 HT1s6 HT1thr Hbelow
                with "Hcg Hcnt Htext Hpc Hptree Hown Henv2 Hcont"). }
    (* ================================================================ *)
    (*  THE BODY: walk(pagetable, a, 0) and the two-way verdict.         *)
    (* ================================================================ *)
    (* --- +0x50 c.li a2,0 --- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x50)) Ra2
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64) m (K - 8) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi50").
    iIntros (CIDp1 Hsp1) "Hcg Hpc".
    set (L1 := <[Regidx Ra2 := regval_into_reg (mword_of_int 0 : mword 64)]> m).
    assert (Hp52 : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x50) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp52) in "Hpc".
    (* --- +0x52 c.mv a1,s2 --- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x52)) Ra1 Rs2 L1 (K - 8) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi52").
    iIntros (CIDp2 Hsp2) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (L2 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (L1 !!! Regidx Rs2))]> L1).
    assert (Hp54 : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x52) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp54) in "Hpc".
    (* --- +0x54 c.mv a0,s4 --- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x54)) Ra0 Rs4 L2 (K - 8) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi54").
    iIntros (CIDp3 Hsp3) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (L3 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (L2 !!! Regidx Rs4))]> L2).
    assert (Hp56 : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x54) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp56) in "Hpc".
    (* --- +0x56 jal ra,walk --- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x56)) Rra
              (mword_of_int 2096392 : mword 21) L3 (K - 8) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi56").
    iIntros (CIDp4 Hsp4) "Hcg Hpc".
    set (L4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x56) : mword 64) 4)]> L3).
    assert (Htgtwk : add_vec (mword_of_int (KernelSyms.uvmunmap + 0x56) : mword 64)
              (sign_extend' 64 (mword_of_int 2096392 : mword 21))
            = mword_of_int KernelSyms.walk) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtwk) in "Hpc".
    assert (HL4a0 : L4 !!! Regidx Ra0
                    = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))).
    { lkp0. rewrite Hs4 Hbase. reflexivity. }
    assert (HL4a1 : L4 !!! Regidx Ra1
                    = add_vec va (mword_of_int (4096 * Z.of_nat done))) by lkp.
    assert (HL4a2 : L4 !!! Regidx Ra2 = (mword_of_int 0 : mword 64)) by lkp.
    assert (HL4sp : L4 !!! Regidx csp_rs1 = spr) by lkp.
    assert (HL4s2 : L4 !!! Regidx Rs2
                    = add_vec va (mword_of_int (4096 * Z.of_nat done))) by lkp.
    assert (HL4s3 : L4 !!! Regidx Rs3
                    = add_vec va (mword_of_int (4096 * Z.of_nat npages))) by lkp.
    assert (HL4s4 : L4 !!! Regidx Rs4 = page_base uroot) by lkp.
    assert (HL4s5 : L4 !!! Regidx Rs5 = m !!! Regidx Rs5) by lkp.
    assert (HL4s6 : L4 !!! Regidx Rs6 = (mword_of_int 4096 : mword 64)) by lkp.
    assert (HL4thr : uu_thr mm L4).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22. thr_peel. apply Hthr; assumption. }
    assert (Hwkva : (uint (L4 !!! Regidx Ra1) < 2 ^ 38)%Z).
    { rewrite HL4a1. rewrite uint_unsigned. rewrite Hcuru.
      change (2 ^ 38)%Z with 274877906944%Z. exact Hc38. }
    assert (Hret5a : ret_pc (L4 !!! Regidx Rra) = mword_of_int (KernelSyms.uvmunmap + 0x5a)).
    { rewrite /L4 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iApply (WalkNoalloc.wp_walk_noalloc_sconf KT1 L4 t m_ad (K - 8)%nat (DfracOwn 1) b p
              ltac:(lia) HL4a0 HL4a2 Hwkva Hrep
              with "Hcg Htext Hpc Hptree").
    iIntros (CIDx Hsx mw) "Hcg Hpc Hptree %Hwcs %Hpay".
    iEval (rewrite Hret5a) in "Hpc".
    assert (Hvv : svpn_of (L4 !!! Regidx Ra1) = vpn_at (svpn_of va) done)
      by (rewrite HL4a1; exact Hvpne).
    rewrite Hvv in Hpay.
    (* ---- the recovered register facts ---- *)
    assert (Hmwsp : mw !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hwcs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HL4sp. }
    assert (Hmws2 : mw !!! Regidx Rs2
                    = add_vec va (mword_of_int (4096 * Z.of_nat done))).
    { rewrite (callee_saved_lookup Hwcs Rs2 ltac:(vm_compute; reflexivity)).
      exact HL4s2. }
    assert (Hmws3 : mw !!! Regidx Rs3
                    = add_vec va (mword_of_int (4096 * Z.of_nat npages))).
    { rewrite (callee_saved_lookup Hwcs Rs3 ltac:(vm_compute; reflexivity)).
      exact HL4s3. }
    assert (Hmws4 : mw !!! Regidx Rs4 = page_base uroot).
    { rewrite (callee_saved_lookup Hwcs Rs4 ltac:(vm_compute; reflexivity)).
      exact HL4s4. }
    assert (Hmws5 : mw !!! Regidx Rs5 = m !!! Regidx Rs5).
    { rewrite (callee_saved_lookup Hwcs Rs5 ltac:(vm_compute; reflexivity)).
      exact HL4s5. }
    assert (Hmws6 : mw !!! Regidx Rs6 = (mword_of_int 4096 : mword 64)).
    { rewrite (callee_saved_lookup Hwcs Rs6 ltac:(vm_compute; reflexivity)).
      exact HL4s6. }
    assert (Hmwthr : uu_thr mm mw).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22.
      rewrite (callee_saved_lookup Hwcs c Hc). apply HL4thr; assumption. }
    (* --- +0x5a c.mv s1,a0 --- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x5a)) Rs1 Ra0 mw (K - 8) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5a").
    iIntros (CIDy Hsy) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B1 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (mw !!! Regidx Ra0))]> mw).
    assert (HB1sp : B1 !!! Regidx csp_rs1 = spr) by lkp.
    assert (HB1s2 : B1 !!! Regidx Rs2
                    = add_vec va (mword_of_int (4096 * Z.of_nat done))) by lkp.
    assert (HB1s3 : B1 !!! Regidx Rs3
                    = add_vec va (mword_of_int (4096 * Z.of_nat npages))) by lkp.
    assert (HB1s4 : B1 !!! Regidx Rs4 = page_base uroot) by lkp.
    assert (HB1s5 : B1 !!! Regidx Rs5 = m !!! Regidx Rs5).
    { rewrite /B1. rewrite upd_ne; [exact Hmws5 | reg_neq]. }
    assert (HB1s5' : uu_s5 df B1) by (rewrite /uu_s5 HB1s5; exact Hs5).
    assert (HB1s6 : B1 !!! Regidx Rs6 = (mword_of_int 4096 : mword 64)) by lkp.
    assert (HB1thr : uu_thr mm B1).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22. thr_peel. apply Hmwthr; assumption. }
    assert (HB1a0 : B1 !!! Regidx Ra0 = mw !!! Regidx Ra0) by lkp.
    assert (HB1s1 : B1 !!! Regidx Rs1 = mw !!! Regidx Ra0).
    { rewrite /B1 upd_eq. rewrite add_vec_zero_l. reflexivity. }
    assert (Hp5c : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x5a) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5c) in "Hpc".
    assert (Htgt4a : add_vec (mword_of_int (KernelSyms.uvmunmap + 0x5c) : mword 64)
              (sign_extend' 64 (sign_extend' 13
                 (concat_vec (mword_of_int 247 : mword 8) ('b"0"))))
            = mword_of_int (KernelSyms.uvmunmap + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    destruct Hpay as [(Ha0z & Hnone) | (p2 & p1 & w0 & Hl0 & Ha0v & Hverd)].
    { (* ============ walk found no leaf table: continue ============ *)
      assert (Hbz : eq_vec (rget B1 Ra0) zero_reg = true).
      { rgne. rewrite HB1a0 Ha0z. vm_compute; reflexivity. }
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x5c))
                (mword_of_int 247 : mword 8) (Cregidx (mword_of_int 2)) Ra0 B1 (K - 8) b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                Hbz ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi5c").
      iApply bi.later_intro. iIntros (CIDz Hsz) "Hcg Hpc".
      iEval (rewrite Htgt4a) in "Hpc".
      destruct (uu_step_absent df fx um m_ad (svpn_of va) done
                  Hwf Hfx Hvok Hview Hnone) as (HstepF & Hstep).
      iDestruct (cpu_own_transport CID0 CIDz ilvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("TAIL" $! CIDz with "[%]"); [wp_next_chain|].
      iApply ("TAIL" $! B1 t m_ad with "[%] Hcg Hcnt Hpc Hptree [Hown]").
      { split_and!; try assumption; try exact Hbase.
        rewrite HstepF Hstep. exact Hview. }
      { rewrite Hstep. iExact "Hown". } }
    (* ============ walk reached the L0 slot ============ *)
    iDestruct (ptree_own_level0_ro (DfracOwn 1) t (vpn_at (svpn_of va) done) p2 p1 w0 Hl0
                 with "Hptree") as "(#Hcl0 & Hcell & Hclose)".
    iDestruct (phys_word_pointsto_ram with "Hcell") as %Hslotram.
    iDestruct (pt_slot_phys_to_mem (u_next_base p1) (vpn_idx 0 (vpn_at (svpn_of va) done))
                 (DfracOwn 1) w0 with "Hcl0 Hcell") as "Hcell".
    assert (Ha0nz : mw !!! Regidx Ra0 <> (mword_of_int 0 : mword 64)).
    { rewrite Ha0v. intro Heq. rewrite Heq in Hslotram.
      unfold addr_is_ram in Hslotram. destruct Hslotram as [Hlo _].
      apply (proj2 (Z.leb_le _ _)) in Hlo. vm_compute in Hlo. discriminate. }
    assert (Hbnz : eq_vec (rget B1 Ra0) zero_reg = false).
    { rgne. rewrite HB1a0. apply eq_vec_false_iff. intro He. apply Ha0nz.
      rewrite He. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x5c))
              (mword_of_int 247 : mword 8) (Cregidx (mword_of_int 2)) Ra0 B1 (K - 8) b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              Hbnz with "Hcg Hpc Hi5c").
    iIntros (CIDz1 Hsz1) "Hcg Hpc".
    assert (Hp5e : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x5c) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5e) in "Hpc".
    (* --- +0x5e c.ld a5,0(a0) --- *)
    assert (Hea0 : forall X : mword 64,
        add_vec X (sign_extend' 64 (zero_extend' 12
          (concat_vec (mword_of_int 0 : mword 5) ('b"000")))) = X).
    { intro X.
      replace (sign_extend' 64 (zero_extend' 12
        (concat_vec (mword_of_int 0 : mword 5) ('b"000"))) : mword 64)
        with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.uvmunmap + 0x5e)) Ra5 Ra0
              (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")))
              B1 (K - 8) w0 b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5e [Hcell]").
    { iEval (rewrite Hea0; rgne; rewrite HB1a0 Ha0v). iExact "Hcell". }
    iIntros (CIDz2 Hsz2) "Hcg Hpc Hcell".
    iEval (rewrite Hea0; rgne; rewrite HB1a0 Ha0v) in "Hcell".
    set (B2 := <[Regidx Ra5 := regval_into_reg w0]> B1).
    assert (HB2a5 : B2 !!! Regidx Ra5 = w0) by (rewrite /B2 upd_eq; reflexivity).
    (* give the tree back: the read left the slot alone *)
    iDestruct (pt_slot_mem_to_phys (u_next_base p1) (vpn_idx 0 (vpn_at (svpn_of va) done))
                 (DfracOwn 1) w0 with "Hcl0 Hcell") as "Hcell".
    iDestruct ("Hclose" with "Hcell") as "Hptree".
    assert (Hp60 : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x5e) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp60) in "Hpc".
    (* --- +0x60 andi a4,a5,1 : PTE_V --- *)
    iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x60)) Ra4 Ra5
              (mword_of_int 1 : mword 12)
              (and_vec w0 (sign_extend' 64 (mword_of_int 1 : mword 12)))
              B2 (K - 8) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rewrite HB2a5; reflexivity)
              with "Hcg Hpc Hi60").
    iIntros (CIDz3 Hsz3) "Hcg Hpc".
    set (B3 := <[Regidx Ra4 := regval_into_reg
                  (and_vec w0 (sign_extend' 64 (mword_of_int 1 : mword 12)))]> B2).
    assert (HB3a4 : B3 !!! Regidx Ra4
                    = and_vec w0 (sign_extend' 64 (mword_of_int 1 : mword 12)))
      by (rewrite /B3 upd_eq; reflexivity).
    assert (HB3sp : B3 !!! Regidx csp_rs1 = spr) by lkp.
    assert (HB3s1 : B3 !!! Regidx Rs1 = mw !!! Regidx Ra0) by lkp.
    assert (HB3s2 : B3 !!! Regidx Rs2
                    = add_vec va (mword_of_int (4096 * Z.of_nat done))) by lkp.
    assert (HB3s3 : B3 !!! Regidx Rs3
                    = add_vec va (mword_of_int (4096 * Z.of_nat npages))) by lkp.
    assert (HB3s4 : B3 !!! Regidx Rs4 = page_base uroot) by lkp.
    assert (HB3s5 : B3 !!! Regidx Rs5 = m !!! Regidx Rs5).
    { rewrite /B3. rewrite upd_ne; [| reg_neq]. rewrite /B2. rewrite upd_ne; [| reg_neq].
      exact HB1s5. }
    assert (HB3s5' : uu_s5 df B3)
      by (rewrite /uu_s5 HB3s5; exact Hs5).
    assert (HB3s6 : B3 !!! Regidx Rs6 = (mword_of_int 4096 : mword 64)) by lkp.
    assert (HB3thr : uu_thr mm B3).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22. thr_peel. apply Hmwthr; assumption. }
    assert (Hp64 : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x60) : mword 64) 4
                   = mword_of_int (KernelSyms.uvmunmap + 0x64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp64) in "Hpc".
    assert (Htgt4a' : add_vec (mword_of_int (KernelSyms.uvmunmap + 0x64) : mword 64)
              (sign_extend' 64 (sign_extend' 13
                 (concat_vec (mword_of_int 243 : mword 8) ('b"0"))))
            = mword_of_int (KernelSyms.uvmunmap + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    destruct Hverd as [Hsome | (Hw0z & Hnone)].
    2:{ (* ---- the slot holds the literal zero: continue ---- *)
      assert (Hbz : eq_vec (rget B3 Ra4) zero_reg = true).
      { rgne. rewrite HB3a4 Hw0z. vm_compute; reflexivity. }
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x64))
                (mword_of_int 243 : mword 8) (Cregidx (mword_of_int 6)) Ra4 B3 (K - 8) b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                Hbz ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi64").
      iApply bi.later_intro. iIntros (CIDz4 Hsz4) "Hcg Hpc".
      iEval (rewrite Htgt4a') in "Hpc".
      destruct (uu_step_absent df fx um m_ad (svpn_of va) done
                  Hwf Hfx Hvok Hview Hnone) as (HstepF & Hstep).
      iDestruct (cpu_own_transport CID0 CIDz4 ilvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("TAIL" $! CIDz4 with "[%]"); [wp_next_chain|].
      iApply ("TAIL" $! B3 t m_ad with "[%] Hcg Hcnt Hpc Hptree [Hown]").
      { split_and!; try assumption; try exact Hbase.
        rewrite HstepF Hstep. exact Hview. }
      { rewrite Hstep. iExact "Hown". } }
    (* ---- the vpn IS mapped: free its page and clear the leaf ---- *)
    assert (Hv0 : pte_valid w0).
    { destruct Hrep as (Hmaps & _).
      destruct (Hmaps (vpn_at (svpn_of va) done) w0 Hsome) as (q2 & q1 & Hmp).
      destruct Hmp as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hvv0 & _).
      exact Hvv0. }
    assert (Hlt54 : bv_unsigned w0 < 18014398509481984).
    { destruct Hrep as (Hmaps & _).
      destruct (Hmaps (vpn_at (svpn_of va) done) w0 Hsome) as (q2 & q1 & Hmp).
      destruct Hmp as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                        & Hvv0 & _ & Hnn & Hpb).
      exact (pte_hi_zero w0 Hvv0 Hnn Hpb). }
    assert (Hbnz4 : eq_vec (rget B3 Ra4) zero_reg = false).
    { rgne. rewrite HB3a4. rewrite (pte_valid_bit0 w0 Hv0). vm_compute; reflexivity. }
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x64))
              (mword_of_int 243 : mword 8) (Cregidx (mword_of_int 6)) Ra4 B3 (K - 8) b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              Hbnz4 with "Hcg Hpc Hi64").
    iIntros (CIDz5 Hsz5) "Hcg Hpc".
    assert (Hp66 : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x64) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x66)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp66) in "Hpc".
    (* ================================================================ *)
    (*  THE +0x46 STORE, SHARED BY BOTH do_free ARMS.                    *)
    (*  do_free != 0 falls through +0x6a..+0x72 (PTE2PA, then kfree) and  *)
    (*  reaches the store by the [c.j] at +0x74; do_free == 0 takes the   *)
    (*  [beq] at +0x66 straight to it.  Everything from the store on --   *)
    (*  the tree update, the view move, the +0x4a join -- is identical,   *)
    (*  which is why the whole [df] split is ONE [destruct] here.         *)
    (* ================================================================ *)
    iAssert (wp_next b p (fun (CIDs : CpuId) =>
        uu_store_body b p spr va uroot done npages df um K ilvl eb mm mw t
          CIDs lks))%I with "[TAIL]" as "STORE".
    { iIntros (CIDs Hss ms).
      iIntros "(%Hmksp & %Hss1 & %Hmks2 & %Hmks3 & %Hmks4 & %Hmks5 & %Hmks6 & %Hmkthr)
               Hcg Hcnt Hpc Hptree Hown".
      (* the instruction fact must be re-posed INSIDE: the outer
         [iPoseProof]s are spatial and the [with "[TAIL]"] clause does not
         carry them in (durable-notes). *)
      iPoseProof (uui_46 with "Htext") as "Hi46s".
      (* --- +0x46 sd zero,0(s1) : *pte = 0 --- *)
      iDestruct (ptree_own_level0_upd (DfracOwn 1) t (vpn_at (svpn_of va) done) p2 p1 w0 Hl0
                   with "Hptree") as "(_ & Hcell & Hupd)".
      iDestruct (pt_slot_phys_to_mem (u_next_base p1) (vpn_idx 0 (vpn_at (svpn_of va) done))
                   (DfracOwn 1) w0 with "Hcl0 Hcell") as "Hcell".
      assert (Hzoff : forall X : mword 64,
          add_vec X (sign_extend' 64 (mword_of_int 0 : mword 12)) = X).
      { intro X.
        replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
          with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
        apply kv_addv_zero. }
      iApply (wp_sd_zero_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.uvmunmap + 0x46)) Rs1
                (mword_of_int 0 : mword 12) ms (K - 8) w0 b
                with "Hcg Hpc Hi46s [Hcell]").
      { iEval (rewrite Hzoff; rgne; rewrite Hss1 Ha0v). iExact "Hcell". }
      iIntros (CIDk3 Hsk3) "Hcg Hpc Hcell".
      iEval (rewrite Hzoff; rgne; rewrite Hss1 Ha0v) in "Hcell".
      assert (Hzr : (zero_reg : mword 64) = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hzr) in "Hcell".
      iDestruct (pt_slot_mem_to_phys (u_next_base p1) (vpn_idx 0 (vpn_at (svpn_of va) done))
                   (DfracOwn 1) (mword_of_int 0) with "Hcl0 Hcell") as "Hcell".
      iDestruct ("Hupd" $! (mword_of_int 0) with "Hcell") as "Hptree".
      assert (Hp4a : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x46) : mword 64) 4
                     = mword_of_int (KernelSyms.uvmunmap + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp4a) in "Hpc".
      (* --- the new tree / map / view / descriptor --- *)
      assert (HrepS : pt_rep0 (ptree_set_leaf t (vpn_at (svpn_of va) done) (mword_of_int 0))
                              (delete (vpn_at (svpn_of va) done) m_ad))
        by (exact (pt_rep0_delete t m_ad (vpn_at (svpn_of va) done) p2 p1 w0 Hrep Hl0)).
      assert (HbaseS : pt_base (ptree_set_leaf t (vpn_at (svpn_of va) done) (mword_of_int 0))
                       = uroot)
        by (rewrite ptree_set_leaf_base; exact Hbase).
      assert (HviewS : uptg_view (uu_fx df fx (svpn_of va) (S done))
                (uu_um df um (svpn_of va) (S done))
                (delete (vpn_at (svpn_of va) done) m_ad)).
      { exact (uu_step_delete df fx um m_ad (svpn_of va) done
                 Hwf Hfx Hvok Hview). }
      iDestruct (cpu_own_transport CIDs CIDk3 ilvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("TAIL" $! CIDk3 with "[%]"); [wp_next_chain|].
      iApply ("TAIL" $! ms (ptree_set_leaf t (vpn_at (svpn_of va) done) (mword_of_int 0))
                          (delete (vpn_at (svpn_of va) done) m_ad)
                with "[%] Hcg Hcnt Hpc Hptree [Hown]").
      { split_and!; assumption. }
      { iExact "Hown". }
    }
    destruct df.
    2:{ (* ============ do_free == 0: NOTHING is freed ============ *)
      (* proc_freepagetable's two calls and proc_pagetable's second failure
         tail land here.  The leaf being cleared is a FIXED one, whose page
         is kernel text (trampoline) or belongs to [proc_priv] (trapframe),
         so there is no [page_own] to hand kfree and no [upt_pages_own] to
         shrink -- which is exactly why the branch skips the call. *)
      assert (Hs5z : eq_vec (rget B3 Rs5) zero_reg = true).
      { rgne. rewrite HB3s5. rewrite /uu_s5 in Hs5. rewrite Hs5.
        exact bc_moi_iszero. }
      iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x66))
                (mword_of_int 8160 : mword 13) Rs5 B3 (K - 8) b
                ltac:(vm_compute; discriminate) Hs5z
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi66").
      iApply bi.later_intro. iIntros (CIDz6 Hsz6) "Hcg Hpc".
      assert (Htgt46' : add_vec (mword_of_int (KernelSyms.uvmunmap + 0x66) : mword 64)
                (sign_extend' 64 (mword_of_int 8160 : mword 13))
              = mword_of_int (KernelSyms.uvmunmap + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt46') in "Hpc".
      iDestruct (cpu_own_transport CID0 CIDz6 ilvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("STORE" $! CIDz6 with "[%]"); [wp_next_chain|].
      iApply ("STORE" $! B3 with "[%] Hcg Hcnt Hpc Hptree [Hown]").
      { split_and!; assumption. }
      { iExact "Hown". } }
    (* ============ do_free != 0: PTE2PA, kfree, then the store ========= *)
    (* --- +0x66 beq s5,zero : do_free != 0, so NOT taken --- *)
    assert (Hs5nz : eq_vec (rget B3 Rs5) zero_reg = false).
    { rgne. rewrite HB3s5. apply eq_vec_false_iff. intro He.
      rewrite /uu_s5 in Hs5. apply Hs5.
      rewrite He. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x66))
              (mword_of_int 8160 : mword 13) Rs5 B3 (K - 8) b
              ltac:(vm_compute; discriminate) Hs5nz
              with "Hcg Hpc Hi66").
    iIntros (CIDz6 Hsz6) "Hcg Hpc".
    assert (Hp6a : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x66) : mword 64) 4
                   = mword_of_int (KernelSyms.uvmunmap + 0x6a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6a) in "Hpc".
    (* --- +0x6a c.srli a5,a5,0xa  /  +0x6c slli a0,a5,0xc : PTE2PA --- *)
    assert (HB3a5 : B3 !!! Regidx Ra5 = w0) by lkp.
    iApply (wp_csrli_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x6a)) (Cregidx (mword_of_int 7))
              Ra5 (mword_of_int 10 : mword 6) B3 (K - 8) b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok)
              with "Hcg Hpc Hi6a").
    iIntros (CIDz7 Hsz7) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B4 := <[Regidx Ra5 := regval_into_reg
        (shift_bits_right (B3 !!! Regidx Ra5)
           (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> B3).
    assert (HB4a5 : B4 !!! Regidx Ra5
                    = shift_bits_right w0
                        (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0)).
    { rewrite /B4 upd_eq. rewrite HB3a5. reflexivity. }
    assert (Hp6c : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x6a) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x6c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6c) in "Hpc".
    assert (Hs10 : int_of_mword false
              (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0) = 10)
      by (vm_compute; reflexivity).
    assert (Hs12 : int_of_mword false
              (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0) = 12)
      by (vm_compute; reflexivity).
    assert (Hpte2pa : shift_bits_left (rget B4 Ra5)
              (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0)
            = page_base (pte_ppn w0)).
    { rgne. rewrite HB4a5. apply pte2pa; [ exact Hs10 | exact Hs12 | exact Hlt54 ]. }
    iApply (wp_slli_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x6c)) Ra0 Ra5
              (mword_of_int 12 : mword 6) (page_base (pte_ppn w0)) B4 (K - 8) b
              ltac:(vm_compute; discriminate) ltac:(rdok) Hpte2pa
              with "Hcg Hpc Hi6c").
    iIntros (CIDz8 Hsz8) "Hcg Hpc".
    set (B5 := <[Regidx Ra0 := regval_into_reg (page_base (pte_ppn w0))]> B4).
    assert (Hp70 : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x6c) : mword 64) 4
                   = mword_of_int (KernelSyms.uvmunmap + 0x70)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp70) in "Hpc".
    (* --- the page comes OUT of the invariant --- *)
    destruct (uptg_view_um fx (um_del_run um (svpn_of va) done) m_ad
                (vpn_at (svpn_of va) done) w0 Hfx Hvok Hview Hsome)
      as (wu & au & du & Humsome & Hw0ad).
    assert (Hppn : pte_ppn w0 = pte_ppn wu)
      by (rewrite Hw0ad; apply pte_ppn_set_ad).
    assert (Hwfd : uptg_wf (um_del_run um (svpn_of va) done))
      by (apply uptg_wf_del_run; exact Hwf).
    assert (Hpv : page_valid (page_base (pte_ppn wu)))
      by (exact (uptg_page_valid (um_del_run um (svpn_of va) done)
                   (vpn_at (svpn_of va) done) wu Hwfd Humsome)).
    iDestruct (uptg_own_shrink (um_del_run um (svpn_of va) done)
                 (vpn_at (svpn_of va) done) wu Hwfd Humsome with "Hkmapb Hown")
      as "[Hpage Hown]".
    (* --- +0x70 jal ra,kfree --- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x70)) Rra
              (mword_of_int 2095062 : mword 21) B5 (K - 8) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi70").
    iIntros (CIDz9 Hsz9) "Hcg Hpc".
    set (B6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x70) : mword 64) 4)]> B5).
    assert (Htgtkf : add_vec (mword_of_int (KernelSyms.uvmunmap + 0x70) : mword 64)
              (sign_extend' 64 (mword_of_int 2095062 : mword 21))
            = mword_of_int KernelSyms.kfree) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtkf) in "Hpc".
    assert (HB6a0 : B6 !!! Regidx Ra0 = page_base (pte_ppn wu)).
    { rewrite /B6. rewrite upd_ne; [| reg_neq]. rewrite /B5 upd_eq.
      rewrite Hppn. reflexivity. }
    assert (HB6sp : B6 !!! Regidx csp_rs1 = spr) by lkp.
    assert (HB6s1 : B6 !!! Regidx Rs1 = mw !!! Regidx Ra0) by lkp.
    assert (HB6s2 : B6 !!! Regidx Rs2
                    = add_vec va (mword_of_int (4096 * Z.of_nat done))) by lkp.
    assert (HB6s3 : B6 !!! Regidx Rs3
                    = add_vec va (mword_of_int (4096 * Z.of_nat npages))) by lkp.
    assert (HB6s4 : B6 !!! Regidx Rs4 = page_base uroot) by lkp.
    assert (HB6s5 : B6 !!! Regidx Rs5 = m !!! Regidx Rs5).
    { rewrite /B6. rewrite upd_ne; [| reg_neq]. rewrite /B5. rewrite upd_ne; [| reg_neq].
      rewrite /B4. rewrite upd_ne; [| reg_neq]. exact HB3s5. }
    assert (HB6s6 : B6 !!! Regidx Rs6 = (mword_of_int 4096 : mword 64)) by lkp.
    assert (HB6thr : uu_thr mm B6).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22. thr_peel. apply Hmwthr; assumption. }
    assert (Hret74 : ret_pc (B6 !!! Regidx Rra) = mword_of_int (KernelSyms.uvmunmap + 0x74)).
    { rewrite /B6 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iDestruct (cpu_own_transport CID0 CIDz9 ilvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Kfree.wp_kfree_sconf KT1 γa γk (mword_of_int KernelSyms.kmem)
              (mword_of_int (KernelSyms.kmem + 24)) B6 None ilvl eb p (K - 8)%nat b lks
              ltac:(lia) ltac:(reflexivity) ltac:(reflexivity) Hilvl Hbelow
              with "Hcg Hcnt Htext Hpc Hlock [Hpage] Havail").
    all: try lkbelow.
    { rewrite /kfree_pre HB6a0.
      iSplitR; [iPureIntro; exact Hpv | iExact "Hpage"]. }
    iIntros (CIDk1 Hsk1 mk) "Hcg Hcnt Hpc %Hkcs _".
    iEval (rewrite Hret74) in "Hpc".
    assert (Hmksp : mk !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hkcs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HB6sp. }
    assert (Hmks1 : mk !!! Regidx Rs1 = mw !!! Regidx Ra0).
    { rewrite (callee_saved_lookup Hkcs Rs1 ltac:(vm_compute; reflexivity)).
      exact HB6s1. }
    assert (Hmks2 : mk !!! Regidx Rs2
                    = add_vec va (mword_of_int (4096 * Z.of_nat done))).
    { rewrite (callee_saved_lookup Hkcs Rs2 ltac:(vm_compute; reflexivity)).
      exact HB6s2. }
    assert (Hmks3 : mk !!! Regidx Rs3
                    = add_vec va (mword_of_int (4096 * Z.of_nat npages))).
    { rewrite (callee_saved_lookup Hkcs Rs3 ltac:(vm_compute; reflexivity)).
      exact HB6s3. }
    assert (Hmks4 : mk !!! Regidx Rs4 = page_base uroot).
    { rewrite (callee_saved_lookup Hkcs Rs4 ltac:(vm_compute; reflexivity)).
      exact HB6s4. }
    assert (Hmks5 : uu_s5 true mk).
    { rewrite /uu_s5.
      rewrite (callee_saved_lookup Hkcs Rs5 ltac:(vm_compute; reflexivity)).
      rewrite HB6s5. rewrite /uu_s5 in Hs5. exact Hs5. }
    assert (Hmks6 : mk !!! Regidx Rs6 = (mword_of_int 4096 : mword 64)).
    { rewrite (callee_saved_lookup Hkcs Rs6 ltac:(vm_compute; reflexivity)).
      exact HB6s6. }
    assert (Hmkthr : uu_thr mm mk).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22.
      rewrite (callee_saved_lookup Hkcs c Hc). apply HB6thr; assumption. }
    (* --- +0x74 c.j -0x2e : back to the store --- *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x74))
              (sign_extend' 21 (concat_vec (mword_of_int 2025 : mword 11) ('b"0")))
              mk (K - 8) b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi74").
    iIntros (CIDk2 Hsk2). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Htgt46 : add_vec (mword_of_int (KernelSyms.uvmunmap + 0x74) : mword 64)
              (sign_extend' 64 (sign_extend' 21
                 (concat_vec (mword_of_int 2025 : mword 11) ('b"0"))))
            = mword_of_int (KernelSyms.uvmunmap + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt46) in "Hpc".
    iDestruct (cpu_own_transport CIDk1 CIDk2 ilvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iSpecialize ("STORE" $! CIDk2 with "[%]"); [wp_next_chain|].
    iApply ("STORE" $! mk with "[%] Hcg Hcnt Hpc Hptree [Hown]").
    { split_and!; assumption. }
    { iExact "Hown". }
  Qed.

  (* ================================================================== *)
  (*  THE WHOLE FUNCTION, over the [fx] axis.  The two sealed instances *)
  (*  below are this lemma at [Some tfp] and at [None].                  *)
  (* ================================================================== *)
  Lemma wp_uvmunmap_gen
      (γa : gname) (mm : regfile)
      (fx : gmap (mword 27) (mword 64)) (uroot : mword 44)
      (um : gmap (mword 27) (mword 64))
      (npages : nat) (K : nat) (eb : bool) (p : mword 64)
      (ilvl : nat) (b df : bool) (lks : gset string) :
    let pcE : mword 64 := mword_of_int KernelSyms.uvmunmap in
    let va := mm !!! Regidx (mword_of_int 11) in
    let vpn0 := svpn_of va in
    let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
    (22 <= K)%nat ->
    (Z.of_nat ilvl + 1 < 2 ^ 31)%Z ->
    mm !!! Regidx (mword_of_int 10) = page_base uroot ->
    subrange_vec_dec va 11 0 = (zeros' 12 : mword 12) ->
    mm !!! Regidx (mword_of_int 12) = (mword_of_int (Z.of_nat npages) : mword 64) ->
    (* do_free, as the boolean the whole proof is indexed by *)
    (if df then mm !!! Regidx (mword_of_int 13) <> (mword_of_int 0 : mword 64)
           else mm !!! Regidx (mword_of_int 13) = (mword_of_int 0 : mword 64)) ->
    (* the run stays inside the Sv39 user space and does not wrap.  This is
       WIDER than [uvm_maxsz]: a fixed-leaf run ends AT the top of it. *)
    (uint va + Z.of_nat npages * 4096 <= 2 ^ 38)%Z ->
    (* ...and which side of the leaf map its vpns are on *)
    (forall k : nat, (k < npages)%nat -> uu_vpn_ok df (vpn_at vpn0 k)) ->
    (* threaded straight to [uu_loop]: kfree's "kmem" bound applies only
       when [do_free != 0]. *)
    (if df then locks_below lks "kmem" else True) ->
    sie_cap_gpr KT1 mm K b p -∗
    cpu_own ilvl eb p b lks -∗
    kernel_text -∗
    pc_is pcE -∗
    uptg fx uroot um -∗
    kalloc_env γa None -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ (mr : regfile),
      sie_cap_gpr KT1 mr K b p -∗
      cpu_own ilvl eb p b lks -∗
      pc_is ret_tgt -∗
      ⌜callee_saved mm mr⌝ -∗
      uptg (uu_fx df fx vpn0 npages) uroot (uu_um df um vpn0 npages) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pcE va vpn0 ret_tgt HK Hilvl Hroot Hval Hnpr Hdf Hrange Hside Hbelow.
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))).
    iIntros "Hcg Hcnt #Htext Hpc Hpt Henv Hcont".
    (* ---- the range premise, as plain [Z] ---- *)
    assert (Hrz : (bv_unsigned va + Z.of_nat npages * 4096 <= 274877906944)%Z).
    { rewrite uint_unsigned in Hrange.
      change (2 ^ 38)%Z with 274877906944%Z in Hrange. exact Hrange. }
    assert (Hva12 : bv_unsigned va mod 4096 = 0) by (apply aligned12_unsigned; exact Hval).
    pose proof (bv_unsigned_in_range 64 va) as [Hva0 _].
    iPoseProof (uui_00 with "Htext") as "Hi00".
    iPoseProof (uui_02 with "Htext") as "Hi02".
    iPoseProof (uui_04 with "Htext") as "Hi04".
    iPoseProof (uui_06 with "Htext") as "Hi06".
    iPoseProof (uui_08 with "Htext") as "Hi08".
    iPoseProof (uui_0c with "Htext") as "Hi0c".
    iPoseProof (uui_0e with "Htext") as "Hi0e".
    iPoseProof (uui_10 with "Htext") as "Hi10".
    iPoseProof (uui_12 with "Htext") as "Hi12".
    iPoseProof (uui_14 with "Htext") as "Hi14".
    iPoseProof (uui_16 with "Htext") as "Hi16".
    iPoseProof (uui_18 with "Htext") as "Hi18".
    iPoseProof (uui_1a with "Htext") as "Hi1a".
    iPoseProof (uui_1c with "Htext") as "Hi1c".
    iPoseProof (uui_1e with "Htext") as "Hi1e".
    iPoseProof (uui_20 with "Htext") as "Hi20".
    iPoseProof (uui_24 with "Htext") as "Hi24".
    iPoseProof (uui_26 with "Htext") as "Hi26".
    (* --- +0x00 c.addi16sp sp,-64 : the 8-slot frame push --- *)
    assert (Hspm : mm !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))
                    = pa_stk (mm !!! Regidx csp_rs1) 8).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 60 : mword 6) mm K 8 b
              ltac:(lia) Hpush with "Hcg Hpc Hi00").
    iIntros (CIDq1 Hsq1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (mm !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))]> mm).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))]> mm) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & _)".
    iDestruct "S1" as (u1) "Hk1".   iDestruct "S2" as (u2) "Hk2".
    iDestruct "S3" as (u3) "Hk3".   iDestruct "S4" as (u4) "Hk4".
    iDestruct "S5" as (u5) "Hk5".   iDestruct "S6" as (u6) "Hk6".
    iDestruct "S7" as (u7) "Hk7".   iDestruct "S8" as (u8) "Hk8".
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (unfold spr, sp0; slot_addr).
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (unfold spr, sp0; slot_addr).
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (unfold spr, sp0; slot_addr).
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (unfold spr, sp0; slot_addr).
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (unfold spr, sp0; slot_addr).
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk sp0 6) by (unfold spr, sp0; slot_addr).
    assert (Hb7 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk sp0 7) by (unfold spr, sp0; slot_addr).
    assert (Hb8 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk sp0 8) by (unfold spr, sp0; slot_addr).
    assert (Hq02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.uvmunmap + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq02) in "Hpc".
    (* --- +0x02 c.sdsp ra,56(sp) --- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x02)) (mword_of_int 7 : mword 6) Rra
              R1 (K - 8) u1 b with "Hcg Hpc Hi02 [Hk1]").
    { iEval (rewrite HspR1 Hb1). iExact "Hk1". }
    iIntros (CIDq2 Hsq2) "Hcg Hpc Hk1". iEval (rewrite HspR1 Hb1) in "Hk1".
    iEval (rgne) in "Hk1".
    assert (HR1ra : R1 !!! Regidx Rra = mm !!! Regidx Rra) by lkp.
    iEval (rewrite HR1ra) in "Hk1".
    assert (Hq04 : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x02) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq04) in "Hpc".
    (* --- +0x04 c.sdsp s0,48(sp) --- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x04)) (mword_of_int 6 : mword 6) Rs0
              R1 (K - 8) u2 b with "Hcg Hpc Hi04 [Hk2]").
    { iEval (rewrite HspR1 Hb2). iExact "Hk2". }
    iIntros (CIDq3 Hsq3) "Hcg Hpc Hk2". iEval (rewrite HspR1 Hb2) in "Hk2".
    iEval (rgne) in "Hk2".
    assert (HR1s0 : R1 !!! Regidx Rs0 = mm !!! Regidx Rs0) by lkp.
    iEval (rewrite HR1s0) in "Hk2".
    assert (Hq06 : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x04) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq06) in "Hpc".
    (* --- +0x06 c.addi4spn s0,sp,64 --- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x06)) (Cregidx (mword_of_int 0))
              (mword_of_int 16 : mword 8) Rs0 R1 (K - 8) b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok)
              with "Hcg Hpc Hi06").
    iIntros (CIDq4 Hsq4) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))))]> R1).
    assert (Hq08 : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x06) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq08) in "Hpc".
    (* --- +0x08 slli a5,a1,0x34 : the alignment test --- *)
    assert (Hs52 : int_of_mword false
              (subrange_vec_dec (mword_of_int 52 : mword 6) (Z.sub log2_xlen 1) 0) = 52)
      by (vm_compute; reflexivity).
    assert (HR2a1 : R2 !!! Regidx Ra1 = va) by lkp.
    assert (Hshl : shift_bits_left (rget R2 Ra1)
              (subrange_vec_dec (mword_of_int 52 : mword 6) (Z.sub log2_xlen 1) 0)
            = (mword_of_int 0 : mword 64)).
    { rgne. rewrite HR2a1. exact (shl52_aligned va _ _ Hs52 Hva12). }
    iApply (wp_slli_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x08)) Ra5 Ra1
              (mword_of_int 52 : mword 6) (mword_of_int 0 : mword 64) R2 (K - 8) b
              ltac:(vm_compute; discriminate) ltac:(rdok) Hshl
              with "Hcg Hpc Hi08").
    iIntros (CIDq5 Hsq5) "Hcg Hpc".
    set (R3 := <[Regidx Ra5 := regval_into_reg (mword_of_int 0 : mword 64)]> R2).
    assert (Hq0c : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x08) : mword 64) 4
                   = mword_of_int (KernelSyms.uvmunmap + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq0c) in "Hpc".
    (* --- +0x0c c.bnez a5 : NOT taken (the panic block is dead) --- *)
    assert (Hbnz : neq_vec (R3 !!! Regidx Ra5) zero_reg = false).
    { rewrite /R3 upd_eq. vm_compute; reflexivity. }
    iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x0c))
              (mword_of_int 17 : mword 8) (Cregidx (mword_of_int 7)) Ra5 R3 (K - 8) b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hbnz
              with "Hcg Hpc Hi0c").
    iIntros (CIDq6 Hsq6) "Hcg Hpc".
    assert (Hq0e : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x0c) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq0e) in "Hpc".
    assert (HspR3 : R3 !!! Regidx csp_rs1 = spr) by lkp.
    (* --- +0x0e .. +0x16 : push s2..s6 --- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x0e)) (mword_of_int 4 : mword 6) Rs2
              R3 (K - 8) u4 b with "Hcg Hpc Hi0e [Hk4]").
    { iEval (rewrite HspR3 Hb4). iExact "Hk4". }
    iIntros (CIDq7 Hsq7) "Hcg Hpc Hk4". iEval (rewrite HspR3 Hb4) in "Hk4".
    iEval (rgne) in "Hk4".
    assert (HR3s2 : R3 !!! Regidx Rs2 = mm !!! Regidx Rs2) by lkp.
    iEval (rewrite HR3s2) in "Hk4".
    assert (Hq10 : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x0e) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq10) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x10)) (mword_of_int 3 : mword 6) Rs3
              R3 (K - 8) u5 b with "Hcg Hpc Hi10 [Hk5]").
    { iEval (rewrite HspR3 Hb5). iExact "Hk5". }
    iIntros (CIDq8 Hsq8) "Hcg Hpc Hk5". iEval (rewrite HspR3 Hb5) in "Hk5".
    iEval (rgne) in "Hk5".
    assert (HR3s3 : R3 !!! Regidx Rs3 = mm !!! Regidx Rs3) by lkp.
    iEval (rewrite HR3s3) in "Hk5".
    assert (Hq12 : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x10) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq12) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x12)) (mword_of_int 2 : mword 6) Rs4
              R3 (K - 8) u6 b with "Hcg Hpc Hi12 [Hk6]").
    { iEval (rewrite HspR3 Hb6). iExact "Hk6". }
    iIntros (CIDq9 Hsq9) "Hcg Hpc Hk6". iEval (rewrite HspR3 Hb6) in "Hk6".
    iEval (rgne) in "Hk6".
    assert (HR3s4 : R3 !!! Regidx Rs4 = mm !!! Regidx Rs4) by lkp.
    iEval (rewrite HR3s4) in "Hk6".
    assert (Hq14 : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x12) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq14) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x14)) (mword_of_int 1 : mword 6) Rs5
              R3 (K - 8) u7 b with "Hcg Hpc Hi14 [Hk7]").
    { iEval (rewrite HspR3 Hb7). iExact "Hk7". }
    iIntros (CIDq10 Hsq10) "Hcg Hpc Hk7". iEval (rewrite HspR3 Hb7) in "Hk7".
    iEval (rgne) in "Hk7".
    assert (HR3s5 : R3 !!! Regidx Rs5 = mm !!! Regidx Rs5) by lkp.
    iEval (rewrite HR3s5) in "Hk7".
    assert (Hq16 : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x14) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq16) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x16)) (mword_of_int 0 : mword 6) Rs6
              R3 (K - 8) u8 b with "Hcg Hpc Hi16 [Hk8]").
    { iEval (rewrite HspR3 Hb8). iExact "Hk8". }
    iIntros (CIDq11 Hsq11) "Hcg Hpc Hk8". iEval (rewrite HspR3 Hb8) in "Hk8".
    iEval (rgne) in "Hk8".
    assert (HR3s6 : R3 !!! Regidx Rs6 = mm !!! Regidx Rs6) by lkp.
    iEval (rewrite HR3s6) in "Hk8".
    assert (Hq18 : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x16) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq18) in "Hpc".
    (* --- +0x18 c.mv s4,a0  /  +0x1a c.mv s2,a1  /  +0x1c c.mv s5,a3 --- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x18)) Rs4 Ra0 R3 (K - 8) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18").
    iIntros (CIDq12 Hsq12) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R4 := <[Regidx Rs4 := regval_into_reg (add_vec zero_reg (R3 !!! Regidx Ra0))]> R3).
    assert (Hq1a : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x18) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq1a) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x1a)) Rs2 Ra1 R4 (K - 8) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a").
    iIntros (CIDq13 Hsq13) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R5 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (R4 !!! Regidx Ra1))]> R4).
    assert (Hq1c : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x1a) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq1c) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x1c)) Rs5 Ra3 R5 (K - 8) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c").
    iIntros (CIDq14 Hsq14) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R6 := <[Regidx Rs5 := regval_into_reg (add_vec zero_reg (R5 !!! Regidx Ra3))]> R5).
    assert (Hq1e : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x1c) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq1e) in "Hpc".
    (* --- +0x1e c.slli a2,a2,0xc --- *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x1e)) (Regidx Ra2) Ra2
              (mword_of_int 12 : mword 6) R6 (K - 8) b
              ltac:(reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok)
              with "Hcg Hpc Hi1e").
    iIntros (CIDq15 Hsq15) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R7 := <[Regidx Ra2 := regval_into_reg
        (shift_bits_left (R6 !!! Regidx Ra2)
           (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> R6).
    assert (Hq20 : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x1e) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq20) in "Hpc".
    (* --- +0x20 add s3,a2,a1 : the loop bound --- *)
    assert (Hs12' : int_of_mword false
              (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0) = 12)
      by (vm_compute; reflexivity).
    assert (HR7a2 : R7 !!! Regidx Ra2
                    = shift_bits_left (mword_of_int (Z.of_nat npages) : mword 64)
                        (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0)).
    { rewrite /R7 upd_eq. rewrite (_ : R6 !!! Regidx Ra2
                                      = (mword_of_int (Z.of_nat npages) : mword 64));
        [reflexivity | lkp0; exact Hnpr]. }
    assert (HR7a1 : R7 !!! Regidx Ra1 = va) by lkp.
    assert (Hbnd : add_vec (rget R7 Ra2) (rget R7 Ra1)
                   = add_vec va (mword_of_int (4096 * Z.of_nat npages))).
    { repeat rgne. rewrite HR7a2 HR7a1. apply shl12_pages_add. exact Hs12'. }
    iApply (wp_add_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x20)) Rs3 Ra2 Ra1
              (add_vec va (mword_of_int (4096 * Z.of_nat npages))) R7 (K - 8) b
              ltac:(vm_compute; discriminate) ltac:(rdok) Hbnd
              with "Hcg Hpc Hi20").
    iIntros (CIDq16 Hsq16) "Hcg Hpc".
    set (R8 := <[Regidx Rs3 := regval_into_reg
                  (add_vec va (mword_of_int (4096 * Z.of_nat npages)))]> R7).
    assert (Hq24 : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x20) : mword 64) 4
                   = mword_of_int (KernelSyms.uvmunmap + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq24) in "Hpc".
    (* --- +0x24 c.lui s6,0x1 : PGSIZE --- *)
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x24)) Rs6
              (sign_extend' 20 (mword_of_int 1 : mword 6)) (mword_of_int 4096 : mword 64)
              R8 (K - 8) b ltac:(vm_compute; discriminate) ltac:(rdok)
              lui_4096 with "Hcg Hpc Hi24").
    iIntros (CIDq17 Hsq17) "Hcg Hpc".
    set (R9 := <[Regidx Rs6 := regval_into_reg (mword_of_int 4096 : mword 64)]> R8).
    assert (Hq26 : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x24) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq26) in "Hpc".
    (* ---- the register facts at the loop entry ---- *)
    assert (HR9sp : R9 !!! Regidx csp_rs1 = spr) by lkp.
    assert (HR9a1 : R9 !!! Regidx Ra1 = va) by lkp.
    assert (HR9s2 : R9 !!! Regidx Rs2 = va).
    { rewrite /R9. rewrite upd_ne; [| reg_neq]. rewrite /R8. rewrite upd_ne; [| reg_neq].
      rewrite /R7. rewrite upd_ne; [| reg_neq]. rewrite /R6. rewrite upd_ne; [| reg_neq].
      rewrite /R5 upd_eq. rewrite add_vec_zero_l.
      rewrite /R4. rewrite upd_ne; [| reg_neq]. reflexivity. }
    assert (HR9s3 : R9 !!! Regidx Rs3
                    = add_vec va (mword_of_int (4096 * Z.of_nat npages))) by lkp.
    assert (HR9s4 : R9 !!! Regidx Rs4 = page_base uroot).
    { rewrite /R9. rewrite upd_ne; [| reg_neq]. rewrite /R8. rewrite upd_ne; [| reg_neq].
      rewrite /R7. rewrite upd_ne; [| reg_neq]. rewrite /R6. rewrite upd_ne; [| reg_neq].
      rewrite /R5. rewrite upd_ne; [| reg_neq]. rewrite /R4 upd_eq.
      rewrite add_vec_zero_l. lkp0. exact Hroot. }
    assert (HR9s5 : uu_s5 df R9).
    { rewrite /uu_s5. destruct df;
        (rewrite /R9; rewrite upd_ne; [| reg_neq]; rewrite /R8; rewrite upd_ne; [| reg_neq];
         rewrite /R7; rewrite upd_ne; [| reg_neq]; rewrite /R6 upd_eq;
         rewrite add_vec_zero_l; lkp0; exact Hdf). }
    assert (HR9s6 : R9 !!! Regidx Rs6 = (mword_of_int 4096 : mword 64)) by lkp.
    assert (HR9thr1 : uu_thr1 mm R9).
    { intros c Hc H2 H8 H18 H19 H20 H21 H22. thr_peel. reflexivity. }
    (* ---- the loop-bound comparison at +0x26 ---- *)
    assert (Hends : bv_unsigned (add_vec va (mword_of_int (4096 * Z.of_nat npages)))
                    = bv_unsigned va + 4096 * Z.of_nat npages).
    { apply pb_va_k_unsigned.
      exact (z_run_end64_gen (bv_unsigned va) (Z.of_nat npages) Hva0
               (Nat2Z.is_nonneg npages) Hrz). }
    destruct (Nat.eq_dec npages 0) as [Hnp0 | Hnppos].
    { (* ============ npages == 0: nothing to do ============ *)
      assert (Hcmp : zopz0zKzJ_u (R9 !!! Regidx Ra1) (R9 !!! Regidx Rs3) = true).
      { rewrite HR9a1 HR9s3. apply bc_geu. rewrite Hends. rewrite Hnp0. cbn [Z.of_nat]. lia. }
      iApply (wp_bgeu_taken_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x26))
                (mword_of_int 82 : mword 13) Rs3 Ra1 R9 (K - 8) b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi26").
      iApply bi.later_intro. iIntros (CIDr1 Hsr1) "Hcg Hpc".
      assert (Htgt78 : add_vec (mword_of_int (KernelSyms.uvmunmap + 0x26) : mword 64)
                (sign_extend' 64 (mword_of_int 82 : mword 13))
              = mword_of_int (KernelSyms.uvmunmap + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt78) in "Hpc".
      iApply (uu_epilogue mm R9 K sp0 b p ltac:(lia) Hspm HR9sp HR9thr1
                with "Hcg Htext Hpc Hk1 Hk2 [Hk3] Hk4 Hk5 Hk6 Hk7 Hk8").
      { iExists u3. iExact "Hk3". }
      iIntros (CIDr2 Hsr2 mf) "Hcg Hpc %Hcs".
      iDestruct (cpu_own_transport CID CIDr2 ilvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("Hcont" $! CIDr2 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "Hcg Hcnt Hpc [%] [Hpt]").
      { exact Hcs. }
      { rewrite Hnp0. rewrite /uu_fx /uu_um.
        destruct df; rewrite um_del_run_0; iExact "Hpt". } }
    (* ============ npages >= 1: run the loop ============ *)
    assert (Hcmp : zopz0zKzJ_u (R9 !!! Regidx Ra1) (R9 !!! Regidx Rs3) = false).
    { rewrite HR9a1 HR9s3. apply bc_ltu. rewrite Hends.
      assert (Hnp1 : (1 <= Z.of_nat npages)%Z) by lia. lia. }
    iApply (wp_bgeu_fall_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x26))
              (mword_of_int 82 : mword 13) Rs3 Ra1 R9 (K - 8) b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              Hcmp with "Hcg Hpc Hi26").
    iIntros (CIDr3 Hsr3) "Hcg Hpc".
    assert (Hq2a : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x26) : mword 64) 4
                   = mword_of_int (KernelSyms.uvmunmap + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq2a) in "Hpc".
    iPoseProof (uui_2a with "Htext") as "Hi2a".
    iPoseProof (uui_2c with "Htext") as "Hi2c".
    iPoseProof (uui_76 with "Htext") as "Hi76".
    (* --- +0x2a c.sdsp s1,40(sp) : the shrink-wrapped save --- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x2a)) (mword_of_int 5 : mword 6) Rs1
              R9 (K - 8) u3 b with "Hcg Hpc Hi2a [Hk3]").
    { iEval (rewrite HR9sp Hb3). iExact "Hk3". }
    iIntros (CIDr4 Hsr4) "Hcg Hpc Hk3". iEval (rewrite HR9sp Hb3) in "Hk3".
    iEval (rgne) in "Hk3".
    assert (HR9s1 : R9 !!! Regidx Rs1 = mm !!! Regidx Rs1) by lkp.
    iEval (rewrite HR9s1) in "Hk3".
    assert (Hq2c : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x2a) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq2c) in "Hpc".
    (* --- +0x2c c.j +0x24 : enter the loop --- *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x2c))
              (sign_extend' 21 (concat_vec (mword_of_int 18 : mword 11) ('b"0")))
              R9 (K - 8) b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi2c").
    iIntros (CIDr5 Hsr5). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Htgt50 : add_vec (mword_of_int (KernelSyms.uvmunmap + 0x2c) : mword 64)
              (sign_extend' 64 (sign_extend' 21
                 (concat_vec (mword_of_int 18 : mword 11) ('b"0"))))
            = mword_of_int (KernelSyms.uvmunmap + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt50) in "Hpc".
    (* --- open the table ONCE --- *)
    iDestruct (uptg_acc_rep0 fx uroot um with "Hpt") as (t m_ad)
      "(%Hrep & %Hview & %Hbase & %Hwf & %Hfx & Hptree & Hown)".
    assert (HR9s2' : R9 !!! Regidx Rs2 = add_vec va (mword_of_int (4096 * Z.of_nat 0))).
    { rewrite HR9s2. cbn [Z.of_nat].
      replace (4096 * 0)%Z with 0%Z by reflexivity.
      symmetry. apply kv_addv_zero. }
    assert (HR9thr : uu_thr mm R9).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22. apply HR9thr1; assumption. }
    iDestruct (cpu_own_transport CID CIDr5 ilvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (uu_loop γa mm fx uroot um npages K eb b df p va spr ilvl lks
              HK Hilvl Hrz Hwf Hfx Hside
              npages 0%nat R9 t m_ad ltac:(lia) ltac:(lia) Hrep
              ltac:(rewrite /uu_fx /uu_um; destruct df;
                    rewrite um_del_run_0; exact Hview) Hbase
              HR9sp HR9s2' HR9s3 HR9s4 HR9s5 HR9s6 HR9thr Hbelow
              with "Hcg Hcnt Htext Hpc Hptree [Hown] Henv").
    { rewrite /uu_um. destruct df; [cbn [um_del_run] |]; iExact "Hown". }
    iIntros (CIDr6 Hsr6 mj) "%Hjsp %Hjthr Hcg Hcnt Hpc Hpt".
    (* --- +0x76 c.ldsp s1,40(sp) --- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmunmap + 0x76)) (mword_of_int 5 : mword 6) Rs1
              mj (K - 8) (mm !!! Regidx Rs1) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi76 [Hk3]").
    { iEval (rewrite Hjsp Hb3). iExact "Hk3". }
    iIntros (CIDr7 Hsr7) "Hcg Hpc Hk3". iEval (rewrite Hjsp Hb3) in "Hk3".
    set (F1 := <[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> mj).
    assert (HF1sp : F1 !!! Regidx csp_rs1 = spr) by lkp.
    assert (HF1thr1 : uu_thr1 mm F1).
    { intros c Hc H2 H8 H18 H19 H20 H21 H22.
      destruct (decide (c = Rs1)) as [-> | H9].
      - rewrite /F1 upd_eq. reflexivity.
      - rewrite /F1. rewrite upd_ne;
          [| intros Hxx; injection Hxx as Hxx2; apply H9; exact Hxx2].
        apply Hjthr; assumption. }
    assert (Hq78 : add_vec_int (mword_of_int (KernelSyms.uvmunmap + 0x76) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmunmap + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq78) in "Hpc".
    iApply (uu_epilogue mm F1 K sp0 b p ltac:(lia) Hspm HF1sp HF1thr1
              with "Hcg Htext Hpc Hk1 Hk2 [Hk3] Hk4 Hk5 Hk6 Hk7 Hk8").
    { iExists (mm !!! Regidx Rs1). iExact "Hk3". }
    iIntros (CIDr8 Hsr8 mf) "Hcg Hpc %Hcs".
    iDestruct (cpu_own_transport CIDr6 CIDr8 ilvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CIDr8 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! mf with "Hcg Hcnt Hpc [%] Hpt").
    exact Hcs.
  Qed.

End ProofUvmunmap.

End UvmunmapCore.

(* ===================================================================== *)
(* THE SEALS.  One proof; each [Module Type] pins [fx] to one literal.   *)
(* ===================================================================== *)

(* The USER-run seals' side condition, derived from the range premise they
   already carry: every vpn a run below the trapframe clears is a user vpn.
   This derivation used to live INSIDE the loop body, which is precisely
   what pinned uvmunmap to user runs; hoisting it here is what lets the
   same loop clear a fixed leaf for a caller that can say so. *)
(* the range relaxation, as a CLOSED [Z] fact.  Inline [lia] fails here with
   "Cannot find witness": the seal's context is mword-laden and the zify hook
   tries to decompose the bitvector terms (durable-notes). *)
Lemma uu_range_wide_Z (a : Z) : (a <= 2 ^ 38 - 8192)%Z -> (a <= 2 ^ 38)%Z.
Proof. lia. Qed.

Lemma uu_range_wide (va : mword 64) (npages : nat) :
  (uint va + Z.of_nat npages * 4096 <= uvm_maxsz)%Z ->
  (uint va + Z.of_nat npages * 4096 <= 2 ^ 38)%Z.
Proof. rewrite /uvm_maxsz. apply uu_range_wide_Z. Qed.

(* [ProcPt.vpn_at_0], reproved here rather than importing ProcPt (the
   CONSTRUCTION side) into a teardown proof. *)
Lemma uu_vpn_at_0 (v : mword 27) : vpn_at v 0 = v.
Proof. apply bv_eq. apply vpn_at_0_bv. Qed.

Lemma uu_side_user (va : mword 64) (npages : nat) :
  (bv_unsigned va + Z.of_nat npages * 4096 <= 274877898752)%Z ->
  forall k : nat, (k < npages)%nat -> uu_vpn_ok true (vpn_at (svpn_of va) k).
Proof.
  intros Hrange k Hk. rewrite /uu_vpn_ok.
  pose proof (bv_unsigned_in_range 64 va) as [Hva0 _].
  assert (Hdnp : (Z.of_nat k + 1 <= Z.of_nat npages)%Z) by lia.
  destruct (z_run_iter (bv_unsigned va) (Z.of_nat k) (Z.of_nat npages)
              Hva0 (Nat2Z.is_nonneg k) Hdnp Hrange) as (Hcnn & Hc38 & Hc64 & Hcvpn).
  assert (Hcuru : bv_unsigned (add_vec va (mword_of_int (4096 * Z.of_nat k)))
                  = bv_unsigned va + 4096 * Z.of_nat k)
    by (apply pb_va_k_unsigned; exact Hc64).
  assert (Hvpne : svpn_of (add_vec va (mword_of_int (4096 * Z.of_nat k)))
                  = vpn_at (svpn_of va) k)
    by (apply svpn_of_run; exact Hc38).
  assert (Hvpnu : bv_unsigned (vpn_at (svpn_of va) k)
                  = (bv_unsigned va + 4096 * Z.of_nat k) / 4096).
  { rewrite <- Hvpne.
    rewrite (svpn_of_unsigned_lo (add_vec va (mword_of_int (4096 * Z.of_nat k)))
               ltac:(rewrite uint_unsigned; rewrite Hcuru; exact Hc38)).
    rewrite uint_unsigned. rewrite Hcuru.
    rewrite Z.shiftr_div_pow2; [reflexivity | lia]. }
  rewrite Hvpnu.
  replace (bv_unsigned tf_vpn) with 67108862 by (vm_compute; reflexivity).
  exact Hcvpn.
Qed.

Module UvmunmapProof (WalkNoalloc : WALK_NOALLOC) (Kfree : KFREE) : UVMUNMAP.

Module Core := UvmunmapCore WalkNoalloc Kfree.

Section SealUvmunmap.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [proc_pt] IS the [upt_fixed_both] instance; the round trip owes [uptg] the two
     conjuncts it does not carry -- [upt_acc_wf] (preserved along the run
     by [upt_acc_wf_del_run]) and the trapframe page's [page_valid], which
     the loop never touches. *)
  Lemma wp_uvmunmap_sconf
      (γa : gname) (mm : regfile)
      (P : uptd) (npages : nat) (K : nat) (eb : bool) (p : mword 64)
      (ilvl : nat) (b : bool) (lks : gset string)
    : wp_uvmunmap_sconf_body γa mm P npages K eb p ilvl b lks.
  Proof.
    cbv beta delta [wp_uvmunmap_sconf_body].
    intros pcE va vpn0 ret_tgt HK Hilvl Hroot Hval Hnpr Hdf Hrange Hbelow.
    iIntros "Hcg Hcnt #Htext Hpc Hpt Henv Hcont".
    assert (Hrz : (bv_unsigned va + Z.of_nat npages * 4096 <= 274877898752)%Z).
    { unfold uvm_maxsz in Hrange. rewrite uint_unsigned in Hrange.
      change (2 ^ 38 - 8192)%Z with 274877898752%Z in Hrange. exact Hrange. }
    iDestruct (proc_pt_wf_get P with "Hpt") as %Hwf.
    destruct Hwf as (_ & Hacc & _ & _ & Htfv).
    iDestruct (proc_pt_uptg P with "Hpt") as "Hpt".
    iApply (Core.wp_uvmunmap_gen γa mm (upt_fixed_both P.(ud_tfp)) P.(ud_root)
              P.(ud_um) npages K eb p ilvl b true lks HK Hilvl Hroot Hval Hnpr Hdf
              (uu_range_wide va npages Hrange) (uu_side_user va npages Hrz) Hbelow
              with "Hcg Hcnt Htext Hpc Hpt Henv").
    iIntros (CID1 Hs1 mr) "Hcg Hcnt Hpc %Hcs Hpt".
    iSpecialize ("Hcont" $! CID1 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! mr with "Hcg Hcnt Hpc [%] [Hpt]").
    { exact Hcs. }
    iApply (uptg_proc_pt (uptd_del_run P vpn0 npages)
              (upt_acc_wf_del_run P.(ud_um) vpn0 npages Hacc) Htfv).
    iExact "Hpt".
  Qed.

End SealUvmunmap.

End UvmunmapProof.

Module UvmunmapBareProof (WalkNoalloc : WALK_NOALLOC) (Kfree : KFREE)
  : UVMUNMAP_BARE.

Module Core := UvmunmapCore WalkNoalloc Kfree.

Section SealUvmunmapBare.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [bare_pt] IS the [∅] instance, definitionally -- there is nothing
     to owe. *)
  Lemma wp_uvmunmap_bare_sconf
      (γa : gname) (mm : regfile)
      (uroot : mword 44) (um : gmap (mword 27) (mword 64))
      (npages : nat) (K : nat) (eb : bool) (p : mword 64)
      (ilvl : nat) (b : bool) (lks : gset string)
    : wp_uvmunmap_bare_sconf_body γa mm uroot um npages K eb p ilvl b lks.
  Proof.
    cbv beta delta [wp_uvmunmap_bare_sconf_body].
    intros pcE va vpn0 ret_tgt HK Hilvl Hroot Hval Hnpr Hdf Hrange Hbelow.
    iIntros "Hcg Hcnt #Htext Hpc Hpt Henv Hcont".
    assert (Hrz : (bv_unsigned va + Z.of_nat npages * 4096 <= 274877898752)%Z).
    { unfold uvm_maxsz in Hrange. rewrite uint_unsigned in Hrange.
      change (2 ^ 38 - 8192)%Z with 274877898752%Z in Hrange. exact Hrange. }
    iEval (rewrite /bare_pt) in "Hpt".
    iApply (Core.wp_uvmunmap_gen γa mm ∅ uroot um npages K eb p ilvl b true lks
              HK Hilvl Hroot Hval Hnpr Hdf
              (uu_range_wide va npages Hrange) (uu_side_user va npages Hrz) Hbelow
              with "Hcg Hcnt Htext Hpc Hpt Henv").
    iIntros (CID1 Hs1 mr) "Hcg Hcnt Hpc %Hcs Hpt".
    iSpecialize ("Hcont" $! CID1 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! mr with "Hcg Hcnt Hpc [%] [Hpt]").
    { exact Hcs. }
    rewrite /bare_pt. iExact "Hpt".
  Qed.

End SealUvmunmapBare.

End UvmunmapBareProof.

(* --------------------------------------------------------------------- *)
(* THE THIRD SEAL: the fixed-leaf unmap.  Same code, same proof, [df] at  *)
(* [false] -- so the [beq s5,zero] at +0x66 is TAKEN, the PTE2PA/kfree    *)
(* block is skipped, and the deletion lands on [fx] instead of [um].      *)
(* --------------------------------------------------------------------- *)

Module UvmunmapFixedProof (WalkNoalloc : WALK_NOALLOC) (Kfree : KFREE)
  : UVMUNMAP_FIXED.

Module Core := UvmunmapCore WalkNoalloc Kfree.

Section SealUvmunmapFixed.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_uvmunmap_fixed_sconf
      (γa : gname) (mm : regfile)
      (fx : gmap (mword 27) (mword 64)) (uroot : mword 44)
      (um : gmap (mword 27) (mword 64)) (v : mword 27)
      (K : nat) (eb : bool) (p : mword 64)
      (ilvl : nat) (b : bool) (lks : gset string)
    : wp_uvmunmap_fixed_sconf_body γa mm fx uroot um v K eb p ilvl b lks.
  Proof.
    cbv beta delta [wp_uvmunmap_fixed_sconf_body].
    intros pcE va ret_tgt HK Hilvl Hroot Hval Hnpr Hdf Hv Hfixed Hrange.
    iIntros "Hcg Hcnt #Htext Hpc Hpt Henv Hcont".
    (* the run is ONE page, so the only vpn it clears is [svpn_of va] itself
       ([vpn_at _ 0]), which the caller has named as a fixed leaf. *)
    assert (Hside : forall k : nat, (k < 1)%nat ->
                      uu_vpn_ok false (vpn_at (svpn_of va) k)).
    { intros k Hk. assert (Hk0 : k = 0%nat) by lia. rewrite Hk0 uu_vpn_at_0.
      rewrite /uu_vpn_ok Hv. exact Hfixed. }
    iApply (Core.wp_uvmunmap_gen γa mm fx uroot um 1%nat K eb p ilvl b false lks
              HK Hilvl Hroot Hval
              ltac:(rewrite Hnpr; reflexivity) Hdf Hrange Hside I
              with "Hcg Hcnt Htext Hpc Hpt Henv").
    iIntros (CID1 Hs1 mr) "Hcg Hcnt Hpc %Hcs Hpt".
    iSpecialize ("Hcont" $! CID1 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! mr with "Hcg Hcnt Hpc [%] [Hpt]").
    { exact Hcs. }
    (* [uu_fx false fx vpn0 1] is [delete (vpn_at vpn0 0) fx]; [uu_um false]
       is [um] untouched. *)
    rewrite /uu_fx /uu_um. cbn [um_del_run]. rewrite uu_vpn_at_0 Hv.
    iExact "Hpt".
  Qed.

End SealUvmunmapFixed.

End UvmunmapFixedProof.
