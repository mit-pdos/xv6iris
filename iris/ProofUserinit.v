(* ProofUserinit.v -- the whole-function WP for xv6's userinit(), against
   [SpecUserinit.wp_userinit_sconf_body].

     void userinit(void) {
       struct proc *p = allocproc();
       initproc = p;
       p->cwd = namei("/");
       p->state = RUNNABLE;
       release(&p->lock);
     }

   ---- THE CODE, READ OFF CodeUserinit.v ----------------------------------

     +0x00            c.addi16sp sp,-32          (4-slot frame)
     +0x02 .. +0x06   c.sdsp ra,24 / s0,16 / s1,8
     +0x08            c.addi4spn s0,sp,32
     +0x0a            jal ra,allocproc           (0x80001b06)
     +0x0e            c.mv s1,a0                 s1 = p
     +0x10 .. +0x14   auipc a5,0x8; sd a0,1796(a5)     initproc = p
     +0x18 .. +0x1c   auipc a0,0x5; addi a0,a0,1484    a0 = "/" (0x80007190)
     +0x20            jal ra,namei               (0x80003a82)
     +0x24            sd a0,336(s1)              p->cwd = ip
     +0x28            c.li a5,3                  RUNNABLE
     +0x2a            c.sw a5,24(s1)             p->state = RUNNABLE
     +0x2c            c.mv a0,s1
     +0x2e            jal ra,release             (0x80000c42)
     +0x32 .. +0x36   c.ldsp ra / s0 / s1
     +0x38            c.addi16sp sp,32
     +0x3a            c.jr ra

   Every [jal] target was resolved numerically against KernelSyms; so was
   [initproc] (0x8000a2b0, the auipc/sd pair) and the "/" literal
   (0x80007190, the auipc/addi pair).  THIS KERNEL'S userinit is SHORTER
   than upstream's -- no uvmfirst, no trapframe writes, no safestrcpy --
   and the decode is what says so: three calls, two stores, nothing else.

   ---- THE THREE THINGS THIS PROOF IS ABOUT --------------------------------

   1. THE RESULT OF [allocproc] IS NOT TESTED.  +0x24 stores through it
      unconditionally, so two of [SpecAllocproc.allocproc_post]'s three arms
      have to be REFUTED, not handled, and the counted regimes are what does
      it: [ProcAvail.procs_avail (Some (S np))] makes [avail_zero] false on
      the empty-table arm, and [K_allocproc < nb] makes it false on the
      freeproc-tail arm.  Both refutations are one [lia]
      (claude-notes/kernel-defects.md, "UNREACHABLE, BY THE CALLER'S
      POSITION").

   2. [namei("/")] RUNS WITH p->lock HELD, BEFORE THE FILE SYSTEM EXISTS.
      It is called at namei's ROOT CORNER, at the BOOT client's premises
      ([SpecNameiRootBoot.NAMEI_ROOT_BOOT], the tree's one assumed contract
      in this cone): no [log_op], no running process, no
      [FsReady.fs_ready], no [ireg_open] -- which could not exist here
      anyway -- and not even the four persistent inode-cache rows, which is
      the whole of what that file assumes over the PROVEN corner.  The lock
      order is the only thing the held [p->lock] costs: "proc" (9) <
      "itable" (14), so [locks_below lks "proc"] gives the corner's own
      premise by [LockRank.locks_below_mono].

   3. THE RELEASE IS A PARK AT RUNNABLE, which is [ProofKforkB5.v]'s move
      with one crossing instead of three: [FORKRET_PARK] turns allocproc's
      raw saved context into [SchedCtx.proc_ctx], the whole state mirror
      moves USED -> RUNNABLE under the held lock ([ProcGeom.pstate_whole_
      update], no side condition), and [SchedCtx.proc_lock_res_intro]
      rebuilds the invariant the [release] gives back.

   The [iref_slots (1 + IREFSPARE)] allocproc hands over is split exactly
   where the design says it is: the [1] is the working directory's unit and
   it pays for the root's [iget] here, precisely as it pays for [idup] in
   kfork; [IREFSPARE] goes into the park. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelDataInv.
Require Import LockRank.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import WireInv.   (* [wire_inv] *)
Require Import CpuOwn.
Require Import LockRank.
Require Import KallocInv.
Require Import KvmSpec.   (* [kalloc_env], [kalloc_env_seal] *)
Require Import FsCfg.     (* [fsc_kalloc] *)
Require Import FirstTok.  (* [first_tok_boot] -- the deposit *)
Require Import FdSlots.
Require Import IrefSlots.
Require Import WpUart.
Require Import DirentEnc PathElems.
Require Import ProcGeom.
Require Import ProcDefs.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SchedCtx.
Require Import ProcAvail.
Require Import SpecAllocproc.
Require Import SpecNameiRootBoot.
Require Import SpecRelease.
Require Import SpecForkretPark.
Require Import SpecUserinit.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import CodeUserinit.
From Kernel Require KernelSyms.
From Kernel Require KernelData.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.

Set Printing Depth 40.

Notation UI := KernelSyms.userinit (only parsing).

(* ===================================================================== *)
(*  PURE FACTS: the frame, the two computed addresses, the budget.        *)
(* ===================================================================== *)

(* the three registers this frame saves, plus sp -- i.e. what a callee's
   [callee_saved] must be transported across but userinit itself rewrites *)
Definition uin_thr (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> (mword_of_int 8 : mword 5) ->
    c <> (mword_of_int 9 : mword 5) ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Definition uin_sp (m M : regfile) : Prop :=
  M !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4.

Lemma uin_frm (X : mword 64) (u : mword 6) (k : nat) :
  (mword_of_int (wrap64 (uint (mword_of_int (- (8 * Z.of_nat 4)) : mword 64)
                         + uint (zero_extend' 64 (concat_vec u ('b"000")) : mword 64)))
   : mword 64)
  = mword_of_int (- (8 * Z.of_nat k)) ->
  add_vec (pa_stk X 4) (zero_extend' 64 (concat_vec u ('b"000"))) = pa_stk X k.
Proof.
  intro H. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
  apply f_equal. exact H.
Qed.

Lemma uin_frm1 (X : mword 64) :
  add_vec (pa_stk X 4) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
  = pa_stk X 1.
Proof. apply uin_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma uin_frm2 (X : mword 64) :
  add_vec (pa_stk X 4) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
  = pa_stk X 2.
Proof. apply uin_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma uin_frm3 (X : mword 64) :
  add_vec (pa_stk X 4) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
  = pa_stk X 3.
Proof. apply uin_frm. apply bv_eq; vm_compute; reflexivity. Qed.

(* THE "/" LITERAL.  Two bytes of .rodata at 0x80007190, which is what the
   [auipc a0,0x5] / [addi a0,a0,1484] pair at +0x18/+0x1c computes.  Named
   (never an inline [ltac:] argument to [kernel_data_window] --
   claude-notes/optimization.md). *)
Definition uin_slash_addr : Z := 0x80007190.
Definition uin_slash_w : mword 16 := mword_of_int 0x2f.

Lemma uin_slash_bytes : forall j : nat, (j < 2)%nat ->
  KernelData.kernel_data !! (uin_slash_addr + Z.of_nat j)%Z
  = Some (nth_byte uin_slash_w j).
Proof.
  intros j Hj.
  destruct j as [|[|j]];
    [ vm_compute; reflexivity | vm_compute; reflexivity | lia ].
Qed.

Lemma uin_slash_b0 : nth_byte uin_slash_w 0 = PathElems.SLASH.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma uin_slash_b1 : nth_byte uin_slash_w 1 = DirentEnc.NUL.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* K_userinit's single premise, in the forms the three calls and the
   two [sie_cap_gpr] carves want. *)
Lemma uin_kb (K : nat) : (K_userinit <= K)%nat ->
  (48 <= K - 4)%nat /\ (K_namei_root_boot <= K - 4)%nat /\ (10 <= K - 4)%nat
  /\ (4 <= K)%nat /\ ((K - 4) + 4 = K)%nat.
Proof. intro H. split_and!; lia. Qed.

(* [pstate_whole] at RUNNABLE, split into what the LOCK keeps: RUNNABLE is
   unclaimed, so the claimant's half is [emp] and the lock takes the whole
   variable back.  [ProofKforkB5.kfkb5_pwhole_used] is the same move at the
   claimed state. *)
Section PstateRunnableHelper.
  Context `{!riscvGS Σ}.
  Lemma uin_pwhole_runnable (pa : mword 64) :
    pstate_whole pa RUNNABLE ⊣⊢ pstate_lock pa RUNNABLE.
  Proof.
    rewrite pstate_whole_split unclaimed_RUNNABLE. apply bi.sep_emp.
  Qed.
End PstateRunnableHelper.

(* ===================================================================== *)

Module UserinitProof (AP : ALLOCPROC) (NR : NAMEI_ROOT_BOOT)
                     (RL : RELEASE) (FP : FORKRET_PARK) : USERINIT.

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.
Local Ltac namidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

Section ProofUserinit.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Local Ltac regne := reg_ne_side.

  (* THE FTABLE'S GNAME IS NOT PICKED HERE ANY MORE: it is the [γf] of the
     [is_ftable γft γf] the contract takes, because the block this park
     hands over ends up inside the first process's trap-loop environment
     ([UsertrapRes.ut_own_nopt] names the table's gname), and that
     environment's file-table row must be the one main built. *)
  Lemma wp_userinit_sconf
      (γp : gname) (γs : list gname)
      (γft γf γw γtl : gname) (pd pav pu : mword 64)
      (m : regfile) (K : nat) (eb : bool) (pj : mword 64)
      (on : option nat) (np : nat) (v0 : mword 64)
      (b : bool) (lks : gset string)
    : wp_userinit_sconf_body γp γs γft γf γw γtl pd pav pu m K eb pj on np v0 b lks.
  Proof.
    cbv beta delta [wp_userinit_sconf_body].
    intros pcE ret_tgt HK Hnb Hdev Hnib Hbelow.
    destruct (uin_kb K HK) as (Kap & Knm & Krl & K4 & Kpop).
    (* the four inode-cache rows are PERSISTENT and are relayed unchanged to
       namei's root corner at +0x20 (fs-cfg-boot.md stage (e)); nothing else
       in userinit's body names them. *)
    iIntros "Hcg Hcpu #Htext #Hkd Hpc #Hpenv #Hitl #Hitinv #Hesc #Hireg
             Hfirst #Hpersist Hfsinit
             #Hpinv #Hlpid
             #Hdcaps #Hwaitlk #Hftable #Hcready #Hwire #Htramp
             Hkenv Hpav Hinitproc Hcont".
    (* the boot arm: at nesting level 0 the exit arm IS the entry base *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcpu") as %Heb. cbn in Heb. subst eb.
    (* the two path bytes, out of the read-only image *)
    iPoseProof (kernel_data_window (wd := 16) uin_slash_addr uin_slash_w 2
                  (mword_of_int uin_slash_addr : mword 64) eq_refl
                  ltac:(unfold uin_slash_addr, text_end; lia)
                  (* the literal is .rodata, well under [rodata_end] -- the
                     upper bound [kernel_data] gained when it stopped
                     claiming the image's writable .data *)
                  ltac:(unfold uin_slash_addr, rodata_end; lia)
                  uin_slash_bytes with "Hkd") as "Hsl".
    iEval (cbn [seq]; rewrite !big_sepL_cons) in "Hsl".
    iDestruct "Hsl" as "(Hp0 & Hp1 & _)".
    iEval (rewrite uin_slash_b0) in "Hp0".
    iEval (rewrite uin_slash_b1) in "Hp1".
    (* the decode *)
    iPoseProof (uin_00 with "Htext") as "Hi00".
    iPoseProof (uin_02 with "Htext") as "Hi02".
    iPoseProof (uin_04 with "Htext") as "Hi04".
    iPoseProof (uin_06 with "Htext") as "Hi06".
    iPoseProof (uin_08 with "Htext") as "Hi08".
    iPoseProof (uin_0a with "Htext") as "Hi0a".
    iPoseProof (uin_0e with "Htext") as "Hi0e".
    iPoseProof (uin_10 with "Htext") as "Hi10".
    iPoseProof (uin_14 with "Htext") as "Hi14".
    iPoseProof (uin_18 with "Htext") as "Hi18".
    iPoseProof (uin_1c with "Htext") as "Hi1c".
    iPoseProof (uin_20 with "Htext") as "Hi20".
    iPoseProof (uin_24 with "Htext") as "Hi24".
    iPoseProof (uin_28 with "Htext") as "Hi28".
    iPoseProof (uin_2a with "Htext") as "Hi2a".
    iPoseProof (uin_2c with "Htext") as "Hi2c".
    iPoseProof (uin_2e with "Htext") as "Hi2e".
    iPoseProof (uin_32 with "Htext") as "Hi32".
    iPoseProof (uin_34 with "Htext") as "Hi34".
    iPoseProof (uin_36 with "Htext") as "Hi36".
    iPoseProof (uin_38 with "Htext") as "Hi38".
    iPoseProof (uin_3a with "Htext") as "Hi3a".
    (* ===== +0x00 c.addi16sp sp,-32 : the four-slot frame ===== *)
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    assert (Hspm : (m !!! Regidx csp_rs1 : mword 64) = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4) by apply stk_push_32.
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m K 4 b
              K4 Hpush with "Hcg Hpc Hi00").
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HR1sp : uin_sp m R1) by (rewrite /uin_sp /R1 upd_eq; exact Hpush).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (w1) "Hf1". iDestruct "S2" as (w2) "Hf2".
    iDestruct "S3" as (w3) "Hf3". iDestruct "S4" as (w4) "Hf4".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 1)
      by (rewrite HR1sp; apply uin_frm1).
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk sp0 2)
      by (rewrite HR1sp; apply uin_frm2).
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk sp0 3)
      by (rewrite HR1sp; apply uin_frm3).
    iEval (rewrite -Hb1) in "Hf1". iEval (rewrite -Hb2) in "Hf2".
    iEval (rewrite -Hb3) in "Hf3".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2
                    = mword_of_int (UI + 0x02)) by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    (* ===== +0x02 c.sdsp ra,24(sp) ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (UI + 0x02))
              (mword_of_int 3 : mword 6) Rra R1 (K - 4)%nat w1 b
              with "Hcg Hpc Hi02 Hf1").
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    assert (Hpp04 : add_vec_int (mword_of_int (UI + 0x02) : mword 64) 2
                    = mword_of_int (UI + 0x04)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    (* ===== +0x04 c.sdsp s0,16(sp) ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (UI + 0x04))
              (mword_of_int 2 : mword 6) Rs0 R1 (K - 4)%nat w2 b
              with "Hcg Hpc Hi04 Hf2").
    iIntros (CID3 Hq3) "Hcg Hpc Hf2".
    assert (Hpp06 : add_vec_int (mword_of_int (UI + 0x04) : mword 64) 2
                    = mword_of_int (UI + 0x06)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    (* ===== +0x06 c.sdsp s1,8(sp) ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (UI + 0x06))
              (mword_of_int 1 : mword 6) Rs1 R1 (K - 4)%nat w3 b
              with "Hcg Hpc Hi06 Hf3").
    iIntros (CID4 Hq4) "Hcg Hpc Hf3".
    assert (Hpp08 : add_vec_int (mword_of_int (UI + 0x06) : mword 64) 2
                    = mword_of_int (UI + 0x08)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    assert (HR1ra : (R1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s0 : (R1 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s1 : (R1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    iEval (rewrite Hb1; rgne; rewrite HR1ra) in "Hf1".
    iEval (rewrite Hb2; rgne; rewrite HR1s0) in "Hf2".
    iEval (rewrite Hb3; rgne; rewrite HR1s1) in "Hf3".
    (* ===== +0x08 c.addi4spn s0,sp,32 ===== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (UI + 0x08))
              (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) Rs0
              R1 (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (HR2sp : uin_sp m R2)
      by (rewrite /uin_sp /R2 upd_ne; [exact HR1sp | nz]).
    assert (HR2ra : (R2 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /R2 upd_ne; [exact HR1ra | nz]).
    assert (HR2thr : uin_thr m R2).
    { intros c Hcs N2 N8 N9.
      rewrite /R2 upd_ne; [| regne]. rewrite /R1 upd_ne; [reflexivity | regne]. }
    assert (Hpp0a : add_vec_int (mword_of_int (UI + 0x08) : mword 64) 2
                    = mword_of_int (UI + 0x0a)) by pcw.
    iEval (rewrite Hpp0a) in "Hpc".
    (* ===================================================================== *)
    (* +0x0a jal ra,allocproc                                                *)
    (* ===================================================================== *)
    iApply (wp_jal_s_sconf (mword_of_int (UI + 0x0a)) Rra
              (mword_of_int 2096976 : mword 21) R2 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0a").
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (R3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (UI + 0x0a) : mword 64) 4)]> R2).
    assert (Htgtap : add_vec (mword_of_int (UI + 0x0a) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096976 : mword 21))
                     = mword_of_int KernelSyms.allocproc) by pcw.
    iEval (rewrite Htgtap) in "Hpc".
    assert (HR3ra : (R3 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (UI + 0x0a) : mword 64) 4)
      by (rewrite /R3; apply upd_eq).
    assert (HR3sp : uin_sp m R3)
      by (rewrite /uin_sp /R3 upd_ne; [exact HR2sp | nz]).
    assert (HR3thr : uin_thr m R3).
    { intros c Hcs N2 N8 N9. rewrite /R3 upd_ne; [| regne].
      exact (HR2thr c Hcs N2 N8 N9). }
    iDestruct (cpu_own_transport CID CID6 0%nat b pj b
                 ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iDestruct (wp_next_shift (b := b) (CIDa := CID) (CIDb := CID6)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (AP.wp_allocproc_sconf fsc_kalloc fsc_kpages γp γf γs R3 0%nat (K - 4)%nat b pj
              on (Some (S np)) b lks
              Kap ltac:(lia) Hnb Hbelow
              with "Hcg Hcpu Htext Hpc Hpinv Hlpid Hkenv Hpav").
    iIntros (CID7 Hq7 mr1) "%Hcsap Hpc Hpost".
    assert (Hpc0e : ret_pc (R3 !!! Regidx Rra : mword 64)
                    = mword_of_int (UI + 0x0e)) by (rewrite HR3ra; pcw).
    iEval (rewrite Hpc0e) in "Hpc".
    (* ---- the two impossible arms ---- *)
    rewrite /allocproc_post.
    iDestruct "Hpost" as "[Hnull | [Hgot | Hfail]]".
    { iDestruct "Hnull" as "(_ & %Hz & _)".
      unfold avail_zero in Hz. exfalso. lia. }
    2:{ iDestruct "Hfail" as "(_ & %Hz & _)".
        destruct Hz as (nz0 & Hnz0 & Hz0).
        destruct Hnb as (nb & Hon & Hnbgt). subst on.
        rewrite avail_sub_Some in Hz0. unfold avail_zero in Hz0.
        exfalso. lia. }
    iDestruct "Hgot" as (j γl ch pid V root tfp ks rest nc)
      "(%Hfacts & Hheld & Hhart & Hpriv & #Hmk & Hfd & Hirs & Hbsl & Hks & Hkfree
        & Hctx & Hcg & Hcpu & Hpay & Hkenv & Hpav)".
    destruct Hfacts as (Hrv & Hj & Hgl & _ & _ & Hcwd0 & Hrest & Hnc).
    iClear "Hkfree".
    (* ===== +0x0e c.mv s1,a0 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (UI + 0x0e)) Rs1 Ra0 mr1
              (trap_res b + (K - 4))%nat false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi0e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (R4 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mr1 !!! Regidx Ra0))]> mr1).
    assert (HR4s1 : (R4 !!! Regidx Rs1 : mword 64) = proc_addr j).
    { rewrite /R4 upd_eq. rewrite Hrv. apply add_vec_zero_l. }
    assert (HR4a0 : (R4 !!! Regidx Ra0 : mword 64) = proc_addr j)
      by (rewrite /R4 upd_ne; [rewrite Hrv; reflexivity | nz]).
    assert (Hpp10 : add_vec_int (mword_of_int (UI + 0x0e) : mword 64) 2
                    = mword_of_int (UI + 0x10)) by pcw.
    iEval (rewrite Hpp10) in "Hpc".
    (* ===== +0x10 auipc a5,0x8 ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (UI + 0x10)) Ra5
              (mword_of_int 8 : mword 20) R4 (trap_res b + (K - 4))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi10").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (R5 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (mword_of_int (UI + 0x10) : mword 64)
                     (auipc_off (mword_of_int 8 : mword 20)))]> R4).
    assert (HR5s1 : (R5 !!! Regidx Rs1 : mword 64) = proc_addr j)
      by (rewrite /R5 upd_ne; [exact HR4s1 | nz]).
    assert (HR5a0 : (R5 !!! Regidx Ra0 : mword 64) = proc_addr j)
      by (rewrite /R5 upd_ne; [exact HR4a0 | nz]).
    assert (Hpp14 : add_vec_int (mword_of_int (UI + 0x10) : mword 64) 4
                    = mword_of_int (UI + 0x14)) by pcw.
    iEval (rewrite Hpp14) in "Hpc".
    (* ===== +0x14 sd a0,1796(a5) : initproc = p ===== *)
    assert (Hinitaddr : add_vec (rget R5 Ra5)
                          (sign_extend' 64 (mword_of_int 1780 : mword 12))
                        = (mword_of_int KernelSyms.initproc : mword 64)).
    { assert (Hr : rget R5 Ra5 = R5 !!! Regidx Ra5) by (rgne; reflexivity).
      rewrite Hr /R5 upd_eq. pcw. }
    iApply (wp_sd_s_sconf (kt := KT1) (ktd := KT0)
              (mword_of_int (UI + 0x14)) Ra0 Ra5 (mword_of_int 1780 : mword 12)
              R5 (trap_res b + (K - 4))%nat v0 false
              with "Hcg Hpc Hi14 [Hinitproc]").
    { iEval (rewrite Hinitaddr). iExact "Hinitproc". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hinitproc".
    iEval (rewrite Hinitaddr) in "Hinitproc".
    (* THE ONLY STORE THIS CELL EVER GETS HAS NOW HAPPENED, so discard the
       fraction immediately.  Not on the way out: the [forkret_park] deposit
       site below (D1) is where a fresh process's trap-loop residue will need
       [initproc ↦₈{un_dqi N} (un_ip N)], and a persistent fact is in scope
       there for free, whereas an exclusive one would have to be carried past
       the park and could not be shared with the parked process at all.
       See [iris/ForkretParkClose.v] and projects/forkret-park.md. *)
    iMod (word_pointsto_persist with "Hinitproc") as "#Hinitproc".
    assert (Hpp18 : add_vec_int (mword_of_int (UI + 0x14) : mword 64) 4
                    = mword_of_int (UI + 0x18)) by pcw.
    iEval (rewrite Hpp18) in "Hpc".
    (* ===== +0x18 auipc a0,0x5 ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (UI + 0x18)) Ra0
              (mword_of_int 5 : mword 20) R5 (trap_res b + (K - 4))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi18").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (R6 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (UI + 0x18) : mword 64)
                     (auipc_off (mword_of_int 5 : mword 20)))]> R5).
    assert (HR6s1 : (R6 !!! Regidx Rs1 : mword 64) = proc_addr j)
      by (rewrite /R6 upd_ne; [exact HR5s1 | nz]).
    assert (Hpp1c : add_vec_int (mword_of_int (UI + 0x18) : mword 64) 4
                    = mword_of_int (UI + 0x1c)) by pcw.
    iEval (rewrite Hpp1c) in "Hpc".
    (* ===== +0x1c addi a0,a0,1484 : a0 = "/" ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (UI + 0x1c)) Ra0 Ra0
              (mword_of_int 1484 : mword 12) R6 (trap_res b + (K - 4))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (R7 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (rget R6 Ra0)
                     (sign_extend' 64 (mword_of_int 1484 : mword 12)))]> R6).
    assert (HR7a0 : (R7 !!! Regidx Ra0 : mword 64)
                    = (mword_of_int uin_slash_addr : mword 64)).
    { rewrite /R7 upd_eq.
      assert (Hr : rget R6 Ra0 = R6 !!! Regidx Ra0) by (rgne; reflexivity).
      rewrite Hr /R6 upd_eq. unfold uin_slash_addr. pcw. }
    assert (HR7s1 : (R7 !!! Regidx Rs1 : mword 64) = proc_addr j)
      by (rewrite /R7 upd_ne; [exact HR6s1 | nz]).
    assert (Hpp20 : add_vec_int (mword_of_int (UI + 0x1c) : mword 64) 4
                    = mword_of_int (UI + 0x20)) by pcw.
    iEval (rewrite Hpp20) in "Hpc".
    (* ===================================================================== *)
    (* +0x20 jal ra,namei                                                    *)
    (* ===================================================================== *)
    iApply (wp_jal_s_sconf (mword_of_int (UI + 0x20)) Rra
              (mword_of_int 7862 : mword 21) R7 (trap_res b + (K - 4))%nat false
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi20").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (R8 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (UI + 0x20) : mword 64) 4)]> R7).
    assert (Htgtnm : add_vec (mword_of_int (UI + 0x20) : mword 64)
                       (sign_extend' 64 (mword_of_int 7862 : mword 21))
                     = mword_of_int KernelSyms.namei) by pcw.
    iEval (rewrite Htgtnm) in "Hpc".
    assert (HR8ra : (R8 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (UI + 0x20) : mword 64) 4)
      by (rewrite /R8; apply upd_eq).
    assert (HR8a0 : (R8 !!! Regidx Ra0 : mword 64)
                    = (mword_of_int uin_slash_addr : mword 64))
      by (rewrite /R8 upd_ne; [exact HR7a0 | nz]).
    assert (HR8s1 : (R8 !!! Regidx Rs1 : mword 64) = proc_addr j)
      by (rewrite /R8 upd_ne; [exact HR7s1 | nz]).
    (* the cwd's own iref unit, out of allocproc's allowance *)
    iDestruct (iref_slots_split 1 IREFSPARE with "Hirs") as "[Hisl Hirs]".
    (* the two path bytes at namei's own a0 *)
    iEval (rewrite -HR8a0) in "Hp0". iEval (rewrite -HR8a0) in "Hp1".
    iApply (NR.wp_namei_root_boot DfracDiscarded R8 1%nat
              (trap_res b + (K - 4))%nat b pj false ({["proc"]} ∪ lks)
              ltac:(lia) ltac:(lia) Hdev Hnib
              ltac:(apply locks_below_union_singleton;
                    [ vm_compute; lia
                    | apply (locks_below_mono lks "proc"%string "itable"%string
                               Hbelow); vm_compute; lia ])
              with "Hcg Hcpu Htext Hkd Hpc Hpenv Hitl Hitinv Hesc Hireg
                    Hisl Hp0 Hp1").
    iApply wp_next_off_intro.
    iIntros (mr2 ipv) "%Hcsnm Hcg Hcpu Hpc _ _ Hip".
    destruct Hcsnm as (Hcsnm & Hnma0).
    assert (Hpc24 : ret_pc (R8 !!! Regidx Rra : mword 64)
                    = mword_of_int (UI + 0x24)) by (rewrite HR8ra; pcw).
    iEval (rewrite Hpc24) in "Hpc".
    assert (Hmr2s1 : (mr2 !!! Regidx Rs1 : mword 64) = proc_addr j).
    { rewrite (callee_saved_lookup Hcsnm Rs1 ltac:(vm_compute; reflexivity)).
      exact HR8s1. }
    (* ===== +0x24 sd a0,336(s1) : p->cwd = ip ===== *)
    iDestruct (proc_priv_nocwd_cwd_pid γf (proc_addr j) pid V with "Hpriv")
      as "(Hcwd & Hpid4 & Hback)".
    assert (Hcwdaddr : add_vec (rget mr2 Rs1)
                         (sign_extend' 64 (mword_of_int 336 : mword 12))
                       = p_cwd (proc_addr j)).
    { assert (Hr : rget mr2 Rs1 = mr2 !!! Regidx Rs1) by (rgne; reflexivity).
      rewrite Hr Hmr2s1. apply p_cwd_sext. }
    iApply (wp_sd_s_sconf (kt := KT1) (ktd := KT0)
              (mword_of_int (UI + 0x24)) Ra0 Rs1 (mword_of_int 336 : mword 12)
              mr2 (trap_res b + (K - 4))%nat (pv_cwd V) false
              with "Hcg Hpc Hi24 [Hcwd]").
    { iEval (rewrite Hcwdaddr). iExact "Hcwd". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hcwd".
    assert (Hstored_cwd : rget mr2 Ra0 = ipv).
    { assert (Hr : rget mr2 Ra0 = mr2 !!! Regidx Ra0) by (rgne; reflexivity).
      rewrite Hr. exact Hnma0. }
    iEval (rewrite Hstored_cwd Hcwdaddr) in "Hcwd".
    iDestruct ("Hback" $! ipv with "Hcwd Hpid4") as "Hpnc".
    (* the reference namei's [iget] returned, in the shape the block wants *)
    iDestruct (cwd_ref_of_held ipv with "Hip") as "Hcref".
    (* THE BLOCK IS *NOT* CLOSED HERE any more.  Since [FirstTok.first_tok]
       became a conjunct of [proc_priv], closing it needs the token too, and
       the token's allocator row is minted by a ghost step -- so the three
       pieces meet at the park below, which is the first point in this proof
       where an [iMod] is available. *)
    assert (Hpp28 : add_vec_int (mword_of_int (UI + 0x24) : mword 64) 4
                    = mword_of_int (UI + 0x28)) by pcw.
    iEval (rewrite Hpp28) in "Hpc".
    (* ===== +0x28 c.li a5,3 ===== *)
    assert (Hwval3 : add_vec (zero_reg : mword 64)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 3 : mword 6)))
                     = (mword_of_int 3 : mword 64)) by pcw.
    iApply (wp_cli_s_sconf (mword_of_int (UI + 0x28)) Ra5
              (mword_of_int 3 : mword 6) (mword_of_int 3 : mword 64)
              mr2 (trap_res b + (K - 4))%nat false ltac:(nz) ltac:(rdok) Hwval3
              with "Hcg Hpc Hi28").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (R9 := <[Regidx Ra5 := regval_into_reg (mword_of_int 3 : mword 64)]> mr2).
    assert (HR9a5 : (R9 !!! Regidx Ra5 : mword 64) = (mword_of_int 3 : mword 64))
      by (rewrite /R9; apply upd_eq).
    assert (HR9s1 : (R9 !!! Regidx Rs1 : mword 64) = proc_addr j)
      by (rewrite /R9 upd_ne; [exact Hmr2s1 | nz]).
    assert (Hpp2a : add_vec_int (mword_of_int (UI + 0x28) : mword 64) 2
                    = mword_of_int (UI + 0x2a)) by pcw.
    iEval (rewrite Hpp2a) in "Hpc".
    (* ===== +0x2a c.sw a5,24(s1) : p->state = RUNNABLE ===== *)
    iDestruct "Hheld" as "(Htok & Hpstcell & Hpwhole & Hpchan & Hppub)".
    assert (Hstaddr : add_vec (rget R9 Rs1)
                        (sign_extend' 64 (mword_of_int 24 : mword 12))
                      = p_state (proc_addr j)).
    { assert (Hr : rget R9 Rs1 = R9 !!! Regidx Rs1) by (rgne; reflexivity).
      rewrite Hr HR9s1. apply p_state_sext. }
    iApply (wp_csw_s_sconf (kt := KT1) (ktd := KT0)
              (mword_of_int (UI + 0x2a)) Ra5 Rs1 (mword_of_int 24 : mword 12)
              R9 (trap_res b + (K - 4))%nat USED false
              with "Hcg Hpc Hi2a [Hpstcell]").
    { iEval (rewrite Hstaddr). iExact "Hpstcell". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hpstcell".
    assert (Hstored_st : trunc32 (rget R9 Ra5) = RUNNABLE).
    { assert (Hr : rget R9 Ra5 = R9 !!! Regidx Ra5) by (rgne; reflexivity).
      rewrite Hr HR9a5. rewrite /RUNNABLE. pcw. }
    iEval (rewrite Hstored_st Hstaddr) in "Hpstcell".
    assert (Hpp2c : add_vec_int (mword_of_int (UI + 0x2a) : mword 64) 2
                    = mword_of_int (UI + 0x2c)) by pcw.
    iEval (rewrite Hpp2c) in "Hpc".
    (* ---- THE PARK, at RUNNABLE ---- *)
    (* the two files each define [forkret_pc]; they are the same constant *)
    iEval (rewrite (_ : SpecAllocproc.forkret_pc = SpecForkretPark.forkret_pc);
           [| reflexivity]) in "Hctx".
    (* ================================================================= *)
    (* THE DEPOSIT SITE -- and it is a DEPOSIT now, not a drop.            *)
    (*                                                                    *)
    (* [FirstTok.first_tok] is a conjunct of [ProcInv.proc_priv], so the   *)
    (* token goes into the FIRST PROCESS'S BLOCK, which this park hands to *)
    (* the scheduler.  That is the whole route: forkret runs on the        *)
    (* context this park saves, forkret's [if (first)] arm is the token's  *)
    (* only consumer, and the block is what a parked process still owns.   *)
    (* No premise of [SpecForkretPark.forkret_park_body] had to grow --    *)
    (* the row rides inside the [proc_priv] that contract already takes.   *)
    (*                                                                    *)
    (* Three of the four rows were carried here across allocproc and namei *)
    (* untouched ([Hfirst], [Hpersist], [Hfsinit]); the fourth is minted   *)
    (* by the seal below.  That row is the NAMED half                      *)
    (* [kalloc_avail fsc_kpages None], not [kalloc_env]'s bundle: the seal *)
    (* is what [FsReady.fs_ready_pre] consumes and it spells the pair, so  *)
    (* the counted chain carries the name down to here                     *)
    (* ([KvmSpec.kalloc_env_at]; fs-cfg-boot.md debt F).                   *)
    (* ================================================================= *)
    (* ================================================================= *)
    (* THE SEAL.  allocproc's draw at +0x0a was the LAST counted kalloc in
       the whole boot -- nothing between here and the scheduler allocates --
       so the allocator's regime leaves the counted world for good here.
       [KallocInv.kalloc_avail_seal] is a one-shot and the result is
       PERSISTENT, which is why it can ride a token that a process carries
       and (at its steady arm) every later process copies. *)
    iMod (kalloc_env_at_seal with "Hkenv") as "#Hkenv".
    (* ...AND THE DEPOSIT.  All four rows of [FirstTok.first_tok]'s boot arm
       are in hand at this instant and nowhere else: the pinned
       [first_addr ↦₄ 1] cell, [first_boot_persist] (main's sixteen
       persistent rows) and [first_fsinit] (SpecFsinit's whole exclusive
       premise pile) were carried across allocproc and namei untouched, and
       the allocator row is what the [iMod] above just minted. *)
    (* [KvmSpec.kalloc_env_at] names the free-list pair, so the token's
       allocator row -- [kalloc_avail fsc_kpages None], the half
       [FsReady.fs_ready_pre] spells out -- is a projection off what
       allocproc handed back.  The bundle's [∃ γk] could never have been
       tied to [fsc_kpages] here; that is why the counted chain names it. *)
    iDestruct (kalloc_env_at_avail with "Hkenv") as "#Hkav".
    iDestruct (first_tok_boot with "Hfirst Hpersist Hkav Hfsinit")
      as "Hftok".
    iAssert (proc_priv γf (proc_addr j) pid (upd_cwd V ipv))
      with "[Hpnc Hcref Hftok]" as "Hpriv".
    { rewrite proc_priv_split_cwd. iFrame "Hpnc".
      iSplitL "Hcref"; [cbn [upd_cwd pv_cwd]; iExact "Hcref" |].
      iExact "Hftok". }
    (* ...AND THE SLOT LEDGER'S SEAL, beside the allocator's.  allocproc's
       draw at +0x0a was the last counted proc allocation in the boot, and
       the environment the parked process will run on wants the sealed form
       ([ProofSyscall.sysc_proc_env]'s [procs_avail None]).  One-way, and
       persistent afterwards. *)
    (* [procs_avail_seal] allocates an invariant, so it is a FUPD and not a
       basic update -- unlike [kalloc_env_at_seal] two lines up, which [iMod]
       eliminates against a bare [WP] on its own. *)
    iApply fupd_wp.
    iMod (procs_avail_seal ⊤ np with "Hpav") as "#Hpav".
    iModIntro.
    iMod (FP.forkret_park γs γf (proc_addr j) ks rest pid (upd_cwd V ipv) Hrest
            with "Hks Hctx Hpriv Hfd Hirs") as "Hpctx".
    iMod (pstate_whole_update (proc_addr j) USED RUNNABLE with "Hpwhole")
      as "Hpwhole".
    iEval (rewrite uin_pwhole_runnable) in "Hpwhole".
    iRename "Hpwhole" into "Hplock".
    iDestruct (proc_slots_park γs (proc_addr j) RUNNABLE needs_ctx_RUNNABLE
                 with "Hpctx Hhart Hmk") as "Hslots".
    iDestruct (proc_lock_res_intro γs γl (proc_addr j) RUNNABLE ch
                 with "Hpstcell Hplock Hpchan Hppub Hslots") as "HR".
    (* ===== +0x2c c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (UI + 0x2c)) Ra0 Rs1 R9
              (trap_res b + (K - 4))%nat false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi2c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (R10 := <[Regidx Ra0 := regval_into_reg
                   (add_vec (zero_reg : mword 64) (R9 !!! Regidx Rs1))]> R9).
    assert (HR10a0 : (R10 !!! Regidx Ra0 : mword 64) = proc_addr j).
    { rewrite /R10 upd_eq HR9s1. apply add_vec_zero_l. }
    assert (Hpp2e : add_vec_int (mword_of_int (UI + 0x2c) : mword 64) 2
                    = mword_of_int (UI + 0x2e)) by pcw.
    iEval (rewrite Hpp2e) in "Hpc".
    (* ===================================================================== *)
    (* +0x2e jal ra,release                                                  *)
    (* ===================================================================== *)
    iApply (wp_jal_s_sconf (mword_of_int (UI + 0x2e)) Rra
              (mword_of_int 2093160 : mword 21) R10 (trap_res b + (K - 4))%nat false
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi2e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (R11 := <[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (UI + 0x2e) : mword 64) 4)]> R10).
    assert (Htgtrl : add_vec (mword_of_int (UI + 0x2e) : mword 64)
                       (sign_extend' 64 (mword_of_int 2093160 : mword 21))
                     = mword_of_int KernelSyms.release) by pcw.
    iEval (rewrite Htgtrl) in "Hpc".
    assert (HR11ra : (R11 !!! Regidx Rra : mword 64)
                     = add_vec_int (mword_of_int (UI + 0x2e) : mword 64) 4)
      by (rewrite /R11; apply upd_eq).
    assert (HR11a0 : (R11 !!! Regidx Ra0 : mword 64) = proc_addr j)
      by (rewrite /R11 upd_ne; [exact HR10a0 | nz]).
    assert (Hlka : add_vec (R11 !!! Regidx Ra0)
                     (sign_extend' 64 (mword_of_int 0 : mword 12)) = proc_addr j)
      by (rewrite HR11a0; apply addv_sext0).
    iApply (RL.wp_release_sconf KT1 γl (proc_addr j) "proc"%string
              (proc_lock_res γs γl (proc_addr j)) R11 0%nat b pj (K - 4)%nat
              ({["proc"]} ∪ lks) Hlka Krl
              with "Hcg Htext Hpc [] Htok HR Hcpu Hpay").
    { iApply (procs_inv_lookup γs j γl Hgl with "Hpinv"). }
    iIntros (CID20 Hq20 mr3) "Hcg Hpc %Hcsrl Hcpu".
    iEval (rewrite (_ : ({["proc"]} ∪ lks) ∖ {["proc"]} = lks);
           [| apply locks_add_del_below; exact Hbelow]) in "Hcpu".
    assert (Hpc32 : ret_pc (R11 !!! Regidx Rra : mword 64)
                    = mword_of_int (UI + 0x32)) by (rewrite HR11ra; pcw).
    iEval (rewrite Hpc32) in "Hpc".
    (* ---- the three callees' [callee_saved]s, composed ---- *)
    assert (Hcs_ap : callee_saved R3 mr1) by exact Hcsap.
    assert (Hcs_nm : callee_saved R9 mr3).
    { eapply callee_saved_trans; [| exact Hcsrl].
      rewrite /R11. apply callee_saved_insert_r; [vm_compute; reflexivity |].
      rewrite /R10. apply callee_saved_insert_r; [vm_compute; reflexivity |].
      apply callee_saved_refl. }
    (* every register userinit itself does not write is threaded end-to-end *)
    assert (Hthr : uin_thr m mr3).
    { intros c Hcs N2 N8 N9.
      rewrite (callee_saved_lookup Hcs_nm c Hcs).
      rewrite /R9 upd_ne; [| regne].
      rewrite (callee_saved_lookup Hcsnm c Hcs).
      rewrite /R8 upd_ne; [| regne]. rewrite /R7 upd_ne; [| regne].
      rewrite /R6 upd_ne; [| regne]. rewrite /R5 upd_ne; [| regne].
      rewrite /R4 upd_ne; [| regne].
      rewrite (callee_saved_lookup Hcs_ap c Hcs).
      exact (HR3thr c Hcs N2 N8 N9). }
    assert (Hspf : uin_sp m mr3).
    { rewrite /uin_sp.
      rewrite (callee_saved_lookup Hcs_nm csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /R9 upd_ne; [| nz].
      rewrite (callee_saved_lookup Hcsnm csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /R8 upd_ne; [| nz]. rewrite /R7 upd_ne; [| nz].
      rewrite /R6 upd_ne; [| nz]. rewrite /R5 upd_ne; [| nz].
      rewrite /R4 upd_ne; [| nz].
      rewrite (callee_saved_lookup Hcs_ap csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HR3sp. }
    (* ===== +0x32 .. +0x36 : the three restores ===== *)
    assert (Hc1 : add_vec (mr3 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite Hspf; apply uin_frm1).
    assert (Hc2 : add_vec (mr3 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite Hspf; apply uin_frm2).
    assert (Hc3 : add_vec (mr3 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite Hspf; apply uin_frm3).
    iApply (wp_cldsp_s_sconf (mword_of_int (UI + 0x32))
              (mword_of_int 3 : mword 6) Rra mr3 (K - 4)%nat
              (m !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi32 [Hf1]").
    { iEval (rewrite Hc1). iExact "Hf1". }
    iIntros (CID21 Hq21) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> mr3).
    assert (HP1sp : uin_sp m P1)
      by (rewrite /uin_sp /P1 upd_ne; [exact Hspf | nz]).
    assert (HP1thr : uin_thr m P1).
    { intros c Hcs N2 N8 N9. rewrite /P1 upd_ne; [| regne].
      exact (Hthr c Hcs N2 N8 N9). }
    assert (HP1ra : (P1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (Hpp34 : add_vec_int (mword_of_int (UI + 0x32) : mword 64) 2
                    = mword_of_int (UI + 0x34)) by pcw.
    iEval (rewrite Hpp34) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (UI + 0x34))
              (mword_of_int 2 : mword 6) Rs0 P1 (K - 4)%nat
              (m !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi34 [Hf2]").
    { iEval (rewrite HP1sp -Hspf Hc2). iExact "Hf2". }
    iIntros (CID22 Hq22) "Hcg Hpc Hf2".
    iEval (rewrite HP1sp -Hspf Hc2) in "Hf2".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2sp : uin_sp m P2)
      by (rewrite /uin_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2thr : uin_thr m P2).
    { intros c Hcs N2 N8 N9. rewrite /P2 upd_ne; [| regne].
      exact (HP1thr c Hcs N2 N8 N9). }
    assert (HP2ra : (P2 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1ra | nz]).
    assert (Hpp36 : add_vec_int (mword_of_int (UI + 0x34) : mword 64) 2
                    = mword_of_int (UI + 0x36)) by pcw.
    iEval (rewrite Hpp36) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (UI + 0x36))
              (mword_of_int 1 : mword 6) Rs1 P2 (K - 4)%nat
              (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi36 [Hf3]").
    { iEval (rewrite HP2sp -Hspf Hc3). iExact "Hf3". }
    iIntros (CID23 Hq23) "Hcg Hpc Hf3".
    iEval (rewrite HP2sp -Hspf Hc3) in "Hf3".
    set (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2).
    assert (HP3sp : uin_sp m P3)
      by (rewrite /uin_sp /P3 upd_ne; [exact HP2sp | nz]).
    assert (HP3thr : uin_thr m P3).
    { intros c Hcs N2 N8 N9. rewrite /P3 upd_ne; [| regne].
      exact (HP2thr c Hcs N2 N8 N9). }
    assert (HP3ra : (P3 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2ra | nz]).
    assert (Hpp38 : add_vec_int (mword_of_int (UI + 0x36) : mword 64) 2
                    = mword_of_int (UI + 0x38)) by pcw.
    iEval (rewrite Hpp38) in "Hpc".
    (* ===== +0x38 c.addi16sp sp,32 : pop ===== *)
    assert (Hwv : add_vec (P3 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))
                  = sp0)
      by (rewrite HP3sp; apply stk_pop_32).
    assert (Hpopeq : (P3 !!! Regidx csp_rs1 : mword 64)
                     = pa_stk (add_vec (P3 !!! Regidx csp_rs1 : mword 64)
                         (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4)
      by (rewrite Hwv HP3sp; reflexivity).
    iAssert (stack_own (KTR := KT1) sp0 4) with "[Hf1 Hf2 Hf3 Hf4]" as "Hstk".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hf1"; [iExists _; iExact "Hf1" |].
      iSplitL "Hf2"; [iExists _; iExact "Hf2" |].
      iSplitL "Hf3"; [iExists _; iExact "Hf3" |].
      iSplitL "Hf4"; [iExists _; iExact "Hf4" |].
      done. }
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (UI + 0x38))
              (mword_of_int 2 : mword 6) P3 (K - 4)%nat 4 b Hpopeq
              with "Hcg Hpc Hi38 Hstk").
    iIntros (CID24 Hq24) "Hcg Hpc".
    set (P4 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P3 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P3).
    iEval (rewrite Kpop) in "Hcg".
    assert (Hpp3a : add_vec_int (mword_of_int (UI + 0x38) : mword 64) 2
                    = mword_of_int (UI + 0x3a)) by pcw.
    iEval (rewrite Hpp3a) in "Hpc".
    (* ===== +0x3a c.jr ra ===== *)
    assert (HP4ra : (P4 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /P4 upd_ne; [exact HP3ra | nz]).
    iApply (wp_cret_s_sconf (mword_of_int (UI + 0x3a)) Rra P4 K b
              ltac:(nz) with "Hcg Hpc Hi3a").
    iIntros (CID25 Hq25) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (P4 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HP4ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE CONTRACT ===== *)
    assert (Csp : (P4 !!! Regidx csp_rs1 : mword 64)
                  = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P4 upd_eq; exact Hwv).
    assert (Cs0 : (P4 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64)).
    { rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_ne; [| nz].
      rewrite /P2 upd_eq. reflexivity. }
    assert (Cs1 : (P4 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64)).
    { rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_eq. reflexivity. }
    assert (Hfin : uin_thr m P4).
    { intros c Hcs N2 N8 N9. rewrite /P4 upd_ne; [| regne].
      exact (HP3thr c Hcs N2 N8 N9). }
    assert (Cs2 : (P4 !!! Regidx (mword_of_int 18 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 18 : mword 5) : mword 64))
      by (apply Hfin; namidx).
    assert (Cs3 : (P4 !!! Regidx (mword_of_int 19 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 19 : mword 5) : mword 64))
      by (apply Hfin; namidx).
    assert (Cs4 : (P4 !!! Regidx (mword_of_int 20 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 20 : mword 5) : mword 64))
      by (apply Hfin; namidx).
    assert (Cs5 : (P4 !!! Regidx (mword_of_int 21 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 21 : mword 5) : mword 64))
      by (apply Hfin; namidx).
    assert (Cs6 : (P4 !!! Regidx (mword_of_int 22 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 22 : mword 5) : mword 64))
      by (apply Hfin; namidx).
    assert (Cs7 : (P4 !!! Regidx (mword_of_int 23 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 23 : mword 5) : mword 64))
      by (apply Hfin; namidx).
    assert (Cs8 : (P4 !!! Regidx (mword_of_int 24 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 24 : mword 5) : mword 64))
      by (apply Hfin; namidx).
    assert (Cs9 : (P4 !!! Regidx (mword_of_int 25 : mword 5) : mword 64)
                  = (m !!! Regidx (mword_of_int 25 : mword 5) : mword 64))
      by (apply Hfin; namidx).
    assert (Cs10 : (P4 !!! Regidx (mword_of_int 26 : mword 5) : mword 64)
                   = (m !!! Regidx (mword_of_int 26 : mword 5) : mword 64))
      by (apply Hfin; namidx).
    assert (Cs11 : (P4 !!! Regidx (mword_of_int 27 : mword 5) : mword 64)
                   = (m !!! Regidx (mword_of_int 27 : mword 5) : mword 64))
      by (apply Hfin; namidx).
    iDestruct (cpu_own_transport CID20 CID25 0%nat b pj b
                 ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iSpecialize ("Hcont" $! CID25 with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! P4 with "Hcg Hpc [%] Hcpu [] Hpav [Hinitproc]").
    - split; [| exact HP4ra].
      unfold callee_saved. split_and!; assumption.
    - iExact "Hkenv".
    - iExists _. iExact "Hinitproc".
  Qed.

End ProofUserinit.

End UserinitProof.
