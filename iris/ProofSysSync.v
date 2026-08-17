(* ProofSysSync.v -- sys_sync() over the SIE-agnostic sconf world.

     uint64 sys_sync(void) {
       acquire(&log.lock);
       if (log.committing || log.outstanding > 0) {
         int n = log.ncommit + 1;
         while (log.ncommit < n) SLEEP;
       }
       release(&log.lock);
       return 0;
     }

   where SLEEP is the SPLIT sleep protocol (SpecSleep.v's header):

       sleep_prepare(&log); release(&log.lock); sleep(); acquire(&log.lock);

   Structure (CodeSysSync.v has the byte-exact disassembly): a 32-byte
   ra/s0/s1/s2 frame, acquire(&log), the two-part guard at +0x18 / +0x22,
   and -- only inside the taken branch -- the s1/s2 spills, the ncommit
   snapshot and the wait loop.

   THREE THINGS ABOUT THE SHAPE ARE WORTH KNOWING BEFORE READING IT.

   - THE LOOP IS A DO-WHILE, AND THE COUNTER COMPARISON IS BACKWARDS.  gcc
     never materialised [n = ncommit + 1]: s2 holds the ORIGINAL count and
     the back edge at +0x56 is [bge s2,a5] -- "loop while the old count is
     still >= the current one" -- i.e. the exit test is "the counter
     strictly advanced".  The body therefore runs once unconditionally, and
     the loop head is the [c.mv a0,s1] at +0x3e, not the test.

   - s1 AND s2 ARE SPILLED LAZILY, inside the taken branch rather than in
     the prologue (filestat's pattern; see the bump playbook §4e).  So the
     frame's live set differs between the two arms: on the FAST path
     (nothing pending) slots 3 and 4 are never written and s1/s2 are never
     clobbered, while on the slow path they are saved at +0x2a/+0x2c and
     restored at +0x5a/+0x5c.  Both arms meet at +0x5e with s1 and s2 at
     their ENTRY values and the two slots holding junk, which is exactly
     what [ss_exit] asks for -- one tail, two ways in.

   - THE LOOP BODY IS acquiresleep's BODY, INSTRUCTION FOR INSTRUCTION, and
     begin_op's sleep arms are its nearest transcription
     ([ProofBeginOp.bo_armA_body]).  One register serves all four calls
     because [&log] and [&log.lock] are the same address ([lock] is [struct
     log]'s first field).  As there, the park means the retry loop is proved
     by iLöb over a [wp_next]-ANCHORED loop invariant, and the
     trap_csrs/cpu_claim pair splits around the interior release and rejoins
     after the re-acquire ([arm_pay_ext_split] / [arm_pay_ext_join]):
     between +0x46 and +0x50 this thread holds no lock at all, and that
     window is where the park lives.

   WHAT THE PROOF DOES NOT DO.  The contract is empty (SpecSysSync.v's
   header says why), so [log_res] is opened only to READ the three cells the
   guard and the loop test look at, and closed again verbatim -- no ghost
   step anywhere.  The three reads are [committing], [outstanding] and
   [ncommit], and the only thing the proof needs from the invariant is
   [outstanding <= 3], which makes the [bge zero,a5] guard a comparison of
   64-bit literals.

   A functor over ACQUIRE / RELEASE / SLEEP_PREPARE / SLEEP. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.algebra Require Import auth gmap gset frac excl.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map mono_nat.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RiscvModelBytes.
Require Import InstrBytes KernelText WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import W32Arith.
Require Import KernelRvcDecode.
Require Import WpSmodeIntr.
Require Import ProcGeom.
Require Import FdSlots.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpLock.
Require Import DiskPtsto.
Require Import BioDefs.
Require Import FsBlocks LogInv.
Require Import SpecAcquire SpecRelease SpecSleepPrepare SpecSleep.
Require Import SpecSysSync.
Require Import CodeSysSync.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Import Defs.

Local Open Scope Z_scope.

Set Printing Depth 40.

Notation SS := KernelSyms.sys_sync.

Notation Rra := (mword_of_int 1 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Rs1 := (mword_of_int 9 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).

(* ===================================================================== *)
(*  Pure bridges (mword-FREE side conditions -- the zify-hook rule in     *)
(*  claude-notes/durable-notes.md).                                      *)
(* ===================================================================== *)

(* the stack budget: the 4-slot frame, then sleep's 22 (acquire/release's 10) *)
Lemma ss_K4  (K : nat) : (K_sys_sync <= K)%nat -> (4 <= K)%nat.
Proof. lia. Qed.
Lemma ss_K10 (K : nat) : (K_sys_sync <= K)%nat -> (10 <= K - 4)%nat.
Proof. lia. Qed.
Lemma ss_K22 (K : nat) : (K_sys_sync <= K)%nat -> (22 <= K - 4)%nat.
Proof. lia. Qed.
Lemma ss_Kback (K : nat) : (K_sys_sync <= K)%nat -> ((K - 4) + 4)%nat = K.
Proof. lia. Qed.
Lemma ss_noff1 : (Z.of_nat 0 + 1 < 2 ^ 31)%Z.
Proof. lia. Qed.
Lemma ss_noff2 : (Z.of_nat 1 + 1 < 2 ^ 31)%Z.
Proof. vm_compute. reflexivity. Qed.

(* ---- the six relocations ---- *)

Lemma ss_reloc_a0_08 :
  add_vec (add_vec (mword_of_int (SS + 0x08) : mword 64)
                   (auipc_off (mword_of_int 30 : mword 20)))
          (sign_extend' 64 (mword_of_int 1270 : mword 12)) = log_addr.
Proof. rewrite /log_addr. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma ss_reloc_cmt_14 :
  add_vec (add_vec (mword_of_int (SS + 0x14) : mword 64)
                   (auipc_off (mword_of_int 30 : mword 20)))
          (sign_extend' 64 (mword_of_int 1290 : mword 12)) = l_cmt.
Proof.
  rewrite /l_cmt /log_pa /log_addr /pa_add /add_vec_int.
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma ss_reloc_out_1e :
  add_vec (add_vec (mword_of_int (SS + 0x1e) : mword 64)
                   (auipc_off (mword_of_int 30 : mword 20)))
          (sign_extend' 64 (mword_of_int 1276 : mword 12)) = l_out.
Proof.
  rewrite /l_out /log_pa /log_addr /pa_add /add_vec_int.
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma ss_reloc_nc_2e :
  add_vec (add_vec (mword_of_int (SS + 0x2e) : mword 64)
                   (auipc_off (mword_of_int 30 : mword 20)))
          (sign_extend' 64 (mword_of_int 1272 : mword 12)) = l_ncommit.
Proof.
  rewrite /l_ncommit /log_pa /log_addr /pa_add /add_vec_int.
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma ss_reloc_s1_36 :
  add_vec (add_vec (mword_of_int (SS + 0x36) : mword 64)
                   (auipc_off (mword_of_int 30 : mword 20)))
          (sign_extend' 64 (mword_of_int 1224 : mword 12)) = log_addr.
Proof. rewrite /log_addr. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma ss_reloc_a0_5e :
  add_vec (add_vec (mword_of_int (SS + 0x5e) : mword 64)
                   (auipc_off (mword_of_int 30 : mword 20)))
          (sign_extend' 64 (mword_of_int 1184 : mword 12)) = log_addr.
Proof. rewrite /log_addr. apply bv_eq; vm_compute; reflexivity. Qed.

(* the loop test's own cell address, off s1 = &log *)
Lemma ss_addr_nc :
  add_vec log_addr (sign_extend' 64 (mword_of_int 40 : mword 12)) = l_ncommit.
Proof.
  rewrite /l_ncommit /log_pa /log_addr /pa_add /add_vec_int.
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* sleep_prepare's panic arm, refuted: the channel is a static address *)
Lemma ss_log_nz : eq_vec log_addr (zero_reg : mword 64) = false.
Proof. rewrite /log_addr. vm_compute. reflexivity. Qed.

(* ---- the two guard comparisons ---- *)

(* [c.bnez a5] on the [committing] flag, read back sign-extended *)
Lemma ss_cmt_nz (c : bool) :
  neq_vec (sign_extend' 64 (mword_of_int (if c then 1 else 0) : mword 32) : mword 64)
          (zero_reg : mword 64) = c.
Proof. destruct c; vm_compute; reflexivity. Qed.

(* [bge zero,a5] on [outstanding]: [out <= 3] keeps the sign extension the
   identity, so the machine compare IS the [Z] compare. *)
Lemma ss_out_cmp (out : nat) : (out <= 3)%nat ->
  zopz0zKzJ_s (zero_reg : mword 64)
    (sign_extend' 64 (mword_of_int (Z.of_nat out) : mword 32) : mword 64)
  = Z.geb 0 (Z.of_nat out).
Proof.
  intro H. rewrite (w32_sext_moi (Z.of_nat out) ltac:(lia)).
  apply w32_bge0_moi. lia.
Qed.

(* ===================================================================== *)
(*  The two register-map invariants.  HART-FREE (tp is pinned by          *)
(*  [HartTp]).  [ss_regs0] is the shape at the FRAME's boundaries -- the  *)
(*  spill block's entry and the shared tail -- where s1/s2 still hold the *)
(*  CALLER's values; [ss_regs] is the wait loop's, where s1 = &log.       *)
(* ===================================================================== *)

Definition ss_saved (m M : regfile) : Prop :=
  M !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5) /\
  M !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5) /\
  M !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) /\
  M !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) /\
  M !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) /\
  M !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) /\
  M !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) /\
  M !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) /\
  M !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5).

Definition ss_regs0 (m M : regfile) (spd : mword 64) : Prop :=
  M !!! Regidx csp_rs1 = spd /\
  M !!! Regidx Rs1 = m !!! Regidx Rs1 /\
  M !!! Regidx Rs2 = m !!! Regidx Rs2 /\
  ss_saved m M.

Definition ss_regs (m M : regfile) (spd : mword 64) : Prop :=
  M !!! Regidx Rs1 = log_addr /\
  M !!! Regidx csp_rs1 = spd /\
  ss_saved m M.

Lemma ss_saved_cs (m M1 M2 : regfile) :
  callee_saved M1 M2 -> ss_saved m M1 -> ss_saved m M2.
Proof.
  intros Hcs Ha. unfold ss_saved in *.
  destruct Ha as (A&B&Cc&D&E&F&G&H&I).
  repeat split;
    [ rewrite (callee_saved_lookup Hcs (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)); exact A
    | rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)); exact B
    | rewrite (callee_saved_lookup Hcs (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity)); exact Cc
    | rewrite (callee_saved_lookup Hcs (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity)); exact D
    | rewrite (callee_saved_lookup Hcs (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity)); exact E
    | rewrite (callee_saved_lookup Hcs (mword_of_int 24 : mword 5) ltac:(vm_compute; reflexivity)); exact F
    | rewrite (callee_saved_lookup Hcs (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity)); exact G
    | rewrite (callee_saved_lookup Hcs (mword_of_int 26 : mword 5) ltac:(vm_compute; reflexivity)); exact H
    | rewrite (callee_saved_lookup Hcs (mword_of_int 27 : mword 5) ltac:(vm_compute; reflexivity)); exact I ].
Qed.

Lemma ss_regs0_cs (m M1 M2 : regfile) (spd : mword 64) :
  callee_saved M1 M2 -> ss_regs0 m M1 spd -> ss_regs0 m M2 spd.
Proof.
  intros Hcs (A & B & Cc & D). split; [| split; [| split]].
  - rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact A.
  - rewrite (callee_saved_lookup Hcs Rs1 ltac:(vm_compute; reflexivity)). exact B.
  - rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)). exact Cc.
  - exact (ss_saved_cs m M1 M2 Hcs D).
Qed.

Lemma ss_regs_cs (m M1 M2 : regfile) (spd : mword 64) :
  callee_saved M1 M2 -> ss_regs m M1 spd -> ss_regs m M2 spd.
Proof.
  intros Hcs (A & B & Cc). split; [| split].
  - rewrite (callee_saved_lookup Hcs Rs1 ltac:(vm_compute; reflexivity)). exact A.
  - rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact B.
  - exact (ss_saved_cs m M1 M2 Hcs Cc).
Qed.

(* ===================================================================== *)

Section SsProps.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ,
            !fsLogG Σ, !logG Σ}.

  Context {kt : ktier}.
  (* The log lock's resource, opened for exactly the three cells sys_sync
     reads.  Nothing else in [log_res] is touched, and the closing wand puts
     the same three back -- there is no ghost step anywhere in this proof. *)
  Lemma ss_cells (γ : log_names) (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) :
    log_res γ bn γfs cov logstart -∗
    ∃ (out : nat) (cmt : bool) (nc : SailStdpp.Values.mword 32),
      ⌜(out <= 3)%nat⌝ ∗
      l_out ↦₄ (mword_of_int (Z.of_nat out) : mword 32) ∗
      l_cmt ↦₄ (mword_of_int (if cmt then 1 else 0) : mword 32) ∗
      l_ncommit ↦₄ nc ∗
      (l_out ↦₄ (mword_of_int (Z.of_nat out) : mword 32) -∗
       l_cmt ↦₄ (mword_of_int (if cmt then 1 else 0) : mword 32) -∗
       l_ncommit ↦₄ nc -∗
       log_res γ bn γfs cov logstart).
  Proof.
    rewrite /log_res.
    iIntros "H". iDestruct "H" as (out cmt nc om E X)
      "(Hout & Hcmt & Hnc & Hauth & %Hsz & %Hbnd & %Hout3 & %Hcmt0 & Hepa & %Hepos & Hxa & %Hlive & %Hcap & Hrest)".
    iExists out, cmt, nc.
    iSplitR; [iPureIntro; exact Hout3|].
    iFrame "Hout Hcmt Hnc".
    iIntros "Hout Hcmt Hnc".
    iExists out, cmt, nc, om, E, X.
    iFrame "Hout Hcmt Hnc Hauth".
    iSplitR; [iPureIntro; exact Hsz|].
    iSplitR; [iPureIntro; exact Hbnd|].
    iSplitR; [iPureIntro; exact Hout3|].
    iSplitR; [iPureIntro; exact Hcmt0|].
    iFrame "Hepa".
    iSplitR; [iPureIntro; exact Hepos|].
    iFrame "Hxa".
    iSplitR; [iPureIntro; exact Hlive|].
    iSplitR; [iPureIntro; exact Hcap|].
    iExact "Hrest".
  Qed.

  (* The shared TAIL, control at +0x5e (a0 := &log, release, return 0), and
     the WAIT LOOP's invariant, control at +0x3e (the log lock held).  Both
     are [wp_next]s ANCHORED at the function's entry hart [CID0]: the park
     inside the loop means either can be entered at a hart nobody knew about
     when it was established. *)
  Definition ss_exit `{GEN : GenId} (CID0 : CPU)
      (j : nat)
      (γ : log_names) (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z)
      (m : regfile) (K : nat) (eb : bool) (lks : gset string)
      (spd sp0 : mword 64) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
      ∀ (M : regfile),
      ⌜ ss_regs0 m M spd ⌝ -∗
      pa_stk sp0 1 ↦₈[kt] (m !!! Regidx Rra) -∗
      pa_stk sp0 2 ↦₈[kt] (m !!! Regidx Rs0) -∗
      (∃ v : mword 64, pa_stk sp0 3 ↦₈[kt] v) -∗
      (∃ v : mword 64, pa_stk sp0 4 ↦₈[kt] v) -∗
      locked (ln_lk γ) cpu_id -∗
      log_res γ bn γfs cov logstart -∗
      cpu_own 1 eb (proc_addr j) false ({["log"]} ∪ lks) -∗
      trap_csrs kt -∗
      cpu_claim (proc_addr j) -∗
      sie_cap_gpr kt M (trap_res eb + (K - 4))%nat false (proc_addr j) -∗
      pc_is (mword_of_int (SS + 0x5e)) -∗
      WP (Loop : expr riscv_lang)))%I.

  Definition ss_loop `{GEN : GenId} (CID0 : CPU)
      (j : nat)
      (γ : log_names) (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z)
      (m : regfile) (K : nat) (eb : bool) (lks : gset string)
      (spd sp0 : mword 64) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
      ∀ (M : regfile),
      ⌜ ss_regs m M spd ⌝ -∗
      pa_stk sp0 1 ↦₈[kt] (m !!! Regidx Rra) -∗
      pa_stk sp0 2 ↦₈[kt] (m !!! Regidx Rs0) -∗
      pa_stk sp0 3 ↦₈[kt] (m !!! Regidx Rs1) -∗
      pa_stk sp0 4 ↦₈[kt] (m !!! Regidx Rs2) -∗
      locked (ln_lk γ) cpu_id -∗
      log_res γ bn γfs cov logstart -∗
      cpu_own 1 eb (proc_addr j) false ({["log"]} ∪ lks) -∗
      trap_csrs kt -∗
      cpu_claim (proc_addr j) -∗
      sie_cap_gpr kt M (trap_res eb + (K - 4))%nat false (proc_addr j) -∗
      pc_is (mword_of_int (SS + 0x3e)) -∗
      ss_exit CID0 j γ bn γfs cov logstart m K eb lks spd sp0 -∗
      WP (Loop : expr riscv_lang)))%I.

End SsProps.

(* ===================================================================== *)

Module SysSyncProof (Acquire : ACQUIRE) (Release : RELEASE)
                    (SleepPrepare : SLEEP_PREPARE) (Sleep : SLEEP) : SYS_SYNC.

Local Ltac reg_neq :=
  lazymatch goal with |- ?a <> ?b =>
    tryif unify a b then fail else (vm_compute; discriminate) end.

Section SsBodies.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ,
            !fsLogG Σ, !logG Σ}.

  Context {kt : ktier}.
  (* ---- THE SHARED TAIL: +0x5e (a0 := &log) .. +0x72 (c.ret) ---- *)
  Lemma ss_tail_body `{GEN : GenId} `{CID : CpuId} (CID0 : CPU) (j : nat)
      (γ : log_names) (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (m M : regfile) (K : nat) (eb : bool) (lks : gset string)
      (spd sp0 : mword 64) :
    let pj := proc_addr j in
    (K_sys_sync <= K)%nat ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = spd ->
    sp0 = m !!! Regidx csp_rs1 ->
    ss_regs0 m M spd ->
    (* the round trip's cancellation ([release]'s postcondition subtracts
       "log" back off): [locks_add_del_below] needs ["log" ∉ lks],
       which is exactly what this order premise gives. *)
    locks_below lks "log" ->
    kernel_text -∗
    log_ctx γ bn γfs cov logstart dev -∗
    pa_stk sp0 1 ↦₈[kt] (m !!! Regidx Rra) -∗
    pa_stk sp0 2 ↦₈[kt] (m !!! Regidx Rs0) -∗
    (∃ v : mword 64, pa_stk sp0 3 ↦₈[kt] v) -∗
    (∃ v : mword 64, pa_stk sp0 4 ↦₈[kt] v) -∗
    locked (ln_lk γ) cpu_id -∗
    log_res γ bn γfs cov logstart -∗
    cpu_own 1 eb pj false ({["log"]} ∪ lks) -∗
    trap_csrs kt -∗
    cpu_claim pj -∗
    sie_cap_gpr kt M (trap_res eb + (K - 4))%nat false pj -∗
    pc_is (mword_of_int (SS + 0x5e)) -∗
    wp_next (CID0 := CID0) true pj (fun (CID : CpuId) =>
      ∀ (mf : regfile),
        ⌜ callee_saved m mf ⌝ -∗
        ⌜ mf !!! Regidx Ra0 = (mword_of_int 0 : mword 64) ⌝ -∗
        sie_cap_gpr kt mf K eb pj -∗
        cpu_own 0 eb pj eb lks -∗
        trap_csrs_ext kt eb -∗
        cpu_claim_ext eb pj -∗
        pc_is (ret_pc (m !!! Regidx Rra)) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj HK Hanch Hspd Hsp0 Hss Hbelow.
    destruct Hss as (Hsp & Hs1v & Hs2v & Hsv).
    destruct Hsv as (H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
    iIntros "#Htext #Hlog Hr24 Hr16 Hr8 Hr0 Htok Hres Hown Htc Hclm Hcg Hpc Hcont".
    iDestruct "Hlog" as "(#Hislock & #Hldev & #Hlstart)".
    iDestruct "Hr8" as (v3) "Hr8". iDestruct "Hr0" as (v4) "Hr0".
    (* the four saved-slot addresses in the [c.ldsp] leaf's spelling *)
    assert (Hb1 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite -Hspd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb2 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite -Hspd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (ssi_5e with "Htext") as "Hi5e".
    iPoseProof (ssi_62 with "Htext") as "Hi62".
    iPoseProof (ssi_66 with "Htext") as "Hi66".
    iPoseProof (ssi_6a with "Htext") as "Hi6a".
    iPoseProof (ssi_6c with "Htext") as "Hi6c".
    iPoseProof (ssi_6e with "Htext") as "Hi6e".
    iPoseProof (ssi_70 with "Htext") as "Hi70".
    iPoseProof (ssi_72 with "Htext") as "Hi72".
    (* +0x5e auipc a0,0x1e *)
    iApply (wp_auipc_s_sconf (mword_of_int (SS + 0x5e)) Ra0
              (mword_of_int 30 : mword 20) M (trap_res eb + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (X1 := <[Regidx Ra0 := regval_into_reg
        (add_vec (mword_of_int (SS + 0x5e) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> M).
    change (<[Regidx Ra0 := regval_into_reg
        (add_vec (mword_of_int (SS + 0x5e) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> M) with X1.
    assert (Hp62 : add_vec_int (mword_of_int (SS + 0x5e) : mword 64) 4 = mword_of_int (SS + 0x62))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp62) in "Hpc".
    (* +0x62 addi a0,a0,1168 *)
    iApply (wp_addi4_s_sconf (mword_of_int (SS + 0x62)) Ra0 Ra0
              (mword_of_int 1184 : mword 12) X1 (trap_res eb + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi62").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (X2 := <[Regidx Ra0 := regval_into_reg
        (add_vec (X1 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 1184 : mword 12)))]> X1).
    change (<[Regidx Ra0 := regval_into_reg
        (add_vec (X1 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 1184 : mword 12)))]> X1) with X2.
    assert (Hp66 : add_vec_int (mword_of_int (SS + 0x62) : mword 64) 4 = mword_of_int (SS + 0x66))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp66) in "Hpc".
    assert (HX2a0 : X2 !!! Regidx Ra0 = log_addr).
    { rewrite /X2 upd_eq /X1 upd_eq. exact ss_reloc_a0_5e. }
    assert (HX2sp : X2 !!! Regidx csp_rs1 = spd).
    { rewrite /X2 upd_ne; [| reg_neq]. rewrite /X1 upd_ne; [| reg_neq]. exact Hsp. }
    (* +0x66 jal ra,release *)
    iApply (wp_jal_s_sconf (mword_of_int (SS + 0x66)) Rra
              (mword_of_int 2084178 : mword 21) X2 (trap_res eb + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi66").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (X3 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (SS + 0x66) : mword 64) 4)]> X2).
    change (<[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (SS + 0x66) : mword 64) 4)]> X2) with X3.
    assert (Hjrel : add_vec (mword_of_int (SS + 0x66) : mword 64)
                      (sign_extend' 64 (mword_of_int 2084178 : mword 21))
                    = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjrel) in "Hpc".
    assert (HX3ra : X3 !!! Regidx Rra = add_vec_int (mword_of_int (SS + 0x66) : mword 64) 4)
      by (rewrite /X3; apply upd_eq).
    assert (HX3a0 : X3 !!! Regidx Ra0 = log_addr)
      by (rewrite /X3 upd_ne; [exact HX2a0 | reg_neq]).
    assert (HX3sp : X3 !!! Regidx csp_rs1 = spd)
      by (rewrite /X3 upd_ne; [exact HX2sp | reg_neq]).
    assert (Hrel_lka : add_vec (X3 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 0 : mword 12)) = log_addr)
      by (rewrite HX3a0; apply addv_sext0).
    (* SPLIT AT THE INDEX: release takes [arm_pay 0 eb pj]; the complement
       rides out to the caller, which is what makes the contract
       index-generic. *)
    iDestruct (arm_pay_ext_split eb _ with "Htc Hclm") as "[Hpay Hext]".
    iApply (Release.wp_release_sconf kt (ln_lk γ) log_addr "log"%string
              (log_res γ bn γfs cov logstart) X3 0%nat eb pj (K - 4)%nat
              ({["log"]} ∪ lks)
              Hrel_lka ltac:(pose proof (ss_K10 K HK); lia)
              with "Hcg Htext Hpc Hislock Htok Hres Hown Hpay").
    iIntros (CIDr Hsr mrel) "Hcg Hpc %Hrelcs Hown".
    iEval (rewrite (locks_add_del_below "log" lks Hbelow)) in "Hown".
    assert (Hpc6a : ret_pc (X3 !!! Regidx Rra) = mword_of_int (SS + 0x6a))
      by (rewrite HX3ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc6a) in "Hpc".
    pose proof Hrelcs as Hrelcs2.
    assert (HmrelSp : mrel !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hrelcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HX3sp. }
    (* +0x6a c.li a0,0 -- the return value, set BEFORE the restores *)
    assert (Hli0 : add_vec (zero_reg : mword 64)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))
                   = (mword_of_int 0 : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_cli_s_sconf (mword_of_int (SS + 0x6a)) Ra0 (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) mrel (K - 4)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok) Hli0
              with "Hcg Hpc Hi6a").
    iIntros (CIDl Hsl) "Hcg Hpc".
    set (Q0 := <[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> mrel).
    change (<[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> mrel) with Q0.
    assert (HQ0sp : Q0 !!! Regidx csp_rs1 = spd)
      by (rewrite /Q0 upd_ne; [exact HmrelSp | reg_neq]).
    assert (Hp6c : add_vec_int (mword_of_int (SS + 0x6a) : mword 64) 2 = mword_of_int (SS + 0x6c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6c) in "Hpc".
    (* +0x6c c.ldsp ra,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (SS + 0x6c)) (mword_of_int 3 : mword 6) Rra
              Q0 (K - 4)%nat (m !!! Regidx Rra) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6c [Hr24]").
    { iEval (rewrite HQ0sp Hb1). iExact "Hr24". }
    iIntros (CIDe1 Hse1) "Hcg Hpc Hr24".
    iEval (rewrite HQ0sp Hb1) in "Hr24".
    set (Q1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra)]> Q0).
    change (<[Regidx Rra := regval_into_reg (m !!! Regidx Rra)]> Q0) with Q1.
    assert (HQ1sp : Q1 !!! Regidx csp_rs1 = spd) by (rewrite /Q1 upd_ne; [exact HQ0sp | reg_neq]).
    assert (Hp6e : add_vec_int (mword_of_int (SS + 0x6c) : mword 64) 2 = mword_of_int (SS + 0x6e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6e) in "Hpc".
    (* +0x6e c.ldsp s0,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (SS + 0x6e)) (mword_of_int 2 : mword 6) Rs0
              Q1 (K - 4)%nat (m !!! Regidx Rs0) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6e [Hr16]").
    { iEval (rewrite HQ1sp Hb2). iExact "Hr16". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hr16".
    iEval (rewrite HQ1sp Hb2) in "Hr16".
    set (Q2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0)]> Q1).
    change (<[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0)]> Q1) with Q2.
    assert (HQ2sp : Q2 !!! Regidx csp_rs1 = spd) by (rewrite /Q2 upd_ne; [exact HQ1sp | reg_neq]).
    assert (Hp70 : add_vec_int (mword_of_int (SS + 0x6e) : mword 64) 2 = mword_of_int (SS + 0x70))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp70) in "Hpc".
    (* +0x70 c.addi16sp sp,32 -- the frame trade back *)
    assert (Hwv : add_vec (Q2 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HQ2sp -Hspd. apply frame_cancel_32. }
    assert (Hpop : Q2 !!! Regidx csp_rs1
                   = pa_stk (add_vec (Q2 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HQ2sp -Hspd. unfold pa_stk, add_vec_int.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iAssert (stack_own (KTR := kt) sp0 4) with "[Hr24 Hr16 Hr8 Hr0]" as "Hframe4".
    { rewrite (stack_own_slots (KTR := kt)). cbn [seq].
      iSplitL "Hr24"; [iExists _; iExact "Hr24"|].
      iSplitL "Hr16"; [iExists _; iExact "Hr16"|].
      iSplitL "Hr8";  [iExists _; iExact "Hr8"|].
      iSplitL "Hr0";  [iExists _; iExact "Hr0"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (SS + 0x70)) (mword_of_int 2 : mword 6) Q2 (K - 4)%nat 4 eb Hpop
              with "Hcg Hpc Hi70 Hframe4").
    iIntros (CIDe3 Hse3) "Hcg Hpc".
    assert (Hnk : ((K - 4) + 4)%nat = K) by (exact (ss_Kback K HK)).
    iEval (rewrite Hnk) in "Hcg".
    set (Q3 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (Q2 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q2).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (Q2 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q2) with Q3.
    assert (Hp72 : add_vec_int (mword_of_int (SS + 0x70) : mword 64) 2 = mword_of_int (SS + 0x72))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp72) in "Hpc".
    (* +0x72 c.ret *)
    assert (HQ3ra : Q3 !!! Regidx Rra = m !!! Regidx Rra).
    { rewrite /Q3 upd_ne; [| reg_neq]. rewrite /Q2 upd_ne; [| reg_neq].
      rewrite /Q1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (SS + 0x72)) Rra Q3 K eb
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi72").
    iIntros (CIDe4 Hse4) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (Q3 !!! Regidx Rra) = ret_pc (m !!! Regidx Rra))
      by (rewrite HQ3ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* the postcondition *)
    assert (Hthr : forall c : mword 5, is_cs_idx c = true ->
              c <> Rra -> c <> csp_rs1 -> c <> Rs0 -> c <> Ra0 ->
              Q3 !!! Regidx c = M !!! Regidx c).
    { intros c Hcs N1 N2 N8 N10.
      rewrite /Q3 /Q2 /Q1 /Q0. repeat (rewrite upd_ne; [| congruence]).
      rewrite (callee_saved_lookup Hrelcs2 c Hcs).
      rewrite /X3 /X2 /X1. repeat (rewrite upd_ne; [| congruence]). reflexivity. }
    assert (HQ3a0 : Q3 !!! Regidx Ra0 = (mword_of_int 0 : mword 64)).
    { rewrite /Q3 upd_ne; [| reg_neq]. rewrite /Q2 upd_ne; [| reg_neq].
      rewrite /Q1 upd_ne; [| reg_neq]. rewrite /Q0 upd_eq. reflexivity. }
    iDestruct (cpu_own_transport CIDr CIDe4 0 eb pj eb ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iDestruct "Hext" as "[Hextc Hextm]".
    iDestruct (trap_csrs_ext_transport CID CIDe4 eb pj ltac:(wp_next_chain)
                 with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID CIDe4 eb pj ltac:(wp_next_chain)
                 with "Hextm") as "Hextm".
    iSpecialize ("Hcont" $! CIDe4 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! Q3 with "[%] [%] Hcg Hown Hextc Hextm Hpc").
    { unfold callee_saved.
      split. { rewrite /Q3 upd_eq. rewrite Hwv. exact Hsp0. }
      split. { rewrite /Q3 upd_ne; [| reg_neq]. rewrite /Q2 upd_eq. reflexivity. }
      split. { rewrite (Hthr Rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Hs1v. }
      split. { rewrite (Hthr Rs2 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Hs2v. }
      split. { rewrite (Hthr (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H19. }
      split. { rewrite (Hthr (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H20. }
      split. { rewrite (Hthr (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H21. }
      split. { rewrite (Hthr (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H22. }
      split. { rewrite (Hthr (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H23. }
      split. { rewrite (Hthr (mword_of_int 24 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H24. }
      split. { rewrite (Hthr (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H25. }
      split. { rewrite (Hthr (mword_of_int 26 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H26. }
      { rewrite (Hthr (mword_of_int 27 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H27. } }
    { exact HQ3a0. }
  Qed.

  (* ---- THE WAIT LOOP's body: +0x3e (the park quartet) .. +0x56 (the back
     edge), with the FALLING arm restoring s1/s2 and dropping into the tail
     at +0x5e.  The Löb hypothesis arrives WITH its [▷]; the taken [bge] at
     +0x56 is what strips it. ---- *)
  Lemma ss_loop_body `{GEN : GenId} `{CID : CpuId} (CID0 : CPU)
      (γs : list gname) (j : nat) (γl : gname)
      (γ : log_names) (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (m M : regfile) (K : nat) (eb : bool) (lks : gset string)
      (spd sp0 : mword 64) :
    let pj := proc_addr j in
    (K_sys_sync <= K)%nat ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = spd ->
    ss_regs m M spd ->
    (* sys_sync acquires "log" (3) DIRECTLY and, while holding it, reaches
       "proc" (11) via sleep_prepare/sleep's own re-acquire -- ONE premise at
       "log" covers the whole cone (LockRank.v: [locks_below_mono] lifts it to
       "proc", [locks_below_union_singleton] carries it across the "log" hold,
       [locks_add_del_below] cancels the release/re-acquire round trip). *)
    locks_below lks "log" ->
    kernel_text -∗
    log_ctx γ bn γfs cov logstart dev -∗
    procs_inv (kt := kt) γs -∗
    ▷ ss_loop (kt := kt) CID0 j γ bn γfs cov logstart m K eb lks spd sp0 -∗
    ss_exit (kt := kt) CID0 j γ bn γfs cov logstart m K eb lks spd sp0 -∗
    pa_stk sp0 1 ↦₈[kt] (m !!! Regidx Rra) -∗
    pa_stk sp0 2 ↦₈[kt] (m !!! Regidx Rs0) -∗
    pa_stk sp0 3 ↦₈[kt] (m !!! Regidx Rs1) -∗
    pa_stk sp0 4 ↦₈[kt] (m !!! Regidx Rs2) -∗
    locked (ln_lk γ) cpu_id -∗
    log_res γ bn γfs cov logstart -∗
    cpu_own 1 eb pj false ({["log"]} ∪ lks) -∗
    trap_csrs kt -∗
    cpu_claim pj -∗
    sie_cap_gpr kt M (trap_res eb + (K - 4))%nat false pj -∗
    pc_is (mword_of_int (SS + 0x3e)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj HK Hj Hjl Hanch Hspd Hss Hbelow.
    assert (Hbelowproc : locks_below lks "proc")
      by lkbelow.
    assert (Hbeloweproc : locks_below ({["log"]} ∪ lks) "proc")
      by (apply locks_below_union_singleton; [vm_compute; lia | exact Hbelowproc]).
    iIntros "#Htext #Hlog #Hpinv IH Hexit Hr24 Hr16 Hr8 Hr0 Htok Hres Hown Htc Hclm Hcg Hpc".
    iDestruct "Hlog" as "(#Hislock & #Hldev & #Hlstart)".
    assert (HssM : ss_regs m M spd) by exact Hss.
    destruct Hss as (Hs1 & Hsp & Hsv).
    iPoseProof (ssi_3e with "Htext") as "Hi3e".
    iPoseProof (ssi_40 with "Htext") as "Hi40".
    iPoseProof (ssi_44 with "Htext") as "Hi44".
    iPoseProof (ssi_46 with "Htext") as "Hi46".
    iPoseProof (ssi_4a with "Htext") as "Hi4a".
    iPoseProof (ssi_4e with "Htext") as "Hi4e".
    iPoseProof (ssi_50 with "Htext") as "Hi50".
    iPoseProof (ssi_54 with "Htext") as "Hi54".
    iPoseProof (ssi_56 with "Htext") as "Hi56".
    iPoseProof (ssi_5a with "Htext") as "Hi5a".
    iPoseProof (ssi_5c with "Htext") as "Hi5c".
    (* THE SPLIT SLEEP PROTOCOL: the loop invariant carries [trap_csrs] and
       [cpu_claim pj] index-free; the interior release wants the PAY half and
       the lock-free sleep() wants the COMPLEMENT. *)
    iDestruct (arm_pay_ext_split eb pj with "Htc Hclm") as "[Hpay [Htcx Hclmx]]".
    (* +0x3e c.mv a0,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (SS + 0x3e)) Ra0 Rs1
              M (trap_res eb + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A0 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M !!! Regidx Rs1))]> M).
    change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M !!! Regidx Rs1))]> M) with A0.
    assert (Hp40 : add_vec_int (mword_of_int (SS + 0x3e) : mword 64) 2 = mword_of_int (SS + 0x40))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp40) in "Hpc".
    assert (HA0a0 : A0 !!! Regidx Ra0 = log_addr).
    { rewrite /A0 upd_eq. rewrite Hs1. apply add_vec_zero_l. }
    (* +0x40 jal ra,sleep_prepare *)
    iApply (wp_jal_s_sconf (mword_of_int (SS + 0x40)) Rra
              (mword_of_int 2088986 : mword 21) A0 (trap_res eb + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi40").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (A1 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (SS + 0x40) : mword 64) 4)]> A0).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (SS + 0x40) : mword 64) 4)]> A0) with A1.
    assert (Hjsp : add_vec (mword_of_int (SS + 0x40) : mword 64)
                     (sign_extend' 64 (mword_of_int 2088986 : mword 21))
                   = mword_of_int KernelSyms.sleep_prepare)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjsp) in "Hpc".
    assert (HA1ra : A1 !!! Regidx Rra = add_vec_int (mword_of_int (SS + 0x40) : mword 64) 4)
      by (rewrite /A1; apply upd_eq).
    assert (HA1a0 : A1 !!! Regidx Ra0 = log_addr)
      by (rewrite /A1 upd_ne; [exact HA0a0 | reg_neq]).
    assert (HcsA1 : callee_saved M A1).
    { rewrite /A1 /A0.
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_refl. }
    assert (HssA1 : ss_regs m A1 spd) by (apply (ss_regs_cs m M A1 spd HcsA1 HssM)).
    assert (HA1nz : eq_vec (A1 !!! Regidx Ra0) (zero_reg : mword 64) = false)
      by (rewrite HA1a0; exact ss_log_nz).
    (* -------------------- sleep_prepare(&log) -------------------- *)
    iApply (SleepPrepare.wp_sleep_prepare_sconf kt γs j γl A1
              (trap_res eb + (K - 4))%nat 1%nat eb false ({["log"]} ∪ lks)
              Hj Hjl HA1nz ss_noff2 ltac:(pose proof (ss_K22 K HK); lia) Hbeloweproc
              with "Hcg Hown Htext Hpc Hpinv").
    all: try lkbelow.
    iApply wp_next_off_intro. iIntros (mfp) "%Hpcs Hcg Hown Hpc".
    assert (Hp44 : ret_pc (A1 !!! Regidx Rra) = mword_of_int (SS + 0x44))
      by (rewrite HA1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp44) in "Hpc".
    assert (HssPr : ss_regs m mfp spd) by (apply (ss_regs_cs m A1 mfp spd Hpcs HssA1)).
    assert (HPrs1 : mfp !!! Regidx Rs1 = log_addr) by (destruct HssPr as (Xx & _); exact Xx).
    (* +0x44 c.mv a0,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (SS + 0x44)) Ra0 Rs1
              mfp (trap_res eb + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi44").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A2 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mfp !!! Regidx Rs1))]> mfp).
    change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mfp !!! Regidx Rs1))]> mfp) with A2.
    assert (HA2a0 : A2 !!! Regidx Ra0 = log_addr).
    { rewrite /A2 upd_eq. rewrite HPrs1. apply add_vec_zero_l. }
    assert (Hp46 : add_vec_int (mword_of_int (SS + 0x44) : mword 64) 2 = mword_of_int (SS + 0x46))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp46) in "Hpc".
    (* +0x46 jal ra,release *)
    iApply (wp_jal_s_sconf (mword_of_int (SS + 0x46)) Rra
              (mword_of_int 2084210 : mword 21) A2 (trap_res eb + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi46").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (A3 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (SS + 0x46) : mword 64) 4)]> A2).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (SS + 0x46) : mword 64) 4)]> A2) with A3.
    assert (Hjrl : add_vec (mword_of_int (SS + 0x46) : mword 64)
                     (sign_extend' 64 (mword_of_int 2084210 : mword 21))
                   = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjrl) in "Hpc".
    assert (HA3ra : A3 !!! Regidx Rra = add_vec_int (mword_of_int (SS + 0x46) : mword 64) 4)
      by (rewrite /A3; apply upd_eq).
    assert (HA3a0 : A3 !!! Regidx Ra0 = log_addr)
      by (rewrite /A3 upd_ne; [exact HA2a0 | reg_neq]).
    assert (HcsA3 : callee_saved mfp A3).
    { rewrite /A3 /A2.
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_refl. }
    assert (HssA3 : ss_regs m A3 spd) by (apply (ss_regs_cs m mfp A3 spd HcsA3 HssPr)).
    assert (Hrel_lka : add_vec (A3 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 0 : mword 12)) = log_addr)
      by (rewrite HA3a0; apply addv_sext0).
    (* -------------------- release(&log.lock) -------------------- *)
    iApply (Release.wp_release_sconf kt (ln_lk γ) log_addr "log"%string
              (log_res γ bn γfs cov logstart) A3 0%nat eb pj (K - 4)%nat
              ({["log"]} ∪ lks)
              Hrel_lka ltac:(pose proof (ss_K10 K HK); lia)
              with "Hcg Htext Hpc Hislock Htok Hres Hown Hpay").
    iIntros (CIDr Hsr mfr) "Hcg Hpc %Hrcs Hown".
    iEval (rewrite (locks_add_del_below "log" lks Hbelow)) in "Hown".
    assert (Hp4a : ret_pc (A3 !!! Regidx Rra) = mword_of_int (SS + 0x4a))
      by (rewrite HA3ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp4a) in "Hpc".
    assert (HssRl : ss_regs m mfr spd) by (apply (ss_regs_cs m A3 mfr spd Hrcs HssA3)).
    (* +0x4a jal ra,sleep *)
    iApply (wp_jal_s_sconf (mword_of_int (SS + 0x4a)) Rra
              (mword_of_int 2089036 : mword 21) mfr (K - 4)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi4a").
    iIntros (CIDj Hsj) "Hcg Hpc".
    set (A4 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (SS + 0x4a) : mword 64) 4)]> mfr).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (SS + 0x4a) : mword 64) 4)]> mfr) with A4.
    assert (Hjsl : add_vec (mword_of_int (SS + 0x4a) : mword 64)
                     (sign_extend' 64 (mword_of_int 2089036 : mword 21))
                   = mword_of_int KernelSyms.sleep)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjsl) in "Hpc".
    assert (HA4ra : A4 !!! Regidx Rra = add_vec_int (mword_of_int (SS + 0x4a) : mword 64) 4)
      by (rewrite /A4; apply upd_eq).
    assert (HcsA4 : callee_saved mfr A4).
    { rewrite /A4. apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
    assert (HssA4 : ss_regs m A4 spd) by (apply (ss_regs_cs m mfr A4 spd HcsA4 HssRl)).
    (* ========================== sleep() ========================== *)
    iDestruct (cpu_own_transport CIDr CIDj 0 eb pj eb ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID CIDj eb pj ltac:(wp_next_chain) with "Htcx") as "Htcx".
    iDestruct (cpu_claim_ext_transport CID CIDj eb pj ltac:(wp_next_chain) with "Hclmx") as "Hclmx".
    iApply (Sleep.wp_sleep_sconf kt γs j γl A4 (K - 4)%nat eb lks Hj Hjl
              ltac:(pose proof (ss_K22 K HK); lia) Hbelowproc
              with "Hcg Hown Htext Hpc Hpinv Htcx Hclmx").
    all: try lkbelow.
    iIntros (CIDs Hss2 mfs) "%Hscs Hcg Hown Hpc Htcx Hclmx".
    assert (Hp4e : ret_pc (A4 !!! Regidx Rra) = mword_of_int (SS + 0x4e))
      by (rewrite HA4ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp4e) in "Hpc".
    assert (HssSl : ss_regs m mfs spd) by (apply (ss_regs_cs m A4 mfs spd Hscs HssA4)).
    assert (HSls1 : mfs !!! Regidx Rs1 = log_addr) by (destruct HssSl as (Xx & _); exact Xx).
    (* +0x4e c.mv a0,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (SS + 0x4e)) Ra0 Rs1
              mfs (K - 4)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4e").
    iIntros (CIDm Hsm) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A5 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mfs !!! Regidx Rs1))]> mfs).
    change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mfs !!! Regidx Rs1))]> mfs) with A5.
    assert (HA5a0 : A5 !!! Regidx Ra0 = log_addr).
    { rewrite /A5 upd_eq. rewrite HSls1. apply add_vec_zero_l. }
    assert (Hp50 : add_vec_int (mword_of_int (SS + 0x4e) : mword 64) 2 = mword_of_int (SS + 0x50))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp50) in "Hpc".
    (* +0x50 jal ra,acquire *)
    iApply (wp_jal_s_sconf (mword_of_int (SS + 0x50)) Rra
              (mword_of_int 2084064 : mword 21) A5 (K - 4)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi50").
    iIntros (CIDn Hsn) "Hcg Hpc".
    set (A6 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (SS + 0x50) : mword 64) 4)]> A5).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (SS + 0x50) : mword 64) 4)]> A5) with A6.
    assert (Hjaq : add_vec (mword_of_int (SS + 0x50) : mword 64)
                     (sign_extend' 64 (mword_of_int 2084064 : mword 21))
                   = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjaq) in "Hpc".
    assert (HA6ra : A6 !!! Regidx Rra = add_vec_int (mword_of_int (SS + 0x50) : mword 64) 4)
      by (rewrite /A6; apply upd_eq).
    assert (HA6a0 : A6 !!! Regidx Ra0 = log_addr)
      by (rewrite /A6 upd_ne; [exact HA5a0 | reg_neq]).
    assert (HcsA6 : callee_saved mfs A6).
    { rewrite /A6 /A5.
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_refl. }
    assert (HssA6 : ss_regs m A6 spd) by (apply (ss_regs_cs m mfs A6 spd HcsA6 HssSl)).
    (* -------------------- acquire(&log.lock) -------------------- *)
    iDestruct (cpu_own_transport CIDs CIDn 0 eb pj eb ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Acquire.wp_acquire_sconf kt (ln_lk γ) "log"%string
              (log_res γ bn γfs cov logstart) A6 0%nat eb pj (K - 4)%nat eb lks
              ss_noff1 ltac:(pose proof (ss_K10 K HK); lia) Hbelow
              with "Hcg Hown Htext Hpc []").
    all: try lkbelow.
    { iEval (rewrite HA6a0). iExact "Hislock". }
    iIntros (CIDa Hsa msA mfa) "%Hmsf Hcg Hpc %Hacs Htok Hres Hown Hpay".
    assert (Hp54 : ret_pc (A6 !!! Regidx Rra) = mword_of_int (SS + 0x54))
      by (rewrite HA6ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp54) in "Hpc".
    assert (HssAq : ss_regs m mfa spd) by (apply (ss_regs_cs m A6 mfa spd Hacs HssA6)).
    assert (HAqs1 : mfa !!! Regidx Rs1 = log_addr) by (destruct HssAq as (Xx & _); exact Xx).
    (* the pair, rebuilt at the hart the test is reached on *)
    iDestruct (trap_csrs_ext_transport CIDs CIDa eb pj ltac:(wp_next_chain) with "Htcx") as "Htcx".
    iDestruct (cpu_claim_ext_transport CIDs CIDa eb pj ltac:(wp_next_chain) with "Hclmx") as "Hclmx".
    iDestruct (arm_pay_ext_join eb pj with "Hpay [Htcx Hclmx]") as "[Htc Hclm]".
    { iSplitL "Htcx"; [iExact "Htcx" | iExact "Hclmx"]. }
    (* +0x54 c.lw a5,40(s1) : a5 := log.ncommit *)
    iDestruct (ss_cells with "Hres") as (out2 cmt2 nc2) "(%Hout3b & Hout & Hcmt & Hnc & Hclose)".
    assert (Hnca : add_vec (rget mfa Rs1) (sign_extend' 64 (mword_of_int 40 : mword 12)) = l_ncommit).
    { rgne. rewrite HAqs1. exact ss_addr_nc. }
    iEval (rewrite -Hnca) in "Hnc".
    iApply (wp_clw_s_sconf (kt := kt) (ktd := KT0) (mword_of_int (SS + 0x54)) Ra5 Rs1
              (mword_of_int 40 : mword 12) mfa (trap_res eb + (K - 4))%nat nc2 false
              (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi54 Hnc").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hnc".
    iEval (rewrite Hnca) in "Hnc".
    iDestruct ("Hclose" with "Hout Hcmt Hnc") as "Hres".
    set (Z1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 nc2)]> mfa).
    change (<[Regidx Ra5 := regval_into_reg (sign_extend' 64 nc2)]> mfa) with Z1.
    assert (Hp56 : add_vec_int (mword_of_int (SS + 0x54) : mword 64) 2 = mword_of_int (SS + 0x56))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp56) in "Hpc".
    assert (HcsZ1 : callee_saved mfa Z1).
    { rewrite /Z1. apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
    assert (HssZ1 : ss_regs m Z1 spd) by (apply (ss_regs_cs m mfa Z1 spd HcsZ1 HssAq)).
    (* +0x56 bge s2,a5 : loop while the OLD count is still >= the current *)
    destruct (zopz0zKzJ_s (rget Z1 Rs2) (rget Z1 Ra5)) eqn:Hcmp56.
    - (* ---- TAKEN: the counter has not moved; back edge to +0x3e ---- *)
      assert (Htgt3e : add_vec (mword_of_int (SS + 0x56) : mword 64)
                         (sign_extend' 64 (mword_of_int 8168 : mword 13))
                       = mword_of_int (SS + 0x3e))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_bge_taken_s_sconf (mword_of_int (SS + 0x56)) (mword_of_int 8168 : mword 13)
                Ra5 Rs2 Z1 (trap_res eb + (K - 4))%nat false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp56 ltac:(rewrite Htgt3e; vm_compute; reflexivity)
                with "Hcg Hpc Hi56").
      iApply wp_next_off_intro. iNext. iIntros "Hcg Hpc".
      iEval (rewrite Htgt3e) in "Hpc".
      rewrite /ss_loop.
      iSpecialize ("IH" $! CIDa with "[%]"); [wp_next_chain|].
      iApply ("IH" $! Z1 with "[%] Hr24 Hr16 Hr8 Hr0 Htok Hres Hown Htc Hclm Hcg Hpc Hexit").
      exact HssZ1.
    - (* ---- FALL: the counter advanced; restore s1/s2 and take the tail ---- *)
      iApply (wp_bge_fall_s_sconf (mword_of_int (SS + 0x56)) (mword_of_int 8168 : mword 13)
                Ra5 Rs2 Z1 (trap_res eb + (K - 4))%nat false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp56 with "Hcg Hpc Hi56").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hp5a : add_vec_int (mword_of_int (SS + 0x56) : mword 64) 4 = mword_of_int (SS + 0x5a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp5a) in "Hpc".
      destruct HssZ1 as (HZ1s1 & HZ1sp & HZ1sv).
      assert (Hb3 : add_vec (Z1 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
      { rewrite HZ1sp -Hspd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
        apply f_equal. apply bv_eq; vm_compute; reflexivity. }
      (* +0x5a c.ldsp s1,8(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (SS + 0x5a)) (mword_of_int 1 : mword 6) Rs1
                Z1 (trap_res eb + (K - 4))%nat (m !!! Regidx Rs1) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi5a [Hr8]").
      { iEval (rewrite Hb3). iExact "Hr8". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hr8".
      iEval (rewrite Hb3) in "Hr8".
      set (Z2 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1)]> Z1).
      change (<[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1)]> Z1) with Z2.
      assert (HZ2sp : Z2 !!! Regidx csp_rs1 = spd) by (rewrite /Z2 upd_ne; [exact HZ1sp | reg_neq]).
      assert (Hb4 : add_vec (Z2 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
      { rewrite HZ2sp -Hspd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
        apply f_equal. apply bv_eq; vm_compute; reflexivity. }
      assert (Hp5c : add_vec_int (mword_of_int (SS + 0x5a) : mword 64) 2 = mword_of_int (SS + 0x5c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp5c) in "Hpc".
      (* +0x5c c.ldsp s2,0(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (SS + 0x5c)) (mword_of_int 0 : mword 6) Rs2
                Z2 (trap_res eb + (K - 4))%nat (m !!! Regidx Rs2) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi5c [Hr0]").
      { iEval (rewrite Hb4). iExact "Hr0". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hr0".
      iEval (rewrite Hb4) in "Hr0".
      set (Z3 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> Z2).
      change (<[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> Z2) with Z3.
      assert (Hp5e : add_vec_int (mword_of_int (SS + 0x5c) : mword 64) 2 = mword_of_int (SS + 0x5e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp5e) in "Hpc".
      assert (HssZ3 : ss_regs0 m Z3 spd).
      { split; [| split; [| split]].
        - rewrite /Z3 upd_ne; [| reg_neq]. exact HZ2sp.
        - rewrite /Z3 upd_ne; [| reg_neq]. rewrite /Z2 upd_eq. reflexivity.
        - rewrite /Z3 upd_eq. reflexivity.
        - destruct HZ1sv as (P19&P20&P21&P22&P23&P24&P25&P26&P27).
          repeat split;
            (rewrite /Z3 upd_ne; [| reg_neq]; rewrite /Z2 upd_ne; [| reg_neq]);
            first [ exact P19 | exact P20 | exact P21 | exact P22 | exact P23
                  | exact P24 | exact P25 | exact P26 | exact P27 ]. }
      rewrite /ss_exit.
      iSpecialize ("Hexit" $! CIDa with "[%]"); [wp_next_chain|].
      iApply ("Hexit" $! Z3 with "[%] Hr24 Hr16 [Hr8] [Hr0] Htok Hres Hown Htc Hclm Hcg Hpc").
      { exact HssZ3. }
      { iExists (m !!! Regidx Rs1). iExact "Hr8". }
      { iExists (m !!! Regidx Rs2). iExact "Hr0". }
  Qed.

  (* ---- THE SPILL BLOCK: +0x2a (save s1/s2) .. +0x3a (s1 := &log), the
     entry to the wait loop.  Both guard arms -- "committing" (taken) and
     "outstanding > 0" (fallen) -- converge here. ---- *)
  Lemma ss_entry_body `{GEN : GenId} `{CID : CpuId} (CID0 : CPU)
      (j : nat)
      (γ : log_names) (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z)
      (m M : regfile) (K : nat) (eb : bool) (lks : gset string)
      (spd sp0 : mword 64) :
    let pj := proc_addr j in
    (K_sys_sync <= K)%nat ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = spd ->
    ss_regs0 m M spd ->
    kernel_text -∗
    ss_loop (kt := kt) CID0 j γ bn γfs cov logstart m K eb lks spd sp0 -∗
    ss_exit (kt := kt) CID0 j γ bn γfs cov logstart m K eb lks spd sp0 -∗
    pa_stk sp0 1 ↦₈[kt] (m !!! Regidx Rra) -∗
    pa_stk sp0 2 ↦₈[kt] (m !!! Regidx Rs0) -∗
    (∃ v : mword 64, pa_stk sp0 3 ↦₈[kt] v) -∗
    (∃ v : mword 64, pa_stk sp0 4 ↦₈[kt] v) -∗
    locked (ln_lk γ) cpu_id -∗
    log_res γ bn γfs cov logstart -∗
    cpu_own 1 eb pj false ({["log"]} ∪ lks) -∗
    trap_csrs kt -∗
    cpu_claim pj -∗
    sie_cap_gpr kt M (trap_res eb + (K - 4))%nat false pj -∗
    pc_is (mword_of_int (SS + 0x2a)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj HK Hanch Hspd Hss.
    iIntros "#Htext Hloop Hexit Hr24 Hr16 Hr8 Hr0 Htok Hres Hown Htc Hclm Hcg Hpc".
    destruct Hss as (Hsp & Hs1v & Hs2v & Hsv).
    iDestruct "Hr8" as (v3) "Hr8". iDestruct "Hr0" as (v4) "Hr0".
    iPoseProof (ssi_2a with "Htext") as "Hi2a".
    iPoseProof (ssi_2c with "Htext") as "Hi2c".
    iPoseProof (ssi_2e with "Htext") as "Hi2e".
    iPoseProof (ssi_32 with "Htext") as "Hi32".
    iPoseProof (ssi_36 with "Htext") as "Hi36".
    iPoseProof (ssi_3a with "Htext") as "Hi3a".
    assert (Hb3 : add_vec (M !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite Hsp -Hspd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb4 : add_vec (M !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite Hsp -Hspd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    (* +0x2a c.sdsp s1,8(sp) *)
    iEval (rewrite -Hb3) in "Hr8".
    iApply (wp_csdsp_s_sconf (mword_of_int (SS + 0x2a)) (mword_of_int 1 : mword 6) Rs1
              M (trap_res eb + (K - 4))%nat v3 false with "Hcg Hpc Hi2a Hr8").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hr8".
    iEval (rgne) in "Hr8". iEval (rewrite Hb3 Hs1v) in "Hr8".
    assert (Hp2c : add_vec_int (mword_of_int (SS + 0x2a) : mword 64) 2 = mword_of_int (SS + 0x2c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2c) in "Hpc".
    (* +0x2c c.sdsp s2,0(sp) *)
    iEval (rewrite -Hb4) in "Hr0".
    iApply (wp_csdsp_s_sconf (mword_of_int (SS + 0x2c)) (mword_of_int 0 : mword 6) Rs2
              M (trap_res eb + (K - 4))%nat v4 false with "Hcg Hpc Hi2c Hr0").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hr0".
    iEval (rgne) in "Hr0". iEval (rewrite Hb4 Hs2v) in "Hr0".
    assert (Hp2e : add_vec_int (mword_of_int (SS + 0x2c) : mword 64) 2 = mword_of_int (SS + 0x2e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2e) in "Hpc".
    (* +0x2e auipc s2,0x1e *)
    iApply (wp_auipc_s_sconf (mword_of_int (SS + 0x2e)) Rs2
              (mword_of_int 30 : mword 20) M (trap_res eb + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (Y1 := <[Regidx Rs2 := regval_into_reg
        (add_vec (mword_of_int (SS + 0x2e) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> M).
    change (<[Regidx Rs2 := regval_into_reg
        (add_vec (mword_of_int (SS + 0x2e) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> M) with Y1.
    assert (Hp32 : add_vec_int (mword_of_int (SS + 0x2e) : mword 64) 4 = mword_of_int (SS + 0x32))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp32) in "Hpc".
    assert (HY1s2 : Y1 !!! Regidx Rs2
                    = add_vec (mword_of_int (SS + 0x2e) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))
      by (rewrite /Y1; apply upd_eq).
    (* +0x32 lw s2,1256(s2) : s2 := log.ncommit *)
    iDestruct (ss_cells with "Hres") as (out cmt nc) "(%Hout3 & Hout & Hcmt & Hnc & Hclose)".
    assert (Hnca : add_vec (rget Y1 Rs2) (sign_extend' 64 (mword_of_int 1272 : mword 12)) = l_ncommit).
    { rgne. rewrite HY1s2. exact ss_reloc_nc_2e. }
    iEval (rewrite -Hnca) in "Hnc".
    iApply (wp_lw_s_sconf (kt := kt) (ktd := KT0) (mword_of_int (SS + 0x32)) Rs2 Rs2
              (mword_of_int 1272 : mword 12) Y1 (trap_res eb + (K - 4))%nat nc false
              (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi32 Hnc").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hnc".
    iEval (rewrite Hnca) in "Hnc".
    iDestruct ("Hclose" with "Hout Hcmt Hnc") as "Hres".
    set (Y2 := <[Regidx Rs2 := regval_into_reg (sign_extend' 64 nc)]> Y1).
    change (<[Regidx Rs2 := regval_into_reg (sign_extend' 64 nc)]> Y1) with Y2.
    assert (Hp36 : add_vec_int (mword_of_int (SS + 0x32) : mword 64) 4 = mword_of_int (SS + 0x36))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp36) in "Hpc".
    (* +0x36 auipc s1,0x1e *)
    iApply (wp_auipc_s_sconf (mword_of_int (SS + 0x36)) Rs1
              (mword_of_int 30 : mword 20) Y2 (trap_res eb + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi36").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (Y3 := <[Regidx Rs1 := regval_into_reg
        (add_vec (mword_of_int (SS + 0x36) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> Y2).
    change (<[Regidx Rs1 := regval_into_reg
        (add_vec (mword_of_int (SS + 0x36) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> Y2) with Y3.
    assert (Hp3a : add_vec_int (mword_of_int (SS + 0x36) : mword 64) 4 = mword_of_int (SS + 0x3a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp3a) in "Hpc".
    (* +0x3a addi s1,s1,1208 *)
    iApply (wp_addi4_s_sconf (mword_of_int (SS + 0x3a)) Rs1 Rs1
              (mword_of_int 1224 : mword 12) Y3 (trap_res eb + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3a").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (Y4 := <[Regidx Rs1 := regval_into_reg
        (add_vec (Y3 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 1224 : mword 12)))]> Y3).
    change (<[Regidx Rs1 := regval_into_reg
        (add_vec (Y3 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 1224 : mword 12)))]> Y3) with Y4.
    assert (Hp3e : add_vec_int (mword_of_int (SS + 0x3a) : mword 64) 4 = mword_of_int (SS + 0x3e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp3e) in "Hpc".
    assert (HssY4 : ss_regs m Y4 spd).
    { split; [| split].
      - rewrite /Y4 upd_eq /Y3 upd_eq. exact ss_reloc_s1_36.
      - rewrite /Y4 upd_ne; [| reg_neq]. rewrite /Y3 upd_ne; [| reg_neq].
        rewrite /Y2 upd_ne; [| reg_neq]. rewrite /Y1 upd_ne; [| reg_neq]. exact Hsp.
      - destruct Hsv as (P19&P20&P21&P22&P23&P24&P25&P26&P27).
        repeat split;
          (rewrite /Y4 upd_ne; [| reg_neq]; rewrite /Y3 upd_ne; [| reg_neq];
           rewrite /Y2 upd_ne; [| reg_neq]; rewrite /Y1 upd_ne; [| reg_neq]);
          first [ exact P19 | exact P20 | exact P21 | exact P22 | exact P23
                | exact P24 | exact P25 | exact P26 | exact P27 ]. }
    rewrite /ss_loop.
    iSpecialize ("Hloop" $! CID with "[%]"); [wp_next_chain|].
    iApply ("Hloop" $! Y4 with "[%] Hr24 Hr16 Hr8 Hr0 Htok Hres Hown Htc Hclm Hcg Hpc Hexit").
    exact HssY4.
  Qed.

End SsBodies.

(* ===================================================================== *)

Section ProofSysSync.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ,
            !fsLogG Σ, !logG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Context {kt : ktier}.
  Lemma wp_sys_sync_sconf
      (γs : list gname) (j : nat) (γl : gname)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
    : wp_sys_sync_sconf_body kt γs j γl bn γ γfs cov logstart dev m K eb b lks.
  Proof.
    cbv beta delta [wp_sys_sync_sconf_body].
    intros pcE pj ret_tgt HK Hj Hjl Hbelow.
    set (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iIntros "Hcg Hown Hextc Hextm #Htext Hpc #Hlog #Hpinv Hcont".
    iPoseProof "Hlog" as "#Hlogc".
    iDestruct "Hlogc" as "(#Hislock & #Hldev & #Hlstart)".
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hbm.
    subst b.
    iPoseProof (ssi_00 with "Htext") as "Hi00".
    iPoseProof (ssi_02 with "Htext") as "Hi02".
    iPoseProof (ssi_04 with "Htext") as "Hi04".
    iPoseProof (ssi_06 with "Htext") as "Hi06".
    iPoseProof (ssi_08 with "Htext") as "Hi08".
    iPoseProof (ssi_0c with "Htext") as "Hi0c".
    iPoseProof (ssi_10 with "Htext") as "Hi10".
    (* ===================== PROLOGUE: 4-slot frame, ra/s0 saved ========== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hspd : add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = spd)
      by reflexivity.
    assert (Hsp0 : sp0 = m !!! Regidx csp_rs1) by reflexivity.
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m K 4 eb
              ltac:(pose proof (ss_K4 K HK); lia) Hpush
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spd) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite (stack_own_slots (KTR := kt)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (vr24) "Hr24". iDestruct "S2" as (vr16) "Hr16".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HspR1. rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HspR1. rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    assert (Hp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (SS + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    (* +0x02 c.sdsp ra,24(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (SS + 0x02)) (mword_of_int 3 : mword 6) Rra
              R1 (K - 4)%nat vr24 eb with "Hcg Hpc Hi02 Hr24").
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    iEval (rgne) in "Hr24".
    assert (Hp04 : add_vec_int (mword_of_int (SS + 0x02) : mword 64) 2 = mword_of_int (SS + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    (* +0x04 c.sdsp s0,16(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (SS + 0x04)) (mword_of_int 2 : mword 6) Rs0
              R1 (K - 4)%nat vr16 eb with "Hcg Hpc Hi04 Hr16").
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    iEval (rgne) in "Hr16".
    assert (Hp06 : add_vec_int (mword_of_int (SS + 0x04) : mword 64) 2 = mword_of_int (SS + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    iEval (rewrite Hb1) in "Hr24". iEval (rewrite Hb2) in "Hr16".
    assert (Hr1v : R1 !!! Regidx Rra = m !!! Regidx Rra)
      by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (Hr8v : R1 !!! Regidx Rs0 = m !!! Regidx Rs0)
      by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite Hr1v) in "Hr24". iEval (rewrite Hr8v) in "Hr16".
    (* +0x06 c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (SS + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8)
              Rs0 R1 (K - 4)%nat eb
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06").
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
        (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    change (<[Regidx Rs0 := regval_into_reg
        (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1) with R2.
    assert (Hp08 : add_vec_int (mword_of_int (SS + 0x06) : mword 64) 2 = mword_of_int (SS + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    (* +0x08 auipc a0,0x1e ; +0x0c addi a0,a0,1254 : a0 := &log *)
    iApply (wp_auipc_s_sconf (mword_of_int (SS + 0x08)) Ra0
              (mword_of_int 30 : mword 20) R2 (K - 4)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (R3 := <[Regidx Ra0 := regval_into_reg
        (add_vec (mword_of_int (SS + 0x08) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> R2).
    change (<[Regidx Ra0 := regval_into_reg
        (add_vec (mword_of_int (SS + 0x08) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> R2) with R3.
    assert (Hp0c : add_vec_int (mword_of_int (SS + 0x08) : mword 64) 4 = mword_of_int (SS + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0c) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (SS + 0x0c)) Ra0 Ra0
              (mword_of_int 1270 : mword 12) R3 (K - 4)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c").
    iIntros (CID6 Hs6) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R4 := <[Regidx Ra0 := regval_into_reg
        (add_vec (R3 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 1270 : mword 12)))]> R3).
    change (<[Regidx Ra0 := regval_into_reg
        (add_vec (R3 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 1270 : mword 12)))]> R3) with R4.
    assert (Hp10 : add_vec_int (mword_of_int (SS + 0x0c) : mword 64) 4 = mword_of_int (SS + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    assert (HR4a0 : R4 !!! Regidx Ra0 = log_addr).
    { rewrite /R4 upd_eq /R3 upd_eq. exact ss_reloc_a0_08. }
    (* +0x10 jal ra,acquire *)
    iApply (wp_jal_s_sconf (mword_of_int (SS + 0x10)) Rra
              (mword_of_int 2084128 : mword 21) R4 (K - 4)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi10").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (Maq := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (SS + 0x10) : mword 64) 4)]> R4).
    change (<[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (SS + 0x10) : mword 64) 4)]> R4) with Maq.
    assert (Hjaq : add_vec (mword_of_int (SS + 0x10) : mword 64)
                     (sign_extend' 64 (mword_of_int 2084128 : mword 21))
                   = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjaq) in "Hpc".
    assert (HMaqa0 : Maq !!! Regidx Ra0 = log_addr)
      by (rewrite /Maq upd_ne; [exact HR4a0 | reg_neq]).
    assert (HMaqra : Maq !!! Regidx Rra = add_vec_int (mword_of_int (SS + 0x10) : mword 64) 4)
      by (rewrite /Maq; apply upd_eq).
    assert (HMaqcsp : Maq !!! Regidx csp_rs1 = spd).
    { rewrite /Maq upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq].
      rewrite /R3 upd_ne; [| reg_neq]. rewrite /R2 upd_ne; [| reg_neq]. exact HspR1. }
    assert (Hpro_cs : forall c : mword 5,
              c <> csp_rs1 -> c <> Rs0 -> c <> Ra0 -> c <> Rra ->
              Maq !!! Regidx c = m !!! Regidx c).
    { intros c N2 N8 N10 N1.
      rewrite /Maq upd_ne; [| congruence]. rewrite /R4 upd_ne; [| congruence].
      rewrite /R3 upd_ne; [| congruence]. rewrite /R2 upd_ne; [| congruence].
      rewrite /R1 upd_ne; [reflexivity | congruence]. }
    (* ===================== acquire(&log.lock) ===================== *)
    iDestruct (cpu_own_transport CID CID7 0 eb pj eb ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (Acquire.wp_acquire_sconf kt (ln_lk γ) "log"%string (log_res γ bn γfs cov logstart) Maq
              0%nat eb pj (K - 4)%nat eb lks
              ss_noff1 ltac:(pose proof (ss_K10 K HK); lia) Hbelow
              with "Hcg Hown Htext Hpc []").
    all: try lkbelow.
    { iEval (rewrite HMaqa0). iExact "Hislock". }
    iIntros (CIDa Hsa ms Macq) "%Hmsf Hcg Hpc %Hcsacq Htok Hres Hown Hpay".
    iDestruct (trap_csrs_ext_transport CID CIDa eb pj ltac:(wp_next_chain)
                 with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID CIDa eb pj ltac:(wp_next_chain)
                 with "Hextm") as "Hextm".
    iDestruct (arm_pay_ext_join eb _ with "Hpay [$Hextc $Hextm]") as "[Htc Hclm]".
    assert (Hpc14 : ret_pc (Maq !!! Regidx Rra) = mword_of_int (SS + 0x14))
      by (rewrite HMaqra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    assert (Hacq_csp : Macq !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hcsacq csp_rs1 ltac:(vm_compute; reflexivity)). exact HMaqcsp. }
    assert (Hacq_rest : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Ra0 -> c <> Rra ->
              Macq !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N10 N1.
      rewrite (callee_saved_lookup Hcsacq c Hcs). exact (Hpro_cs c N2 N8 N10 N1). }
    assert (HssAcq : ss_regs0 m Macq spd).
    { unfold ss_regs0, ss_saved. repeat split;
        first [ exact Hacq_csp
              | apply Hacq_rest; [vm_compute; reflexivity | reg_neq..] ]. }
    (* ============ the anchored TAIL and the Löb-closed WAIT LOOP ========= *)
    iAssert (ss_exit CID j γ bn γfs cov logstart m K eb lks spd sp0) with "[Hcont]" as "Hexit".
    { rewrite /ss_exit.
      iIntros (CIDx Hsx Mx) "%HssE Hr24 Hr16 Hr8 Hr0 Htok Hres Hown Htc Hclm Hcg Hpc".
      iApply (ss_tail_body (CID := CIDx) CID j γ bn γfs cov logstart dev m Mx K eb lks spd sp0
                HK Hsx Hspd Hsp0 HssE Hbelow
                with "Htext Hlog Hr24 Hr16 Hr8 Hr0 Htok Hres Hown Htc Hclm Hcg Hpc Hcont"). }
    iAssert (ss_loop CID j γ bn γfs cov logstart m K eb lks spd sp0) with "[]" as "Hloop".
    { iLöb as "IH". rewrite /ss_loop.
      iIntros (CIDy Hsy My) "%HssL Hr24 Hr16 Hr8 Hr0 Htok Hres Hown Htc Hclm Hcg Hpc Hexit".
      iApply (ss_loop_body (CID := CIDy) CID γs j γl γ bn γfs cov logstart dev m My K eb lks spd sp0
                HK Hj Hjl Hsy Hspd HssL Hbelow
                with "Htext Hlog Hpinv IH Hexit Hr24 Hr16 Hr8 Hr0 Htok Hres Hown Htc Hclm Hcg Hpc"). }
    (* ============ +0x14..+0x26: the two-part guard ============ *)
    iPoseProof (ssi_14 with "Htext") as "Hi14".
    iPoseProof (ssi_18 with "Htext") as "Hi18".
    iPoseProof (ssi_1c with "Htext") as "Hi1c".
    iPoseProof (ssi_1e with "Htext") as "Hi1e".
    iPoseProof (ssi_22 with "Htext") as "Hi22".
    iPoseProof (ssi_26 with "Htext") as "Hi26".
    iDestruct (ss_cells with "Hres") as (out cmt nc) "(%Hout3 & Hout & Hcmt & Hnc & Hclose)".
    (* +0x14 auipc a5,0x1e *)
    iApply (wp_auipc_s_sconf (mword_of_int (SS + 0x14)) Ra5
              (mword_of_int 30 : mword 20) Macq (trap_res eb + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (G1 := <[Regidx Ra5 := regval_into_reg
        (add_vec (mword_of_int (SS + 0x14) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> Macq).
    change (<[Regidx Ra5 := regval_into_reg
        (add_vec (mword_of_int (SS + 0x14) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> Macq) with G1.
    assert (HG1a5 : G1 !!! Regidx Ra5
                    = add_vec (mword_of_int (SS + 0x14) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))
      by (rewrite /G1; apply upd_eq).
    assert (Hp18 : add_vec_int (mword_of_int (SS + 0x14) : mword 64) 4 = mword_of_int (SS + 0x18))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp18) in "Hpc".
    (* +0x18 lw a5,1274(a5) : a5 := log.committing *)
    assert (Hcmta : add_vec (rget G1 Ra5) (sign_extend' 64 (mword_of_int 1290 : mword 12)) = l_cmt).
    { rgne. rewrite HG1a5. exact ss_reloc_cmt_14. }
    iEval (rewrite -Hcmta) in "Hcmt".
    iApply (wp_lw_s_sconf (kt := kt) (ktd := KT0) (mword_of_int (SS + 0x18)) Ra5 Ra5
              (mword_of_int 1290 : mword 12) G1 (trap_res eb + (K - 4))%nat
              (mword_of_int (if cmt then 1 else 0) : mword 32) false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18 Hcmt").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hcmt".
    iEval (rewrite Hcmta) in "Hcmt".
    set (G2 := <[Regidx Ra5 := regval_into_reg
        (sign_extend' 64 (mword_of_int (if cmt then 1 else 0) : mword 32))]> G1).
    change (<[Regidx Ra5 := regval_into_reg
        (sign_extend' 64 (mword_of_int (if cmt then 1 else 0) : mword 32))]> G1) with G2.
    assert (HG2a5 : G2 !!! Regidx Ra5
                    = sign_extend' 64 (mword_of_int (if cmt then 1 else 0) : mword 32))
      by (rewrite /G2; apply upd_eq).
    assert (Hp1c : add_vec_int (mword_of_int (SS + 0x18) : mword 64) 4 = mword_of_int (SS + 0x1c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1c) in "Hpc".
    assert (HssG2 : ss_regs0 m G2 spd).
    { apply (ss_regs0_cs m Macq G2 spd); [| exact HssAcq].
      rewrite /G2 /G1.
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_refl. }
    (* +0x1c c.bnez a5 -> +0x2a *)
    assert (Htgt2a : add_vec (mword_of_int (SS + 0x1c) : mword 64)
                       (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 7 : mword 8) ('b"0"))))
                     = mword_of_int (SS + 0x2a))
      by (apply bv_eq; vm_compute; reflexivity).
    destruct cmt.
    - (* ============== COMMITTING: straight to the spill block ============ *)
      iDestruct ("Hclose" with "Hout Hcmt Hnc") as "Hres".
      iApply (wp_cbnez_taken_s_sconf (mword_of_int (SS + 0x1c)) (mword_of_int 7 : mword 8)
                (Cregidx (mword_of_int 7)) Ra5 G2 (trap_res eb + (K - 4))%nat false
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HG2a5; exact (ss_cmt_nz true))
                ltac:(rewrite Htgt2a; vm_compute; reflexivity)
                with "Hcg Hpc Hi1c").
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt2a) in "Hpc".
      iApply (ss_entry_body (CID := CIDa) CID j γ bn γfs cov logstart m G2 K eb lks spd sp0
                HK ltac:(wp_next_chain) Hspd HssG2
                with "Htext Hloop Hexit Hr24 Hr16 [S3] [S4] Htok Hres Hown Htc Hclm Hcg Hpc").
      { iExact "S3". }
      { iExact "S4". }
    - (* ============== NOT COMMITTING: test [outstanding] ================= *)
      iApply (wp_cbnez_fall_s_sconf (mword_of_int (SS + 0x1c)) (mword_of_int 7 : mword 8)
                (Cregidx (mword_of_int 7)) Ra5 G2 (trap_res eb + (K - 4))%nat false
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HG2a5; exact (ss_cmt_nz false))
                with "Hcg Hpc Hi1c").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hp1e : add_vec_int (mword_of_int (SS + 0x1c) : mword 64) 2 = mword_of_int (SS + 0x1e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp1e) in "Hpc".
      (* +0x1e auipc a5,0x1e *)
      iApply (wp_auipc_s_sconf (mword_of_int (SS + 0x1e)) Ra5
                (mword_of_int 30 : mword 20) G2 (trap_res eb + (K - 4))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi1e").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (G3 := <[Regidx Ra5 := regval_into_reg
          (add_vec (mword_of_int (SS + 0x1e) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> G2).
      change (<[Regidx Ra5 := regval_into_reg
          (add_vec (mword_of_int (SS + 0x1e) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> G2) with G3.
      assert (HG3a5 : G3 !!! Regidx Ra5
                      = add_vec (mword_of_int (SS + 0x1e) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))
        by (rewrite /G3; apply upd_eq).
      assert (Hp22 : add_vec_int (mword_of_int (SS + 0x1e) : mword 64) 4 = mword_of_int (SS + 0x22))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp22) in "Hpc".
      (* +0x22 lw a5,1260(a5) : a5 := log.outstanding *)
      assert (Houta : add_vec (rget G3 Ra5) (sign_extend' 64 (mword_of_int 1276 : mword 12)) = l_out).
      { rgne. rewrite HG3a5. exact ss_reloc_out_1e. }
      iEval (rewrite -Houta) in "Hout".
      iApply (wp_lw_s_sconf (kt := kt) (ktd := KT0) (mword_of_int (SS + 0x22)) Ra5 Ra5
                (mword_of_int 1276 : mword 12) G3 (trap_res eb + (K - 4))%nat
                (mword_of_int (Z.of_nat out) : mword 32) false (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi22 Hout").
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hout".
      iEval (rewrite Houta) in "Hout".
      iDestruct ("Hclose" with "Hout Hcmt Hnc") as "Hres".
      set (G4 := <[Regidx Ra5 := regval_into_reg
          (sign_extend' 64 (mword_of_int (Z.of_nat out) : mword 32))]> G3).
      change (<[Regidx Ra5 := regval_into_reg
          (sign_extend' 64 (mword_of_int (Z.of_nat out) : mword 32))]> G3) with G4.
      assert (HG4a5 : G4 !!! Regidx Ra5
                      = sign_extend' 64 (mword_of_int (Z.of_nat out) : mword 32))
        by (rewrite /G4; apply upd_eq).
      assert (Hp26 : add_vec_int (mword_of_int (SS + 0x22) : mword 64) 4 = mword_of_int (SS + 0x26))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp26) in "Hpc".
      assert (HssG4 : ss_regs0 m G4 spd).
      { apply (ss_regs0_cs m G2 G4 spd); [| exact HssG2].
        rewrite /G4 /G3.
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_refl. }
      (* +0x26 bge zero,a5 -> +0x5e (the log is idle: nothing to wait for) *)
      assert (Htgt5e : add_vec (mword_of_int (SS + 0x26) : mword 64)
                         (sign_extend' 64 (mword_of_int 56 : mword 13))
                       = mword_of_int (SS + 0x5e))
        by (apply bv_eq; vm_compute; reflexivity).
      destruct (Z.geb 0 (Z.of_nat out)) eqn:Hgb.
      + (* ---- FAST PATH: no operation is open, and none is committing ---- *)
        iApply (wp_bge_x0_taken_s_sconf (mword_of_int (SS + 0x26)) (mword_of_int 56 : mword 13)
                  Ra5 G4 (trap_res eb + (K - 4))%nat false
                  ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite HG4a5; rewrite (ss_out_cmp out Hout3); exact Hgb)
                  ltac:(rewrite Htgt5e; vm_compute; reflexivity)
                  with "Hcg Hpc Hi26").
        iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htgt5e) in "Hpc".
        rewrite /ss_exit.
        iSpecialize ("Hexit" $! CIDa with "[%]"); [wp_next_chain|].
        iApply ("Hexit" $! G4 with "[%] Hr24 Hr16 [S3] [S4] Htok Hres Hown Htc Hclm Hcg Hpc").
        { exact HssG4. }
        { iExact "S3". }
        { iExact "S4". }
      + (* ---- SOMETHING IS PENDING: fall into the spill block ---- *)
        iApply (wp_bge_x0_fall_s_sconf (mword_of_int (SS + 0x26)) (mword_of_int 56 : mword 13)
                  Ra5 G4 (trap_res eb + (K - 4))%nat false
                  ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite HG4a5; rewrite (ss_out_cmp out Hout3); exact Hgb)
                  with "Hcg Hpc Hi26").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hp2a : add_vec_int (mword_of_int (SS + 0x26) : mword 64) 4 = mword_of_int (SS + 0x2a))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp2a) in "Hpc".
        iApply (ss_entry_body (CID := CIDa) CID j γ bn γfs cov logstart m G4 K eb lks spd sp0
                  HK ltac:(wp_next_chain) Hspd HssG4
                  with "Htext Hloop Hexit Hr24 Hr16 [S3] [S4] Htok Hres Hown Htc Hclm Hcg Hpc").
        { iExact "S3". }
        { iExact "S4". }
  Qed.

End ProofSysSync.

End SysSyncProof.
