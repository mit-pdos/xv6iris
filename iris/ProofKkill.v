(* ProofKkill.v -- whole-function WP for kkill() (xv6's kill()).

     int kkill(int pid) {
       if (pid == 0) return -1;
       for (p = proc; p < &proc[NPROC]; p++) {
         acquire(&p->lock);
         if (p->pid == pid) {
           p->killed = 1;
           if (p->state == SLEEPING) p->state = RUNNABLE;
           release(&p->lock); return 0;
         }
         release(&p->lock);
       }
       return -1;
     }

   Forty-three instructions @ 0x80002194; a 48-byte ra/s0/s1/s2/s3 frame
   (slot 0 padding), and structurally wakeup's scan: a bounded fuel
   induction over proc[], acquiring and releasing each slot in turn, with
   the counting token [intr_count] NET-ZERO across every pair.

   The [pid == 0] guard is outside the frame: [+0x00 c.beqz a0,+0x68] ahead
   of the prologue and [+0x68 c.li a0,-1 ; +0x6a c.ret] after the epilogue,
   so it needs no stack, no lock and no invariant.

   EXPLICIT-CPUID NOTE (same as ProofWakeup).  Outside the lock-held stretch
   a trap may migrate the thread, so the loop invariant is a
   [wp_next b (fun CID => ...)] and the two propositions that carry a hart
   -- the loop head (+0x22) and the exit continuation (+0x54) -- are
   ANCHORED at the lemma's own [CID0].  From acquire's return (+0x28) to the
   release call the index is the literal [false] (a held lock pins
   noff >= 1), so that whole stretch stays at one hart and its leaves
   collapse with [wp_next_off_intro].

   WHAT THE LOOP BODY TOUCHES, AND WHY IT IS CHEAP.  Everything kkill reads
   or writes is at the TOP LEVEL of [proc_lock_res]: [p->pid] is the
   invariant's permanent half of the cell, [p->killed] is [proc_pub]'s
   existentially-quantified flag (so the store needs no premise), and
   SLEEPING -> RUNNABLE is [SchedCtx.proc_lock_res_wakeup] -- both guards'
   booleans are fixed across that transition, so neither [proc_slots] slot
   is ever opened. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import RiscvExtras.
Require Import InstrBytes KernelText.
Require Import StackOwn CalleeSaved.
Require Import WpMmodeLeafBase.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSmodeIntr.
Require Import IntrDefs WpNext.
Require Import CpuOwn.
Require Import WpLock.
Require Import ProcGeom.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import SchedCtx.
Require Import SpecAcquire SpecRelease.
Require Import SpecKkill.
From Kernel Require KernelInstrs KernelSyms.
Require Import CodeKkill.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import CtxIdDefs.
Import Defs.
Local Open Scope Z_scope.
(* a failing tactic in a whole-function WP over the proc invariant otherwise
   spends tens of minutes FORMATTING the goal -- see durable-notes. *)
Set Printing Depth 40.

(* ------------------------------------------------------------------ *)
(* Pure helpers.  Stated with only [mword]/[Z] in scope, per the zify   *)
(* rule in durable-notes.                                               *)
(* ------------------------------------------------------------------ *)

Lemma kk_eq_vec_refl {n} (x : mword n) : eq_vec x x = true.
Proof. apply eq_vec_true_iff. reflexivity. Qed.

(* a state cell whose 64-bit sign extension is 2 is SLEEPING *)
Lemma kk_sext_sleeping (st : mword 32) :
  sign_extend' 64 st = (mword_of_int 2 : mword 64) -> st = SLEEPING.
Proof.
  intro H.
  assert (Ht : trunc32 (sign_extend' 64 st) = trunc32 (mword_of_int 2 : mword 64))
    by (rewrite H; reflexivity).
  rewrite trunc32_sext64 in Ht. rewrite Ht. apply bv_eq; vm_compute; reflexivity.
Qed.

(* the three field displacements the loop body uses *)
Lemma kk_pid_off (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 48 : mword 12)) = p_pid X.
Proof. reflexivity. Qed.

Lemma kk_killed_off (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 40 : mword 12)) = p_killed X.
Proof. rewrite /p_killed. f_equal; apply bv_eq; vm_compute; reflexivity. Qed.

Lemma kk_state_off (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 24 : mword 12)) = p_state X.
Proof. rewrite /p_state /state_off. f_equal; apply bv_eq; vm_compute; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The register invariants.  [kk_cs_rest] is the callee-saved registers  *)
(* kkill neither saves nor uses -- s4..s11 -- stated as ONE predicate     *)
(* rather than eight equalities: the loop threads it through both calls   *)
(* with [callee_saved_lookup] and the epilogue cashes it in for the       *)
(* eight matching conjuncts of the final [callee_saved].  Spelled with    *)
(* [csp_rs1] (not [mword_of_int 2]), per durable-notes: [congruence]      *)
(* cannot bridge the two.                                                 *)
(* ------------------------------------------------------------------ *)

Definition kk_cs_rest (M mb : regfile) : Prop :=
  forall r : mword 5, is_cs_idx r = true ->
    r <> csp_rs1 -> r <> mword_of_int 8 -> r <> mword_of_int 9 ->
    r <> mword_of_int 18 -> r <> mword_of_int 19 ->
    M !!! Regidx r = mb !!! Regidx r.

Lemma kk_cs_rest_cs (M M' mb : regfile) :
  callee_saved M M' -> kk_cs_rest M mb -> kk_cs_rest M' mb.
Proof.
  intros Hcs H r Hr N2 N8 N9 N18 N19.
  rewrite (callee_saved_lookup Hcs r Hr). by apply H.
Qed.

(* an insert at a NON-callee-saved register (a0/a4/a5/ra) *)
Lemma kk_cs_rest_ncs (M mb : regfile) (rr : mword 5) (v : mword 64) :
  is_cs_idx rr = false -> kk_cs_rest M mb -> kk_cs_rest (<[Regidx rr := v]> M) mb.
Proof.
  intros Hn H r Hr N2 N8 N9 N18 N19.
  rewrite upd_ne; [by apply H |].
  intro He. apply (is_cs_idx_true_neq rr r Hn Hr). by symmetry.
Qed.

(* ... and at each of the five registers that ARE callee-saved but are
   excluded by the predicate's own premises: sp, s0, s1, s2, s3. *)
Lemma kk_cs_rest_sp (M mb : regfile) (v : mword 64) :
  kk_cs_rest M mb -> kk_cs_rest (<[Regidx csp_rs1 := v]> M) mb.
Proof. intros H r Hr N2 N8 N9 N18 N19. rewrite upd_ne; [by apply H | congruence]. Qed.
Lemma kk_cs_rest_s0 (M mb : regfile) (v : mword 64) :
  kk_cs_rest M mb -> kk_cs_rest (<[Regidx (mword_of_int 8 : mword 5) := v]> M) mb.
Proof. intros H r Hr N2 N8 N9 N18 N19. rewrite upd_ne; [by apply H | congruence]. Qed.
Lemma kk_cs_rest_s1 (M mb : regfile) (v : mword 64) :
  kk_cs_rest M mb -> kk_cs_rest (<[Regidx (mword_of_int 9 : mword 5) := v]> M) mb.
Proof. intros H r Hr N2 N8 N9 N18 N19. rewrite upd_ne; [by apply H | congruence]. Qed.
Lemma kk_cs_rest_s2 (M mb : regfile) (v : mword 64) :
  kk_cs_rest M mb -> kk_cs_rest (<[Regidx (mword_of_int 18 : mword 5) := v]> M) mb.
Proof. intros H r Hr N2 N8 N9 N18 N19. rewrite upd_ne; [by apply H | congruence]. Qed.
Lemma kk_cs_rest_s3 (M mb : regfile) (v : mword 64) :
  kk_cs_rest M mb -> kk_cs_rest (<[Regidx (mword_of_int 19 : mword 5) := v]> M) mb.
Proof. intros H r Hr N2 N8 N9 N18 N19. rewrite upd_ne; [by apply H | congruence]. Qed.

(* the loop head's register state at iteration [k] *)
Definition kkl_regs (M mb : regfile) (spd pidv : mword 64) (k : nat) : Prop :=
  M !!! Regidx (mword_of_int 9 : mword 5) = proc_addr k /\
  M !!! Regidx csp_rs1 = spd /\
  M !!! Regidx (mword_of_int 18 : mword 5) = pidv /\
  M !!! Regidx (mword_of_int 19 : mword 5) = proc_addr NPROC /\
  kk_cs_rest M mb.

(* ... and the epilogue's, which is all the return path needs to know *)
Definition kk_exit_regs (M mb : regfile) (spd rv : mword 64) : Prop :=
  M !!! Regidx csp_rs1 = spd /\
  M !!! Regidx (mword_of_int 10 : mword 5) = rv /\
  (rv = (zero_reg : mword 64) \/ rv = mword_of_int (-1)) /\
  kk_cs_rest M mb.


Module KkillProof (Acquire : ACQUIRE) (Release : RELEASE) : KKILL.

Section ProofKkill.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ, !fileG Σ}.
  (* NO section [CpuId]: the loop lemma is applied at the hart the prologue
     hands back, which a section variable could not express. *)

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).

  (* ================================================================== *)
  (* The scan, +0x22 .. +0x54.                                          *)
  (* ================================================================== *)
  Lemma wp_kkill_loop `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
       (γs : list gname) (mb : regfile)
      (spd pidv pme : mword 64) (lvl av : nat) (eb : bool) (b : bool) (lks : gset string) :
    (* THE C's OWN GUARD, RELAYED (XV6_REV 64c58ba): kkill returns -1 for
       pid 0 before the scan starts, so every slot this loop can match has
       a NONZERO pid -- which is what lets the write re-close
       [SchedCtx.kill_paid] on its live arm ([kill_paid_kill]'s side
       condition; the free arm's [⌜kl = 0⌝] is an invariant exactly because
       no writer reaches a free slot). *)
    pidv <> (zero_reg : mword 64) ->
    length γs = NPROC ->
    (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
    (10 <= av)%nat ->
    (* the scan enters each slot fresh: the caller's held set must bound
       below "proc"'s rank (LockRank.v); [locks_below_not_elem] gives the
       per-slot non-membership the ghost step needs. *)
    locks_below lks "proc" ->
    (* THE KILL CREDENTIAL (lane KILL-PAY, K2): the scan is what writes
       [p->killed = 1], so the price is charged here as well as at the
       entry -- [SchedCtx.proc_pub]'s killed row cannot be re-bundled at a
       nonzero flag without it.  Persistent, so the loop carries it into
       every iteration for free. *)
    app_taint -∗
    procs_inv γs -∗
    (* the exit continuation: control at the epilogue entry [kkill+0x54],
       at whatever hart the scan ended on, with a0 = 0 or -1. *)
    wp_next (CID0 := CID0) b pme (fun (CIDq : CpuId) =>
      ∀ (Mx : regfile) (rv : mword 64),
        ⌜ kk_exit_regs Mx mb spd rv ⌝ -∗
        sie_cap_gpr KT1 Mx av b pme -∗
        cpu_own lvl eb pme b lks -∗
        pc_is (mword_of_int (KernelSyms.kkill + 0x54)) -∗
        mWP (Loop : expr riscv_lang)) -∗
    ∀ (k : nat) (M : regfile),
      ⌜(k < NPROC)%nat⌝ -∗ ⌜kkl_regs M mb spd pidv k⌝ -∗
      sie_cap_gpr KT1 M av b pme -∗
      cpu_own lvl eb pme b lks -∗
      kernel_text -∗ pc_is (mword_of_int (KernelSyms.kkill + 0x22)) -∗
      mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hpidnz Hlen Hlvl Hav Hno.
    iIntros "#Hkc #Hpinv Hqexit".
    (* BOUNDED loop: ordinary Coq induction on a [fuel] bounding the
       remaining iterations [NPROC - k].  The exit continuation is a
       PREMISE of the statement (fdalloc's rule), so the IH keeps its
       leading [∀ k M]. *)
    iAssert (∀ (fuel : nat),
               wp_next (CID0 := CID0) b pme (fun (CID : CpuId) =>
                 ∀ (k : nat) (M : regfile),
                   ⌜(NPROC - k <= fuel)%nat⌝ -∗ ⌜(k < NPROC)%nat⌝ -∗
                   ⌜kkl_regs M mb spd pidv k⌝ -∗
                   wp_next (CID0 := CID0) b pme (fun (CIDq : CpuId) =>
                     ∀ (Mx : regfile) (rv : mword 64),
                       ⌜ kk_exit_regs Mx mb spd rv ⌝ -∗
                       sie_cap_gpr KT1 Mx av b pme -∗
                       cpu_own lvl eb pme b lks -∗
                       pc_is (mword_of_int (KernelSyms.kkill + 0x54)) -∗
                       mWP (Loop : expr riscv_lang)) -∗
                   sie_cap_gpr KT1 M av b pme -∗
                   cpu_own lvl eb pme b lks -∗
                   kernel_text -∗ pc_is (mword_of_int (KernelSyms.kkill + 0x22)) -∗
                   mWP (Loop : expr riscv_lang)))%I with "[]" as "Hloop".
    { iIntros (fuel). iInduction fuel as [|fuel IHf] "IHf".
      { iIntros (CIDk Hsk k M) "%Hfuel %Hk %Hregs Hqx Hcg Hown Htext Hpc".
        exfalso. lia. }
      iIntros (CIDk Hsk k M) "%Hfuel %Hk %Hregs Hqx Hcg Hown #Htext Hpc".
      destruct Hregs as (Hm9 & Hmsp & Hm18 & Hm19 & Hmcs).
      iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hbmatch. symmetry in Hbmatch.
      destruct (lookup_lt_is_Some_2 γs k ltac:(rewrite Hlen; exact Hk)) as [γk Hγk].
      iDestruct (procs_inv_lookup γs k γk Hγk with "Hpinv") as "#Hlockk".
      (* ---- +0x22 c.mv a0,s1 ---- *)
      assert (Hrg22 : rget (CID := CIDk) M Rs1 = M !!! Regidx Rs1) by (rgne; reflexivity).
      iApply (wp_cmv_s_sconf (CID := CIDk) (mword_of_int (KernelSyms.kkill + 0x22)) Ra0 Rs1
                M av b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (kki_22 with "Htext"). }
      iIntros (CIDa Hsa) "Hcg Hpc".
      iEval (rewrite Hrg22) in "Hcg".
      set (M22 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M !!! Regidx Rs1))]> M).
      change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M !!! Regidx Rs1))]> M) with M22.
      assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.kkill + 0x22) : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x24))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp24) in "Hpc".
      (* ---- +0x24 jal ra,acquire ---- *)
      iApply (wp_jal_s_sconf (CID := CIDa) (mword_of_int (KernelSyms.kkill + 0x24)) Rra
                (mword_of_int 2091666 : mword 21) M22 av b
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (kki_24 with "Htext"). }
      iIntros (CIDb Hsb) "Hcg Hpc".
      set (M24 := <[Regidx Rra := regval_into_reg
                     (add_vec_int (mword_of_int (KernelSyms.kkill + 0x24) : mword 64) 4)]> M22).
      change (<[Regidx Rra := regval_into_reg
                 (add_vec_int (mword_of_int (KernelSyms.kkill + 0x24) : mword 64) 4)]> M22) with M24.
      assert (Hjacq : add_vec (mword_of_int (KernelSyms.kkill + 0x24) : mword 64)
                        (sign_extend' 64 (mword_of_int 2091666 : mword 21)) = mword_of_int KernelSyms.acquire)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjacq) in "Hpc".
      assert (HM24ra : M24 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.kkill + 0x24) : mword 64) 4)
        by (rewrite /M24; apply upd_eq).
      assert (HM24a0 : M24 !!! Regidx Ra0 = proc_addr k).
      { rewrite /M24 upd_ne; [| vm_compute; discriminate].
        rewrite /M22 upd_eq add_vec_zero_l. exact Hm9. }
      assert (HcsM24 : callee_saved M M24).
      { rewrite /M24. apply callee_saved_insert_r; [vm_compute; reflexivity |].
        rewrite /M22. apply callee_saved_insert_r; [vm_compute; reflexivity | apply callee_saved_refl]. }
      (* ---- acquire(&p->lock) ---- *)
      iDestruct (cpu_own_transport CIDk CIDb lvl eb pme b ltac:(wp_next_chain)
                   with "Hown") as "Hown".
      iApply (Acquire.wp_acquire_sconf KT1 (CID := CIDb) γk "proc"%string (proc_lock_pay γs γk (proc_addr k)) M24 lvl eb pme av b lks
                ltac:(lia) ltac:(lia) Hno
                with "Hcg Hown Htext Hpc [Hlockk]").
      all: try lkbelow.
      { iEval (rewrite HM24a0). iExact "Hlockk". }
      iIntros (CIDf Hsf ms Macq) "%Hms Hcg Hpc %Hpins Htok HR _ Hown Hpay".
      assert (Hpc28 : ret_pc (M24 !!! Regidx Rra) = mword_of_int (KernelSyms.kkill + 0x28))
        by (rewrite HM24ra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc28) in "Hpc".
      iDestruct (proc_lock_res_elim γs γk (proc_addr k) with "HR")
        as (st ch) "(Hpst & Hpg & Hpch & Hpub & Hslots)".
      iDestruct "Hpub" as (kl xs pidc) "(Hkilled & Hxstate & Hpidhalf & Hrow)".
      (* register facts through acquire *)
      assert (HcsMacq : callee_saved M Macq) by (eapply callee_saved_trans; [exact HcsM24 | exact Hpins]).
      assert (HA9 : Macq !!! Regidx Rs1 = proc_addr k)
        by (rewrite (callee_saved_lookup HcsMacq Rs1 ltac:(vm_compute; reflexivity)); exact Hm9).
      assert (HAsp : Macq !!! Regidx csp_rs1 = spd)
        by (rewrite (callee_saved_lookup HcsMacq csp_rs1 ltac:(vm_compute; reflexivity)); exact Hmsp).
      assert (HA18 : Macq !!! Regidx Rs2 = pidv)
        by (rewrite (callee_saved_lookup HcsMacq Rs2 ltac:(vm_compute; reflexivity)); exact Hm18).
      assert (HA19 : Macq !!! Regidx Rs3 = proc_addr NPROC)
        by (rewrite (callee_saved_lookup HcsMacq Rs3 ltac:(vm_compute; reflexivity)); exact Hm19).
      assert (HAcs : kk_cs_rest Macq mb) by (eapply kk_cs_rest_cs; [exact HcsMacq | exact Hmcs]).
      (* ---- +0x28 c.lw a5,48(s1) : a5 := p->pid ---- *)
      assert (Hea28 : add_vec (rget (CID := CIDf) Macq Rs1)
                        (sign_extend' 64 (mword_of_int 48 : mword 12)) = p_pid (proc_addr k)).
      { rewrite (rget_ne (CID := CIDf) Macq Rs1 ltac:(vm_compute; discriminate)) HA9.
        apply kk_pid_off. }
      iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (CID := CIDf) (mword_of_int (KernelSyms.kkill + 0x28)) Ra5 Rs1
                (mword_of_int 48 : mword 12) Macq (trap_res b + av)%nat pidc false (dqm := DfracOwn (1/4))
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hpidhalf]").
      { iApply (kki_28 with "Htext"). }
      { iEval (rewrite Hea28). iExact "Hpidhalf". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hpidhalf". iEval (rewrite Hea28) in "Hpidhalf".
      set (M28 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 pidc)]> Macq).
      change (<[Regidx Ra5 := regval_into_reg (sign_extend' 64 pidc)]> Macq) with M28.
      assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.kkill + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x2a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2a) in "Hpc".
      assert (HB15 : M28 !!! Regidx Ra5 = sign_extend' 64 pidc) by (rewrite /M28; apply upd_eq).
      assert (HB9 : M28 !!! Regidx Rs1 = proc_addr k)
        by (rewrite /M28 upd_ne; [exact HA9 | vm_compute; discriminate]).
      assert (HBsp : M28 !!! Regidx csp_rs1 = spd)
        by (rewrite /M28 upd_ne; [exact HAsp | vm_compute; discriminate]).
      assert (HB18 : M28 !!! Regidx Rs2 = pidv)
        by (rewrite /M28 upd_ne; [exact HA18 | vm_compute; discriminate]).
      assert (HB19 : M28 !!! Regidx Rs3 = proc_addr NPROC)
        by (rewrite /M28 upd_ne; [exact HA19 | vm_compute; discriminate]).
      assert (HBcs : kk_cs_rest M28 mb)
        by (rewrite /M28; apply kk_cs_rest_ncs; [vm_compute; reflexivity | exact HAcs]).
      (* ---- +0x2a beq a5,s2 : does this slot's pid match? ---- *)
      assert (Hrg2a_15 : rget (CID := CIDf) M28 Ra5 = M28 !!! Regidx Ra5) by (rgne; reflexivity).
      assert (Hrg2a_18 : rget (CID := CIDf) M28 Rs2 = M28 !!! Regidx Rs2) by (rgne; reflexivity).
      destruct (eq_vec (M28 !!! Regidx Ra5) (M28 !!! Regidx Rs2)) eqn:Hcmp2a.
      - (* ================= TAKEN: pid matches -> kill it ================= *)
        assert (Hcmp28r : eq_vec (rget (CID := CIDf) M28 Ra5) (rget (CID := CIDf) M28 Rs2) = true)
          by (rewrite Hrg2a_15 Hrg2a_18; exact Hcmp2a).
        (* ...AND THIS SLOT'S PID IS NOT ZERO: the branch matched the
           argument, and the argument is not zero (the C's guard, relayed
           as [Hpidnz]).  It is what re-closes the killed row. *)
        assert (Hpcnz : bv_unsigned pidc <> 0).
        { intro Hz0.
          assert (Hpz : pidc = (mword_of_int 0 : mword 32))
            by (apply bv_eq; rewrite Hz0; vm_compute; reflexivity).
          apply Hpidnz.
          assert (Heqv : M28 !!! Regidx Ra5 = M28 !!! Regidx Rs2)
            by (apply eq_vec_true_iff; exact Hcmp2a).
          rewrite -HB18 -Heqv HB15 Hpz.
          apply bv_eq; vm_compute; reflexivity. }
        iApply (wp_beq_taken_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.kkill + 0x2a))
                  (mword_of_int 22 : mword 13) Rs2 Ra5 M28 (trap_res b + av)%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hcmp28r ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (kki_2a with "Htext"). }
        iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Htgt40 : add_vec (mword_of_int (KernelSyms.kkill + 0x2a) : mword 64)
                           (sign_extend' 64 (mword_of_int 22 : mword 13)) = mword_of_int (KernelSyms.kkill + 0x40))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt40) in "Hpc".
        (* ---- the SHARED release-and-return-0 block at +0x4c, reached from
           both arms of the SLEEPING test.  Stated at the FIXED hart CIDf:
           the whole stretch runs with the lock held, i.e. at index false. ---- *)
        iAssert (∀ (Mr : regfile),
                   ⌜ Mr !!! Regidx Rs1 = proc_addr k /\
                     Mr !!! Regidx csp_rs1 = spd /\
                     kk_cs_rest Mr mb ⌝ -∗
                   sie_cap_gpr KT1 (CID := CIDf) Mr (trap_res b + av)%nat false pme -∗
                   pc_is (CID := CIDf) (mword_of_int (KernelSyms.kkill + 0x4c)) -∗
                   locked γk CIDf -∗ proc_lock_res γs γk (proc_addr k) -∗
                   mWP (LoopE gen_id CIDf : expr riscv_lang))%I
          with "[Hown Hpay Hqx]" as "Hret0".
        { iIntros (Mr) "%Hmr Hcg Hpc Htok HR".
          destruct Hmr as (Hr9 & Hrsp & Hrcs).
          (* +0x4c c.mv a0,s1 *)
          assert (Hrgr9 : rget (CID := CIDf) Mr Rs1 = Mr !!! Regidx Rs1) by (rgne; reflexivity).
          iApply (wp_cmv_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.kkill + 0x4c)) Ra0 Rs1
                    Mr (trap_res b + av)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc []").
          { iApply (kki_4c with "Htext"). }
          iApply wp_next_off_intro. iIntros "Hcg Hpc".
          iEval (rewrite Hrgr9) in "Hcg".
          set (Mr4c := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (Mr !!! Regidx Rs1))]> Mr).
          change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (Mr !!! Regidx Rs1))]> Mr) with Mr4c.
          assert (Hpp4e : add_vec_int (mword_of_int (KernelSyms.kkill + 0x4c) : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x4e))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp4e) in "Hpc".
          (* +0x4e jal ra,release *)
          iApply (wp_jal_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.kkill + 0x4e)) Rra
                    (mword_of_int 2091760 : mword 21) Mr4c (trap_res b + av)%nat false
                    ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (kki_4e with "Htext"). }
          iApply wp_next_off_intro. iIntros "Hcg Hpc".
          set (Mr4e := <[Regidx Rra := regval_into_reg
                          (add_vec_int (mword_of_int (KernelSyms.kkill + 0x4e) : mword 64) 4)]> Mr4c).
          change (<[Regidx Rra := regval_into_reg
                     (add_vec_int (mword_of_int (KernelSyms.kkill + 0x4e) : mword 64) 4)]> Mr4c) with Mr4e.
          assert (Hjrel2 : add_vec (mword_of_int (KernelSyms.kkill + 0x4e) : mword 64)
                             (sign_extend' 64 (mword_of_int 2091760 : mword 21)) = mword_of_int KernelSyms.release)
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hjrel2) in "Hpc".
          assert (HMr4e_ra : Mr4e !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.kkill + 0x4e) : mword 64) 4)
            by (rewrite /Mr4e; apply upd_eq).
          assert (HMr4e_a0 : Mr4e !!! Regidx Ra0 = proc_addr k).
          { rewrite /Mr4e upd_ne; [| vm_compute; discriminate].
            rewrite /Mr4c upd_eq add_vec_zero_l. exact Hr9. }
          assert (HMr4e_sp : Mr4e !!! Regidx csp_rs1 = spd).
          { rewrite /Mr4e upd_ne; [| vm_compute; discriminate].
            rewrite /Mr4c upd_ne; [| vm_compute; discriminate]. exact Hrsp. }
          assert (HMr4e_cs : kk_cs_rest Mr4e mb).
          { rewrite /Mr4e. apply kk_cs_rest_ncs; [vm_compute; reflexivity |].
            rewrite /Mr4c. apply kk_cs_rest_ncs; [vm_compute; reflexivity | exact Hrcs]. }
          assert (Hlka2 : add_vec (Mr4e !!! Regidx Ra0)
                            (sign_extend' 64 (mword_of_int 0 : mword 12)) = proc_addr k)
            by (rewrite HMr4e_a0; apply addv_sext0).
          (* This is a NESTED release (level [S lvl]), so its ENTRY index
             carries the trap reserve AT ITS OWN EXIT ARM -- and the spec
             spells that arm generically, as [match lvl with O => eb | S _ =>
             false end], where this proof carries the equal-but-syntactically-
             different local [b].  The two agree by [Hbmatch] (from
             [cpu_own_eb_agree]), but only the RESERVE summand needs the spec's
             spelling, so move [Hcg]'s index over to it and leave the rest of
             the context on [b]; the [rewrite -Hbmatch] after the [iApply] then
             brings the release's [match lvl]-phrased continuation back to [b],
             which is what the code after the call is written against. *)
          iEval (rewrite Hbmatch) in "Hcg".
          iApply (Release.wp_release_sconf KT1 (CID := CIDf) γk (proc_addr k) "proc"%string (proc_lock_pay γs γk (proc_addr k)) Mr4e lvl eb pme av
                    ({["proc"]} ∪ lks)
                    Hlka2 ltac:(lia)
                    with "Hcg Htext Hpc Hlockk Htok HR Hown Hpay").
          rewrite -Hbmatch.
          iIntros (CIDg Hsg mr) "Hcg Hpc %Hpinsr Hown".
          (* acquire handed back [{[rank "proc"]} ∪ lks]; release hands back
             that set minus the same singleton, and [Hno] (via
             [locks_below_not_elem]) says the round trip is a no-op: this
             hart never held a "proc" lock to begin with. *)
          pose proof (locks_below_not_elem lks "proc" Hno) as Hnotin1.
          assert (Heqlks1 : ({["proc"]} ∪ lks) ∖ {["proc"]} = lks)
      by (apply locks_add_del_below; lkbelow).
          iEval (rewrite Heqlks1) in "Hown".
          assert (Hpc52 : ret_pc (Mr4e !!! Regidx Rra) = mword_of_int (KernelSyms.kkill + 0x52))
            by (rewrite HMr4e_ra; apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpc52) in "Hpc".
          (* +0x52 c.li a0,0 *)
          iApply (wp_cli_s_sconf (CID := CIDg) (mword_of_int (KernelSyms.kkill + 0x52)) Ra0
                    (mword_of_int 0 : mword 6) (zero_reg : mword 64) mr av b
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (kki_52 with "Htext"). }
          iIntros (CIDh Hsh) "Hcg Hpc".
          set (Mfin := <[Regidx Ra0 := regval_into_reg (zero_reg : mword 64)]> mr).
          change (<[Regidx Ra0 := regval_into_reg (zero_reg : mword 64)]> mr) with Mfin.
          assert (Hpp54 : add_vec_int (mword_of_int (KernelSyms.kkill + 0x52) : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x54))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp54) in "Hpc".
          iDestruct (cpu_own_transport CIDg CIDh lvl eb pme b ltac:(wp_next_chain)
                       with "Hown") as "Hown".
          iSpecialize ("Hqx" $! CIDh with "[%]"); [wp_next_chain|].
          iApply ("Hqx" $! Mfin (zero_reg : mword 64) with "[%] Hcg Hown Hpc").
          unfold kk_exit_regs.
          split.
          { rewrite /Mfin upd_ne; [| vm_compute; discriminate].
            rewrite (callee_saved_lookup Hpinsr csp_rs1 ltac:(vm_compute; reflexivity)).
            exact HMr4e_sp. }
          split; [rewrite /Mfin; apply upd_eq|].
          split; [by left|].
          rewrite /Mfin. apply kk_cs_rest_ncs; [vm_compute; reflexivity|].
          eapply kk_cs_rest_cs; [exact Hpinsr | exact HMr4e_cs]. }
        (* ---- +0x40 c.li a5,1 ---- *)
        iApply (wp_cli_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.kkill + 0x40)) Ra5
                  (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64) M28 (trap_res b + av)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (kki_40 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (M40 := <[Regidx Ra5 := regval_into_reg (mword_of_int 1 : mword 64)]> M28).
        change (<[Regidx Ra5 := regval_into_reg (mword_of_int 1 : mword 64)]> M28) with M40.
        assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.kkill + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x42))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp42) in "Hpc".
        assert (HC9 : M40 !!! Regidx Rs1 = proc_addr k)
          by (rewrite /M40 upd_ne; [exact HB9 | vm_compute; discriminate]).
        assert (HCsp : M40 !!! Regidx csp_rs1 = spd)
          by (rewrite /M40 upd_ne; [exact HBsp | vm_compute; discriminate]).
        assert (HCcs : kk_cs_rest M40 mb)
          by (rewrite /M40; apply kk_cs_rest_ncs; [vm_compute; reflexivity | exact HBcs]).
        (* ---- +0x42 c.sw a5,40(s1) : p->killed = 1 ---- *)
        assert (Hea42 : add_vec (rget (CID := CIDf) M40 Rs1)
                          (sign_extend' 64 (mword_of_int 40 : mword 12)) = p_killed (proc_addr k)).
        { rewrite (rget_ne (CID := CIDf) M40 Rs1 ltac:(vm_compute; discriminate)) HC9.
          apply kk_killed_off. }
        iApply (wp_csw_s_sconf (kt := KT1) (ktd := KT0) (CID := CIDf) (mword_of_int (KernelSyms.kkill + 0x42)) Ra5 Rs1
                  (mword_of_int 40 : mword 12) M40 (trap_res b + av)%nat kl false
                  with "Hcg Hpc [] [Hkilled]").
        { iApply (kki_42 with "Htext"). }
        { iEval (rewrite Hea42). iExact "Hkilled". }
        iApply wp_next_off_intro. iIntros "Hcg Hpc Hkilled".
        iEval (rewrite Hea42) in "Hkilled".
        assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.kkill + 0x42) : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x44))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp44) in "Hpc".
        (* ---- +0x44 c.lw a4,24(s1) : a4 := p->state ---- *)
        assert (Hea44 : add_vec (rget (CID := CIDf) M40 Rs1)
                          (sign_extend' 64 (mword_of_int 24 : mword 12)) = p_state (proc_addr k)).
        { rewrite (rget_ne (CID := CIDf) M40 Rs1 ltac:(vm_compute; discriminate)) HC9.
          apply kk_state_off. }
        iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (CID := CIDf) (mword_of_int (KernelSyms.kkill + 0x44)) Ra4 Rs1
                  (mword_of_int 24 : mword 12) M40 (trap_res b + av)%nat st false (dqm := DfracOwn 1)
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc [] [Hpst]").
        { iApply (kki_44 with "Htext"). }
        { iEval (rewrite Hea44). iExact "Hpst". }
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc Hpst". iEval (rewrite Hea44) in "Hpst".
        set (M44 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 st)]> M40).
        change (<[Regidx Ra4 := regval_into_reg (sign_extend' 64 st)]> M40) with M44.
        assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.kkill + 0x44) : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x46))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp46) in "Hpc".
        (* ---- +0x46 c.li a5,2 ---- *)
        iApply (wp_cli_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.kkill + 0x46)) Ra5
                  (mword_of_int 2 : mword 6) (mword_of_int 2 : mword 64) M44 (trap_res b + av)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (kki_46 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (M46 := <[Regidx Ra5 := regval_into_reg (mword_of_int 2 : mword 64)]> M44).
        change (<[Regidx Ra5 := regval_into_reg (mword_of_int 2 : mword 64)]> M44) with M46.
        assert (Hpp48 : add_vec_int (mword_of_int (KernelSyms.kkill + 0x46) : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x48))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp48) in "Hpc".
        assert (HD14 : M46 !!! Regidx Ra4 = sign_extend' 64 st).
        { rewrite /M46 upd_ne; [| vm_compute; discriminate]. rewrite /M44. apply upd_eq. }
        assert (HD15 : M46 !!! Regidx Ra5 = (mword_of_int 2 : mword 64)) by (rewrite /M46; apply upd_eq).
        assert (HD9 : M46 !!! Regidx Rs1 = proc_addr k).
        { rewrite /M46 upd_ne; [| vm_compute; discriminate].
          rewrite /M44 upd_ne; [| vm_compute; discriminate]. exact HC9. }
        assert (HDsp : M46 !!! Regidx csp_rs1 = spd).
        { rewrite /M46 upd_ne; [| vm_compute; discriminate].
          rewrite /M44 upd_ne; [| vm_compute; discriminate]. exact HCsp. }
        assert (HDcs : kk_cs_rest M46 mb).
        { rewrite /M46. apply kk_cs_rest_ncs; [vm_compute; reflexivity |].
          rewrite /M44. apply kk_cs_rest_ncs; [vm_compute; reflexivity | exact HCcs]. }
        (* ---- +0x48 beq a4,a5 : is it SLEEPING? ---- *)
        assert (Hrg48_14 : rget (CID := CIDf) M46 Ra4 = M46 !!! Regidx Ra4) by (rgne; reflexivity).
        assert (Hrg48_15 : rget (CID := CIDf) M46 Ra5 = M46 !!! Regidx Ra5) by (rgne; reflexivity).
        destruct (eq_vec (M46 !!! Regidx Ra4) (M46 !!! Regidx Ra5)) eqn:Hcmp48.
        + (* TAKEN: SLEEPING -> wake it *)
          assert (Hcmp46r : eq_vec (rget (CID := CIDf) M46 Ra4) (rget (CID := CIDf) M46 Ra5) = true)
            by (rewrite Hrg48_14 Hrg48_15; exact Hcmp48).
          iApply (wp_beq_taken_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.kkill + 0x48))
                    (mword_of_int 26 : mword 13) Ra5 Ra4 M46 (trap_res b + av)%nat false
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hcmp46r ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (kki_48 with "Htext"). }
          iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
          assert (Htgt62 : add_vec (mword_of_int (KernelSyms.kkill + 0x48) : mword 64)
                             (sign_extend' 64 (mword_of_int 26 : mword 13)) = mword_of_int (KernelSyms.kkill + 0x62))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Htgt62) in "Hpc".
          assert (Hst_sl : st = SLEEPING).
          { apply kk_sext_sleeping. rewrite HD14 HD15 in Hcmp48.
            by apply eq_vec_true_iff in Hcmp48. }
          (* +0x62 c.li a5,3 *)
          iApply (wp_cli_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.kkill + 0x62)) Ra5
                    (mword_of_int 3 : mword 6) (mword_of_int 3 : mword 64) M46 (trap_res b + av)%nat false
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (kki_62 with "Htext"). }
          iApply wp_next_off_intro. iIntros "Hcg Hpc".
          set (M62 := <[Regidx Ra5 := regval_into_reg (mword_of_int 3 : mword 64)]> M46).
          change (<[Regidx Ra5 := regval_into_reg (mword_of_int 3 : mword 64)]> M46) with M62.
          assert (Hpp64 : add_vec_int (mword_of_int (KernelSyms.kkill + 0x62) : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x64))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp64) in "Hpc".
          assert (HE9 : M62 !!! Regidx Rs1 = proc_addr k)
            by (rewrite /M62 upd_ne; [exact HD9 | vm_compute; discriminate]).
          assert (HEsp : M62 !!! Regidx csp_rs1 = spd)
            by (rewrite /M62 upd_ne; [exact HDsp | vm_compute; discriminate]).
          assert (HEcs : kk_cs_rest M62 mb)
            by (rewrite /M62; apply kk_cs_rest_ncs; [vm_compute; reflexivity | exact HDcs]).
          (* +0x64 c.sw a5,24(s1) : p->state = RUNNABLE *)
          assert (Hea64 : add_vec (rget (CID := CIDf) M62 Rs1)
                            (sign_extend' 64 (mword_of_int 24 : mword 12)) = p_state (proc_addr k)).
          { rewrite (rget_ne (CID := CIDf) M62 Rs1 ltac:(vm_compute; discriminate)) HE9.
            apply kk_state_off. }
          iApply (wp_csw_s_sconf (kt := KT1) (ktd := KT0) (CID := CIDf) (mword_of_int (KernelSyms.kkill + 0x64)) Ra5 Rs1
                    (mword_of_int 24 : mword 12) M62 (trap_res b + av)%nat st false
                    with "Hcg Hpc [] [Hpst]").
          { iApply (kki_64 with "Htext"). }
          { iEval (rewrite Hea64). iExact "Hpst". }
          iApply wp_next_off_intro. iIntros "Hcg Hpc Hpst".
          assert (Hstored : trunc32 (rget (CID := CIDf) M62 Ra5) = RUNNABLE).
          { rewrite (rget_ne (CID := CIDf) M62 Ra5 ltac:(vm_compute; discriminate)).
            rewrite /M62 upd_eq /RUNNABLE. apply bv_eq; vm_compute; reflexivity. }
          iEval (rewrite Hstored) in "Hpst". iEval (rewrite Hea64) in "Hpst".
          assert (Hpp66 : add_vec_int (mword_of_int (KernelSyms.kkill + 0x64) : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x66))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp66) in "Hpc".
          (* reassemble: SLEEPING -> RUNNABLE keeps both guards fixed *)
          iAssert (|==> proc_pub (proc_addr k))%I with "[Hkilled Hxstate Hpidhalf Hrow]" as ">Hpub".
          { (* the flag is 1 here, so the row must be re-closed on its PAID
               arm -- and what pays is the price the slot itself publishes:
               the target's payload at -1, bought with the application's
               TAINT ([RiscvPtsto.app_taint], lane SELF-KILL, §4b').
               THE STEP IS A GHOST UPDATE because the writer also FIRES the
               incarnation's kill one-shot (lane SELF-KILL, P6): from here
               on the flag is nonzero for good, and that is the fact
               [killed()] relays and [kexit] spends. *)
            iMod (kill_paid_kill pidc kl (trunc32 (rget (CID := CIDf) M40 Ra5))
                    Hpcnz with "[] Hkc Hrow") as "Hrow";
              [ iPureIntro;
                rewrite (rget_ne (CID := CIDf) M40 Ra5 ltac:(vm_compute; discriminate));
                rewrite /M40 upd_eq;
                intro Hc; apply (f_equal (@bv_unsigned 32)) in Hc;
                vm_compute in Hc; discriminate | ].
            iModIntro. iExists _, xs, pidc.
            iFrame "Hkilled Hxstate Hpidhalf Hrow". }
          iApply fupd_wp.
          iMod (proc_lock_res_wakeup γs γk (proc_addr k) st ch Hst_sl
                  with "Hpst Hpg Hpch Hpub Hslots") as "HR".
          iModIntro.
          (* +0x66 c.j -> +0x4c *)
          assert (Htgt4c : add_vec (mword_of_int (KernelSyms.kkill + 0x66) : mword 64)
                             (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2035 : mword 11) ('b"0"))))
                           = mword_of_int (KernelSyms.kkill + 0x4c))
            by (apply bv_eq; vm_compute; reflexivity).
          iApply (wp_cj_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.kkill + 0x66))
                    (sign_extend' 21 (concat_vec (mword_of_int 2035 : mword 11) ('b"0")))
                    M62 (trap_res b + av)%nat false ltac:(rewrite Htgt4c; vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (kki_66 with "Htext"). }
          iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc".
          iEval (rewrite Htgt4c) in "Hpc".
          iApply ("Hret0" $! M62 with "[%] Hcg Hpc Htok HR").
          split; [exact HE9|]. split; [exact HEsp|]. exact HEcs.
        + (* FALL: not SLEEPING -> straight to the shared block *)
          assert (Hcmp46r : eq_vec (rget (CID := CIDf) M46 Ra4) (rget (CID := CIDf) M46 Ra5) = false)
            by (rewrite Hrg48_14 Hrg48_15; exact Hcmp48).
          iApply (wp_beq_fall_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.kkill + 0x48))
                    (mword_of_int 26 : mword 13) Ra5 Ra4 M46 (trap_res b + av)%nat false
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hcmp46r with "Hcg Hpc []").
          { iApply (kki_48 with "Htext"). }
          iApply wp_next_off_intro. iIntros "Hcg Hpc".
          assert (Hpp4c : add_vec_int (mword_of_int (KernelSyms.kkill + 0x48) : mword 64) 4 = mword_of_int (KernelSyms.kkill + 0x4c))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp4c) in "Hpc".
          iAssert (|==> proc_pub (proc_addr k))%I with "[Hkilled Hxstate Hpidhalf Hrow]" as ">Hpub".
          { iMod (kill_paid_kill pidc kl (trunc32 (rget (CID := CIDf) M40 Ra5))
                    Hpcnz with "[] Hkc Hrow") as "Hrow";
              [ iPureIntro;
                rewrite (rget_ne (CID := CIDf) M40 Ra5 ltac:(vm_compute; discriminate));
                rewrite /M40 upd_eq;
                intro Hc; apply (f_equal (@bv_unsigned 32)) in Hc;
                vm_compute in Hc; discriminate | ].
            iModIntro. iExists _, xs, pidc.
            iFrame "Hkilled Hxstate Hpidhalf Hrow". }
          iDestruct (proc_lock_res_intro γs γk (proc_addr k) st ch
                       with "Hpst Hpg Hpch Hpub Hslots") as "HR".
          iApply ("Hret0" $! M46 with "[%] Hcg Hpc Htok HR").
          split; [exact HD9|]. split; [exact HDsp|]. exact HDcs.
      - (* ============ FALL: no match -> release, p++, loop ============ *)
        assert (Hcmp28r : eq_vec (rget (CID := CIDf) M28 Ra5) (rget (CID := CIDf) M28 Rs2) = false)
          by (rewrite Hrg2a_15 Hrg2a_18; exact Hcmp2a).
        iApply (wp_beq_fall_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.kkill + 0x2a))
                  (mword_of_int 22 : mword 13) Rs2 Ra5 M28 (trap_res b + av)%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hcmp28r with "Hcg Hpc []").
        { iApply (kki_2a with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.kkill + 0x2a) : mword 64) 4 = mword_of_int (KernelSyms.kkill + 0x2e))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp2e) in "Hpc".
        (* nothing moved: put the lock resource straight back *)
        (* nothing was written: the row goes straight back, unchanged. *)
        iAssert (proc_pub (proc_addr k)) with "[Hkilled Hxstate Hpidhalf Hrow]" as "Hpub".
        { iExists kl, xs, pidc. iFrame "Hkilled Hxstate Hpidhalf Hrow". }
        iDestruct (proc_lock_res_intro γs γk (proc_addr k) st ch
                     with "Hpst Hpg Hpch Hpub Hslots") as "HR".
        (* +0x2e c.mv a0,s1 *)
        assert (Hrg2e : rget (CID := CIDf) M28 Rs1 = M28 !!! Regidx Rs1) by (rgne; reflexivity).
        iApply (wp_cmv_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.kkill + 0x2e)) Ra0 Rs1
                  M28 (trap_res b + av)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc []").
        { iApply (kki_2e with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        iEval (rewrite Hrg2e) in "Hcg".
        set (M2e := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M28 !!! Regidx Rs1))]> M28).
        change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M28 !!! Regidx Rs1))]> M28) with M2e.
        assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.kkill + 0x2e) : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x30))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp30) in "Hpc".
        (* +0x30 jal ra,release *)
        iApply (wp_jal_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.kkill + 0x30)) Rra
                  (mword_of_int 2091790 : mword 21) M2e (trap_res b + av)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (kki_30 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (M30 := <[Regidx Rra := regval_into_reg
                       (add_vec_int (mword_of_int (KernelSyms.kkill + 0x30) : mword 64) 4)]> M2e).
        change (<[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (KernelSyms.kkill + 0x30) : mword 64) 4)]> M2e) with M30.
        assert (Hjrel1 : add_vec (mword_of_int (KernelSyms.kkill + 0x30) : mword 64)
                           (sign_extend' 64 (mword_of_int 2091790 : mword 21)) = mword_of_int KernelSyms.release)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjrel1) in "Hpc".
        assert (HM30_ra : M30 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.kkill + 0x30) : mword 64) 4)
          by (rewrite /M30; apply upd_eq).
        assert (HM30_a0 : M30 !!! Regidx Ra0 = proc_addr k).
        { rewrite /M30 upd_ne; [| vm_compute; discriminate].
          rewrite /M2e upd_eq add_vec_zero_l. exact HB9. }
        assert (HM30_9 : M30 !!! Regidx Rs1 = proc_addr k).
        { rewrite /M30 upd_ne; [| vm_compute; discriminate].
          rewrite /M2e upd_ne; [| vm_compute; discriminate]. exact HB9. }
        assert (HM30_sp : M30 !!! Regidx csp_rs1 = spd).
        { rewrite /M30 upd_ne; [| vm_compute; discriminate].
          rewrite /M2e upd_ne; [| vm_compute; discriminate]. exact HBsp. }
        assert (HM30_18 : M30 !!! Regidx Rs2 = pidv).
        { rewrite /M30 upd_ne; [| vm_compute; discriminate].
          rewrite /M2e upd_ne; [| vm_compute; discriminate]. exact HB18. }
        assert (HM30_19 : M30 !!! Regidx Rs3 = proc_addr NPROC).
        { rewrite /M30 upd_ne; [| vm_compute; discriminate].
          rewrite /M2e upd_ne; [| vm_compute; discriminate]. exact HB19. }
        assert (HM30_cs : kk_cs_rest M30 mb).
        { rewrite /M30. apply kk_cs_rest_ncs; [vm_compute; reflexivity |].
          rewrite /M2e. apply kk_cs_rest_ncs; [vm_compute; reflexivity | exact HBcs]. }
        assert (Hlka1 : add_vec (M30 !!! Regidx Ra0)
                          (sign_extend' 64 (mword_of_int 0 : mword 12)) = proc_addr k)
          by (rewrite HM30_a0; apply addv_sext0).
        (* Nested release: same [b] vs [match lvl] reserve-spelling step as the
           +0x4e site above -- see the comment there. *)
        iEval (rewrite Hbmatch) in "Hcg".
        iApply (Release.wp_release_sconf KT1 (CID := CIDf) γk (proc_addr k) "proc"%string (proc_lock_pay γs γk (proc_addr k)) M30 lvl eb pme av
                  ({["proc"]} ∪ lks)
                  Hlka1 ltac:(lia)
                  with "Hcg Htext Hpc Hlockk Htok HR Hown Hpay").
        rewrite -Hbmatch.
        iIntros (CIDg Hsg mr) "Hcg Hpc %Hpinsr Hown".
        (* see the +0x4e release above: [Hno] kills the difference. *)
        pose proof (locks_below_not_elem lks "proc" Hno) as Hnotin2.
        assert (Heqlks2 : ({["proc"]} ∪ lks) ∖ {["proc"]} = lks)
      by (apply locks_add_del_below; lkbelow).
        iEval (rewrite Heqlks2) in "Hown".
        assert (Hpc34 : ret_pc (M30 !!! Regidx Rra) = mword_of_int (KernelSyms.kkill + 0x34))
          by (rewrite HM30_ra; apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc34) in "Hpc".
        assert (HR9 : mr !!! Regidx Rs1 = proc_addr k)
          by (rewrite (callee_saved_lookup Hpinsr Rs1 ltac:(vm_compute; reflexivity)); exact HM30_9).
        assert (HRsp : mr !!! Regidx csp_rs1 = spd)
          by (rewrite (callee_saved_lookup Hpinsr csp_rs1 ltac:(vm_compute; reflexivity)); exact HM30_sp).
        assert (HR18 : mr !!! Regidx Rs2 = pidv)
          by (rewrite (callee_saved_lookup Hpinsr Rs2 ltac:(vm_compute; reflexivity)); exact HM30_18).
        assert (HR19 : mr !!! Regidx Rs3 = proc_addr NPROC)
          by (rewrite (callee_saved_lookup Hpinsr Rs3 ltac:(vm_compute; reflexivity)); exact HM30_19).
        assert (HRcs : kk_cs_rest mr mb) by (eapply kk_cs_rest_cs; [exact Hpinsr | exact HM30_cs]).
        (* +0x34 addi s1,s1,360 : p++ *)
        assert (Hrg34 : rget (CID := CIDg) mr Rs1 = mr !!! Regidx Rs1) by (rgne; reflexivity).
        iApply (wp_addi4_s_sconf (CID := CIDg) (mword_of_int (KernelSyms.kkill + 0x34)) Rs1 Rs1
                  (mword_of_int 368 : mword 12) mr av b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc []").
        { iApply (kki_34 with "Htext"). }
        iIntros (CIDi Hsi) "Hcg Hpc".
        iEval (rewrite Hrg34) in "Hcg".
        set (M34 := <[Regidx Rs1 := regval_into_reg
                       (add_vec (mr !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 368 : mword 12)))]> mr).
        change (<[Regidx Rs1 := regval_into_reg
                   (add_vec (mr !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 368 : mword 12)))]> mr) with M34.
        assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.kkill + 0x34) : mword 64) 4 = mword_of_int (KernelSyms.kkill + 0x38))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp38) in "Hpc".
        assert (HF9 : M34 !!! Regidx Rs1 = proc_addr (S k)).
        { rewrite /M34 upd_eq HR9. apply (proc_addr_succ k). }
        assert (HFsp : M34 !!! Regidx csp_rs1 = spd)
          by (rewrite /M34 upd_ne; [exact HRsp | vm_compute; discriminate]).
        assert (HF18 : M34 !!! Regidx Rs2 = pidv)
          by (rewrite /M34 upd_ne; [exact HR18 | vm_compute; discriminate]).
        assert (HF19 : M34 !!! Regidx Rs3 = proc_addr NPROC)
          by (rewrite /M34 upd_ne; [exact HR19 | vm_compute; discriminate]).
        assert (HFcs : kk_cs_rest M34 mb) by (rewrite /M34; apply kk_cs_rest_s1; exact HRcs).
        (* +0x38 bne s1,s3 : keep scanning, or fall out with -1 *)
        assert (Hrg38_9 : rget (CID := CIDi) M34 Rs1 = M34 !!! Regidx Rs1) by (rgne; reflexivity).
        assert (Hrg38_19 : rget (CID := CIDi) M34 Rs3 = M34 !!! Regidx Rs3) by (rgne; reflexivity).
        destruct (neq_vec (M34 !!! Regidx Rs1) (M34 !!! Regidx Rs3)) eqn:Hcmp38.
        + (* TAKEN: more slots -- back edge to +0x22 *)
          assert (Hcmp36r : neq_vec (rget (CID := CIDi) M34 Rs1) (rget (CID := CIDi) M34 Rs3) = true)
            by (rewrite Hrg38_9 Hrg38_19; exact Hcmp38).
          iApply (wp_bne_taken_s_sconf (CID := CIDi) (mword_of_int (KernelSyms.kkill + 0x38))
                    (mword_of_int 8170 : mword 13) Rs3 Rs1 M34 av b
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hcmp36r ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (kki_38 with "Htext"). }
          iApply bi.later_intro. iIntros (CIDj Hsj) "Hcg Hpc".
          assert (Htgt22 : add_vec (mword_of_int (KernelSyms.kkill + 0x38) : mword 64)
                             (sign_extend' 64 (mword_of_int 8170 : mword 13)) = mword_of_int (KernelSyms.kkill + 0x22))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Htgt22) in "Hpc".
          assert (HkS : (S k < NPROC)%nat).
          { destruct (Nat.lt_ge_cases (S k) NPROC) as [Hlt | Hge]; [exact Hlt|].
            assert (HeqN : S k = NPROC) by lia.
            exfalso.
            assert (Hbad : neq_vec (M34 !!! Regidx Rs1) (M34 !!! Regidx Rs3) = false).
            { rewrite HF9 HF19 HeqN. unfold neq_vec. rewrite kk_eq_vec_refl. reflexivity. }
            rewrite Hcmp38 in Hbad. discriminate. }
          iDestruct (cpu_own_transport CIDg CIDj lvl eb pme b ltac:(wp_next_chain)
                       with "Hown") as "Hown".
          iSpecialize ("IHf" $! CIDj with "[%]"); [wp_next_chain|].
          iApply ("IHf" $! (S k) M34 with "[%] [%] [%] Hqx Hcg Hown Htext Hpc").
          * lia.
          * exact HkS.
          * unfold kkl_regs.
            split; [exact HF9|]. split; [exact HFsp|]. split; [exact HF18|].
            split; [exact HF19|]. exact HFcs.
        + (* FALL: the scan is over -- return -1 *)
          assert (Hcmp36r : neq_vec (rget (CID := CIDi) M34 Rs1) (rget (CID := CIDi) M34 Rs3) = false)
            by (rewrite Hrg38_9 Hrg38_19; exact Hcmp38).
          iApply (wp_bne_fall_s_sconf (CID := CIDi) (mword_of_int (KernelSyms.kkill + 0x38))
                    (mword_of_int 8170 : mword 13) Rs3 Rs1 M34 av b
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hcmp36r with "Hcg Hpc []").
          { iApply (kki_38 with "Htext"). }
          iIntros (CIDj Hsj) "Hcg Hpc".
          assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.kkill + 0x38) : mword 64) 4 = mword_of_int (KernelSyms.kkill + 0x3c))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp3c) in "Hpc".
          (* +0x3c c.li a0,-1 *)
          iApply (wp_cli_s_sconf (CID := CIDj) (mword_of_int (KernelSyms.kkill + 0x3c)) Ra0
                    (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64) M34 av b
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (kki_3c with "Htext"). }
          iIntros (CIDl Hsl) "Hcg Hpc".
          set (M3c := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> M34).
          change (<[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> M34) with M3c.
          assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.kkill + 0x3c) : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x3e))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp3e) in "Hpc".
          (* +0x3e c.j -> +0x54 *)
          assert (Htgt54 : add_vec (mword_of_int (KernelSyms.kkill + 0x3e) : mword 64)
                             (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 11 : mword 11) ('b"0"))))
                           = mword_of_int (KernelSyms.kkill + 0x54))
            by (apply bv_eq; vm_compute; reflexivity).
          iApply (wp_cj_s_sconf (CID := CIDl) (mword_of_int (KernelSyms.kkill + 0x3e))
                    (sign_extend' 21 (concat_vec (mword_of_int 11 : mword 11) ('b"0")))
                    M3c av b ltac:(rewrite Htgt54; vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (kki_3e with "Htext"). }
          iIntros (CIDm Hsm). iApply bi.later_intro. iIntros "Hcg Hpc".
          iEval (rewrite Htgt54) in "Hpc".
          iDestruct (cpu_own_transport CIDg CIDm lvl eb pme b ltac:(wp_next_chain)
                       with "Hown") as "Hown".
          iSpecialize ("Hqx" $! CIDm with "[%]"); [wp_next_chain|].
          iApply ("Hqx" $! M3c (mword_of_int (-1) : mword 64) with "[%] Hcg Hown Hpc").
          unfold kk_exit_regs.
          split; [rewrite /M3c upd_ne; [exact HFsp | vm_compute; discriminate]|].
          split; [rewrite /M3c; apply upd_eq|].
          split; [by right|].
          rewrite /M3c. apply kk_cs_rest_ncs; [vm_compute; reflexivity | exact HFcs]. }
    iIntros (k M) "%Hk %Hregs Hcg Hown Htext Hpc".
    iSpecialize ("Hloop" $! (NPROC - k)%nat).
    iSpecialize ("Hloop" $! CID0 with "[%]"); [by intros|].
    iApply ("Hloop" $! k M with "[%] [%] [%] Hqexit Hcg Hown Htext Hpc");
      [lia | exact Hk | exact Hregs].
  Qed.

End ProofKkill.

(* ==================================================================== *)
(* The whole function: prologue -> scan (k = 0) -> epilogue.            *)
(* ==================================================================== *)
Section ProofKkillMain.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ, !fileG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).

  Lemma wp_kkill_sconf  (γs : list gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (b : bool) (lks : gset string)
    : wp_kkill_sconf_body γs m av n eb p b lks.
  Proof using .
    cbv beta delta [wp_kkill_sconf_body].
    intros pcE ret_tgt Hlen Hn Hav Hno.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "#Hkc Hcg Hcpu #Htext Hpc #Hprocs Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcpu") as %Hbeq.
    (* +0x00 c.beqz a0,+0x68 -- [if (pid == 0) return -1;] *)
    destruct (eq_vec (rget (CID := CID) m Ra0) zero_reg) eqn:Hpid0.
    { (* taken: the +0x68 tail, outside the frame *)
      assert (Hgt68 : add_vec (pcE : mword 64)
                        (sign_extend' 64 (sign_extend' 13
                           (concat_vec (mword_of_int 52 : mword 8) ('b"0"))))
                      = mword_of_int (KernelSyms.kkill + 0x68))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_cbeqz_taken_s_sconf pcE (mword_of_int 52 : mword 8)
                (Cregidx (mword_of_int 2)) Ra0 m av b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                Hpid0 ltac:(rewrite Hgt68; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (kki_00 with "Htext"). }
      iApply bi.later_intro.
      iIntros (CIDz0 Hkz0) "Hcg Hpc".
      iEval (rewrite Hgt68) in "Hpc".
      (* +0x68 c.li a0,-1 *)
      iApply (wp_cli_s_sconf (CID := CIDz0) (mword_of_int (KernelSyms.kkill + 0x68)) Ra0
                (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64) m av b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (kki_68 with "Htext"). }
      iIntros (CIDz1 Hkz1) "Hcg Hpc".
      set (G0 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> m).
      change (<[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> m) with G0.
      assert (Hgp6a : add_vec_int (mword_of_int (KernelSyms.kkill + 0x68) : mword 64) 2
                      = mword_of_int (KernelSyms.kkill + 0x6a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hgp6a) in "Hpc".
      (* +0x6a c.ret *)
      assert (HG0ra : G0 !!! Regidx Rra = m !!! Regidx Rra)
        by (rewrite /G0 upd_ne; [reflexivity | vm_compute; discriminate]).
      iApply (wp_cret_s_sconf (CID := CIDz1) (mword_of_int (KernelSyms.kkill + 0x6a)) Rra G0 av b
                ltac:(vm_compute; discriminate) with "Hcg Hpc []").
      { iApply (kki_6a with "Htext"). }
      iIntros (CIDz2 Hkz2) "Hcg Hpc".
      iEval (rgne) in "Hpc".
      assert (Hgret : ret_pc (G0 !!! Regidx Rra) = ret_tgt) by (rewrite HG0ra; reflexivity).
      iEval (rewrite Hgret) in "Hpc".
      iDestruct (cpu_own_transport CID CIDz2 n eb p b ltac:(wp_next_chain)
                   with "Hcpu") as "Hcpu".
      iSpecialize ("Hcont" $! CIDz2 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! G0 (mword_of_int (-1) : mword 64) with "[%] Hcg Hcpu Hpc").
      split; [| split].
      - rewrite /G0. apply callee_saved_insert_r;
          [vm_compute; reflexivity | apply callee_saved_refl].
      - rewrite /G0. apply upd_eq.
      - by right. }
    (* fall: the prologue at +0x02 *)
    iApply (wp_cbeqz_fall_s_sconf pcE (mword_of_int 52 : mword 8)
              (Cregidx (mword_of_int 2)) Ra0 m av b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              Hpid0 with "Hcg Hpc []").
    { iApply (kki_00 with "Htext"). }
    iIntros (CIDg0 Hkg0) "Hcg Hpc".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* ===================== PROLOGUE (48-byte frame) ===================== *)
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int (KernelSyms.kkill + 0x02))
              (mword_of_int 61 : mword 6) m av 6 b
              ltac:(lia) (stk_push_48 (m !!! Regidx csp_rs1))
              with "Hcg Hpc []").
    { iApply (kki_02 with "Htext"). }
    iIntros (CID1 Hk1) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
              (add_vec (m !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m) with M1.
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.kkill + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.kkill + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /M1 upd_eq; apply stk_push_48).
    assert (E5 : pa_stk (pa_stk sp0 4) 1 = pa_stk sp0 5) by (rewrite pa_stk_assoc; reflexivity).
    assert (E6 : pa_stk (pa_stk sp0 4) 2 = pa_stk sp0 6) by (rewrite pa_stk_assoc; reflexivity).
    rewrite (stack_own_split (KTR := KT1) sp0 4 6 ltac:(lia)). change (6 - 4)%nat with 2%nat.
    iDestruct "Hframe" as "[Hf14 Hf56]".
    iDestruct (stack_own_4_elim with "Hf14") as (u1 u2 u3 u4) "(Hb1 & Hb2 & Hb3 & Hb4)".
    iDestruct (stack_own_2_elim with "Hf56") as (w5 w6) "[Hb5 Hb6]".
    iEval (rewrite E5) in "Hb5". iEval (rewrite E6) in "Hb6".
    (* the five save-slot addresses, as the c.sdsp displacements compute them *)
    assert (Hpa : forall u k : nat, (k + u = 6)%nat -> (u < 6)%nat ->
              add_vec (M1 !!! Regidx csp_rs1)
                (zero_extend' 64 (concat_vec (mword_of_int (Z.of_nat u) : mword 6) ('b"000")))
              = pa_stk sp0 k).
    { intros u k Hku Hu. rewrite HM1sp.
      destruct u as [|[|[|[|[|[|]]]]]]; try lia;
        destruct k as [|[|[|[|[|[|[|]]]]]]]; try lia;
        unfold pa_stk, add_vec_int; rewrite add_vec_off2;
        apply f_equal; apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa1 := Hpa 5%nat 1%nat ltac:(lia) ltac:(lia)).
    assert (Hpa2 := Hpa 4%nat 2%nat ltac:(lia) ltac:(lia)).
    assert (Hpa3 := Hpa 3%nat 3%nat ltac:(lia) ltac:(lia)).
    assert (Hpa4 := Hpa 2%nat 4%nat ltac:(lia) ltac:(lia)).
    assert (Hpa5 := Hpa 1%nat 5%nat ltac:(lia) ltac:(lia)).
    (* +0x04..+0x0c: save ra/s0/s1/s2/s3 *)
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.kkill + 0x04)) (mword_of_int 5 : mword 6) Rra
              M1 (av - 6)%nat u1 b with "Hcg Hpc [] Hb1").
    { iApply (kki_04 with "Htext"). }
    iIntros (CID2 Hk2) "Hcg Hpc Hb1".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.kkill + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.kkill + 0x06)) (mword_of_int 4 : mword 6) Rs0
              M1 (av - 6)%nat u2 b with "Hcg Hpc [] Hb2").
    { iApply (kki_06 with "Htext"). }
    iIntros (CID3 Hk3) "Hcg Hpc Hb2".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.kkill + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    iEval (rewrite -Hpa3) in "Hb3".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.kkill + 0x08)) (mword_of_int 3 : mword 6) Rs1
              M1 (av - 6)%nat u3 b with "Hcg Hpc [] Hb3").
    { iApply (kki_08 with "Htext"). }
    iIntros (CID4 Hk4) "Hcg Hpc Hb3".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.kkill + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    iEval (rewrite -Hpa4) in "Hb4".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.kkill + 0x0a)) (mword_of_int 2 : mword 6) Rs2
              M1 (av - 6)%nat u4 b with "Hcg Hpc [] Hb4").
    { iApply (kki_0a with "Htext"). }
    iIntros (CID5 Hk5) "Hcg Hpc Hb4".
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.kkill + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    iEval (rewrite -Hpa5) in "Hb5".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.kkill + 0x0c)) (mword_of_int 1 : mword 6) Rs3
              M1 (av - 6)%nat w5 b with "Hcg Hpc [] Hb5").
    { iApply (kki_0c with "Htext"). }
    iIntros (CID6 Hk6) "Hcg Hpc Hb5".
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.kkill + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x0e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* normalize the five saved cells to [pa_stk sp0 _ ↦₈[KT1] (m !!! r)] *)
    assert (HM1ra : M1 !!! Regidx Rra = m !!! Regidx Rra)
      by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HM1s0 : M1 !!! Regidx Rs0 = m !!! Regidx Rs0)
      by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HM1s1 : M1 !!! Regidx Rs1 = m !!! Regidx Rs1)
      by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HM1s2 : M1 !!! Regidx Rs2 = m !!! Regidx Rs2)
      by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HM1s3 : M1 !!! Regidx Rs3 = m !!! Regidx Rs3)
      by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rgne; rewrite Hpa1 HM1ra) in "Hb1".
    iEval (rgne; rewrite Hpa2 HM1s0) in "Hb2".
    iEval (rgne; rewrite Hpa3 HM1s1) in "Hb3".
    iEval (rgne; rewrite Hpa4 HM1s2) in "Hb4".
    iEval (rgne; rewrite Hpa5 HM1s3) in "Hb5".
    (* +0x0e: c.addi4spn s0,sp,48 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.kkill + 0x0e)) (Cregidx (mword_of_int 0))
              (mword_of_int 12 : mword 8) Rs0 M1 (av - 6)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (kki_0e with "Htext"). }
    iIntros (CID7 Hk7) "Hcg Hpc".
    set (M2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> M1).
    change (<[Regidx Rs0 := regval_into_reg
              (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> M1) with M2.
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.kkill + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    assert (HM2sp : M2 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /M2 upd_ne; [exact HM1sp | vm_compute; discriminate]).
    (* +0x10: c.mv s2,a0 -- park [pid] *)
    assert (Hrg10 : rget (CID := CID7) M2 Ra0 = M2 !!! Regidx Ra0) by (rgne; reflexivity).
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.kkill + 0x10)) Rs2 Ra0 M2 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (kki_10 with "Htext"). }
    iIntros (CID8 Hk8) "Hcg Hpc".
    iEval (rewrite Hrg10) in "Hcg".
    set (M3 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (M2 !!! Regidx Ra0))]> M2).
    change (<[Regidx Rs2 := regval_into_reg (add_vec zero_reg (M2 !!! Regidx Ra0))]> M2) with M3.
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.kkill + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x12))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* +0x12 auipc s1,0x10 ; +0x16 addi s1,s1,1722 : s1 := &proc[0] *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.kkill + 0x12)) Rs1 (mword_of_int 0x10 : mword 20)
              M3 (av - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (kki_12 with "Htext"). }
    iIntros (CID9 Hk9) "Hcg Hpc".
    set (M4 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.kkill + 0x12) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))]> M3).
    change (<[Regidx Rs1 := regval_into_reg
              (add_vec (mword_of_int (KernelSyms.kkill + 0x12) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))]> M3) with M4.
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.kkill + 0x12) : mword 64) 4 = mword_of_int (KernelSyms.kkill + 0x16))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    assert (Hrg16 : rget (CID := CID9) M4 Rs1 = M4 !!! Regidx Rs1) by (rgne; reflexivity).
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.kkill + 0x16)) Rs1 Rs1 (mword_of_int 1756 : mword 12)
              M4 (av - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (kki_16 with "Htext"). }
    iIntros (CID10 Hk10) "Hcg Hpc".
    iEval (rewrite Hrg16) in "Hcg".
    set (M5 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (M4 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 1756 : mword 12)))]> M4).
    change (<[Regidx Rs1 := regval_into_reg
              (add_vec (M4 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 1756 : mword 12)))]> M4) with M5.
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.kkill + 0x16) : mword 64) 4 = mword_of_int (KernelSyms.kkill + 0x1a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    assert (HM5s1 : M5 !!! Regidx Rs1 = proc_addr 0).
    { rewrite /M5 upd_eq /M4 upd_eq. unfold proc_addr, proc_base, proc_size.
      apply bv_eq; vm_compute; reflexivity. }
    (* +0x1a auipc s3,0x16 ; +0x1e addi s3,s3,162 : s3 := &proc[NPROC] *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.kkill + 0x1a)) Rs3 (mword_of_int 0x16 : mword 20)
              M5 (av - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (kki_1a with "Htext"). }
    iIntros (CID11 Hk11) "Hcg Hpc".
    set (M6 := <[Regidx Rs3 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.kkill + 0x1a) : mword 64) (auipc_off (mword_of_int 0x16 : mword 20)))]> M5).
    change (<[Regidx Rs3 := regval_into_reg
              (add_vec (mword_of_int (KernelSyms.kkill + 0x1a) : mword 64) (auipc_off (mword_of_int 0x16 : mword 20)))]> M5) with M6.
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.kkill + 0x1a) : mword 64) 4 = mword_of_int (KernelSyms.kkill + 0x1e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    assert (Hrg1e : rget (CID := CID11) M6 Rs3 = M6 !!! Regidx Rs3) by (rgne; reflexivity).
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.kkill + 0x1e)) Rs3 Rs3 (mword_of_int 724 : mword 12)
              M6 (av - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (kki_1e with "Htext"). }
    iIntros (CID12 Hk12) "Hcg Hpc".
    iEval (rewrite Hrg1e) in "Hcg".
    set (M7 := <[Regidx Rs3 := regval_into_reg
                  (add_vec (M6 !!! Regidx Rs3) (sign_extend' 64 (mword_of_int 724 : mword 12)))]> M6).
    change (<[Regidx Rs3 := regval_into_reg
              (add_vec (M6 !!! Regidx Rs3) (sign_extend' 64 (mword_of_int 724 : mword 12)))]> M6) with M7.
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.kkill + 0x1e) : mword 64) 4 = mword_of_int (KernelSyms.kkill + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    assert (HM7s3 : M7 !!! Regidx Rs3 = proc_addr NPROC).
    { rewrite /M7 upd_eq /M6 upd_eq. unfold proc_addr, proc_base, NPROC, proc_size.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HM7s1 : M7 !!! Regidx Rs1 = proc_addr 0).
    { rewrite /M7 upd_ne; [| vm_compute; discriminate].
      rewrite /M6 upd_ne; [| vm_compute; discriminate]. exact HM5s1. }
    assert (HM7sp : M7 !!! Regidx csp_rs1 = pa_stk sp0 6).
    { rewrite /M7 upd_ne; [| vm_compute; discriminate].
      rewrite /M6 upd_ne; [| vm_compute; discriminate].
      rewrite /M5 upd_ne; [| vm_compute; discriminate].
      rewrite /M4 upd_ne; [| vm_compute; discriminate].
      rewrite /M3 upd_ne; [| vm_compute; discriminate]. exact HM2sp. }
    assert (HM7cs : kk_cs_rest M7 m).
    { rewrite /M7. apply kk_cs_rest_s3.
      rewrite /M6. apply kk_cs_rest_s3.
      rewrite /M5. apply kk_cs_rest_s1.
      rewrite /M4. apply kk_cs_rest_s1.
      rewrite /M3. apply kk_cs_rest_s2.
      rewrite /M2. apply kk_cs_rest_s0.
      rewrite /M1. apply kk_cs_rest_sp.
      intros r Hr N2 N8 N9 N18 N19. reflexivity. }
    (* the same five slot addresses, over the frame base itself -- what the
       epilogue's c.ldsp displacements compute *)
    assert (Hqa : forall u k : nat, (k + u = 6)%nat -> (u < 6)%nat ->
              add_vec (pa_stk sp0 6)
                (zero_extend' 64 (concat_vec (mword_of_int (Z.of_nat u) : mword 6) ('b"000")))
              = pa_stk sp0 k).
    { intros u k Hku Hu.
      destruct u as [|[|[|[|[|[|]]]]]]; try lia;
        destruct k as [|[|[|[|[|[|[|]]]]]]]; try lia;
        unfold pa_stk, add_vec_int; rewrite add_vec_off2;
        apply f_equal; apply bv_eq; vm_compute; reflexivity. }
    assert (Hqa1 := Hqa 5%nat 1%nat ltac:(lia) ltac:(lia)).
    assert (Hqa2 := Hqa 4%nat 2%nat ltac:(lia) ltac:(lia)).
    assert (Hqa3 := Hqa 3%nat 3%nat ltac:(lia) ltac:(lia)).
    assert (Hqa4 := Hqa 2%nat 4%nat ltac:(lia) ltac:(lia)).
    assert (Hqa5 := Hqa 1%nat 5%nat ltac:(lia) ltac:(lia)).
    (* ===================== the epilogue, as the scan's exit ============ *)
    (* Built BEFORE the scan and handed to it: the loop never touches the
       frame, so the six saved cells and [Hcont] are captured here. *)
    iAssert (wp_next (CID0 := CID12) b p (fun (CIDq : CpuId) =>
               ∀ (Mx : regfile) (rv : mword 64),
                 ⌜ kk_exit_regs Mx m (pa_stk sp0 6) rv ⌝ -∗
                 sie_cap_gpr KT1 Mx (av - 6)%nat b p -∗
                 cpu_own n eb p b lks -∗
                 pc_is (mword_of_int (KernelSyms.kkill + 0x54)) -∗
                 mWP (Loop : expr riscv_lang)))%I
      with "[Hcont Hb1 Hb2 Hb3 Hb4 Hb5 Hb6]" as "Hqexit".
    { iIntros (CIDx Hsx Mx rv) "%Hx Hcg Hown Hpc".
      destruct Hx as (Hxsp & Hxa0 & Hxrv & Hxcs).
      (* +0x54 c.ldsp ra,40(sp) *)
      iEval (rewrite -Hqa1 -Hxsp) in "Hb1".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kkill + 0x54)) (mword_of_int 5 : mword 6) Rra
                Mx (av - 6)%nat (m !!! Regidx Rra) b (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] Hb1").
      { iApply (kki_54 with "Htext"). }
      iIntros (CIDy1 Hsy1) "Hcg Hpc Hb1".
      iEval (rewrite Hxsp Hqa1) in "Hb1".
      set (T1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra)]> Mx).
      change (<[Regidx Rra := regval_into_reg (m !!! Regidx Rra)]> Mx) with T1.
      assert (Hqp56 : add_vec_int (mword_of_int (KernelSyms.kkill + 0x54) : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x56))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hqp56) in "Hpc".
      assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 6)
        by (rewrite /T1 upd_ne; [exact Hxsp | vm_compute; discriminate]).
      (* +0x56 c.ldsp s0,32(sp) *)
      iEval (rewrite -Hqa2 -HT1sp) in "Hb2".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kkill + 0x56)) (mword_of_int 4 : mword 6) Rs0
                T1 (av - 6)%nat (m !!! Regidx Rs0) b (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] Hb2").
      { iApply (kki_56 with "Htext"). }
      iIntros (CIDy2 Hsy2) "Hcg Hpc Hb2".
      iEval (rewrite HT1sp Hqa2) in "Hb2".
      set (T2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0)]> T1).
      change (<[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0)]> T1) with T2.
      assert (Hqp58 : add_vec_int (mword_of_int (KernelSyms.kkill + 0x56) : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x58))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hqp58) in "Hpc".
      assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 6)
        by (rewrite /T2 upd_ne; [exact HT1sp | vm_compute; discriminate]).
      (* +0x58 c.ldsp s1,24(sp) *)
      iEval (rewrite -Hqa3 -HT2sp) in "Hb3".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kkill + 0x58)) (mword_of_int 3 : mword 6) Rs1
                T2 (av - 6)%nat (m !!! Regidx Rs1) b (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] Hb3").
      { iApply (kki_58 with "Htext"). }
      iIntros (CIDy3 Hsy3) "Hcg Hpc Hb3".
      iEval (rewrite HT2sp Hqa3) in "Hb3".
      set (T3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1)]> T2).
      change (<[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1)]> T2) with T3.
      assert (Hqp5a : add_vec_int (mword_of_int (KernelSyms.kkill + 0x58) : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x5a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hqp5a) in "Hpc".
      assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 6)
        by (rewrite /T3 upd_ne; [exact HT2sp | vm_compute; discriminate]).
      (* +0x5a c.ldsp s2,16(sp) *)
      iEval (rewrite -Hqa4 -HT3sp) in "Hb4".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kkill + 0x5a)) (mword_of_int 2 : mword 6) Rs2
                T3 (av - 6)%nat (m !!! Regidx Rs2) b (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] Hb4").
      { iApply (kki_5a with "Htext"). }
      iIntros (CIDy4 Hsy4) "Hcg Hpc Hb4".
      iEval (rewrite HT3sp Hqa4) in "Hb4".
      set (T4 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> T3).
      change (<[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> T3) with T4.
      assert (Hqp5c : add_vec_int (mword_of_int (KernelSyms.kkill + 0x5a) : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x5c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hqp5c) in "Hpc".
      assert (HT4sp : T4 !!! Regidx csp_rs1 = pa_stk sp0 6)
        by (rewrite /T4 upd_ne; [exact HT3sp | vm_compute; discriminate]).
      (* +0x5c c.ldsp s3,8(sp) *)
      iEval (rewrite -Hqa5 -HT4sp) in "Hb5".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kkill + 0x5c)) (mword_of_int 1 : mword 6) Rs3
                T4 (av - 6)%nat (m !!! Regidx Rs3) b (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] Hb5").
      { iApply (kki_5c with "Htext"). }
      iIntros (CIDy5 Hsy5) "Hcg Hpc Hb5".
      iEval (rewrite HT4sp Hqa5) in "Hb5".
      set (T5 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3)]> T4).
      change (<[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3)]> T4) with T5.
      assert (Hqp5e : add_vec_int (mword_of_int (KernelSyms.kkill + 0x5c) : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x5e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hqp5e) in "Hpc".
      assert (HT5sp : T5 !!! Regidx csp_rs1 = pa_stk sp0 6)
        by (rewrite /T5 upd_ne; [exact HT4sp | vm_compute; discriminate]).
      (* +0x5e: c.addi16sp sp,48 -- the frame pop *)
      assert (Hwv : add_vec (T5 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0)
        by (rewrite HT5sp; apply stk_pop_48).
      assert (Hpop : T5 !!! Regidx csp_rs1
                     = pa_stk (add_vec (T5 !!! Regidx csp_rs1)
                         (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6)
        by (rewrite Hwv; exact HT5sp).
      iEval (rewrite -E5) in "Hb5". iEval (rewrite -E6) in "Hb6".
      iDestruct (stack_own_4_intro sp0 (m !!! Regidx Rra) (m !!! Regidx Rs0)
                   (m !!! Regidx Rs1) (m !!! Regidx Rs2) with "Hb1 Hb2 Hb3 Hb4") as "Hf14".
      iDestruct (stack_own_2_intro (pa_stk sp0 4) (m !!! Regidx Rs3) w6 with "Hb5 Hb6") as "Hf56".
      iAssert (stack_own (KTR := KT1) sp0 6) with "[Hf14 Hf56]" as "Hframe".
      { rewrite (stack_own_split (KTR := KT1) sp0 4 6 ltac:(lia)). change (6 - 4)%nat with 2%nat. iFrame. }
      iEval (rewrite -Hwv) in "Hframe".
      iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.kkill + 0x5e)) (mword_of_int 3 : mword 6)
                T5 (av - 6)%nat 6 b Hpop with "Hcg Hpc [] Hframe").
      { iApply (kki_5e with "Htext"). }
      iIntros (CIDy6 Hsy6) "Hcg Hpc".
      assert (Hnk : ((av - 6) + 6)%nat = av) by lia.
      iEval (rewrite Hnk) in "Hcg".
      set (T6 := <[Regidx csp_rs1 := regval_into_reg
                    (add_vec (T5 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> T5).
      change (<[Regidx csp_rs1 := regval_into_reg
                (add_vec (T5 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> T5) with T6.
      assert (Hqp60 : add_vec_int (mword_of_int (KernelSyms.kkill + 0x5e) : mword 64) 2 = mword_of_int (KernelSyms.kkill + 0x60))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hqp60) in "Hpc".
      (* +0x60: c.ret *)
      assert (HT6ra : T6 !!! Regidx Rra = m !!! Regidx Rra).
      { rewrite /T6 upd_ne; [| vm_compute; discriminate].
        rewrite /T5 upd_ne; [| vm_compute; discriminate].
        rewrite /T4 upd_ne; [| vm_compute; discriminate].
        rewrite /T3 upd_ne; [| vm_compute; discriminate].
        rewrite /T2 upd_ne; [| vm_compute; discriminate].
        rewrite /T1. apply upd_eq. }
      iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.kkill + 0x60)) Rra T6 av b
                ltac:(vm_compute; discriminate) with "Hcg Hpc []").
      { iApply (kki_60 with "Htext"). }
      iIntros (CIDy7 Hsy7) "Hcg Hpc".
      iEval (rgne) in "Hpc".
      assert (Hretfin : ret_pc (T6 !!! Regidx Rra) = ret_tgt) by (rewrite HT6ra; reflexivity).
      iEval (rewrite Hretfin) in "Hpc".
      (* ===================== the postcondition ===================== *)
      assert (HT6sp : T6 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1) by (rewrite /T6 upd_eq; exact Hwv).
      assert (HT6s0 : T6 !!! Regidx Rs0 = m !!! Regidx Rs0).
      { rewrite /T6 upd_ne; [| vm_compute; discriminate].
        rewrite /T5 upd_ne; [| vm_compute; discriminate].
        rewrite /T4 upd_ne; [| vm_compute; discriminate].
        rewrite /T3 upd_ne; [| vm_compute; discriminate].
        rewrite /T2. apply upd_eq. }
      assert (HT6s1 : T6 !!! Regidx Rs1 = m !!! Regidx Rs1).
      { rewrite /T6 upd_ne; [| vm_compute; discriminate].
        rewrite /T5 upd_ne; [| vm_compute; discriminate].
        rewrite /T4 upd_ne; [| vm_compute; discriminate].
        rewrite /T3. apply upd_eq. }
      assert (HT6s2 : T6 !!! Regidx Rs2 = m !!! Regidx Rs2).
      { rewrite /T6 upd_ne; [| vm_compute; discriminate].
        rewrite /T5 upd_ne; [| vm_compute; discriminate].
        rewrite /T4. apply upd_eq. }
      assert (HT6s3 : T6 !!! Regidx Rs3 = m !!! Regidx Rs3).
      { rewrite /T6 upd_ne; [| vm_compute; discriminate].
        rewrite /T5. apply upd_eq. }
      assert (HT6a0 : T6 !!! Regidx Ra0 = rv).
      { rewrite /T6 upd_ne; [| vm_compute; discriminate].
        rewrite /T5 upd_ne; [| vm_compute; discriminate].
        rewrite /T4 upd_ne; [| vm_compute; discriminate].
        rewrite /T3 upd_ne; [| vm_compute; discriminate].
        rewrite /T2 upd_ne; [| vm_compute; discriminate].
        rewrite /T1 upd_ne; [| vm_compute; discriminate]. exact Hxa0. }
      assert (HT6rest : kk_cs_rest T6 m).
      { rewrite /T6. apply kk_cs_rest_sp.
        intros r Hr N2 N8 N9 N18 N19.
        assert (N1 : r <> mword_of_int 1)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /T5 upd_ne; [| congruence].
        rewrite /T4 upd_ne; [| congruence].
        rewrite /T3 upd_ne; [| congruence].
        rewrite /T2 upd_ne; [| congruence].
        rewrite /T1 upd_ne; [| congruence].
        by apply Hxcs. }
      iDestruct (cpu_own_transport CIDx CIDy7 n eb p b ltac:(wp_next_chain)
                   with "Hown") as "Hown".
      iSpecialize ("Hcont" $! CIDy7 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! T6 rv with "[%] Hcg Hown Hpc").
      split; [| split; [exact HT6a0 | exact Hxrv]].
      unfold callee_saved.
      split; [exact HT6sp|]. split; [exact HT6s0|]. split; [exact HT6s1|].
      split; [exact HT6s2|]. split; [exact HT6s3|].
      repeat (split; [apply HT6rest; vm_compute; first [reflexivity | discriminate]|]).
      apply HT6rest; vm_compute; first [reflexivity | discriminate]. }
    (* ===================== the scan ===================== *)
    iDestruct (cpu_own_transport CID CID12 n eb p b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    (* THE C's GUARD, RELAYED INTO THE SCAN: this is the fall-through of
       [+0x00 c.beqz a0], so the argument is not zero and no slot the loop
       can match has a zero pid (lane SELF-KILL, §4b'). *)
    assert (Hargnz : add_vec zero_reg (M2 !!! Regidx Ra0) <> (zero_reg : mword 64)).
    { intro Hz0. apply (proj1 (eq_vec_false_iff _ _) Hpid0).
      rewrite (rget_ne (CID := CID) m Ra0 ltac:(vm_compute; discriminate)).
      rewrite -Hz0 add_vec_zero_l /M2 upd_ne;
        [| vm_compute; discriminate].
      rewrite /M1 upd_ne; [ reflexivity | vm_compute; discriminate ]. }
    iPoseProof (wp_kkill_loop (CID0 := CID12)  γs m (pa_stk sp0 6)
                  (add_vec zero_reg (M2 !!! Regidx Ra0)) p n (av - 6)%nat eb b lks
                  Hargnz Hlen Hn ltac:(lia) Hno with "Hkc Hprocs Hqexit") as "Hscan".
    iApply ("Hscan" $! 0%nat M7 with "[%] [%] Hcg Hcpu Htext Hpc").
    - unfold NPROC; lia.
    - unfold kkl_regs.
      split; [exact HM7s1|]. split; [exact HM7sp|].
      split.
      { rewrite /M7 upd_ne; [| vm_compute; discriminate].
        rewrite /M6 upd_ne; [| vm_compute; discriminate].
        rewrite /M5 upd_ne; [| vm_compute; discriminate].
        rewrite /M4 upd_ne; [| vm_compute; discriminate].
        rewrite /M3. apply upd_eq. }
      split; [exact HM7s3|]. exact HM7cs.
  Qed.

End ProofKkillMain.

End KkillProof.
