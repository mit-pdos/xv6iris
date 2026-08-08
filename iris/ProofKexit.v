(* ProofKexit.v -- kexit(), the whole function, over sconf.

   The C, the instruction map and the contract are in SpecKexit.v; this file
   is the proof.  Like ProofKwait.v it is one [Lemma] per block of the
   control-flow graph, bottom up, so that each [Qed] releases its own proof
   term:

     kx_prologue  +0x00 .. +0x10   carve the 6-slot frame, save ra/s0..s4,
                                   s0 = sp+48, s4 = status
     kx_loop      +0x3e/+0x38      THE fd LOOP, fuel-inducted downward on
                                   [NOFILE - fd]
     kx_park      +0x60 .. +0xa2   wait_lock / reparent / wakeup / p->lock /
                                   the two stores / release / sched / panic
     kx_rest      +0x4c .. +0xa2   begin_op / iput / end_op / p->cwd = 0,
                                   then [kx_park]
     wp_kexit_sconf                the prologue, myproc, the initproc test,
                                   and the loop with [kx_rest] as its exit

   FOUR THINGS THIS PROOF HAD TO GET RIGHT.

   * THERE IS NO EPILOGUE, AND THAT IS THE POINT.  kexit diverges, so the
     six frame cells are never reloaded and the six stack slots are never
     given back: [kx_frame] is EXISTENTIAL in the saved values (nothing will
     ever read them) and is simply carried to the [jal sched], where the
     post-resume arm drops it into [panic_wp_any] along with everything else.
     The same is true of [own_ctx] and [park_hlf] -- they go in and do not
     come back, which is the whole difference between this park and yield's.

   * THE LOOP IS HART-GENERIC.  It runs at level 0 with [eb = true], so the
     [jal fileclose] may trap and resume the thread on another hart: the loop
     statement carries its own [CID0] binder and every crossing goes through
     [wp_next_chain] / [cpu_own_transport], exactly as reparent's scan does.
     Its exit test is an ADDRESS comparison rather than a counter --
     [&p->ofile[NOFILE]] IS [&p->cwd] ([ProcGeom.p_ofile_end]) -- so the
     index is recovered from the pointer by [p_ofile_end_inj].

   * EACH ITERATION IS A CONSERVATION STEP.  The descriptor's [file_ref] goes
     to fileclose, which hands back exactly one [fd_slot], which is what the
     emptied [ProcInv.ofile_slot] owns.  The [beqz]-taken arm skips a slot
     that is already null and owns its unit already, and puts the slot back
     unchanged ([ProcInv.upd_ofile_id]).  So the loop's postcondition --
     every descriptor null -- costs the caller nothing beyond the block it
     already had.

   * THE PID QUARTER AND THE CWD CELL COME OUT TOGETHER.  begin_op, iput and
     end_op each want [p_pid pj ↦₄{dq} _], and the cwd cell has to stay out
     across all three (it is read at +0x50 and cleared at +0x5c, and +0x5c is
     the first moment [cwd_ref] can be re-supplied).  Neither single accessor
     will do -- each consumes the whole block -- so this is what
     [ProcInv.proc_priv_cwd_pid] is for. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import SmodeCore.
Require Import InstrBytes KernelText.
Require Import StackOwn CalleeSaved.
Require Import WpMmodeLeafBase.
Require Import KernelRvcDecode.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSmodeIntr.
Require Import IntrDefs HartTp WpNext.
Require Import CpuOwn.
Require Import WpLock.
Require Import ProcGeom.
Require Import SwtchCtx.
Require Import FdSlots FileInv.
Require Import ProcInv.
Require Import SchedCtx.
Require Import WaitInv.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import SpecMyproc SpecAcquire SpecRelease SpecSched.
Require Import KallocInv.
Require Import SpecIput.
Require Import SpecFileclose SpecReparent SpecWakeup.
Require Import SpecBeginOp SpecEndOp SpecIput.
Require Import SpecPanic.
Require Import SpecProcinit.
Require Import SpecKexit.
From Kernel Require KernelInstrs KernelSyms.
Require Import CodeKexit.
Import Defs.
Local Open Scope Z_scope.
(* a failing tactic in a whole-function WP over [proc_priv] otherwise spends
   tens of minutes FORMATTING the goal -- see durable-notes. *)
Set Printing Depth 40.

Notation KX := KernelSyms.kexit.

(* [rget m k] at a NON-tp index is the plain map lookup.  Written name-free
   (durable-notes: an Ltac body cannot mention a hypothesis by literal
   name). *)
Local Ltac rgne :=
  rewrite rget_ne;
  [ | let H1 := fresh in let H2 := fresh in
      intro H1; injection H1 as H2; vm_compute in H2; congruence ].

(* ---------------------------------------------------------------------- *)
(* Pure helpers.  Stated at the TOP LEVEL with only [mword]/[Z]/[nat] in     *)
(* scope, per the zify rule in durable-notes.                               *)
(* ---------------------------------------------------------------------- *)

(* the [c.li a5,5] value truncated to 32 bits is ZOMBIE. *)
Lemma kx_zombie :
  trunc32 (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 5 : mword 6))) : mword 64)
  = (mword_of_int 5 : mword 32).
Proof. vm_compute. reflexivity. Qed.

(* the loop's postcondition, as a per-index fact: descriptors below [fd]
   have been closed and nulled. *)
Definition kx_nulled (fd : nat) (V : pprivate) : Prop :=
  forall i, (i < fd)%nat -> pv_ofile V !! i = Some (zero_reg : mword 64).

Lemma kx_nulled_0 (V : pprivate) : kx_nulled 0 V.
Proof. intros i Hi. exfalso. lia. Qed.

(* ... and at [fd = NOFILE] that IS the [replicate] the ZOMBIE park wants
   ([ProcInv.proc_priv_to_dormant_zombie]). *)
Lemma kx_nulled_all (V : pprivate) :
  length (pv_ofile V) = NOFILE ->
  kx_nulled NOFILE V ->
  pv_ofile V = replicate NOFILE (zero_reg : mword 64).
Proof.
  intros Hlen Hn. apply list_eq. intro i.
  destruct (Nat.lt_ge_cases i NOFILE) as [Hlt | Hge].
  - rewrite (Hn i Hlt). symmetry. by apply lookup_replicate_2.
  - rewrite (lookup_ge_None_2 (pv_ofile V) i ltac:(lia)).
    symmetry. apply lookup_ge_None_2. rewrite length_replicate. lia.
Qed.

Lemma kx_nulled_skip (fd : nat) (V : pprivate) :
  kx_nulled fd V -> pv_ofile V !! fd = Some (zero_reg : mword 64) ->
  kx_nulled (S fd) V.
Proof.
  intros Hn Hfd i Hi.
  destruct (Nat.eq_dec i fd) as [-> | Hne]; [exact Hfd|].
  apply Hn. lia.
Qed.

Lemma kx_nulled_close (fd : nat) (V : pprivate) :
  kx_nulled fd V -> (fd < length (pv_ofile V))%nat ->
  kx_nulled (S fd) (upd_ofile V fd (zero_reg : mword 64)).
Proof.
  intros Hn Hlt i Hi. cbn [upd_ofile pv_ofile].
  destruct (Nat.eq_dec i fd) as [-> | Hne].
  - by apply list_lookup_insert.
  - rewrite list_lookup_insert_ne; [| congruence]. apply Hn. lia.
Qed.

(* the exit test, as an index fact: the cursor has walked off the array
   exactly when its index is NOFILE.  Stated here so the loop body never
   runs [lia] with a [bv_unsigned] in context. *)
Lemma kx_end_of_eq (i fd : nat) :
  (i < NPROC)%nat -> (fd < NOFILE)%nat ->
  p_ofile (proc_addr i) (S fd) = p_cwd (proc_addr i) -> S fd = NOFILE.
Proof. intros Hi Hfd Heq. apply (p_ofile_end_inj i (S fd) Hi ltac:(lia) Heq). Qed.

(* ---------------------------------------------------------------------- *)
(* The frame.  EXISTENTIAL in the saved values: kexit never returns, so     *)
(* nothing ever reloads them and no caller has to be told what they were.   *)
(* ---------------------------------------------------------------------- *)
Definition kx_fcell (spF : mword 64) (u : Z) : mword 64 :=
  add_vec spF (zero_extend' 64 (concat_vec (mword_of_int u : mword 6) ('b"000"))).

Definition kx_frame `{!riscvGS Σ} (spF : mword 64) : iProp Σ :=
  (∃ v5 v4 v3 v2 v1 v0 : mword 64,
     kx_fcell spF 5 ↦₈ v5 ∗ kx_fcell spF 4 ↦₈ v4 ∗ kx_fcell spF 3 ↦₈ v3 ∗
     kx_fcell spF 2 ↦₈ v2 ∗ kx_fcell spF 1 ↦₈ v1 ∗ kx_fcell spF 0 ↦₈ v0)%I.

(* the register shape the fd loop threads: the cursor, its end pointer, the
   process and the exit status.  s0 is dead after the prologue and s5..s11
   are never touched, so -- there being no epilogue -- neither appears. *)
Definition kxl_regs (M : regfile) (pj sv : mword 64) (fd : nat) : Prop :=
  M !!! Regidx (mword_of_int 9)  = p_ofile pj fd /\
  M !!! Regidx (mword_of_int 18) = p_cwd pj /\
  M !!! Regidx (mword_of_int 19) = pj /\
  M !!! Regidx (mword_of_int 20) = sv /\
  (forall r : regidx, r ∈ dom (rf_to_gmap M)).

(* ... and what survives past the loop: everything below +0x4c reads only
   s3 (the process) and s4 (the status). *)
Definition kxt_regs (M : regfile) (pj sv : mword 64) : Prop :=
  M !!! Regidx (mword_of_int 19) = pj /\
  M !!! Regidx (mword_of_int 20) = sv /\
  (forall r : regidx, r ∈ dom (rf_to_gmap M)).

Module KexitProof (Myproc : MYPROC) (Fileclose : FILECLOSE)
                  (BeginOp : BEGIN_OP) (Iput : IPUT) (EndOp : END_OP)
                  (Acquire : ACQUIRE) (Reparent : REPARENT) (Wakeup : WAKEUP)
                  (Release : RELEASE) (Sched : SCHED) : KEXIT.

(* ===================================================================== *)
(* The prologue.  No call in it, so [CID] can be a section variable.      *)
(* ===================================================================== *)
Section KexitPro.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* +0x00 .. +0x10: carve the 6-slot frame, save ra/s0..s4, set s0, and
     park the argument in s4.  Control lands on the [jal myproc]. *)
  Lemma kx_prologue (Φ : mval -> iProp Σ) (m : regfile) (K : nat)
      (b : bool) (pme : mword 64) :
    let sp0 : mword 64 := m !!! Regidx csp_rs1 in
    let spF := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))) in
    (6 <= K)%nat ->
    (forall r : regidx, r ∈ dom (rf_to_gmap m)) ->
    sie_cap_gpr m K b pme -∗
    kernel_text -∗ pc_is (mword_of_int KernelSyms.kexit) -∗
    wp_next b pme (fun (CID : CpuId) =>
      ∀ M : regfile,
        ⌜ M !!! Regidx (mword_of_int 20) = m !!! Regidx (mword_of_int 10)
        /\ (forall r : regidx, r ∈ dom (rf_to_gmap M)) ⌝ -∗
        sie_cap_gpr M (K - 6) b pme -∗
        pc_is (mword_of_int (KX + 0x12)) -∗
        kx_frame spF -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 spF HK6 Hdom.
    iIntros "Hcg #Htext Hpc Hcont".
    iPoseProof (kxi_00 with "Htext") as "Hi00".
    iPoseProof (kxi_02 with "Htext") as "Hi02".
    iPoseProof (kxi_04 with "Htext") as "Hi04".
    iPoseProof (kxi_06 with "Htext") as "Hi06".
    iPoseProof (kxi_08 with "Htext") as "Hi08".
    iPoseProof (kxi_0a with "Htext") as "Hi0a".
    iPoseProof (kxi_0c with "Htext") as "Hi0c".
    iPoseProof (kxi_0e with "Htext") as "Hi0e".
    iPoseProof (kxi_10 with "Htext") as "Hi10".
    (* +0x00 c.addi16sp sp,-48 : trade 6 slots out of the capability *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    assert (Hsp1 : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))
                   = pa_stk (m !!! Regidx csp_rs1) 6).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spF) by (rewrite /R1 upd_eq; reflexivity).
    iApply (wp_caddi16sp_push_s_sconf Φ (mword_of_int KernelSyms.kexit) (mword_of_int 61 : mword 6) m K 6 b HK6 Hsp1
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hst1) "Hcg Hframe Hpc".
    assert (Hsp0f : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    iEval (rewrite Hsp0f stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(C1 & C2 & C3 & C4 & C5 & C6 & _)".
    iDestruct "C1" as (v1) "Hc1". iDestruct "C2" as (v2) "Hc2".
    iDestruct "C3" as (v3) "Hc3". iDestruct "C4" as (v4) "Hc4".
    iDestruct "C5" as (v5) "Hc5". iDestruct "C6" as (v6) "Hc6".
    assert (Hb5 : pa_stk sp0 1 = kx_fcell spF 5).
    { unfold kx_fcell, spF, pa_stk, add_vec_int. rewrite po_addv_assoc. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb4 : pa_stk sp0 2 = kx_fcell spF 4).
    { unfold kx_fcell, spF, pa_stk, add_vec_int. rewrite po_addv_assoc. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb3 : pa_stk sp0 3 = kx_fcell spF 3).
    { unfold kx_fcell, spF, pa_stk, add_vec_int. rewrite po_addv_assoc. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb2 : pa_stk sp0 4 = kx_fcell spF 2).
    { unfold kx_fcell, spF, pa_stk, add_vec_int. rewrite po_addv_assoc. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb1 : pa_stk sp0 5 = kx_fcell spF 1).
    { unfold kx_fcell, spF, pa_stk, add_vec_int. rewrite po_addv_assoc. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb0 : pa_stk sp0 6 = kx_fcell spF 0).
    { unfold kx_fcell, spF, pa_stk, add_vec_int. rewrite po_addv_assoc. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hb5) in "Hc1". iEval (rewrite Hb4) in "Hc2". iEval (rewrite Hb3) in "Hc3".
    iEval (rewrite Hb2) in "Hc4". iEval (rewrite Hb1) in "Hc5". iEval (rewrite Hb0) in "Hc6".
    assert (Hpp02 : add_vec_int (mword_of_int KernelSyms.kexit : mword 64) 2 = mword_of_int (KX + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,40(sp) *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KX + 0x02)) (mword_of_int 5 : mword 6) (mword_of_int 1 : mword 5) R1 (K - 6)%nat v1 b
              with "Hcg Hpc Hi02 [Hc1] [-]").
    { iEval (rewrite HspR1). iExact "Hc1". }
    iIntros (CID2 Hst2) "Hcg Hpc Hc1".
    iEval (rewrite HspR1) in "Hc1".
    assert (Hpp04 : add_vec_int (mword_of_int (KX + 0x02) : mword 64) 2 = mword_of_int (KX + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,32(sp) *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KX + 0x04)) (mword_of_int 4 : mword 6) (mword_of_int 8 : mword 5) R1 (K - 6)%nat v2 b
              with "Hcg Hpc Hi04 [Hc2] [-]").
    { iEval (rewrite HspR1). iExact "Hc2". }
    iIntros (CID3 Hst3) "Hcg Hpc Hc2".
    iEval (rewrite HspR1) in "Hc2".
    assert (Hpp06 : add_vec_int (mword_of_int (KX + 0x04) : mword 64) 2 = mword_of_int (KX + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,24(sp) *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KX + 0x06)) (mword_of_int 3 : mword 6) (mword_of_int 9 : mword 5) R1 (K - 6)%nat v3 b
              with "Hcg Hpc Hi06 [Hc3] [-]").
    { iEval (rewrite HspR1). iExact "Hc3". }
    iIntros (CID4 Hst4) "Hcg Hpc Hc3".
    iEval (rewrite HspR1) in "Hc3".
    assert (Hpp08 : add_vec_int (mword_of_int (KX + 0x06) : mword 64) 2 = mword_of_int (KX + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp s2,16(sp) *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KX + 0x08)) (mword_of_int 2 : mword 6) (mword_of_int 18 : mword 5) R1 (K - 6)%nat v4 b
              with "Hcg Hpc Hi08 [Hc4] [-]").
    { iEval (rewrite HspR1). iExact "Hc4". }
    iIntros (CID5 Hst5) "Hcg Hpc Hc4".
    iEval (rewrite HspR1) in "Hc4".
    assert (Hpp0a : add_vec_int (mword_of_int (KX + 0x08) : mword 64) 2 = mword_of_int (KX + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.sdsp s3,8(sp) *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KX + 0x0a)) (mword_of_int 1 : mword 6) (mword_of_int 19 : mword 5) R1 (K - 6)%nat v5 b
              with "Hcg Hpc Hi0a [Hc5] [-]").
    { iEval (rewrite HspR1). iExact "Hc5". }
    iIntros (CID6 Hst6) "Hcg Hpc Hc5".
    iEval (rewrite HspR1) in "Hc5".
    assert (Hpp0c : add_vec_int (mword_of_int (KX + 0x0a) : mword 64) 2 = mword_of_int (KX + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c c.sdsp s4,0(sp) *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KX + 0x0c)) (mword_of_int 0 : mword 6) (mword_of_int 20 : mword 5) R1 (K - 6)%nat v6 b
              with "Hcg Hpc Hi0c [Hc6] [-]").
    { iEval (rewrite HspR1). iExact "Hc6". }
    iIntros (CID7 Hst7) "Hcg Hpc Hc6".
    iEval (rewrite HspR1) in "Hc6".
    assert (Hpp0e : add_vec_int (mword_of_int (KX + 0x0c) : mword 64) 2 = mword_of_int (KX + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e c.addi4spn s0,sp,48 *)
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (KX + 0x0e)) (Cregidx (mword_of_int 0)) (mword_of_int 12 : mword 8) (mword_of_int 8 : mword 5)
              R1 (K - 6)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e [-]").
    iIntros (CID8 Hst8) "Hcg Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> R1).
    assert (Hpp10 : add_vec_int (mword_of_int (KX + 0x0e) : mword 64) 2 = mword_of_int (KX + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 c.mv s4,a0 : s4 := status *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KX + 0x10)) (mword_of_int 20 : mword 5) (mword_of_int 10 : mword 5)
              R2 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10 [-]").
    iIntros (CID9 Hst9) "Hcg Hpc".
    assert (Ha0_rg : rget (CID := CID8) R2 (mword_of_int 10 : mword 5) = R2 !!! Regidx (mword_of_int 10 : mword 5))
      by (rgne; reflexivity).
    iEval (rewrite Ha0_rg) in "Hcg".
    set (R3 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (add_vec zero_reg (R2 !!! Regidx (mword_of_int 10 : mword 5)))]> R2).
    assert (Hpp12 : add_vec_int (mword_of_int (KX + 0x10) : mword 64) 2 = mword_of_int (KX + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    iSpecialize ("Hcont" $! CID9 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! R3 with "[%] Hcg Hpc [Hc1 Hc2 Hc3 Hc4 Hc5 Hc6]").
    - split; [| intro r; apply rf_to_gmap_dom].
      rewrite /R3 upd_eq. unfold regval_into_reg. rewrite add_vec_zero_l.
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate].
    - rewrite /kx_frame. iExists _, _, _, _, _, _.
      iFrame "Hc1 Hc2 Hc3 Hc4 Hc5 Hc6".
  Qed.

End KexitPro.

(* ===================================================================== *)
(* THE fd LOOP.  No [Context CID]: the [jal fileclose] can resume the      *)
(* thread on another hart, so every crossing rebinds and the statement     *)
(* carries its own [CID0] binder.                                          *)
(* ===================================================================== *)
Section KexitLoop.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !kallocG Σ}.

  Lemma kx_loop `{GEN : GenId} `{CID0 : CpuId}
      (Φ : mval -> iProp Σ) (γft γf : gname) (fn : fclose_names)
      (j : nat) (pid : mword 32) (sv : mword 64)
      (av : nat) (eb : bool) (C : iProp Σ) (b : bool) :
    let pj := proc_addr j in
    (j < NPROC)%nat ->
    fcn_j fn = j ->
    fcn_dq fn = DfracOwn (1/4) ->
    fcn_pid fn = pid ->
    (fileclose_stack <= av)%nat ->
    kernel_text -∗
    is_ftable γft γf -∗
    panic_wp_any -∗
    (* the exit continuation: control at [begin_op]'s call site, every
       descriptor null. *)
    wp_next (CID0 := CID0) b pj (fun (CID : CpuId) =>
      ∀ (Mx : regfile) (Vx : pprivate),
        ⌜ kxt_regs Mx pj sv ⌝ -∗
        ⌜ pv_ofile Vx = replicate NOFILE (zero_reg : mword 64) ⌝ -∗
        sie_cap_gpr Mx av b pj -∗
        cpu_own 0 eb pj C b -∗
        pc_is (mword_of_int (KX + 0x4c)) -∗
        proc_priv γf pj pid Vx -∗
        (∃ on', fileclose_pipe_env Φ fn on' 0%nat) -∗
        fileclose_fs_env_nopid Φ fn 0%nat eb pj -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    ∀ (fd : nat) (M : regfile) (V : pprivate),
      ⌜(fd < NOFILE)%nat⌝ -∗ ⌜kxl_regs M pj sv fd⌝ -∗ ⌜kx_nulled fd V⌝ -∗
      sie_cap_gpr M av b pj -∗
      cpu_own 0 eb pj C b -∗
      pc_is (mword_of_int (KX + 0x3e)) -∗
      proc_priv γf pj pid V -∗
      (∃ on', fileclose_pipe_env Φ fn on' 0%nat) -∗
      fileclose_fs_env_nopid Φ fn 0%nat eb pj -∗
      WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pj Hj Hfnj Hfndq Hfnpid Hav.
    iIntros "#Htext #Hft #Hpanic Hqexit".
    iAssert (∀ (fuel : nat),
               wp_next (CID0 := CID0) b pj (fun (CID : CpuId) =>
                 ∀ (fd : nat) (M : regfile) (V : pprivate),
                   ⌜(NOFILE - fd <= fuel)%nat⌝ -∗ ⌜(fd < NOFILE)%nat⌝ -∗
                   ⌜kxl_regs M pj sv fd⌝ -∗ ⌜kx_nulled fd V⌝ -∗
                   wp_next (CID0 := CID0) b pj (fun (CIDq : CpuId) =>
                     ∀ (Mx : regfile) (Vx : pprivate),
                       ⌜ kxt_regs Mx pj sv ⌝ -∗
                       ⌜ pv_ofile Vx = replicate NOFILE (zero_reg : mword 64) ⌝ -∗
                       sie_cap_gpr Mx av b pj -∗
                       cpu_own 0 eb pj C b -∗
                       pc_is (mword_of_int (KX + 0x4c)) -∗
                       proc_priv γf pj pid Vx -∗
                       (∃ on', fileclose_pipe_env Φ fn on' 0%nat) -∗
                       fileclose_fs_env_nopid Φ fn 0%nat eb pj -∗
                       WP (Loop : expr riscv_lang) {{ Φ }}) -∗
                   sie_cap_gpr M av b pj -∗
                   cpu_own 0 eb pj C b -∗
                   pc_is (mword_of_int (KX + 0x3e)) -∗
                   proc_priv γf pj pid V -∗
                   (∃ on', fileclose_pipe_env Φ fn on' 0%nat) -∗
                   fileclose_fs_env_nopid Φ fn 0%nat eb pj -∗
                   WP (Loop : expr riscv_lang) {{ Φ }}))%I with "[]" as "Hloop".
    { iIntros (fuel). iInduction fuel as [|fuel IHf] "IHf".
      { iIntros (CIDk Hsk fd M V) "%Hfuel %Hfd %Hregs %Hnul Hqx Hcg Hown Hpc Hpriv Hpenv Hfenv".
        exfalso. lia. }
      iIntros (CIDk Hsk fd M V) "%Hfuel %Hfd %Hregs %Hnul Hqx Hcg Hown Hpc Hpriv Hpenv Hfenv".
      destruct Hregs as (Hs1 & Hs2 & Hs3 & Hs4 & Hdom).
      (* ---- the p++/test tail at +0x38, reached from BOTH arms of the
         [beqz] and from different harts, hence the [wp_next] wrapper. ---- *)
      iAssert (wp_next (CID0 := CID0) b pj (fun (CIDt : CpuId) =>
                 ∀ (Mt : regfile) (Vt : pprivate),
                   ⌜ kxl_regs Mt pj sv fd ⌝ -∗ ⌜ kx_nulled (S fd) Vt ⌝ -∗
                   sie_cap_gpr Mt av b pj -∗
                   cpu_own 0 eb pj C b -∗
                   pc_is (mword_of_int (KX + 0x38)) -∗
                   proc_priv γf pj pid Vt -∗
                   (∃ on', fileclose_pipe_env Φ fn on' 0%nat) -∗
                   fileclose_fs_env_nopid Φ fn 0%nat eb pj -∗
                   WP (Loop : expr riscv_lang) {{ Φ }}))%I
        with "[Hqx]" as "Htail".
      { iIntros (CIDt Hst Mt Vt) "%Hmt %Hnt Hcg Hown Hpc Hpriv Hpenv Hfenv".
        destruct Hmt as (Ht9 & Ht18 & Ht19 & Ht20 & Htdom).
        iPoseProof (kxi_38 with "Htext") as "Hi38".
        iPoseProof (kxi_3a with "Htext") as "Hi3a".
        (* +0x38 c.addi s1,s1,8 : the cursor moves to &p->ofile[fd+1] *)
        assert (Hrgt9 : rget (CID := CIDt) Mt (mword_of_int 9 : mword 5)
                        = Mt !!! Regidx (mword_of_int 9 : mword 5)) by (rgne; reflexivity).
        iApply (wp_caddi_s_sconf (CID := CIDt) Φ (mword_of_int (KX + 0x38))
                  (mword_of_int 9 : mword 5) (mword_of_int 8 : mword 6)
                  Mt av b ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi38 [-]").
        iIntros (CIDt1 Hst1) "Hcg Hpc".
        iEval (rewrite Hrgt9) in "Hcg".
        set (Mt38 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
             (add_vec (Mt !!! Regidx (mword_of_int 9 : mword 5))
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6))))]> Mt).
        assert (Hpp3a : add_vec_int (mword_of_int (KX + 0x38) : mword 64) 2 = mword_of_int (KX + 0x3a))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp3a) in "Hpc".
        assert (HM9 : Mt38 !!! Regidx (mword_of_int 9 : mword 5) = p_ofile pj (S fd)).
        { rewrite /Mt38 upd_eq Ht9. apply p_ofile_succ. }
        assert (HM18 : Mt38 !!! Regidx (mword_of_int 18 : mword 5) = p_cwd pj).
        { rewrite /Mt38 upd_ne; [exact Ht18 | vm_compute; discriminate]. }
        assert (HM19 : Mt38 !!! Regidx (mword_of_int 19 : mword 5) = pj).
        { rewrite /Mt38 upd_ne; [exact Ht19 | vm_compute; discriminate]. }
        assert (HM20 : Mt38 !!! Regidx (mword_of_int 20 : mword 5) = sv).
        { rewrite /Mt38 upd_ne; [exact Ht20 | vm_compute; discriminate]. }
        assert (HMdom : forall r : regidx, r ∈ dom (rf_to_gmap Mt38))
          by (intro r; apply rf_to_gmap_dom).
        assert (Hrg9' : rget (CID := CIDt1) Mt38 (mword_of_int 9 : mword 5)
                        = Mt38 !!! Regidx (mword_of_int 9 : mword 5)) by (rgne; reflexivity).
        assert (Hrg18' : rget (CID := CIDt1) Mt38 (mword_of_int 18 : mword 5)
                         = Mt38 !!! Regidx (mword_of_int 18 : mword 5)) by (rgne; reflexivity).
        (* +0x3a beq s1,s2 : exit iff the cursor has walked off the array *)
        destruct (eq_vec (Mt38 !!! Regidx (mword_of_int 9 : mword 5))
                         (Mt38 !!! Regidx (mword_of_int 18 : mword 5))) eqn:Hcmp.
        + (* TAKEN: fd+1 = NOFILE, so every descriptor is null *)
          assert (Hcmpr : eq_vec (rget (CID := CIDt1) Mt38 (mword_of_int 9 : mword 5))
                                 (rget (CID := CIDt1) Mt38 (mword_of_int 18 : mword 5)) = true)
            by (rewrite Hrg9' Hrg18'; exact Hcmp).
          iApply (wp_beq_taken_s_sconf (CID := CIDt1) Φ (mword_of_int (KX + 0x3a))
                    (mword_of_int 18 : mword 13) (mword_of_int 18 : mword 5) (mword_of_int 9 : mword 5)
                    Mt38 av b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hcmpr ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi3a [-]").
          iNext. iIntros (CIDt2 Hst2) "Hcg Hpc".
          assert (Htgt4c : add_vec (mword_of_int (KX + 0x3a) : mword 64)
                             (sign_extend' 64 (mword_of_int 18 : mword 13)) = mword_of_int (KX + 0x4c))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Htgt4c) in "Hpc".
          assert (HkS : S fd = NOFILE).
          { apply (kx_end_of_eq j fd Hj Hfd).
            apply (proj1 (eq_vec_true_iff (p_ofile pj (S fd)) (p_cwd pj))).
            rewrite -HM9 -HM18. exact Hcmp. }
          iDestruct (proc_priv_ofile_len with "Hpriv") as "%Hlen".
          iDestruct (cpu_own_transport CIDt CIDt2 0 eb pj C b ltac:(wp_next_chain)
                       with "Hown") as "Hown".
          iSpecialize ("Hqx" $! CIDt2 with "[%]"); [wp_next_chain|].
          iApply ("Hqx" $! Mt38 Vt with "[%] [%] Hcg Hown Hpc Hpriv Hpenv Hfenv").
          * split; [exact HM19|]. split; [exact HM20|]. exact HMdom.
          * apply kx_nulled_all; [exact Hlen | rewrite -HkS; exact Hnt].
        + (* FALL: one more descriptor to look at *)
          assert (Hcmpr : eq_vec (rget (CID := CIDt1) Mt38 (mword_of_int 9 : mword 5))
                                 (rget (CID := CIDt1) Mt38 (mword_of_int 18 : mword 5)) = false)
            by (rewrite Hrg9' Hrg18'; exact Hcmp).
          iApply (wp_beq_fall_s_sconf (CID := CIDt1) Φ (mword_of_int (KX + 0x3a))
                    (mword_of_int 18 : mword 13) (mword_of_int 18 : mword 5) (mword_of_int 9 : mword 5)
                    Mt38 av b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hcmpr with "Hcg Hpc Hi3a [-]").
          iIntros (CIDt2 Hst2) "Hcg Hpc".
          assert (HkS : (S fd < NOFILE)%nat).
          { destruct (Nat.lt_ge_cases (S fd) NOFILE) as [Hlt | Hge]; [exact Hlt|].
            assert (HeqN : S fd = NOFILE) by (unfold NOFILE in *; lia).
            exfalso.
            assert (Hbad : eq_vec (Mt38 !!! Regidx (mword_of_int 9 : mword 5))
                             (Mt38 !!! Regidx (mword_of_int 18 : mword 5)) = true).
            { rewrite HM9 HM18 HeqN p_ofile_end. apply eq_vec_refl. }
            rewrite Hcmp in Hbad. discriminate. }
          assert (Hpp3e : add_vec_int (mword_of_int (KX + 0x3a) : mword 64) 4 = mword_of_int (KX + 0x3e))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp3e) in "Hpc".
          iDestruct (cpu_own_transport CIDt CIDt2 0 eb pj C b ltac:(wp_next_chain)
                       with "Hown") as "Hown".
          iSpecialize ("IHf" $! CIDt2 with "[%]"); [wp_next_chain|].
          iApply ("IHf" $! (S fd) Mt38 Vt with "[%] [%] [%] [%] Hqx Hcg Hown Hpc Hpriv Hpenv Hfenv").
          * unfold NOFILE in *; lia.
          * exact HkS.
          * split; [exact HM9|]. split; [exact HM18|]. split; [exact HM19|].
            split; [exact HM20|]. exact HMdom.
          * exact Hnt. }
      (* ================= the body at +0x3e .. +0x4a ================= *)
      iDestruct (proc_priv_ofile_len with "Hpriv") as "%Hlen".
      destruct (lookup_lt_is_Some_2 (pv_ofile V) fd ltac:(rewrite Hlen; exact Hfd)) as [v Hv].
      (* the pid quarter and the descriptor come out TOGETHER: fileclose's
         file-system arm threads the pid cell down to bread's acquiresleep,
         and neither one-at-a-time accessor can be open while the other is. *)
      iDestruct (proc_priv_pid_ofile γf pj pid V fd v Hv with "Hpriv")
        as "(Hpidq & Hslot & Hback)".
      iDestruct "Hslot" as "[Hcell Hpay]".
      iPoseProof (kxi_3e with "Htext") as "Hi3e".
      iPoseProof (kxi_40 with "Htext") as "Hi40".
      (* +0x3e c.ld a0,0(s1) : a0 := p->ofile[fd] *)
      assert (Hrgk9 : rget (CID := CIDk) M (mword_of_int 9 : mword 5)
                      = M !!! Regidx (mword_of_int 9 : mword 5)) by (rgne; reflexivity).
      iApply (wp_cld_s_sconf (CID := CIDk) Φ (mword_of_int (KX + 0x3e))
                (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 0 : mword 12)
                M av v b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi3e [Hcell] [-]").
      { iEval (rewrite Hrgk9 Hs1 addv_sext0). iExact "Hcell". }
      iIntros (CIDl Hsl) "Hcg Hpc Hcell".
      iEval (rewrite Hrgk9 Hs1 addv_sext0) in "Hcell".
      set (M3e := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg v]> M).
      assert (Hpp40 : add_vec_int (mword_of_int (KX + 0x3e) : mword 64) 2 = mword_of_int (KX + 0x40))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp40) in "Hpc".
      assert (HM3e_10 : M3e !!! Regidx (mword_of_int 10 : mword 5) = v)
        by (rewrite /M3e; apply upd_eq).
      assert (HM3e_9 : M3e !!! Regidx (mword_of_int 9 : mword 5) = p_ofile pj fd)
        by (rewrite /M3e upd_ne; [exact Hs1 | vm_compute; discriminate]).
      assert (HM3e_18 : M3e !!! Regidx (mword_of_int 18 : mword 5) = p_cwd pj)
        by (rewrite /M3e upd_ne; [exact Hs2 | vm_compute; discriminate]).
      assert (HM3e_19 : M3e !!! Regidx (mword_of_int 19 : mword 5) = pj)
        by (rewrite /M3e upd_ne; [exact Hs3 | vm_compute; discriminate]).
      assert (HM3e_20 : M3e !!! Regidx (mword_of_int 20 : mword 5) = sv)
        by (rewrite /M3e upd_ne; [exact Hs4 | vm_compute; discriminate]).
      assert (Hrgl10 : rget (CID := CIDl) M3e (mword_of_int 10 : mword 5)
                       = M3e !!! Regidx (mword_of_int 10 : mword 5)) by (rgne; reflexivity).
      (* +0x40 c.beqz a0 : skip a descriptor that is already null *)
      destruct (eq_vec v (zero_reg : mword 64)) eqn:Hz.
      - (* TAKEN: nothing to close; the slot goes back unchanged *)
        assert (Hv0 : v = (zero_reg : mword 64)) by (apply eq_vec_true_iff; exact Hz).
        assert (Hzr : eq_vec (rget (CID := CIDl) M3e (mword_of_int 10 : mword 5)) zero_reg = true)
          by (rewrite Hrgl10 HM3e_10; exact Hz).
        iApply (wp_cbeqz_taken_s_sconf (CID := CIDl) Φ (mword_of_int (KX + 0x40))
                  (mword_of_int 252 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
                  M3e av b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  Hzr ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi40 [-]").
        iNext. iIntros (CIDm Hsm) "Hcg Hpc".
        assert (Htgt38 : add_vec (mword_of_int (KX + 0x40) : mword 64)
                           (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0"))))
                         = mword_of_int (KX + 0x38))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt38) in "Hpc".
        iDestruct ("Hback" $! v with "Hpidq [Hcell Hpay]") as "Hpriv".
        { rewrite /ofile_slot. iSplitL "Hcell"; [iExact "Hcell" | iExact "Hpay"]. }
        iEval (rewrite (upd_ofile_id V fd v Hv)) in "Hpriv".
        iDestruct (cpu_own_transport CIDk CIDm 0 eb pj C b ltac:(wp_next_chain)
                     with "Hown") as "Hown".
        iSpecialize ("Htail" $! CIDm with "[%]"); [wp_next_chain|].
        iApply ("Htail" $! M3e V with "[%] [%] Hcg Hown Hpc Hpriv Hpenv Hfenv").
        + split; [exact HM3e_9|]. split; [exact HM3e_18|]. split; [exact HM3e_19|].
          split; [exact HM3e_20|]. intro r; apply rf_to_gmap_dom.
        + apply kx_nulled_skip; [exact Hnul|]. rewrite -Hv0. exact Hv.
      - (* FALL: this descriptor names a file -- close it and null the cell *)
        iDestruct "Hpay" as "[[%Hz0 _] | (%kf & %q & %Cf & [%Hfn %Hkf] & Href)]".
        { exfalso. rewrite Hz0 in Hz. rewrite eq_vec_refl in Hz. discriminate. }
        assert (Hzf : eq_vec (rget (CID := CIDl) M3e (mword_of_int 10 : mword 5)) zero_reg = false)
          by (rewrite Hrgl10 HM3e_10; exact Hz).
        iApply (wp_cbeqz_fall_s_sconf (CID := CIDl) Φ (mword_of_int (KX + 0x40))
                  (mword_of_int 252 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
                  M3e av b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  Hzf with "Hcg Hpc Hi40 [-]").
        iIntros (CIDm Hsm) "Hcg Hpc".
        assert (Hpp42 : add_vec_int (mword_of_int (KX + 0x40) : mword 64) 2 = mword_of_int (KX + 0x42))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp42) in "Hpc".
        iPoseProof (kxi_42 with "Htext") as "Hi42".
        iPoseProof (kxi_46 with "Htext") as "Hi46".
        iPoseProof (kxi_4a with "Htext") as "Hi4a".
        (* +0x42 jal ra,fileclose *)
        iApply (wp_jal_s_sconf (CID := CIDm) Φ (mword_of_int (KX + 0x42))
                  (mword_of_int 1 : mword 5) (mword_of_int 8210 : mword 21) M3e av b
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi42 [-]").
        iIntros (CIDn Hsn) "Hcg Hpc".
        set (M42 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
             (add_vec_int (mword_of_int (KX + 0x42) : mword 64) 4)]> M3e).
        assert (Hjfc : add_vec (mword_of_int (KX + 0x42) : mword 64)
                         (sign_extend' 64 (mword_of_int 8210 : mword 21)) = mword_of_int KernelSyms.fileclose)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjfc) in "Hpc".
        assert (HM42ra : M42 !!! Regidx (mword_of_int 1 : mword 5)
                         = add_vec_int (mword_of_int (KX + 0x42) : mword 64) 4)
          by (rewrite /M42; apply upd_eq).
        assert (HM42a0 : M42 !!! Regidx (mword_of_int 10 : mword 5) = fnode kf).
        { rewrite /M42 upd_ne; [| vm_compute; discriminate]. rewrite HM3e_10. exact Hfn. }
        iDestruct (cpu_own_transport CIDk CIDn 0 eb pj C b ltac:(wp_next_chain)
                     with "Hown") as "Hown".
        iDestruct "Hpenv" as (onk) "Hpenv".
        iDestruct (fileclose_loop_open Φ fn onk 0%nat eb pj Cf
                     with "Hpenv Hfenv [Hpidq]") as "[Hfcenv Hfcback]".
        { rewrite Hfnj Hfndq Hfnpid. iExact "Hpidq". }
        iApply (Fileclose.wp_fileclose_sconf (CID := CIDn) Φ γft γf kf q Cf fn onk M42 0 eb pj C av b
                  ltac:(lia) ltac:(lia) HM42a0
                  with "Hcg Hown Htext Hpc Hft Hpanic Href Hfcenv [-]").
        iIntros (CIDo Hso mr) "Hcg Hown Hpc %Hcs Hfdslot Hout".
        iDestruct ("Hfcback" with "Hout") as "(Hpenv & Hfenv & Hpidq)".
        iEval (rewrite Hfnj Hfndq Hfnpid) in "Hpidq".
        assert (Hpc46 : ret_pc (M42 !!! Regidx (mword_of_int 1 : mword 5))
                        = mword_of_int (KX + 0x46))
          by (rewrite HM42ra; apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc46) in "Hpc".
        assert (Hmr9 : mr !!! Regidx (mword_of_int 9 : mword 5) = p_ofile pj fd).
        { rewrite (callee_saved_lookup Hcs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /M42 upd_ne; [| vm_compute; discriminate]. exact HM3e_9. }
        assert (Hmr18 : mr !!! Regidx (mword_of_int 18 : mword 5) = p_cwd pj).
        { rewrite (callee_saved_lookup Hcs (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /M42 upd_ne; [| vm_compute; discriminate]. exact HM3e_18. }
        assert (Hmr19 : mr !!! Regidx (mword_of_int 19 : mword 5) = pj).
        { rewrite (callee_saved_lookup Hcs (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /M42 upd_ne; [| vm_compute; discriminate]. exact HM3e_19. }
        assert (Hmr20 : mr !!! Regidx (mword_of_int 20 : mword 5) = sv).
        { rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /M42 upd_ne; [| vm_compute; discriminate]. exact HM3e_20. }
        assert (Hrgo9 : rget (CID := CIDo) mr (mword_of_int 9 : mword 5)
                        = mr !!! Regidx (mword_of_int 9 : mword 5)) by (rgne; reflexivity).
        (* +0x46 sd x0,0(s1) : p->ofile[fd] = 0 *)
        iApply (wp_sd_zero_s_sconf (CID := CIDo) Φ (mword_of_int (KX + 0x46))
                  (mword_of_int 9 : mword 5) (mword_of_int 0 : mword 12) mr av v b
                  with "Hcg Hpc Hi46 [Hcell] [-]").
        { iEval (rewrite Hrgo9 Hmr9 addv_sext0). iExact "Hcell". }
        iIntros (CIDp Hsp2) "Hcg Hpc Hcell".
        iEval (rewrite Hrgo9 Hmr9 addv_sext0) in "Hcell".
        assert (Hpp4a : add_vec_int (mword_of_int (KX + 0x46) : mword 64) 4 = mword_of_int (KX + 0x4a))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp4a) in "Hpc".
        (* the emptied descriptor owns the unit fileclose handed back *)
        iDestruct ("Hback" $! (zero_reg : mword 64) with "Hpidq [Hcell Hfdslot]") as "Hpriv".
        { rewrite /ofile_slot. iSplitL "Hcell"; [iExact "Hcell"|].
          iLeft. iFrame "Hfdslot". done. }
        (* +0x4a c.j -> +0x38 *)
        iApply (wp_cj_s_sconf (CID := CIDp) Φ (mword_of_int (KX + 0x4a))
                  (sign_extend' 21 (concat_vec (mword_of_int 2039 : mword 11) ('b"0")))
                  mr av b ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi4a [-]").
        iIntros (CIDr Hsr).
        iNext. iIntros "Hcg Hpc".
        assert (Htgt38 : add_vec (mword_of_int (KX + 0x4a) : mword 64)
                           (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2039 : mword 11) ('b"0"))))
                         = mword_of_int (KX + 0x38))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt38) in "Hpc".
        iDestruct (cpu_own_transport CIDo CIDr 0 eb pj C b ltac:(wp_next_chain)
                     with "Hown") as "Hown".
        iSpecialize ("Htail" $! CIDr with "[%]"); [wp_next_chain|].
        iApply ("Htail" $! mr (upd_ofile V fd (zero_reg : mword 64))
                  with "[%] [%] Hcg Hown Hpc Hpriv Hpenv Hfenv").
        + split; [exact Hmr9|]. split; [exact Hmr18|]. split; [exact Hmr19|].
          split; [exact Hmr20|]. intro r; apply rf_to_gmap_dom.
        + apply kx_nulled_close; [exact Hnul|]. rewrite Hlen. exact Hfd. }
    iIntros (fd M V) "%Hfd %Hregs %Hnul Hcg Hown Hpc Hpriv".
    iSpecialize ("Hloop" $! (NOFILE - fd)%nat).
    iSpecialize ("Hloop" $! CID0 with "[%]"); [by intros|].
    iApply ("Hloop" $! fd M V with "[%] [%] [%] [%] Hqexit Hcg Hown Hpc Hpriv");
      [lia | exact Hfd | exact Hregs | exact Hnul].
  Qed.

End KexitLoop.

(* ===================================================================== *)
(* THE PARK.  +0x60 .. +0xa2: wait_lock, reparent, wakeup, p->lock, the    *)
(* two stores, the release, sched -- and the [panic("zombie exit")] a      *)
(* resumed zombie would run, which is what lets the saved context be       *)
(* FORGOTTEN rather than proved unreachable.                               *)
(*                                                                        *)
(* Own [CID0] binder: the first acquire's crossing is at the caller's [b], *)
(* so the lock is won at a hart the entry could not name.  From there to   *)
(* the release the lock is HELD, the index is the literal [false] and      *)
(* every leaf and callee collapses through [wp_next_off].                  *)
(* ===================================================================== *)
Section KexitPark.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ}.

  (* the [C]-payload extraction sched's [emp] slot needs.  Its OWN hart
     binder: the call site is past an interrupts-enabled stretch, so a lemma
     sharing an enclosing Section's [Context CID] would silently pin to the
     entry hart. *)
  Lemma kx_cpu_own_ctx_take `{GEN : GenId} `{CID0 : CpuId}
      (n : nat) (eb : bool) (p : mword 64) (D : iProp Σ) :
    cpu_own n eb p D false -∗ D ∗ cpu_own n eb p emp false.
  Proof.
    iIntros "[Hh HD]". iFrame "HD". rewrite cpu_own_off. iFrame "Hh".
  Qed.

  Lemma kx_park `{GEN : GenId} `{CID0 : CpuId}
      (Φ : mval -> iProp Σ) (γf γw : gname) (γs : list gname)
      (j : nat) (γl : gname) (ip sv : mword 64) (dqi : dfrac)
      (M : regfile) (av : nat) (eb : bool) (C : iProp Σ) (b : bool)
      (pid : mword 32) (V : pprivate) :
    let pj := proc_addr j in
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    eb = true ->
    (24 <= av)%nat ->
    kxt_regs M pj sv ->
    pv_ofile V = replicate NOFILE (zero_reg : mword 64) ->
    pv_cwd V = (zero_reg : mword 64) ->
    sie_cap_gpr M av b pj -∗
    cpu_own 0 eb pj C b -∗
    kernel_text -∗ pc_is (mword_of_int (KX + 0x60)) -∗
    procs_inv Φ γs -∗ scheds_inv Φ γs -∗ panic_wp_any -∗
    own_ctx (p_context pj) -∗
    park_hlf j true -∗
    is_lock γw wait_lock_addr "wait_lock"%string wait_res -∗
    (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip -∗
    fd_slots FDSPARE -∗
    proc_priv γf pj pid V -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pj Hj Hgl Heb Hav Hregs Hof Hcwd. subst eb.
    destruct Hregs as (Hs3 & Hs4 & Hdom).
    iIntros "Hcg Hown #Htext Hpc #Hprocs #Hscheds #Hpanic Hoc Hpark #Hwl Hinit Hsp Hpriv".
    iDestruct (procs_inv_len with "Hprocs") as "%Hlen".
    iPoseProof (kxi_60 with "Htext") as "Hi60".
    iPoseProof (kxi_64 with "Htext") as "Hi64".
    iPoseProof (kxi_68 with "Htext") as "Hi68".
    (* +0x60 auipc a0,0x10 ; +0x64 addi a0,a0,740 : a0 := &wait_lock *)
    iApply (wp_auipc_s_sconf (CID := CID0) Φ (mword_of_int (KX + 0x60))
              (mword_of_int 10 : mword 5) (mword_of_int 0x10 : mword 20)
              M av b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi60 [-]").
    iIntros (CIDu Hsu) "Hcg Hpc".
    set (P0 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
         (add_vec (mword_of_int (KX + 0x60) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))]> M).
    assert (Hpp64 : add_vec_int (mword_of_int (KX + 0x60) : mword 64) 4 = mword_of_int (KX + 0x64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp64) in "Hpc".
    iApply (wp_addi4_s_sconf (CID := CIDu) Φ (mword_of_int (KX + 0x64))
              (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 740 : mword 12)
              P0 av b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi64 [-]").
    iIntros (CIDv Hsv2) "Hcg Hpc".
    assert (Hrgu10 : rget (CID := CIDu) P0 (mword_of_int 10 : mword 5)
                     = P0 !!! Regidx (mword_of_int 10 : mword 5)) by (rgne; reflexivity).
    iEval (rewrite Hrgu10) in "Hcg".
    set (P1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
         (add_vec (P0 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 740 : mword 12)))]> P0).
    assert (HP1a0 : P1 !!! Regidx (mword_of_int 10 : mword 5) = wait_lock_addr).
    { rewrite /P1 upd_eq /P0 upd_eq. unfold wait_lock_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp68 : add_vec_int (mword_of_int (KX + 0x64) : mword 64) 4 = mword_of_int (KX + 0x68))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp68) in "Hpc".
    (* +0x68 jal ra,acquire *)
    iApply (wp_jal_s_sconf (CID := CIDv) Φ (mword_of_int (KX + 0x68))
              (mword_of_int 1 : mword 5) (mword_of_int 2091908 : mword 21) P1 av b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi68 [-]").
    iIntros (CIDw Hsw) "Hcg Hpc".
    set (P2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
         (add_vec_int (mword_of_int (KX + 0x68) : mword 64) 4)]> P1).
    assert (Hjaq : add_vec (mword_of_int (KX + 0x68) : mword 64)
                     (sign_extend' 64 (mword_of_int 2091908 : mword 21)) = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjaq) in "Hpc".
    assert (HP2ra : P2 !!! Regidx (mword_of_int 1 : mword 5)
                    = add_vec_int (mword_of_int (KX + 0x68) : mword 64) 4)
      by (rewrite /P2; apply upd_eq).
    assert (HP2a0 : P2 !!! Regidx (mword_of_int 10 : mword 5) = wait_lock_addr)
      by (rewrite /P2 upd_ne; [exact HP1a0 | vm_compute; discriminate]).
    assert (HP2s3 : P2 !!! Regidx (mword_of_int 19 : mword 5) = pj).
    { rewrite /P2 upd_ne; [| vm_compute; discriminate].
      rewrite /P1 upd_ne; [| vm_compute; discriminate].
      rewrite /P0 upd_ne; [exact Hs3 | vm_compute; discriminate]. }
    assert (HP2s4 : P2 !!! Regidx (mword_of_int 20 : mword 5) = sv).
    { rewrite /P2 upd_ne; [| vm_compute; discriminate].
      rewrite /P1 upd_ne; [| vm_compute; discriminate].
      rewrite /P0 upd_ne; [exact Hs4 | vm_compute; discriminate]. }
    iDestruct (cpu_own_transport CID0 CIDw 0 true pj C b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (Acquire.wp_acquire_sconf (CID := CIDw) Φ γw "wait_lock"%string wait_res
              P2 0 true pj C av b ltac:(lia) ltac:(lia)
              with "Hcg Hown Htext Hpc [] Hpanic [-]").
    { iEval (rewrite HP2a0). iExact "Hwl". }
    (* FROM HERE TO THE RELEASE THE LOCK IS HELD: index [false] throughout. *)
    iIntros (CIDa Hsa msa macq) "%Hmsfa Hcg Hpc %Hcsa Hlkw Hres Hown Hpay".
    assert (Hpc6c : ret_pc (P2 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KX + 0x6c))
      by (rewrite HP2ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc6c) in "Hpc".
    iDestruct "Hres" as (ps) "Hpar".
    iDestruct (parents_own_length with "Hpar") as "%Hpslen".
    assert (Hacq_s3 : macq !!! Regidx (mword_of_int 19 : mword 5) = pj).
    { rewrite (callee_saved_lookup Hcsa (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HP2s3. }
    assert (Hacq_s4 : macq !!! Regidx (mword_of_int 20 : mword 5) = sv).
    { rewrite (callee_saved_lookup Hcsa (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HP2s4. }
    iPoseProof (kxi_6c with "Htext") as "Hi6c".
    iPoseProof (kxi_6e with "Htext") as "Hi6e".
    (* +0x6c c.mv a0,s3 : a0 := p *)
    iApply (wp_cmv_s_sconf (CID := CIDa) Φ (mword_of_int (KX + 0x6c))
              (mword_of_int 10 : mword 5) (mword_of_int 19 : mword 5)
              macq av false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6c [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    assert (Hrga19 : rget (CID := CIDa) macq (mword_of_int 19 : mword 5)
                     = macq !!! Regidx (mword_of_int 19 : mword 5)) by (rgne; reflexivity).
    iEval (rewrite Hrga19) in "Hcg".
    set (P3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
         (add_vec zero_reg (macq !!! Regidx (mword_of_int 19 : mword 5)))]> macq).
    assert (HP3a0 : P3 !!! Regidx (mword_of_int 10 : mword 5) = pj).
    { rewrite /P3 upd_eq. unfold regval_into_reg. rewrite add_vec_zero_l. exact Hacq_s3. }
    assert (HP3s3 : P3 !!! Regidx (mword_of_int 19 : mword 5) = pj)
      by (rewrite /P3 upd_ne; [exact Hacq_s3 | vm_compute; discriminate]).
    assert (HP3s4 : P3 !!! Regidx (mword_of_int 20 : mword 5) = sv)
      by (rewrite /P3 upd_ne; [exact Hacq_s4 | vm_compute; discriminate]).
    assert (Hpp6e : add_vec_int (mword_of_int (KX + 0x6c) : mword 64) 2 = mword_of_int (KX + 0x6e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp6e) in "Hpc".
    (* +0x6e jal ra,reparent *)
    iApply (wp_jal_s_sconf (CID := CIDa) Φ (mword_of_int (KX + 0x6e))
              (mword_of_int 1 : mword 5) (mword_of_int 2096956 : mword 21) P3 av false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi6e [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (P4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
         (add_vec_int (mword_of_int (KX + 0x6e) : mword 64) 4)]> P3).
    assert (Hjrp : add_vec (mword_of_int (KX + 0x6e) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096956 : mword 21)) = mword_of_int KernelSyms.reparent)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjrp) in "Hpc".
    assert (HP4ra : P4 !!! Regidx (mword_of_int 1 : mword 5)
                    = add_vec_int (mword_of_int (KX + 0x6e) : mword 64) 4)
      by (rewrite /P4; apply upd_eq).
    assert (HP4a0 : P4 !!! Regidx (mword_of_int 10 : mword 5) = pj)
      by (rewrite /P4 upd_ne; [exact HP3a0 | vm_compute; discriminate]).
    assert (HP4s3 : P4 !!! Regidx (mword_of_int 19 : mword 5) = pj)
      by (rewrite /P4 upd_ne; [exact HP3s3 | vm_compute; discriminate]).
    assert (HP4s4 : P4 !!! Regidx (mword_of_int 20 : mword 5) = sv)
      by (rewrite /P4 upd_ne; [exact HP3s4 | vm_compute; discriminate]).
    iApply (Reparent.wp_reparent_sconf (CID := CIDa) Φ P4 γs pj ip ps dqi 1%nat av true C false
              ltac:(unfold K_reparent; lia) ltac:(intro r; apply rf_to_gmap_dom) Hlen ltac:(lia)
              with "Hcg Hown Htext Hpc Hpanic Hprocs Hinit Hpar [-]").
    iApply wp_next_off_intro.
    iIntros (Mrp) "[%Hcsr %Hdomr] Hcg Hown Htext2 Hpc Hinit Hpar".
    (* reparent's output table is indexed by the a0 IT saw, which is [p] *)
    iEval (rewrite HP4a0) in "Hpar".
    assert (Hpc72 : ret_pc (P4 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KX + 0x72))
      by (rewrite HP4ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc72) in "Hpc".
    assert (Hrp_s3 : Mrp !!! Regidx (mword_of_int 19 : mword 5) = pj).
    { rewrite (callee_saved_lookup Hcsr (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HP4s3. }
    assert (Hrp_s4 : Mrp !!! Regidx (mword_of_int 20 : mword 5) = sv).
    { rewrite (callee_saved_lookup Hcsr (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HP4s4. }
    (* +0x72 ld a0,56(s3) : a0 := p->parent, out of the table wait_lock
       protects (reparent has already rewritten it). *)
    destruct (lookup_lt_is_Some_2 (rp_map pj ip ps) j
                ltac:(rewrite rp_map_length Hpslen; exact Hj)) as [w Hw].
    iDestruct (parents_own_read (rp_map pj ip ps) j w Hw with "Hpar") as "[Hpcell Hpback]".
    iPoseProof (kxi_72 with "Htext") as "Hi72".
    iPoseProof (kxi_76 with "Htext") as "Hi76".
    assert (Hrgr19 : rget (CID := CIDa) Mrp (mword_of_int 19 : mword 5)
                     = Mrp !!! Regidx (mword_of_int 19 : mword 5)) by (rgne; reflexivity).
    iApply (wp_ld_s_sconf (CID := CIDa) Φ (mword_of_int (KX + 0x72))
              (mword_of_int 10 : mword 5) (mword_of_int 19 : mword 5) (mword_of_int 56 : mword 12)
              Mrp av w false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi72 [Hpcell] [-]").
    { iEval (rewrite Hrgr19 Hrp_s3 p_parent_sext). iExact "Hpcell". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hpcell".
    iEval (rewrite Hrgr19 Hrp_s3 p_parent_sext) in "Hpcell".
    iDestruct ("Hpback" with "Hpcell") as "Hpar".
    set (P5 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg w]> Mrp).
    assert (Hpp76 : add_vec_int (mword_of_int (KX + 0x72) : mword 64) 4 = mword_of_int (KX + 0x76))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp76) in "Hpc".
    assert (HP5s3 : P5 !!! Regidx (mword_of_int 19 : mword 5) = pj)
      by (rewrite /P5 upd_ne; [exact Hrp_s3 | vm_compute; discriminate]).
    assert (HP5s4 : P5 !!! Regidx (mword_of_int 20 : mword 5) = sv)
      by (rewrite /P5 upd_ne; [exact Hrp_s4 | vm_compute; discriminate]).
    (* +0x76 jal ra,wakeup(p->parent) : nothing it touches is visible here *)
    iApply (wp_jal_s_sconf (CID := CIDa) Φ (mword_of_int (KX + 0x76))
              (mword_of_int 1 : mword 5) (mword_of_int 2096842 : mword 21) P5 av false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi76 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (P6 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
         (add_vec_int (mword_of_int (KX + 0x76) : mword 64) 4)]> P5).
    assert (Hjwk : add_vec (mword_of_int (KX + 0x76) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096842 : mword 21)) = mword_of_int KernelSyms.wakeup)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjwk) in "Hpc".
    assert (HP6ra : P6 !!! Regidx (mword_of_int 1 : mword 5)
                    = add_vec_int (mword_of_int (KX + 0x76) : mword 64) 4)
      by (rewrite /P6; apply upd_eq).
    assert (HP6s3 : P6 !!! Regidx (mword_of_int 19 : mword 5) = pj)
      by (rewrite /P6 upd_ne; [exact HP5s3 | vm_compute; discriminate]).
    assert (HP6s4 : P6 !!! Regidx (mword_of_int 20 : mword 5) = sv)
      by (rewrite /P6 upd_ne; [exact HP5s4 | vm_compute; discriminate]).
    iApply (Wakeup.wp_wakeup_sconf (CID := CIDa) Φ P6 γs
              (mycpu_ret (rget (CID := CIDa) P6 Rtp)) pj 1%nat av true C false
              ltac:(lia) ltac:(intro r; apply rf_to_gmap_dom) Hlen ltac:(reflexivity)
              ltac:(rewrite rget_tp; apply mycpu_ret_nonzero; apply tp_ok_cid_of)
              ltac:(lia)
              with "Hcg Hown Htext Hpc Hpanic Hprocs [-]").
    iApply wp_next_off_intro.
    iIntros (Mwk) "[%Hcsw %Hdomw] Hcg Hown Htext3 Hpc".
    assert (Hpc7a : ret_pc (P6 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KX + 0x7a))
      by (rewrite HP6ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc7a) in "Hpc".
    assert (Hwk_s3 : Mwk !!! Regidx (mword_of_int 19 : mword 5) = pj).
    { rewrite (callee_saved_lookup Hcsw (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HP6s3. }
    assert (Hwk_s4 : Mwk !!! Regidx (mword_of_int 20 : mword 5) = sv).
    { rewrite (callee_saved_lookup Hcsw (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HP6s4. }
    iPoseProof (kxi_7a with "Htext") as "Hi7a".
    iPoseProof (kxi_7c with "Htext") as "Hi7c".
    (* +0x7a c.mv a0,s3 ; +0x7c jal ra,acquire(&p->lock) *)
    iApply (wp_cmv_s_sconf (CID := CIDa) Φ (mword_of_int (KX + 0x7a))
              (mword_of_int 10 : mword 5) (mword_of_int 19 : mword 5)
              Mwk av false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi7a [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    assert (Hrgw19 : rget (CID := CIDa) Mwk (mword_of_int 19 : mword 5)
                     = Mwk !!! Regidx (mword_of_int 19 : mword 5)) by (rgne; reflexivity).
    iEval (rewrite Hrgw19) in "Hcg".
    set (P7 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
         (add_vec zero_reg (Mwk !!! Regidx (mword_of_int 19 : mword 5)))]> Mwk).
    assert (HP7a0 : P7 !!! Regidx (mword_of_int 10 : mword 5) = pj).
    { rewrite /P7 upd_eq. unfold regval_into_reg. rewrite add_vec_zero_l. exact Hwk_s3. }
    assert (HP7s3 : P7 !!! Regidx (mword_of_int 19 : mword 5) = pj)
      by (rewrite /P7 upd_ne; [exact Hwk_s3 | vm_compute; discriminate]).
    assert (HP7s4 : P7 !!! Regidx (mword_of_int 20 : mword 5) = sv)
      by (rewrite /P7 upd_ne; [exact Hwk_s4 | vm_compute; discriminate]).
    assert (Hpp7c : add_vec_int (mword_of_int (KX + 0x7a) : mword 64) 2 = mword_of_int (KX + 0x7c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7c) in "Hpc".
    iApply (wp_jal_s_sconf (CID := CIDa) Φ (mword_of_int (KX + 0x7c))
              (mword_of_int 1 : mword 5) (mword_of_int 2091888 : mword 21) P7 av false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi7c [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (P8 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
         (add_vec_int (mword_of_int (KX + 0x7c) : mword 64) 4)]> P7).
    assert (Hjaq2 : add_vec (mword_of_int (KX + 0x7c) : mword 64)
                      (sign_extend' 64 (mword_of_int 2091888 : mword 21)) = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjaq2) in "Hpc".
    assert (HP8ra : P8 !!! Regidx (mword_of_int 1 : mword 5)
                    = add_vec_int (mword_of_int (KX + 0x7c) : mword 64) 4)
      by (rewrite /P8; apply upd_eq).
    assert (HP8a0 : P8 !!! Regidx (mword_of_int 10 : mword 5) = pj)
      by (rewrite /P8 upd_ne; [exact HP7a0 | vm_compute; discriminate]).
    assert (HP8s3 : P8 !!! Regidx (mword_of_int 19 : mword 5) = pj)
      by (rewrite /P8 upd_ne; [exact HP7s3 | vm_compute; discriminate]).
    assert (HP8s4 : P8 !!! Regidx (mword_of_int 20 : mword 5) = sv)
      by (rewrite /P8 upd_ne; [exact HP7s4 | vm_compute; discriminate]).
    iPoseProof (procs_inv_lookup Φ γs j γl Hgl with "Hprocs") as "#Hislock".
    iApply (Acquire.wp_acquire_sconf (CID := CIDa) Φ γl "proc"%string
              (proc_lock_res Φ γs γl pj) P8 1%nat true pj C av false
              ltac:(lia) ltac:(lia)
              with "Hcg Hown Htext Hpc [] Hpanic [-]").
    { iEval (rewrite HP8a0). iExact "Hislock". }
    iApply wp_next_off_intro.
    iIntros (msb mlk) "%Hmsfb Hcg Hpc %Hcsl Hlkp HR Hown Hpay2".
    assert (Hpc80 : ret_pc (P8 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KX + 0x80))
      by (rewrite HP8ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc80) in "Hpc".
    assert (Hlk_s3 : mlk !!! Regidx (mword_of_int 19 : mword 5) = pj).
    { rewrite (callee_saved_lookup Hcsl (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HP8s3. }
    assert (Hlk_s4 : mlk !!! Regidx (mword_of_int 20 : mword 5) = sv).
    { rewrite (callee_saved_lookup Hcsl (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HP8s4. }
    (* unpack p->lock.  The detachable slots go: the process is RUNNING, so
       all three are [emp], and nothing here has to know that. *)
    iDestruct (proc_lock_res_elim Φ γs γl pj with "HR") as (st0 ch0) "(Hstate & Hchan & Hpub & Hslot)".
    iClear "Hslot".
    iDestruct "Hpub" as (kl xs pidv) "(Hkilled & Hxstate & Hpidh)".
    iPoseProof (kxi_80 with "Htext") as "Hi80".
    iPoseProof (kxi_84 with "Htext") as "Hi84".
    iPoseProof (kxi_86 with "Htext") as "Hi86".
    (* +0x80 sw s4,44(s3) : p->xstate = status *)
    assert (Hrgl19 : rget (CID := CIDa) mlk (mword_of_int 19 : mword 5)
                     = mlk !!! Regidx (mword_of_int 19 : mword 5)) by (rgne; reflexivity).
    assert (Hxaddr : add_vec (rget (CID := CIDa) mlk (mword_of_int 19 : mword 5))
                       (sign_extend' 64 (mword_of_int 44 : mword 12)) = p_xstate pj)
      by (rewrite Hrgl19 Hlk_s3; apply p_xstate_sext).
    iApply (wp_sw_s_sconf (CID := CIDa) Φ (mword_of_int (KX + 0x80))
              (mword_of_int 20 : mword 5) (mword_of_int 19 : mword 5) (mword_of_int 44 : mword 12)
              mlk av xs false with "Hcg Hpc Hi80 [Hxstate] [-]").
    { iEval (rewrite Hxaddr). iExact "Hxstate". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hxstate".
    iEval (rewrite Hxaddr) in "Hxstate".
    assert (Hpp84 : add_vec_int (mword_of_int (KX + 0x80) : mword 64) 4 = mword_of_int (KX + 0x84))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp84) in "Hpc".
    (* +0x84 c.li a5,5 ; +0x86 sw a5,24(s3) : p->state = ZOMBIE *)
    iApply (wp_cli_s_sconf (CID := CIDa) Φ (mword_of_int (KX + 0x84))
              (mword_of_int 15 : mword 5) (mword_of_int 5 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 5 : mword 6))))
              mlk av false ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc Hi84 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (P9 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
         (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 5 : mword 6))))]> mlk).
    assert (Hpp86 : add_vec_int (mword_of_int (KX + 0x84) : mword 64) 2 = mword_of_int (KX + 0x86))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp86) in "Hpc".
    assert (HP9s3 : P9 !!! Regidx (mword_of_int 19 : mword 5) = pj)
      by (rewrite /P9 upd_ne; [exact Hlk_s3 | vm_compute; discriminate]).
    assert (Hrg9_19 : rget (CID := CIDa) P9 (mword_of_int 19 : mword 5)
                      = P9 !!! Regidx (mword_of_int 19 : mword 5)) by (rgne; reflexivity).
    assert (Hsaddr : add_vec (rget (CID := CIDa) P9 (mword_of_int 19 : mword 5))
                       (sign_extend' 64 (mword_of_int 24 : mword 12)) = p_state pj)
      by (rewrite Hrg9_19 HP9s3; apply p_state_sext).
    assert (Hsval : trunc32 (rget (CID := CIDa) P9 (mword_of_int 15 : mword 5)) = ZOMBIE).
    { rewrite rget_ne;
        [| let H1 := fresh in let H2 := fresh in
           intro H1; injection H1 as H2; vm_compute in H2; congruence].
      rewrite /P9 upd_eq. unfold ZOMBIE. exact kx_zombie. }
    iApply (wp_sw_s_sconf (CID := CIDa) Φ (mword_of_int (KX + 0x86))
              (mword_of_int 15 : mword 5) (mword_of_int 19 : mword 5) (mword_of_int 24 : mword 12)
              P9 av st0 false with "Hcg Hpc Hi86 [Hstate] [-]").
    { iEval (rewrite Hsaddr). iExact "Hstate". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hstate".
    iEval (rewrite Hsaddr Hsval) in "Hstate".
    assert (Hpp8a : add_vec_int (mword_of_int (KX + 0x86) : mword 64) 4 = mword_of_int (KX + 0x8a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp8a) in "Hpc".
    (* +0x8a auipc a0,0x10 ; +0x8e addi a0,a0,698 : a0 := &wait_lock again *)
    iPoseProof (kxi_8a with "Htext") as "Hi8a".
    iPoseProof (kxi_8e with "Htext") as "Hi8e".
    iPoseProof (kxi_92 with "Htext") as "Hi92".
    iApply (wp_auipc_s_sconf (CID := CIDa) Φ (mword_of_int (KX + 0x8a))
              (mword_of_int 10 : mword 5) (mword_of_int 0x10 : mword 20)
              P9 av false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi8a [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (PA := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
         (add_vec (mword_of_int (KX + 0x8a) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))]> P9).
    assert (Hpp8e : add_vec_int (mword_of_int (KX + 0x8a) : mword 64) 4 = mword_of_int (KX + 0x8e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp8e) in "Hpc".
    iApply (wp_addi4_s_sconf (CID := CIDa) Φ (mword_of_int (KX + 0x8e))
              (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 698 : mword 12)
              PA av false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi8e [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    assert (HrgA10 : rget (CID := CIDa) PA (mword_of_int 10 : mword 5)
                     = PA !!! Regidx (mword_of_int 10 : mword 5)) by (rgne; reflexivity).
    iEval (rewrite HrgA10) in "Hcg".
    set (PB := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
         (add_vec (PA !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 698 : mword 12)))]> PA).
    assert (HPBa0 : PB !!! Regidx (mword_of_int 10 : mword 5) = wait_lock_addr).
    { rewrite /PB upd_eq /PA upd_eq. unfold wait_lock_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp92 : add_vec_int (mword_of_int (KX + 0x8e) : mword 64) 4 = mword_of_int (KX + 0x92))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp92) in "Hpc".
    (* +0x92 jal ra,release(&wait_lock) : back to level 1, still holding
       p->lock -- which is exactly what sched wants. *)
    iApply (wp_jal_s_sconf (CID := CIDa) Φ (mword_of_int (KX + 0x92))
              (mword_of_int 1 : mword 5) (mword_of_int 2092002 : mword 21) PB av false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi92 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (PC := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
         (add_vec_int (mword_of_int (KX + 0x92) : mword 64) 4)]> PB).
    assert (Hjrl : add_vec (mword_of_int (KX + 0x92) : mword 64)
                     (sign_extend' 64 (mword_of_int 2092002 : mword 21)) = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjrl) in "Hpc".
    assert (HPCra : PC !!! Regidx (mword_of_int 1 : mword 5)
                    = add_vec_int (mword_of_int (KX + 0x92) : mword 64) 4)
      by (rewrite /PC; apply upd_eq).
    assert (HPCa0 : PC !!! Regidx (mword_of_int 10 : mword 5) = wait_lock_addr)
      by (rewrite /PC upd_ne; [exact HPBa0 | vm_compute; discriminate]).
    iApply (Release.wp_release_sconf (CID := CIDa) Φ γw wait_lock_addr "wait_lock"%string
              wait_res PC 1%nat true pj C av
              ltac:(rewrite HPCa0; apply addv_sext0) ltac:(lia)
              with "Hcg Htext Hpc Hwl Hlkw [Hpar] Hown Hpay2 [-]").
    { iExists _. iExact "Hpar". }
    iApply wp_next_off_intro.
    iIntros (mrel) "Hcg Hpc %Hcsrel Hown".
    assert (Hpc96 : ret_pc (PC !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KX + 0x96))
      by (rewrite HPCra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc96) in "Hpc".
    (* +0x96 jal ra,sched : the ZOMBIE park. *)
    iPoseProof (kxi_96 with "Htext") as "Hi96".
    iApply (wp_jal_s_sconf (CID := CIDa) Φ (mword_of_int (KX + 0x96))
              (mword_of_int 1 : mword 5) (mword_of_int 2096502 : mword 21) mrel av false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi96 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (PD := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
         (add_vec_int (mword_of_int (KX + 0x96) : mword 64) 4)]> mrel).
    assert (Hjsd : add_vec (mword_of_int (KX + 0x96) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096502 : mword 21)) = mword_of_int KernelSyms.sched)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjsd) in "Hpc".
    assert (HPDra : PD !!! Regidx (mword_of_int 1 : mword 5)
                    = add_vec_int (mword_of_int (KX + 0x96) : mword 64) 4)
      by (rewrite /PD; apply upd_eq).
    (* the C payload comes out (sched's slot is [emp]) and the parked
       scheduler record is checked out of the global invariant, which is what
       flips the receipt to [false] -- the fifth conjunct of [proc_held]. *)
    iDestruct (kx_cpu_own_ctx_take with "Hown") as "[HC Hcpuemp]".
    iDestruct (cpu_own_set_proc 1%nat true pj pj emp with "Hcpuemp") as "[Hph Hback]".
    iApply fupd_wp.
    iMod (SchedCtx.scheds_take Φ γs ⊤ CIDa j with "Hscheds Hph Hpark")
      as "(Hvc & Hph & Hpark)"; [solve_ndisj|exact Hj|].
    iModIntro.
    iDestruct ("Hback" with "Hph") as "Hcpuemp".
    iApply (Sched.wp_sched_sconf (CID := CIDa) Φ γs j γl ZOMBIE ch0 PD av true
              Hj Hgl park_ok_ZOMBIE ltac:(lia)
              with "Hcg Htext Hpc Hprocs [Hlkp Hstate Hchan Hkilled Hxstate Hpidh Hpark]
                    [Hpriv Hsp] Hpay Hcpuemp Hoc Hvc [-]").
    { rewrite /proc_held. iFrame "Hlkp Hstate Hchan Hpark".
      iExists kl, (trunc32 (rget (CID := CIDa) mlk (mword_of_int 20 : mword 5))), pidv.
      iFrame "Hkilled Hxstate Hpidh". }
    { iApply (kexit_park_pay γf j pid V Hof Hcwd with "Hpriv Hsp"). }
    (* THE POST-RESUME ARM.  A dispatched zombie returns here and panics --
       which is why forgetting its record costs nothing. *)
    iIntros (CIDz Hsz mf ch') "%Hcsz Hcg Hpc Hheld Htc #Havail Hcpuemp Hoc Hvc".
    assert (Hpc9a : ret_pc (PD !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KX + 0x9a))
      by (rewrite HPDra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc9a) in "Hpc".
    iPoseProof (kxi_9a with "Htext") as "Hi9a".
    iPoseProof (kxi_9e with "Htext") as "Hi9e".
    iPoseProof (kxi_a2 with "Htext") as "Hia2".
    (* +0x9a auipc a0,5 ; +0x9e addi a0,a0,314 ; +0xa2 jal panic *)
    iApply (wp_auipc_s_sconf (CID := CIDz) Φ (mword_of_int (KX + 0x9a))
              (mword_of_int 10 : mword 5) (mword_of_int 5 : mword 20)
              mf av false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi9a [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (PZ := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
         (add_vec (mword_of_int (KX + 0x9a) : mword 64) (auipc_off (mword_of_int 5 : mword 20)))]> mf).
    assert (Hpp9e : add_vec_int (mword_of_int (KX + 0x9a) : mword 64) 4 = mword_of_int (KX + 0x9e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp9e) in "Hpc".
    iApply (wp_addi4_s_sconf (CID := CIDz) Φ (mword_of_int (KX + 0x9e))
              (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 314 : mword 12)
              PZ av false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi9e [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (PZ2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
         (add_vec (rget (CID := CIDz) PZ (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 314 : mword 12)))]> PZ).
    assert (Hppa2 : add_vec_int (mword_of_int (KX + 0x9e) : mword 64) 4 = mword_of_int (KX + 0xa2))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppa2) in "Hpc".
    iApply (wp_jal_s_sconf (CID := CIDz) Φ (mword_of_int (KX + 0xa2))
              (mword_of_int 1 : mword 5) (mword_of_int 2090856 : mword 21) PZ2 av false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hia2 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    assert (Hjpn : add_vec (mword_of_int (KX + 0xa2) : mword 64)
                     (sign_extend' 64 (mword_of_int 2090856 : mword 21)) = mword_of_int KernelSyms.panic)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjpn) in "Hpc".
    iPoseProof (panic_wp_any_at CIDz with "Hpanic") as "Hpw".
    iApply ("Hpw" with "Htext Hpc Hcg").
  Qed.

End KexitPark.

(* ===================================================================== *)
(* +0x4c .. +0x5c: [begin_op(); iput(p->cwd); end_op(); p->cwd = 0;].      *)
(* The whole file-system stack rides through for these four instructions   *)
(* and nothing log-shaped survives them.                                   *)
(* ===================================================================== *)
Section KexitRest.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
            !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ}.

  Lemma kx_rest `{GEN : GenId} `{CID0 : CpuId}
      (Φ : mval -> iProp Σ) (γf γw : gname) (γs : list gname)
      (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (ip sv : mword 64) (dqi : dfrac)
      (M : regfile) (av : nat) (eb : bool) (C : iProp Σ) (b : bool)
      (pid : mword 32) (V : pprivate) :
    let pj := proc_addr j in
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    eb = true ->
    (60 <= av)%nat ->
    log_geom_ok cov logstart ->
    kxt_regs M pj sv ->
    pv_ofile V = replicate NOFILE (zero_reg : mword 64) ->
    sie_cap_gpr M av b pj -∗
    cpu_own 0 eb pj C b -∗
    kernel_text -∗ pc_is (mword_of_int (KX + 0x4c)) -∗
    procs_inv Φ γs -∗ scheds_inv Φ γs -∗ panic_wp_any -∗
    own_ctx (p_context pj) -∗
    park_hlf j true -∗
    is_lock γw wait_lock_addr "wait_lock"%string wait_res -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    bslots bn 3 -∗
    (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip -∗
    fd_slots FDSPARE -∗
    proc_priv γf pj pid V -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pj Hj Hgl Heb Hav Hgeom Hregs Hof. subst eb.
    destruct Hregs as (Hs3 & Hs4 & Hdom).
    iIntros "Hcg Hown #Htext Hpc #Hprocs #Hscheds #Hpanic Hoc Hpark #Hwl".
    iIntros "#Hbio #Hlog Hseam Hgen #Hdev #Hgeo #Hdlk Hbsl Hinit Hsp Hpriv".
    (* the cwd cell, its reference, and the pid quarter -- all three out at
       once; see the header. *)
    iDestruct (proc_priv_cwd_pid γf pj pid V with "Hpriv") as "(Hcwd & Href & Hpidq & Hpback)".
    iPoseProof (kxi_4c with "Htext") as "Hi4c".
    iPoseProof (kxi_50 with "Htext") as "Hi50".
    iPoseProof (kxi_54 with "Htext") as "Hi54".
    iPoseProof (kxi_58 with "Htext") as "Hi58".
    iPoseProof (kxi_5c with "Htext") as "Hi5c".
    (* +0x4c jal ra,begin_op *)
    iApply (wp_jal_s_sconf (CID := CID0) Φ (mword_of_int (KX + 0x4c))
              (mword_of_int 1 : mword 5) (mword_of_int 7046 : mword 21) M av b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi4c [-]").
    iIntros (CID1 Hs1) "Hcg Hpc".
    set (Q0 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
         (add_vec_int (mword_of_int (KX + 0x4c) : mword 64) 4)]> M).
    assert (Hjbo : add_vec (mword_of_int (KX + 0x4c) : mword 64)
                     (sign_extend' 64 (mword_of_int 7046 : mword 21)) = mword_of_int KernelSyms.begin_op)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjbo) in "Hpc".
    assert (HQ0ra : Q0 !!! Regidx (mword_of_int 1 : mword 5)
                    = add_vec_int (mword_of_int (KX + 0x4c) : mword 64) 4)
      by (rewrite /Q0; apply upd_eq).
    assert (HQ0s3 : Q0 !!! Regidx (mword_of_int 19 : mword 5) = pj)
      by (rewrite /Q0 upd_ne; [exact Hs3 | vm_compute; discriminate]).
    assert (HQ0s4 : Q0 !!! Regidx (mword_of_int 20 : mword 5) = sv)
      by (rewrite /Q0 upd_ne; [exact Hs4 | vm_compute; discriminate]).
    iDestruct (cpu_own_transport CID0 CID1 0 true pj C b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (BeginOp.wp_begin_op_sconf (CID := CID1) Φ γs j γl bn γ γfs cov logstart dev
              pid (DfracOwn (1/4)) Q0 av true C b
              ltac:(unfold K_begin_op; lia) Hj Hgl eq_refl
              with "Hcg Hown Htext Hpc Hpanic Hlog Hpidq Hprocs Hscheds Hoc Hpark [-]").
    iIntros (CID2 Hs2 mbo) "%Hcsbo Hcg Hown Hpc Hoc Hpark Hpidq Hop".
    assert (Hpc50 : ret_pc (Q0 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KX + 0x50))
      by (rewrite HQ0ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc50) in "Hpc".
    assert (Hbo_s3 : mbo !!! Regidx (mword_of_int 19 : mword 5) = pj).
    { rewrite (callee_saved_lookup Hcsbo (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HQ0s3. }
    assert (Hbo_s4 : mbo !!! Regidx (mword_of_int 20 : mword 5) = sv).
    { rewrite (callee_saved_lookup Hcsbo (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HQ0s4. }
    (* +0x50 ld a0,336(s3) : a0 := p->cwd *)
    assert (Hrgbo19 : rget (CID := CID2) mbo (mword_of_int 19 : mword 5)
                      = mbo !!! Regidx (mword_of_int 19 : mword 5)) by (rgne; reflexivity).
    iApply (wp_ld_s_sconf (CID := CID2) Φ (mword_of_int (KX + 0x50))
              (mword_of_int 10 : mword 5) (mword_of_int 19 : mword 5) (mword_of_int 336 : mword 12)
              mbo av (pv_cwd V) b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi50 [Hcwd] [-]").
    { iEval (rewrite Hrgbo19 Hbo_s3 p_cwd_sext). iExact "Hcwd". }
    iIntros (CID3 Hs3') "Hcg Hpc Hcwd".
    iEval (rewrite Hrgbo19 Hbo_s3 p_cwd_sext) in "Hcwd".
    set (Q1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (pv_cwd V)]> mbo).
    assert (Hpp54 : add_vec_int (mword_of_int (KX + 0x50) : mword 64) 4 = mword_of_int (KX + 0x54))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp54) in "Hpc".
    assert (HQ1a0 : Q1 !!! Regidx (mword_of_int 10 : mword 5) = pv_cwd V)
      by (rewrite /Q1; apply upd_eq).
    assert (HQ1s3 : Q1 !!! Regidx (mword_of_int 19 : mword 5) = pj)
      by (rewrite /Q1 upd_ne; [exact Hbo_s3 | vm_compute; discriminate]).
    assert (HQ1s4 : Q1 !!! Regidx (mword_of_int 20 : mword 5) = sv)
      by (rewrite /Q1 upd_ne; [exact Hbo_s4 | vm_compute; discriminate]).
    (* +0x54 jal ra,iput *)
    iApply (wp_jal_s_sconf (CID := CID3) Φ (mword_of_int (KX + 0x54))
              (mword_of_int 1 : mword 5) (mword_of_int 4846 : mword 21) Q1 av b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi54 [-]").
    iIntros (CID4 Hs4') "Hcg Hpc".
    set (Q2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
         (add_vec_int (mword_of_int (KX + 0x54) : mword 64) 4)]> Q1).
    assert (Hjip : add_vec (mword_of_int (KX + 0x54) : mword 64)
                     (sign_extend' 64 (mword_of_int 4846 : mword 21)) = mword_of_int KernelSyms.iput)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjip) in "Hpc".
    assert (HQ2ra : Q2 !!! Regidx (mword_of_int 1 : mword 5)
                    = add_vec_int (mword_of_int (KX + 0x54) : mword 64) 4)
      by (rewrite /Q2; apply upd_eq).
    assert (HQ2a0 : Q2 !!! Regidx (mword_of_int 10 : mword 5) = pv_cwd V)
      by (rewrite /Q2 upd_ne; [exact HQ1a0 | vm_compute; discriminate]).
    assert (HQ2s3 : Q2 !!! Regidx (mword_of_int 19 : mword 5) = pj)
      by (rewrite /Q2 upd_ne; [exact HQ1s3 | vm_compute; discriminate]).
    assert (HQ2s4 : Q2 !!! Regidx (mword_of_int 20 : mword 5) = sv)
      by (rewrite /Q2 upd_ne; [exact HQ1s4 | vm_compute; discriminate]).
    iDestruct (cpu_own_transport CID2 CID4 0 true pj C b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (Iput.wp_iput_sconf (CID := CID4) Φ γs j γl γu γd γk pd pav pu bn γ γfs
              cov logstart dev (pv_cwd V) MAXOPBLOCKS pid (DfracOwn (1/4)) Q2 av true C b
              ltac:(unfold K_iput; lia) Hgeom ltac:(unfold iput_units; lia) Hj Hgl HQ2a0 eq_refl
              with "Hcg Hown Htext Hpc Hpanic Hbio Hlog Hpidq Hprocs Hscheds Hoc Hpark
                    Hdev Hgeo Hdlk Hbsl Href Hop [-]").
    iIntros (CID5 Hs5 mip n') "%Hcsip Hcg Hown Hpc Hoc Hpark Hpidq Hbsl %Hn' Hop".
    assert (Hpc58 : ret_pc (Q2 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KX + 0x58))
      by (rewrite HQ2ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc58) in "Hpc".
    assert (Hip_s3 : mip !!! Regidx (mword_of_int 19 : mword 5) = pj).
    { rewrite (callee_saved_lookup Hcsip (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HQ2s3. }
    assert (Hip_s4 : mip !!! Regidx (mword_of_int 20 : mword 5) = sv).
    { rewrite (callee_saved_lookup Hcsip (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HQ2s4. }
    (* +0x58 jal ra,end_op *)
    iApply (wp_jal_s_sconf (CID := CID5) Φ (mword_of_int (KX + 0x58))
              (mword_of_int 1 : mword 5) (mword_of_int 7146 : mword 21) mip av b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi58 [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (Q3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
         (add_vec_int (mword_of_int (KX + 0x58) : mword 64) 4)]> mip).
    assert (Hjeo : add_vec (mword_of_int (KX + 0x58) : mword 64)
                     (sign_extend' 64 (mword_of_int 7146 : mword 21)) = mword_of_int KernelSyms.end_op)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjeo) in "Hpc".
    assert (HQ3ra : Q3 !!! Regidx (mword_of_int 1 : mword 5)
                    = add_vec_int (mword_of_int (KX + 0x58) : mword 64) 4)
      by (rewrite /Q3; apply upd_eq).
    assert (HQ3s3 : Q3 !!! Regidx (mword_of_int 19 : mword 5) = pj)
      by (rewrite /Q3 upd_ne; [exact Hip_s3 | vm_compute; discriminate]).
    assert (HQ3s4 : Q3 !!! Regidx (mword_of_int 20 : mword 5) = sv)
      by (rewrite /Q3 upd_ne; [exact Hip_s4 | vm_compute; discriminate]).
    iDestruct (cpu_own_transport CID5 CID6 0 true pj C b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (EndOp.wp_end_op_sconf (CID := CID6) Φ γs j γl γu γd γk pd pav pu bn γ γfs
              cov logstart dev n' pid (DfracOwn (1/4)) Q3 av true C b
              ltac:(unfold K_end_op; lia) Hgeom Hj Hgl eq_refl
              with "Hcg Hown Htext Hpc Hpanic Hbio Hlog Hseam Hgen Hpidq Hprocs Hscheds
                    Hoc Hpark Hdev Hgeo Hdlk Hop [-]").
    iIntros (CID7 Hs7 meo) "%Hcseo Hcg Hown Hpc Hoc Hpark Hpidq".
    assert (Hpc5c : ret_pc (Q3 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KX + 0x5c))
      by (rewrite HQ3ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc5c) in "Hpc".
    assert (Heo_s3 : meo !!! Regidx (mword_of_int 19 : mword 5) = pj).
    { rewrite (callee_saved_lookup Hcseo (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HQ3s3. }
    assert (Heo_s4 : meo !!! Regidx (mword_of_int 20 : mword 5) = sv).
    { rewrite (callee_saved_lookup Hcseo (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HQ3s4. }
    (* +0x5c sd x0,336(s3) : p->cwd = 0, the first moment [cwd_ref] can be
       re-supplied ([ProcInv.cwd_ref_null]). *)
    assert (Hrgeo19 : rget (CID := CID7) meo (mword_of_int 19 : mword 5)
                      = meo !!! Regidx (mword_of_int 19 : mword 5)) by (rgne; reflexivity).
    iApply (wp_sd_zero_s_sconf (CID := CID7) Φ (mword_of_int (KX + 0x5c))
              (mword_of_int 19 : mword 5) (mword_of_int 336 : mword 12) meo av (pv_cwd V) b
              with "Hcg Hpc Hi5c [Hcwd] [-]").
    { iEval (rewrite Hrgeo19 Heo_s3 p_cwd_sext). iExact "Hcwd". }
    iIntros (CID8 Hs8) "Hcg Hpc Hcwd".
    iEval (rewrite Hrgeo19 Heo_s3 p_cwd_sext) in "Hcwd".
    assert (Hpp60 : add_vec_int (mword_of_int (KX + 0x5c) : mword 64) 4 = mword_of_int (KX + 0x60))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp60) in "Hpc".
    iDestruct ("Hpback" $! (zero_reg : mword 64) with "Hcwd [] Hpidq") as "Hpriv".
    { iApply cwd_ref_null. }
    iDestruct (cpu_own_transport CID7 CID8 0 true pj C b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (kx_park (CID0 := CID8) Φ γf γw γs j γl ip sv dqi meo av true C b pid
              (upd_cwd V (zero_reg : mword 64))
              Hj Hgl eq_refl ltac:(lia)
              ltac:(split; [exact Heo_s3 | split; [exact Heo_s4 | intro r; apply rf_to_gmap_dom]])
              ltac:(cbn [upd_cwd pv_ofile]; exact Hof)
              ltac:(cbn [upd_cwd pv_cwd]; reflexivity)
              with "Hcg Hown Htext Hpc Hprocs Hscheds Hpanic Hoc Hpark Hwl Hinit Hsp Hpriv").
  Qed.

End KexitRest.

(* ===================================================================== *)
(* The whole function.                                                    *)
(* ===================================================================== *)
Section ProofKexit.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
            !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !kallocG Σ}.

  Lemma wp_kexit_sconf `{GEN : GenId} `{CID0 : CpuId}
      (γft γf γw : gname)
      (Φ : mval -> iProp Σ) (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (ip : mword 64) (dqi : dfrac)
      (γkl : gname) (γka : gname * gname)
      (on : option nat) (fn : fclose_names)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (b : bool)
      (pid : mword 32) (V : pprivate)
    : wp_kexit_sconf_body γft γf γw Φ γs j γl γu γd γk pd pav pu bn γ γfs
                          cov logstart dev ip dqi γkl γka on fn
                          m av eb C b pid V.
  Proof.
    cbv beta delta [wp_kexit_sconf_body].
    intros pcE pj Hfn Hj Hgl HK Hgeom Heb. subst eb. subst fn.
    unfold K_kexit in HK.
    iIntros "Hcg Hown #Htext Hpc #Hprocs #Hscheds #Hpanic Hoc Hpark #Hwl #Hft".
    iIntros "#Hkmem Hav0".
    iIntros "#Hbio #Hlog #Hseam #Hgen #Hdev #Hgeo #Hdlk Hbsl Hinit Hsp Hpriv".
    assert (Hdom : forall r : regidx, r ∈ dom (rf_to_gmap m))
      by (intro r; apply rf_to_gmap_dom).
    (* ---- prologue ---- *)
    iApply (kx_prologue (CID := CID0) Φ m av b pj ltac:(lia) Hdom
              with "Hcg Htext Hpc [-]").
    iIntros (CIDp Hsp M) "[%Hs4 %HdomM] Hcg Hpc Hframe".
    iDestruct (cpu_own_transport CID0 CIDp 0 true pj C b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    (* ---- +0x12 jal myproc ---- *)
    iPoseProof (kxi_12 with "Htext") as "Hi12".
    iApply (wp_jal_s_sconf (CID := CIDp) Φ (mword_of_int (KX + 0x12))
              (mword_of_int 1 : mword 5) (mword_of_int 2095320 : mword 21) M (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi12 [-]").
    iIntros (CID1 Hs1) "Hcg Hpc".
    set (A0 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
         (add_vec_int (mword_of_int (KX + 0x12) : mword 64) 4)]> M).
    assert (Hjmp : add_vec (mword_of_int (KX + 0x12) : mword 64)
                     (sign_extend' 64 (mword_of_int 2095320 : mword 21)) = mword_of_int KernelSyms.myproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmp) in "Hpc".
    assert (HA0ra : A0 !!! Regidx (mword_of_int 1 : mword 5)
                    = add_vec_int (mword_of_int (KX + 0x12) : mword 64) 4)
      by (rewrite /A0; apply upd_eq).
    assert (HA0s4 : A0 !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 10 : mword 5))
      by (rewrite /A0 upd_ne; [exact Hs4 | vm_compute; discriminate]).
    iDestruct (cpu_own_transport CIDp CID1 0 true pj C b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (Myproc.wp_myproc_sconf (CID := CID1) Φ A0 (av - 6)%nat 0 true pj C b
              ltac:(lia) ltac:(lia)
              with "Hcg Hown Htext Hpc [-]").
    iIntros (CID2 Hs2 ms mp) "%Hmsf Hcg Hown Hpc %Hmp".
    destruct Hmp as [Hcsmp Ha0mp].
    assert (Hpc16 : ret_pc (A0 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KX + 0x16))
      by (rewrite HA0ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    assert (Hmp_s4 : mp !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 10 : mword 5)).
    { rewrite (callee_saved_lookup Hcsmp (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HA0s4. }
    (* +0x16 c.mv s3,a0 : s3 := p *)
    iPoseProof (kxi_16 with "Htext") as "Hi16".
    iApply (wp_cmv_s_sconf (CID := CID2) Φ (mword_of_int (KX + 0x16))
              (mword_of_int 19 : mword 5) (mword_of_int 10 : mword 5)
              mp (av - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16 [-]").
    iIntros (CID3 Hs3) "Hcg Hpc".
    assert (Hrg2_10 : rget (CID := CID2) mp (mword_of_int 10 : mword 5)
                      = mp !!! Regidx (mword_of_int 10 : mword 5)) by (rgne; reflexivity).
    iEval (rewrite Hrg2_10) in "Hcg".
    set (A1 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg
         (add_vec zero_reg (mp !!! Regidx (mword_of_int 10 : mword 5)))]> mp).
    assert (HA1s3 : A1 !!! Regidx (mword_of_int 19 : mword 5) = pj).
    { rewrite /A1 upd_eq. unfold regval_into_reg. rewrite add_vec_zero_l. exact Ha0mp. }
    assert (HA1a0 : A1 !!! Regidx (mword_of_int 10 : mword 5) = pj)
      by (rewrite /A1 upd_ne; [exact Ha0mp | vm_compute; discriminate]).
    assert (HA1s4 : A1 !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 10 : mword 5))
      by (rewrite /A1 upd_ne; [exact Hmp_s4 | vm_compute; discriminate]).
    assert (Hpp18 : add_vec_int (mword_of_int (KX + 0x16) : mword 64) 2 = mword_of_int (KX + 0x18))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* +0x18 auipc a5,0x8 ; +0x1c ld a5,524(a5) : a5 := initproc *)
    iPoseProof (kxi_18 with "Htext") as "Hi18".
    iPoseProof (kxi_1c with "Htext") as "Hi1c".
    iApply (wp_auipc_s_sconf (CID := CID3) Φ (mword_of_int (KX + 0x18))
              (mword_of_int 15 : mword 5) (mword_of_int 0x8 : mword 20)
              A1 (av - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18 [-]").
    iIntros (CID4 Hs4') "Hcg Hpc".
    set (A2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
         (add_vec (mword_of_int (KX + 0x18) : mword 64) (auipc_off (mword_of_int 0x8 : mword 20)))]> A1).
    assert (Hpp1c : add_vec_int (mword_of_int (KX + 0x18) : mword 64) 4 = mword_of_int (KX + 0x1c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    assert (Hrg4_15 : rget (CID := CID4) A2 (mword_of_int 15 : mword 5)
                      = A2 !!! Regidx (mword_of_int 15 : mword 5)) by (rgne; reflexivity).
    assert (Hipa : add_vec (rget (CID := CID4) A2 (mword_of_int 15 : mword 5))
                     (sign_extend' 64 (mword_of_int 524 : mword 12))
                   = (mword_of_int KernelSyms.initproc : mword 64)).
    { rewrite Hrg4_15 /A2 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_ld_s_sconf (CID := CID4) Φ (mword_of_int (KX + 0x1c))
              (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 524 : mword 12)
              A2 (av - 6)%nat ip b (dqm := dqi) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c [Hinit] [-]").
    { iEval (rewrite Hipa). iExact "Hinit". }
    iIntros (CID5 Hs5) "Hcg Hpc Hinit".
    iEval (rewrite Hipa) in "Hinit".
    set (A3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg ip]> A2).
    assert (Hpp20 : add_vec_int (mword_of_int (KX + 0x1c) : mword 64) 4 = mword_of_int (KX + 0x20))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    assert (HA3a5 : A3 !!! Regidx (mword_of_int 15 : mword 5) = ip)
      by (rewrite /A3; apply upd_eq).
    assert (HA3a0 : A3 !!! Regidx (mword_of_int 10 : mword 5) = pj).
    { rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [exact HA1a0 | vm_compute; discriminate]. }
    assert (HA3s3 : A3 !!! Regidx (mword_of_int 19 : mword 5) = pj).
    { rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [exact HA1s3 | vm_compute; discriminate]. }
    assert (HA3s4 : A3 !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 10 : mword 5)).
    { rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [exact HA1s4 | vm_compute; discriminate]. }
    (* +0x20 addi s1,a0,208 : s1 := &p->ofile[0] *)
    iPoseProof (kxi_20 with "Htext") as "Hi20".
    iPoseProof (kxi_24 with "Htext") as "Hi24".
    iPoseProof (kxi_28 with "Htext") as "Hi28".
    iApply (wp_addi4_s_sconf (CID := CID5) Φ (mword_of_int (KX + 0x20))
              (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 208 : mword 12)
              A3 (av - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi20 [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    assert (Hrg5_10 : rget (CID := CID5) A3 (mword_of_int 10 : mword 5)
                      = A3 !!! Regidx (mword_of_int 10 : mword 5)) by (rgne; reflexivity).
    iEval (rewrite Hrg5_10) in "Hcg".
    set (A4 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
         (add_vec (A3 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 208 : mword 12)))]> A3).
    assert (HA4s1 : A4 !!! Regidx (mword_of_int 9 : mword 5) = p_ofile pj 0%nat).
    { rewrite /A4 upd_eq HA3a0. apply p_ofile_zero. }
    assert (Hpp24 : add_vec_int (mword_of_int (KX + 0x20) : mword 64) 4 = mword_of_int (KX + 0x24))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    (* +0x24 addi s2,a0,336 : s2 := &p->cwd, which IS &p->ofile[NOFILE] *)
    iApply (wp_addi4_s_sconf (CID := CID6) Φ (mword_of_int (KX + 0x24))
              (mword_of_int 18 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 336 : mword 12)
              A4 (av - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24 [-]").
    iIntros (CID7 Hs7) "Hcg Hpc".
    assert (Hrg6_10 : rget (CID := CID6) A4 (mword_of_int 10 : mword 5)
                      = A4 !!! Regidx (mword_of_int 10 : mword 5)) by (rgne; reflexivity).
    iEval (rewrite Hrg6_10) in "Hcg".
    set (A5 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
         (add_vec (A4 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 336 : mword 12)))]> A4).
    assert (HA4a0 : A4 !!! Regidx (mword_of_int 10 : mword 5) = pj)
      by (rewrite /A4 upd_ne; [exact HA3a0 | vm_compute; discriminate]).
    assert (HA5s2 : A5 !!! Regidx (mword_of_int 18 : mword 5) = p_cwd pj).
    { rewrite /A5 upd_eq HA4a0. apply p_cwd_sext. }
    assert (HA5s1 : A5 !!! Regidx (mword_of_int 9 : mword 5) = p_ofile pj 0%nat)
      by (rewrite /A5 upd_ne; [exact HA4s1 | vm_compute; discriminate]).
    assert (HA5a0 : A5 !!! Regidx (mword_of_int 10 : mword 5) = pj)
      by (rewrite /A5 upd_ne; [exact HA4a0 | vm_compute; discriminate]).
    assert (HA5a5 : A5 !!! Regidx (mword_of_int 15 : mword 5) = ip).
    { rewrite /A5 upd_ne; [| vm_compute; discriminate].
      rewrite /A4 upd_ne; [exact HA3a5 | vm_compute; discriminate]. }
    assert (HA5s3 : A5 !!! Regidx (mword_of_int 19 : mword 5) = pj).
    { rewrite /A5 upd_ne; [| vm_compute; discriminate].
      rewrite /A4 upd_ne; [exact HA3s3 | vm_compute; discriminate]. }
    assert (HA5s4 : A5 !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 10 : mword 5)).
    { rewrite /A5 upd_ne; [| vm_compute; discriminate].
      rewrite /A4 upd_ne; [exact HA3s4 | vm_compute; discriminate]. }
    assert (Hpp28 : add_vec_int (mword_of_int (KX + 0x24) : mword 64) 4 = mword_of_int (KX + 0x28))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    assert (Hrg7_15 : rget (CID := CID7) A5 (mword_of_int 15 : mword 5)
                      = A5 !!! Regidx (mword_of_int 15 : mword 5)) by (rgne; reflexivity).
    assert (Hrg7_10 : rget (CID := CID7) A5 (mword_of_int 10 : mword 5)
                      = A5 !!! Regidx (mword_of_int 10 : mword 5)) by (rgne; reflexivity).
    (* +0x28 bne a5,a0 : the [p == initproc] panic test *)
    destruct (eq_vec ip pj) eqn:Hcmp.
    - (* p IS initproc: panic("init exiting").  NOT ruled out -- see
         SpecKexit.v's header. *)
      assert (Hfall : neq_vec (rget (CID := CID7) A5 (mword_of_int 15 : mword 5))
                              (rget (CID := CID7) A5 (mword_of_int 10 : mword 5)) = false).
      { rewrite Hrg7_15 Hrg7_10 HA5a5 HA5a0. unfold neq_vec. rewrite Hcmp. reflexivity. }
      iApply (wp_bne_fall_s_sconf (CID := CID7) Φ (mword_of_int (KX + 0x28))
                (mword_of_int 22 : mword 13) (mword_of_int 10 : mword 5) (mword_of_int 15 : mword 5)
                A5 (av - 6)%nat b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hfall with "Hcg Hpc Hi28 [-]").
      iIntros (CID8 Hs8) "Hcg Hpc".
      assert (Hpp2c : add_vec_int (mword_of_int (KX + 0x28) : mword 64) 4 = mword_of_int (KX + 0x2c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2c) in "Hpc".
      iPoseProof (kxi_2c with "Htext") as "Hi2c".
      iPoseProof (kxi_30 with "Htext") as "Hi30".
      iPoseProof (kxi_34 with "Htext") as "Hi34".
      iApply (wp_auipc_s_sconf (CID := CID8) Φ (mword_of_int (KX + 0x2c))
                (mword_of_int 10 : mword 5) (mword_of_int 5 : mword 20)
                A5 (av - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi2c [-]").
      iIntros (CID9 Hs9) "Hcg Hpc".
      set (B0 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
           (add_vec (mword_of_int (KX + 0x2c) : mword 64) (auipc_off (mword_of_int 5 : mword 20)))]> A5).
      assert (Hpp30 : add_vec_int (mword_of_int (KX + 0x2c) : mword 64) 4 = mword_of_int (KX + 0x30))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp30) in "Hpc".
      iApply (wp_addi4_s_sconf (CID := CID9) Φ (mword_of_int (KX + 0x30))
                (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 408 : mword 12)
                B0 (av - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi30 [-]").
      iIntros (CIDA HsA) "Hcg Hpc".
      set (B1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
           (add_vec (rget (CID := CID9) B0 (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 408 : mword 12)))]> B0).
      assert (Hpp34 : add_vec_int (mword_of_int (KX + 0x30) : mword 64) 4 = mword_of_int (KX + 0x34))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp34) in "Hpc".
      iApply (wp_jal_s_sconf (CID := CIDA) Φ (mword_of_int (KX + 0x34))
                (mword_of_int 1 : mword 5) (mword_of_int 2090966 : mword 21) B1 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi34 [-]").
      iIntros (CIDB HsB) "Hcg Hpc".
      assert (Hjpn : add_vec (mword_of_int (KX + 0x34) : mword 64)
                       (sign_extend' 64 (mword_of_int 2090966 : mword 21)) = mword_of_int KernelSyms.panic)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjpn) in "Hpc".
      iPoseProof (panic_wp_any_at CIDB with "Hpanic") as "Hpw".
      iApply ("Hpw" with "Htext Hpc Hcg").
    - (* the ordinary path: into the fd loop at +0x3e *)
      assert (Htaken : neq_vec (rget (CID := CID7) A5 (mword_of_int 15 : mword 5))
                               (rget (CID := CID7) A5 (mword_of_int 10 : mword 5)) = true).
      { rewrite Hrg7_15 Hrg7_10 HA5a5 HA5a0. unfold neq_vec. rewrite Hcmp. reflexivity. }
      assert (Htgt3e : add_vec (mword_of_int (KX + 0x28) : mword 64)
                         (sign_extend' 64 (mword_of_int 22 : mword 13)) = mword_of_int (KX + 0x3e))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_bne_taken_s_sconf (CID := CID7) Φ (mword_of_int (KX + 0x28))
                (mword_of_int 22 : mword 13) (mword_of_int 10 : mword 5) (mword_of_int 15 : mword 5)
                A5 (av - 6)%nat b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Htaken ltac:(rewrite Htgt3e; vm_compute; reflexivity)
                with "Hcg Hpc Hi28 [-]").
      iNext. iIntros (CID8 Hs8) "Hcg Hpc".
      iEval (rewrite Htgt3e) in "Hpc".
      iDestruct (cpu_own_transport CID2 CID8 0 true pj C b ltac:(wp_next_chain)
                   with "Hown") as "Hown".
      (* ---- the fd loop, with [kx_rest] as its exit continuation ---- *)
      (* fileclose's environment, assembled from what kexit already owns.
         The pid cell is NOT in it: it comes out of [proc_priv] one call at a
         time ([ProcInv.proc_priv_pid_ofile]), since the block is what the
         loop is walking. *)
      iAssert (∃ on', fileclose_pipe_env Φ (MkFCloseNames γs j γl γkl γka γu γd γk
                        pd pav pu bn γ γfs cov logstart dev pid (DfracOwn (1/4)))
                        on' 0%nat)%I with "[Hav0]" as "Hpenv".
      { iExists on. rewrite /fileclose_pipe_env; cbn [fcn_procs fcn_kmem fcn_kalloc].
        iSplitR.
        { iPureIntro.
          assert (E : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
          rewrite E. lia. }
        iFrame "Hprocs Hkmem Hav0". }
      iAssert (fileclose_fs_env_nopid Φ (MkFCloseNames γs j γl γkl γka γu γd γk
                 pd pav pu bn γ γfs cov logstart dev pid (DfracOwn (1/4)))
                 0%nat true pj)%I with "[Hbsl Hoc Hpark]" as "Hfenv".
      { rewrite /fileclose_fs_env_nopid.
        cbn [fcn_procs fcn_j fcn_plock fcn_uart fcn_disk fcn_dlock fcn_pd fcn_pav
             fcn_pu fcn_bio fcn_log fcn_fs fcn_cov fcn_logstart fcn_dev].
        iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
        iSplitR; [iPureIntro; exact Hj|].
        iSplitR; [iPureIntro; exact Hgl|].
        iSplitR; [iPureIntro; exact Hgeom|].
        iFrame "Hprocs Hscheds Hbio Hlog Hseam Hgen Hdev Hgeo Hdlk Hbsl Hoc Hpark". }
      iPoseProof (kx_loop (CID0 := CID8) Φ γft γf
                    (MkFCloseNames γs j γl γkl γka γu γd γk pd pav pu bn γ γfs
                       cov logstart dev pid (DfracOwn (1/4))) j pid
                    (m !!! Regidx (mword_of_int 10 : mword 5))
                    (av - 6)%nat true C b Hj eq_refl eq_refl eq_refl
                    ltac:(unfold fileclose_stack, K_iput; lia)
                    with "Htext Hft Hpanic") as "Hloop".
      iSpecialize ("Hloop" with "[Hinit Hsp Hframe]").
      { iIntros (CIDx Hsx Mx Vx) "%Hxregs %Hxof Hcg Hown Hpc Hpriv Hpenv Hfenv".
        iDestruct "Hfenv" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                               _ & _ & _ & Hbsl & Hoc & Hpark)".
        iApply (kx_rest (CID0 := CIDx) Φ γf γw γs j γl γu γd γk pd pav pu bn γ γfs
                  cov logstart dev ip (m !!! Regidx (mword_of_int 10 : mword 5)) dqi
                  Mx (av - 6)%nat true C b pid Vx
                  Hj Hgl eq_refl ltac:(lia) Hgeom Hxregs Hxof
                  with "Hcg Hown Htext Hpc Hprocs Hscheds Hpanic Hoc Hpark Hwl
                        Hbio Hlog Hseam Hgen Hdev Hgeo Hdlk Hbsl Hinit Hsp Hpriv"). }
      iApply ("Hloop" $! 0%nat A5 V with "[%] [%] [%] Hcg Hown Hpc Hpriv Hpenv Hfenv").
      + unfold NOFILE. lia.
      + split; [exact HA5s1|]. split; [exact HA5s2|]. split; [exact HA5s3|].
        split; [exact HA5s4|]. intro r; apply rf_to_gmap_dom.
      + apply kx_nulled_0.
  Qed.

End ProofKexit.

End KexitProof.
