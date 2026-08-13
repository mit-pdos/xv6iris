(* ProofFreeproc.v -- freeproc() over the SIE-agnostic sconf world.

     static void freeproc(struct proc *p) {
       if (p->trapframe) kfree(p->trapframe);
       p->trapframe = 0;
       if (p->pagetable) proc_freepagetable(p->pagetable, p->sz);
       p->pagetable = 0;
       p->sz = 0;  p->pid = 0;  p->name[0] = 0;
       p->chan = 0;  p->killed = 0;  p->xstate = 0;
       p->state = UNUSED;
     }

   Spec of record: SpecFreeproc.v.  Twenty-six instructions @
   KernelSyms.freeproc: a 32-byte ra/s0/s1 frame (slot 0 is padding -- the
   function saves three registers into four slots), two GUARDED calls, and
   nine zeroing stores.

   THE SHAPE IS TWO NESTED JOINS, and the proof mirrors them with two
   [iAssert]ed continuation blocks:

     +0x22 .. +0x4a   ZERO -- the nine stores and the epilogue.  Both
                      pagetable arms reach it (the [c.beqz] at +0x1a jumps
                      here; the call falls through into it), differing only
                      in what p->pagetable still holds, so the block is
                      parameterized by that word and by the register map.
     +0x14 .. +0x22   PGT -- store 0 into p->trapframe, then the pagetable
                      load, branch and call.  Both trapframe arms reach it,
                      differing only in what p->trapframe still holds.

   PGT closes over ZERO; the two trapframe arms both close over PGT.  So
   each of the four paths through the function is written once.

   WHY THE PRECONDITION IS NOT [proc_dormant _ ZOMBIE]: see the spec's
   header.  The short version is that allocproc's second failure tail
   arrives with a live trapframe page and NO page table, which
   [proc_dormant]'s [st]-keyed disjunct cannot name -- so the two optional
   slots ([fp_pt] / [fp_tf]) are independent, and the [destruct] on each is
   exactly the runtime branch. *)
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
Require Import WpMmodeLeafBase.
Require Import RegFile.
Require Import CalleeSaved StackOwn.
Require Import KernelRvcDecode.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import KallocInv.
Require Import PageGeom.
Require Import CpuOwn.
Require Import ProcGeom.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SchedCtx.
Require Import InstrBytes.
Require Import CodeFreeproc.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import SpecKfree SpecProcFreepagetable.
Require Import SpecFreeproc.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §0  The pure vocabulary.  mword-FREE where it can be: with an mword in *)
(*     the context the zify hook makes [lia] fail (durable-notes).        *)
(* ===================================================================== *)

Lemma fr_cap (K : nat) : (44 <= K)%nat ->
  (4 <= K)%nat /\ (14 <= K - 4)%nat /\ (40 <= K - 4)%nat.
Proof. lia. Qed.

Lemma fr_kback (K : nat) : (44 <= K)%nat -> ((K - 4) + 4)%nat = K.
Proof. lia. Qed.

(* the [struct proc] displacements, in the [sign_extend' 64 (mword 12)]
   shape a load/store leaf produces them.  [p_pid] / [p_pagetable] /
   [p_trapframe] are already spelled that way in ProcGeom. *)
Lemma fr_off_24 (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 24 : mword 12)) = p_state X.
Proof. rewrite /p_state /state_off. f_equal; apply bv_eq; vm_compute; reflexivity. Qed.
Lemma fr_off_32 (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 32 : mword 12)) = p_chan X.
Proof. rewrite /p_chan /chan_off. f_equal; apply bv_eq; vm_compute; reflexivity. Qed.
Lemma fr_off_40 (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 40 : mword 12)) = p_killed X.
Proof. rewrite /p_killed. f_equal; apply bv_eq; vm_compute; reflexivity. Qed.
Lemma fr_off_44 (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 44 : mword 12)) = p_xstate X.
Proof. rewrite /p_xstate. f_equal; apply bv_eq; vm_compute; reflexivity. Qed.
Lemma fr_off_48 (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 48 : mword 12)) = p_pid X.
Proof. reflexivity. Qed.
Lemma fr_off_72 (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 72 : mword 12)) = p_sz X.
Proof. rewrite /p_sz. f_equal; apply bv_eq; vm_compute; reflexivity. Qed.
Lemma fr_off_80 (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 80 : mword 12)) = p_pagetable X.
Proof. reflexivity. Qed.
Lemma fr_off_88 (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 88 : mword 12)) = p_trapframe X.
Proof. reflexivity. Qed.
Lemma fr_off_344 (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 344 : mword 12)) = p_name X 0.
Proof. rewrite /p_name. f_equal; apply bv_eq; vm_compute; reflexivity. Qed.

(* the two zero constants the stores actually leave behind *)
Lemma fr_z64 : (zero_reg : mword 64) = (mword_of_int 0 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma fr_z32 : (mword_of_int 0 : mword 32) = UNUSED.
Proof. reflexivity. Qed.

(* [p->name] after the [sb zero,344(s1)]: byte 0 becomes 0, the rest stand.
   The length is what [proc_fields] asks for and [insert] preserves it. *)
Lemma fr_name_len (bs : list (bv 8)) :
  length bs = PNAMELEN -> length (<[0%nat := (mword_of_int 0 : mword 8)]> bs) = PNAMELEN.
Proof. intro H. rewrite length_insert. exact H. Qed.

Module FreeprocProof (KF : KFREE) (PFP : PROC_FREEPAGETABLE) : FREEPROC.

Section ProofFreeproc.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation FR := KernelSyms.freeproc.
  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).

  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?false => tryif unify a false then fail else (vm_compute; discriminate)
    end.

  (* Discharge an [upd_ne] side goal inside a callee-saved TRANSPORT peel,
     where the register is a VARIABLE.  THE FOUR [exact]s COME FIRST: the
     cost of a FAILED tactic grows with the proof term, and leading with the
     [vm_compute] branch makes every frame-register write pay for its
     failure (durable-notes; it was 42s on proc_pagetable). *)
  Ltac thr_side Hc H2 H8 H9 :=
    let Hx := fresh "Hx" in
    let Hx2 := fresh "Hx2" in
    intros Hx; injection Hx as Hx2;
    first [ exact (H2 Hx2) | exact (H8 Hx2) | exact (H9 Hx2)
          | rewrite Hx2 in Hc; vm_compute in Hc; discriminate ].

  (* [callee_saved mm m] minus the three frame registers freeproc saves and
     restores itself.  Threaded one fact per callee boundary. *)
  Definition fr_thr (mm m : regfile) : Prop :=
    forall c : mword 5, is_cs_idx c = true ->
      c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
      m !!! Regidx c = mm !!! Regidx c.

  Lemma fr_thr_refl (mm : regfile) : fr_thr mm mm.
  Proof. intros c _ _ _ _. reflexivity. Qed.

  (* ONE INSERT AT A TIME.  Unfolding the whole [set]-bound tower first does
     not work: the written values contain lookups of their own, so [rewrite
     upd_ne] can pick a redex inside a value. *)
  Lemma fr_thr_ins (mm m : regfile) (k : mword 5) (v : mword 64) :
    (forall c : mword 5, is_cs_idx c = true ->
       c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> Regidx c <> Regidx k) ->
    fr_thr mm m -> fr_thr mm (<[Regidx k := v]> m).
  Proof.
    intros Hk H c Hc H2 H8 H9.
    rewrite upd_ne; [| exact (Hk c Hc H2 H8 H9)]. apply H; assumption.
  Qed.

  (* [thr_peel] unfolds the [set]-bound tower until it hits a variable, which
     may be [mm] itself (a stretch with no callee in it) or an earlier
     threaded map.  Close with whichever applies. *)
  Ltac thr_peel :=
    repeat first
      [ lazymatch goal with
        | |- fr_thr _ ?M => is_var M; progress unfold M
        end
      | apply fr_thr_ins; [ intros c Hc H2 H8 H9; thr_side Hc H2 H8 H9 |] ].

  Ltac thr_done := thr_peel; first [ apply fr_thr_refl | assumption ].

  Lemma wp_freeproc_sconf
      (γa : gname) (mm : regfile)
      (j : nat) (γl : gname) (V : pprivate) (pid st : mword 32) (ch : mword 64)
      (opt : option uptd) (otf : option (mword 44 * list (mword 64)))
      (K : nat) (eb : bool) (pme : mword 64) (C : iProp Σ)
      (ilvl : nat)
    : wp_freeproc_sconf_body γa mm j γl V pid st ch opt otf K eb pme C ilvl.
  Proof.
    cbv beta delta [wp_freeproc_sconf_body].
    intros pcE pa ret_tgt HK Hilvl Ha0.
    pose proof (fr_cap K HK) as (Hc4 & Hckf & Hcpf).
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iIntros "Hcg Hcpu #Htext Hpc Hheld Hrest Hpg Htf #Henv Hcont".
    iDestruct "Hrest" as "(%Hpure & Hpid & Hfields & Hof & Hunits & Hspare & Hctx)".
    destruct Hpure as (Hofv & Hcwdv & Hszb).
    iDestruct "Hheld" as "(Hlk & Hstate & Hpsg & Hchan & Hpub)".
    (* THE MIRROR FOLLOWS THE CELL.  freeproc's caller holds p->lock for the
       whole call, so it holds the WHOLE variable and the move needs no side
       condition; doing it up front rather than at the store keeps it out of
       the non-modal goal the postcondition is assembled in. *)
    iApply fupd_wp.
    iMod (pstate_whole_update (proc_addr j) st UNUSED with "Hpsg") as "Hpsg".
    iModIntro.
    iDestruct "Hpub" as (kl xs pid2) "(Hkilled & Hxstate & Hpid2)".
    iDestruct "Hfields" as "(Hsz & Hcwd & %Hnmlen & Hnm)".
    (* [proc_held] is stated at [proc_addr j] and the block at the [let]-bound
       [pa].  Convertible, but [iFrame]/[iSpecialize] want them SYNTACTICALLY
       equal, so fold once here and unfold once at the hand-back. *)
    assert (Hpaj : proc_addr j = pa) by reflexivity.
    iEval (rewrite Hpaj) in "Hstate".
    iEval (rewrite Hpaj) in "Hchan".
    iEval (rewrite Hpaj) in "Hkilled".
    iEval (rewrite Hpaj) in "Hxstate".
    iEval (rewrite Hpaj) in "Hpid2".
    (* the two halves name the same word; settle it ONCE, at the top, so the
       tail block can just join them. *)
    iDestruct (word4_pointsto_agree with "Hpid Hpid2") as %Hpideq.
    subst pid2.

    (* ================================================================= *)
    (* §A  PROLOGUE: the 32-byte frame; only three slots are written.     *)
    (* ================================================================= *)
    iPoseProof (fri_00 with "Htext") as "Hi00".
    iPoseProof (fri_02 with "Htext") as "Hi02".
    iPoseProof (fri_04 with "Htext") as "Hi04".
    iPoseProof (fri_06 with "Htext") as "Hi06".
    iPoseProof (fri_08 with "Htext") as "Hi08".
    iPoseProof (fri_0a with "Htext") as "Hi0a".
    iPoseProof (fri_0c with "Htext") as "Hi0c".
    iPoseProof (fri_0e with "Htext") as "Hi0e".
    assert (Hspm : mm !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (mm !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) mm K 4 false
              Hc4 Hpush with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> mm).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> mm) with A0.
    assert (HA0sp : A0 !!! Regidx csp_rs1 = spd) by (rewrite /A0 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & _)".
    iDestruct "S1c" as (vr24) "Hr24".
    iDestruct "S2c" as (vr16) "Hr16".
    iDestruct "S3c" as (vr8) "Hr8".
    iDestruct "S4c" as (vr0) "Hr0".
    assert (Hb1 : pa_stk sp0 1
                  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2
                  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : pa_stk sp0 3
                  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : pa_stk sp0 4
                  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (FR + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    (* +0x02 sd ra,24(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (FR + 0x02)) (mword_of_int 3 : mword 6) Rra
              A0 (K - 4)%nat vr24 false with "Hcg Hpc Hi02 [Hr24]").
    { iEval (rewrite HA0sp -Hb1). iExact "Hr24". }
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    iEval (rewrite HA0sp -Hb1) in "Hr24".
    assert (HA0ra : A0 !!! Regidx Rra = mm !!! Regidx Rra)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    iEval (rgne; rewrite HA0ra) in "Hr24".
    assert (Hpc04 : add_vec_int (mword_of_int (FR + 0x02) : mword 64) 2 = mword_of_int (FR + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    (* +0x04 sd s0,16(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (FR + 0x04)) (mword_of_int 2 : mword 6) Rs0
              A0 (K - 4)%nat vr16 false with "Hcg Hpc Hi04 [Hr16]").
    { iEval (rewrite HA0sp -Hb2). iExact "Hr16". }
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    iEval (rewrite HA0sp -Hb2) in "Hr16".
    assert (HA0s0 : A0 !!! Regidx Rs0 = mm !!! Regidx Rs0)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    iEval (rgne; rewrite HA0s0) in "Hr16".
    assert (Hpc06 : add_vec_int (mword_of_int (FR + 0x04) : mword 64) 2 = mword_of_int (FR + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    (* +0x06 sd s1,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (FR + 0x06)) (mword_of_int 1 : mword 6) Rs1
              A0 (K - 4)%nat vr8 false with "Hcg Hpc Hi06 [Hr8]").
    { iEval (rewrite HA0sp -Hb3). iExact "Hr8". }
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    iEval (rewrite HA0sp -Hb3) in "Hr8".
    assert (HA0s1 : A0 !!! Regidx Rs1 = mm !!! Regidx Rs1)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    iEval (rgne; rewrite HA0s1) in "Hr8".
    assert (Hpc08 : add_vec_int (mword_of_int (FR + 0x06) : mword 64) 2 = mword_of_int (FR + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    (* +0x08 addi s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (FR + 0x08)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 A0 (K - 4)%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (A1 := <[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0).
    assert (Hpc0a : add_vec_int (mword_of_int (FR + 0x08) : mword 64) 2 = mword_of_int (FR + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    (* +0x0a mv s1,a0 : s1 := p *)
    iApply (wp_cmv_s_sconf (mword_of_int (FR + 0x0a)) Rs1 Ra0 A1 (K - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi0a").
    iIntros (CID6 Hs6) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (A2 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx Ra0))]> A1).
    assert (HA2s1 : A2 !!! Regidx Rs1 = pa).
    { rewrite /A2 upd_eq. rewrite add_vec_zero_l.
      rewrite /A1 upd_ne; [| reg_neq]. rewrite /A0 upd_ne; [| reg_neq]. exact Ha0. }
    assert (HA2a0 : A2 !!! Regidx Ra0 = pa).
    { rewrite /A2 upd_ne; [| reg_neq]. rewrite /A1 upd_ne; [| reg_neq].
      rewrite /A0 upd_ne; [| reg_neq]. exact Ha0. }
    assert (HA2sp : A2 !!! Regidx csp_rs1 = spd).
    { rewrite /A2 /A1. repeat (rewrite upd_ne; [| reg_neq]). exact HA0sp. }
    assert (HA2thr : fr_thr mm A2) by (thr_peel; apply fr_thr_refl).
    assert (Hpc0c : add_vec_int (mword_of_int (FR + 0x0a) : mword 64) 2 = mword_of_int (FR + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".

    (* ================================================================= *)
    (* §Z  THE ZEROING TAIL, +0x22 .. +0x4a -- both pagetable arms.       *)
    (*     Everything it needs but the register map, the pc, the two      *)
    (*     address-space cells and the caps is CAPTURED: those resources  *)
    (*     are untouched between here and the join.                       *)
    (* ================================================================= *)
    iAssert (wp_next false pme (fun (CIDz : CpuId) =>
        ∀ (me : regfile) (pgv : mword 64),
        ⌜ me !!! Regidx csp_rs1 = spd
          /\ me !!! Regidx Rs1 = pa
          /\ fr_thr mm me ⌝ -∗
        sie_cap_gpr me (K - 4)%nat false pme -∗
        cpu_own ilvl eb pme C false -∗
        pc_is (mword_of_int (FR + 0x22) : mword 64) -∗
        p_pagetable pa ↦₈ pgv -∗
        p_trapframe pa ↦₈ (zero_reg : mword 64) -∗
        (* p->sz is a PARAMETER, not captured: the pagetable arm LOADS it
           for proc_freepagetable before this block stores 0 into it. *)
        p_sz pa ↦₈ pv_sz V -∗
        WP (Loop : expr riscv_lang)))%I
      with "[Hcont Hr24 Hr16 Hr8 Hr0 Hlk Hstate Hpsg Hchan Hkilled Hxstate Hpid Hpid2
             Hcwd Hnm Hof Hunits Hspare Hctx]" as "ZERO".
    { iIntros (CIDz Hsz0 me pgv).
      iIntros "(%Hmesp & %Hmes1 & %Hmethr) Hcg Hcpu Hpc Hpg Htf Hsz".
      (* the instruction facts must be re-posed INSIDE with FRESH names *)
      iPoseProof (fri_22 with "Htext") as "Hj22".
      iPoseProof (fri_26 with "Htext") as "Hj26".
      iPoseProof (fri_2a with "Htext") as "Hj2a".
      iPoseProof (fri_2e with "Htext") as "Hj2e".
      iPoseProof (fri_32 with "Htext") as "Hj32".
      iPoseProof (fri_36 with "Htext") as "Hj36".
      iPoseProof (fri_3a with "Htext") as "Hj3a".
      iPoseProof (fri_3e with "Htext") as "Hj3e".
      iPoseProof (fri_42 with "Htext") as "Hj42".
      iPoseProof (fri_44 with "Htext") as "Hj44".
      iPoseProof (fri_46 with "Htext") as "Hj46".
      iPoseProof (fri_48 with "Htext") as "Hj48".
      iPoseProof (fri_4a with "Htext") as "Hj4a".
      (* +0x22 sd zero,80(s1) : p->pagetable = 0 *)
      iApply (wp_sd_zero_s_sconf (mword_of_int (FR + 0x22)) Rs1
                (mword_of_int 80 : mword 12) me (K - 4)%nat pgv false
                with "Hcg Hpc Hj22 [Hpg]").
      { iEval (rgne; rewrite Hmes1 fr_off_80). iExact "Hpg". }
      iIntros (CIDz1 Hsz1) "Hcg Hpc Hpg".
      iEval (rgne; rewrite Hmes1 fr_off_80) in "Hpg".
      assert (Hq26 : add_vec_int (mword_of_int (FR + 0x22) : mword 64) 4 = mword_of_int (FR + 0x26))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq26) in "Hpc".
      (* +0x26 sd zero,72(s1) : p->sz = 0 *)
      iApply (wp_sd_zero_s_sconf (mword_of_int (FR + 0x26)) Rs1
                (mword_of_int 72 : mword 12) me (K - 4)%nat (pv_sz V) false
                with "Hcg Hpc Hj26 [Hsz]").
      { iEval (rgne; rewrite Hmes1 fr_off_72). iExact "Hsz". }
      iIntros (CIDz2 Hsz2) "Hcg Hpc Hsz".
      iEval (rgne; rewrite Hmes1 fr_off_72) in "Hsz".
      assert (Hq2a : add_vec_int (mword_of_int (FR + 0x26) : mword 64) 4 = mword_of_int (FR + 0x2a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq2a) in "Hpc".
      (* +0x2a sw zero,48(s1) : p->pid = 0.  BOTH halves are needed -- one
         came in with the block, the other out of [proc_pub]. *)
      iDestruct (word4_pointsto_half_join with "Hpid Hpid2") as "Hpidf".
      iApply (wp_sw_zero_s_sconf (mword_of_int (FR + 0x2a)) Rs1
                (mword_of_int 48 : mword 12) me (K - 4)%nat pid false
                with "Hcg Hpc Hj2a [Hpidf]").
      { iEval (rgne; rewrite Hmes1 fr_off_48). iExact "Hpidf". }
      iIntros (CIDz3 Hsz3) "Hcg Hpc Hpidf".
      iEval (rgne; rewrite Hmes1 fr_off_48) in "Hpidf".
      iDestruct (word4_pointsto_half_split with "Hpidf") as "[Hpid Hpid2]".
      assert (Hq2e : add_vec_int (mword_of_int (FR + 0x2a) : mword 64) 4 = mword_of_int (FR + 0x2e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq2e) in "Hpc".
      (* +0x2e sb zero,344(s1) : p->name[0] = 0.  Take byte 0 out with an
         INSERT accessor rather than destructing the list: the wand puts the
         NEW byte back and hands [pname_cells] at the updated list, which is
         exactly the [V'] the dormant block wants. *)
      assert (Hnb0 : is_Some (pv_name V !! 0%nat)).
      { apply lookup_lt_is_Some_2. rewrite Hnmlen. unfold PNAMELEN. lia. }
      destruct Hnb0 as (nb0 & Hnb0).
      iEval (rewrite /pname_cells) in "Hnm".
      iDestruct (big_sepL_insert_acc _ _ 0%nat nb0 Hnb0 with "Hnm") as "[Hnm0 Hnmback]".
      iDestruct (sie_cap_gpr_x0 me (K - 4)%nat false pme (mword_of_int 0 : mword 5)
                   ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx0 Hcg]".
      assert (Hsbv : trunc8 (rget me (mword_of_int 0 : mword 5)) = (mword_of_int 0 : mword 8)).
      { rgne. rewrite Hx0. apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_sb_s_sconf (mword_of_int (FR + 0x2e)) (mword_of_int 0 : mword 5) Rs1
                (mword_of_int 344 : mword 12) me (K - 4)%nat nb0 false
                with "Hcg Hpc Hj2e [Hnm0]").
      { iEval (rgne; rewrite Hmes1 fr_off_344). iExact "Hnm0". }
      iIntros (CIDz4 Hsz4) "Hcg Hpc Hnm0".
      iEval (rgne; rewrite Hmes1 fr_off_344; rewrite Hsbv) in "Hnm0".
      iDestruct ("Hnmback" $! (mword_of_int 0 : mword 8) with "Hnm0") as "Hnm".
      assert (Hq32 : add_vec_int (mword_of_int (FR + 0x2e) : mword 64) 4 = mword_of_int (FR + 0x32))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq32) in "Hpc".
      (* +0x32 sd zero,32(s1) : p->chan = 0 *)
      iApply (wp_sd_zero_s_sconf (mword_of_int (FR + 0x32)) Rs1
                (mword_of_int 32 : mword 12) me (K - 4)%nat ch false
                with "Hcg Hpc Hj32 [Hchan]").
      { iEval (rgne; rewrite Hmes1 fr_off_32). iExact "Hchan". }
      iIntros (CIDz5 Hsz5) "Hcg Hpc Hchan".
      iEval (rgne; rewrite Hmes1 fr_off_32) in "Hchan".
      assert (Hq36 : add_vec_int (mword_of_int (FR + 0x32) : mword 64) 4 = mword_of_int (FR + 0x36))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq36) in "Hpc".
      (* +0x36 sw zero,40(s1) : p->killed = 0 *)
      iApply (wp_sw_zero_s_sconf (mword_of_int (FR + 0x36)) Rs1
                (mword_of_int 40 : mword 12) me (K - 4)%nat kl false
                with "Hcg Hpc Hj36 [Hkilled]").
      { iEval (rgne; rewrite Hmes1 fr_off_40). iExact "Hkilled". }
      iIntros (CIDz6 Hsz6) "Hcg Hpc Hkilled".
      iEval (rgne; rewrite Hmes1 fr_off_40) in "Hkilled".
      assert (Hq3a : add_vec_int (mword_of_int (FR + 0x36) : mword 64) 4 = mword_of_int (FR + 0x3a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq3a) in "Hpc".
      (* +0x3a sw zero,44(s1) : p->xstate = 0 *)
      iApply (wp_sw_zero_s_sconf (mword_of_int (FR + 0x3a)) Rs1
                (mword_of_int 44 : mword 12) me (K - 4)%nat xs false
                with "Hcg Hpc Hj3a [Hxstate]").
      { iEval (rgne; rewrite Hmes1 fr_off_44). iExact "Hxstate". }
      iIntros (CIDz7 Hsz7) "Hcg Hpc Hxstate".
      iEval (rgne; rewrite Hmes1 fr_off_44) in "Hxstate".
      assert (Hq3e : add_vec_int (mword_of_int (FR + 0x3a) : mword 64) 4 = mword_of_int (FR + 0x3e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq3e) in "Hpc".
      (* +0x3e sw zero,24(s1) : p->state = UNUSED *)
      iApply (wp_sw_zero_s_sconf (mword_of_int (FR + 0x3e)) Rs1
                (mword_of_int 24 : mword 12) me (K - 4)%nat st false
                with "Hcg Hpc Hj3e [Hstate]").
      { iEval (rgne; rewrite Hmes1 fr_off_24). iExact "Hstate". }
      iIntros (CIDz8 Hsz8) "Hcg Hpc Hstate".
      iEval (rgne; rewrite Hmes1 fr_off_24) in "Hstate".
      assert (Hq42 : add_vec_int (mword_of_int (FR + 0x3e) : mword 64) 4 = mword_of_int (FR + 0x42))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq42) in "Hpc".
      (* ---- the epilogue, +0x42 .. +0x4a ---- *)
      (* +0x42 ld ra,24(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (FR + 0x42)) (mword_of_int 3 : mword 6) Rra
                me (K - 4)%nat (mm !!! Regidx Rra) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hj42 [Hr24]").
      { iEval (rewrite Hmesp -Hb1). iExact "Hr24". }
      iIntros (CIDz9 Hsz9) "Hcg Hpc Hr24".
      iEval (rewrite Hmesp -Hb1) in "Hr24".
      set (E0 := <[Regidx Rra := regval_into_reg (mm !!! Regidx Rra)]> me).
      assert (HE0sp : E0 !!! Regidx csp_rs1 = spd)
        by (rewrite /E0 upd_ne; [exact Hmesp | reg_neq]).
      assert (Hq44 : add_vec_int (mword_of_int (FR + 0x42) : mword 64) 2 = mword_of_int (FR + 0x44))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq44) in "Hpc".
      (* +0x44 ld s0,16(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (FR + 0x44)) (mword_of_int 2 : mword 6) Rs0
                E0 (K - 4)%nat (mm !!! Regidx Rs0) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hj44 [Hr16]").
      { iEval (rewrite HE0sp -Hb2). iExact "Hr16". }
      iIntros (CIDza Hsza) "Hcg Hpc Hr16".
      iEval (rewrite HE0sp -Hb2) in "Hr16".
      set (E1 := <[Regidx Rs0 := regval_into_reg (mm !!! Regidx Rs0)]> E0).
      assert (HE1sp : E1 !!! Regidx csp_rs1 = spd)
        by (rewrite /E1 upd_ne; [exact HE0sp | reg_neq]).
      assert (Hq46 : add_vec_int (mword_of_int (FR + 0x44) : mword 64) 2 = mword_of_int (FR + 0x46))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq46) in "Hpc".
      (* +0x46 ld s1,8(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (FR + 0x46)) (mword_of_int 1 : mword 6) Rs1
                E1 (K - 4)%nat (mm !!! Regidx Rs1) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hj46 [Hr8]").
      { iEval (rewrite HE1sp -Hb3). iExact "Hr8". }
      iIntros (CIDzb Hszb') "Hcg Hpc Hr8".
      iEval (rewrite HE1sp -Hb3) in "Hr8".
      set (E2 := <[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> E1).
      assert (HE2sp : E2 !!! Regidx csp_rs1 = spd)
        by (rewrite /E2 upd_ne; [exact HE1sp | reg_neq]).
      assert (Hq48 : add_vec_int (mword_of_int (FR + 0x46) : mword 64) 2 = mword_of_int (FR + 0x48))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq48) in "Hpc".
      (* +0x48 addi sp,sp,32 -- the frame pop *)
      set (E3 := <[Regidx csp_rs1 := regval_into_reg
          (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E2).
      assert (Hwv : add_vec (E2 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
      { rewrite HE2sp. rewrite /spd. apply frame_cancel_32. }
      assert (Hpop : E2 !!! Regidx csp_rs1
                     = pa_stk (add_vec (E2 !!! Regidx csp_rs1)
                          (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
      { rewrite Hwv HE2sp. symmetry. exact Hspd4. }
      iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hr0]" as "Hframe".
      { rewrite stack_own_slots. cbn [seq].
        iSplitL "Hr24". { iExists (mm !!! Regidx Rra). iExact "Hr24". }
        iSplitL "Hr16". { iExists (mm !!! Regidx Rs0). iExact "Hr16". }
        iSplitL "Hr8".  { iExists (mm !!! Regidx Rs1). iExact "Hr8". }
        iSplitL "Hr0".  { iExists vr0. iExact "Hr0". }
        done. }
      iEval (rewrite -Hwv) in "Hframe".
      iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (FR + 0x48)) (mword_of_int 2 : mword 6)
                E2 (K - 4)%nat 4 false Hpop with "Hcg Hpc Hj48 Hframe").
      iIntros (CIDzc Hszc) "Hcg Hpc".
      change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E2 !!! Regidx csp_rs1)
                (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E2) with E3.
      iEval (rewrite (fr_kback K HK)) in "Hcg".
      assert (Hq4a : add_vec_int (mword_of_int (FR + 0x48) : mword 64) 2 = mword_of_int (FR + 0x4a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq4a) in "Hpc".
      (* +0x4a ret *)
      assert (HE3ra : E3 !!! Regidx Rra = mm !!! Regidx Rra).
      { rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq].
        rewrite /E1 upd_ne; [| reg_neq]. rewrite /E0 upd_eq. reflexivity. }
      assert (Hrt : ret_pc (E3 !!! Regidx Rra) = ret_tgt) by (rewrite HE3ra; reflexivity).
      iApply (wp_cret_s_sconf (mword_of_int (FR + 0x4a)) Rra E3 K false
                ltac:(vm_compute; discriminate) with "Hcg Hpc Hj4a").
      iIntros (CIDzd Hszd) "Hcg Hpc".
      iEval (rgne) in "Hpc". iEval (rewrite Hrt) in "Hpc".
      (* ---- hand everything back ---- *)
      iDestruct (cpu_own_transport CIDz CIDzd ilvl eb pme C false ltac:(wp_next_chain)
                   with "Hcpu") as "Hcpu".
      iSpecialize ("Hcont" $! CIDzd with "[]"); [ iPureIntro; wp_next_chain | ].
      iApply ("Hcont" $! E3 with "Hcg Hcpu Hpc [%] [Hlk Hstate Hpsg Hchan Hkilled Hxstate Hpid2]
                                  [Hpid Hsz Hcwd Hnm Hof Hunits Hspare Hctx Hpg Htf]").
      { (* callee_saved mm E3 *)
        assert (HE3thr : fr_thr mm E3).
        { thr_done. }
        unfold callee_saved.
        split. { rewrite /E3 upd_eq. rewrite HE2sp. rewrite /spd. apply frame_cancel_32. }
        split. { rewrite /E3 /E2. repeat (rewrite upd_ne; [| reg_neq]). rewrite /E1 upd_eq. reflexivity. }
        split. { rewrite /E3. rewrite upd_ne; [| reg_neq]. rewrite /E2 upd_eq. reflexivity. }
        repeat split;
          apply HE3thr; first [ vm_compute; reflexivity | vm_compute; discriminate ]. }
      { (* proc_held at UNUSED, chan 0 *)
        rewrite /proc_held /proc_pub Hpaj.
        (* the returned [proc_held] names the hart at the RET, which is this
           one because the whole function runs at [b = false] (the caller
           holds p->lock).  [wp_next]'s equality is exactly that. *)
        assert (Hcpueq : (CIDzd : CPU) = (CID : CPU))
          by (assert (Hsh : false = false \/ pme = zero_reg -> (CIDzd : CPU) = (CID : CPU))
                by wp_next_chain;
              exact (Hsh (or_introl eq_refl))).
        rewrite Hcpueq.
        iFrame "Hlk".
        iFrame "Hpsg".
        iEval (rewrite fr_z32) in "Hstate". iFrame "Hstate".
        (* the store leaf already leaves [zero_reg] in the chan cell *)
        iFrame "Hchan".
        iExists (mword_of_int 0 : mword 32), (mword_of_int 0 : mword 32),
                (mword_of_int 0 : mword 32).
        iFrame "Hkilled Hxstate Hpid2". }
      { (* proc_dormant pa UNUSED, at the emptied V *)
        iApply (fp_to_dormant_unused pa
                  (MkPPriv (zero_reg : mword 64) (pv_upt V) (pv_tf V)
                           (pv_ofile V) (pv_cwd V) (<[0%nat := (mword_of_int 0 : mword 8)]> (pv_name V)))
                  (mword_of_int 0 : mword 32) (pv_sz V)
                  with "[Hpid Hsz Hcwd Hnm Hof Hunits Hspare Hctx] [Hpg] [Htf]").
        - rewrite /fp_rest. cbn [pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
          iSplitR.
          { iPureIntro. split_and!; [exact Hofv | exact Hcwdv |].
            rewrite uint_unsigned. unfold uvm_maxsz. vm_compute. discriminate. }
          iFrame "Hpid Hof Hunits Hspare Hctx".
          rewrite /proc_fields. cbn [pv_sz pv_cwd pv_name].
          iFrame "Hsz Hcwd".
          iSplitR. { iPureIntro. apply fr_name_len. exact Hnmlen. }
          rewrite /pname_cells. iExact "Hnm".
        - rewrite /fp_pt. iExact "Hpg".
        - rewrite /fp_tf. iExact "Htf". } }

    (* ================================================================= *)
    (* §P  THE PAGETABLE STEP, +0x14 .. +0x22 -- both trapframe arms.     *)
    (* ================================================================= *)
    iAssert (wp_next false pme (fun (CIDp : CpuId) =>
        ∀ (me : regfile) (tfv : mword 64),
        ⌜ me !!! Regidx csp_rs1 = spd
          /\ me !!! Regidx Rs1 = pa
          /\ fr_thr mm me ⌝ -∗
        sie_cap_gpr me (K - 4)%nat false pme -∗
        cpu_own ilvl eb pme C false -∗
        pc_is (mword_of_int (FR + 0x14) : mword 64) -∗
        p_trapframe pa ↦₈ tfv -∗
        p_sz pa ↦₈ pv_sz V -∗
        WP (Loop : expr riscv_lang)))%I
      with "[ZERO Hpg]" as "PGT".
    { iIntros (CIDp Hsp0 me tfv).
      iIntros "(%Hmesp & %Hmes1 & %Hmethr) Hcg Hcpu Hpc Htf Hsz".
      iPoseProof (fri_14 with "Htext") as "Hj14".
      iPoseProof (fri_18 with "Htext") as "Hj18".
      iPoseProof (fri_1a with "Htext") as "Hj1a".
      iPoseProof (fri_1c with "Htext") as "Hj1c".
      iPoseProof (fri_1e with "Htext") as "Hj1e".
      (* +0x14 sd zero,88(s1) : p->trapframe = 0 *)
      iApply (wp_sd_zero_s_sconf (mword_of_int (FR + 0x14)) Rs1
                (mword_of_int 88 : mword 12) me (K - 4)%nat tfv false
                with "Hcg Hpc Hj14 [Htf]").
      { iEval (rgne; rewrite Hmes1 fr_off_88). iExact "Htf". }
      iIntros (CIDp1 Hsp1) "Hcg Hpc Htf".
      iEval (rgne; rewrite Hmes1 fr_off_88) in "Htf".
      assert (Hq18 : add_vec_int (mword_of_int (FR + 0x14) : mword 64) 4 = mword_of_int (FR + 0x18))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq18) in "Hpc".
      (* +0x18 ld a0,80(s1) : a0 := p->pagetable *)
      destruct opt as [P |].
      - (* ---- a LIVE user table: the call runs ---- *)
        iDestruct "Hpg" as "(Hpgc & Hpt & %Hszok)".
        destruct Hszok as (Hbelow & Hszr).
        (* the root page's [page_valid] -- what refutes the [c.beqz] at +0x1a
           -- is READ OFF the table rather than demanded of the caller. *)
        iDestruct (proc_pt_root_valid P with "Hpt") as %Hrootv.
        iApply (wp_cld_s_sconf (mword_of_int (FR + 0x18)) Ra0 Rs1
                  (mword_of_int 80 : mword 12) me (K - 4)%nat (page_base P.(ud_root)) false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hj18 [Hpgc]").
        { iEval (rgne; rewrite Hmes1 fr_off_80). iExact "Hpgc". }
        iIntros (CIDp2 Hsp2) "Hcg Hpc Hpgc".
        iEval (rgne; rewrite Hmes1 fr_off_80) in "Hpgc".
        set (B0 := <[Regidx Ra0 := regval_into_reg (page_base P.(ud_root))]> me).
        assert (HB0a0 : B0 !!! Regidx Ra0 = page_base P.(ud_root))
          by (rewrite /B0 upd_eq; reflexivity).
        assert (HB0s1 : B0 !!! Regidx Rs1 = pa)
          by (rewrite /B0 upd_ne; [exact Hmes1 | reg_neq]).
        assert (HB0sp : B0 !!! Regidx csp_rs1 = spd)
          by (rewrite /B0 upd_ne; [exact Hmesp | reg_neq]).
        assert (Hq1a : add_vec_int (mword_of_int (FR + 0x18) : mword 64) 2 = mword_of_int (FR + 0x1a))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq1a) in "Hpc".
        (* +0x1a beqz a0 -- FALLS: a live table's root is a kalloc page *)
        assert (Hrootnz : page_base P.(ud_root) <> (zero_reg : mword 64)).
        { rewrite fr_z64. apply page_valid_ne_null. exact Hrootv. }
        iApply (wp_cbeqz_fall_s_sconf (mword_of_int (FR + 0x1a)) (mword_of_int 4 : mword 8)
                  (Cregidx (mword_of_int 2)) Ra0 B0 (K - 4)%nat false
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite HB0a0; apply eq_vec_false_iff; exact Hrootnz)
                  with "Hcg Hpc Hj1a").
        iIntros (CIDp3 Hsp3) "Hcg Hpc".
        assert (Hq1c : add_vec_int (mword_of_int (FR + 0x1a) : mword 64) 2 = mword_of_int (FR + 0x1c))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq1c) in "Hpc".
        (* +0x1c ld a1,72(s1) : a1 := p->sz *)
        iApply (wp_cld_s_sconf (mword_of_int (FR + 0x1c)) Ra1 Rs1
                  (mword_of_int 72 : mword 12) B0 (K - 4)%nat (pv_sz V) false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hj1c [Hsz]").
        { iEval (rgne; rewrite HB0s1 fr_off_72). iExact "Hsz". }
        iIntros (CIDp4 Hsp4) "Hcg Hpc Hsz".
        iEval (rgne; rewrite HB0s1 fr_off_72) in "Hsz".
        set (B1 := <[Regidx Ra1 := regval_into_reg (pv_sz V)]> B0).
        assert (Hq1e : add_vec_int (mword_of_int (FR + 0x1c) : mword 64) 2 = mword_of_int (FR + 0x1e))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq1e) in "Hpc".
        (* +0x1e jal proc_freepagetable *)
        iApply (wp_jal_s_sconf (mword_of_int (FR + 0x1e)) Rra (mword_of_int 2097052 : mword 21)
                  B1 (K - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hj1e").
        iIntros (CIDp5 Hsp5) "Hcg Hpc".
        set (B2 := <[Regidx Rra := regval_into_reg
            (add_vec_int (mword_of_int (FR + 0x1e) : mword 64) 4)]> B1).
        assert (Htgt : add_vec (mword_of_int (FR + 0x1e) : mword 64)
                         (sign_extend' 64 (mword_of_int 2097052 : mword 21))
                       = mword_of_int KernelSyms.proc_freepagetable)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt) in "Hpc".
        assert (HB2a0 : B2 !!! Regidx Ra0 = page_base P.(ud_root)).
        { rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [| reg_neq]. exact HB0a0. }
        assert (HB2a1 : B2 !!! Regidx Ra1 = pv_sz V).
        { rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_eq. reflexivity. }
        assert (HB2sp : B2 !!! Regidx csp_rs1 = spd).
        { rewrite /B2 /B1. repeat (rewrite upd_ne; [| reg_neq]). exact HB0sp. }
        assert (HB2s1 : B2 !!! Regidx Rs1 = pa).
        { rewrite /B2 /B1. repeat (rewrite upd_ne; [| reg_neq]). exact HB0s1. }
        assert (HB2thr : fr_thr mm B2) by thr_done.
        assert (HB2ra : B2 !!! Regidx Rra
                        = add_vec_int (mword_of_int (FR + 0x1e) : mword 64) 4)
          by (rewrite /B2 upd_eq; reflexivity).
        iDestruct (cpu_own_transport CIDp CIDp5 ilvl eb pme C false ltac:(wp_next_chain)
                     with "Hcpu") as "Hcpu".
        iApply (PFP.wp_proc_freepagetable_sconf γa B2 P (K - 4)%nat eb pme C ilvl false
                  Hcpf Hilvl HB2a0
                  ltac:(rewrite HB2a1; exact Hszr)
                  ltac:(rewrite HB2a1; exact Hbelow)
                  with "Hcg Hcpu Htext Hpc Hpt Henv").
        iIntros (CIDp6 Hsp6 mr) "Hcg Hcpu Hpc %Hcs".
        assert (Hret22 : ret_pc (B2 !!! Regidx Rra) = mword_of_int (FR + 0x22)).
        { rewrite HB2ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
        iEval (rewrite Hret22) in "Hpc".
        iSpecialize ("ZERO" $! CIDp6 with "[%]"); [wp_next_chain|].
        iApply ("ZERO" $! mr (page_base P.(ud_root)) with "[%] Hcg Hcpu Hpc Hpgc Htf Hsz").
        split_and!.
        + rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HB2sp.
        + rewrite (callee_saved_lookup Hcs Rs1 ltac:(vm_compute; reflexivity)). exact HB2s1.
        + intros c Hc H2 H8 H9.
          rewrite (callee_saved_lookup Hcs c Hc). apply HB2thr; assumption.
      - (* ---- NO table: p->pagetable is already 0, the call is skipped ---- *)
        iApply (wp_cld_s_sconf (mword_of_int (FR + 0x18)) Ra0 Rs1
                  (mword_of_int 80 : mword 12) me (K - 4)%nat (zero_reg : mword 64) false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hj18 [Hpg]").
        { iEval (rgne; rewrite Hmes1 fr_off_80). iExact "Hpg". }
        iIntros (CIDp2 Hsp2) "Hcg Hpc Hpg".
        iEval (rgne; rewrite Hmes1 fr_off_80) in "Hpg".
        set (B0 := <[Regidx Ra0 := regval_into_reg (zero_reg : mword 64)]> me).
        assert (HB0a0 : B0 !!! Regidx Ra0 = (zero_reg : mword 64))
          by (rewrite /B0 upd_eq; reflexivity).
        assert (HB0s1 : B0 !!! Regidx Rs1 = pa)
          by (rewrite /B0 upd_ne; [exact Hmes1 | reg_neq]).
        assert (HB0sp : B0 !!! Regidx csp_rs1 = spd)
          by (rewrite /B0 upd_ne; [exact Hmesp | reg_neq]).
        assert (HB0thr : fr_thr mm B0) by thr_done.
        assert (Hq1a : add_vec_int (mword_of_int (FR + 0x18) : mword 64) 2 = mword_of_int (FR + 0x1a))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq1a) in "Hpc".
        (* +0x1a beqz a0 -- TAKEN, straight to the zeroing tail *)
        iApply (wp_cbeqz_taken_s_sconf (mword_of_int (FR + 0x1a)) (mword_of_int 4 : mword 8)
                  (Cregidx (mword_of_int 2)) Ra0 B0 (K - 4)%nat false
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite HB0a0; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hj1a").
        iNext. iIntros (CIDp3 Hsp3) "Hcg Hpc".
        assert (Htg22 : add_vec (mword_of_int (FR + 0x1a) : mword 64)
                          (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 4 : mword 8) ('b"0"))))
                        = mword_of_int (FR + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htg22) in "Hpc".
        iDestruct (cpu_own_transport CIDp CIDp3 ilvl eb pme C false ltac:(wp_next_chain)
                     with "Hcpu") as "Hcpu".
        iSpecialize ("ZERO" $! CIDp3 with "[%]"); [wp_next_chain|].
        iApply ("ZERO" $! B0 (zero_reg : mword 64) with "[%] Hcg Hcpu Hpc Hpg Htf Hsz").
        split_and!; [exact HB0sp | exact HB0s1 | exact HB0thr]. }

    (* ================================================================= *)
    (* §T  THE TRAPFRAME STEP, +0x0c .. +0x14.                            *)
    (* ================================================================= *)
    (* +0x0c ld a0,88(a0) : a0 := p->trapframe *)
    destruct otf as [tw |].
    - (* ---- a LIVE trapframe page: kfree runs ---- *)
      destruct tw as (tfp & ws).
      iDestruct "Htf" as "(Htfc & Htfp & %Htfval)".
      cbn [fst snd] in *.
      iApply (wp_cld_s_sconf (mword_of_int (FR + 0x0c)) Ra0 Ra0
                (mword_of_int 88 : mword 12) A2 (K - 4)%nat (page_base tfp) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi0c [Htfc]").
      { iEval (rgne; rewrite HA2a0 fr_off_88). iExact "Htfc". }
      iIntros (CID7 Hs7) "Hcg Hpc Htfc".
      iEval (rgne; rewrite HA2a0 fr_off_88) in "Htfc".
      set (T0 := <[Regidx Ra0 := regval_into_reg (page_base tfp)]> A2).
      assert (HT0a0 : T0 !!! Regidx Ra0 = page_base tfp)
        by (rewrite /T0 upd_eq; reflexivity).
      assert (HT0s1 : T0 !!! Regidx Rs1 = pa)
        by (rewrite /T0 upd_ne; [exact HA2s1 | reg_neq]).
      assert (HT0sp : T0 !!! Regidx csp_rs1 = spd)
        by (rewrite /T0 upd_ne; [exact HA2sp | reg_neq]).
      assert (Hpc0e : add_vec_int (mword_of_int (FR + 0x0c) : mword 64) 2 = mword_of_int (FR + 0x0e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc0e) in "Hpc".
      (* +0x0e beqz a0 -- FALLS *)
      assert (Htfnz : page_base tfp <> (zero_reg : mword 64))
        by (rewrite fr_z64; apply page_valid_ne_null; exact Htfval).
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (FR + 0x0e)) (mword_of_int 3 : mword 8)
                (Cregidx (mword_of_int 2)) Ra0 T0 (K - 4)%nat false
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HT0a0; apply eq_vec_false_iff; exact Htfnz)
                with "Hcg Hpc Hi0e").
      iIntros (CID8 Hs8) "Hcg Hpc".
      assert (Hpc10 : add_vec_int (mword_of_int (FR + 0x0e) : mword 64) 2 = mword_of_int (FR + 0x10))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc10) in "Hpc".
      (* +0x10 jal kfree *)
      iPoseProof (fri_10 with "Htext") as "Hi10".
      iApply (wp_jal_s_sconf (mword_of_int (FR + 0x10)) Rra (mword_of_int 2092846 : mword 21)
                T0 (K - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi10").
      iIntros (CID9 Hs9) "Hcg Hpc".
      set (T1 := <[Regidx Rra := regval_into_reg
          (add_vec_int (mword_of_int (FR + 0x10) : mword 64) 4)]> T0).
      assert (Htgtk : add_vec (mword_of_int (FR + 0x10) : mword 64)
                        (sign_extend' 64 (mword_of_int 2092846 : mword 21))
                      = mword_of_int KernelSyms.kfree)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtk) in "Hpc".
      assert (HT1a0 : T1 !!! Regidx Ra0 = page_base tfp)
        by (rewrite /T1 upd_ne; [exact HT0a0 | reg_neq]).
      assert (HT1sp : T1 !!! Regidx csp_rs1 = spd)
        by (rewrite /T1 upd_ne; [exact HT0sp | reg_neq]).
      assert (HT1s1 : T1 !!! Regidx Rs1 = pa)
        by (rewrite /T1 upd_ne; [exact HT0s1 | reg_neq]).
      assert (HT1thr : fr_thr mm T1) by thr_done.
      assert (HT1ra : T1 !!! Regidx Rra
                      = add_vec_int (mword_of_int (FR + 0x10) : mword 64) 4)
        by (rewrite /T1 upd_eq; reflexivity).
      (* the trapframe page, back as the anonymous bytes kfree wants *)
      iDestruct (tf_page_to_page_own tfp ws with "Htfp") as "Hpage".
      (* kfree is stated over the RAW kmem lock and count, not the bundle:
         open [kalloc_env] once here.  It is at [None], hence persistent, so
         nothing is lost by opening it. *)
      iDestruct "Henv" as (γk) "(#Hkmem & #Havail & #Hpanic)".
      iDestruct (cpu_own_transport CID CID9 ilvl eb pme C false ltac:(wp_next_chain)
                   with "Hcpu") as "Hcpu".
      iApply (KF.wp_kfree_sconf γa γk (mword_of_int KernelSyms.kmem)
                (mword_of_int (KernelSyms.kmem + 24)) T1 None ilvl eb pme C
                (K - 4)%nat false
                Hckf eq_refl eq_refl Hilvl
                with "Hcg Hcpu Htext Hpc Hkmem [Hpage] Havail Hpanic").
      { rewrite /kfree_pre. iSplitR; [iPureIntro; rewrite HT1a0; exact Htfval |].
        iEval (rewrite HT1a0). iExact "Hpage". }
      iIntros (CIDk Hsk mrk) "Hcg Hcpu Hpc %Hcsk _".
      assert (Hret14 : ret_pc (T1 !!! Regidx Rra) = mword_of_int (FR + 0x14)).
      { rewrite HT1ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hret14) in "Hpc".
      iSpecialize ("PGT" $! CIDk with "[%]"); [wp_next_chain|].
      iApply ("PGT" $! mrk (page_base tfp) with "[%] Hcg Hcpu Hpc Htfc Hsz").
      split_and!.
      + rewrite (callee_saved_lookup Hcsk csp_rs1 ltac:(vm_compute; reflexivity)). exact HT1sp.
      + rewrite (callee_saved_lookup Hcsk Rs1 ltac:(vm_compute; reflexivity)). exact HT1s1.
      + intros c Hc H2 H8 H9.
        rewrite (callee_saved_lookup Hcsk c Hc). apply HT1thr; assumption.
    - (* ---- NO trapframe page: the cell is already 0, kfree is skipped ---- *)
      iApply (wp_cld_s_sconf (mword_of_int (FR + 0x0c)) Ra0 Ra0
                (mword_of_int 88 : mword 12) A2 (K - 4)%nat (zero_reg : mword 64) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi0c [Htf]").
      { iEval (rgne; rewrite HA2a0 fr_off_88). iExact "Htf". }
      iIntros (CID7 Hs7) "Hcg Hpc Htf".
      iEval (rgne; rewrite HA2a0 fr_off_88) in "Htf".
      set (T0 := <[Regidx Ra0 := regval_into_reg (zero_reg : mword 64)]> A2).
      assert (HT0a0 : T0 !!! Regidx Ra0 = (zero_reg : mword 64))
        by (rewrite /T0 upd_eq; reflexivity).
      assert (HT0s1 : T0 !!! Regidx Rs1 = pa)
        by (rewrite /T0 upd_ne; [exact HA2s1 | reg_neq]).
      assert (HT0sp : T0 !!! Regidx csp_rs1 = spd)
        by (rewrite /T0 upd_ne; [exact HA2sp | reg_neq]).
      assert (HT0thr : fr_thr mm T0) by thr_done.
      assert (Hpc0e : add_vec_int (mword_of_int (FR + 0x0c) : mword 64) 2 = mword_of_int (FR + 0x0e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc0e) in "Hpc".
      (* +0x0e beqz a0 -- TAKEN *)
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (FR + 0x0e)) (mword_of_int 3 : mword 8)
                (Cregidx (mword_of_int 2)) Ra0 T0 (K - 4)%nat false
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HT0a0; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi0e").
      iNext. iIntros (CID8 Hs8) "Hcg Hpc".
      assert (Htg14 : add_vec (mword_of_int (FR + 0x0e) : mword 64)
                        (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0"))))
                      = mword_of_int (FR + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htg14) in "Hpc".
      iDestruct (cpu_own_transport CID CID8 ilvl eb pme C false ltac:(wp_next_chain)
                   with "Hcpu") as "Hcpu".
      iSpecialize ("PGT" $! CID8 with "[%]"); [wp_next_chain|].
      iApply ("PGT" $! T0 (zero_reg : mword 64) with "[%] Hcg Hcpu Hpc Htf Hsz").
      split_and!; [exact HT0sp | exact HT0s1 | exact HT0thr].
  Qed.

End ProofFreeproc.

End FreeprocProof.
