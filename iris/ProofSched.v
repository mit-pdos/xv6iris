(* ProofSched.v -- the whole-function sconf-tier proof of sched()
   (SpecSched.v), as a sealed functor over its callees' interfaces
   (myproc, holding, swtch).  See claude-notes/projects/yield-sched.md. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import InstrBytes KernelText.
Require Import IntrDefs HartTp WpNext WpSmodeIntr.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSconfCsr.
Require Import WpLock.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpGprCsrwCommon.
Require WpGprCsrwC.
Require Import CodeSched.
Require Import SpecMyproc SpecHolding SpecSwtch SpecSched.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Import Defs.
Local Open Scope Z_scope.
Set Printing Depth 40.

(* ===================================================================== *)
(* Pure helpers: address arithmetic + the SIE-bit fact.                   *)
(* ===================================================================== *)





(* the workhorse address reconciliation: pulling the (symbolic) shift term
   [sh] out front on both sides leaves a CLOSED constant equality. *)
Lemma sched_reconcile (sh a b c d : mword 64) :
  bv_unsigned (add_vec a b) = bv_unsigned (add_vec c d) ->
  add_vec (add_vec sh a) b = add_vec (add_vec sh c) d.
Proof.
  intro H. rewrite add_vec64_unsigned in H. rewrite (add_vec64_unsigned c d) in H.
  apply bv_eq.
  rewrite (add_vec64_unsigned (add_vec sh a) b) (add_vec64_unsigned sh a).
  rewrite (add_vec64_unsigned (add_vec sh c) d) (add_vec64_unsigned sh c).
  rewrite !bv_wrap_add_idemp_l.
  rewrite <- !Z.add_assoc.
  rewrite <- (bv_wrap_add_idemp_r 64 (bv_unsigned sh) (bv_unsigned a + bv_unsigned b)).
  rewrite <- (bv_wrap_add_idemp_r 64 (bv_unsigned sh) (bv_unsigned c + bv_unsigned d)).
  rewrite H. reflexivity.
Qed.

(* a variant where the shift sits INSIDE the right factor of the left side. *)
Lemma sched_reconcile2 (sh a b c d : mword 64) :
  bv_unsigned (add_vec a b) = bv_unsigned (add_vec c d) ->
  add_vec a (add_vec sh b) = add_vec (add_vec c sh) d.
Proof.
  intro H.
  rewrite (add_vec64_comm sh b). rewrite <- (add_vec_assoc a b sh).
  rewrite (add_vec64_comm (add_vec a b) sh).
  rewrite (add_vec64_comm c sh). rewrite (add_vec_assoc sh c d).
  assert (Hab : add_vec a b = add_vec c d) by (apply bv_eq; exact H).
  rewrite Hab. reflexivity.
Qed.

(* a saved-register frame slot address in terms of the pushed sp. *)
Lemma sched_frame_bridge (sp0 : mword 64) (j : nat) (uimm : mword 6) :
  bv_unsigned (add_vec (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))
                       (zero_extend' 64 (concat_vec uimm ('b"000"))) : mword 64)
    = bv_wrap 64 (- (8 * Z.of_nat j)) ->
  pa_stk sp0 j
    = add_vec (add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))
              (zero_extend' 64 (concat_vec uimm ('b"000"))).
Proof.
  intro H.
  assert (Heq : add_vec (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))
                        (zero_extend' 64 (concat_vec uimm ('b"000")))
                = (mword_of_int (- (8 * Z.of_nat j)) : mword 64)).
  { apply bv_eq. rewrite H.
    unfold mword_of_int, Values.to_word, get_word. cbn.
    rewrite Z_to_bv_unsigned. reflexivity. }
  unfold pa_stk, add_vec_int. rewrite add_vec_assoc. rewrite Heq. reflexivity.
Qed.

Lemma sched_sstatus_clear (ms : mword 64) :
  eq_vec (_get_Mstatus_SIE ms) ('b"1") = false ->
  neq_vec (and_vec (sstatus_read ms)
             (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))) zero_reg = false.
Proof.
  intro HSIE.
  unfold neq_vec. apply negb_false_iff. apply eq_vec_true_iff.
  assert (Hz : _get_Mstatus_SIE ms = ('b"0" : mword 1))
    by (apply mword1_zero_of_ne_one; exact HSIE).
  assert (Hb1 : Z.testbit (bv_unsigned (sstatus_read ms)) 1 = false).
  { unfold sstatus_read. rewrite WpGprCsrwC.subrange_full.
    apply WpGprCsrwC.sie_bit. rewrite WpGprCsrwC.mSIE_lower. exact Hz. }
  assert (Hmask : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)) : mword 64) = 2)
    by (vm_compute; reflexivity).
  assert (Hzr : bv_unsigned (zero_reg : mword 64) = 0) by (vm_compute; reflexivity).
  apply bv_eq. rewrite WpGprCsrwC.and_vec_unsigned. rewrite Hmask. rewrite Hzr.
  apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec. rewrite Z.bits_0.
  destruct (decide (j = 1)) as [->|Hne].
  - rewrite Hb1. reflexivity.
  - assert (Ht2 : Z.testbit 2 j = false).
    { destruct (Z.eq_dec j 0) as [->|Hj0].
      - reflexivity.
      - apply Z.bits_above_log2; [lia|]. change (Z.log2 2) with 1. lia. }
    rewrite Ht2. apply andb_false_r.
Qed.

(* THE IDLE-HATCH REFUTATION.  sched's crossing index is the literal [true]
   (a park moves the hart with interrupts off), so [wp_next true pj]'s
   pinning condition reduces to [pj = zero_reg] -- and a real process
   address never is.  This is what lets the continuation be USED at the
   resuming hart. *)
Lemma sched_pj_nonzero (j : nat) :
  (j < NPROC)%nat -> proc_addr j <> (zero_reg : mword 64).
Proof.
  intros Hj Heq. apply (f_equal (@bv_unsigned _)) in Heq.
  rewrite (proc_addr_unsigned j Hj) in Heq.
  assert (Hz : bv_unsigned (zero_reg : mword 64) = 0) by (vm_compute; reflexivity).
  rewrite Hz in Heq.
  unfold KernelSyms.proc, proc_size in Heq. lia.
Qed.

(* [sched_noff_ne_one] -- the [2 <= k] direction of sched's [bne a4,a5]
   check -- lived here, and had exactly one user: the noff >= 2 walk that
   took the branch.  With that walk deleted only the noff = 1 direction is
   ever needed, and the [wp_sched_sconf] proof does it inline from the
   literal level. *)

Module SchedProof (Myproc : MYPROC) (Holding : HOLDING) (Swtch : SWTCH) : SCHED.

(* ===================================================================== *)
(* THE POST-RESUME HALF, AS ITS OWN LEMMA.                                *)
(*                                                                        *)
(* sched()'s own context record is MIGRATABLE now ([Ao = None], SwtchCtx), *)
(* so the swtch continuation is quantified over the resuming hart [h] and  *)
(* CANNOT be pinned back to the ambient instance.                          *)
(* Everything after the swtch -- the intena restore, the ghost retune, the *)
(* epilogue, the postcondition -- therefore has to hold at an ARBITRARY    *)
(* hart.  Rather than re-thread [(CID := h)] through ~200 leaf             *)
(* applications, the whole half is ONE lemma whose [CID] is a binder, and  *)
(* the pre-swtch half applies it once at [(CID := h)].                     *)
(* (Inside a Section that fixes [CID] this would be impossible:            *)
(* a section variable cannot be instantiated from within its own section.) *)
(*                                                                        *)
(* Its pure premises are exactly the pre-swtch register tower's facts,     *)
(* restated at the RETURNED file [m'].  There is no tp premise any more:   *)
(* [tp_pin] makes the resumed file's tp THIS hart's id by construction,    *)
(* and [rget_tp] reads it off with no hypothesis at all.                   *)
(* ===================================================================== *)
Section SchedPostSwtch.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.

  Lemma sched_post_swtch `{GEN : GenId} `{CID : CpuId}
       (γs : list gname)
      (j : nat) (γl : gname) (ch' : mword 64)
      (m m' : regfile) (av : nat) (eb eb' : bool)
      (sp0 spd vgap : mword 64) :
    let pj := proc_addr j in
    (6 <= av)%nat ->
    (* the pushed frame base, and where the frame lives *)
    add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))) = spd ->
    sp0 = m !!! Regidx csp_rs1 ->
    m' !!! Regidx csp_rs1 = spd ->
    (* s2 = &cpus[0] as the +0x46 auipc/addi pair computed it; s3 = the saved
       base-enable word read at +0x54 *)
    m' !!! Regidx (mword_of_int 18 : mword 5)
      = add_vec (add_vec (mword_of_int (KernelSyms.sched + 0x46) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20))) (sign_extend' 64 (mword_of_int 0x576 : mword 12)) ->
    m' !!! Regidx (mword_of_int 19 : mword 5) = sign_extend' 64 (intena_val eb) ->
    (* s4..s11: untouched by sched, hence still the entry file's *)
    m' !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5) ->
    m' !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) ->
    m' !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) ->
    m' !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) ->
    m' !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) ->
    m' !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) ->
    m' !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) ->
    m' !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5) ->
    kernel_text -∗
    sie_cap_gpr m' (av - 6)%nat false pj -∗
    (* at the RESUMER's base [eb'] -- swtch stores nothing to struct cpu.
       THE SET IS {proc}, BOTH WAYS, in every real instantiation: sched is
       entered holding exactly this proc's lock ([sched]'s own [noff != 1]
       check is the C-level shadow of it), the lock stays held across the
       swtch, and the resumer comes back holding it too.  ∅ appears only in
       the scheduler loop, between its [release(&p->lock)] and the next
       [acquire] -- which is exactly where [intr_on()] sits.  Stated with the
       the literal proc singleton, which is what
       [wp_sched_sconf]'s own (∀-generic) contract hands this helper -- the
       set is carried, never inspected, so genericity costs nothing here. *)
    cpu_own 1 eb' pj false {["proc"]} -∗
    pc_is (mword_of_int (KernelSyms.sched + 0x72)) -∗
    (* the five saved callee-saved words + the frame's bottom slot *)
    pa_stk sp0 1 ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
    pa_stk sp0 2 ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
    pa_stk sp0 3 ↦₈ (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
    pa_stk sp0 4 ↦₈ (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
    pa_stk sp0 5 ↦₈ (m !!! Regidx (mword_of_int 19 : mword 5)) -∗
    pa_stk sp0 6 ↦₈ vgap -∗
    (* what the dispatch payload delivered *)
    proc_held cpu_id j γl RUNNING ch' -∗
    trap_csrs -∗
    own_ctx (p_context pj) -∗
    hart_full j cpu_id -∗
    ▷ sched_vc_at γs cpu_id (a_cpu_ctx cid_word) pj -∗
    ( ∀ (mf : regfile) (ch0 : mword 64),
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr mf av false pj -∗
        pc_is (ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))) -∗
        proc_held cpu_id j γl RUNNING ch0 -∗
        trap_csrs -∗
        cpu_own 1 eb pj false {["proc"]} -∗
        own_ctx (p_context pj) -∗
        hart_full j cpu_id -∗
        ▷ sched_vc_at γs cpu_id (a_cpu_ctx cid_word) pj -∗
        WP (Loop : expr riscv_lang) ) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj Hav Hspd Hsp0 Hsp_m' Hs2addr Hs3v
           Hm20 Hm21 Hm22 Hm23 Hm24 Hm25 Hm26 Hm27.
    iIntros "#Htext Hcg Hcpu Hpc Hr1 Hr2 Hr3 Hr4 Hr5 Hgap Hheld' Htc Hown Htag Hvc' Hcont".
    (* frame-slot address bridges: slot k sits at [spd + 8*(6-k)]. *)
    assert (Hb1 : pa_stk sp0 1 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))
      by (rewrite -Hspd; apply sched_frame_bridge; vm_compute; reflexivity).
    assert (Hb2 : pa_stk sp0 2 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))
      by (rewrite -Hspd; apply sched_frame_bridge; vm_compute; reflexivity).
    assert (Hb3 : pa_stk sp0 3 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))))
      by (rewrite -Hspd; apply sched_frame_bridge; vm_compute; reflexivity).
    assert (Hb4 : pa_stk sp0 4 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))
      by (rewrite -Hspd; apply sched_frame_bridge; vm_compute; reflexivity).
    assert (Hb5 : pa_stk sp0 5 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))))
      by (rewrite -Hspd; apply sched_frame_bridge; vm_compute; reflexivity).
    (* the returned cpu bundle came back at the RESUMER's base [eb'] (the wand
       is [∀ eb']); unfold it -- the intena-restore store + a ghost retune below
       bring it back to this thread's own saved base [eb]. *)
    iEval (rewrite cpu_own_off /cpu_hart /cpu_priv /cpu_cells) in "Hcpu".
    iDestruct "Hcpu" as "(((_ & Hnoff2 & Hint2 & Hcur2) & Hlks2) & Hcnt2)".
    set (iv' := intena_val eb' : mword 32).
    (* ------------------------------------------------------------------ *)
    (* +0x72..+0x7a: restore c->intena := s3.                             *)
    (* ------------------------------------------------------------------ *)
    (* +0x72 c.mv a5,tp *)
    iPoseProof (sdi_72 with "Htext") as "Hi72".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sched + 0x72)) (mword_of_int 15 : mword 5) (mword_of_int 4 : mword 5)
              m' (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi72").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (E0 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (rget m' (mword_of_int 4 : mword 5)))]> m').
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (rget m' (mword_of_int 4 : mword 5)))]> m') with E0.
    assert (Hpc74 : add_vec_int (mword_of_int (KernelSyms.sched + 0x72) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x74)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc74) in "Hpc".
    (* +0x74 sext.w a5 *)
    iPoseProof (sdi_74 with "Htext") as "Hi74".
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.sched + 0x74)) (mword_of_int 15 : mword 5) (mword_of_int 0 : mword 6)
              E0 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi74").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (E1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec (add_vec (E0 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> E0).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec (add_vec (E0 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> E0) with E1.
    assert (Hpc76 : add_vec_int (mword_of_int (KernelSyms.sched + 0x74) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x76)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc76) in "Hpc".
    (* +0x76 c.slli a5,7 *)
    iPoseProof (sdi_76 with "Htext") as "Hi76".
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.sched + 0x76)) (Regidx (mword_of_int 15)) (mword_of_int 15 : mword 5) (mword_of_int 7 : mword 6)
              E1 (av - 6)%nat false eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi76").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (E2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_left (E1 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 7 : mword 6) (Z.sub log2_xlen 1) 0))]> E1).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_left (E1 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 7 : mword 6) (Z.sub log2_xlen 1) 0))]> E1) with E2.
    assert (HshE : E2 !!! Regidx (mword_of_int 15 : mword 5) = mycpu_a5 cid_word)
      by (rewrite /E2 upd_eq /E1 upd_eq /E0 upd_eq (rget_tp m'); reflexivity).
    assert (Hpc78 : add_vec_int (mword_of_int (KernelSyms.sched + 0x76) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc78) in "Hpc".
    (* +0x78 c.add s2,s2,a5 *)
    iPoseProof (sdi_78 with "Htext") as "Hi78".
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.sched + 0x78)) (mword_of_int 18 : mword 5) (mword_of_int 15 : mword 5)
              E2 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi78").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (E3 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (E2 !!! Regidx (mword_of_int 18 : mword 5)) (E2 !!! Regidx (mword_of_int 15 : mword 5)))]> E2).
    change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (E2 !!! Regidx (mword_of_int 18 : mword 5)) (E2 !!! Regidx (mword_of_int 15 : mword 5)))]> E2) with E3.
    assert (Hpc7a : add_vec_int (mword_of_int (KernelSyms.sched + 0x78) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x7a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc7a) in "Hpc".
    (* +0x7a sw s3,172(s2) : reconcile to a_cpu_int, store into the cell *)
    assert (HE2s2 : E2 !!! Regidx (mword_of_int 18 : mword 5)
                    = add_vec (add_vec (mword_of_int (KernelSyms.sched + 0x46) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20))) (sign_extend' 64 (mword_of_int 0x576 : mword 12))).
    { rewrite /E2 upd_ne; [| vm_compute; discriminate]. rewrite /E1 upd_ne; [| vm_compute; discriminate].
      rewrite /E0 upd_ne; [| vm_compute; discriminate]. exact Hs2addr. }
    assert (Hrec_int2 : add_vec (rget E3 (mword_of_int 18 : mword 5)) (sign_extend' 64 (mword_of_int 172 : mword 12)) = a_cpu_int cid_word).
    { rgne. assert (HE3v : E3 !!! Regidx (mword_of_int 18 : mword 5)
                     = add_vec (add_vec (add_vec (mword_of_int (KernelSyms.sched + 0x46) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20))) (sign_extend' 64 (mword_of_int 0x576 : mword 12))) (mycpu_a5 cid_word))
        by (rewrite /E3 upd_eq HE2s2 HshE; reflexivity).
      rewrite HE3v. rewrite (add_vec64_comm _ (mycpu_a5 cid_word)).
      unfold a_cpu_int, mycpu_ret. rewrite (add_vec64_comm _ (mycpu_a5 cid_word)).
      apply sched_reconcile. vm_compute. reflexivity. }
    iPoseProof (sdi_7a with "Htext") as "Hi7a".
    iApply (wp_sw_s_sconf (mword_of_int (KernelSyms.sched + 0x7a)) (mword_of_int 19 : mword 5) (mword_of_int 18 : mword 5)
              (mword_of_int 172 : mword 12) E3 (av - 6)%nat iv' false
              with "Hcg Hpc Hi7a [Hint2]").
    { iEval (rewrite Hrec_int2). iExact "Hint2". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hint2".
    iEval (rewrite Hrec_int2) in "Hint2".
    assert (Hpc7e : add_vec_int (mword_of_int (KernelSyms.sched + 0x7a) : mword 64) 4 = mword_of_int (KernelSyms.sched + 0x7e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc7e) in "Hpc".
    (* the restored intena cell holds this thread's saved base [intena_val eb]
       (s3 = the value read at +0x54, sign-extended then truncated back). *)
    assert (HE3s3 : E3 !!! Regidx (mword_of_int 19 : mword 5) = sign_extend' 64 (intena_val eb)).
    { rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_ne; [| vm_compute; discriminate].
      rewrite /E0 upd_ne; [| vm_compute; discriminate].
      exact Hs3v. }
    assert (Hstoreval : trunc32 (rget E3 (mword_of_int 19 : mword 5)) = intena_val eb).
    { rgne. rewrite HE3s3. destruct eb; vm_compute; reflexivity. }
    iEval (rewrite Hstoreval) in "Hint2".
    (* retune the count token from the resumer's base [eb'] to this thread's own
       saved base [eb].  Both directions are IDENTITIES now: the token is the
       bare '0' eighth at every level ≥ 1, because the handler resource it used
       to carry rides in [trap_csrs] instead -- which is also what removed the
       old obligation to name it at the RESUMING hart's ghost.  The intena cell
       was just restored to [intena_val eb] by the store. *)
    iAssert (intr_count 1 eb) with "[Hcnt2]" as "Hcnt2".
    { destruct eb.
      - iApply (intr_count_retune_on 0 eb' with "Hcnt2").
      - iApply (intr_count_retune_off 0 eb' with "Hcnt2"). }
    (* refold [cpu_own 1 eb pj emp false] -- at the swtch seam, carrying the
       pinned proc singleton (see the header comment). *)
    iAssert (cpu_own 1 eb pj false {["proc"]}) with "[Hcur2 Hnoff2 Hint2 Hlks2 Hcnt2]" as "Hcpu".
    { rewrite cpu_own_off /cpu_hart /cpu_priv /cpu_cells.
      iFrame "Hnoff2 Hcnt2 Hcur2 Hint2 Hlks2". iPureIntro; vm_compute; reflexivity. }
    (* ------------------------------------------------------------------ *)
    (* +0x7e..+0x8a: epilogue -- restore ra/s0/s1/s2/s3, pop frame, ret.   *)
    (* ------------------------------------------------------------------ *)
    (* the five saved frame cells arrive at [pa_stk sp0 k]; bridge each to
       the [spd + imm] form the c.ldsp leaves compute. *)
    iEval (rewrite Hb1) in "Hr1". iEval (rewrite Hb2) in "Hr2".
    iEval (rewrite Hb3) in "Hr3". iEval (rewrite Hb4) in "Hr4".
    iEval (rewrite Hb5) in "Hr5".
    (* sp = spd in the epilogue maps. *)
    assert (Hsp_E3 : E3 !!! Regidx csp_rs1 = spd).
    { rewrite /E3 upd_ne; [| vm_compute; discriminate]. rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_ne; [| vm_compute; discriminate]. rewrite /E0 upd_ne; [| vm_compute; discriminate].
      exact Hsp_m'. }
    (* +0x7e c.ldsp ra,40 *)
    iPoseProof (sdi_7e with "Htext") as "Hi7e".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sched + 0x7e)) (mword_of_int 5 : mword 6) (mword_of_int 1 : mword 5)
              E3 (av - 6)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi7e [Hr1]").
    { iEval (rewrite Hsp_E3). iExact "Hr1". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr1".
    set (E4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> E3).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> E3) with E4.
    assert (Hpc80 : add_vec_int (mword_of_int (KernelSyms.sched + 0x7e) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x80)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc80) in "Hpc".
    assert (Hsp_E4 : E4 !!! Regidx csp_rs1 = spd) by (rewrite /E4 upd_ne; [exact Hsp_E3 | vm_compute; discriminate]).
    (* +0x80 c.ldsp s0,32 *)
    iPoseProof (sdi_80 with "Htext") as "Hi80".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sched + 0x80)) (mword_of_int 4 : mword 6) (mword_of_int 8 : mword 5)
              E4 (av - 6)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi80 [Hr2]").
    { iEval (rewrite Hsp_E4). iExact "Hr2". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr2".
    set (E5 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E4).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E4) with E5.
    assert (Hpc82 : add_vec_int (mword_of_int (KernelSyms.sched + 0x80) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x82)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc82) in "Hpc".
    assert (Hsp_E5 : E5 !!! Regidx csp_rs1 = spd) by (rewrite /E5 upd_ne; [exact Hsp_E4 | vm_compute; discriminate]).
    (* +0x82 c.ldsp s1,24 *)
    iPoseProof (sdi_82 with "Htext") as "Hi82".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sched + 0x82)) (mword_of_int 3 : mword 6) (mword_of_int 9 : mword 5)
              E5 (av - 6)%nat (m !!! Regidx (mword_of_int 9 : mword 5)) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi82 [Hr3]").
    { iEval (rewrite Hsp_E5). iExact "Hr3". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr3".
    set (E6 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E5).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E5) with E6.
    assert (Hpc84 : add_vec_int (mword_of_int (KernelSyms.sched + 0x82) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x84)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc84) in "Hpc".
    assert (Hsp_E6 : E6 !!! Regidx csp_rs1 = spd) by (rewrite /E6 upd_ne; [exact Hsp_E5 | vm_compute; discriminate]).
    (* +0x84 c.ldsp s2,16 *)
    iPoseProof (sdi_84 with "Htext") as "Hi84".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sched + 0x84)) (mword_of_int 2 : mword 6) (mword_of_int 18 : mword 5)
              E6 (av - 6)%nat (m !!! Regidx (mword_of_int 18 : mword 5)) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi84 [Hr4]").
    { iEval (rewrite Hsp_E6). iExact "Hr4". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr4".
    set (E7 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> E6).
    change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> E6) with E7.
    assert (Hpc86 : add_vec_int (mword_of_int (KernelSyms.sched + 0x84) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x86)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc86) in "Hpc".
    assert (Hsp_E7 : E7 !!! Regidx csp_rs1 = spd) by (rewrite /E7 upd_ne; [exact Hsp_E6 | vm_compute; discriminate]).
    (* +0x86 c.ldsp s3,8 *)
    iPoseProof (sdi_86 with "Htext") as "Hi86".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sched + 0x86)) (mword_of_int 1 : mword 6) (mword_of_int 19 : mword 5)
              E7 (av - 6)%nat (m !!! Regidx (mword_of_int 19 : mword 5)) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi86 [Hr5]").
    { iEval (rewrite Hsp_E7). iExact "Hr5". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr5".
    set (E8 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 19 : mword 5))]> E7).
    change (<[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 19 : mword 5))]> E7) with E8.
    assert (Hpc88 : add_vec_int (mword_of_int (KernelSyms.sched + 0x86) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x88)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc88) in "Hpc".
    assert (Hsp_E8 : E8 !!! Regidx csp_rs1 = spd) by (rewrite /E8 upd_ne; [exact Hsp_E7 | vm_compute; discriminate]).
    (* +0x88 c.addi16sp sp,48 : pop the frame *)
    iPoseProof (sdi_88 with "Htext") as "Hi88".
    assert (Hspd6 : pa_stk sp0 6 = spd).
    { rewrite -Hspd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpopsp : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0).
    { rewrite -Hspd add_vec_assoc.
      assert (HAB : add_vec (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite HAB. apply kv_addv_zero. }
    iEval (rewrite Hsp_E3) in "Hr1". iEval (rewrite Hsp_E4) in "Hr2".
    iEval (rewrite Hsp_E5) in "Hr3". iEval (rewrite Hsp_E6) in "Hr4".
    iEval (rewrite Hsp_E7) in "Hr5".
    iAssert (stack_own sp0 6) with "[Hr1 Hr2 Hr3 Hr4 Hr5 Hgap]" as "Hframe6".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr1". { iExists _. iEval (rewrite Hb1). iExact "Hr1". }
      iSplitL "Hr2". { iExists _. iEval (rewrite Hb2). iExact "Hr2". }
      iSplitL "Hr3". { iExists _. iEval (rewrite Hb3). iExact "Hr3". }
      iSplitL "Hr4". { iExists _. iEval (rewrite Hb4). iExact "Hr4". }
      iSplitL "Hr5". { iExists _. iEval (rewrite Hb5). iExact "Hr5". }
      iSplitL "Hgap". { iExists _. iExact "Hgap". }
      done. }
    assert (Hpop_prem : E8 !!! Regidx csp_rs1 = pa_stk (add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6).
    { rewrite Hsp_E8 Hpopsp Hspd6. reflexivity. }
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.sched + 0x88)) (mword_of_int 3 : mword 6) E8 (av - 6)%nat 6 false
              Hpop_prem
              with "Hcg Hpc Hi88 [Hframe6]").
    { rewrite Hsp_E8 Hpopsp. iExact "Hframe6". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (Ef := <[Regidx csp_rs1 := regval_into_reg (add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E8).
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E8) with Ef.
    assert (Havk : ((av - 6) + 6)%nat = av) by lia.
    iEval (rewrite Havk) in "Hcg".
    assert (Hpc8a : add_vec_int (mword_of_int (KernelSyms.sched + 0x88) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x8a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc8a) in "Hpc".
    (* +0x8a c.ret *)
    assert (HEfra : Ef !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /Ef upd_ne; [| vm_compute; discriminate].
      rewrite /E8 upd_ne; [| vm_compute; discriminate]. rewrite /E7 upd_ne; [| vm_compute; discriminate].
      rewrite /E6 upd_ne; [| vm_compute; discriminate]. rewrite /E5 upd_ne; [| vm_compute; discriminate].
      rewrite /E4 upd_eq. reflexivity. }
    iPoseProof (sdi_8a with "Htext") as "Hi8a".
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.sched + 0x8a)) (mword_of_int 1 : mword 5) Ef av false
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi8a").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hret_final : ret_pc (rget Ef (mword_of_int 1 : mword 5))
                         = ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)))
      by (rgne; rewrite HEfra; reflexivity).
    iEval (rewrite Hret_final) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* Postcondition.                                                      *)
    (* ------------------------------------------------------------------ *)
    (* threading helper for the untouched callee-saved registers s4..s11. *)
    (* per-register threading for s4..s11: Ef -> m' (the eight [Hm*] premises,
       which the caller derives from the callee image + its own tower). *)
    assert (Hs_final : forall c : mword 5,
      Regidx c ≠ Regidx (mword_of_int 1) -> Regidx c ≠ Regidx (mword_of_int 8) ->
      Regidx c ≠ Regidx (mword_of_int 9) -> Regidx c ≠ Regidx (mword_of_int 15) ->
      Regidx c ≠ Regidx (mword_of_int 18) -> Regidx c ≠ Regidx (mword_of_int 19) ->
      Regidx c ≠ Regidx csp_rs1 ->
      m' !!! Regidx c = m !!! Regidx c ->
      Ef !!! Regidx c = m !!! Regidx c).
    { intros c H1 H8 H9 H15 H18 H19 Hsp Hmm.
      rewrite /Ef upd_ne; [| exact Hsp].
      rewrite /E8 upd_ne; [| exact H19]. rewrite /E7 upd_ne; [| exact H18].
      rewrite /E6 upd_ne; [| exact H9]. rewrite /E5 upd_ne; [| exact H8].
      rewrite /E4 upd_ne; [| exact H1]. rewrite /E3 upd_ne; [| exact H18].
      rewrite /E2 upd_ne; [| exact H15]. rewrite /E1 upd_ne; [| exact H15].
      rewrite /E0 upd_ne; [| exact H15].
      exact Hmm. }
    iApply ("Hcont" $! Ef ch'
              with "[%] Hcg Hpc Hheld' Htc Hcpu Hown Htag Hvc'").
    { (* callee_saved m Ef *)
      assert (Hf_sp : Ef !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
        by (rewrite /Ef upd_eq Hsp_E8 -Hsp0; exact Hpopsp).
      assert (Hf_s0 : Ef !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5)).
      { rewrite /Ef upd_ne; [| vm_compute; discriminate].
        rewrite /E8 upd_ne; [| vm_compute; discriminate]. rewrite /E7 upd_ne; [| vm_compute; discriminate].
        rewrite /E6 upd_ne; [| vm_compute; discriminate]. rewrite /E5 upd_eq. reflexivity. }
      assert (Hf_s1 : Ef !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5)).
      { rewrite /Ef upd_ne; [| vm_compute; discriminate].
        rewrite /E8 upd_ne; [| vm_compute; discriminate]. rewrite /E7 upd_ne; [| vm_compute; discriminate].
        rewrite /E6 upd_eq. reflexivity. }
      assert (Hf_s2 : Ef !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5)).
      { rewrite /Ef upd_ne; [| vm_compute; discriminate].
        rewrite /E8 upd_ne; [| vm_compute; discriminate]. rewrite /E7 upd_eq. reflexivity. }
      assert (Hf_s3 : Ef !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5)).
      { rewrite /Ef upd_ne; [| vm_compute; discriminate]. rewrite /E8 upd_eq. reflexivity. }
      assert (Hf_s4 : Ef !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5))
        by (apply Hs_final; (first [ vm_compute; discriminate | exact Hm20 ])).
      assert (Hf_s5 : Ef !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5))
        by (apply Hs_final; (first [ vm_compute; discriminate | exact Hm21 ])).
      assert (Hf_s6 : Ef !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5))
        by (apply Hs_final; (first [ vm_compute; discriminate | exact Hm22 ])).
      assert (Hf_s7 : Ef !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5))
        by (apply Hs_final; (first [ vm_compute; discriminate | exact Hm23 ])).
      assert (Hf_s8 : Ef !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5))
        by (apply Hs_final; (first [ vm_compute; discriminate | exact Hm24 ])).
      assert (Hf_s9 : Ef !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5))
        by (apply Hs_final; (first [ vm_compute; discriminate | exact Hm25 ])).
      assert (Hf_s10 : Ef !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5))
        by (apply Hs_final; (first [ vm_compute; discriminate | exact Hm26 ])).
      assert (Hf_s11 : Ef !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5))
        by (apply Hs_final; (first [ vm_compute; discriminate | exact Hm27 ])).
      unfold callee_saved. repeat split; assumption. }
  Qed.

End SchedPostSwtch.

Section ProofSched.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_sched_sconf 
      (γs : list gname) (j : nat) (γl : gname) (st : mword 32) (ch : mword 64)
      (m : regfile) (av : nat) (eb : bool)
    : wp_sched_sconf_body γs j γl st ch m av eb.
  Proof.
    cbv beta delta [wp_sched_sconf_body].
    intros pcE pj ret_tgt Hj Hgl Hneeds Hav.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg #Htext Hpc #Hprocs Hheld Hpay Htc Hcpu Hown Htag Hvc Hcont".
    (* the cpu bundle [cpu_own 1 eb pj emp false] arrives whole at level 1;
       it is unfolded to the individual cells + counting token after myproc.
       NOTE: no handler stash is taken from it.  The return path resumes on a
       DIFFERENT hart, whose SIE ghost is a different (canonical) name, so a
       stash copied here would be about the wrong one; the resource arrives
       inside the dispatch payload's own [trap_csrs] instead. *)
    iDestruct "Hheld" as "(Hlocked & Hstate & Hchan & Hpub)".
    iDestruct "Hown" as (ctxvs) "[%Hctxlen Hctxcells]".
    (* ------------------------------------------------------------------ *)
    (* Prologue: 48-byte frame (push 6), save ra/s0/s1/s2/s3.             *)
    (* ------------------------------------------------------------------ *)
    set (spd := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))).
    iPoseProof (sdi_00 with "Htext") as "Hi00".
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 6).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 61 : mword 6) m av 6 false
              ltac:(lia) Hpush with "Hcg Hpc Hi00").
    iApply wp_next_off_intro.
    iIntros "Hcg Hframe Hpc".
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m) with A0.
    assert (HcspA0 : A0 !!! Regidx csp_rs1 = spd) by (rewrite /A0 upd_eq; reflexivity).
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    (* split the 6-slot frame into cells. *)
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & S5c & S6c & _)".
    iDestruct "S1c" as (vr1) "Hr1". iDestruct "S2c" as (vr2) "Hr2".
    iDestruct "S3c" as (vr3) "Hr3". iDestruct "S4c" as (vr4) "Hr4".
    iDestruct "S5c" as (vr5) "Hr5". iDestruct "S6c" as (vgap) "Hgap".
    assert (Hb1 : pa_stk sp0 1 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))
      by (apply sched_frame_bridge; vm_compute; reflexivity).
    assert (Hb2 : pa_stk sp0 2 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))
      by (apply sched_frame_bridge; vm_compute; reflexivity).
    assert (Hb3 : pa_stk sp0 3 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))))
      by (apply sched_frame_bridge; vm_compute; reflexivity).
    assert (Hb4 : pa_stk sp0 4 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))
      by (apply sched_frame_bridge; vm_compute; reflexivity).
    assert (Hb5 : pa_stk sp0 5 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))))
      by (apply sched_frame_bridge; vm_compute; reflexivity).
    (* +0x02 c.sdsp ra,40 *)
    iPoseProof (sdi_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sched + 0x02)) (mword_of_int 5 : mword 6) (mword_of_int 1 : mword 5)
              A0 (av - 6)%nat vr1 false with "Hcg Hpc Hi02 [Hr1]").
    { iEval (rewrite HcspA0 -Hb1). iExact "Hr1". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr1".
    iEval (rgne) in "Hr1".
    assert (Hpc04 : add_vec_int (mword_of_int (KernelSyms.sched + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    (* +0x04 c.sdsp s0,32 *)
    iPoseProof (sdi_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sched + 0x04)) (mword_of_int 4 : mword 6) (mword_of_int 8 : mword 5)
              A0 (av - 6)%nat vr2 false with "Hcg Hpc Hi04 [Hr2]").
    { iEval (rewrite HcspA0 -Hb2). iExact "Hr2". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr2".
    iEval (rgne) in "Hr2".
    assert (Hpc06 : add_vec_int (mword_of_int (KernelSyms.sched + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    (* +0x06 c.sdsp s1,24 *)
    iPoseProof (sdi_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sched + 0x06)) (mword_of_int 3 : mword 6) (mword_of_int 9 : mword 5)
              A0 (av - 6)%nat vr3 false with "Hcg Hpc Hi06 [Hr3]").
    { iEval (rewrite HcspA0 -Hb3). iExact "Hr3". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr3".
    iEval (rgne) in "Hr3".
    assert (Hpc08 : add_vec_int (mword_of_int (KernelSyms.sched + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    (* +0x08 c.sdsp s2,16 *)
    iPoseProof (sdi_08 with "Htext") as "Hi08".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sched + 0x08)) (mword_of_int 2 : mword 6) (mword_of_int 18 : mword 5)
              A0 (av - 6)%nat vr4 false with "Hcg Hpc Hi08 [Hr4]").
    { iEval (rewrite HcspA0 -Hb4). iExact "Hr4". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr4".
    iEval (rgne) in "Hr4".
    assert (Hpc0a : add_vec_int (mword_of_int (KernelSyms.sched + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    (* +0x0a c.sdsp s3,8 *)
    iPoseProof (sdi_0a with "Htext") as "Hi0a".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sched + 0x0a)) (mword_of_int 1 : mword 6) (mword_of_int 19 : mword 5)
              A0 (av - 6)%nat vr5 false with "Hcg Hpc Hi0a [Hr5]").
    { iEval (rewrite HcspA0 -Hb5). iExact "Hr5". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr5".
    iEval (rgne) in "Hr5".
    assert (Hpc0c : add_vec_int (mword_of_int (KernelSyms.sched + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    (* +0x0c c.addi4spn s0,sp,48 *)
    iPoseProof (sdi_0c with "Htext") as "Hi0c".
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.sched + 0x0c)) (Cregidx (mword_of_int 0)) (mword_of_int 12 : mword 8) (mword_of_int 8 : mword 5)
              A0 (av - 6)%nat false ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (A1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> A0).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> A0) with A1.
    assert (Hpc0e : add_vec_int (mword_of_int (KernelSyms.sched + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0e) in "Hpc".
    (* +0x0e jal myproc *)
    iPoseProof (sdi_0e with "Htext") as "Hi0e".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sched + 0x0e)) (mword_of_int 1 : mword 5) (mword_of_int 2095824 : mword 21)
              A1 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0e").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (A2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sched + 0x0e) : mword 64) 4)]> A1).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sched + 0x0e) : mword 64) 4)]> A1) with A2.
    assert (Hpcmp : add_vec (mword_of_int (KernelSyms.sched + 0x0e) : mword 64) (sign_extend' 64 (mword_of_int 2095824 : mword 21))
                    = mword_of_int KernelSyms.myproc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcmp) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x0e: myproc() -- returns a0 = proc_addr j; noff/intena untouched. *)
    (* ------------------------------------------------------------------ *)
    assert (HA2ra : A2 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.sched + 0x0e) : mword 64) 4)
      by (rewrite /A2 upd_eq; reflexivity).
    iApply (Myproc.wp_myproc_sconf A2 (av - 6)%nat 1 eb (proc_addr j) false {["proc"]}
              ltac:(vm_compute; reflexivity)
              ltac:(lia)
              with "Hcg Hcpu Htext Hpc").
    iApply wp_next_off_intro.
    iIntros (ms mp) "%Hmsf Hcg Hcpu Hpc %Hmp".
    destruct Hmp as [Hcs_mp Ha0_mp].
    (* re-unfold the (unchanged) returned bundle into the individual cells the
       check-chain reads, and name the level-1 intena value. *)
    iEval (rewrite cpu_own_off /cpu_hart /cpu_priv /cpu_cells) in "Hcpu".
    iDestruct "Hcpu" as "(((_ & Hnoff & Hint & Hcur) & Hlks) & Hcnt)".
    set (iv := intena_val eb : mword 32).
    assert (Hpc12 : ret_pc (A2 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.sched + 0x12)) by (rewrite HA2ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    (* +0x12 c.mv s1,a0 : s1 := a0 = proc_addr j *)
    iPoseProof (sdi_12 with "Htext") as "Hi12".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sched + 0x12)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              mp (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Ha0_mpr : rget mp (mword_of_int 10 : mword 5) = proc_addr j)
      by (rgne; exact Ha0_mp).
    set (B0 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (rget mp (mword_of_int 10 : mword 5)))]> mp).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (rget mp (mword_of_int 10 : mword 5)))]> mp) with B0.
    assert (Hpc14 : add_vec_int (mword_of_int (KernelSyms.sched + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    (* +0x14 jal holding *)
    iPoseProof (sdi_14 with "Htext") as "Hi14".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sched + 0x14)) (mword_of_int 1 : mword 5) (mword_of_int 2092356 : mword 21)
              B0 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi14").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (B1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sched + 0x14) : mword 64) 4)]> B0).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sched + 0x14) : mword 64) 4)]> B0) with B1.
    assert (Hpchd : add_vec (mword_of_int (KernelSyms.sched + 0x14) : mword 64) (sign_extend' 64 (mword_of_int 2092356 : mword 21))
                    = mword_of_int KernelSyms.holding) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpchd) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x14: holding(&p->lock) -- locked, so a0 := 1.                     *)
    (* ------------------------------------------------------------------ *)
    (* a0 is still proc_addr j (myproc's return, unmodified by c.mv/jal). *)
    assert (Ha0_B1 : B1 !!! Regidx (mword_of_int 10 : mword 5) = proc_addr j).
    { rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite /B0 upd_ne; [| vm_compute; discriminate]. exact Ha0_mp. }
    iPoseProof (procs_inv_lookup γs j γl Hgl with "Hprocs") as "#Hislock".
    assert (Hlkb : add_vec (B1 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = proc_addr j).
    { rewrite Ha0_B1.
      assert (H0 : sign_extend' 64 (mword_of_int 0 : mword 12) = (mword_of_int 0 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite H0. apply kv_addv_zero. }
    assert (HB1ra : B1 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.sched + 0x14) : mword 64) 4)
      by (rewrite /B1 upd_eq; reflexivity).
    iApply (Holding.wp_holding_lockinv_locked_s_sconf γl (proc_addr j) "proc"
              (proc_lock_res γs γl (proc_addr j)) False%I B1 (av - 6)%nat pj
              Hlkb ltac:(lia) (lock_refute_False _)
              with "Hcg Htext Hpc [] Hlocked").
    { iApply (is_lock_openable with "Hislock"). }
    iIntros (mh) "Hcg Hpc %Hmh Hlocked".
    destruct Hmh as [Hcs_mh Ha0_mh].
    assert (Hpc18 : ret_pc (add_vec_int (mword_of_int (KernelSyms.sched + 0x14) : mword 64) 4)
                    = mword_of_int (KernelSyms.sched + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    (* pc after holding = ret_tgt = ret_pc(B1!!!x1) = KernelSyms.sched+0x18. *)
    iEval (rewrite HB1ra Hpc18) in "Hpc".
    (* +0x18 c.beqz a0 : a0 = 1, falls through. *)
    iPoseProof (sdi_18 with "Htext") as "Hi18".
    assert (Ha0_beqz : eq_vec (rget mh (mword_of_int 10 : mword 5)) zero_reg = false)
      by (rgne; rewrite Ha0_mh; vm_compute; reflexivity).
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.sched + 0x18)) (mword_of_int 58 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
              mh (av - 6)%nat false ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Ha0_beqz
              with "Hcg Hpc Hi18").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpc1a : add_vec_int (mword_of_int (KernelSyms.sched + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1a) in "Hpc".
    (* tp and s1 threaded through holding. *)
    assert (Hs1_mh : mh !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j)).
    { rewrite (callee_saved_lookup Hcs_mh (mword_of_int 9) ltac:(vm_compute; reflexivity)).
      rewrite /B1 upd_ne; [| vm_compute; discriminate]. rewrite /B0 upd_eq Ha0_mpr. reflexivity. }
    (* ------------------------------------------------------------------ *)
    (* +0x1a..+0x30: read mycpu()->noff (inlined) and check == 1.          *)
    (* ------------------------------------------------------------------ *)
    (* +0x1a c.mv a5,tp *)
    iPoseProof (sdi_1a with "Htext") as "Hi1a".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sched + 0x1a)) (mword_of_int 15 : mword 5) (mword_of_int 4 : mword 5)
              mh (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (C0 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (rget mh (mword_of_int 4 : mword 5)))]> mh).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (rget mh (mword_of_int 4 : mword 5)))]> mh) with C0.
    assert (Hpc1c : add_vec_int (mword_of_int (KernelSyms.sched + 0x1a) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1c) in "Hpc".
    (* +0x1c sext.w a5 *)
    iPoseProof (sdi_1c with "Htext") as "Hi1c".
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.sched + 0x1c)) (mword_of_int 15 : mword 5) (mword_of_int 0 : mword 6)
              C0 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (C1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec (add_vec (C0 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> C0).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec (add_vec (C0 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> C0) with C1.
    assert (Hpc1e : add_vec_int (mword_of_int (KernelSyms.sched + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1e) in "Hpc".
    (* +0x1e c.slli a5,7 *)
    iPoseProof (sdi_1e with "Htext") as "Hi1e".
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.sched + 0x1e)) (Regidx (mword_of_int 15)) (mword_of_int 15 : mword 5) (mword_of_int 7 : mword 6)
              C1 (av - 6)%nat false eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (C2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_left (C1 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 7 : mword 6) (Z.sub log2_xlen 1) 0))]> C1).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_left (C1 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 7 : mword 6) (Z.sub log2_xlen 1) 0))]> C1) with C2.
    assert (Hsh : C2 !!! Regidx (mword_of_int 15 : mword 5) = mycpu_a5 cid_word).
    { rewrite /C2 upd_eq /C1 upd_eq /C0 upd_eq (rget_tp mh). reflexivity. }
    assert (Hpc20 : add_vec_int (mword_of_int (KernelSyms.sched + 0x1e) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc20) in "Hpc".
    (* +0x20 auipc a4,0x10 *)
    iPoseProof (sdi_20 with "Htext") as "Hi20".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.sched + 0x20)) (mword_of_int 14 : mword 5) (mword_of_int 0x10 : mword 20)
              C2 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi20").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (C3 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.sched + 0x20) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))]> C2).
    change (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.sched + 0x20) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))]> C2) with C3.
    assert (Hpc24 : add_vec_int (mword_of_int (KernelSyms.sched + 0x20) : mword 64) 4 = mword_of_int (KernelSyms.sched + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc24) in "Hpc".
    (* +0x24 addi a4,a4,1290 *)
    iPoseProof (sdi_24 with "Htext") as "Hi24".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sched + 0x24)) (mword_of_int 14 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 0x59c : mword 12)
              C3 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (C4 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (C3 !!! Regidx (mword_of_int 14 : mword 5)) (sign_extend' 64 (mword_of_int 1436 : mword 12)))]> C3).
    change (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (C3 !!! Regidx (mword_of_int 14 : mword 5)) (sign_extend' 64 (mword_of_int 1436 : mword 12)))]> C3) with C4.
    assert (Hpc28 : add_vec_int (mword_of_int (KernelSyms.sched + 0x24) : mword 64) 4 = mword_of_int (KernelSyms.sched + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    (* +0x28 c.add a5,a5,a4 *)
    iPoseProof (sdi_28 with "Htext") as "Hi28".
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.sched + 0x28)) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5)
              C4 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi28").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (C5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (C4 !!! Regidx (mword_of_int 15 : mword 5)) (C4 !!! Regidx (mword_of_int 14 : mword 5)))]> C4).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (C4 !!! Regidx (mword_of_int 15 : mword 5)) (C4 !!! Regidx (mword_of_int 14 : mword 5)))]> C4) with C5.
    assert (Hpc2a : add_vec_int (mword_of_int (KernelSyms.sched + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    (* +0x2a lw a4,168(a5) : reconcile to a_cpu_noff *)
    assert (Hrec_noff : add_vec (rget C5 (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 168 : mword 12))
                        = a_cpu_noff cid_word).
    { rgne. assert (HC5v : C5 !!! Regidx (mword_of_int 15 : mword 5)
                     = add_vec (mycpu_a5 cid_word)
                         (add_vec (add_vec (mword_of_int (KernelSyms.sched + 0x20) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))
                                  (sign_extend' 64 (mword_of_int 0x59c : mword 12)))).
      { rewrite /C5 upd_eq.
        rewrite (_ : C4 !!! Regidx (mword_of_int 15 : mword 5) = mycpu_a5 cid_word).
        2:{ rewrite /C4 upd_ne; [| vm_compute; discriminate]. rewrite /C3 upd_ne; [| vm_compute; discriminate]. exact Hsh. }
        rewrite (_ : C4 !!! Regidx (mword_of_int 14 : mword 5)
                     = add_vec (add_vec (mword_of_int (KernelSyms.sched + 0x20) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20))) (sign_extend' 64 (mword_of_int 0x59c : mword 12))).
        2:{ rewrite /C4 upd_eq /C3 upd_eq. reflexivity. }
        reflexivity. }
      rewrite HC5v.
      unfold a_cpu_noff, mycpu_ret.
      rewrite (add_vec64_comm _ (mycpu_a5 cid_word)).
      apply sched_reconcile. vm_compute. reflexivity. }
    iPoseProof (sdi_2a with "Htext") as "Hi2a".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.sched + 0x2a)) (mword_of_int 14 : mword 5) (mword_of_int 15 : mword 5)
              (mword_of_int 168 : mword 12) C5 (av - 6)%nat (mword_of_int 1 : mword 32) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2a [Hnoff]").
    { iEval (rewrite Hrec_noff). iExact "Hnoff". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hnoff".
    iEval (rewrite Hrec_noff) in "Hnoff".
    set (C6 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (sign_extend' 64 (mword_of_int 1 : mword 32))]> C5).
    change (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (sign_extend' 64 (mword_of_int 1 : mword 32))]> C5) with C6.
    assert (Hpc2e : add_vec_int (mword_of_int (KernelSyms.sched + 0x2a) : mword 64) 4 = mword_of_int (KernelSyms.sched + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2e) in "Hpc".
    (* +0x2e c.li a5,1 *)
    iPoseProof (sdi_2e with "Htext") as "Hi2e".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sched + 0x2e)) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) C6 (av - 6)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc Hi2e").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (C7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> C6).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> C6) with C7.
    assert (Hpc30 : add_vec_int (mword_of_int (KernelSyms.sched + 0x2e) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc30) in "Hpc".
    (* +0x30 bne a4,a5 : a4 = 1 = a5, falls through *)
    iPoseProof (sdi_30 with "Htext") as "Hi30".
    assert (Ha4C7 : C7 !!! Regidx (mword_of_int 14 : mword 5) = sign_extend' 64 (mword_of_int 1 : mword 32)).
    { rewrite /C7 upd_ne; [| vm_compute; discriminate]. rewrite /C6 upd_eq. reflexivity. }
    assert (Ha5C7 : C7 !!! Regidx (mword_of_int 15 : mword 5) = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
      by (rewrite /C7 upd_eq; reflexivity).
    assert (Hbne : neq_vec (rget C7 (mword_of_int 14 : mword 5)) (rget C7 (mword_of_int 15 : mword 5)) = false)
      by (rgne; rgne; rewrite Ha4C7 Ha5C7; vm_compute; reflexivity).
    iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.sched + 0x30)) (mword_of_int 104 : mword 13) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5)
              C7 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              Hbne
              with "Hcg Hpc Hi30").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpc34 : add_vec_int (mword_of_int (KernelSyms.sched + 0x30) : mword 64) 4 = mword_of_int (KernelSyms.sched + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc34) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x34..+0x38: read p->state and check != RUNNING.                   *)
    (* ------------------------------------------------------------------ *)
    (* +0x34 c.lw a4,24(s1) : reconcile to p_state (proc_addr j) *)
    assert (Hrec_state : add_vec (rget C7 (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 24 : mword 12))
                         = p_state (proc_addr j)).
    { rgne. assert (HC7s1 : C7 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j)).
      { rewrite /C7 upd_ne; [| vm_compute; discriminate]. rewrite /C6 upd_ne; [| vm_compute; discriminate].
        rewrite /C5 upd_ne; [| vm_compute; discriminate]. rewrite /C4 upd_ne; [| vm_compute; discriminate].
        rewrite /C3 upd_ne; [| vm_compute; discriminate]. rewrite /C2 upd_ne; [| vm_compute; discriminate].
        rewrite /C1 upd_ne; [| vm_compute; discriminate]. rewrite /C0 upd_ne; [| vm_compute; discriminate].
        exact Hs1_mh. }
      rewrite HC7s1 add_vec_zero_l. unfold p_state, state_off.
      assert (H24 : sign_extend' 64 (mword_of_int 24 : mword 12) = (mword_of_int 24 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite H24. reflexivity. }
    iPoseProof (sdi_34 with "Htext") as "Hi34".
    iApply (wp_clw_s_sconf (mword_of_int (KernelSyms.sched + 0x34)) (mword_of_int 14 : mword 5) (mword_of_int 9 : mword 5)
              (mword_of_int 24 : mword 12) C7 (av - 6)%nat st false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi34 [Hstate]").
    { iEval (rewrite Hrec_state). iExact "Hstate". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hstate".
    iEval (rewrite Hrec_state) in "Hstate".
    set (C8 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (sign_extend' 64 st)]> C7).
    change (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (sign_extend' 64 st)]> C7) with C8.
    assert (Hpc36 : add_vec_int (mword_of_int (KernelSyms.sched + 0x34) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc36) in "Hpc".
    (* +0x36 c.li a5,4 *)
    iPoseProof (sdi_36 with "Htext") as "Hi36".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sched + 0x36)) (mword_of_int 15 : mword 5) (mword_of_int 4 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6)))) C8 (av - 6)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc Hi36").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (C9 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))))]> C8).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))))]> C8) with C9.
    assert (Hpc38 : add_vec_int (mword_of_int (KernelSyms.sched + 0x36) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc38) in "Hpc".
    (* +0x38 beq a4,a5 : state != RUNNING (needs_ctx st), falls through *)
    iPoseProof (sdi_38 with "Htext") as "Hi38".
    assert (Ha4C9 : C9 !!! Regidx (mword_of_int 14 : mword 5) = sign_extend' 64 st).
    { rewrite /C9 upd_ne; [| vm_compute; discriminate]. rewrite /C8 upd_eq. reflexivity. }
    assert (Ha5C9 : C9 !!! Regidx (mword_of_int 15 : mword 5) = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))))
      by (rewrite /C9 upd_eq; reflexivity).
    assert (Hbeq : eq_vec (sign_extend' 64 st) (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6)))) = false).
    { apply park_ok_cases in Hneeds as [Hn | ->].
      - apply needs_ctx_cases in Hn as [H|[H|H]]; subst st;
          vm_compute; reflexivity.
      - vm_compute; reflexivity. }
    assert (Hbeqr : eq_vec (rget C9 (mword_of_int 14 : mword 5)) (rget C9 (mword_of_int 15 : mword 5)) = false)
      by (rgne; rgne; rewrite Ha4C9 Ha5C9; exact Hbeq).
    iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.sched + 0x38)) (mword_of_int 108 : mword 13) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5)
              C9 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              Hbeqr
              with "Hcg Hpc Hi38").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpc3c : add_vec_int (mword_of_int (KernelSyms.sched + 0x38) : mword 64) 4 = mword_of_int (KernelSyms.sched + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc3c) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x3c..+0x42: csrr sstatus; check SIE == 0.                         *)
    (* ------------------------------------------------------------------ *)
    iPoseProof (sdi_3c with "Htext") as "Hi3c".
    iApply (wp_csrr_sstatus_s_sconf (mword_of_int (KernelSyms.sched + 0x3c)) (mword_of_int 15 : mword 5)
              C9 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3c").
    iApply wp_next_off_intro.
    (* at the DISABLED index the leaf itself reports [SIE = sie_bit false];
       no ghost juggling with the counting token is needed any more. *)
    iIntros (ms2) "%Hmsf2 Hhs Hsc Htlbinv Hpc Hfile Hcapdisj".
    iDestruct "Hcapdisj" as "(Hstk & %HSIE0 & Harm)".
    set (C10 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sstatus_read ms2)]> C9).
    iDestruct (sconf_at_close with "Hsc") as "Hsc".
    iDestruct (sie_cap_gpr_join C10 (av - 6)%nat false pj with "Hhs Hsc [Hstk Htlbinv Harm] Hfile") as "Hcg".
    { rewrite /sie_cap. iFrame "Hstk Htlbinv Harm". iApply sie_cap_wit_KT0. }
    assert (Hpc40 : add_vec_int (mword_of_int (KernelSyms.sched + 0x3c) : mword 64) 4 = mword_of_int (KernelSyms.sched + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc40) in "Hpc".
    (* +0x40 c.andi a5,a5,2 *)
    iPoseProof (sdi_40 with "Htext") as "Hi40".
    iApply (wp_candi_s_sconf (mword_of_int (KernelSyms.sched + 0x40)) (mword_of_int 15 : mword 5) (mword_of_int 2 : mword 6)
              C10 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi40").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (C11 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (and_vec (C10 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))]> C10).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (and_vec (C10 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))]> C10) with C11.
    assert (Hpc42 : add_vec_int (mword_of_int (KernelSyms.sched + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc42) in "Hpc".
    (* +0x42 c.bnez a5 : SIE bit clear, falls through *)
    iPoseProof (sdi_42 with "Htext") as "Hi42".
    assert (HSIEne : eq_vec (_get_Mstatus_SIE ms2) ('b"1") = false) by (rewrite HSIE0; vm_compute; reflexivity).
    assert (Ha5C11 : C11 !!! Regidx (mword_of_int 15 : mword 5)
                     = and_vec (sstatus_read ms2) (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))).
    { rewrite /C11 upd_eq /C10 upd_eq. reflexivity. }
    assert (Hbnez : neq_vec (rget C11 (mword_of_int 15 : mword 5)) zero_reg = false)
      by (rgne; rewrite Ha5C11; exact (sched_sstatus_clear ms2 HSIEne)).
    iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.sched + 0x42)) (mword_of_int 55 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
              C11 (av - 6)%nat false ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              Hbnez
              with "Hcg Hpc Hi42").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpc44 : add_vec_int (mword_of_int (KernelSyms.sched + 0x42) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc44) in "Hpc".
    (* tp / s1 threaded through the check chain. *)
    assert (HC11_x9 : C11 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j)).
    { rewrite /C11 upd_ne; [| vm_compute; discriminate]. rewrite /C10 upd_ne; [| vm_compute; discriminate].
      rewrite /C9 upd_ne; [| vm_compute; discriminate]. rewrite /C8 upd_ne; [| vm_compute; discriminate].
      rewrite /C7 upd_ne; [| vm_compute; discriminate]. rewrite /C6 upd_ne; [| vm_compute; discriminate].
      rewrite /C5 upd_ne; [| vm_compute; discriminate]. rewrite /C4 upd_ne; [| vm_compute; discriminate].
      rewrite /C3 upd_ne; [| vm_compute; discriminate]. rewrite /C2 upd_ne; [| vm_compute; discriminate].
      rewrite /C1 upd_ne; [| vm_compute; discriminate]. rewrite /C0 upd_ne; [| vm_compute; discriminate].
      exact Hs1_mh. }
    (* ------------------------------------------------------------------ *)
    (* +0x44..+0x54: read mycpu()->intena into s3.                        *)
    (* ------------------------------------------------------------------ *)
    (* +0x44 c.mv a5,tp *)
    iPoseProof (sdi_44 with "Htext") as "Hi44".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sched + 0x44)) (mword_of_int 15 : mword 5) (mword_of_int 4 : mword 5)
              C11 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi44").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (D0 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (rget C11 (mword_of_int 4 : mword 5)))]> C11).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (rget C11 (mword_of_int 4 : mword 5)))]> C11) with D0.
    assert (Hpc46 : add_vec_int (mword_of_int (KernelSyms.sched + 0x44) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc46) in "Hpc".
    (* +0x46 auipc s2,0x10 *)
    iPoseProof (sdi_46 with "Htext") as "Hi46".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.sched + 0x46)) (mword_of_int 18 : mword 5) (mword_of_int 0x10 : mword 20)
              D0 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi46").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (D1 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.sched + 0x46) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))]> D0).
    change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.sched + 0x46) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))]> D0) with D1.
    assert (Hpc4a : add_vec_int (mword_of_int (KernelSyms.sched + 0x46) : mword 64) 4 = mword_of_int (KernelSyms.sched + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc4a) in "Hpc".
    (* +0x4a addi s2,s2,1252 *)
    iPoseProof (sdi_4a with "Htext") as "Hi4a".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sched + 0x4a)) (mword_of_int 18 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0x576 : mword 12)
              D1 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4a").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (D2 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (D1 !!! Regidx (mword_of_int 18 : mword 5)) (sign_extend' 64 (mword_of_int 1398 : mword 12)))]> D1).
    change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (D1 !!! Regidx (mword_of_int 18 : mword 5)) (sign_extend' 64 (mword_of_int 1398 : mword 12)))]> D1) with D2.
    assert (Hpc4e : add_vec_int (mword_of_int (KernelSyms.sched + 0x4a) : mword 64) 4 = mword_of_int (KernelSyms.sched + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc4e) in "Hpc".
    (* +0x4e sext.w a5 *)
    iPoseProof (sdi_4e with "Htext") as "Hi4e".
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.sched + 0x4e)) (mword_of_int 15 : mword 5) (mword_of_int 0 : mword 6)
              D2 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4e").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (D3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec (add_vec (D2 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> D2).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec (add_vec (D2 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> D2) with D3.
    assert (Hpc50 : add_vec_int (mword_of_int (KernelSyms.sched + 0x4e) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc50) in "Hpc".
    (* +0x50 c.slli a5,7 *)
    iPoseProof (sdi_50 with "Htext") as "Hi50".
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.sched + 0x50)) (Regidx (mword_of_int 15)) (mword_of_int 15 : mword 5) (mword_of_int 7 : mword 6)
              D3 (av - 6)%nat false eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi50").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (D4 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_left (D3 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 7 : mword 6) (Z.sub log2_xlen 1) 0))]> D3).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_left (D3 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 7 : mword 6) (Z.sub log2_xlen 1) 0))]> D3) with D4.
    assert (HshD : D4 !!! Regidx (mword_of_int 15 : mword 5) = mycpu_a5 cid_word).
    { rewrite /D4 upd_eq /D3 upd_eq.
      rewrite /D2 upd_ne; [| vm_compute; discriminate]. rewrite /D1 upd_ne; [| vm_compute; discriminate].
      rewrite /D0 upd_eq (rget_tp C11). reflexivity. }
    assert (HD4s2 : D4 !!! Regidx (mword_of_int 18 : mword 5)
                    = add_vec (add_vec (mword_of_int (KernelSyms.sched + 0x46) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20))) (sign_extend' 64 (mword_of_int 0x576 : mword 12))).
    { rewrite /D4 upd_ne; [| vm_compute; discriminate]. rewrite /D3 upd_ne; [| vm_compute; discriminate].
      rewrite /D2 upd_eq /D1 upd_eq. reflexivity. }
    assert (Hpc52 : add_vec_int (mword_of_int (KernelSyms.sched + 0x50) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc52) in "Hpc".
    (* +0x52 c.add a5,a5,s2 *)
    iPoseProof (sdi_52 with "Htext") as "Hi52".
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.sched + 0x52)) (mword_of_int 15 : mword 5) (mword_of_int 18 : mword 5)
              D4 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi52").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (D5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (D4 !!! Regidx (mword_of_int 15 : mword 5)) (D4 !!! Regidx (mword_of_int 18 : mword 5)))]> D4).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (D4 !!! Regidx (mword_of_int 15 : mword 5)) (D4 !!! Regidx (mword_of_int 18 : mword 5)))]> D4) with D5.
    assert (Hpc54 : add_vec_int (mword_of_int (KernelSyms.sched + 0x52) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc54) in "Hpc".
    (* +0x54 lw s3,172(a5) : reconcile to a_cpu_int *)
    assert (Hrec_int : add_vec (rget D5 (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 172 : mword 12))
                       = a_cpu_int cid_word).
    { rgne. assert (HD5v : D5 !!! Regidx (mword_of_int 15 : mword 5)
                     = add_vec (mycpu_a5 cid_word)
                         (add_vec (add_vec (mword_of_int (KernelSyms.sched + 0x46) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))
                                  (sign_extend' 64 (mword_of_int 0x576 : mword 12)))).
      { rewrite /D5 upd_eq HshD HD4s2. reflexivity. }
      rewrite HD5v. unfold a_cpu_int, mycpu_ret.
      rewrite (add_vec64_comm _ (mycpu_a5 cid_word)).
      apply sched_reconcile. vm_compute. reflexivity. }
    iPoseProof (sdi_54 with "Htext") as "Hi54".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.sched + 0x54)) (mword_of_int 19 : mword 5) (mword_of_int 15 : mword 5)
              (mword_of_int 172 : mword 12) D5 (av - 6)%nat iv false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi54 [Hint]").
    { iEval (rewrite Hrec_int). iExact "Hint". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hint".
    iEval (rewrite Hrec_int) in "Hint".
    set (D6 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (sign_extend' 64 (iv : mword 32))]> D5).
    change (<[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (sign_extend' 64 (iv : mword 32))]> D5) with D6.
    assert (Hpc58 : add_vec_int (mword_of_int (KernelSyms.sched + 0x54) : mword 64) 4 = mword_of_int (KernelSyms.sched + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc58) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x58..+0x6a: build a1 = &c->context, a0 = &p->context.            *)
    (* ------------------------------------------------------------------ *)
    (* +0x58 c.mv a5,tp *)
    iPoseProof (sdi_58 with "Htext") as "Hi58".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sched + 0x58)) (mword_of_int 15 : mword 5) (mword_of_int 4 : mword 5)
              D6 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi58").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (D7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (rget D6 (mword_of_int 4 : mword 5)))]> D6).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (rget D6 (mword_of_int 4 : mword 5)))]> D6) with D7.
    assert (Hpc5a : add_vec_int (mword_of_int (KernelSyms.sched + 0x58) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc5a) in "Hpc".
    (* +0x5a sext.w a5 *)
    iPoseProof (sdi_5a with "Htext") as "Hi5a".
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.sched + 0x5a)) (mword_of_int 15 : mword 5) (mword_of_int 0 : mword 6)
              D7 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5a").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (D8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec (add_vec (D7 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> D7).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec (add_vec (D7 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> D7) with D8.
    assert (Hpc5c : add_vec_int (mword_of_int (KernelSyms.sched + 0x5a) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc5c) in "Hpc".
    (* +0x5c c.slli a5,7 *)
    iPoseProof (sdi_5c with "Htext") as "Hi5c".
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.sched + 0x5c)) (Regidx (mword_of_int 15)) (mword_of_int 15 : mword 5) (mword_of_int 7 : mword 6)
              D8 (av - 6)%nat false eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5c").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (D9 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_left (D8 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 7 : mword 6) (Z.sub log2_xlen 1) 0))]> D8).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_left (D8 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 7 : mword 6) (Z.sub log2_xlen 1) 0))]> D8) with D9.
    assert (HshD2 : D9 !!! Regidx (mword_of_int 15 : mword 5) = mycpu_a5 cid_word).
    { rewrite /D9 upd_eq /D8 upd_eq /D7 upd_eq (rget_tp D6). reflexivity. }
    assert (Hpc5e : add_vec_int (mword_of_int (KernelSyms.sched + 0x5c) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc5e) in "Hpc".
    (* +0x5e c.addi a5,a5,8 *)
    iPoseProof (sdi_5e with "Htext") as "Hi5e".
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.sched + 0x5e)) (mword_of_int 15 : mword 5) (mword_of_int 8 : mword 6)
              D9 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5e").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (D10 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (add_vec (D9 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6))))]> D9).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (add_vec (D9 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6))))]> D9) with D10.
    assert (HD10a5 : D10 !!! Regidx (mword_of_int 15 : mword 5)
                     = add_vec (mycpu_a5 cid_word) (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6))))
      by (rewrite /D10 upd_eq HshD2; reflexivity).
    assert (Hpc60 : add_vec_int (mword_of_int (KernelSyms.sched + 0x5e) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc60) in "Hpc".
    (* +0x60 auipc a1,0x10 *)
    iPoseProof (sdi_60 with "Htext") as "Hi60".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.sched + 0x60)) (mword_of_int 11 : mword 5) (mword_of_int 0x10 : mword 20)
              D10 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi60").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (D11 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.sched + 0x60) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))]> D10).
    change (<[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.sched + 0x60) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20)))]> D10) with D11.
    assert (Hpc64 : add_vec_int (mword_of_int (KernelSyms.sched + 0x60) : mword 64) 4 = mword_of_int (KernelSyms.sched + 0x64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc64) in "Hpc".
    (* +0x64 addi a1,a1,1274 *)
    iPoseProof (sdi_64 with "Htext") as "Hi64".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sched + 0x64)) (mword_of_int 11 : mword 5) (mword_of_int 11 : mword 5) (mword_of_int 0x58c : mword 12)
              D11 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi64").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (D12 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (D11 !!! Regidx (mword_of_int 11 : mword 5)) (sign_extend' 64 (mword_of_int 1420 : mword 12)))]> D11).
    change (<[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (D11 !!! Regidx (mword_of_int 11 : mword 5)) (sign_extend' 64 (mword_of_int 1420 : mword 12)))]> D11) with D12.
    assert (HD12a1 : D12 !!! Regidx (mword_of_int 11 : mword 5)
                     = add_vec (add_vec (mword_of_int (KernelSyms.sched + 0x60) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20))) (sign_extend' 64 (mword_of_int 0x58c : mword 12)))
      by (rewrite /D12 upd_eq /D11 upd_eq; reflexivity).
    assert (HD12a5 : D12 !!! Regidx (mword_of_int 15 : mword 5)
                     = add_vec (mycpu_a5 cid_word) (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6)))).
    { rewrite /D12 upd_ne; [| vm_compute; discriminate]. rewrite /D11 upd_ne; [| vm_compute; discriminate]. exact HD10a5. }
    assert (Hpc68 : add_vec_int (mword_of_int (KernelSyms.sched + 0x64) : mword 64) 4 = mword_of_int (KernelSyms.sched + 0x68)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc68) in "Hpc".
    (* +0x68 c.add a1,a1,a5 *)
    iPoseProof (sdi_68 with "Htext") as "Hi68".
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.sched + 0x68)) (mword_of_int 11 : mword 5) (mword_of_int 15 : mword 5)
              D12 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi68").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (D13 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (D12 !!! Regidx (mword_of_int 11 : mword 5)) (D12 !!! Regidx (mword_of_int 15 : mword 5)))]> D12).
    change (<[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (D12 !!! Regidx (mword_of_int 11 : mword 5)) (D12 !!! Regidx (mword_of_int 15 : mword 5)))]> D12) with D13.
    assert (Hpc6a : add_vec_int (mword_of_int (KernelSyms.sched + 0x68) : mword 64) 2 = mword_of_int (KernelSyms.sched + 0x6a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc6a) in "Hpc".
    (* s1 threaded to D13 *)
    assert (HD13_x9 : D13 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j)).
    { rewrite /D13 upd_ne; [| vm_compute; discriminate]. rewrite /D12 upd_ne; [| vm_compute; discriminate].
      rewrite /D11 upd_ne; [| vm_compute; discriminate]. rewrite /D10 upd_ne; [| vm_compute; discriminate].
      rewrite /D9 upd_ne; [| vm_compute; discriminate]. rewrite /D8 upd_ne; [| vm_compute; discriminate].
      rewrite /D7 upd_ne; [| vm_compute; discriminate]. rewrite /D6 upd_ne; [| vm_compute; discriminate].
      rewrite /D5 upd_ne; [| vm_compute; discriminate]. rewrite /D4 upd_ne; [| vm_compute; discriminate].
      rewrite /D3 upd_ne; [| vm_compute; discriminate]. rewrite /D2 upd_ne; [| vm_compute; discriminate].
      rewrite /D1 upd_ne; [| vm_compute; discriminate]. rewrite /D0 upd_ne; [| vm_compute; discriminate].
      exact HC11_x9. }
    (* +0x6a addi a0,s1,96 *)
    iPoseProof (sdi_6a with "Htext") as "Hi6a".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sched + 0x6a)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 0x60 : mword 12)
              D13 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6a").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (D14 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (D13 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 0x60 : mword 12)))]> D13).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (D13 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 0x60 : mword 12)))]> D13) with D14.
    assert (Hpc6e : add_vec_int (mword_of_int (KernelSyms.sched + 0x6a) : mword 64) 4 = mword_of_int (KernelSyms.sched + 0x6e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc6e) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x6e: jal swtch, then the swtch(&p->context, &c->context) call.    *)
    (* ------------------------------------------------------------------ *)
    iPoseProof (sdi_6e with "Htext") as "Hi6e".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sched + 0x6e)) (mword_of_int 1 : mword 5) (mword_of_int 1346 : mword 21)
              D14 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi6e").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (Mc := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sched + 0x6e) : mword 64) 4)]> D14).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sched + 0x6e) : mword 64) 4)]> D14) with Mc.
    assert (Hpcsw : add_vec (mword_of_int (KernelSyms.sched + 0x6e) : mword 64) (sign_extend' 64 (mword_of_int 1346 : mword 21))
                    = mword_of_int KernelSyms.swtch) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcsw) in "Hpc".
    (* call-site register facts. *)
    assert (Hra_Mc : Mc !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.sched + 0x6e) : mword 64) 4)
      by (rewrite /Mc upd_eq; reflexivity).
    assert (Holdc : Mc !!! Regidx (mword_of_int 10 : mword 5) = p_context (proc_addr j)).
    { rewrite /Mc upd_ne; [| vm_compute; discriminate]. rewrite /D14 upd_eq HD13_x9 add_vec_zero_l.
      unfold p_context, context_off.
      assert (H96 : sign_extend' 64 (mword_of_int 96 : mword 12) = (mword_of_int 96 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite H96. reflexivity. }
    assert (Hnewc : Mc !!! Regidx (mword_of_int 11 : mword 5) = a_cpu_ctx cid_word).
    { rewrite /Mc upd_ne; [| vm_compute; discriminate]. rewrite /D14 upd_ne; [| vm_compute; discriminate].
      rewrite /D13 upd_eq HD12a1 HD12a5. unfold a_cpu_ctx, mycpu_ret.
      apply sched_reconcile2. vm_compute. reflexivity. }
    (* FULL-BUNDLE swtch: hand [sie_cap_gpr] and [cpu_own] whole (the swtch
       proof internally carves the stack/off-eighth and parks them in the OLD
       record).  Refold the check-chain cells into the level-1 [cpu_own]. *)
    iAssert (cpu_own 1 eb pj false {["proc"]}) with "[Hnoff Hint Hlks Hcnt Hcur]" as "Hcpu".
    { rewrite cpu_own_off /cpu_hart /cpu_priv /cpu_cells.
      iFrame "Hnoff Hint Hcnt Hcur Hlks". iPureIntro; vm_compute; reflexivity. }
    (* ------------------------------------------------------------------ *)
    (* THE CROSSING'S [back] IS THE PARKED STATE'S OWN [needs_ctx], and the *)
    (* two parks are genuinely different from here on.                      *)
    (* ------------------------------------------------------------------ *)
    assert (Hcsp_Mc : Mc !!! Regidx csp_rs1 = spd).
    { rewrite /Mc upd_ne; [| vm_compute; discriminate].
      rewrite /D14 upd_ne; [| vm_compute; discriminate]. rewrite /D13 upd_ne; [| vm_compute; discriminate].
      rewrite /D12 upd_ne; [| vm_compute; discriminate]. rewrite /D11 upd_ne; [| vm_compute; discriminate].
      rewrite /D10 upd_ne; [| vm_compute; discriminate]. rewrite /D9 upd_ne; [| vm_compute; discriminate].
      rewrite /D8 upd_ne; [| vm_compute; discriminate]. rewrite /D7 upd_ne; [| vm_compute; discriminate].
      rewrite /D6 upd_ne; [| vm_compute; discriminate]. rewrite /D5 upd_ne; [| vm_compute; discriminate].
      rewrite /D4 upd_ne; [| vm_compute; discriminate]. rewrite /D3 upd_ne; [| vm_compute; discriminate].
      rewrite /D2 upd_ne; [| vm_compute; discriminate]. rewrite /D1 upd_ne; [| vm_compute; discriminate].
      rewrite /D0 upd_ne; [| vm_compute; discriminate].
      rewrite /C11 upd_ne; [| vm_compute; discriminate]. rewrite /C10 upd_ne; [| vm_compute; discriminate].
      rewrite /C9 upd_ne; [| vm_compute; discriminate]. rewrite /C8 upd_ne; [| vm_compute; discriminate].
      rewrite /C7 upd_ne; [| vm_compute; discriminate]. rewrite /C6 upd_ne; [| vm_compute; discriminate].
      rewrite /C5 upd_ne; [| vm_compute; discriminate]. rewrite /C4 upd_ne; [| vm_compute; discriminate].
      rewrite /C3 upd_ne; [| vm_compute; discriminate]. rewrite /C2 upd_ne; [| vm_compute; discriminate].
      rewrite /C1 upd_ne; [| vm_compute; discriminate]. rewrite /C0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_mh csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /B1 upd_ne; [| vm_compute; discriminate]. rewrite /B0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_mp csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /A2 upd_ne; [| vm_compute; discriminate]. rewrite /A1 upd_ne; [| vm_compute; discriminate].
      exact HcspA0. }
    destruct (needs_ctx st) eqn:Hnc; last first.
    { (* ---- THE PARK THAT NEVER RETURNS (kexit's).  No record is left, so
           no continuation is owed -- and sched's own frame and unused tail
           are dead the instant the swtch happens.  Both go to the payload,
           which is what lets the dying thread leave its slot a WHOLE free
           kernel stack (ProcDefs.kstack_free) instead of a page with a hole
           where this frame used to be. ---- *)
      iAssert (stack_own sp0 6) with "[Hr1 Hr2 Hr3 Hr4 Hr5 Hgap]" as "Hframe6".
      { rewrite stack_own_slots. cbn [seq].
        iSplitL "Hr1". { iExists _. iEval (rewrite Hb1 -HcspA0). iExact "Hr1". }
        iSplitL "Hr2". { iExists _. iEval (rewrite Hb2 -HcspA0). iExact "Hr2". }
        iSplitL "Hr3". { iExists _. iEval (rewrite Hb3 -HcspA0). iExact "Hr3". }
        iSplitL "Hr4". { iExists _. iEval (rewrite Hb4 -HcspA0). iExact "Hr4". }
        iSplitL "Hr5". { iExists _. iEval (rewrite Hb5 -HcspA0). iExact "Hr5". }
        iSplitL "Hgap". { iExists _. iExact "Hgap". }
        done. }
      (* take the free tail out of the bundle: swtch touches no stack, so it
         runs at avail 0 and the tail crosses in the payload instead. *)
      iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
      iEval (rewrite /sie_cap) in "Hcap".
      iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
      iEval (rewrite Hcsp_Mc) in "Hstk".
      iAssert (sie_cap Mc 0%nat false pj) with "[Htr Harm]" as "Hcap0".
      { rewrite /sie_cap. iSplitR "Htr Harm".
        { rewrite Hcsp_Mc. by iApply stack_own_0. }
        iFrame "Htr Harm Hwit". }
      iDestruct (sie_cap_gpr_join Mc 0%nat false pj with "Hhs Hsc Hcap0 Hfile") as "Hcg0".
      (* frame ++ tail = the whole region sched was called with *)
      assert (Hgeom6 : pa_stk sp0 6 = spd).
      { rewrite /spd -Hpush. reflexivity. }
      assert (Havsplit : av = (6 + (av - 6))%nat) by lia.
      iAssert (stack_own sp0 av) with "[Hframe6 Hstk]" as "Hfull".
      { iEval (rewrite {1}Havsplit (stack_own_app sp0 6 (av - 6))).
        iSplitL "Hframe6"; [iExact "Hframe6" |].
        iEval (rewrite Hgeom6). iExact "Hstk". }
      iPoseProof ("Hpay" with "Hfull") as "Hpp".
      iPoseProof (p_sched_to_cpu γs cpu_id j γl st ch Hj Hgl Hneeds
                    with "Htc [Hlocked Hstate Hchan Hpub] Htag Hpp") as "HP".
      { rewrite /proc_held. iFrame "Hlocked Hstate Hchan Hpub". }
      iEval (rewrite Hnc) in "HP".
      iApply (Swtch.wp_swtch_sconf (p_sched γs) (Some cpu_id) None
                (p_context (proc_addr j)) (a_cpu_ctx cid_word)
                Mc ctxvs 0%nat eb pj false
                Hctxlen Holdc Hnewc (adm_pin cpu_id)
                with "Htext Hcg0 Hcpu Hpc Hctxcells Hvc [HP] []").
      { iEval (rewrite (rget_tp Mc)). iExact "HP". }
      done. }
    (* ---- A RESUMABLE PARK: the caller comes back, so its continuation is
           its record.  [park_pay] is [emp] here, so the closer's argument is
           not needed and the payload is free. ---- *)
    iAssert (park_pay (proc_addr j) st) as "Hpp".
    { iApply (park_pay_needs_ctx (proc_addr j) st Hnc). }
    (* build the parking-proc payload (proc-held facts only; the cpu bundle
       now crosses at the swtch's [cpu_own] interface, not in the payload). *)
    iPoseProof (p_sched_to_cpu γs cpu_id j γl st ch Hj Hgl Hneeds
                  with "Htc [Hlocked Hstate Hchan Hpub] Htag Hpp") as "HP".
    { rewrite /proc_held. iFrame "Hlocked Hstate Hchan Hpub". }
    iEval (rewrite Hnc) in "HP".
    (* apply swtch.  The TARGET record is PINNED at this hart
       (cpus[cid].context is only ever resumed from hart cid's own tp); the
       record sched deposits for ITSELF is a PROC context, hence MIGRATABLE
       ([Ao = None]) -- which is what makes the whole post-resume half below
       ∀-hart, and what lets [procs_inv] be hart-free. *)
    iApply (Swtch.wp_swtch_sconf (p_sched γs) (Some cpu_id) None
              (p_context (proc_addr j)) (a_cpu_ctx cid_word)
              Mc ctxvs (av - 6)%nat eb pj true
              Hctxlen Holdc Hnewc (adm_pin cpu_id)
              with "Htext Hcg Hcpu Hpc Hctxcells Hvc [HP]").
    { iEval (rewrite (rget_tp Mc)). iExact "HP". }
    (* THE SEAM IS CLOSED BY THE CONTRACT, not by a ghost fact: [SpecSwtch]
       pins the held set at [{["proc"]}] on BOTH sides, because
       swtch is reachable only while holding exactly this proc's lock (sched's
       own [noff != 1] check is the C-level statement of it).  The resumption
       therefore arrives at the same singleton rather than at a freshly
       quantified set nothing could tie back. *)
    iIntros (h m' eb') "%Hadm' %Hcallee Hcg Hcpu Hpc Hctxback Hresume".
    (* [Ao = None] -- the resumption's hart is NOT pinned; [Hadm'] is vacuous
       and everything from here on is at an arbitrary [h]. *)
    clear Hadm'.
    (* resume: elim the SECOND disjunct (dispatched proc).  It delivers the
       lock at hart [h] and hart [h]'s trap CSRs ([intr_res] among them). *)
    iDestruct "Hresume" as (A' cret backr) "[Hvc' Hpayr]".
    iDestruct (p_sched_at_proc γs h A' j cret (rget (CID := h) m' (mword_of_int 4 : mword 5)) pj backr Hj with "Hpayr")
      as "(%Htpv & %Hcret & %Hpidx & %HA' & %Hbackr & Htc' & Hpay2)".
    subst A'. subst backr.
    iDestruct "Hpay2" as (γl' ch') "(%Hgl' & Hheld' & Htag')".
    assert (γl' = γl) as -> by (rewrite Hgl in Hgl'; injection Hgl'; auto).
    iEval (rewrite Hcret) in "Hvc'".
    (* callee-image component equalities. *)
    unfold callee_img, ctx_regs in Hcallee. simpl in Hcallee.
    injection Hcallee as Hm1 Hm2 Hm8 Hm9 Hm18 Hm19 Hm20 Hm21 Hm22 Hm23 Hm24 Hm25 Hm26 Hm27.
    (* ------------------------------------------------------------------ *)
    (* Everything the post-resume half needs about the returned file [m'], *)
    (* read off this tower ONCE.  From here the proof is hart-generic and   *)
    (* runs inside [sched_post_swtch] at [(CID := h)].                      *)
    (* ------------------------------------------------------------------ *)
    (* sp threads unchanged from the prologue push all the way through. *)
    assert (Hsp_m' : m' !!! Regidx csp_rs1 = spd).
    { change (Regidx csp_rs1) with (Regidx (mword_of_int 2 : mword 5)).
      rewrite Hm2. change (Regidx (mword_of_int 2 : mword 5)) with (Regidx csp_rs1). exact Hcsp_Mc. }
    (* pc lands on the saved return address KernelSyms.sched+0x72. *)
    assert (Hpctgt : ret_pc (m' !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.sched + 0x72))
      by (rewrite Hm1 Hra_Mc; vm_compute; reflexivity).
    iEval (rewrite Hpctgt) in "Hpc".
    (* s2 = &cpus[0], as the +0x46 auipc/addi pair computed it. *)
    assert (HMc_x18 : Mc !!! Regidx (mword_of_int 18 : mword 5)
                      = add_vec (add_vec (mword_of_int (KernelSyms.sched + 0x46) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20))) (sign_extend' 64 (mword_of_int 0x576 : mword 12))).
    { rewrite /Mc upd_ne; [| vm_compute; discriminate]. rewrite /D14 upd_ne; [| vm_compute; discriminate].
      rewrite /D13 upd_ne; [| vm_compute; discriminate]. rewrite /D12 upd_ne; [| vm_compute; discriminate].
      rewrite /D11 upd_ne; [| vm_compute; discriminate]. rewrite /D10 upd_ne; [| vm_compute; discriminate].
      rewrite /D9 upd_ne; [| vm_compute; discriminate]. rewrite /D8 upd_ne; [| vm_compute; discriminate].
      rewrite /D7 upd_ne; [| vm_compute; discriminate]. rewrite /D6 upd_ne; [| vm_compute; discriminate].
      rewrite /D5 upd_ne; [| vm_compute; discriminate]. exact HD4s2. }
    assert (Hs2addr : m' !!! Regidx (mword_of_int 18 : mword 5)
                      = add_vec (add_vec (mword_of_int (KernelSyms.sched + 0x46) : mword 64) (auipc_off (mword_of_int 0x10 : mword 20))) (sign_extend' 64 (mword_of_int 0x576 : mword 12)))
      by (rewrite Hm18; exact HMc_x18).
    (* s3 = the saved base-enable word read at +0x54. *)
    assert (HMc_x19 : Mc !!! Regidx (mword_of_int 19 : mword 5) = sign_extend' 64 (intena_val eb)).
    { rewrite /Mc upd_ne; [| vm_compute; discriminate].
      rewrite /D14 upd_ne; [| vm_compute; discriminate].
      rewrite /D13 upd_ne; [| vm_compute; discriminate].
      rewrite /D12 upd_ne; [| vm_compute; discriminate].
      rewrite /D11 upd_ne; [| vm_compute; discriminate].
      rewrite /D10 upd_ne; [| vm_compute; discriminate].
      rewrite /D9 upd_ne; [| vm_compute; discriminate].
      rewrite /D8 upd_ne; [| vm_compute; discriminate].
      rewrite /D7 upd_ne; [| vm_compute; discriminate].
      rewrite /D6 upd_eq. reflexivity. }
    assert (Hs3v : m' !!! Regidx (mword_of_int 19 : mword 5) = sign_extend' 64 (intena_val eb))
      by (rewrite Hm19; exact HMc_x19).
    (* the registers sched never touches, threaded Mc -> m ... *)
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
      Regidx c ≠ Regidx (mword_of_int 1) -> Regidx c ≠ Regidx (mword_of_int 8) ->
      Regidx c ≠ Regidx (mword_of_int 9) -> Regidx c ≠ Regidx (mword_of_int 10) ->
      Regidx c ≠ Regidx (mword_of_int 11) -> Regidx c ≠ Regidx (mword_of_int 14) ->
      Regidx c ≠ Regidx (mword_of_int 15) -> Regidx c ≠ Regidx (mword_of_int 18) ->
      Regidx c ≠ Regidx (mword_of_int 19) -> Regidx c ≠ Regidx csp_rs1 ->
      Mc !!! Regidx c = m !!! Regidx c).
    { intros c Hcs H1 H8 H9 H10 H11 H14 H15 H18 H19 Hsp.
      rewrite /Mc upd_ne; [| exact H1].
      rewrite /D14 upd_ne; [| exact H10]. rewrite /D13 upd_ne; [| exact H11].
      rewrite /D12 upd_ne; [| exact H11]. rewrite /D11 upd_ne; [| exact H11].
      rewrite /D10 upd_ne; [| exact H15]. rewrite /D9 upd_ne; [| exact H15].
      rewrite /D8 upd_ne; [| exact H15]. rewrite /D7 upd_ne; [| exact H15].
      rewrite /D6 upd_ne; [| exact H19]. rewrite /D5 upd_ne; [| exact H15].
      rewrite /D4 upd_ne; [| exact H15]. rewrite /D3 upd_ne; [| exact H15].
      rewrite /D2 upd_ne; [| exact H18]. rewrite /D1 upd_ne; [| exact H18].
      rewrite /D0 upd_ne; [| exact H15].
      rewrite /C11 upd_ne; [| exact H15]. rewrite /C10 upd_ne; [| exact H15].
      rewrite /C9 upd_ne; [| exact H15]. rewrite /C8 upd_ne; [| exact H14].
      rewrite /C7 upd_ne; [| exact H15]. rewrite /C6 upd_ne; [| exact H14].
      rewrite /C5 upd_ne; [| exact H15]. rewrite /C4 upd_ne; [| exact H14].
      rewrite /C3 upd_ne; [| exact H14]. rewrite /C2 upd_ne; [| exact H15].
      rewrite /C1 upd_ne; [| exact H15]. rewrite /C0 upd_ne; [| exact H15].
      rewrite (callee_saved_lookup Hcs_mh c Hcs).
      rewrite /B1 upd_ne; [| exact H1]. rewrite /B0 upd_ne; [| exact H9].
      rewrite (callee_saved_lookup Hcs_mp c Hcs).
      rewrite /A2 upd_ne; [| exact H1]. rewrite /A1 upd_ne; [| exact H8].
      rewrite /A0 upd_ne; [| exact Hsp]. reflexivity. }
    (* ... and hence m' -> m for s4..s11. *)
    assert (Hf20 : m' !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5))
      by (rewrite Hm20; apply Hthread; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    assert (Hf21 : m' !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5))
      by (rewrite Hm21; apply Hthread; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    assert (Hf22 : m' !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5))
      by (rewrite Hm22; apply Hthread; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    assert (Hf23 : m' !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5))
      by (rewrite Hm23; apply Hthread; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    assert (Hf24 : m' !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5))
      by (rewrite Hm24; apply Hthread; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    assert (Hf25 : m' !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5))
      by (rewrite Hm25; apply Hthread; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    assert (Hf26 : m' !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5))
      by (rewrite Hm26; apply Hthread; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    assert (Hf27 : m' !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5))
      by (rewrite Hm27; apply Hthread; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    (* the saved frame cells, re-addressed at [pa_stk sp0 k]. *)
    assert (HA0ra : A0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HA0s0 : A0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HA0s1 : A0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HA0s2 : A0 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HA0s3 : A0 !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HcspA0 HA0ra -Hb1) in "Hr1".
    iEval (rewrite HcspA0 HA0s0 -Hb2) in "Hr2".
    iEval (rewrite HcspA0 HA0s1 -Hb3) in "Hr3".
    iEval (rewrite HcspA0 HA0s2 -Hb4) in "Hr4".
    iEval (rewrite HcspA0 HA0s3 -Hb5) in "Hr5".
    (* THE CROSSING INDEX IS THE LITERAL [true] -- a park moves the hart with
       interrupts OFF -- so the continuation's pinning condition reduces to
       [pj = zero_reg], which a real process address refutes.  Strip the
       wrapper here, at the hart the dispatch actually resumed on. *)
    iSpecialize ("Hcont" $! h with "[%]").
    { intros [Hf | Hz]; [ discriminate
                        | exfalso; exact (sched_pj_nonzero j Hj Hz) ]. }
    (* ONE application of the post-resume half, at the resuming hart. *)
    iApply (sched_post_swtch (CID := h)  γs j γl ch' m m' av eb eb' sp0 spd vgap
              ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)
              Hsp_m' Hs2addr Hs3v Hf20 Hf21 Hf22 Hf23 Hf24 Hf25 Hf26 Hf27
              with "Htext Hcg Hcpu Hpc Hr1 Hr2 Hr3 Hr4 Hr5 Hgap Hheld' Htc' [Hctxback] Htag' Hvc' Hcont").
    { rewrite /own_ctx. iExists (callee_img Mc). iSplit.
      { iPureIntro. unfold callee_img, ctx_regs. reflexivity. }
      iExact "Hctxback". }
  Qed.

  (* ===================================================================== *)
  (*  THERE IS NO SECOND WALK.                                             *)
  (* ===================================================================== *)
  (* [wp_sched_locks] used to walk sched+0x00 .. +0x30 again at noff >= 2 and
     TAKE the [bne] into panic("sched locks").  Its only client was
     [SpecSleep]'s nested lemma, which is gone; see SpecSched.v's header for
     why, and note that deleting it is what turns "we permit this panic" into
     "no proof can reach it".  The single walk that remains, above, refutes
     the branch at noff = 1 and never mentions the panic credentials. *)

End ProofSched.

End SchedProof.
