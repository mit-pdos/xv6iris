(* ProofSleep.v -- the whole-function sconf-tier proof of sleep()
   (SpecSleep.v), as a sealed functor over its callees' interfaces
   (myproc, acquire, sched, release).  See claude-notes/projects/yield-sched.md.

   sleep(chan, lk) @ 0x80001f06: the 48-byte frame prologue (byte-identical to
   sched's) saving ra/s0/s1/s2/s3 / s3 = chan / s2 = lk / p = myproc() /
   acquire(&p->lock) / release(lk) / p->chan = chan (8-byte sd) /
   p->state = SLEEPING (c.sw) / sched() / p->chan = 0 (8-byte sd of x0) /
   release(&p->lock) / acquire(lk) / epilogue.  The proof threads the
   scheduler-swtch protocol resources exactly as yield does (acquire proc j's
   lock, hand sched the parking-proc payload at SLEEPING, release with the
   process RUNNING), wrapped in the caller condition lock's release/reacquire
   (noff 1 -> 2 -> 1 around sched, then 1 -> 0 -> 1 around the proc lock).

   TWO INDICES, AND THEY ARE OPPOSITE CONSTANTS (SpecSleep.v): sleep runs at
   noff = 1, so [cpu_own 1 eb pj C b] pins its RESOURCE index at the literal
   [false] -- every leaf before the park, and every leaf between acquire's
   return and release's call, is therefore a plain [rewrite wp_next_off].  Its
   CROSSING index is the literal [true]: a [swtch] moves the hart with
   interrupts OFF.  The only hart-GENERIC stretch is the one sleep's
   push/pop imbalance opens up: the interior pop of p->lock reaches level 0
   with [eb = true], so from that release's exit to the re-acquire's return
   the hart may move, and those leaves take [iIntros (CIDk Hsk)].

   THE SCHEDULER RECORD IS GLOBAL NOW (SchedCtx.scheds_inv): sleep no longer
   carries [▷ sched_vc] -- fourteen exclusive words of ONE hart's struct cpu,
   for which no [wp_next] transport exists -- but the persistent [scheds_inv]
   plus the hart-free per-PROC receipt [park_hlf j true].  Its two moves are
   [scheds_take] just before the [jal sched] (which turns the receipt into the
   [park_hlf j false] that [proc_held] now demands, and produces the
   [▷ sched_vc] sched's own contract still wants) and [scheds_put] at the
   RESUMED hart, which deposits the record back and returns the receipt.

   The CONDITION lock is taken generically ([lock_openable] plus a credential
   [Tk] -- ACQUIRE_GEN / RELEASE_GEN), so a process may sleep on a reclaimable
   object's lock: [Tk] rides the sleeper's frame through sched(), which is what
   keeps the object alive under it.  p->lock stays a static [is_lock], so its
   two call sites want the plain ACQUIRE / RELEASE forms.  Those come in as
   EXTRA FUNCTOR PARAMETERS rather than from [AcquireOfGen] / [ReleaseOfGen]:
   a whole-function proof file must never [Require] another one (see
   claude-notes/design/spec-modules.md -- the module shape exists precisely so
   a function's proof depends on its callees' SPECS only, and every function
   proof can be checked in parallel).  Deriving the plain forms in here would
   have added a ProofSleep -> ProofAcquire/ProofRelease edge; the caller
   (LinkSleep.v) passes both flavours instead, exactly as ProofPipeclose.v
   takes ACQUIRE_GEN and RELEASE_CANCEL side by side.

   [SleepOfGen] at the bottom restates the [Tk := emp], [Dk := False] instance
   for the ordinary [SLEEP] consumers. *)
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
Require Import InstrBytes KernelText IntrDefs SpecPanic.
Require Import HartTp WpNext.
Require Import WpSmodeIntr.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
(* for [wp_next_shift]: the ONE re-anchoring of the caller's ["Hcont"] from
   the parking hart to the dispatching one.  Do NOT hand-roll a local twin --
   that bridge belongs to the file that owns [wp_next]'s block engine. *)
Require Import WpSconfVc.
Require Import WpLock.
Require Import FdSlots.
Require Import ProcGeom.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import CodeSleep.
Require Import SpecMyproc SpecAcquire SpecSched SpecRelease SpecSleep.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import KernelRvcDecode.
Import Defs.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* Pure helpers: address arithmetic + the noff-cell value forms.          *)
(* ===================================================================== *)




(* a saved-register frame slot address in terms of the pushed sp (local copy
   of ProofSched.sched_frame_bridge, which lives in a proof file). *)
Lemma sl_frame_bridge (sp0 : mword 64) (j : nat) (uimm : mword 6) :
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
  unfold pa_stk, add_vec_int. rewrite po_addv_assoc. rewrite Heq. reflexivity.
Qed.


(* acquire's noff output (push_off's +1 store) over the entry value 1 is
   exactly [mword_of_int 2] (noff around the caller condition lock). *)
Lemma sl_acq_noff_two :
  (autocast (T := mword) (subrange_vec_dec
     (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 (mword_of_int 1 : mword 32))
        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))
     (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = (mword_of_int 2 : mword 32).
Proof. vm_compute. reflexivity. Qed.

(* acquire's noff output over the entry value 0 is [mword_of_int 1] (the
   final reacquire of the condition lock). *)
Lemma sl_acq_noff_one :
  (autocast (T := mword) (subrange_vec_dec
     (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 (mword_of_int 0 : mword 32))
        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))
     (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = (mword_of_int 1 : mword 32).
Proof. vm_compute. reflexivity. Qed.

(* release's noff output (pop_off's -1 store) over the entry value 2 is
   [mword_of_int 1] (release of the condition lock, before sched). *)
Lemma sl_rel_noff_one :
  (autocast (T := mword) (subrange_vec_dec
     (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 (mword_of_int 2 : mword 32))
        (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))
     (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = (mword_of_int 1 : mword 32).
Proof. vm_compute. reflexivity. Qed.

(* release's noff output over the entry value 1 is [mword_of_int 0] (release
   of the proc lock, after sched). *)
Lemma sl_rel_noff_zero :
  (autocast (T := mword) (subrange_vec_dec
     (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 (mword_of_int 1 : mword 32))
        (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))
     (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = (mword_of_int 0 : mword 32).
Proof. vm_compute. reflexivity. Qed.

(* the c.li a5,2 value truncated to 32 bits is SLEEPING = mword_of_int 2. *)
Lemma sl_sleeping :
  trunc32 (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))) : mword 64)
  = (mword_of_int 2 : mword 32).
Proof. vm_compute. reflexivity. Qed.

(* p->lock is a STATIC kernel lock, so its two call sites take the plain
   [Acquire] / [Release]; only the caller's CONDITION lock lk goes through
   [AcquireGen] / [ReleaseGen].  Both flavours are parameters -- see the
   header note on why they are not derived in here. *)
Module SleepGenProof (Myproc : MYPROC) (Acquire : ACQUIRE) (AcquireGen : ACQUIRE_GEN)
                     (Sched : SCHED) (Release : RELEASE) (ReleaseGen : RELEASE_GEN) : SLEEP_GEN.
(* ===================================================================== *)
(* THE POST-RESUME HALF, AS ITS OWN LEMMA.                                *)
(*                                                                        *)
(* sched() does not return on the hart it parked from (SpecSched.v): proc  *)
(* contexts are migratable, so its continuation is wrapped in [wp_next     *)
(* true pj] and the rebound [CID] IS the dispatching hart.  Everything     *)
(* sleep does after the park -- deposit the scheduler record, clear        *)
(* p->chan, release p->lock, RE-ACQUIRE the condition lock, the epilogue   *)
(* -- therefore runs at an ARBITRARY hart, which a Section-fixed [CID]     *)
(* cannot express.  So the whole half is ONE lemma whose [CID0] is a       *)
(* binder, and whose own continuation is a [wp_next true pj] anchored      *)
(* there; the pre-park half re-anchors ["Hcont"] with [wp_next_shift] and  *)
(* applies this once at [(CID0 := the resumed hart)].                      *)
(* Note [panic_wp_any] arrives HERE too: it is the re-acquire whose        *)
(* holding-panic arm has to be closed, at whatever hart runs it, which is  *)
(* exactly why acquire's contract takes the hart-generic form.             *)
(* ===================================================================== *)
Section SleepPostSched.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ}.

  Lemma sleep_post_sched `{GEN : GenId} `{CID0 : CpuId}
      (Φ : mval -> iProp Σ) (γs : list gname)
      (j : nat) (γl : gname) (ch' : mword 64)
      (γk : gname) (lka lk0 : mword 64) (Rk Tk Dk : iProp Σ)
      (m msch : regfile) (av : nat) (C : iProp Σ)
      (sp0 spd vgap : mword 64) :
    let pj := proc_addr j in
    (22 <= av)%nat ->
    (j < NPROC)%nat ->
    add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))) = spd ->
    sp0 = m !!! Regidx csp_rs1 ->
    add_vec lk0 (sign_extend' 64 (mword_of_int 0 : mword 12)) = lka ->
    (⊢ Tk -∗ Dk -∗ False) ->
    (forall i : CPU, ⊢ locked_pre γk i -∗ Dk -∗ False) ->
    msch !!! Regidx csp_rs1 = spd ->
    msch !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j) ->
    msch !!! Regidx (mword_of_int 18 : mword 5) = add_vec zero_reg lk0 ->
    (* s4..s11: untouched by sleep and by everything it calls *)
    msch !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5) ->
    msch !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) ->
    msch !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) ->
    msch !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) ->
    msch !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) ->
    msch !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) ->
    msch !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) ->
    msch !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5) ->
    kernel_text -∗
    is_lock γl (proc_addr j) "proc"%string (proc_lock_res Φ γs γl (proc_addr j)) -∗
    scheds_inv Φ γs -∗
    lock_openable γk lka Rk Dk -∗
    panic_wp_any -∗
    sie_cap_gpr msch (av - 6)%nat false pj -∗
    pc_is (mword_of_int (KernelSyms.sleep + 0x2e)) -∗
    proc_held cpu_id j γl RUNNING ch' -∗
    trap_csrs -∗
    cpu_own 1 true pj emp false -∗
    C -∗
    Tk -∗
    own_ctx (p_context pj) -∗
    ▷ sched_vc Φ γs (a_cpu_ctx cid_word) pj -∗
    (* the five saved callee-saved words + the frame's bottom slot *)
    pa_stk sp0 1 ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
    pa_stk sp0 2 ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
    pa_stk sp0 3 ↦₈ (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
    pa_stk sp0 4 ↦₈ (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
    pa_stk sp0 5 ↦₈ (m !!! Regidx (mword_of_int 19 : mword 5)) -∗
    pa_stk sp0 6 ↦₈ vgap -∗
    wp_next true pj (fun (CID : CpuId) =>
      ∀ (mf : regfile),
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr mf av false pj -∗
        cpu_own 1 true pj C false -∗
        trap_csrs_pay 0 true -∗
        pc_is (ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))) -∗
        Tk -∗
        locked γk cpu_id -∗
        Rk -∗
        own_ctx (p_context pj) -∗
        park_hlf j true -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pj Hav Hjn Hspd Hsp0 Hlka0 HrefT HrefLkp Hsp_msch Hs1_msch Hs2_msch
           Hmsch20 Hmsch21 Hmsch22 Hmsch23 Hmsch24 Hmsch25 Hmsch26 Hmsch27.
    iIntros "#Htext #Hislock #Hscheds #Hkopen #Hpanicany Hcg Hpc Hheld' Htc Hcpuemp HC HTk Hown' Hvc'
              Hr1 Hr2 Hr3 Hr4 Hr5 Hgap Hcont".
    (* frame-slot address bridges: slot k sits at [spd + 8*(6-k)]. *)
    assert (Hb1 : pa_stk sp0 1 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))
      by (rewrite -Hspd; apply sl_frame_bridge; vm_compute; reflexivity).
    assert (Hb2 : pa_stk sp0 2 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))
      by (rewrite -Hspd; apply sl_frame_bridge; vm_compute; reflexivity).
    assert (Hb3 : pa_stk sp0 3 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))))
      by (rewrite -Hspd; apply sl_frame_bridge; vm_compute; reflexivity).
    assert (Hb4 : pa_stk sp0 4 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))
      by (rewrite -Hspd; apply sl_frame_bridge; vm_compute; reflexivity).
    assert (Hb5 : pa_stk sp0 5 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))))
      by (rewrite -Hspd; apply sl_frame_bridge; vm_compute; reflexivity).
    iDestruct "Hheld'" as "(Hlocked & Hstate & Hchan & Hpub & Hpark)".
    (* ------------------------------------------------------------------ *)
    (* THE RESUMED THREAD'S FIRST MOVE: deposit hart [CID0]'s scheduler     *)
    (* record back into the global invariant, turning the crossing's        *)
    (* [park_hlf j false] back into the receipt sleep's postcondition owes.  *)
    (* ------------------------------------------------------------------ *)
    iDestruct (cpu_own_set_proc 1 true pj pj emp with "Hcpuemp") as "[Hph Hback]".
    iApply fupd_wp.
    iMod (SchedCtx.scheds_put Φ γs ⊤ (CID0 : CPU) j with "Hscheds Hph Hpark Hvc'") as "[Hph Hpark]";
      [solve_ndisj|exact Hjn|].
    iModIntro.
    iDestruct ("Hback" with "Hph") as "Hcpuemp".
    iAssert (cpu_own 1 true (proc_addr j) C false) with "[Hcpuemp HC]" as "Hcpu".
    { iApply (cpu_own_ctx_swap with "Hcpuemp"). iIntros "_". iExact "HC". }
    (* ------------------------------------------------------------------ *)
    (* +0x2e: sd x0,32(s1) -- p->chan := 0.                                *)
    (* ------------------------------------------------------------------ *)
    assert (Hrec_chan2 : add_vec (msch !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 32 : mword 12))
                         = p_chan (proc_addr j)).
    { rewrite Hs1_msch add_vec_zero_l. unfold p_chan, chan_off.
      assert (H32 : sign_extend' 64 (mword_of_int 32 : mword 12) = (mword_of_int 32 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite H32. reflexivity. }
    assert (Hrec_chan2g : add_vec (rget msch (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 32 : mword 12))
                          = p_chan (proc_addr j)) by (rgne; exact Hrec_chan2).
    iPoseProof (sli_2e with "Htext") as "Hi2e".
    iApply (wp_sd_zero_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x2e)) (mword_of_int 9 : mword 5)
              (mword_of_int 32 : mword 12) msch (av - 6)%nat ch' false
              with "Hcg Hpc Hi2e [Hchan] [-]").
    { iEval (rewrite Hrec_chan2g). iExact "Hchan". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hchan".
    iEval (rewrite Hrec_chan2g) in "Hchan".
    assert (Hpc32 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x2e) : mword 64) 4 = mword_of_int (KernelSyms.sleep + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc32) in "Hpc".
    (* +0x32 c.mv a0,s1 : a0 := proc_addr j *)
    iPoseProof (sli_32 with "Htext") as "Hi32".
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x32)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              msch (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi32 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (E0 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec zero_reg (msch !!! Regidx (mword_of_int 9 : mword 5)))]> msch).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec zero_reg (msch !!! Regidx (mword_of_int 9 : mword 5)))]> msch) with E0.
    assert (Hpc34 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x32) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc34) in "Hpc".
    (* +0x34 jal release *)
    iPoseProof (sli_34 with "Htext") as "Hi34".
    iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x34)) (mword_of_int 1 : mword 5) (mword_of_int 2092364 : mword 21)
              E0 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi34 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x34) : mword 64) 4)]> E0).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x34) : mword 64) 4)]> E0) with E1.
    assert (Hpcrl2 : add_vec (mword_of_int (KernelSyms.sleep + 0x34) : mword 64) (sign_extend' 64 (mword_of_int 2092364 : mword 21))
                    = mword_of_int KernelSyms.release) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcrl2) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x34: release(&p->lock) -- RUNNING (slot emp), n = 0.              *)
    (* THE HART UNPINS HERE: this pop reaches level 0 with eb = true, so    *)
    (* release re-enables SIE at its last instruction and its exit index is *)
    (* [true].  Everything from here to the re-acquire's return is generic. *)
    (* ------------------------------------------------------------------ *)
    assert (Ha0_E1 : E1 !!! Regidx (mword_of_int 10 : mword 5) = proc_addr j).
    { rewrite /E1 upd_ne; [| vm_compute; discriminate]. rewrite /E0 upd_eq Hs1_msch !add_vec_zero_l. reflexivity. }
    assert (HE1ra : E1 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.sleep + 0x34) : mword 64) 4)
      by (rewrite /E1 upd_eq; reflexivity).
    assert (Hlka_r2 : add_vec (E1 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = proc_addr j).
    { rewrite Ha0_E1.
      assert (H0 : sign_extend' 64 (mword_of_int 0 : mword 12) = (mword_of_int 0 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite H0. apply kv_addv_zero. }
    (* rebuild the proc lock resource: RUNNING needs no context, no dormant
       block and no park receipt -- all three slot guards are false. *)
    iAssert (proc_lock_res Φ γs γl (proc_addr j)) with "[Hstate Hchan Hpub]" as "HR2".
    { rewrite /proc_lock_res. iExists RUNNING, (zero_reg : mword 64). iFrame "Hstate Hchan Hpub".
      rewrite /proc_slots needs_ctx_RUNNING inv_dormant_RUNNING not_running_RUNNING.
      iSplitR; [done|]. iSplitR; [done|]. done. }
    iApply (Release.wp_release_sconf Φ γl (proc_addr j) "proc"%string
              (proc_lock_res Φ γs γl (proc_addr j)) E1 0 true (proc_addr j) C (av - 6)%nat
              Hlka_r2
              ltac:(lia)
              with "Hcg Htext Hpc Hislock Hlocked HR2 Hcpu Htc [-]").
    iIntros (CID1 Hs1 mrel2) "Hcg Hpc %Hcs_rel2 Hcpu".
    assert (Hpc38 : ret_pc (E1 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.sleep + 0x38)) by (rewrite HE1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc38) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x38: acquire(lk) -- reacquire the caller condition lock (n = 0).  *)
    (* ------------------------------------------------------------------ *)
    (* thread s2 = lk0 through release/sched/release. *)
    assert (Hs2_mrel2 : mrel2 !!! Regidx (mword_of_int 18 : mword 5) = add_vec zero_reg lk0).
    { rewrite (callee_saved_lookup Hcs_rel2 (mword_of_int 18) ltac:(vm_compute; reflexivity)).
      rewrite /E1 upd_ne; [| vm_compute; discriminate].
      rewrite /E0 upd_ne; [| vm_compute; discriminate]. exact Hs2_msch. }
    (* +0x38 c.mv a0,s2 *)
    iPoseProof (sli_38 with "Htext") as "Hi38".
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x38)) (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 5)
              mrel2 (av - 6)%nat true ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi38 [-]").
    iIntros (CID2 Hs2) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (F0 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec zero_reg (mrel2 !!! Regidx (mword_of_int 18 : mword 5)))]> mrel2).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec zero_reg (mrel2 !!! Regidx (mword_of_int 18 : mword 5)))]> mrel2) with F0.
    assert (Hpc3a : add_vec_int (mword_of_int (KernelSyms.sleep + 0x38) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc3a) in "Hpc".
    (* +0x3a jal acquire *)
    iPoseProof (sli_3a with "Htext") as "Hi3a".
    iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x3a)) (mword_of_int 1 : mword 5) (mword_of_int 2092222 : mword 21)
              F0 (av - 6)%nat true ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi3a [-]").
    iIntros (CID3 Hs3) "Hcg Hpc".
    set (F1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x3a) : mword 64) 4)]> F0).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x3a) : mword 64) 4)]> F0) with F1.
    assert (Hpcaq2 : add_vec (mword_of_int (KernelSyms.sleep + 0x3a) : mword 64) (sign_extend' 64 (mword_of_int 2092222 : mword 21))
                    = mword_of_int KernelSyms.acquire) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcaq2) in "Hpc".
    assert (Ha0_F1 : F1 !!! Regidx (mword_of_int 10 : mword 5) = lk0).
    { rewrite /F1 upd_ne; [| vm_compute; discriminate]. rewrite /F0 upd_eq Hs2_mrel2 !add_vec_zero_l. reflexivity. }
    assert (HF1ra : F1 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.sleep + 0x3a) : mword 64) 4)
      by (rewrite /F1 upd_eq; reflexivity).
    (* reconcile lk-derived acquire addresses to the spec's lka forms. *)
    assert (Hislk_f : F1 !!! Regidx (mword_of_int 10 : mword 5) = lka).
    { rewrite Ha0_F1 -Hlka0. symmetry.
      assert (H0 : sign_extend' 64 (mword_of_int 0 : mword 12) = (mword_of_int 0 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite H0. apply kv_addv_zero. }
    (* the bundle was stranded at the release's exit hart; re-anchor it. *)
    iDestruct (cpu_own_transport CID1 CID3 0 true pj C true ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    (* the parked credential "HTk" is presented here, and handed back. *)
    iApply (AcquireGen.wp_acquire_gen_sconf Φ γk Rk Tk Dk F1 0 true (proc_addr j) C (av - 6)%nat true
              ltac:(lia)
              ltac:(lia)
              HrefT HrefLkp
              with "Hcg Hcpu Htext Hpc [Hkopen] HTk Hpanicany [-]").
    { iEval (rewrite Hislk_f). iExact "Hkopen". }
    iIntros (CID4 Hs4 ms3 macq2) "%Hmsf3 HTk Hcg Hpc %Hcs_acq2 Hklocked HRk Hcpu Hpay0'".
    assert (Hpc3e : ret_pc (F1 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.sleep + 0x3e)) by (rewrite HF1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc3e) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* Epilogue: restore ra/s0/s1/s2/s3, pop the frame, return.            *)
    (* The lock is held again, so the hart is pinned from here on.         *)
    (* ------------------------------------------------------------------ *)
    (* the five saved frame cells arrive at [pa_stk sp0 k]; bridge each to
       the [spd + imm] form the c.ldsp leaves compute. *)
    iEval (rewrite Hb1) in "Hr1". iEval (rewrite Hb2) in "Hr2".
    iEval (rewrite Hb3) in "Hr3". iEval (rewrite Hb4) in "Hr4".
    iEval (rewrite Hb5) in "Hr5".
    (* sp threads (callee-saved) through all six callees back to the push. *)
    assert (Hcsp_macq2 : macq2 !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hcs_acq2 csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /F1 upd_ne; [| vm_compute; discriminate]. rewrite /F0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_rel2 csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /E1 upd_ne; [| vm_compute; discriminate].
      rewrite /E0 upd_ne; [| vm_compute; discriminate]. exact Hsp_msch. }
    (* +0x3e c.ldsp ra,40 *)
    iPoseProof (sli_3e with "Htext") as "Hi3e".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x3e)) (mword_of_int 5 : mword 6) (mword_of_int 1 : mword 5)
              macq2 (av - 6)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3e [Hr1] [-]").
    { iEval (rewrite Hcsp_macq2). iExact "Hr1". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr1".
    set (G4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> macq2).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> macq2) with G4.
    assert (Hpc40 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x3e) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc40) in "Hpc".
    assert (HcspG4 : G4 !!! Regidx csp_rs1 = spd) by (rewrite /G4 upd_ne; [exact Hcsp_macq2 | vm_compute; discriminate]).
    (* +0x40 c.ldsp s0,32 *)
    iPoseProof (sli_40 with "Htext") as "Hi40".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x40)) (mword_of_int 4 : mword 6) (mword_of_int 8 : mword 5)
              G4 (av - 6)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi40 [Hr2] [-]").
    { iEval (rewrite HcspG4). iExact "Hr2". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr2".
    set (G5 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> G4).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> G4) with G5.
    assert (Hpc42 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc42) in "Hpc".
    assert (HcspG5 : G5 !!! Regidx csp_rs1 = spd) by (rewrite /G5 upd_ne; [exact HcspG4 | vm_compute; discriminate]).
    (* +0x42 c.ldsp s1,24 *)
    iPoseProof (sli_42 with "Htext") as "Hi42".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x42)) (mword_of_int 3 : mword 6) (mword_of_int 9 : mword 5)
              G5 (av - 6)%nat (m !!! Regidx (mword_of_int 9 : mword 5)) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi42 [Hr3] [-]").
    { iEval (rewrite HcspG5). iExact "Hr3". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr3".
    set (G6 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> G5).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> G5) with G6.
    assert (Hpc44 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x42) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc44) in "Hpc".
    assert (HcspG6 : G6 !!! Regidx csp_rs1 = spd) by (rewrite /G6 upd_ne; [exact HcspG5 | vm_compute; discriminate]).
    (* +0x44 c.ldsp s2,16 *)
    iPoseProof (sli_44 with "Htext") as "Hi44".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x44)) (mword_of_int 2 : mword 6) (mword_of_int 18 : mword 5)
              G6 (av - 6)%nat (m !!! Regidx (mword_of_int 18 : mword 5)) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi44 [Hr4] [-]").
    { iEval (rewrite HcspG6). iExact "Hr4". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr4".
    set (G7 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> G6).
    change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> G6) with G7.
    assert (Hpc46 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x44) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc46) in "Hpc".
    assert (HcspG7 : G7 !!! Regidx csp_rs1 = spd) by (rewrite /G7 upd_ne; [exact HcspG6 | vm_compute; discriminate]).
    (* +0x46 c.ldsp s3,8 *)
    iPoseProof (sli_46 with "Htext") as "Hi46".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x46)) (mword_of_int 1 : mword 6) (mword_of_int 19 : mword 5)
              G7 (av - 6)%nat (m !!! Regidx (mword_of_int 19 : mword 5)) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi46 [Hr5] [-]").
    { iEval (rewrite HcspG7). iExact "Hr5". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr5".
    set (G8 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 19 : mword 5))]> G7).
    change (<[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 19 : mword 5))]> G7) with G8.
    assert (Hpc48 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x46) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc48) in "Hpc".
    assert (HcspG8 : G8 !!! Regidx csp_rs1 = spd) by (rewrite /G8 upd_ne; [exact HcspG7 | vm_compute; discriminate]).
    (* +0x48 c.addi16sp sp,48 : pop the frame *)
    iPoseProof (sli_48 with "Htext") as "Hi48".
    assert (Hspd6 : pa_stk sp0 6 = spd).
    { rewrite -Hspd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpopsp : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0).
    { rewrite -Hspd po_addv_assoc.
      assert (HAB : add_vec (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite HAB. apply kv_addv_zero. }
    iEval (rewrite Hcsp_macq2) in "Hr1". iEval (rewrite HcspG4) in "Hr2".
    iEval (rewrite HcspG5) in "Hr3". iEval (rewrite HcspG6) in "Hr4".
    iEval (rewrite HcspG7) in "Hr5".
    iAssert (stack_own sp0 6) with "[Hr1 Hr2 Hr3 Hr4 Hr5 Hgap]" as "Hframe6".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr1". { iExists _. iEval (rewrite Hb1). iExact "Hr1". }
      iSplitL "Hr2". { iExists _. iEval (rewrite Hb2). iExact "Hr2". }
      iSplitL "Hr3". { iExists _. iEval (rewrite Hb3). iExact "Hr3". }
      iSplitL "Hr4". { iExists _. iEval (rewrite Hb4). iExact "Hr4". }
      iSplitL "Hr5". { iExists _. iEval (rewrite Hb5). iExact "Hr5". }
      iSplitL "Hgap". { iExists _. iExact "Hgap". }
      done. }
    assert (Hpop_prem : G8 !!! Regidx csp_rs1 = pa_stk (add_vec (G8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6).
    { rewrite HcspG8 Hpopsp Hspd6. reflexivity. }
    iApply (wp_caddi16sp_pop_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x48)) (mword_of_int 3 : mword 6) G8 (av - 6)%nat 6 false
              Hpop_prem
              with "Hcg Hpc Hi48 [Hframe6] [-]").
    { rewrite HcspG8 Hpopsp. iExact "Hframe6". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (Gf := <[Regidx csp_rs1 := regval_into_reg (add_vec (G8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> G8).
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (G8 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> G8) with Gf.
    assert (Havk : ((av - 6) + 6)%nat = av) by lia.
    iEval (rewrite Havk) in "Hcg".
    assert (Hpc4a : add_vec_int (mword_of_int (KernelSyms.sleep + 0x48) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc4a) in "Hpc".
    (* +0x4a c.ret *)
    assert (HGfra : Gf !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /Gf upd_ne; [| vm_compute; discriminate].
      rewrite /G8 upd_ne; [| vm_compute; discriminate]. rewrite /G7 upd_ne; [| vm_compute; discriminate].
      rewrite /G6 upd_ne; [| vm_compute; discriminate]. rewrite /G5 upd_ne; [| vm_compute; discriminate].
      rewrite /G4 upd_eq. reflexivity. }
    iPoseProof (sli_4a with "Htext") as "Hi4a".
    iApply (wp_cret_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x4a)) (mword_of_int 1 : mword 5) Gf av false
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi4a [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hret_final : ret_pc (Gf !!! Regidx (mword_of_int 1 : mword 5))
                         = ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)))
      by (rewrite HGfra; reflexivity).
    iEval (rewrite Hret_final) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* Postcondition.  [callee_saved] is tp-free now (13 conjuncts), so     *)
    (* there is no tp fact left to establish -- [tp_pin] makes the resumed  *)
    (* file's tp THIS hart's id by construction.                            *)
    (* ------------------------------------------------------------------ *)
    (* threading helper: the registers sleep never writes go Gf -> msch,
       and the eight [Hmsch_*] premises carry them the rest of the way. *)
    assert (Hthr : forall c : mword 5, is_cs_idx c = true ->
      Regidx c ≠ Regidx (mword_of_int 1) -> Regidx c ≠ Regidx csp_rs1 ->
      Regidx c ≠ Regidx (mword_of_int 8) -> Regidx c ≠ Regidx (mword_of_int 9) ->
      Regidx c ≠ Regidx (mword_of_int 10) -> Regidx c ≠ Regidx (mword_of_int 18) ->
      Regidx c ≠ Regidx (mword_of_int 19) ->
      Gf !!! Regidx c = msch !!! Regidx c).
    { intros c Hcs H1 Hsp H8 H9 H10 H18 H19.
      rewrite /Gf upd_ne; [| exact Hsp].
      rewrite /G8 upd_ne; [| exact H19]. rewrite /G7 upd_ne; [| exact H18].
      rewrite /G6 upd_ne; [| exact H9]. rewrite /G5 upd_ne; [| exact H8].
      rewrite /G4 upd_ne; [| exact H1].
      rewrite (callee_saved_lookup Hcs_acq2 c Hcs).
      rewrite /F1 upd_ne; [| exact H1]. rewrite /F0 upd_ne; [| exact H10].
      rewrite (callee_saved_lookup Hcs_rel2 c Hcs).
      rewrite /E1 upd_ne; [| exact H1]. rewrite /E0 upd_ne; [| exact H10].
      reflexivity. }
    assert (Csp : Gf !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite /Gf upd_eq HcspG8 Hpopsp Hsp0; reflexivity).
    assert (Cs0 : Gf !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5)).
    { rewrite /Gf upd_ne; [| vm_compute; discriminate].
      rewrite /G8 upd_ne; [| vm_compute; discriminate]. rewrite /G7 upd_ne; [| vm_compute; discriminate].
      rewrite /G6 upd_ne; [| vm_compute; discriminate]. rewrite /G5 upd_eq. reflexivity. }
    assert (Cs1 : Gf !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5)).
    { rewrite /Gf upd_ne; [| vm_compute; discriminate].
      rewrite /G8 upd_ne; [| vm_compute; discriminate]. rewrite /G7 upd_ne; [| vm_compute; discriminate].
      rewrite /G6 upd_eq. reflexivity. }
    assert (Cs2 : Gf !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5)).
    { rewrite /Gf upd_ne; [| vm_compute; discriminate].
      rewrite /G8 upd_ne; [| vm_compute; discriminate]. rewrite /G7 upd_eq. reflexivity. }
    assert (Cs3 : Gf !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5)).
    { rewrite /Gf upd_ne; [| vm_compute; discriminate]. rewrite /G8 upd_eq. reflexivity. }
    assert (Cs4 : Gf !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5))
      by (rewrite (Hthr (mword_of_int 20) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch20).
    assert (Cs5 : Gf !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5))
      by (rewrite (Hthr (mword_of_int 21) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch21).
    assert (Cs6 : Gf !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5))
      by (rewrite (Hthr (mword_of_int 22) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch22).
    assert (Cs7 : Gf !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5))
      by (rewrite (Hthr (mword_of_int 23) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch23).
    assert (Cs8 : Gf !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5))
      by (rewrite (Hthr (mword_of_int 24) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch24).
    assert (Cs9 : Gf !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5))
      by (rewrite (Hthr (mword_of_int 25) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch25).
    assert (Cs10 : Gf !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5))
      by (rewrite (Hthr (mword_of_int 26) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch26).
    assert (Cs11 : Gf !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5))
      by (rewrite (Hthr (mword_of_int 27) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch27).
    iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! Gf with "[%] Hcg Hcpu Hpay0' Hpc HTk Hklocked HRk Hown' Hpark").
    { unfold callee_saved. repeat split; assumption. }
  Qed.

End SleepPostSched.

Section ProofSleep.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* extract the opaque context-slot payload, leaving the bundle at slot
     [emp] (what the sched call-site hands across the swtch). *)
  Lemma cpu_own_ctx_take (n : nat) (eb : bool) (p : mword 64) (D : iProp Σ) (b : bool) :
    cpu_own n eb p D b -∗ D ∗ cpu_own n eb p emp b.
  Proof.
    iIntros "[Hrest HD]". iFrame "HD". rewrite /cpu_own. iFrame "Hrest".
  Qed.

  Lemma wp_sleep_gen_sconf (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (γk : gname) (lka : mword 64) (Rk Tk Dk : iProp Σ)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
    : wp_sleep_gen_sconf_body Φ γs j γl γk lka Rk Tk Dk m av eb C.
  Proof.
    cbv beta delta [wp_sleep_gen_sconf_body].
    intros pcE pj chan lk0 ret_tgt Hj Hgl Hlka0 Heb Hav HrefT HrefLk HrefLkp. subst eb.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    (* "HTk" is PARKED across the whole middle of the proof: the credential
       rides the sleeping process's frame through sched() and is presented
       again at the re-acquire of lk.  So is "Hpark", the hart-free park
       receipt, which [scheds_take] spends just before the jal. *)
    iIntros "Hcg Hcpu Hpay0 #Htext Hpc #Hprocs #Hscheds #Hkopen HTk Hklocked HRk #Hpanicany Hown Hpark Hcont".
    (* ------------------------------------------------------------------ *)
    (* Prologue: 48-byte frame (push 6), save ra/s0/s1/s2/s3.             *)
    (* sleep runs at noff = 1, so the resource index is the literal        *)
    (* [false] and every leaf up to the park is [rewrite wp_next_off].     *)
    (* ------------------------------------------------------------------ *)
    set (spd := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))).
    iPoseProof (sli_00 with "Htext") as "Hi00".
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 6).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi16sp_push_s_sconf Φ pcE (mword_of_int 61 : mword 6) m av 6 false
              ltac:(lia) Hpush with "Hcg Hpc Hi00 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hframe Hpc".
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m) with A0.
    assert (HcspA0 : A0 !!! Regidx csp_rs1 = spd) by (rewrite /A0 upd_eq; reflexivity).
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & S5c & S6c & _)".
    iDestruct "S1c" as (vr1) "Hr1". iDestruct "S2c" as (vr2) "Hr2".
    iDestruct "S3c" as (vr3) "Hr3". iDestruct "S4c" as (vr4) "Hr4".
    iDestruct "S5c" as (vr5) "Hr5". iDestruct "S6c" as (vgap) "Hgap".
    assert (Hb1 : pa_stk sp0 1 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))))
      by (apply sl_frame_bridge; vm_compute; reflexivity).
    assert (Hb2 : pa_stk sp0 2 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))))
      by (apply sl_frame_bridge; vm_compute; reflexivity).
    assert (Hb3 : pa_stk sp0 3 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))))
      by (apply sl_frame_bridge; vm_compute; reflexivity).
    assert (Hb4 : pa_stk sp0 4 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))
      by (apply sl_frame_bridge; vm_compute; reflexivity).
    assert (Hb5 : pa_stk sp0 5 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))))
      by (apply sl_frame_bridge; vm_compute; reflexivity).
    (* +0x02 c.sdsp ra,40 *)
    iPoseProof (sli_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x02)) (mword_of_int 5 : mword 6) (mword_of_int 1 : mword 5)
              A0 (av - 6)%nat vr1 false with "Hcg Hpc Hi02 [Hr1] [-]").
    { iEval (rewrite HcspA0 -Hb1). iExact "Hr1". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr1".
    iEval (rgne) in "Hr1".
    assert (Hpc04 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    (* +0x04 c.sdsp s0,32 *)
    iPoseProof (sli_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x04)) (mword_of_int 4 : mword 6) (mword_of_int 8 : mword 5)
              A0 (av - 6)%nat vr2 false with "Hcg Hpc Hi04 [Hr2] [-]").
    { iEval (rewrite HcspA0 -Hb2). iExact "Hr2". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr2".
    iEval (rgne) in "Hr2".
    assert (Hpc06 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    (* +0x06 c.sdsp s1,24 *)
    iPoseProof (sli_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x06)) (mword_of_int 3 : mword 6) (mword_of_int 9 : mword 5)
              A0 (av - 6)%nat vr3 false with "Hcg Hpc Hi06 [Hr3] [-]").
    { iEval (rewrite HcspA0 -Hb3). iExact "Hr3". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr3".
    iEval (rgne) in "Hr3".
    assert (Hpc08 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    (* +0x08 c.sdsp s2,16 *)
    iPoseProof (sli_08 with "Htext") as "Hi08".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x08)) (mword_of_int 2 : mword 6) (mword_of_int 18 : mword 5)
              A0 (av - 6)%nat vr4 false with "Hcg Hpc Hi08 [Hr4] [-]").
    { iEval (rewrite HcspA0 -Hb4). iExact "Hr4". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr4".
    iEval (rgne) in "Hr4".
    assert (Hpc0a : add_vec_int (mword_of_int (KernelSyms.sleep + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    (* +0x0a c.sdsp s3,8 *)
    iPoseProof (sli_0a with "Htext") as "Hi0a".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x0a)) (mword_of_int 1 : mword 6) (mword_of_int 19 : mword 5)
              A0 (av - 6)%nat vr5 false with "Hcg Hpc Hi0a [Hr5] [-]").
    { iEval (rewrite HcspA0 -Hb5). iExact "Hr5". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr5".
    iEval (rgne) in "Hr5".
    assert (Hpc0c : add_vec_int (mword_of_int (KernelSyms.sleep + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    (* +0x0c c.addi4spn s0,sp,48 *)
    iPoseProof (sli_0c with "Htext") as "Hi0c".
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x0c)) (Cregidx (mword_of_int 0)) (mword_of_int 12 : mword 8) (mword_of_int 8 : mword 5)
              A0 (av - 6)%nat false ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (A1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> A0).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> A0) with A1.
    assert (Hpc0e : add_vec_int (mword_of_int (KernelSyms.sleep + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0e) in "Hpc".
    (* +0x0e c.mv s3,a0 : s3 := chan *)
    iPoseProof (sli_0e with "Htext") as "Hi0e".
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x0e)) (mword_of_int 19 : mword 5) (mword_of_int 10 : mword 5)
              A1 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A2 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg
        (add_vec zero_reg (A1 !!! Regidx (mword_of_int 10 : mword 5)))]> A1).
    change (<[Regidx (mword_of_int 19 : mword 5) := regval_into_reg
        (add_vec zero_reg (A1 !!! Regidx (mword_of_int 10 : mword 5)))]> A1) with A2.
    assert (Hpc10 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    (* +0x10 c.mv s2,a1 : s2 := lk0 *)
    iPoseProof (sli_10 with "Htext") as "Hi10".
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x10)) (mword_of_int 18 : mword 5) (mword_of_int 11 : mword 5)
              A2 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A3 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (add_vec zero_reg (A2 !!! Regidx (mword_of_int 11 : mword 5)))]> A2).
    change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg
        (add_vec zero_reg (A2 !!! Regidx (mword_of_int 11 : mword 5)))]> A2) with A3.
    assert (Hpc12 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    (* record s3 = chan, s2 = lk0. *)
    assert (HA3s3 : A3 !!! Regidx (mword_of_int 19 : mword 5) = add_vec zero_reg chan).
    { rewrite /A3 upd_ne; [| vm_compute; discriminate]. rewrite /A2 upd_eq.
      rewrite /A1 upd_ne; [| vm_compute; discriminate]. rewrite /A0 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HA3s2 : A3 !!! Regidx (mword_of_int 18 : mword 5) = add_vec zero_reg lk0).
    { rewrite /A3 upd_eq. rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate]. rewrite /A0 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    (* +0x12 jal myproc *)
    iPoseProof (sli_12 with "Htext") as "Hi12".
    iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x12)) (mword_of_int 1 : mword 5) (mword_of_int 2095588 : mword 21)
              A3 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi12 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (A4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x12) : mword 64) 4)]> A3).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x12) : mword 64) 4)]> A3) with A4.
    assert (Hpcmp : add_vec (mword_of_int (KernelSyms.sleep + 0x12) : mword 64) (sign_extend' 64 (mword_of_int 2095588 : mword 21))
                    = mword_of_int KernelSyms.myproc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcmp) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x12: myproc() -- a0 = proc_addr j; noff/intena round-trip at n=1.  *)
    (* ------------------------------------------------------------------ *)
    assert (HA4ra : A4 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.sleep + 0x12) : mword 64) 4)
      by (rewrite /A4 upd_eq; reflexivity).
    iApply (Myproc.wp_myproc_sconf Φ A4 (av - 6)%nat 1 true (proc_addr j) C false
              ltac:(lia)
              ltac:(lia)
              with "Hcg Hcpu Htext Hpc [-]").
    iApply wp_next_off_intro.
    iIntros (ms mp) "%Hmsf Hcg Hcpu Hpc %Hmp".
    destruct Hmp as [Hcs_mp Ha0_mp].
    assert (Hpc16 : ret_pc (A4 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.sleep + 0x16)) by (rewrite HA4ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    (* +0x16 c.mv s1,a0 : s1 := proc_addr j *)
    iPoseProof (sli_16 with "Htext") as "Hi16".
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x16)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              mp (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B0 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (mp !!! Regidx (mword_of_int 10 : mword 5)))]> mp).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (mp !!! Regidx (mword_of_int 10 : mword 5)))]> mp) with B0.
    assert (Hpc18 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc18) in "Hpc".
    (* +0x18 jal acquire *)
    iPoseProof (sli_18 with "Htext") as "Hi18".
    iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x18)) (mword_of_int 1 : mword 5) (mword_of_int 2092256 : mword 21)
              B0 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi18 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (B1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x18) : mword 64) 4)]> B0).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x18) : mword 64) 4)]> B0) with B1.
    assert (Hpcaq : add_vec (mword_of_int (KernelSyms.sleep + 0x18) : mword 64) (sign_extend' 64 (mword_of_int 2092256 : mword 21))
                    = mword_of_int KernelSyms.acquire) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcaq) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x18: acquire(&p->lock) -- take proc j's lock (n = 1).             *)
    (* ------------------------------------------------------------------ *)
    assert (Ha0_B1 : B1 !!! Regidx (mword_of_int 10 : mword 5) = proc_addr j).
    { rewrite /B1 upd_ne; [| vm_compute; discriminate]. rewrite /B0 upd_ne; [| vm_compute; discriminate]. exact Ha0_mp. }
    assert (HB1ra : B1 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.sleep + 0x18) : mword 64) 4)
      by (rewrite /B1 upd_eq; reflexivity).
    iPoseProof (procs_inv_lookup Φ γs j γl Hgl with "Hprocs") as "#Hislock".
    iApply (Acquire.wp_acquire_sconf Φ γl "proc"%string
              (proc_lock_res Φ γs γl (proc_addr j)) B1 1 true (proc_addr j) C (av - 6)%nat false
              ltac:(lia)
              ltac:(lia)
              with "Hcg Hcpu Htext Hpc [Hislock] Hpanicany [-]").
    { iEval (rewrite Ha0_B1). iExact "Hislock". }
    iApply wp_next_off_intro.
    iIntros (ms2 macq) "%Hmsf2 Hcg Hpc %Hcs_acq Hlocked HR Hcpu Hpay1".
    assert (Hpc1c : ret_pc (B1 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.sleep + 0x1c)) by (rewrite HB1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1c) in "Hpc".
    (* unpack the proc lock resource; drop the context slot. *)
    iDestruct (proc_lock_res_elim Φ γs γl (proc_addr j) with "HR") as (st0 ch0) "(Hstate & Hchan & Hpub & Hslot)".
    iClear "Hslot".
    (* +0x1c c.mv a0,s2 : a0 := lk0 (via zero_reg twice) *)
    iPoseProof (sli_1c with "Htext") as "Hi1c".
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x1c)) (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 5)
              macq (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (C0 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec zero_reg (macq !!! Regidx (mword_of_int 18 : mword 5)))]> macq).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec zero_reg (macq !!! Regidx (mword_of_int 18 : mword 5)))]> macq) with C0.
    assert (Hpc1e : add_vec_int (mword_of_int (KernelSyms.sleep + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1e) in "Hpc".
    (* +0x1e jal release *)
    iPoseProof (sli_1e with "Htext") as "Hi1e".
    iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x1e)) (mword_of_int 1 : mword 5) (mword_of_int 2092386 : mword 21)
              C0 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1e [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (C1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x1e) : mword 64) 4)]> C0).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x1e) : mword 64) 4)]> C0) with C1.
    assert (Hpcrl1 : add_vec (mword_of_int (KernelSyms.sleep + 0x1e) : mword 64) (sign_extend' 64 (mword_of_int 2092386 : mword 21))
                    = mword_of_int KernelSyms.release) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcrl1) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x1e: release(lk) -- give up the caller condition lock (n = 1).    *)
    (* The level only drops to 1, so the exit index is still [false] and   *)
    (* the hart stays pinned.                                              *)
    (* ------------------------------------------------------------------ *)
    (* thread s2 = lk0 through myproc/acquire; a0 reduces to lk0. *)
    assert (Hs2_macq : macq !!! Regidx (mword_of_int 18 : mword 5) = add_vec zero_reg lk0).
    { rewrite (callee_saved_lookup Hcs_acq (mword_of_int 18) ltac:(vm_compute; reflexivity)).
      rewrite /B1 upd_ne; [| vm_compute; discriminate]. rewrite /B0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_mp (mword_of_int 18) ltac:(vm_compute; reflexivity)).
      rewrite /A4 upd_ne; [| vm_compute; discriminate]. exact HA3s2. }
    assert (Ha0_C1 : C1 !!! Regidx (mword_of_int 10 : mword 5) = lk0).
    { rewrite /C1 upd_ne; [| vm_compute; discriminate]. rewrite /C0 upd_eq Hs2_macq !add_vec_zero_l. reflexivity. }
    assert (HC1ra : C1 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.sleep + 0x1e) : mword 64) 4)
      by (rewrite /C1 upd_eq; reflexivity).
    assert (Hlka_r1 : add_vec (C1 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = lka)
      by (rewrite Ha0_C1; exact Hlka0).
    (* the finisher CLOSES the invariant again (Out = emp): sleep gives the
       condition lock back, it does not dispose of it. *)
    iApply (ReleaseGen.wp_release_gen_sconf Φ γk lka Rk Dk emp%I C1 1 true (proc_addr j) C (av - 6)%nat
              Hlka_r1
              ltac:(lia)
              (HrefLk cpu_id) (HrefLkp cpu_id)
              with "Hcg Htext Hpc Hkopen Hklocked HRk [] Hcpu Hpay1 [-]").
    { iApply lock_finisher_close. }
    iApply wp_next_off_intro.
    iIntros (mrel1) "_ Hcg Hpc %Hcs_rel1 Hcpu".
    assert (Hpc22 : ret_pc (C1 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.sleep + 0x22)) by (rewrite HC1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc22) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x22: sd s3,32(s1) -- p->chan := chan.                             *)
    (* ------------------------------------------------------------------ *)
    (* thread s1 = proc_addr j and s3 = chan through the calls. *)
    assert (Hs1_mrel1 : mrel1 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j)).
    { rewrite (callee_saved_lookup Hcs_rel1 (mword_of_int 9) ltac:(vm_compute; reflexivity)).
      rewrite /C1 upd_ne; [| vm_compute; discriminate]. rewrite /C0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_acq (mword_of_int 9) ltac:(vm_compute; reflexivity)).
      rewrite /B1 upd_ne; [| vm_compute; discriminate]. rewrite /B0 upd_eq Ha0_mp. reflexivity. }
    assert (Hs3_mrel1 : mrel1 !!! Regidx (mword_of_int 19 : mword 5) = add_vec zero_reg chan).
    { rewrite (callee_saved_lookup Hcs_rel1 (mword_of_int 19) ltac:(vm_compute; reflexivity)).
      rewrite /C1 upd_ne; [| vm_compute; discriminate]. rewrite /C0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_acq (mword_of_int 19) ltac:(vm_compute; reflexivity)).
      rewrite /B1 upd_ne; [| vm_compute; discriminate]. rewrite /B0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_mp (mword_of_int 19) ltac:(vm_compute; reflexivity)).
      rewrite /A4 upd_ne; [| vm_compute; discriminate]. exact HA3s3. }
    assert (Hrec_chan : add_vec (mrel1 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 32 : mword 12))
                        = p_chan (proc_addr j)).
    { rewrite Hs1_mrel1 add_vec_zero_l. unfold p_chan, chan_off.
      assert (H32 : sign_extend' 64 (mword_of_int 32 : mword 12) = (mword_of_int 32 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite H32. reflexivity. }
    assert (Hrec_chang : add_vec (rget mrel1 (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 32 : mword 12))
                         = p_chan (proc_addr j)) by (rgne; exact Hrec_chan).
    assert (Hs3_mrel1g : rget mrel1 (mword_of_int 19 : mword 5) = add_vec zero_reg chan)
      by (rgne; exact Hs3_mrel1).
    iPoseProof (sli_22 with "Htext") as "Hi22".
    iApply (wp_sd_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x22)) (mword_of_int 19 : mword 5) (mword_of_int 9 : mword 5)
              (mword_of_int 32 : mword 12) mrel1 (av - 6)%nat ch0 false
              with "Hcg Hpc Hi22 [Hchan] [-]").
    { iEval (rewrite Hrec_chang). iExact "Hchan". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hchan".
    iEval (rewrite Hrec_chang Hs3_mrel1g add_vec_zero_l) in "Hchan".
    assert (Hpc26 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x22) : mword 64) 4 = mword_of_int (KernelSyms.sleep + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc26) in "Hpc".
    (* +0x26 c.li a5,2 *)
    iPoseProof (sli_26 with "Htext") as "Hi26".
    iApply (wp_cli_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x26)) (mword_of_int 15 : mword 5) (mword_of_int 2 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))) mrel1 (av - 6)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc Hi26 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (D0 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))]> mrel1).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))]> mrel1) with D0.
    assert (Hpc28 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    (* +0x28 c.sw a5,24(s1) : p->state := SLEEPING *)
    assert (HD0s1 : D0 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j))
      by (rewrite /D0 upd_ne; [| vm_compute; discriminate]; exact Hs1_mrel1).
    assert (Hrec_state : add_vec (D0 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 24 : mword 12))
                         = p_state (proc_addr j)).
    { rewrite HD0s1 add_vec_zero_l. unfold p_state, state_off.
      assert (H24 : sign_extend' 64 (mword_of_int 24 : mword 12) = (mword_of_int 24 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite H24. reflexivity. }
    assert (Hrec_stateg : add_vec (rget D0 (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 24 : mword 12))
                          = p_state (proc_addr j)) by (rgne; exact Hrec_state).
    assert (Hsv : trunc32 (D0 !!! Regidx (mword_of_int 15 : mword 5)) = SLEEPING).
    { rewrite /D0 upd_eq. unfold SLEEPING. exact sl_sleeping. }
    assert (Hsvg : trunc32 (rget D0 (mword_of_int 15 : mword 5)) = SLEEPING)
      by (rgne; exact Hsv).
    iPoseProof (sli_28 with "Htext") as "Hi28".
    iApply (wp_csw_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x28)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
              (mword_of_int 24 : mword 12) D0 (av - 6)%nat st0 false
              with "Hcg Hpc Hi28 [Hstate] [-]").
    { iEval (rewrite Hrec_stateg). iExact "Hstate". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hstate".
    iEval (rewrite Hrec_stateg Hsvg) in "Hstate".
    assert (Hpc2a : add_vec_int (mword_of_int (KernelSyms.sleep + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    (* +0x2a jal sched *)
    iPoseProof (sli_2a with "Htext") as "Hi2a".
    iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.sleep + 0x2a)) (mword_of_int 1 : mword 5) (mword_of_int 2096878 : mword 21)
              D0 (av - 6)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi2a [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (D1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x2a) : mword 64) 4)]> D0).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x2a) : mword 64) 4)]> D0) with D1.
    assert (Hpcsd : add_vec (mword_of_int (KernelSyms.sleep + 0x2a) : mword 64) (sign_extend' 64 (mword_of_int 2096878 : mword 21))
                    = mword_of_int KernelSyms.sched) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcsd) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x2a: sched() -- park at SLEEPING; resumes dispatched again.        *)
    (* ------------------------------------------------------------------ *)
    assert (HD1ra : D1 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.sleep + 0x2a) : mword 64) 4)
      by (rewrite /D1 upd_eq; reflexivity).
    iDestruct (cpu_own_ctx_take with "Hcpu") as "[HC Hcpuemp]".
    (* CHECK THE SCHEDULER RECORD OUT of the global invariant: [scheds_take]
       spends the [park_hlf j true] receipt (leaving the [park_hlf j false]
       that [proc_held] carries across the crossing) and produces exactly the
       [▷ sched_vc] sched's own contract demands. *)
    iDestruct (cpu_own_set_proc 1 true (proc_addr j) (proc_addr j) emp with "Hcpuemp") as "[Hph Hback]".
    iApply fupd_wp.
    iMod (SchedCtx.scheds_take Φ γs ⊤ (CID : CPU) j with "Hscheds Hph Hpark") as "(Hvc & Hph & Hpark)";
      [solve_ndisj|exact Hj|].
    iModIntro.
    iDestruct ("Hback" with "Hph") as "Hcpuemp".
    (* the trap-CSR set the spec's own pay carries crosses inside the chain
       payload and comes back at the dispatching hart, where the release of
       p->lock spends it. *)
    iAssert trap_csrs with "[Hpay0]" as "Htc". { iExact "Hpay0". }
    iApply (Sched.wp_sched_sconf Φ γs j γl SLEEPING chan D1 (av - 6)%nat true
              Hj Hgl (needs_ctx_SLEEPING) eq_refl ltac:(lia)
              with "Hcg Htext Hpc Hprocs [Hlocked Hstate Hchan Hpub Hpark] Htc Hcpuemp Hown Hvc [-]").
    { rewrite /proc_held. iFrame "Hlocked Hstate Hchan Hpub Hpark". }
    (* SCHED RETURNS ON HART [CIDs].  Everything below runs there, inside
       [sleep_post_sched] at [(CID0 := CIDs)]. *)
    iIntros (CIDs Hss msch ch') "%Hcs_sch Hcg Hpc Hheld' Htc' #Havail Hcpuemp Hown' Hvc'".
    (* what the post-resume half needs about [msch], read off this tower. *)
    assert (Hsp_msch : msch !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hcs_sch csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /D1 upd_ne; [| vm_compute; discriminate]. rewrite /D0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_rel1 csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /C1 upd_ne; [| vm_compute; discriminate]. rewrite /C0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_acq csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /B1 upd_ne; [| vm_compute; discriminate]. rewrite /B0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_mp csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /A4 upd_ne; [| vm_compute; discriminate]. rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate]. rewrite /A1 upd_ne; [| vm_compute; discriminate].
      exact HcspA0. }
    assert (Hs1_msch : msch !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j)).
    { rewrite (callee_saved_lookup Hcs_sch (mword_of_int 9) ltac:(vm_compute; reflexivity)).
      rewrite /D1 upd_ne; [| vm_compute; discriminate]. exact HD0s1. }
    assert (Hs2_msch : msch !!! Regidx (mword_of_int 18 : mword 5) = add_vec zero_reg lk0).
    { rewrite (callee_saved_lookup Hcs_sch (mword_of_int 18) ltac:(vm_compute; reflexivity)).
      rewrite /D1 upd_ne; [| vm_compute; discriminate]. rewrite /D0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_rel1 (mword_of_int 18) ltac:(vm_compute; reflexivity)).
      rewrite /C1 upd_ne; [| vm_compute; discriminate]. rewrite /C0 upd_ne; [| vm_compute; discriminate].
      exact Hs2_macq. }
    assert (Hthr : forall c : mword 5, is_cs_idx c = true ->
      Regidx c ≠ Regidx (mword_of_int 1) -> Regidx c ≠ Regidx csp_rs1 ->
      Regidx c ≠ Regidx (mword_of_int 8) -> Regidx c ≠ Regidx (mword_of_int 9) ->
      Regidx c ≠ Regidx (mword_of_int 10) -> Regidx c ≠ Regidx (mword_of_int 15) ->
      Regidx c ≠ Regidx (mword_of_int 18) -> Regidx c ≠ Regidx (mword_of_int 19) ->
      msch !!! Regidx c = m !!! Regidx c).
    { intros c Hcs H1 Hsp H8 H9 H10 H15 H18 H19.
      rewrite (callee_saved_lookup Hcs_sch c Hcs).
      rewrite /D1 upd_ne; [| exact H1]. rewrite /D0 upd_ne; [| exact H15].
      rewrite (callee_saved_lookup Hcs_rel1 c Hcs).
      rewrite /C1 upd_ne; [| exact H1]. rewrite /C0 upd_ne; [| exact H10].
      rewrite (callee_saved_lookup Hcs_acq c Hcs).
      rewrite /B1 upd_ne; [| exact H1]. rewrite /B0 upd_ne; [| exact H9].
      rewrite (callee_saved_lookup Hcs_mp c Hcs).
      rewrite /A4 upd_ne; [| exact H1]. rewrite /A3 upd_ne; [| exact H18].
      rewrite /A2 upd_ne; [| exact H19]. rewrite /A1 upd_ne; [| exact H8].
      rewrite /A0 upd_ne; [| exact Hsp]. reflexivity. }
    assert (Hmsch20 : msch !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5))
      by (apply Hthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    assert (Hmsch21 : msch !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5))
      by (apply Hthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    assert (Hmsch22 : msch !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5))
      by (apply Hthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    assert (Hmsch23 : msch !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5))
      by (apply Hthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    assert (Hmsch24 : msch !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5))
      by (apply Hthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    assert (Hmsch25 : msch !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5))
      by (apply Hthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    assert (Hmsch26 : msch !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5))
      by (apply Hthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    assert (Hmsch27 : msch !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5))
      by (apply Hthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
    (* the pc: sched hands back [ret_pc (D1 !!! ra)] = KernelSyms.sleep + 0x2e *)
    assert (Hpc2e : ret_pc (D1 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.sleep + 0x2e)) by (rewrite HD1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2e) in "Hpc".
    (* the five saved frame cells, re-addressed at [pa_stk sp0 k]. *)
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
    (* re-anchor the caller's continuation at the DISPATCHING hart, and run
       the post-resume half there. *)
    iDestruct (wp_next_shift Hss with "Hcont") as "Hcont".
    iApply (sleep_post_sched (CID0 := CIDs) Φ γs j γl ch' γk lka lk0 Rk Tk Dk m msch av C
              sp0 spd vgap
              ltac:(lia) Hj ltac:(reflexivity) ltac:(reflexivity) Hlka0 HrefT HrefLkp
              Hsp_msch Hs1_msch Hs2_msch
              Hmsch20 Hmsch21 Hmsch22 Hmsch23 Hmsch24 Hmsch25 Hmsch26 Hmsch27
              with "Htext Hislock Hscheds Hkopen Hpanicany Hcg Hpc Hheld' Htc' Hcpuemp HC HTk Hown' Hvc'
                    Hr1 Hr2 Hr3 Hr4 Hr5 Hgap Hcont").
  Qed.

End ProofSleep.

End SleepGenProof.

(* The static-kernel-lock instance: no credential, nothing can die.  Verbatim
   the statement the ordinary [SLEEP] consumers (acquiresleep, sys_pause) were
   written against. *)
Module SleepOfGen (G : SLEEP_GEN) : SLEEP.

Section OfGen.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_sleep_sconf (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (γk : gname) (lka : mword 64) (sk : string) (Rk : iProp Σ)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
    : wp_sleep_sconf_body Φ γs j γl γk lka sk Rk m av eb C.
  Proof.
    cbv beta delta [wp_sleep_sconf_body].
    intros pcE pj chan lk0 ret_tgt Hj Hgl Hlka0 Heb Hav.
    iIntros "Hcg Hcpu Hpay0 #Htext Hpc #Hprocs #Hscheds #Hkislock Hklocked HRk #Hpanic Hown Hpark Hcont".
    iApply (G.wp_sleep_gen_sconf Φ γs j γl γk lka Rk emp%I False%I m av eb C
              Hj Hgl Hlka0 Heb Hav
              (lock_refute_False _) (fun i => lock_refute_False _) (fun i => lock_refute_False _)
              with "Hcg Hcpu Hpay0 Htext Hpc Hprocs Hscheds [] [] Hklocked HRk Hpanic Hown Hpark [-]").
    { iApply (is_lock_openable with "Hkislock"). }
    { done. }
    iIntros (CIDf) "%Hsf".
    iIntros (mf) "%Hcs Hcg Hcpu Hpay Hpc _ Hklocked HRk Hown Hpark".
    iApply ("Hcont" $! CIDf with "[%] [//] Hcg Hcpu Hpay Hpc Hklocked HRk Hown Hpark").
    { exact Hsf. }
  Qed.

End OfGen.

End SleepOfGen.
