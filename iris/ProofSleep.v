(* ProofSleep.v -- the whole-function sconf-tier proof of sleep()
   (SpecSleep.v), as a functor over its callees' interfaces
   (myproc, acquire, sched, release).  See claude-notes/completed/yield-sched.md.

   sleep() is yield() WITH A GUARD:

     p = myproc(); acquire(&p->lock);
     if (p->chan != 0) { p->state = SLEEPING; sched(); }
     release(&p->lock);

   so the proof is ProofYield.v's, with the [c.li]/[c.sw]/[jal sched] run
   moved behind a [c.ld a5,32(s1)] + [c.beqz a5,+0x20] and duplicated on the
   arm that does park.  Everything else -- the 32-byte prologue, the myproc /
   acquire pair, the scheduler-swtch protocol threading (SchedCtx.v), the
   release and the epilogue -- is byte-for-byte yield's.

   THE TWO ARMS REJOIN AT +0x20, AND THEY REJOIN ON DIFFERENT HARTS.  The
   parking arm returns from sched() wherever some scheduler dispatched the
   process; the no-park arm never left this hart.  So the release at +0x22 and
   the epilogue behind it are proved ONCE, hart-generically, as [sleep_join]
   with its OWN [CID0] binder -- the tree's rejoining-arms shape (see
   claude-notes/completed/fileclose.md) -- and each arm applies it at its own
   hart, [(CID0 := CIDs)] on the park arm and [(CID0 := CIDa)] on the no-park
   one.  THE JOIN PREDICATE DOES NOT MENTION WHICH ARM RAN: both arrive
   holding p->lock with [p->state] at RUNNING (the no-park arm never wrote it;
   the park arm was dispatched back to RUNNING) and with the whole
   proc-side bundle -- [proc_held ... RUNNING ch], the raw context cells, the
   hart tag and this hart's parked scheduler record.

   THE EXPLICIT-CPUID SHAPE.  sleep's contract is [wp_next true pj ...] -- the
   crossing index of a parking function is the literal [true] -- while its
   RESOURCE index is [eb] up to the acquire and the literal [false] from
   there to the release, where the held lock pins the hart and every leaf
   collapses via [wp_next_off].  sleep's own [wp_next] obligation is
   dischargeable at ANY hart: at index [true] the only pinning condition left
   is [pj = zero_reg], which [SchedCtx.proc_addr_nonzero] refutes, so
   [WpNext.wp_next_retarget] moves it to whichever hart the arm ended on.

   THE PARKED SCHEDULER RECORD LIVES IN THE RUNNING PROC'S OWN LOCK.  sleep
   holds that lock already (it is about to read [p->chan]), so it takes the
   record straight out of [proc_slots]' RUNNING arm -- no invariant, no fancy
   update, no receipt.  [SchedCtx.proc_slots_running] is the take-out: the
   thread presents the HART TAG half it carries inside [IntrDefs.cpu_claim],
   which both refutes every non-RUNNING arm and collapses the arm's
   existential hart to this one, and gets back the whole tag, the raw context
   cells and this hart's parked record.  On the park arm all three cross the
   swtch and come back at the RESUMING hart; on the no-park arm they never
   move.  Either way [proc_slots_running_intro] puts them back into the lock
   the release gives up.

   THE SECOND LEMMA, [wp_sleep_nested], is the same walk entered at noff =
   [S n] -- a thread that already holds a spinlock.  There the guard's two
   arms do not rejoin at all: the park arm reaches sched() at [S (S n)] and
   panics ("sched locks"), while the no-park arm releases p->lock and
   RETURNS.  That is why it is not a divergence lemma; SpecSleep.v's header
   on [wp_sleep_nested_body] records why no premise could make it one.  The
   whole walk runs at the literal [false] -- the interior release pops to
   [S n >= 1], so nothing re-enables and the hart never moves -- so it needs
   no [wp_next], no trap CSRs, and opens the lock resource for its CELLS
   only: no hart tag, no claim, no [proc_slots_running]. *)
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
Require Import InstrBytes KernelText IntrDefs.
Require Import HartTp WpNext.
Require Import WpSmodeIntr.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpLock.
Require Import FdSlots.
Require Import ProcGeom.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import KernelRvcDecode.
Require Import CodeSleep.
Require Import SpecMyproc SpecAcquire SpecSched SpecRelease SpecSleep.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* Pure helper: the stored state value.                                   *)
(* ===================================================================== *)

(* the c.li a5,2 value truncated to 32 bits is SLEEPING = mword_of_int 2. *)
Lemma sl_sleeping :
  trunc32 (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))) : mword 64)
  = (mword_of_int 2 : mword 32).
Proof. vm_compute. reflexivity. Qed.

(* generic register-map peel over the proofs' [set]-chains (hit-first).  Top
   level rather than Section-local: BOTH the join lemma and the nested-entry
   lemma want it, and an [Ltac] declared inside a [Section] does not survive
   the section's close. *)
Ltac sl_peel :=
  repeat first
    [ rewrite upd_eq
    | rewrite upd_ne; [| vm_compute; discriminate]
    | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ].

Module SleepProof (Myproc : MYPROC) (Acquire : ACQUIRE) (Sched : SCHED) (Release : RELEASE) : SLEEP.

(* ===================================================================== *)
(* THE REJOINING-ARMS EPILOGUE, AS ITS OWN LEMMA.                         *)
(*                                                                        *)
(* The two arms of the +0x16 [beqz] rejoin at +0x20 ON DIFFERENT HARTS:    *)
(* sched() does not return on the hart it parked from (SpecSched.v) -- proc*)
(* contexts are migratable, so its continuation is a [wp_next true] whose  *)
(* rebound [CID] is the DISPATCHING hart -- while the no-park arm never    *)
(* left the hart it started on.  Everything from the join onwards -- the   *)
(* release, the epilogue, the postcondition -- therefore has to hold at an *)
(* ARBITRARY hart, which a Section-fixed [CID] cannot express.  So the     *)
(* whole tail is ONE lemma with its OWN [CID0] binder (the porting guide's *)
(* rule for a decomposed proof), applied once per arm; and its own         *)
(* continuation is a [wp_next] as well: release re-enables interrupts at   *)
(* its last instruction, so even the epilogue is hart-generic.             *)
(*                                                                        *)
(* ITS PREMISES DO NOT MENTION WHICH ARM RAN.  Both arrive holding p->lock *)
(* with [p->state] at RUNNING -- the no-park arm never wrote it, the park  *)
(* arm was dispatched back to RUNNING -- and carrying the whole proc-side  *)
(* bundle: [proc_held ... RUNNING ch], the raw context cells, the hart tag *)
(* and this hart's parked scheduler record.  The chan value [ch'] is the   *)
(* only thing that differs, and it is existential in the lock invariant.   *)
(* ===================================================================== *)
Section SleepJoin.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ}.

  (* extract the opaque context-slot payload, leaving the bundle at slot
     [emp] (what the sched call-site hands across the swtch).  It carries its
     OWN hart binder: the call site is PAST an interrupts-enabled stretch, so
     a lemma sharing an enclosing section's [Context CID] would silently pin
     to the entry hart (porting guide, "a helper lemma sharing the enclosing
     Section's Context"). *)
  Lemma cpu_own_ctx_take `{GEN : GenId} `{CID0 : CpuId}
      (n : nat) (eb : bool) (p : mword 64) (D : iProp Σ) :
    cpu_own n eb p D false -∗ D ∗ cpu_own n eb p emp false.
  Proof.
    iIntros "[Hh HD]". iFrame "HD". rewrite cpu_own_off. iFrame "Hh".
  Qed.

  Lemma sleep_join `{GEN : GenId} `{CID0 : CpuId}
       (γs : list gname)
      (j : nat) (γl : gname) (ch' : mword 64)
      (m mj : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 spd vgap : mword 64) :
    let pj := proc_addr j in
    (20 <= av)%nat ->
    (j < NPROC)%nat ->
    add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = spd ->
    sp0 = m !!! Regidx csp_rs1 ->
    (* NOTE: the old [⌜mj !!! x4 = cid_word⌝] premise is GONE -- [tp_pin]
       makes the tp slot unobservable, so nothing can read it. *)
    mj !!! Regidx csp_rs1 = spd ->
    mj !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j) ->
    (* s2..s11: untouched by sleep and by everything it calls *)
    mj !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5) ->
    mj !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5) ->
    mj !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5) ->
    mj !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) ->
    mj !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) ->
    mj !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) ->
    mj !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) ->
    mj !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) ->
    mj !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) ->
    mj !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5) ->
    kernel_text -∗
    is_lock γl (proc_addr j) "proc"%string (proc_lock_res γs γl (proc_addr j)) -∗
    sie_cap_gpr mj (trap_res eb + (av - 4))%nat false pj -∗
    pc_is (mword_of_int (KernelSyms.sleep + 0x20)) -∗
    proc_held cpu_id j γl RUNNING ch' -∗
    trap_csrs -∗
    cpu_own 1 eb pj C false -∗
    (* the cells the RUNNING arm of the lock holds -- handed back by swtch on
       the park arm, never given up on the no-park one.  They go into the
       RUNNING lock at the release below, which is where the NEXT park will
       find them. *)
    own_ctx (p_context pj) -∗
    (* the hart tag, whole, at the hart the dispatch resumed us on: half goes
       back into [run_slot] at the release, half becomes this thread's own
       [cpu_claim]. *)
    hart_full j cpu_id -∗
    ▷ sched_vc γs (a_cpu_ctx cid_word) pj -∗
    (* the three saved frame words + the frame's bottom slot *)
    pa_stk sp0 1 ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
    pa_stk sp0 2 ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
    pa_stk sp0 3 ↦₈ (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
    pa_stk sp0 4 ↦₈ vgap -∗
    wp_next true pj (fun (CID : CpuId) =>
      ∀ (mf : regfile),
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr mf av eb pj -∗
        cpu_own 0 eb pj C eb -∗
        pc_is (ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))) -∗
        trap_csrs_ext eb -∗
        cpu_claim_ext eb pj -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj Hav Hj Hspd Hsp0 Hsp_mj Hs1_mj
           Hmj18 Hmj19 Hmj20 Hmj21 Hmj22 Hmj23 Hmj24 Hmj25 Hmj26 Hmj27.
    iIntros "#Htext #Hislock Hcg Hpc Hheld' Htc Hcpu Hown' Htag Hvc' Hr24 Hr16 Hr8 Hgap Hcont".
    (* frame-slot address bridges: slot k sits at [spd + 8*(4-k)]. *)
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite -Hspd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb1 : pa_stk sp0 1
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite -Hspd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite -Hspd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : pa_stk sp0 3
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite -Hspd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iDestruct "Hheld'" as "(Hlocked & Hstate & Hpg & Hchan & Hpub)".
    (* ------------------------------------------------------------------ *)
    (* WHAT THE DISPATCH HANDED BACK, taken apart once.  The record and the *)
    (* raw context cells go into this proc's own lock at the release below; *)
    (* the tag splits between that slot and this thread's [cpu_claim].      *)
    (* Nothing here is a fancy update: no invariant is in the way any more. *)
    (* ------------------------------------------------------------------ *)
    (* half #2 comes back out of [proc_held]'s whole share: at RUNNING the
       lock keeps only the tie, and the claim is this thread's again. *)
    iDestruct (pstate_whole_split (proc_addr j) RUNNING) as "[Hws _]".
    iDestruct ("Hws" with "Hpg") as "[Hpg Hclm]".
    rewrite unclaimed_RUNNING.
    iDestruct (pstate_at_elim j (1/2) RUNNING Hj with "Hclm") as "Hclm".
    rewrite hart_split. iDestruct "Htag" as "[Htaga Htagb]".
    (* +0x20: c.mv a0,s1 : a0 := s1 = proc_addr j -- lock still held, so the
       hart is PINNED and [wp_next_off] collapses the binder. *)
    iPoseProof (sli_20 with "Htext") as "Hi20".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sleep + 0x20)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              mj (trap_res eb + (av - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi20").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (D0 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec zero_reg (mj !!! Regidx (mword_of_int 9 : mword 5)))]> mj).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec zero_reg (mj !!! Regidx (mword_of_int 9 : mword 5)))]> mj) with D0.
    assert (Hpc22 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x20) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc22) in "Hpc".
    (* +0x1e: jal release *)
    iPoseProof (sli_22 with "Htext") as "Hi22".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sleep + 0x22)) (mword_of_int 1 : mword 5) (mword_of_int 2092288 : mword 21)
              D0 (trap_res eb + (av - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi22").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (D1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x22) : mword 64) 4)]> D0).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x22) : mword 64) 4)]> D0) with D1.
    assert (Hpcrl : add_vec (mword_of_int (KernelSyms.sleep + 0x22) : mword 64) (sign_extend' 64 (mword_of_int 2092288 : mword 21))
                    = mword_of_int KernelSyms.release) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcrl) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x1e: release(&p->lock) -- with the process RUNNING (slot emp).    *)
    (* ------------------------------------------------------------------ *)
    assert (Ha0_D1 : D1 !!! Regidx (mword_of_int 10 : mword 5) = proc_addr j).
    { rewrite /D1 upd_ne; [| vm_compute; discriminate].
      rewrite /D0 upd_eq Hs1_mj !add_vec_zero_l. reflexivity. }
    assert (HD1ra : D1 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.sleep + 0x22) : mword 64) 4)
      by (rewrite /D1 upd_eq; reflexivity).
    assert (Hlka : add_vec (D1 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = proc_addr j).
    { rewrite Ha0_D1.
      assert (H0 : sign_extend' 64 (mword_of_int 0 : mword 12) = (mword_of_int 0 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite H0. apply kv_addv_zero. }
    (* rebuild the lock resource: at RUNNING there is no parked record, no
       dormant block and -- since it IS running -- no park receipt either,
       but the RAW CONTEXT CELLS go back in.  They are what swtch handed
       this thread when the scheduler resumed it, and leaving them in the
       lock is what lets the NEXT park (or the next preempting trap) find
       them without being handed them by a caller. *)
    iAssert (proc_lock_res γs γl (proc_addr j)) with "[Hstate Hpg Hchan Hpub Hown' Htaga Hvc']" as "HR2".
    { rewrite /proc_lock_res. iExists RUNNING, ch'. iFrame "Hstate Hpg Hchan Hpub".
      iApply (proc_slots_running_intro γs j cpu_id Hj with "Htaga Hown' Hvc'"). }
    (* THE TRAP-CSR SPLIT.  release consumes [arm_pay 0 eb _] -- the set
       at [eb = true], nothing at [eb = false].  The complement is what this
       call was handed from outside and owes back to sleep's caller; exactly
       one of the two is [emp]. *)
    iEval (rewrite -(trap_csrs_ext_split eb)) in "Htc".
    iDestruct "Htc" as "[Hpay Hext]".
    (* THE FREED STATE HALF takes the same two-sided cut.  At [eb = true] the
       release's last instruction re-enables interrupts, so half #2 goes back
       INTO [sie_arm true pj] as the arm's claim; at [eb = false] no arm is
       rebuilt and the thread keeps it, to hand to sleep's caller. *)
    iDestruct (cpu_claim_proc j Hj with "Hclm Htagb") as "Hclm".
    iEval (rewrite -(cpu_claim_ext_split eb pj)) in "Hclm".
    iDestruct "Hclm" as "[Hclmp Hclmx]".
    iApply (Release.wp_release_sconf γl (proc_addr j) "proc"%string
              (proc_lock_res γs γl (proc_addr j)) D1 0 eb pj C (av - 4)%nat
              Hlka
              ltac:(lia)
              with "Hcg Htext Hpc Hislock Hlocked HR2 Hcpu [$Hpay $Hclmp]").
    (* release's exit index is [outb = eb]: at [eb = true] it re-enables at
       its LAST instruction, so the hart can move there and the epilogue
       below is hart-GENERIC; at [eb = false] it does not, and the chain
       pins every step to this hart.  Either way the leaves run at [eb]. *)
    iIntros (CIDr Hsr mrel) "Hcg Hpc %Hcs_rel Hcpu".
    assert (Hpc26 : ret_pc (D1 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.sleep + 0x26)) by (rewrite HD1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc26) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* Epilogue: restore ra/s0/s1, pop the frame, return (mirror myproc).  *)
    (* ------------------------------------------------------------------ *)
    (* sp threads (callee-saved) through all four callees back to the push. *)
    assert (Hcsp_mrel : mrel !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hcs_rel csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /D1 upd_ne; [| vm_compute; discriminate]. rewrite /D0 upd_ne; [| vm_compute; discriminate].
      exact Hsp_mj. }
    (* the three saved frame cells arrive at [pa_stk sp0 k]; bridge each to
       the [spd + imm] form the c.ldsp leaves compute. *)
    iEval (rewrite Hb1) in "Hr24".
    iEval (rewrite Hb2) in "Hr16".
    iEval (rewrite Hb3) in "Hr8".
    (* +0x22: c.ldsp ra,24 *)
    iPoseProof (sli_26 with "Htext") as "Hi26".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sleep + 0x26)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              mrel (av - 4)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26 [Hr24]").
    { iEval (rewrite Hcsp_mrel). iExact "Hr24". }
    iIntros (CIDe1 Hse1) "Hcg Hpc Hr24".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mrel).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mrel) with E1.
    assert (Hpc28 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    assert (HcspE1 : E1 !!! Regidx csp_rs1 = spd)
      by (rewrite /E1 upd_ne; [exact Hcsp_mrel | vm_compute; discriminate]).
    (* +0x24: c.ldsp s0,16 *)
    iPoseProof (sli_28 with "Htext") as "Hi28".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sleep + 0x28)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              E1 (av - 4)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi28 [Hr16]").
    { iEval (rewrite HcspE1). iExact "Hr16". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hr16".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1) with E2.
    assert (Hpc2a : add_vec_int (mword_of_int (KernelSyms.sleep + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    assert (HcspE2 : E2 !!! Regidx csp_rs1 = spd)
      by (rewrite /E2 upd_ne; [exact HcspE1 | vm_compute; discriminate]).
    (* +0x26: c.ldsp s1,8 *)
    iPoseProof (sli_2a with "Htext") as "Hi2a".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sleep + 0x2a)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              E2 (av - 4)%nat (m !!! Regidx (mword_of_int 9 : mword 5)) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2a [Hr8]").
    { iEval (rewrite HcspE2). iExact "Hr8". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hr8".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2) with E3.
    assert (Hpc2c : add_vec_int (mword_of_int (KernelSyms.sleep + 0x2a) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2c) in "Hpc".
    assert (HcspE3 : E3 !!! Regidx csp_rs1 = spd)
      by (rewrite /E3 upd_ne; [exact HcspE2 | vm_compute; discriminate]).
    (* +0x28: c.addi16sp sp,32 -- pop the frame *)
    set (E4 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3).
    assert (Hsp0up : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite -Hspd po_addv_assoc.
      assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                            (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite HAB. apply avi0. }
    assert (HE4sp : E4 !!! Regidx csp_rs1 = sp0).
    { rewrite /E4 upd_eq HcspE3. exact Hsp0up. }
    assert (Hwv : add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HcspE3. exact Hsp0up. }
    assert (Hpop : E3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HcspE3. symmetry. exact Hspd4. }
    iPoseProof (sli_2c with "Htext") as "Hi2c".
    iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hgap]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24". { iExists _. iEval (rewrite Hb1 -Hcsp_mrel). iExact "Hr24". }
      iSplitL "Hr16". { iExists _. iEval (rewrite Hb2 -HcspE1). iExact "Hr16". }
      iSplitL "Hr8".  { iExists _. iEval (rewrite Hb3 -HcspE2). iExact "Hr8". }
      iSplitL "Hgap". { iExists _. iExact "Hgap". }
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.sleep + 0x2c)) (mword_of_int 2 : mword 6) E3 (av - 4)%nat 4 eb Hpop
              with "Hcg Hpc Hi2c Hframe4").
    iIntros (CIDe4 Hse4) "Hcg Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3) with E4.
    assert (Hpc2e : add_vec_int (mword_of_int (KernelSyms.sleep + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2e) in "Hpc".
    (* +0x2a: c.ret *)
    assert (HE4ra : E4 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1. apply upd_eq. }
    iPoseProof (sli_2e with "Htext") as "Hi2e".
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.sleep + 0x2e)) (mword_of_int 1 : mword 5) E4 av eb
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi2e").
    iIntros (CIDe5 Hse5) "Hcg Hpc".
    assert (Hra_final : ret_pc (rget E4 (mword_of_int 1 : mword 5))
                        = ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)))
      by (rgne; rewrite HE4ra; reflexivity).
    iEval (rewrite Hra_final) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* Post: hand every resource straight back; callee_saved via threading.*)
    (* The tp conjunct is GONE -- [tp_pin] makes it true by construction,  *)
    (* so [callee_saved] has thirteen components, not fourteen.            *)
    (* ------------------------------------------------------------------ *)
    (* the registers sleep itself never writes thread E4 -> mrel -> mj,
       and the ten [Hmj_*] premises carry them the rest of the way. *)
    assert (Cthr : forall c : mword 5, is_cs_idx c = true ->
      Regidx c ≠ Regidx (mword_of_int 1) -> Regidx c ≠ Regidx (mword_of_int 8) ->
      Regidx c ≠ Regidx (mword_of_int 9) -> Regidx c ≠ Regidx (mword_of_int 10) ->
      Regidx c ≠ Regidx csp_rs1 ->
      E4 !!! Regidx c = mj !!! Regidx c).
    { intros c Hcs H1 H8 H9 H10 Hsp.
      rewrite /E4 upd_ne; [| exact Hsp].
      rewrite /E3 upd_ne; [| exact H9]. rewrite /E2 upd_ne; [| exact H8].
      rewrite /E1 upd_ne; [| exact H1].
      rewrite (callee_saved_lookup Hcs_rel c Hcs).
      rewrite /D1 upd_ne; [| exact H1]. rewrite /D0 upd_ne; [| exact H10].
      reflexivity. }
    assert (Csp : E4 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite HE4sp Hsp0; reflexivity).
    assert (Cs0 : E4 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (sl_peel; reflexivity).
    assert (Cs1 : E4 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (sl_peel; reflexivity).
    assert (Cs2 : E4 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5))
      by (rewrite (Cthr (mword_of_int 18) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmj18).
    assert (Cs3 : E4 !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5))
      by (rewrite (Cthr (mword_of_int 19) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmj19).
    assert (Cs4 : E4 !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5))
      by (rewrite (Cthr (mword_of_int 20) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmj20).
    assert (Cs5 : E4 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5))
      by (rewrite (Cthr (mword_of_int 21) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmj21).
    assert (Cs6 : E4 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5))
      by (rewrite (Cthr (mword_of_int 22) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmj22).
    assert (Cs7 : E4 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5))
      by (rewrite (Cthr (mword_of_int 23) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmj23).
    assert (Cs8 : E4 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5))
      by (rewrite (Cthr (mword_of_int 24) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmj24).
    assert (Cs9 : E4 !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5))
      by (rewrite (Cthr (mword_of_int 25) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmj25).
    assert (Cs10 : E4 !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5))
      by (rewrite (Cthr (mword_of_int 26) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmj26).
    assert (Cs11 : E4 !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5))
      by (rewrite (Cthr (mword_of_int 27) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmj27).
    iDestruct (cpu_own_transport CIDr CIDe5 0 eb pj C eb ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    (* the trap CSRs the caller lent are PER-HART, so they transport rather
       than frame: [emp] at [eb = true], and at [eb = false] the epilogue
       could not have moved the hart. *)
    iDestruct (trap_csrs_ext_transport CID0 CIDe5 eb pj ltac:(wp_next_chain)
                 with "Hext") as "Hext".
    (* SO DOES THE CLAIM'S COMPLEMENT, which is hart-indexed now that
       [cpu_claim] carries the hart tag. *)
    iDestruct (cpu_claim_ext_transport CID0 CIDe5 eb pj ltac:(wp_next_chain)
                 with "Hclmx") as "Hclmx".
    (* The handler resource needs no transport of its own any more: it rides
       inside [trap_csrs_ext], which was already transported above. *)
    iSpecialize ("Hcont" $! CIDe5 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E4 with "[%] Hcg Hcpu Hpc Hext Hclmx").
    unfold callee_saved. repeat split; assumption.
  Qed.

End SleepJoin.

Section ProofSleepBody.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_sleep_sconf 
      (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
    : wp_sleep_sconf_body γs j γl m av eb C.
  Proof.
    cbv beta delta [wp_sleep_sconf_body].
    intros pcE pj ret_tgt Hj Hgl Hav.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcpu #Htext Hpc #Hprocs #Hpanic Hext Hclmx Hcont".
    (* ONE INDEX.  [eb] is both the saved base enable and the resource index:
       at level 0 they are forced equal ([CpuOwn.cpu_own_eb_agree]), so there
       is nothing to derive and nothing to case-split on.  sleep's own
       [wp_next true] obligation is dischargeable at any hart regardless,
       since [pj = proc_addr j] is never [zero_reg]. *)
    (* ------------------------------------------------------------------ *)
    (* Prologue: 32-byte frame (push 4), save ra/s0/s1 (mirror myproc).   *)
    (* ------------------------------------------------------------------ *)
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HcspA0 : A0 !!! Regidx csp_rs1 = spd) by (rewrite /A0 upd_eq; reflexivity).
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (sli_00 with "Htext") as "Hi00".
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m av 4 eb ltac:(lia) Hpush
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with A0.
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & _)".
    iDestruct "S1c" as (vr24) "Hr24".
    iDestruct "S2c" as (vr16) "Hr16".
    iDestruct "S3c" as (vr8) "Hr8".
    iDestruct "S4c" as (vgap) "Hgap".
    assert (Hb1 : pa_stk sp0 1
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : pa_stk sp0 3
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* +0x02/0x04/0x06: c.sdsp ra/s0/s1 *)
    iPoseProof (sli_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sleep + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              A0 (av - 4)%nat vr24 eb with "Hcg Hpc Hi02 [Hr24]").
    { iEval (rewrite HcspA0 -Hb1). iExact "Hr24". }
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    iEval (rgne) in "Hr24".
    assert (Hpc04 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    iPoseProof (sli_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sleep + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              A0 (av - 4)%nat vr16 eb with "Hcg Hpc Hi04 [Hr16]").
    { iEval (rewrite HcspA0 -Hb2). iExact "Hr16". }
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    iEval (rgne) in "Hr16".
    assert (Hpc06 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    iPoseProof (sli_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sleep + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              A0 (av - 4)%nat vr8 eb with "Hcg Hpc Hi06 [Hr8]").
    { iEval (rewrite HcspA0 -Hb3). iExact "Hr8". }
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    iEval (rgne) in "Hr8".
    assert (Hpc08 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    (* +0x08: c.addi4spn s0,sp,32 *)
    iPoseProof (sli_08 with "Htext") as "Hi08".
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.sleep + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              A0 (av - 4)%nat eb
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (A1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0) with A1.
    assert (Hpc0a : add_vec_int (mword_of_int (KernelSyms.sleep + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x0a: jal myproc -> a0 = proc_addr j; noff/intena/cur_proc round.  *)
    (* ------------------------------------------------------------------ *)
    iPoseProof (sli_0a with "Htext") as "Hi0a".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sleep + 0x0a)) (mword_of_int 1 : mword 5) (mword_of_int 2095536 : mword 21)
              A1 (av - 4)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0a").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (A2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x0a) : mword 64) 4)]> A1).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x0a) : mword 64) 4)]> A1) with A2.
    assert (Hpcmp : add_vec (mword_of_int (KernelSyms.sleep + 0x0a) : mword 64) (sign_extend' 64 (mword_of_int 2095536 : mword 21))
                    = mword_of_int KernelSyms.myproc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcmp) in "Hpc".
    assert (HA2ra : A2 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.sleep + 0x0a) : mword 64) 4)
      by (rewrite /A2 upd_eq; reflexivity).
    iDestruct (cpu_own_transport CID CID6 0 eb pj C eb ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (Myproc.wp_myproc_sconf A2 (av - 4)%nat 0 eb pj C eb
              ltac:(lia)
              ltac:(lia)
              with "Hcg Hcpu Htext Hpc").
    iIntros (CID7 Hs7 ms mp) "%Hmsf Hcg Hcpu Hpc %Hmp".
    destruct Hmp as [Hcs_mp Ha0_mp].
    assert (Hpc0e : ret_pc (A2 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.sleep + 0x0e)) by (rewrite HA2ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0e) in "Hpc".
    (* +0x0e: c.mv s1,a0 : s1 := a0 = proc_addr j *)
    iPoseProof (sli_0e with "Htext") as "Hi0e".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sleep + 0x0e)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              mp (av - 4)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e").
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (B0 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (mp !!! Regidx (mword_of_int 10 : mword 5)))]> mp).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (mp !!! Regidx (mword_of_int 10 : mword 5)))]> mp) with B0.
    assert (Hpc10 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    (* +0x10: jal acquire *)
    iPoseProof (sli_10 with "Htext") as "Hi10".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sleep + 0x10)) (mword_of_int 1 : mword 5) (mword_of_int 2092170 : mword 21)
              B0 (av - 4)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi10").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (B1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x10) : mword 64) 4)]> B0).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x10) : mword 64) 4)]> B0) with B1.
    assert (Hpcaq : add_vec (mword_of_int (KernelSyms.sleep + 0x10) : mword 64) (sign_extend' 64 (mword_of_int 2092170 : mword 21))
                    = mword_of_int KernelSyms.acquire) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcaq) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x10: acquire(&p->lock) -- take proc j's lock.                     *)
    (* ------------------------------------------------------------------ *)
    assert (Ha0_B1 : B1 !!! Regidx (mword_of_int 10 : mword 5) = proc_addr j).
    { rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite /B0 upd_ne; [| vm_compute; discriminate]. exact Ha0_mp. }
    assert (HB1ra : B1 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.sleep + 0x10) : mword 64) 4)
      by (rewrite /B1 upd_eq; reflexivity).
    iPoseProof (procs_inv_lookup γs j γl Hgl with "Hprocs") as "#Hislock".
    iDestruct (cpu_own_transport CID7 CID9 0 eb pj C eb ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (Acquire.wp_acquire_sconf γl "proc"%string
              (proc_lock_res γs γl (proc_addr j)) B1 0 eb pj C (av - 4)%nat eb
              ltac:(lia)
              ltac:(lia)
              with "Hcg Hcpu Htext Hpc [Hislock] Hpanic").
    { iEval (rewrite Ha0_B1). iExact "Hislock". }
    (* FROM HERE TO THE RELEASE THE LOCK IS HELD, so the index is the literal
       [false] and every leaf collapses with [wp_next_off]. *)
    iIntros (CIDa Hsa ms2 macq) "%Hmsf2 Hcg Hpc %Hcs_acq Hlocked HR Hcpu [Hpay Hclmp]".
    assert (Hpc14 : ret_pc (B1 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.sleep + 0x14)) by (rewrite HB1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    (* unpack the lock resource.  THE PARK RECEIPT PAYS FOR THE STATE: the
       half this thread carries refutes the slot's [not_running] arm, so the
       state under the lock is RUNNING -- and the RUNNING arm is exactly the
       raw context cells sched may be about to want.  That is why sleep needs no
       [own_ctx] premise: it takes the cells from the lock. *)
    (* REJOIN THE CLAIM FIRST: acquire's [push_off] handed out the arm's
       share and the caller brought the complement, and exactly one of the
       two is [emp].  Taking it apart yields the state half AND the HART TAG
       half, and the tag half is what buys the take-out below. *)
    (* the caller's complement is at the ENTRY hart; transport it forward
       first ([emp] at [eb = true], and at [eb = false] the acquire could not
       have moved the hart).  It is hart-indexed because [cpu_claim] carries
       the hart tag. *)
    iDestruct (cpu_claim_ext_transport CID CIDa eb pj ltac:(wp_next_chain)
                 with "Hclmx") as "Hclmx".
    iDestruct (cpu_claim_ext_split eb (proc_addr j)) as "[Hcj _]".
    iDestruct ("Hcj" with "[$Hclmp $Hclmx]") as "Hclm".
    iDestruct (cpu_claim_elim j Hj with "Hclm") as "[Hclm Htag]".
    (* THE TAKE-OUT.  Presenting the tag half at the acquired lock proves the
       state under it is RUNNING -- at any other state the lock holds the
       WHOLE tag and 1 + 1/2 does not validate -- and collapses the RUNNING
       arm's existential hart to this one.  Out come the whole tag, the raw
       context cells sched is about to want, and THIS hart's parked scheduler
       record.  That is why sleep needs no [own_ctx] premise and no global
       invariant: it takes all three from the lock it just took. *)
    iDestruct (proc_lock_res_elim γs γl (proc_addr j) with "HR") as (st0 ch0) "(Hstate & Hpg & Hchan & Hpub & Hslot)".
    iDestruct (proc_slots_running γs j CIDa st0 Hj with "Htag Hslot")
      as "(-> & Htag & Hown & Hvc)".
    (* the claim's half #2 joins the lock's tie into the WHOLE mirror, which
       is what the store to p->state below is allowed to move. *)
    iDestruct (pstate_at_intro j (1/2) RUNNING Hj with "Hclm") as "Hclm".
    iDestruct (pstate_whole_split (proc_addr j) RUNNING) as "[_ Hwe]".
    iDestruct ("Hwe" with "[Hpg Hclm]") as "Hpg".
    { rewrite unclaimed_RUNNING. iFrame "Hpg Hclm". }
    (* the s1 / sp values thread (callee-saved) through myproc and acquire;
       both arms need them, so they are read off the [set]-chain once. *)
    assert (Hs1_macq : macq !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j)).
    { rewrite (callee_saved_lookup Hcs_acq (mword_of_int 9) ltac:(vm_compute; reflexivity)).
      rewrite /B1 upd_ne; [| vm_compute; discriminate]. rewrite /B0 upd_eq Ha0_mp. reflexivity. }
    assert (Hsp_macq : macq !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hcs_acq csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /B1 upd_ne; [| vm_compute; discriminate]. rewrite /B0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_mp csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /A2 upd_ne; [| vm_compute; discriminate]. rewrite /A1 upd_ne; [| vm_compute; discriminate].
      exact HcspA0. }
    assert (Hthr_acq : forall c : mword 5, is_cs_idx c = true ->
      Regidx c ≠ Regidx (mword_of_int 1) -> Regidx c ≠ Regidx (mword_of_int 8) ->
      Regidx c ≠ Regidx (mword_of_int 9) -> Regidx c ≠ Regidx csp_rs1 ->
      macq !!! Regidx c = m !!! Regidx c).
    { intros c Hcs H1 H8 H9 Hsp.
      rewrite (callee_saved_lookup Hcs_acq c Hcs).
      rewrite /B1 upd_ne; [| exact H1]. rewrite /B0 upd_ne; [| exact H9].
      rewrite (callee_saved_lookup Hcs_mp c Hcs).
      rewrite /A2 upd_ne; [| exact H1]. rewrite /A1 upd_ne; [| exact H8].
      rewrite /A0 upd_ne; [| exact Hsp]. reflexivity. }
    (* the three saved frame cells, re-addressed at [pa_stk sp0 k] -- likewise
       common to both arms, and untouched by everything below. *)
    assert (HraA0 : A0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0A0 : A0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1A0 : A0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HcspA0 HraA0 -Hb1) in "Hr24".
    iEval (rewrite HcspA0 Hs0A0 -Hb2) in "Hr16".
    iEval (rewrite HcspA0 Hs1A0 -Hb3) in "Hr8".
    (* THE TRAP-CSR SET, ASSEMBLED ONCE.  Half comes from acquire's own
       [arm_pay 0 eb _] (the set at [eb = true], nothing at [eb = false]) and
       the other half is the [trap_csrs_ext eb] sleep's caller brought for
       exactly this reason; the lent half is at the ENTRY hart, so it is
       transported forward first ([emp] at [eb = true], and at [eb = false]
       nothing above could have moved the hart).  BOTH arms want the whole
       set: the park arm hands it across the swtch, the no-park arm carries
       it straight into the release. *)
    iDestruct (trap_csrs_ext_transport CID CIDa eb pj ltac:(wp_next_chain)
                 with "Hext") as "Hext".
    iAssert trap_csrs with "[Hpay Hext]" as "Htc".
    { iEval (rewrite -(trap_csrs_ext_split eb)). iFrame "Hpay Hext". }
    (* ------------------------------------------------------------------ *)
    (* +0x14: c.ld a5,32(s1) -- a5 := p->chan, read under p->lock.         *)
    (* ------------------------------------------------------------------ *)
    assert (Hrec_chan : add_vec (rget macq (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 32 : mword 12))
                        = p_chan (proc_addr j)).
    { rgne. rewrite Hs1_macq add_vec_zero_l. unfold p_chan, chan_off.
      assert (H32 : sign_extend' 64 (mword_of_int 32 : mword 12) = (mword_of_int 32 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite H32. reflexivity. }
    iPoseProof (sli_14 with "Htext") as "Hi14".
    iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.sleep + 0x14)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
              (mword_of_int 32 : mword 12) macq (trap_res eb + (av - 4))%nat ch0 false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [Hchan]").
    { iEval (rewrite Hrec_chan). iExact "Hchan". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hchan".
    iEval (rewrite Hrec_chan) in "Hchan".
    set (L0 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg ch0]> macq).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg ch0]> macq) with L0.
    assert (Hpc16 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    (* the two register facts that survive the load, for either arm. *)
    assert (Hsp_L0 : L0 !!! Regidx csp_rs1 = spd)
      by (rewrite /L0 upd_ne; [exact Hsp_macq | vm_compute; discriminate]).
    assert (Hs1_L0 : L0 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j))
      by (rewrite /L0 upd_ne; [exact Hs1_macq | vm_compute; discriminate]).
    assert (Hthr_L0 : forall c : mword 5, is_cs_idx c = true ->
      Regidx c ≠ Regidx (mword_of_int 1) -> Regidx c ≠ Regidx (mword_of_int 8) ->
      Regidx c ≠ Regidx (mword_of_int 9) -> Regidx c ≠ Regidx (mword_of_int 15) ->
      Regidx c ≠ Regidx csp_rs1 -> L0 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs H1 H8 H9 H15 Hsp. rewrite /L0 upd_ne; [| exact H15].
      exact (Hthr_acq c Hcs H1 H8 H9 Hsp). }
    (* sleep's own [wp_next true pj] obligation transports to ANY hart: the
       index is the LITERAL [true] (a parking function's always is), so the
       only pinning condition left is [pj = zero_reg], which
       [proc_addr_nonzero] refutes.  Both arms re-anchor ["Hcont"] with this
       and [WpNext.wp_next_retarget] -- the park arm at the DISPATCHING hart,
       the no-park arm at the one it never left. *)
    assert (Hrt : forall CIDx : CpuId, true = false \/ proc_addr j = zero_reg ->
                  (CIDx : CPU) = (CID : CPU)).
    { intros CIDx [Hf | Hz]; [discriminate | exfalso; exact (proc_addr_nonzero j Hj Hz)]. }
    (* ------------------------------------------------------------------ *)
    (* +0x16: c.beqz a5,+0x20 -- THE GUARD, and the only thing that makes   *)
    (* sleep more than yield: a wakeup that landed between the caller's     *)
    (* sleep_prepare and here cleared p->chan, and then this call must NOT  *)
    (* park (that is the lost-wakeup race).  Both arms rejoin at +0x20.     *)
    (* ------------------------------------------------------------------ *)
    iPoseProof (sli_16 with "Htext") as "Hi16".
    destruct (eq_vec (rget L0 (mword_of_int 15 : mword 5)) zero_reg) eqn:Hbz.
    - (* ================================================================= *)
      (* p->chan == 0: THE NO-PARK ARM.  Branch taken straight to +0x20 -- *)
      (* nothing is written, nothing is handed across a swtch, and the      *)
      (* join is reached on the hart we are already on.                     *)
      (* ================================================================= *)
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.sleep + 0x16)) (mword_of_int 5 : mword 8)
                (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5) L0 (trap_res eb + (av - 4))%nat false
                creg_c7 ltac:(vm_compute; discriminate) Hbz ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi16").
      (* the leaf's continuation sits under a [▷]; [bi.later_intro] takes it
         off the GOAL without walking the context, which matters because the
         parked-scheduler record must stay [▷]'d for the lock. *)
      iApply bi.later_intro.
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      assert (Htgt20 : add_vec (mword_of_int (KernelSyms.sleep + 0x16) : mword 64)
                         (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 5 : mword 8) ('b"0"))))
                       = mword_of_int (KernelSyms.sleep + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt20) in "Hpc".
      assert (HL18 : L0 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5))
        by (apply Hthr_L0; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
      assert (HL19 : L0 !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5))
        by (apply Hthr_L0; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
      assert (HL20 : L0 !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5))
        by (apply Hthr_L0; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
      assert (HL21 : L0 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5))
        by (apply Hthr_L0; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
      assert (HL22 : L0 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5))
        by (apply Hthr_L0; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
      assert (HL23 : L0 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5))
        by (apply Hthr_L0; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
      assert (HL24 : L0 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5))
        by (apply Hthr_L0; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
      assert (HL25 : L0 !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5))
        by (apply Hthr_L0; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
      assert (HL26 : L0 !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5))
        by (apply Hthr_L0; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
      assert (HL27 : L0 !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5))
        by (apply Hthr_L0; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
      iApply (sleep_join (CID0 := CIDa) γs j γl ch0 m L0 av eb C sp0 spd vgap
                ltac:(lia) Hj ltac:(reflexivity) ltac:(reflexivity)
                Hsp_L0 Hs1_L0
                HL18 HL19 HL20 HL21 HL22 HL23 HL24 HL25 HL26 HL27
                with "Htext Hislock Hcg Hpc [Hlocked Hstate Hpg Hchan Hpub] Htc Hcpu Hown Htag Hvc
                      Hr24 Hr16 Hr8 Hgap [Hcont]").
      { rewrite /proc_held. iFrame "Hlocked Hstate Hpg Hchan Hpub". }
      iApply (wp_next_retarget _ _ _ _ _ (Hrt CIDa) with "Hcont").
    - (* ================================================================= *)
      (* p->chan <> 0: THE PARK ARM.  Fall through to +0x18, mark the proc  *)
      (* SLEEPING and hand the parking payload to sched(); the join is      *)
      (* reached on whichever hart dispatched the process again.            *)
      (* ================================================================= *)
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.sleep + 0x16)) (mword_of_int 5 : mword 8)
                (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5) L0 (trap_res eb + (av - 4))%nat false
                creg_c7 ltac:(vm_compute; discriminate) Hbz
                with "Hcg Hpc Hi16").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      assert (Hpc18 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc18) in "Hpc".
      (* +0x18: c.li a5,2 *)
      iPoseProof (sli_18 with "Htext") as "Hi18".
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sleep + 0x18)) (mword_of_int 15 : mword 5) (mword_of_int 2 : mword 6)
                (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))) L0 (trap_res eb + (av - 4))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
                with "Hcg Hpc Hi18").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      set (C0 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))]> L0).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))]> L0) with C0.
      assert (Hpc1a : add_vec_int (mword_of_int (KernelSyms.sleep + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc1a) in "Hpc".
      (* s1 still holds p, so p->state's address reconciles to p_state pj. *)
      assert (HC0s1 : C0 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j))
        by (rewrite /C0 upd_ne; [exact Hs1_L0 | vm_compute; discriminate]).
      assert (Hrec_state : add_vec (C0 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 24 : mword 12))
                           = p_state (proc_addr j)).
      { rewrite HC0s1 add_vec_zero_l. unfold p_state, state_off.
        assert (H24 : sign_extend' 64 (mword_of_int 24 : mword 12) = (mword_of_int 24 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
        rewrite H24. reflexivity. }
      assert (Hsv : trunc32 (C0 !!! Regidx (mword_of_int 15 : mword 5)) = SLEEPING).
      { rewrite /C0 upd_eq. unfold SLEEPING. exact sl_sleeping. }
      (* the [rget]-spelled twins the store leaf's [pa] / [storeval] want. *)
      assert (Hrec_state_g : add_vec (rget C0 (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 24 : mword 12))
                             = p_state (proc_addr j)) by (rgne; exact Hrec_state).
      assert (Hsv_g : trunc32 (rget C0 (mword_of_int 15 : mword 5)) = SLEEPING)
        by (rgne; exact Hsv).
      (* +0x1a: c.sw a5,24(s1) : p->state := SLEEPING *)
      iPoseProof (sli_1a with "Htext") as "Hi1a".
      iApply (wp_csw_s_sconf (mword_of_int (KernelSyms.sleep + 0x1a)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
                (mword_of_int 24 : mword 12) C0 (trap_res eb + (av - 4))%nat RUNNING false
                with "Hcg Hpc Hi1a [Hstate]").
      { iEval (rewrite Hrec_state_g). iExact "Hstate". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hstate".
      iEval (rewrite Hrec_state_g Hsv_g) in "Hstate".
      assert (Hpc1c : add_vec_int (mword_of_int (KernelSyms.sleep + 0x1a) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc1c) in "Hpc".
      (* +0x1c: jal sched *)
      iPoseProof (sli_1c with "Htext") as "Hi1c".
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sleep + 0x1c)) (mword_of_int 1 : mword 5) (mword_of_int 2096832 : mword 21)
                C0 (trap_res eb + (av - 4))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi1c").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      set (C1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x1c) : mword 64) 4)]> C0).
      change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x1c) : mword 64) 4)]> C0) with C1.
      assert (Hpcsd : add_vec (mword_of_int (KernelSyms.sleep + 0x1c) : mword 64) (sign_extend' 64 (mword_of_int 2096832 : mword 21))
                      = mword_of_int KernelSyms.sched) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpcsd) in "Hpc".
      (* ---------------------------------------------------------------- *)
      (* +0x1c: sched() -- park; resumes with the process dispatched again.*)
      (* ---------------------------------------------------------------- *)
      assert (HC1ra : C1 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.sleep + 0x1c) : mword 64) 4)
        by (rewrite /C1 upd_eq; reflexivity).
      iDestruct (cpu_own_ctx_take with "Hcpu") as "[HC Hcpuemp]".
      iApply fupd_wp.
      (* the store to p->state above moved the CELL; the mirror follows here,
         which the whole variable permits with no side condition.  This is the
         claim being RETURNED: SLEEPING is unclaimed, so after the park the
         lock owns both halves again. *)
      iMod (pstate_whole_update (proc_addr j) RUNNING SLEEPING with "Hpg") as "Hpg".
      iModIntro.
      iApply (Sched.wp_sched_sconf γs j γl SLEEPING ch0 C1 (trap_res eb + (av - 4))%nat eb
                Hj Hgl (park_ok_SLEEPING) ltac:(lia)
                with "Hcg Htext Hpc Hprocs [Hlocked Hstate Hpg Hchan Hpub] [] Htc Hcpuemp Hown Htag Hvc").
      { rewrite /proc_held. iFrame "Hlocked Hstate Hpg Hchan Hpub". }
      (* a SLEEPING park owes the slot nothing beyond its record. *)
      { iApply (park_pay_needs_ctx (proc_addr j) SLEEPING needs_ctx_SLEEPING). }
      (* SCHED RETURNS ON HART [CIDs].  Everything below runs there, inside
         [sleep_join] at [(CID0 := CIDs)]. *)
      iIntros (CIDs Hss msch ch') "%Hcs_sch Hcg Hpc Hheld' Htc' Hcpuemp Hown' Htag' Hvc'".
      (* what the join half needs about [msch], read off this tower. *)
      assert (Hsp_msch : msch !!! Regidx csp_rs1 = spd).
      { rewrite (callee_saved_lookup Hcs_sch csp_rs1 ltac:(vm_compute; reflexivity)).
        rewrite /C1 upd_ne; [| vm_compute; discriminate]. rewrite /C0 upd_ne; [| vm_compute; discriminate].
        exact Hsp_L0. }
      assert (Hs1_msch : msch !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j)).
      { rewrite (callee_saved_lookup Hcs_sch (mword_of_int 9) ltac:(vm_compute; reflexivity)).
        rewrite /C1 upd_ne; [| vm_compute; discriminate]. exact HC0s1. }
      assert (Hthr : forall c : mword 5, is_cs_idx c = true ->
        Regidx c ≠ Regidx (mword_of_int 1) -> Regidx c ≠ Regidx (mword_of_int 8) ->
        Regidx c ≠ Regidx (mword_of_int 9) -> Regidx c ≠ Regidx (mword_of_int 15) ->
        Regidx c ≠ Regidx csp_rs1 ->
        msch !!! Regidx c = m !!! Regidx c).
      { intros c Hcs H1 H8 H9 H15 Hsp.
        rewrite (callee_saved_lookup Hcs_sch c Hcs).
        rewrite /C1 upd_ne; [| exact H1]. rewrite /C0 upd_ne; [| exact H15].
        exact (Hthr_L0 c Hcs H1 H8 H9 H15 Hsp). }
      assert (Hmsch18 : msch !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5))
        by (apply Hthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
      assert (Hmsch19 : msch !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5))
        by (apply Hthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
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
      (* the pc: sched hands back [ret_pc (C1 !!! ra)] = KernelSyms.sleep + 0x20 *)
      assert (Hpc20 : ret_pc (C1 !!! Regidx (mword_of_int 1 : mword 5))
                      = mword_of_int (KernelSyms.sleep + 0x20)) by (rewrite HC1ra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc20) in "Hpc".
      (* re-inject the opaque context-slot payload into the returned bundle. *)
      iAssert (cpu_own 1 eb (proc_addr j) C false) with "[Hcpuemp HC]" as "Hcpu".
      { iApply (cpu_own_ctx_swap with "Hcpuemp"). iIntros "_". iExact "HC". }
      (* ONE application of the join half, at the DISPATCHING hart. *)
      iApply (sleep_join (CID0 := CIDs) γs j γl ch' m msch av eb C sp0 spd vgap
                ltac:(lia) Hj ltac:(reflexivity) ltac:(reflexivity)
                Hsp_msch Hs1_msch
                Hmsch18 Hmsch19 Hmsch20 Hmsch21 Hmsch22 Hmsch23 Hmsch24 Hmsch25 Hmsch26 Hmsch27
                with "Htext Hislock Hcg Hpc Hheld' Htc' Hcpu Hown' Htag' Hvc' Hr24 Hr16 Hr8 Hgap
                      [Hcont]").
      iApply (wp_next_retarget _ _ _ _ _ (Hrt CIDs) with "Hcont").
  Qed.

  (* ===================================================================== *)
  (* sleep ENTERED WITH A SPINLOCK HELD (SpecSleep.v, ROUTE B lemma 2).     *)
  (*                                                                       *)
  (* The whole walk runs at the literal [false]: entry index [false], and   *)
  (* [cpu_own (S n)] with [n >= 0] means the interior release pops to       *)
  (* [S n >= 1], so nothing re-enables and the hart never moves.  Every     *)
  (* leaf therefore collapses with [wp_next_off_intro] and no hart binder   *)
  (* appears anywhere -- which is also why this lemma needs no [wp_next]    *)
  (* and no trap CSRs.                                                     *)
  (*                                                                       *)
  (* THE LOCK RESOURCE IS OPENED FOR ITS CELLS ONLY.  [wp_sleep_sconf]      *)
  (* refutes the slot's [not_running] arm with the hart tag, so as to learn *)
  (* [st0 = RUNNING] and take the parked record out for the swtch; none of  *)
  (* that is needed here.  The park arm never comes back, so it may write   *)
  (* [p->state] at an arbitrary [st0] and walk away from the slot; the      *)
  (* no-park arm touches nothing and hands the slot straight back to the    *)
  (* release.  Hence no [arm_pay] plumbing, no [cpu_claim], no hart tag --  *)
  (* the premise set is correspondingly smaller.                           *)
  (* ===================================================================== *)
  Lemma wp_sleep_nested
      (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (n : nat)
    : wp_sleep_nested_body γs j γl m av eb C n.
  Proof.
    cbv beta delta [wp_sleep_nested_body].
    intros pcE pj ret_tgt Hj Hgl Hav Hn.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcpu #Htext Hpc #Hprocs #Hpanic Hcont".
    (* ------------------------------------------------------------------ *)
    (* Prologue: 32-byte frame (push 4), save ra/s0/s1.                    *)
    (* ------------------------------------------------------------------ *)
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    set (N0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HcspN0 : N0 !!! Regidx csp_rs1 = spd) by (rewrite /N0 upd_eq; reflexivity).
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (sli_00 with "Htext") as "Hi00".
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m av 4 false ltac:(lia) Hpush
              with "Hcg Hpc Hi00").
    iApply wp_next_off_intro.
    iIntros "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with N0.
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & _)".
    iDestruct "S1c" as (vr24) "Hr24".
    iDestruct "S2c" as (vr16) "Hr16".
    iDestruct "S3c" as (vr8) "Hr8".
    iDestruct "S4c" as (vgap) "Hgap".
    assert (Hb1 : pa_stk sp0 1
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : pa_stk sp0 3
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* +0x02/0x04/0x06: c.sdsp ra/s0/s1 *)
    iPoseProof (sli_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sleep + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              N0 (av - 4)%nat vr24 false with "Hcg Hpc Hi02 [Hr24]").
    { iEval (rewrite HcspN0 -Hb1). iExact "Hr24". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr24".
    iEval (rgne) in "Hr24".
    assert (Hpc04 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    iPoseProof (sli_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sleep + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              N0 (av - 4)%nat vr16 false with "Hcg Hpc Hi04 [Hr16]").
    { iEval (rewrite HcspN0 -Hb2). iExact "Hr16". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr16".
    iEval (rgne) in "Hr16".
    assert (Hpc06 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    iPoseProof (sli_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sleep + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              N0 (av - 4)%nat vr8 false with "Hcg Hpc Hi06 [Hr8]").
    { iEval (rewrite HcspN0 -Hb3). iExact "Hr8". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hr8".
    iEval (rgne) in "Hr8".
    assert (Hpc08 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    (* +0x08: c.addi4spn s0,sp,32 *)
    iPoseProof (sli_08 with "Htext") as "Hi08".
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.sleep + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              N0 (av - 4)%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (N1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (N0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> N0).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (N0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> N0) with N1.
    assert (Hpc0a : add_vec_int (mword_of_int (KernelSyms.sleep + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x0a: jal myproc -> a0 = proc_addr j, at noff = S n.               *)
    (* ------------------------------------------------------------------ *)
    iPoseProof (sli_0a with "Htext") as "Hi0a".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sleep + 0x0a)) (mword_of_int 1 : mword 5) (mword_of_int 2095536 : mword 21)
              N1 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0a").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (N2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x0a) : mword 64) 4)]> N1).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x0a) : mword 64) 4)]> N1) with N2.
    assert (Hpcmp : add_vec (mword_of_int (KernelSyms.sleep + 0x0a) : mword 64) (sign_extend' 64 (mword_of_int 2095536 : mword 21))
                    = mword_of_int KernelSyms.myproc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcmp) in "Hpc".
    assert (HN2ra : N2 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.sleep + 0x0a) : mword 64) 4)
      by (rewrite /N2 upd_eq; reflexivity).
    iApply (Myproc.wp_myproc_sconf N2 (av - 4)%nat (S n) eb pj C false
              ltac:(lia)
              ltac:(lia)
              with "Hcg Hcpu Htext Hpc").
    iApply wp_next_off_intro.
    iIntros (ms mp) "%Hmsf Hcg Hcpu Hpc %Hmp".
    destruct Hmp as [Hcs_mp Ha0_mp].
    assert (Hpc0e : ret_pc (N2 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.sleep + 0x0e)) by (rewrite HN2ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0e) in "Hpc".
    (* +0x0e: c.mv s1,a0 *)
    iPoseProof (sli_0e with "Htext") as "Hi0e".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sleep + 0x0e)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              mp (av - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (N3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (mp !!! Regidx (mword_of_int 10 : mword 5)))]> mp).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (mp !!! Regidx (mword_of_int 10 : mword 5)))]> mp) with N3.
    assert (Hpc10 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    (* +0x10: jal acquire *)
    iPoseProof (sli_10 with "Htext") as "Hi10".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sleep + 0x10)) (mword_of_int 1 : mword 5) (mword_of_int 2092170 : mword 21)
              N3 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi10").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (N4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x10) : mword 64) 4)]> N3).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x10) : mword 64) 4)]> N3) with N4.
    assert (Hpcaq : add_vec (mword_of_int (KernelSyms.sleep + 0x10) : mword 64) (sign_extend' 64 (mword_of_int 2092170 : mword 21))
                    = mword_of_int KernelSyms.acquire) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcaq) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x10: acquire(&p->lock) -- THE SECOND LOCK: noff S n -> S (S n).   *)
    (* ------------------------------------------------------------------ *)
    assert (Ha0_N4 : N4 !!! Regidx (mword_of_int 10 : mword 5) = proc_addr j).
    { rewrite /N4 upd_ne; [| vm_compute; discriminate].
      rewrite /N3 upd_ne; [| vm_compute; discriminate]. exact Ha0_mp. }
    assert (HN4ra : N4 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.sleep + 0x10) : mword 64) 4)
      by (rewrite /N4 upd_eq; reflexivity).
    iPoseProof (procs_inv_lookup γs j γl Hgl with "Hprocs") as "#Hislock".
    iApply (Acquire.wp_acquire_sconf γl "proc"%string
              (proc_lock_res γs γl (proc_addr j)) N4 (S n) eb pj C (av - 4)%nat false
              ltac:(lia)
              ltac:(lia)
              with "Hcg Hcpu Htext Hpc [Hislock] Hpanic").
    { iEval (rewrite Ha0_N4). iExact "Hislock". }
    iApply wp_next_off_intro.
    iIntros (ms2 macq) "%Hmsf2 Hcg Hpc %Hcs_acq Hlocked HR Hcpu Hpay".
    assert (Hpc14 : ret_pc (N4 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.sleep + 0x14)) by (rewrite HN4ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    (* the lock resource, FOR ITS CELLS ONLY -- see the header. *)
    iDestruct (proc_lock_res_elim γs γl (proc_addr j) with "HR") as (st0 ch0) "(Hstate & Hpg & Hchan & Hpub & Hslot)".
    (* the register facts both arms need, read off the [set]-chain once. *)
    assert (Hs1_macq : macq !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j)).
    { rewrite (callee_saved_lookup Hcs_acq (mword_of_int 9) ltac:(vm_compute; reflexivity)).
      rewrite /N4 upd_ne; [| vm_compute; discriminate]. rewrite /N3 upd_eq Ha0_mp. reflexivity. }
    assert (Hsp_macq : macq !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hcs_acq csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /N4 upd_ne; [| vm_compute; discriminate]. rewrite /N3 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_mp csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /N2 upd_ne; [| vm_compute; discriminate]. rewrite /N1 upd_ne; [| vm_compute; discriminate].
      exact HcspN0. }
    assert (Hthr_acq : forall c : mword 5, is_cs_idx c = true ->
      Regidx c ≠ Regidx (mword_of_int 1) -> Regidx c ≠ Regidx (mword_of_int 8) ->
      Regidx c ≠ Regidx (mword_of_int 9) -> Regidx c ≠ Regidx csp_rs1 ->
      macq !!! Regidx c = m !!! Regidx c).
    { intros c Hcs H1 H8 H9 Hsp.
      rewrite (callee_saved_lookup Hcs_acq c Hcs).
      rewrite /N4 upd_ne; [| exact H1]. rewrite /N3 upd_ne; [| exact H9].
      rewrite (callee_saved_lookup Hcs_mp c Hcs).
      rewrite /N2 upd_ne; [| exact H1]. rewrite /N1 upd_ne; [| exact H8].
      rewrite /N0 upd_ne; [| exact Hsp]. reflexivity. }
    (* the three saved frame cells, re-addressed at [pa_stk sp0 k]. *)
    assert (HraN0 : N0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /N0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0N0 : N0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /N0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1N0 : N0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /N0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HcspN0 HraN0 -Hb1) in "Hr24".
    iEval (rewrite HcspN0 Hs0N0 -Hb2) in "Hr16".
    iEval (rewrite HcspN0 Hs1N0 -Hb3) in "Hr8".
    (* ------------------------------------------------------------------ *)
    (* +0x14: c.ld a5,32(s1) -- a5 := p->chan, read under p->lock.         *)
    (* ------------------------------------------------------------------ *)
    assert (Hrec_chan : add_vec (rget macq (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 32 : mword 12))
                        = p_chan (proc_addr j)).
    { rgne. rewrite Hs1_macq add_vec_zero_l. unfold p_chan, chan_off.
      assert (H32 : sign_extend' 64 (mword_of_int 32 : mword 12) = (mword_of_int 32 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite H32. reflexivity. }
    iPoseProof (sli_14 with "Htext") as "Hi14".
    iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.sleep + 0x14)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
              (mword_of_int 32 : mword 12) macq (av - 4)%nat ch0 false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [Hchan]").
    { iEval (rewrite Hrec_chan). iExact "Hchan". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hchan".
    iEval (rewrite Hrec_chan) in "Hchan".
    set (N5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg ch0]> macq).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg ch0]> macq) with N5.
    assert (Hpc16 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    assert (Hsp_N5 : N5 !!! Regidx csp_rs1 = spd)
      by (rewrite /N5 upd_ne; [exact Hsp_macq | vm_compute; discriminate]).
    assert (Hs1_N5 : N5 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j))
      by (rewrite /N5 upd_ne; [exact Hs1_macq | vm_compute; discriminate]).
    assert (Hthr_N5 : forall c : mword 5, is_cs_idx c = true ->
      Regidx c ≠ Regidx (mword_of_int 1) -> Regidx c ≠ Regidx (mword_of_int 8) ->
      Regidx c ≠ Regidx (mword_of_int 9) -> Regidx c ≠ Regidx (mword_of_int 15) ->
      Regidx c ≠ Regidx csp_rs1 -> N5 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs H1 H8 H9 H15 Hsp. rewrite /N5 upd_ne; [| exact H15].
      exact (Hthr_acq c Hcs H1 H8 H9 Hsp). }
    (* ------------------------------------------------------------------ *)
    (* +0x16: c.beqz a5,+0x20 -- and here the two arms genuinely differ:    *)
    (* one panics in sched, the other returns.  See the spec's header.     *)
    (* ------------------------------------------------------------------ *)
    iPoseProof (sli_16 with "Htext") as "Hi16".
    destruct (eq_vec (rget N5 (mword_of_int 15 : mword 5)) zero_reg) eqn:Hbz.
    - (* ================================================================= *)
      (* p->chan == 0: NO PARK.  Release p->lock and return -- noff is back *)
      (* at [S n] and the caller's continuation takes it from there.        *)
      (* ================================================================= *)
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.sleep + 0x16)) (mword_of_int 5 : mword 8)
                (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5) N5 (av - 4)%nat false
                creg_c7 ltac:(vm_compute; discriminate) Hbz ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi16").
      iApply bi.later_intro.
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      assert (Htgt20 : add_vec (mword_of_int (KernelSyms.sleep + 0x16) : mword 64)
                         (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 5 : mword 8) ('b"0"))))
                       = mword_of_int (KernelSyms.sleep + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt20) in "Hpc".
      (* +0x20: c.mv a0,s1 *)
      iPoseProof (sli_20 with "Htext") as "Hi20".
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sleep + 0x20)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                N5 (av - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi20").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      iEval (repeat rgne) in "Hcg".
      set (N6 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (add_vec zero_reg (N5 !!! Regidx (mword_of_int 9 : mword 5)))]> N5).
      change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
          (add_vec zero_reg (N5 !!! Regidx (mword_of_int 9 : mword 5)))]> N5) with N6.
      assert (Hpc22 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x20) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc22) in "Hpc".
      (* +0x22: jal release *)
      iPoseProof (sli_22 with "Htext") as "Hi22".
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sleep + 0x22)) (mword_of_int 1 : mword 5) (mword_of_int 2092288 : mword 21)
                N6 (av - 4)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi22").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      set (N7 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x22) : mword 64) 4)]> N6).
      change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x22) : mword 64) 4)]> N6) with N7.
      assert (Hpcrl : add_vec (mword_of_int (KernelSyms.sleep + 0x22) : mword 64) (sign_extend' 64 (mword_of_int 2092288 : mword 21))
                      = mword_of_int KernelSyms.release) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpcrl) in "Hpc".
      assert (Ha0_N7 : N7 !!! Regidx (mword_of_int 10 : mword 5) = proc_addr j).
      { rewrite /N7 upd_ne; [| vm_compute; discriminate].
        rewrite /N6 upd_eq Hs1_N5 !add_vec_zero_l. reflexivity. }
      assert (HN7ra : N7 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.sleep + 0x22) : mword 64) 4)
        by (rewrite /N7 upd_eq; reflexivity).
      assert (Hlka : add_vec (N7 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = proc_addr j).
      { rewrite Ha0_N7.
        assert (H0 : sign_extend' 64 (mword_of_int 0 : mword 12) = (mword_of_int 0 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
        rewrite H0. apply kv_addv_zero. }
      (* the lock resource goes back EXACTLY as it came out: this arm wrote
         nothing, so the slot -- whatever arm it was in -- is untouched. *)
      iAssert (proc_lock_res γs γl (proc_addr j)) with "[Hstate Hpg Hchan Hpub Hslot]" as "HR2".
      { rewrite /proc_lock_res. iExists st0, ch0. iFrame "Hstate Hpg Hchan Hpub Hslot". }
      iApply (Release.wp_release_sconf γl (proc_addr j) "proc"%string
                (proc_lock_res γs γl (proc_addr j)) N7 (S n) eb pj C (av - 4)%nat
                Hlka
                ltac:(lia)
                with "Hcg Htext Hpc Hislock Hlocked HR2 Hcpu Hpay").
      iApply wp_next_off_intro.
      iIntros (mrel) "Hcg Hpc %Hcs_rel Hcpu".
      assert (Hpc26 : ret_pc (N7 !!! Regidx (mword_of_int 1 : mword 5))
                      = mword_of_int (KernelSyms.sleep + 0x26)) by (rewrite HN7ra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc26) in "Hpc".
      (* ---------------------------------------------------------------- *)
      (* Epilogue: restore ra/s0/s1, pop the frame, return.                *)
      (* ---------------------------------------------------------------- *)
      assert (Hcsp_mrel : mrel !!! Regidx csp_rs1 = spd).
      { rewrite (callee_saved_lookup Hcs_rel csp_rs1 ltac:(vm_compute; reflexivity)).
        rewrite /N7 upd_ne; [| vm_compute; discriminate]. rewrite /N6 upd_ne; [| vm_compute; discriminate].
        exact Hsp_N5. }
      iEval (rewrite Hb1) in "Hr24".
      iEval (rewrite Hb2) in "Hr16".
      iEval (rewrite Hb3) in "Hr8".
      (* +0x26: c.ldsp ra,24 *)
      iPoseProof (sli_26 with "Htext") as "Hi26".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sleep + 0x26)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
                mrel (av - 4)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi26 [Hr24]").
      { iEval (rewrite Hcsp_mrel). iExact "Hr24". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hr24".
      set (P1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mrel).
      change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mrel) with P1.
      assert (Hpc28 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc28) in "Hpc".
      assert (HcspP1 : P1 !!! Regidx csp_rs1 = spd)
        by (rewrite /P1 upd_ne; [exact Hcsp_mrel | vm_compute; discriminate]).
      (* +0x28: c.ldsp s0,16 *)
      iPoseProof (sli_28 with "Htext") as "Hi28".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sleep + 0x28)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
                P1 (av - 4)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi28 [Hr16]").
      { iEval (rewrite HcspP1). iExact "Hr16". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hr16".
      set (P2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> P1).
      change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> P1) with P2.
      assert (Hpc2a : add_vec_int (mword_of_int (KernelSyms.sleep + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc2a) in "Hpc".
      assert (HcspP2 : P2 !!! Regidx csp_rs1 = spd)
        by (rewrite /P2 upd_ne; [exact HcspP1 | vm_compute; discriminate]).
      (* +0x2a: c.ldsp s1,8 *)
      iPoseProof (sli_2a with "Htext") as "Hi2a".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sleep + 0x2a)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
                P2 (av - 4)%nat (m !!! Regidx (mword_of_int 9 : mword 5)) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi2a [Hr8]").
      { iEval (rewrite HcspP2). iExact "Hr8". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hr8".
      set (P3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> P2).
      change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> P2) with P3.
      assert (Hpc2c : add_vec_int (mword_of_int (KernelSyms.sleep + 0x2a) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc2c) in "Hpc".
      assert (HcspP3 : P3 !!! Regidx csp_rs1 = spd)
        by (rewrite /P3 upd_ne; [exact HcspP2 | vm_compute; discriminate]).
      (* +0x2c: c.addi16sp sp,32 -- pop the frame *)
      set (P4 := <[Regidx csp_rs1 := regval_into_reg
          (add_vec (P3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P3).
      assert (Hsp0up : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
      { rewrite /spd po_addv_assoc.
        assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                              (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = mword_of_int 0)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite HAB. apply avi0. }
      assert (HP4sp : P4 !!! Regidx csp_rs1 = sp0).
      { rewrite /P4 upd_eq HcspP3. exact Hsp0up. }
      assert (Hwv : add_vec (P3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
      { rewrite HcspP3. exact Hsp0up. }
      assert (Hpop : P3 !!! Regidx csp_rs1
                     = pa_stk (add_vec (P3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
      { rewrite Hwv HcspP3. symmetry. exact Hspd4. }
      iPoseProof (sli_2c with "Htext") as "Hi2c".
      iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hgap]" as "Hframe4".
      { rewrite stack_own_slots. cbn [seq].
        iSplitL "Hr24". { iExists _. iEval (rewrite Hb1 -Hcsp_mrel). iExact "Hr24". }
        iSplitL "Hr16". { iExists _. iEval (rewrite Hb2 -HcspP1). iExact "Hr16". }
        iSplitL "Hr8".  { iExists _. iEval (rewrite Hb3 -HcspP2). iExact "Hr8". }
        iSplitL "Hgap". { iExists _. iExact "Hgap". }
        done. }
      iEval (rewrite -Hwv) in "Hframe4".
      iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.sleep + 0x2c)) (mword_of_int 2 : mword 6) P3 (av - 4)%nat 4 false Hpop
                with "Hcg Hpc Hi2c Hframe4").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
      iEval (rewrite Hnk) in "Hcg".
      change (<[Regidx csp_rs1 := regval_into_reg
          (add_vec (P3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P3) with P4.
      assert (Hpc2e : add_vec_int (mword_of_int (KernelSyms.sleep + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc2e) in "Hpc".
      (* +0x2e: c.ret *)
      assert (HP4ra : P4 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
      { rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /P2 upd_ne; [| vm_compute; discriminate].
        rewrite /P1. apply upd_eq. }
      iPoseProof (sli_2e with "Htext") as "Hi2e".
      iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.sleep + 0x2e)) (mword_of_int 1 : mword 5) P4 av false
                ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi2e").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      assert (Hra_final : ret_pc (rget P4 (mword_of_int 1 : mword 5))
                          = ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)))
        by (rgne; rewrite HP4ra; reflexivity).
      iEval (rewrite Hra_final) in "Hpc".
      (* ---------------------------------------------------------------- *)
      (* Post: the caller's continuation, at the level it came in on.      *)
      (* ---------------------------------------------------------------- *)
      assert (Cthr : forall c : mword 5, is_cs_idx c = true ->
        Regidx c ≠ Regidx (mword_of_int 1) -> Regidx c ≠ Regidx (mword_of_int 8) ->
        Regidx c ≠ Regidx (mword_of_int 9) -> Regidx c ≠ Regidx (mword_of_int 10) ->
        Regidx c ≠ Regidx (mword_of_int 15) -> Regidx c ≠ Regidx csp_rs1 ->
        P4 !!! Regidx c = m !!! Regidx c).
      { intros c Hcs H1 H8 H9 H10 H15 Hsp.
        rewrite /P4 upd_ne; [| exact Hsp].
        rewrite /P3 upd_ne; [| exact H9]. rewrite /P2 upd_ne; [| exact H8].
        rewrite /P1 upd_ne; [| exact H1].
        rewrite (callee_saved_lookup Hcs_rel c Hcs).
        rewrite /N7 upd_ne; [| exact H1]. rewrite /N6 upd_ne; [| exact H10].
        exact (Hthr_N5 c Hcs H1 H8 H9 H15 Hsp). }
      assert (Csp : P4 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
        by (rewrite HP4sp; reflexivity).
      assert (Cs0 : P4 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
        by (sl_peel; reflexivity).
      assert (Cs1 : P4 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
        by (sl_peel; reflexivity).
      assert (Cs2 : P4 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5))
        by (apply Cthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
      assert (Cs3 : P4 !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5))
        by (apply Cthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
      assert (Cs4 : P4 !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5))
        by (apply Cthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
      assert (Cs5 : P4 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5))
        by (apply Cthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
      assert (Cs6 : P4 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5))
        by (apply Cthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
      assert (Cs7 : P4 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5))
        by (apply Cthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
      assert (Cs8 : P4 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5))
        by (apply Cthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
      assert (Cs9 : P4 !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5))
        by (apply Cthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
      assert (Cs10 : P4 !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5))
        by (apply Cthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
      assert (Cs11 : P4 !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5))
        by (apply Cthr; (first [ vm_compute; reflexivity | vm_compute; discriminate ])).
      iApply ("Hcont" $! P4 with "[%] Hcg Hcpu Hpc").
      unfold callee_saved. repeat split; assumption.
    - (* ================================================================= *)
      (* p->chan <> 0: THE PARK, AT noff = S (S n) -- sched() panics        *)
      (* ("sched locks"), and nothing comes back.                          *)
      (* ================================================================= *)
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.sleep + 0x16)) (mword_of_int 5 : mword 8)
                (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5) N5 (av - 4)%nat false
                creg_c7 ltac:(vm_compute; discriminate) Hbz
                with "Hcg Hpc Hi16").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      assert (Hpc18 : add_vec_int (mword_of_int (KernelSyms.sleep + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc18) in "Hpc".
      (* +0x18: c.li a5,2 *)
      iPoseProof (sli_18 with "Htext") as "Hi18".
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sleep + 0x18)) (mword_of_int 15 : mword 5) (mword_of_int 2 : mword 6)
                (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))) N5 (av - 4)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
                with "Hcg Hpc Hi18").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      set (Q0 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))]> N5).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))]> N5) with Q0.
      assert (Hpc1a : add_vec_int (mword_of_int (KernelSyms.sleep + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc1a) in "Hpc".
      assert (HQ0s1 : Q0 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j))
        by (rewrite /Q0 upd_ne; [exact Hs1_N5 | vm_compute; discriminate]).
      assert (Hrec_state : add_vec (Q0 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 24 : mword 12))
                           = p_state (proc_addr j)).
      { rewrite HQ0s1 add_vec_zero_l. unfold p_state, state_off.
        assert (H24 : sign_extend' 64 (mword_of_int 24 : mword 12) = (mword_of_int 24 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
        rewrite H24. reflexivity. }
      assert (Hrec_state_g : add_vec (rget Q0 (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 24 : mword 12))
                             = p_state (proc_addr j)) by (rgne; exact Hrec_state).
      (* +0x1a: c.sw a5,24(s1) : p->state := SLEEPING.  The state under the
         lock is arbitrary here -- this arm never returns, so nothing is
         owed about it and the ghost mirror is simply dropped. *)
      iPoseProof (sli_1a with "Htext") as "Hi1a".
      iApply (wp_csw_s_sconf (mword_of_int (KernelSyms.sleep + 0x1a)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
                (mword_of_int 24 : mword 12) Q0 (av - 4)%nat st0 false
                with "Hcg Hpc Hi1a [Hstate]").
      { iEval (rewrite Hrec_state_g). iExact "Hstate". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hstate".
      assert (Hpc1c : add_vec_int (mword_of_int (KernelSyms.sleep + 0x1a) : mword 64) 2 = mword_of_int (KernelSyms.sleep + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc1c) in "Hpc".
      (* +0x1c: jal sched *)
      iPoseProof (sli_1c with "Htext") as "Hi1c".
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sleep + 0x1c)) (mword_of_int 1 : mword 5) (mword_of_int 2096832 : mword 21)
                Q0 (av - 4)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi1c").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      set (Q1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x1c) : mword 64) 4)]> Q0).
      change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep + 0x1c) : mword 64) 4)]> Q0) with Q1.
      assert (Hpcsd : add_vec (mword_of_int (KernelSyms.sleep + 0x1c) : mword 64) (sign_extend' 64 (mword_of_int 2096832 : mword 21))
                      = mword_of_int KernelSyms.sched) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpcsd) in "Hpc".
      (* ---------------------------------------------------------------- *)
      (* +0x1c: sched() at noff = S (S n) >= 2 -- panic("sched locks").    *)
      (* ---------------------------------------------------------------- *)
      iApply (Sched.wp_sched_locks γs j γl Q1 (av - 4)%nat eb C n
                Hj Hgl ltac:(lia) ltac:(lia)
                with "Hcg Htext Hpc Hprocs Hlocked Hcpu Hpanic").
  Qed.

End ProofSleepBody.

End SleepProof.
