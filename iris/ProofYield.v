(* ProofYield.v -- the whole-function sconf-tier proof of yield()
   (SpecYield.v), as a sealed functor over its callees' interfaces
   (myproc, acquire, sched, release).  See claude-notes/projects/yield-sched.md.

   yield() @ 0x80001eda: the 32-byte frame prologue (byte-identical to
   myproc's) / p = myproc() / acquire(&p->lock) / p->state = RUNNABLE (the
   c.sw) / sched() / release(&p->lock) / epilogue.  The proof threads the
   scheduler-swtch protocol resources (SchedCtx.v): it acquires proc j's lock,
   flips the state to RUNNABLE, hands sched the parking-proc payload
   (proc_held + cpu_cells), and -- once dispatched again -- releases with the
   process RUNNING (needs_ctx RUNNING = false, so the lock slot is emp).

   THE EXPLICIT-CPUID SHAPE.  yield's contract is [wp_next b pj ...], and [b]
   is DERIVABLY [true] here: the entry bundle is [cpu_own 0 eb pj C b] with
   [eb = true], and [CpuOwn.cpu_own_forces_on] turns that into [b = true].  So
   the whole function is the hart-GENERIC case -- except for the stretch
   between acquire's return and release's call, where the held lock pins the
   hart at the literal [false] and every leaf collapses via [wp_next_off].
   yield's own [wp_next] obligation is discharged at whatever hart the
   epilogue ends on: at [b = true] the pinning condition is
   [pj = zero_reg], which [SchedCtx.proc_addr_nonzero] refutes.

   THE PARKED SCHEDULER RECORD LIVES IN THE RUNNING PROC'S OWN LOCK.  yield
   holds that lock already (it is about to write [p->state]), so it takes the
   record straight out of [proc_slots]' RUNNING arm -- no invariant, no fancy
   update, no receipt.  [SchedCtx.proc_slots_running] is the take-out: the
   thread presents the HART TAG half it carries inside [IntrDefs.cpu_claim],
   which both refutes every non-RUNNING arm and collapses the arm's
   existential hart to this one, and gets back the whole tag, the raw context
   cells and this hart's parked record.  All three cross the swtch; the
   dispatch side hands them back at the RESUMING hart, where
   [proc_slots_running_intro] puts them into the lock the release gives up. *)
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
Require Import RiscvExtras.
Require Import StackOwn CalleeSaved.
Require Import InstrBytes KernelText IntrDefs.
Require Import HartTp WpNext.
Require Import WpSmodeIntr.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpLock.
Require Import FdSlots.
Require Import ProcGeom.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import CodeYield.
Require Import SpecMyproc SpecAcquire SpecSched SpecRelease SpecYield.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* Pure helpers: address arithmetic + the two noff-cell value forms.      *)
(* ===================================================================== *)



(* acquire's noff output (push_off's +1 store over the entry value 0) is
   exactly [mword_of_int 1] (closed; needed for sched's cpu_cells). *)
Lemma yd_acq_noff_one :
  (autocast (T := mword) (subrange_vec_dec
     (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 (mword_of_int 0 : mword 32))
        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))
     (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = (mword_of_int 1 : mword 32).
Proof. vm_compute. reflexivity. Qed.

(* release's noff output (pop_off's -1 store over the entry value 1) is
   exactly [mword_of_int 0] (closed; needed for yield's postcondition). *)
Lemma yd_rel_noff_zero :
  (autocast (T := mword) (subrange_vec_dec
     (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 (mword_of_int 1 : mword 32))
        (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))
     (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = (mword_of_int 0 : mword 32).
Proof. vm_compute. reflexivity. Qed.

(* the c.li a5,3 value truncated to 32 bits is RUNNABLE = mword_of_int 3. *)
Lemma yd_runnable :
  trunc32 (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 3 : mword 6))) : mword 64)
  = (mword_of_int 3 : mword 32).
Proof. vm_compute. reflexivity. Qed.

Module YieldProof (Myproc : MYPROC) (Acquire : ACQUIRE) (Sched : SCHED) (Release : RELEASE) : YIELD.

(* ===================================================================== *)
(* THE POST-RESUME HALF, AS ITS OWN LEMMA.                                *)
(*                                                                        *)
(* sched() does not return on the hart it parked from (SpecSched.v): proc  *)
(* contexts are migratable, so its continuation is a [wp_next true] whose  *)
(* rebound [CID] is the DISPATCHING hart.  Everything yield does after the *)
(* park -- the release, the epilogue, the postcondition -- therefore has   *)
(* to hold at an ARBITRARY hart, which a Section-fixed [CID] cannot        *)
(* express.  So the whole half is ONE lemma with its OWN [CID0] binder     *)
(* (the porting guide's rule for a decomposed proof), and its own          *)
(* continuation is a [wp_next] as well: release re-enables interrupts at   *)
(* its last instruction, so even the epilogue is hart-generic.             *)
(* ===================================================================== *)
Section YieldPostSched.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.

  (* generic register-map peel over the proof's [set]-chain (hit-first). *)
  Local Ltac yd_peel :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| vm_compute; discriminate]
      | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ].

  Lemma yield_post_sched `{GEN : GenId} `{CID0 : CpuId}
       (γs : list gname)
      (j : nat) (γl : gname) (ch' : mword 64)
      (m msch : regfile) (av : nat) (eb : bool)
      (sp0 spd vgap : mword 64) (lks : gset string) :
    let pj := proc_addr j in
    (20 <= av)%nat ->
    (j < NPROC)%nat ->
    add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = spd ->
    sp0 = m !!! Regidx csp_rs1 ->
    (* NOTE: the old [⌜msch !!! x4 = cid_word⌝] premise is GONE -- [tp_pin]
       makes the tp slot unobservable, so nothing can read it. *)
    msch !!! Regidx csp_rs1 = spd ->
    msch !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j) ->
    (* s2..s11: untouched by yield and by everything it calls *)
    msch !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5) ->
    msch !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5) ->
    msch !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5) ->
    msch !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) ->
    msch !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) ->
    msch !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) ->
    msch !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) ->
    msch !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) ->
    msch !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) ->
    msch !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5) ->
    (* release's order premise -- see [wp_yield_sconf] where it originates
       (yield's own [lks] is [∅], so this is [locks_below_empty]) *)
    locks_below lks "proc" ->
    kernel_text -∗
    is_lock γl (proc_addr j) "proc"%string (proc_lock_res γs γl (proc_addr j)) -∗
    sie_cap_gpr KT1 msch (trap_res eb + (av - 4))%nat false pj -∗
    pc_is (mword_of_int (KernelSyms.yield + 0x1c)) -∗
    proc_held cpu_id j γl RUNNING ch' -∗
    trap_csrs KT1 -∗
    cpu_own 1 eb pj false ({["proc"]} ∪ lks) -∗
    (* the cells swtch handed back; they go into the RUNNING lock at the
       release below, which is where the NEXT yield will find them. *)
    own_ctx (p_context pj) -∗
    (* the slot's ALLOCATION MARKER: the RUNNING lock resource carries it
       like every non-UNUSED arm, and the release below puts it back
       ([ProcAvail.v]).  Persistent. *)
    pslot_used_at pj -∗
    (* the hart tag, whole, at the hart the dispatch resumed us on: half goes
       back into [run_slot] at the release, half becomes this thread's own
       [cpu_claim]. *)
    hart_full j cpu_id -∗
    ▷ sched_vc γs (a_cpu_ctx cid_word) pj -∗
    (* the three saved frame words + the frame's bottom slot *)
    pa_stk sp0 1 ↦₈[KT1] (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
    pa_stk sp0 2 ↦₈[KT1] (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
    pa_stk sp0 3 ↦₈[KT1] (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
    pa_stk sp0 4 ↦₈[KT1] vgap -∗
    wp_next true pj (fun (CID : CpuId) =>
      ∀ (mf : regfile),
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr KT1 mf av eb pj -∗
        cpu_own 0 eb pj eb lks -∗
        pc_is (ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))) -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb pj -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj Hav Hj Hspd Hsp0 Hsp_msch Hs1_msch
           Hmsch18 Hmsch19 Hmsch20 Hmsch21 Hmsch22 Hmsch23 Hmsch24 Hmsch25 Hmsch26 Hmsch27 Hfresh.
    iIntros "#Htext #Hislock Hcg Hpc Hheld' Htc Hcpuemp Hown' #Hmk Htag Hvc' Hr24 Hr16 Hr8 Hgap Hcont".
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
    (* [cpu_own] carries no context-slot payload any more, so what used to be
       a re-injection is now just the bundle itself, unchanged. *)
    iRename "Hcpuemp" into "Hcpu".
    (* +0x1c: c.mv a0,s1 : a0 := s1 = proc_addr j -- lock still held, so the
       hart is PINNED and [wp_next_off] collapses the binder. *)
    iPoseProof (ydi_1c with "Htext") as "Hi1c".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.yield + 0x1c)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              msch (trap_res eb + (av - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (D0 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec zero_reg (msch !!! Regidx (mword_of_int 9 : mword 5)))]> msch).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec zero_reg (msch !!! Regidx (mword_of_int 9 : mword 5)))]> msch) with D0.
    assert (Hpc1e : add_vec_int (mword_of_int (KernelSyms.yield + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.yield + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1e) in "Hpc".
    (* +0x1e: jal release *)
    iPoseProof (ydi_1e with "Htext") as "Hi1e".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.yield + 0x1e)) (mword_of_int 1 : mword 5) (mword_of_int 2092396 : mword 21)
              D0 (trap_res eb + (av - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1e").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (D1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.yield + 0x1e) : mword 64) 4)]> D0).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.yield + 0x1e) : mword 64) 4)]> D0) with D1.
    assert (Hpcrl : add_vec (mword_of_int (KernelSyms.yield + 0x1e) : mword 64) (sign_extend' 64 (mword_of_int 2092396 : mword 21))
                    = mword_of_int KernelSyms.release) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcrl) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x1e: release(&p->lock) -- with the process RUNNING (slot emp).    *)
    (* ------------------------------------------------------------------ *)
    assert (Ha0_D1 : D1 !!! Regidx (mword_of_int 10 : mword 5) = proc_addr j).
    { rewrite /D1 upd_ne; [| vm_compute; discriminate].
      rewrite /D0 upd_eq Hs1_msch !add_vec_zero_l. reflexivity. }
    assert (HD1ra : D1 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.yield + 0x1e) : mword 64) 4)
      by (rewrite /D1 upd_eq; reflexivity).
    assert (Hlka : add_vec (D1 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = proc_addr j).
    { rewrite Ha0_D1.
      assert (H0 : sign_extend' 64 (mword_of_int 0 : mword 12) = (mword_of_int 0 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite H0. apply kv_addv_zero. }
    (* rebuild the lock resource: at RUNNING there is no parked record, no
       dormant block and -- since it IS running -- no park receipt either,
       but the RAW CONTEXT CELLS go back in.  They are what swtch handed
       this thread when the scheduler resumed it, and leaving them in the
       lock is what lets the NEXT yield (or the next preempting trap) find
       them without being handed them by a caller. *)
    iAssert (proc_lock_res γs γl (proc_addr j)) with "[Hstate Hpg Hchan Hpub Hown' Htaga Hvc']" as "HR2".
    { rewrite /proc_lock_res. iExists RUNNING, ch'. iFrame "Hstate Hpg Hchan Hpub".
      iApply (proc_slots_running_intro γs j cpu_id Hj with "Htaga Hown' Hvc' Hmk"). }
    (* THE TRAP-CSR SPLIT.  release consumes [arm_pay 0 eb _] -- the set
       at [eb = true], nothing at [eb = false].  The complement is what this
       call was handed from outside and owes back to yield's caller; exactly
       one of the two is [emp]. *)
    iEval (rewrite -(trap_csrs_ext_split eb)) in "Htc".
    iDestruct "Htc" as "[Hpay Hext]".
    (* THE FREED STATE HALF takes the same two-sided cut.  At [eb = true] the
       release's last instruction re-enables interrupts, so half #2 goes back
       INTO [sie_arm true pj] as the arm's claim; at [eb = false] no arm is
       rebuilt and the thread keeps it, to hand to yield's caller. *)
    iDestruct (cpu_claim_proc j Hj with "Hclm Htagb") as "Hclm".
    iEval (rewrite -(cpu_claim_ext_split eb pj)) in "Hclm".
    iDestruct "Hclm" as "[Hclmp Hclmx]".
    iApply (Release.wp_release_sconf KT1 γl (proc_addr j) "proc"%string
              (proc_lock_res γs γl (proc_addr j)) D1 0 eb pj (av - 4)%nat
              ({["proc"]} ∪ lks) Hlka
              ltac:(lia)
              with "Hcg Htext Hpc Hislock Hlocked HR2 Hcpu [$Hpay $Hclmp]").
    (* release's exit index is [outb = eb]: at [eb = true] it re-enables at
       its LAST instruction, so the hart can move there and the epilogue
       below is hart-GENERIC; at [eb = false] it does not, and the chain
       pins every step to this hart.  Either way the leaves run at [eb]. *)
    iIntros (CIDr Hsr mrel) "Hcg Hpc %Hcs_rel Hcpu".
    (* yield is BALANCED: what it acquired it released, so the set release
       hands back collapses to the entry [lks]. *)
    pose proof (locks_below_not_elem lks "proc" Hfresh) as Hnotin.
    assert (Hsetback : ({["proc"]} ∪ lks) ∖ {["proc"]} = lks)
      by (apply locks_add_del_below; lkbelow).
    iEval (rewrite Hsetback) in "Hcpu".
    assert (Hpc22 : ret_pc (D1 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.yield + 0x22)) by (rewrite HD1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc22) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* Epilogue: restore ra/s0/s1, pop the frame, return (mirror myproc).  *)
    (* ------------------------------------------------------------------ *)
    (* sp threads (callee-saved) through all four callees back to the push. *)
    assert (Hcsp_mrel : mrel !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hcs_rel csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /D1 upd_ne; [| vm_compute; discriminate]. rewrite /D0 upd_ne; [| vm_compute; discriminate].
      exact Hsp_msch. }
    (* the three saved frame cells arrive at [pa_stk sp0 k]; bridge each to
       the [spd + imm] form the c.ldsp leaves compute. *)
    iEval (rewrite Hb1) in "Hr24".
    iEval (rewrite Hb2) in "Hr16".
    iEval (rewrite Hb3) in "Hr8".
    (* +0x22: c.ldsp ra,24 *)
    iPoseProof (ydi_22 with "Htext") as "Hi22".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.yield + 0x22)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              mrel (av - 4)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 [Hr24]").
    { iEval (rewrite Hcsp_mrel). iExact "Hr24". }
    iIntros (CIDe1 Hse1) "Hcg Hpc Hr24".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mrel).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mrel) with E1.
    assert (Hpc24 : add_vec_int (mword_of_int (KernelSyms.yield + 0x22) : mword 64) 2 = mword_of_int (KernelSyms.yield + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc24) in "Hpc".
    assert (HcspE1 : E1 !!! Regidx csp_rs1 = spd)
      by (rewrite /E1 upd_ne; [exact Hcsp_mrel | vm_compute; discriminate]).
    (* +0x24: c.ldsp s0,16 *)
    iPoseProof (ydi_24 with "Htext") as "Hi24".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.yield + 0x24)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              E1 (av - 4)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24 [Hr16]").
    { iEval (rewrite HcspE1). iExact "Hr16". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hr16".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1) with E2.
    assert (Hpc26 : add_vec_int (mword_of_int (KernelSyms.yield + 0x24) : mword 64) 2 = mword_of_int (KernelSyms.yield + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc26) in "Hpc".
    assert (HcspE2 : E2 !!! Regidx csp_rs1 = spd)
      by (rewrite /E2 upd_ne; [exact HcspE1 | vm_compute; discriminate]).
    (* +0x26: c.ldsp s1,8 *)
    iPoseProof (ydi_26 with "Htext") as "Hi26".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.yield + 0x26)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              E2 (av - 4)%nat (m !!! Regidx (mword_of_int 9 : mword 5)) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26 [Hr8]").
    { iEval (rewrite HcspE2). iExact "Hr8". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hr8".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2) with E3.
    assert (Hpc28 : add_vec_int (mword_of_int (KernelSyms.yield + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.yield + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    assert (HcspE3 : E3 !!! Regidx csp_rs1 = spd)
      by (rewrite /E3 upd_ne; [exact HcspE2 | vm_compute; discriminate]).
    (* +0x28: c.addi16sp sp,32 -- pop the frame *)
    set (E4 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3).
    assert (Hsp0up : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite -Hspd add_vec_assoc.
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
    iPoseProof (ydi_28 with "Htext") as "Hi28".
    iAssert (stack_own (KTR := KT1) sp0 4) with "[Hr24 Hr16 Hr8 Hgap]" as "Hframe4".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hr24". { iExists _. iEval (rewrite Hb1 -Hcsp_mrel). iExact "Hr24". }
      iSplitL "Hr16". { iExists _. iEval (rewrite Hb2 -HcspE1). iExact "Hr16". }
      iSplitL "Hr8".  { iExists _. iEval (rewrite Hb3 -HcspE2). iExact "Hr8". }
      iSplitL "Hgap". { iExists _. iExact "Hgap". }
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.yield + 0x28)) (mword_of_int 2 : mword 6) E3 (av - 4)%nat 4 eb Hpop
              with "Hcg Hpc Hi28 Hframe4").
    iIntros (CIDe4 Hse4) "Hcg Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3) with E4.
    assert (Hpc2a : add_vec_int (mword_of_int (KernelSyms.yield + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.yield + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    (* +0x2a: c.ret *)
    assert (HE4ra : E4 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1. apply upd_eq. }
    iPoseProof (ydi_2a with "Htext") as "Hi2a".
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.yield + 0x2a)) (mword_of_int 1 : mword 5) E4 av eb
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi2a").
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
    (* the registers yield itself never writes thread E4 -> mrel -> msch,
       and the ten [Hmsch_*] premises carry them the rest of the way. *)
    assert (Cthr : forall c : mword 5, is_cs_idx c = true ->
      Regidx c ≠ Regidx (mword_of_int 1) -> Regidx c ≠ Regidx (mword_of_int 8) ->
      Regidx c ≠ Regidx (mword_of_int 9) -> Regidx c ≠ Regidx (mword_of_int 10) ->
      Regidx c ≠ Regidx csp_rs1 ->
      E4 !!! Regidx c = msch !!! Regidx c).
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
      by (yd_peel; reflexivity).
    assert (Cs1 : E4 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (yd_peel; reflexivity).
    assert (Cs2 : E4 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5))
      by (rewrite (Cthr (mword_of_int 18) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch18).
    assert (Cs3 : E4 !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5))
      by (rewrite (Cthr (mword_of_int 19) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch19).
    assert (Cs4 : E4 !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5))
      by (rewrite (Cthr (mword_of_int 20) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch20).
    assert (Cs5 : E4 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5))
      by (rewrite (Cthr (mword_of_int 21) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch21).
    assert (Cs6 : E4 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5))
      by (rewrite (Cthr (mword_of_int 22) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch22).
    assert (Cs7 : E4 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5))
      by (rewrite (Cthr (mword_of_int 23) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch23).
    assert (Cs8 : E4 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5))
      by (rewrite (Cthr (mword_of_int 24) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch24).
    assert (Cs9 : E4 !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5))
      by (rewrite (Cthr (mword_of_int 25) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch25).
    assert (Cs10 : E4 !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5))
      by (rewrite (Cthr (mword_of_int 26) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch26).
    assert (Cs11 : E4 !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5))
      by (rewrite (Cthr (mword_of_int 27) ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)); exact Hmsch27).
    iDestruct (cpu_own_transport CIDr CIDe5 0 eb pj eb ltac:(wp_next_chain)
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

End YieldPostSched.

Section ProofYield.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_yield_sconf 
      (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (eb : bool)
    : wp_yield_sconf_body γs j γl m av eb.
  Proof.
    cbv beta delta [wp_yield_sconf_body].
    intros pcE pj ret_tgt Hj Hgl Hav.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcpu #Htext Hpc #Hprocs Hext Hclmx Hcont".
    (* ONE INDEX.  [eb] is both the saved base enable and the resource index:
       at level 0 they are forced equal ([CpuOwn.cpu_own_eb_agree]), so there
       is nothing to derive and nothing to case-split on.  yield's own
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
    iPoseProof (ydi_00 with "Htext") as "Hi00".
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m av 4 eb ltac:(lia) Hpush
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with A0.
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.yield + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
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
    iPoseProof (ydi_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.yield + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              A0 (av - 4)%nat vr24 eb with "Hcg Hpc Hi02 [Hr24]").
    { iEval (rewrite HcspA0 -Hb1). iExact "Hr24". }
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    iEval (rgne) in "Hr24".
    assert (Hpc04 : add_vec_int (mword_of_int (KernelSyms.yield + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.yield + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    iPoseProof (ydi_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.yield + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              A0 (av - 4)%nat vr16 eb with "Hcg Hpc Hi04 [Hr16]").
    { iEval (rewrite HcspA0 -Hb2). iExact "Hr16". }
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    iEval (rgne) in "Hr16".
    assert (Hpc06 : add_vec_int (mword_of_int (KernelSyms.yield + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.yield + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    iPoseProof (ydi_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.yield + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              A0 (av - 4)%nat vr8 eb with "Hcg Hpc Hi06 [Hr8]").
    { iEval (rewrite HcspA0 -Hb3). iExact "Hr8". }
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    iEval (rgne) in "Hr8".
    assert (Hpc08 : add_vec_int (mword_of_int (KernelSyms.yield + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.yield + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    (* +0x08: c.addi4spn s0,sp,32 *)
    iPoseProof (ydi_08 with "Htext") as "Hi08".
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.yield + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              A0 (av - 4)%nat eb
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (A1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0) with A1.
    assert (Hpc0a : add_vec_int (mword_of_int (KernelSyms.yield + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.yield + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x0a: jal myproc -> a0 = proc_addr j; noff/intena/cur_proc round.  *)
    (* ------------------------------------------------------------------ *)
    iPoseProof (ydi_0a with "Htext") as "Hi0a".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.yield + 0x0a)) (mword_of_int 1 : mword 5) (mword_of_int 2095640 : mword 21)
              A1 (av - 4)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0a").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (A2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.yield + 0x0a) : mword 64) 4)]> A1).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.yield + 0x0a) : mword 64) 4)]> A1) with A2.
    assert (Hpcmp : add_vec (mword_of_int (KernelSyms.yield + 0x0a) : mword 64) (sign_extend' 64 (mword_of_int 2095640 : mword 21))
                    = mword_of_int KernelSyms.myproc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcmp) in "Hpc".
    assert (HA2ra : A2 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.yield + 0x0a) : mword 64) 4)
      by (rewrite /A2 upd_eq; reflexivity).
    iDestruct (cpu_own_transport CID CID6 0 eb pj eb ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (Myproc.wp_myproc_sconf A2 (av - 4)%nat 0 eb pj eb
              _ ltac:(lia)
              ltac:(lia)
              with "Hcg Hcpu Htext Hpc").
    iIntros (CID7 Hs7 ms mp) "%Hmsf Hcg Hcpu Hpc %Hmp".
    destruct Hmp as [Hcs_mp Ha0_mp].
    assert (Hpc0e : ret_pc (A2 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.yield + 0x0e)) by (rewrite HA2ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0e) in "Hpc".
    (* +0x0e: c.mv s1,a0 : s1 := a0 = proc_addr j *)
    iPoseProof (ydi_0e with "Htext") as "Hi0e".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.yield + 0x0e)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              mp (av - 4)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e").
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    set (B0 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (mp !!! Regidx (mword_of_int 10 : mword 5)))]> mp).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (mp !!! Regidx (mword_of_int 10 : mword 5)))]> mp) with B0.
    assert (Hpc10 : add_vec_int (mword_of_int (KernelSyms.yield + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.yield + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    (* +0x10: jal acquire *)
    iPoseProof (ydi_10 with "Htext") as "Hi10".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.yield + 0x10)) (mword_of_int 1 : mword 5) (mword_of_int 2092274 : mword 21)
              B0 (av - 4)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi10").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (B1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.yield + 0x10) : mword 64) 4)]> B0).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.yield + 0x10) : mword 64) 4)]> B0) with B1.
    assert (Hpcaq : add_vec (mword_of_int (KernelSyms.yield + 0x10) : mword 64) (sign_extend' 64 (mword_of_int 2092274 : mword 21))
                    = mword_of_int KernelSyms.acquire) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcaq) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x10: acquire(&p->lock) -- take proc j's lock.                     *)
    (* ------------------------------------------------------------------ *)
    assert (Ha0_B1 : B1 !!! Regidx (mword_of_int 10 : mword 5) = proc_addr j).
    { rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite /B0 upd_ne; [| vm_compute; discriminate]. exact Ha0_mp. }
    assert (HB1ra : B1 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.yield + 0x10) : mword 64) 4)
      by (rewrite /B1 upd_eq; reflexivity).
    iPoseProof (procs_inv_lookup γs j γl Hgl with "Hprocs") as "#Hislock".
    iDestruct (cpu_own_transport CID7 CID9 0 eb pj eb ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (Acquire.wp_acquire_sconf KT1 γl "proc"%string
              (proc_lock_res γs γl (proc_addr j)) B1 0 eb pj (av - 4)%nat eb ∅
              ltac:(lia)
              ltac:(lia)
              (locks_below_empty "proc")
              with "Hcg Hcpu Htext Hpc [Hislock]").
    all: try lkbelow.
    { iEval (rewrite Ha0_B1). iExact "Hislock". }
    (* FROM HERE TO THE RELEASE THE LOCK IS HELD, so the index is the literal
       [false] and every leaf collapses with [wp_next_off]. *)
    iIntros (CIDa Hsa ms2 macq) "%Hmsf2 Hcg Hpc %Hcs_acq Hlocked HR Hcpu [Hpay Hclmp]".
    assert (Hpc14 : ret_pc (B1 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.yield + 0x14)) by (rewrite HB1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    (* unpack the lock resource.  THE PARK RECEIPT PAYS FOR THE STATE: the
       half this thread carries refutes the slot's [not_running] arm, so the
       state under the lock is RUNNING -- and the RUNNING arm is exactly the
       raw context cells sched is about to want.  That is why yield needs no
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
       record.  That is why yield needs no [own_ctx] premise and no global
       invariant: it takes all three from the lock it just took. *)
    iDestruct (proc_lock_res_elim γs γl (proc_addr j) with "HR") as (st0 ch0) "(Hstate & Hpg & Hchan & Hpub & Hslot)".
    iDestruct (proc_slots_running γs j CIDa st0 Hj with "Htag Hslot")
      as "(-> & Htag & Hown & Hvc & #Hmk)".
    (* the claim's half #2 joins the lock's tie into the WHOLE mirror, which
       is what the store to p->state below is allowed to move. *)
    iDestruct (pstate_at_intro j (1/2) RUNNING Hj with "Hclm") as "Hclm".
    iDestruct (pstate_whole_split (proc_addr j) RUNNING) as "[_ Hwe]".
    iDestruct ("Hwe" with "[Hpg Hclm]") as "Hpg".
    { rewrite unclaimed_RUNNING. iFrame "Hpg Hclm". }
    (* +0x14: c.li a5,3 *)
    iPoseProof (ydi_14 with "Htext") as "Hi14".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.yield + 0x14)) (mword_of_int 15 : mword 5) (mword_of_int 3 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 3 : mword 6)))) macq (trap_res eb + (av - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc Hi14").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (C0 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 3 : mword 6))))]> macq).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 3 : mword 6))))]> macq) with C0.
    assert (Hpc16 : add_vec_int (mword_of_int (KernelSyms.yield + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.yield + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    (* the s1 value threads (callee-saved) through acquire, so p->state's
       address reconciles to p_state (proc_addr j). *)
    assert (HC0s1 : C0 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j)).
    { rewrite /C0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_acq (mword_of_int 9) ltac:(vm_compute; reflexivity)).
      rewrite /B1 upd_ne; [| vm_compute; discriminate]. rewrite /B0 upd_eq Ha0_mp. reflexivity. }
    assert (Hrec_state : add_vec (C0 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 24 : mword 12))
                         = p_state (proc_addr j)).
    { rewrite HC0s1 add_vec_zero_l. unfold p_state, state_off.
      assert (H24 : sign_extend' 64 (mword_of_int 24 : mword 12) = (mword_of_int 24 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite H24. reflexivity. }
    assert (Hsv : trunc32 (C0 !!! Regidx (mword_of_int 15 : mword 5)) = RUNNABLE).
    { rewrite /C0 upd_eq. unfold RUNNABLE. exact yd_runnable. }
    (* the [rget]-spelled twins the store leaf's [pa] / [storeval] want. *)
    assert (Hrec_state_g : add_vec (rget C0 (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 24 : mword 12))
                           = p_state (proc_addr j)) by (rgne; exact Hrec_state).
    assert (Hsv_g : trunc32 (rget C0 (mword_of_int 15 : mword 5)) = RUNNABLE)
      by (rgne; exact Hsv).
    (* +0x16: c.sw a5,24(s1) : p->state := RUNNABLE *)
    iPoseProof (ydi_16 with "Htext") as "Hi16".
    iApply (wp_csw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.yield + 0x16)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
              (mword_of_int 24 : mword 12) C0 (trap_res eb + (av - 4))%nat RUNNING false
              with "Hcg Hpc Hi16 [Hstate]").
    { iEval (rewrite Hrec_state_g). iExact "Hstate". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hstate".
    iEval (rewrite Hrec_state_g Hsv_g) in "Hstate".
    assert (Hpc18 : add_vec_int (mword_of_int (KernelSyms.yield + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.yield + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc18) in "Hpc".
    (* +0x18: jal sched *)
    iPoseProof (ydi_18 with "Htext") as "Hi18".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.yield + 0x18)) (mword_of_int 1 : mword 5) (mword_of_int 2096940 : mword 21)
              C0 (trap_res eb + (av - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi18").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (C1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.yield + 0x18) : mword 64) 4)]> C0).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.yield + 0x18) : mword 64) 4)]> C0) with C1.
    assert (Hpcsd : add_vec (mword_of_int (KernelSyms.yield + 0x18) : mword 64) (sign_extend' 64 (mword_of_int 2096940 : mword 21))
                    = mword_of_int KernelSyms.sched) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcsd) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x18: sched() -- park; resumes with the process dispatched again.  *)
    (* ------------------------------------------------------------------ *)
    assert (HC1ra : C1 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.yield + 0x18) : mword 64) 4)
      by (rewrite /C1 upd_eq; reflexivity).
    iRename "Hcpu" into "Hcpuemp".
    (* sched's crossing wants the WHOLE trap-CSR set, unconditionally: those
       are per-hart registers and the park can move harts.  Half of it comes
       from acquire's own [arm_pay 0 eb _] (the set at [eb = true],
       nothing at [eb = false]) and the other half is [trap_csrs_ext eb],
       which yield's caller brought for exactly this reason. *)
    (* the lent half is at the ENTRY hart; transport it forward first
       ([emp] at [eb = true], and at [eb = false] nothing above could have
       moved the hart). *)
    iDestruct (trap_csrs_ext_transport CID CIDa eb pj ltac:(wp_next_chain)
                 with "Hext") as "Hext".
    iAssert (trap_csrs KT1) with "[Hpay Hext]" as "Htc".
    { iEval (rewrite -(trap_csrs_ext_split eb)). iFrame "Hpay Hext". }
    iApply fupd_wp.
    (* the store to p->state above moved the CELL; the mirror follows here,
       which the whole variable permits with no side condition.  This is the
       claim being RETURNED: RUNNABLE is unclaimed, so after the park the
       lock owns both halves again. *)
    iMod (pstate_whole_update (proc_addr j) RUNNING RUNNABLE with "Hpg") as "Hpg".
    iModIntro.
    iApply (Sched.wp_sched_sconf γs j γl RUNNABLE ch0 C1 (trap_res eb + (av - 4))%nat eb
              Hj Hgl (park_ok_RUNNABLE) ltac:(lia)
              with "Hcg Htext Hpc Hprocs [Hlocked Hstate Hpg Hchan Hpub] [] Htc Hcpuemp Hown Htag Hvc").
    { rewrite /proc_held. iFrame "Hlocked Hstate Hpg Hchan Hpub". }
    (* a RUNNABLE park owes the slot nothing beyond its record. *)
    { iIntros "_". iApply (park_pay_needs_ctx (proc_addr j) RUNNABLE needs_ctx_RUNNABLE). }
    (* SCHED RETURNS ON HART [CIDs].  Everything below runs there, inside
       [yield_post_sched] at [(CID0 := CIDs)]. *)
    iIntros (CIDs Hss msch ch') "%Hcs_sch Hcg Hpc Hheld' Htc' Hcpuemp Hown' Htag' Hvc'".
    (* what the post-resume half needs about [msch], read off this tower. *)
    assert (Hsp_msch : msch !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hcs_sch csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /C1 upd_ne; [| vm_compute; discriminate]. rewrite /C0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_acq csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /B1 upd_ne; [| vm_compute; discriminate]. rewrite /B0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_mp csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /A2 upd_ne; [| vm_compute; discriminate]. rewrite /A1 upd_ne; [| vm_compute; discriminate].
      exact HcspA0. }
    assert (Hs1_msch : msch !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg (proc_addr j)).
    { rewrite (callee_saved_lookup Hcs_sch (mword_of_int 9) ltac:(vm_compute; reflexivity)).
      rewrite /C1 upd_ne; [| vm_compute; discriminate]. exact HC0s1. }
    assert (Hthr : forall c : mword 5, is_cs_idx c = true ->
      Regidx c ≠ Regidx (mword_of_int 1) -> Regidx c ≠ Regidx (mword_of_int 8) ->
      Regidx c ≠ Regidx (mword_of_int 9) -> Regidx c ≠ Regidx (mword_of_int 10) ->
      Regidx c ≠ Regidx (mword_of_int 15) -> Regidx c ≠ Regidx csp_rs1 ->
      msch !!! Regidx c = m !!! Regidx c).
    { intros c Hcs H1 H8 H9 H10 H15 Hsp.
      rewrite (callee_saved_lookup Hcs_sch c Hcs).
      rewrite /C1 upd_ne; [| exact H1]. rewrite /C0 upd_ne; [| exact H15].
      rewrite (callee_saved_lookup Hcs_acq c Hcs).
      rewrite /B1 upd_ne; [| exact H1]. rewrite /B0 upd_ne; [| exact H9].
      rewrite (callee_saved_lookup Hcs_mp c Hcs).
      rewrite /A2 upd_ne; [| exact H1]. rewrite /A1 upd_ne; [| exact H8].
      rewrite /A0 upd_ne; [| exact Hsp]. reflexivity. }
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
    (* the pc: sched hands back [ret_pc (C1 !!! ra)] = KernelSyms.yield + 0x1c *)
    assert (Hpc1c : ret_pc (C1 !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (KernelSyms.yield + 0x1c)) by (rewrite HC1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1c) in "Hpc".
    (* the three saved frame cells, re-addressed at [pa_stk sp0 k]. *)
    assert (HraA0 : A0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0A0 : A0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1A0 : A0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HcspA0 HraA0 -Hb1) in "Hr24".
    iEval (rewrite HcspA0 Hs0A0 -Hb2) in "Hr16".
    iEval (rewrite HcspA0 Hs1A0 -Hb3) in "Hr8".
    (* ONE application of the post-resume half, at the resuming hart. *)
    iApply (yield_post_sched (CID0 := CIDs)  γs j γl ch' m msch av eb sp0 spd vgap ∅
              ltac:(lia) Hj ltac:(reflexivity) ltac:(reflexivity)
              Hsp_msch Hs1_msch
              Hmsch18 Hmsch19 Hmsch20 Hmsch21 Hmsch22 Hmsch23 Hmsch24 Hmsch25 Hmsch26 Hmsch27
              (locks_below_empty "proc")
              with "Htext Hislock Hcg Hpc Hheld' Htc' Hcpuemp Hown' Hmk Htag' Hvc' Hr24 Hr16 Hr8 Hgap
                    [Hcont]").
    (* yield's own [wp_next true pj] obligation, re-anchored at the resuming
       hart -- [WpNext.wp_next_retarget], the transport for exactly this.  The
       index is the LITERAL [true] (a parking function's always is), so the
       only pinning condition left is [pj = zero_reg], which
       [proc_addr_nonzero] refutes -- the obligation transports to ANY hart,
       at either [eb]. *)
    assert (Hrt : true = false \/ proc_addr j = zero_reg ->
                  (CIDs : CPU) = (CID : CPU)).
    { intros [Hf | Hz]; [discriminate | exfalso; exact (proc_addr_nonzero j Hj Hz)]. }
    iApply (wp_next_retarget _ _ _ _ _ Hrt with "Hcont").
  Qed.

End ProofYield.

End YieldProof.
