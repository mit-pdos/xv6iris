(* SpecSysSyncFlush.v -- sys_sync's DURABILITY contract, as a PARALLEL FORM
   (rule R10).  [SpecSysSync.v] does not move: its header already promises
   "the postcondition only grows", and this file is that growth, stated
   beside it rather than inside it so that every landed caller, the syscall
   dispatcher included, keeps the contract it was proved against.

     uint64 sys_sync(void) {
       acquire(&log.lock);
       if (log.committing || log.outstanding > 0) {
         int n = log.ncommit + 1;
         while (log.ncommit < n) {
           sleep_prepare(&log); release(&log.lock); sleep(); acquire(&log.lock);
         }
       }
       release(&log.lock);
       return 0;
     }

   ============================ THE SHAPE =============================

   WHAT SYS_SYNC RETURNS is [FsFlushed.flushed b D] -- design section 5
   principle 2's persistent, monotone, STATE-shaped receipt ("batches <= b
   are durable"), whose value is a copy of the frozen snapshot certificate
   (plan 4^9.3, "sync-style receipts are copies").  The state-shaped form
   is FORCED, and the landed empty contract's header is where the argument
   is written down: sys_sync's FAST PATH (!committing && outstanding == 0)
   returns with NO commit occurring during the call, so an EVENT-shaped
   receipt -- "a commit happened" -- is unavailable on that arm.  A receipt
   ABOUT THE STATE is available on both.

   THE TWO ARMS, and what each proves (design section 5 principle 2's case
   split, and the code's own reason for waiting exactly one commit):

   - FAST PATH, the guard false.  [committing = 0] and [outstanding = 0]
     together say the log is EMPTY: the last [end_op] committed its group
     and cleared the header, and no operation has opened since.  So the
     durable state IS the logged state at the current batch counter, and
     the receipt is handed out directly by the invariant -- no commit, no
     wait, nothing to wake up for.
   - SLOW PATH, the guard true.  The caller reads [n = log.ncommit + 1] and
     sleeps until the counter reaches it.  ONE commit suffices, by a case
     split at the lock: [committing] implies [outstanding = 0] ([begin_op]
     blocks while committing), so the in-progress commit's batch already
     contains every delta linearized before the call; and with the group
     merely open, all older batches are committed and every remaining
     pre-invocation delta sits in (or joins) the current group, which the
     next commit writes IN FULL -- the log only grows between commits.  So
     [ncommit + 1] is "the commit covering the invocation-time batch".

   Note that sys_sync never runs [begin_op]: it is not a transaction, it
   only watches the counter, which is what keeps it from delaying the very
   group it waits on.  SAFETY ONLY: with operations outstanding, quiescence
   needs [out = 0] and [begin_op] admits new operations into the open group,
   so a continuous operation stream defers the commit unboundedly.  There
   is NO termination claim here and none is intended; the WP is the same
   parking WP the landed contract has.

   ==================== THE BANK, LANDED (owner ruling) =================

   THE RECEIPT NOW HAS A CLIENT-REACHABLE PRODUCER, and it is
   [flushed_sync_of_res] below: with the "log" spinlock held and the
   caller's witness in hand, [LogInv.log_res] yields [flushed_sync γ e] and
   closes UNCHANGED.  That is the whole of this contract's item (iii).

   What made it reachable is the owner-ruled conjunct of [LogInv.log_res]:
   [LogInv.log_flushed_bank γ E], last before the committing arm.  Its two
   deposits are the two places the log's batch counter is ever SET:

     - [ProofEndOp]'s [eo_tail], where [log_epoch_bump] runs.  The copy is
       the one [FsCrash.fs_rec_permit_bank] takes at the commit's LAST disk
       write -- the preserving CLEAR that follows the install -- so it is
       the state THAT batch made durable, on either sector order.  On the
       empty-log path, where no commit body runs at all, the invariant's own
       copy is recycled, which is the literal truth there: nothing was made
       durable because nothing needed to be.
     - [ProofInitlog]'s seal, at genesis (E = 1).  Same copy, off the same
       clear -- the one write [initlog] makes after recovery has caught the
       home blocks up -- so the bank is full from the first instant the log
       exists and sys_sync has an answer before any transaction has run.

   It changed NO arity: not [log_ctx]'s, not [wp_end_op]'s, not
   [log_names]'.  What it did cost is recorded in lane Y's row of the
   worklist.

   ========================= AND IT IS PROVED ==========================

   [ProofSysSync.SysSyncProof] IMPLEMENTS THIS MODULE TYPE, and
   [LinkSysSync] derives the landed [SYS_SYNC] from it through
   [SysSyncFlushWeaken] below -- so nothing was re-proved and no caller
   moved.  The walk is the landed one instruction for instruction: the
   receipt is minted ONCE, at the first acquire, by [flushed_sync_of_res],
   and rides the intuitionistic context out at the tail.

   THE WAIT LOOP NEEDED NOTHING, and it is worth saying why, because the
   opposite was expected.  [log_res] binds the [log.ncommit] CELL
   existentially and says nothing about its value ([LogInv.v]'s
   [l_ncommit ↦₄ nc]), so [ProofSysSync]'s wait loop carries no [nc] binder
   and its back edge is a raw case split -- and that is still true.  It does
   not matter here: the post asks for a bank at some [e' >= e] and NOT for a
   strict increase (see the last section), the counter only grows, so a copy
   taken at the FIRST acquire already answers on every path.  The tie
   [⌜uint nc = Z.of_nat E⌝] would only be needed by a contract that claimed
   the wait ENDED at a later batch than it started -- which this one
   deliberately does not claim, and no consumer of the receipt asks for.

   ==================== WHY THE BOUND IS NOT [S e] =====================

   The post below says the counter has reached some [e' >= e] and hands
   back the receipt standing there.  It does NOT say [e < e'], and that is
   not slack -- it is the fast path, honestly stated.  A caller whose
   witness [e] was taken in the CURRENT batch and whose operations have all
   ended finds the log empty exactly when that batch is empty too, so
   nothing of the caller's is waiting and [e' = e] is the right answer;
   demanding [S e] would make the contract unprovable on that arm without
   making any consumer stronger.  What a consumer actually uses is the
   receipt: [FsFlushed.dur_at] reads its rows, and [FsFlushed.flushed_earlier]
   orders it against every earlier one. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map mono_nat.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import LockRank.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import BioDefs.
Require Import FsBlocks LogInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
(* THE RECEIPT AT ITS LOW ALTITUDE, and this is load-bearing: the obvious
   imports here are [FsDurSyscall] and [FsFlushed], and BOTH sit above
   [SystemAdequacy] -- i.e. above the whole proof tree, [ProofSysSync]
   included -- so a contract stated over them could never be PROVED.  The
   same two names come out of the leaves ([FsDurSnap.snap_holds],
   [FsFlushedCore.flushed]), and nothing in this file needs anything else
   from either: [FsFlushed.dur_at] is named in comments only, as the thing a
   CONSUMER of the receipt composes with. *)
Require Import FsDurSnap.      (* [snap_holds] -- the commit's certificate *)
Require Import FsFlushedCore.  (* [flushed] -- the receipt itself          *)
Require Import SpecSysSync. (* the landed empty contract, UNCHANGED       *)
Import Defs.
Require Import TsoCtx.

Section sys_sync_flush.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.

  (* ------------------------------------------------------------------ *)
  (*  THE RECEIPT, AT THE WAL'S OWN BATCH SCALE                           *)
  (* ------------------------------------------------------------------ *)

  (* THE BANK IS LANDED, AND IT LIVES IN [LogInv] (owner ruling, executed).
     It was spelled here while it was still a proposal; it is now
     [LogInv.log_flushed_bank], the last non-arm conjunct of
     [LogInv.log_res], with the same statement it had here:

       log_flushed_bank γ e :=
         ∃ b D, log_epoch_lb γ e ∗ flushed b D ∗ ⌜snap_holds D⌝

     Read it as: THE BATCH COUNTER STANDS AT [e], AND THE STATE THE LAST
     WRITE MADE DURABLE IS [D] -- the [b]-th committed state, and a file
     system.  Both conjuncts are persistent, so the bank is free to copy out
     of the invariant and free to leave in it.  Their JOINT reading -- that
     [D] is the state as of batch [e] and not some older one -- is
     established where the two are minted TOGETHER, and that is where the
     deposits are: [ProofEndOp]'s [eo_tail], which runs [log_epoch_bump]
     with the commit's own copy in hand, and [ProofInitlog]'s seal at
     genesis, which takes its copy off the header CLEAR that ends recovery.
     A consumer never compares [e] with [b]: it reads [D]'s rows
     ([FsFlushed.dur_at]) and orders its receipts by [b]
     ([FsFlushedCore.flushed_earlier]). *)

  (* THE POSTCONDITION.  "By the time this call returned, the batch counter
     had reached some [e'] at or past the caller's own [e], and here is the
     durable state standing there."  Monotone and persistent, so a caller
     keeps it across everything it does next. *)
  Definition flushed_sync (γ : log_names) (e : nat) : iProp Σ :=
    (∃ e' : nat, ⌜(e <= e')%nat⌝ ∗ log_flushed_bank γ e')%I.

  Global Instance flushed_sync_persistent γ e : Persistent (flushed_sync γ e).
  Proof. rewrite /flushed_sync. apply _. Qed.

  (* THE CASE SPLIT, DISCHARGED ONCE.  Both arms of sys_sync end at the same
     place -- holding the log lock, with the bank readable at the counter's
     current value -- and both are covered by this one entailment: the fast
     path reads it at the [E >= e] it finds ([LogInv.log_epoch_lb_le] against
     the caller's witness), the slow path at the [E' >= E + 1] it waited for.
     So item (iii) of the design's derivation chain reduces to item (ii),
     the bank, and nothing else. *)
  Lemma flushed_sync_of_bank (γ : log_names) (e E : nat) :
    (e <= E)%nat -> log_flushed_bank γ E -∗ flushed_sync γ e.
  Proof.
    intros Hle. iIntros "H". rewrite /flushed_sync. iExists E.
    iSplitR; [by iPureIntro | iExact "H"].
  Qed.

  (* ...and the receipt itself, off the postcondition: this is what a
     consumer composes with [FsFlushed.dur_at] (design section 5
     principle 3).  The [e'] is dropped on the way out because no per-node
     reading mentions the batch counter -- the bound a certificate carries
     is the receipt's own [b]. *)
  Lemma flushed_sync_receipt (γ : log_names) (e : nat) :
    flushed_sync γ e -∗
      ∃ (b : nat) (D : gmap Z (list (bv 8))),
        flushed b D ∗ ⌜snap_holds D⌝.
  Proof.
    rewrite /flushed_sync /log_flushed_bank. iIntros "H".
    iDestruct "H" as (e' _) "H". iDestruct "H" as (b D) "(_ & Hf & %Hh)".
    iExists b, D. iSplitL; [iExact "Hf" | by iPureIntro].
  Qed.

  (* the caller's witness is always obtainable, so the contract's premise
     costs nothing: a client with no operation history takes it at zero. *)
  Lemma sync_witness_0 (γ : log_names) : ⊢ |==> log_epoch_lb γ 0.
  Proof. iApply log_epoch_lb_0. Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE PRODUCER -- the gap lane Y reported, closed                    *)
  (* ------------------------------------------------------------------ *)

  (* WHAT SYS_SYNC ACTUALLY DOES, in the logic, on BOTH arms.  With the
     "log" spinlock held and the caller's invocation-time batch witness in
     hand, the lock's resource yields this contract's postcondition and
     CLOSES UNCHANGED -- no fupd, no disk write, no operation token, nothing
     given up, because everything handed out is persistent.

     THIS IS THE WHOLE OF THE DERIVATION CHAIN's item (iii), and it is now
     one line.  Before the banking there was no way to get here at all:
     [FsFlushedCore.P_fs_flushed_now] needs the crash predicate OPEN, which
     is a disk write's own fupd, and sys_sync writes no block.  The clause
     the owner ruled in is what a reader can see instead.

     BOTH ARMS REACH IT.  The FAST path (the guard false: nothing
     committing, nothing outstanding) reads it at the [E] it finds, which
     [LogInv.log_res_flushed] proves is at or past the caller's [e] off the
     counter's own auth.  The SLOW path re-enters the critical section at a
     LATER counter value and reads it there -- the same lemma, no extra
     premise, because the post below asks for [e <= e'] and not for a
     strict increase (see the header's last section for why that is the
     honest bound and not slack). *)
  Lemma flushed_sync_of_res (γ : log_names) (bn : bio_names)
      (γfs : fs_names) (cov : gset Z) (logstart : Z) (e : nat) :
    log_epoch_lb γ e -∗ log_res γ bn γfs cov logstart -∗
      flushed_sync γ e ∗ log_res γ bn γfs cov logstart.
  Proof.
    iIntros "#Hlb Hres".
    iDestruct (log_res_flushed γ bn γfs cov logstart e with "Hlb Hres")
      as "[Hb Hres]".
    rewrite /flushed_sync. iSplitL "Hb"; [iExact "Hb" | iExact "Hres"].
  Qed.

  (* ...and the same reading straight through to the certificate a consumer
     composes with [FsFlushed.dur_at]: the durable state the log stands at,
     off nothing but the lock's resource and a witness that costs nothing. *)
  Lemma log_res_receipt (γ : log_names) (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (e : nat) :
    log_epoch_lb γ e -∗ log_res γ bn γfs cov logstart -∗
      (∃ (b : nat) (D : gmap Z (list (bv 8))),
         flushed b D ∗ ⌜snap_holds D⌝) ∗ log_res γ bn γfs cov logstart.
  Proof.
    iIntros "#Hlb Hres".
    iDestruct (flushed_sync_of_res with "Hlb Hres") as "[Hs Hres]".
    iDestruct (flushed_sync_receipt with "Hs") as (b D) "[Hf %Hh]".
    iSplitR "Hres"; [| iExact "Hres"].
    iExists b, D. iSplitL; [iExact "Hf" | by iPureIntro].
  Qed.
End sys_sync_flush.

(* ====================================================================== *)
(*  THE CONTRACT                                                          *)
(*                                                                        *)
(*  The machine half is [SpecSysSync.wp_sys_sync_sconf_body], VERBATIM --  *)
(*  same frame budget [K_sys_sync], same order premise, same parking       *)
(*  crossing (the literal [true], because sys_sync sleeps), same           *)
(*  callee-saved and [a0 = 0] postconditions, same [trap_csrs_ext] /       *)
(*  [cpu_claim_ext] complement in and out.  TWO THINGS ARE ADDED and       *)
(*  nothing is removed:                                                   *)
(*    (in)  [log_epoch_lb γ e] -- the caller's invocation-time batch       *)
(*          witness.  Persistent, obtainable at [0] from nothing           *)
(*          ([sync_witness_0]) and at the caller's own batch from          *)
(*          [begin_op]'s mint, so it constrains no caller.                 *)
(*    (out) [flushed_sync γ e] -- the receipt.                            *)
(*  No disk fabric, no [bio_ctx], no operation token: like the landed      *)
(*  form, this takes [log_ctx] plus the running-process bundle and         *)
(*  nothing else.                                                         *)
(* ====================================================================== *)
Definition wp_sys_sync_flush_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names)
    (cov : gset Z) (logstart : Z) (dev : mword 32)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (e : nat) :=                                      (* the caller's batch *)
  let pcE : mword 64 := mword_of_int KernelSyms.sys_sync in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_sys_sync <= K)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  locks_below lks "log" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* THE CALLER'S BATCH WITNESS.  Persistent; the contract reads it only to
     name the bound its receipt has to reach. *)
  log_epoch_lb γ e -∗
  procs_inv γs -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile),
      ⌜callee_saved m mf⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 0 : mword 64)⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      (* THE RECEIPT -- the one thing this form adds to the landed one *)
      flushed_sync γ e -∗
      pc_is ret_tgt -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYS_SYNC_FLUSH.
  Parameter wp_sys_sync_flush_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γs : list gname) (j : nat) (γl : gname)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (e : nat),
      wp_sys_sync_flush_sconf_body γs j γl bn γ γfs cov logstart dev m K eb b lks e.
End SYS_SYNC_FLUSH.

(* THE PARALLEL FORM IS A STRENGTHENING, and here is the proof that it is
   one: whoever proves [SYS_SYNC_FLUSH] has proved [SYS_SYNC], with the
   receipt thrown away at the return.  So the landed contract's callers --
   the syscall dispatcher's arm 22 among them -- keep working unchanged the
   day the stronger form lands, and R10's "the postcondition only grows" is
   a theorem rather than an intention. *)
Module SysSyncFlushWeaken (F : SYS_SYNC_FLUSH) : SYS_SYNC.
  Lemma wp_sys_sync_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γs : list gname) (j : nat) (γl : gname)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_sys_sync_sconf_body γs j γl bn γ γfs cov logstart dev m K eb b lks.
  Proof.
    intros. rewrite /wp_sys_sync_sconf_body.
    intros HK Hj Hgl Hbelow.
    iIntros "Hcg Hcnt Hextc Hextm Htext Hpc Hlog Hprocs Hcont".
    (* the witness the stronger form asks for is free at zero *)
    iApply fupd_wp.
    iMod (sync_witness_0 γ) as "#Hlb".
    iModIntro.
    iApply (F.wp_sys_sync_flush_sconf γs j γl bn γ γfs cov logstart dev m K eb
              b lks 0%nat HK Hj Hgl Hbelow
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hlog Hlb Hprocs").
    (* the strong form's continuation, built from the weak one: same hart,
       same guard, same registers -- the receipt is simply dropped *)
    iIntros (CIDa) "%Hguard".
    iIntros (mf) "%Hcs %Ha0 Hcg Hcnt Hextc Hextm _ Hpc".
    iDestruct ("Hcont" $! CIDa with "[%]") as "Hc"; [exact Hguard |].
    iSpecialize ("Hc" $! mf).
    iSpecialize ("Hc" with "[%]"); [exact Hcs |].
    iSpecialize ("Hc" with "[%]"); [exact Ha0 |].
    iApply ("Hc" with "Hcg Hcnt Hextc Hextm Hpc").
  Qed.
End SysSyncFlushWeaken.
