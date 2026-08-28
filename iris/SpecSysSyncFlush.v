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

   ======================= WHAT IS STILL OWED ==========================

   THIS MODULE TYPE HAS NO IMPLEMENTING FUNCTOR YET, deliberately, and
   nothing in the tree instantiates it (there is no [LinkSysSyncFlush]).
   What stands between it and a proof is ONE conjunct of [LogInv.log_res]:

     THE BANK.  The committer already HOLDS the receipt this contract
     returns -- it is [FsCrash.fs_commit_L_seq_permit]'s residual, which
     [ProofEndOp] takes at the [write_head] call and drops one line later
     ("the receipt is dropped: nothing in this stage consumes a durability
     receipt -- sys_sync is phase D's").  It must instead be carried to the
     re-deposit at the end of the commit, where the same proof bumps the
     batch counter ([LogInv.log_epoch_bump], ProofEndOp's [Hommt] step), and
     deposited there as [log_flushed_bank] below.  Being PERSISTENT, it
     costs the invariant nothing to hand back out: every later opener of the
     log lock -- sys_sync's three reads of the cells included -- takes a
     copy and closes with the invariant unchanged.

   [log_flushed_bank] is spelled below as a real definition, so that the
   owner's decision is a diff against something that type-checks rather
   than against prose, and [flushed_sync_of_bank] PROVES that the bank is
   enough for this contract on BOTH arms.  What the decision costs is
   measured in lane Y's report: the conjunct re-elaborates [LogInv.v] and
   therefore the whole proof tree, and it breaks the positional patterns at
   ~14 sites in ProofBeginOp / ProofEndOp / ProofLogWrite / ProofInitlog
   (ProofSysSync's own three openers survive it -- they close with
   [iExact "Hrest"]).  It changes NO arity: not [log_ctx]'s, not
   [wp_end_op]'s, not [log_names]'.

   A SECOND, SMALLER DEBT lives beside it and is named here because a
   prover will meet it first: [log_res] binds the [log.ncommit] CELL
   existentially and says nothing about its value ([LogInv.v]'s
   [l_ncommit ↦₄ nc]), and [ProofSysSync]'s wait loop accordingly carries
   no [nc] binder at all -- each iteration re-reads an unrelated value and
   the back edge is discharged by a raw case split.  Proving that the WAIT
   ends at a LATER batch than it started needs the cell tied to the ghost
   counter ([⌜uint nc = Z.of_nat E⌝] or its off-by-one) and the loop
   invariant re-stated over that tie.  The FAST path needs neither: it
   reads the bank and returns.

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
Require Import FsDurSyscall. (* [snap_holds] -- the commit's own certificate *)
Require Import FsFlushed.   (* [flushed], [dur_at]; the receipt itself      *)
Require Import SpecSysSync. (* the landed empty contract, UNCHANGED       *)
Import Defs.

Section sys_sync_flush.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.

  (* ------------------------------------------------------------------ *)
  (*  THE RECEIPT, AT THE WAL'S OWN BATCH SCALE                           *)
  (* ------------------------------------------------------------------ *)

  (* WHAT THE LOG INVARIANT MUST CARRY (the bank; see the header).  Read
     it as: THE BATCH COUNTER STANDS AT [e], AND THE STATE THE LAST COMMIT
     MADE DURABLE IS [D] -- the [b]-th committed state, and a file system.

     Both conjuncts are landed resources and both are persistent, so the
     bank is free to copy out of the invariant and free to leave in it.
     Their JOINT reading -- that [D] is the state as of batch [e] and not
     some older one -- is established where the two are minted TOGETHER,
     which is the one place it can be: the commit's re-deposit, which bumps
     the counter with the commit's own receipt in hand.  Nothing weaker
     would do, and nothing stronger is needed: a consumer never compares
     [e] with [b], it reads [D]'s rows ([FsFlushed.dur_at]) and orders its
     receipts by [b] ([FsFlushed.flushed_earlier]). *)
  Definition log_flushed_bank (γ : log_names) (e : nat) : iProp Σ :=
    (∃ (b : nat) (D : gmap Z (list (bv 8))),
       log_epoch_lb γ e ∗ flushed b D ∗ ⌜snap_holds D⌝)%I.

  Global Instance log_flushed_bank_persistent γ e :
    Persistent (log_flushed_bank γ e).
  Proof. rewrite /log_flushed_bank. apply _. Qed.

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
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
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
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
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
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
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
