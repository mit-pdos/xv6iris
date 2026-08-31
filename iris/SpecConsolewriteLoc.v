(* SpecConsolewriteLoc.v -- consolewrite's LOCATED trace contract: the
   PARALLEL FORM of [SpecConsolewrite.wp_consolewrite_sconf_body] (R10 --
   the landed contract does not move, and this file adds a second one
   beside it).

   Worklist: claude-notes/projects/fs-syscall-specs.md, the console-write
   lane; the plan is [SpecSysWriteConsAU.v]'s "WHAT THE PROVER OWES" item 4:

       a located parallel form of SpecConsolewrite threading the seed
       through the chunk loop ([uart_sent_from_chain] is the glue; the
       count bookkeeping [i += nn] only after a full chunk push gives the
       arms' length equations).

   WHAT IT ADDS TO THE LANDED CONTRACT, and it is the whole diff: the seed
   [uart_sent γu tr0] as a premise, and [cons_sent_cnt γu tr0 r] as a
   postcondition beside the landed range fact [0 <= r <= Z.max 0 n].

   THE COUNT IS THE RECEIPT'S LENGTH, and that is what makes this contract
   worth stating.  consolewrite has NO failing exit: a copy that faults
   BREAKS and the count already pushed is the answer, and [i += nn] runs
   only AFTER [uartwrite(buf, nn)] returned, i.e. only after all [nn] bytes
   of that chunk were accepted.  So at every exit the returned [r] is
   exactly the number of bytes this call handed the UART -- which is the
   equation [SpecSysWriteConsAU]'s OK and SHORT arms are stated on
   ([wcons_ok] at [r = n], [wcons_short] at [r < n]; one predicate serves
   both because consolewrite cannot tell them apart and does not need to).

   ...AND SINCE RULING A (2026-08-31) IT SAYS WHICH BYTES.  The receipt used
   to claim LENGTH and ORDER only, because [either_copyin]'s user arm handed
   the destination back at an existential content.  It does not any more:
   [SpecEitherCopyin.either_copyin_post] relays [SpecCopyin.copyin_got] on
   its success exit, so each chunk's bytes are pinned to the process's own
   image, and [cons_sent_cnt] carries the join --
   [SpecCopyin.ubytes_at (us_M U) uaddr bs] beside the length.  That is what
   makes "init's printf printed THESE characters" stateable: the accepted
   run IS the caller's buffer, byte for byte, at the image it lent.

   WHAT IS STILL NOT CLAIMED is the WIRE, not the bytes: this is an
   ACCEPTANCE receipt (SpecSysWriteConsAU.v's header is the design of
   record for why), and SpecConsolewrite.v's landed header keeps the old
   stance because the landed contract does not carry the seed at all.

   EVERYTHING ELSE IS [SpecConsolewrite.v] LINE FOR LINE -- same binders,
   same premises in the same order, same frame, same stack budget, same
   parking and lock-rank premises, same image discipline.  The walk
   ([ProofConsolewriteLoc.v]) is the matching diff against
   [ProofConsolewrite.v]. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
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
Require Import ProcGeom CpuOwn.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import FdSlots ProcInv.
Require Import FileInvDefs.
Require Import DiskPtsto WpUart.
Require Import UartTxInv.
Require Import UartSentLoc.       (* [uart_sent_from]: the located receipt *)
Require Import SpecCopyin.        (* [ubytes_at]: the content seam        *)
Require Import SpecConsolewrite.  (* the landed contract this parallels;
                                     [consolewrite_stack] *)
Require Import SchedCtx.
Require Export SwtchCtx.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Import Defs.
Local Open Scope Z_scope.

Section ConsSentCnt.
  Context `{!riscvGS Σ, !xv6G Σ}.

  (* THE DEVICE-WRITE RECEIPT AT A COUNT: [r] bytes were accepted by the
     UART, in order, after the seed -- AND THEY ARE THE CALLER'S OWN BYTES,
     the process's run at user va [ua] in the image [M] it lent (RULING A,
     the content seam; [SpecCopyin.ubytes_at]).  This is
     [SpecSysWriteConsAU.wcons_ok]'s body at [n := r], which is how the
     syscall's OK and SHORT arms are both read off it.

     THE BYTE STRING IS STILL BOUND EXISTENTIALLY and that is not a
     weakness: [M] is a PARTIAL map, so "the bytes at [ua]" is not a
     function this layer can apply; the equation pins every one of them
     against the image the caller handed in, which is the whole of what
     "printf printed MY characters" needs. *)
  Definition cons_sent_cnt (γu : uart_names) (tr0 : list (bv 8))
      (M : gmap Z (bv 8)) (ua : mword 64) (r : Z) : iProp Σ :=
    (∃ bs : list (bv 8),
       ⌜Z.of_nat (length bs) = r⌝ ∗ ⌜ubytes_at M ua bs⌝ ∗
       uart_sent_from γu tr0 bs)%I.

  Global Instance cons_sent_cnt_persistent γu tr0 M ua r :
    Persistent (cons_sent_cnt γu tr0 M ua r).
  Proof. apply _. Qed.

  (* the empty call's receipt, free from the seed: the [n <= 0] exit and the
     loop's entry both start here *)
  Lemma cons_sent_cnt_zero (γu : uart_names) (tr0 : list (bv 8))
      (M : gmap Z (bv 8)) (ua : mword 64) :
    uart_sent γu tr0 -∗ cons_sent_cnt γu tr0 M ua 0.
  Proof.
    iIntros "H". iExists []. iSplitR; [done|].
    iSplitR; [iPureIntro; apply ubytes_at_nil|].
    by iApply uart_sent_from_refl.
  Qed.

  (* THE SEED FOR THE NEXT CHUNK, read off the receipt one already holds.
     Every field is persistent or pure, so this DOES NOT CONSUME the
     receipt -- the walk keeps it for the exit that returns [r] unchanged
     (consolewrite's copy-failed break) and uses the [tr1] it hands out to
     seed the next [uartwrite]. *)
  Lemma cons_sent_cnt_seed (γu : uart_names) (tr0 : list (bv 8))
      (M : gmap Z (bv 8)) (ua : mword 64) (r : Z) :
    cons_sent_cnt γu tr0 M ua r -∗
    ∃ (tr1 bs1 : list (bv 8)),
      ⌜Z.of_nat (length bs1) = r⌝ ∗ ⌜ubytes_at M ua bs1⌝ ∗
      ⌜tr0 `prefix_of` tr1⌝ ∗
      ⌜bs1 `sublist_of` drop (length tr0) tr1⌝ ∗ uart_sent γu tr1.
  Proof.
    iIntros "H". iDestruct "H" as (bs1) "(%Hlen & %Hby & Hfrom)".
    iDestruct "Hfrom" as (tr1) "(#Htr & %Hp & %Hs)".
    iExists tr1, bs1. by iFrame "Htr".
  Qed.

  (* THE CHUNK STEP, and the only genuinely new fact in this file: a receipt
     for [r] bytes, followed by a located receipt for [k] more bytes seeded
     at the first one's own trace witness, is a receipt for [r + k].  This is
     [i += nn] in the logic -- the count bookkeeping and the trace
     bookkeeping are the same step, which is why the returned count IS the
     receipt's length at every exit. *)
  Lemma cons_sent_cnt_chunk (γu : uart_names) (tr0 tr1 : list (bv 8))
      (M : gmap Z (bv 8)) (ua : mword 64)
      (r : Z) (bs1 bs2 : list (bv 8)) :
    Z.of_nat (length bs1) = r ->
    tr0 `prefix_of` tr1 ->
    bs1 `sublist_of` drop (length tr0) tr1 ->
    (* the two content halves: what is already accepted, and what this chunk
       copied -- the latter at the BUMPED base, which is exactly the
       [add a2,si,sbase] the loop performs *)
    ubytes_at M ua bs1 ->
    ubytes_at M (add_vec_int ua (Z.of_nat (length bs1))) bs2 ->
    uart_sent_from γu tr1 bs2 -∗
    cons_sent_cnt γu tr0 M ua (r + Z.of_nat (length bs2)).
  Proof.
    iIntros (Hlen Hp Hb Hb1 Hb2) "H".
    iExists ((bs1 ++ bs2)%list). iSplitR.
    { iPureIntro. rewrite length_app. lia. }
    iSplitR; [iPureIntro; exact (ubytes_at_app M ua bs1 bs2 Hb1 Hb2)|].
    by iApply (uart_sent_from_chain γu tr0 tr1 bs1 bs2 Hp Hb with "H").
  Qed.

End ConsSentCnt.

Definition wp_consolewrite_loc_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γa : gname) (γf : gname)
    (γs : list gname) (j : nat) (γlp : gname)
    (γu : uart_names) (γv : disk_names) (γl : gname)
    (m : regfile) (av : nat) (eb : bool)
    (pid : mword 32) (U : ustate) (n : Z) (b : bool) (lks : gset string)
    (tr0 : list (bv 8)) :=
  let pcE : mword 64 := mword_of_int KernelSyms.consolewrite in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* THE USER SOURCE, named (RULING A).  a1 was unconstrained and unnamed
     until the content seam; it is a [let], not a premise, so no caller
     moves. *)
  let uaddr : mword 64 := m !!! Regidx (mword_of_int 11 : mword 5) in
  (j < NPROC)%nat ->
  γs !! j = Some γlp ->
  length γs = NPROC ->
  m !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 1 : mword 64) ->
  m !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int n : mword 64) ->
  (- 2 ^ 31 <= n < 2 ^ 31)%Z ->
  (consolewrite_stack <= av)%nat ->
  eb = true ->
  locks_below lks "proc" ->
  sie_cap_gpr KT1 m av b pj -∗
  cpu_own 0%nat eb pj b lks -∗
  kernel_text -∗ pc_is pcE -∗
  proc_priv_core pj pid U -∗
  kalloc_env γa None -∗
  dev_inv γu γv -∗
  is_txlock γl γu -∗
  procs_inv γs -∗
  (* ---- THE SEED: the one addition to the landed premises.  Persistent,
     and free at [[]] ([UartSentLoc.uart_sent_nil]). ---- *)
  uart_sent γu tr0 -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (r : Z) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P'⌝ -∗
      ⌜(0 <= r <= Z.max 0 n)%Z⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int r : mword 64)⌝ -∗
      sie_cap_gpr KT1 mf av b pj -∗
      cpu_own 0%nat eb pj b lks -∗
      pc_is ret_tgt -∗
      proc_priv_core pj pid (us_upt U P') -∗
      (* THE RECEIPT, at the returned count: [r] bytes accepted, in order,
         after the seed, AND THEY ARE THE BYTES AT [a1] in the image the
         caller lent (RULING A).  Persistent -- the caller keeps it forever.
         [us_M U] is the INPUT image and stays the right one to state it
         against: consolewrite only READS user memory, and the pages a copy
         faults in were already in the view. *)
      cons_sent_cnt γu tr0 (us_M U) uaddr r -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type CONSOLEWRITE_LOC.
  Parameter wp_consolewrite_loc_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γa : gname) (γf : gname) (γs : list gname) (j : nat) (γlp : gname)
      (γu : uart_names) (γv : disk_names) (γl : gname)
      (m : regfile) (av : nat) (eb : bool)
      (pid : mword 32) (U : ustate) (n : Z) (b : bool) (lks : gset string)
      (tr0 : list (bv 8)),
      wp_consolewrite_loc_sconf_body γa γf γs j γlp γu γv γl m av eb pid U n b lks tr0.
End CONSOLEWRITE_LOC.
