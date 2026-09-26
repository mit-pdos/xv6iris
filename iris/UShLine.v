(* ===================================================================== *)
(* UShLine.v -- SH-LINE 2b PHASE 2: SH'S CONSOLE READ, SUPPLIED.          *)
(*                                                                        *)
(* [UConsLine.ush_read_recv_leaf] is the read leaf sh's [gets] wants: the  *)
(* one that KEEPS the kernel's receipt, so the shell learns that the byte  *)
(* it was handed is the next one after the byte it was handed last.  Two   *)
(* things have to happen for that leaf to exist, and both need the         *)
(* CONCRETE deposit bundle ([UexecExecInst]'s instance of                  *)
(* [UexecSG.uexecSG]) in scope -- which is why this file is here and not   *)
(* beside [UkSh.v] or [UShKernel.v], where the class is abstract           *)
(* (SH-LINE 2b phase 1's finding).                                        *)
(*                                                                        *)
(*  S1  THE FAMILY.  read's deposit and read's post are read at the SAME   *)
(*      [UexecSG.sfam], so a program that wants to be told something about *)
(*      its window has to NAME the family it deposited.  [xfam_rd] is      *)
(*      [UexecExecInst.xfam]'s point at two fields: the process's own exit *)
(*      payload ([kf_xpay], which [UkRun.udepwf_std]'s pure row demands)   *)
(*      and [rf_ret] -- WHAT THE CALLER ASKS TO BE TOLD.                   *)
(*                                                                        *)
(*  S2/S3  THE ACCESS LEMMA AND THE DISCHARGE ARE GONE (lane ECHO-OUT    *)
(*      part 5).  [ush_read_sup] built read(5)'s console deposit out of    *)
(*      the reader lease and the boundary's INPUT LICENCE, and             *)
(*      [ush_read_recv_leaf_holds] discharged [UkSh.ush_read_recv_leaf]    *)
(*      from the two.  At the echo application's REAL input claim          *)
(*      ([EchoOut.ecl]) the flat [WpUart.cons_licence] is FALSE -- the       *)
(*      claim's non-taint arms pin the delivered sequence and its count,   *)
(*      so moving [dl] needs the READER's half of [EchoOut.dl_cnt], which  *)
(*      the lease does not carry yet.  The leaf is therefore OWED, at the  *)
(*      statement [ush_read_recv_leaf_holds] used to prove, from           *)
(*      [UInitBootAdequacy]'s [Hsh_owed] through                           *)
(*      [UInitBoot.echo_Hinit_boot]; lane IO-LEAF paid it (S5-S7 below), *)
(*      and [Hsh_owed] is GONE entirely since redesign R3.                *)
(*      Section S2 below carries the full argument.                        *)
(*                                                                        *)
(*  S5/S6/S7  THE READ SIDE ON THE ERA'S OWN LINK, AND THE LEAF PAID     *)
(*      (lane IO-LEAF, M5).  S5 rebuilds the access lemma at              *)
(*      [EchoLinks.echo_link_rd]: the console deposit's boundary half is  *)
(*      the era's read link at sh's own delivered count now, not the      *)
(*      licence, and the credential it spends comes off SH'S OWN LEASE    *)
(*      ([UserConsole.ucons_pay]'s [Rd], under the same existential as    *)
(*      the cursor).  It also proves the bridge the survey called for:    *)
(*      the byte the call delivered IS the era's input at sh's own count, *)
(*      and the input it extends to is DISCIPLINED.  S6 is the LEAF on    *)
(*      that deposit, with the [-1] arm refuted at                        *)
(*      the console descriptor by TRAP-ROWS T2.  S7 is the OWED           *)
(*      statement, [ush_read_recv_leaf_holds], discharged -- so the S2/S3 *)
(*      note above is history; [Hsh_owed] went down to two conjuncts      *)
(*      here and was deleted outright by redesign R3.                     *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
(* THE GHOST BINDER LIST, each module IMPORTED and not merely required --
   naming a class without its defining module in scope introduces a FRESH
   Type variable and the kernel's [uexecSG] instance becomes invisible to
   resolution ([UInitSh.v]'s header). *)
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserHeap.
Require Import UexecSlot UexecRet UsysMemOk UexecSG.
Require Import UkRun UkRunSys.
Require Import UexecExecInst.      (* THE INSTANCE: [uexecSG_xv6] *)
Require Import UkReadRows.         (* the read leaf's SHARED key-level rows:
                                      [xfam_rd], the intro/elim pair, the two
                                      [fd_st_of_key] readings, the count *)
Require Import UkReadCons.         (* THE NEUTRAL CONSOLE MEMBER of the read
                                      leaf -- this file's leaf is its echo
                                      INSTANCE (lane RD-4) *)
Require Import SpecFileread.       (* [fileread_in] / [console_receipt] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import AppInv.      (* [app_sup], [app_rdcred] *)
Require Import FsCfg.
Require Import ConsoleInv.         (* [cons_acc] / [cons_out] / [CONSOLE] *)
Require Import WpUart.             (* [cons_read_pay]: E5's console I/O
                                      boundary (lane CONS-IO) *)
Require Import UserConsole.        (* [upos] / [ucons_pay] *)
Require Import UkSh.               (* [ush_narrow_count_le] *)
Require UkInit.                    (* [init_rd]: the exit family, the pair *)
(* THE ERA'S READ SIDE (lane IO-LEAF, M5).  [EchoOut] is the application's
   CLAIM and [EchoLinks] the program-side law built on it; this file names
   neither the boot record nor its four equations -- the law arrives as a
   premise, exactly as [UkSh.sh_deps] does.  [EchoOut] requires nothing
   above [SpecConsoleintr], so there is no cycle with the U tier. *)
Require Import LineWords.          (* [rest_of] / [wl_nl] *)
Require Import EchoOut.            (* [era_pin] / [dl_cnt] / [read_ret] *)
Require Import EchoLinksLine.      (* [ewc_lcred]: the loop's tight family (step 4) *)
Require Import LinkRec.            (* the era's link record: [lk_rres],
                                      [lk_ban_read_taint], [lk_lcred_read] *)
Require Import ReadRec.            (* the era's READ record: [rk_disc],
                                      [rk_rd], [rk_rd_taint], [rk_arms] *)
Require Import EchoLinks.          (* [echo_links] and its two read
                                      projections *)
Require Import CtxIdDefs.
Local Open Scope Z_scope.
Import Defs.

(* THE RING'S TRANSLATION ON A DISCIPLINED INPUT ([disc_input_no_cr]) and
   THE BYTE THE READ DELIVERED ([rr_byte_of_rows]) MOVED to [ReadRec.v]
   (lane LINK-GEN-4): they are what the echo instance of [ReadRec] is
   built out of, and that record sits below this file. *)

Section UShLine.
  (* THE KERNEL'S INSTANCE IS AMBIENT ([UInitSh.v]'s header): no local
     [Context {SG}] / [Context {PS}], and NO separate [uartGhostG] either
     -- [Xv6G.xv6_uart] is the one path from the bundle to the console
     ring's cameras, and it is what makes the program's spelling of the
     reader token and the ring's own ONE proposition
     ([UserConsole.ucons_reader_eq]). *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  (* the era's own cameras (lane IO-LEAF, M5).  A NARROW class beside the
     bundle, on [UShOut.v]'s and [UInitBanner.v]'s context list: the
     application's ghosts are not [Xv6G.xv6G]'s and binding a second copy
     of a bundle class is what makes the kernel's instance invisible. *)
  Context `{!echoOutG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).

  (* =================================================================== *)
  (*  S1  THE FAMILY                                                      *)
  (* =================================================================== *)
  (* [UexecExecInst.xfam] at the two fields read's rows look at, and the
     trivial ones everywhere else: a deposit is read at ONE number
     ([UexecExecInst.xv6_sbundle] is a match on it), so the rest of the
     record is inert.  [UInitConsK.xfam_mknod] is the mold. *)
  (* [Rin] IS A PARAMETER NOW (lane IO-LEAF, M5): read's console deposit
     carries [WpUart.cons_read_pay (S gen_id) (rf_in f)] beside the ring's
     own payment, and what sh asks to be told about the window it CONSUMED
     is the era's [EchoOut.read_ret] -- not [True], which was only ever
     payable while the application's input claim was [emp]. *)
  (* [xfam_rd] MOVED to [UkReadRows.v] (lane RD-4), beside its inode twin
     [xfam_rdf]: the two ARE the two arms of the read leaf, and neither file
     that needed one could see the other. *)

  (* WHAT SH ASKS TO BE TOLD.  A lease holder's choice: the window it was
     handed begins at ITS OWN position and its half of the pair comes back
     at the new one -- or the ring's marker moved behind its back
     ([ConsoleInv.cons_out]'s second disjunct), which for a constraining
     application is the taint, and then the number means nothing any more.
     THE TWO DISJUNCTS ARE NOT THE CALLER'S CHOICE: which one it gets is
     decided by whether a tokenless reader popped while the call slept. *)
  Definition ush_rd_ret (γp : gname) (T : iProp Σ) (n : nat)
      : nat -> nat -> iProp Σ :=
    (* ...AND THE LEASE COMES BACK WITH THE POSITION (lane KILL-PAY,
       K4(a)).  The reader token no longer rides in the run's payload row
       -- that row is a WAND from the kill credential now -- so it goes
       down into the call in the program's own hand and comes back here.
       The TAINTED arm hands back only the position:
       [UserConsole.ucons_pay_taint] rebuilds the payload from [T].
       ...AND IT COMES BACK IN PIECES, not as [UserConsole.ucons_pay]
       (lane IO-LEAF, M5).  The payload's left arm now carries the
       application's own per-position credential beside the token
       ([ucons_pay]'s [Rd]), and THAT credential is what the BOUNDARY half
       of the deposit returns -- in the receipt, not here.  The two halves
       of read's console arm fire independently, so the lease can only be
       reassembled where both answers are in hand, which is the leaf. *)
    fun cur dc =>
      ((⌜cur = n⌝ ∗ upos γp (n + dc)%nat
          ∗ ucons_reader fsc_cons (n + dc)%nat ∗ upos_a γp (n + dc)%nat)
       ∨ (T ∗ ∃ n' : nat, upos γp n'))%I.

  (* AT THE CLASS'S OWN FAMILY TYPE, not at [xfam] ([UConsOpen.v]'s note):
     the ecall leaves take [UexecSG.sfam], and an [xfam]-typed argument is
     checked before the instance evar is resolved and so does not
     convert. *)
  Definition ush_read_fam_at (γp : gname) (T : iProp Σ) (n : nat)
      (Rin : list (list mobs * bv 8) -> iProp Σ) (Q : Z -> iProp Σ) : sfam :=
    xfam_rd Q (ush_rd_ret γp T n) Rin.

  Definition ush_read_fam (γp : gname) (T : iProp Σ) (n : nat)
      (Q : Z -> iProp Σ) : sfam :=
    ush_read_fam_at γp T n (fun _ => True%I) Q.

  (* =================================================================== *)
  (*  S1b  THE TWO KEY-LEVEL ROWS MOVED (lane RD-4)                       *)
  (*                                                                      *)
  (*  [sbundle_at_read_intro_at] / [spost_at_read_elim_at] were this       *)
  (*  file's copies of the deposit's INTRO and the post's ELIM in the      *)
  (*  process's direction; [UkReadFile.v] carried the same two lemmas word *)
  (*  for word, because neither arm's file could see the other's.  They    *)
  (*  are one pair now, [UkReadRows.sbundle_at_read_intro] /               *)
  (*  [UkReadRows.spost_at_read_elim], and they say nothing about the      *)
  (*  descriptor -- which is exactly why there was only ever one of them.  *)
  (* =================================================================== *)

  (* THE DESCRIPTOR THE CALL RAN ON, out of the caller's own ledger: the
     arm [SpecFileread.fileread_in] takes is selected by the KEY's table,
     and what a program holds is the low [NSTD] slots of it. *)
  Lemma ush_fd_st_console (v0 : mword 64) (fdv l : list fdstate) (wr : bool) :
    bv_signed (trunc32 v0) = 0 ->
    take NSTD fdv = l ->
    l !! 0%nat = Some (FdOpen true wr (FdDevice CONSOLE)) ->
    fd_st_of_key v0 fdv = FdOpen true wr (FdDevice CONSOLE).
  Proof using .
    intros H0 Htake Hl0.
    exact (std_fd_st_of_key v0 fdv l 0%nat _ H0 ltac:(unfold NSTD; lia)
             Htake Hl0).
  Qed.

  (* =================================================================== *)
  (*  S2  THE ACCESS LEMMA IS GONE (lane ECHO-OUT part 5).                *)
  (*                                                                      *)
  (*  [ush_read_sup] built read(5)'s CONSOLE deposit out of the reader     *)
  (*  lease and the boundary's INPUT LICENCE, and [ush_read_recv_leaf_     *)
  (*  holds] below it discharged [UkSh.ush_read_recv_leaf] from the two.   *)
  (*  BOTH ARE DELETED, and the reason is that the second half of that     *)
  (*  payment stopped being free.  [SpecFileread.fileread_in]'s console    *)
  (*  arm is [ConsoleInv.cons_acc … ∗ WpUart.cons_read_pay (S gen_id)      *)
  (*  Rin]: the ring's own payment, which the lease pays, BESIDE the       *)
  (*  application's delivered-sequence link.  While the application's      *)
  (*  input claim was [emp] the link was free ([WpUart.cons_licence] at      *)
  (*  [RiscvPtsto.in_res_triv]) and this file took that licence as a       *)
  (*  Coq-level premise; at the echo application's REAL claim              *)
  (*  ([EchoOut.ecl]) the flat licence is FALSE -- the claim's two         *)
  (*  non-taint arms carry [⌜(dl ++ ws) `prefix_of` echoed pops⌝] and the  *)
  (*  delivered count [EchoOut.dl_cnt v (1/2) (length dl)], so an          *)
  (*  arbitrary window is refuted and moving [dl] at all needs the         *)
  (*  READER's other half of that ghost.  Only the taint arm is free,      *)
  (*  which is exactly what [App.al_sup] says, and the payload's      *)
  (*  LEASE arm ([UserConsole.ucons_pay]) carries no taint.                *)
  (*                                                                      *)
  (*  SO THE LEAF WAS OWED, NOT PROVED: a Coq-level premise of            *)
  (*  [UInitBoot.echo_Hinit_boot] and the third conjunct of                *)
  (*  [UInitBootAdequacy]'s [Hsh_owed], both since gone, on               *)
  (*  [UkSh.sh_deps]'s mould.  Lane IO-LEAF discharged it: it puts         *)
  (*  [EchoOut.era_pin] and the                                            *)
  (*  reader's [dl_cnt] half on sh's lease and runs the leaf through       *)
  (*  [EchoOut.echo_read_link], whose [WpUart.cons_link] hands over        *)
  (*  [⌜ConsLog.read_ok pops dl ws⌝].                                      *)
  (*  WHAT SURVIVES HERE is everything that never touched the licence:     *)
  (*  the read family, the two [sbundle] adapters, the two [fd_st]         *)
  (*  readings, [ush_count_is_cap], and the SHUT arm's deposit             *)
  (*  ([ush_read_sup_closed]).                                            *)
  (* =================================================================== *)

  (* =================================================================== *)
  (*  S3  THE DISCHARGE (header)                                          *)
  (* =================================================================== *)
  (* THE KERNEL'S COUNT IS THE CALLER'S REQUEST (lane CONS-ROWS).  The
     trapframe's argument 2 reaches file.c as a 32-bit INT
     ([SpecSysRead.sys_rw_count]) while the leaf names the request as a
     [nat] read off the same word unsigned; the two agree exactly below the
     sign boundary, which is [UConsLine.ush_read_recv_leaf]'s
     [Z.of_nat cap < 2 ^ 31] premise.  Above it the kernel really is
     answering a different request, so this is a bridge and not a
     formality. *)
  Lemma ush_count_is_cap (w : mword 64) (cap : nat) :
    uint w = Z.of_nat cap -> (Z.of_nat cap < 2 ^ 31)%Z ->
    sys_rw_count w = Z.of_nat cap.
  Proof using . exact (uread_count_is_cap w cap). Qed.
  (* THE DESCRIPTOR THE CALL RAN ON, at the row's OTHER arm: a SHUT fd 0.
     [SpecFileread.fileread_in]'s [FdClosed] arm asks for nothing and
     [fileread_extra_core]'s says [r = -1] (lane CLOSED-READ) -- so the
     shell's read leaf answers on both arms of [UkSh.ush_fd0p] and [gets]
     does not have to case split on which table it was handed. *)
  Lemma ush_fd_st_closed (v0 : mword 64) (fdv l : list fdstate) :
    bv_signed (trunc32 v0) = 0 ->
    take NSTD fdv = l ->
    l !! 0%nat = Some FdClosed ->
    fd_st_of_key v0 fdv = FdClosed.
  Proof using .
    intros H0 Htake Hl0.
    exact (std_fd_st_of_key v0 fdv l 0%nat _ H0 ltac:(unfold NSTD; lia)
             Htake Hl0).
  Qed.

  (* ...AND THE SUPPLY AT THAT ARM, which costs nothing at all: the shut
     descriptor's bundle is [P -∗ P], so the call spends no token and the
     caller keeps the position it came in with. *)
  (* AT ANY [Rin] (lane IO-LEAF, M5): the shut descriptor's arm of
     [SpecFileread.fileread_in] is [P -∗ P] and reads no boundary link at
     all, so the closed arm of the leaf costs the same whether the caller
     asked to be told about its window or not. *)
  Lemma ush_read_sup_closed (N : uk_names Σ) (γp : gname) (T : iProp Σ)
      (Rin : list (list mobs * bv 8) -> iProp Σ)
      (m : regfile) (pc : mword 64) (l : list fdstate) (n : nat) :
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = 0 ->
    l !! 0%nat = Some FdClosed ->
    ⊢ udepwf_std N m pc USYS_read
        (ush_read_fam_at γp T n Rin (ukn_pay N)) l.
  Proof using .
    intros Ha0 Hl0.
    rewrite /udepwf_std. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv cw gn cs pidv) "%Htake #Hmpay Hheap Hufd".
    iFrame "Hheap Hufd".
    iApply (sbundle_at_read_intro uslot
              (ush_read_fam_at γp T n Rin (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
              (m !!! Regidx a0_idx) (m !!! Regidx a2_idx) fdv
              (tf_of_arg0 m pc) (tf_of_arg2 m pc)
              (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false secc_all)).
    rewrite (ush_fd_st_closed (m !!! Regidx a0_idx) fdv l Ha0 Htake Hl0).
    rewrite /fileread_in. iIntros "HP". iExact "HP".
  Qed.

  (* =================================================================== *)
  (*  S5  THE ERA'S READ LINK AS SH'S DEPOSIT (lane IO-LEAF, M5)          *)
  (*                                                                     *)
  (*  S2 says why the flat input licence is FALSE at the echo             *)
  (*  application's real input claim, and what has to replace it: the     *)
  (*  READER's half of [EchoOut.dl_cnt] at sh's own cursor, spent through *)
  (*  [EchoOut.echo_read_link].  This section is the deposit, S6 the leaf *)
  (*  built on it, and the leaf IS the statement lane ECHO-OUT part 5     *)
  (*  left owed -- which took [UInitBootAdequacy]'s [Hsh_owed] down to    *)
  (*  two conjuncts on the way to deleting it (redesign R3).              *)
  (*                                                                     *)
  (*  WHERE THE HALF LIVES.  Not in a new conjunct of [UkSh.ush_at]: it   *)
  (*  is inside the CONSOLE LEASE the shell already carries, as the [Rd]  *)
  (*  of [UserConsole.ucons_pay], under the same existential as           *)
  (*  [upos_a].  That is the only place the era's delivered count and the *)
  (*  ring's cursor can be said to be the SAME number -- a holder of      *)
  (*  [upos γp n] pins the existential by [UserConsole.upos_agree] and    *)
  (*  reads the credential at its own [n] -- and it is what makes the     *)
  (*  credential round-trip: /init lends the lease at every fork          *)
  (*  ([uinit_lend]) and reaps it at every wait ([uinit_redeem]), so      *)
  (*  round [k > 0]'s shell is handed one exactly as round 0's is.        *)
  (* =================================================================== *)

  (* THE CREDENTIAL ITSELF -- [UserConsole.ucons_pay]'s [Rd] at the echo
     era.  The era pin is PERSISTENT and travels with the half only to
     name the era's ghosts; what is exclusive is the half. *)
  (* ...AND IT IS AT A LINE BOUNDARY (lane IO-LEAF, M5(3)).  The payload
     is what crosses between processes -- /init lends it at every fork and
     reaps it at every wait -- and what the NEXT shell needs to know about
     the count it is handed is that a LINE starts there: without it the
     first byte its [gets] takes is not the first byte of a line.  It is
     the payload and not the pieces that carries the fact, because the
     pieces are what a shell holds IN THE MIDDLE of a line, where it is
     false ([UkSh.ush_lease] is the mid-line form). *)
  (* THE READER'S RECEIPT RESIDUE (lane IO-LEAF, step 4): what the era's
     read link hands back at a window's far end, beyond the delivered
     count -- the reader's two bounds on the transcript's resolution and
     the WRITER'S cursor bound at the stream those bounds compute
     ([EchoOut.read_ret]'s trailing conjuncts, PROLOGUE-ALTS-3).  It is what
     refutes a credential that still owes the round's banner at a
     boundary the reader is past ([EchoLinks.wr_owed_read_refute]):
     [ush_wb_read_holds] below.  Persistent, so it rides the pieces and the
     lease's read side for free; at the boot it is the era's own turn at
     count 0 ([UInitBoot]). *)
  (* IT IS [LinkRec.lk_rres] AT THE ECHO INSTANCE (lane LINK-GEN-3).
     [LinkRec.echo_rres] spells this body for exactly this identity, and
     the two laws below are stated at [lk_rres] so that a second era
     supplies its own ([rd_stage_f] / [proc_before_f] at the file). *)
  Definition rd_res (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    (∃ ps0 cs0 : list nat,
       ⌜rd_stage ps0 cs0 I⌝ ∗ turn_lb v (length (proc_before ps0 cs0 I))
       ∗ ps_lb v ps0 ∗ cs_lb v cs0)%I.

  Global Instance rd_res_persistent v I : Persistent (rd_res v I).
  Proof using . rewrite /rd_res. apply _. Qed.
  Global Instance rd_res_timeless v I : Timeless (rd_res v I).
  Proof using . rewrite /rd_res. apply _. Qed.

  (* THE PAYLOAD IS AT A COUNT AND ITS CONTENT IS AN INPUT (project
     echo-any-line).  /init's side of the lease is position-indexed -- the
     ring's pair holds a NUMBER -- so the payload is a family over [n] and
     the era's input of that length is under the existential.  Two lower
     bounds of one era's echoed list that have the same length are the
     SAME list ([EchoOut.inp_lb_agree]), so nothing is lost by hiding it. *)
  Definition ush_rd_pin_at (Rres : era_pins -> list (bv 8) -> iProp Σ)
      (γ : echo_gn) (n : nat) : iProp Σ :=
    (∃ (v : era_pins) (I : list (bv 8)),
       ⌜length I = n /\ rest_of I = []⌝
       ∗ era_pin γ (S gen_id) v ∗ dl_cnt v (1/2) n
       ∗ inp_lb v I ∗ Rres v I)%I.

  Definition ush_rd_pin (γ : echo_gn) (n : nat) : iProp Σ :=
    ush_rd_pin_at rd_res γ n.

  Global Instance ush_rd_pin_at_timeless Rres γ n
      `{!forall (v : era_pins) (I : list (bv 8)), Timeless (Rres v I)} :
    Timeless (ush_rd_pin_at Rres γ n).
  Proof using . rewrite /ush_rd_pin_at. apply _. Qed.
  Global Instance ush_rd_pin_timeless γ n : Timeless (ush_rd_pin γ n).
  Proof using . rewrite /ush_rd_pin /ush_rd_pin_at. apply _. Qed.

  (* ...AND THE EXIT FAMILY (lane IO-LEAF, step 3): what sh's exit payload
     carries per count is the read side above AND the BANNER-OWED
     credential [Wb n] -- init's next round's banner is payable from it --
     which the shell reaches only at its shut-fd-0 exit with fd 2 closed.
     The right arm is AFFINE until step 4 (every other exit assembles the
     payload without a credential); it is spelled ONCE, at
     [UkInit.init_rd], and this is that family at the era's read side. *)
  Definition ush_rd_x_at (Rres : era_pins -> list (bv 8) -> iProp Σ)
      (γ : echo_gn) (Wb : list (bv 8) -> iProp Σ) (n : nat) : iProp Σ :=
    UkInit.init_rd (ush_rd_pin_at Rres γ)
      (fun m : nat => ∃ I : list (bv 8), ⌜length I = m⌝ ∗ Wb I)%I n.

  Definition ush_rd_x (γ : echo_gn) (Wb : list (bv 8) -> iProp Σ) (n : nat)
      : iProp Σ := ush_rd_x_at rd_res γ Wb n.

  Global Instance ush_rd_x_timeless γ Wb n
      `{!forall I : list (bv 8), Timeless (Wb I)} :
    Timeless (ush_rd_x γ Wb n).
  Proof using .
    rewrite /ush_rd_x /ush_rd_x_at /UkInit.init_rd /UkInit.init_rd_cred.
    apply _.
  Qed.

  (* =================================================================== *)
  (*  THE LEASE, UNBUNDLED (lane IO-LEAF, M5(3); [UkSh]'s [Pm]).          *)
  (*                                                                     *)
  (*  Between a line's first byte and its '\n' the shell's count is at no *)
  (*  boundary, so the payload above cannot be reassembled -- what the    *)
  (*  shell holds there is its PIECES: both halves of the position pair,  *)
  (*  the ring's reader token, and the era's own half of the delivered    *)
  (*  count.  The two laws below are what [UkSh] knows about them.        *)
  (* =================================================================== *)
  (* ...AND THE ERA'S INPUT ITSELF (lane IO-LEAF, M6a(3); project
     echo-any-line): [inp_lb v I] is what the era's read link hands back at
     a window's far end, and it is what the WRITE credential needs at the
     next line boundary ([EchoLinks.ewc_read]) -- so it rides with the
     pieces from the read that produced it to the boundary that spends it.
     Persistent, so it costs the payload nothing to carry ([ush_rd_pin] has
     it too, at the boot end from [EchoOut.eturn]). *)
  (* AT AN ABSTRACT RESIDUE (lane LINK-GEN-3).  The reader's receipt is
     the ONE place the era's own writer model reaches the shell's loop --
     [rd_stage] compares a reader's position against the WRITER's cursor
     -- so the residue is a parameter and [ush_mid] is this at the echo
     era's ([LinkRec.lk_rres (echo_link_inst T γ)], which is [rd_res]).
     The file application's round carries [ush_mid_at (lk_rres
     file_link_inst) (fgn_echo g) γp]: echo's ghost algebra verbatim, its
     own writer cursor. *)
  Definition ush_mid_at (Rres : era_pins -> list (bv 8) -> iProp Σ)
      (γ : echo_gn) (γp : gname) (I : list (bv 8)) : iProp Σ :=
    (upos γp (length I) ∗ upos_a γp (length I)
     ∗ ucons_reader fsc_cons (length I)
     ∗ ∃ v : era_pins, era_pin γ (S gen_id) v ∗ dl_cnt v (1/2) (length I)
                       ∗ inp_lb v I ∗ Rres v I)%I.

  Definition ush_mid (γ : echo_gn) (γp : gname) (I : list (bv 8)) : iProp Σ :=
    ush_mid_at rd_res γ γp I.

  (* WHAT THE ABSTRACT CREDENTIAL FAMILIES TELL THIS FILE ABOUT THEIR
     INPUT (project echo-any-line).  [Wc] and [Wb] are OPAQUE here -- the
     loop must not name an era -- but the seam between /init's
     position-indexed payload and sh's input-indexed credential has to
     identify the two inputs, and a length alone does not: what identifies
     them is that both are lower bounds of the SAME era's echoed list
     ([EchoOut.inp_lb_agree]).  So the reading is a Coq-level premise,
     discharged where the families are concrete
     ([UInitSh.cons_cred_holds] / [UInitBoot.echo_cc_holds]).  The
     banner-owed family's reading carries the BOUNDARY fact too, which is
     what [ush_at_of_mid_wb] spends: a credential that still owes a
     round's banner is owed at an input that closed its last line
     ([EchoLinks.wr_ban]). *)
  Definition ush_wc_inp (γ : echo_gn) (T : iProp Σ)
      (Wc : list (bv 8) -> nat -> iProp Σ) : Prop :=
    forall (I : list (bv 8)) (p : nat),
      ⊢ Wc I p -∗ Wc I p
        ∗ ((∃ v : era_pins, era_pin γ (S gen_id) v ∗ inp_lb v I) ∨ T).

  Definition ush_wb_inp (γ : echo_gn) (T : iProp Σ)
      (Wb : list (bv 8) -> iProp Σ) : Prop :=
    forall I : list (bv 8),
      ⊢ Wb I -∗ Wb I
        ∗ (((∃ v : era_pins, era_pin γ (S gen_id) v ∗ inp_lb v I)
            ∗ ⌜rest_of I = []⌝) ∨ T).

  (* ...AND THE TWO READINGS, AT THE FAMILIES THE APPLICATION PICKS.  The
     loop's tight credential and the banner-owed one both carry the era's
     input on their untainted arm, which is what the seam above needs.
     Proved here rather than at the boot assembly because the shapes are
     [EchoLinksLine]'s and this is the file that already names them. *)
  Lemma ush_wc_inp_lcred (γ : echo_gn) (T : iProp Σ) `{!Persistent T} :
    ush_wc_inp γ T (EchoLinksLine.ewc_lcred T γ (S gen_id)).
  Proof using .
    intros I p. iIntros "H".
    rewrite /EchoLinksLine.ewc_lcred.
    iDestruct "H" as (v) "[#Hpin Hc]".
    iAssert (EchoLinksLine.ewc_lpr T v I p ∗ (inp_lb v I ∨ T))%I
      with "[Hc]" as "[Hc #Hi]".
    { destruct p as [| [| [| p']]]; cbn [EchoLinksLine.ewc_lpr].
      - rewrite /EchoLinksLine.ewc_line /EchoLinksLine.ewc_pro
                /EchoLinksLine.ewc_post /EchoLinksLine.ewc_blk.
        iDestruct "Hc" as "[[Hl | #HT] | Hq]".
        + iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
          iSplitL "Htn".
          * iLeft. iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE".
            by iPureIntro.
          * iLeft. iExact "HE".
        + iSplit; [ iLeft; iRight; iExact "HT" | iRight; iExact "HT" ].
        + iDestruct "Hq" as (a) "[%Ha [Hl | #HT]]".
          * iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
            iSplitL "Htn".
            -- iRight. iExists a. iSplitR; [ by iPureIntro | ].
               iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE".
               by iPureIntro.
            -- iLeft. iExact "HE".
          * iSplit.
            -- iRight. iExists a. iSplitR; [ by iPureIntro | ].
               iRight. iExact "HT".
            -- iRight. iExact "HT".
      - rewrite /EchoLinksLine.ewc_sp_t.
        iDestruct "Hc" as "[Hl | #HT]".
        + iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
          iSplitL "Htn".
          * iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE". by iPureIntro.
          * iLeft. iExact "HE".
        + iSplit; [ iRight; iExact "HT" | iRight; iExact "HT" ].
      - rewrite /EchoLinksLine.ewc_open_t.
        iDestruct "Hc" as "[Hl | #HT]".
        + iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
          iSplitL "Htn".
          * iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE". by iPureIntro.
          * iLeft. iExact "HE".
        + iSplit; [ iRight; iExact "HT" | iRight; iExact "HT" ].
      - rewrite /EchoLinksLine.ewc_blk.
        iDestruct "Hc" as "[Hl | #HT]".
        + iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
          iSplitL "Htn".
          * iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE". by iPureIntro.
          * iLeft. iExact "HE".
        + iSplit; [ iRight; iExact "HT" | iRight; iExact "HT" ]. }
    iSplitL "Hc"; [ iExists v; iFrame "Hpin Hc" | ].
    iDestruct "Hi" as "[HE | HT]";
      [ iLeft; iExists v; iFrame "Hpin HE" | iRight; iExact "HT" ].
  Qed.

  Lemma ush_wb_inp_ban (γ : echo_gn) (T : iProp Σ) `{!Persistent T} :
    ush_wb_inp γ T
      (fun I : list (bv 8) => ∃ v : era_pins,
         era_pin γ (S gen_id) v ∗ EchoLinks.ewc_ban T v I 0%nat)%I.
  Proof using .
    intros I. iIntros "H". iDestruct "H" as (v) "[#Hpin Hc]".
    rewrite /EchoLinks.ewc_ban.
    iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iSplit; [ iExists v; iFrame "Hpin"; iRight; iExact "HT"
              | iRight; iExact "HT" ]. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iSplitL "Htn".
    - iExists v. iFrame "Hpin". iLeft. iExists ps, cs, P.
      iFrame "Htn Hps Hcs HE". by iPureIntro.
    - iLeft. iSplit.
      + iExists v. iFrame "Hpin HE".
      + iPureIntro. exact (proj1 (proj2 Hw)).
  Qed.

  (* the payload comes apart into the pieces: the credential slot of the
     exit family is DROPPED (nothing in the loop holds it) *)
  Lemma ush_mid_of_at (γ : echo_gn) (T : iProp Σ) `{!Persistent T}
      (Wb : list (bv 8) -> iProp Σ) (N : uk_names Σ) (γp : gname) (n : nat) :
    ukn_pay N = ucons_pay fsc_cons γp T (ush_rd_x γ Wb) ->
    ⊢ UkSh.ush_at N γp n -∗
      ∃ I : list (bv 8), ⌜length I = n⌝
        ∗ UkSh.ush_lease N γp T (ush_mid γ γp) I.
  Proof using .
    intro Hpay. rewrite /UkSh.ush_at /UkSh.ush_lease.
    iIntros "[Hpos Hlease]". iEval (rewrite Hpay /ucons_pay) in "Hlease".
    iDestruct "Hlease" as "[Hl | #HT]"; last first.
    { iExists (replicate n wl_nl).
      iSplitR; [ iPureIntro; apply length_replicate | ].
      iRight. iFrame "HT". rewrite /UkSh.ush_pos /UkSh.ush_at.
      iExists n. iFrame "Hpos". rewrite Hpay.
      iApply (ucons_pay_taint with "HT"). }
    iDestruct "Hl" as (n') "(Hrd0 & Hpa & Hcred)".
    iDestruct (upos_agree γp n n' with "Hpos Hpa") as %<-.
    rewrite /ush_rd_x /UkInit.init_rd /UkInit.init_rd_cred.
    iDestruct "Hcred" as "[Hcred _]".
    iDestruct "Hcred" as (v I) "([%Hlen %Hrest] & #Hpin & Hdl & #HE & #Hres)".
    iExists I. iSplitR; [ by iPureIntro | ].
    iLeft. rewrite /ush_mid /ush_mid_at Hlen. iFrame "Hpos Hpa Hrd0".
    iExists v. iFrame "Hpin Hdl HE Hres".
  Qed.

  (* ...and go back together at a boundary WITH THE BANNER-OWED
     CREDENTIAL: the exit family's own arm (its only one since lane
     EXEC-SEAM, (C)),
     which sh's shut-fd-0 exit assembles when its fd 2 was closed (step
     3; [UkSh.ush_at_of_pm_wb]'s discharge) *)
  Lemma ush_at_of_mid_taint (γ : echo_gn) (T : iProp Σ) `{!Persistent T}
      (Wb : list (bv 8) -> iProp Σ) (N : uk_names Σ) (γp : gname)
      (I : list (bv 8)) :
    ukn_pay N = ucons_pay fsc_cons γp T (ush_rd_x γ Wb) ->
    ⊢ T -∗ ush_mid γ γp I -∗ UkSh.ush_at N γp (length I).
  Proof using .
    intro Hpay. rewrite /ush_mid /ush_mid_at /UkSh.ush_at.
    iIntros "#HT (Hpos & _ & _ & _)". iFrame "Hpos". rewrite Hpay.
    iApply (ucons_pay_taint with "HT").
  Qed.

  Lemma ush_at_of_mid_wb (γ : echo_gn) (T : iProp Σ) `{!Persistent T}
      (Wb : list (bv 8) -> iProp Σ) (N : uk_names Σ) (γp : gname)
      (I : list (bv 8)) :
    ukn_pay N = ucons_pay fsc_cons γp T (ush_rd_x γ Wb) ->
    ush_wb_inp γ T Wb ->
    ⊢ ush_mid γ γp I -∗ Wb I -∗ UkSh.ush_at N γp (length I).
  Proof using .
    intros Hpay Hwbi. iIntros "Hmid Hb".
    iDestruct (Hwbi I with "Hb") as "[Hb Hrd]".
    iDestruct "Hrd" as "[[_ %Hrest] | #HT]"; last first.
    { iApply (ush_at_of_mid_taint γ T Wb N γp I Hpay with "HT Hmid"). }
    iEval (rewrite /ush_mid /ush_mid_at) in "Hmid".
    iDestruct "Hmid" as "(Hpos & Hpa & Hrd0 & Hcred)".
    rewrite /UkSh.ush_at. iFrame "Hpos". rewrite Hpay.
    iApply (ucons_pay_tok fsc_cons γp T (ush_rd_x γ Wb) (length I) (-1)
              with "Hrd0 Hpa [Hcred Hb]").
    rewrite /ush_rd_x /UkInit.init_rd /UkInit.init_rd_cred /ush_rd_pin.
    iSplitR "Hb"; last first.
    { iExists I. iSplitR; [ by iPureIntro | ]. iExact "Hb". }
    iDestruct "Hcred" as (v) "(#Hpin & Hdl & #HE & #Hres)".
    iExists v, I. iSplitR; [ by iPureIntro | ]. iFrame "Hpin Hdl HE Hres".
  Qed.

  (* THE WRITE CREDENTIAL'S STEP AT A READ (lane IO-LEAF, M6a(3)).  A line
     read leaves the pieces at [I ++ l ++ "\n"] carrying the era's input
     there,
     and that bound is exactly what takes the credential the prompt left
     ([EchoLinks.ewc_pr] at [2]) to the next boundary's ([0]):
     [EchoLinks.ewc_read].  The pieces come back untouched -- the bound is
     persistent -- so this is the ONE law [UkSh]'s loop needs about the
     credential beyond the prompt's own ([UkSh.ush_wc_read]). *)
  Lemma ush_mid_wc_read (γ : echo_gn) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T} (γp : gname) (I l : list (bv 8)) :
    wl_nl ∉ l ->
    ush_mid γ γp (I ++ l ++ [wl_nl]) -∗
    EchoLinks.ewc_cred T γ (S gen_id) I 2%nat -∗
    ush_mid γ γp (I ++ l ++ [wl_nl])
    ∗ EchoLinks.ewc_cred T γ (S gen_id) (I ++ l ++ [wl_nl]) 0%nat.
  Proof using .
    intro Hnl. iIntros "(Hpos & Hpa & Hrd0 & Hcred) Hc".
    iDestruct "Hcred" as (v) "(#Hpin & Hdl & #HE & #Hres)".
    rewrite /EchoLinks.ewc_cred. iDestruct "Hc" as (v') "[#Hpin' Hc]".
    iDestruct (era_pin_agree with "Hpin Hpin'") as %<-.
    iSplitR "Hc".
    { rewrite /ush_mid /ush_mid_at. iFrame "Hpos Hpa Hrd0". iExists v.
      iFrame "Hpin Hdl HE Hres". }
    iExists v. iFrame "Hpin".
    iEval (cbn [EchoLinks.ewc_pr]) in "Hc". cbn [EchoLinks.ewc_pr].
    iApply (EchoLinks.ewc_read T v I l Hnl with "HE Hc").
  Qed.

  (* ...AND THE SAME AT THE LOOP'S TIGHT FAMILY (step 4;
     [EchoLinksLine.ewc_lcred], what the top instantiates [Wc] at): the read
     leaves the BLOCK-OWED credential at the next boundary (index 3). *)
  (* THE ERA'S SIDE OF BOTH IS THE RECORD'S NOW (lane LINK-GEN-3): the
     read's step is [LinkRec.lk_lcred_read] and the refutation is
     [LinkRec.lk_ban_read_taint], both at [lk_epin] -- the ECHO-side pin,
     which is what the pieces carry at either era.  [Hep] is the one-way
     bridge from the pieces' own pin to the record's; it is the identity
     at echo and at the file alike ([lk_epin file_link_inst :=
     era_pin (fgn_echo g)]). *)
  Lemma ush_mid_wc_read_t_at (L : LinkRec Σ) (γ : echo_gn) (γp : gname)
      (k : nat) (I l : list (bv 8)) :
    wl_nl ∉ l ->
    (forall v : era_pins, ⊢ era_pin γ (S gen_id) v -∗ lk_epin L k v) ->
    ush_mid_at (lk_rres L) γ γp (I ++ l ++ [wl_nl]) -∗
    lk_lcred L k I 2%nat -∗
    ush_mid_at (lk_rres L) γ γp (I ++ l ++ [wl_nl])
    ∗ lk_lcred L k (I ++ l ++ [wl_nl]) 3%nat.
  Proof using .
    intros Hnl Hep. iIntros "(Hpos & Hpa & Hrd0 & Hcred) Hc".
    iDestruct "Hcred" as (v) "(#Hpin & Hdl & #HE & #Hres)".
    iSplitR "Hc".
    { rewrite /ush_mid_at. iFrame "Hpos Hpa Hrd0". iExists v.
      iFrame "Hpin Hdl HE Hres". }
    iDestruct (Hep v with "Hpin") as "#Hep".
    iApply (lk_lcred_read L k I l v Hnl with "Hep HE Hc").
  Qed.

  (* THE PIECES' PIN IS THE RECORD'S ECHO-SIDE PIN, at the echo instance *)
  Lemma ep_refl (γ : echo_gn) (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (v : era_pins) :
    ⊢ era_pin γ (S gen_id) v -∗ lk_epin (echo_link_inst T γ) (S gen_id) v.
  Proof using . by iIntros "$". Qed.

  (* ...AND THE SAME AT THE LOOP'S TIGHT FAMILY (step 4;
     [EchoLinksLine.ewc_lcred], what the top instantiates [Wc] at): the read
     leaves the BLOCK-OWED credential at the next boundary (index 3). *)
  Definition ush_mid_wc_read_t (γ : echo_gn) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T} (γp : gname) (I l : list (bv 8)) :
    wl_nl ∉ l ->
    ush_mid γ γp (I ++ l ++ [wl_nl]) -∗
    EchoLinksLine.ewc_lcred T γ (S gen_id) I 2%nat -∗
    ush_mid γ γp (I ++ l ++ [wl_nl])
    ∗ EchoLinksLine.ewc_lcred T γ (S gen_id) (I ++ l ++ [wl_nl]) 3%nat
    := fun Hnl => ush_mid_wc_read_t_at (echo_link_inst T γ) γ γp (S gen_id)
                    I l Hnl (ep_refl γ T).

  (* THE DISCIPLINE LEMMA AT THE PIECES (step 4; [UkSh.ush_wb_read]'s
     discharge).  A shell whose fd 2 is closed printed no prompt, so the
     era still owes the round's banner at the input [I]
     ([UInitBanner.kinit_ban], spelled out here); the pieces a whole
     line's read leaves at [I ++ l ++ "\n"] carry the reader's receipt of
     that line, whose writer-cursor bound is at least the stream through
     the block the line closed -- strictly more than a banner-owed cursor
     at [I] can be ([EchoLinks.wr_owed_read_refute]).  So the credential's
     untainted arm is refuted and what is left is the taint. *)
  Lemma ush_wb_read_holds_at (L : LinkRec Σ) (γ : echo_gn) (γp : gname)
      (k : nat) (I l : list (bv 8)) :
    wl_nl ∉ l ->
    (forall v : era_pins, ⊢ era_pin γ (S gen_id) v -∗ lk_epin L k v) ->
    ush_mid_at (lk_rres L) γ γp (I ++ l ++ [wl_nl]) -∗
    (∃ v : era_pins, lk_pin L k v ∗ lk_ban L k v I 0%nat) -∗
    ush_mid_at (lk_rres L) γ γp (I ++ l ++ [wl_nl]) ∗ lk_T L.
  Proof using .
    intros Hnl Hep. iIntros "(Hpos & Hpa & Hrd0 & Hcred) Hb".
    iDestruct "Hcred" as (v) "(#Hpin & Hdl & #HE & #Hres)".
    iDestruct "Hb" as (v') "[#Hpin' Hb]".
    iDestruct (Hep v with "Hpin") as "#Hep".
    iDestruct (lk_pin_epin L k v' with "Hpin'") as "#Hep'".
    iDestruct (lk_epin_agr L k v v' with "Hep Hep'") as %<-.
    iSplitR "Hb".
    { rewrite /ush_mid_at. iFrame "Hpos Hpa Hrd0". iExists v.
      iFrame "Hpin Hdl HE Hres". }
    iApply (lk_ban_read_taint L k v I l Hnl with "Hb Hres").
  Qed.

  Definition ush_wb_read_holds (γ : echo_gn) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T} (γp : gname) (I l : list (bv 8)) :
    wl_nl ∉ l ->
    ush_mid γ γp (I ++ l ++ [wl_nl]) -∗
    (∃ v : era_pins, era_pin γ (S gen_id) v ∗ EchoLinks.ewc_ban T v I 0%nat) -∗
    ush_mid γ γp (I ++ l ++ [wl_nl]) ∗ T
    := fun Hnl => ush_wb_read_holds_at (echo_link_inst T γ) γ γp (S gen_id)
                    I l Hnl (ep_refl γ T).

  (* =================================================================== *)
  (*  THE ENTRY LAW (lane IO-LEAF, step 3).  What /init lends its child   *)
  (*  is the RAW lease -- the position's program half and the lease at    *)
  (*  the READ family alone ([ush_rd_pin], the lend family) -- beside the *)
  (*  loop's credential slot at the lent count; the exit payload is at    *)
  (*  the EXIT family ([ush_rd_x]) and is assembled by sh where it leaves. *)
  (*  The lend's token arm pins the count against the program's half     *)
  (*  ([upos_agree]) and the pieces are [ush_mid]; its taint arm is the   *)
  (*  loop's taint arm, with the payload free at the exit family.  The    *)
  (*  boundary fact rides inside [ush_rd_pin], which is what makes it     *)
  (*  round-trip through /init's restart loop.                            *)
  (* =================================================================== *)
  Lemma ush_posb_of_lend (γ : echo_gn) (T : iProp Σ) `{!Persistent T}
      (N : uk_names Σ) (γp : gname)
      (Wc : list (bv 8) -> nat -> iProp Σ)
      (Wb : list (bv 8) -> iProp Σ) (l : list fdstate) (n : nat) :
    ukn_pay N = ucons_pay fsc_cons γp T (ush_rd_x γ Wb) ->
    ush_wc_inp γ T Wc ->
    ush_wb_inp γ T Wb ->
    ⊢ upos γp n -∗ ucons_pay fsc_cons γp T (ush_rd_pin γ) (-1) -∗
      (* the lent slot AT THE ERA'S INPUT OF THAT LENGTH, OR THE TAINT
         (lane EXEC-SEAM, (C)): /init's lend names the taint on its third
         arm, and a tainted turn is the cursor's own right arm *)
      ((∃ I : list (bv 8), ⌜length I = n⌝ ∗ UkSh.ush_wcp Wc Wb l I 0%nat)
       ∨ T) -∗
      UkSh.ush_posb N γp T Wc Wb (ush_mid γ γp) l 0%nat.
  Proof using .
    intros Hpay Hwci Hwbi. rewrite /ucons_pay.
    iAssert (□ (T -∗ upos γp n -∗
               UkSh.ush_posb N γp T Wc Wb (ush_mid γ γp) l 0%nat))%I
      as "#Htaint".
    { iModIntro. iIntros "#HT Hpos".
      iApply (UkSh.ush_posb_taint N γp T Wc Wb (ush_mid γ γp) l 0%nat
                with "HT [Hpos]").
      rewrite /UkSh.ush_pos /UkSh.ush_at. iExists n. iFrame "Hpos".
      rewrite Hpay. iApply (ucons_pay_taint with "HT"). }
    iIntros "Hpos Hl [Hwc | #HT]"; last first.
    { iApply ("Htaint" with "HT Hpos"). }
    iDestruct "Hl" as "[Hl | #HT]"; last first.
    { iApply ("Htaint" with "HT Hpos"). }
    iDestruct "Hwc" as (I) "[%Hlen Hwc]".
    iDestruct "Hl" as (n') "(Hrd0 & Hpa & Hcred)".
    iDestruct (upos_agree γp n n' with "Hpos Hpa") as %<-.
    iDestruct "Hcred" as (v I0) "([%Hlen0 %Hrest] & #Hpin & Hdl & #HE & #Hres)".
    (* THE TWO INPUTS ARE THE SAME (project echo-any-line): the lend's and
       the credential's are lower bounds of one era's echoed list and have
       the same length ([EchoOut.inp_lb_agree]).  Under the taint there is
       nothing to identify and nothing to identify it with. *)
    iAssert (UkSh.ush_wcp Wc Wb l I 0%nat
             ∗ ((∃ v' : era_pins, era_pin γ (S gen_id) v' ∗ inp_lb v' I) ∨ T))%I
      with "[Hwc]" as "[Hwc Hrd]".
    { iEval (rewrite /UkSh.ush_wcp) in "Hwc".
      iDestruct "Hwc" as "[[%Hrow Hc] | [%Hrow Hb]]".
      - iDestruct (Hwci I 0%nat with "Hc") as "[Hc Hr]".
        iSplitR "Hr"; [ | iExact "Hr" ].
        rewrite /UkSh.ush_wcp. iLeft. iSplitR; [ by iPureIntro | ].
        iExact "Hc".
      - iDestruct (Hwbi I with "Hb") as "[Hb Hr]".
        iSplitR "Hr".
        + rewrite /UkSh.ush_wcp. iRight. iSplitR; [ by iPureIntro | ].
          iExact "Hb".
        + iDestruct "Hr" as "[[Hrv _] | #HT]";
            [ iLeft; iExact "Hrv" | iRight; iExact "HT" ]. }
    iDestruct "Hrd" as "[Hrd | #HT]"; last first.
    { iApply ("Htaint" with "HT Hpos"). }
    iDestruct "Hrd" as (v') "[#Hpin' #HE']".
    iDestruct (era_pin_agree with "Hpin Hpin'") as %<-.
    iDestruct (inp_lb_agree v I0 I ltac:(lia) with "HE HE'") as %<-.
    iApply (UkSh.ush_posb_of_wc N γp T Wc Wb (ush_mid γ γp) l 0%nat I0 Hrest
              with "[Hpos Hpa Hrd0 Hdl] Hwc").
    rewrite /ush_mid /ush_mid_at Hlen0. iFrame "Hpos Hpa Hrd0".
    iExists v. iFrame "Hpin Hdl HE Hres".
  Qed.

  (* =================================================================== *)
  (*  THE FOUR LAWS ABOVE AT AN ABSTRACT RESIDUE (lane PIPE-CC).          *)
  (*                                                                     *)
  (*  [ush_mid_of_at], [ush_at_of_mid_taint], [ush_at_of_mid_wb] and      *)
  (*  [ush_posb_of_lend] are already generic in the credential families   *)
  (*  [Wc]/[Wb]; what they are NOT generic in is the reader's RESIDUE --  *)
  (*  they name [ush_mid]/[ush_rd_x]/[ush_rd_pin], which are the [_at]    *)
  (*  families at [rd_res], the ECHO era's.  A second era's round carries *)
  (*  [ush_mid_at (lk_rres L) γ γp] ([UShPipeRound]'s [Pm]), so it needs  *)
  (*  the same four one parameter up.  SAME PROOFS, character for         *)
  (*  character, with the residue threaded LINEARLY -- the landed ones    *)
  (*  intro it as persistent, which an abstract residue need not be.      *)
  (*                                                                     *)
  (*  The landed four do not move and are not re-proved through these:    *)
  (*  they are [Qed] and their callers ([UInitBoot.echo_cc_holds]) must   *)
  (*  not be disturbed.                                                   *)
  (*                                                                     *)
  (*  NAMES: [ush_lease_of_at] is [ush_mid_of_at]'s twin under a name     *)
  (*  that does not end in two [_at]s -- the landed one's [_at] is        *)
  (*  [UkSh.ush_at], the suffix here is the residue.                      *)
  (* =================================================================== *)
  Lemma ush_lease_of_at (Rres : era_pins -> list (bv 8) -> iProp Σ)
      (γ : echo_gn) (T : iProp Σ) `{!Persistent T}
      (Wb : list (bv 8) -> iProp Σ) (N : uk_names Σ) (γp : gname) (n : nat) :
    ukn_pay N = ucons_pay fsc_cons γp T (ush_rd_x_at Rres γ Wb) ->
    ⊢ UkSh.ush_at N γp n -∗
      ∃ I : list (bv 8), ⌜length I = n⌝
        ∗ UkSh.ush_lease N γp T (ush_mid_at Rres γ γp) I.
  Proof using .
    intro Hpay. rewrite /UkSh.ush_at /UkSh.ush_lease.
    iIntros "[Hpos Hlease]". iEval (rewrite Hpay /ucons_pay) in "Hlease".
    iDestruct "Hlease" as "[Hl | #HT]"; last first.
    { iExists (replicate n wl_nl).
      iSplitR; [ iPureIntro; apply length_replicate | ].
      iRight. iFrame "HT". rewrite /UkSh.ush_pos /UkSh.ush_at.
      iExists n. iFrame "Hpos". rewrite Hpay.
      iApply (ucons_pay_taint with "HT"). }
    iDestruct "Hl" as (n') "(Hrd0 & Hpa & Hcred)".
    iDestruct (upos_agree γp n n' with "Hpos Hpa") as %<-.
    rewrite /ush_rd_x_at /UkInit.init_rd /UkInit.init_rd_cred.
    iDestruct "Hcred" as "[Hcred _]".
    iDestruct "Hcred" as (v I) "([%Hlen %Hrest] & #Hpin & Hdl & #HE & Hres)".
    iExists I. iSplitR; [ by iPureIntro | ].
    iLeft. rewrite /ush_mid_at Hlen. iFrame "Hpos Hpa Hrd0".
    iExists v. iFrame "Hpin Hdl HE Hres".
  Qed.

  Lemma ush_at_of_mid_taint_at (Rres : era_pins -> list (bv 8) -> iProp Σ)
      (γ : echo_gn) (T : iProp Σ) `{!Persistent T}
      (Wb : list (bv 8) -> iProp Σ) (N : uk_names Σ) (γp : gname)
      (I : list (bv 8)) :
    ukn_pay N = ucons_pay fsc_cons γp T (ush_rd_x_at Rres γ Wb) ->
    ⊢ T -∗ ush_mid_at Rres γ γp I -∗ UkSh.ush_at N γp (length I).
  Proof using .
    intro Hpay. rewrite /ush_mid_at /UkSh.ush_at.
    iIntros "#HT (Hpos & _ & _ & _)". iFrame "Hpos". rewrite Hpay.
    iApply (ucons_pay_taint with "HT").
  Qed.

  Lemma ush_at_of_mid_wb_at (Rres : era_pins -> list (bv 8) -> iProp Σ)
      (γ : echo_gn) (T : iProp Σ) `{!Persistent T}
      (Wb : list (bv 8) -> iProp Σ) (N : uk_names Σ) (γp : gname)
      (I : list (bv 8)) :
    ukn_pay N = ucons_pay fsc_cons γp T (ush_rd_x_at Rres γ Wb) ->
    ush_wb_inp γ T Wb ->
    ⊢ ush_mid_at Rres γ γp I -∗ Wb I -∗ UkSh.ush_at N γp (length I).
  Proof using .
    intros Hpay Hwbi. iIntros "Hmid Hb".
    iDestruct (Hwbi I with "Hb") as "[Hb Hrd]".
    iDestruct "Hrd" as "[[_ %Hrest] | #HT]"; last first.
    { iApply (ush_at_of_mid_taint_at Rres γ T Wb N γp I Hpay with "HT Hmid"). }
    iEval (rewrite /ush_mid_at) in "Hmid".
    iDestruct "Hmid" as "(Hpos & Hpa & Hrd0 & Hcred)".
    rewrite /UkSh.ush_at. iFrame "Hpos". rewrite Hpay.
    iApply (ucons_pay_tok fsc_cons γp T (ush_rd_x_at Rres γ Wb)
              (length I) (-1) with "Hrd0 Hpa [Hcred Hb]").
    rewrite /ush_rd_x_at /UkInit.init_rd /UkInit.init_rd_cred /ush_rd_pin_at.
    iSplitR "Hb"; last first.
    { iExists I. iSplitR; [ by iPureIntro | ]. iExact "Hb". }
    iDestruct "Hcred" as (v) "(#Hpin & Hdl & #HE & Hres)".
    iExists v, I. iSplitR; [ by iPureIntro | ]. iFrame "Hpin Hdl HE Hres".
  Qed.

  Lemma ush_posb_of_lend_at (Rres : era_pins -> list (bv 8) -> iProp Σ)
      (γ : echo_gn) (T : iProp Σ) `{!Persistent T}
      (N : uk_names Σ) (γp : gname)
      (Wc : list (bv 8) -> nat -> iProp Σ)
      (Wb : list (bv 8) -> iProp Σ) (l : list fdstate) (n : nat) :
    ukn_pay N = ucons_pay fsc_cons γp T (ush_rd_x_at Rres γ Wb) ->
    ush_wc_inp γ T Wc ->
    ush_wb_inp γ T Wb ->
    ⊢ upos γp n -∗ ucons_pay fsc_cons γp T (ush_rd_pin_at Rres γ) (-1) -∗
      ((∃ I : list (bv 8), ⌜length I = n⌝ ∗ UkSh.ush_wcp Wc Wb l I 0%nat)
       ∨ T) -∗
      UkSh.ush_posb N γp T Wc Wb (ush_mid_at Rres γ γp) l 0%nat.
  Proof using .
    intros Hpay Hwci Hwbi. rewrite /ucons_pay.
    iAssert (□ (T -∗ upos γp n -∗
               UkSh.ush_posb N γp T Wc Wb (ush_mid_at Rres γ γp) l 0%nat))%I
      as "#Htaint".
    { iModIntro. iIntros "#HT Hpos".
      iApply (UkSh.ush_posb_taint N γp T Wc Wb (ush_mid_at Rres γ γp) l 0%nat
                with "HT [Hpos]").
      rewrite /UkSh.ush_pos /UkSh.ush_at. iExists n. iFrame "Hpos".
      rewrite Hpay. iApply (ucons_pay_taint with "HT"). }
    iIntros "Hpos Hl [Hwc | #HT]"; last first.
    { iApply ("Htaint" with "HT Hpos"). }
    iDestruct "Hl" as "[Hl | #HT]"; last first.
    { iApply ("Htaint" with "HT Hpos"). }
    iDestruct "Hwc" as (I) "[%Hlen Hwc]".
    iDestruct "Hl" as (n') "(Hrd0 & Hpa & Hcred)".
    iDestruct (upos_agree γp n n' with "Hpos Hpa") as %<-.
    iDestruct "Hcred" as (v I0) "([%Hlen0 %Hrest] & #Hpin & Hdl & #HE & Hres)".
    iAssert (UkSh.ush_wcp Wc Wb l I 0%nat
             ∗ ((∃ v' : era_pins, era_pin γ (S gen_id) v' ∗ inp_lb v' I) ∨ T))%I
      with "[Hwc]" as "[Hwc Hrd]".
    { iEval (rewrite /UkSh.ush_wcp) in "Hwc".
      iDestruct "Hwc" as "[[%Hrow Hc] | [%Hrow Hb]]".
      - iDestruct (Hwci I 0%nat with "Hc") as "[Hc Hr]".
        iSplitR "Hr"; [ | iExact "Hr" ].
        rewrite /UkSh.ush_wcp. iLeft. iSplitR; [ by iPureIntro | ].
        iExact "Hc".
      - iDestruct (Hwbi I with "Hb") as "[Hb Hr]".
        iSplitR "Hr".
        + rewrite /UkSh.ush_wcp. iRight. iSplitR; [ by iPureIntro | ].
          iExact "Hb".
        + iDestruct "Hr" as "[[Hrv _] | #HT]";
            [ iLeft; iExact "Hrv" | iRight; iExact "HT" ]. }
    iDestruct "Hrd" as "[Hrd | #HT]"; last first.
    { iApply ("Htaint" with "HT Hpos"). }
    iDestruct "Hrd" as (v') "[#Hpin' #HE']".
    iDestruct (era_pin_agree with "Hpin Hpin'") as %<-.
    iDestruct (inp_lb_agree v I0 I ltac:(lia) with "HE HE'") as %<-.
    iApply (UkSh.ush_posb_of_wc N γp T Wc Wb (ush_mid_at Rres γ γp) l 0%nat
              I0 Hrest with "[Hpos Hpa Hrd0 Hdl Hres] Hwc").
    rewrite /ush_mid_at Hlen0. iFrame "Hpos Hpa Hrd0".
    iExists v. iFrame "Hpin Hdl HE Hres".
  Qed.

  (* WHAT SH ASKS TO BE TOLD ABOUT THE WINDOW IT CONSUMED.  [EchoOut.
     read_ret] is the era's own answer: the delivered count moved to the
     window's far end, the prefix fact, and the two index laws SH-LINE
     turns into the line.  The RIGHT disjunct is the arm an already
     TAINTED era answers on -- there the reader holds no half of the count
     and the link is free ([EchoLinks.echo_link_rd_taint]), so the answer
     can only be the taint itself.
     ONE definition and not two, because [WpUart.cons_read_pay] quantifies
     the window INSIDE: the program deposits ONE link and is told which
     window it got in the receipt. *)
  (* AT THE RECORD (lane LINK-GEN-4): the era's pin, the input at the
     window's near end, the reader's residue there, and the read's own
     RETURN -- or the taint.  [ush_rd_in] is this at the echo instance. *)
  Definition ush_rd_in_at {L : LinkRec Σ} (R : ReadRec L) (γ : echo_gn)
      (I : list (bv 8)) (ws : list (list mobs * bv 8)) : iProp Σ :=
    ((∃ v : era_pins, era_pin γ (S gen_id) v ∗ inp_lb v I ∗ lk_rres L v I
        ∗ lk_rr L (S gen_id) v (length I) ws)
     ∨ lk_T L)%I.

  Definition ush_rd_in (T : iProp Σ) (γ : echo_gn) (I : list (bv 8))
      (ws : list (list mobs * bv 8)) : iProp Σ :=
    ((∃ v : era_pins, era_pin γ (S gen_id) v ∗ inp_lb v I ∗ rd_res v I
        ∗ read_ret T (S gen_id) v (length I) ws)
     ∨ T)%I.

  Definition ush_read_fam_era_at {L : LinkRec Σ} (R : ReadRec L)
      (γ : echo_gn) (γp : gname)
      (I : list (bv 8)) (Q : Z -> iProp Σ) : sfam :=
    ush_read_fam_at γp (lk_T L) (length I) (ush_rd_in_at R γ I) Q.

  Definition ush_read_fam_era (T : iProp Σ) (γ : echo_gn) (γp : gname)
      (I : list (bv 8)) (Q : Z -> iProp Σ) : sfam :=
    ush_read_fam_at γp T (length I) (ush_rd_in T γ I) Q.

  (* =================================================================== *)
  (*  THE ACCESS LEMMA, REBUILT ON THE ERA'S LINK.                        *)
  (*                                                                     *)
  (*  Two payments, side by side, exactly as [SpecFileread.fileread_in]'s *)
  (*  console arm asks for them: the RING's ([ConsoleInv.cons_acc]), paid *)
  (*  by the reader lease sh carries, and the BOUNDARY's                  *)
  (*  ([WpUart.cons_read_pay]), which used to be bought outright from     *)
  (*  [WpUart.cons_licence] and is now the era's read link at sh's own      *)
  (*  delivered count -- READ OFF THE SAME LEASE.  Both arms of the lease *)
  (*  answer both payments: the token arm pays the ring with the token    *)
  (*  and the boundary with the half beside it, and the taint arm pays    *)
  (*  the ring with [ConsoleInv.cons_dirty_cred] and the boundary with    *)
  (*  [EchoLinks.echo_link_rd_taint].                                     *)
  (* =================================================================== *)
  (* THE PAYMENT ITSELF, WITHOUT THE DEPOSIT AROUND IT (lane RD-4).  The
     neutral console member ([UkReadCons.wp_uk_ecall_read_cons]) takes the
     two payments as they stand, so what this file owes is only the era's
     answer to them; the deposit's wrapping is the member's.  BOTH ARMS OF
     THE LEASE ANSWER BOTH PAYMENTS, and they must be split ONCE: the token
     arm pays the ring with the token and the console history with the half
     beside it, the taint arm pays the ring with
     [ConsoleInv.cons_dirty_cred] and the history with
     [EchoLinks.echo_link_rd_taint]. *)
  (* the echo instances' reading of the supply, at the dirty credential *)
  Lemma ush_rdcred_w (T : iProp Σ) : (⊢ T -∗ app_sup) -> ⊢ T -∗ app_rdcred.
  Proof using . intros H. iIntros "HT". iApply app_rdcred_of_sup. by iApply H. Qed.

  Lemma ush_read_pay_era_at {L : LinkRec Σ} (R : ReadRec L) (γ : echo_gn)
      (N : uk_names Σ) (γp : gname) (I : list (bv 8)) :
    (* E2's two readings of the supply *)
    (⊢ app_sup -∗ lk_T L) ->
    (⊢ lk_T L -∗ app_rdcred) ->
    (* ...and the era's WILD credential's (lane S0) *)
    (⊢ riscv_rdwild (S gen_id) -∗ lk_T L) ->
    (* the pieces' own pin IS the record's ([lk_pin file_link_inst :=
       era_pin (fgn_echo g)]; at echo it is the identity) *)
    (forall v : era_pins, ⊢ era_pin γ (S gen_id) v -∗ lk_pin L (S gen_id) v) ->
    lk_links L -∗
    (* THE LEASE, IN THE PIECES A LINE'S MIDDLE LEAVES IT IN (lane
       IO-LEAF, M5(3)): the payload's own form asserts a LINE BOUNDARY,
       which is false between a line's first byte and its '\n'. *)
    UkSh.ush_lease N γp (lk_T L) (ush_mid_at (lk_rres L) γ γp) I -∗
    cons_acc fsc_cons app_rdcred (ush_rd_ret γp (lk_T L) (length I))
    ∗ cons_read_pay (S gen_id) (ush_rd_in_at R γ I).
  Proof using .
    intros Hst Hts Hwd Hep.
    iIntros "#Hlk HP". set (n := length I).
    iEval (rewrite /UkSh.ush_lease /ush_mid_at) in "HP".
    iDestruct "HP" as "[Hl | [#HT Hp]]".
    - (* THE LEASE HOLDER'S ARM: the token, both halves of the position
         pair, and the era's credential beside them, all at ONE number. *)
      iDestruct "Hl" as "(Hpos & Hpa & Hrd0 & Hcred)".
      iDestruct "Hcred" as (v) "(#Hpin & Hdl & #HE & #Hres)".
      iSplitR "Hdl"; last first.
      { (* THE CONSOLE HISTORY'S HALF: the era's read link at sh's own
           count, which is ONE answer to [WpUart.cons_link]'s atomic
           update -- ConsLog's [EvRead] event. *)
        iIntros (ws).
        iDestruct (Hep v with "Hpin") as "#Hpl".
        iApply (rk_rd L R (S gen_id) n v ws _ with "Hlk Hpl Hdl").
        iIntros "Hret". rewrite /ush_rd_in_at. iLeft. iExists v.
        iFrame "Hpin HE Hres Hret". }
      iEval (rewrite ucons_reader_eq) in "Hrd0".
      iApply (cons_acc_reader fsc_cons app_rdcred n with "Hrd0 [Hpos Hpa]").
      iIntros (cur dc) "Hout". rewrite /cons_out.
      iDestruct "Hout" as "[Hrd' [%Hcur | #Hdirty]]".
      + (* nobody read behind its back: the window is at its own position,
           and BOTH halves move ([upos_update]) *)
        subst cur.
        iMod (upos_update γp n (n + dc)%nat with "Hpos Hpa") as "[Hpos Hpa]".
        iModIntro. rewrite /ush_rd_ret. iLeft.
        iSplitR; [ done | ]. iFrame "Hpos Hpa".
        rewrite ucons_reader_eq. iExact "Hrd'".
      + (* a tokenless reader popped while the call slept *)
        iAssert (lk_T L) as "#HT";
          [ iApply (app_rdcred_elim _ Hst Hwd); iExact "Hdirty" | ].
        iModIntro. iClear "Hrd'".
        rewrite /ush_rd_ret. iRight. iFrame "HT".
        iExists n. iExact "Hpos".
    - (* THE TAINTED ARM: the lease holds no token and no credential;
         both payments are free ([AppEcho.echo_sup_of_taint] read
         forwards, and [EchoLinks.echo_link_rd_taint]). *)
      iEval (rewrite /UkSh.ush_pos /UkSh.ush_at) in "Hp".
      iDestruct "Hp" as (n') "[Hpos _]".
      iSplitL "Hpos".
      + iApply (cons_acc_cred fsc_cons app_rdcred with "[] [Hpos]").
        * rewrite /cons_dirty_cred. iModIntro. iApply Hts. iExact "HT".
        * iIntros (cur dc). iModIntro.
          rewrite /ush_rd_ret. iRight. iFrame "HT". iExists n'.
          iExact "Hpos".
      + iIntros (ws).
        iApply (rk_rd_taint L R ws _ with "Hlk HT").
        iIntros "#HT'". rewrite /ush_rd_in_at. iRight. iExact "HT'".
  Qed.

  (* ...and the ECHO instance, at [ReadRec]'s own ([lk_pin] is [era_pin γ],
     so the bridge is the identity wand) *)
  Lemma rr_ep_refl (γ : echo_gn) (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (v : era_pins) :
    ⊢ era_pin γ (S gen_id) v -∗ lk_pin (echo_link_inst T γ) (S gen_id) v.
  Proof using . by iIntros "$". Qed.

  Definition ush_read_pay_era (γ : echo_gn) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T}
      (N : uk_names Σ) (γp : gname) (I : list (bv 8)) :
    (⊢ app_sup -∗ T) ->
    (⊢ T -∗ app_sup) ->
    (⊢ riscv_rdwild (S gen_id) -∗ T) ->
    echo_links T γ -∗
    UkSh.ush_lease N γp T (ush_mid γ γp) I -∗
    cons_acc fsc_cons app_rdcred (ush_rd_ret γp T (length I))
    ∗ cons_read_pay (S gen_id) (ush_rd_in T γ I)
    := fun Hst Hts Hwd =>
         ush_read_pay_era_at (echo_read_inst T γ) γ N γp I Hst (ush_rdcred_w _ Hts) Hwd
           (rr_ep_refl γ T).

  (* ...AND THE DEPOSIT, at its exact former statement: the neutral
     supplier at the era's own [Rd] and [Rin].  [UkReadCons.read_cons_fam]
     and [ush_read_fam_era] are the same record ([UkReadRows.xfam_rd] at
     those two), which is the whole content of "sh's read is an INSTANCE of
     the console member". *)
  Lemma ush_read_sup_era_at {L : LinkRec Σ} (R : ReadRec L) (γ : echo_gn)
      (N : uk_names Σ) (γp : gname)
      (m : regfile) (pc : mword 64) (l : list fdstate) (I : list (bv 8))
      (wr : bool) :
    (* the descriptor is fd 0, and fd 0 is the console *)
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = 0 ->
    l !! 0%nat = Some (FdOpen true wr (FdDevice CONSOLE)) ->
    (* E2's two readings of the supply *)
    (⊢ app_sup -∗ lk_T L) ->
    (⊢ lk_T L -∗ app_rdcred) ->
    (* ...and the era's WILD credential's (lane S0) *)
    (⊢ riscv_rdwild (S gen_id) -∗ lk_T L) ->
    (forall v : era_pins, ⊢ era_pin γ (S gen_id) v -∗ lk_pin L (S gen_id) v) ->
    lk_links L -∗
    UkSh.ush_lease N γp (lk_T L) (ush_mid_at (lk_rres L) γ γp) I -∗
    udepwf_std N m pc USYS_read (ush_read_fam_era_at R γ γp I (ukn_pay N)) l.
  Proof using .
    intros Ha0 Hl0 Hst Hts Hwd Hep.
    iIntros "#Hlk HP".
    iDestruct (ush_read_pay_era_at R γ N γp I Hst Hts Hwd Hep with "Hlk HP")
      as "[Hacc Hlink]".
    iApply (udepwf_std_read_cons N m pc l 0%nat wr
              (ush_rd_ret γp (lk_T L) (length I)) (ush_rd_in_at R γ I)
              Ha0 ltac:(unfold NSTD; lia) Hl0 with "Hacc Hlink").
  Qed.

  Definition ush_read_sup_era (γ : echo_gn) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T}
      (N : uk_names Σ) (γp : gname)
      (m : regfile) (pc : mword 64) (l : list fdstate) (I : list (bv 8))
      (wr : bool) :
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = 0 ->
    l !! 0%nat = Some (FdOpen true wr (FdDevice CONSOLE)) ->
    (⊢ app_sup -∗ T) ->
    (⊢ T -∗ app_sup) ->
    (⊢ riscv_rdwild (S gen_id) -∗ T) ->
    echo_links T γ -∗
    UkSh.ush_lease N γp T (ush_mid γ γp) I -∗
    udepwf_std N m pc USYS_read (ush_read_fam_era T γ γp I (ukn_pay N)) l
    := fun Ha0 Hl0 Hst Hts Hwd =>
         ush_read_sup_era_at (echo_read_inst T γ) γ N γp m pc l I wr
           Ha0 Hl0 Hst (ush_rdcred_w _ Hts) Hwd (rr_ep_refl γ T).

  (* =================================================================== *)
  (*  THE BYTE THE READ DELIVERED IS THE INPUT'S, AT SH'S OWN COUNT       *)
  (*  (the survey's S4(a)/(b), as a lemma).                               *)
  (*                                                                     *)
  (*  Three rows of one receipt meet here.  The WINDOW row                *)
  (*  ([ConsoleInv.cons_window]) says the [j]th byte the call DELIVERED   *)
  (*  is the ring's stored entry at [cur + j] and the caller's buffer     *)
  (*  byte is its translation.  The BOUNDARY row says the window the call *)
  (*  CONSUMED is that same stored run read at the bound                  *)
  (*  [ConsoleInv.cons_swallow] extends to, so the two agree wherever a   *)
  (*  byte was delivered.  And [EchoOut.ein_read_byte] places that byte   *)
  (*  in the ERA'S INPUT at the reader's own delivered count, which       *)
  (*  [EchoOut.read_ret] pins to [length I] -- so it is the FIRST of the  *)
  (*  bytes [J] the call added.                                           *)
  (*                                                                     *)
  (*  STATED AT INDEX 0 AND NOT AT EVERY [j], because that is the only    *)
  (*  index the era's law reaches: [ein_read_byte] is at the count the    *)
  (*  window STARTS at, and sh's [gets] reads at [cap = 1] precisely so   *)
  (*  that the byte it copies is that one ([UkSh.v]'s S3).                *)
  (* =================================================================== *)
  (* =================================================================== *)
  (*  S6  THE LEAF (lane IO-LEAF, M5)                                     *)
  (*                                                                     *)
  (*  [UkSh.ush_read_recv_leaf] itself, at ITS OWN answer: since the      *)
  (*  boundary became the era's INPUT (project echo-any-line) the two     *)
  (*  answers coincide -- what the shell is told is the bytes the call    *)
  (*  added to the input, their parse, and the first of them, which is    *)
  (*  exactly what [UkSh.ush_read_ans] asks for at [Pm := ush_mid].  The  *)
  (*  era's own facts (the delivered-count half, the cursor bounds) go    *)
  (*  back into the PIECES, which is where the next read looks for them.  *)
  (*                                                                     *)
  (*  THE [-1] ARM IS REFUTED at an open readable console descriptor by   *)
  (*  TRAP-ROWS T2 ([UexecRet.uexec_live_ok]'s read clause), and that is  *)
  (*  what makes the credential's round trip possible at all: the         *)
  (*  receipt's [-1] arm hands back no window, and the boundary link the  *)
  (*  deposit carried goes with it.  At a SHUT fd 0 the deposit carries   *)
  (*  no link ([SpecFileread.fileread_in]'s [FdClosed] arm is [P -* P]),  *)
  (*  so the lease comes straight back and the [-1] arm is the answer.    *)
  (* =================================================================== *)

  Lemma ush_read_recv_era_at {L : LinkRec Σ} (R : ReadRec L) (γ : echo_gn)
      (Wb : list (bv 8) -> iProp Σ)
      (N : uk_names Σ) (γp : gname) (l : list fdstate)
      (h : CpuId) (m : regfile) (pc : mword 64) (a : Z) (k cap : nat)
      (I : list (bv 8)) (f : nat -> bv 8) (avail : nat) :
    ukn_pay N
      = ucons_pay fsc_cons γp (lk_T L) (ush_rd_x_at (lk_rres L) γ Wb) ->
    (⊢ app_sup -∗ lk_T L) ->
    (⊢ lk_T L -∗ app_rdcred) ->
    (* ...and the era's WILD credential's (lane S0) *)
    (⊢ riscv_rdwild (S gen_id) -∗ lk_T L) ->
    (forall v : era_pins, ⊢ era_pin γ (S gen_id) v -∗ lk_pin L (S gen_id) v) ->
    usysno m = USYS_read ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = 0 ->
    uint (m !!! Regidx a1_idx) = a ->
    uint (m !!! Regidx a2_idx) = Z.of_nat cap ->
    (cap <= k)%nat ->
    (Z.of_nat cap < 2 ^ 31)%Z ->
    UkSh.ush_fd0p l ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    lk_links L -∗
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    ubytes (ukn_d N) a k f -∗
    ustd (ukn_fd N) l -∗
    UkSh.ush_lease N γp (lk_T L) (ush_mid_at (lk_rres L) γ γp) I -∗
    urun (PS := uprogSG_free) N h m pc avail -∗
    (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8),
       ⌜ (d <= cap)%nat ⌝ -∗
       ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
       ustd (ukn_fd N) l -∗
       UkSh.ush_read_ans_at N γp (lk_T L) (ush_mid_at (lk_rres L) γ γp)
         (rk_disc L R) fsc_cons l r cap I g -∗
       ubytes (ukn_d N) a k g -∗
       urun (PS := uprogSG_free) N h'
         (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hpay Hst Hts Hwd Hep Hn Ha0 Ha1 Ha2 Hcapk Hcap31 Hfd0 Hal.
    iIntros "#Hlk #Hi Hbuf Hstd Hpos Hrun Hcont".
    subst a. set (n := length I).
    pose proof (UkSh.ush_narrow_count_le (m !!! Regidx a2_idx) cap Ha2) as Hbnd.
    assert (Hcnt : sys_rw_count (m !!! Regidx a2_idx) = Z.of_nat cap)
      by exact (ush_count_is_cap (m !!! Regidx a2_idx) cap Ha2 Hcap31).
    change (2 ^ 31)%Z with 2147483648%Z in Hcap31.
    (* THE LEASE, OUT OF THE PROGRAM'S OWN HAND, IN PIECES (lane IO-LEAF,
       M5(3)): mid-line the era's credential is at no boundary, so what
       the walk carries is [UkSh.ush_lease] and not the payload. *)
    destruct Hfd0 as [[wr Hl0] | Hcl].
    - (* ================= fd 0 IS THE CONSOLE ================= *)
      (* THE ECHO TAILORING IS A WRAPPER NOW (lane RD-4).  The walk, the
         refutation of the [-1] arm at an open readable console descriptor,
         the receipt's two GUARDED rows (the per-byte ledger's linearity
         and [ConsoleInv.cons_swallow]'s copy-out fault) and the window's
         assembly are all the NEUTRAL console member's
         ([UkReadCons.wp_uk_ecall_read_cons]) -- none of them was ever
         about an application.  What is left here is the era's own reading
         of the input segment the call consumed, which is what [Rin] is
         for. *)
      assert (Hfdc : UkSh.ush_fd0c l) by (exists wr; exact Hl0).
      iDestruct (ush_read_pay_era_at R γ N γp I Hst Hts Hwd Hep with "Hlk Hpos")
        as "[Hacc Hlink]".
      iApply (wp_uk_ecall_read_cons (PS := uprogSG_free) N h m pc
                (uint (m !!! Regidx a1_idx)) k cap f avail l 0%nat wr
                (ush_rd_ret γp (lk_T L) n) (ush_rd_in_at R γ I)
                Hn Ha0 ltac:(unfold NSTD; lia) Hl0 eq_refl Ha2 Hcapk Hcap31
                Hal with "Hi Hrun Hstd Hbuf Hacc Hlink").
      iIntros (h' r d g) "%Hd %Hgf Hstd Hans Hbuf Hrun".
      iDestruct "Hans" as (dd dc cur hs)
        "(%Hdr & %Hddcap & %Hb1 & %Hb4 & #Htags & Hrd & Hwin)".
      rewrite /ush_rd_ret.
      iDestruct "Hrd" as "[(%Hcur & Hp & Hrdt & Hpa) | [#HT Hp]]"; last first.
      { (* the caller's own [Rd] came back tainted *)
        iApply ("Hcont" $! h' r d g with "[%] [%] Hstd [Hp] Hbuf Hrun");
          [ exact Hd | exact Hgf | ].
        rewrite /UkSh.ush_read_ans /UkSh.ush_pos /UkSh.ush_at.
        iRight. iRight. iFrame "HT".
        iDestruct "Hp" as (n') "Hp". iExists n'. iFrame "Hp".
        rewrite Hpay. iApply (ucons_pay_taint with "HT"). }
      subst cur.
      iDestruct "Hwin" as "[Hw | #Hdirty]"; last first.
      { (* a tokenless reader popped while the call slept *)
        iAssert (lk_T L) as "#HT";
          [ iApply (app_rdcred_elim _ Hst Hwd); iExact "Hdirty" | ].
        iApply ("Hcont" $! h' r d g with "[%] [%] Hstd [Hp] Hbuf Hrun");
          [ exact Hd | exact Hgf | ].
        rewrite /UkSh.ush_read_ans /UkSh.ush_pos /UkSh.ush_at.
        iRight. iRight. iFrame "HT". iExists (n + dc)%nat. iFrame "Hp".
        rewrite Hpay. iApply (ucons_pay_taint with "HT"). }
      rewrite /uread_cons_win.
      iDestruct "Hw" as (sl) "(%Hch & #Hlb & %Hwinf & #Hsw & %Hddc & Hbnd)".
      iDestruct "Hbnd" as (sl2 ws)
        "(#Hlb2 & %Hpre2 & %Hlen2 & %Hlws & %Hwsj & Hrin)".
      (* THE BOUNDARY'S ANSWER, and THE PIECES KEPT TOGETHER (lane
         IO-LEAF, M5(3)): the era's credential at the window's far end
         goes back beside the token and both halves of the position pair,
         but NOT into the payload -- the far end is in the middle of a
         line, where the payload's own boundary row is false.
         WHAT THE CALL ADDED IS A LIST, NOT A COUNT (project
         echo-any-line): the era's input at the far end is the lease's own
         input extended by [J], because both are lower bounds of one
         echoed list ([EchoOut.inp_lb_cmp]) and the lease's is the
         shorter. *)
      iAssert ((∃ J : list (bv 8),
                  ⌜length J = dc⌝ ∗ ⌜rk_disc L R (I ++ J)⌝
                  ∗ ⌜(0 < dd)%nat -> g 0%nat = J !!! 0%nat⌝
                  ∗ ush_mid_at (lk_rres L) γ γp (I ++ J))
               ∨ (lk_T L ∗ UkSh.ush_pos N γp))%I
        with "[Hrin Hrdt Hpa Hp]" as "Hera".
      { rewrite /ush_rd_in_at.
        iDestruct "Hrin" as "[Hret | #HT]"; last first.
        { iRight. iFrame "HT". rewrite /UkSh.ush_pos /UkSh.ush_at.
          iExists (n + dc)%nat. iFrame "Hp". rewrite Hpay.
          iApply (ucons_pay_taint with "HT"). }
        iDestruct "Hret" as (v) "(#Hpin & #HE0 & #Hres0 & Hret)".
        (* THE WINDOW ARM, AS ONE LAW (lane LINK-GEN-4): everything this
           block used to open [EchoOut.read_ret] by hand for is
           [ReadRec.rk_arms], at the rows the console member just handed
           over. *)
        iDestruct (Hep v with "Hpin") as "#Hpl".
        iDestruct (lk_pin_epin L (S gen_id) v with "Hpl") as "#Hepl".
        iDestruct (rk_arms L R fsc_cons v I ws sl sl2 hs dd dc g
                     Hddc Hlws Hwinf Hpre2 Hwsj
                     with "Hepl HE0 Hres0 Hret Htags Hsw Hlb2")
          as "[Hwin | #HT]"; last first.
        { iRight. iFrame "HT". rewrite /UkSh.ush_pos /UkSh.ush_at.
          iExists (n + dc)%nat. iFrame "Hp". rewrite Hpay.
          iApply (ucons_pay_taint with "HT"). }
        iDestruct "Hwin" as "[Hdlr Hj]".
        iDestruct "Hj" as (J) "(%HJlen & %HJdisc & %HJbyte & #HEn & #Hresn)".
        iLeft. iExists J.
        iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
        iSplitR; [ by iPureIntro | ].
        assert (Hcl : length (I ++ J) = (n + dc)%nat)
          by (rewrite length_app HJlen; reflexivity).
        rewrite /ush_mid_at Hcl.
        iFrame "Hp Hpa Hrdt". iExists v. iFrame "Hpin Hdlr HEn Hresn". }
      iDestruct "Hera" as "[Hera | [#HT Hp']]"; last first.
      { iApply ("Hcont" $! h' r d g with "[%] [%] Hstd [Hp'] Hbuf Hrun");
          [ exact Hd | exact Hgf | ].
        rewrite /UkSh.ush_read_ans_at. iRight. iRight. iFrame "HT Hp'". }
      iDestruct "Hera" as (J) "(%HJlen & %HJdisc & %HJbyte & Hmid)".
      iApply ("Hcont" $! h' r d g
                with "[%] [%] Hstd [Hmid] Hbuf Hrun");
        [ exact Hd | exact Hgf | ].
      rewrite /UkSh.ush_read_ans_at. iLeft.
      iExists dd, dc, hs, sl, J.
      iSplitR; [ by iPureIntro | ].
      iSplitR; [ iPureIntro; exact Hddcap | ].
      iSplitR; [ iPureIntro; exact Hb1 | ].
      iSplitR; [ iPureIntro; exact Hb4 | ].
      iSplitR; [ by iPureIntro | ].
      iSplitR; [ iExact "Hlb" | ].
      iSplitR; [ iExact "Htags" | ].
      iSplitR; [ iPureIntro; exact Hwinf | ].
      iSplitR; [ iExact "Hsw" | ].
      iSplitR; [ by iPureIntro | ].
      iSplitR; [ by iPureIntro | ].
      iSplitR; [ by iPureIntro | ].
      iSplitR; [ by iPureIntro | ]. iExact "Hmid".
    - (* ================= fd 0 IS SHUT ================= *)
      iDestruct (ush_read_sup_closed N γp (lk_T L) (ush_rd_in_at R γ I) m pc l n
                   Ha0 Hcl) as "Hsb".
      iApply (wp_uk_ecall_read_recv (PS := uprogSG_free) N h m pc
                (bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0
                            : mword 32))
                k f avail (ush_read_fam_era_at R γ γp I (ukn_pay N)) l
                Hn eq_refl ltac:(lia) Hal
                with "Hi Hrun Hsb Hstd Hbuf").
      iIntros (h' r d g W M' fdv' cw' cs')
        "%Hd %Hgf %Hlin %HM %Hnf %Harg0 %Harg1 %Harg2 %Htake %Hlz %Hlive
         Hstd Hpost Hrun Hbuf".
      iDestruct (spost_at_read_elim uslot
                   (ush_read_fam_era_at R γ γp I (ukn_pay N)) W
                   (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                   (m !!! Regidx a2_idx) (uvis_fd W) r M' fdv' cw' cs'
                   Harg0 Harg1 Harg2 eq_refl with "Hpost")
        as "[%Hfrret Hpost']".
      iDestruct "Hpost'" as (P) "(%Hperm & %Hwf & %Hlazy & Hrec)".
      iEval (rewrite (ush_fd_st_closed (m !!! Regidx a0_idx) (uvis_fd W) l
                        Ha0 Htake Hcl) /fileread_extra_core) in "Hrec".
      iDestruct "Hrec" as "%Hm1".
      iApply ("Hcont" $! h' r d g
                with "[%] [%] Hstd [Hpos] Hbuf Hrun");
        [ lia | exact Hgf | ].
      rewrite /UkSh.ush_read_ans /UkSh.ush_lease.
      iDestruct "Hpos" as "[Hmid | [#HT Hp]]";
        [ | iRight; iRight; iFrame "HT Hp" ].
      iRight. iLeft.
      iSplitR; [ by iPureIntro | ].
      iSplitR; [ by iPureIntro | ]. iExact "Hmid".
  Qed.

  (* ...AT A NAMED TABLE VIEW (seccomp S4): the read keeps the view *)
  Lemma ush_read_recv_era_at_vw {L : LinkRec Σ} (R : ReadRec L) (γ : echo_gn)
      (Wb : list (bv 8) -> iProp Σ)
      (N : uk_names Σ) (γp : gname) (l vw : list fdstate)
      (h : CpuId) (m : regfile) (pc : mword 64) (a : Z) (k cap : nat)
      (I : list (bv 8)) (f : nat -> bv 8) (avail : nat) :
    ukn_pay N
      = ucons_pay fsc_cons γp (lk_T L) (ush_rd_x_at (lk_rres L) γ Wb) ->
    (⊢ app_sup -∗ lk_T L) ->
    (⊢ lk_T L -∗ app_rdcred) ->
    (* ...and the era's WILD credential's (lane S0) *)
    (⊢ riscv_rdwild (S gen_id) -∗ lk_T L) ->
    (forall v : era_pins, ⊢ era_pin γ (S gen_id) v -∗ lk_pin L (S gen_id) v) ->
    usysno m = USYS_read ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = 0 ->
    uint (m !!! Regidx a1_idx) = a ->
    uint (m !!! Regidx a2_idx) = Z.of_nat cap ->
    (cap <= k)%nat ->
    (Z.of_nat cap < 2 ^ 31)%Z ->
    UkSh.ush_fd0p l ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    lk_links L -∗
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    ubytes (ukn_d N) a k f -∗
    ustd_at (ukn_fd N) l vw -∗
    UkSh.ush_lease N γp (lk_T L) (ush_mid_at (lk_rres L) γ γp) I -∗
    urun (PS := uprogSG_free) N h m pc avail -∗
    (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8),
       ⌜ (d <= cap)%nat ⌝ -∗
       ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
       ustd_at (ukn_fd N) l vw -∗
       UkSh.ush_read_ans_at N γp (lk_T L) (ush_mid_at (lk_rres L) γ γp)
         (rk_disc L R) fsc_cons l r cap I g -∗
       ubytes (ukn_d N) a k g -∗
       urun (PS := uprogSG_free) N h'
         (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hpay Hst Hts Hwd Hep Hn Ha0 Ha1 Ha2 Hcapk Hcap31 Hfd0 Hal.
    iIntros "#Hlk #Hi Hbuf Hstd Hpos Hrun Hcont".
    subst a. set (n := length I).
    pose proof (UkSh.ush_narrow_count_le (m !!! Regidx a2_idx) cap Ha2) as Hbnd.
    assert (Hcnt : sys_rw_count (m !!! Regidx a2_idx) = Z.of_nat cap)
      by exact (ush_count_is_cap (m !!! Regidx a2_idx) cap Ha2 Hcap31).
    change (2 ^ 31)%Z with 2147483648%Z in Hcap31.
    (* THE LEASE, OUT OF THE PROGRAM'S OWN HAND, IN PIECES (lane IO-LEAF,
       M5(3)): mid-line the era's credential is at no boundary, so what
       the walk carries is [UkSh.ush_lease] and not the payload. *)
    destruct Hfd0 as [[wr Hl0] | Hcl].
    - (* ================= fd 0 IS THE CONSOLE ================= *)
      (* THE ECHO TAILORING IS A WRAPPER NOW (lane RD-4).  The walk, the
         refutation of the [-1] arm at an open readable console descriptor,
         the receipt's two GUARDED rows (the per-byte ledger's linearity
         and [ConsoleInv.cons_swallow]'s copy-out fault) and the window's
         assembly are all the NEUTRAL console member's
         ([UkReadCons.wp_uk_ecall_read_cons]) -- none of them was ever
         about an application.  What is left here is the era's own reading
         of the input segment the call consumed, which is what [Rin] is
         for. *)
      assert (Hfdc : UkSh.ush_fd0c l) by (exists wr; exact Hl0).
      iDestruct (ush_read_pay_era_at R γ N γp I Hst Hts Hwd Hep with "Hlk Hpos")
        as "[Hacc Hlink]".
      iApply (wp_uk_ecall_read_cons_at (PS := uprogSG_free) N h m pc
                (uint (m !!! Regidx a1_idx)) k cap f avail l vw 0%nat wr
                (ush_rd_ret γp (lk_T L) n) (ush_rd_in_at R γ I)
                Hn Ha0 ltac:(unfold NSTD; lia) Hl0 eq_refl Ha2 Hcapk Hcap31
                Hal with "Hi Hrun Hstd Hbuf Hacc Hlink").
      iIntros (h' r d g) "%Hd %Hgf Hstd Hans Hbuf Hrun".
      iDestruct "Hans" as (dd dc cur hs)
        "(%Hdr & %Hddcap & %Hb1 & %Hb4 & #Htags & Hrd & Hwin)".
      rewrite /ush_rd_ret.
      iDestruct "Hrd" as "[(%Hcur & Hp & Hrdt & Hpa) | [#HT Hp]]"; last first.
      { (* the caller's own [Rd] came back tainted *)
        iApply ("Hcont" $! h' r d g with "[%] [%] Hstd [Hp] Hbuf Hrun");
          [ exact Hd | exact Hgf | ].
        rewrite /UkSh.ush_read_ans /UkSh.ush_pos /UkSh.ush_at.
        iRight. iRight. iFrame "HT".
        iDestruct "Hp" as (n') "Hp". iExists n'. iFrame "Hp".
        rewrite Hpay. iApply (ucons_pay_taint with "HT"). }
      subst cur.
      iDestruct "Hwin" as "[Hw | #Hdirty]"; last first.
      { (* a tokenless reader popped while the call slept *)
        iAssert (lk_T L) as "#HT";
          [ iApply (app_rdcred_elim _ Hst Hwd); iExact "Hdirty" | ].
        iApply ("Hcont" $! h' r d g with "[%] [%] Hstd [Hp] Hbuf Hrun");
          [ exact Hd | exact Hgf | ].
        rewrite /UkSh.ush_read_ans /UkSh.ush_pos /UkSh.ush_at.
        iRight. iRight. iFrame "HT". iExists (n + dc)%nat. iFrame "Hp".
        rewrite Hpay. iApply (ucons_pay_taint with "HT"). }
      rewrite /uread_cons_win.
      iDestruct "Hw" as (sl) "(%Hch & #Hlb & %Hwinf & #Hsw & %Hddc & Hbnd)".
      iDestruct "Hbnd" as (sl2 ws)
        "(#Hlb2 & %Hpre2 & %Hlen2 & %Hlws & %Hwsj & Hrin)".
      (* THE BOUNDARY'S ANSWER, and THE PIECES KEPT TOGETHER (lane
         IO-LEAF, M5(3)): the era's credential at the window's far end
         goes back beside the token and both halves of the position pair,
         but NOT into the payload -- the far end is in the middle of a
         line, where the payload's own boundary row is false.
         WHAT THE CALL ADDED IS A LIST, NOT A COUNT (project
         echo-any-line): the era's input at the far end is the lease's own
         input extended by [J], because both are lower bounds of one
         echoed list ([EchoOut.inp_lb_cmp]) and the lease's is the
         shorter. *)
      iAssert ((∃ J : list (bv 8),
                  ⌜length J = dc⌝ ∗ ⌜rk_disc L R (I ++ J)⌝
                  ∗ ⌜(0 < dd)%nat -> g 0%nat = J !!! 0%nat⌝
                  ∗ ush_mid_at (lk_rres L) γ γp (I ++ J))
               ∨ (lk_T L ∗ UkSh.ush_pos N γp))%I
        with "[Hrin Hrdt Hpa Hp]" as "Hera".
      { rewrite /ush_rd_in_at.
        iDestruct "Hrin" as "[Hret | #HT]"; last first.
        { iRight. iFrame "HT". rewrite /UkSh.ush_pos /UkSh.ush_at.
          iExists (n + dc)%nat. iFrame "Hp". rewrite Hpay.
          iApply (ucons_pay_taint with "HT"). }
        iDestruct "Hret" as (v) "(#Hpin & #HE0 & #Hres0 & Hret)".
        (* THE WINDOW ARM, AS ONE LAW (lane LINK-GEN-4): everything this
           block used to open [EchoOut.read_ret] by hand for is
           [ReadRec.rk_arms], at the rows the console member just handed
           over. *)
        iDestruct (Hep v with "Hpin") as "#Hpl".
        iDestruct (lk_pin_epin L (S gen_id) v with "Hpl") as "#Hepl".
        iDestruct (rk_arms L R fsc_cons v I ws sl sl2 hs dd dc g
                     Hddc Hlws Hwinf Hpre2 Hwsj
                     with "Hepl HE0 Hres0 Hret Htags Hsw Hlb2")
          as "[Hwin | #HT]"; last first.
        { iRight. iFrame "HT". rewrite /UkSh.ush_pos /UkSh.ush_at.
          iExists (n + dc)%nat. iFrame "Hp". rewrite Hpay.
          iApply (ucons_pay_taint with "HT"). }
        iDestruct "Hwin" as "[Hdlr Hj]".
        iDestruct "Hj" as (J) "(%HJlen & %HJdisc & %HJbyte & #HEn & #Hresn)".
        iLeft. iExists J.
        iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
        iSplitR; [ by iPureIntro | ].
        assert (Hcl : length (I ++ J) = (n + dc)%nat)
          by (rewrite length_app HJlen; reflexivity).
        rewrite /ush_mid_at Hcl.
        iFrame "Hp Hpa Hrdt". iExists v. iFrame "Hpin Hdlr HEn Hresn". }
      iDestruct "Hera" as "[Hera | [#HT Hp']]"; last first.
      { iApply ("Hcont" $! h' r d g with "[%] [%] Hstd [Hp'] Hbuf Hrun");
          [ exact Hd | exact Hgf | ].
        rewrite /UkSh.ush_read_ans_at. iRight. iRight. iFrame "HT Hp'". }
      iDestruct "Hera" as (J) "(%HJlen & %HJdisc & %HJbyte & Hmid)".
      iApply ("Hcont" $! h' r d g
                with "[%] [%] Hstd [Hmid] Hbuf Hrun");
        [ exact Hd | exact Hgf | ].
      rewrite /UkSh.ush_read_ans_at. iLeft.
      iExists dd, dc, hs, sl, J.
      iSplitR; [ by iPureIntro | ].
      iSplitR; [ iPureIntro; exact Hddcap | ].
      iSplitR; [ iPureIntro; exact Hb1 | ].
      iSplitR; [ iPureIntro; exact Hb4 | ].
      iSplitR; [ by iPureIntro | ].
      iSplitR; [ iExact "Hlb" | ].
      iSplitR; [ iExact "Htags" | ].
      iSplitR; [ iPureIntro; exact Hwinf | ].
      iSplitR; [ iExact "Hsw" | ].
      iSplitR; [ by iPureIntro | ].
      iSplitR; [ by iPureIntro | ].
      iSplitR; [ by iPureIntro | ].
      iSplitR; [ by iPureIntro | ]. iExact "Hmid".
    - (* ================= fd 0 IS SHUT ================= *)
      iDestruct (ush_read_sup_closed N γp (lk_T L) (ush_rd_in_at R γ I) m pc l n
                   Ha0 Hcl) as "Hsb".
      iApply (wp_uk_ecall_read_recv_at (PS := uprogSG_free) N h m pc
                (bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0
                            : mword 32))
                k f avail (ush_read_fam_era_at R γ γp I (ukn_pay N)) l vw
                Hn eq_refl ltac:(lia) Hal
                with "Hi Hrun Hsb Hstd Hbuf").
      iIntros (h' r d g W M' fdv' cw' cs')
        "%Hd %Hgf %Hlin %HM %Hnf %Harg0 %Harg1 %Harg2 %Htake %Hlz %Hlive
         Hstd Hpost Hrun Hbuf".
      iDestruct (spost_at_read_elim uslot
                   (ush_read_fam_era_at R γ γp I (ukn_pay N)) W
                   (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                   (m !!! Regidx a2_idx) (uvis_fd W) r M' fdv' cw' cs'
                   Harg0 Harg1 Harg2 eq_refl with "Hpost")
        as "[%Hfrret Hpost']".
      iDestruct "Hpost'" as (P) "(%Hperm & %Hwf & %Hlazy & Hrec)".
      iEval (rewrite (ush_fd_st_closed (m !!! Regidx a0_idx) (uvis_fd W) l
                        Ha0 Htake Hcl) /fileread_extra_core) in "Hrec".
      iDestruct "Hrec" as "%Hm1".
      iApply ("Hcont" $! h' r d g
                with "[%] [%] Hstd [Hpos] Hbuf Hrun");
        [ lia | exact Hgf | ].
      rewrite /UkSh.ush_read_ans /UkSh.ush_lease.
      iDestruct "Hpos" as "[Hmid | [#HT Hp]]";
        [ | iRight; iRight; iFrame "HT Hp" ].
      iRight. iLeft.
      iSplitR; [ by iPureIntro | ].
      iSplitR; [ by iPureIntro | ]. iExact "Hmid".
  Qed.

  (* =================================================================== *)
  (*  S7  THE OWED STATEMENT, DISCHARGED.                                 *)
  (*                                                                     *)
  (*  This is [UShLine.ush_read_recv_leaf_holds] back, at the same        *)
  (*  statement lane ECHO-OUT part 5 deleted it at, with the flat input   *)
  (*  licence replaced by the era's read link and the credential read off *)
  (*  sh's own lease -- which took [UInitBootAdequacy]'s [Hsh_owed] down  *)
  (*  to two conjuncts on the way to deleting it (redesign R3).           *)
  (*                                                                     *)
  (*  [echo_links] is a COQ-LEVEL premise for the licence's own reason:   *)
  (*  the result is a Coq-level [⊢], and the discharge site               *)
  (*  ([UInitBoot.echo_Hinit_boot]) is where the record's four equations  *)
  (*  are, which is where [EchoLinks.echo_links_holds] proves it.         *)
  (* =================================================================== *)
  Lemma ush_read_recv_leaf_holds_at {L : LinkRec Σ} (R : ReadRec L)
      (γ : echo_gn) (Wb : list (bv 8) -> iProp Σ)
      (N : uk_names Σ) (γp : gname) (l : list fdstate) :
    ukn_pay N
      = ucons_pay fsc_cons γp (lk_T L) (ush_rd_x_at (lk_rres L) γ Wb) ->
    (⊢ app_sup -∗ lk_T L) ->
    (⊢ lk_T L -∗ app_rdcred) ->
    (* ...and the era's WILD credential's (lane S0) *)
    (⊢ riscv_rdwild (S gen_id) -∗ lk_T L) ->
    (forall v : era_pins, ⊢ era_pin γ (S gen_id) v -∗ lk_pin L (S gen_id) v) ->
    (⊢ lk_links L) ->
    (* AT THE FREE INSTANCE, NAMED (durable-notes, the two-instances
       wedge): [UkRun.urun] carries [udep], so the leaf is PS-indexed, and
       the one that consumes it -- sh's entry -- is at
       [UexecExecInst.uprogSG_free] while ambient resolution here would
       find [uprogSG_gen].  The two are not convertible. *)
    ⊢ UkSh.ush_read_recv_leaf_at (PS := uprogSG_free) N γp (lk_T L)
        (ush_mid_at (lk_rres L) γ γp) (rk_disc L R) fsc_cons l.
  Proof using .
    intros Hpay Hst Hts Hwd Hep Hlk.
    iAssert (lk_links L) as "#Hlk"; [ iApply Hlk | ].
    rewrite /UkSh.ush_read_recv_leaf_at.
    iIntros (h m pc a k cap I f avail)
      "%Hn %Ha0 %Ha1 %Ha2 %Hcapk %Hcap31 %Hfd0 %Hal #Hi Hbuf Hstd Hpos Hrun
       Hcont".
    iDestruct "Hstd" as (vw) "[#Hvok Hstd]".
    iApply (ush_read_recv_era_at_vw R γ Wb N γp l vw h m pc a k cap I f avail
              Hpay Hst Hts Hwd Hep Hn Ha0 Ha1 Ha2 Hcapk Hcap31 Hfd0 Hal
              with "Hlk Hi Hbuf Hstd Hpos Hrun").
    iIntros (h' r d g) "%Hd %Hgf Hstd Hans Hbuf Hrun".
    iApply ("Hcont" $! h' r d g with "[%] [%] [Hstd] Hans Hbuf Hrun");
      [ exact Hd | exact Hgf | rewrite /UkSh.ush_std /ustd_ok; iExists vw; by iFrame "Hvok Hstd" ].
  Qed.

  (* ...AND THE ECHO INSTANCES, by [Definition] with no proof text. *)
  Definition ush_read_recv_era (γ : echo_gn) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T} (Wb : list (bv 8) -> iProp Σ)
      (N : uk_names Σ) (γp : gname) (l : list fdstate)
      (h : CpuId) (m : regfile) (pc : mword 64) (a : Z) (k cap : nat)
      (I : list (bv 8)) (f : nat -> bv 8) (avail : nat) :
    ukn_pay N = ucons_pay fsc_cons γp T (ush_rd_x γ Wb) ->
    (⊢ app_sup -∗ T) ->
    (⊢ T -∗ app_sup) ->
    (⊢ riscv_rdwild (S gen_id) -∗ T) ->
    usysno m = USYS_read ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = 0 ->
    uint (m !!! Regidx a1_idx) = a ->
    uint (m !!! Regidx a2_idx) = Z.of_nat cap ->
    (cap <= k)%nat ->
    (Z.of_nat cap < 2 ^ 31)%Z ->
    UkSh.ush_fd0p l ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    echo_links T γ -∗
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    ubytes (ukn_d N) a k f -∗
    ustd (ukn_fd N) l -∗
    UkSh.ush_lease N γp T (ush_mid γ γp) I -∗
    urun (PS := uprogSG_free) N h m pc avail -∗
    (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8),
       ⌜ (d <= cap)%nat ⌝ -∗
       ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
       ustd (ukn_fd N) l -∗
       UkSh.ush_read_ans N γp T (ush_mid γ γp) fsc_cons l r cap I g -∗
       ubytes (ukn_d N) a k g -∗
       urun (PS := uprogSG_free) N h'
         (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang)
    := fun Hpay Hst Hts Hwd =>
         ush_read_recv_era_at (echo_read_inst T γ) γ Wb N γp l h m pc a k cap
           I f avail Hpay Hst (ush_rdcred_w _ Hts) Hwd (rr_ep_refl γ T).

  Definition ush_read_recv_leaf_holds (γ : echo_gn) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T} (Wb : list (bv 8) -> iProp Σ)
      (N : uk_names Σ) (γp : gname) (l : list fdstate) :
    ukn_pay N = ucons_pay fsc_cons γp T (ush_rd_x γ Wb) ->
    (⊢ app_sup -∗ T) ->
    (⊢ T -∗ app_sup) ->
    (⊢ riscv_rdwild (S gen_id) -∗ T) ->
    (⊢ echo_links T γ) ->
    ⊢ UkSh.ush_read_recv_leaf (PS := uprogSG_free) N γp T
        (ush_mid γ γp) fsc_cons l
    := fun Hpay Hst Hts Hwd =>
         ush_read_recv_leaf_holds_at (echo_read_inst T γ) γ Wb N γp l
           Hpay Hst (ush_rdcred_w _ Hts) Hwd (rr_ep_refl γ T).

End UShLine.
