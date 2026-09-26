(* ===================================================================== *)
(* UkInit.v -- the `init` program on the separation-logic heap.            *)
(*                                                                        *)
(* Three things make init different from sync and echo:                    *)
(*                                                                        *)
(*   IT DOES NOT TERMINATE.  main's restart loop and its inner wait loop   *)
(*   both run forever, so main and start have no continuation and no       *)
(*   postcondition, and the two loops close through [iLoeb] and            *)
(*   [wp_uk_btype_later] -- the first unbounded loops in this tier.        *)
(*                                                                        *)
(*   IT ASSUMES NOTHING ABOUT WHAT THE KERNEL RETURNS.  Every arm of every *)
(*   test in main is reachable, because init handles each failure itself:  *)
(*   mknod when the console is missing, and a diagnostic printf + exit(1)  *)
(*   when fork, exec or wait fails.                                        *)
(*                                                                        *)
(*   IT PRINTS.  The whole printf cone (printf -> vprintf -> putc ->       *)
(*   write) is verified here for a format string containing no '%', which  *)
(*   is what all four of init's literals are -- so printf is a glorified   *)
(*   write(1, s, len).                                                     *)
(* THIS FILE holds the SYSCALL STUB layer only.  The rest of init is one
   file per function, so a change to one does not recompile the others:
   UkInitPutc.v, UkInitVprintf.v, UkInitPrintf.v, UkInitMain.v.  The
   register-index facts they share are in UkProgAbi.v. *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import UmodeArith.  (* [zext8_moi] -- the byte in a1, at the width
                                the store leaves it *)
Require Import RegFile.
Require Import UexecSlot.   (* [uvis] -- the key vocabulary *)
Require Import UserHeap.    (* [ubyte] -- the byte putc spills into its frame *)
Require Import UserPerm.    (* [perm_of] / [lazy_free] -- the rows the write
                               leaf hands back with the short arm's reason *)
Require Import ProcPtOwn.   (* [proc_pt_wf] *)
Require Import UserPtTree.  (* [uva_rmapped] *)
Require Import UkRun UkRunLeaf UkRunSys.
Require Import UkRunExecRef.  (* [udepw_at_refR] -- the exec deposit at a
                                 supplier-named refund (lane M6b) *)
Require Import UCodeInit.
Require Import UInitArgv.  (* [init_argv] -- the writable half of init's image *)
Require Import CtxIdDefs.
Require User.InitSyms User.InitInstrs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.

Require Import FdSlots.  (* [fdstate] / [FdClosed] -- the console prologue's
                            rows name the descriptor states themselves *)
Require Import ProcGeom. (* [NOFILE] -- the bound the tracked dup's number
                            comes back with *)
Require Import UInitFd.  (* the console prologue's ledger rows, at an
                            ABSTRACT descriptor state: [ufd_l0] .. [ufd_l3],
                            the three scans, and init's head *)
Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)
Require Import UsysMemOk. (* [USYS_exec] -- excluded by the minting law *)
Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)
Require Import UserChildren. (* [uch] -- init's own half of its children set,
                                at the very set wait() moves and redeems
                                through *)
Require Import UexecRet.     (* [uwait_ans] -- what the wait leaf answers *)
Require Import Xv6Cameras.   (* [uartGhostG] -- the console ring's cameras *)
Require Import UartNames.    (* [cons_names] *)
Require Import UserConsole.  (* [ucons_pay] / [upos] -- sh's exit payload
                                and its half of the position pair *)
Require Import UserCwd.  (* [ucwd]: the process's own half of its cwd -- the
                            exec leaf is indexed by it *)
Require FsImg.           (* [FsImg.ROOTINO]: init never chdirs, so its
                            working directory is the root inum forever.
                            QUALIFIED, not imported: this file has no other
                            business with the file-system tower. *)

Section UkInit.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  (* THE PROGRAM'S PAYLOAD, as a section hypothesis: all this walk needs
     of it is that it does not read the exit status ([UkRun.ukn_const]),
     which is what lets the exit stub answer the additive pair out of the
     one resource the run keeps.  A SECTION hypothesis rather than a
     premise on the exit stub, so that every lemma between the entry and
     the ecall is generalized over it automatically and no intermediate
     statement has to carry it by hand.
     AT THE CLASS AND NOT AT [ukn_triv], because these lemmas are walked
     by TWO records: /init's own, whose payload is trivial
     ([UInitKernel.init_uexec_slot], through [UkRun.ukn_const_of_triv]),
     and the CHILD it forks to exec sh, whose payload is the console
     reader token ([UserConsole.ucons_pay], constant by
     [UserConsole.ucons_pay_const]). *)
  Context `{Hpay : !ukn_const N}.
  (* ...AND THAT IT HOLDS NO OFFSET HALF (lane OFF-HAND-4, S1).  dup(2)
     COPIES its argument's descriptor row onto the slot fdalloc chose, and
     that slot is not one the record can be said to hold
     ([UkRun.urun_rows_dup]'s guard, [UsysMemOk.usys_fd_ok_held]'s note),
     so the two dup leaves ask their caller for the empty held set.  A
     CLASS, [ukn_const]'s mould: it is named only in the [Proof using] of
     the lemmas that walk a dup, and the entry constructor that minted the
     record is what discharges it. *)
  (* the fields, under the names the engine has always used *)
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Local Notation γfd := (ukn_fd N).
  Local Notation γcwd := (ukn_cwd N).
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
  Context `{!ctokG Σ}.
  (* the console ring's cameras, at the narrow class ([UserConsole.v]'s
     header): the POSITION init lends its child is stated over them. *)
  Context `{!uartGhostG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  (* THE NUMBERS THIS PROGRAM ADMITS ([UexecSG.uprogSG]'s [psok]).  A SECTION
     hypothesis, so no lemma statement in this file names it and the ~570
     [urun] sites did not move; the program's kernel-side constructor
     discharges it.
     AT THE FREE NUMBERS AND NO MORE (lane SUPPLY-SPLIT).  It used to read
     "every number but exec", which at the generic instance is true and at
     a VERIFIED program's instance is not: a program whose supplier is the
     application's ([AppInv.app_sup] -- for the echo application, the
     TAINT) could only ever be entered tainted.  What a verified program
     admits is [UexecSG.free_num] -- every number whose bundle is [emp],
     plus chdir, whose branch is a closed fact -- and at
     [UexecExecInst.uprogSG_free] this hypothesis is the identity.  A call
     at a number OUTSIDE that set takes its own deposit as a premise
     ([UkRun.udepw_law]) and is named at its site. *)
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation s7_idx := (mword_of_int 23 : mword 5).
  Local Notation s8_idx := (mword_of_int 24 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).

  (* ===================================================================== *)
  (* THE SYSCALL STUBS.  usys.S's three-instruction bodies: the number into *)
  (* a7, [ecall], return.  Eight of them, and the row each takes is the     *)
  (* whole of what distinguishes them:                                      *)
  (*                                                                        *)
  (*   open, mknod, dup, write   the QUIET row -- none of the four writes    *)
  (*                             a user byte, so the heap comes back as it   *)
  (*                             went in                                     *)
  (*   exit                      the arm with no continuation                *)
  (*   wait                      the null-status-pointer arm: init passes    *)
  (*                             a null pointer, so nothing is copied out    *)
  (*   exec                      the failure arm, which is the only one      *)
  (*                             that returns here at all                    *)
  (*   fork                      two successors; see the fork leaf           *)
  (* ===================================================================== *)
  (* THE LEDGER GOES IN AND COMES BACK AT A STATE THIS PROOF DOES NOT NAME.
     open allocates, and an allocation that lands on a standard stream
     rewrites that slot's fragment -- which lives in the ledger -- so the
     table cannot move without it.  init does not read the result here
     (it drops the descriptor), so [ustd_any] is all it needs to carry;
     what it would take to say init's own open lands on 0 is the ledger at
     a NAMED state, which is [UserFd.ualloc]'s business. *)
  (* THE OPEN DEPOSIT, AS A PREMISE (lane SUPPLY-SPLIT, P4).  open(15) is a
     CLAIM number -- its create / trunc / child legs are write-kind commits
     on the abstract view -- so this leaf does not route through
     [UkRun.udep]'s law.  Under the CREDENTIAL /init's opens go through the
     PINNED leaves below ([uki_open_absent_leaf] / [uki_open_console_leaf],
     discharged in UInitConsK); this walk is what the TAINT arm takes, and
     its one premise is the taint's own deposit. *)
  Lemma wp_kinit_open (h : CpuId) (m : regfile) (avail : nat) :
    udepw_law 15 -∗
    init_code γt -∗
    urun N h m (mword_of_int InitSyms.open) avail -∗
    ustd_any γfd -∗
    (∀ (h' : CpuId) (ret : mword 64),
       ustd_any γfd -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    iIntros "#Hwr #Hcode Hrun Hstd Hcont".
    iDestruct "Hstd" as (l) "Hstd".
    destruct init_syms_pins as (Hstart & Hmain & Hprintf & Hvprintf & Hputc & Hopen & Hmknod & Hdup & Hfork & Hwait & Hexec & Hwrite & Hexit). rewrite Hopen.
    (* ---- 0x3b2  c.li a7,15 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x3b2)
              (mword_of_int 15 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_3b2 with "Hcode"). }
    assert (E0 : add_vec_int (mword_of_int 0x3b2 : mword 64) 2
                 = mword_of_int 0x3b4)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 15 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m).
    (* ---- 0x3b4  ecall -- the QUIET row ---- *)
    (* open MOVES THE DESCRIPTOR TABLE, so it is not the quiet leaf: the
       dedicated one mints the handle for whatever descriptor came back.
       init does not yet carry that handle -- it is dropped here -- but the
       leaf is what will hand it over when it does. *)
    iApply (wp_uk_ecall_open N h1 m1 (mword_of_int 0x3b4) l avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 15 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun [] Hstd").
    { iApply (uis_init_3b4 with "Hcode"). }
    (* THE FLAGGED DEPOSIT: open(15), the taint arm's own *)
    { iApply (udepw_of_law N m1 (mword_of_int 0x3b4) 15 with "Hwr"). }
    assert (E1 : add_vec_int (mword_of_int 0x3b4 : mword 64) 4
                 = mword_of_int 0x3b8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2 ret) "Hal Hrun".
    (* the ledger, off whichever arm the allocation took *)
    iAssert (ustd_any γfd) with "[Hal]" as "Hstd".
    { iDestruct "Hal" as "[Hal | [_ Hstd]]"; [| by iExists l].
      iDestruct "Hal" as (fd rd wr t) "[_ Hal]".
      iDestruct (ualloc_ledger with "Hal") as "Hstd". by iExists _. }
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0x3b8  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 15 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0x3b8) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_3b8 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hstd Hrun").
  Qed.

  (* ===================================================================== *)
  (* INIT'S CONSOLE PROLOGUE, AS THREE LEAVES (lane OPEN-PIN, phase 3).      *)
  (*                                                                        *)
  (* [wp_kinit_open] above DROPS the descriptor and [wp_kinit_mknod] goes    *)
  (* through the QUIET leaf, so neither says anything about the console.     *)
  (* What says something is a PINNED bundle at the path "console", and a     *)
  (* pin is a fact about the abstract file-system view -- which this file    *)
  (* may not name: it sits below the file-system tower, and the rule is the  *)
  (* one [UConsLine.v:202] states for the read leaf's taint (THE PROGRAM     *)
  (* TIER NAMES NO APPLICATION).                                            *)
  (*                                                                        *)
  (* So the three calls are stated HERE, as leaf BODIES in program-tier      *)
  (* vocabulary over three abstract pieces, and DISCHARGED at the era, where *)
  (* the pin lives -- [UkSh.ush_read_leaf] and its discharge one tier up     *)
  (* ([UShLine.ush_read_recv_leaf_holds]) are the mould, and the discharge   *)
  (* walks the same three instructions each                                  *)
  (* stub above walks, with [UkRunSys.wp_uk_ecall_open_recv_body] /          *)
  (* [wp_uk_ecall_quiet_recv_body] in place of the post-dropping leaves.     *)
  (*                                                                        *)
  (*   [T]   THE TAINT.  The application is off its discipline; the ledger   *)
  (*         is at a state nobody named and nothing is claimed.              *)
  (*   [K]   THE ABSENCE CREDENTIAL ([AppEcho.cons_key] at echo's era).  An  *)
  (*         EXCLUSIVE token whose holder knows the console node does not    *)
  (*         exist, which is what makes the FIRST open's success arm         *)
  (*         REFUTABLE rather than an arm init has to carry.  It goes in and *)
  (*         comes back: one credential answers the first open, the mknod    *)
  (*         and -- if the mknod failed -- the second open in turn.          *)
  (*   [stc] THE DESCRIPTOR THE CONSOLE OPEN INSTALLS                        *)
  (*         ([UInitCons.init_cons_fd] at echo's era).                       *)
  (*                                                                        *)
  (* AND THE MKNOD'S SUCCESS ARM HANDS BACK THE SECOND OPEN'S LEAF.  That is *)
  (* how "the node exists now" crosses from the application tier to this     *)
  (* one without being nameable here: the era's flag                         *)
  (* ([AppEcho.cons_made]) is what the resolving pin runs on, and what a     *)
  (* program-tier statement can carry instead of the flag is the leaf the    *)
  (* flag proves.                                                            *)
  (* ===================================================================== *)

  (* THE SECOND open, AT THE RESOLVING PIN: three arms and no more.  fd 0
     is the console; or the allocation failed ([filealloc] / [fdalloc],
     about which /init proves NOTHING -- app-echo.md, "OPEN-PIN FINDINGS",
     FACT 3) and the ledger did not move; or the taint.  The number 0 is
     the LEDGER's answer and not the kernel's ([UInitFd.ufd_alloc0]). *)
  Definition uki_open_console_leaf (T : iProp Σ) (stc : fdstate) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (avail : nat),
       init_code γt -∗
       (* THE READ-ONLY IMAGE AND THE TWO ARGUMENT WORDS.  A pinned open is
          about a PATH, and the path is a string in /init's own .rodata at
          0x980 read through the LOANED heap ([UInitConsK]'s supplier), so
          the era-level discharge needs the persistent view of those bytes
          and the two registers the stub is called with: a0 = "console",
          a1 = O_RDWR.  Both call sites hold them
          ([UkInitMain.wp_kinit_main] @0x0e-0x16,
          [wp_kinit_main_repair_tail] @0x74-0x7e). *)
       init_rodata γt -∗
       ⌜ m !!! Regidx a0_idx = (mword_of_int 0x980 : mword 64)
         /\ m !!! Regidx a1_idx = (mword_of_int 2 : mword 64) ⌝ -∗
       urun N h m (mword_of_int InitSyms.open) avail -∗
       UserCwd.ucwd γcwd FsImg.ROOTINO -∗
       ustd_ok T γfd ufd_l0 -∗
       (∀ (h' : CpuId) (ret : mword 64),
          ((⌜ret = (mword_of_int 0 : mword 64)⌝ ∗ ustd_ok T γfd (ufd_l1 stc))
           ∨ (⌜ret = (mword_of_int (-1) : mword 64)⌝ ∗ ustd_ok T γfd ufd_l0)
           ∨ (ustd_any γfd ∗ T)) -∗
          UserCwd.ucwd γcwd FsImg.ROOTINO -∗
          urun N h'
            (<[Regidx a0_idx := ret]>
               (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m))
            (ret_pc (m !!! Regidx ra_idx)) avail -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* THE FIRST open, AT THE PIN THAT MISSES -- and the repair arm's second
     open when the mknod failed.  TWO arms: the call returned [-1] and
     nothing moved, or the taint.  There is no third: at a view the
     credential holds of, the walk dies at hop 0, so the success arm is
     refuted rather than carried -- which is what makes the [blt a0,x0] at
     0x1a provably take the repair arm.

     THE LEDGER IS ARBITRARY because both callers are: the first open runs
     at [UInitFd.ufd_l0] and the repair arm's second open at whatever the
     failed mknod left, which is the same list -- but nothing here needs to
     know that. *)
  Definition uki_open_absent_leaf (T K : iProp Σ) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (l : list fdstate) (avail : nat),
       init_code γt -∗
       (* the read-only image and the two argument words, for
          [uki_open_console_leaf]'s reason *)
       init_rodata γt -∗
       ⌜ m !!! Regidx a0_idx = (mword_of_int 0x980 : mword 64)
         /\ m !!! Regidx a1_idx = (mword_of_int 2 : mword 64) ⌝ -∗
       urun N h m (mword_of_int InitSyms.open) avail -∗
       UserCwd.ucwd γcwd FsImg.ROOTINO -∗
       ustd_ok T γfd l -∗
       K -∗
       (∀ (h' : CpuId) (ret : mword 64),
          ((⌜ret = (mword_of_int (-1) : mword 64)⌝ ∗ ustd_ok T γfd l ∗ K)
           ∨ (ustd_any γfd ∗ T)) -∗
          UserCwd.ucwd γcwd FsImg.ROOTINO -∗
          urun N h'
            (<[Regidx a0_idx := ret]>
               (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m))
            (ret_pc (m !!! Regidx ra_idx)) avail -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* THE MKNOD, which is where the console node comes into existence and the
     one place /init's own WRITE pays a step of the application's claim
     rather than reading one out of its supply.  Three arms, and the first
     is what the whole lane is for: the node exists, so the SECOND open's
     leaf is available.  On failure the credential comes back -- and then
     the second open is the MISS leaf again, and fd 0 stays closed. *)
  (* WHAT THE MKNOD LEAVES, as ONE resource (lane E2).  Three arms:
     the node exists now, so the SECOND open's leaf is available; the call
     failed and what comes back is SOME credential with its own miss leaf
     (at the KEY arm that is the SEAL -- [AppEcho.cons_never] -- and not
     the key, because /init will not try again and sh's own first open has
     to be able to miss too: lane SH-OPEN); or the taint.

     [Cns] RIDES THE FIRST TWO ARMS.  It is the console credential /init's
     exec of sh hands on ([UkSh.ush_fd0]'s pin side, SH-OPEN's
     [ush_cons_in]), and WHICH credential it is is decided HERE and not at
     /init's entry -- the mknod's outcome is what decides it.  Abstract at
     this tier for the reason every application fact is
     ([UConsLine.v:202]: THE PROGRAM TIER NAMES NO APPLICATION); the taint
     arm carries none because [init_cons_sup]'s second law pays it. *)
  Definition uki_mknod_out (T Cns : iProp Σ) (stc : fdstate) : iProp Σ :=
    ((uki_open_console_leaf T stc ∗ Cns)
     ∨ (∃ K' : iProp Σ, □ uki_open_absent_leaf T K' ∗ K' ∗ Cns)
     ∨ T)%I.

  Definition uki_mknod_leaf (T K Cns : iProp Σ) (stc : fdstate) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (avail : nat),
       init_code γt -∗
       (* the read-only image and the THREE argument words: a0 = "console"
          at 0x980, a1 = CONSOLE, a2 = 0 -- the numbers row 17 reads
          through [SysMknodDefs.dev_arg].  The repair arm holds all four
          ([UkInitMain.wp_kinit_main_repair] @0x64-0x70). *)
       init_rodata γt -∗
       ⌜ m !!! Regidx a0_idx = (mword_of_int 0x980 : mword 64)
         /\ m !!! Regidx a1_idx = (mword_of_int 1 : mword 64)
         /\ m !!! Regidx a2_idx = (mword_of_int 0 : mword 64) ⌝ -∗
       urun N h m (mword_of_int InitSyms.mknod) avail -∗
       UserCwd.ucwd γcwd FsImg.ROOTINO -∗
       K -∗
       (∀ (h' : CpuId) (ret : mword 64),
          uki_mknod_out T Cns stc -∗
          UserCwd.ucwd γcwd FsImg.ROOTINO -∗
          urun N h'
            (<[Regidx a0_idx := ret]>
               (<[Regidx a7_idx := (mword_of_int 17 : mword 64)]> m))
            (ret_pc (m !!! Regidx ra_idx)) avail -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* ...AND THE PAIR /init CARRIES FROM ITS ENTRY, persistently: the miss
     leaf is used TWICE (0x16 and, on the repair arm, 0x7e) and the mknod
     leaf once, and both are entailed by persistent ingredients at the era
     -- [AppInv.app_inv], the [□] claim law and
     [UInitCons.init_cons_abs_law] -- so the bundle is a [□] and threads
     through the restart loop's [iLöb] the way [init_exec_sup] does. *)
  Definition init_cons_leaves (T K Cns : iProp Σ) (stc : fdstate) : iProp Σ :=
    (□ uki_open_absent_leaf T K ∗ □ uki_mknod_leaf T K Cns stc)%I.

  (* WHAT THE FIRST OPEN LEAVES, as ONE resource: the call returned [-1]
     (the pure half is read at the [blt] and dropped), so the ledger and the
     credential are back -- or the application is tainted and the ledger is
     at a state nobody named.  Both of /init's console arms are walked from
     this, which is why the repair arm takes it rather than the credential:
     under the taint the credential is gone and the mknod and the second
     open still have to be walked. *)
  Definition uki_cons_in (T K : iProp Σ) : iProp Σ :=
    ((ustd_ok T γfd ufd_l0 ∗ K) ∨ (ustd_any γfd ∗ T))%I.

  (* ...AND WHAT THE REPAIR ARM'S SECOND OPEN IS, whichever of the three
     things the mknod left: a call at the all-closed ledger that lands
     /init's head.  ONE shape, so the 0x74..0x82 tail is walked ONCE. *)
  (* ...and what it is CALLED at: the ledger the first open left, or the
     taint.  Both arms reach the repair arm, because /init's C tests
     neither the mknod's result nor the second open's. *)
  Definition uki_open2_in (T : iProp Σ) : iProp Σ :=
    (ustd_ok T γfd ufd_l0 ∨ (ustd_any γfd ∗ T))%I.

  Definition uki_open2 (T : iProp Σ) (stc : fdstate) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (avail : nat),
       init_code γt -∗
       (* the read-only image and the two argument words, threaded to
          whichever of the three leaves the mknod's answer chose *)
       init_rodata γt -∗
       ⌜ m !!! Regidx a0_idx = (mword_of_int 0x980 : mword 64)
         /\ m !!! Regidx a1_idx = (mword_of_int 2 : mword 64) ⌝ -∗
       urun N h m (mword_of_int InitSyms.open) avail -∗
       UserCwd.ucwd γcwd FsImg.ROOTINO -∗
       uki_open2_in T -∗
       (∀ (h' : CpuId) (ret : mword 64),
          (* THE HEAD BEFORE THE TWO DUPS (lane IO-LEAF, M1(f)): the console
             arm is the NAMED ledger the open left, [UInitFd.ufd_l1 stc],
             and not `some list whose slot 0 is [stc]'.  Carrying the name
             through the two dups at 0x20 and 0x26 is what pins fds 1 and
             2 ([UkInitMain.wp_kinit_main_from_1e]). *)
          ufd_head1 T stc γfd -∗
          UserCwd.ucwd γcwd FsImg.ROOTINO -∗
          urun N h'
            (<[Regidx a0_idx := ret]>
               (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m))
            (ret_pc (m !!! Regidx ra_idx)) avail -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  Global Instance init_cons_leaves_persistent T K Cns stc :
    Persistent (init_cons_leaves T K Cns stc).
  Proof using . rewrite /init_cons_leaves. apply _. Qed.

  (* ===================================================================== *)
  (* THE OTHER ARM OF THE CONSOLE DANCE (lane E2): THE VIEW ALREADY HAS      *)
  (* THE NODE.                                                              *)
  (*                                                                        *)
  (* Everything above is /init's dance when its FIRST open MISSES, and that  *)
  (* is one of the two states the application's boot resource can be in      *)
  (* ([AppEcho.echo_boot] is [cons_key r ∨ ∃ i, cons_made r i], and THE ARM  *)
  (* IS DECIDED BY THE VIEW, never by the era: era 0's image carries no      *)
  (* device node, but any later era's view does once /init's mknod           *)
  (* committed).  At the FLAG arm the first open HITS, so                    *)
  (* [uki_open_absent_leaf] -- whose post says the call returned [-1] -- is  *)
  (* not provable and must not be what the walk's first open takes.  What it *)
  (* takes there is [uki_open_console_leaf], the SAME leaf as the second     *)
  (* open at the miss arm: the node is there, the pin resolves, and the      *)
  (* three arms are fd 0 / the allocation failed / the taint.                *)
  (*                                                                        *)
  (* THE REPAIR ARM IS STILL WALKED AT THE FLAG, and that is the whole       *)
  (* reason this is a PAIR and not a single leaf: /init proves nothing about *)
  (* [filealloc]/[fdalloc] succeeding (app-echo.md, OPEN-PIN FINDINGS, FACT  *)
  (* 3), so the first open can return [-1] with the node present, the [blt]  *)
  (* at 0x1a takes the repair arm, and the mknod at 0x64 runs -- against a   *)
  (* view that ALREADY HAS `console` in the root, where [create] finds the   *)
  (* entry and returns 0, so the call fails and nothing commits.  The leaf   *)
  (* for it therefore takes NO credential and always hands the console leaf  *)
  (* back: the node was there before the call and is there after it.         *)
  (* ===================================================================== *)
  Definition uki_mknod_hit_leaf (T Cns : iProp Σ) (stc : fdstate) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (avail : nat),
       init_code γt -∗
       init_rodata γt -∗
       ⌜ m !!! Regidx a0_idx = (mword_of_int 0x980 : mword 64)
         /\ m !!! Regidx a1_idx = (mword_of_int 1 : mword 64)
         /\ m !!! Regidx a2_idx = (mword_of_int 0 : mword 64) ⌝ -∗
       urun N h m (mword_of_int InitSyms.mknod) avail -∗
       UserCwd.ucwd γcwd FsImg.ROOTINO -∗
       (∀ (h' : CpuId) (ret : mword 64),
          uki_mknod_out T Cns stc -∗
          UserCwd.ucwd γcwd FsImg.ROOTINO -∗
          urun N h'
            (<[Regidx a0_idx := ret]>
               (<[Regidx a7_idx := (mword_of_int 17 : mword 64)]> m))
            (ret_pc (m !!! Regidx ra_idx)) avail -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* THE THREE WAYS TO GET ONE, and they are the three states /init's
     repair arm can be in: the MISS route spends its credential in the
     pinned leaf; the FLAG route already has one; and under the taint
     there is no pin at all and the generic stub walks the call, paid by
     17's deposit off the taint. *)
  Lemma uki_mknod_hit_of_leaf (T K Cns : iProp Σ) (stc : fdstate) :
    uki_mknod_leaf T K Cns stc -∗ K -∗ uki_mknod_hit_leaf T Cns stc.
  Proof using .
    iIntros "Hl HK" (h m avail) "#Hcode #Hro %Hargs Hrun Hcwd Hcont".
    iApply ("Hl" $! h m avail with "Hcode Hro [%] Hrun Hcwd HK Hcont").
    exact Hargs.
  Qed.


  (* ...AND THE PAIR THE FLAG ARM CARRIES FROM THE ENTRY, [init_cons_leaves]'
     twin: the first open's leaf is the CONSOLE one and the repair's mknod
     needs no credential. *)
  Definition init_cons_hit (T Cns : iProp Σ) (stc : fdstate) : iProp Σ :=
    (□ uki_open_console_leaf T stc ∗ □ uki_mknod_hit_leaf T Cns stc ∗ Cns)%I.

  (* THE CONSOLE DANCE, AS ONE ENTRY PREMISE.  This is what
     [UInitKernel.init_uexec_slot] takes in place of the pair
     [init_cons_leaves T K stc] and [K]: the arm the application's boot
     resource decided, WITH its credential inside it -- so the constructor
     no longer carries a [K] parameter that only one of the two arms has.
     LINEAR, because the miss arm's credential is exclusive; the leaves
     inside both arms are persistent, which is what lets one dance serve
     every round of the restart loop's [iLob]. *)
  Definition init_cons_dance (T Cns : iProp Σ) (stc : fdstate) : iProp Σ :=
    ((∃ K : iProp Σ, init_cons_leaves T K Cns stc ∗ K)
     ∨ init_cons_hit T Cns stc)%I.

  Lemma init_cons_dance_miss (T K Cns : iProp Σ) (stc : fdstate) :
    init_cons_leaves T K Cns stc -∗ K -∗ init_cons_dance T Cns stc.
  Proof using .
    iIntros "#Hl HK". rewrite /init_cons_dance. iLeft.
    iExists K. iFrame "Hl HK".
  Qed.

  Lemma init_cons_dance_hit (T Cns : iProp Σ) (stc : fdstate) :
    init_cons_hit T Cns stc -∗ init_cons_dance T Cns stc.
  Proof using . iIntros "Hh". rewrite /init_cons_dance. by iRight. Qed.

  (* ===================================================================== *)
  (* THE DEPOSITS /init OWES (lane SUPPLY-SPLIT, P4), as ONE persistent      *)
  (* bundle, so the chain from [wp_kinit_start] down to the write leaf       *)
  (* threads one name instead of three.                                     *)
  (*                                                                        *)
  (*   write(16)  UNCONDITIONALLY.  Every line /init prints -- the banner,   *)
  (*              "init: starting sh", the three diagnostics -- is one       *)
  (*              ecall of 16, whose branch of                               *)
  (*              [UexecExecInst.xv6_sbundle] is the write chain at a key    *)
  (*              whose descriptor row may be an inode.  The minting law is  *)
  (*              key-free, so no supplier admits it; E5's output lane       *)
  (*              discharges this from the application's console claim.      *)
  (*   open(15) and mknod(17) UNDER THE TAINT ONLY.  With the credential in  *)
  (*              hand both go through the PINNED leaves                     *)
  (*              ([init_cons_leaves]), which UInitConsK discharges at the   *)
  (*              era; the taint arms have no pin and walk the generic stub, *)
  (*              so they take the deposit -- as a law OFF [T], which is     *)
  (*              what the era can actually pay ([AppEcho.echo_sup_of_taint] *)
  (*              turns the taint into the supply, and the supply pays any   *)
  (*              number's bundle).                                          *)
  (*                                                                        *)
  (* WHAT IS NOT HERE: [UkRun.udep] at the generic supplier.  That is the    *)
  (* whole point of the lane -- /init's slot may not be a function of        *)
  (* [AppInv.app_sup], because for the echo application that IS the taint.   *)
  (* ===================================================================== *)
  (* [init_deps] is stated AFTER this section (lane EXEC-SEAM, (D)): its
     write conjunct now bundles the closed-fd leaf at EVERY record, and a
     record-generic law cannot be spelled at the section's [N]. *)

  (* ...and mknod's, for open's reason: 17's branch is a create, and the
     credential arm goes through [uki_mknod_leaf]. *)
  Lemma wp_kinit_mknod (h : CpuId) (m : regfile) (avail : nat) :
    udepw_law 17 -∗
    init_code γt -∗
    urun N h m (mword_of_int InitSyms.mknod) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 17 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    iIntros "#Hwr #Hcode Hrun Hcont".
    destruct init_syms_pins as (Hstart & Hmain & Hprintf & Hvprintf & Hputc & Hopen & Hmknod & Hdup & Hfork & Hwait & Hexec & Hwrite & Hexit). rewrite Hmknod.
    (* ---- 0x3ba  c.li a7,17 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x3ba)
              (mword_of_int 17 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_3ba with "Hcode"). }
    assert (E0 : add_vec_int (mword_of_int 0x3ba : mword 64) 2
                 = mword_of_int 0x3bc)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 17 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 17 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 17 : mword 64)]> m).
    (* ---- 0x3bc  ecall -- the QUIET row ---- *)
    iApply (wp_uk_ecall_quiet N h1 m1 (mword_of_int 0x3bc) 17 avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 17 : mword 64));
                    vm_compute; reflexivity)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate)
              (* ...and the three descriptor-moving numbers, and chdir *)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate)
              (* ...and a number the full mask passes, not seccomp's *)
              ltac:(lia) ltac:(discriminate)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun []").
    { iApply (uis_init_3bc with "Hcode"). }
    (* THE FLAGGED DEPOSIT: mknod(17), the taint arm's own *)
    { iApply (udepw_of_law N m1 (mword_of_int 0x3bc) 17 with "Hwr"). }
    assert (E1 : add_vec_int (mword_of_int 0x3bc : mword 64) 4
                 = mword_of_int 0x3c0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2 ret) "Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0x3c0  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 17 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0x3c0) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_3c0 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hrun").
  Qed.

  Lemma uki_mknod_hit_of_taint (T Cns : iProp Σ) `{!Persistent T}
      (stc : fdstate) :
    □ (T -∗ udepw_law 17) -∗ T -∗ uki_mknod_hit_leaf T Cns stc.
  Proof using .
    iIntros "#Hwl #Ht" (h m avail) "#Hcode #Hro %Hargs Hrun Hcwd Hcont".
    iDestruct ("Hwl" with "Ht") as "#Hwr17".
    iApply (wp_kinit_mknod h m avail with "Hwr17 Hcode Hrun").
    iIntros (h' ret) "Hrun".
    iApply ("Hcont" $! h' ret with "[] Hcwd Hrun").
    rewrite /uki_mknod_out. iRight. iRight. iExact "Ht".
  Qed.

  (* ===================================================================== *)
  (* THE FIRST open, AT EITHER ARM OF THE DANCE -- ONE SHAPE, so /init's     *)
  (* walk is written once.                                                  *)
  (*                                                                        *)
  (* The two arms of [init_cons_dance] differ in WHICH leaf answers the      *)
  (* call at 0x16 (the MISS leaf at the key, or the CONSOLE leaf at the      *)
  (* flag) and in nothing else: the [blt] at 0x1a reads the return value,    *)
  (* the repair arm at 0x64 needs a mknod step, and the fall-through at      *)
  (* 0x1e needs the head.  So both are collapsed to THIS post before the     *)
  (* call, and the walk below sees three arms at either era.                 *)
  (*                                                                        *)
  (* THE MKNOD STEP RIDES THE TWO ARMS THAT REACH THE REPAIR.  At the miss   *)
  (* arm it is the pinned leaf with the credential already spent into it;    *)
  (* at the taint it is the generic stub off 17's deposit; at the flag's     *)
  (* own [-1] arm (the open failed at [filealloc]/[fdalloc], about which     *)
  (* /init proves NOTHING) it is the credential-free leaf.                   *)
  (* ===================================================================== *)
  Definition uki_open1_out (T Cns : iProp Σ) (stc : fdstate)
      (ret : mword 64) : iProp Σ :=
    ((⌜ret = (mword_of_int 0 : mword 64)⌝ ∗ ustd_ok T γfd (ufd_l1 stc) ∗ Cns)
     ∨ (⌜ret = (mword_of_int (-1) : mword 64)⌝ ∗ ustd_ok T γfd ufd_l0
        ∗ uki_mknod_hit_leaf T Cns stc)
     ∨ (ustd_any γfd ∗ T ∗ uki_mknod_hit_leaf T Cns stc))%I.

  Definition uki_open1 (T Cns : iProp Σ) (stc : fdstate) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (avail : nat),
       init_code γt -∗
       init_rodata γt -∗
       ⌜ m !!! Regidx a0_idx = (mword_of_int 0x980 : mword 64)
         /\ m !!! Regidx a1_idx = (mword_of_int 2 : mword 64) ⌝ -∗
       urun N h m (mword_of_int InitSyms.open) avail -∗
       UserCwd.ucwd γcwd FsImg.ROOTINO -∗
       ustd_ok T γfd ufd_l0 -∗
       (∀ (h' : CpuId) (ret : mword 64),
          uki_open1_out T Cns stc ret -∗
          UserCwd.ucwd γcwd FsImg.ROOTINO -∗
          urun N h'
            (<[Regidx a0_idx := ret]>
               (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m))
            (ret_pc (m !!! Regidx ra_idx)) avail -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  Lemma uki_open1_of_dance (T Cns : iProp Σ) `{!Persistent T}
      (stc : fdstate) :
    □ (T -∗ udepw_law 17) -∗ init_cons_dance T Cns stc -∗ uki_open1 T Cns stc.
  Proof using .
    iIntros "#Hwl17 Hd".
    iIntros (h m avail) "#Hcode #Hro %Hargs Hrun Hcwd Hstd Hcont".
    iDestruct "Hd" as "[[%K [[#Habs #Hmkl] HK]] | (#Hcl0 & #Hmklh & HC)]".
    - (* THE MISS ROUTE: the first open is the dead walk, and it returns -1 *)
      iApply ("Habs" $! h m ufd_l0 avail
                with "Hcode Hro [%] Hrun Hcwd Hstd HK"); [ exact Hargs | ].
      iIntros (h' ret) "Hans Hcwd Hrun".
      iApply ("Hcont" $! h' ret with "[Hans] Hcwd Hrun").
      rewrite /uki_open1_out.
      iDestruct "Hans" as "[(%Hr & Hstd & HK) | [Hstd #HT]]".
      + iRight. iLeft. iSplitR; [ by iPureIntro | ]. iFrame "Hstd".
        iApply (uki_mknod_hit_of_leaf T K Cns stc with "Hmkl HK").
      + iRight. iRight. iFrame "Hstd HT".
        iApply (uki_mknod_hit_of_taint T Cns stc with "Hwl17 HT").
    - (* THE FLAG ROUTE: the node is there, so the first open is the PINNED
         one -- the same leaf as the miss route's SECOND open. *)
      iApply ("Hcl0" $! h m avail
                with "Hcode Hro [%] Hrun Hcwd Hstd"); [ exact Hargs | ].
      iIntros (h' ret) "Hans Hcwd Hrun".
      iApply ("Hcont" $! h' ret with "[Hans HC] Hcwd Hrun").
      rewrite /uki_open1_out.
      iDestruct "Hans" as "[(%Hr & Hstd) | [(%Hr & Hstd) | [Hstd #HT]]]".
      + iLeft. iSplitR; [ by iPureIntro | ]. iFrame "Hstd HC".
      + iRight. iLeft. iSplitR; [ by iPureIntro | ]. iFrame "Hstd".
        iExact "Hmklh".
      + iRight. iRight. iFrame "Hstd HT".
        iApply (uki_mknod_hit_of_taint T Cns stc with "Hwl17 HT").
  Qed.

  Lemma wp_kinit_dup (h : CpuId) (m : regfile) (avail : nat) :
    init_code γt -∗
    urun N h m (mword_of_int InitSyms.dup) avail -∗
    ustd_any γfd -∗
    (∀ (h' : CpuId) (ret : mword 64),
       ustd_any γfd -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpsok_free.
    iIntros "#Hcode Hrun Hstd Hcont".
    iDestruct "Hstd" as (l) "Hstd".
    destruct init_syms_pins as (Hstart & Hmain & Hprintf & Hvprintf & Hputc & Hopen & Hmknod & Hdup & Hfork & Hwait & Hexec & Hwrite & Hexit). rewrite Hdup.
    (* ---- 0x3ea  c.li a7,10 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x3ea)
              (mword_of_int 10 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_3ea with "Hcode"). }
    assert (E0 : add_vec_int (mword_of_int 0x3ea : mword 64) 2
                 = mword_of_int 0x3ec)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 10 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m).
    (* ---- 0x3ec  ecall -- the QUIET row ---- *)
    (* dup moves the table.  init does not yet track the console descriptor
       it is duplicating, so this is the untracked leaf: it moves the
       authority and hands back no handle.  Switching to
       [wp_uk_ecall_dup] -- which pays a handle and returns two -- is what
       "init's dup is specified" will mean, and needs the handle from
       [wp_kinit_open] threaded down to here. *)
    iApply (wp_uk_ecall_dup_untracked N h1 m1
              (mword_of_int 0x3ec) l avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 10 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun [] Hstd").
    { iApply (uis_init_3ec with "Hcode"). }
    { iApply udepw_of_psok; [ apply Hpsok_free; free_lit | ];
      (discriminate || assumption || (vm_compute; discriminate)). }
    assert (E1 : add_vec_int (mword_of_int 0x3ec : mword 64) 4
                 = mword_of_int 0x3f0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2 ret l') "Hstd Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0x3f0  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 10 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0x3f0) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_3f0 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "[Hstd] Hrun"). by iExists l'.
  Qed.

  (* --------------------------------------------------------------------- *)
  (* dup @0x3ea, ON AN OPEN STANDARD STREAM -- the TRACKED leaf.             *)
  (*                                                                        *)
  (* [wp_kinit_dup] above goes through [UkRunSys.wp_uk_ecall_dup_untracked], *)
  (* which moves the authority and hands the ledger back at a state it does  *)
  (* not name.  That is why /init has never been able to say its console is  *)
  (* on fds 1 and 2.  This is the same three instructions through the        *)
  (* TRACKED leaf: the caller hands in a claim on the SOURCE -- which for a  *)
  (* standard stream is the ledger's own row ([UInitFd.ufd_dup_src]) -- and  *)
  (* gets [UserFd.ualloc] back, so the DESTINATION is decided by its own     *)
  (* ledger.                                                                 *)
  (*                                                                        *)
  (* The source claim is NOT handed back: both arms of [UserFd.ufd_own] at a *)
  (* standard stream are PURE, so it is re-derivable from the ledger the     *)
  (* call returns and carrying it would only make the two call sites split   *)
  (* a resource they can rebuild.                                            *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kinit_dup_cons (h : CpuId) (m : regfile) (avail : nat)
      (l : list fdstate) (fd0 : nat) (st : fdstate) :
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd0 ->
    st <> FdClosed ->
    (fd0 < NSTD)%nat ->
    l !! fd0 = Some st ->
    init_code γt -∗
    urun N h m (mword_of_int InitSyms.dup) avail -∗
    ustd γfd l -∗
    (∀ (h' : CpuId) (ret : mword 64),
       ((∃ fd1 : nat,
           ⌜ret = (mword_of_int (Z.of_nat fd1) : mword 64)
            /\ (fd1 < NOFILE)%nat⌝ ∗ ualloc γfd l fd1 st)
        (* ...OR IT FAILED, AND THE LEDGER SAYS WHY: the source is OPEN
           ([Hne]), so the only reason left in [UsysMemOk]'s dup row is a
           FULL TABLE -- which the ledger reports as `no closed slot'.  A
           caller whose ledger has one refutes this arm by computation;
           /init's does, right after its console open. *)
        ∨ (⌜ret = (mword_of_int (-1) : mword 64)
            /\ fd_lowest_closed l = None⌝ ∗ ustd γfd l)) -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof.
    intros Harg Hne Hlt Hrow.
    iIntros "#Hcode Hrun Hstd Hcont".
    destruct init_syms_pins as (Hstart & Hmain & Hprintf & Hvprintf & Hputc & Hopen & Hmknod & Hdup & Hfork & Hwait & Hexec & Hwrite & Hexit). rewrite Hdup.
    (* ---- 0x3ea  c.li a7,10 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x3ea)
              (mword_of_int 10 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_3ea with "Hcode"). }
    assert (E0 : add_vec_int (mword_of_int 0x3ea : mword 64) 2
                 = mword_of_int 0x3ec)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 10 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m).
    assert (Harg1 : bv_signed (trunc32 (m1 !!! Regidx a0_idx)) = Z.of_nat fd0).
    { unfold m1.
      rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
                 (mword_of_int 10 : mword 64) ltac:(vm_compute; discriminate)).
      exact Harg. }
    (* ---- 0x3ec  ecall -- the TRACKED dup leaf ---- *)
    iApply (wp_uk_ecall_dup N h1 m1 (mword_of_int 0x3ec) l fd0 st avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 10 : mword 64));
                    vm_compute; reflexivity)
              Harg1 Hne
              ltac:(vm_compute; reflexivity)
              with "[] Hrun [] Hstd []").
    { iApply (uis_init_3ec with "Hcode"). }
    { iApply udepw_of_psok; [ apply Hpsok_free; free_lit | ];
      (discriminate || assumption || (vm_compute; discriminate)). }
    { iApply (ufd_dup_src γfd l fd0 st); [ exact Hlt | exact Hrow ]. }
    assert (E1 : add_vec_int (mword_of_int 0x3ec : mword 64) 4
                 = mword_of_int 0x3f0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2 ret) "Hal Hrun".
    iAssert (((∃ fd1 : nat,
                 ⌜ret = (mword_of_int (Z.of_nat fd1) : mword 64)
                  /\ (fd1 < NOFILE)%nat⌝ ∗ ualloc γfd l fd1 st)
              ∨ (⌜ret = (mword_of_int (-1) : mword 64)
                  /\ fd_lowest_closed l = None⌝ ∗ ustd γfd l)))%I
      with "[Hal]" as "Hans".
    { iDestruct "Hal" as "[Hs | Hf]".
      - iDestruct "Hs" as (fd1) "(%Hr & Ha & _)".
        iLeft. iExists fd1. iFrame "Ha". by iPureIntro.
      - iDestruct "Hf" as "(%Hr & Hl & _)".
        iRight. iFrame "Hl". by iPureIntro. }
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0x3f0  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 10 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0x3f0) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_3f0 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hans Hrun").
  Qed.

  (* ...AT A NAMED TABLE VIEW (seccomp S4) *)
  Lemma wp_kinit_dup_cons_at (h : CpuId) (m : regfile) (avail : nat)
      (l v : list fdstate) (fd0 : nat) (st : fdstate) :
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd0 ->
    st <> FdClosed ->
    (fd0 < NSTD)%nat ->
    l !! fd0 = Some st ->
    init_code γt -∗
    urun N h m (mword_of_int InitSyms.dup) avail -∗
    ustd_at γfd l v -∗
    (∀ (h' : CpuId) (ret : mword 64),
       ((∃ fd1 : nat,
           ⌜ret = (mword_of_int (Z.of_nat fd1) : mword 64)
            /\ (fd1 < NOFILE)%nat⌝ ∗
           ∃ fdv : list fdstate, ⌜tab_le fdv v /\ fdv !! fd0 = Some st⌝
             ∗ ualloc_v γfd l fd1 st (<[fd1 := st]> fdv))
        (* ...OR IT FAILED, AND THE LEDGER SAYS WHY: the source is OPEN
           ([Hne]), so the only reason left in [UsysMemOk]'s dup row is a
           FULL TABLE -- which the ledger reports as `no closed slot'.  A
           caller whose ledger has one refutes this arm by computation;
           /init's does, right after its console open. *)
        ∨ (⌜ret = (mword_of_int (-1) : mword 64)
            /\ fd_lowest_closed l = None⌝ ∗ ustd_at γfd l v)) -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof.
    intros Harg Hne Hlt Hrow.
    iIntros "#Hcode Hrun Hstd Hcont".
    destruct init_syms_pins as (Hstart & Hmain & Hprintf & Hvprintf & Hputc & Hopen & Hmknod & Hdup & Hfork & Hwait & Hexec & Hwrite & Hexit). rewrite Hdup.
    (* ---- 0x3ea  c.li a7,10 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x3ea)
              (mword_of_int 10 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_3ea with "Hcode"). }
    assert (E0 : add_vec_int (mword_of_int 0x3ea : mword 64) 2
                 = mword_of_int 0x3ec)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 10 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m).
    assert (Harg1 : bv_signed (trunc32 (m1 !!! Regidx a0_idx)) = Z.of_nat fd0).
    { unfold m1.
      rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
                 (mword_of_int 10 : mword 64) ltac:(vm_compute; discriminate)).
      exact Harg. }
    (* ---- 0x3ec  ecall -- the TRACKED dup leaf ---- *)
    iApply (wp_uk_ecall_dup_at N h1 m1 (mword_of_int 0x3ec) l v fd0 st avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 10 : mword 64));
                    vm_compute; reflexivity)
              Harg1 Hne
              ltac:(vm_compute; reflexivity)
              with "[] Hrun [] Hstd []").
    { iApply (uis_init_3ec with "Hcode"). }
    { iApply udepw_of_psok; [ apply Hpsok_free; free_lit | ];
      (discriminate || assumption || (vm_compute; discriminate)). }
    { iApply (ufd_dup_src γfd l fd0 st); [ exact Hlt | exact Hrow ]. }
    assert (E1 : add_vec_int (mword_of_int 0x3ec : mword 64) 4
                 = mword_of_int 0x3f0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2 ret) "Hal Hrun".
    iAssert (((∃ fd1 : nat,
                 ⌜ret = (mword_of_int (Z.of_nat fd1) : mword 64)
                  /\ (fd1 < NOFILE)%nat⌝ ∗
                 ∃ fdv : list fdstate, ⌜tab_le fdv v /\ fdv !! fd0 = Some st⌝
                   ∗ ualloc_v γfd l fd1 st (<[fd1 := st]> fdv))
              ∨ (⌜ret = (mword_of_int (-1) : mword 64)
                  /\ fd_lowest_closed l = None⌝ ∗ ustd_at γfd l v)))%I
      with "[Hal]" as "Hans".
    { iDestruct "Hal" as "[Hs | Hf]".
      - iDestruct "Hs" as (fd1) "(%Hr & Ha & _)".
        iLeft. iExists fd1. iFrame "Ha". by iPureIntro.
      - iDestruct "Hf" as "(%Hr & Hl & _)".
        iRight. iFrame "Hl". by iPureIntro. }
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0x3f0  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 10 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0x3f0) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_3f0 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hans Hrun").
  Qed.

  (* --------------------------------------------------------------------- *)
  (* dup @0x3ea, ON A CLOSED STANDARD STREAM -- the arm where /init's        *)
  (* console never opened.  Its C runs the two dups WHATEVER the second open *)
  (* returned ([UInitCons.v]'s finding (a)), so this arm is walked, and what *)
  (* it has to establish is that the LEDGER DID NOT MOVE.                    *)
  (*                                                                        *)
  (* WHAT THE ROW GIVES: the LEDGER comes back at the very list it went in   *)
  (* at, AND the call is known to have returned -1 -- the dup row's success  *)
  (* arm now carries `the source was open', which a closed source refutes    *)
  (* ([UkRunSys.wp_uk_ecall_dup_closed]).  /init needs only the first half:  *)
  (* its C reads neither dup result.                                         *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kinit_dup_closed (h : CpuId) (m : regfile) (avail : nat)
      (l : list fdstate) (fd0 : nat) :
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd0 ->
    (fd0 < NSTD)%nat ->
    l !! fd0 = Some FdClosed ->
    init_code γt -∗
    urun N h m (mword_of_int InitSyms.dup) avail -∗
    ustd γfd l -∗
    (∀ (h' : CpuId) (ret : mword 64),
       ⌜ret = (mword_of_int (-1) : mword 64)⌝ -∗
       ustd γfd l -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof.
    intros Harg Hlt Hrow.
    iIntros "#Hcode Hrun Hstd Hcont".
    destruct init_syms_pins as (Hstart & Hmain & Hprintf & Hvprintf & Hputc & Hopen & Hmknod & Hdup & Hfork & Hwait & Hexec & Hwrite & Hexit). rewrite Hdup.
    (* ---- 0x3ea  c.li a7,10 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x3ea)
              (mword_of_int 10 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_3ea with "Hcode"). }
    assert (E0 : add_vec_int (mword_of_int 0x3ea : mword 64) 2
                 = mword_of_int 0x3ec)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 10 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m).
    assert (Harg1 : bv_signed (trunc32 (m1 !!! Regidx a0_idx)) = Z.of_nat fd0).
    { unfold m1.
      rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
                 (mword_of_int 10 : mword 64) ltac:(vm_compute; discriminate)).
      exact Harg. }
    assert (Hno : usysno m1 = USYS_dup).
    { unfold m1, usysno.
      rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 10 : mword 64)).
      vm_compute; reflexivity. }
    (* ---- 0x3ec  ecall -- the CLOSED-source dup leaf ---- *)
    iApply (wp_uk_ecall_dup_closed N h1 m1 (mword_of_int 0x3ec) l fd0 avail
              Hno Harg1 Hlt Hrow
              ltac:(vm_compute; reflexivity)
              with "[] Hrun [] Hstd").
    { iApply (uis_init_3ec with "Hcode"). }
    { iApply udepw_of_psok; [ apply Hpsok_free; free_lit | ];
      (discriminate || assumption || (vm_compute; discriminate)). }
    assert (E1 : add_vec_int (mword_of_int 0x3ec : mword 64) 4
                 = mword_of_int 0x3f0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2 ret) "%Hret Hstd Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0x3f0  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 10 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0x3f0) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_3f0 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "[] Hstd Hrun"); by iPureIntro.
  Qed.

  (* ...AT A NAMED TABLE VIEW (seccomp S4) *)
  Lemma wp_kinit_dup_closed_at (h : CpuId) (m : regfile) (avail : nat)
      (l v : list fdstate) (fd0 : nat) :
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd0 ->
    (fd0 < NSTD)%nat ->
    l !! fd0 = Some FdClosed ->
    init_code γt -∗
    urun N h m (mword_of_int InitSyms.dup) avail -∗
    ustd_at γfd l v -∗
    (∀ (h' : CpuId) (ret : mword 64),
       ⌜ret = (mword_of_int (-1) : mword 64)⌝ -∗
       ustd_at γfd l v -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof.
    intros Harg Hlt Hrow.
    iIntros "#Hcode Hrun Hstd Hcont".
    destruct init_syms_pins as (Hstart & Hmain & Hprintf & Hvprintf & Hputc & Hopen & Hmknod & Hdup & Hfork & Hwait & Hexec & Hwrite & Hexit). rewrite Hdup.
    (* ---- 0x3ea  c.li a7,10 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x3ea)
              (mword_of_int 10 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_3ea with "Hcode"). }
    assert (E0 : add_vec_int (mword_of_int 0x3ea : mword 64) 2
                 = mword_of_int 0x3ec)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 10 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m).
    assert (Harg1 : bv_signed (trunc32 (m1 !!! Regidx a0_idx)) = Z.of_nat fd0).
    { unfold m1.
      rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
                 (mword_of_int 10 : mword 64) ltac:(vm_compute; discriminate)).
      exact Harg. }
    assert (Hno : usysno m1 = USYS_dup).
    { unfold m1, usysno.
      rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 10 : mword 64)).
      vm_compute; reflexivity. }
    (* ---- 0x3ec  ecall -- the CLOSED-source dup leaf ---- *)
    iApply (wp_uk_ecall_dup_closed_at N h1 m1 (mword_of_int 0x3ec) l v fd0 avail
              Hno Harg1 Hlt Hrow
              ltac:(vm_compute; reflexivity)
              with "[] Hrun [] Hstd").
    { iApply (uis_init_3ec with "Hcode"). }
    { iApply udepw_of_psok; [ apply Hpsok_free; free_lit | ];
      (discriminate || assumption || (vm_compute; discriminate)). }
    assert (E1 : add_vec_int (mword_of_int 0x3ec : mword 64) 4
                 = mword_of_int 0x3f0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2 ret) "%Hret Hstd Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0x3f0  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 10 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0x3f0) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_3f0 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "[] Hstd Hrun"); by iPureIntro.
  Qed.

  (* --------------------------------------------------------------------- *)
  (* THE SECOND OPEN, AT WHICHEVER OF THE MKNOD'S THREE ANSWERS CAME BACK.   *)
  (* Three constructors for one shape, so the repair arm walks 0x74..0x82    *)
  (* once instead of three times.                                            *)
  (* --------------------------------------------------------------------- *)

  (* the node exists: the PINNED open at the resolving pin *)
  (* THE TAINT ARM IS THE SAME ON ALL THREE, so it is proved once: there is
     no pin to run on, the generic stub walks the call, and the head's
     third arm is what comes out. *)
  (* ...AND THE TAINT'S OWN DEPOSIT RIDES WITH IT (lane SUPPLY-SPLIT, P4).
     The generic stub walks the call, and 15 is a CLAIM number, so what the
     arm needs is open's deposit -- but only UNDER the taint, which is
     exactly the shape the era can pay: the taint entails the application's
     supply ([AppEcho.echo_sup_of_taint]) and the supply pays any number's
     bundle ([UexecExecInst.xv6_sbundle_of_supply_ne]).  This tier may not
     name an application, so what crosses is the deposit as a LAW OFF [T]. *)
  Lemma uki_open2_taint_arm (T : iProp Σ) `{!Persistent T} (stc : fdstate) :
    □ (T -∗ udepw_law 15) -∗ T -∗ uki_open2 T stc.
  Proof using .
    rewrite /uki_open2 /uki_open2_in.
    iIntros "#Hwl #Ht" (h m avail) "#Hcode #Hro %Hargs Hrun Hcwd Hin Hcont".
    iDestruct ("Hwl" with "Ht") as "#Hwr".
    iApply (wp_kinit_open h m avail with "Hwr Hcode Hrun [Hin]").
    { iDestruct "Hin" as "[H | [H _]]"; [ iExists ufd_l0; iApply (ustd_ok_ustd with "H") | iExact "H" ]. }
    iIntros (h' ret) "Hstd Hrun".
    iApply ("Hcont" $! h' ret with "[Hstd] Hcwd Hrun").
    iDestruct "Hstd" as (l) "H". iApply (ufd_head1_taint with "Ht H").
  Qed.

  (* the node exists: the PINNED open at the resolving pin.  Its taint arm
     is the lemma above, because under the taint there is no pin. *)
  Lemma uki_open2_of_console (T : iProp Σ) `{!Persistent T} (stc : fdstate) :
    □ (T -∗ udepw_law 15) -∗ uki_open_console_leaf T stc -∗ uki_open2 T stc.
  Proof using .
    iIntros "#Hwl Hlf".
    rewrite /uki_open2 /uki_open2_in.
    iIntros (h m avail) "#Hcode #Hro %Hargs Hrun Hcwd Hin Hcont".
    iDestruct "Hin" as "[Hstd | [Hstd #Ht]]"; last first.
    { iDestruct (uki_open2_taint_arm T stc with "Hwl Ht") as "Hop".
      rewrite /uki_open2 /uki_open2_in.
      iApply ("Hop" $! h m avail with "Hcode Hro [%] Hrun Hcwd [Hstd] Hcont");
        [ exact Hargs | ].
      iRight. iFrame "Hstd Ht". }
    iApply ("Hlf" $! h m avail with "Hcode Hro [%] Hrun Hcwd Hstd");
      [ exact Hargs | ].
    iIntros (h' ret) "Hans Hcwd Hrun".
    iApply ("Hcont" $! h' ret with "[Hans] Hcwd Hrun").
    iDestruct "Hans" as "[[_ H] | [[_ H] | [H Ht]]]".
    - iApply (ufd_head1_l1 with "H").
    - iApply (ufd_head1_closed with "H").
    - iDestruct "H" as (l) "H". iApply (ufd_head1_taint with "Ht H").
  Qed.

  (* the mknod failed and handed the credential back: the MISS pin again,
     and fd 0 stays closed *)
  Lemma uki_open2_of_absent (T K : iProp Σ) `{!Persistent T} (stc : fdstate) :
    □ (T -∗ udepw_law 15) -∗ uki_open_absent_leaf T K -∗ K -∗ uki_open2 T stc.
  Proof using .
    iIntros "#Hwl Hlf HK".
    rewrite /uki_open2 /uki_open2_in.
    iIntros (h m avail) "#Hcode #Hro %Hargs Hrun Hcwd Hin Hcont".
    iDestruct "Hin" as "[Hstd | [Hstd #Ht]]"; last first.
    { iDestruct (uki_open2_taint_arm T stc with "Hwl Ht") as "Hop".
      rewrite /uki_open2 /uki_open2_in.
      iApply ("Hop" $! h m avail with "Hcode Hro [%] Hrun Hcwd [Hstd] Hcont");
        [ exact Hargs | ].
      iRight. iFrame "Hstd Ht". }
    iApply ("Hlf" $! h m ufd_l0 avail with "Hcode Hro [%] Hrun Hcwd Hstd HK");
      [ exact Hargs | ].
    iIntros (h' ret) "Hans Hcwd Hrun".
    iApply ("Hcont" $! h' ret with "[Hans] Hcwd Hrun").
    iDestruct "Hans" as "[(_ & H & _) | [H Ht]]".
    - iApply (ufd_head1_closed with "H").
    - iDestruct "H" as (l) "H". iApply (ufd_head1_taint with "Ht H").
  Qed.

  (* --------------------------------------------------------------------- *)
  (* dup(0), ON THE HEAD AT A NAMED LEDGER -- ONE lemma for both of /init's  *)
  (* dups and all three arms, and the step that PINS fds 1 and 2 (lane       *)
  (* IO-LEAF, M1(f)).                                                        *)
  (*                                                                        *)
  (* The caller names the ledger the console arm is at and the slot its own  *)
  (* scan reaches, and the head comes back at [<[k := st]> l].  THE FAILURE  *)
  (* ARM DIES HERE: since lane DUP-ROW [wp_kinit_dup_cons]'s -1 arm carries  *)
  (* `fd_lowest_closed l = None', which [Hk] refutes -- so on the console    *)
  (* arm the dup PROVABLY lands, and it lands where the ledger says.  On the *)
  (* closed arm both dups fail on a closed descriptor and the ledger does    *)
  (* not move; on the taint arm the untracked leaf moves the authority and   *)
  (* names nothing.                                                          *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kinit_dup_headL (T : iProp Σ) (stc : fdstate) (l : list fdstate)
      (k : nat) (h : CpuId) (m : regfile) (avail : nat) :
    stc <> FdClosed ->
    l !! 0%nat = Some stc ->
    fd_lowest_closed l = Some k ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat 0 ->
    init_code γt -∗
    urun N h m (mword_of_int InitSyms.dup) avail -∗
    ufd_headL T γfd l -∗
    (∀ (h' : CpuId) (ret : mword 64),
       ufd_headL T γfd (<[k := stc]> l) -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof.
    intros Hne Hrow Hk Harg.
    iIntros "#Hcode Hrun Hhd Hcont".
    rewrite /ufd_headL.
    iDestruct "Hhd" as "[Hstd | [H | [H Ht]]]".
    - (* CONSOLE: the TRACKED leaf, and the ledger decides where it lands *)
      iDestruct "Hstd" as (vw) "[Hok Hstd]".
      iApply (wp_kinit_dup_cons_at h m avail l vw 0%nat stc Harg Hne
                ltac:(unfold NSTD; lia) Hrow with "Hcode Hrun Hstd").
      iIntros (h' ret) "Hal Hrun".
      iApply ("Hcont" $! h' ret with "[Hal Hok] Hrun").
      iDestruct "Hal" as "[Hs | [%Hf Hl]]"; last first.
      { (* the table cannot be full: the caller's own scan found slot [k] *)
        exfalso. destruct Hf as [_ Hf]. rewrite Hk in Hf. discriminate. }
      iDestruct "Hs" as (fd1) "[_ Ha]". iDestruct "Ha" as (fdv) "[%Hfv Ha]".
      destruct Hfv as [Htab Hsrc].
      rewrite /ualloc_v. iDestruct "Ha" as "[Hl _]".
      rewrite /ustd_after Hk. iLeft. rewrite /ustd_ok. iExists _. iFrame "Hl".
      iDestruct "Hok" as "[%Hok | HT]"; [| by iRight].
      iLeft. iPureIntro. exact (ush_view_ok_dup fdv vw fd1 0%nat stc Hok Htab Hsrc).
    - (* CLOSED: the source is a closed standard stream *)
      iDestruct "H" as (vw) "[Hok H]".
      iApply (wp_kinit_dup_closed_at h m avail ufd_l0 vw 0%nat Harg
                ltac:(unfold NSTD; lia) ufd_l0_row0 with "Hcode Hrun H").
      iIntros (h' ret) "_ Hstd Hrun".
      iApply ("Hcont" $! h' ret with "[Hstd Hok] Hrun").
      iRight. iLeft. rewrite /ustd_ok. iExists vw. iFrame "Hok Hstd".
    - (* TAINT: nothing is named, so the untracked leaf is the honest one *)
      iApply (wp_kinit_dup h m avail with "Hcode Hrun H").
      iIntros (h' ret) "Hstd Hrun".
      iApply ("Hcont" $! h' ret with "[Ht Hstd] Hrun").
      iDestruct "Hstd" as (l') "Hstd".
      iRight. iRight. iSplitL "Hstd"; [ by iExists l' | iExact "Ht" ].
  Qed.

  (* ...and write's.  16's branch is the write chain at a key whose
     descriptor row may be an inode and the minting law is key-free, so no
     supplier admits it; /init's banner and diagnostics all come through
     here, and E5's output lane is what discharges the premise. *)
  Lemma wp_kinit_write (h : CpuId) (m : regfile) (avail : nat) :
    udepw_law 16 -∗
    init_code γt -∗
    urun N h m (mword_of_int InitSyms.write) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    iIntros "#Hwr #Hcode Hrun Hcont".
    destruct init_syms_pins as (Hstart & Hmain & Hprintf & Hvprintf & Hputc & Hopen & Hmknod & Hdup & Hfork & Hwait & Hexec & Hwrite & Hexit). rewrite Hwrite.
    (* ---- 0x392  c.li a7,16 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x392)
              (mword_of_int 16 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_392 with "Hcode"). }
    assert (E0 : add_vec_int (mword_of_int 0x392 : mword 64) 2
                 = mword_of_int 0x394)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 16 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m).
    (* ---- 0x394  ecall -- the QUIET row ---- *)
    iApply (wp_uk_ecall_quiet N h1 m1 (mword_of_int 0x394) 16 avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 16 : mword 64));
                    vm_compute; reflexivity)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate)
              (* ...and the three descriptor-moving numbers, and chdir *)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate)
              (* ...and a number the full mask passes, not seccomp's *)
              ltac:(lia) ltac:(discriminate)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun []").
    { iApply (uis_init_394 with "Hcode"). }
    (* THE FLAGGED DEPOSIT: write(16), E5's to discharge *)
    { iApply (udepw_of_law N m1 (mword_of_int 0x394) 16 with "Hwr"). }
    assert (E1 : add_vec_int (mword_of_int 0x394 : mword 64) 4
                 = mword_of_int 0x398)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2 ret) "Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0x398  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 16 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0x398) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_398 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hrun").
  Qed.
  (* ===================================================================== *)
  (*  THE PRINTF CONE'S PER-BYTE WRITE OBLIGATION (lane IO-LEAF).           *)
  (*                                                                       *)
  (*  ulib's [putc] is one [write(fd, &c, 1)], and the whole cone above it  *)
  (*  -- vprintf's loop, printf -- is that call repeated.  A caller that    *)
  (*  wants to SAY something about the bytes carries [Ci] into each one and *)
  (*  takes [Co] out, and supplies THIS instead of the flagged deposit.     *)
  (*                                                                       *)
  (*  IT NAMES NOTHING BUT THE PROGRAM TIER'S OWN VOCABULARY -- the byte    *)
  (*  putc spilled into its frame, the run, [Ci], [Co] -- and that is       *)
  (*  forced: this cone sits BELOW the file system and cannot name row      *)
  (*  16's reading at all ([UkWriteLeaf]'s header).  The CONCRETE discharge *)
  (*  -- the console chain, the era's write link, the short arm's           *)
  (*  refutation ([UkWriteLeaf.uwrite_no_short]) -- is stated above         *)
  (*  [UkWriteLeaf] and reaches the walk as a premise, exactly the way      *)
  (*  sh's read leaf reaches [UkSh] from [UShLine].                         *)
  (*                                                                       *)
  (*  THE BYTE IS PUTC'S OWN and comes straight back: 16 writes no user     *)
  (*  byte, and the frame word putc borrowed has to be whole again before   *)
  (*  it gives the stack back.                                             *)
  (* ===================================================================== *)
  (* the byte a caller puts in a1 IS the byte putc spills, read at the
     width the store leaves it ([RiscvModelBytes.nth_byte] at 0) *)
  Lemma nth_byte0_moi (b : bv 8) :
    nth_byte (mword_of_int (bv_unsigned b) : mword 64) 0%nat = b.
  Proof using .
    rewrite <- zext8_moi. apply bv_eq.
    rewrite /nth_byte bv_extract_unsigned zext8_unsigned.
    change (8 * N.of_nat 0)%N with 0%N.
    rewrite Z.shiftr_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
  Qed.

  Definition kinit_w1 (fdv : mword 64) (b : bv 8) (Ci Co : iProp Σ) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (avail : nat),
       (* the descriptor and the count are the caller's to fix: which arm
          of [SpecFilewrite.filewrite_in] row 16 asks for is decided by
          argument 0's ledger row, and putc's call is one byte wide *)
       ⌜m !!! Regidx a0_idx = fdv⌝ -∗
       ⌜m !!! Regidx a2_idx = (mword_of_int 1 : mword 64)⌝ -∗
       init_code γt -∗
       ubyte γd (uint (m !!! Regidx a1_idx)) b -∗
       Ci -∗
       urun N h m (mword_of_int InitSyms.write) avail -∗
       (∀ (h' : CpuId) (ret : mword 64),
          ubyte γd (uint (m !!! Regidx a1_idx)) b -∗
          Co -∗
          urun N h'
            (<[Regidx a0_idx := ret]>
               (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m))
            (ret_pc (m !!! Regidx ra_idx)) avail -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* ...AND THE TRIVIAL ONE: the flagged deposit pays row 16 and the post
     is thrown away, which is what every caller of the cone did before
     lane IO-LEAF and what init's three DIE arms still do. *)
  Lemma kinit_w1_of_law (fdv : mword 64) (b : bv 8) :
    udepw_law 16 -∗ kinit_w1 fdv b emp emp.
  Proof using .
    iIntros "#Hwr" (h m avail) "_ _ #Hcode Hbuf _ Hrun Hcont".
    iApply (wp_kinit_write h m avail with "Hwr Hcode Hrun").
    iIntros (h' ret) "Hrun".
    iApply ("Hcont" $! h' ret with "Hbuf [] Hrun"). done.
  Qed.

  (* ...and it FRAMES: whatever else a caller wants to carry across the
     call rides beside [Ci]/[Co] untouched, which is how the ledger the
     console arm reads its row from travels with the cursor. *)
  Lemma kinit_w1_frame (fdv : mword 64) (b : bv 8) (Ci Co R : iProp Σ) :
    kinit_w1 fdv b Ci Co -∗ kinit_w1 fdv b (Ci ∗ R) (Co ∗ R).
  Proof using .
    iIntros "Hw" (h m avail) "%Ha0 %Ha2 #Hcode Hbuf [HCi HR] Hrun Hcont".
    iApply ("Hw" $! h m avail with "[%] [%] Hcode Hbuf HCi Hrun");
      [ exact Ha0 | exact Ha2 | ].
    iIntros (h' ret) "Hbuf HCo Hrun".
    iApply ("Hcont" $! h' ret with "Hbuf [$HCo $HR] Hrun").
  Qed.

  (* ...AND WHAT THE BOOT HANDS <init> SO THAT ONE STRING MAY BE JUSTIFIED
     (lane IO-LEAF): give it the descriptor table and it gives back a
     per-byte family for the [len] bytes [f], the family's start token, and
     the table.  LINEAR -- it carries the era's credential, which is spent
     once.

     AT ONE LEDGER, AND NOT UNDER A [∀ l] (lane IO-LEAF, M1(f)).  It used
     to be quantified over every list, because which row fd 1 was at was
     not decided by /init's code and the application's side had to answer
     for every row it could be -- which is what made the free write law
     ([UkRun.udepw_law] 16) a premise of the payment's proof.  It is
     decided now: the console arm of /init's head is the NAMED ledger
     [UInitFd.ufd_l3 stc], where the open landed at 0 and the two dups at
     1 and 2, so the payment is asked for at THAT list and its fd 1 is the
     console.  The other two arms of the head never ask for it -- they
     print through the flagged deposit ([UkInitMain.wp_kinit_banner]). *)
  (* ...AND WHAT COMES BACK WITH THE TABLE (lane IO-LEAF, M4a(2)): the
     family's LAST token, as whatever the supplier says it is worth.  M1
     dropped it here -- the third component was the table alone -- and the
     credential died with the banner; [Rt] is the parameter that lets the
     supplier hand it on, and /init lends it to the shell it forks.  An
     OPAQUE [iProp], for [kinit_w1]'s reason: this tier cannot name the
     application's claim, and a parameter is all it needs. *)
  Definition kinit_banner_pay (stc : fdstate) (len : nat) (f : nat -> bv 8)
      (Rt : iProp Σ) : iProp Σ :=
    (* ...AT ANY NAMED TABLE VIEW (seccomp S4): a print moves no descriptor,
       so the ledger comes back at the view it went in at *)
    (∀ v : list fdstate, UserFd.ustd_at γfd (ufd_l3 stc) v -∗
     ∃ Ch : nat -> iProp Σ,
       □ (∀ j : nat, ⌜(j < len)%nat⌝ -∗
            kinit_w1 (mword_of_int 1 : mword 64) (f j) (Ch j) (Ch (S j)))
       ∗ Ch 0%nat ∗ (Ch len -∗ UserFd.ustd_at γfd (ufd_l3 stc) v ∗ Rt))%I.

  (* ...AND THE SAME STUB WITH THE OUTPUT CHAIN AND THE POST                *)
  (* (app-echo.md, lane IO-LEAF, first half; the leaf is                    *)
  (* [UkRunSys.wp_uk_ecall_write_chain]).                                   *)
  (*                                                                       *)
  (* [wp_kinit_write] above pays row 16 from the FLAGGED DEPOSIT            *)
  (* ([UkRun.udepw_law] 16) and throws the post away.  This is the same     *)
  (* three instructions with the deposit taken at /init's OWN cursor family *)
  (* and the post handed back, so that the banner and the two diagnostics   *)
  (* can justify their own bytes and read their [wf_Q] at the count that    *)
  (* was pushed.  Both stubs stand: the quiet one keeps working from the    *)
  (* licence, and IO-LEAF's second half swaps the call only where /init has *)
  (* a claim to make.                                                       *)
  (* ...AND IT CARRIES THE CALLER'S SOURCE RUN (lane IO-LEAF), which is
     what makes the post's SHORT arm refutable: see
     [UkRunSys.wp_uk_ecall_write_chain_buf].  The run and the two rows go
     straight through. *)
  Lemma wp_kinit_write_chain (h : CpuId) (m : regfile) (avail : nat)
      (fdep : sfam) (l : list fdstate)
      (dq : dfrac) (nb : nat) (fb : nat -> bv 8) :
    init_code γt -∗
    urun N h m (mword_of_int InitSyms.write) avail -∗
    udepwf_std N (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
      (add_vec_int (mword_of_int InitSyms.write : mword 64) 2) 16 fdep l -∗
    UserFd.ustd γfd l -∗
    ubytesq γd dq (uint (m !!! Regidx a1_idx)) nb fb -∗
    (∀ (h' : CpuId) (ret : mword 64) (W : uvis) (cw' : Z) (cs' : gset gname),
       ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx a0_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx a1_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 2) = m !!! Regidx a2_idx⌝ -∗
       ⌜take NSTD (uvis_fd W) = l⌝ -∗
       ⌜uvis_lazy W = false⌝ -∗
       ⌜ forall (P : uptd) (j : nat),
           ProcPtOwn.proc_pt_wf P ->
           perm_of (ud_um P) (uvis_sz W) = uvis_perm W ->
           lazy_free (ud_um P) (uvis_sz W) ->
           (j < nb)%nat ->
           UserPtTree.uva_rmapped P
             (uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))) ⌝ -∗
       UserFd.ustd γfd l -∗
       ubytesq γd dq (uint (m !!! Regidx a1_idx)) nb fb -∗
       spost_at uslot 16 fdep W ret (uvis_M W) (uvis_fd W) cw' cs' -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    iIntros "#Hcode Hrun Hsb Hstd Hbuf Hcont".
    destruct init_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwrite & _). rewrite Hwrite.
    (* ---- 0x392  c.li a7,16 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x392)
              (mword_of_int 16 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_392 with "Hcode"). }
    assert (E392 : add_vec_int (mword_of_int 0x392 : mword 64) 2
                   = mword_of_int 0x394)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 16 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E392 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m).
    (* ---- 0x394  ecall -- THE CHAIN-PAYING WRITE ---- *)
    (* the buffer address is the CALLER's a1: the stub writes a7 and then
       a0, and neither is a1 *)
    assert (Ha1m1 : m1 !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx)
                  (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)).
    rewrite <- Ha1m1.
    iApply (wp_uk_ecall_write_chain_buf N h1 m1 (mword_of_int 0x394) avail
              fdep l dq nb fb
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 16 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun Hsb Hstd Hbuf").
    { iApply (uis_init_394 with "Hcode"). }
    assert (E394 : add_vec_int (mword_of_int 0x394 : mword 64) 4
                   = mword_of_int 0x398)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E394.
    iIntros (h2 ret W cw' cs')
      "%Ha0 %Ha1 %Ha2 %Htk %Hlz %Hnf Hstd Hbuf Hpost Hrun".
    rewrite Ha1m1.
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0x398  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 16 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0x398) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_398 with "Hcode"). }
    iIntros (h3) "Hrun".
    (* the three argument words are the CALLER's: the stub writes a7 and
       then a0, and neither is a0/a1/a2 before the bump *)
    iApply ("Hcont" $! h3 ret W cw' cs'
              with "[%] [%] [%] [%] [%] [%] Hstd Hbuf Hpost Hrun").
    { rewrite Ha0 /m1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
               (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)). }
    { rewrite Ha1 /m1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx)
               (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)). }
    { rewrite Ha2 /m1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx)
               (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)). }
    { exact Htk. }
    { exact Hlz. }
    { rewrite <- Ha1m1. exact Hnf. }
  Qed.

  (* ...AT A NAMED TABLE VIEW (seccomp S4) *)
  Lemma wp_kinit_write_chain_at (h : CpuId) (m : regfile) (avail : nat)
      (fdep : sfam) (l v : list fdstate)
      (dq : dfrac) (nb : nat) (fb : nat -> bv 8) :
    init_code γt -∗
    urun N h m (mword_of_int InitSyms.write) avail -∗
    udepwf_std N (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
      (add_vec_int (mword_of_int InitSyms.write : mword 64) 2) 16 fdep l -∗
    UserFd.ustd_at γfd l v -∗
    ubytesq γd dq (uint (m !!! Regidx a1_idx)) nb fb -∗
    (∀ (h' : CpuId) (ret : mword 64) (W : uvis) (cw' : Z) (cs' : gset gname),
       ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx a0_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx a1_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 2) = m !!! Regidx a2_idx⌝ -∗
       ⌜take NSTD (uvis_fd W) = l⌝ -∗
       ⌜uvis_lazy W = false⌝ -∗
       ⌜ forall (P : uptd) (j : nat),
           ProcPtOwn.proc_pt_wf P ->
           perm_of (ud_um P) (uvis_sz W) = uvis_perm W ->
           lazy_free (ud_um P) (uvis_sz W) ->
           (j < nb)%nat ->
           UserPtTree.uva_rmapped P
             (uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))) ⌝ -∗
       UserFd.ustd_at γfd l v -∗
       ubytesq γd dq (uint (m !!! Regidx a1_idx)) nb fb -∗
       spost_at uslot 16 fdep W ret (uvis_M W) (uvis_fd W) cw' cs' -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    iIntros "#Hcode Hrun Hsb Hstd Hbuf Hcont".
    destruct init_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwrite & _). rewrite Hwrite.
    (* ---- 0x392  c.li a7,16 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x392)
              (mword_of_int 16 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_392 with "Hcode"). }
    assert (E392 : add_vec_int (mword_of_int 0x392 : mword 64) 2
                   = mword_of_int 0x394)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 16 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E392 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m).
    (* ---- 0x394  ecall -- THE CHAIN-PAYING WRITE ---- *)
    (* the buffer address is the CALLER's a1: the stub writes a7 and then
       a0, and neither is a1 *)
    assert (Ha1m1 : m1 !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx)
                  (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)).
    rewrite <- Ha1m1.
    iApply (wp_uk_ecall_write_chain_buf_at N h1 m1 (mword_of_int 0x394) avail
              fdep l v dq nb fb
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 16 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun Hsb Hstd Hbuf").
    { iApply (uis_init_394 with "Hcode"). }
    assert (E394 : add_vec_int (mword_of_int 0x394 : mword 64) 4
                   = mword_of_int 0x398)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E394.
    iIntros (h2 ret W cw' cs')
      "%Ha0 %Ha1 %Ha2 %Htk %Hlz %Hnf Hstd Hbuf Hpost Hrun".
    rewrite Ha1m1.
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0x398  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 16 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0x398) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_398 with "Hcode"). }
    iIntros (h3) "Hrun".
    (* the three argument words are the CALLER's: the stub writes a7 and
       then a0, and neither is a0/a1/a2 before the bump *)
    iApply ("Hcont" $! h3 ret W cw' cs'
              with "[%] [%] [%] [%] [%] [%] Hstd Hbuf Hpost Hrun").
    { rewrite Ha0 /m1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
               (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)). }
    { rewrite Ha1 /m1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx)
               (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)). }
    { rewrite Ha2 /m1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx)
               (mword_of_int 16 : mword 64) ltac:(vm_compute; discriminate)). }
    { exact Htk. }
    { exact Hlz. }
    { rewrite <- Ha1m1. exact Hnf. }
  Qed.


  (* THE PAYLOAD IS TRIVIAL AT THIS LANE.  exit's leaf is a PAYMENT
     ([UkRunSys.wp_uk_ecall_exit]): the program owes what its record says
     its exit owes.  init's record is minted at [fun _ => True] -- userinit
     forks it from nobody -- so the premise is the equation and the payment
     is [I]. *)
  Lemma wp_kinit_exit (h : CpuId) (m : regfile) (avail : nat) :
    init_code γt -∗
    (* THE PAYMENT COMES OUT OF THE PROGRAM'S OWN HAND (lane KILL-PAY,
       K4(a)): [UkRun.urun]'s payload row is a WAND from the kill
       credential now, so exit's leaf takes the payload as a premise.
       /init's own record is trivial and pays [I]; the CHILD this file's
       [N] also serves -- the one that execs sh -- holds the console lease
       until its exec succeeds and pays that. *)
    ukn_pay N (-1) -∗
    urun N h m (mword_of_int InitSyms.exit) avail -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpay.
    iIntros "#Hcode Hpay Hrun".
    destruct init_syms_pins as (Hstart & Hmain & Hprintf & Hvprintf & Hputc & Hopen & Hmknod & Hdup & Hfork & Hwait & Hexec & Hwrite & Hexit). rewrite Hexit.
    iApply (wp_uk_cli N h m (mword_of_int 0x372)
              (mword_of_int 2 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_372 with "Hcode"). }
    assert (E0 : add_vec_int (mword_of_int 0x372 : mword 64) 2
                 = mword_of_int 0x374)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 2 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 2 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 2 : mword 64)]> m).
    iApply (wp_uk_ecall_exit N h1 m1 (mword_of_int 0x374) avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 2 : mword 64));
                    vm_compute; reflexivity)
              with "[] [Hpay] Hrun").
    { iApply (uis_init_374 with "Hcode"). }
    (* AT A CONSTANT PAYLOAD the one resource the program holds is exactly
       what the exit leaf owes ([UkRun.ukn_const]). *)
    { rewrite (ukn_const_eq (N := N) (uexitst m1) (-1)). iExact "Hpay". }
  Qed.

  (* ===================================================================== *)
  (* INIT'S OWN EXEC SUPPLY, in place of [UkRun.uxsup].                     *)
  (*                                                                       *)
  (* [uxsup] is the exec bundle at EVERY key -- what a program that answers *)
  (* for nothing runs on.  init answers for exactly one exec: the child     *)
  (* arm's [exec("sh", argv)], at a0 = 0x9b8 ("sh" in its rodata), a1 =     *)
  (* 0x1000 (its .data argument vector) and the working directory it was    *)
  (* born with and never moves ([FsImg.ROOTINO]).  So what init carries is  *)
  (* the [c]-indexed deposit at THOSE keys and no other, and the deposit    *)
  (* is LENT the heap and the fd authority ([UkRun.udepw_at]) because a     *)
  (* pinned bundle's own premises -- the path string in the image, the      *)
  (* descriptor list -- are facts about the very key it is stated at.       *)
  (*                                                                       *)
  (* THE TWO CATALOGS ARE PREMISES for the same reason: the supplier reads  *)
  (* "sh" out of [init_rodata] and the argument vector out of              *)
  (* [init_argv] through the lent [UserHeap.uheap], and the program is what *)
  (* holds them.  Both are persistent, so paying them costs nothing and     *)
  (* they survive the [iLob] the restart loop re-enters.                    *)
  (*                                                                       *)
  (* [N'] is quantified because the arm that execs runs in the FORK CHILD,  *)
  (* under fresh heap names; [m] and [pc] because the key the ecall traps   *)
  (* from is built by the walk that reaches it.                            *)
  (*                                                                       *)
  (* WHERE IT COMES FROM: [UInitSh.init_exec_sup_of_sh_slot] builds it out  *)
  (* of init's PINNED exec bundle for /sh, and [UkRun.udepw_at_of_uxsup]    *)
  (* out of the trivial supplier.                                          *)
  (* ===================================================================== *)
  (* ...AND THE LEDGER IS SPENT ON IT.  exec COPIES the descriptor table,
     so the exec'd program's entry constructor speaks about the CALLER's
     slots -- and nothing in [UkRun.urun]'s [ufd_auth] is the program's
     claim on them: only its own ledger is.  sh says nothing about which
     of its standard streams are open, so what has to travel is the bare
     ledger ([UserFd.ustd_any]) rather than any fact about it; it has to
     travel at all because a table does not move without the fragments of
     the low slots.  init hands it to the supply and does not get it back,
     which costs nothing: the only path past a returning exec is the
     diagnostic and exit(1). *)
  Definition init_exec_sup : iProp Σ :=
    (□ (∀ (N' : uk_names Σ) (m : regfile) (pc : mword 64),
          (* THE RECORD'S PAYLOAD, as a pure row: the exec bundle carries
             the depositing process's own [ChildTok.my_pay] at it
             ([UexecExecInst.exec_sbundle]), and the supplier is lent that
             fact at [UkRun.udepw_at]'s [ukn_pay N'].  A process that execs
             at this lane owes its parent nothing, and its record says so --
             the entry constructor's row, or [UkFork]'s child arm. *)
          ⌜ ukn_pay N' = (fun _ => True)%I ⌝ -∗
          ⌜ m !!! Regidx a0_idx = (mword_of_int 0x9b8 : mword 64) ⌝ -∗
          ⌜ m !!! Regidx a1_idx = (mword_of_int 0x1000 : mword 64) ⌝ -∗
          init_rodata (ukn_t N') -∗
          init_argv (ukn_d N') -∗
          ustd_any (ukn_fd N') -∗
          (* AT THE REFUNDING DEPOSIT (lane KILL-PAY, K4(a), ruling R-A):
             a failed exec hands the process back what it spent, which is
             the only thing left to pay its own [exit(1)] with. *)
          udepw_at_ref N' m pc FsImg.ROOTINO))%I.

  Global Instance init_exec_sup_persistent : Persistent init_exec_sup.
  Proof using . rewrite /init_exec_sup. apply _. Qed.

  (* the trivial supplier still pays it: a bundle at every key is a bundle
     at init's *)
  (* AT THE TRIVIAL PAYLOAD, which is the row [init_exec_sup] already
     carries: a process that execs at this lane owes its parent nothing, so
     the bundle the trivial supplier hands over is at exactly the payload
     the record names. *)
  Lemma init_exec_sup_of_uxsup : uxsup -∗ init_exec_sup.
  Proof using .
    iIntros "#Hx". iModIntro. iIntros (N' m pc) "%Hpeq _ _ _ _ _".
    pose proof (Hpeq : UkRun.ukn_triv N') as Hti.
    iApply (udepw_at_ref_of_uxsup with "Hx").
  Qed.

  (* =================================================================== *)
  (*  THE SAME SUPPLY, PLUS THE POSITION IT LENDS THE CHILD                *)
  (*                                                                       *)
  (*  init's child is the process that execs sh, and what init lends it at *)
  (*  the fork ([UkFork.wp_uk_ecall_fork]'s [Rc]) is the PROGRAM HALF of   *)
  (*  the console position pair ([UserConsole.upos]).  The child carries   *)
  (*  it to its one exec and spends it there: it is the linear half of     *)
  (*  [PinnedExec.pinned_exec_bundle]'s [Pay], and it is what sh holds in  *)
  (*  [UkSh.ush_pstate] afterwards.                                        *)
  (*                                                                       *)
  (*  NOTHING LINEAR IS INSIDE THE BOX: the supply is a WAND from the      *)
  (*  position, which is exactly why ONE box serves every round of init's  *)
  (*  restart loop -- the loop mints a FRESH pair per child and applies    *)
  (*  the box at it ([UserConsole.upos_alloc]).                            *)
  (*                                                                       *)
  (*  THE PAYLOAD IS STILL THE TRIVIAL ONE HERE, and the seam that used   *)
  (*  to block the other one is open: the generic slot exists at any       *)
  (*  CONSTANT payload now ([UexecRet.uexec_wp_uslot],                     *)
  (*  [UexecExecMint.uslot_mint_pay], and                                  *)
  (*  [UexecExecInst.xv6_sbundle_of_supply] at [kf_xpay f = fun _ => R]),  *)
  (*  so [PinnedExec.pex_slot]'s taint arm is payable at a non-trivial     *)
  (*  [Q].  What is left to move is this box and its suppliers: the        *)
  (*  equation above becomes [ukn_pay N' = Qsh γ] and the supplier         *)
  (*  [UkRun.uxsup_at (ukn_pay N')].  The position crosses at either       *)
  (*  payload, which is why it crossed first.                              *)
  (* =================================================================== *)
  (* =================================================================== *)
  (*  THE EXIT PAYLOAD'S FAMILY AND THE LEND'S CREDENTIAL (lane IO-LEAF,   *)
  (*  step 3).                                                            *)
  (*                                                                     *)
  (*  What sh's exit hands back per count is a PAIR: the lease's read      *)
  (*  pieces [Rdl n] (the console reader token's companions -- the era's   *)
  (*  own half of the delivered count) and the credential /init's NEXT     *)
  (*  round's banner is paid from, [Wb n] (“the banner is owed at          *)
  (*  boundary n”).  The banner turns [Wb n] into the shell's PROMPT       *)
  (*  credential [Wc n 0] ("the prompt is owed at n") on the console arm   *)
  (*  and leaves it alone on the closed one (nothing was written), and     *)
  (*  the lend hands the shell the pieces ON the lease and the credential  *)
  (*  BESIDE it, correlated with the descriptor row the shell inherits:    *)
  (*  the both-console row carries the prompt credential, the closed row   *)
  (*  the banner-owed one, and the taint neither.                          *)
  (*                                                                     *)
  (*  AFFINE, ONCE, BY NAME: [init_rd_cred] is [Wb n ∨ True] and the       *)
  (*  lend's third arm is [True] -- the fork arm's re-entry and the wait   *)
  (*  redemption (step 4, M3b core) are what supply a credential at every  *)
  (*  exit; until then the two arms say so here and nowhere else.          *)
  (* =================================================================== *)
  (* THE CREDENTIAL ARM IS THE WHOLE STORY NOW (lane EXEC-SEAM, (C)):
     every exit of the shell hands the banner-owed credential back -- the
     shut-fd-0 exit and the fork panic on [UkSh.ush_at_of_pm_wb], the
     tainted exits on the pair's own taint arm -- so the affine arm has no
     producer left and is gone. *)
  Definition init_rd_cred (Wb : nat -> iProp Σ) (n : nat) : iProp Σ :=
    Wb n.

  Definition init_rd (Rdl Wb : nat -> iProp Σ) (n : nat) : iProp Σ :=
    (Rdl n ∗ init_rd_cred Wb n)%I.

  Global Instance init_rd_timeless (Rdl Wb : nat -> iProp Σ)
      `{!forall i : nat, Timeless (Rdl i)} `{!forall i : nat, Timeless (Wb i)}
      (n : nat) :
    Timeless (init_rd Rdl Wb n).
  Proof using . rewrite /init_rd /init_rd_cred. apply _. Qed.

  (* the credential the lend carries, AT THE LEDGER the child inherits.
     ON THE CONSOLE ROW IT IS THE ROUND-OPEN SHAPE [Wp n] (lane M6b; top:
     [UInitDiag.kinit_pro]) and not the shell's prompt credential: the
     prompt credential is the disjunction the shell is lent ([wr_owed]'s
     two arms), and nothing /init holds separates them
     ([EchoLinksPro.wr_owed_ambiguous]) -- so what a FAILED fork refunds
     and what a FAILED exec refunds would be unpayable at that shape.  The
     round-open shape pays both diagnostics through the links
     ([UkInitMain.kinit_diag_law]) and converts to the prompt credential
     at the shell's entry ([UInitSh.init_exec_sup_of_sh_slot]'s [Wp n -∗
     Wc n 0]).
     THE THIRD ARM IS THE TAINT (lane EXEC-SEAM, (C)): with
     [init_rd_cred]'s affine arm gone, the only credential-less case left
     where the lend is built ([UkInitMain.wp_kinit_banner], the restart
     loop's mint) is the tainted token, and a tainted shell runs on the
     generic slot.  So the lend names [T] like every other resource of the
     walk. *)
  Definition init_lend_cred (T : iProp Σ) (st : fdstate)
      (Wp Wb : nat -> iProp Σ)
      (l : list fdstate) (n : nat) : iProp Σ :=
    ((⌜l = ufd_l3 st⌝ ∗ Wp n)
     ∨ (⌜l = ufd_l0⌝ ∗ Wb n)
     ∨ T)%I.

  (* =================================================================== *)
  (*  THE KILL ROW (lane TL-6; design/user-tree.md §9.4, ruling (b)).     *)
  (*                                                                     *)
  (*  WHAT /init ACTUALLY SPENDS A KILL ON, and it is one site: the       *)
  (*  child it forks is lent the console lease, and a KILLED child        *)
  (*  cannot hand the lease back, so the payload /init chooses for it     *)
  (*  ([UserConsole.ucons_pay])'s kill arm is the application's [T]       *)
  (*  ([UkInitMain.wp_kinit_fork]).  That is the whole spend.             *)
  (*                                                                     *)
  (*  IT USED TO BE A CLOSED ENTAILMENT, [⊢ app_taint -∗ T],      *)
  (*  which reads "a kill is free for the application" and is ECHO's      *)
  (*  fact and no one else's (echo's kill credential IS its taint, so     *)
  (*  the premise was an identity there).  At an application whose kill   *)
  (*  credential is the generic one ([App.app_iface_triv]) the premise    *)
  (*  reads [True -∗ T] and is FALSE for any [T] worth having -- the      *)
  (*  tree claim's taint is exactly such a [T]                            *)
  (*  ([AppTree.tree_bump_free_is_vacuous]).                              *)
  (*                                                                     *)
  (*  SO THE PRICE IS CUT AT THE CREDENTIAL THE ROUND ALREADY HOLDS.      *)
  (*  The kill arm is reached with the lend in hand -- it is what the     *)
  (*  parent is about to hand the child -- so the honest premise is: a    *)
  (*  kill costs the application NO MORE THAN the credential this round   *)
  (*  is already carrying -- give the lend, get it back and the kill      *)
  (*  row.  ECHO discharges it out of its identity and at every arm       *)
  (*  ([init_kill_law_of_taint] below, so echo's site moves by one        *)
  (*  token); an application whose taint is a RESOURCE discharges it by   *)
  (*  reading the taint off the round-open arm ([Wp], which its banner    *)
  (*  left) and, on the banner-owed arm ([Wb], the licence it has not     *)
  (*  spent yet), by SPENDING it -- which is why the law is an update     *)
  (*  and why its conclusion may come back on the lend's third arm.       *)
  (* =================================================================== *)
  Definition init_kill_law (T : iProp Σ) (st : fdstate)
      (Wp Wb : nat -> iProp Σ) : iProp Σ :=
    (□ (∀ (l : list fdstate) (n : nat),
          init_lend_cred T st Wp Wb l n ==∗
          init_lend_cred T st Wp Wb l n ∗ □ (app_taint -∗ T)))%I.

  Global Instance init_kill_law_persistent T st Wp Wb :
    Persistent (init_kill_law T st Wp Wb).
  Proof using . rewrite /init_kill_law. apply _. Qed.

  (* THE OLD PREMISE IMPLIES THE NEW ONE, at every ledger and every
     count: an application for which a kill is free pays the row without
     reading the lend at all.  This is echo's discharge. *)
  Lemma init_kill_law_of_taint (T : iProp Σ) (st : fdstate)
      (Wp Wb : nat -> iProp Σ) :
    (⊢ app_taint -∗ T) ->
    ⊢ init_kill_law T st Wp Wb.
  Proof using .
    intros Hkt. rewrite /init_kill_law.
    iIntros "!>" (l n) "Hl". iModIntro. iFrame "Hl".
    iModIntro. iIntros "#Hc". iApply Hkt. iExact "Hc".
  Qed.

  (* WHAT A FAILED exec REFUNDS (lane M6b): the lend as it went in --
     the child's ledger, the position, the lease and the credential at
     that ledger.  The exec supply below puts exactly this into the
     deposit and names it as the refund ([UkRunExecRef.udepw_at_refR]),
     so the child that comes back from a failed exec holds what pays
     "init: exec sh failed" and then its own exit
     ([UkInitMain.wp_kinit_main_die_de]). *)
  Definition init_lend_ref (cn : cons_names) (T : iProp Σ) (st : fdstate)
      (Cr : cons_cred Σ) (γfd' : gname)
      (l : list fdstate) (γ : gname) (n : nat) : iProp Σ :=
    (UserFd.ustd γfd' l ∗ upos γ n ∗ ucons_pay cn γ T (cc_rd Cr) (-1)
     ∗ init_lend_cred T st (cc_wp Cr) (cc_wbn Cr) l n)%I.

  (*  THE DESCRIPTOR ROW IS THE LEDGER AND ITS ARM, not the head as a
      disjunction: sh's entry is told one thing about its table -- fd 0 is
      the console, or slot 0 is closed, or the taint ([UkSh.ush_fd0]) --
      and that is /init's own head's three arms ([UInitFd.ufd_row]).  The
      ledger crosses here with its row beside it and is SPENT, which is
      right -- the process that execs is replaced -- and the credential
      crosses at the SAME ledger ([init_lend_cred]), which is what lets
      the shell's entry put it in the slot its own prompt reads. *)
  Definition init_exec_sup_pos (cn : cons_names) (T : iProp Σ) (st : fdstate)
      (Cr : cons_cred Σ)
      (γ : gname) (n : nat) : iProp Σ :=
    (∀ (N' : uk_names Σ) (m : regfile) (pc : mword 64) (l : list fdstate),
       ⌜ ukn_pay N' = ucons_pay cn γ T (init_rd (cc_rd Cr) (cc_wbn Cr)) ⌝ -∗
       (* ...AND THE EXEC'ING RECORD HOLDS NO OFFSET HALF (lane OFF-HAND-4,
          S2).  sh's entry is minted at [ukn_held = empty]
          ([UShKernel.sh_uexec_slot]) and [ExecEntry.image_entry_at] no
          longer relays the key's all-parked row, so the SUPPLIER has to
          say it about the table it execs with -- which it reads off its
          own run ([UkRun.urun_rows_parked]) exactly when this row holds.
          The spender is /init's exec leaf, whose record carries the class
          ([UkRun.ukn_parked]); the child that execs sh is minted at its
          parent's set ([UkFork.wp_uk_ecall_fork]). *)
       ⌜ m !!! Regidx a0_idx = (mword_of_int 0x9b8 : mword 64) ⌝ -∗
       ⌜ m !!! Regidx a1_idx = (mword_of_int 0x1000 : mword 64) ⌝ -∗
       init_rodata (ukn_t N') -∗
       init_argv (ukn_d N') -∗
       (* ...AT AN OK VIEW, or the taint (seccomp S4): what sh's entry is
          told about the table it is exec'd at *)
       UserFd.ustd_ok T (ukn_fd N') l -∗
       UInitFd.ufd_row T st l -∗
       init_lend_cred T st (cc_wp Cr) (cc_wbn Cr) l n -∗
       upos γ n -∗
       (* ...AND THE LEASE ITSELF (lane KILL-PAY, K4(a)), at the READ
          family: the console reader token used to ride in the child's own
          payload row and reach sh through [UexecRet]'s deposit; that row
          is a WAND from the kill credential now, so the token crosses
          [PinnedExec]'s [Pay] beside the position and lands in the
          shell's loop as its PIECES ([UkSh.ush_posb]). *)
       ucons_pay cn γ T (cc_rd Cr) (-1) -∗
       (* ...AND THE CHILD'S TWO IDENTITY FRAGMENTS (lane EXEC-SEAM): a
          fork child has no children yet and is not <init>
          ([UkFork.wp_uk_ecall_fork]'s child arm), and the shell's entry
          reads both facts off the key it is resumed at
          ([SpecKexec.exec_slot_pre]'s identity rows) -- so the fragments
          cross here and are spent against the record's authorities inside
          the deposit ([UkRunExecRef.udepw_at_refR_ids]). *)
       UserChildren.uch (ukn_ch N') ∅ -∗
       (∃ p : Z, ⌜p <> 1⌝ ∗ UserChildren.upid (ukn_pid N') p) -∗
       (* ...AND THE REFUND IS THE LEND ITSELF (lane M6b), ledger included:
          a failed exec hands the four back at the shapes they went in at,
          which is what the diagnostic and the exit after it are paid
          from.  [UkRun.udepw_at_ref] could only name the record's own
          exit payload, and the credential does not fit in that family. *)
       (* ...BEHIND AN UPDATE DOOR (lane TL-9; design/user-tree.md 9.8).
          THE NODE IS HANDED THE ROUND'S CREDENTIAL ([init_lend_cred]
          above) AND THE DEPOSIT IT BUILDS MAY SPEND IT.  The supply is a
          [box] ([init_exec_sup_lend] below), so a LINEAR credential can
          only be spent inside the node's own construction -- and with the
          conclusion update-free there was no place inside it where a
          ghost move could run, which is what made the supply unpayable at
          a credential the era holds once (lane TL-8's token count, 9.7(2)).
          The door is the same shape 9.4's ruling (b) already gave the kill
          row ([init_kill_law] is an update for exactly this reason): ECHO
          discharges it with one [iModIntro]
          ([UInitSh.init_exec_sup_of_sh_slot]), and an application whose
          credential is a RESOURCE discharges it by reading the taint off
          the round-open arm or MINTING it on the banner-owed one, where
          the licence is still unspent. *)
       |==> udepw_at_refR_ids N' m pc FsImg.ROOTINO
              (init_lend_ref cn T st Cr (ukn_fd N') l γ n))%I.

  Definition init_exec_sup_lend (cn : cons_names) (T : iProp Σ)
      (st : fdstate) (Cr : cons_cred Σ)
      : iProp Σ :=
    (□ (∀ (γ : gname) (n : nat), init_exec_sup_pos cn T st Cr γ n))%I.

  Global Instance init_exec_sup_lend_persistent cn T st Cr :
    Persistent (init_exec_sup_lend cn T st Cr).
  Proof using . rewrite /init_exec_sup_lend. apply _. Qed.

  (* ...AND THE SAME SUPPLY AS A WAND FROM THE CONSOLE CREDENTIAL (lane E2).
     The exec'd shell's entry is told which console state its parent left
     ([UkSh.ush_fd0] / SH-OPEN's [ush_cons_in]), and WHICH one that is is
     decided by /init's own mknod -- MID-WALK, not at the entry.  So what
     the entry carries is not the supply but a WAND from the credential to
     it, applied once the console dance has settled, plus the law that
     pays it under the taint (where the shell proves nothing anyway).
     Both halves are [□], so the restart loop applies them per round. *)
  Definition init_cons_sup (cn : cons_names) (T Cns : iProp Σ)
      (st : fdstate) (Cr : cons_cred Σ)
      : iProp Σ :=
    (□ (Cns -∗ init_exec_sup_lend cn T st Cr) ∗ □ (T -∗ Cns))%I.

  Global Instance init_cons_sup_persistent cn T Cns st Cr :
    Persistent (init_cons_sup cn T Cns st Cr).
  Proof using . rewrite /init_cons_sup. apply _. Qed.

  Lemma init_cons_sup_taint (cn : cons_names) (T Cns : iProp Σ)
      (st : fdstate) (Cr : cons_cred Σ) :
    init_cons_sup cn T Cns st Cr -∗ T -∗
    init_exec_sup_lend cn T st Cr.
  Proof using .
    iIntros "[#Hw #Ht] HT". iApply "Hw". iApply ("Ht" with "HT").
  Qed.

  (* ...AND THE LEAF IS CWD-INDEXED.  [UkRunSys.wp_uk_ecall_exec_at_cwd]
     takes the program's own half of its working directory beside the
     deposit and hands it back on the failure arm: a pinned bundle is about
     a PATH, and a relative path names a file only against the directory it
     is resolved from.  init's [c] is [FsImg.ROOTINO] at every call site,
     but the leaf is stated at a variable one -- nothing here depends on
     which inum it is. *)
  (* ...AND AT A SUPPLIER-NAMED REFUND (lane M6b): what a failed exec hands
     back is whatever the deposit's own wand says -- for /init's child the
     lend itself ([init_lend_ref]), not the record's exit payload. *)
  Lemma wp_kinit_exec (h : CpuId) (m : regfile) (avail : nat) (c : Z)
      (R : iProp Σ) :
    init_code γt -∗
    urun N h m (mword_of_int InitSyms.exec) avail -∗
    (* the program's half of its working directory *)
    UserCwd.ucwd γcwd c -∗
    (* THE EXEC DEPOSIT, on the EXPLICIT route: exec's bundle reads the key
       (argv, out of the image), so it is not payable from the supplier and
       [UkRun.udepw]'s left disjunct excludes it by construction.  The
       caller hands it in, at the key the ecall traps from and at the one
       working directory it answers for. *)
    udepw_at_refR_ids N
      (<[Regidx a7_idx := (mword_of_int 7 : mword 64)]> m)
      (mword_of_int 0x3ac) c R -∗
    (* exec only comes back when it FAILED, and then it returns -1 -- AND
       IT IS REFUNDED (lane KILL-PAY, K4(a), ruling R-A): what the process
       spent into the deposit comes back, at the shape the supplier named,
       which is what pays the diagnostic and the [exit(1)] it ends in. *)
    (∀ h' : CpuId,
       UserCwd.ucwd γcwd c -∗
       R -∗
       urun N h'
         (<[Regidx a0_idx := (mword_of_int (-1) : mword 64)]>
            (<[Regidx a7_idx := (mword_of_int 7 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    iIntros "#Hcode Hrun Hcwd Hsbx Hcont".
    destruct init_syms_pins as (Hstart & Hmain & Hprintf & Hvprintf & Hputc & Hopen & Hmknod & Hdup & Hfork & Hwait & Hexec & Hwrite & Hexit). rewrite Hexec.
    iApply (wp_uk_cli N h m (mword_of_int 0x3aa)
              (mword_of_int 7 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_3aa with "Hcode"). }
    assert (E0 : add_vec_int (mword_of_int 0x3aa : mword 64) 2
                 = mword_of_int 0x3ac)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 7 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 7 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 7 : mword 64)]> m).
    iApply (wp_uk_ecall_exec_at_cwd_refR_ids N h1 m1 (mword_of_int 0x3ac) avail c R
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 7 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun Hcwd Hsbx").
    { iApply (uis_init_3ac with "Hcode"). }
    assert (E1 : add_vec_int (mword_of_int 0x3ac : mword 64) 4
                 = mword_of_int 0x3b0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2) "Hcwd Hpayret Hrun".
    set (m2 := <[Regidx a0_idx := (mword_of_int (-1) : mword 64)]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) _
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 7 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0x3b0) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_3b0 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 with "Hcwd Hpayret Hrun").
  Qed.

  (* init calls [wait] with a NULL status pointer, which is the only arm
     this tier can carry: the kernel's own [addr != 0] test means nothing
     is copied out, so the heap comes back untouched. *)
  (* AT THE INDEXED HALF, because this is the call init REDEEMS THROUGH.
     init forks one shell and waits for it; what it gets back on the
     reaping arm is the kernel's answer ([UexecRet.uwait_ans]) naming the
     generation that left the set, with that child's escrow and the pid
     uniqueness over the set the call went in at.  A parent holding
     [ChildTok.child_tok] for the shell it forked turns [r = its pid] into
     [γ' = the shell's generation] ([ChildTok.gen_uniq_tok]) and the escrow
     into the payload its fork chose ([ChildTok.gen_pay]); a parentless
     process reaped in its stead answers at a DIFFERENT generation, which
     the same token refutes ([ChildTok.exit_tok_tok_ne]), so the shell is
     still in the set the call left and init loops.  None of that is
     sayable at [UserChildren.uch_any]. *)
  (* ...AND THE ROW A RESUMING CALLER READS OFF ITS OWN -1 (lane M6b,
     "DIE-DW CORRECTED").  A process that comes back from wait was not
     killed (usertrap's second [killed] check exits it before the sret --
     [SpecUsertrap.ut_live_out]), and at a null status pointer the copyout
     exit cannot fire, so the ONLY -1 a user program ever sees is "my own
     child set is empty" -- which is what [UkRunSys.wp_uk_ecall_wait_null_live]
     hands over as [⌜ret = -1 -> cs' = ∅⌝].  init holds a token for the
     shell it forked, so the arm is refuted at the wait head and init's
     "init: wait returned an error" diagnostic is dead code
     ([UkInitMain.wp_kinit_main_loop]). *)
  Lemma wp_kinit_wait (h : CpuId) (m : regfile) (avail : nat)
      (cs : gset gname) :
    uint (m !!! Regidx a0_idx) = 0 ->
    init_code γt -∗
    urun N h m (mword_of_int InitSyms.wait) avail -∗
    UserChildren.uch (ukn_ch N) cs -∗
    (∀ (h' : CpuId) (ret : mword 64) (cs' : gset gname),
       ⌜ret = (mword_of_int (-1) : mword 64) -> cs' = (∅ : gset gname)⌝ -∗
       uwait_ans ret cs cs' -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 3 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       UserChildren.uch (ukn_ch N) cs' -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpsok_free.
    intros Hz.
    iIntros "#Hcode Hrun Hch Hcont".
    destruct init_syms_pins as (Hstart & Hmain & Hprintf & Hvprintf & Hputc & Hopen & Hmknod & Hdup & Hfork & Hwait & Hexec & Hwrite & Hexit). rewrite Hwait.
    iApply (wp_uk_cli N h m (mword_of_int 0x37a)
              (mword_of_int 3 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_37a with "Hcode"). }
    assert (E0 : add_vec_int (mword_of_int 0x37a : mword 64) 2
                 = mword_of_int 0x37c)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 3 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 3 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 3 : mword 64)]> m).
    assert (Ha0 : uint (m1 !!! Regidx a0_idx) = 0).
    { unfold m1.
      rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
                 (mword_of_int 3 : mword 64) ltac:(vm_compute; discriminate)).
      exact Hz. }
    iApply (wp_uk_ecall_wait_null_live N h1 m1 (mword_of_int 0x37c) avail cs
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 3 : mword 64));
                    vm_compute; reflexivity)
              Ha0 ltac:(vm_compute; reflexivity)
              with "[] Hrun [] Hch").
    { iApply (uis_init_37c with "Hcode"). }
    { iApply udepw_of_psok; [ apply Hpsok_free; free_lit | ];
      (discriminate || assumption || (vm_compute; discriminate)). }
    assert (E1 : add_vec_int (mword_of_int 0x37c : mword 64) 4
                 = mword_of_int 0x380)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2 ret cs') "%Hm1 Hans Hrun Hch".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 3 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0x380) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_380 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret cs' with "[%] Hans Hrun Hch"). exact Hm1.
  Qed.

End UkInit.

(* ===================================================================== *)
(*  THE THREE DEPOSITS INIT OWES, record-generic (lane EXEC-SEAM, (D)).   *)
(*                                                                        *)
(*  write(16), open(15) and mknod(17) are CLAIM numbers, each paid under  *)
(*  the taint out of the application's supply; the write conjunct is a    *)
(*  PAIR in the old conjunct's position: the tainted law beside the        *)
(*  CLOSED-FD LEAF -- a write to a closed descriptor puts nothing on the   *)
(*  wire, and its deposit is free at every record                          *)
(*  ([UkWriteClosed.kinit_w1_of_closed_l0]).  That leaf is what init's     *)
(*  diagnostics and banner print on when the console never opened, and    *)
(*  it has to be stated at EVERY record because the exec'ing child's       *)
(*  diagnostics run at a record the fork minted.  No free law remains:     *)
(*  the console row pays through the era's links, the closed row through  *)
(*  this leaf, and the taint row through the law under the taint.          *)
(* ===================================================================== *)
Section InitDeps.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!ctokG Σ}.
  Context `{!uartGhostG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  Definition kinit_wcl : iProp Σ :=
    (□ (∀ (N0 : uk_names Σ) (b : bv 8) (v : list fdstate),
          kinit_w1 N0 (mword_of_int 1 : mword 64) b
            (UserFd.ustd_at (ukn_fd N0) ufd_l0 v) (UserFd.ustd_at (ukn_fd N0) ufd_l0 v)))%I.

  Global Instance kinit_wcl_persistent : Persistent kinit_wcl.
  Proof using . rewrite /kinit_wcl. apply _. Qed.

  Definition kinit_wlaw (T : iProp Σ) : iProp Σ :=
    (□ (T -∗ udepw_law 16) ∗ kinit_wcl)%I.

  Global Instance kinit_wlaw_persistent T : Persistent (kinit_wlaw T).
  Proof using . rewrite /kinit_wlaw. apply _. Qed.

  Definition init_deps (T : iProp Σ) : iProp Σ :=
    (kinit_wlaw T ∗ □ (T -∗ udepw_law 15) ∗ □ (T -∗ udepw_law 17))%I.

  Global Instance init_deps_persistent T : Persistent (init_deps T).
  Proof using . rewrite /init_deps. apply _. Qed.
End InitDeps.
