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
Require Import RegFile.
Require Import UkRun UkRunLeaf UkRunSys.
Require Import UCodeInit.
Require Import TsoCtx.
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
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
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
  (* the pin lives -- [UkSh.ush_read_leaf] / [UkSh.ush_read_leaf_holds] is   *)
  (* the mould, and the discharge walks the same three instructions each     *)
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
          0x970 read through the LOANED heap ([UInitConsK]'s supplier), so
          the era-level discharge needs the persistent view of those bytes
          and the two registers the stub is called with: a0 = "console",
          a1 = O_RDWR.  Both call sites hold them
          ([UkInitMain.wp_kinit_main] @0x0e-0x16,
          [wp_kinit_main_repair_tail] @0x74-0x7e). *)
       init_rodata γt -∗
       ⌜ m !!! Regidx a0_idx = (mword_of_int 0x970 : mword 64)
         /\ m !!! Regidx a1_idx = (mword_of_int 2 : mword 64) ⌝ -∗
       urun N h m (mword_of_int InitSyms.open) avail -∗
       UserCwd.ucwd γcwd FsImg.ROOTINO -∗
       ustd γfd ufd_l0 -∗
       (∀ (h' : CpuId) (ret : mword 64),
          ((⌜ret = (mword_of_int 0 : mword 64)⌝ ∗ ustd γfd (ufd_l1 stc))
           ∨ (⌜ret = (mword_of_int (-1) : mword 64)⌝ ∗ ustd γfd ufd_l0)
           ∨ (ustd_any γfd ∗ T)) -∗
          UserCwd.ucwd γcwd FsImg.ROOTINO -∗
          urun N h'
            (<[Regidx a0_idx := ret]>
               (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m))
            (ret_pc (m !!! Regidx ra_idx)) avail -∗
          WP (Loop : expr riscv_lang)) -∗
       WP (Loop : expr riscv_lang))%I.

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
       ⌜ m !!! Regidx a0_idx = (mword_of_int 0x970 : mword 64)
         /\ m !!! Regidx a1_idx = (mword_of_int 2 : mword 64) ⌝ -∗
       urun N h m (mword_of_int InitSyms.open) avail -∗
       UserCwd.ucwd γcwd FsImg.ROOTINO -∗
       ustd γfd l -∗
       K -∗
       (∀ (h' : CpuId) (ret : mword 64),
          ((⌜ret = (mword_of_int (-1) : mword 64)⌝ ∗ ustd γfd l ∗ K)
           ∨ (ustd_any γfd ∗ T)) -∗
          UserCwd.ucwd γcwd FsImg.ROOTINO -∗
          urun N h'
            (<[Regidx a0_idx := ret]>
               (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m))
            (ret_pc (m !!! Regidx ra_idx)) avail -∗
          WP (Loop : expr riscv_lang)) -∗
       WP (Loop : expr riscv_lang))%I.

  (* THE MKNOD, which is where the console node comes into existence and the
     one place /init's own WRITE pays a step of the application's claim
     rather than reading one out of its supply.  Three arms, and the first
     is what the whole lane is for: the node exists, so the SECOND open's
     leaf is available.  On failure the credential comes back -- and then
     the second open is the MISS leaf again, and fd 0 stays closed. *)
  Definition uki_mknod_leaf (T K : iProp Σ) (stc : fdstate) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (avail : nat),
       init_code γt -∗
       (* the read-only image and the THREE argument words: a0 = "console"
          at 0x970, a1 = CONSOLE, a2 = 0 -- the numbers row 17 reads
          through [SysMknodDefs.dev_arg].  The repair arm holds all four
          ([UkInitMain.wp_kinit_main_repair] @0x64-0x70). *)
       init_rodata γt -∗
       ⌜ m !!! Regidx a0_idx = (mword_of_int 0x970 : mword 64)
         /\ m !!! Regidx a1_idx = (mword_of_int 1 : mword 64)
         /\ m !!! Regidx a2_idx = (mword_of_int 0 : mword 64) ⌝ -∗
       urun N h m (mword_of_int InitSyms.mknod) avail -∗
       UserCwd.ucwd γcwd FsImg.ROOTINO -∗
       K -∗
       (∀ (h' : CpuId) (ret : mword 64),
          (uki_open_console_leaf T stc ∨ K ∨ T) -∗
          UserCwd.ucwd γcwd FsImg.ROOTINO -∗
          urun N h'
            (<[Regidx a0_idx := ret]>
               (<[Regidx a7_idx := (mword_of_int 17 : mword 64)]> m))
            (ret_pc (m !!! Regidx ra_idx)) avail -∗
          WP (Loop : expr riscv_lang)) -∗
       WP (Loop : expr riscv_lang))%I.

  (* ...AND THE PAIR /init CARRIES FROM ITS ENTRY, persistently: the miss
     leaf is used TWICE (0x16 and, on the repair arm, 0x7e) and the mknod
     leaf once, and both are entailed by persistent ingredients at the era
     -- [AppInv.app_inv], the [□] claim law and
     [UInitCons.init_cons_abs_law] -- so the bundle is a [□] and threads
     through the restart loop's [iLöb] the way [init_exec_sup] does. *)
  Definition init_cons_leaves (T K : iProp Σ) (stc : fdstate) : iProp Σ :=
    (□ uki_open_absent_leaf T K ∗ □ uki_mknod_leaf T K stc)%I.

  (* WHAT THE FIRST OPEN LEAVES, as ONE resource: the call returned [-1]
     (the pure half is read at the [blt] and dropped), so the ledger and the
     credential are back -- or the application is tainted and the ledger is
     at a state nobody named.  Both of /init's console arms are walked from
     this, which is why the repair arm takes it rather than the credential:
     under the taint the credential is gone and the mknod and the second
     open still have to be walked. *)
  Definition uki_cons_in (T K : iProp Σ) : iProp Σ :=
    ((ustd γfd ufd_l0 ∗ K) ∨ (ustd_any γfd ∗ T))%I.

  (* ...AND WHAT THE REPAIR ARM'S SECOND OPEN IS, whichever of the three
     things the mknod left: a call at the all-closed ledger that lands
     /init's head.  ONE shape, so the 0x74..0x82 tail is walked ONCE. *)
  (* ...and what it is CALLED at: the ledger the first open left, or the
     taint.  Both arms reach the repair arm, because /init's C tests
     neither the mknod's result nor the second open's. *)
  Definition uki_open2_in (T : iProp Σ) : iProp Σ :=
    (ustd γfd ufd_l0 ∨ (ustd_any γfd ∗ T))%I.

  Definition uki_open2 (T : iProp Σ) (stc : fdstate) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (avail : nat),
       init_code γt -∗
       (* the read-only image and the two argument words, threaded to
          whichever of the three leaves the mknod's answer chose *)
       init_rodata γt -∗
       ⌜ m !!! Regidx a0_idx = (mword_of_int 0x970 : mword 64)
         /\ m !!! Regidx a1_idx = (mword_of_int 2 : mword 64) ⌝ -∗
       urun N h m (mword_of_int InitSyms.open) avail -∗
       UserCwd.ucwd γcwd FsImg.ROOTINO -∗
       uki_open2_in T -∗
       (∀ (h' : CpuId) (ret : mword 64),
          ufd_head T stc γfd -∗
          UserCwd.ucwd γcwd FsImg.ROOTINO -∗
          urun N h'
            (<[Regidx a0_idx := ret]>
               (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m))
            (ret_pc (m !!! Regidx ra_idx)) avail -∗
          WP (Loop : expr riscv_lang)) -∗
       WP (Loop : expr riscv_lang))%I.

  Global Instance init_cons_leaves_persistent T K stc :
    Persistent (init_cons_leaves T K stc).
  Proof. rewrite /init_cons_leaves. apply _. Qed.

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
  Definition init_deps (T : iProp Σ) : iProp Σ :=
    (udepw_law 16 ∗ □ (T -∗ udepw_law 15) ∗ □ (T -∗ udepw_law 17))%I.

  Global Instance init_deps_persistent T : Persistent (init_deps T).
  Proof. rewrite /init_deps. apply _. Qed.

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
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
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
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
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
        ∨ (⌜ret = (mword_of_int (-1) : mword 64)⌝ ∗ ustd γfd l)) -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
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
              ∨ (⌜ret = (mword_of_int (-1) : mword 64)⌝ ∗ ustd γfd l)))%I
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
  (* WHAT THE ROW GIVES AND WHAT IT DOES NOT: the LEDGER comes back at the   *)
  (* very list it went in at, and nothing is claimed about the return value  *)
  (* ([UkRunSys.wp_uk_ecall_dup_closed]'s note -- the dup row carries no     *)
  (* guard for a closed source).  That is all /init needs: its C reads       *)
  (* neither dup result.                                                     *)
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
       ustd γfd l -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
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
    iIntros (h2 ret) "Hstd Hrun".
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
    iApply ("Hcont" $! h3 ret with "Hstd Hrun").
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
  Proof.
    rewrite /uki_open2 /uki_open2_in.
    iIntros "#Hwl #Ht" (h m avail) "#Hcode #Hro %Hargs Hrun Hcwd Hin Hcont".
    iDestruct ("Hwl" with "Ht") as "#Hwr".
    iApply (wp_kinit_open h m avail with "Hwr Hcode Hrun [Hin]").
    { iDestruct "Hin" as "[H | [H _]]"; [ by iExists ufd_l0 | iExact "H" ]. }
    iIntros (h' ret) "Hstd Hrun".
    iApply ("Hcont" $! h' ret with "[Hstd] Hcwd Hrun").
    iDestruct "Hstd" as (l) "H". iApply (ufd_head_taint with "Ht H").
  Qed.

  (* the node exists: the PINNED open at the resolving pin.  Its taint arm
     is the lemma above, because under the taint there is no pin. *)
  Lemma uki_open2_of_console (T : iProp Σ) `{!Persistent T} (stc : fdstate) :
    □ (T -∗ udepw_law 15) -∗ uki_open_console_leaf T stc -∗ uki_open2 T stc.
  Proof.
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
    - iApply (ufd_head_l1 with "H").
    - iApply (ufd_head_closed with "H").
    - iDestruct "H" as (l) "H". iApply (ufd_head_taint with "Ht H").
  Qed.

  (* the mknod failed and handed the credential back: the MISS pin again,
     and fd 0 stays closed *)
  Lemma uki_open2_of_absent (T K : iProp Σ) `{!Persistent T} (stc : fdstate) :
    □ (T -∗ udepw_law 15) -∗ uki_open_absent_leaf T K -∗ K -∗ uki_open2 T stc.
  Proof.
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
    - iApply (ufd_head_closed with "H").
    - iDestruct "H" as (l) "H". iApply (ufd_head_taint with "Ht H").
  Qed.

  (* --------------------------------------------------------------------- *)
  (* dup(0), ON THE HEAD -- ONE lemma for both of /init's dups and all three *)
  (* arms.  The head is CLOSED under it: on the console arm the copy lands   *)
  (* on the lowest CLOSED slot, which is never slot 0                        *)
  (* ([UInitFd.ufd_after_row0]), and a dup that FAILS moves nothing; on the  *)
  (* closed arm both dups fail on a closed descriptor and the ledger does    *)
  (* not move; on the taint arm the untracked leaf moves the authority and   *)
  (* names nothing.                                                          *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kinit_dup_head (T : iProp Σ) (stc : fdstate)
      (h : CpuId) (m : regfile) (avail : nat) :
    stc <> FdClosed ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat 0 ->
    init_code γt -∗
    urun N h m (mword_of_int InitSyms.dup) avail -∗
    ufd_head T stc γfd -∗
    (∀ (h' : CpuId) (ret : mword 64),
       ufd_head T stc γfd -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hne Harg.
    iIntros "#Hcode Hrun Hhd Hcont".
    rewrite /ufd_head /ufd_std_at.
    iDestruct "Hhd" as "[H | [H | [H Ht]]]".
    - (* CONSOLE: the TRACKED leaf, and the ledger decides where it lands *)
      iDestruct "H" as (l) "[Hstd %Hrow]".
      iApply (wp_kinit_dup_cons h m avail l 0%nat stc Harg Hne
                ltac:(unfold NSTD; lia) Hrow with "Hcode Hrun Hstd").
      iIntros (h' ret) "Hal Hrun".
      iApply ("Hcont" $! h' ret with "[Hal] Hrun").
      iDestruct "Hal" as "[Hs | [_ Hl]]".
      + iDestruct "Hs" as (fd1) "[_ Ha]".
        iDestruct (ualloc_ledger with "Ha") as "Hl".
        iApply (ufd_head_at T stc γfd (ustd_after l stc)
                  (ufd_after_row0 l stc Hne Hrow) with "Hl").
      + iApply (ufd_head_at T stc γfd l Hrow with "Hl").
    - (* CLOSED: the source is a closed standard stream *)
      iApply (wp_kinit_dup_closed h m avail ufd_l0 0%nat Harg
                ltac:(unfold NSTD; lia) ufd_l0_row0 with "Hcode Hrun H").
      iIntros (h' ret) "Hstd Hrun".
      iApply ("Hcont" $! h' ret with "[Hstd] Hrun").
      iApply (ufd_head_closed with "Hstd").
    - (* TAINT: nothing is named, so the untracked leaf is the honest one *)
      iApply (wp_kinit_dup h m avail with "Hcode Hrun H").
      iIntros (h' ret) "Hstd Hrun".
      iApply ("Hcont" $! h' ret with "[Ht Hstd] Hrun").
      iDestruct "Hstd" as (l) "Hstd". iApply (ufd_head_taint with "Ht Hstd").
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
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
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

  (* THE PAYLOAD IS TRIVIAL AT THIS LANE.  exit's leaf is a PAYMENT
     ([UkRunSys.wp_uk_ecall_exit]): the program owes what its record says
     its exit owes.  init's record is minted at [fun _ => True] -- userinit
     forks it from nobody -- so the premise is the equation and the payment
     is [I]. *)
  Lemma wp_kinit_exit (h : CpuId) (m : regfile) (avail : nat) :
    init_code γt -∗
    urun N h m (mword_of_int InitSyms.exit) avail -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun".
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
              with "[] [] Hrun").
    { iApply (uis_init_374 with "Hcode"). }
    (* AT A CONSTANT PAYLOAD THE TWO CONJUNCTS ARE ONE PROPOSITION, so the
       resource the run keeps answers both ([UkRun.ukn_const]). *)
    { iIntros "HQ".
      rewrite (ukn_const_eq (N := N) (uexitst m1) (-1)).
      iSplit; iExact "HQ". }
  Qed.

  (* ===================================================================== *)
  (* INIT'S OWN EXEC SUPPLY, in place of [UkRun.uxsup].                     *)
  (*                                                                       *)
  (* [uxsup] is the exec bundle at EVERY key -- what a program that answers *)
  (* for nothing runs on.  init answers for exactly one exec: the child     *)
  (* arm's [exec("sh", argv)], at a0 = 0x9a8 ("sh" in its rodata), a1 =     *)
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
          ⌜ m !!! Regidx a0_idx = (mword_of_int 0x9a8 : mword 64) ⌝ -∗
          ⌜ m !!! Regidx a1_idx = (mword_of_int 0x1000 : mword 64) ⌝ -∗
          init_rodata (ukn_t N') -∗
          init_argv (ukn_d N') -∗
          ustd_any (ukn_fd N') -∗
          udepw_at N' m pc USYS_exec FsImg.ROOTINO))%I.

  Global Instance init_exec_sup_persistent : Persistent init_exec_sup.
  Proof. rewrite /init_exec_sup. apply _. Qed.

  (* the trivial supplier still pays it: a bundle at every key is a bundle
     at init's *)
  (* AT THE TRIVIAL PAYLOAD, which is the row [init_exec_sup] already
     carries: a process that execs at this lane owes its parent nothing, so
     the bundle the trivial supplier hands over is at exactly the payload
     the record names. *)
  Lemma init_exec_sup_of_uxsup : uxsup -∗ init_exec_sup.
  Proof.
    iIntros "#Hx". iModIntro. iIntros (N' m pc) "%Hpeq _ _ _ _ _".
    pose proof (Hpeq : UkRun.ukn_triv N') as Hti.
    iApply (udepw_at_of_uxsup with "Hx").
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
  (*  THE DESCRIPTOR ROW IS THE HEAD ITSELF, not a bare ledger.  sh's
      entry is told one thing about its table -- fd 0 is the console, or
      slot 0 is closed, or the taint ([UkSh.ush_fd0]) -- and that is
      exactly /init's own head ([UInitFd.ufd_head]), whose three arms are
      the same three.  So the head is what crosses here: the supply reads
      the row off it against the lent authority and spends the ledger,
      which is right -- the process that execs is replaced. *)
  Definition init_exec_sup_pos (cn : cons_names) (T : iProp Σ) (st : fdstate)
      (γ : gname) (n : nat) : iProp Σ :=
    (∀ (N' : uk_names Σ) (m : regfile) (pc : mword 64),
       ⌜ ukn_pay N' = ucons_pay cn γ T ⌝ -∗
       ⌜ m !!! Regidx a0_idx = (mword_of_int 0x9a8 : mword 64) ⌝ -∗
       ⌜ m !!! Regidx a1_idx = (mword_of_int 0x1000 : mword 64) ⌝ -∗
       init_rodata (ukn_t N') -∗
       init_argv (ukn_d N') -∗
       UInitFd.ufd_head T st (ukn_fd N') -∗
       upos γ n -∗
       udepw_at N' m pc USYS_exec FsImg.ROOTINO)%I.

  Definition init_exec_sup_lend (cn : cons_names) (T : iProp Σ)
      (st : fdstate) : iProp Σ :=
    (□ (∀ (γ : gname) (n : nat), init_exec_sup_pos cn T st γ n))%I.

  Global Instance init_exec_sup_lend_persistent cn T st :
    Persistent (init_exec_sup_lend cn T st).
  Proof. rewrite /init_exec_sup_lend. apply _. Qed.

  (* ...AND THE LEAF IS CWD-INDEXED.  [UkRunSys.wp_uk_ecall_exec_at_cwd]
     takes the program's own half of its working directory beside the
     deposit and hands it back on the failure arm: a pinned bundle is about
     a PATH, and a relative path names a file only against the directory it
     is resolved from.  init's [c] is [FsImg.ROOTINO] at every call site,
     but the leaf is stated at a variable one -- nothing here depends on
     which inum it is. *)
  Lemma wp_kinit_exec (h : CpuId) (m : regfile) (avail : nat) (c : Z) :
    init_code γt -∗
    urun N h m (mword_of_int InitSyms.exec) avail -∗
    (* the program's half of its working directory *)
    UserCwd.ucwd γcwd c -∗
    (* THE EXEC DEPOSIT, on the EXPLICIT route: exec's bundle reads the key
       (argv, out of the image), so it is not payable from the supplier and
       [UkRun.udepw]'s left disjunct excludes it by construction.  The
       caller hands it in, at the key the ecall traps from and at the one
       working directory it answers for. *)
    udepw_at N
      (<[Regidx a7_idx := (mword_of_int 7 : mword 64)]> m)
      (mword_of_int 0x3ac) USYS_exec c -∗
    (* exec only comes back when it FAILED, and then it returns -1 *)
    (∀ h' : CpuId,
       UserCwd.ucwd γcwd c -∗
       urun N h'
         (<[Regidx a0_idx := (mword_of_int (-1) : mword 64)]>
            (<[Regidx a7_idx := (mword_of_int 7 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
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
    iApply (wp_uk_ecall_exec_at_cwd N h1 m1 (mword_of_int 0x3ac) avail c
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
    iIntros (h2) "Hcwd Hrun".
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
    iApply ("Hcont" $! h3 with "Hcwd Hrun").
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
  Lemma wp_kinit_wait (h : CpuId) (m : regfile) (avail : nat)
      (cs : gset gname) :
    uint (m !!! Regidx a0_idx) = 0 ->
    init_code γt -∗
    urun N h m (mword_of_int InitSyms.wait) avail -∗
    UserChildren.uch (ukn_ch N) cs -∗
    (∀ (h' : CpuId) (ret : mword 64) (cs' : gset gname),
       uwait_ans ret cs cs' -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 3 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       UserChildren.uch (ukn_ch N) cs' -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
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
    iApply (wp_uk_ecall_wait_null N h1 m1 (mword_of_int 0x37c) avail cs
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
    iIntros (h2 ret cs') "Hans Hrun Hch".
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
    iApply ("Hcont" $! h3 ret cs' with "Hans Hrun Hch").
  Qed.

End UkInit.
