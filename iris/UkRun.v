(* ===================================================================== *)
(* UkRun.v -- THE RUNNING PREDICATE, and the leaf interface above it.     *)
(*                                                                        *)
(* [UserHeap.uheap] is the memory half: two ghost_map authorities against  *)
(* the image, the segment facts, the break and the slack.  THIS file      *)
(* packages that together with the machine bundle into the one thing a    *)
(* user-program proof ever holds:                                          *)
(*                                                                        *)
(*   urun N h m pc avail                                                   *)
(*                                                                        *)
(* -- "the process is running, with general registers [m] at pc [pc]".     *)
(* Everything else is INSIDE, existentially: the hart, the loop-constant   *)
(* config, the page table, the residue the trap loop threads, [p->sz], the *)
(* memory image and the permission map.  None of them matter to a user     *)
(* program, and none of them appear in a leaf statement.                   *)
(*                                                                        *)
(* WHY THE EXISTENTIAL AMBIENT IS THE WHOLE TRICK.  Today every leaf       *)
(* consumes a bundle at ONE ambient but demands a continuation good at     *)
(* EVERY ambient ([UexecRet.ukc]'s ∀), because an interrupt may hand the   *)
(* process back on a different hart under a different table.  The program  *)
(* pays for that mismatch by re-introducing five binders after every       *)
(* instruction -- [rewrite /ukc. iIntros (h C pt Rut sz) "%Hlo %Hpm Hb"],  *)
(* seventy-six times in UkEcho.v alone.  Packing the ambient inside [urun] *)
(* makes the caller's continuation [urun ... m' pc' -* WP] good at any       *)
(* ambient BY CONSTRUCTION, so the leaf absorbs the quantifier and the     *)
(* program never sees it.  [ukc] then has nothing left to name.            *)
(*                                                                        *)
(* THE SPLIT BETWEEN REGISTERS AND MEMORY IS DELIBERATE.  Registers are a  *)
(* whole file inside [urun]: there is no framing to be had -- the slot's   *)
(* key is the trapframe, so every instruction's obligation mentions all of *)
(* them anyway.  Memory is the opposite: fragments live OUTSIDE [urun] and *)
(* a leaf names exactly the bytes it touches, so everything else frames.   *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List FunctionalExtensionality.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import RegFile InstrBytes.
Require Import UserPtTree UserExec ProcPtOwn.
Require Import UmodeMem UmodeArith UmodeText.
Require Import UserPerm UexecWp UexecSlot UexecRet.
Require Import FdSlots.      (* [fdstate] -- the key's descriptor view *)
Require Import PipeNames.    (* [pipe_names] -- what a pipe descriptor carries *)
Require Import WpMmodeLeafBase.
Require Import UptTree.
Require Import WpUmodeStore.
Require Import WpUmodeStep.
Require Import UsysMemOk. (* [USYS_exec] -- the number the minting law excludes *)
Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the deposit class and
                             the program's supplier + admitted numbers *)
Require Import UkStep.
Require Import RiscvExtras.
Require Import UserHeap.
Require Import TsoCtx.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.


(* ===================================================================== *)
(* WpUmodeStore's store-run and UserPtTree's are the same map.  The two   *)
(* build it from opposite ends -- [uM_store] folds index 0 outermost,     *)
(* [umem_write] recurses with index n-1 outermost -- so they are equal    *)
(* but not convertible.  The heap speaks [umem_write]; the store leaves   *)
(* speak [uM_store8]; this is the one lemma that lets a leaf wrapper hand *)
(* one to the other.                                                     *)
(* ===================================================================== *)
Lemma uM_store_umem_write (M : gmap Z (bv 8)) (a : Z) (n : nat) (v : mword 64) :
  uM_store M a (Z.of_nat n) v = umem_write M a n (nth_byte v).
Proof.
  apply map_eq. intro k.
  destruct (decide (a <= k < a + Z.of_nat n)) as [Hin | Hout].
  - assert (Hj : (Z.to_nat (k - a) < n)%nat) by lia.
    replace k with (a + Z.of_nat (Z.to_nat (k - a))) by lia.
    rewrite (uM_store_lookup M a (Z.of_nat n) v _
               ltac:(rewrite Nat2Z.id; exact Hj)).
    rewrite (umem_write_lookup_in M a n (nth_byte v) _ Hj). reflexivity.
  - rewrite (uM_store_lookup_ne M a (Z.of_nat n) v k
               ltac:(intros j Hj; rewrite Nat2Z.id in Hj; lia)).
    rewrite (umem_write_lookup_out M a n (nth_byte v) k
               ltac:(intros j Hj; lia)).
    reflexivity.
Qed.

Lemma uM_store8_umem_write (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  uM_store8 M a v = umem_write M a 8 (nth_byte v).
Proof. exact (uM_store_umem_write M a 8%nat v). Qed.

Require Import FdSlots.  (* [fdstate] -- what a descriptor slot holds *)
Require Import ProcGeom.  (* [NOFILE] -- how many of them there are *)
Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)
Require Import UserChildren. (* [uch_auth] -- the PROGRAM's own view of its
                                live children's generations *)
Require Import UserCwd.  (* [ucwd_auth] -- the PROGRAM's own view of its
                            working directory, on the same mold *)
(* ===================================================================== *)
(* THE PROCESS'S GHOST NAMES, IN ONE RECORD.                              *)
(*                                                                        *)
(* The engine's per-process ghosts travel together: every leaf that       *)
(* touches [urun] needs all of them at once, so a name carried loose is   *)
(* an argument on [urun], on every leaf, and on every statement in every  *)
(* program file.  The ENGINE therefore bundles them: [urun], [udepw] and  *)
(* every leaf take the record and read the fields.                        *)
(*                                                                        *)
(* THE LEAF RESOURCES KEEP THEIR OWN NAMES.  [UserHeap.uheap] / [usz] /   *)
(* [utext] / [ubyte] / [ustack] and [UserFd.ufd_auth] / [ufd] / [ustd]    *)
(* are stated at bare gnames and APPLIED at the record's fields.  They    *)
(* are resources in their own right, and they are used at names that are  *)
(* nobody's running process -- the mirrored fragments [UkFork.uheap_fork] *)
(* hands the child before the child's record exists, for one.  The record *)
(* is the ENGINE's bundle, not a replacement for a ghost name.            *)
(*                                                                        *)
(* A program file binds the record and reads the fields under the names   *)
(* the engine has always used, with five [Local Notation]s at the top of  *)
(* its section; the engine's own leaves spell the projections out.        *)
(* ===================================================================== *)
(* THE RECORD IS Σ-PARAMETRIC, and the field that makes it so is the last
   one: a run is keyed by WHAT ITS EXIT OWES, which is an [iProp] and not a
   ghost name.  It belongs here for the same reason the five names do --
   every leaf that touches [urun] needs it at once, and exit's leaf reads
   it -- and it is a FIELD rather than a parameter of [urun] because the
   record is what an entry constructor mints and what a program file binds
   once ([uslot_of_urun] and its two siblings take the pay fact and put it
   here). *)
Record uk_names (Σ : gFunctors) := MkUkNames {
  ukn_t : gname;   (* the text map's authority ([UserHeap.utext]'s) *)
  ukn_d : gname;   (* the data map's ([ubyte], [ustack], the slack) *)
  ukn_s : gname;   (* the break ([usz], a half of a ghost variable) *)
  ukn_fd : gname;  (* the descriptor table's ([UserFd.ufd_auth]) *)
  ukn_cwd : gname; (* the working directory's ([UserCwd.ucwd_auth]) *)
  ukn_ch : gname;  (* the live children's ([UserChildren.uch_auth]) *)
  (* THE EXIT PAYLOAD: what this process's exit owes its parent, as a
     function of the status it exits with.  [ChildTok.my_pay] of the
     process's own generation is what BACKS it -- [urun] carries that fact
     at this very predicate -- so a run cannot name a payload that is not
     its own, and exit's leaf ([UkRunSys.wp_uk_ecall_exit]) pays exactly
     this at exactly the status the program passes. *)
  ukn_pay : Z -> iProp Σ;
  (* THE PROCESS'S OWN PID, AS A GHOST NAME (lane TRAP-ROWS-4, B).
     [urun] binds the key's pid existentially, so until now a program had
     no handle on it at all -- which is what kept wait's reaping arm
     unredeemable: the arm says "the generation you reaped was your own
     child unless YOU are <init>", and a caller that cannot say which pid
     it is can take neither disjunct.  [UserChildren.upid_auth] sits in
     [urun] pinned to [bv_unsigned (uvis_pid W)] and the fragment is what
     an entry constructor hands over -- [ukn_cwd]'s twin, one value wide.
     It is independently what makes getpid(2)'s answer sayable. *)
  (* NO FIELD FOR <INIT>'S PID (lane TRAP-ROWS-4, B1b).  B1a carried a
     pure [ukn_ipid] here on the way to pinning wait's reaping arm at a
     number; the pin is now the LITERAL 1 -- the C carves
     [int nextpid = 1] and userinit's allocproc is the first allocation --
     so the two rows that would have read it,
     [UkRunSys.wp_uk_ecall_wait_null_pid]'s [⌜p = 1⌝] disjunct and
     [UkFork.wp_uk_ecall_fork]'s [⌜pidc <> 1⌝], name the literal and an
     entry constructor has nothing left to choose. *)
  ukn_pid : gname;
  (* [ukn_held] IS DELETED (lane OFF-LINK-2, L6).  It was the set of
     descriptors a record might hold an offset half of, and it existed to
     carry "every unparked row of this table is one of these" through the
     generic tier -- the fact design/app-file.md SS3.5's principle retires
     (the generic tier pays the TAINT, and is told nothing about offsets).
     It had been dead data since lane OFF-HAND-6's H3 deleted its one
     consumer; every row and premise that mentioned it goes with it. *)
}.
Global Arguments MkUkNames {_} _ _ _ _ _ _ _ _.
Global Arguments ukn_t {_} _.
Global Arguments ukn_d {_} _.
Global Arguments ukn_s {_} _.
Global Arguments ukn_fd {_} _.
Global Arguments ukn_cwd {_} _.
Global Arguments ukn_ch {_} _.
Global Arguments ukn_pay {_} _.
Global Arguments ukn_pid {_} _.

(* [ukn_parked] IS DELETED WITH THE FIELD (lane OFF-LINK-2, L6): the class
   said [ukn_held N = ∅], and there is no such field to constrain. *)

(* THE TRIVIAL PAYLOAD, AS A CLASS.  A program whose exit owes its parent
   nothing has to be able to SAY so at its exit ecall
   ([UkRunSys.wp_uk_ecall_exit] is a payment), and the fact is fixed by
   whoever minted the record -- an entry constructor
   ([UkRun.uslot_of_urun*]'s row) or fork's child arm ([UkFork]).  A CLASS
   rather than a plain hypothesis so that it travels the way a ghost class
   does: a file's section carries one, every lemma that needs it is
   generalized over it, and a CROSS-FILE call fills it by instance
   resolution instead of by an extra argument at every site.  L7 is what
   gives init and sh a payload that is not this one; the class then simply
   has no instance for them. *)
Class ukn_triv {Σ : gFunctors} (N : uk_names Σ) : Prop :=
  ukn_triv_eq : ukn_pay N = (fun _ => True)%I.

(* ...AND THE WEAKER FACT A PROGRAM WITH A REAL PAYLOAD STILL HAS
   (app-echo.md, "SH-LINE RULING"): the payload DOES NOT READ THE STATUS.

   The only thing a program does with its own payload between its entry and
   its exit is pay [UkRunSys.wp_uk_ecall_exit]'s premise
   [ukn_pay N (-1) -∗ ukn_pay N xs ∧ ukn_pay N (-1)], and that premise is
   provable from ONE resource exactly when the two sides are the SAME
   proposition.  A shell that is lent the console's reader token owes its
   parent that token whether it exits or is killed
   ([UserConsole.ucons_pay] is constant by [ucons_pay_const]), so this is
   the class its files carry where they used to carry [ukn_triv] -- and
   nothing else about the payload leaks into a program statement.

   A CLASS, for [ukn_triv]'s reasons, and with no parameter: a parameter
   would have to be guessed by instance resolution at every call site. *)
Class ukn_const {Σ : gFunctors} (N : uk_names Σ) : Prop :=
  ukn_const_eq : forall x y : Z, ukn_pay N x = ukn_pay N y.

(* ...AND WHAT A TRIVIAL PAYLOAD PAYS AT ITS OWN EXIT: nothing (lane
   KILL-PAY, K4(a)).  [UkRunSys.wp_uk_ecall_exit]'s premise takes the
   payload out of the PROGRAM's hand now -- [urun]'s row is a WAND from
   the kill credential, so there is nothing there to spend -- and a
   program that owes its parent nothing has it for free.  A walk SHARED
   between a shell and its forked child carries this as a Coq-level
   premise rather than the class [ukn_triv] itself, because the shell's
   own payload is a real resource and the walk has to be statable at
   both. *)
Lemma ukn_pay_free_of_triv {Σ : gFunctors} (N : uk_names Σ) :
  ukn_triv N -> ⊢ ukn_pay N (-1).
Proof. intros Ht. rewrite Ht. done. Qed.

(* the trivial payload is a constant one.  NOT an [Instance]: a program
   file carries exactly one of the two as a section hypothesis, and a
   resolution path from [ukn_triv] would make both available in the files
   that carry [ukn_triv] and neither statement say which it meant. *)
Lemma ukn_const_of_triv {Σ : gFunctors} (N : uk_names Σ) :
  ukn_triv N -> ukn_const N.
Proof. intros Ht x y. by rewrite Ht. Qed.

(* ...AND THE ROUTE AN ENTRY CONSTRUCTOR TAKES.  What a constructor is
   handed is the EQUATION [ukn_pay N = Q] (the record it mints is keyed at
   the payload the kernel gave it -- [uslot_of_urun_all]'s row), and what
   the program's own leaves want is the CLASS.  At a payload that does not
   read the status -- which is every payload a program can pay an exit with
   out of one resource -- the two are one step apart.  [UserConsole.
   ucons_pay_const] is the witness sh's entry supplies. *)
Lemma ukn_const_of_eq {Σ : gFunctors} (N : uk_names Σ) (Q : Z -> iProp Σ) :
  ukn_pay N = Q -> (forall x y : Z, Q x = Q y) -> ukn_const N.
Proof. intros Heq HQ x y. rewrite Heq. exact (HQ x y). Qed.

(* ...AND THE BRIDGE TO THE FORM THE GENERIC SLOT IS STATED AT
   (GENERIC-PAY).  [UexecRet.uexec_wp_uslot] and the two supply laws are
   indexed by a payload of the shape [fun _ => R] -- a literal constant
   function -- while [ukn_const] is the pointwise statement.  The witness
   is the payload at the kill status, which is the resource the run
   carries ([urun]'s [ukn_pay N (-1)] conjunct), so the two readings of
   "what this process owes" are one resource by construction. *)
Lemma ukn_pay_const {Σ : gFunctors} (N : uk_names Σ) `{!ukn_const N} :
  ukn_pay N = (fun _ => ukn_pay N (-1)).
Proof.
  apply functional_extensionality. intros x. exact (ukn_const_eq x (-1)).
Qed.

Section UkRun.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  (* NO ambient [CpuId]: the hart is an explicit argument of [urun], and the
     [WP] under that binder resolves to the one bound there -- the trick
     [UexecRet.ukc] uses. *)
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.

  (* ===================================================================== *)
  (* §1 THE RUNNING PREDICATE.                                             *)
  (* ===================================================================== *)
  (* [avail] is the FREE STACK, in words, below the current sp -- the
     user-mode twin of [sie_cap_gpr]'s counting argument.  The process owns
     it; an sp-adjust hands a frame out of it or takes one back; every other
     instruction threads it unchanged, which is why every leaf that writes a
     register takes [unot_sp] as a premise (a write to sp would move the
     index this ownership is keyed by). *)
  (* THE DESCRIPTOR VIEW IS HIDDEN HERE, exactly as the break and the image
     are: [urun] is what a PROGRAM proof carries between instructions, and a
     program that never looks at its descriptors should not have to name
     them.  A leaf that IS closing back up has just destructed the
     existential, so it can say which view it is at -- the same discipline
     [sz] follows, and the reason [urun_close] takes [fdv] as a parameter. *)
  (* THE DEPOSIT SUPPLIER AND ITS MINTING LAW.  Since the ARM, the trap
     contract's returning arm demands the process's bundle for the number it
     is at ([UexecRet.uexec_dep_F]); a leaf below the file-system tower
     cannot see that the instance's [sbundle_at] is [emp] at its number, so it
     pays with the law below.

     WHY IT RIDES IN [urun] AND NOT IN [uvb], AND WHY IT IS ABSTRACT.  A
     [uvb] conjunct would make the KERNEL owe the supply to resume ANY
     process, and an application whose predicate is not trivially true
     cannot pay that -- echo's is [taint ∨ pins], true of every view only
     after the taint is minted -- so every pre-taint trap round would be
     unsatisfiable: the GAP-premise trap sitting in the trap loop.  Carrying
     a CONCRETE [□ ssupply] here instead is the SAME refutation one level
     down: echo could not build a [urun] at all before the taint.  So what
     rides here is an ABSTRACT supplier the program chooses, the way [Rut]
     and [Rfd] are abstract, with the numbers it undertakes to pay for
     ([psok]) beside it -- both fields of the ambient [UexecSG.uprogSG],
     which is what keeps every program lemma statement from naming either.

     THE LAW IS KEY-FREE, AND THAT IS FORCED, NOT CHOSEN.  A law stated at
     [urun]'s own bound key would have to survive every move the program
     makes to that key, because [urun] is re-established after every
     instruction: a store moves [M] ([urun_close] at
     [umem_write M …]), sbrk moves [pm] and [sz], open / dup / close / pipe
     move [fdv], and every returning ecall moves [cw].  Closed under all
     five, a key-indexed law IS the key-free one.  So the admission [psok]
     is a set of NUMBERS, and a bundle whose content reads the key -- exec's,
     which reads argv out of the image -- is not payable through this law at
     all: it goes the EXPLICIT-PREMISE route the exec leaf already uses
     ([UkRunSys.wp_uk_ecall_exec] takes the deposit as a hypothesis), which
     is why [USYS_exec] is excluded here.  A bundle that IS key-free once
     the descriptor view is fixed -- echo's console write, whose input is a
     trace seed minted from unit -- goes through the law.  THE HONEST
     CONSEQUENCE: a program admitting a number pays that number's bundle at
     EVERY key, not only at the call it is about to make. *)
  (* BUPD-SHAPED, like the class's own two laws ([UexecSG.v]'s header): a
     bundle may hold a resource that is free but not derivable from [emp]
     -- write's console arm carries the trace seed, the mono-list unit --
     and putting the update in the LAW rather than in a particular supplier
     is what keeps such a piece payable by a program whose supplier is
     [emp].  The ARM still demands a plain [sbundle]; the leaf runs the
     update inside its own WP step. *)
  (* ...AND THE LAW NAMES THE PAYLOAD (app-echo.md, "SH-LINE RULING", R1).
     read's bundle is a WAND FROM THE DEPOSITING PROCESS'S OWN EXIT
     PAYLOAD, and a leaf must deposit at the family whose payload it is
     about to pay the trap's payment row at ([UexecRet.uexec_pay_dep]) --
     so the mint takes that payload rather than choosing a family and
     leaving the leaf to re-key, which [UexecSG.sbundle_at_at] no longer
     licenses at read.  Every [Q] is admissible: read's console arm is
     payable out of the persistent credential at any [P]
     ([FsAbsInvFire.fsabs_fileread_in]). *)
  (* ...AND CLOSE(21) IS A SECOND, KEY-GUARDED LAW (design/pipe.md, "The
     byte queue").  Clearing a pipe end's flag word steps the pipe's EXACT
     ghost state, so [UexecSG.free_num] no longer admits 21 and the
     key-free law above cannot mint it: at a PIPE key the deposit is a
     close link, payable only by a holder of the fragment or by the taint.
     At every OTHER descriptor it is [emp] -- and that is a fact about the
     KEY, not about the number, which is why it cannot be a clause of
     [psok] and is a law of its own.  The close leaves hold the HANDLE that
     decides ([UkRunSys.wp_uk_ecall_close]), so a caller of theirs that
     closes anything but a pipe carries no row at all. *)
  Definition ukey_nonpipe (W : uvis) : Prop :=
    forall (rb wb : bool) (gp : pipe_names),
      fd_st_of_key (tf_w (uvis_tf W) (tf_arg_idx 0)) (uvis_fd W)
      <> FdOpen rb wb (FdPipe gp).

  (* ...AND EXIT(2) IS A THIRD ONE, close's twin over a WHOLE TABLE
     (design/pipe.md, "The exit path").  kexit closes every descriptor the
     dying process holds, so the exit number's bundle row is
     [SpecFileclose.fileclose_cpays] of the KEY's own table
     ([UexecExecInst.xv6_sbundle] at 2), and 2 left [UexecSG.free_num] with
     it.  At a table that holds no pipe row every payment is [emp] and the
     row is minted from nothing ([UexecExecInst.xv6_sbundle_exit_nopipe]);
     a table the caller cannot read that way costs an explicit deposit, as
     any other flagged number does. *)
  (* THE TABLE PREDICATE IS [FdSlots.fdv_nopipe] and not a local copy: it
     is the very proposition [UsysMemOk.usys_fd_ok]'s open row carries and
     [usys_fd_ok_nopipe] preserves, so a leaf re-establishes it at the
     table its round returned with one lemma and no translation.
     [FdSlots.fdv_nopipe_elem] is its reading in the shape
     [UexecExecInst.xv6_sbundle_exit_nopipe] wants. *)
  Definition ukey_table_nopipe (W : uvis) : Prop := fdv_nopipe (uvis_fd W).

  Definition udep : iProp Σ :=
    (□ Dsup ∗
     ⌜ forall (n : Z) (W : uvis) (Q : Z -> iProp Σ),
         psok n -> n <> USYS_exec ->
         ⊢ □ Dsup ==∗ sbundle_pay uslot n Q W ⌝ ∗
     ⌜ forall (W : uvis) (Q : Z -> iProp Σ),
         ukey_nonpipe W ->
         ⊢ □ Dsup ==∗ sbundle_pay uslot 21 Q W ⌝ ∗
     (* ...AND EXIT'S ROW OFF THE TABLE'S REGISTRATIONS (design/app-pipe.md
        SS2, lane PIPE-REG).  This used to be guarded on the PURE
        [ukey_table_nopipe W] -- "the key's table holds no pipe" -- which is
        the reading no program that has called pipe(2) can have.  What it
        takes now is a RESOURCE, one registration per row of the key's own
        table ([UexecSG.srow_reg], the class field the instance answers
        with [PipeReg.pipe_row_reg]), and the pure reading is a COROLLARY
        ([udep_exit_dep] below, whose statement did not move) because a row
        that is not a pipe registers itself.  A pipe-holding program's run
        carries the registrations instead, which is the whole point. *)
     ⌜ forall (W : uvis) (Q : Z -> iProp Σ),
         ⊢ □ Dsup -∗ ([∗ list] st ∈ uvis_fd W, srow_reg st) ==∗
             sbundle_pay uslot USYS_exit Q W ⌝ ∗
     (* ...AND EXIT'S ROW AT ANY TABLE AT ALL, OUT OF THE TAINT
        (design/pipe.md, "The exit path").  A pipe row's close payment is
        [PipeQueue.pipe_cpay], which is a close link OR the taint, so a
        process that holds the taint owes nothing whatever its table holds
        ([SpecFileclose.fileclose_cpays_taint]).  This is the arm a program
        that CALLS pipe(2) exits by: it gives up [fdv_nopipe] at the pipe
        leaf and carries the credential instead. *)
     ⌜ forall (W : uvis) (Q : Z -> iProp Σ),
         ⊢ □ Dsup -∗ app_taint ==∗ sbundle_pay uslot USYS_exit Q W ⌝)%I.

  Global Instance udep_persistent : Persistent udep.
  Proof using . rewrite /udep. apply _. Qed.

  (* what a leaf does with it: mint the deposit the ecall arm asks for *)
  Lemma udep_dep (n : Z) (W : uvis) (Q : Z -> iProp Σ) :
    psok n -> n <> USYS_exec -> udep -∗ |==> sbundle_pay uslot n Q W.
  Proof using .
    intros Hok Hne. iIntros "[#Hs [%Hlaw _]]".
    iApply (Hlaw n W Q Hok Hne). iExact "Hs".
  Qed.

  (* ...and the close row's own, at a key whose argument 0 is not a pipe *)
  Lemma udep_close_dep (W : uvis) (Q : Z -> iProp Σ) :
    ukey_nonpipe W -> udep -∗ |==> sbundle_pay uslot 21 Q W.
  Proof using .
    intros Hnp. iIntros "[#Hs [_ [%Hlaw _]]]".
    iApply (Hlaw W Q Hnp). iExact "Hs".
  Qed.

  (* ...AND THE EXIT ROW'S, OFF THE TABLE'S REGISTRATIONS.  The law itself
     (design/app-pipe.md SS2): one [UexecSG.srow_reg] per row of the key's
     table, which is what [urun_nopipe]'s left arm is. *)
  Lemma udep_exit_regs (W : uvis) (Q : Z -> iProp Σ) :
    ([∗ list] st ∈ uvis_fd W, srow_reg st) -∗ udep -∗
    |==> sbundle_pay uslot USYS_exit Q W.
  Proof using .
    iIntros "Hr [#Hs [_ [_ [%Hlaw _]]]]".
    iApply (Hlaw W Q with "Hs Hr").
  Qed.

  (* ...AND THE ROWS AT A TABLE THAT HOLDS NO PIPE, which is the class's
     one law about the row read over a whole table
     ([UexecSG.srow_reg_nopipe]).  What makes a program that never calls
     pipe(2) pay nothing whatever. *)
  Lemma srow_regs_nopipe (fdv : list fdstate) :
    fdv_nopipe fdv -> ⊢ [∗ list] st ∈ fdv, srow_reg st.
  Proof using .
    intros Hnp. iApply big_sepL_intro. iIntros "!>" (k st Hk).
    iApply (srow_reg_nopipe st (fdv_nopipe_lookup fdv k st Hnp Hk)).
  Qed.

  (* ...and the exit row's at a key whose TABLE holds no pipe, the reading
     the pipe-free programs have always had -- a COROLLARY now, and its
     statement did not move *)
  Lemma udep_exit_dep (W : uvis) (Q : Z -> iProp Σ) :
    ukey_table_nopipe W -> udep -∗ |==> sbundle_pay uslot USYS_exit Q W.
  Proof using .
    intros Hnp. iIntros "#Hd".
    iApply (udep_exit_regs W Q with "[] Hd").
    iApply (srow_regs_nopipe (uvis_fd W) Hnp).
  Qed.

  (* ...and the same row out of the taint, at ANY table *)
  Lemma udep_exit_taint (W : uvis) (Q : Z -> iProp Σ) :
    app_taint -∗ udep -∗ |==> sbundle_pay uslot USYS_exit Q W.
  Proof using .
    iIntros "#Ht [#Hs [_ [_ [_ %Hlaw]]]]".
    iApply (Hlaw W Q with "Hs Ht").
  Qed.

  (* [avail] is the FREE STACK, in words, below the current sp -- the
     user-mode twin of [sie_cap_gpr]'s counting argument.  The process owns
     it; an sp-adjust hands a frame out of it or takes one back; every other
     instruction threads it unchanged, which is why every leaf that writes a
     register takes [unot_sp] as a premise (a write to sp would move the
     index this ownership is keyed by). *)
  (* THE DESCRIPTOR VIEW IS HIDDEN HERE, exactly as the break and the image
     are: [urun] is what a PROGRAM proof carries between instructions, and a
     program that never looks at its descriptors should not have to name
     them.  A leaf that IS closing back up has just destructed the
     existential, so it can say which view it is at -- the same discipline
     [sz] follows, and the reason [urun_close] takes [fdv] as a parameter. *)
  (* THE ECALL LEAF'S DEPOSIT PREMISE, as a WAND OFF THE AUTHORITIES the
     leaf already holds -- and it has to be a wand and not a bare premise:
     the key the deposit is at is [uvis_of_run m pc M pm sz fdv cw], and
     [M] / [pm] / [sz] / [fdv] / [cw] are bound by [urun]'s own existential,
     so a leaf has them only AFTER it destructs and can never name them in
     its own statement.  Same wall as the key-free law above, one level out.

     THE DISJUNCTION IS THE TWO ROUTES.  Left: the number is one the program
     admits ([psok]), and the leaf mints the bundle from [udep] --
     [udepw_mint].  Right: the program hands an EXPLICIT deposit at this
     key, which is what exec takes always, and what a program with a
     key-reading bundle (init's mknod, a constraining application's write)
     takes at its own numbers. *)
  (* THE PAY FACT IS LENT WITH THE HEAP.  The exec bundle a supplier may
     have to produce carries the depositing process's own knowledge of its
     payload ([UexecExecInst.exec_sbundle]), which is keyed at the KEY's
     generation -- bound by this ∀, so it cannot come from anywhere but
     here.  The run holds it ([urun]'s own conjunct) and the minting law
     below is what lends it; persistent, so lending costs nothing and
     nothing has to come back. *)
  Definition udepw (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) : iProp Σ :=
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
       (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname) (pidv : mword 32),
       my_pay gn (ukn_pay N) -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
       (⌜psok n /\ n <> USYS_exec⌝
        (* AT THE PROGRAM'S OWN PAYLOAD (R1): the explicit deposit is
           the one the leaf hands the trap beside [ukn_pay N (-1)], and
           read's bundle is a wand from exactly that. *)
        ∨ sbundle_pay uslot n (ukn_pay N)
            (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)))%I.

  (* THE FAMILY-NAMED EXPLICIT DEPOSIT (app-echo.md, lane CONS-CURSOR, C3).
     [udepw]'s explicit disjunct hides the deposited FAMILY under an
     existential, which is exactly right for every leaf that DISCARDS its
     post: the witness is minted and handed straight over.  A leaf that
     HANDS THE POST TO THE PROGRAM cannot use that shape -- the program has
     to read its post at the family it deposited, and an existential loses
     it -- so this variant names the family, and [udepwf_udepw] is the
     forgetful direction the other leaves still take.

     NOT PERSISTENT, and that is the point.  [uxsup] can be a [□] over every
     key because an exec bundle is inexhaustible; the console read's deposit
     carries the READER TOKEN, which is exclusive, so the program supplies
     it through this wand -- once, at whatever key the walk has reached --
     rather than at every key. *)
  Definition udepwf (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) (fdep : sfam) : iProp Σ :=
    ((* AT THE PROGRAM'S OWN PAYLOAD (R1), stated once rather than under
        the key binders: read's deposit is a wand from it, and a program
        that names its family names its payload with it. *)
     ⌜sexit_pay fdep = ukn_pay N⌝ ∗
     ∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
       (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname) (pidv : mword 32),
       my_pay gn (ukn_pay N) -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
       sbundle_at uslot n fdep (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all))%I.

  Lemma udepwf_udepw (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) (fdep : sfam) :
    udepwf N m pc n fdep -∗ udepw N m pc n.
  Proof using .
    rewrite /udepwf /udepw. iIntros "[%Hpay H]" (M pm sz fdv cw gn cs pidv) "Hp Hh Hf".
    iDestruct ("H" $! M pm sz fdv cw gn cs pidv with "Hp Hh Hf") as "(Hh & Hf & Hb)".
    iFrame "Hh Hf". iRight. iExists fdep. iSplitR; [done | iExact "Hb"].
  Qed.

  (* the GENERIC route's supplier: a number the program admits *)
  Lemma udepw_of_psok (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) :
    psok n -> n <> USYS_exec -> ⊢ udepw N m pc n.
  Proof using .
    intros Hok Hne. rewrite /udepw. iIntros (M pm sz fdv cw gn cs pidv) "_ Hh Hf".
    iFrame "Hh Hf". iLeft. iPureIntro. exact (conj Hok Hne).
  Qed.

  (* ...AND THE FLAGGED DEPOSIT (lane SUPPLY-SPLIT, P4): the premise a
     program takes for a number OUTSIDE its supplier's admitted set.  It is
     [udepw] at every key and under a [□], for two reasons: the call sits
     inside a loop (init's and sh's printf, echo's three writes), so a
     linear premise could not answer the second turn; and the key the call
     is made at is bound by the walk, not by the caller, so a key-fixed
     premise could not be stated where the program lemma is.

     WHAT IT IS NOT: [udep].  A verified program may not take the
     program-generic supplier -- at this instance that is [AppInv.app_sup],
     which for the echo application IS the taint
     ([AppEcho.echo_taint_of_sup]), so a slot taking it could only ever be
     entered tainted.  ONE NUMBER'S deposit is exactly the work owed, and
     naming it per number is what makes the debt readable. *)
  (* IT QUANTIFIES THE RECORD TOO.  A program's lemmas are stated at the
     section's [N], but the one that forks re-enters at its CHILD's record
     ([UkInitMain.wp_kinit_main_child] is proved at an [N'] the fork arm
     binds), and a slot constructor's run is built per trap round under its
     own [∀ N].  A deposit for a number is not about the record -- the
     bundle's content reads the KEY and the payload only through
     [ukn_pay N], which every discharger answers at any payload -- so the
     law is stated once, over all three binders, and every site applies it. *)
  Definition udepw_law (n : Z) : iProp Σ :=
    (□ ∀ (N : uk_names Σ) (m : regfile) (pc : mword 64), udepw N m pc n)%I.

  Global Instance udepw_law_persistent n : Persistent (udepw_law n).
  Proof using . rewrite /udepw_law. apply _. Qed.

  Lemma udepw_of_law (N : uk_names Σ) (m : regfile) (pc : mword 64) (n : Z) :
    udepw_law n -∗ udepw N m pc n.
  Proof using . iIntros "#H". iApply "H". Qed.

  (* ...and the instance's own supplier of one, so a program whose number IS
     admitted never needs the premise ([UexecSG.free_num]) *)
  Lemma udepw_law_of_psok (n : Z) :
    psok n -> n <> USYS_exec -> ⊢ udepw_law n.
  Proof using .
    intros Hok Hne. rewrite /udepw_law. iIntros "!>" (N m pc).
    iApply (udepw_of_psok N m pc n Hok Hne).
  Qed.

  (* THE LEAF'S USE OF IT, at every number including exec: the left
     disjunct carries [n <> USYS_exec] itself, so at exec only the explicit
     deposit can have been taken and no side condition is owed here. *)
  (* ...UNDER A BASIC UPDATE, since the law is (UexecSG.v's header).  Every
     call site is inside its leaf's own WP goal, which absorbs it. *)
  Lemma udepw_mint (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
      (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname) (pidv : mword 32) :
    udep -∗ my_pay gn (ukn_pay N) -∗ udepw N m pc n -∗
    uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv ==∗
    uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
    sbundle_pay uslot n (ukn_pay N) (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all).
  Proof using .
    iIntros "#Hdep #Hmp Hsb Hheap Hufd".
    iDestruct ("Hsb" $! M pm sz fdv cw gn cs pidv with "Hmp Hheap Hufd")
      as "(Hheap & Hufd & [%Hok | Hb])"; iFrame "Hheap Hufd";
      [ iApply (udep_dep n _ (ukn_pay N) (proj1 Hok) (proj2 Hok) with "Hdep")
      | by iModIntro ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE ROW-AWARE DEPOSIT (design/app-pipe.md SS4.3aa, lane                *)
  (* SH-PIPE-ROUND-13).  [udepw] quantifies the descriptor TABLE            *)
  (* universally, so a payer of [udepw N m pc 21] has to cover the close of *)
  (* an ARBITRARY table's argument-0 row -- including some other pipe's.    *)
  (* No verified program can do that: [PipeReg.pipe_reg] pays exactly ONE   *)
  (* pipe's close, so the only producer of [udepw_law 21] is the taint      *)
  (* ([UexecExecMint.udepw_law_of_sup_close]), and the pipeline round --    *)
  (* which closes four pipe rows per turn -- had no untainted route at all. *)
  (*                                                                        *)
  (* THE ROW IS ALREADY PINNED AT THE CALL SITE and was simply being thrown *)
  (* away: [udepw_cl_mint] below takes [fd_st_of_key a0 fdv = st] as a Coq  *)
  (* premise (the close leaves derive it from the caller's own handle,      *)
  (* [UserFd.ufd_agree]), and that is exactly the fact a row-aware payer    *)
  (* needs.  So this is [udepw] with that equation moved INSIDE the table   *)
  (* binder as an antecedent: a payer owes the row only at the tables whose *)
  (* argument-0 descriptor IS the [st] the deposit is indexed by.  Strictly *)
  (* weaker than [udepw] ([udepw_row_of_udepw]), so every landed consumer   *)
  (* re-discharges unchanged, and payable from a registration               *)
  (* ([UexecExecMint.udepw_row_of_reg_close]).                              *)
  (* ------------------------------------------------------------------- *)
  Definition udepw_row (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) (st : fdstate) : iProp Σ :=
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
       (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname) (pidv : mword 32),
       ⌜fd_st_of_key (m !!! Regidx (mword_of_int 10 : mword 5)) fdv = st⌝ -∗
       my_pay gn (ukn_pay N) -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
       (⌜psok n /\ n <> USYS_exec⌝
        ∨ |==> sbundle_pay uslot n (ukn_pay N)
            (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)))%I.

  (* the forgetful direction: a payer for every table pays at this one *)
  Lemma udepw_row_of_udepw (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) (st : fdstate) :
    udepw N m pc n -∗ udepw_row N m pc n st.
  Proof using .
    rewrite /udepw /udepw_row.
    iIntros "H" (M pm sz fdv cw gn cs pidv) "_ Hp Hh Hf".
    iDestruct ("H" $! M pm sz fdv cw gn cs pidv with "Hp Hh Hf")
      as "(Hh & Hf & [%Hok | Hb])"; iFrame "Hh Hf";
      [ by iLeft | iRight; by iModIntro ].
  Qed.

  (* ...and the mint, [udepw_mint] with the row equation handed over *)
  Lemma udepw_row_mint (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) (st : fdstate) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm)
      (sz : Z) (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname)
      (pidv : mword 32) :
    fd_st_of_key (m !!! Regidx (mword_of_int 10 : mword 5)) fdv = st ->
    udep -∗ my_pay gn (ukn_pay N) -∗ udepw_row N m pc n st -∗
    uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv ==∗
    uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
    sbundle_pay uslot n (ukn_pay N) (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all).
  Proof using .
    intros Hkey. iIntros "#Hdep #Hmp Hsb Hheap Hufd".
    iDestruct ("Hsb" $! M pm sz fdv cw gn cs pidv with "[%] Hmp Hheap Hufd")
      as "(Hheap & Hufd & Hd)"; [ exact Hkey | ].
    iFrame "Hheap Hufd".
    iDestruct "Hd" as "[%Hok | Hb]";
      [ iApply (udep_dep n _ (ukn_pay N) (proj1 Hok) (proj2 Hok) with "Hdep")
      | iExact "Hb" ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE CLOSE LEAF'S DEPOSIT, IN THE TWO SHAPES A CALLER CAN HAVE IT       *)
  (* (design/pipe.md, "The byte queue").                                    *)
  (*                                                                        *)
  (* LEFT: the caller KNOWS its descriptor is not a pipe -- a console, an    *)
  (* inode, a device -- and owes nothing at all; the leaf mints the row out  *)
  (* of the key-guarded law above, off the [udep] its own run carries.       *)
  (* RIGHT: the caller does NOT know -- it holds a descriptor whose type   *)
  (* nothing told it, an fd read out of a table it did not fill -- and then  *)
  (* it hands over a deposit at 21 like any other flagged number             *)
  (* ([udepw_law], which the pipe arm makes payable out of the taint --      *)
  (* [UexecExecMint.udepw_law_of_sup_close]).                                *)
  (*                                                                        *)
  (* THE OLD READING OF THE RIGHT ARM IS GONE (survey R4, lane SUP-ONE).     *)
  (* It used to say that a descriptor [open] RETURNED forced the right arm,  *)
  (* because "[UsysMemOk.usys_fd_ok]'s open row does not pin the type".      *)
  (* The row pins [fdst_nopipe] and has since the pipe landing; what was     *)
  (* missing was the EXPORT, and the five [UkRunSys.wp_uk_ecall_open*]       *)
  (* leaves carry it now.  So a program that opened its own descriptor takes *)
  (* [udepw_cl_nopipe] below and owes NOTHING -- which is what took          *)
  (* [udepw_law 21] out of [UkCat.cat_deps].                                 *)
  (* ------------------------------------------------------------------- *)
  Definition udepw_cl (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (st : fdstate) : iProp Σ :=
    (⌜forall (rb wb : bool) (gp : pipe_names),
        st <> FdOpen rb wb (FdPipe gp)⌝
     ∨ udepw_row N m pc 21 st)%I.

  Lemma udepw_cl_nonpipe (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (st : fdstate) :
    (forall (rb wb : bool) (gp : pipe_names), st <> FdOpen rb wb (FdPipe gp)) ->
    ⊢ udepw_cl N m pc st.
  Proof using . intros Hnp. rewrite /udepw_cl. iLeft. by iPureIntro. Qed.

  (* ...AND THE FREE ROUTE AT THE FACT THE OPEN LEAVES EXPORT (survey R4):
     [FdSlots.fdst_nopipe] is the shape [UsysMemOk.usys_fd_ok]'s open row
     states and the leaves hand out, and this is the one line that turns it
     into the left arm. *)
  Lemma udepw_cl_nopipe (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (st : fdstate) :
    fdst_nopipe st -> ⊢ udepw_cl N m pc st.
  Proof using .
    intros Hnp. apply udepw_cl_nonpipe.
    intros rb wb gp Heq. rewrite Heq in Hnp. exact Hnp.
  Qed.

  Lemma udepw_cl_of_udepw (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (st : fdstate) :
    udepw N m pc 21 -∗ udepw_cl N m pc st.
  Proof using .
    iIntros "H". rewrite /udepw_cl. iRight.
    iApply (udepw_row_of_udepw N m pc 21 st with "H").
  Qed.

  (* ...AND THE ROW-AWARE ONE, which is what a registered pipe end can pay
     ([UexecExecMint.udepw_row_of_reg_close] is the producer). *)
  Lemma udepw_cl_of_row (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (st : fdstate) :
    udepw_row N m pc 21 st -∗ udepw_cl N m pc st.
  Proof using . iIntros "H". rewrite /udepw_cl. by iRight. Qed.

  (* ...AND THE MINT, at the key the leaf has destructed its run into.  The
     reading of argument 0 against that key's own table is what the leaf's
     handle buys ([UserFd.ufd_agree]), and it is what turns "my descriptor
     is not a pipe" into "this key's close row is [emp]". *)
  Lemma udepw_cl_mint (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (st : fdstate) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
      (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname)
      (pidv : mword 32) :
    fd_st_of_key (m !!! Regidx (mword_of_int 10 : mword 5)) fdv = st ->
    udep -∗ my_pay gn (ukn_pay N) -∗ udepw_cl N m pc st -∗
    uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv ==∗
    uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
    sbundle_pay uslot 21 (ukn_pay N)
      (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all).
  Proof using .
    intros Hkey. iIntros "#Hdep #Hmp [%Hnp | Hsb] Hheap Hufd".
    - iFrame "Hheap Hufd".
      assert (Hnpk : ukey_nonpipe
                       (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)).
      { rewrite /ukey_nonpipe.
        (* the key's argument 0 IS a0, and its table IS [fdv]: both by
           [reflexivity] at [uvis_of_run] *)
        assert (Ha0 : tf_w (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all))
                        (tf_arg_idx 0) = m !!! Regidx (mword_of_int 10 : mword 5))
          by reflexivity.
        assert (Hfd : uvis_fd (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
                      = fdv) by reflexivity.
        rewrite Ha0 Hfd Hkey. exact Hnp. }
      iApply (udep_close_dep (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
                (ukn_pay N) Hnpk with "Hdep").
    - iApply (udepw_row_mint N m pc 21 st M pm sz fdv cw gn cs pidv Hkey
                with "Hdep Hmp Hsb Hheap Hufd").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* EXIT'S ROW IS THE RUN'S OWN, AND [urun] IS WHERE IT LIVES               *)
  (* (design/pipe.md, "The exit path").                                      *)
  (*                                                                         *)
  (* kexit closes every descriptor the dying process holds, so 2's bundle    *)
  (* row is [SpecFileclose.fileclose_cpays] of the KEY's table.  At a table   *)
  (* that holds no pipe row every payment is [emp]; at one that does, each    *)
  (* pipe row's payment is a close link OR the taint.  Neither fact is        *)
  (* about the exit instruction: both are about the TABLE, which is bound     *)
  (* by [urun]'s existential and changes only at a trap.  So this rides in    *)
  (* the run, where [UsysMemOk.usys_fd_ok_nopipe] re-establishes it at        *)
  (* every number but pipe(2), and an exit leaf takes no deposit at all --    *)
  (* which is why no verified program names [USYS_exit] in its deposit list.  *)
  (*                                                                         *)
  (* PERSISTENT, so a leaf that destructs its run keeps a copy for free.      *)
  (* ------------------------------------------------------------------- *)
  (* ...AND IT IS A RESOURCE NOW, NOT A PURE FACT (design/app-pipe.md SS2,
     lane PIPE-REG).  The left arm used to be [⌜fdv_nopipe fdv⌝] -- "this
     table holds no pipe end" -- which no program that has called pipe(2)
     can ever say again, so after pipe(2) only the TAINT was left and a
     verified program could not hold a pipe.  The left arm is now the
     REGISTRY: one persistent registration per row
     ([UexecSG.srow_reg], answered by [PipeReg.pipe_row_reg] at the one
     instance).  It is strictly weaker than the pure fact
     ([srow_regs_nopipe] derives it) and it is what a pipe-holding program
     carries: a registration is under a [□], so two rows on one pipe, a
     dup'd row and a forked child's copy of the table all pay from the same
     handle, and the fragment itself never has to be in the run.

     THE TAINT ARM STAYS, for two reasons and neither is the old one: the
     generic tier's supply buys it and would otherwise have to build a
     registry it has no names for, and [urun_nopipe_taint]'s statement
     names [riscv_kill_cred], which the class the left arm is stated at
     cannot (see this lane's finding).  A registered program never touches
     it.

     STILL PERSISTENT; NOT TIMELESS, and it never was declared timeless --
     [PipeReg.pipe_reg] is a [□] over a fupd-producing wand.  No consumer
     strips a later off it. *)
  Definition urun_nopipe (fdv : list fdstate) : iProp Σ :=
    (([∗ list] st ∈ fdv, srow_reg st) ∨ app_taint)%I.

  Global Instance urun_nopipe_persistent (fdv : list fdstate) :
    Persistent (urun_nopipe fdv).
  Proof using . rewrite /urun_nopipe. apply _. Qed.

  (* THE REGISTERED ARM, which is what a program that holds a pipe redeems
     its run with ([UkRunSys.wp_uk_ecall_pipe]'s post owes exactly this). *)
  Lemma urun_nopipe_regs (fdv : list fdstate) :
    ([∗ list] st ∈ fdv, srow_reg st) -∗ urun_nopipe fdv.
  Proof using . iIntros "H". rewrite /urun_nopipe. by iLeft. Qed.

  Lemma urun_nopipe_intro (fdv : list fdstate) :
    fdv_nopipe fdv -> ⊢ urun_nopipe fdv.
  Proof using .
    intros H. iApply urun_nopipe_regs. iApply (srow_regs_nopipe fdv H).
  Qed.

  Lemma urun_nopipe_closed (n : nat) : ⊢ urun_nopipe (replicate n FdClosed).
  Proof using . apply urun_nopipe_intro, fdv_nopipe_closed. Qed.

  Lemma urun_nopipe_taint (fdv : list fdstate) :
    app_taint -∗ urun_nopipe fdv.
  Proof using . iIntros "#H". rewrite /urun_nopipe. by iRight. Qed.

  (* THE ONE BIG-OP MOVE the three row-shaped readings below run on: a row
     overwritten by a REGISTERED one.  Out of range the insert is the
     identity, which is why no in-range premise is owed anywhere. *)
  Lemma urun_nopipe_regs_insert (fdv : list fdstate) (k : nat) (st : fdstate) :
    srow_reg st -∗ ([∗ list] s ∈ fdv, srow_reg s) -∗
    ([∗ list] s ∈ <[k := st]> fdv, srow_reg s).
  Proof using .
    iIntros "Hst Hr".
    destruct (decide (k < length fdv)%nat) as [Hlt | Hge].
    - apply lookup_lt_is_Some_2 in Hlt as [x Hx].
      iDestruct (big_sepL_insert_acc (fun _ s => srow_reg s) fdv k x Hx
                   with "Hr") as "[_ Hback]".
      iApply ("Hback" $! st with "Hst").
    - rewrite list_insert_ge; [ iExact "Hr" | lia ].
  Qed.

  (* ...and the row a dup COPIES, read off the table it copies from *)
  Lemma urun_nopipe_regs_lookup (fdv : list fdstate) (k : nat) (st : fdstate) :
    fdv !! k = Some st -> ([∗ list] s ∈ fdv, srow_reg s) -∗ srow_reg st.
  Proof using .
    intros Hk. iIntros "Hr".
    iDestruct (big_sepL_lookup_acc (fun _ s => srow_reg s) fdv k st Hk
                 with "Hr") as "[#Hst _]".
    iExact "Hst".
  Qed.

  (* ...at the TOTAL lookup, which out of range is [FdClosed] and registers
     itself *)
  Lemma urun_nopipe_regs_lookup_total (fdv : list fdstate) (k : nat) :
    ([∗ list] s ∈ fdv, srow_reg s) -∗ srow_reg (fdv !!! k).
  Proof using .
    iIntros "Hr". destruct (fdv !! k) as [x |] eqn:Hk.
    - rewrite (list_lookup_total_correct _ _ _ Hk).
      iApply (urun_nopipe_regs_lookup fdv k x Hk with "Hr").
    - assert (Hcl : fdv !!! k = FdClosed)
        by (rewrite list_lookup_total_alt Hk; reflexivity).
      rewrite Hcl. iApply (srow_reg_nopipe FdClosed fdst_nopipe_closed).
  Qed.

  (* ...and the quiet reading, for the leaves whose round did not touch the
     table at all *)
  (* ...AND THE ROW A PIPE PUTS IN, at the resource (design/app-pipe.md
     SS2).  This is what [UkRunSys.wp_uk_ecall_pipe]'s REGISTRAR redeems the
     run with: a registered row goes into the table and the run's reading
     survives, which is the whole of what pipe(2) used to break.  The taint
     arm answers at any row, as it always did. *)
  Lemma urun_nopipe_insert_reg (fdv : list fdstate) (k : nat) (st : fdstate) :
    srow_reg st -∗ urun_nopipe fdv -∗ urun_nopipe (<[k := st]> fdv).
  Proof using .
    iIntros "Hst Hr". rewrite /urun_nopipe.
    iDestruct "Hr" as "[Hr | #Ht]"; [ iLeft | by iRight ].
    iApply (urun_nopipe_regs_insert fdv k st with "Hst Hr").
  Qed.

  Lemma urun_nopipe_quiet (fdv fdv' : list fdstate) :
    fdv' = fdv -> urun_nopipe fdv -∗ urun_nopipe fdv'.
  Proof using . intros ->. iIntros "$". Qed.

  (* ...and the two row-shaped readings, for the leaves that hold the row
     rather than [usys_fd_ok] itself.  OPEN installs an inode or a device
     ([UsysMemOk.usys_fd_ok]'s open row now says so), CLOSE installs
     [FdClosed], and DUP copies a row the table already had. *)
  Lemma urun_nopipe_insert (fdv : list fdstate) (k : nat) (st : fdstate) :
    fdst_nopipe st -> urun_nopipe fdv -∗ urun_nopipe (<[k := st]> fdv).
  Proof using .
    intros Hst. rewrite /urun_nopipe. iIntros "[Hr | #Ht]"; [ iLeft | by iRight ].
    iApply (urun_nopipe_regs_insert fdv k st with "[] Hr").
    iApply (srow_reg_nopipe st Hst).
  Qed.

  Lemma urun_nopipe_dup (fdv : list fdstate) (k j : nat) (st : fdstate) :
    fdv !! k = Some st -> urun_nopipe fdv -∗ urun_nopipe (<[j := st]> fdv).
  Proof using .
    intros Hk. rewrite /urun_nopipe. iIntros "[#Hr | #Ht]"; [ iLeft | by iRight ].
    iApply (urun_nopipe_regs_insert fdv j st with "[] Hr").
    iApply (urun_nopipe_regs_lookup fdv k st Hk with "Hr").
  Qed.

  Lemma urun_nopipe_copy (fdv : list fdstate) (k j : nat) :
    urun_nopipe fdv -∗ urun_nopipe (<[j := fdv !!! k]> fdv).
  Proof using .
    rewrite /urun_nopipe. iIntros "[#Hr | #Ht]"; [ iLeft | by iRight ].
    iApply (urun_nopipe_regs_insert fdv j (fdv !!! k) with "[] Hr").
    iApply (urun_nopipe_regs_lookup_total fdv k with "Hr").
  Qed.

  (* THE ROUND'S EFFECT ON IT, at every number but pipe(2): the table the
     round returned holds no pipe row either.  This is the twin of
     [ucwd_auth_quiet] and [UserFd.ufd_auth_quiet] -- what a leaf runs to
     re-close its run -- except that here the table really does move and
     [UsysMemOk.usys_fd_ok_nopipe] is what carries the fact across. *)
  Lemma urun_nopipe_step (n : Z) (tf : list (mword 64)) (r : mword 64)
      (fdv fdv' : list fdstate) :
    n <> USYS_pipe -> usys_fd_ok n tf r fdv fdv' ->
    urun_nopipe fdv -∗ urun_nopipe fdv'.
  (* THE SAME CASE SPLIT [usys_fd_ok_nopipe] RUNS, with a resource instead
     of a Prop: every row of [fdv'] is a row of [fdv] or a row the arm
     itself says is not a pipe. *)
  Proof using .
    unfold usys_fd_ok. intros Hne Hok. iIntros "#Hr".
    destruct (decide (n = USYS_close)) as [_ | _].
    { destruct Hok as [Hok _].
      destruct (decide (uint r = 0)) as [_ | _]; subst;
        [ iApply (urun_nopipe_insert fdv _ FdClosed fdst_nopipe_closed with "Hr")
        | iExact "Hr" ]. }
    destruct (decide (n = USYS_dup)) as [_ | _].
    { destruct Hok as [(fd1 & _ & _ & _ & ->) | (_ & -> & _)];
        [ iApply (urun_nopipe_copy fdv (Z.to_nat (usys_argfd tf)) fd1 with "Hr")
        | iExact "Hr" ]. }
    destruct (decide (n = USYS_open)) as [_ | _].
    { destruct Hok as [(fd & rd & wr & t & _ & _ & He & Hop) | [_ ->]];
        [ | iExact "Hr" ].
      rewrite He.
      iApply (urun_nopipe_insert fdv fd (FdOpen rd wr t) Hop with "Hr"). }
    destruct (decide (n = USYS_pipe)) as [He | _]; [ exfalso; exact (Hne He) | ].
    subst. iExact "Hr".
  Qed.


  (* ===================================================================== *)
  (* THE RUN'S TWO TABLE ROWS, IN ONE CONJUNCT (lane OFF-HAND-3, R1).        *)
  (*                                                                        *)
  (* [urun_nopipe] is the first: whether the table holds a pipe end.  The    *)
  (* second is the OFFSET ROW -- if this record answers for its offsets,     *)
  (* every descriptor in the table is parked -- and it is here, bundled      *)
  (* with the first rather than beside it, because a hundred leaves          *)
  (* destructure [urun] positionally and hand the conjunct straight back to  *)
  (* [urun_close]: bundled, the new row costs those leaves NOTHING; spelled  *)
  (* beside it, it would cost every one of them a name.  The leaves that DO  *)
  (* move the table take the row through the steps below, which are          *)
  (* [urun_nopipe_*]'s twins one fact wider.                                 *)
  (*                                                                        *)
  (* THE ROW IS PURE AND GUARDED BY THE RECORD, never a disjunction with     *)
  (* the taint (lane OFF-HAND-2's "one thing"): the taint is the case that   *)
  (* NEEDS the fact, so an escape hatch on the right would make the row      *)
  (* useless exactly where it is spent.                                      *)
  (* ===================================================================== *)
  (* ...AND THE OFFSET HALF OF IT IS GONE (lane OFF-HAND-6's H3 emptied
     [urun_parked_row] and lane OFF-LINK-2's L6 deleted it): the rows a run
     carries between traps are about PIPES and nothing else.  A held row's
     coupling is the box's arm and the node's link (design/app-file.md SS3),
     neither of which any tier has to be told about. *)
  Definition urun_rows (N : uk_names Σ) (fdv : list fdstate) : iProp Σ :=
    urun_nopipe fdv.

  Global Instance urun_rows_persistent (N : uk_names Σ) (fdv : list fdstate) :
    Persistent (urun_rows N fdv).
  Proof using . rewrite /urun_rows. apply _. Qed.

  (* the projection, for the rows that are still stated at the pipe fact
     alone (exit's deposit) *)
  Lemma urun_rows_nopipe (N : uk_names Σ) (fdv : list fdstate) :
    urun_rows N fdv -∗ urun_nopipe fdv.
  Proof using . iIntros "$". Qed.

  Lemma urun_rows_intro (N : uk_names Σ) (fdv : list fdstate) :
    fdv_nopipe fdv -> ⊢ urun_rows N fdv.
  Proof using .
    intros Hnp. rewrite /urun_rows. iApply (urun_nopipe_intro fdv Hnp).
  Qed.

  Lemma urun_rows_closed (N : uk_names Σ) (n : nat) :
    ⊢ urun_rows N (replicate n FdClosed).
  Proof using .
    apply urun_rows_intro, fdv_nopipe_closed.
  Qed.

  (* THE TAINT'S PIPE ROW, with the offset row still owed.  A tainted
     process pays the pipe half out of the kill credential; the offset half
     is not tainted-escapable and has to come from the table. *)
  Lemma urun_rows_taint (N : uk_names Σ) (fdv : list fdstate) :
    app_taint -∗ urun_rows N fdv.
  Proof using .
    iIntros "#H". rewrite /urun_rows. iApply (urun_nopipe_taint fdv with "H").
  Qed.

  (* THE ROUND'S EFFECT ON BOTH ROWS, at every number but pipe(2).  The
     offset half is [UsysMemOk.usys_fd_ok_held], which is free at every
     number but dup -- see its note: a dup COPIES its argument's row, so a
     copy of a HELD one lands on a slot the record may not hold.  The
     guard is free at every all-parked table and is what the two dup
     leaves pay. *)
  Lemma urun_rows_step (N : uk_names Σ) (n : Z) (tf : list (mword 64))
      (r : mword 64) (fdv fdv' : list fdstate) :
    n <> USYS_pipe -> usys_fd_ok n tf r fdv fdv' ->
    urun_rows N fdv -∗ urun_rows N fdv'.
  Proof using .
    intros Hne Hok. iIntros "Hnp". rewrite /urun_rows.
    iApply (urun_nopipe_step n tf r fdv fdv' Hne Hok with "Hnp").
  Qed.

  Lemma urun_rows_quiet (N : uk_names Σ) (fdv fdv' : list fdstate) :
    fdv' = fdv -> urun_rows N fdv -∗ urun_rows N fdv'.
  Proof using . intros ->. iIntros "$". Qed.

  (* ...and the three row-shaped readings, for the leaves that hold the row
     rather than [usys_fd_ok] itself. *)
  Lemma urun_rows_insert (N : uk_names Σ) (fdv : list fdstate) (k : nat)
      (st : fdstate) :
    fdst_nopipe st ->
    urun_rows N fdv -∗ urun_rows N (<[k := st]> fdv).
  Proof using .
    intros Hnp. iIntros "Hn". rewrite /urun_rows. iApply (urun_nopipe_insert fdv k st Hnp with "Hn").
  Qed.

  (* ...AND DUP'S, WITH ITS ONE GUARD (lane OFF-HAND-4, S1).  The copied
     row has to be parked, because the slot fdalloc chose is not one the
     record can be said to hold -- [UsysMemOk.usys_fd_ok_held]'s note.
     Free at every all-parked table, which is what the two dup leaves
     derive it from. *)
  Lemma urun_rows_dup (N : uk_names Σ) (fdv : list fdstate) (k j : nat)
      (st : fdstate) :
    fdv !! k = Some st ->
    urun_rows N fdv -∗ urun_rows N (<[j := st]> fdv).
  Proof using .
    intros Hk. iIntros "Hn". rewrite /urun_rows. iApply (urun_nopipe_dup fdv k j st Hk with "Hn").
  Qed.

  Lemma urun_rows_copy (N : uk_names Σ) (fdv : list fdstate) (k j : nat) :
    urun_rows N fdv -∗ urun_rows N (<[j := fdv !!! k]> fdv).
  Proof using .
    iIntros "Hn". rewrite /urun_rows. iApply (urun_nopipe_copy fdv k j with "Hn").
  Qed.

  (* ...AND WHAT IT BUYS: exit's deposit at the key the leaf has destructed
     its run into, off the [udep] the same run carries and nothing else. *)
  Lemma udep_exit_run (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
      (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname)
      (pidv : mword 32) :
    udep -∗ urun_rows N fdv ==∗
    sbundle_pay uslot USYS_exit (ukn_pay N)
      (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all).
  Proof using .
    iIntros "#Hdep Hrows".
    iDestruct (urun_rows_nopipe N fdv with "Hrows") as "Hnpx".
    rewrite /urun_nopipe. iDestruct "Hnpx" as "[Hr | #Ht]".
    - iApply (udep_exit_regs (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
                (ukn_pay N) with "Hr Hdep").
    - iApply (udep_exit_taint (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
                (ukn_pay N) with "Ht Hdep").
  Qed.

  (* THE EXEC DEPOSIT'S CARRIER, and why it is key-free too.  exec is the
     one number the law above excludes -- its bundle reads argv out of the
     key's image -- so its deposit takes the EXPLICIT route.  But the key an
     exec ecall traps from is built by the walk that reaches it ([M], [pm],
     [sz], [fdv], [cw] bound by [urun]'s existential, the register file by
     the caller's own instruction sequence), so no lemma up the chain can
     NAME it: what a program that execs carries is the bundle AT EVERY KEY,
     persistently.  This is the ARM's spelling of the enriched tier's own
     supplier: a program that execs takes it as an explicit premise and
     hands it down to its exec leaf, and the kernel-side constructor -- which
     sits above the file-system tower and holds the process's exec bundle --
     is what pays it.

     NOT IN [urun].  A conjunct there would make EVERY program owe the exec
     bundle at every key, which is the GAP-premise trap [udep]'s note
     refutes one number over: a constraining application (echo, at
     [Dsup := emp]) could not build a [urun] at all. *)
  (* ...AND IT NAMES THE PAYLOAD, WHICH FOR THIS SUPPLIER IS THE TRIVIAL
     ONE (EXEC-PAY).  exec's bundle READS the depositing process's own exit
     payload -- it is what the kernel hands the new image's slot
     ([SpecKexec.exec_slot_pre]'s two wands, and the [Q (-1)] beside the
     pay fact) -- so a supplier can no longer hand a bundle at SOME family
     and let the leaf re-key it ([UexecSG.sbundle_at_at] no longer licenses
     that at exec): it names the payload, exactly as read's mint does.
     [uxsup] is the supplier a program that answers for NOTHING carries,
     and such a program's payload is [fun _ => True] -- so this is the
     bundle at that payload, and its two consumers below take
     [ukn_triv].  A process whose exit owes something real (sh, once it
     holds the console reader) execs on a PINNED supply instead
     ([UkInit.init_exec_sup]'s shape), which names its own payload. *)
  (* ...AT A CHOSEN PAYLOAD (GENERIC-PAY).  Once the generic slot exists at
     a CONSTANT payload, a program whose exit owes a real resource can
     take this supplier too: the bundle names the payload the exec'ing
     process pays the trap's payment row at, and the kernel relays that
     resource to the new image's slot ([SpecKexec.exec_slot_pre]).  [uxsup]
     is this at the trivial payload, which is what a program answering for
     NOTHING carries. *)
  Definition uxsup_at (Q : Z -> iProp Σ) : iProp Σ :=
    (□ ∀ W : uvis, sbundle_pay uslot USYS_exec Q W)%I.

  Global Instance uxsup_at_persistent Q : Persistent (uxsup_at Q).
  Proof using . rewrite /uxsup_at. apply _. Qed.

  Definition uxsup : iProp Σ := uxsup_at (fun _ => True)%I.

  Global Instance uxsup_persistent : Persistent uxsup.
  Proof using . rewrite /uxsup. apply _. Qed.

  (* what an exec leaf's caller does with it: the explicit disjunct of
     [udepw], at whatever key the walk has reached *)
  Lemma udepw_of_uxsup (N : uk_names Σ) `{!ukn_triv N}
      (m : regfile) (pc : mword 64) :
    uxsup -∗ udepw N m pc USYS_exec.
  Proof using .
    iIntros "#Hx" (M pm sz fdv cw gn cs pidv) "_ Hh Hf". iFrame "Hh Hf". iRight.
    rewrite (ukn_triv_eq (N := N)). iApply "Hx".
  Qed.

  (* ...AND THE SAME AT THE RECORD'S OWN PAYLOAD, which is what a program
     at [ukn_const] takes in place of [ukn_triv] (GENERIC-PAY).  Nothing
     about the payload is read here: the supplier already names it. *)
  Lemma udepw_of_uxsup_at (N : uk_names Σ)
      (m : regfile) (pc : mword 64) :
    uxsup_at (ukn_pay N) -∗ udepw N m pc USYS_exec.
  Proof using .
    iIntros "#Hx" (M pm sz fdv cw gn cs pidv) "_ Hh Hf". iFrame "Hh Hf". iRight.
    iApply "Hx".
  Qed.

  (* ...AND WHAT A SUPPLIER THAT ONLY HAS THE BUNDLE AT ONE WORKING
     DIRECTORY DOES INSTEAD.  [uxsup] asks for exec's bundle at EVERY key;
     an application whose exec claim is about a PATH cannot pay that,
     because a path names a file only relative to the directory it is
     resolved from.  What such an application has is the bundle at every
     key whose cwd is the ONE inum its process is at -- and that is NOT a
     [udepw], because the [cw] a [udepw] must answer at is bound by its own
     ∀ and only agreement against [urun]'s half can pin it.  The agreement
     therefore happens in the LEAF, which has destructed [urun] and holds
     that half: see [UkRunSys.wp_uk_ecall_exec_at_cwd], which takes the
     program's half and a [c]-indexed deposit in place of a [udepw] and
     hands the half back. *)

  (* THE CWD-FIXED DEPOSIT.  [udepw] with the working directory FIXED at
     [c] -- the [∀ cw] gone -- and the SAME LOAN of the two authorities.

     THE LOAN IS THE WHOLE POINT.  A supplier that answers at every key is
     free to ignore what it is lent ([udepw_at_of_bundle] below is that
     supplier).  A PINNED bundle is not: it owes [exec_path_of M pv pl] --
     the path string read out of the program's own rodata, which is a fact
     about [M] and reaches a supplier through [UserHeap.uheap_text] -- and
     [length sts = NOFILE] / [fd_lowest_closed sts = None], which are
     readings of [ufd_auth]'s list.  Both are facts about the very key the
     bundle is stated at, so the only way to state them is to hand the
     supplier the authorities they are read off and take them back beside
     the bundle. *)
  Definition udepw_at (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) (c : Z) : iProp Σ :=
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
       (fdv : list fdstate) (gn : gname) (cs : gset gname) (pidv : mword 32),
       my_pay gn (ukn_pay N) -∗
       (* ...AND WHETHER THE KEY'S TABLE HOLDS A PIPE ROW, LENT WITH THEM
          (design/pipe.md, "The exit path").  A pinned exec supply builds
          the NEW image's entry, and an entry constructor now asks whether
          the process's table holds a pipe row -- which is a fact about the
          exec'ING process's table ([SpecKexec.kexec_image_ok_fd]) and
          therefore about the very [fdv] this loan is at.  The leaf has it
          in its run and it is persistent, so lending it costs nothing and
          nothing comes back. *)
       urun_rows N fdv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
       (⌜psok n /\ n <> USYS_exec⌝
        ∨ sbundle_pay uslot n (ukn_pay N)
            (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all)))%I.

  (* [udepw] IS THE ∀-CWD FORM, one direction.  The two differ only in
     where the [cw] binder sits, so the equivalence holds both ways; this
     is the direction a caller holding a [udepw] needs, and stating it
     rather than redefining [udepw] as [∀ cw, udepw_at … cw] is what keeps
     the ∀-ORDER at [udepw]'s twenty-odd use sites ([iDestruct ("Hsb" $! M
     pm sz fdv cw)]) unmoved. *)
  Lemma udepw_at_of_udepw (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) (c : Z) :
    udepw N m pc n -∗ udepw_at N m pc n c.
  Proof using .
    iIntros "Hd" (M pm sz fdv gn cs pidv) "Hmp _ Hh Hf".
    iApply ("Hd" $! M pm sz fdv c gn cs pidv with "Hmp Hh Hf").
  Qed.

  (* ...AND THE SUPPLIER THAT IGNORES THE LOAN: a caller that already has
     the bundle at every [(M, pm, sz, fdv)] of this one cwd hands it back
     unread.  [udepw_at] is WEAKER to supply than the bare family, which is
     why the leaf can take it in the bare one's place. *)
  (* AT EVERY NUMBER BUT read (R1): the supplier hands a bundle at SOME
     family and the deposit is wanted at the leaf's own payload, which is a
     free re-keying at every branch that does not read one. *)
  Lemma udepw_at_of_bundle (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) (c : Z) :
    n <> USYS_read -> n <> USYS_exec ->
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
       (fdv : list fdstate) (gn : gname) (cs : gset gname) (pidv : mword 32),
       sbundle uslot n (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all)) -∗
    udepw_at N m pc n c.
  Proof using .
    intros Hne Hnx. iIntros "Hb" (M pm sz fdv gn cs pidv) "_ _ Hh Hf".
    iFrame "Hh Hf". iRight.
    iApply (sbundle_pay_of_sbundle uslot n (ukn_pay N) _ Hne Hnx). iApply "Hb".
  Qed.

  (* the trivial supplier at the ∀-key form, through the two above *)
  Lemma udepw_at_of_uxsup (N : uk_names Σ) `{!ukn_triv N}
      (m : regfile) (pc : mword 64) (c : Z) :
    uxsup -∗ udepw_at N m pc USYS_exec c.
  Proof using .
    iIntros "#Hx" (M pm sz fdv gn cs pidv) "_ _ Hh Hf".
    iFrame "Hh Hf". iRight. rewrite (ukn_triv_eq (N := N)). iApply "Hx".
  Qed.

  (* ...AND THE TRIVIAL SUPPLIER READ AT A TRIVIAL RECORD'S OWN PAYLOAD:
     what a caller holding [uxsup] hands a lemma stated at [uxsup_at
     (ukn_pay N)] when its own record pays nothing (sh's forked child,
     [UkFork.wp_uk_ecall_fork_any]'s arm). *)
  Lemma uxsup_at_triv (N : uk_names Σ) `{!ukn_triv N} :
    uxsup -∗ uxsup_at (ukn_pay N).
  Proof using . rewrite (ukn_triv_eq (N := N)). iIntros "H". iExact "H". Qed.

  (* ...and the same at the record's own payload (GENERIC-PAY) *)
  Lemma udepw_at_of_uxsup_at (N : uk_names Σ)
      (m : regfile) (pc : mword 64) (c : Z) :
    uxsup_at (ukn_pay N) -∗ udepw_at N m pc USYS_exec c.
  Proof using .
    iIntros "#Hx" (M pm sz fdv gn cs pidv) "_ _ Hh Hf".
    iFrame "Hh Hf". iRight. iApply "Hx".
  Qed.

  (* THE LEAF'S USE OF IT, [udepw_mint]'s shape at the fixed cwd *)
  Lemma udepw_at_mint (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) (c : Z) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm)
      (sz : Z) (fdv : list fdstate) (gn : gname) (cs : gset gname) (pidv : mword 32) :
    udep -∗ my_pay gn (ukn_pay N) -∗ urun_rows N fdv -∗ udepw_at N m pc n c -∗
    uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv ==∗
    uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
    sbundle_pay uslot n (ukn_pay N) (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all).
  Proof using .
    iIntros "#Hdep #Hmp #Hnpw Hsb Hheap Hufd".
    iDestruct ("Hsb" $! M pm sz fdv gn cs with "Hmp Hnpw Hheap Hufd")
      as "(Hheap & Hufd & [%Hok | Hb])"; iFrame "Hheap Hufd";
      [ iApply (udep_dep n _ (ukn_pay N) (proj1 Hok) (proj2 Hok) with "Hdep")
      | by iModIntro ].
  Qed.


  (* ===================================================================== *)
  (* THE CWD-FIXED exec DEPOSIT THAT REFUNDS (app-echo.md, lane KILL-PAY,   *)
  (* K4(a), ruling R-A).                                                    *)
  (*                                                                       *)
  (* [udepw_at] is used at exec and nowhere else, and an exec that FAILS    *)
  (* comes back to a process that has spent into the exec deposit the very  *)
  (* resource its own [exit(1)] would need, so the kernel gives it back:    *)
  (* the arm's post at exec is [UexecSG.spost_at_exec], a wand from “the    *)
  (* answer was -1” to the family's own refund.                             *)
  (*                                                                       *)
  (* WHAT THE INDEX WOULD HAVE BEEN, and is not: the refund itself.  The    *)
  (* family is existential here -- a supplier hands a bundle at SOME [f] -- *)
  (* so a leaf cannot NAME [sexec_refund f], and indexing the deposit by it *)
  (* would put a resource-shaped parameter through every pinned supply.     *)
  (* What the deposit carries instead is the one consequence a leaf wants:  *)
  (* the refund PAYS THIS RECORD'S EXIT at the kill status.  It is          *)
  (* persistent, so it costs a [□]-boxed supply nothing; at [ukn_triv] it   *)
  (* is [_ -∗ True], and at init's pinned supply for /sh the refund IS the  *)
  (* lease beside the position, so the wand is a projection.                *)
  (* ===================================================================== *)
  Definition udepw_at_ref (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (c : Z) : iProp Σ :=
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
       (fdv : list fdstate) (gn : gname) (cs : gset gname) (pidv : mword 32),
       my_pay gn (ukn_pay N) -∗
       (* ...AND WHETHER THE KEY'S TABLE HOLDS A PIPE ROW, LENT WITH THEM
          (design/pipe.md, "The exit path").  A pinned exec supply builds
          the NEW image's entry, and an entry constructor now asks whether
          the process's table holds a pipe row -- which is a fact about the
          exec'ING process's table ([SpecKexec.kexec_image_ok_fd]) and
          therefore about the very [fdv] this loan is at.  The leaf has it
          in its run and it is persistent, so lending it costs nothing and
          nothing comes back. *)
       urun_rows N fdv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
       sbundle_pay_ref uslot (ukn_pay N)
         (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all))%I.

  (* ...AND THE FORGETFUL DIRECTION, for a leaf that wants no refund *)
  Lemma udepw_at_of_ref (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (c : Z) :
    udepw_at_ref N m pc c -∗ udepw_at N m pc USYS_exec c.
  Proof using .
    rewrite /udepw_at_ref /udepw_at.
    iIntros "Hd" (M pm sz fdv gn cs pidv) "Hmp #Hnpw Hh Hf".
    iDestruct ("Hd" $! M pm sz fdv gn cs pidv with "Hmp Hnpw Hh Hf")
      as "(Hh & Hf & Hb)".
    iFrame "Hh Hf". iRight.
    iApply (sbundle_pay_of_ref with "Hb").
  Qed.

  (* the trivial supplier pays it: at [ukn_triv] the refund wand is free *)
  Lemma udepw_at_ref_of_uxsup (N : uk_names Σ) `{!ukn_triv N}
      (m : regfile) (pc : mword 64) (c : Z) :
    uxsup -∗ udepw_at_ref N m pc c.
  Proof using .
    iIntros "#Hx" (M pm sz fdv gn cs pidv) "_ _ Hh Hf".
    iFrame "Hh Hf".
    iAssert (sbundle_pay uslot USYS_exec (fun _ => True)%I
               (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all)) as "Hb";
      [ iApply "Hx" | ].
    iDestruct "Hb" as (f) "[%Hpay Hb]".
    rewrite (ukn_triv_eq (N := N)).
    rewrite /sbundle_pay_ref.
    iExists f. iSplitR; [ done | ].
    iSplitR; [ iIntros "!> _"; done | ].
    iExact "Hb".
  Qed.

  (* THE FAMILY-NAMED DEPOSIT AT A FIXED WORKING DIRECTORY.
     [udepwf] is to [udepw] what this is to [udepw_at]: the two axes are
     INDEPENDENT and a PINNED OPEN needs both at once.

       NAMING THE FAMILY is what a leaf that HANDS THE POST BACK needs --
         the program reads its receipt at the family it deposited, and
         [udepw]'s existential loses it ([udepwf]'s note).
       FIXING THE CWD is what a PINNED bundle needs -- a pin is about a
         PATH, and "console" names a file only relative to the directory it
         is resolved from, so a supplier built out of
         [PinnedOpen.pinned_open_bundle] can answer at ONE [cw] and no
         other.  [udepwf]'s own ∀ binds [cw], so it cannot be supplied.

     THE LOAN IS [udepw_at]'s, for its reason: a pinned open owes
     [ArgPath.arg_path_of M pv pl] -- the path string read out of the
     program's own rodata through [UserHeap.uheap_text] -- which is a fact
     about the very key the bundle is stated at.  The agreement between the
     [c] here and the key's own cwd happens in the LEAF, which has
     destructed [urun] and holds both halves ([UkRunSys.
     wp_uk_ecall_exec_at_cwd] is the landed instance of that move). *)
  Definition udepwf_at (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) (fdep : sfam) (c : Z) : iProp Σ :=
    (⌜sexit_pay fdep = ukn_pay N⌝ ∗
     ∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
       (fdv : list fdstate) (gn : gname) (cs : gset gname) (pidv : mword 32),
       my_pay gn (ukn_pay N) -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
       sbundle_at uslot n fdep (uvis_of_run m pc M pm sz fdv c gn cs pidv false secc_all))%I.

  (* [udepwf] IS THE ∀-CWD FORM, in the direction a caller that has one
     needs -- [udepw_at_of_udepw]'s twin, and stated rather than made the
     definition for the same reason: the ∀-ORDER at [udepwf]'s use sites
     stays put. *)
  Lemma udepwf_at_of_udepwf (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) (fdep : sfam) (c : Z) :
    udepwf N m pc n fdep -∗ udepwf_at N m pc n fdep c.
  Proof using .
    rewrite /udepwf /udepwf_at. iIntros "[%Hpay Hd]".
    iSplitR; [ done |].
    iIntros (M pm sz fdv gn cs pidv) "Hmp Hh Hf".
    iApply ("Hd" $! M pm sz fdv c gn cs pidv with "Hmp Hh Hf").
  Qed.

  (* ...AND THE FORGETFUL DIRECTION, which is what a leaf that DISCARDS its
     post takes: [udepw_at]'s explicit disjunct at the named family. *)
  Lemma udepwf_at_udepw_at (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) (fdep : sfam) (c : Z) :
    udepwf_at N m pc n fdep c -∗ udepw_at N m pc n c.
  Proof using .
    rewrite /udepwf_at /udepw_at. iIntros "[%Hpay Hd]".
    iIntros (M pm sz fdv gn cs pidv) "Hmp _ Hh Hf".
    iDestruct ("Hd" $! M pm sz fdv gn cs pidv with "Hmp Hh Hf")
      as "(Hh & Hf & Hb)".
    iFrame "Hh Hf". iRight. iExists fdep.
    iSplitR; [ done | iExact "Hb" ].
  Qed.

  (* THE LEDGER-FIXED EXPLICIT DEPOSIT (app-echo.md, lane SH-LINE, S4).
     [udepwf_at] fixes the working directory because a PINNED OPEN is about
     a path; this one fixes the low [NSTD] descriptor states because a
     CONSOLE READ is about a descriptor.  Row 5's bundle is
     [SpecFileread.fileread_in] at [FdSlots.fd_st_of_key (xk_a W 0)
     (uvis_fd W)], so which ARM the supplier has to answer is decided by
     the key's own descriptor table -- and a supplier holding the reader
     token has to answer the CONSOLE arm and no other, because that is the
     only arm the token is spent on.  [udepwf]'s own ∀ binds [fdv], so it
     cannot be told; the leaf, which has destructed [urun] and holds both
     the authority and the caller's ledger, can ([UserFd.ustd_agree]), and
     that is why the fact enters as a premise INSIDE the ∀ here.

     THE CWD IS STILL ∀-BOUND: a read's bundle reads no path. *)
  Definition udepwf_std (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) (fdep : sfam) (l : list fdstate) : iProp Σ :=
    (⌜sexit_pay fdep = ukn_pay N⌝ ∗
     ∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
       (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname)
       (pidv : mword 32),
       ⌜take NSTD fdv = l⌝ -∗
       my_pay gn (ukn_pay N) -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
       sbundle_at uslot n fdep (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all))%I.

  (* [udepwf] IS THE ∀-LEDGER FORM, in the direction a caller that has one
     needs -- [udepwf_at_of_udepwf]'s twin. *)
  Lemma udepwf_std_of_udepwf (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) (fdep : sfam) (l : list fdstate) :
    udepwf N m pc n fdep -∗ udepwf_std N m pc n fdep l.
  Proof using .
    rewrite /udepwf /udepwf_std. iIntros "[%Hpay Hd]".
    iSplitR; [ done |].
    iIntros (M pm sz fdv cw gn cs pidv) "_ Hmp Hh Hf".
    iApply ("Hd" $! M pm sz fdv cw gn cs pidv with "Hmp Hh Hf").
  Qed.

  (* THE TWO IDENTITY AUTHORITIES, AS ONE CONJUNCT (lane TRAP-ROWS-4, B).
     [uch_auth] ties a program's [UserChildren.uch] to the set the key is
     at; [upid_auth] does the same for the pid, which [urun] binds
     existentially and which nothing the program holds could name until
     now.  Pinning the pid is what lets a caller say "my pid is [p]" and
     have that mean something about the key its next ecall traps from --
     and that is what makes wait's reaping arm redeemable
     ([UkRunSys.wp_uk_ecall_wait_null_live]).
       THEY ARE ONE CONJUNCT AND NOT TWO on purpose: a hundred leaves
     destructure [urun] positionally and hand this very hypothesis back to
     [urun_close], and none of them reads either half.  Bundled, the pid
     authority costs those leaves NOTHING; spelled beside it, it would cost
     every one of them a name.  The four leaves that DO read a half take it
     through the accessors below.
       AT [bv_unsigned pidv]: the ghost is over [Z], because a
     [ghost_varG Σ (mword 32)] would be a new class in this tier -- see
     [UserChildren.upid_auth]'s note. *)
  Definition urun_ids (N : uk_names Σ) (cs : gset gname) (pidv : mword 32)
      : iProp Σ :=
    (uch_auth (ukn_ch N) cs ∗ upid_auth (ukn_pid N) (bv_unsigned pidv))%I.

  Global Instance urun_ids_timeless N cs pidv : Timeless (urun_ids N cs pidv).
  Proof using . rewrite /urun_ids. apply _. Qed.

  Lemma urun_ids_intro (N : uk_names Σ) (cs : gset gname) (pidv : mword 32) :
    uch_auth (ukn_ch N) cs -∗ upid_auth (ukn_pid N) (bv_unsigned pidv) -∗
    urun_ids N cs pidv.
  Proof using . iIntros "H1 H2". iFrame "H1 H2". Qed.

  (* the children half, LENT: the fork and wait leaves read it against the
     program's own fragment and give it straight back *)
  Lemma urun_ids_ch (N : uk_names Σ) (cs : gset gname) (pidv : mword 32) :
    urun_ids N cs pidv -∗
    uch_auth (ukn_ch N) cs ∗
    (∀ cs' : gset gname,
       uch_auth (ukn_ch N) cs' -∗ urun_ids N cs' pidv).
  Proof using .
    iIntros "[Hch Hpid]". iSplitL "Hch"; [ iExact "Hch" | ].
    iIntros (cs') "Hch". iFrame "Hch Hpid".
  Qed.

  (* ...and the pid half, LENT the same way.  A borrow, because what it is
     spent on is an agreement ([UserChildren.upid_agree]) -- a process's pid
     never moves. *)
  Lemma urun_ids_pid (N : uk_names Σ) (cs : gset gname) (pidv : mword 32) :
    urun_ids N cs pidv -∗
    upid_auth (ukn_pid N) (bv_unsigned pidv) ∗
    (upid_auth (ukn_pid N) (bv_unsigned pidv) -∗ urun_ids N cs pidv).
  Proof using .
    iIntros "[Hch Hpid]". iSplitL "Hpid"; [ iExact "Hpid" | ].
    iIntros "Hpid". iFrame "Hch Hpid".
  Qed.

  Definition urun (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) : iProp Σ :=
    (∃ (xi : CtxIdDefs.CurCtx) (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ)
       (Rut : uptd -> iProp Σ) (sz : Z)
       (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (fdv : list fdstate)
       (* THE WORKING DIRECTORY IS HIDDEN TOO, exactly as the image, the
          break and the descriptor view are: a program that never looks at
          its cwd should not have to name it.  A program that DOES holds
          [UserCwd.ucwd] outside, and the authority below is what ties that
          half to the [cw] the key is at. *)
       (cw : Z)
       (* ...AND SO ARE THE TWO WAIT-EXIT READINGS.  The process's own
          generation [gn] has no resource beside it -- nothing the program
          holds names it -- and its live children [cs] do: the authority
          below is what ties a program's [UserChildren.uch] to the set the
          key is at. *)
       (gn : gname) (cs : gset gname) (pidv : mword 32),
       ⌜ loop_ok C pt ⌝ ∗ ⌜ perm_of (ud_um pt) sz = pm ⌝ ∗
       (* ...AND THE FILL IS EMPTY (lane KILL-PAY, milestone LAZY-ROW): the
          slot guard's own row, read off the guard at the constructor and
          carried between instructions so the store and load leaves can
          REFUTE their page-fault arms.  The run's key is at
          [uvis_lazy = false], so the row arrives without its antecedent. *)
       ⌜ lazy_free (ud_um pt) sz ⌝ ∗
       (* A6.140: the residue-token accessor rides the bundle as a PURE
          fact, so a leaf that re-enters [ukc] can hand it back over *)
       ⌜ forall pt' : uptd,
           ⊢ Rut pt' -∗ TsoCtx.own_context (CID := h) (cur_ctx (CurCtx := xi)) ∗
                        (TsoCtx.own_context (CID := h) (cur_ctx (CurCtx := xi)) -∗ Rut pt') ⌝ ∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗
       ustack (ukn_d N) (m !!! Regidx csp_rs1) avail ∗
       (* THE PROGRAM'S OWN VIEW OF ITS DESCRIPTORS, keyed at the very [fdv]
          the bundle is at.  This is the conjunct that makes a user-level fd
          fact possible: [urun] is where [fdv] is bound and carried between
          instructions, so it is the only place an authority can be pinned
          to it.  The HANDLES ([UserFd.ufd]) live outside, in the program's
          own context, which is what lets a proof say "I hold fd 1" without
          naming the whole table.
          Note this is NOT [Rfd] one line down: [Rfd] is the KERNEL's
          fragment bundle, chosen by the loop and handed back whole at every
          trap, and a program never learns its ghost name. *)
       ufd_auth (ukn_fd N) fdv ∗
       (* THE PROGRAM'S OWN VIEW OF ITS WORKING DIRECTORY, keyed at the very
          [cw] the bundle is at -- the descriptor authority's twin, one
          value wide.  [cw] is bound by this existential, so this is the
          only place a half can be pinned to it, and pinning it is what
          lets a program say "my working directory is inum [c]" and have
          that mean something about the key its next ecall traps from. *)
       ucwd_auth (ukn_cwd N) cw ∗
       (* THE PROGRAM'S OWN VIEW OF ITS CHILDREN, keyed at the very [cs]
          the bundle is at -- the cwd authority's twin, one set wide.  A
          program learns which children it has only by agreement against
          this half, which is what makes wait(2)'s two arms mean
          something. *)
       urun_ids N cs pidv ∗
       (* ...AND THE PROCESS'S OWN KNOWLEDGE OF ITS EXIT PAYLOAD, at the
          generation the key carries.  PERSISTENT, so it costs no leaf
          anything to thread; it is here because [gn] is bound by this
          existential and this is therefore the only place the record's
          [ukn_pay] can be tied to the process's actual generation.  It is
          what exit's leaf pays the trap loop's deposit row with
          ([UexecRet.uexec_pay_dep]), and it is what an entry constructor
          receives and mints the record at. *)
       my_pay gn (ukn_pay N) ∗
       (* THE PAYLOAD AT THE KILL STATUS IS NOT HERE ANY MORE (lane
          SELF-KILL, P6).  The run used to carry [app_taint -∗
          ukn_pay N (-1)] between traps, hand it to the kernel at every
          entry and take it back at every resume.  Nothing is deposited at
          a trap now -- the price of a KILL is the killer's, paid into
          <p->lock>'s own killed row ([SchedCtx.kill_row]) -- so the row is
          gone and a program that owes a payload at its own [exit] takes it
          as a premise of the exit leaf instead
          ([UkRunSys.wp_uk_ecall_exit]). *)
       udep ∗
       (* ...AND WHETHER THE TABLE HOLDS A PIPE ROW (design/pipe.md, "The
          exit path").  PERSISTENT and PURE on its left arm, and it is here
          because [fdv] is bound by this existential: exit's bundle row is
          the close payments of the KEY's table, so the fact that decides
          it is a fact about the run, re-established at every trap out of
          [UsysMemOk.usys_fd_ok_nopipe] ([urun_nopipe_step]).  With it
          here, [UkRunSys.wp_uk_ecall_exit] and the fault leaves' owed side
          take no deposit at all. *)
       urun_rows N fdv ∗
       uvb (CID := h) (XI := xi) C pt Rfd Rut sz pm fdv cw gn cs pidv false secc_all M m pc)%I.

  (* THE ROUND'S EFFECT ON THE CWD, AT EVERY NUMBER BUT CHDIR.  A leaf
     re-closes [urun] at the [cw'] the round resumed the process at, and
     [UsysMemOk.usys_cwd_ok_quiet] says that is the [cw] it trapped from.
     Re-keying the engine's half by that equation is the ONLY thing a leaf
     has to do about the working directory, and it is why the program's
     half rides through every call untouched.  [UserFd.ufd_auth_quiet]'s
     twin, one value wide. *)
  Lemma ucwd_auth_quiet (N : uk_names Σ) (cw cw' : Z) :
    cw' = cw -> ucwd_auth (ukn_cwd N) cw -∗ ucwd_auth (ukn_cwd N) cw'.
  Proof using . intros ->. iIntros "$". Qed.

  (* THE MOVER, for the day a chdir leaf exists.  [UsysMemOk.usys_cwd_ok]
     has exactly one non-quiet row and no leaf takes it yet; when one does,
     this is the step it runs, with the new inum coming off the row. *)
  Lemma ucwd_move (N : uk_names Σ) (c c' : Z) :
    ucwd_auth (ukn_cwd N) c -∗ ucwd (ukn_cwd N) c ==∗
    ucwd_auth (ukn_cwd N) c' ∗ ucwd (ukn_cwd N) c'.
  Proof using . iApply ucwd_update. Qed.

  (* THE ROUND'S EFFECT ON THE CHILDREN SET, AT EVERY NUMBER.  This lane's
     row ([UsysMemOk.usys_ch_ok]) is the identity everywhere, so a leaf
     re-closes [urun] at the very set it trapped from and this re-key is
     all it has to do.  [ucwd_auth_quiet]'s twin; fork's, wait's and
     exit's leaves will spend [uch_move] instead. *)
  Lemma uch_auth_quiet (N : uk_names Σ) (cs cs' : gset gname) :
    cs' = cs -> uch_auth (ukn_ch N) cs -∗ uch_auth (ukn_ch N) cs'.
  Proof using . intros ->. iIntros "$". Qed.

  (* ...and the same at the bundled pair, which is what a leaf holds *)
  Lemma urun_ids_quiet (N : uk_names Σ) (cs cs' : gset gname) (pidv : mword 32) :
    cs' = cs -> urun_ids N cs pidv -∗ urun_ids N cs' pidv.
  Proof using . intros ->. iIntros "$". Qed.

  (* THE MOVER, for the day a fork/wait/exit leaf moves the set. *)
  Lemma uch_move (N : uk_names Σ) (S S' : gset gname) :
    uch_auth (ukn_ch N) S -∗ uch (ukn_ch N) S ==∗
    uch_auth (ukn_ch N) S' ∗ uch (ukn_ch N) S'.
  Proof using . iApply uch_update. Qed.

  (* "this instruction does not write sp".  Every leaf that writes a general
     register carries it; a concrete [rd] decides it by [vm_compute]. *)
  Definition unot_sp (rd : mword 5) : Prop := Regidx csp_rs1 <> Regidx rd.

  Lemma unot_sp_upd (rd : mword 5) (v : mword 64) (m : regfile) :
    unot_sp rd -> (<[Regidx rd := v]> m) !!! Regidx csp_rs1 = m !!! Regidx csp_rs1.
  Proof using . intro H. exact (upd_ne m (Regidx rd) (Regidx csp_rs1) v H). Qed.

  (* THE CLOSE.  This is the lemma that makes the whole interface work: a
     continuation phrased on [urun] discharges the ∀-quantified [ukc] that
     every existing leaf demands, because [urun] supplies its own ambient. *)
  (* [sz] is a parameter: [urun] hides the break existentially, but a leaf
     that is closing back up has just destructed it, so it can say which one.
     Re-introducing the existential at THAT size is all this does. *)
  Lemma urun_close (N : uk_names Σ) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm)
      (sz : Z) (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname) (pidv : mword 32)
      (m : regfile) (pc : mword 64)
      (avail : nat) :
    uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
    ustack (ukn_d N) (m !!! Regidx csp_rs1) avail -∗
    (* ...and the descriptor authority, at the same [fdv] the key is at *)
    ufd_auth (ukn_fd N) fdv -∗
    (* ...and the cwd authority, at the same [cw] the key is at *)
    ucwd_auth (ukn_cwd N) cw -∗
    (* ...and the two identity authorities, at the same [cs] and [pidv] the
       key is at -- ONE conjunct, so no leaf that hands them straight back
       moved ([urun_ids]) *)
    urun_ids N cs pidv -∗
    (* ...and the process's own knowledge of its exit payload, back at the
       same generation -- persistent, like the supplier below *)
    my_pay gn (ukn_pay N) -∗
    (* the deposit supplier and its law, back at the same key -- persistent,
       so a leaf that destructed [urun] hands the very copy it read *)
    udep -∗
    (* ...and whether the table holds a pipe row, at the same [fdv] -- the
       run's own reading (design/pipe.md, "The exit path").  PERSISTENT
       like the two above it, so a leaf hands back the copy it read. *)
    urun_rows N fdv -∗
    (∀ h : CpuId, urun N h m pc avail -∗ mWP (Loop : expr riscv_lang)) -∗
    ukcq (ukn_pay N) pm M sz fdv cw gn cs pidv m pc.
  Proof using .
    iIntros "Hheap Hstk Hufd Hcwd Hch #Hmy #Hdep #Hnpx Hcont".
    rewrite /ukcq. iFrame "Hmy".
    rewrite /ukc. iIntros (h xi C pt Rfd Rut HRut) "%Hlo %Hpm %Hlzf Hb".
    iApply ("Hcont" $! h).
    iExists xi, C, pt, Rfd, Rut, sz, M, pm, fdv, cw, gn, cs, pidv.
    iFrame "Hheap Hstk Hufd Hcwd Hch Hmy Hdep Hnpx Hb". iPureIntro.
    split_and!; [ exact Hlo | exact Hpm | exact (Hlzf eq_refl) | exact HRut ].
  Qed.

  (* [uv_upd] is the OTHER way a leaf writes a register (jalr's, where the
     write is optional).  It hid a real bug: the generated wrapper did not
     recognise the shape, so it claimed [avail] was preserved across an
     instruction that can write sp -- and that showed up not as a proof
     failure but as unification diverging inside the transparent [rf_upd].
     Hence this lemma, and the [unot_sp] premise that goes with it. *)
  Lemma uv_upd_not_sp (m : regfile) (rd : mword 5)
      (wr : option (mword 5 * mword 64)) (d : mword 64) :
    unot_sp rd ->
    (uint rd = 0 /\ wr = None) \/ (uint rd <> 0 /\ wr = Some (rd, d)) ->
    (uv_upd m wr) !!! Regidx csp_rs1 = m !!! Regidx csp_rs1.
  Proof using .
    intros Hns [[_ ->] | [_ ->]]; [ reflexivity | ].
    cbn [uv_upd]. exact (unot_sp_upd rd (regval_into_reg d) m Hns).
  Qed.

  (* ...and the same when the instruction WROTE a register: the free stack
     is keyed by sp, and [unot_sp] says this write was not to sp. *)
  Lemma urun_close_upd (N : uk_names Σ) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (m : regfile) (rd : mword 5) (v : mword 64)
      (sz : Z) (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname) (pidv : mword 32)
      (pc' : mword 64) (avail : nat) :
    unot_sp rd ->
    uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
    ustack (ukn_d N) (m !!! Regidx csp_rs1) avail -∗
    ufd_auth (ukn_fd N) fdv -∗
    ucwd_auth (ukn_cwd N) cw -∗
    urun_ids N cs pidv -∗
    my_pay gn (ukn_pay N) -∗
    udep -∗
    urun_rows N fdv -∗
    (∀ h : CpuId, urun N h (<[Regidx rd := v]> m) pc' avail -∗
                  mWP (Loop : expr riscv_lang)) -∗
    ukcq (ukn_pay N) pm M sz fdv cw gn cs pidv (<[Regidx rd := v]> m) pc'.
  Proof using .
    intros Hns. iIntros "Hheap Hstk Hufd Hcwd Hch #Hmy #Hdep #Hnpx Hcont".
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwd Hch Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd v m Hns). iExact "Hstk".
  Qed.

  (* ===================================================================== *)
  (* THE GENERIC CONTINUATION FOR A RUNNING PROCESS (app-echo.md, lane      *)
  (* SH-LINE, S4/S5: "sh's continuation goes generic").                     *)
  (*                                                                        *)
  (* An application's taint arm hands out a SLOT at a key                    *)
  (* ([PinnedExec.pex_slot]'s [T]-arm, [UexecExecMint.uslot_mint]), and      *)
  (* every consumer of one so far has been at a key -- an exec, a boot.  A   *)
  (* program that learns the taint MID-WALK holds a [urun] and no key, and   *)
  (* this is the step that closes that gap: the key a running process is at  *)
  (* is [UexecSlot.uvis_of_run] of its own registers and pc, the slot there  *)
  (* IS the U-mode continuation ([UexecRet.uslot_run]), and a [urun] carries *)
  (* exactly the residue that continuation takes.  Everything else the run   *)
  (* holds -- its heap, its stack, its ledger -- is DROPPED, which is what   *)
  (* "generic" means: the process goes on running, and nothing is promised   *)
  (* about it any more.                                                      *)
  (*                                                                        *)
  (* THE ALIGNMENT PREMISE is the one thing the run does not carry: a slot   *)
  (* is stated at a RESUME pc, and [uslot_run] is the round trip only at a   *)
  (* 2-aligned one.  Every pc a program names is a literal, so it is         *)
  (* [vm_compute] at the call site.                                          *)
  (* ===================================================================== *)
  Lemma urun_gen (N : uk_names Σ) (T : iProp Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) :
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    (* ...AND IT ANSWERS FOR NO OFFSETS (lane OFF-HAND-6, H3): the family
     the taint runs on is not narrowed any more
     ([ExecEntry.image_entry_taint]), because a held row's half is in the
     descriptor bundle and the kernel holds it at every fire. *)
    (* THE RUN CARRIES NO PAYLOAD (lane SELF-KILL, P6) and the TAINT ARM
       ASKS FOR NONE (P6b): a tainted process runs on the generic family,
       whose constant payload is carried PERSISTENTLY
       ([UexecExecMint.uslot_mint_all] at [□ (app_taint -∗ R)]) and
       is built out of [T] itself ([UserConsole.ucons_pay_taint]).  So all
       that crosses here is the taint and the key's own pay fact. *)
    □ (∀ W : uvis,
         T -∗ my_pay (uvis_gen W) (ukn_pay N) -∗ uslot W) -∗
    T -∗ urun N h m pc avail -∗ mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hal. iIntros "#Hgen HT Hrun".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv)
      "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iDestruct ("Hgen" $! (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
                 with "HT []") as "Hslot".
    { cbn [uvis_gen uvis_of_run]. iExact "Hmy". }
    rewrite (uslot_run m pc M pm sz fdv cw gn cs pidv Hx0 Hal).
    iApply ("Hslot" $! h xi C pt Rfd Rut HRut with "[%] [%] [%] Hb");
      [ exact Hlo | exact Hpm | intros _; exact Hlzf ].
  Qed.

  (* ===================================================================== *)
  (* §2 THE FETCH BRIDGE.                                                  *)
  (*                                                                       *)
  (* [uinstr_is] plus the heap gives the Prop-level decode fact the         *)
  (* existing engine consumes.  Every clause of [UmodeMem.uinstr] comes off *)
  (* a text fragment except [ui_inpage], which is TEMPORARY: it is here     *)
  (* only until WpUmodeStep's [uv_fetch_base_2] takes the second halfword's *)
  (* leaf as a premise instead of deriving it from the window being on one  *)
  (* page.  The source for that premise is the fragment at [uint pc + 2],   *)
  (* which this lemma already has in hand.                                  *)
  (* ===================================================================== *)
  Lemma uheap_text_byte (γt γd γs : gname) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm)
      (szh : Z) (a : Z) (b : bv 8) :
    uheap γt γd γs M pm szh -∗ utext γt a b -∗
    ⌜ M !! a = Some b /\ forall pt sz, proc_pt_wf pt ->
        perm_of (ud_um pt) sz = pm -> uva_fetch_leaf pt (mword_of_int a) ⌝.
  Proof using .
    iIntros "Hheap Hb".
    iDestruct (uheap_text with "Hheap Hb") as %(HM & (q & Hq & Hx) & Hbnd).
    iPureIntro. split; [ exact HM | ].
    intros pt sz Hwf Hpmeq.
    unfold uperm_at in Hq. rewrite <- Hpmeq in Hq.
    destruct (perm_of_X pt sz _ q Hwf Hq Hx) as (w & Hw & Hok).
    exists w. exact (conj Hw Hok).
  Qed.


  (* the byte AT THE PC gives the two things every branch of the bridge needs:
     the pc is canonical, and its page is fetch-ok at any table realizing the
     key.  Factored out so the three decode shapes below do not triplicate it. *)
  Lemma uheap_text_pc (γt γd γs : gname) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm)
      (szh : Z) (pc : mword 64) (b : bv 8) :
    uheap γt γd γs M pm szh -∗ utext γt (uint pc + Z.of_nat 0) b -∗
    ⌜ uva_canon pc /\
      forall pt sz, proc_pt_wf pt -> perm_of (ud_um pt) sz = pm ->
                    uva_fetch_leaf pt pc ⌝.
  Proof using .
    iIntros "Hheap Hb".
    iDestruct (uheap_text_byte with "Hheap Hb") as %(_ & Hlf).
    iDestruct (uheap_text with "Hheap Hb") as %(_ & _ & Hbnd).
    iPureIntro.
    change (Z.of_nat 0) with 0 in Hbnd, Hlf. rewrite Z.add_0_r in Hbnd, Hlf.
    destruct (ucanon_of_bound (uint pc) Hbnd) as [_ Hcan].
    rewrite moi_of_uint in Hcan, Hlf.
    exact (conj Hcan Hlf).
  Qed.

  (* ...and the pc's page is TEXT of every table the projection came from:
     X off the text half's class, not-W off its new clause, and
     [UmodeText.uva_text_of_perm] reads both off the leaf word *)
  Lemma uheap_text_pc_text (γt γd γs : gname) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm)
      (szh : Z) (pc : mword 64) (b : bv 8) :
    uheap γt γd γs M pm szh -∗ utext γt (uint pc + Z.of_nat 0) b -∗
    ⌜ forall pt sz, proc_pt_wf pt -> perm_of (ud_um pt) sz = pm ->
                    uva_text pt (uint pc) ⌝.
  Proof using .
    iIntros "Hheap Hb".
    iDestruct (uheap_text with "Hheap Hb") as %(_ & Hx & _).
    iDestruct (uheap_text_nw with "Hheap Hb") as %Hnw.
    iPureIntro.
    change (Z.of_nat 0) with 0 in Hx, Hnw. rewrite Z.add_0_r in Hx, Hnw.
    intros pt sz Hwf Hpmeq. subst pm.
    destruct Hx as (q & Hq & Hqx).
    destruct (up_W q) eqn:Hqw.
    - exfalso. apply Hnw. exists q. split; [ exact Hq | exact Hqw ].
    - exact (uva_text_of_perm pt sz (uint pc) q Hq Hqx Hqw).
  Qed.

  (* THE BRIDGE: [uinstr_is] plus the heap gives the Prop-level decode fact
     the existing engine consumes.  Every clause of [UmodeMem.uinstr] comes
     off a text fragment -- the leaf and canonicity from the byte at the pc,
     the code bytes from the run -- except [ui_inpage], which [uinstr_is]
     still carries for its one remaining consumer. *)
  Lemma uinstr_is_uk_instr (γt γd γs : gname) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm)
      (szh : Z) (pc : mword 64) (is_rvc : bool) (i : instruction) :
    uheap γt γd γs M pm szh -∗ uinstr_is γt pc is_rvc i -∗
    ⌜ uk_instr pm M pc is_rvc i ⌝.
  Proof using .
    iIntros "Hheap #Hi". rewrite /uinstr_is.
    iDestruct "Hi" as "(%Hal2 & %Hpg & Hcode)".
    destruct is_rvc.
    - iDestruct "Hcode" as (h) "(%HisRVC & %Hdec & Hbs)".
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
      + (* compressed at a 4-ALIGNED pc: the window IS a 4-byte word whose
           low half is the halfword *)
        iDestruct "Hbs" as (w) "(%Hlow & #Hbs)".
        iDestruct (uheap_text_run with "Hheap Hbs") as %Hb4.
        iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbs") as "#H0";
          [ reflexivity | ].
        iDestruct (uheap_text_pc with "Hheap H0") as %[Hcanon Hlf].
        iDestruct (uheap_text_pc_text with "Hheap H0") as %Htx.
        iPureIntro. intros pt sz Hwf Hpmeq.
        refine (UInstr pt M pc true i Hal2 Hcanon (Hlf pt sz Hwf Hpmeq) Hpg _
                  (Htx pt sz Hwf Hpmeq)).
        exists h. split_and!; [ exact HisRVC | | exact Hdec | ].
        * intros j Hj. rewrite <- Hlow.
          rewrite (nth_byte_subrange_lo w j ltac:(lia)).
          exact (Hb4 j ltac:(lia)).
        * intros _. exists (nth_byte w 2), (nth_byte w 3).
          pose proof (Hb4 2%nat ltac:(lia)) as H2.
          pose proof (Hb4 3%nat ltac:(lia)) as H3.
          change (Z.of_nat 2) with 2 in H2. change (Z.of_nat 3) with 3 in H3.
          exact (conj H2 H3).
      + (* compressed at a 2-mod-4 pc: two bytes, no trailing obligation *)
        iDestruct "Hbs" as "#Hbs".
        iDestruct (uheap_text_run with "Hheap Hbs") as %Hb2.
        iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbs") as "#H0";
          [ reflexivity | ].
        iDestruct (uheap_text_pc with "Hheap H0") as %[Hcanon Hlf].
        iDestruct (uheap_text_pc_text with "Hheap H0") as %Htx.
        iPureIntro. intros pt sz Hwf Hpmeq.
        refine (UInstr pt M pc true i Hal2 Hcanon (Hlf pt sz Hwf Hpmeq) Hpg _
                  (Htx pt sz Hwf Hpmeq)).
        exists h. split_and!; [ exact HisRVC | exact Hb2 | exact Hdec | ].
        intros Hc. rewrite Hc in Hal4. discriminate Hal4.
    - iDestruct "Hcode" as (w) "(%HnRVC & %Hdec & #Hbs)".
      iDestruct (uheap_text_run with "Hheap Hbs") as %Hb4.
      iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbs") as "#H0";
        [ reflexivity | ].
      iDestruct (uheap_text_pc with "Hheap H0") as %[Hcanon Hlf].
      iDestruct (uheap_text_pc_text with "Hheap H0") as %Htx.
      iPureIntro. intros pt sz Hwf Hpmeq.
      refine (UInstr pt M pc false i Hal2 Hcanon (Hlf pt sz Hwf Hpmeq) Hpg _
                (Htx pt sz Hwf Hpmeq)).
      exists w. split_and!; [ exact HnRVC | exact Hb4 | exact Hdec ].
  Qed.


  (* ===================================================================== *)
  (* §3 WHAT A MEMORY LEAF READS OFF THE HEAP.                                                        *)
  (*                                                                       *)
  (* Two representatives, one register-only and one memory, cut in the     *)
  (* shape every remaining leaf will take:                                 *)
  (*                                                                       *)
  (*   the instruction resource, the memory the instruction TOUCHES, the   *)
  (*   run, and a continuation at the updated run.                         *)
  (*                                                                       *)
  (* No ambient, no [ukc], no postcondition, and the immediate in NORMAL   *)
  (* FORM.  Everything the instruction does not touch frames, because it   *)
  (* is either inside [urun] (registers, image, table, permissions) or     *)
  (* outside and unmentioned (every other byte).                           *)
  (* ===================================================================== *)

  (* THE DATA WORD AT AN ADDRESS: in range, and WRITABLE.  This is where
     the permission table stops being visible -- the caller holds an
     exclusive [uword], and the heap turns that into the leaf's
     [uk_store_ok] without the caller ever naming a page or a PTE bit.
     Consuming the run inside this proof is free: the conclusion is pure, so
     the caller's [iDestruct … as %…] keeps both the heap and the word. *)
  Lemma uheap_uword_at (γt γd γs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz : Z) (dq : dfrac) (a : Z) (w : mword 64) :
    uheap γt γd γs M pm sz -∗ uwordq γd dq a w -∗
    ⌜ 0 <= a < 2 ^ 38 /\ uw_addr pm a ⌝.
  Proof using .
    iIntros "Hheap Hw". rewrite /uwordq /ubytesq.
    iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hw") as "H0";
      [ reflexivity | ].
    iDestruct (uheap_ubyte with "Hheap H0") as %(_ & Hw & Hb).
    iPureIntro. change (Z.of_nat 0) with 0 in Hw, Hb.
    rewrite Z.add_0_r in Hw, Hb. exact (conj Hb Hw).
  Qed.

  (* A RUN OF OWNED DATA BYTES: present in the image at its own values, on
     writable pages, in range.  This is the single lemma every memory leaf
     goes through -- it is what replaces the caller-supplied permission,
     canonicity and presence premises of the UkStore/UkLoad leaves. *)
  Lemma uheap_ubytes_at (γt γd γs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz : Z) (dq : dfrac) (a : Z) (n : nat)
      (f : nat -> bv 8) :
    uheap γt γd γs M pm sz -∗ ubytesq γd dq a n f -∗
    ⌜ forall j : nat, (j < n)%nat ->
        M !! (a + Z.of_nat j)%Z = Some (f j) /\
        uw_addr pm (a + Z.of_nat j)%Z /\
        0 <= a + Z.of_nat j < 2 ^ 38 ⌝.
  Proof using .
    iIntros "Hheap Hbs". rewrite /ubytes /ubytesq.
    iInduction n as [| n IH] "IH" forall (f).
    - iPureIntro. intros j Hj. exfalso. lia.
    - iEval (rewrite seq_S big_sepL_app /=) in "Hbs".
      iDestruct "Hbs" as "(Hlo & Hhi & _)".
      iDestruct (uheap_ubyte with "Hheap Hhi") as %Hn.
      (* the IH is generalised over [f], so instantiate that before feeding it *)
      iDestruct ("IH" $! f with "Hheap Hlo") as %Hlo.
      iPureIntro. intros j Hj.
      destruct (decide (j = n)) as [-> | Hne]; [ exact Hn | apply Hlo; lia ].
  Qed.

  (* ===================================================================== *)
  (* WHAT THE FREE STACK ITSELF SAYS ABOUT SP.                             *)
  (*                                                                       *)
  (* The deepest word [ustack γd sp n] owns sits at [uint sp - 8n], and     *)
  (* [uheap] bounds every owned address below MAXVA -- so “sp has n words   *)
  (* of room below it” is a CONSEQUENCE of holding the free stack, not an   *)
  (* obligation on whoever moves sp.  The sp-adjust rules take neither as   *)
  (* a premise.                                                            *)
  (* ===================================================================== *)
  Lemma ustack_room (γt γd γs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz : Z) (sp : mword 64) (n : nat) :
    uheap γt γd γs M pm sz -∗ ustack γd sp n -∗ ⌜ 8 * Z.of_nat n <= uint sp ⌝.
  Proof using .
    iIntros "Hheap Hstk".
    destruct n as [| n'].
    - iPureIntro. pose proof (proj1 (bv_unsigned_in_range _ sp)) as H0.
      rewrite uint_unsigned. lia.
    - iDestruct (ustack_acc γd sp (S n') n' ltac:(lia) with "Hstk") as "[Hw _]".
      iDestruct "Hw" as (w) "Hw".
      iDestruct (uheap_uword_at with "Hheap Hw") as %[Hb _].
      iPureIntro. rewrite Nat2Z.inj_succ. lia.
  Qed.

  (* ...and the same fact read at a MOVED sp: had [sp + 8k] wrapped, its own
     frame's deepest word would be at a negative address. *)
  Lemma ustack_nowrap (γt γd γs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz : Z) (sp : mword 64) (k : nat) :
    uheap γt γd γs M pm sz -∗
    ustack γd (add_vec_int sp (8 * Z.of_nat k)) k -∗
    ⌜ uint sp + 8 * Z.of_nat k < Z64 ⌝.
  Proof using .
    iIntros "Hheap Hstk".
    iDestruct (ustack_room γt γd γs M pm sz
                 (add_vec_int sp (8 * Z.of_nat k)) k with "Hheap Hstk") as %Hr.
    iPureIntro.
    pose proof (bv_unsigned_in_range _ (add_vec_int sp (8 * Z.of_nat k))) as Hr2.
    rewrite Zmod64 in Hr2. rewrite <- uint_unsigned in Hr2.
    pose proof (bv_unsigned_in_range _ sp) as Hs.
    rewrite Zmod64 in Hs. rewrite <- uint_unsigned in Hs.
    (* the moved sp's unsigned value IS the sum mod 2^64 *)
    assert (Hmod : uint (add_vec_int sp (8 * Z.of_nat k))
                   = (uint sp + 8 * Z.of_nat k) mod Z64).
    { unfold add_vec_int. rewrite !uint_unsigned.
      rewrite add_vec64_unsigned moi64_unsigned. unfold bv_wrap.
      assert (E64 : bv_modulus 64 = 18446744073709551616)
        by (vm_compute; reflexivity).
      rewrite E64 Zplus_mod_idemp_r. unfold Z64. reflexivity. }
    destruct (decide (uint sp + 8 * Z.of_nat k < Z64)) as [Hlt | Hge];
      [ exact Hlt | exfalso ].
    (* one wrap at most: [8k] and [uint sp] are each below 2^64 *)
    assert (Hstep : (uint sp + 8 * Z.of_nat k) mod Z64
                    = uint sp + 8 * Z.of_nat k - Z64).
    { assert (Ha : uint sp + 8 * Z.of_nat k
                   = (uint sp + 8 * Z.of_nat k - Z64) + 1 * Z64) by lia.
      rewrite {1}Ha. rewrite Z_mod_plus_full.
      apply Z.mod_small. unfold Z64 in *. lia. }
    rewrite Hstep in Hmod. unfold Z64 in *. lia.
  Qed.

  (* ...and what a PROGRAM can read off its own run, without opening it: the
     two stack facts every prologue used to take as premises. *)
  Lemma urun_stack (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) :
    urun N h m pc avail -∗
    ⌜ uint (m !!! Regidx csp_rs1) mod 8 = 0
      /\ 8 * Z.of_nat avail <= uint (m !!! Regidx csp_rs1) ⌝.
  Proof using .
    iIntros "Hrun".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwd & Hch & #Hdep & Hb)".
    iDestruct (ustack_align with "Hstk") as %Hal.
    iDestruct (ustack_room with "Hheap Hstk") as %Hroom.
    iPureIntro. exact (conj Hal Hroom).
  Qed.

  (* ===================================================================== *)
  (* §4 THE ENTRY: the process's FIRST WP.                                 *)
  (*                                                                       *)
  (* This is the other end of the interface.  A program never constructs a  *)
  (* [urun]; it is handed one here, together with the points-to facts for   *)
  (* its whole initial image, in exchange for a proof that it is safe from  *)
  (* the key's resume state.  The gnames are FRESH -- allocated at this     *)
  (* WP, under the ambient the slot quantifies over -- which is why they    *)
  (* are arguments of [urun] rather than section variables.                 *)
  (* ===================================================================== *)

  (* [uheap_alloc]'s one premise, discharged.  Two sources: a MAPPED address
     sits in a page the table maps, and [upt_map_wf] puts every such page
     below the trapframe; a LIVE address is below the break, and [usz_ok]
     puts the break below the trapframe too. *)
  Lemma umem_lazy_bound {CIDL : CpuId} {XIL : CtxIdDefs.CurCtx} (pt : uptd) (sz : Z) (M : gmap Z (bv 8)) :
    proc_pt_wf pt -> usz_ok sz ->
    umem_lazy_x pt sz M -∗ ⌜ forall a : Z, is_Some (M !! a) -> 0 <= a < 2 ^ 38 ⌝.
  Proof using .
    iIntros (Hwf Hsz) "H". iDestruct "H" as (Mp) "(_ & %Hiff & _ & _)".
    iPureIntro. intros a Ha.
    change (2 ^ 38) with 274877906944.
    destruct (proj1 (Hiff a) Ha) as [Hm | Hl].
    - destruct Hm as (vpn & w & j & Hvl & Hj & ->).
      destruct Hwf as (Hmw & _).
      destruct (Hmw vpn w Hvl) as [Hlt _].
      rewrite tf_vpn_unsigned in Hlt.
      pose proof (proj1 (bv_unsigned_in_range _ vpn)) as Hv0.
      lia.
    - pose proof (usz_ok_live sz a Hsz Hl). lia.
  Qed.

  (* THE ENTRY, with the process's initial free stack carved out of its data.
     [avail] words below the resume sp become [urun]'s free stack; the rest
     of the data is DROPPED (affinely), which is fine for a program whose
     only memory is its stack.  A program that also needs static data wants
     the non-lossy form of [ubytes_of_map], which its induction already
     produces -- see the note there.

     The two premises are exactly what the old [uk_stack] gate decided, in
     the vocabulary of the heap: enough room below sp, and the bytes there
     actually present in the data half.  [sz] is bound by the slot, so the
     second is stated for every [sz] the bundle could carry. *)
  (* [UserHeap.umap_split_at] at an arbitrary decidable cut: the data map
     split into the part satisfying [P] and its complement *)
  Local Lemma umap_split_pred (γd : gname) (D : gmap Z (bv 8)) (P : Z -> Prop)
      `{!forall a : Z, Decision (P a)} :
    ([∗ map] k ↦ b ∈ D, ubyte γd k b) -∗
      ([∗ map] k ↦ b ∈ base.filter (fun kv : Z * bv 8 => P kv.1) D,
         ubyte γd k b) ∗
      ([∗ map] k ↦ b ∈ base.filter (fun kv : Z * bv 8 => ~ P kv.1) D,
         ubyte γd k b).
  Proof using .
    iIntros "H".
    rewrite -(big_sepM_union (fun k b => ubyte γd k b)
                (base.filter (fun kv : Z * bv 8 => P kv.1) D)
                (base.filter (fun kv : Z * bv 8 => ~ P kv.1) D)
                (map_disjoint_filter_complement _ D)).
    rewrite (map_filter_union_complement (fun kv : Z * bv 8 => P kv.1) D).
    iExact "H".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE GENERAL FORM: [uslot_of_urun]'s mint and carve with the data      *)
  (* OUTSIDE the frame handed over EXCLUSIVELY -- the bytes below the      *)
  (* frame's base and the bytes at or above sp.  A program whose static    *)
  (* data (a .bss buffer, say) lies below its stack takes it out of the    *)
  (* first half; an argument area is in the second.  [UShKernel.v] is what *)
  (* needs it: sh reads and writes its line buffer, which the lossy entry  *)
  (* would drop.                                                          *)
  (* ------------------------------------------------------------------- *)
  Lemma uslot_of_urun_all (W : uvis) (avail : nat) (Q : Z -> iProp Σ) :
    uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) mod 8 = 0 ->
    8 * Z.of_nat avail
      <= uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) ->
    (forall j : nat, (j < 8 * avail)%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                     - 8 * Z.of_nat avail + Z.of_nat j)%Z)) ->
    length (uvis_fd W) = NOFILE ->
    (* the map stops at the break -- [uslot_of_urun]'s own premise *)
    (forall (p : mword 27) (q : uperm), uvis_perm W !! p = Some q ->
       bv_unsigned p * 4096 < UserPtTree.pgroundup (uvis_sz W)) ->
    (* ...AND THE KEY'S LAZY BIT IS [false] (lane LAZY-FLAG, L6).  The
       verified-program tier runs at an EMPTY FILL: [UexecRet.ukcq], and
       with it [urun], is hardwired at [false], so a constructor can only
       build a slot for a key that says so.  A process that called
       [sbrklazy] simply has no [urun] to run on -- a restriction of that
       tier, not of the model.  WHO SUPPLIES IT: exec, whose fresh image is
       eager ([SpecKexec.exec_slot_pre]'s success wands; lane LAZY-FLAG's
       K4 is what puts the fact on them). *)
    uvis_lazy W = false ->
    (* ...AND ITS MASK IS FULL (upstream a083670): [urun] is keyed at
       [ProcDefs.secc_all], as it is at [false] above.  WHO SUPPLIES IT:
       userinit's first record, fork's copy, exec's keep
       ([SpecKexec.exec_slot_pre]'s mask row). *)
    uvis_secc W = ProcDefs.secc_all ->
    (* ...AND NO HONESTY ROW ON THE HELD SET (lane OFF-HAND-6's H3 emptied
       it, lane OFF-LINK-2's L6 deleted the field): a constructor says
       nothing about offsets and an entry may be taken at a key with a HELD
       descriptor, which is what makes a redirect child's exec provable
       (design/app-file.md SS3). *)
    (* ...and the deposit supplier, exactly as [uslot_of_urun] takes it *)
    udep -∗
    (* ...AND THE PROCESS'S OWN KNOWLEDGE OF ITS EXIT PAYLOAD.  A [urun]
       carries it ([ChildTok.my_pay] at the key's generation) because the
       exit leaf pays the trap loop's deposit row out of it
       ([UkRunSys.wp_uk_ecall_exit]), and a constructor is the only place
       it can enter: the record it mints is what fixes [ukn_pay].  The
       kernel is what hands it over -- fork through the child slot's
       premise, exec through [SpecKexec.exec_slot_pre]'s wands, and
       userinit at the trivial payload. *)
    (* ...AND WHETHER THE PROCESS'S TABLE HOLDS A PIPE ROW (design/pipe.md,
       "The exit path").  The run carries this between traps
       ([urun_nopipe]) and exit's bundle row is minted off it, so an ENTRY
       is where it comes in.  It is a fact about the key the kernel handed
       over and it travels the way every other such fact does:
       [SpecKexec.kexec_image_ok_fd] says an exec'd image's table IS the
       exec'ing process's, so a chain of pipe-free programs stays pipe-free
       and the boot process's table is [FdSlots.fdt0], all closed.  A
       program that means to call pipe(2) comes in on the right arm
       instead ([urun_nopipe_taint]). *)
    (* ...AND WHETHER IT ANSWERS FOR ITS OFFSETS (lane OFF-HAND-3, R1).
       [hs] is the set the minted record carries and this is the premise
       that makes it honest: a constructor may claim a set only if every
       unparked row of the key's table is in it.  Every landed entry
       passes [empty] at a table the kernel has just handed over
       ([SpecKexec.exec_slot_pre]'s all-parked row,
       [FdSlots.fdv_all_parked_fdt0] at the boot), and a constructor for a
       program that means to HOLD an offset half passes the slots it means
       to hold. *)
    urun_nopipe (uvis_fd W) -∗
    my_pay (uvis_gen W) Q -∗
    (∀ (N : uk_names Σ) (h : CpuId),
       (* the record's payload IS the one that came in, which is what lets
          the program's proof read its own [ukn_pay] *)
       ⌜ ukn_pay N = Q ⌝ -∗
       ⌜ usz_ok (uvis_sz W) ⌝ -∗
       usz (ukn_s N) (uvis_sz W) -∗
       utext_all (ukn_t N) (uvis_M W) (uvis_perm W) -∗
       ustd (ukn_fd N) (take NSTD (uvis_fd W)) -∗
       (* ...AND THE PROGRAM'S OWN HALF OF ITS WORKING DIRECTORY, at the
          inum the resumed key carries.  Same reason the ledger comes out
          here: this is where the process's [urun] is created, so it is
          where the tie between the program's half and the key's [cw]
          begins.  A program that never looks at its cwd drops it. *)
       ucwd (ukn_cwd N) (uvis_cwd W) -∗
       (* ...AND ITS OWN HALF OF ITS CHILDREN SET, at the very set the
          resumed key carries -- [∅] at every entry that exists today,
          because an entry constructor builds the FIRST run of a program
          and a program that has not forked has no children. *)
       uch (ukn_ch N) (uvis_ch W) -∗
       (* ...AND ITS OWN HALF OF ITS PID (lane TRAP-ROWS-4, B): the number
          the resumed key carries, at the record's own ghost name.  It is
          what a caller reads wait's reaping arm against
          ([UkRunSys.wp_uk_ecall_wait_null_live]) and what makes getpid(2)'s
          answer sayable.  A program that never asks drops it. *)
       upid (ukn_pid N) (bv_unsigned (uvis_pid W)) -∗
       ([∗ map] k ↦ b ∈ base.filter
             (fun kv : Z * bv 8 =>
                kv.1 < uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                       - 8 * Z.of_nat avail)
             (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)),
          ubyte (ukn_d N) k b) -∗
       ([∗ map] k ↦ b ∈ base.filter
             (fun kv : Z * bv 8 =>
                ~ (kv.1 < uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)))
             (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)),
          ubyte (ukn_d N) k b) -∗
       urun N h (tf_resume_gpr0 (uvis_tf W))
         (tf_resume_pc (uvis_tf W)) avail -∗
       mWP (Loop : expr riscv_lang))
    -∗ uslot W.
  Proof using .
    intros Hal8 Hroom Hstk Hfdlen Hstop Hlzf Hscf.
    iIntros "#Hdep #Hnpx #Hpay Hprog".
    rewrite uslot_ukc /ukc Hlzf Hscf.
    iIntros (h xi C pt Rfd Rut HRut) "%Hlo %Hpm %Hlzr Hb".
    set (sz := uvis_sz W).
    assert (Hwf : proc_pt_wf pt)
      by (destruct Hlo as (_ & _ & _ & _ & _ & H); exact H).
    rewrite /uvb /uvb_F /user_ptm_inv_x.
    iDestruct "Hb" as
      "(Hamb & Hregs & %Hsz & (Htlb & Hlazy & %Hinj & %Hacc) &
        Hfrag & Hcfg & Hgpr & Hpc & Hrut & Hkont)".
    iDestruct (umem_lazy_bound pt sz (uvis_M W) Hwf Hsz with "Hlazy") as %Hcan.
    iMod (uheap_alloc (uvis_M W) (uvis_perm W) sz Hcan Hstop)
      as (γt γd γs) "(Hheap & Hszf & #Ht & Hd)".
    iMod (ufd_alloc_std (uvis_fd W) ∅ Hfdlen (map_empty_subseteq _))
      as (γfd) "(Hufd & Hstd & _)".
    (* ...AND THE WORKING DIRECTORY'S PAIR, at the inum the resumed key
       carries: the authority stays in the [urun] being built, the
       fragment goes to the program. *)
    iMod (ucwd_alloc (uvis_cwd W)) as (γc) "[Hcwa Hcwf]".
    (* ...AND THE CHILDREN SET'S PAIR, at the set the resumed key carries:
       the authority stays in the [urun] being built, the fragment goes to
       the program. *)
    iMod (uch_alloc (uvis_ch W)) as (γch) "[Hcha Hchf]".
    (* ...AND THE PID'S PAIR, at the pid the resumed key carries: the
       authority stays in the [urun] being built (bundled with the
       children's -- [urun_ids]), the fragment goes to the program.  It is
       what lets the program NAME its own pid (lane TRAP-ROWS-4, B). *)
    iMod (upid_alloc (bv_unsigned (uvis_pid W))) as (γpid) "[Hpida Hpidf]".
    rewrite -/(utext_all γt (uvis_M W) (uvis_perm W)).
    (* ---- the two cuts: at the frame's base, then at sp ---- *)
    set (sp := tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1).
    set (D := udata_lo (uvis_M W) (uvis_perm W) sz).
    set (base := (uint sp - 8 * Z.of_nat avail)%Z).
    iDestruct (umap_split_at γd D base with "Hd") as "[Dlo Dhi]".
    iDestruct (umap_split_pred γd _ (fun a : Z => a < uint sp) with "Dhi")
      as "[Dmid Dtop]".
    (* the upper half is [~ (k < sp)] on [D] itself: a key at or above sp
       is not below [base] *)
    iAssert ([∗ map] k ↦ b ∈ base.filter
                 (fun kv : Z * bv 8 => ~ (kv.1 < uint sp)) D, ubyte γd k b)%I
      with "[Dtop]" as "Dtop".
    { assert (E : base.filter (fun kv : Z * bv 8 => ~ (kv.1 < uint sp))
                    (base.filter (fun kv : Z * bv 8 => ~ (kv.1 < base)) D)
                  = base.filter (fun kv : Z * bv 8 => ~ (kv.1 < uint sp)) D).
      { rewrite map_filter_filter. apply map_filter_ext.
        intros k b _. cbn.
        split; [ intros [H _]; exact H
               | intro H; split; [ exact H | unfold base; lia ] ]. }
      rewrite E. iExact "Dtop". }
    (* ---- the frame, out of the middle ---- *)
    set (f := fun j : nat =>
                default (bv_0 8)
                  (base.filter (fun kv : Z * bv 8 => kv.1 < uint sp)
                     (base.filter (fun kv : Z * bv 8 => ~ (kv.1 < base)) D)
                     !! (base + Z.of_nat j)%Z)).
    assert (Hf : forall j : nat, (j < 8 * avail)%nat ->
                   base.filter (fun kv : Z * bv 8 => kv.1 < uint sp)
                     (base.filter (fun kv : Z * bv 8 => ~ (kv.1 < base)) D)
                     !! (base + Z.of_nat j)%Z = Some (f j)).
    { intros j Hj. destruct (Hstk j Hj) as [b Hb].
      assert (Hb' : base.filter (fun kv : Z * bv 8 => kv.1 < uint sp)
                      (base.filter (fun kv : Z * bv 8 => ~ (kv.1 < base)) D)
                      !! (base + Z.of_nat j)%Z = Some b).
      { apply umap_filter_lookup_lt; [ unfold base; lia | ].
        apply umap_filter_lookup_ge; [ lia | exact Hb ]. }
      unfold f. rewrite Hb'. reflexivity. }
    iDestruct (ubytes_of_map γd _ base (8 * avail) f Hf with "Dmid") as "Hbs".
    iDestruct (ustack_of_ubytes γd sp avail f Hal8 Hroom with "Hbs") as "Hstk".
    iSpecialize ("Hprog" $! (MkUkNames γt γd γs γfd γc γch Q γpid) h
                   with "[%] [%] Hszf Ht Hstd Hcwf Hchf Hpidf Dlo Dtop");
      [ reflexivity | exact Hsz | ].
    iApply "Hprog".
    iExists xi, C, pt, Rfd, Rut, sz, (uvis_M W), (uvis_perm W), (uvis_fd W),
      (uvis_cwd W), (uvis_gen W), (uvis_ch W), (uvis_pid W).
    iSplitR; [ iPureIntro; exact Hlo | ].
    iSplitR; [ iPureIntro; exact Hpm | ].
    iSplitR; [ iPureIntro; exact (Hlzr eq_refl) | ].
    iSplitR; [ iPureIntro; exact HRut | ].
    (* the record is minted at [Q], so the payload the constructor was
       handed IS the run's [ukn_pay N (-1)] *)
    (* the two identity authorities go in as ONE conjunct ([urun_ids]) *)
    iDestruct (urun_ids_intro (MkUkNames γt γd γs γfd γc γch Q γpid)
                 (uvis_ch W) (uvis_pid W) with "Hcha Hpida") as "Hcha".
    iFrame "Hheap Hstk Hufd Hcwa Hcha Hpay Hdep".
    iSplitR; [ rewrite /urun_rows; iExact "Hnpx" | ].
    rewrite /uvb /uvb_F /user_ptm_inv_x.
    iFrame "Hamb Hregs Hfrag Hcfg Hgpr Hpc Hrut Hkont Htlb Hlazy".
    iPureIntro. split_and!; [ exact Hsz | exact Hinj | exact Hacc ].
  Qed.

  Lemma uslot_of_urun (W : uvis) (avail : nat) (Q : Z -> iProp Σ) :
    (* the resume sp is word-aligned -- what [ustack] now asserts, and the
       one place it is an obligation rather than a consequence, since it is
       a fact about the process the kernel set up *)
    uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) mod 8 = 0 ->
    8 * Z.of_nat avail
      <= uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) ->
    (* DECIDABLE FROM THE KEY, now that the key carries the break.  Before
       [uvis_sz] existed this had to be stated for every [sz] the slot's ∀
       admitted -- which includes [sz = 0], so it was not merely
       undecidable, it was unsatisfiable. *)
    (forall j : nat, (j < 8 * avail)%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                     - 8 * Z.of_nat avail + Z.of_nat j)%Z)) ->
    (* the descriptor table is [NOFILE] slots -- what the process's own
       authority is minted with ([UserFd.ufd_auth] carries it) *)
    length (uvis_fd W) = NOFILE ->
    (* THE MAP STOPS AT THE BREAK: above the page the break sits in, the
       key's permission view has no entry.  It is the U tier's reading of
       [ProcPtOwn.um_below] -- which the bundle does not carry, so it is
       stated here, where the program's own layout decides it -- and it is
       what makes [sbrk]'s new run FRESH ([UserHeap]'s own clause). *)
    (forall (p : mword 27) (q : uperm), uvis_perm W !! p = Some q ->
       bv_unsigned p * 4096 < UserPtTree.pgroundup (uvis_sz W)) ->
    (* ...AND THE KEY'S LAZY BIT IS [false] -- see [uslot_of_urun_all]. *)
    uvis_lazy W = false ->
    (* ...AND ITS MASK IS FULL (upstream a083670): [urun] is keyed at
       [ProcDefs.secc_all], as it is at [false] above.  WHO SUPPLIES IT:
       userinit's first record, fork's copy, exec's keep
       ([SpecKexec.exec_slot_pre]'s mask row). *)
    uvis_secc W = ProcDefs.secc_all ->
    (* ...AND NO HONESTY ROW ON THE HELD SET (lane OFF-HAND-6's H3 emptied
       it, lane OFF-LINK-2's L6 deleted the field): a constructor says
       nothing about offsets and an entry may be taken at a key with a HELD
       descriptor, which is what makes a redirect child's exec provable
       (design/app-file.md SS3). *)
    (* THE DEPOSIT SUPPLIER, at the key the slot is being built for.  This
       is the one obligation the ARM adds to an entry constructor: whoever
       hands a program a [urun] says which syscall bundles it can pay and
       out of what.  [UexecCond.cond_entry_slot] passes the generic one
       ([Dsup := ssupply], every number admitted); a verified program's
       constructor passes its own. *)
    udep -∗
    (* ...AND THE PROCESS'S OWN KNOWLEDGE OF ITS EXIT PAYLOAD.  A [urun]
       carries it ([ChildTok.my_pay] at the key's generation) because the
       exit leaf pays the trap loop's deposit row out of it
       ([UkRunSys.wp_uk_ecall_exit]), and a constructor is the only place
       it can enter: the record it mints is what fixes [ukn_pay].  The
       kernel is what hands it over -- fork through the child slot's
       premise, exec through [SpecKexec.exec_slot_pre]'s wands, and
       userinit at the trivial payload. *)
    (* ...AND WHETHER THE PROCESS'S TABLE HOLDS A PIPE ROW (design/pipe.md,
       "The exit path").  The run carries this between traps
       ([urun_nopipe]) and exit's bundle row is minted off it, so an ENTRY
       is where it comes in.  It is a fact about the key the kernel handed
       over and it travels the way every other such fact does:
       [SpecKexec.kexec_image_ok_fd] says an exec'd image's table IS the
       exec'ing process's, so a chain of pipe-free programs stays pipe-free
       and the boot process's table is [FdSlots.fdt0], all closed.  A
       program that means to call pipe(2) comes in on the right arm
       instead ([urun_nopipe_taint]). *)
    (* ...AND WHETHER IT ANSWERS FOR ITS OFFSETS (lane OFF-HAND-3, R1).
       [hs] is the set the minted record carries and this is the premise
       that makes it honest: a constructor may claim a set only if every
       unparked row of the key's table is in it.  Every landed entry
       passes [empty] at a table the kernel has just handed over
       ([SpecKexec.exec_slot_pre]'s all-parked row,
       [FdSlots.fdv_all_parked_fdt0] at the boot), and a constructor for a
       program that means to HOLD an offset half passes the slots it means
       to hold. *)
    urun_nopipe (uvis_fd W) -∗
    my_pay (uvis_gen W) Q -∗
    (∀ (N : uk_names Σ) (h : CpuId),
       (* the record's payload IS the one that came in, which is what lets
          the program's proof read its own [ukn_pay] *)
       ⌜ ukn_pay N = Q ⌝ -∗
       ⌜ usz_ok (uvis_sz W) ⌝ -∗
       usz (ukn_s N) (uvis_sz W) -∗
       utext_all (ukn_t N) (uvis_M W) (uvis_perm W) -∗
       (* THE LEDGER OF THE STANDARD STREAMS, at the states the resumed key
          carries.  It comes out here because it has to: the low [NSTD] keys
          are in [UserFd.ufd_map] by construction, so their fragments exist
          from the moment the authority does, and an exclusive fragment for
          a key already in the map can never be minted later.  A program
          that does not care about its standard streams drops it -- and then
          calls no allocating syscall, which is the honest reading of "it is
          not tracking its descriptors". *)
       ustd (ukn_fd N) (take NSTD (uvis_fd W)) -∗
       (* ...AND THE PROGRAM'S OWN HALF OF ITS WORKING DIRECTORY, at the
          inum the resumed key carries.  Same reason the ledger comes out
          here: this is where the process's [urun] is created, so it is
          where the tie between the program's half and the key's [cw]
          begins.  A program that never looks at its cwd drops it. *)
       ucwd (ukn_cwd N) (uvis_cwd W) -∗
       (* ...AND ITS OWN HALF OF ITS CHILDREN SET, at the very set the
          resumed key carries -- [∅] at every entry that exists today,
          because an entry constructor builds the FIRST run of a program
          and a program that has not forked has no children. *)
       uch (ukn_ch N) (uvis_ch W) -∗
       (* ...AND ITS OWN HALF OF ITS PID (lane TRAP-ROWS-4, B): the number
          the resumed key carries, at the record's own ghost name.  It is
          what a caller reads wait's reaping arm against
          ([UkRunSys.wp_uk_ecall_wait_null_live]) and what makes getpid(2)'s
          answer sayable.  A program that never asks drops it. *)
       upid (ukn_pid N) (bv_unsigned (uvis_pid W)) -∗
       urun N h (tf_resume_gpr0 (uvis_tf W)) (tf_resume_pc (uvis_tf W))
         avail -∗
       mWP (Loop : expr riscv_lang))
    -∗ uslot W.
  Proof using .
    intros Hal8 Hroom Hstk Hfdlen Hstop Hlzf Hscf.
    iIntros "#Hdep #Hnpx #Hpay Hprog". rewrite uslot_ukc /ukc Hlzf Hscf.
    iIntros (h xi C pt Rfd Rut HRut) "%Hlo %Hpm %Hlzr Hb".
    set (sz := uvis_sz W).
    assert (Hwf : proc_pt_wf pt)
      by (destruct Hlo as (_ & _ & _ & _ & _ & H); exact H).
    rewrite /uvb /uvb_F /user_ptm_inv_x.
    iDestruct "Hb" as
      "(Hamb & Hregs & %Hsz & (Htlb & Hlazy & %Hinj & %Hacc) &
        Hfrag & Hcfg & Hgpr & Hpc & Hrut & Hkont)".
    iDestruct (umem_lazy_bound pt sz (uvis_M W) Hwf Hsz with "Hlazy") as %Hcan.
    iMod (uheap_alloc (uvis_M W) (uvis_perm W) sz Hcan Hstop)
      as (γt γd γs) "(Hheap & Hszf & #Ht & Hd)".
    (* ...AND THE PROGRAM'S DESCRIPTOR AUTHORITY, minted here beside the
       heap's three names.  This is where a process's [urun] is created, so
       it is where its own view of its table begins -- at the view the
       resumed KEY carries, which is the view the kernel is handing it. *)
    iMod (ufd_alloc_std (uvis_fd W) ∅ Hfdlen (map_empty_subseteq _))
      as (γfd) "(Hufd & Hstd & _)".
    (* ...AND THE WORKING DIRECTORY'S PAIR, at the inum the resumed key
       carries: the authority stays in the [urun] being built, the
       fragment goes to the program. *)
    iMod (ucwd_alloc (uvis_cwd W)) as (γc) "[Hcwa Hcwf]".
    (* ...AND THE CHILDREN SET'S PAIR, at the set the resumed key carries:
       the authority stays in the [urun] being built, the fragment goes to
       the program. *)
    iMod (uch_alloc (uvis_ch W)) as (γch) "[Hcha Hchf]".
    (* ...AND THE PID'S PAIR, at the pid the resumed key carries: the
       authority stays in the [urun] being built (bundled with the
       children's -- [urun_ids]), the fragment goes to the program.  It is
       what lets the program NAME its own pid (lane TRAP-ROWS-4, B). *)
    iMod (upid_alloc (bv_unsigned (uvis_pid W))) as (γpid) "[Hpida Hpidf]".
    rewrite -/(utext_all γt (uvis_M W) (uvis_perm W)).
    (* ---- the carve ---- *)
    set (sp := tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1).
    set (D := udata_lo (uvis_M W) (uvis_perm W) sz).
    set (base := (uint sp - 8 * Z.of_nat avail)%Z).
    set (f := fun j : nat => default (bv_0 8) (D !! (base + Z.of_nat j)%Z)).
    assert (Hf : forall j : nat, (j < 8 * avail)%nat ->
                   D !! (base + Z.of_nat j)%Z = Some (f j)).
    { intros j Hj. destruct (Hstk j Hj) as [b Hb].
      unfold f. unfold D, base in *. rewrite Hb. reflexivity. }
    iDestruct (ubytes_of_map γd D base (8 * avail) f Hf with "Hd") as "Hbs".
    iDestruct (ustack_of_ubytes γd sp avail f Hal8 Hroom with "Hbs") as "Hstk".
    iSpecialize ("Hprog" $! (MkUkNames γt γd γs γfd γc γch Q γpid) h
                   with "[%] [%] Hszf Ht Hstd Hcwf Hchf Hpidf");
      [ reflexivity | exact Hsz | ].
    iApply "Hprog".
    iExists xi, C, pt, Rfd, Rut, sz, (uvis_M W), (uvis_perm W), (uvis_fd W),
      (uvis_cwd W), (uvis_gen W), (uvis_ch W), (uvis_pid W).
    iSplitR; [ iPureIntro; exact Hlo | ].
    iSplitR; [ iPureIntro; exact Hpm | ].
    iSplitR; [ iPureIntro; exact (Hlzr eq_refl) | ].
    iSplitR; [ iPureIntro; exact HRut | ].
    (* the record is minted at [Q], so the payload the constructor was
       handed IS the run's [ukn_pay N (-1)] *)
    (* the two identity authorities go in as ONE conjunct ([urun_ids]) *)
    iDestruct (urun_ids_intro (MkUkNames γt γd γs γfd γc γch Q γpid)
                 (uvis_ch W) (uvis_pid W) with "Hcha Hpida") as "Hcha".
    iFrame "Hheap Hstk Hufd Hcwa Hcha Hpay Hdep".
    iSplitR; [ rewrite /urun_rows; iExact "Hnpx" | ].
    rewrite /uvb /uvb_F /user_ptm_inv_x.
    iFrame "Hamb Hregs Hfrag Hcfg Hgpr Hpc Hrut Hkont Htlb Hlazy".
    iPureIntro. split_and!; [ exact Hsz | exact Hinj | exact Hacc ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ...AND THE SAME DEPOSIT WITH A READ-ONLY AREA ALONGSIDE.              *)
  (*                                                                      *)
  (* [uslot_of_urun] spends the whole data map on the frame.  A program    *)
  (* that also reads what exec left it -- its argument vector -- needs the *)
  (* rest of the map back, so this one CUTS the map at the entry sp:       *)
  (* everything below is frame territory and is carved into the free       *)
  (* stack exactly as before, everything at or above is PERSISTED and      *)
  (* handed over read-only.  The cut is [UkAbi.uk_args]'s own [uka_lo].    *)
  (*                                                                      *)
  (* Persisting is what makes the argument area cheap: the program may     *)
  (* take as many views of it as it likes and none of them has to be       *)
  (* disjoint from any other, so no caller and no entry gate ever has to   *)
  (* decide whether two argv slots point at the same string.               *)
  (* ------------------------------------------------------------------- *)
  Lemma uslot_of_urun_ro (W : uvis) (avail : nat) (Q : Z -> iProp Σ) :
    uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) mod 8 = 0 ->
    8 * Z.of_nat avail
      <= uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) ->
    (forall j : nat, (j < 8 * avail)%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                     - 8 * Z.of_nat avail + Z.of_nat j)%Z)) ->
    (* the descriptor table is [NOFILE] slots -- what the process's own
       authority is minted with ([UserFd.ufd_auth] carries it) *)
    length (uvis_fd W) = NOFILE ->
    (* THE MAP STOPS AT THE BREAK: above the page the break sits in, the
       key's permission view has no entry.  It is the U tier's reading of
       [ProcPtOwn.um_below] -- which the bundle does not carry, so it is
       stated here, where the program's own layout decides it -- and it is
       what makes [sbrk]'s new run FRESH ([UserHeap]'s own clause). *)
    (forall (p : mword 27) (q : uperm), uvis_perm W !! p = Some q ->
       bv_unsigned p * 4096 < UserPtTree.pgroundup (uvis_sz W)) ->
    (* ...AND THE KEY'S LAZY BIT IS [false] -- see [uslot_of_urun_all]. *)
    uvis_lazy W = false ->
    (* ...AND ITS MASK IS FULL (upstream a083670): [urun] is keyed at
       [ProcDefs.secc_all], as it is at [false] above.  WHO SUPPLIES IT:
       userinit's first record, fork's copy, exec's keep
       ([SpecKexec.exec_slot_pre]'s mask row). *)
    uvis_secc W = ProcDefs.secc_all ->
    (* ...AND NO HONESTY ROW ON THE HELD SET (lane OFF-HAND-6's H3 emptied
       it, lane OFF-LINK-2's L6 deleted the field): a constructor says
       nothing about offsets and an entry may be taken at a key with a HELD
       descriptor, which is what makes a redirect child's exec provable
       (design/app-file.md SS3). *)
    (* THE DEPOSIT SUPPLIER, at the key the slot is being built for.  This
       is the one obligation the ARM adds to an entry constructor: whoever
       hands a program a [urun] says which syscall bundles it can pay and
       out of what.  [UexecCond.cond_entry_slot] passes the generic one
       ([Dsup := ssupply], every number admitted); a verified program's
       constructor passes its own. *)
    udep -∗
    (* ...AND THE PROCESS'S OWN KNOWLEDGE OF ITS EXIT PAYLOAD.  A [urun]
       carries it ([ChildTok.my_pay] at the key's generation) because the
       exit leaf pays the trap loop's deposit row out of it
       ([UkRunSys.wp_uk_ecall_exit]), and a constructor is the only place
       it can enter: the record it mints is what fixes [ukn_pay].  The
       kernel is what hands it over -- fork through the child slot's
       premise, exec through [SpecKexec.exec_slot_pre]'s wands, and
       userinit at the trivial payload. *)
    (* ...AND WHETHER THE PROCESS'S TABLE HOLDS A PIPE ROW (design/pipe.md,
       "The exit path").  The run carries this between traps
       ([urun_nopipe]) and exit's bundle row is minted off it, so an ENTRY
       is where it comes in.  It is a fact about the key the kernel handed
       over and it travels the way every other such fact does:
       [SpecKexec.kexec_image_ok_fd] says an exec'd image's table IS the
       exec'ing process's, so a chain of pipe-free programs stays pipe-free
       and the boot process's table is [FdSlots.fdt0], all closed.  A
       program that means to call pipe(2) comes in on the right arm
       instead ([urun_nopipe_taint]). *)
    (* ...AND WHETHER IT ANSWERS FOR ITS OFFSETS (lane OFF-HAND-3, R1).
       [hs] is the set the minted record carries and this is the premise
       that makes it honest: a constructor may claim a set only if every
       unparked row of the key's table is in it.  Every landed entry
       passes [empty] at a table the kernel has just handed over
       ([SpecKexec.exec_slot_pre]'s all-parked row,
       [FdSlots.fdv_all_parked_fdt0] at the boot), and a constructor for a
       program that means to HOLD an offset half passes the slots it means
       to hold. *)
    urun_nopipe (uvis_fd W) -∗
    my_pay (uvis_gen W) Q -∗
    (∀ (N : uk_names Σ) (h : CpuId),
       (* the record's payload IS the one that came in, which is what lets
          the program's proof read its own [ukn_pay] *)
       ⌜ ukn_pay N = Q ⌝ -∗
       ⌜ usz_ok (uvis_sz W) ⌝ -∗
       usz (ukn_s N) (uvis_sz W) -∗
       utext_all (ukn_t N) (uvis_M W) (uvis_perm W) -∗
       (* THE LEDGER OF THE STANDARD STREAMS, at the states the resumed key
          carries.  It comes out here because it has to: the low [NSTD] keys
          are in [UserFd.ufd_map] by construction, so their fragments exist
          from the moment the authority does, and an exclusive fragment for
          a key already in the map can never be minted later.  A program
          that does not care about its standard streams drops it -- and then
          calls no allocating syscall, which is the honest reading of "it is
          not tracking its descriptors". *)
       ustd (ukn_fd N) (take NSTD (uvis_fd W)) -∗
       (* ...AND THE PROGRAM'S OWN HALF OF ITS WORKING DIRECTORY, at the
          inum the resumed key carries.  Same reason the ledger comes out
          here: this is where the process's [urun] is created, so it is
          where the tie between the program's half and the key's [cw]
          begins.  A program that never looks at its cwd drops it. *)
       ucwd (ukn_cwd N) (uvis_cwd W) -∗
       (* ...AND ITS OWN HALF OF ITS CHILDREN SET, at the very set the
          resumed key carries -- [∅] at every entry that exists today,
          because an entry constructor builds the FIRST run of a program
          and a program that has not forked has no children. *)
       uch (ukn_ch N) (uvis_ch W) -∗
       (* ...AND ITS OWN HALF OF ITS PID (lane TRAP-ROWS-4, B): the number
          the resumed key carries, at the record's own ghost name.  It is
          what a caller reads wait's reaping arm against
          ([UkRunSys.wp_uk_ecall_wait_null_live]) and what makes getpid(2)'s
          answer sayable.  A program that never asks drops it. *)
       upid (ukn_pid N) (bv_unsigned (uvis_pid W)) -∗
       ([∗ map] k ↦ b ∈ base.filter
             (fun kv : Z * bv 8 =>
                ~ (kv.1 < uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)))
             (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)),
          ubyteq (ukn_d N) DfracDiscarded k b) -∗
       urun N h (tf_resume_gpr0 (uvis_tf W)) (tf_resume_pc (uvis_tf W))
         avail -∗
       mWP (Loop : expr riscv_lang))
    -∗ uslot W.
  Proof using .
    intros Hal8 Hroom Hstk Hfdlen Hstop Hlzf Hscf.
    iIntros "#Hdep #Hnpx #Hpay Hprog". rewrite uslot_ukc /ukc Hlzf Hscf.
    iIntros (h xi C pt Rfd Rut HRut) "%Hlo %Hpm %Hlzr Hb".
    set (sz := uvis_sz W).
    assert (Hwf : proc_pt_wf pt)
      by (destruct Hlo as (_ & _ & _ & _ & _ & H); exact H).
    rewrite /uvb /uvb_F /user_ptm_inv_x.
    iDestruct "Hb" as
      "(Hamb & Hregs & %Hsz & (Htlb & Hlazy & %Hinj & %Hacc) &
        Hfrag & Hcfg & Hgpr & Hpc & Hrut & Hkont)".
    iDestruct (umem_lazy_bound pt sz (uvis_M W) Hwf Hsz with "Hlazy") as %Hcan.
    iMod (uheap_alloc (uvis_M W) (uvis_perm W) sz Hcan Hstop)
      as (γt γd γs) "(Hheap & Hszf & #Ht & Hd)".
    (* ...AND THE PROGRAM'S DESCRIPTOR AUTHORITY, minted here beside the
       heap's three names.  This is where a process's [urun] is created, so
       it is where its own view of its table begins -- at the view the
       resumed KEY carries, which is the view the kernel is handing it. *)
    iMod (ufd_alloc_std (uvis_fd W) ∅ Hfdlen (map_empty_subseteq _))
      as (γfd) "(Hufd & Hstd & _)".
    (* ...AND THE WORKING DIRECTORY'S PAIR, at the inum the resumed key
       carries: the authority stays in the [urun] being built, the
       fragment goes to the program. *)
    iMod (ucwd_alloc (uvis_cwd W)) as (γc) "[Hcwa Hcwf]".
    (* ...AND THE CHILDREN SET'S PAIR, at the set the resumed key carries:
       the authority stays in the [urun] being built, the fragment goes to
       the program. *)
    iMod (uch_alloc (uvis_ch W)) as (γch) "[Hcha Hchf]".
    (* ...AND THE PID'S PAIR, at the pid the resumed key carries: the
       authority stays in the [urun] being built (bundled with the
       children's -- [urun_ids]), the fragment goes to the program.  It is
       what lets the program NAME its own pid (lane TRAP-ROWS-4, B). *)
    iMod (upid_alloc (bv_unsigned (uvis_pid W))) as (γpid) "[Hpida Hpidf]".
    rewrite -/(utext_all γt (uvis_M W) (uvis_perm W)).
    (* ---- the cut at the entry sp ---- *)
    set (sp := tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1).
    set (D := udata_lo (uvis_M W) (uvis_perm W) sz).
    iDestruct (umap_split_at γd D (uint sp) with "Hd") as "[Dlo Dhi]".
    iMod (uarea_persist γd _ with "Dhi") as "#Dhi".
    (* ---- the frame, out of what is below sp ---- *)
    set (base := (uint sp - 8 * Z.of_nat avail)%Z).
    set (f := fun j : nat =>
                default (bv_0 8)
                  (base.filter (fun kv : Z * bv 8 => kv.1 < uint sp) D
                     !! (base + Z.of_nat j)%Z)).
    assert (Hf : forall j : nat, (j < 8 * avail)%nat ->
                   base.filter (fun kv : Z * bv 8 => kv.1 < uint sp) D
                     !! (base + Z.of_nat j)%Z = Some (f j)).
    { intros j Hj. destruct (Hstk j Hj) as [b Hb].
      assert (Hb' : base.filter (fun kv : Z * bv 8 => kv.1 < uint sp) D
                      !! (base + Z.of_nat j)%Z = Some b)
        by (apply umap_filter_lookup_lt; [ unfold base; lia | exact Hb ]).
      unfold f. rewrite Hb'. reflexivity. }
    iDestruct (ubytes_of_map γd
                 (base.filter (fun kv : Z * bv 8 => kv.1 < uint sp) D)
                 base (8 * avail) f Hf with "Dlo") as "Hbs".
    iDestruct (ustack_of_ubytes γd sp avail f Hal8 Hroom with "Hbs") as "Hstk".
    iSpecialize ("Hprog" $! (MkUkNames γt γd γs γfd γc γch Q γpid) h
                   with "[%] [%] Hszf Ht Hstd Hcwf Hchf Hpidf Dhi");
      [ reflexivity | exact Hsz | ].
    iApply "Hprog".
    iExists xi, C, pt, Rfd, Rut, sz, (uvis_M W), (uvis_perm W), (uvis_fd W),
      (uvis_cwd W), (uvis_gen W), (uvis_ch W), (uvis_pid W).
    iSplitR; [ iPureIntro; exact Hlo | ].
    iSplitR; [ iPureIntro; exact Hpm | ].
    iSplitR; [ iPureIntro; exact (Hlzr eq_refl) | ].
    iSplitR; [ iPureIntro; exact HRut | ].
    (* the record is minted at [Q], so the payload the constructor was
       handed IS the run's [ukn_pay N (-1)] *)
    (* the two identity authorities go in as ONE conjunct ([urun_ids]) *)
    iDestruct (urun_ids_intro (MkUkNames γt γd γs γfd γc γch Q γpid)
                 (uvis_ch W) (uvis_pid W) with "Hcha Hpida") as "Hcha".
    iFrame "Hheap Hstk Hufd Hcwa Hcha Hpay Hdep".
    iSplitR; [ rewrite /urun_rows; iExact "Hnpx" | ].
    rewrite /uvb /uvb_F /user_ptm_inv_x.
    iFrame "Hamb Hregs Hfrag Hcfg Hgpr Hpc Hrut Hkont Htlb Hlazy".
    iPureIntro. split_and!; [ exact Hsz | exact Hinj | exact Hacc ].
  Qed.

End UkRun.
