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
From Stdlib Require Import ZArith Bool Lia List.
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
  ukn_pay : Z -> iProp Σ
}.
Global Arguments MkUkNames {_} _ _ _ _ _ _ _.
Global Arguments ukn_t {_} _.
Global Arguments ukn_d {_} _.
Global Arguments ukn_s {_} _.
Global Arguments ukn_fd {_} _.
Global Arguments ukn_cwd {_} _.
Global Arguments ukn_ch {_} _.
Global Arguments ukn_pay {_} _.

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
  Definition udep : iProp Σ :=
    (□ Dsup ∗
     ⌜ forall (n : Z) (W : uvis),
         psok n -> n <> USYS_exec ->
         ⊢ □ Dsup ==∗ sbundle uslot n W ⌝)%I.

  Global Instance udep_persistent : Persistent udep.
  Proof. rewrite /udep. apply _. Qed.

  (* what a leaf does with it: mint the deposit the ecall arm asks for *)
  Lemma udep_dep (n : Z) (W : uvis) :
    psok n -> n <> USYS_exec -> udep -∗ |==> sbundle uslot n W.
  Proof.
    intros Hok Hne. iIntros "[#Hs %Hlaw]".
    iApply (Hlaw n W Hok Hne). iExact "Hs".
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
       (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname),
       my_pay gn (ukn_pay N) -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
       (⌜psok n /\ n <> USYS_exec⌝
        ∨ sbundle uslot n (uvis_of_run m pc M pm sz fdv cw gn cs)))%I.

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
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
       (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname),
       my_pay gn (ukn_pay N) -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
       sbundle_at uslot n fdep (uvis_of_run m pc M pm sz fdv cw gn cs))%I.

  Lemma udepwf_udepw (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) (fdep : sfam) :
    udepwf N m pc n fdep -∗ udepw N m pc n.
  Proof.
    rewrite /udepwf /udepw. iIntros "H" (M pm sz fdv cw gn cs) "Hp Hh Hf".
    iDestruct ("H" $! M pm sz fdv cw gn cs with "Hp Hh Hf") as "(Hh & Hf & Hb)".
    iFrame "Hh Hf". iRight. iExists fdep. iExact "Hb".
  Qed.

  (* the GENERIC route's supplier: a number the program admits *)
  Lemma udepw_of_psok (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) :
    psok n -> n <> USYS_exec -> ⊢ udepw N m pc n.
  Proof.
    intros Hok Hne. rewrite /udepw. iIntros (M pm sz fdv cw gn cs) "_ Hh Hf".
    iFrame "Hh Hf". iLeft. iPureIntro. exact (conj Hok Hne).
  Qed.

  (* THE LEAF'S USE OF IT, at every number including exec: the left
     disjunct carries [n <> USYS_exec] itself, so at exec only the explicit
     deposit can have been taken and no side condition is owed here. *)
  (* ...UNDER A BASIC UPDATE, since the law is (UexecSG.v's header).  Every
     call site is inside its leaf's own WP goal, which absorbs it. *)
  Lemma udepw_mint (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
      (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname) :
    udep -∗ my_pay gn (ukn_pay N) -∗ udepw N m pc n -∗
    uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv ==∗
    uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
    sbundle uslot n (uvis_of_run m pc M pm sz fdv cw gn cs).
  Proof.
    iIntros "#Hdep #Hmp Hsb Hheap Hufd".
    iDestruct ("Hsb" $! M pm sz fdv cw gn cs with "Hmp Hheap Hufd")
      as "(Hheap & Hufd & [%Hok | Hb])"; iFrame "Hheap Hufd";
      [ iApply (udep_dep n _ (proj1 Hok) (proj2 Hok) with "Hdep")
      | by iModIntro ].
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
  Definition uxsup : iProp Σ := (□ ∀ W : uvis, sbundle uslot USYS_exec W)%I.

  Global Instance uxsup_persistent : Persistent uxsup.
  Proof. rewrite /uxsup. apply _. Qed.

  (* what an exec leaf's caller does with it: the explicit disjunct of
     [udepw], at whatever key the walk has reached *)
  Lemma udepw_of_uxsup (N : uk_names Σ) (m : regfile) (pc : mword 64) :
    uxsup -∗ udepw N m pc USYS_exec.
  Proof.
    iIntros "#Hx" (M pm sz fdv cw gn cs) "_ Hh Hf". iFrame "Hh Hf". iRight.
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
       (fdv : list fdstate) (gn : gname) (cs : gset gname),
       my_pay gn (ukn_pay N) -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
       (⌜psok n /\ n <> USYS_exec⌝
        ∨ sbundle uslot n (uvis_of_run m pc M pm sz fdv c gn cs)))%I.

  (* [udepw] IS THE ∀-CWD FORM, one direction.  The two differ only in
     where the [cw] binder sits, so the equivalence holds both ways; this
     is the direction a caller holding a [udepw] needs, and stating it
     rather than redefining [udepw] as [∀ cw, udepw_at … cw] is what keeps
     the ∀-ORDER at [udepw]'s twenty-odd use sites ([iDestruct ("Hsb" $! M
     pm sz fdv cw)]) unmoved. *)
  Lemma udepw_at_of_udepw (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) (c : Z) :
    udepw N m pc n -∗ udepw_at N m pc n c.
  Proof.
    iIntros "Hd" (M pm sz fdv gn cs) "Hmp Hh Hf".
    iApply ("Hd" $! M pm sz fdv c gn cs with "Hmp Hh Hf").
  Qed.

  (* ...AND THE SUPPLIER THAT IGNORES THE LOAN: a caller that already has
     the bundle at every [(M, pm, sz, fdv)] of this one cwd hands it back
     unread.  [udepw_at] is WEAKER to supply than the bare family, which is
     why the leaf can take it in the bare one's place. *)
  Lemma udepw_at_of_bundle (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) (c : Z) :
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
       (fdv : list fdstate) (gn : gname) (cs : gset gname),
       sbundle uslot n (uvis_of_run m pc M pm sz fdv c gn cs)) -∗
    udepw_at N m pc n c.
  Proof.
    iIntros "Hb" (M pm sz fdv gn cs) "_ Hh Hf". iFrame "Hh Hf". iRight.
    iApply "Hb".
  Qed.

  (* the trivial supplier at the ∀-key form, through the two above *)
  Lemma udepw_at_of_uxsup (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (c : Z) :
    uxsup -∗ udepw_at N m pc USYS_exec c.
  Proof.
    iIntros "#Hx". iApply udepw_at_of_bundle. iIntros (M pm sz fdv gn cs).
    iApply "Hx".
  Qed.

  (* THE LEAF'S USE OF IT, [udepw_mint]'s shape at the fixed cwd *)
  Lemma udepw_at_mint (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (n : Z) (c : Z) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm)
      (sz : Z) (fdv : list fdstate) (gn : gname) (cs : gset gname) :
    udep -∗ my_pay gn (ukn_pay N) -∗ udepw_at N m pc n c -∗
    uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv ==∗
    uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
    sbundle uslot n (uvis_of_run m pc M pm sz fdv c gn cs).
  Proof.
    iIntros "#Hdep #Hmp Hsb Hheap Hufd".
    iDestruct ("Hsb" $! M pm sz fdv gn cs with "Hmp Hheap Hufd")
      as "(Hheap & Hufd & [%Hok | Hb])"; iFrame "Hheap Hufd";
      [ iApply (udep_dep n _ (proj1 Hok) (proj2 Hok) with "Hdep")
      | by iModIntro ].
  Qed.

  Definition urun (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) : iProp Σ :=
    (∃ (xi : TsoCtx.CurCtx) (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ)
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
       (gn : gname) (cs : gset gname),
       ⌜ loop_ok C pt ⌝ ∗ ⌜ perm_of (ud_um pt) sz = pm ⌝ ∗
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
       uch_auth (ukn_ch N) cs ∗
       (* ...AND THE PROCESS'S OWN KNOWLEDGE OF ITS EXIT PAYLOAD, at the
          generation the key carries.  PERSISTENT, so it costs no leaf
          anything to thread; it is here because [gn] is bound by this
          existential and this is therefore the only place the record's
          [ukn_pay] can be tied to the process's actual generation.  It is
          what exit's leaf pays the trap loop's deposit row with
          ([UexecRet.uexec_pay_dep]), and it is what an entry constructor
          receives and mints the record at. *)
       my_pay gn (ukn_pay N) ∗
       (* ...AND THE PAYLOAD ITSELF, AT THE KILL STATUS.  Linear, and it
          lives HERE rather than in the kernel's block because it is the
          PROGRAM's between traps: a process that was lent a resource goes
          on holding it while it runs.  Every kernel entry takes it
          ([UexecRet.uexec_pay_dep]) and every resume hands it back
          ([uexec_pay_arm]); the kernel spends it only on the kill path,
          where the process's own continuation is never delivered and
          nothing the program does could pay.  At [ukn_triv] it is [True]
          and costs nothing. *)
       ukn_pay N (-1) ∗
       udep ∗
       uvb (CID := h) (XI := xi) C pt Rfd Rut sz pm fdv cw gn cs M m pc)%I.

  (* THE ROUND'S EFFECT ON THE CWD, AT EVERY NUMBER BUT CHDIR.  A leaf
     re-closes [urun] at the [cw'] the round resumed the process at, and
     [UsysMemOk.usys_cwd_ok_quiet] says that is the [cw] it trapped from.
     Re-keying the engine's half by that equation is the ONLY thing a leaf
     has to do about the working directory, and it is why the program's
     half rides through every call untouched.  [UserFd.ufd_auth_quiet]'s
     twin, one value wide. *)
  Lemma ucwd_auth_quiet (N : uk_names Σ) (cw cw' : Z) :
    cw' = cw -> ucwd_auth (ukn_cwd N) cw -∗ ucwd_auth (ukn_cwd N) cw'.
  Proof. intros ->. iIntros "$". Qed.

  (* THE MOVER, for the day a chdir leaf exists.  [UsysMemOk.usys_cwd_ok]
     has exactly one non-quiet row and no leaf takes it yet; when one does,
     this is the step it runs, with the new inum coming off the row. *)
  Lemma ucwd_move (N : uk_names Σ) (c c' : Z) :
    ucwd_auth (ukn_cwd N) c -∗ ucwd (ukn_cwd N) c ==∗
    ucwd_auth (ukn_cwd N) c' ∗ ucwd (ukn_cwd N) c'.
  Proof. iApply ucwd_update. Qed.

  (* THE ROUND'S EFFECT ON THE CHILDREN SET, AT EVERY NUMBER.  This lane's
     row ([UsysMemOk.usys_ch_ok]) is the identity everywhere, so a leaf
     re-closes [urun] at the very set it trapped from and this re-key is
     all it has to do.  [ucwd_auth_quiet]'s twin; fork's, wait's and
     exit's leaves will spend [uch_move] instead. *)
  Lemma uch_auth_quiet (N : uk_names Σ) (cs cs' : gset gname) :
    cs' = cs -> uch_auth (ukn_ch N) cs -∗ uch_auth (ukn_ch N) cs'.
  Proof. intros ->. iIntros "$". Qed.

  (* THE MOVER, for the day a fork/wait/exit leaf moves the set. *)
  Lemma uch_move (N : uk_names Σ) (S S' : gset gname) :
    uch_auth (ukn_ch N) S -∗ uch (ukn_ch N) S ==∗
    uch_auth (ukn_ch N) S' ∗ uch (ukn_ch N) S'.
  Proof. iApply uch_update. Qed.

  (* "this instruction does not write sp".  Every leaf that writes a general
     register carries it; a concrete [rd] decides it by [vm_compute]. *)
  Definition unot_sp (rd : mword 5) : Prop := Regidx csp_rs1 <> Regidx rd.

  Lemma unot_sp_upd (rd : mword 5) (v : mword 64) (m : regfile) :
    unot_sp rd -> (<[Regidx rd := v]> m) !!! Regidx csp_rs1 = m !!! Regidx csp_rs1.
  Proof. intro H. exact (upd_ne m (Regidx rd) (Regidx csp_rs1) v H). Qed.

  (* THE CLOSE.  This is the lemma that makes the whole interface work: a
     continuation phrased on [urun] discharges the ∀-quantified [ukc] that
     every existing leaf demands, because [urun] supplies its own ambient. *)
  (* [sz] is a parameter: [urun] hides the break existentially, but a leaf
     that is closing back up has just destructed it, so it can say which one.
     Re-introducing the existential at THAT size is all this does. *)
  Lemma urun_close (N : uk_names Σ) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm)
      (sz : Z) (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname)
      (m : regfile) (pc : mword 64)
      (avail : nat) :
    uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
    ustack (ukn_d N) (m !!! Regidx csp_rs1) avail -∗
    (* ...and the descriptor authority, at the same [fdv] the key is at *)
    ufd_auth (ukn_fd N) fdv -∗
    (* ...and the cwd authority, at the same [cw] the key is at *)
    ucwd_auth (ukn_cwd N) cw -∗
    (* ...and the children authority, at the same [cs] the key is at *)
    uch_auth (ukn_ch N) cs -∗
    (* ...and the process's own knowledge of its exit payload, back at the
       same generation -- persistent, like the supplier below *)
    my_pay gn (ukn_pay N) -∗
    (* ...AND THE PAYLOAD THE RUN KEEPS, which is what this close HANDS THE
       ENGINE: the conclusion is the continuation WITH the payment beside it
       ([UexecRet.ukcq]), because an interrupt can trap between any two
       instructions and the kernel has to be paid there too.  The run the
       continuation rebuilds is at the payload the engine HANDS BACK -- the
       same predicate, by the family the deposit and the arm share. *)
    ukn_pay N (-1) -∗
    (* the deposit supplier and its law, back at the same key -- persistent,
       so a leaf that destructed [urun] hands the very copy it read *)
    udep -∗
    (∀ h : CpuId, urun N h m pc avail -∗ WP (Loop : expr riscv_lang)) -∗
    ukcq (ukn_pay N) pm M sz fdv cw gn cs m pc.
  Proof.
    iIntros "Hheap Hstk Hufd Hcwd Hch #Hmy Hpay #Hdep Hcont".
    rewrite /ukcq. iFrame "Hmy Hpay". iIntros "Hpay".
    rewrite /ukc. iIntros (h xi C pt Rfd Rut HRut) "%Hlo %Hpm Hb".
    iApply ("Hcont" $! h).
    iExists xi, C, pt, Rfd, Rut, sz, M, pm, fdv, cw, gn, cs.
    iFrame "Hheap Hstk Hufd Hcwd Hch Hmy Hpay Hdep Hb". iPureIntro.
    split_and!; [ exact Hlo | exact Hpm | exact HRut ].
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
  Proof.
    intros Hns [[_ ->] | [_ ->]]; [ reflexivity | ].
    cbn [uv_upd]. exact (unot_sp_upd rd (regval_into_reg d) m Hns).
  Qed.

  (* ...and the same when the instruction WROTE a register: the free stack
     is keyed by sp, and [unot_sp] says this write was not to sp. *)
  Lemma urun_close_upd (N : uk_names Σ) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (m : regfile) (rd : mword 5) (v : mword 64)
      (sz : Z) (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname)
      (pc' : mword 64) (avail : nat) :
    unot_sp rd ->
    uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
    ustack (ukn_d N) (m !!! Regidx csp_rs1) avail -∗
    ufd_auth (ukn_fd N) fdv -∗
    ucwd_auth (ukn_cwd N) cw -∗
    uch_auth (ukn_ch N) cs -∗
    my_pay gn (ukn_pay N) -∗
    ukn_pay N (-1) -∗
    udep -∗
    (∀ h : CpuId, urun N h (<[Regidx rd := v]> m) pc' avail -∗
                  WP (Loop : expr riscv_lang)) -∗
    ukcq (ukn_pay N) pm M sz fdv cw gn cs (<[Regidx rd := v]> m) pc'.
  Proof.
    intros Hns. iIntros "Hheap Hstk Hufd Hcwd Hch #Hmy Hpay #Hdep Hcont".
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwd Hch Hmy Hpay Hdep Hcont").
    rewrite (unot_sp_upd rd v m Hns). iExact "Hstk".
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
  Proof.
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
  Proof.
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
  Proof.
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
  Proof.
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
  Proof.
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
  Proof.
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
  (* [uheap] bounds every owned address below MAXVA -- so "sp has n words   *)
  (* of room below it" is a CONSEQUENCE of holding the free stack, not an   *)
  (* obligation on whoever moves sp.  The sp-adjust rules take neither as   *)
  (* a premise.                                                            *)
  (* ===================================================================== *)
  Lemma ustack_room (γt γd γs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz : Z) (sp : mword 64) (n : nat) :
    uheap γt γd γs M pm sz -∗ ustack γd sp n -∗ ⌜ 8 * Z.of_nat n <= uint sp ⌝.
  Proof.
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
  Proof.
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
  Proof.
    iIntros "Hrun".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hcwd & Hch & #Hdep & Hb)".
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
  Lemma umem_lazy_bound {CIDL : CpuId} {XIL : TsoCtx.CurCtx} (pt : uptd) (sz : Z) (M : gmap Z (bv 8)) :
    proc_pt_wf pt -> usz_ok sz ->
    umem_lazy_x pt sz M -∗ ⌜ forall a : Z, is_Some (M !! a) -> 0 <= a < 2 ^ 38 ⌝.
  Proof.
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
  Proof.
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
    my_pay (uvis_gen W) Q -∗
    (* ...AND THE PAYLOAD ITSELF, at the kill status.  A constructor is
       where it enters, as the fact is: the run this builds carries it
       between traps ([urun]'s own conjunct), hands it to the kernel at
       every entry and is handed it back at every resume.  Whoever builds
       the slot supplies it -- fork's child arm out of the payload the
       parent chose, exec through [SpecKexec.exec_slot_pre]'s wands, and
       userinit at the trivial payload, where it is [True]. *)
    Q (-1) -∗
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
       WP (Loop : expr riscv_lang))
    -∗ uslot W.
  Proof.
    intros Hal8 Hroom Hstk Hfdlen Hstop. iIntros "#Hdep #Hpay Hpayv Hprog".
    rewrite uslot_ukc /ukc.
    iIntros (h xi C pt Rfd Rut HRut) "%Hlo %Hpm Hb".
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
    iSpecialize ("Hprog" $! (MkUkNames γt γd γs γfd γc γch Q) h
                   with "[%] [%] Hszf Ht Hstd Hcwf Hchf Dlo Dtop");
      [ reflexivity | exact Hsz | ].
    iApply "Hprog".
    iExists xi, C, pt, Rfd, Rut, sz, (uvis_M W), (uvis_perm W), (uvis_fd W),
      (uvis_cwd W), (uvis_gen W), (uvis_ch W).
    iSplitR; [ iPureIntro; exact Hlo | ].
    iSplitR; [ iPureIntro; exact Hpm | ].
    iSplitR; [ iPureIntro; exact HRut | ].
    (* the record is minted at [Q], so the payload the constructor was
       handed IS the run's [ukn_pay N (-1)] *)
    iFrame "Hheap Hstk Hufd Hcwa Hcha Hpay Hpayv Hdep".
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
    my_pay (uvis_gen W) Q -∗
    (* ...AND THE PAYLOAD ITSELF, at the kill status.  A constructor is
       where it enters, as the fact is: the run this builds carries it
       between traps ([urun]'s own conjunct), hands it to the kernel at
       every entry and is handed it back at every resume.  Whoever builds
       the slot supplies it -- fork's child arm out of the payload the
       parent chose, exec through [SpecKexec.exec_slot_pre]'s wands, and
       userinit at the trivial payload, where it is [True]. *)
    Q (-1) -∗
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
       urun N h (tf_resume_gpr0 (uvis_tf W)) (tf_resume_pc (uvis_tf W))
         avail -∗
       WP (Loop : expr riscv_lang))
    -∗ uslot W.
  Proof.
    intros Hal8 Hroom Hstk Hfdlen Hstop. iIntros "#Hdep #Hpay Hpayv Hprog". rewrite uslot_ukc /ukc.
    iIntros (h xi C pt Rfd Rut HRut) "%Hlo %Hpm Hb".
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
    iSpecialize ("Hprog" $! (MkUkNames γt γd γs γfd γc γch Q) h
                   with "[%] [%] Hszf Ht Hstd Hcwf Hchf");
      [ reflexivity | exact Hsz | ].
    iApply "Hprog".
    iExists xi, C, pt, Rfd, Rut, sz, (uvis_M W), (uvis_perm W), (uvis_fd W),
      (uvis_cwd W), (uvis_gen W), (uvis_ch W).
    iSplitR; [ iPureIntro; exact Hlo | ].
    iSplitR; [ iPureIntro; exact Hpm | ].
    iSplitR; [ iPureIntro; exact HRut | ].
    (* the record is minted at [Q], so the payload the constructor was
       handed IS the run's [ukn_pay N (-1)] *)
    iFrame "Hheap Hstk Hufd Hcwa Hcha Hpay Hpayv Hdep".
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
    my_pay (uvis_gen W) Q -∗
    (* ...AND THE PAYLOAD ITSELF, at the kill status.  A constructor is
       where it enters, as the fact is: the run this builds carries it
       between traps ([urun]'s own conjunct), hands it to the kernel at
       every entry and is handed it back at every resume.  Whoever builds
       the slot supplies it -- fork's child arm out of the payload the
       parent chose, exec through [SpecKexec.exec_slot_pre]'s wands, and
       userinit at the trivial payload, where it is [True]. *)
    Q (-1) -∗
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
       ([∗ map] k ↦ b ∈ base.filter
             (fun kv : Z * bv 8 =>
                ~ (kv.1 < uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)))
             (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)),
          ubyteq (ukn_d N) DfracDiscarded k b) -∗
       urun N h (tf_resume_gpr0 (uvis_tf W)) (tf_resume_pc (uvis_tf W))
         avail -∗
       WP (Loop : expr riscv_lang))
    -∗ uslot W.
  Proof.
    intros Hal8 Hroom Hstk Hfdlen Hstop. iIntros "#Hdep #Hpay Hpayv Hprog". rewrite uslot_ukc /ukc.
    iIntros (h xi C pt Rfd Rut HRut) "%Hlo %Hpm Hb".
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
    iSpecialize ("Hprog" $! (MkUkNames γt γd γs γfd γc γch Q) h
                   with "[%] [%] Hszf Ht Hstd Hcwf Hchf Dhi");
      [ reflexivity | exact Hsz | ].
    iApply "Hprog".
    iExists xi, C, pt, Rfd, Rut, sz, (uvis_M W), (uvis_perm W), (uvis_fd W),
      (uvis_cwd W), (uvis_gen W), (uvis_ch W).
    iSplitR; [ iPureIntro; exact Hlo | ].
    iSplitR; [ iPureIntro; exact Hpm | ].
    iSplitR; [ iPureIntro; exact HRut | ].
    (* the record is minted at [Q], so the payload the constructor was
       handed IS the run's [ukn_pay N (-1)] *)
    iFrame "Hheap Hstk Hufd Hcwa Hcha Hpay Hpayv Hdep".
    rewrite /uvb /uvb_F /user_ptm_inv_x.
    iFrame "Hamb Hregs Hfrag Hcfg Hgpr Hpc Hrut Hkont Htlb Hlazy".
    iPureIntro. split_and!; [ exact Hsz | exact Hinj | exact Hacc ].
  Qed.

End UkRun.
