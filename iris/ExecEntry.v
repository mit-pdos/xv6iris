(* ===================================================================== *)
(* ExecEntry.v -- THE EXEC'D PROGRAM'S OWN PROMISE AT ITS KEY, NAMED.     *)
(*                                                                       *)
(* design/user-exec.md section 1's obligation (E).  An exec bundle fuses  *)
(* three separable things: the RESOLUTION of the path (the walk and the   *)
(* observation, [PinnedObs] at a pin, owned shares at a fragment          *)
(* supplier), the LOADABILITY of the file ([ElfLoadable.                  *)
(* kexec_loadable_of_b], one decision), and the ENTRY -- if the kernel   *)
(* builds a key out of THIS file, my program runs there.  Only the third *)
(* is about the program, and this file is the only place it is spelled.   *)
(*                                                                       *)
(* WHAT IT IS.  [SpecKexec.exec_slot_pre]'s arm (a) hands the caller a    *)
(* key [W'] together with everything the kernel proved about it -- the    *)
(* image fact [kexec_image_ok f na alen afun sts W'], the four identity   *)
(* rows (cwd, lazy, children, pid), and the exec'ing process's pay fact   *)
(* -- and asks for the new image's WP at that key.  A caller that pins    *)
(* the file it is willing to run answers with a [□]-constructor of        *)
(* exactly that shape; [PinnedExec.pex_slot] took it as an anonymous      *)
(* premise, and every program-side supplier restated it.  Named, it is a  *)
(* definition two program proofs can be stated at and an assembly can     *)
(* take as a premise.                                                     *)
(*                                                                       *)
(* WHY THE CALLER'S DATA IS IN THE STATEMENT (the EX-1 ruling).  The      *)
(* design page writes the entry as [image_entry f Q Pay X], as if the     *)
(* program's key were the only input.  It is not: the rows the kernel     *)
(* proves are EQUATIONS against the CALLER's readings ([uvis_cwd W' = cw] *)
(* -- exec inherits the working directory; [uvis_ch W' = cs] and          *)
(* [uvis_pid W' = pidv] -- exec keeps the process; [uvis_fd W' = sts] --  *)
(* exec closes no descriptor), and a program that reads any of them needs *)
(* the caller's value in its own statement.  sh reads all four (its       *)
(* pinned open of console is at [ROOTINO], its wait redeems one child,  *)
(* its table row is /init's).  So the six caller-side parameters are      *)
(* [sts], [cw], [cs], [pidv] and -- see below -- [M] and [av].            *)
(*                                                                       *)
(* AND WHY THE ARGUMENT READING IS IN IT (the second EX-1 ruling).        *)
(* [SpecSysExec.exec_args_of M av na alen afun] is the CALLER's reading   *)
(* of its own argv: not the shape of a vector but the pointers the        *)
(* caller's image holds at [av + 8i] and the strings they name.  The      *)
(* entry is [∀ na alen afun]-quantified -- the kernel quantifies them at  *)
(* the slot wand -- and NO verified program's entry holds at every        *)
(* argument vector: both landed entries need a ROOM bound                 *)
(* ([UShKernel.sh_slot_of_kexec]'s frame, [UShEcho.echo_slot_of_kexec]'s  *)
(* 96 bytes), which is an inequality about [alen] and [na] and is false   *)
(* for a big enough vector.  What discharges it is the caller's reading   *)
(* ([UInitSh.init_args_det], [UShEcho.echo_args_det]) -- so the reading   *)
(* has to be a premise the entry may consume, and leaving it on the       *)
(* assembly side would make both entries unprovable.  It is therefore    *)
(* relayed, exactly as [PinnedExec.pex_slot] relays it today.             *)
(*                                                                       *)
(* THE TWO SHAPES.  [image_entry_at] is the entry AT ONE argument shape   *)
(* -- the form a program proof is naturally in, and the form the kernel's *)
(* own boot call needs ([SpecKexec.exec_au_pre]: forkret hands            *)
(* [kexec(/init, …)] a literal vector, so there is no caller image to   *)
(* read one out of) -- and [image_entry] is the same thing under the      *)
(* caller's reading.  [image_entry_of_at] and [image_entry_at_of] are the *)
(* two directions between them; the reading is a pure premise, so moving  *)
(* it across the [∀] costs nothing.                                       *)
(*                                                                       *)
(* THE TAINT ARM [image_entry_taint] is the generic entry: a process that *)
(* answers for nothing runs on [UkRun.uxsup]'s family, which exists at    *)
(* every key given the taint and the pay fact.  It is the other half of   *)
(* every exec bundle, and it says nothing about [f] -- which is the whole *)
(* content of exec-ing an unverified binary is the same rule.          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map invariants.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import FdSlots.         (* [fdstate] *)
Require Import ChildTok.        (* [my_pay]: the exec wands' pay fact, and
                                   [ctokG] -- THE ONLY ghost class this file
                                   binds.  [Xv6G.xv6G] carries it as a FIELD
                                   instance ([xv6_ctok]), so a consumer that
                                   binds the bundle resolves these definitions
                                   at the same instance my_pay itself resolves
                                   at there; binding both here would be the
                                   two-providers-in-one-scope hazard
                                   (durable-notes, Typeclasses and
                                   ghost-class bundling). *)
Require Import UexecSlot.       (* [uvis] and its readings *)
Require Import ElfFile.         (* [elf_bytes] *)
Require Import SpecKexec.       (* [kexec_image_ok]: what the kernel built *)
Require Import SpecSysExec.     (* [exec_args_of]: the CALLER's argv reading *)
Import Defs.

Local Open Scope Z_scope.

Section ExecEntry.
  Context `{!ctokG Σ}.

  (* ------------------------------------------------------------------ *)
  (*  1.  THE ENTRY AT ONE ARGUMENT SHAPE                                 *)
  (* ------------------------------------------------------------------ *)

  (* [PinnedExec.pex_slot_at]'s [□]-constructor premise, verbatim: the
     image fact, the four identity rows, the pay fact and the program's
     own linear payload, concluding at the program's WP family [X].

     [Pay] is what the new image must OWN from birth -- sh's console
     lease and its position; for most programs it is [emp].  It goes to
     THIS arm only: the taint arm never hands a caller a constructor. *)
  Definition image_entry_at (f : elf_bytes) (na : nat) (alen : nat -> nat)
      (afun : nat -> nat -> bv 8) (sts : list fdstate)
      (cw : Z) (secc : mword 64) (cs : gset gname) (pidv : mword 32)
      (Q : Z -> iProp Σ) (Pay : iProp Σ) (X : uvis -d> iPropO Σ) : iProp Σ :=
    (□ (∀ W' : uvis,
          ⌜kexec_image_ok f na alen afun sts W'⌝ -∗
          ⌜uvis_cwd W' = cw⌝ -∗
          ⌜uvis_lazy W' = false⌝ -∗
          ⌜uvis_secc W' = secc⌝ -∗
          ⌜uvis_ch W' = cs⌝ -∗
          ⌜uvis_pid W' = pidv⌝ -∗
          (* NO ALL-PARKED ROW HERE (lane OFF-HAND-4, S2; design/app-file.md
             SS3 fact 4, RULED).  Lane OFF-HAND-3 relayed
             [SpecKexec.exec_slot_pre]'s row into this entry, and that is
             WRONG for a VERIFIED image: an entry that RECEIVES "the table
             is all parked" can never be entered with a held row, and the
             redirect child execs /echo holding [f] at a held offset.  The
             fact is not lost -- [kexec_image_ok] pins [uvis_fd W' = sts]
             ([SpecKexec.kexec_image_ok_fd]) and [sts] is a PARAMETER here,
             so an entry that wants the discipline states it about [sts] as
             its own premise and an entry that means to hold a row states
             the set instead ([UsysMemOk.fdv_held_in]).  The TAINT arm
             keeps a row, because the generic family really does need one:
             see [image_entry_taint]. *)
          my_pay (uvis_gen W') Q -∗ Pay -∗ X W'))%I.

  (* ------------------------------------------------------------------ *)
  (*  2.  THE ENTRY UNDER THE CALLER'S ARGUMENT READING                   *)
  (* ------------------------------------------------------------------ *)

  (* [PinnedExec.pex_slot]'s [□]-constructor premise, verbatim -- the
     shape a SYSCALL's bundle needs, where the argument shape is whatever
     the caller's image at [av] turns out to hold. *)
  Definition image_entry (f : elf_bytes) (M : gmap Z (bv 8)) (av : mword 64)
      (sts : list fdstate) (cw : Z) (secc : mword 64) (cs : gset gname) (pidv : mword 32)
      (Q : Z -> iProp Σ) (Pay : iProp Σ) (X : uvis -d> iPropO Σ) : iProp Σ :=
    (□ (∀ (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
          (W' : uvis),
          ⌜kexec_image_ok f na alen afun sts W'⌝ -∗
          ⌜uvis_cwd W' = cw⌝ -∗
          ⌜uvis_lazy W' = false⌝ -∗
          ⌜uvis_secc W' = secc⌝ -∗
          ⌜uvis_ch W' = cs⌝ -∗
          ⌜uvis_pid W' = pidv⌝ -∗
          (* ...and NO all-parked row -- [image_entry_at]'s note (lane
             OFF-HAND-4, S2) *)
          ⌜exec_args_of M av na alen afun⌝ -∗
          my_pay (uvis_gen W') Q -∗ Pay -∗ X W'))%I.

  (* ------------------------------------------------------------------ *)
  (*  3.  THE TAINT'S ENTRY                                               *)
  (* ------------------------------------------------------------------ *)

  (* ...AND IT TAKES NO ALL-PARKED ROW (lane OFF-HAND-6, H3;
     design/app-file.md SS3 fact 4).  It used to: lanes OFF-HAND-3/4/5 each
     carried a row saying the key's table had no descriptor with its offset
     half outside the kernel, on the theory that a generic family could
     never be handed such a descriptor.  Fact 4 makes the theory false and
     the row pointless in one step -- THE HALF IS IN THE DESCRIPTOR BUNDLE
     ([FdSlots.foff_row] at [OffHeld]), so the kernel holds it at every
     fire and a generic image's deposits owe nothing about offsets at any
     mode.  A held row therefore crosses an exec on BOTH arms, which is
     the whole point of the fact, and the two lemmas that used to carry the
     row from [sts] to the key ([SpecKexec.kexec_image_ok_parked] /
     [exec_key_ok_parked]) are consumer-less again.  NOTE the two provers
     never read it ([UShEchoPay], [UInitSh] both introduce it as [_]):
     what the row cost was the PREMISE on every builder, and that is what
     this deletes. *)
  Definition image_entry_taint (T : iProp Σ) (Q : Z -> iProp Σ)
      (X : uvis -d> iPropO Σ) : iProp Σ :=
    (□ (∀ W' : uvis, T -∗ my_pay (uvis_gen W') Q -∗ X W'))%I.

  Global Instance image_entry_at_persistent f na alen afun sts cw cs pidv
      Q Pay X :
    Persistent (image_entry_at f na alen afun sts cw secc cs pidv Q Pay X).
  Proof using . rewrite /image_entry_at. apply _. Qed.

  Global Instance image_entry_persistent f M av sts cw cs pidv Q Pay X :
    Persistent (image_entry f M av sts cw secc cs pidv Q Pay X).
  Proof using . rewrite /image_entry. apply _. Qed.

  Global Instance image_entry_taint_persistent T Q X :
    Persistent (image_entry_taint T Q X).
  Proof using . rewrite /image_entry_taint. apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (*  4.  THE TWO SHAPES ARE THE SAME THING                               *)
  (* ------------------------------------------------------------------ *)

  (* A program proved at each argument shape the caller's image admits IS
     an entry.  This is the step a program-side supplier takes: it reads
     [exec_args_of] -- which is a FUNCTION of the caller's image on the
     range that matters ([UInitSh.init_args_det], [UShEcho.echo_args_det])
     -- and then knows the vector its room bound is about. *)
  Lemma image_entry_of_at (f : elf_bytes) (M : gmap Z (bv 8)) (av : mword 64)
      (sts : list fdstate) (cw : Z) (secc : mword 64) (cs : gset gname) (pidv : mword 32)
      (Q : Z -> iProp Σ) (Pay : iProp Σ) (X : uvis -d> iPropO Σ) :
    □ (∀ (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8),
         ⌜exec_args_of M av na alen afun⌝ -∗
         image_entry_at f na alen afun sts cw secc cs pidv Q Pay X) -∗
    image_entry f M av sts cw secc cs pidv Q Pay X.
  Proof using .
    iIntros "#H". rewrite /image_entry. iIntros "!>" (na alen afun W')
      "%Hok %Hcw %Hlz %Hch %Hpid %Hargs Hp HPay".
    iDestruct ("H" $! na alen afun with "[%]") as "#He"; [ exact Hargs | ].
    rewrite /image_entry_at.
    iApply ("He" $! W' with "[%] [%] [%] [%] [%] Hp HPay");
      [ exact Hok | exact Hcw | exact Hlz | exact Hch | exact Hpid ].
  Qed.

  (* ...and back, at any shape the reading admits *)
  Lemma image_entry_at_of (f : elf_bytes) (M : gmap Z (bv 8)) (av : mword 64)
      (sts : list fdstate) (cw : Z) (secc : mword 64) (cs : gset gname) (pidv : mword 32)
      (Q : Z -> iProp Σ) (Pay : iProp Σ) (X : uvis -d> iPropO Σ)
      (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8) :
    exec_args_of M av na alen afun ->
    image_entry f M av sts cw secc cs pidv Q Pay X -∗
    image_entry_at f na alen afun sts cw secc cs pidv Q Pay X.
  Proof using .
    intros Hargs. iIntros "#H". rewrite /image_entry_at.
    iIntros "!>" (W') "%Hok %Hcw %Hlz %Hch %Hpid Hp HPay".
    rewrite /image_entry.
    iApply ("H" $! na alen afun W' with "[%] [%] [%] [%] [%] [%] Hp HPay");
      [ exact Hok | exact Hcw | exact Hlz | exact Hch | exact Hpid
      | exact Hargs ].
  Qed.

End ExecEntry.
