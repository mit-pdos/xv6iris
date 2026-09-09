(* ===================================================================== *)
(* UserCwd.v -- THE PROCESS'S WORKING DIRECTORY, AS A RESOURCE.           *)
(*                                                                        *)
(* The key a user process is resumed at carries its working directory's   *)
(* inum ([UexecSlot.uvis_cwd], the kernel's [ProcDefs.pv_cwi]), and        *)
(* [UkRun.urun] binds it existentially exactly as it binds the image, the  *)
(* break and the descriptor view.  A program that never looks at its cwd   *)
(* therefore never names it.  A program that DOES -- one whose exec        *)
(* deposit is a claim about a path, which is a claim about the directory   *)
(* the path is resolved from -- needs a carrier for the claim that its     *)
(* working directory is inum [c], and that carrier is this file.           *)
(*                                                                        *)
(* THE SHAPE IS [UserFd]'s, one value wide.  A descriptor table is a ghost *)
(* map because its slots move independently; a working directory is ONE    *)
(* inum, so the ghost is one variable split in half:                       *)
(*                                                                        *)
(*   ucwd_auth γc c   the ENGINE's half, inside [UkRun.urun], pinned to    *)
(*                    the very [cw] the trap key is at -- that pinning is  *)
(*                    the whole content of the resource, and it is why the *)
(*                    half has to live in [urun] and not beside it.        *)
(*   ucwd γc c        the PROGRAM's half, a separable resource a proof     *)
(*                    carries into a subroutine, frames across unrelated   *)
(*                    calls, and hands to the syscall that reads it.       *)
(*                                                                        *)
(* WHY HALVES AND NOT A PERSISTENT PIN.  chdir moves the cwd               *)
(* ([UsysMemOk.usys_cwd_ok]'s one non-quiet row), so the value must be     *)
(* updatable; an update needs the whole variable, so each side holds       *)
(* enough that neither can move it alone.  Every other syscall keeps the   *)
(* cwd ([UsysMemOk.usys_cwd_ok_quiet]), so the program's half rides        *)
(* through a call untouched and no leaf but chdir's mentions it.           *)
(* ===================================================================== *)
From Stdlib Require Import ZArith.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
Local Open Scope Z_scope.

Section UserCwd.
  (* the same [ghost_varG Σ Z] the break rides on ([UserHeap.usz]) -- no
     new camera, so the whole-system functor list is unchanged *)
  Context `{!ghost_varG Σ Z}.

  (* the ENGINE's half: [UkRun.urun] carries it at the key's [uvis_cwd] *)
  Definition ucwd_auth (γc : gname) (c : Z) : iProp Σ :=
    ghost_var γc (1/2) c.

  (* the PROGRAM's half *)
  Definition ucwd (γc : gname) (c : Z) : iProp Σ :=
    ghost_var γc (1/2) c.

  Global Instance ucwd_auth_timeless γc c : Timeless (ucwd_auth γc c).
  Proof. apply _. Qed.
  Global Instance ucwd_timeless γc c : Timeless (ucwd γc c).
  Proof. apply _. Qed.

  (* the fragment READS the engine's half: this is the lemma the whole
     resource exists for, and it is why the authority sits INSIDE [urun]
     rather than beside it -- [cw] is bound by [urun]'s own existential, so
     a program learns it only by agreement. *)
  Lemma ucwd_agree (γc : gname) (c c' : Z) :
    ucwd_auth γc c -∗ ucwd γc c' -∗ ⌜ c = c' ⌝.
  Proof.
    iIntros "H1 H2". iDestruct (ghost_var_agree with "H1 H2") as %->. done.
  Qed.

  (* ...and BOTH halves move it, which is what chdir will spend. *)
  Lemma ucwd_update (γc : gname) (c c' c'' : Z) :
    ucwd_auth γc c -∗ ucwd γc c' ==∗ ucwd_auth γc c'' ∗ ucwd γc c''.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %->.
    iMod (ghost_var_update_2 c'' with "H1 H2") as "[$ $]"; [ | done ].
    rewrite Qp.half_half. reflexivity.
  Qed.

  (* the mint, at the cwd the key carries: an entry constructor keeps the
     authority in the [urun] it is building and hands the fragment to the
     program. *)
  Lemma ucwd_alloc (c : Z) :
    ⊢ |==> ∃ γc : gname, ucwd_auth γc c ∗ ucwd γc c.
  Proof.
    iMod (ghost_var_alloc c) as (γc) "Hc".
    iEval (rewrite -Qp.half_half) in "Hc".
    iDestruct (ghost_var_split with "Hc") as "[HA HF]".
    iModIntro. iExists γc. iFrame "HA HF".
  Qed.

  (* A FRAGMENT AT A VALUE THE CARRIER IS NOT READING -- [UserFd.ustd_any]'s
     shape.  A program that holds its cwd only so that it can hand it to a
     chdir it does not care about the result of carries THIS, which has no
     index and therefore costs its lemma statements one resource and no
     binder. *)
  Definition ucwd_any (γc : gname) : iProp Σ :=
    (∃ c : Z, ucwd γc c)%I.

  Global Instance ucwd_any_timeless γc : Timeless (ucwd_any γc).
  Proof. apply _. Qed.

  Lemma ucwd_any_of (γc : gname) (c : Z) : ucwd γc c -∗ ucwd_any γc.
  Proof. iIntros "H". iExists c. iExact "H". Qed.

End UserCwd.
