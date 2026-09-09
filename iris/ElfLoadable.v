(* ===================================================================== *)
(* ElfLoadable.v -- THE TWO VERIFIED IMAGES ARE FILES xv6's exec LOADS:   *)
(* [kexec_loadable ElfUser.sh_elf] and [kexec_loadable ElfUser.init_elf], *)
(* plus the COMPUTABLE form of [SpecKexec.kexec_loadable] they are proved *)
(* through.                                                              *)
(*                                                                       *)
(* WHY A FILE OF ITS OWN.  [kexec_loadable] is [SpecKexec]'s, so          *)
(* [ElfUser.v] -- which sits far below the Iris stack and is on           *)
(* [FsImgCheck]'s cone -- cannot name it; and the two [*Kernel.v] entry   *)
(* constructors deliberately reduce NOTHING of their program's dumped     *)
(* image ([UShKernel.v]'s header), so the [vm_compute] belongs neither    *)
(* there.  This file is the one place that pays it, in [ElfUser.v]'s own  *)
(* style: a decidable check reduced with a single [vm_cast_no_check].     *)
(*                                                                       *)
(* THE COMPUTABLE FORM.  [kexec_loadable] is four conjuncts, three of     *)
(* which are not [Decision]-shaped ([loads_ascending] is a [Prop]         *)
(* fixpoint, the header bound is an [exists], the phdr row a [Forall]).   *)
(* So each gets a boolean twin and a one-induction bridge, and the two    *)
(* instances below take [elf_wf] from [ElfUser]'s own theorem and reduce  *)
(* only the remaining three -- all of which read the file's HEADER and    *)
(* PROGRAM-HEADER TABLE, near the front, which is the cheap end of a      *)
(* whole-file [vm_compute] (claude-notes/design/elf.md).                  *)
(*                                                                       *)
(* WHERE THEY ARE SPENT.  The exec deposit's arm (a) takes               *)
(* [⌜kexec_loadable f⌝] beside the observation's receipt, and its arm (b) *)
(* is REFUTED from [~ anode_loadable a] once the pin says which file the  *)
(* observed node holds ([SpecKexec.exec_slot_pre]).                       *)
(*                                                                       *)
(* If a [vm_compute] here ever fails, DO NOT weaken the statement: the    *)
(* dumped binary is then not a file xv6's loader accepts, which is a fact *)
(* about the toolchain, not about this proof.                            *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List Bool.
From stdpp Require Import gmap list bitvector.definitions.
Require Import PageGeom.        (* [PGSIZE] *)
Require Import ElfFile.         (* [elf_phdr], [elf_loads], [elf_parse_ehdr] *)
Require Import SpecKexec.       (* [kexec_loadable], [loads_ascending] *)
Require Import ElfUser.         (* [sh_elf] / [init_elf] and their [elf_wf] *)
Require Import FsAbsDefs.       (* [anode] / [MkAnode] / [AFile] (FsAbs's own rule: LAST) *)

Local Open Scope Z_scope.

(*  [ElfUser.v]'s own reduction tactic, and its header is where the
    reasoning lives: the cast is handed to the kernel directly, built at
    the CHEAP side, so the goal's heavy side is evaluated once.  *)
Local Ltac vm_eq :=
  lazymatch goal with
  | |- _ = ?r => vm_cast_no_check (@eq_refl _ r)
  end.

(* ===================================================================== *)
(*  1.  THE COMPUTABLE TWIN OF EACH NON-DECIDABLE CONJUNCT                *)
(* ===================================================================== *)

Fixpoint loads_ascending_b (ps : list elf_phdr) : bool :=
  match ps with
  | [] => true
  | p :: ps' =>
      (match ps' with
       | [] => true
       | q :: _ => Z.leb (ep_vaddr p + ep_memsz p) (ep_vaddr q)
       end) && loads_ascending_b ps'
  end.

Lemma loads_ascending_of_b (ps : list elf_phdr) :
  loads_ascending_b ps = true -> loads_ascending ps.
Proof.
  induction ps as [| p ps IH]; cbn [loads_ascending_b loads_ascending];
    [ intros _; exact I | ].
  intro H. apply andb_prop in H as [H1 H2]. split; [ | exact (IH H2) ].
  destruct ps as [| q ps']; [ exact I | apply Z.leb_le; exact H1 ].
Qed.

Definition phdr_loadable_b (p : elf_phdr) : bool :=
  Z.ltb (ep_offset p) (2 ^ 31) && Z.eqb (ep_vaddr p `mod` PGSIZE) 0.

Lemma phdrs_loadable_of_b (ps : list elf_phdr) :
  forallb phdr_loadable_b ps = true ->
  Forall (fun p => ep_offset p < 2 ^ 31 /\ ep_vaddr p `mod` PGSIZE = 0) ps.
Proof.
  induction ps as [| p ps IH]; cbn [forallb]; [ intros _; constructor | ].
  intro H. apply andb_prop in H as [H1 H2]. constructor; [ | exact (IH H2) ].
  unfold phdr_loadable_b in H1. apply andb_prop in H1 as [Ha Hb].
  split; [ apply Z.ltb_lt; exact Ha | apply Z.eqb_eq; exact Hb ].
Qed.

Definition ehdr_phoff_b (f : elf_bytes) : bool :=
  match elf_parse_ehdr f with
  | Some e => Z.ltb (ee_phoff e) (2 ^ 31)
  | None => false
  end.

Lemma ehdr_phoff_of_b (f : elf_bytes) :
  ehdr_phoff_b f = true ->
  exists e, elf_parse_ehdr f = Some e /\ ee_phoff e < 2 ^ 31.
Proof.
  unfold ehdr_phoff_b.
  destruct (elf_parse_ehdr f) as [e |] eqn:He; [ | discriminate ].
  intro H. exists e. split; [ reflexivity | apply Z.ltb_lt; exact H ].
Qed.

(* ...and the whole predicate, for a caller that has no [elf_wf] to hand *)
Definition kexec_loadable_b (f : elf_bytes) : bool :=
  elf_wf f && ehdr_phoff_b f
  && forallb phdr_loadable_b (elf_loads f)
  && loads_ascending_b (elf_loads f).

Lemma kexec_loadable_of_b (f : elf_bytes) :
  kexec_loadable_b f = true -> kexec_loadable f.
Proof.
  unfold kexec_loadable_b, kexec_loadable. intro H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2].
  split; [ exact H1 | ].
  split; [ exact (ehdr_phoff_of_b f H2) | ].
  split; [ exact (phdrs_loadable_of_b _ H3) | exact (loads_ascending_of_b _ H4) ].
Qed.

(* ===================================================================== *)
(*  2.  THE TWO INSTANCES                                                 *)
(*                                                                        *)
(*  [elf_wf] is CITED from [ElfUser.v] rather than recomputed -- it is    *)
(*  the one conjunct that walks the whole file.  The three below read the *)
(*  64-byte header and the four-entry program-header table.               *)
(* ===================================================================== *)

Lemma sh_elf_loadable : kexec_loadable ElfUser.sh_elf.
Proof.
  unfold kexec_loadable.
  split; [ exact ElfUser.sh_elf_wf | ].
  split; [ apply ehdr_phoff_of_b; vm_eq | ].
  split; [ apply phdrs_loadable_of_b; vm_eq
         | apply loads_ascending_of_b; vm_eq ].
Qed.

Lemma init_elf_loadable : kexec_loadable ElfUser.init_elf.
Proof.
  unfold kexec_loadable.
  split; [ exact ElfUser.init_elf_wf | ].
  split; [ apply ehdr_phoff_of_b; vm_eq | ].
  split; [ apply phdrs_loadable_of_b; vm_eq
         | apply loads_ascending_of_b; vm_eq ].
Qed.

(* ...and the two nodes the era-0 pins name ARE loadable files, which is
   what refutes the exec deposit's arm (b) at a pinned exec. *)
Lemma sh_anode_loadable (nl : nat) :
  anode_loadable (MkAnode (AFile ElfUser.sh_elf) nl).
Proof. exists ElfUser.sh_elf, nl. split; [ reflexivity | exact sh_elf_loadable ]. Qed.

Lemma init_anode_loadable (nl : nat) :
  anode_loadable (MkAnode (AFile ElfUser.init_elf) nl).
Proof. exists ElfUser.init_elf, nl. split; [ reflexivity | exact init_elf_loadable ]. Qed.
