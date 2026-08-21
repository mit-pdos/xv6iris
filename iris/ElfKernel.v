(* ElfKernel.v -- THE SANITY CHECK: the generated kernel dump IS the
   kernel ELF, read through the general ELF64 semantics.

   Everywhere else in the tree the kernel image is the GENERATED dump --
   [KernelInstrs.kernel_bytes], [KernelData.kernel_data], and the geometry
   constants [kernelEntry] / [kernel_segments] / [kernelMemBase] /
   [kernelMemEnd] / [kernelRodataEnd].  Those come out of
   [tools/dump_elf.py], which does its OWN section/instruction reasoning
   about the linked binary; a bug in the dumper is a bug the proofs cannot
   see, because the dumper's output is what the proofs call "the kernel".

   This file closes that hole, once, by a different route.  It takes the
   kernel ELF as a RAW BYTE BLOB ([KernelElfRaw.kernel_elf_hex], decoded by
   [PStringBytes.pstring_hex_bytes]), runs the general, kernel-agnostic
   ELF64 semantics of [ElfFile.v] over it, and proves by [vm_compute] that
   what falls out is EXACTLY the dump -- byte for byte, in the image
   theorems [kernel_elf_file_image] / [kernel_elf_image], and literal for
   literal in the geometry ones.  The dumper's reasoning and the ELF spec's
   reasoning are independent; agreeing on 41648 file-backed bytes and a
   103208-byte .bss is not something two independent bugs do.

   THE RAW IS THE LITERAL FILE: [kernel/kernel], the binary qemu runs, byte
   for byte, DWARF included.  That is only committable as ground truth
   because the xv6 build passes [-ffile-prefix-map=$(CURDIR)=.]: DWARF
   would otherwise embed the absolute build directory, making the file
   differ between build trees; with the flag it is byte-identical
   (verified from two build directories).  The dumper refuses a file that
   embeds its own build directory, so a flagless build fails loudly
   instead of producing a tree-dependent dump.

   ONE [vm_compute]-HEAVY FILE, BY DESIGN, AND OUT OF EVERY CONE.  Each
   theorem below re-decodes 285200 bytes and rebuilds the maps; that is a
   few seconds apiece and the whole file is well under the minute.  The
   price is paid HERE and nowhere else: NOTHING IN THE TREE IMPORTS THIS
   FILE, and nothing should.  It is a leaf, checked by CI, whose value is
   that it fails loudly if the dump and the binary ever drift apart.  If
   you find yourself wanting to [Require] it from a proof, you want a
   lemma about the dump instead.

   If a [vm_compute] here ever fails, DO NOT weaken the statement.  A
   mismatch between the dump and the ELF is precisely the event this file
   exists to catch: find the disagreeing address (compute both sides'
   lookup) and fix the dumper.  *)

From Stdlib Require Import ZArith List.
From Stdlib.Strings Require Import PString.
From stdpp Require Import gmap.
From stdpp.bitvector Require Import definitions.
From xv6iris Require Import ElfFile PStringBytes.
From Kernel Require Import KernelElfRaw KernelInstrs KernelData.

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  The kernel, as a file                                                 *)
(* ====================================================================== *)

(* [Typeclasses Opaque] for the same reason the generated maps carry it:
   resolution must never force a 285200-element list. *)
Definition kernel_elf : elf_bytes := pstring_hex_bytes kernel_elf_hex.
Global Typeclasses Opaque kernel_elf.

(*  ONE REDUCTION, NOT TWO.  [vm_compute. reflexivity.] reduces the goal in
    the tactic engine and then the KERNEL re-runs the same reduction at
    [Qed] to check the [vm_cast] the tactic left behind, so every sentence
    below costs its [vm_compute] twice ([elf_sections_wf] measured 11.6 s +
    11.1 s; claude-notes/optimization.md, "[Qed] re-checks and therefore
    DOUBLES every [vm_compute]").  [vm_eq] hands the kernel that cast
    directly and typechecks nothing at tactic time: same proof term, same
    VM, and this file goes 54.0 s -> 28.7 s.

    IT MUST BE THE **RIGHT** SIDE: [eq_refl rhs] casts [rhs = rhs] to
    [lhs = rhs] and the kernel reduces the heavy side once, where the
    mirror spelling [eq_refl lhs] makes the VM evaluate it TWICE -- 78.3 s
    on this file, WORSE than the [vm_compute] it replaces.

    THE COST: a disagreement now surfaces at [Qed] as a kernel conversion
    failure with no goal in view.  Put [vm_compute. reflexivity.] back on
    the ONE failing lemma to see it -- and then fix the dump, never the
    statement (see the note at the top of this file). *)
Local Ltac vm_eq :=
  lazymatch goal with
  | |- _ = ?r => vm_cast_no_check (@eq_refl _ r)
  end.

(* The length, over [Z].  NEVER state a [nat]-vs-large-literal equality
   (see claude-notes/durable-notes.md): [285200 : nat] is a 285200-deep
   successor chain.  This one goes through [pstring_hex_bytes_length], so
   only the STRING's length is computed. *)
Lemma kernel_elf_length : Z.of_nat (length kernel_elf) = kernel_elf_size.
Proof.
  unfold kernel_elf. rewrite pstring_hex_bytes_length. vm_compute. reflexivity.
Qed.

(* ====================================================================== *)
(*  Well-formedness                                                       *)
(* ====================================================================== *)

Lemma kernel_elf_wf : elf_wf kernel_elf = true.
Proof. vm_eq. Qed.

Lemma kernel_elf_sections_wf : elf_sections_wf kernel_elf = true.
Proof. vm_eq. Qed.

(* ====================================================================== *)
(*  Geometry: the ELF's own numbers are the dump's constants              *)
(* ====================================================================== *)

Lemma kernel_elf_entry : elf_entry kernel_elf = Some KernelData.kernelEntry.
Proof. vm_eq. Qed.

Lemma kernel_elf_segments :
  elf_segments kernel_elf = Some KernelData.kernel_segments.
Proof. vm_eq. Qed.

Lemma kernel_elf_base : elf_mem_base kernel_elf = Some KernelData.kernelMemBase.
Proof. vm_eq. Qed.

Lemma kernel_elf_end : elf_mem_end kernel_elf = Some KernelData.kernelMemEnd.
Proof. vm_eq. Qed.

(* The read-only / writable split lives in the SECTION table -- the single
   RWX PT_LOAD cannot express it -- so this is the one geometry constant
   that depends on [elf_sections_wf] rather than [elf_wf]. *)
Lemma kernel_elf_rodata_end :
  elf_rodata_end kernel_elf = Some KernelData.kernelRodataEnd.
Proof. vm_eq. Qed.

(* ====================================================================== *)
(*  THE image theorem: the dump is exactly the ELF's file-backed image    *)
(* ====================================================================== *)

(* [bool_decide] on a [gmap Z (bv 8)] equality: the decision procedure
   computes, so the proof term stays [eq_refl] and no 41648-element list
   ever enters it. *)
Lemma kernel_elf_file_image_bool :
  bool_decide (elf_file_image kernel_elf
               = KernelInstrs.kernel_bytes ∪ KernelData.kernel_data) = true.
Proof. vm_eq. Qed.

Lemma kernel_elf_file_image :
  elf_file_image kernel_elf = KernelInstrs.kernel_bytes ∪ KernelData.kernel_data.
Proof.
  pose proof kernel_elf_file_image_bool as H.
  apply bool_decide_eq_true_1 in H. exact H.
Qed.

(* ====================================================================== *)
(*  The zero part (.bss), and the full loaded image                       *)
(* ====================================================================== *)

(* The single PT_LOAD is (vaddr 0x80000000, filesz 0xa2a0, memsz 0x235c8),
   so the zero window is [vaddr+filesz, vaddr+memsz) = [0x8000a2a0,
   0x800235c8), i.e. 0x235c8 - 0xa2a0 = 103208 bytes.  Both literals are
   [Z]: [replicate] wants a [nat], but a [nat] LITERAL of 103208 is the
   successor-chain trap, so it is written [Z.to_nat kernel_bss_size]. *)
Definition kernel_bss_lo : Z := 0x8000a2a0.
Definition kernel_bss_size : Z := 103208.

Lemma kernel_elf_zero_image_bool :
  bool_decide (elf_zero_image kernel_elf
               = map_seqZ kernel_bss_lo
                   (replicate (Z.to_nat kernel_bss_size) elf_zero_byte)) = true.
Proof. vm_eq. Qed.

Lemma kernel_elf_zero_image :
  elf_zero_image kernel_elf
  = map_seqZ kernel_bss_lo (replicate (Z.to_nat kernel_bss_size) elf_zero_byte).
Proof.
  pose proof kernel_elf_zero_image_bool as H.
  apply bool_decide_eq_true_1 in H. exact H.
Qed.

(* The tie that makes the two halves meet: the zero window ends exactly at
   the dump's [kernelMemEnd], and starts exactly at [kernelMemBase] plus
   the segment's [filesz]. *)
Lemma kernel_bss_top : kernel_bss_lo + kernel_bss_size = KernelData.kernelMemEnd.
Proof. vm_compute. reflexivity. Qed.

Lemma kernel_bss_bot : KernelData.kernelMemBase + 0xa2a0 = kernel_bss_lo.
Proof. vm_compute. reflexivity. Qed.

(* The FULL loaded image.  Not a third giant [vm_compute]: [elf_image_split]
   is the general fact that a well-formed file's image is the disjoint
   union of its file-backed and zero parts, so this follows from
   [kernel_elf_wf] and [kernel_elf_file_image]. *)
Lemma kernel_elf_image :
  elf_image kernel_elf
  = (KernelInstrs.kernel_bytes ∪ KernelData.kernel_data) ∪ elf_zero_image kernel_elf.
Proof.
  destruct (elf_image_split kernel_elf kernel_elf_wf) as [Hsplit _].
  rewrite Hsplit, kernel_elf_file_image. reflexivity.
Qed.

(* ... and, spelled out, with the .bss written as the concrete window. *)
Lemma kernel_elf_image_concrete :
  elf_image kernel_elf
  = (KernelInstrs.kernel_bytes ∪ KernelData.kernel_data)
    ∪ map_seqZ kernel_bss_lo (replicate (Z.to_nat kernel_bss_size) elf_zero_byte).
Proof. rewrite kernel_elf_image, kernel_elf_zero_image. reflexivity. Qed.

