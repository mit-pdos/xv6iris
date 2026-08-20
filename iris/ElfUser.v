(* ElfUser.v -- THE SANITY CHECK, U-MODE SIDE: each generated user-program
   dump IS that program's ELF, read through the general ELF64 semantics.

   Sibling of [ElfKernel.v], which does exactly this for the kernel; read
   that file's header first -- the motivation (the dumper's reasoning is
   what the proofs call "the program", so a dumper bug is invisible to
   them), the method ([pstring_hex_bytes] over the raw blob, the general
   semantics of [ElfFile.v] on top, [vm_compute]d decidable checks bridged
   with [bool_decide_eq_true_1]), the [Typeclasses Opaque] discipline, and
   the leaf-by-design rule (NOTHING IMPORTS THIS FILE, and nothing should)
   are all identical here and are not repeated.  This file is the same
   theorem set four more times, for the four verified user programs:
   [sync], [echo], [sh], [init].

   WHAT IS NEW HERE, AND WHY IT IS WORTH FOUR MORE INSTANCES.  These are
   not just four more binaries: their SHAPES exercise parts of the general
   semantics that the kernel's single RWX PT_LOAD never reaches.

     - TWO PT_LOADs per program, not one.  A text segment R-E at vaddr 0
       and a writable segment above it holding .data + .bss.  So
       [elf_file_image] / [elf_zero_image] / [elf_image] are genuine
       [segs_union] FOLDS over two segments here, and the disjointness
       side conditions of [elf_image_split] are doing real work rather
       than degenerating to a one-element list.

     - The text segment has [filesz = memsz], so ITS zero map is EMPTY.
       The whole .bss comes from the second segment; the [∅ ∪ _] leg of
       the fold is on the critical path of every zero-image theorem.

     - [sync] and [echo] have a PURE-BSS writable segment: [filesz = 0].
       It contributes NO file bytes at all -- [seg_file_bytes] is an empty
       [take] -- so their entire file-backed image comes from the text
       segment, while their .bss comes from a segment with no file window.

     - The ENTRY IS NOT THE LOWEST TEXT ADDRESS ([syncEntry] = 0x12,
       [echoEntry] = 0x7c, [shEntry] = 0x9d0, [initEntry] = 0xbc): xv6
       links `start` ahead of `main`, and [elf_entry] must report the
       header's [e_entry], not [elf_mem_base].

     - FOUR program headers, only two of them PT_LOAD: a
       PT_RISCV_ATTRIBUTES and a PT_GNU_STACK sit in the table and MUST be
       filtered out by [elf_loads] / [elf_segments].  The kernel's table
       has nothing to filter, so this is the first check that the filter
       is right.

   As in [ElfKernel.v], the raws are the DEBUG-STRIPPED images
   ([objcopy --strip-debug]): DWARF embeds the absolute build directory,
   so only the stripped file is byte-identical across clones, and it keeps
   everything that matters here (program headers, every allocated section,
   all loadable bytes, the symtab).

   These files are small -- 11-16 kB against the kernel's 55 kB -- so the
   whole file is seconds, not the kernel file's minute.

   If a [vm_compute] here ever fails, DO NOT weaken the statement.  A
   mismatch between a dump and its binary is precisely the event this file
   exists to catch: find the disagreeing address (compute both sides'
   lookup) and fix the dumper.  *)

From Stdlib Require Import ZArith List.
From Stdlib.Strings Require Import PString.
From stdpp Require Import gmap.
From stdpp.bitvector Require Import definitions.
From xv6iris Require Import ElfFile PStringBytes.
From User Require Import
  SyncElfRaw SyncInstrs SyncData
  EchoElfRaw EchoInstrs EchoData
  ShElfRaw   ShInstrs   ShData
  InitElfRaw InitInstrs InitData.

Local Open Scope Z_scope.

(* ====================================================================== *)
(* ====================================================================== *)
(*  sync                                                                  *)
(*                                                                        *)
(*  entry 0x12; loads (0x0, 0xd44, 0xd44, R-X) and                        *)
(*  (0x1000, 0x0, 0x20, RW-) -- the pure-bss writable segment.            *)
(* ====================================================================== *)
(* ====================================================================== *)

(* [Typeclasses Opaque] for the same reason the generated maps carry it:
   resolution must never force a 10960-element list. *)
Definition sync_elf : elf_bytes := pstring_hex_bytes SyncElfRaw.sync_elf_hex.
Global Typeclasses Opaque sync_elf.

(* The length, over [Z].  NEVER state a [nat]-vs-large-literal equality
   (see claude-notes/durable-notes.md): [10960 : nat] is a 10960-deep
   successor chain.  This one goes through [pstring_hex_bytes_length], so
   only the STRING's length is computed. *)
Lemma sync_elf_length : Z.of_nat (length sync_elf) = SyncElfRaw.sync_elf_size.
Proof.
  unfold sync_elf. rewrite pstring_hex_bytes_length. vm_compute. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(*  Well-formedness                                                        *)
(* ---------------------------------------------------------------------- *)

Lemma sync_elf_wf : elf_wf sync_elf = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sync_elf_sections_wf : elf_sections_wf sync_elf = true.
Proof. vm_compute. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(*  Geometry: the ELF's own numbers are the dump's constants               *)
(* ---------------------------------------------------------------------- *)

(* 0x12, NOT [syncMemBase] = 0x0: `start` is linked ahead of `main`. *)
Lemma sync_elf_entry : elf_entry sync_elf = Some SyncData.syncEntry.
Proof. vm_compute. reflexivity. Qed.

(* Two entries, in program-header order -- and the PT_RISCV_ATTRIBUTES and
   PT_GNU_STACK headers that sit alongside them are filtered out. *)
Lemma sync_elf_segments :
  elf_segments sync_elf = Some SyncData.sync_segments.
Proof. vm_compute. reflexivity. Qed.

Lemma sync_elf_base : elf_mem_base sync_elf = Some SyncData.syncMemBase.
Proof. vm_compute. reflexivity. Qed.

Lemma sync_elf_end : elf_mem_end sync_elf = Some SyncData.syncMemEnd.
Proof. vm_compute. reflexivity. Qed.

(* The read-only / writable split lives in the SECTION table, so this is
   the one geometry constant that depends on [elf_sections_wf] rather than
   [elf_wf].  (Here the PT_LOAD flags do distinguish R-X from RW-, but the
   semantics reads the sections, exactly as the dumper does.) *)
Lemma sync_elf_rodata_end :
  elf_rodata_end sync_elf = Some SyncData.syncRodataEnd.
Proof. vm_compute. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(*  THE image theorem: the dump is exactly the ELF's file-backed image     *)
(* ---------------------------------------------------------------------- *)

(* [bool_decide] on a [gmap Z (bv 8)] equality: the decision procedure
   computes, so the proof term stays [eq_refl] and no 3396-element list
   ever enters it.  The writable segment contributes nothing to this side
   ([filesz = 0]); every file-backed byte comes from the text segment. *)
Lemma sync_elf_file_image_bool :
  bool_decide (elf_file_image sync_elf
               = SyncInstrs.sync_bytes ∪ SyncData.sync_data) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sync_elf_file_image :
  elf_file_image sync_elf = SyncInstrs.sync_bytes ∪ SyncData.sync_data.
Proof.
  pose proof sync_elf_file_image_bool as H.
  apply bool_decide_eq_true_1 in H. exact H.
Qed.

(* ---------------------------------------------------------------------- *)
(*  The zero part (.bss), and the full loaded image                        *)
(* ---------------------------------------------------------------------- *)

(* Text is (vaddr 0x0, filesz 0xd44, memsz 0xd44): filesz = memsz, so its
   zero window is EMPTY.  The whole .bss is the writable segment's
   (vaddr 0x1000, filesz 0x0, memsz 0x20), i.e. [0x1000, 0x1020).  Both
   literals are [Z]: [replicate] wants a [nat], but a [nat] LITERAL of 32
   would be a successor chain (and 103208 in the kernel's case certainly
   is), so it is uniformly written [Z.to_nat sync_bss_size]. *)
Definition sync_bss_lo : Z := 0x1000.
Definition sync_bss_size : Z := 32.   (* 0x20 = memsz - filesz *)

Lemma sync_elf_zero_image_bool :
  bool_decide (elf_zero_image sync_elf
               = map_seqZ sync_bss_lo
                   (replicate (Z.to_nat sync_bss_size) elf_zero_byte)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sync_elf_zero_image :
  elf_zero_image sync_elf
  = map_seqZ sync_bss_lo (replicate (Z.to_nat sync_bss_size) elf_zero_byte).
Proof.
  pose proof sync_elf_zero_image_bool as H.
  apply bool_decide_eq_true_1 in H. exact H.
Qed.

(* The tie that makes the two halves meet: the zero window ends exactly at
   the dump's [syncMemEnd].  (Unlike the kernel's [kernel_bss_bot], there
   is no matching tie to [syncMemBase]: the .bss belongs to the SECOND
   load segment, so its bottom is that segment's [vaddr + filesz], not the
   image base -- [sync_elf_segments] is what pins it.) *)
Lemma sync_bss_top : sync_bss_lo + sync_bss_size = SyncData.syncMemEnd.
Proof. vm_compute. reflexivity. Qed.

(* The FULL loaded image.  Not a third giant [vm_compute]: [elf_image_split]
   is the general fact that a well-formed file's image is the disjoint
   union of its file-backed and zero parts, so this follows from
   [sync_elf_wf] and [sync_elf_file_image]. *)
Lemma sync_elf_image :
  elf_image sync_elf
  = (SyncInstrs.sync_bytes ∪ SyncData.sync_data) ∪ elf_zero_image sync_elf.
Proof.
  destruct (elf_image_split sync_elf sync_elf_wf) as [Hsplit _].
  rewrite Hsplit, sync_elf_file_image. reflexivity.
Qed.

(* ... and, spelled out, with the .bss written as the concrete window. *)
Lemma sync_elf_image_concrete :
  elf_image sync_elf
  = (SyncInstrs.sync_bytes ∪ SyncData.sync_data)
    ∪ map_seqZ sync_bss_lo (replicate (Z.to_nat sync_bss_size) elf_zero_byte).
Proof. rewrite sync_elf_image, sync_elf_zero_image. reflexivity. Qed.

(* ====================================================================== *)
(* ====================================================================== *)
(*  echo                                                                  *)
(*                                                                        *)
(*  Same shape as [sync]: entry 0x7c; loads (0x0, 0xdcc, 0xdcc, R-X) and  *)
(*  (0x1000, 0x0, 0x20, RW-) -- again a pure-bss writable segment.        *)
(* ====================================================================== *)
(* ====================================================================== *)

Definition echo_elf : elf_bytes := pstring_hex_bytes EchoElfRaw.echo_elf_hex.
Global Typeclasses Opaque echo_elf.

Lemma echo_elf_length : Z.of_nat (length echo_elf) = EchoElfRaw.echo_elf_size.
Proof.
  unfold echo_elf. rewrite pstring_hex_bytes_length. vm_compute. reflexivity.
Qed.

Lemma echo_elf_wf : elf_wf echo_elf = true.
Proof. vm_compute. reflexivity. Qed.

Lemma echo_elf_sections_wf : elf_sections_wf echo_elf = true.
Proof. vm_compute. reflexivity. Qed.

Lemma echo_elf_entry : elf_entry echo_elf = Some EchoData.echoEntry.
Proof. vm_compute. reflexivity. Qed.

Lemma echo_elf_segments :
  elf_segments echo_elf = Some EchoData.echo_segments.
Proof. vm_compute. reflexivity. Qed.

Lemma echo_elf_base : elf_mem_base echo_elf = Some EchoData.echoMemBase.
Proof. vm_compute. reflexivity. Qed.

Lemma echo_elf_end : elf_mem_end echo_elf = Some EchoData.echoMemEnd.
Proof. vm_compute. reflexivity. Qed.

Lemma echo_elf_rodata_end :
  elf_rodata_end echo_elf = Some EchoData.echoRodataEnd.
Proof. vm_compute. reflexivity. Qed.

Lemma echo_elf_file_image_bool :
  bool_decide (elf_file_image echo_elf
               = EchoInstrs.echo_bytes ∪ EchoData.echo_data) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma echo_elf_file_image :
  elf_file_image echo_elf = EchoInstrs.echo_bytes ∪ EchoData.echo_data.
Proof.
  pose proof echo_elf_file_image_bool as H.
  apply bool_decide_eq_true_1 in H. exact H.
Qed.

(* Writable segment (vaddr 0x1000, filesz 0x0, memsz 0x20): .bss is
   [0x1000, 0x1020), and the text segment's zero window is empty. *)
Definition echo_bss_lo : Z := 0x1000.
Definition echo_bss_size : Z := 32.   (* 0x20 = memsz - filesz *)

Lemma echo_elf_zero_image_bool :
  bool_decide (elf_zero_image echo_elf
               = map_seqZ echo_bss_lo
                   (replicate (Z.to_nat echo_bss_size) elf_zero_byte)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma echo_elf_zero_image :
  elf_zero_image echo_elf
  = map_seqZ echo_bss_lo (replicate (Z.to_nat echo_bss_size) elf_zero_byte).
Proof.
  pose proof echo_elf_zero_image_bool as H.
  apply bool_decide_eq_true_1 in H. exact H.
Qed.

Lemma echo_bss_top : echo_bss_lo + echo_bss_size = EchoData.echoMemEnd.
Proof. vm_compute. reflexivity. Qed.

Lemma echo_elf_image :
  elf_image echo_elf
  = (EchoInstrs.echo_bytes ∪ EchoData.echo_data) ∪ elf_zero_image echo_elf.
Proof.
  destruct (elf_image_split echo_elf echo_elf_wf) as [Hsplit _].
  rewrite Hsplit, echo_elf_file_image. reflexivity.
Qed.

Lemma echo_elf_image_concrete :
  elf_image echo_elf
  = (EchoInstrs.echo_bytes ∪ EchoData.echo_data)
    ∪ map_seqZ echo_bss_lo (replicate (Z.to_nat echo_bss_size) elf_zero_byte).
Proof. rewrite echo_elf_image, echo_elf_zero_image. reflexivity. Qed.

(* ====================================================================== *)
(* ====================================================================== *)
(*  sh                                                                    *)
(*                                                                        *)
(*  The interesting one: entry 0x9d0; loads (0x0, 0x1c54, 0x1c54, R-X)    *)
(*  and (0x2000, 0x10, 0x98, RW-).  The writable segment has a NONEMPTY   *)
(*  file window (0x10 bytes of .data) AND a .bss tail, so BOTH legs of    *)
(*  [seg_map] are nonempty for it and both segments contribute to         *)
(*  [elf_file_image].                                                     *)
(* ====================================================================== *)
(* ====================================================================== *)

Definition sh_elf : elf_bytes := pstring_hex_bytes ShElfRaw.sh_elf_hex.
Global Typeclasses Opaque sh_elf.

Lemma sh_elf_length : Z.of_nat (length sh_elf) = ShElfRaw.sh_elf_size.
Proof.
  unfold sh_elf. rewrite pstring_hex_bytes_length. vm_compute. reflexivity.
Qed.

Lemma sh_elf_wf : elf_wf sh_elf = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sh_elf_sections_wf : elf_sections_wf sh_elf = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sh_elf_entry : elf_entry sh_elf = Some ShData.shEntry.
Proof. vm_compute. reflexivity. Qed.

Lemma sh_elf_segments :
  elf_segments sh_elf = Some ShData.sh_segments.
Proof. vm_compute. reflexivity. Qed.

Lemma sh_elf_base : elf_mem_base sh_elf = Some ShData.shMemBase.
Proof. vm_compute. reflexivity. Qed.

Lemma sh_elf_end : elf_mem_end sh_elf = Some ShData.shMemEnd.
Proof. vm_compute. reflexivity. Qed.

Lemma sh_elf_rodata_end :
  elf_rodata_end sh_elf = Some ShData.shRodataEnd.
Proof. vm_compute. reflexivity. Qed.

(* Here the fold really is over two nonempty file windows: [0x0, 0x1c54)
   from the text segment and [0x2000, 0x2010) from the writable one.  The
   dump's split puts the latter entirely in [sh_data] (whose top is
   0x2010), so this equality checks the [∪] across segments too. *)
Lemma sh_elf_file_image_bool :
  bool_decide (elf_file_image sh_elf
               = ShInstrs.sh_bytes ∪ ShData.sh_data) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sh_elf_file_image :
  elf_file_image sh_elf = ShInstrs.sh_bytes ∪ ShData.sh_data.
Proof.
  pose proof sh_elf_file_image_bool as H.
  apply bool_decide_eq_true_1 in H. exact H.
Qed.

(* Writable segment (vaddr 0x2000, filesz 0x10, memsz 0x98): the .bss
   starts ABOVE the file window, at 0x2000 + 0x10 = 0x2010, and runs to
   0x2098.  The text segment's zero window is empty (filesz = memsz). *)
Definition sh_bss_lo : Z := 0x2010.
Definition sh_bss_size : Z := 136.   (* 0x88 = 0x98 - 0x10 *)

Lemma sh_elf_zero_image_bool :
  bool_decide (elf_zero_image sh_elf
               = map_seqZ sh_bss_lo
                   (replicate (Z.to_nat sh_bss_size) elf_zero_byte)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sh_elf_zero_image :
  elf_zero_image sh_elf
  = map_seqZ sh_bss_lo (replicate (Z.to_nat sh_bss_size) elf_zero_byte).
Proof.
  pose proof sh_elf_zero_image_bool as H.
  apply bool_decide_eq_true_1 in H. exact H.
Qed.

Lemma sh_bss_top : sh_bss_lo + sh_bss_size = ShData.shMemEnd.
Proof. vm_compute. reflexivity. Qed.

Lemma sh_elf_image :
  elf_image sh_elf
  = (ShInstrs.sh_bytes ∪ ShData.sh_data) ∪ elf_zero_image sh_elf.
Proof.
  destruct (elf_image_split sh_elf sh_elf_wf) as [Hsplit _].
  rewrite Hsplit, sh_elf_file_image. reflexivity.
Qed.

Lemma sh_elf_image_concrete :
  elf_image sh_elf
  = (ShInstrs.sh_bytes ∪ ShData.sh_data)
    ∪ map_seqZ sh_bss_lo (replicate (Z.to_nat sh_bss_size) elf_zero_byte).
Proof. rewrite sh_elf_image, sh_elf_zero_image. reflexivity. Qed.

(* ====================================================================== *)
(* ====================================================================== *)
(*  init                                                                  *)
(*                                                                        *)
(*  entry 0xbc; loads (0x0, 0xe6c, 0xe6c, R-X) and                        *)
(*  (0x1000, 0x10, 0x30, RW-) -- like [sh], .data then .bss above it.     *)
(* ====================================================================== *)
(* ====================================================================== *)

Definition init_elf : elf_bytes := pstring_hex_bytes InitElfRaw.init_elf_hex.
Global Typeclasses Opaque init_elf.

Lemma init_elf_length : Z.of_nat (length init_elf) = InitElfRaw.init_elf_size.
Proof.
  unfold init_elf. rewrite pstring_hex_bytes_length. vm_compute. reflexivity.
Qed.

Lemma init_elf_wf : elf_wf init_elf = true.
Proof. vm_compute. reflexivity. Qed.

Lemma init_elf_sections_wf : elf_sections_wf init_elf = true.
Proof. vm_compute. reflexivity. Qed.

Lemma init_elf_entry : elf_entry init_elf = Some InitData.initEntry.
Proof. vm_compute. reflexivity. Qed.

Lemma init_elf_segments :
  elf_segments init_elf = Some InitData.init_segments.
Proof. vm_compute. reflexivity. Qed.

Lemma init_elf_base : elf_mem_base init_elf = Some InitData.initMemBase.
Proof. vm_compute. reflexivity. Qed.

Lemma init_elf_end : elf_mem_end init_elf = Some InitData.initMemEnd.
Proof. vm_compute. reflexivity. Qed.

Lemma init_elf_rodata_end :
  elf_rodata_end init_elf = Some InitData.initRodataEnd.
Proof. vm_compute. reflexivity. Qed.

Lemma init_elf_file_image_bool :
  bool_decide (elf_file_image init_elf
               = InitInstrs.init_bytes ∪ InitData.init_data) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma init_elf_file_image :
  elf_file_image init_elf = InitInstrs.init_bytes ∪ InitData.init_data.
Proof.
  pose proof init_elf_file_image_bool as H.
  apply bool_decide_eq_true_1 in H. exact H.
Qed.

(* Writable segment (vaddr 0x1000, filesz 0x10, memsz 0x30): .bss is
   [0x1010, 0x1030); the text segment's zero window is empty. *)
Definition init_bss_lo : Z := 0x1010.
Definition init_bss_size : Z := 32.   (* 0x20 = 0x30 - 0x10 *)

Lemma init_elf_zero_image_bool :
  bool_decide (elf_zero_image init_elf
               = map_seqZ init_bss_lo
                   (replicate (Z.to_nat init_bss_size) elf_zero_byte)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma init_elf_zero_image :
  elf_zero_image init_elf
  = map_seqZ init_bss_lo (replicate (Z.to_nat init_bss_size) elf_zero_byte).
Proof.
  pose proof init_elf_zero_image_bool as H.
  apply bool_decide_eq_true_1 in H. exact H.
Qed.

Lemma init_bss_top : init_bss_lo + init_bss_size = InitData.initMemEnd.
Proof. vm_compute. reflexivity. Qed.

Lemma init_elf_image :
  elf_image init_elf
  = (InitInstrs.init_bytes ∪ InitData.init_data) ∪ elf_zero_image init_elf.
Proof.
  destruct (elf_image_split init_elf init_elf_wf) as [Hsplit _].
  rewrite Hsplit, init_elf_file_image. reflexivity.
Qed.

Lemma init_elf_image_concrete :
  elf_image init_elf
  = (InitInstrs.init_bytes ∪ InitData.init_data)
    ∪ map_seqZ init_bss_lo (replicate (Z.to_nat init_bss_size) elf_zero_byte).
Proof. rewrite init_elf_image, init_elf_zero_image. reflexivity. Qed.
