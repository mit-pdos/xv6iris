(* ElfFile.v -- ELF64 FILE semantics over a byte list: what an ELF file
   MEANS, i.e. the memory image a loader must establish from it.

   THE FILE-SIDE GROUND TRUTH, AND THE OTHER HALF OF [ElfEnc.v].
   [ElfEnc.v] is the CODE-side reader vocabulary: the two stack buffers
   kexec [readi]s an executable into, and the little-endian field
   projections kexec actually performs on them -- including the deliberate
   [int] truncations the C code forces ([eh_phoff] and [ph_off] are FOUR-byte
   signed loads at offsets 32 and 8, because the C assigns a [uint64] field
   to an [int]).  This file is the other half: the file's OWN contents, as
   the sequence of bytes exec() reads out of the FS, with the HONEST
   full-width fields the ELF64 spec defines.

   The two agree on layout and disagree only in width, by design:

       ehdr:  entry @ 0x18   ElfEnc [eh_entry]  le_at f 24 8   -- same
              phoff @ 0x20   ElfEnc [eh_phoff]  le_at f 32 4   -- TRUNCATED
              phnum @ 0x38   ElfEnc [eh_phnum]  le_at f 56 2   -- same
              magic @ 0      ElfEnc [eh_magic]  le_at f 0  4   -- same
       phdr:  type   @ 0     ElfEnc [ph_type]                  -- same
              flags  @ 4     ElfEnc [ph_flags]                 -- same
              offset @ 8     ElfEnc [ph_off]    le_at f 8 4    -- TRUNCATED
              vaddr  @ 16, filesz @ 32, memsz @ 40             -- same

   so [ee_phoff] here and [eh_phoff] there are EQUAL exactly when the file's
   [e_phoff] is below 2^31, and likewise for [ep_offset]/[ph_off].  Those
   bounds are NOT part of [elf_wf] below: this file states what the ELF
   spec says, and an "xv6-loadable" predicate at exec-spec time is where the
   extra hypotheses ([ee_phoff f < 2^31], [ep_offset p < 2^31], ...) belong,
   because they are facts about the CODE's ability to read the file, not
   about the file.  Under them the bridge is a one-line congruence through
   [ElfEnc.le_at_ext].

   ONE BYTE ASSEMBLER IN THE TREE.  Every reader here is built on
   [RiscvModelBytes.assemble_bytes], through [elf_le_at], which is exactly
   [ElfEnc.le_at]'s body with the buffer's naming function [f : nat -> bv 8]
   replaced by a list's total lookup [(l !!!)].  There is deliberately no
   second little-endian assembler; see [ElfEnc.v]'s header for the rule.

   TOTAL vs OPTION, and why the split is where it is.  [elf_le_at] is TOTAL
   (list [!!!] returns the inhabitant on an out-of-range index), so every
   reader could be total; the readers nonetheless return [option Z] and a
   [None] carries "the file is too short".  Two consequences the consumers
   rely on:
     - [elf_phdrs] / [elf_shdrs] / [elf_parse_ehdr] / [elf_entry] are
       [option]: a truncated file has no header table, and saying so is
       the point.
     - [elf_loads] and hence the IMAGE functions are TOTAL, returning [] /
       [empty] on a file that does not parse.  [elf_image] of garbage is
       [empty], which is harmless, and [elf_wf] is what carries the meaning.
   Making the image functions total is what keeps a spec from having to
   thread an [option (gmap ...)] through every rule.

   EXECUTABILITY.  Every definition is meant to be run by [vm_compute] on a
   ~55 kB file, so: [Z] arithmetic throughout (a [nat] appears only as
   structural fuel, via [Z.to_nat]); segment windows are ONE [take]/[drop]
   pass, never a per-byte [!!!] walk; and nothing anywhere reverses a list
   ([List.rev] is quadratic and costs ~55 s on a 55k list).  Header and
   program-header reads are near the front of the file so their [!!!] walks
   are cheap; the SECTION table sits at the very end, so [elf_shdrs] is the
   one construction whose cost is a real (but small, ~1 s) constant.

   iris-FREE (no proofmode, no ssreflect), like [ElfEnc.v] and
   [RiscvModelBytes.v], so vanilla [rewrite ... by ...] stays available. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap.
From stdpp Require Import bitvector.definitions.
Require Import RiscvModelBytes.

Local Open Scope Z_scope.

(* The file contents.  Index = FILE OFFSET, always. *)
Definition elf_bytes := list (bv 8).

(* ====================================================================== *)
(*  Little-endian readers                                                 *)
(* ====================================================================== *)

(* [ElfEnc.le_at]'s body with [f : nat -> bv 8] replaced by [(l !!!)]. *)
Definition elf_le_at (l : elf_bytes) (o n : nat) : Z :=
  assemble_bytes (map (fun j => l !!! (o + j)%nat) (seq 0 n)).

(* [map] (Stdlib) and [<$>] (stdpp) are the same function; bridged once. *)
Lemma elf_map_is_fmap {A B : Type} (g : A -> B) (l : list A) : map g l = g <$> l.
Proof. induction l as [|x l IH]; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Lemma elf_le_bytes_length (l : elf_bytes) (o n : nat) :
  length (map (fun j => l !!! (o + j)%nat) (seq 0 n)) = n.
Proof. rewrite elf_map_is_fmap, length_fmap, length_seq. reflexivity. Qed.

(* THE SPELLING BRIDGE between the [le_at]-shaped readers and the
   [take]/[drop]-shaped segment windows below. *)
Lemma elf_le_bytes_take_drop (l : elf_bytes) (o n : nat) :
  (o + n <= length l)%nat ->
  map (fun j => l !!! (o + j)%nat) (seq 0 n) = take n (drop o l).
Proof.
  intros Hlen. apply list_eq. intros j.
  rewrite elf_map_is_fmap, list_lookup_fmap.
  destruct (Nat.lt_ge_cases j n) as [Hj|Hj].
  - rewrite lookup_seq_lt by exact Hj. simpl.
    rewrite lookup_take by exact Hj. rewrite lookup_drop.
    rewrite (list_lookup_lookup_total_lt l (o + j)%nat) by lia.
    reflexivity.
  - rewrite lookup_ge_None_2 by (rewrite length_seq; lia). simpl.
    symmetry. apply lookup_ge_None_2.
    rewrite length_take, length_drop. lia.
Qed.

(* Are the [n] bytes at index [o] all present?  Checking only the LAST of
   them keeps this O(o+n) rather than O(length l). *)
Definition elf_avail (l : elf_bytes) (o n : nat) : bool :=
  match n with
  | O => true
  | S k => match l !! (o + k)%nat with Some _ => true | None => false end
  end.

Lemma elf_avail_spec (l : elf_bytes) (o n : nat) :
  (0 < n)%nat -> (elf_avail l o n = true <-> (o + n <= length l)%nat).
Proof.
  intros Hn. destruct n as [|k]; [lia|]. simpl elf_avail.
  destruct (l !! (o + k)%nat) eqn:Hl.
  - split; [intros _|reflexivity].
    apply lookup_lt_Some in Hl. lia.
  - split; [discriminate|]. intros Hle.
    assert (Hs : is_Some (l !! (o + k)%nat)) by (apply lookup_lt_is_Some_2; lia).
    destruct Hs as [x Hx]. rewrite Hl in Hx. discriminate.
Qed.

(* [elf_read f o n]: the [n]-byte little-endian value at file offset [o],
   or [None] if the file is too short (or [o] is negative). *)
Definition elf_read (f : elf_bytes) (o : Z) (n : nat) : option Z :=
  if (0 <=? o) && elf_avail f (Z.to_nat o) n
  then Some (elf_le_at f (Z.to_nat o) n) else None.

Definition elf_read_u8  (f : elf_bytes) (o : Z) : option Z := elf_read f o 1.
Definition elf_read_u16 (f : elf_bytes) (o : Z) : option Z := elf_read f o 2.
Definition elf_read_u32 (f : elf_bytes) (o : Z) : option Z := elf_read f o 4.
Definition elf_read_u64 (f : elf_bytes) (o : Z) : option Z := elf_read f o 8.

Lemma elf_read_Some (f : elf_bytes) (o : Z) (n : nat) (v : Z) :
  (0 < n)%nat ->
  (elf_read f o n = Some v
   <-> 0 <= o /\ o + Z.of_nat n <= Z.of_nat (length f)
       /\ v = elf_le_at f (Z.to_nat o) n).
Proof.
  intros Hn. unfold elf_read.
  destruct (0 <=? o) eqn:Ho; simpl.
  - apply Z.leb_le in Ho.
    destruct (elf_avail f (Z.to_nat o) n) eqn:Hav.
    + apply (elf_avail_spec f (Z.to_nat o) n) in Hav; [|exact Hn].
      split.
      * intros [= <-]. split; [exact Ho|]. split; [lia|reflexivity].
      * intros (_ & _ & ->). reflexivity.
    + split; [discriminate|]. intros (_ & Hle & _).
      assert (Hc : elf_avail f (Z.to_nat o) n = true)
        by (apply (elf_avail_spec f (Z.to_nat o) n); [exact Hn|lia]).
      rewrite Hc in Hav. discriminate.
  - apply Z.leb_gt in Ho.
    split; [discriminate|]. intros (Hge & _). lia.
Qed.

(* ====================================================================== *)
(*  The three header records                                              *)
(* ====================================================================== *)

Record elf_ehdr := ElfEhdr {
  ee_entry : Z;      (* e_entry     @ 0x18, u64 *)
  ee_phoff : Z;      (* e_phoff     @ 0x20, u64 *)
  ee_phentsize : Z;  (* e_phentsize @ 0x36, u16 *)
  ee_phnum : Z;      (* e_phnum     @ 0x38, u16 *)
  ee_shoff : Z;      (* e_shoff     @ 0x28, u64 *)
  ee_shentsize : Z;  (* e_shentsize @ 0x3A, u16 *)
  ee_shnum : Z;      (* e_shnum     @ 0x3C, u16 *)
  ee_shstrndx : Z;   (* e_shstrndx  @ 0x3E, u16 *)
}.

Record elf_phdr := ElfPhdr {
  ep_type : Z;       (* p_type   @ 0,  u32 *)
  ep_flags : Z;      (* p_flags  @ 4,  u32 *)
  ep_offset : Z;     (* p_offset @ 8,  u64 *)
  ep_vaddr : Z;      (* p_vaddr  @ 16, u64 *)
  ep_paddr : Z;      (* p_paddr  @ 24, u64 *)
  ep_filesz : Z;     (* p_filesz @ 32, u64 *)
  ep_memsz : Z;      (* p_memsz  @ 40, u64 *)
  ep_align : Z;      (* p_align  @ 48, u64 *)
}.

Record elf_shdr := ElfShdr {
  es_name : Z;       (* sh_name   @ 0,  u32 *)
  es_type : Z;       (* sh_type   @ 4,  u32 *)
  es_flags : Z;      (* sh_flags  @ 8,  u64 *)
  es_addr : Z;       (* sh_addr   @ 16, u64 *)
  es_offset : Z;     (* sh_offset @ 24, u64 *)
  es_size : Z;       (* sh_size   @ 32, u64 *)
}.

Global Instance elf_ehdr_eq_dec : EqDecision elf_ehdr.
Proof. solve_decision. Defined.
Global Instance elf_phdr_eq_dec : EqDecision elf_phdr.
Proof. solve_decision. Defined.
Global Instance elf_shdr_eq_dec : EqDecision elf_shdr.
Proof. solve_decision. Defined.

(* ====================================================================== *)
(*  Parsing                                                               *)
(* ====================================================================== *)

Definition elf_byte_is (f : elf_bytes) (o v : Z) : bool :=
  match elf_read_u8 f o with Some b => Z.eqb b v | None => false end.

(* \x7f E L F, then EI_CLASS = 2 (ELF64) and EI_DATA = 1 (little-endian). *)
Definition elf_magic_ok (f : elf_bytes) : bool :=
  elf_byte_is f 0 0x7f && elf_byte_is f 1 0x45 &&
  elf_byte_is f 2 0x4c && elf_byte_is f 3 0x46 &&
  elf_byte_is f 4 2 && elf_byte_is f 5 1.

Definition elf_parse_ehdr (f : elf_bytes) : option elf_ehdr :=
  entry ← elf_read_u64 f 0x18;
  phoff ← elf_read_u64 f 0x20;
  shoff ← elf_read_u64 f 0x28;
  phentsize ← elf_read_u16 f 0x36;
  phnum ← elf_read_u16 f 0x38;
  shentsize ← elf_read_u16 f 0x3A;
  shnum ← elf_read_u16 f 0x3C;
  shstrndx ← elf_read_u16 f 0x3E;
  Some (ElfEhdr entry phoff phentsize phnum shoff shentsize shnum shstrndx).

Definition elf_parse_phdr (f : elf_bytes) (o : Z) : option elf_phdr :=
  ty ← elf_read_u32 f o;
  fl ← elf_read_u32 f (o + 4);
  off ← elf_read_u64 f (o + 8);
  va ← elf_read_u64 f (o + 16);
  pa ← elf_read_u64 f (o + 24);
  fsz ← elf_read_u64 f (o + 32);
  msz ← elf_read_u64 f (o + 40);
  al ← elf_read_u64 f (o + 48);
  Some (ElfPhdr ty fl off va pa fsz msz al).

Definition elf_parse_shdr (f : elf_bytes) (o : Z) : option elf_shdr :=
  nm ← elf_read_u32 f o;
  ty ← elf_read_u32 f (o + 4);
  fl ← elf_read_u64 f (o + 8);
  ad ← elf_read_u64 f (o + 16);
  off ← elf_read_u64 f (o + 24);
  sz ← elf_read_u64 f (o + 32);
  Some (ElfShdr nm ty fl ad off sz).

(* [n] entries of [step] bytes each, starting at [o], IN TABLE ORDER --
   fuel counts down and each entry is consed onto the front of the tail's
   result, so no reversal is needed. *)
Fixpoint elf_table {A : Type} (parse : Z -> option A) (o step : Z) (n : nat)
  : option (list A) :=
  match n with
  | O => Some nil
  | S k => a ← parse o; r ← elf_table parse (o + step) step k; Some (a :: r)
  end.

Definition elf_phdrs (f : elf_bytes) : option (list elf_phdr) :=
  e ← elf_parse_ehdr f;
  elf_table (elf_parse_phdr f) (ee_phoff e) (ee_phentsize e) (Z.to_nat (ee_phnum e)).

Definition elf_shdrs (f : elf_bytes) : option (list elf_shdr) :=
  e ← elf_parse_ehdr f;
  elf_table (elf_parse_shdr f) (ee_shoff e) (ee_shentsize e) (Z.to_nat (ee_shnum e)).

(* PT_LOAD = 1.  TOTAL: a file that does not parse simply has no segments. *)
Definition elf_loads (f : elf_bytes) : list elf_phdr :=
  match elf_phdrs f with
  | Some ps => List.filter (fun p => Z.eqb (ep_type p) 1) ps
  | None => nil
  end.

Definition elf_entry (f : elf_bytes) : option Z := ee_entry <$> elf_parse_ehdr f.

(* ====================================================================== *)
(*  THE SEMANTICS: the memory image a loader must establish               *)
(* ====================================================================== *)

Definition elf_zero_byte : bv 8 := Z_to_bv 8 0.

(* The [filesz] window at [offset] -- one [take]/[drop] pass. *)
Definition seg_file_bytes (f : elf_bytes) (p : elf_phdr) : list (bv 8) :=
  take (Z.to_nat (ep_filesz p)) (drop (Z.to_nat (ep_offset p)) f).

Definition seg_file_map (f : elf_bytes) (p : elf_phdr) : gmap Z (bv 8) :=
  map_seqZ (ep_vaddr p) (seg_file_bytes f p).

(* The .bss tail: [memsz - filesz] zero bytes above the file window. *)
Definition seg_zero_bytes (p : elf_phdr) : list (bv 8) :=
  replicate (Z.to_nat (ep_memsz p - ep_filesz p)) elf_zero_byte.

Definition seg_zero_map (p : elf_phdr) : gmap Z (bv 8) :=
  map_seqZ (ep_vaddr p + ep_filesz p) (seg_zero_bytes p).

Definition seg_map (f : elf_bytes) (p : elf_phdr) : gmap Z (bv 8) :=
  seg_file_map f p ∪ seg_zero_map p.

(* The union of a per-segment map over a segment list. *)
Definition segs_union {A : Type} (g : A -> gmap Z (bv 8)) (ps : list A)
  : gmap Z (bv 8) := foldr (fun p m => g p ∪ m) ∅ ps.

Definition elf_file_image (f : elf_bytes) : gmap Z (bv 8) :=
  segs_union (seg_file_map f) (elf_loads f).
Definition elf_zero_image (f : elf_bytes) : gmap Z (bv 8) :=
  segs_union seg_zero_map (elf_loads f).
Definition elf_image (f : elf_bytes) : gmap Z (bv 8) :=
  segs_union (seg_map f) (elf_loads f).

(* ====================================================================== *)
(*  Geometry -- the dump's vocabulary                                     *)
(* ====================================================================== *)

Definition zlist_min (l : list Z) : option Z :=
  match l with nil => None | x :: r => Some (foldr Z.min x r) end.
Definition zlist_max (l : list Z) : option Z :=
  match l with nil => None | x :: r => Some (foldr Z.max x r) end.

Definition elf_mem_base (f : elf_bytes) : option Z :=
  zlist_min (ep_vaddr <$> elf_loads f).
Definition elf_mem_end (f : elf_bytes) : option Z :=
  zlist_max ((fun p => ep_vaddr p + ep_memsz p) <$> elf_loads f).

(* EXACTLY the shape of [KernelData.kernel_segments]: (vaddr, filesz,
   memsz, flags) per PT_LOAD, in program-header order. *)
Definition elf_segments (f : elf_bytes) : option (list (Z * Z * Z * Z)) :=
  ps ← elf_phdrs f;
  Some ((fun p => (ep_vaddr p, ep_filesz p, ep_memsz p, ep_flags p))
          <$> List.filter (fun p => Z.eqb (ep_type p) 1) ps).

(* The read-only / writable split, which a single RWX PT_LOAD cannot
   express: the LOWEST address of an allocated WRITABLE section, or -- if
   there is none -- the end of the image, i.e. the whole image is
   read-only.  Mirrors [rodata_end] in tools/dump_elf.py. *)
Definition sh_alloc_write (s : elf_shdr) : bool :=
  negb (Z.eqb (Z.land (es_flags s) 2) 0) && negb (Z.eqb (Z.land (es_flags s) 1) 0).

Definition elf_rodata_end (f : elf_bytes) : option Z :=
  ss ← elf_shdrs f;
  match zlist_min (es_addr <$> List.filter sh_alloc_write ss) with
  | Some a => Some a
  | None => elf_mem_end f
  end.

(* ====================================================================== *)
(*  Well-formedness                                                       *)
(* ====================================================================== *)

Definition phdr_wf (f : elf_bytes) (p : elf_phdr) : bool :=
  (0 <=? ep_offset p) && (0 <=? ep_filesz p) &&
  (ep_offset p + ep_filesz p <=? Z.of_nat (length f)) &&
  (ep_filesz p <=? ep_memsz p) &&
  (0 <=? ep_vaddr p) && (ep_vaddr p + ep_memsz p <? 2 ^ 64).

(* Two segments' MEMORY ranges do not overlap.  The last two disjuncts
   make an empty segment vacuously disjoint from everything. *)
Definition range_disj_b (p q : elf_phdr) : bool :=
  (ep_vaddr p + ep_memsz p <=? ep_vaddr q) || (ep_vaddr q + ep_memsz q <=? ep_vaddr p)
  || (ep_memsz p <=? 0) || (ep_memsz q <=? 0).

Fixpoint loads_disjoint_b (ps : list elf_phdr) : bool :=
  match ps with
  | nil => true
  | p :: r => List.forallb (range_disj_b p) r && loads_disjoint_b r
  end.

Definition elf_wf (f : elf_bytes) : bool :=
  match elf_parse_ehdr f, elf_phdrs f with
  | Some e, Some _ =>
      elf_magic_ok f &&
      (ee_phentsize e =? 56) &&
      (0 <=? ee_phoff e) && (0 <=? ee_phnum e) &&
      (ee_phoff e + ee_phnum e * 56 <=? Z.of_nat (length f)) &&
      List.forallb (phdr_wf f) (elf_loads f) &&
      loads_disjoint_b (elf_loads f)
  | _, _ => false
  end.

(* The section side.  exec() never reads sections, so this is a SEPARATE
   predicate: an image can be perfectly loadable with a broken (or
   stripped-away) section table. *)
Definition elf_sections_wf (f : elf_bytes) : bool :=
  match elf_parse_ehdr f, elf_shdrs f with
  | Some e, Some _ =>
      (ee_shentsize e =? 64) &&
      (0 <=? ee_shoff e) && (0 <=? ee_shnum e) &&
      (ee_shoff e + ee_shnum e * 64 <=? Z.of_nat (length f))
  | _, _ => false
  end.

(* ====================================================================== *)
(*  Reading [elf_wf] back as a proposition                                *)
(* ====================================================================== *)

Record phdr_ok (f : elf_bytes) (p : elf_phdr) : Prop := {
  po_offset : 0 <= ep_offset p;
  po_filesz : 0 <= ep_filesz p;
  po_window : ep_offset p + ep_filesz p <= Z.of_nat (length f);
  po_memsz : ep_filesz p <= ep_memsz p;
  po_vaddr : 0 <= ep_vaddr p;
  po_top : ep_vaddr p + ep_memsz p < 2 ^ 64;
}.

Lemma phdr_wf_ok (f : elf_bytes) (p : elf_phdr) : phdr_wf f p = true -> phdr_ok f p.
Proof.
  unfold phdr_wf. intros H.
  rewrite !andb_true_iff in H.
  destruct H as [[[[[H1 H2] H3] H4] H5] H6].
  apply Z.leb_le in H1, H2, H3, H4, H5. apply Z.ltb_lt in H6.
  constructor; assumption.
Qed.

(* [a] lies in [p]'s loaded memory range. *)
Definition in_seg (p : elf_phdr) (a : Z) : Prop :=
  ep_vaddr p <= a < ep_vaddr p + ep_memsz p.

Lemma range_disj_b_spec (p q : elf_phdr) (a : Z) :
  range_disj_b p q = true -> in_seg p a -> in_seg q a -> False.
Proof.
  unfold range_disj_b, in_seg. rewrite !orb_true_iff, !Z.leb_le. lia.
Qed.

Lemma loads_disjoint_b_spec (ps : list elf_phdr) (p q : elf_phdr) :
  loads_disjoint_b ps = true -> p ∈ ps -> q ∈ ps -> p <> q ->
  range_disj_b p q = true.
Proof.
  induction ps as [|c ps IH]; intros Hd Hp Hq Hne.
  { inversion Hp. }
  simpl in Hd. apply andb_true_iff in Hd as [Hall Hd].
  rewrite elem_of_cons in Hp, Hq.
  rewrite List.forallb_forall in Hall.
  setoid_rewrite <- elem_of_list_In in Hall.
  destruct Hp as [->|Hp]; destruct Hq as [->|Hq].
  - contradiction.
  - apply Hall, Hq.
  - specialize (Hall p Hp).
    unfold range_disj_b in *. rewrite !orb_true_iff in *. tauto.
  - apply IH; assumption.
Qed.

Lemma elf_wf_phdr_ok (f : elf_bytes) (p : elf_phdr) :
  elf_wf f = true -> p ∈ elf_loads f -> phdr_ok f p.
Proof.
  unfold elf_wf. destruct (elf_parse_ehdr f) as [e|]; [|discriminate].
  destruct (elf_phdrs f) as [ps|]; [|discriminate].
  intros H Hp.
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [_ Hall].
  rewrite List.forallb_forall in Hall.
  apply phdr_wf_ok, Hall, elem_of_list_In, Hp.
Qed.

Lemma elf_wf_loads_disj (f : elf_bytes) (p q : elf_phdr) (a : Z) :
  elf_wf f = true -> p ∈ elf_loads f -> q ∈ elf_loads f -> p <> q ->
  in_seg p a -> in_seg q a -> False.
Proof.
  intros Hwf Hp Hq Hne. eapply range_disj_b_spec.
  eapply loads_disjoint_b_spec; [|exact Hp|exact Hq|exact Hne].
  revert Hwf. unfold elf_wf.
  destruct (elf_parse_ehdr f) as [e|]; [|discriminate].
  destruct (elf_phdrs f) as [ps|]; [|discriminate].
  rewrite !andb_true_iff. tauto.
Qed.

(* ====================================================================== *)
(*  Segment lookup laws                                                   *)
(* ====================================================================== *)

Lemma seg_file_bytes_length (f : elf_bytes) (p : elf_phdr) :
  phdr_ok f p -> Z.of_nat (length (seg_file_bytes f p)) = ep_filesz p.
Proof.
  intros [Ho Hf Hw Hm Hv Ht]. unfold seg_file_bytes.
  rewrite length_take, length_drop. lia.
Qed.

Lemma seg_file_bytes_lookup (f : elf_bytes) (p : elf_phdr) (k : nat) :
  phdr_ok f p -> (Z.of_nat k < ep_filesz p) ->
  seg_file_bytes f p !! k = f !! (Z.to_nat (ep_offset p) + k)%nat.
Proof.
  intros [Ho Hf Hw Hm Hv Ht] Hk. unfold seg_file_bytes.
  rewrite lookup_take by lia. rewrite lookup_drop. reflexivity.
Qed.

Lemma lookup_seg_file_map (f : elf_bytes) (p : elf_phdr) (a : Z) (b : bv 8) :
  phdr_ok f p ->
  (seg_file_map f p !! a = Some b
   <-> ep_vaddr p <= a < ep_vaddr p + ep_filesz p
       /\ f !! Z.to_nat (ep_offset p + (a - ep_vaddr p)) = Some b).
Proof.
  intros Hok. pose proof Hok as [Ho Hf Hw Hm Hv Ht].
  pose proof (seg_file_bytes_length f p Hok) as Hlen.
  unfold seg_file_map. rewrite lookup_map_seqZ_Some. split.
  - intros [Hge Hl].
    pose proof (lookup_lt_Some _ _ _ Hl) as Hlt.
    assert (Hb : a < ep_vaddr p + ep_filesz p) by lia.
    rewrite seg_file_bytes_lookup in Hl by (exact Hok || lia).
    split; [lia|].
    replace (Z.to_nat (ep_offset p + (a - ep_vaddr p)))
      with (Z.to_nat (ep_offset p) + Z.to_nat (a - ep_vaddr p))%nat by lia.
    exact Hl.
  - intros [Hrange Hl]. split; [lia|].
    rewrite seg_file_bytes_lookup by (exact Hok || lia).
    replace (Z.to_nat (ep_offset p) + Z.to_nat (a - ep_vaddr p))%nat
      with (Z.to_nat (ep_offset p + (a - ep_vaddr p))) by lia.
    exact Hl.
Qed.

Lemma seg_zero_bytes_length (p : elf_phdr) :
  ep_filesz p <= ep_memsz p ->
  Z.of_nat (length (seg_zero_bytes p)) = ep_memsz p - ep_filesz p.
Proof. intros H. unfold seg_zero_bytes. rewrite length_replicate. lia. Qed.

Lemma lookup_seg_zero_map (p : elf_phdr) (a : Z) (b : bv 8) :
  ep_filesz p <= ep_memsz p ->
  (seg_zero_map p !! a = Some b
   <-> ep_vaddr p + ep_filesz p <= a < ep_vaddr p + ep_memsz p /\ b = elf_zero_byte).
Proof.
  intros Hm. unfold seg_zero_map, seg_zero_bytes.
  rewrite lookup_map_seqZ_Some. split.
  - intros [Hge Hl]. apply lookup_replicate in Hl as [-> Hlt].
    split; [lia|reflexivity].
  - intros [Hrange ->]. split; [lia|].
    apply lookup_replicate. split; [reflexivity|lia].
Qed.

Lemma seg_file_zero_disjoint (f : elf_bytes) (p : elf_phdr) :
  phdr_ok f p -> seg_file_map f p ##ₘ seg_zero_map p.
Proof.
  intros Hok. pose proof (seg_file_bytes_length f p Hok) as Hlen.
  unfold seg_file_map, seg_zero_map. apply map_seqZ_disjoint. lia.
Qed.

Lemma lookup_seg_map (f : elf_bytes) (p : elf_phdr) (a : Z) (b : bv 8) :
  phdr_ok f p ->
  (seg_map f p !! a = Some b
   <-> (ep_vaddr p <= a < ep_vaddr p + ep_filesz p
        /\ f !! Z.to_nat (ep_offset p + (a - ep_vaddr p)) = Some b)
       \/ (ep_vaddr p + ep_filesz p <= a < ep_vaddr p + ep_memsz p
           /\ b = elf_zero_byte)).
Proof.
  intros Hok. pose proof Hok as [Ho Hf Hw Hm Hv Ht].
  unfold seg_map.
  rewrite lookup_union_Some by (apply seg_file_zero_disjoint, Hok).
  rewrite lookup_seg_file_map by exact Hok.
  rewrite lookup_seg_zero_map by exact Hm.
  reflexivity.
Qed.

Lemma seg_map_in_seg (f : elf_bytes) (p : elf_phdr) (a : Z) :
  phdr_ok f p -> (is_Some (seg_map f p !! a) <-> in_seg p a).
Proof.
  intros Hok. pose proof Hok as [Ho Hf Hw Hm Hv Ht]. unfold in_seg. split.
  - intros [b Hb]. apply lookup_seg_map in Hb as [[? ?]|[? ?]]; [lia|lia|exact Hok].
  - intros Hr.
    destruct (Z_lt_le_dec a (ep_vaddr p + ep_filesz p)) as [Hlt|Hge].
    + assert (Hi : (Z.to_nat (ep_offset p + (a - ep_vaddr p)) < length f)%nat) by lia.
      apply lookup_lt_is_Some_2 in Hi as [b Hb].
      exists b. apply lookup_seg_map; [exact Hok|]. left. split; [lia|exact Hb].
    + exists elf_zero_byte. apply lookup_seg_map; [exact Hok|].
      right. split; [lia|reflexivity].
Qed.

Lemma seg_map_disjoint (f : elf_bytes) (p q : elf_phdr) :
  phdr_ok f p -> phdr_ok f q ->
  (forall a, in_seg p a -> in_seg q a -> False) ->
  seg_map f p ##ₘ seg_map f q.
Proof.
  intros Hp Hq Hdisj. apply map_disjoint_spec. intros a x y Hx Hy.
  apply (Hdisj a).
  - apply (seg_map_in_seg f p a Hp). exists x. exact Hx.
  - apply (seg_map_in_seg f q a Hq). exists y. exact Hy.
Qed.

Lemma seg_file_zero_disjoint_cross (f : elf_bytes) (p q : elf_phdr) :
  phdr_ok f p -> phdr_ok f q ->
  (p = q \/ (forall a, in_seg p a -> in_seg q a -> False)) ->
  seg_file_map f p ##ₘ seg_zero_map q.
Proof.
  intros Hp Hq [->|Hdisj]; [apply seg_file_zero_disjoint, Hq|].
  apply (map_disjoint_weaken _ (seg_map f p) _ (seg_map f q)).
  - apply seg_map_disjoint; assumption.
  - apply map_union_subseteq_l.
  - apply map_union_subseteq_r, seg_file_zero_disjoint, Hq.
Qed.

(* ====================================================================== *)
(*  The union of a family of segment maps                                 *)
(* ====================================================================== *)

Section segs.
  Context {A : Type} `{EqDecision A}.
  Implicit Types g : A -> gmap Z (bv 8).

  Lemma segs_union_lookup_inv g (ps : list A) (a : Z) (b : bv 8) :
    segs_union g ps !! a = Some b -> exists p, p ∈ ps /\ g p !! a = Some b.
  Proof.
    induction ps as [|c ps IH]; simpl.
    { rewrite lookup_empty. discriminate. }
    intros H. apply lookup_union_Some_raw in H as [H|[_ H]].
    - exists c. split; [apply elem_of_list_here|exact H].
    - apply IH in H as [p [Hp Hg]]. exists p.
      split; [apply elem_of_list_further, Hp|exact Hg].
  Qed.

  Lemma segs_union_disjoint_l g1 g2 (p : A) (qs : list A) :
    (forall q, q ∈ qs -> g1 p ##ₘ g2 q) -> g1 p ##ₘ segs_union g2 qs.
  Proof.
    induction qs as [|c qs IH]; simpl; intros H.
    { apply map_disjoint_empty_r. }
    apply map_disjoint_union_r_2.
    - apply H, elem_of_list_here.
    - apply IH. intros q Hq. apply H, elem_of_list_further, Hq.
  Qed.

  Lemma segs_union_disjoint g1 g2 (ps qs : list A) :
    (forall p q, p ∈ ps -> q ∈ qs -> g1 p ##ₘ g2 q) ->
    segs_union g1 ps ##ₘ segs_union g2 qs.
  Proof.
    induction ps as [|c ps IH]; simpl; intros H.
    { apply map_disjoint_empty_l. }
    apply map_disjoint_union_l_2.
    - apply segs_union_disjoint_l. intros q Hq.
      apply H; [apply elem_of_list_here|exact Hq].
    - apply IH. intros p q Hp Hq.
      apply H; [apply elem_of_list_further, Hp|exact Hq].
  Qed.

  Lemma segs_union_lookup g (ps : list A) (a : Z) (b : bv 8) :
    (forall p q, p ∈ ps -> q ∈ ps -> p <> q -> g p ##ₘ g q) ->
    (segs_union g ps !! a = Some b <-> exists p, p ∈ ps /\ g p !! a = Some b).
  Proof.
    intros Hdisj. split; [apply segs_union_lookup_inv|].
    revert Hdisj. induction ps as [|c ps IH]; simpl; intros Hdisj [p [Hp Hg]].
    { inversion Hp. }
    rewrite elem_of_cons in Hp. destruct Hp as [->|Hp].
    - apply lookup_union_Some_l, Hg.
    - assert (Hrest : segs_union g ps !! a = Some b).
      { apply IH; [|exists p; split; assumption].
        intros x y Hx Hy Hne.
        apply Hdisj; [apply elem_of_list_further, Hx
                     |apply elem_of_list_further, Hy|exact Hne]. }
      destruct (decide (c = p)) as [->|Hne].
      + apply lookup_union_Some_l, Hg.
      + apply lookup_union_Some_raw. right. split; [|exact Hrest].
        apply (map_disjoint_Some_l (g p) (g c) a b); [|exact Hg].
        apply Hdisj; [apply elem_of_list_further, Hp
                     |apply elem_of_list_here|congruence].
  Qed.

  Lemma segs_union_elem_of_dom g (ps : list A) (a : Z) :
    a ∈ dom (segs_union g ps) <-> exists p, p ∈ ps /\ a ∈ dom (g p).
  Proof.
    induction ps as [|c ps IH]; simpl.
    { rewrite dom_empty_L, elem_of_empty. split; [contradiction|].
      intros [p [Hp _]]. inversion Hp. }
    rewrite dom_union_L, elem_of_union, IH. split.
    - intros [H|[p [Hp Hg]]].
      + exists c. split; [apply elem_of_list_here|exact H].
      + exists p. split; [apply elem_of_list_further, Hp|exact Hg].
    - intros [p [Hp Hg]]. rewrite elem_of_cons in Hp.
      destruct Hp as [->|Hp]; [left; exact Hg|right; exists p; split; assumption].
  Qed.

  Lemma segs_union_split g1 g2 (ps : list A) :
    (forall p q, p ∈ ps -> q ∈ ps -> g1 p ##ₘ g2 q) ->
    segs_union (fun p => g1 p ∪ g2 p) ps = segs_union g1 ps ∪ segs_union g2 ps.
  Proof.
    induction ps as [|c ps IH]; simpl; intros H.
    { rewrite (left_id_L ∅ (∪)). reflexivity. }
    rewrite IH by (intros p q Hp Hq;
                   apply H; apply elem_of_list_further; assumption).
    assert (Hbx : g2 c ##ₘ segs_union g1 ps).
    { apply segs_union_disjoint_l. intros q Hq. apply symmetry.
      apply H; [apply elem_of_list_further, Hq|apply elem_of_list_here]. }
    rewrite <- !(assoc_L (∪)). f_equal.
    rewrite !(assoc_L (∪)). rewrite (map_union_comm _ _ Hbx). reflexivity.
  Qed.
End segs.

(* ====================================================================== *)
(*  THE ABSTRACT LAWS -- what an exec() spec consumes                     *)
(* ====================================================================== *)

Lemma elf_wf_seg_map_disjoint (f : elf_bytes) (p q : elf_phdr) :
  elf_wf f = true -> p ∈ elf_loads f -> q ∈ elf_loads f -> p <> q ->
  seg_map f p ##ₘ seg_map f q.
Proof.
  intros Hwf Hp Hq Hne. apply seg_map_disjoint.
  - eapply elf_wf_phdr_ok; eassumption.
  - eapply elf_wf_phdr_ok; eassumption.
  - intros a. eapply elf_wf_loads_disj; eassumption.
Qed.

Lemma elf_wf_file_zero_disjoint (f : elf_bytes) (p q : elf_phdr) :
  elf_wf f = true -> p ∈ elf_loads f -> q ∈ elf_loads f ->
  seg_file_map f p ##ₘ seg_zero_map q.
Proof.
  intros Hwf Hp Hq.
  assert (Hokp : phdr_ok f p) by (eapply elf_wf_phdr_ok; eassumption).
  assert (Hokq : phdr_ok f q) by (eapply elf_wf_phdr_ok; eassumption).
  apply seg_file_zero_disjoint_cross; [exact Hokp|exact Hokq|].
  destruct (decide (p = q)) as [->|Hne]; [left; reflexivity|].
  right. intros a. eapply elf_wf_loads_disj; eassumption.
Qed.

(* [elf_image] IS the disjoint union of its file-backed and zero parts. *)
Lemma elf_image_split (f : elf_bytes) :
  elf_wf f = true ->
  elf_image f = elf_file_image f ∪ elf_zero_image f
  /\ elf_file_image f ##ₘ elf_zero_image f.
Proof.
  intros Hwf. split.
  - unfold elf_image, elf_file_image, elf_zero_image, seg_map.
    apply segs_union_split. intros p q Hp Hq.
    eapply elf_wf_file_zero_disjoint; eassumption.
  - unfold elf_file_image, elf_zero_image.
    apply segs_union_disjoint. intros p q Hp Hq.
    eapply elf_wf_file_zero_disjoint; eassumption.
Qed.

(* THE lookup law: every byte of the image is either a file byte at the
   segment's file offset, or a zero of the segment's .bss tail. *)
Lemma elf_image_lookup (f : elf_bytes) (a : Z) (b : bv 8) :
  elf_wf f = true ->
  (elf_image f !! a = Some b
   <-> exists p, p ∈ elf_loads f /\
         ((ep_vaddr p <= a < ep_vaddr p + ep_filesz p
           /\ f !! Z.to_nat (ep_offset p + (a - ep_vaddr p)) = Some b)
          \/ (ep_vaddr p + ep_filesz p <= a < ep_vaddr p + ep_memsz p
              /\ b = elf_zero_byte))).
Proof.
  intros Hwf. unfold elf_image.
  rewrite segs_union_lookup
    by (intros p q Hp Hq Hne; eapply elf_wf_seg_map_disjoint; eassumption).
  split.
  - intros [p [Hp Hg]]. exists p. split; [exact Hp|].
    apply lookup_seg_map; [eapply elf_wf_phdr_ok; eassumption|exact Hg].
  - intros [p [Hp Hcase]]. exists p. split; [exact Hp|].
    apply lookup_seg_map; [eapply elf_wf_phdr_ok; eassumption|exact Hcase].
Qed.

Lemma elf_file_image_lookup (f : elf_bytes) (a : Z) (b : bv 8) :
  elf_wf f = true ->
  (elf_file_image f !! a = Some b
   <-> exists p, p ∈ elf_loads f /\
         ep_vaddr p <= a < ep_vaddr p + ep_filesz p /\
         f !! Z.to_nat (ep_offset p + (a - ep_vaddr p)) = Some b).
Proof.
  intros Hwf. unfold elf_file_image.
  rewrite segs_union_lookup.
  - split.
    + intros [p [Hp Hg]]. exists p.
      apply lookup_seg_file_map in Hg; [|eapply elf_wf_phdr_ok; eassumption].
      split; [exact Hp|exact Hg].
    + intros [p [Hp Hcase]]. exists p. split; [exact Hp|].
      apply lookup_seg_file_map; [eapply elf_wf_phdr_ok; eassumption|exact Hcase].
  - intros p q Hp Hq Hne.
    apply (map_disjoint_weaken _ (seg_map f p) _ (seg_map f q)).
    + eapply elf_wf_seg_map_disjoint; eassumption.
    + apply map_union_subseteq_l.
    + apply map_union_subseteq_l.
Qed.

Lemma elf_zero_image_lookup (f : elf_bytes) (a : Z) (b : bv 8) :
  elf_wf f = true ->
  (elf_zero_image f !! a = Some b
   <-> exists p, p ∈ elf_loads f /\
         ep_vaddr p + ep_filesz p <= a < ep_vaddr p + ep_memsz p /\
         b = elf_zero_byte).
Proof.
  intros Hwf. unfold elf_zero_image.
  rewrite segs_union_lookup.
  - split.
    + intros [p [Hp Hg]]. exists p.
      assert (Hok : phdr_ok f p) by (eapply elf_wf_phdr_ok; eassumption).
      apply lookup_seg_zero_map in Hg; [|apply Hok].
      split; [exact Hp|exact Hg].
    + intros [p [Hp Hcase]]. exists p. split; [exact Hp|].
      assert (Hok : phdr_ok f p) by (eapply elf_wf_phdr_ok; eassumption).
      apply lookup_seg_zero_map; [apply Hok|exact Hcase].
  - intros p q Hp Hq Hne.
    assert (Hokp : phdr_ok f p) by (eapply elf_wf_phdr_ok; eassumption).
    assert (Hokq : phdr_ok f q) by (eapply elf_wf_phdr_ok; eassumption).
    apply (map_disjoint_weaken _ (seg_map f p) _ (seg_map f q)).
    + eapply elf_wf_seg_map_disjoint; eassumption.
    + apply map_union_subseteq_r, seg_file_zero_disjoint, Hokp.
    + apply map_union_subseteq_r, seg_file_zero_disjoint, Hokq.
Qed.

(* The image's DOMAIN is exactly the union of the PT_LOAD memory ranges --
   [filesz] plays no role here, which is the point of [memsz]. *)
Lemma elf_image_dom (f : elf_bytes) (a : Z) :
  elf_wf f = true ->
  (a ∈ dom (elf_image f) <-> exists p, p ∈ elf_loads f /\ in_seg p a).
Proof.
  intros Hwf. unfold elf_image. rewrite segs_union_elem_of_dom. split.
  - intros [p [Hp Hd]]. exists p. split; [exact Hp|].
    apply (seg_map_in_seg f p a); [eapply elf_wf_phdr_ok; eassumption|].
    apply elem_of_dom, Hd.
  - intros [p [Hp Hr]]. exists p. split; [exact Hp|].
    apply elem_of_dom, (seg_map_in_seg f p a);
      [eapply elf_wf_phdr_ok; eassumption|exact Hr].
Qed.
