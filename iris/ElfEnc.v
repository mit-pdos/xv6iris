(* ElfEnc.v -- the ELF HEADER and PROGRAM HEADER byte vocabulary: the two
   stack buffers kexec reads its executable through, and the little-endian
   field projections it reads them with.

   The FIFTH byte vocabulary of the tree, after [BlockWords.v]'s words,
   [DinodeEnc.v]'s records, [BitmapEnc.v]'s bits and [DirentEnc.v]'s
   dirents -- and the first one that is a pure READER.  The four earlier
   files all encode a list of pure records INTO bytes because the kernel
   writes those bytes back; kexec never writes an ELF header, it only
   [readi]s 64 (resp. 56) bytes into a stack buffer and then loads four
   (resp. six) fields out of it.  So there is no [elfhdr] record and no
   [elfhdr_bytes] encoder here: the buffer is named by a function
   [f : nat -> bv 8] (a [ByteBuf] window's naming function), and a field is
   a Z-valued PROJECTION of that function.

   THE GEOMETRY IS READ OFF kexec's OWN INSTRUCTION STREAM, not off elf.h
   -- the rule [DinodeEnc.v], [DirentEnc.v] and [InodeInv.v] already state.
   The two buffers' bases come from the [addi] kexec hands [readi]:

     kexec+0x40   li a4,64 ; addi a2,s0,-432 ; jal readi
                                  ==>  ELF BUFFER BASE = s0-432, and
                                       sizeof(struct elfhdr) = 64
     kexec+0x132  mv a4,s11 (s11 = 56) ; addi a2,s0,-488 ; jal readi
                  kexec+0xbc  li s11,56
                                  ==>  PH BUFFER BASE = s0-488, and
                                       sizeof(struct proghdr) = 56

   and every field offset is then (displacement - base):

     kexec+0x54   lw  a4,-432(s0) ; lui a5,0x464c4 ; addi a5,a5,1407
                                  ==>  magic @ 0, 4 bytes, compared against
                                       0x464c457f = ELF_MAGIC
     kexec+0x2ec  ld  a4,-408(s0)   (into p->trapframe->epc)
                                  ==>  entry @ 24, 8 bytes
     kexec+0xb4   lw  a3,-400(s0)   (the [off] of the phdr loop)
                                  ==>  phoff @ 32, read as a 4-byte SIGNED
                                       load -- see the note below
     kexec+0xac   lhu a5,-376(s0) ; beqz a5,...    (the loop bound)
     kexec+0x124  lhu a5,-376(s0) ; bge s10,a5,...
                                  ==>  phnum @ 56, 2 bytes, ZERO-extended

     kexec+0x142  lw  a5,-488(s0) ; li a4,1 ; bne a5,a4,...
                                  ==>  ph.type   @ 0,  4 bytes, and
                                       ELF_PROG_LOAD = 1
     kexec+0x16c  lw  a0,-484(s0) ; jal flags2perm
                                  ==>  ph.flags  @ 4,  4 bytes
     kexec+0x194  lw  s7,-480(s0)   (the [offset] argument of loadseg)
                                  ==>  ph.off    @ 8,  4 bytes, SIGNED
     kexec+0x158  ld  a5,-472(s0) ; kexec+0x190  ld s8,-472(s0)
                                  ==>  ph.vaddr  @ 16, 8 bytes
     kexec+0x150  ld  a5,-456(s0) ; kexec+0x188  lw s3,-456(s0)
                                  ==>  ph.filesz @ 32, 8 bytes (and its LOW
                                       WORD is what the loadseg guard reads)
     kexec+0x14c  ld  s1,-448(s0)
                                  ==>  ph.memsz  @ 40, 8 bytes

   [ph.paddr] (@24) and [ph.align] (@48) are NEVER READ by kexec -- no
   instruction in the function touches -464(s0) or -440(s0) -- so this file
   deliberately gives them no projection.

   THE [int off] TRUNCATION.  The C writes

       for (i = 0, off = elf.phoff; i < elf.phnum; i++, off += sizeof(ph))

   with [int i, off], while [elf.phoff] is a [uint64].  The compiler
   therefore emits a 4-byte SIGNED load ([lw]) at the field's base, i.e.
   the machine reads only the LOW FOUR BYTES of the 8-byte field and
   sign-extends them.  A header whose [phoff] has its high word set, or
   whose bit 31 is set, is read as a DIFFERENT (possibly negative) value
   than the field holds.  That is the code's behaviour and this model says
   it: [eh_phoff] is the 4-byte little-endian reading at offset 32, NOT the
   8-byte field, and a consumer that needs the sign-extended register value
   applies the sign extension to THIS number.  [ph_off] (@8) has exactly
   the same story ([loadseg]'s [offset] parameter is a [uint], but the
   value handed to it comes out of an [lw]).  [eh_magic] is an [lw] too,
   but 0x464c457f has bit 31 clear, so its sign extension is the identity
   and the unsigned reading below is faithful.

   EVERY LAW IS STATED WITH LITERAL OFFSETS AND SIZES -- 0/4/8/16/24/32/40/
   56 and 2/4/8 -- never with a folded constant, for the reason
   [DinodeEnc.v] gives: a consumer's offsets arrive as LITERALS out of the
   instruction stream (the [-432]/[-488] displacements above, minus the
   base), and a [rewrite] against a folded constant does not match.

   The little-endian assembler is the tree's EXISTING
   [RiscvModelBytes.assemble_bytes] (the same one [read_bytes] and
   [nth_byte_assemble_len] are stated over); there is deliberately no
   second byte assembler here.

   iris-FREE (no proofmode, no ssreflect), like [BlockWords.v] /
   [DinodeEnc.v] / [DirentEnc.v], so it stays usable from the
   vanilla-[rewrite ... by ...] files. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
Require Import RiscvModelBytes.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The little-endian field reader over a buffer's naming function.         *)
(* ---------------------------------------------------------------------- *)

(* [le_at f o n] is the value of the [n]-byte little-endian field at byte
   offset [o] of the buffer named by [f].  Byte [o] is the least
   significant, which is what [assemble_bytes] means. *)
Definition le_at (f : nat -> bv 8) (o n : nat) : Z :=
  assemble_bytes (map (fun j => f (o + j)%nat) (seq 0 n)).

(* [map] (Stdlib) and [<$>] (stdpp) are the same function; the bridge is
   stated once so every proof below can use stdpp's [list_lookup_fmap] /
   [length_fmap] on [le_at]'s byte list. *)
Lemma map_eq_fmap {A B : Type} (g : A -> B) (l : list A) : map g l = g <$> l.
Proof. induction l as [|a l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma le_bytes_length (f : nat -> bv 8) (o n : nat) :
  length (map (fun j => f (o + j)%nat) (seq 0 n)) = n.
Proof. rewrite map_eq_fmap, length_fmap, length_seq. reflexivity. Qed.

Lemma le_bytes_lookup (f : nat -> bv 8) (o n j : nat) :
  (j < n)%nat ->
  map (fun k => f (o + k)%nat) (seq 0 n) !!! j = f (o + j)%nat.
Proof.
  intros Hj. apply list_lookup_total_correct.
  rewrite map_eq_fmap, list_lookup_fmap, lookup_seq_lt by exact Hj.
  reflexivity.
Qed.

(* the range of an [n]-byte field *)
Lemma le_at_bound (f : nat -> bv 8) (o n : nat) :
  0 <= le_at f o n < 2 ^ (8 * Z.of_nat n).
Proof.
  unfold le_at.
  pose proof (assemble_bytes_bound (map (fun j => f (o + j)%nat) (seq 0 n))) as H.
  rewrite le_bytes_length in H. exact H.
Qed.

(* ...in the form every consumer wants it: the bound as a LITERAL. *)
Lemma le_at_bound_lit (f : nat -> bv 8) (o n : nat) (b : Z) :
  2 ^ (8 * Z.of_nat n) = b -> 0 <= le_at f o n < b.
Proof. intros <-. apply le_at_bound. Qed.

(* THE CONGRUENCE a proof needs when the buffer's naming function is
   rewritten: only the [n] bytes at [o] matter. *)
Lemma le_at_ext (f g : nat -> bv 8) (o n : nat) :
  (forall j, (j < n)%nat -> f (o + j)%nat = g (o + j)%nat) ->
  le_at f o n = le_at g o n.
Proof.
  intros H. unfold le_at. f_equal.
  rewrite !map_eq_fmap. apply list_eq. intros j.
  destruct (Nat.lt_ge_cases j n) as [Hj|Hj].
  - rewrite !list_lookup_fmap, lookup_seq_lt by exact Hj.
    simpl. rewrite H by exact Hj. reflexivity.
  - rewrite !list_lookup_fmap.
    rewrite lookup_ge_None_2 by (rewrite length_seq; lia).
    reflexivity.
Qed.

(* THE LAW THE WP LOAD LEAVES NEED: the word a load delivers, split back
   into bytes, IS the buffer.  Stated at an arbitrary destination width
   [m] wide enough to hold the field, so the 32- and 64-bit instances are
   one application each. *)
Lemma le_at_nth_byte (m : N) (f : nat -> bv 8) (o n j : nat) :
  (8 * Z.of_nat n <= Z.of_N m) -> (j < n)%nat ->
  nth_byte (Z_to_bv m (le_at f o n) : bv m) j = f (o + j)%nat.
Proof.
  intros Hm Hj. unfold le_at.
  rewrite (nth_byte_assemble_len m _ j) by (rewrite le_bytes_length; lia).
  apply le_bytes_lookup, Hj.
Qed.

(* ...and at the field's own width, which is where a byte window is turned
   straight back into a word. *)
Lemma le_at_nth_byte_exact (f : nat -> bv 8) (o n j : nat) :
  (j < n)%nat ->
  nth_byte (Z_to_bv (8 * N.of_nat n) (le_at f o n) : bv (8 * N.of_nat n)) j
  = f (o + j)%nat.
Proof. intros Hj. apply le_at_nth_byte; [lia | exact Hj]. Qed.

(* ====================================================================== *)
(*  struct elfhdr -- 64 bytes; kexec reads exactly four fields.           *)
(* ====================================================================== *)

Definition eh_magic (f : nat -> bv 8) : Z := le_at f 0 4.
Definition eh_entry (f : nat -> bv 8) : Z := le_at f 24 8.

(* THE LOW WORD of the 8-byte [phoff] field -- see the header comment: the
   C assigns [elf.phoff] to an [int off], so the machine performs a 4-byte
   SIGNED load at offset 32 and never looks at bytes 36..39.  A consumer
   that needs the register value sign-extends THIS number. *)
Definition eh_phoff (f : nat -> bv 8) : Z := le_at f 32 4.

Definition eh_phnum (f : nat -> bv 8) : Z := le_at f 56 2.

(* the constant kexec's [lui 0x464c4 ; addi 1407] builds *)
Definition ELF_MAGIC : Z := 0x464C457F.

Definition eh_magic_ok (f : nat -> bv 8) : Prop := eh_magic f = ELF_MAGIC.

Lemma eh_magic_bound (f : nat -> bv 8) : 0 <= eh_magic f < 2 ^ 32.
Proof. unfold eh_magic. apply le_at_bound_lit. reflexivity. Qed.

Lemma eh_entry_bound (f : nat -> bv 8) : 0 <= eh_entry f < 2 ^ 64.
Proof. unfold eh_entry. apply le_at_bound_lit. reflexivity. Qed.

Lemma eh_phoff_bound (f : nat -> bv 8) : 0 <= eh_phoff f < 2 ^ 32.
Proof. unfold eh_phoff. apply le_at_bound_lit. reflexivity. Qed.

(* the loop bound [i < elf.phnum] is a zero-extended halfword *)
Lemma eh_phnum_bound (f : nat -> bv 8) : 0 <= eh_phnum f < 65536.
Proof. unfold eh_phnum. apply le_at_bound_lit. reflexivity. Qed.

(* ====================================================================== *)
(*  struct proghdr -- 56 bytes; kexec reads six of the eight fields.      *)
(*  ([paddr] @24 and [align] @48 are never read.)                         *)
(* ====================================================================== *)

Definition ph_type   (f : nat -> bv 8) : Z := le_at f 0 4.
Definition ph_flags  (f : nat -> bv 8) : Z := le_at f 4 4.

(* the LOW WORD of the 8-byte [off] field, for exactly the same reason as
   [eh_phoff]: the value reaches [loadseg] through an [lw]. *)
Definition ph_off    (f : nat -> bv 8) : Z := le_at f 8 4.

Definition ph_vaddr  (f : nat -> bv 8) : Z := le_at f 16 8.
Definition ph_filesz (f : nat -> bv 8) : Z := le_at f 32 8.
Definition ph_memsz  (f : nat -> bv 8) : Z := le_at f 40 8.

(* the constant kexec's [li a4,1 ; bne] tests [ph.type] against *)
Definition ELF_PROG_LOAD : Z := 1.

Lemma ph_type_bound (f : nat -> bv 8) : 0 <= ph_type f < 2 ^ 32.
Proof. unfold ph_type. apply le_at_bound_lit. reflexivity. Qed.

Lemma ph_flags_bound (f : nat -> bv 8) : 0 <= ph_flags f < 2 ^ 32.
Proof. unfold ph_flags. apply le_at_bound_lit. reflexivity. Qed.

Lemma ph_off_bound (f : nat -> bv 8) : 0 <= ph_off f < 2 ^ 32.
Proof. unfold ph_off. apply le_at_bound_lit. reflexivity. Qed.

Lemma ph_vaddr_bound (f : nat -> bv 8) : 0 <= ph_vaddr f < 2 ^ 64.
Proof. unfold ph_vaddr. apply le_at_bound_lit. reflexivity. Qed.

Lemma ph_filesz_bound (f : nat -> bv 8) : 0 <= ph_filesz f < 2 ^ 64.
Proof. unfold ph_filesz. apply le_at_bound_lit. reflexivity. Qed.

Lemma ph_memsz_bound (f : nat -> bv 8) : 0 <= ph_memsz f < 2 ^ 64.
Proof. unfold ph_memsz. apply le_at_bound_lit. reflexivity. Qed.

(* ====================================================================== *)
(*  Where the i-th program header sits in the file.                        *)
(* ====================================================================== *)

(* [off = elf.phoff] before the loop, [off += sizeof(ph)] on every
   iteration -- i.e. header [i] is read from file offset
   [elf.phoff + 56 * i].  The stride 56 is [li s11,56] at kexec+0xbc,
   which is also the [n] handed to [readi]. *)
Definition ph_at (f : nat -> bv 8) (i : nat) : Z := eh_phoff f + 56 * Z.of_nat i.

Lemma ph_at_0 (f : nat -> bv 8) : ph_at f 0 = eh_phoff f.
Proof. unfold ph_at. lia. Qed.

(* the loop's own step, in the shape the invariant advances by *)
Lemma ph_at_succ (f : nat -> bv 8) (i : nat) :
  ph_at f (S i) = ph_at f i + 56.
Proof. unfold ph_at. rewrite Nat2Z.inj_succ. lia. Qed.
