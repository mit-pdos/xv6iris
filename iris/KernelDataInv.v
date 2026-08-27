(* KernelDataInv.v -- the kernel global-DATA image resource [kernel_data], the
   read-only analogue of [kernel_text] (KernelText.v).

   [kernel_text] resides the kernel's instruction bytes at their physical
   addresses as persistent code (`↦ₓ□`) points-to facts so that any fetch can
   extract a code window without borrow/return.  [kernel_data] does the same
   for the kernel's initialized global-data image (KernelData.kernel_data, the
   ELF `.data` section): a persistent per-byte resource from which a data load
   extracts a word window, exactly as fetch extracts a code window from
   [kernel_text].  It is the intended mechanism for reading read-only kernel
   globals in a whole-function WP (rather than threading raw `↦₄` hypotheses).

   Like [kernel_text] this is a build LEAF -- importing it gives the data image
   + the word-window lemma without any WP-stack dependency. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvPtsto.
Require Import KernelText.
From Kernel Require KernelData KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ====================================================================== *)
(* THE READ-ONLY WINDOW of the initialized-data image.                     *)
(*                                                                        *)
(* [kernel_data] below resides these bytes at [DfracDiscarded] -- i.e. it  *)
(* claims they are read-only FOREVER -- so its domain must contain no byte *)
(* the kernel ever stores to.  The dump's single PT_LOAD is RWX and says   *)
(* nothing about that; the ELF's SECTION flags do, and                     *)
(* [RiscvLang.rodata_end] is their reading (the lowest writable allocated  *)
(* section, here `.data`).  So the window is bounded ABOVE as well as      *)
(* below: [text_end, rodata_end), which is .rodata + .eh_frame.            *)
(*                                                                        *)
(* The upper bound is not optional.  xv6 STORES to `first` (forkret's      *)
(* `first = 0`) and to `nextpid` (allocpid's `nextpid = nextpid + 1`),     *)
(* and both are initialized `.data`, hence in the dumped image.  Resident  *)
(* at [DfracDiscarded] they would make [kernel_data] contradict any        *)
(* ownership of those cells -- and a contradictory premise does not fail   *)
(* to compile, it silently makes every contract carrying it VACUOUS.  The  *)
(* tier index does NOT save you: [mem_pointsto] bottoms out in a           *)
(* [pointsto] keyed on the PHYSICAL address, and a kernel global is        *)
(* identity-mapped, so the two points-tos really do collide.  §T below is  *)
(* the tripwire that fails loudly if this bound is ever widened back.      *)
(* ====================================================================== *)
Definition kdata_ro : gmap Z (bv 8) :=
  base.filter (fun p : Z * bv 8 => text_end <= p.1 < rodata_end)
    KernelData.kernel_data.

(* the one introduction rule: a dumped byte inside the window is in [kdata_ro].

   NOT [by apply map_lookup_filter_Some_2].  That leaves the side condition
   as the BETA-REDEX [(fun p => text_end <= p.1 < rodata_end) (a, b)], and
   stdpp's [done] on a two-conjunct redex over this 17932-entry map costs
   MINUTES (measured: 1.3 s here, >14 min with [by]) -- with no error, so it
   reads as a hung build.  Reduce it first and close it by hand; the same
   goes for every [map_lookup_filter_Some*] step over [kernel_data]. *)
Lemma kdata_ro_lookup (a : Z) (b : bv 8) :
  KernelData.kernel_data !! a = Some b -> text_end <= a -> a < rodata_end ->
  kdata_ro !! a = Some b.
Proof.
  intros Hlk Hlo Hhi.
  apply map_lookup_filter_Some_2; [exact Hlk | cbn; split; assumption].
Qed.

(* ...and its converse, which is §T's tripwire *)
Lemma kdata_ro_bounds (a : Z) (b : bv 8) :
  kdata_ro !! a = Some b -> text_end <= a < rodata_end.
Proof.
  intro H. apply map_lookup_filter_Some in H.
  destruct H as [_ H]. cbn in H. exact H.
Qed.

Section KernelDataInv.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* The initialized global-data image, RE-SCOPED to the READ-ONLY kernel-data
     window [kdata_ro]: the dump also carries 5332 sub-etext bytes
     (inter-function padding + the trampoline page's tail) that no proof
     consumes -- those are dropped by the lower bound (adequacy exposes them
     as [↦ₓ□] with the rest of the sub-etext image) -- and the writable
     `.data`/`.got` tail, which the UPPER bound drops (see the header).  Each
     remaining byte resides at its physical address as a DfracDiscarded
     (`↦ₘ□`) points-to -- hence persistent and duplicable, like
     [kernel_text]. *)
  Definition kernel_data : iProp Σ :=
    ([∗ map] a↦b ∈ kdata_ro, (mword_of_int a : Arch.pa) ↦ₘ□ b)%I.

  Global Instance kernel_data_persistent : Persistent kernel_data.
  Proof. apply _. Qed.

  (* THE ONE EXTRACTION RULE: the [W] persistent bytes the image holds at
     [A .. A+W), as an arbitrary byte FUNCTION.  Every caller is an instance
     -- a machine word ([kernel_data_window] below), a NUL-terminated string
     ([kernel_data_string]), or a fixed-length name literal that is NOT
     NUL-terminated inside its window (`.`/`..` in create/sys_unlink), which
     is why the general [f] and not [nth_byte] is the primitive.  Mirror of
     [kernel_window_pc]. *)
  Lemma kernel_data_bytes (A : Z) (W : nat) (f : nat -> bv 8) (a : mword 64) :
    a = mword_of_int A ->
    text_end <= A ->
    A + Z.of_nat W <= rodata_end ->
    (forall j, (j < W)%nat ->
       KernelData.kernel_data !! (A + Z.of_nat j)%Z = Some (f j)) ->
    kernel_data -∗ ([∗ list] j ∈ seq 0 W, (pa_add a j) ↦ₘ□ f j).
  Proof.
    iIntros (-> HA HR Hbytes) "#Hd". iApply big_sepL_intro. iIntros "!>" (k j Hk).
    apply lookup_seq in Hk. destruct Hk as [-> Hlt]. simpl.
    rewrite pa_add_mword.
    iApply (big_sepM_lookup _ _ (A + Z.of_nat k)%Z (f k) with "Hd").
    apply kdata_ro_lookup; [apply Hbytes; exact Hlt | lia | lia].
  Qed.

  (* Extract the bytes of a global WORD at address [A] from [kernel_data].
     [w] is the little-endian word whose bytes the image holds at [A..A+W). *)
  Lemma kernel_data_window {wd : Z} (A : Z) (w : mword wd) (W : nat) (a : mword 64) :
    a = mword_of_int A ->
    text_end <= A ->
    A + Z.of_nat W <= rodata_end ->
    (forall j, (j < W)%nat ->
       KernelData.kernel_data !! (A + Z.of_nat j)%Z = Some (nth_byte w j)) ->
    kernel_data -∗
    ([∗ list] j ∈ seq 0 W, (pa_add a j) ↦ₘ□ nth_byte w j).
  Proof. exact (kernel_data_bytes A W (nth_byte w) a). Qed.

  (* Extract a NUL-terminated STRING literal from the image: the string
     points-to [↦ₛ□] whose bytes the image holds at [A .. A+|s|].  The
     read-only-globals analogue of [kernel_data_window] for the one kind of
     global whose length is not a machine word -- a C string constant (the
     names the kernel passes to [initlock], say).  Persistent, so the string
     never has to be threaded. *)
  Lemma kernel_data_string (A : Z) (s : string) (a : mword 64) :
    a = mword_of_int A ->
    text_end <= A ->
    A + Z.of_nat (S (String.length s)) <= rodata_end ->
    (forall j b, cstring_bytes s !! j = Some b ->
       KernelData.kernel_data !! (A + Z.of_nat j)%Z = Some b) ->
    kernel_data -∗ a ↦ₛ□ s.
  Proof.
    iIntros (-> HA HR Hbytes) "#Hd". rewrite /string_pointsto.
    iApply big_sepL_intro. iIntros "!>" (j b Hj).
    rewrite pa_add_mword.
    (* the index is inside the NUL-terminated byte list, so [A + j] is inside
       the window the caller's [HR] bounds *)
    assert (Hjlt : (j < S (String.length s))%nat)
      by (rewrite <- cstring_bytes_length; eapply lookup_lt_Some, Hj).
    iApply (big_sepM_lookup _ _ (A + Z.of_nat j)%Z b with "Hd").
    apply kdata_ro_lookup; [by apply Hbytes | lia | lia].
  Qed.

  (* ================================================================== *)
  (* §T  THE TRIPWIRE.                                                   *)
  (*                                                                    *)
  (* What must never regress is the UPPER bound: [kernel_data]'s domain  *)
  (* stops below the first writable byte of the image.  Stated           *)
  (* positively (as a domain fact rather than as a refutation, because   *)
  (* the whole point of this file's fix is that owning a writable cell   *)
  (* alongside [kernel_data] must now be SATISFIABLE), plus the two      *)
  (* [vm_compute]d instances that pin it to the image: the globals xv6   *)
  (* demonstrably stores to.  Widen the filter, or move the image so     *)
  (* that a written global falls below [rodata_end], and these fail.     *)
  (* ================================================================== *)

  (* nothing at or above the boundary is resident in [kernel_data] *)
  Lemma kdata_ro_writable_none (a : Z) : rodata_end <= a -> kdata_ro !! a = None.
  Proof.
    intro Ha. destruct (kdata_ro !! a) as [b|] eqn:E; [| reflexivity].
    exfalso. apply kdata_ro_bounds in E. lia.
  Qed.

  (* `first` -- forkret's `first = 0` stores to it *)
  Lemma kdata_ro_first : kdata_ro !! KernelSyms.first_1 = None.
  Proof. apply kdata_ro_writable_none. vm_compute. discriminate. Qed.

  (* `nextpid` -- allocpid's `nextpid = nextpid + 1` stores to it *)
  Lemma kdata_ro_nextpid : kdata_ro !! KernelSyms.nextpid = None.
  Proof. apply kdata_ro_writable_none. vm_compute. discriminate. Qed.

End KernelDataInv.

(* A BIG-OP UNDER A TRANSPARENT NAME IS AN [iFrame] BOMB (optimization.md):
   a [∗ map] over the WHOLE kernel .rodata; named in 172 files.
   AT THE END OF THE FILE, so this file's own lemmas -- the accessors every
   consumer should be using -- can still take it apart. *)
Global Typeclasses Opaque kernel_data.
