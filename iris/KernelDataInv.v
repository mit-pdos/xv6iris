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
From Kernel Require KernelData.
Local Open Scope Z_scope.
Import Defs.

Section KernelDataInv.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* The initialized global-data image, RE-SCOPED to the kernel-DATA region
     (rwx-kmap): the dump also carries 5332 sub-etext bytes (inter-function
     padding + the trampoline page's tail) that no proof consumes -- those
     are dropped here (adequacy exposes them as [↦ₓ□] with the rest of the
     sub-etext image).  Each remaining byte resides at its physical address
     as a DfracDiscarded (`↦ₘ□`) points-to -- hence persistent and
     duplicable, like [kernel_text]. *)
  Definition kernel_data : iProp Σ :=
    ([∗ map] a↦b ∈ base.filter (fun p : Z * bv 8 => text_end <= p.1)
                     KernelData.kernel_data,
       (mword_of_int a : Arch.pa) ↦ₘ□ b)%I.

  Global Instance kernel_data_persistent : Persistent kernel_data.
  Proof. apply _. Qed.

  (* Extract the four persistent bytes of a global word at address [A] from
     [kernel_data] (mirror of [kernel_window_pc]).  [w] is the little-endian
     word whose bytes the image holds at [A..A+W). *)
  Lemma kernel_data_window {wd : Z} (A : Z) (w : mword wd) (W : nat) (a : mword 64) :
    a = mword_of_int A ->
    text_end <= A ->
    (forall j, (j < W)%nat ->
       KernelData.kernel_data !! (A + Z.of_nat j)%Z = Some (nth_byte w j)) ->
    kernel_data -∗
    ([∗ list] j ∈ seq 0 W, (pa_add a j) ↦ₘ□ nth_byte w j).
  Proof.
    iIntros (-> HA Hbytes) "#Hd". iApply big_sepL_intro. iIntros "!>" (k j Hk).
    apply lookup_seq in Hk. destruct Hk as [-> Hlt]. simpl.
    rewrite pa_add_mword.
    iApply (big_sepM_lookup _ _ (A + Z.of_nat k)%Z (nth_byte w k) with "Hd").
    apply map_lookup_filter_Some_2; [apply Hbytes; exact Hlt | cbn; lia].
  Qed.

  (* Extract a NUL-terminated STRING literal from the image: the string
     points-to [↦ₛ□] whose bytes the image holds at [A .. A+|s|].  The
     read-only-globals analogue of [kernel_data_window] for the one kind of
     global whose length is not a machine word -- a C string constant (the
     names the kernel passes to [initlock], say).  Persistent, so the string
     never has to be threaded. *)
  Lemma kernel_data_string (A : Z) (s : string) (a : mword 64) :
    a = mword_of_int A ->
    text_end <= A ->
    (forall j b, cstring_bytes s !! j = Some b ->
       KernelData.kernel_data !! (A + Z.of_nat j)%Z = Some b) ->
    kernel_data -∗ a ↦ₛ□ s.
  Proof.
    iIntros (-> HA Hbytes) "#Hd". rewrite /string_pointsto.
    iApply big_sepL_intro. iIntros "!>" (j b Hj).
    rewrite pa_add_mword.
    iApply (big_sepM_lookup _ _ (A + Z.of_nat j)%Z b with "Hd").
    apply map_lookup_filter_Some_2; [by apply Hbytes | cbn; lia].
  Qed.

End KernelDataInv.
