(* PipeInv.v -- [struct pipe] (kernel/pipe.c): its geometry, the two-ended
   reference algebra, the resource [pi->lock] protects, and the well-formedness
   predicate [is_pipe].

     #define PIPESIZE 512
     struct pipe { struct spinlock lock; char data[PIPESIZE];
                   uint nread; uint nwrite; int readopen; int writeopen; };

   A pipe is one kalloc'd page holding a single self-contained object, so --
   unlike the ftable, whose slots live in a global array under one global lock
   -- EVERYTHING about it is protected by its OWN lock, and there is no
   lock-free immutable part at all: no field of a [struct pipe] is ever read
   without holding [pi->lock].  So the predicate is exactly what the shape of
   the C code says it should be:

     is_pipe γl γp pi  :=  ⌜page_valid pi⌝ ∗ is_lock γl pi "pipe" (pipe_res γp pi)

   persistent, and [pipe_res] owns every remaining byte of the page.

   ---- the reference count ----

   xv6 does not give a pipe an int refcount; it gives it TWO int flags,
   [readopen] and [writeopen], one per end, and pipeclose(pi, writable) clears
   the one its argument selects and frees the page when both have reached 0.
   The count of outstanding references IS [readopen + writeopen], so the ghost
   mirrors the ends rather than a single number: per end, a FRACTION ghost

     pipe_ref γp w q   -- q of the [w] end of pi ([w] = the struct file's
                          [writable] flag, i.e. pipeclose's second argument)

   with the invariant holding, per end, either "the flag is nonzero" or "the
   flag is zero AND the whole fraction has come home".  Three things fall out,
   and they are the whole reason for the shape:

   * a holder of ANY positive fraction of an end proves that end's flag is
     nonzero -- otherwise the invariant would hold fraction 1 of it as well;
   * only a holder of the FULL fraction of an end can close it, so an end
     cannot be closed twice, and a file that was [dup]ed cannot close the pipe
     out from under its twin;
   * the closer of the second end recovers fraction 1 of BOTH ends, which is
     the licence to reclaim the page.

   A single counter would not do any of this: it could not tell pipeclose(pi,1)
   twice apart from one close of each end.

   ---- the page, and reclaiming it ----

   [pipe_res] holds the data buffer, the four counter/flag words, AND every
   byte of the page that [struct pipe] does not name (the 4 padding bytes
   inside [struct spinlock], and everything past its 552-byte extent) -- see
   [pipe_slack].  Nothing ever reads those; they are held only so that the
   page can be handed back to kfree, which memsets all 4096 bytes.

   NOTE (blocks pipeclose, not pipealloc): with [is_lock] built on a plain
   Iris [inv], the page can never actually be reclaimed -- the invariant is
   permanent, so [pipe_res] can never be taken back out, and worse,
   [lock_name] DISCARDS the 8-byte name field forever.  Freeing a pipe will
   therefore need (a) a cancellable form of [is_lock] (WpLock over [cinv],
   with a fractional cancel token that the two end references carry), and
   (b) a name field that is reclaimable rather than [↦₈□].  pipealloc needs
   none of this -- gcc proved its [kfree(pi)] arm dead (pi is 0 on every path
   reaching [bad]) -- so the decision belongs with pipeclose.

   Design: claude-notes/design/pipe.md. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
From iris.algebra Require Import frac.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants own.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
Require Import KallocInv.
Require Import WpLock.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(*  Geometry                                                           *)
(* ------------------------------------------------------------------ *)

Definition PIPESIZE : nat := 512.
Definition pipe_data_off : nat := 24.       (* sizeof(struct spinlock) *)
Definition pipe_sizeof : nat := 552.        (* 24 + 512 + 4*4 *)
Definition pipe_pgbytes : nat := 4096.

(* the field addresses, in the EXACT [add_vec base (sign_extend' 64 imm)] form
   the sw/lw instructions compute (all four offsets fit the 12-bit immediate),
   so a load/store address unifies with the cell without rewriting. *)
Definition poff_of (a : mword 64) (i : Z) : mword 64 :=
  add_vec a (sign_extend' 64 (mword_of_int i : mword 12)).

Definition a_pnread  (pi : mword 64) : mword 64 := poff_of pi 536.
Definition a_pnwrite (pi : mword 64) : mword 64 := poff_of pi 540.

(* the open flag of ONE end, selected by the [writable] bit -- the same bool
   that indexes [pipe_ref] and that pipeclose receives as its argument.  One
   indexed field, not two, so every law below is stated once. *)
Definition a_popen (pi : mword 64) (w : bool) : mword 64 :=
  poff_of pi (if w then 548 else 544).      (* writeopen / readopen *)

(* the lock is the FIRST member, so &pi->lock = pi -- which is exactly the a0
   pipealloc passes to initlock. *)

(* the two flag values, in the form the c.beqz / c.bnez tests consume. *)
Definition pflag_open (v : mword 32) : Prop :=
  neq_vec (sign_extend' 64 v) zero_reg = true.

Lemma pflag_one_open : pflag_open (mword_of_int 1 : mword 32).
Proof. reflexivity. Qed.

Lemma pflag_zero_not_open : ~ pflag_open (mword_of_int 0 : mword 32).
Proof. unfold pflag_open. cbn. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(*  The reference algebra: one fraction ghost per end                   *)
(* ------------------------------------------------------------------ *)

Class pipeG (Σ : gFunctors) := PipeG { pipe_inG :: inG Σ fracR }.
Definition pipeΣ : gFunctors := #[GFunctor fracR].
Global Instance subG_pipeΣ {Σ} : subG pipeΣ Σ -> pipeG Σ.
Proof. solve_inG. Qed.

(* a pipe's ghost identity: one gname per end. *)
Record pipe_names := MkPipeNames { pn_read : gname; pn_write : gname }.

Definition pn_end (γp : pipe_names) (w : bool) : gname :=
  if w then pn_write γp else pn_read γp.

Section PipeInv.
  Context `{!riscvGS Σ, !lockG Σ, !pipeG Σ}.

  (* ---- THE reference: a share of one END of the pipe ----

     Held by whoever holds the [struct file] for that end (FileInv's
     [file_payload]); split by filedup along with the file's own content
     fraction, and recombined by the last fileclose, which then hands the full
     [pipe_ref γp w 1] to pipeclose.  q = 1 is "I am the only holder of this
     end", which is precisely the right to close it. *)
  Definition pipe_ref (γp : pipe_names) (w : bool) (q : Qp) : iProp Σ :=
    own (pn_end γp w) q.

  Global Instance pipe_ref_timeless γp w q : Timeless (pipe_ref γp w q).
  Proof. apply _. Qed.
  Global Instance pipe_ref_fractional γp w :
    Fractional (fun q => pipe_ref γp w q).
  Proof. intros q1 q2. by rewrite /pipe_ref -own_op frac_op. Qed.

  Lemma pipe_ref_split γp w q1 q2 :
    pipe_ref γp w (q1 + q2) ⊣⊢ pipe_ref γp w q1 ∗ pipe_ref γp w q2.
  Proof. by rewrite /pipe_ref -own_op frac_op. Qed.

  Lemma pipe_ref_valid γp w q : pipe_ref γp w q -∗ ⌜(q ≤ 1)%Qp⌝.
  Proof. iIntros "H". by iDestruct (own_valid with "H") as %?%frac_valid. Qed.

  (* the whole point of the [q = 1] state: nobody else holds any of this end. *)
  Lemma pipe_ref_full_excl γp w q :
    pipe_ref γp w 1 -∗ pipe_ref γp w q -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite frac_op in Hv. apply frac_valid in Hv.
    iPureIntro. exact (Qp.not_add_le_l 1 q Hv).
  Qed.

  (* ---- the per-end coupling between the flag and the ghost ---- *)

  Definition pipe_endstate (γp : pipe_names) (w : bool) (v : mword 32) : iProp Σ :=
    (⌜pflag_open v⌝                                   (* the end is still open *)
     ∨ ⌜v = (mword_of_int 0 : mword 32)⌝ ∗ pipe_ref γp w 1)%I.
                                            (* closed: the reference came home *)

  Global Instance pipe_endstate_timeless γp w v : Timeless (pipe_endstate γp w v).
  Proof. apply _. Qed.

  Lemma pipe_endstate_open_intro γp w v :
    pflag_open v -> ⊢ pipe_endstate γp w v.
  Proof. iIntros (H). by iLeft. Qed.

  (* holding ANY share of an end proves its flag is nonzero.  The conclusion is
     pure, so [iDestruct ... as %H] keeps both inputs. *)
  Lemma pipe_endstate_holder γp w v q :
    pipe_endstate γp w v -∗ pipe_ref γp w q -∗ ⌜pflag_open v⌝.
  Proof.
    iIntros "Hst Hq".
    iDestruct "Hst" as "[%Hop|[-> Hfull]]"; [done|].
    iExFalso. iApply (pipe_ref_full_excl with "Hfull Hq").
  Qed.

  (* pipeclose's own end, after its [pi->{read,write}open = 0] store. *)
  Lemma pipe_endstate_close γp w :
    pipe_ref γp w 1 -∗ pipe_endstate γp w (mword_of_int 0 : mword 32).
  Proof. iIntros "H". iRight. by iFrame "H". Qed.

  (* pipeclose reading the OTHER end's flag as 0: the whole of that end comes
     out of the invariant, so the closer ends up owning both ends outright --
     the licence to reclaim the page. *)
  Lemma pipe_endstate_closed γp w :
    pipe_endstate γp w (mword_of_int 0 : mword 32) -∗ pipe_ref γp w 1.
  Proof.
    iIntros "[%Hop|[_ $]]".
    exfalso. exact (pflag_zero_not_open Hop).
  Qed.

  (* ---- the page bytes ---- *)

  (* pi->data[0..PIPESIZE), contents tracked: piperead/pipewrite will need to
     say WHICH bytes are in the pipe, and the byte window is the only place
     that can be said.  (The queue coupling -- the live bytes being those at
     indices [nread, nwrite) mod PIPESIZE -- is not imposed here; it belongs
     with the read/write specs, and lands as an extra conjunct of
     [pipe_res].) *)
  Definition pipe_data (pi : mword 64) (bs : list (bv 8)) : iProp Σ :=
    ([∗ list] j ↦ b ∈ bs, pa_add pi (pipe_data_off + j) ↦ₘ b)%I.

  (* the bytes of the page that [struct pipe] does not name: the 4 padding
     bytes between [lock.locked] and [lock.name], and everything past
     sizeof(struct pipe).  No code touches them; they are held so that the
     page can go back to kfree, which memsets the lot. *)
  Definition pipe_slack (pi : mword 64) : iProp Σ :=
    (([∗ list] j ∈ seq 4 4, byte_any (pa_add pi j)) ∗
     ([∗ list] j ∈ seq pipe_sizeof (pipe_pgbytes - pipe_sizeof),
        byte_any (pa_add pi j)))%I.

  Typeclasses Opaque pipe_data pipe_slack.

  (* ---- the resource pi->lock protects: EVERY field but the lock itself ---- *)
  Definition pipe_res (γp : pipe_names) (pi : mword 64) : iProp Σ :=
    (∃ (nr nw ro wo : mword 32) (bs : list (bv 8)),
       a_pnread pi      ↦₄ nr ∗
       a_pnwrite pi     ↦₄ nw ∗
       a_popen pi false ↦₄ ro ∗
       a_popen pi true  ↦₄ wo ∗
       pipe_endstate γp false ro ∗
       pipe_endstate γp true wo ∗
       ⌜length bs = PIPESIZE⌝ ∗ pipe_data pi bs ∗
       pipe_slack pi)%I.

  (* ---- THE predicate: a well-formed [struct pipe] ----

     Persistent, so every holder of either end shares it.  [page_valid] is
     kalloc's guarantee travelling with the object: it is what makes the page
     re-freeable, so it has to survive to pipeclose. *)
  Definition is_pipe (γl : gname) (γp : pipe_names) (pi : mword 64) : iProp Σ :=
    (⌜page_valid pi⌝ ∗ is_lock γl pi "pipe"%string (pipe_res γp pi))%I.

  Global Instance is_pipe_persistent γl γp pi : Persistent (is_pipe γl γp pi).
  Proof. apply _. Qed.

  Lemma is_pipe_valid γl γp pi : is_pipe γl γp pi -∗ ⌜page_valid pi⌝.
  Proof. by iIntros "[$ _]". Qed.
  Lemma is_pipe_lock γl γp pi :
    is_pipe γl γp pi -∗ is_lock γl pi "pipe"%string (pipe_res γp pi).
  Proof. by iIntros "[_ $]". Qed.

  (* ---- what a [struct file] of type FD_PIPE carries ----

     FileInv's [file_payload]: the pipe itself (persistent) plus the share of
     the end that the file's [writable] flag selects.  Keyed by the pipe's
     ADDRESS, since that is all [fcontent] records.

     CAVEAT for fileclose: two [pipe_held] shares of the same address cannot be
     recombined without knowing they name the same [γp].  Every share of one
     ftable slot's payload descends from a single split, so this never bites
     within a slot; if it ever does (a fraction parked in [file_rest] and
     recombined across holders), the fix is to pin the identity -- either an
     [agree] component on the ftable authority's per-slot entry, or a global
     address-keyed pipe registry. *)
  Definition pipe_held (pi : mword 64) (w : bool) (q : Qp) : iProp Σ :=
    (∃ (γl : gname) (γp : pipe_names), is_pipe γl γp pi ∗ pipe_ref γp w q)%I.

  (* ------------------------------------------------------------------ *)
  (*  Construction: pipealloc's ghost step                               *)
  (* ------------------------------------------------------------------ *)

  Lemma pipe_names_alloc :
    ⊢ |==> ∃ γp : pipe_names, pipe_ref γp false 1 ∗ pipe_ref γp true 1.
  Proof.
    iMod (own_alloc (1%Qp : fracR)) as (γr) "Hr"; [done|].
    iMod (own_alloc (1%Qp : fracR)) as (γw) "Hw"; [done|].
    iModIntro. iExists (MkPipeNames γr γw). by iFrame "Hr Hw".
  Qed.

  (* The state pipealloc has in hand once initlock returns: the four fields it
     wrote (readopen = writeopen = 1, nread = nwrite = 0), the lock's two words
     zeroed and its name sealed, the untouched data buffer, and the rest of the
     page.  Out come the pipe and its two ends, one for each of the two files.

     Note the data buffer is NOT zeroed by pipealloc -- [bs] is whatever kalloc
     handed over -- which is exactly right: no byte of it is readable until
     nwrite has passed it. *)
  Lemma new_pipe E (pi : mword 64) (bs : list (bv 8)) :
    page_valid pi ->
    length bs = PIPESIZE ->
    lock_name pi "pipe"%string -∗
    pi ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_cpu pi ↦₈ (zero_reg : mword 64) -∗
    a_pnread pi ↦₄ (mword_of_int 0 : mword 32) -∗
    a_pnwrite pi ↦₄ (mword_of_int 0 : mword 32) -∗
    a_popen pi false ↦₄ (mword_of_int 1 : mword 32) -∗
    a_popen pi true ↦₄ (mword_of_int 1 : mword 32) -∗
    pipe_data pi bs -∗
    pipe_slack pi
    ={E}=∗ ∃ (γl : gname) (γp : pipe_names),
             is_pipe γl γp pi ∗ pipe_ref γp false 1 ∗ pipe_ref γp true 1.
  Proof.
    iIntros (Hpv Hlen) "#Hnm Hword Hcpu Hnr Hnw Hro Hwo Hdata Hslack".
    iMod pipe_names_alloc as (γp) "[Hrd Hwr]".
    iMod (newlock E pi "pipe"%string (pipe_res γp pi)
            with "Hnm Hword Hcpu [Hnr Hnw Hro Hwo Hdata Hslack]") as (γl) "#Hlk".
    { iExists (mword_of_int 0 : mword 32), (mword_of_int 0 : mword 32),
              (mword_of_int 1 : mword 32), (mword_of_int 1 : mword 32), bs.
      iFrame "Hnr Hnw Hro Hwo Hdata Hslack".
      iSplitR; [by iApply pipe_endstate_open_intro; apply pflag_one_open|].
      iSplitR; [by iApply pipe_endstate_open_intro; apply pflag_one_open|].
      done. }
    iModIntro. iExists γl, γp. iFrame "Hrd Hwr". by iSplit.
  Qed.

End PipeInv.
