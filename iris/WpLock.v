(* WpLock.v -- the standard CSL/Iris spin-lock invariant for xv6's
   [struct spinlock], mirroring iris_heap_lang/lib/spin_lock.v but over the
   PHYSICAL fields of the Sail RISC-V machine: the 4-byte lock word
   ([lk->locked] @ +0) AND the 8-byte owner word ([lk->cpu] @ +16).

     lock_inv      -- ∃ v st, lock word ↦ v ∗ lk->cpu ↦ (cpu of st) ∗ ghost st
                        ∗ (st free ∗ v = 0 ∗ frag ∗ R  ∨  st held ∗ v ≠ 0)
     is_lock       -- lock_name ∗ inv lockN lock_inv   (persistent)
     locked γ i    -- the lock-HOLDER token: hart [i] holds the lock and
                      [lk->cpu] holds [cpus_ptr i] = &cpus[i]

   BOTH physical fields belong to the invariant: no proof threads either of
   them, and there is no per-caller [lk->cpu] cell to pass around (the shape
   that made the cpu word look like private state -- unsound as soon as two
   harts race for the same lock).  What a holder carries instead is
   [locked γ i], and that token PINS [lk->cpu = cpus_ptr i]: the state ghost
   mirrors the field and the holder's fragment agrees with the invariant's
   authority.  So [holding()] provably returns 1 for the holder, which is all
   [release] needs.  A NON-holder learns nothing about the field -- so
   holding() may answer either way for it, and acquire's
   [if(holding(lk)) panic] arm is discharged by panic's contract rather than
   shown dead (SpecAcquire.v).

   [lock_state] mirrors both fields as one value, including the one-store
   window inside acquire (word already taken, [lk->cpu] not yet written):

     None            -- free:               word = 0, lk->cpu = 0
     Some (i, false) -- held by i, lk->cpu = 0 (acquire's window; release's
                        window between its cpu clear and its word clear)
     Some (i, true)  -- held by i, lk->cpu = cpus_ptr i                     *)
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl gmap.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import invariants own.
Require Import SailStdpp.Base SailStdpp.Operators_mwords.
Require Import Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Import WpMycpu ProcGeom.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* The lock's ghost state.                                               *)
(*                                                                       *)
(* An excl_auth over [lock_state]: the invariant keeps the authority, the *)
(* holder keeps the fragment -- so the holder's token pins the [cpu]      *)
(* field, and the fragment cannot be forged.                              *)
(* ===================================================================== *)
Definition lock_state : Type := option (CPU * bool).

Definition lockUR : ucmra := excl_authUR (leibnizO lock_state).

Class lockG (Σ : gFunctors) := LockG { lock_inG :: inG Σ lockUR }.
Definition lockΣ : gFunctors := #[GFunctor lockUR].
Global Instance subG_lockΣ {Σ} : subG lockΣ Σ -> lockG Σ.
Proof. solve_inG. Qed.

Section Lock.
  Context `{!riscvGS Σ, !lockG Σ}.

  (* sibling of [minstretN]; the two are disjoint by construction, so a leaf
     can open [is_lock] INSIDE the step engine's [⊤ ∖ ↑minstretN] callback. *)
  Definition lockN : namespace := nroot .@ "xv6spinlock".

  (* ---- the ghost pieces ---------------------------------------------- *)

  (* the authority on the lock's state; lives in the invariant. *)
  Definition lock_auth (γ : gname) (st : lock_state) : iProp Σ :=
    own γ ((●E (st : leibnizO lock_state)) : lockUR).
  (* the state fragment; the free one lives in the invariant, a held one is
     the holder's token (see [locked] / [locked_pre]). *)
  Definition lock_frag (γ : gname) (st : lock_state) : iProp Σ :=
    own γ ((◯E (st : leibnizO lock_state)) : lockUR).

  (* THE holder token: hart [i] holds the lock and [lk->cpu = cpus_ptr i]. *)
  Definition locked (γ : gname) (i : CPU) : iProp Σ :=
    lock_frag γ (Some (i, true)).
  (* the same, in the window where [lk->cpu] is still 0 (internal to the
     acquire / release proofs; no caller ever sees it). *)
  Definition locked_pre (γ : gname) (i : CPU) : iProp Σ :=
    lock_frag γ (Some (i, false)).

  (* the value [lk->cpu] holds in each state: the OWNER word. *)
  Definition lk_cpu_val (st : lock_state) : mword 64 :=
    match st with
    | Some (i, true) => cpus_ptr i
    | _ => (zero_reg : mword 64)
    end.

  Lemma lk_cpu_val_none : lk_cpu_val None = (zero_reg : mword 64).
  Proof. reflexivity. Qed.
  Lemma lk_cpu_val_win (i : CPU) : lk_cpu_val (Some (i, false)) = (zero_reg : mword 64).
  Proof. reflexivity. Qed.
  Lemma lk_cpu_val_held (i : CPU) : lk_cpu_val (Some (i, true)) = cpus_ptr i.
  Proof. reflexivity. Qed.


  Global Instance lock_auth_timeless γ st : Timeless (lock_auth γ st).
  Proof. apply _. Qed.
  Global Instance lock_frag_timeless γ st : Timeless (lock_frag γ st).
  Proof. apply _. Qed.

  (* ---- the ghost laws ------------------------------------------------ *)

  (* the fragment agrees with the authority: this is what pins [lk->cpu]. *)
  Lemma lock_frag_agree γ st st' :
    lock_auth γ st -∗ lock_frag γ st' -∗ ⌜st = st'⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    iPureIntro. exact (excl_auth_agree_L _ _ Hv).
  Qed.


  (* the state fragment is exclusive: two of them cannot coexist, whatever
     states they claim -- so two holder tokens are impossible. *)
  Lemma lock_frag_exclusive γ st st' :
    lock_frag γ st -∗ lock_frag γ st' -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    destruct (proj1 (excl_auth_frag_op_valid _ _) Hv).
  Qed.

  Lemma locked_exclusive γ i j : locked γ i -∗ locked γ j -∗ False.
  Proof. apply lock_frag_exclusive. Qed.

  (* A bare exclusive token out of the same RA, for a client that needs an
     abstract "held" marker with no hart identity in it: the SLEEPlock's
     holder token (SleepLock.v).  A sleeplock is held by a PROCESS, not by a
     hart, and its gname carries nothing else -- no [lock_inv], no tickets. *)
  Definition lock_tok_excl (γ : gname) : iProp Σ := lock_frag γ None.

  Lemma lock_tok_excl_exclusive γ :
    lock_tok_excl γ -∗ lock_tok_excl γ -∗ False.
  Proof. apply lock_frag_exclusive. Qed.

  Global Instance lock_tok_excl_timeless γ : Timeless (lock_tok_excl γ).
  Proof. apply _. Qed.

  Lemma lock_tok_excl_alloc : ⊢ |==> ∃ γ : gname, lock_tok_excl γ.
  Proof.
    iMod (own_alloc ((◯E (None : leibnizO lock_state)) : lockUR)) as (γ) "H".
    { apply auth_frag_valid. done. }
    iModIntro. iExists γ. iExact "H".
  Qed.

  (* THE holder law: the token pins the owner word to your own [struct cpu]. *)
  Lemma locked_state γ st i :
    lock_auth γ st -∗ locked γ i -∗ ⌜st = Some (i, true)⌝.
  Proof. apply lock_frag_agree. Qed.

  Lemma locked_cpu_eq γ st i :
    lock_auth γ st -∗ locked γ i -∗ ⌜lk_cpu_val st = cpus_ptr i⌝.
  Proof.
    iIntros "Hg Ht".
    iDestruct (locked_state with "Hg Ht") as %->. done.
  Qed.

  Lemma locked_pre_state γ st i :
    lock_auth γ st -∗ locked_pre γ i -∗ ⌜st = Some (i, false)⌝.
  Proof. apply lock_frag_agree. Qed.

  (* ---- the four state transitions (one per lock instruction) --------- *)

  Local Lemma lock_state_update γ st st' :
    lock_auth γ st -∗ lock_frag γ st ==∗ lock_auth γ st' ∗ lock_frag γ st'.
  Proof.
    iIntros "Ha Hf".
    rewrite -own_op.
    iApply (own_update_2 with "Ha Hf").
    apply excl_auth_update.
  Qed.

  (* acquire's amoswap: a free lock becomes "held by i, cpu not yet
     written". *)
  Lemma lock_take γ i :
    lock_auth γ None -∗ lock_frag γ None ==∗
    lock_auth γ (Some (i, false)) ∗ locked_pre γ i.
  Proof. apply lock_state_update. Qed.

  (* acquire's [lk->cpu = mycpu()]: the window closes, the holder gets THE
     token. *)
  Lemma lock_setcpu γ st i :
    lock_auth γ st -∗ locked_pre γ i ==∗
    ⌜st = Some (i, false)⌝ ∗ lock_auth γ (Some (i, true)) ∗ locked γ i.
  Proof.
    iIntros "Ha Hf".
    iDestruct (locked_pre_state with "Ha Hf") as %->.
    iMod (lock_state_update γ (Some (i, false)) (Some (i, true)) with "Ha Hf") as "[Ha Hf]".
    iModIntro. iSplitR; [done|]. iFrame "Ha Hf".
  Qed.

  (* release's [lk->cpu = 0]: back into the window. *)
  Lemma lock_clrcpu γ st i :
    lock_auth γ st -∗ locked γ i ==∗
    ⌜st = Some (i, true)⌝ ∗ lock_auth γ (Some (i, false)) ∗ locked_pre γ i.
  Proof.
    iIntros "Ha Hf".
    iDestruct (locked_state with "Ha Hf") as %->.
    iMod (lock_state_update γ (Some (i, true)) (Some (i, false)) with "Ha Hf") as "[Ha Hf]".
    iModIntro. iSplitR; [done|]. iFrame "Ha Hf".
  Qed.

  (* release's word clear: the lock goes free again. *)
  Lemma lock_give γ st i :
    lock_auth γ st -∗ locked_pre γ i ==∗
    ⌜st = Some (i, false)⌝ ∗ lock_auth γ None ∗ lock_frag γ None.
  Proof.
    iIntros "Ha Hf".
    iDestruct (locked_pre_state with "Ha Hf") as %->.
    iMod (lock_state_update γ (Some (i, false)) None with "Ha Hf") as "[Ha Hf]".
    iModIntro. iSplitR; [done|]. iFrame "Ha Hf".
  Qed.

  (* ---- the physical fields ------------------------------------------- *)

  (* the physical 4-byte little-endian lock word at address [lk]: the 4-byte
     word points-to [↦₄] (which also bundles the 4-byte alignment of [lk]). *)
  Definition lock_word (lk : mword 64) (v : mword 32) : iProp Σ :=
    (lk ↦₄ v)%I.

  (* [lk->cpu]: the 8-byte owner word at +16, in the address form the
     acquire / release / holding leaves see it ([add_vec lk (sext 16)]). *)
  Definition lock_cpu (lk : mword 64) : mword 64 :=
    add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)).

  Definition lock_inv (γ : gname) (lk : mword 64) (R : iProp Σ) : iProp Σ :=
    (∃ (v : mword 32) (st : lock_state),
       lock_word lk v ∗
       lock_cpu lk ↦₈ lk_cpu_val st ∗
       lock_auth γ st ∗
       (⌜st = None⌝ ∗ ⌜v = (mword_of_int 0 : mword 32)⌝ ∗ lock_frag γ None ∗ R
        ∨ ⌜st ≠ None⌝ ∗ ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝))%I.

  (* the lock's NAME: [lk->name] (the 8-byte pointer field at +8) holds the
     address of a NUL-terminated string [s].  initlock writes the field once
     and nothing ever writes it again, so both the field and the string it
     points at are held at [DfracDiscarded] -- [lock_name] is PERSISTENT, and
     therefore rides along inside the (persistent) lock predicate at no
     ownership cost: no proof has to thread the name field, and every holder
     of the lock knows which lock it is by name. *)
  Definition lock_name_field (lk : mword 64) : mword 64 :=
    add_vec lk (sign_extend' 64 (mword_of_int 8 : mword 12)).

  Definition lock_name (lk : mword 64) (s : string) : iProp Σ :=
    (∃ p : mword 64, lock_name_field lk ↦₈□ p ∗ p ↦ₛ□ s)%I.

  Global Instance lock_name_persistent lk s : Persistent (lock_name lk s).
  Proof. apply _. Qed.

  (* a lock is its (immutable) name plus the invariant over its two words. *)
  Definition is_lock (γ : gname) (lk : mword 64) (s : string) (R : iProp Σ) : iProp Σ :=
    (lock_name lk s ∗ inv lockN (lock_inv γ lk R))%I.

  Global Instance is_lock_persistent γ lk s R : Persistent (is_lock γ lk s R).
  Proof. apply _. Qed.

  (* the two projections + the introduction rule (the only interface the
     lock leaves and [newlock] need). *)
  Lemma is_lock_name γ lk s R : is_lock γ lk s R -∗ lock_name lk s.
  Proof. iIntros "[$ _]". Qed.
  Lemma is_lock_inv γ lk s R : is_lock γ lk s R -∗ inv lockN (lock_inv γ lk R).
  Proof. iIntros "[_ $]". Qed.
  Lemma is_lock_intro γ lk s R :
    lock_name lk s -∗ inv lockN (lock_inv γ lk R) -∗ is_lock γ lk s R.
  Proof. iIntros "#Hn #Hi". by iFrame "Hn Hi". Qed.

  Global Instance mem_pointsto_timeless a dq b : Timeless (mem_pointsto a dq b).
  Proof. rewrite /mem_pointsto. apply _. Qed.

  Global Instance lock_word_timeless lk v : Timeless (lock_word lk v).
  Proof. rewrite /lock_word /word4_pointsto. apply _. Qed.

  (* ---- lock construction (the "newlock" ghost step) ------------------ *)

  (* a FREE physical lock (word 0, cpu word 0) plus the resource it protects
     and its name become a lock. *)
  Lemma newlock E (lk : mword 64) (s : string) (R : iProp Σ) :
    lock_name lk s -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_cpu lk ↦₈ (zero_reg : mword 64) -∗
    R ={E}=∗ ∃ γ : gname, is_lock γ lk s R.
  Proof.
    iIntros "#Hnm Hword Hcpu HR".
    iMod (own_alloc ((●E (None : leibnizO lock_state) ⋅ ◯E (None : leibnizO lock_state))
                     : lockUR)) as (γ) "H"; [ apply excl_auth_valid | ].
    iDestruct (own_op with "H") as "[Ha Hf]".
    iMod (inv_alloc lockN E (lock_inv γ lk R) with "[Hword Hcpu Ha Hf HR]") as "#Hinv".
    { iNext. iExists (mword_of_int 0 : mword 32), None.
      rewrite /lock_word. iFrame "Hword Hcpu Ha".
      iLeft. iFrame "Hf HR". done. }
    iModIntro. iExists γ.
    iApply (is_lock_intro with "Hnm Hinv").
  Qed.

End Lock.
