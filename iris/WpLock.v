(* WpLock.v -- the standard CSL/Iris spin-lock invariant for xv6's
   [struct spinlock], mirroring iris_heap_lang/lib/spin_lock.v but over the
   PHYSICAL fields of the Sail RISC-V machine: the 4-byte lock word
   ([lk->locked] @ +0) AND the 8-byte owner word ([lk->cpu] @ +16).

     lock_inv      -- ∃ v st, lock word ↦ v ∗ lk_cpu_res st lk ∗ ghost st
                        ∗ (st free ∗ v = 0 ∗ frag ∗ R  ∨  st held ∗ v ≠ 0)
     lk_cpu_res    -- the owner field, WHOLE at 0 while the lock is free or
                      in a one-store window, and HALF at [cpus_ptr i] plus
                      the held-lock-set fragment [lk_in i lk] while hart [i]
                      holds it (the other half is in that hart's
                      [LockSet.cpu_locks]).  See the block at its definition.
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
From stdpp Require Import bitvector.definitions.  (* [bv 8]: the M4 owner-cell kit is stated per byte *)
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl gmap auth ufrac.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import invariants cancelable_invariants own.
Require Import SailStdpp.Base SailStdpp.Operators_mwords.
Require Import Riscv.rv64d.
Require Import Riscv.rv64d_types.  (* A6.84: the ledger word's carrier types *)
Require Import RiscvPtsto RiscvLang.
(* EXPORTED: [lock_cpu] (the +16 owner-field address) lives there, because the
   per-cpu held-lock set is stated over it, and the ~40 files that reach
   [lock_cpu] through this one keep working. *)
Require Export LockSet.
Require Import ProcGeom.
Require Import RiscvModelBytes.  (* [nth_byte] / [bv_eq_of_bytes]: the M4 owner-cell kit below is stated per BYTE *)
Require Import TsoMemPa.  (* [agent]: the racy owner-cell kit quantifies over the log's authors *)
Require Export Xv6Cameras.  (* the cameras this file states its theory over *)
(* the context axis (tso-port M3): the PAYLOAD of every lock is a function
   of the thread of control that holds its facts -- see the block above
   [lock_inv]. *)
Require Import Ktier KMap RiscvExtras.  (* A6.84: [ktier_pin] / [kmap_at] --
   a ledger cell carries no MAPPING, so [lk_addr_claim] states one here *)
Require Import TsoCtx.
(* [lock_name_intro] mints the deliberately-RAW name-field metadata
   (tso-port.md §0.8' ruling 2) out of a context-indexed store result, so it
   leaves the ledger through [TsoCtx.ctx_word_pointsto_forget] -- the named
   one-way projection (§6 amendment A6.8), where the SC-era file used the
   now-dead [TsoCtxShim.ctx_word_to_mem].  Sound and final: the field is
   discarded one line later, so nothing will ever load it again. *)
Local Open Scope Z_scope.


Section Lock.
  Context `{!riscvGS Σ, !lockG Σ}.
  (* the ambient context, used ONLY by the construction lemmas at the
     bottom (the creator deposits the payload at its own identity); a
     section variable, so nothing else picks it up. *)
  Context `{XI : CurCtx}.

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

  (* the one agent that may be missing an own-last record in each state:
     the HOLDER, and nobody else (see [lk_own_ok] below). *)
  Definition lk_ex (st : lock_state) : option CPU :=
    match st with Some (i, true) => Some i | _ => None end.

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
     word points-to (which also bundles the 4-byte alignment of [lk]).

     ∃-CONTEXT, AND THAT IS A CORRECTNESS FIX, NOT A STYLE ONE
     (tso-port.md §0.19′'s ruling, replayed here at A6.72; main's [WpLock]
     at HEAD is the reference).  The cell is exactly [lk_cpu_res]'s owner
     word one field over and it takes the same shape for the same reason
     (§0.8′ ruling 2: lock metadata raw, lock-internal CELLS ∃-context):

     1. AN AMBIENT INDEX HERE DRAGS A CONTEXT INTO [is_lock].  This cell
        sits inside [lock_inv], hence inside the PERSISTENT HANDLE, and a
        boot-minted [is_lock] could then not be stated at another thread.
        §0.12′'s park record carries three lock handles (wait / ticks /
        nextpid) across a ∀-quantified resume context PRECISELY because
        [is_lock] is a CLOSED TERM; the ambient index falsified that
        outright, and no payload conversion could have repaired it.  The ∃
        closes the term again, and it is also the TRUE statement: the word
        belongs to whichever hart last stored it.
     2. RAW WAS CONSIDERED AND IS WRONG.  The lock word is only ever READ
        exclusively (acquire's [amoswap.w.aq] takes the machine's exclusive
        arm), so a raw cell would discharge every load -- but release's word
        clear is a STORE, and a store owes [Wobl_ram], whose γts update
        needs the cell's timestamp element.  A cell with no ledger residue
        cannot be stored to (A6.16).  So the residue stays.

     THE CLIENT-FACING SPELLINGS DO NOT MOVE: the creators still take, and
     the destroyers still hand back, [lk ↦₄ 0] at the caller's own context,
     and [lock_word_intro] is that bridge.

     >>> AND THE ELIMINATION DIRECTION IS NOT A LEMMA HERE.  Main states
     [lock_word_acc] as a [⊣⊢] and proves the ∃-elimination with
     [TsoCtxShim.ctx_word4_{to,of}_mem] -- sound at SC, where [ctx] is
     degenerate, and FALSE at this machine: a cell at an unknown ξ licenses
     no load at ours.  That direction is the M4 racy-owner-cell entry
     ([WpSconfLock]'s [wp_ld_lkcpu_lockopen_gen] is its twin one field
     over), and it is deliberately absent until the M4 memo lands. <<< *)
  (* >>> A6.84: THE ∃ IS GONE, AND WHAT REPLACED IT IS BETTER.  The ∃ξ
     closed [is_lock]'s term at the cost of an existential nothing could
     eliminate -- "a cell at an unknown ξ licenses no load at ours" -- so
     the two lock leaves that READ the word were unprovable.  At the
     LEDGER tier the cell has no ξ AT ALL: [phys_ledger_word4] is the
     eight-byte carrier's four-byte twin, ξ-free BY CONSTRUCTION, and the
     store gates over it are context-free ([ledger_store_win_at_ok]), so
     release's clear and the AMO's write need no [own_context] either.
     [is_lock] is a closed term for the reason §0.19′ wanted and with no
     residual existential.

     WHAT IT COSTS is the address's MAPPING, which a ledger cell does not
     carry: the invariant keeps the two [lk_addr_claim]s instead.  They
     are PERSISTENT and about the ADDRESS, not the value, so one peek
     serves every leaf ([WpSconfLock.lock_claims]).  <<< *)
  Definition lock_word (lk : mword 64) (v : mword 32) : iProp Σ :=
    TsoCtx.phys_ledger_word4 lk (DfracOwn 1) v.

  (* the INTRODUCTION leg, which is all the creators need.  ONE-WAY, and
     deliberately: the lock's word never goes back to the ctx tower. *)
  Lemma lock_word_intro (lk : mword 64) (v : mword 32) :
    lk ↦₄ v ⊢ lock_word lk v.
  Proof. rewrite /lock_word. iIntros "H". by iApply TsoCtx.ctx_word4_ledger_kt0. Qed.

  (* ===================================================================
     THE OWNER FIELD, AND THE HELD-SET FRAGMENT BESIDE IT.

     [lk->cpu] ([LockSet.lock_cpu], the 8-byte word at +16) is owned WHOLE by
     the invariant in every state.  What varies is what sits beside it: while
     hart [i] holds the lock, the invariant also keeps the held-set fragment
     [lk_in i r] at this lock's NAME (its rank orders it, but the set holds
     the name -- see LockRank.v's [locks_below]).  So
     the two readings of "this lock is held by hart i" -- the C field and the
     ghost set -- are one resource, and neither can drift from the other:

       - RELEASE's [lk->cpu = 0] retires the fragment, which is exactly the
         licence to take the name out of the hart's set
         ([LockSet.cpu_locks_delete]).
       - ACQUIRE's [lk->cpu = mycpu()] mints it, which needs [r ∉ S] -- and
         that is supplied by the caller's ORDER PREMISE
         ([LockRank.locks_below S r]), not read off the machine.
       - a hart whose set omits [r] therefore CANNOT be the holder, so
         [holding(lk)] is provably 0 and acquire's [if(holding(lk)) panic()]
         arm is DEAD rather than discharged by a panic credential.

     WHAT THIS REPLACED, AND WHY THE SIMPLIFICATION IS THE ORDER'S DOING.
     Before the lock order existed, acquire had no premise to lean on, so
     [r ∉ S] had to be DERIVED: the hart co-owned HALF of every held lock's
     cpu cell (pinned at [cpus_ptr i]) and freshness fell out of the cell
     disagreeing at 0 in acquire's one-store window.  That forced a
     state-dependent sibling ([lk_cpu_half] / [lk_cpu_rest]), a fixed 1/2
     fraction the two READ leaves had to be blind to -- because
     [WpSconfMem.wp_load_s_sconf_au] fixes its [dqm] OUTSIDE the fupd that
     opens the invariant, where [st] is still existential -- and an EXCHANGE
     wand in each of the two cpu-word STORE leaves.  With the premise
     supplying freshness, all of it goes: the cell is [DfracOwn 1] in every
     state, the read leaves are state-blind for free, and the stores are
     ordinary stores. *)
  Definition lk_cpu_frag (st : lock_state) (r : string) : iProp Σ :=
    match st with
    | Some (i, true) => lk_in i r
    | _ => emp
    end%I.

  (* THE OWNER CELL'S CONTEXT IS ∃-QUANTIFIED, not ambient: [lk_cpu_res]
     sits inside [lock_inv] under the invariant, so an ambient index here
     would drag a context into [is_lock] -- the persistent HANDLE -- and a
     handle minted at boot could not be stated at another thread.  ∃ is
     also the true statement: the cell belongs to whichever hart last
     stored it.  The window lemmas below keep the ∃ ([lk_cpu_cell]); the
     SC-era trade for the acting hart's ambient form died with the shim,
     and recovering it is the M4 racy-kit entry spelled out there. *)
  (* THE ADDRESS CLAIM a ledger cell does not carry.  Character for
     character [WpSconfMem.mem_claim] under its alignment -- that file
     sits ABOVE this one, so the content is restated here and
     [WpSconfLock.lock_claims] is the one line that converts (they are
     convertible at [KT0], which is the only tier a lock lives at). *)
  (* THE ADDRESS CLAIM A LEDGER CELL DOES NOT CARRY.
     PER BYTE, not merely at the base (A6.86).  The base form is what the
     translation engines want ([WpSconfMem.mem_claim] under its alignment),
     but the PAGE that reclaims the cell wants one per byte -- a free page's
     bytes are [TsoCtx.mem_free], and [mem_free] is the kmap claim over the
     visibility-free byte.  Both readings are here because the producer has
     both for free: every creator pays this claim off a CTX WORD it still
     holds, and a ctx word is ctx BYTES, each carrying its own mapping.
     *That* is why the arithmetic never appears: the claim is read off the
     tower before the cell leaves it, not reconstructed after. *)
  Definition lk_addr_claim (a : Arch.pa) (width : Z) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) width = true⌝ ∗
     ∃ ppn : mword 44,
       kmap_at (svpn_of a) ppn KP_rw ∗
       ⌜(uint a < 274877906944)%Z⌝ ∗
       ⌜addr_is_ram (pa_of ppn a)⌝ ∗
       ⌜ktier_pin KT0 ppn a⌝ ∗
       ([∗ list] j ∈ seq 0 (Z.to_nat width),
          ∃ ppj : mword 44,
            kmap_at (svpn_of (pa_add a j)) ppj KP_rw ∗
            ⌜(uint (pa_add a j) < 274877906944)%Z⌝ ∗
            ⌜ktier_pin KT0 ppj (pa_add a j)⌝))%I.

  Global Instance lk_addr_claim_persistent a width :
    Persistent (lk_addr_claim a width).
  Proof. rewrite /lk_addr_claim. apply _. Qed.

  (* the per-byte half, which is what a free page's bytes are keyed by *)
  Lemma lk_addr_claim_bytes (a : Arch.pa) (width : Z) :
    lk_addr_claim a width ⊢
    [∗ list] j ∈ seq 0 (Z.to_nat width),
      ∃ ppj : mword 44,
        kmap_at (svpn_of (pa_add a j)) ppj KP_rw ∗
        ⌜(uint (pa_add a j) < 274877906944)%Z⌝ ∗
        ⌜ktier_pin KT0 ppj (pa_add a j)⌝.
  Proof. rewrite /lk_addr_claim. by iIntros "(_ & % & _ & _ & _ & _ & $)". Qed.

  (* the generic producer: a ctx WORD of any width carries its own claim --
     the base one off byte 0, the per-byte ones off each byte. *)
  Local Lemma lk_addr_claim_of_bytes (a : Arch.pa) (dq : dfrac) (w : Z)
      (f : nat -> bv 8) :
    (0 < w)%Z ->
    is_aligned_paddr (Physaddr a) w = true ->
    ([∗ list] j ∈ seq 0 (Z.to_nat w),
       ctx_pointsto (KTR := KT0) cur_ctx (pa_add a j) dq (f j))
    ⊢ lk_addr_claim a w.
  Proof.
    intros Hw Hal. iIntros "Hb".
    iAssert ([∗ list] j ∈ seq 0 (Z.to_nat w),
               ∃ ppj : mword 44,
                 kmap_at (svpn_of (pa_add a j)) ppj KP_rw ∗
                 ⌜(uint (pa_add a j) < 274877906944)%Z⌝ ∗
                 ⌜ktier_pin KT0 ppj (pa_add a j)⌝)%I as "#Hbytes".
    { iApply (big_sepL_impl with "Hb"). iIntros "!>" (k j _) "H".
      iEval (rewrite (ctx_pointsto_phys (KTR := KT0))) in "H".
      iDestruct "H" as (ppj) "(#Hk & %Hc & %Hp & _)".
      iExists ppj. iFrame "Hk". by iPureIntro. }
    iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hb") as "Hb0".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    iEval (rewrite (ctx_pointsto_phys (KTR := KT0))) in "Hb0".
    iDestruct "Hb0" as (ppn) "(#Hk & %Hc & %Hp & Hph)".
    iDestruct (ctx_phys_pointsto_ram with "Hph") as %Hram.
    rewrite /lk_addr_claim.
    iSplitR; [done|]. iExists ppn. iFrame "Hk Hbytes". iPureIntro. split_and!; done.
  Qed.

  (* a ctx word carries its own claim, which is how the creators pay it *)
  Lemma lk_addr_claim_of4 (lk : mword 64) (dq : dfrac) (v : mword 32) :
    ctx_word4_pointsto (KTR := KT0) cur_ctx lk dq v ⊢ lk_addr_claim lk 4.
  Proof.
    rewrite ctx_word4_pointsto_unfold. iIntros "[%Hal Hb]".
    iApply (lk_addr_claim_of_bytes lk dq 4 (nth_byte v) ltac:(lia) Hal).
    iExact "Hb".
  Qed.

  (* ...and the EIGHT-byte one, which is how [initlock] pays for the owner
     cell's claim BEFORE the store that takes the cell out of the tower. *)
  Lemma lk_addr_claim_of8 (a : Arch.pa) (dq : dfrac) (v : mword 64) :
    ctx_word_pointsto (KTR := KT0) cur_ctx a dq v ⊢ lk_addr_claim a 8.
  Proof.
    rewrite ctx_word_pointsto_unfold. iIntros "[%Hal Hb]".
    iApply (lk_addr_claim_of_bytes a dq 8 (nth_byte v) ltac:(lia) Hal).
    iExact "Hb".
  Qed.


  (* ---- THE OWNER CELL AT THE LEDGER TIER, WITH THE RACY PAYLOAD ----

     [lk->cpu] is the one cell in the tree that is READ RACILY, by a hart
     that does not hold the lock, and what it must conclude is an
     EXCLUSION ("the recorded owner is not me").  That is a claim about
     the READER'S OWN WRITE HISTORY, so it rides in the ledger element's
     window payload (TsoMemPa §12c/§12d) and NOT in this invariant --
     tso-pin-memo.md §3's rule, and the reason the cell cannot stay in
     the ctx tower. *)
  (* >>> A6.84 (re-applied): THE RACY KIT MOVES UP.  [lk_cpu_pay]
     below is stated at [lkcpu_z] / [lkcpu_cp], so the kit that
     defines them has to precede it; nothing in the block depends on
     the physical fields, so this is a pure reordering. <<< *)

  (* ================================================================== *)
  (* THE RACY OWNER-CELL KIT AT THE LOCK'S OWN PARAMETERS                *)
  (* (tso-m4-memo.md §3/§8; tso-machine-flip.md A6.82).                   *)
  (*                                                                    *)
  (* This is what [holding()]'s [notheld] read cashes, and it is stated   *)
  (* here -- beside [lk_cpu_val] -- because its two side conditions are   *)
  (* facts about [cpus_ptr] and nothing else: the pointer is INJECTIVE    *)
  (* and never NULL.  The kit asks for them per BYTE, and the memo's      *)
  (* layout computation (§3) is why that is not the same request: for     *)
  (* harts 1..6 there is NO single byte offset separating them from every *)
  (* other hart, so a byte-keyed kit is defeated here and the WINDOW      *)
  (* form -- one timestamp resolving all eight bytes -- is what closes    *)
  (* the gap.  [nth_byte_ne] below is the whole bridge: two words that    *)
  (* differ differ AT SOME BYTE, which is all the window form needs.      *)
  (*                                                                    *)
  (* [agent] is [nat] and covers the DMA agents as well as the harts.     *)
  (* They never write a lock, and giving them [zero_reg] as their "own    *)
  (* word" is exactly what makes the per-agent distinguishing premise     *)
  (* true of them too -- by the same [cpus_ptr] nonzeroness a free lock   *)
  (* uses.                                                               *)
  (* ================================================================== *)

  (* two words that differ, differ at a byte *)
  Lemma nth_byte_ne (w1 w2 : mword 64) :
    w1 <> w2 -> exists k, (k < 8)%nat /\ nth_byte w1 k <> nth_byte w2 k.
  Proof.
    intros Hne.
    assert (H : forall l : list nat,
              (exists k, k ∈ l /\ nth_byte w1 k <> nth_byte w2 k)
              \/ (forall k, k ∈ l -> nth_byte w1 k = nth_byte w2 k)).
    { induction l as [|x xs IH].
      - right. intros k Hk. by apply elem_of_nil in Hk.
      - destruct (decide (nth_byte w1 x = nth_byte w2 x)) as [He|Hnee].
        + destruct IH as [(k & Hk & Hkk) | Hall].
          * left. exists k. split; [ by apply elem_of_cons; right | done ].
          * right. intros k Hk. apply elem_of_cons in Hk as [->|Hk];
              [ done | by apply Hall ].
        + left. exists x. split; [ by apply elem_of_cons; left | done ]. }
    destruct (H (seq 0 8)) as [(k & Hk & Hkk) | Hall].
    - exists k. apply elem_of_seq in Hk. split; [lia | done].
    - exfalso. apply Hne. apply (bv_eq_of_bytes (n := 8) w1 w2).
      intros j Hj. apply Hall, elem_of_seq. lia.
  Qed.

  (* a hart's [struct cpu] pointer is not the clear word *)
  Lemma cpus_ptr_ne_zero (i : CPU) : (zero_reg : mword 64) <> cpus_ptr i.
  Proof.
    intros Heq. pose proof (cpus_ptr_nonzero i) as Hne.
    rewrite -Heq in Hne.
    assert (Ht : eq_vec (zero_reg : mword 64) (zero_reg : mword 64) = true)
      by (apply eq_vec_true_iff; reflexivity).
    rewrite Ht in Hne. discriminate.
  Qed.

  (* the owner word of an arbitrary AGENT: a hart's [struct cpu] pointer,
     and the clear word for everything that is not a hart. *)
  Definition agent_cpus_ptr (h : agent) : mword 64 :=
    match decide (h < NCPU)%nat with
    | left Hh => cpus_ptr (nat_to_fin Hh)
    | right _ => (zero_reg : mword 64)
    end.

  Lemma agent_cpus_ptr_hart (c : CPU) : agent_cpus_ptr (hart_agent c) = cpus_ptr c.
  Proof.
    rewrite /agent_cpus_ptr. case_decide as Hh.
    - f_equal. apply fin_to_nat_inj. by rewrite fin_to_nat_to_fin.
    - exfalso. pose proof (fin_to_nat_lt c). rewrite /hart_agent in Hh. lia.
  Qed.

  Lemma agent_cpus_ptr_ne (h : agent) (c : CPU) :
    h <> hart_agent c -> agent_cpus_ptr h <> cpus_ptr c.
  Proof.
    intros Hne. rewrite /agent_cpus_ptr. case_decide as Hh.
    - intros Heq. apply cpus_ptr_inj in Heq. apply Hne.
      rewrite /hart_agent -Heq fin_to_nat_to_fin //.
    - exact (cpus_ptr_ne_zero c).
  Qed.

  (* THE TWO BYTE FUNCTIONS the owner cell's window payload is stated at:
     the CLEAR word a free lock holds, and each author's own word. *)
  Definition lkcpu_z : nat -> bv 8 := nth_byte (zero_reg : mword 64).
  Definition lkcpu_cp (h : agent) : nat -> bv 8 := nth_byte (agent_cpus_ptr h).

  (* THE [notheld] READ, DISCHARGED.  A hart whose own-last record for the
     window is [Some t] -- which every hart has from the mint until it
     acquires, and again from its own release -- and whose receipt has
     passed the floor, provably does not read its OWN [struct cpu] pointer
     out of [lk->cpu], AT EVERY view it can reach.  That is the whole
     content of [SpecAcquire]'s dead panic arm. *)
  Lemma lkcpu_read_not_mine `{CID : CpuId} (g : gstate) (lk : mword 64)
      (dq : dfrac) (f : nat -> bv 8) (ts : nat -> nat)
      (own : agent -> option nat) (lo t K : nat) :
    own (hart_agent cpu_id) = Some t ->
    (lo <= K)%nat ->
    tso_interp_at riscv_eraGS g -∗
    TsoGhost.view_lb view_name loglen_name (hart_agent cpu_id) K -∗
    ([∗ list] j ∈ seq 0 8,
       TsoCtx.phys_ledger_wpay (pa_add (lock_cpu lk) j) dq (f j) (ts j)
         (TsoMemPa.TsWin (lock_cpu lk) 8 j lkcpu_z lkcpu_cp own lo)) -∗
    ⌜forall (tv : nat), (g.(gtv) cpu_id <= tv)%nat -> forall w : mword 64,
       tso_read_bytes g.(gimg) g.(glog) (hart_agent cpu_id) tv (lock_cpu lk)
         (N.of_nat 8) w -> w <> cpus_ptr cpu_id⌝.
  Proof.
    intros Hown HloK.
    assert (Hcpw : forall k, (k < 8)%nat ->
              nth_byte (cpus_ptr cpu_id) k = lkcpu_cp (hart_agent cpu_id) k).
    { intros k Hk. by rewrite /lkcpu_cp agent_cpus_ptr_hart. }
    assert (Hzk : exists k, (k < 8)%nat /\
              lkcpu_z k <> lkcpu_cp (hart_agent cpu_id) k).
    { rewrite /lkcpu_z /lkcpu_cp agent_cpus_ptr_hart.
      apply nth_byte_ne. exact (cpus_ptr_ne_zero cpu_id). }
    assert (Hinj : forall h', h' <> hart_agent cpu_id ->
              exists k, (k < 8)%nat /\
                lkcpu_cp h' k <> lkcpu_cp (hart_agent cpu_id) k).
    { intros h' Hne. rewrite /lkcpu_cp (agent_cpus_ptr_hart cpu_id).
      apply nth_byte_ne. exact (agent_cpus_ptr_ne h' cpu_id Hne). }
    iIntros "Hint #HK Hb".
    iApply (TsoCtx.ledger_read_racy_word_ok g (lock_cpu lk) 8%nat dq f ts
              lkcpu_z lkcpu_cp own lo t K (m := 64) (cpus_ptr cpu_id)
              ltac:(lia) Hown HloK Hcpw Hzk Hinj with "Hint HK Hb").
  Qed.

  (* [s] -- the lock's NAME -- rather than a bare rank: [is_lock] already
     carries it, so instantiating with [lock_rank s] leaves no second degree
     of freedom that could disagree with the name in [lock_name]. *)
  (* THE PAYLOAD IS A FUNCTION OF THE CONTEXT (tso-port M3).  A lock's
     facts belong, at any moment, to a THREAD OF CONTROL: the depositor's
     until release re-indexes them, the lock's own while parked here, the
     acquirer's after its AMO.  A fixed [iProp] payload cannot say that --
     whichever context its facts were elaborated at, every OTHER thread's
     acquire would receive them at the wrong index.  So [R : CtxId →
     iProp]; clients write payloads with the ambient spellings under
     [TsoCtx]'s [<{ P }>] wrapper and owe [CtxMorph R] at acquire/release
     (SpecAcquire.v / SpecRelease.v) -- a payload that fails it
     structurally is a real TSO bug found early.


     AT SC the parked payload is the ∃-closure below: the index is
     phantom under the seal, so "some context's facts" is as strong as
     anyone's, and the acquire-side re-indexing is a [CtxMorph] step
     against the shim's [ctx_dom_sc].  AT CUTOVER this free arm instead
     holds [R ξ_L] beside the lock's own internal context token
     ([TsoCtxTwin2]'s parked shape: release deposits by
     [ctx_dom_to_parked]-transport, acquire withdraws by
     [ctx_dom_of_parked] against its AMO-at-the-top evidence); the
     statement list above this definition is what stays. *)

  Definition lk_cpu_pay (lk : mword 64) (v : mword 64)
      (own : agent -> option nat) (lo : nat) : iProp Σ :=
    ([∗ list] j ∈ seq 0 8, ∃ t : nat,
       TsoCtx.phys_ledger_wpay (pa_add (lock_cpu lk) j) (DfracOwn 1)
         (nth_byte v j) t
         (TsoMemPa.TsWin (lock_cpu lk) 8 j lkcpu_z lkcpu_cp own lo))%I.

  (* the AUTHOR's form: the same window with the store's own message
     fragment beside every byte.  That is what makes the HOLDER's read of
     the cell IT wrote exact ([TsoCtx.ledger_read_wpay_vis_ok]) -- and it
     is why the held arm carries more than the free one, which A6.78 §(2)
     named and nothing before it did. *)
  Definition lk_cpu_pay_vis (h : agent) (lk : mword 64) (v : mword 64)
      (own : agent -> option nat) (lo : nat) : iProp Σ :=
    ([∗ list] j ∈ seq 0 8, ∃ t : nat,
       TsoCtx.ledger_vis h 0 t ∗
       TsoCtx.phys_ledger_wpay (pa_add (lock_cpu lk) j) (DfracOwn 1)
         (nth_byte v j) t
         (TsoMemPa.TsWin (lock_cpu lk) 8 j lkcpu_z lkcpu_cp own lo))%I.

  Lemma lk_cpu_pay_vis_forget h lk v own lo :
    lk_cpu_pay_vis h lk v own lo ⊢ lk_cpu_pay lk v own lo.
  Proof.
    rewrite /lk_cpu_pay_vis /lk_cpu_pay.
    iIntros "H". iApply (big_sepL_impl with "H").
    iIntros "!>" (k j _) "(%t & _ & H)". by iExists t.
  Qed.

  Global Instance lk_cpu_pay_timeless lk v own lo :
    Timeless (lk_cpu_pay lk v own lo).
  Proof. rewrite /lk_cpu_pay. apply _. Qed.
  Global Instance lk_cpu_pay_vis_timeless h lk v own lo :
    Timeless (lk_cpu_pay_vis h lk v own lo).
  Proof. rewrite /lk_cpu_pay_vis. apply _. Qed.

  (* >>> THE OWN-INVARIANT, AND IT IS ONE SENTENCE: the ONLY agent that
     may be missing an own-last record is the HOLDER.  Acquire's store
     writes the author's own word and REVOKES its entry
     ([ledger_store_wpay_ok]'s second arm); release's writes the clear
     word and RESTORES it (the first).  Every other agent's entry frames.
     A [notheld] reader is a non-holder by definition, so this is exactly
     the premise [lkcpu_read_not_mine] consumes. <<< *)
  Definition lk_own_ok (ex : option CPU) (own : agent -> option nat) : Prop :=
    forall h : agent, own h = None -> exists i : CPU, ex = Some i /\ h = hart_agent i.

  Definition lk_cpu_cell_ex (lk : mword 64) (v : mword 64)
      (ex : option CPU) : iProp Σ :=
    (∃ (own : agent -> option nat) (lo : nat),
       ⌜lk_own_ok ex own⌝ ∗
       match ex with
       | Some i => lk_cpu_pay_vis (hart_agent i) lk v own lo
       | None => lk_cpu_pay lk v own lo
       end)%I.

  Definition lk_cpu_cell (lk : mword 64) (v : mword 64) : iProp Σ :=
    lk_cpu_cell_ex lk v None.

  (* the held cell forgets its author fragment and becomes an ordinary
     one, at the cost of the exactness the holder had *)
  Lemma lk_cpu_cell_ex_forget lk v ex :
    lk_cpu_cell_ex lk v ex ⊢ lk_cpu_cell lk v ∨ ⌜is_Some ex⌝.
  Proof.
    iIntros "(%own & %lo & %Hok & Hb)". destruct ex as [i|].
    - iRight. iPureIntro. by eexists.
    - iLeft. iExists own, lo. by iFrame "Hb".
  Qed.

  (* what [initlock]'s post hands over and every creator takes: the
     window payload at the CLEAR word, plus the address claim the ledger
     cells do not carry. *)
  Definition lk_cpu_fresh (lk : mword 64) : iProp Σ :=
    (lk_addr_claim (lock_cpu lk) 8 ∗ lk_cpu_cell lk (zero_reg : mword 64))%I.

  (* THE RECLAMATION, AND IT IS THE WHOLE POINT (tso-port.md §0.26′).
     A lock on a kalloc'd page must be able to DIE.  Its owner word is a
     ledger cell and cannot re-enter the ctx tower -- that needs a drain
     (A6.84 §(2)) -- but it does not have to: [kfree] wants only the page's
     FUTURE, and a wpay cell has one.  The claim supplies the mapping the
     cell dropped; the payload supplies the fraction and the element. *)
  Lemma lk_cpu_fresh_free (lk : mword 64) :
    lk_cpu_fresh lk ⊢
    [∗ list] j ∈ seq 0 8,
      TsoCtx.mem_free (KTR := KT0) (pa_add (lock_cpu lk) j) (DfracOwn 1).
  Proof.
    rewrite /lk_cpu_fresh /lk_cpu_cell /lk_cpu_cell_ex /lk_cpu_pay.
    iIntros "[#Hcl (%own & %lo & _ & Hp)]".
    iDestruct (lk_addr_claim_bytes with "Hcl") as "#Hb".
    change (Z.to_nat 8) with 8%nat.
    iApply (big_sepL_impl with "Hp"). iIntros "!>" (k j Hk) "(%t & Hw)".
    iDestruct (big_sepL_lookup _ _ k j Hk with "Hb") as (ppj) "(#Hkj & %Hcj & %Hpj)".
    rewrite /TsoCtx.mem_free. iExists ppj. iFrame "Hkj".
    iSplitR; [done|]. iSplitR; [done|].
    rewrite (ktier_pin_id ppj (pa_add (lock_cpu lk) j) Hpj).
    by iApply TsoCtx.phys_ledger_wpay_free.
  Qed.

  Definition lk_cpu_res (st : lock_state) (lk : mword 64) (r : string) : iProp Σ :=
    (lk_cpu_cell_ex lk (lk_cpu_val st) (lk_ex st) ∗ lk_cpu_frag st r)%I.

  (* the leaves strip this under [>] inside the step engine's callback, and
     [st] is a VARIABLE there, so the match is stuck and the structural
     instances cannot see the two branches.  Stated once, here. *)
  Global Instance lk_cpu_frag_timeless st r : Timeless (lk_cpu_frag st r).
  Proof. destruct st as [[i []]|]; apply _. Qed.
  Global Instance lk_cpu_res_timeless st lk r : Timeless (lk_cpu_res st lk r).
  Proof. apply _. Qed.

  (* THE OWNER CELL, NAMED (§6 amendment A6.8).  The SC-era file stated the
     ∃-cell EQUAL to the acting hart's ambient form ([lk_cpu_cell_acc], via
     the shim) and phrased the three unfold lemmas at that ambient form.
     THE ELIMINATION DIRECTION IS FALSE AT TSO -- a ledger fact is pinned to
     its context, and the ∃ hides WHICH, so nothing can dominate it -- so the
     equation is gone and the unfold lemmas are stated at the cell itself.
     [lk_cpu_cell_intro] is the surviving (trivial) half.

     WHAT THE ELIMINATION NEEDS, so the M4 worklist entry is written down
     rather than implied: the invariant must hold the cell's context PARKED
     ([TsoCtx.ctx_parked ξ T]) beside the word, and the acquirer -- whose
     AMO puts its view at the log top -- mints [ctx_dom ξ cur_ctx] from it
     with [TsoCtx.ctx_dom_of_parked] and moves the word with
     [ctx_morph_word].  That is the racy-kit design; it is the ONE reason
     [lk_cpu_res] may not simply go ambient (an ambient index in the payload
     would drag a context into the persistent [is_lock] handle).  The
     failures at the leaves that read and write this cell
     ([WpSconfLock]) are that entry. *)
  (* the free / window form: the whole cell at 0 and no fragment. *)
  Lemma lk_cpu_res_free (lk : mword 64) (r : string) :
    lk_cpu_res None lk r ⊣⊢ lk_cpu_cell lk (zero_reg : mword 64).
  Proof. rewrite /lk_cpu_res /lk_cpu_cell /=. apply bi.sep_emp. Qed.
  Lemma lk_cpu_res_win (i : CPU) (lk : mword 64) (r : string) :
    lk_cpu_res (Some (i, false)) lk r ⊣⊢ lk_cpu_cell lk (zero_reg : mword 64).
  Proof. rewrite /lk_cpu_res /lk_cpu_cell /=. apply bi.sep_emp. Qed.
  (* THE HELD FORM CARRIES MORE THAN THE OTHER TWO, and that is the
     author-fragment point (A6.78 §(2)): the holder's own read of the
     cell must be EXACT, so the held cell keeps the store's message
     fragment beside every byte. *)
  Lemma lk_cpu_res_held (i : CPU) (lk : mword 64) (r : string) :
    lk_cpu_res (Some (i, true)) lk r ⊣⊢
    lk_cpu_cell_ex lk (cpus_ptr i) (Some i) ∗ lk_in i r.
  Proof. rewrite /lk_cpu_res /=. reflexivity. Qed.

  (* A6.66 THE PARKED-RECORD FREE ARM (tso-port.md §0.18′, ported from the
     main tree's landed shape).  The free arm holds the payload's facts
     BESIDE the record's own context token, so release deposits into a
     fresh record and acquire absorbs out of it -- and [ctx_dom] leaves
     the lock's transport path entirely.
     PER-PUBLICATION, not per-lock: §0.18′'s stamp analysis says the tie
     [T' ≤ t_release] is per-publication, so a record is minted at each
     release and abandoned by the winner that claims it.  Nothing needs to
     ratchet across generations and no token travels with the holder. *)
  Definition lock_pay (R : CtxId -> iProp Σ) : iProp Σ :=
    (∃ (ξ : CtxId) (T : nat), ctx_parked ξ T ∗ R ξ)%I.

  (* THE CREATOR'S MINT -- AND HERE IT IS HONEST, WHICH IT IS NOT ON MAIN.
     §0.18′ had to quarantine this at one site behind the shim's
     [ctx_dom_sc], because at SC there is no way to move a payload onto a
     fresh parked context.  THIS tree has the real [ctx_deposit], so the
     mint is a plain deposit into a freshly allocated record and there is
     NO quarantine anywhere on the lock's transport path.
     WHAT IT COSTS INSTEAD, and the trade is worth naming: [ctx_deposit]
     wants the creator's running token, so this lemma takes [own_context]
     and hands it straight back.  That is the 19-call-site creator cascade
     §0.18′ priced and deferred -- deferred there because the quarantine
     was cheaper, taken here because the honest proof exists.  Every
     newlock wrapper gains a token it already has in scope at its call
     sites. *)
  (* A6.64's lesson applies to the STATEMENT here: [own_context] is
     CpuId-indexed, and this section binds no [CpuId], so the creator's
     hart is a parameter -- the token the caller hands over is at ITS
     hart, not at some ambient one. *)
  Lemma lock_pay_intro `{CID : CpuId} (R : CtxId -> iProp Σ) `{!CtxMorph R} :
    own_context cur_ctx -∗ R cur_ctx ==∗ own_context cur_ctx ∗ lock_pay R.
  Proof.
    iIntros "Hrun HR".
    iMod ctx_parked_alloc as (ξc) "Hpk".
    iMod (ctx_deposit R cur_ctx ξc 0 with "Hrun Hpk HR")
      as "(Hrun & %T' & _ & Hpk & HR)".
    iModIntro. iFrame "Hrun". iExists ξc, T'. iFrame "Hpk HR".
  Qed.

  (* THE TWO ADDRESS CLAIMS RIDE HERE, LAST, and outside the ∃: they are
     about the ADDRESSES, so no state mentions them, and they are
     persistent, so one peek serves every leaf.  They are what the ledger
     tier costs (a ledger cell carries no mapping) and they are cheaper
     than what they replaced -- [lock_claims] used to have to take the
     cell APART to read a claim off it, and that is where the last live
     [TsoCtxShim] use lived. *)
  Definition lock_inv (γ : gname) (lk : mword 64) (s : string)
      (R : CtxId → iProp Σ) : iProp Σ :=
    ((∃ (v : mword 32) (st : lock_state),
        lock_word lk v ∗
        lk_cpu_res st lk s ∗
        lock_auth γ st ∗
        (⌜st = None⌝ ∗ ⌜v = (mword_of_int 0 : mword 32)⌝ ∗ lock_frag γ None ∗
           lock_pay R
         ∨ ⌜st ≠ None⌝ ∗ ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝)) ∗
     lk_addr_claim lk 4 ∗ lk_addr_claim (lock_cpu lk) 8)%I.

  (* the lock's NAME: [lk->name] (the 8-byte pointer field at +8) holds the
     address of a NUL-terminated string [s].  initlock writes the field once
     and nothing ever writes it again, so both the field and the string it
     points at are held at [DfracDiscarded] -- [lock_name] is PERSISTENT, and
     therefore rides along inside the (persistent) lock predicate at no
     ownership cost: no proof has to thread the name field, and every holder
     of the lock knows which lock it is by name. *)
  Definition lock_name_field (lk : mword 64) : mword 64 :=
    add_vec lk (sign_extend' 64 (mword_of_int 8 : mword 12)).

  (* CONTEXT-FREE, deliberately, and in the two different ways the port has
     for it.  The name field is lock METADATA -- written once by initlock,
     discarded, read by nobody's data path -- and it rides inside [is_lock];
     were either half of it stated at an ambient ξ, that ξ would be in the
     HANDLE, and a handle minted at boot's context could not even be stated
     at another thread's (§0.8′ ruling 2, which the park rows depend on).

     - the FIELD is the RAW [word_pointsto] (the M1 flip's ruling; the intro
       below converts the minter's context-indexed store result through the
       shim);
     - the STRING is [TsoCtx.ctx_string_all], the ∀-context DERIVED form of
       [↦ₛ] (§0.21′).  [↦ₛ] itself is context-relative now -- it has to be,
       [p->name] is written at runtime -- so the handle takes the derived
       fact, which [KernelDataInv.kernel_data_string_all] mints for a rodata
       literal with no seam at all. *)
  Definition lock_name (lk : mword 64) (s : string) : iProp Σ :=
    (∃ p : mword 64,
       word_pointsto (lock_name_field lk) DfracDiscarded p ∗
       ctx_string_all p DfracDiscarded s)%I.

  Global Instance lock_name_persistent lk s : Persistent (lock_name lk s).
  Proof. apply _. Qed.

  (* Sealing the name field.  [initlock] hands the field back OWNED (it is
     inside the object's storage, and [kfree] memsets it, so a lock on a
     kalloc'd page cannot afford to have it discarded); a caller whose lock is
     static seals it here and forgets it.  A basic update, so this works in
     place inside a WP goal -- no [fupd_wp] needed. *)
  Lemma lock_name_intro (lk p : mword 64) (s : string) :
    ctx_string_all p DfracDiscarded s -∗
    lock_name_field lk ↦₈ p ==∗ lock_name lk s.
  Proof.
    iIntros "#Hs Hf".
    iDestruct (ctx_word_pointsto_forget with "Hf") as "Hf".
    iMod (word_pointsto_persist with "Hf") as "#Hfp".
    iModIntro. iExists p. by iFrame "Hfp Hs".
  Qed.

  (* a lock is its (immutable) name plus the invariant over its two words. *)
  Definition is_lock (γ : gname) (lk : mword 64) (s : string)
      (R : CtxId → iProp Σ) : iProp Σ :=
    (lock_name lk s ∗ inv lockN (lock_inv γ lk s R))%I.

  Global Instance is_lock_persistent γ lk s R : Persistent (is_lock γ lk s R).
  Proof. apply _. Qed.

  (* PERFORMANCE, and it is a big one: WITHOUT this seal, every [iIntros "#Hlk"]
     of an [is_lock] re-derives persistence by UNFOLDING the definition and
     descending through [lock_inv γ lk s R] into [R].  For a lock whose resource
     is large (the virtio disk lock's [disk_res], with its 4096-entry
     descriptor big-ops) that single [#]-intro measured **5.1 s** -- 22 % of
     [ProofEndOp]'s whole [typeclasses eauto] budget, at three sites.  With the
     constant sealed, resolution stops at [is_lock_persistent] above and the
     cost disappears (ProofEndOp 92.5 s -> 78 s from this line alone).
     Everything a consumer needs is lemma-driven ([is_lock_name] /
     [is_lock_inv] / [is_lock_intro] below), so nothing needs the unfolding. *)
  Global Typeclasses Opaque is_lock.

  (* the two projections + the introduction rule (the only interface the
     lock leaves and [newlock] need). *)
  (* these three are the ONLY places that may look inside [is_lock] -- the
     [Typeclasses Opaque] above means an [iDestruct]/[iFrame] elsewhere can no
     longer take it apart, which is the point: it must come through here. *)
  Lemma is_lock_name γ lk s R : is_lock γ lk s R -∗ lock_name lk s.
  Proof. rewrite /is_lock. iIntros "[$ _]". Qed.
  Lemma is_lock_inv γ lk s R : is_lock γ lk s R -∗ inv lockN (lock_inv γ lk s R).
  Proof. rewrite /is_lock. iIntros "[_ $]". Qed.
  Lemma is_lock_intro γ lk s R :
    lock_name lk s -∗ inv lockN (lock_inv γ lk s R) -∗ is_lock γ lk s R.
  Proof. rewrite /is_lock. iIntros "#Hn #Hi". by iFrame "Hn Hi". Qed.

  (* ---- THE OPENING INTERFACE ------------------------------------------

     WpSconfLock.v is the only file in the tree that ever opens a lock, and
     all its leaves do the same three things: open [lock_inv], take one
     machine step, put it back.  [lock_openable] is that pattern named, with
     two parameters that decide WHOSE lock it is:

       T -- the OPENING CREDENTIAL.  Presented to open, handed straight back.
       D -- the DISPOSAL certificate.  Surrendering it destroys the invariant
            instead of closing it, and the opener keeps the contents.

     Two instances, and they are the whole point:

       inv lockN (lock_inv γ lk s R)              -- any T, D := False
            anyone may open, nobody may destroy: a static kernel lock, and
            exactly today's behaviour
       inv lockN (lock_inv γ lk s R ∨ D)          -- any T that REFUTES D
            the object may die: the invariant degenerates into a husk holding
            [D], and whoever can produce [D] puts it there and walks off with
            the memory.  [T] is whatever proves the object is not dead yet.

     A lock's storage is reclaimable exactly when the right to touch it is a
     resource rather than free knowledge -- which is the real xv6 rule for a
     kalloc'd object: you may take [pi->lock] only while you hold a reference
     to it, OR while you hold the lock.  Both are legitimate credentials, and
     BOTH are needed: the last holder to let go of a reference has already
     given it back by the time it calls release, and what licenses release's
     own three opens is the lock it is still holding.  That is why [T] is a
     parameter and not a fixed token -- see [lock_openable_holder].

     The mask is universally quantified so this file needs no [minstretN]; the
     leaves instantiate it at [⊤ ∖ ↑minstretN]. *)
  Definition lock_openable (γ : gname) (lk : mword 64) (s : string)
      (R : CtxId → iProp Σ) (D : iProp Σ) : iProp Σ :=
    (□ ∀ (E : coPset) (T : iProp Σ),
         ⌜↑lockN ⊆ E⌝ -∗ (T -∗ D -∗ False) -∗ T ={E, E ∖ ↑lockN}=∗
         ▷ lock_inv γ lk s R ∗ T ∗
         ((▷ lock_inv γ lk s R ={E ∖ ↑lockN, E}=∗ True)      (* put it back *)
          ∧ (D ={E ∖ ↑lockN, E}=∗ True)))%I.               (* or destroy it *)

  Global Instance lock_openable_persistent γ lk s R D :
    Persistent (lock_openable γ lk s R D).
  Proof. apply _. Qed.

  (* a permanent [inv]: nothing has to be refuted, and no disposal is
     possible. *)
  Lemma lock_openable_inv γ lk s R :
    inv lockN (lock_inv γ lk s R) ⊢ lock_openable γ lk s R False.
  Proof.
    iIntros "#Hi !>" (E T HE) "_ HT".
    iMod (inv_acc E lockN with "Hi") as "[Hbody Hclose]"; [done|].
    iModIntro. iFrame "Hbody HT".
    iSplit; [iExact "Hclose" | iIntros "%Hf"; destruct Hf].
  Qed.

  (* the bridge every existing lock user rides: today's lock IS the permanent
     instance of the generic one. *)
  Lemma is_lock_openable γ lk s R : is_lock γ lk s R ⊢ lock_openable γ lk s R False.
  Proof. iIntros "H". iApply lock_openable_inv. by iApply is_lock_inv. Qed.

  (* the refutation obligation is vacuous for a lock that cannot die. *)
  Lemma lock_refute_False (T : iProp Σ) : ⊢ T -∗ False -∗ False.
  Proof. iIntros "_ []". Qed.

  (* ---- the CANCELLABLE flavour ----------------------------------------

     One invariant with a dead branch, and any credential that refutes it.
     This is what a [cinv] would be if its accessor did not insist on a share
     of the very token that has to be WHOLE in order to cancel -- and that
     insistence is exactly what a multiply-owned object cannot satisfy: the
     last holder to let go of a reference has already given it back by the
     time it calls release, and what licenses release's own opens is the LOCK
     it is still holding, a different resource entirely.  Quantifying [T]
     inside the accessor is what lets the two coexist.

     [D] must be timeless: the dead branch is refuted UNDER a later, and there
     is no step to take there. *)
  Lemma lock_openable_of_dead γ lk s R D `{!Timeless D} :
    inv lockN (lock_inv γ lk s R ∨ D) ⊢ lock_openable γ lk s R D.
  Proof.
    iIntros "#Hi !>" (E T HE) "Hrefute HT".
    iMod (inv_acc E lockN with "Hi") as "[Hbody Hclose]"; [done|].
    rewrite bi.later_or. iDestruct "Hbody" as "[Hlive | >Hdead]".
    2:{ iExFalso. iApply ("Hrefute" with "HT Hdead"). }
    iModIntro. iFrame "Hlive HT".
    iSplit.
    - iIntros "Hb". iApply "Hclose". by iLeft.
    - iIntros "Hd". iApply "Hclose". iRight. by iNext.
  Qed.

  (* ---- THE FINISHING INTERFACE ---------------------------------------

     The other half: what the CALLER of release's word clear supplies to
     decide the invariant's fate.  At that instant the store has happened and
     the state ghost is back at [None], so the two zeroed words, the ghost
     state and [R] are all in hand at once -- which is why the choice has to
     be made HERE and not one instruction later.  The finisher is handed the
     close-or-destroy choice at mask [E] and the contents in PIECES, and
     produces the leaf's output resource [Out].

     Pieces, not a reassembled [lock_inv]: a destroying caller needs the ghost
     state (that is what it turns into a certificate) and a closing one can
     rebuild the body from them.  The two canonical instances are below. *)
  Definition lock_finisher (γ : gname) (lk : mword 64) (s : string)
      (R : CtxId → iProp Σ) (D Out : iProp Σ)
      (E : coPset) : iProp Σ :=
    ( ((▷ lock_inv γ lk s R ={E ∖ ↑lockN, E}=∗ True)
       ∧ (D ={E ∖ ↑lockN, E}=∗ True)) -∗
      lock_auth γ None -∗ lock_frag γ None -∗
      lk ↦₄ (mword_of_int 0 : mword 32) -∗
      lk_cpu_fresh lk -∗
      lock_pay R -∗
      |={E ∖ ↑lockN, E}=> Out)%I.

  (* put it back: today's release, and equally the release of an object that
     merely still has other holders -- [D] is not used, only not taken. *)
  Lemma lock_finisher_close γ lk s R D E : ⊢ lock_finisher γ lk s R D emp E.
  Proof.
    iIntros "[Hclose _] Hauth Hfrag Hword [#Hc8 Hcpu] HR".
    iDestruct (lk_addr_claim_of4 with "Hword") as "#Hc4".
    iMod ("Hclose" with "[Hauth Hfrag Hword Hcpu HR]") as "_"; [| by iModIntro].
    iNext. rewrite /lock_inv. iFrame "Hc4 Hc8".
    iExists (mword_of_int 0 : mword 32), None.
    iDestruct (lock_word_intro with "Hword") as "Hword".
    rewrite lk_cpu_res_free. iFrame "Hword Hcpu Hauth".
    iLeft. by iFrame "Hfrag HR".
  Qed.

  (* destroy it and keep the storage.  The certificate [D] is assembled HERE,
     out of the ghost state the lock just gave up plus whatever the caller
     finds in [R] -- not brought along ready-made.  That generality is what a
     multiply-owned object needs: the last holder to let go has necessarily
     already surrendered its share of the certificate into [R], and [R] is
     only in hand at this instant (see PipeInv.pipe_res_dead). *)
  Lemma lock_finisher_destroy γ lk s R D Out E :
    (lock_frag γ None -∗ lock_pay R ==∗ D ∗ Out) -∗
    lock_finisher γ lk s R D
      (lk ↦₄ (mword_of_int 0 : mword 32) ∗ lk_cpu_fresh lk ∗ Out) E.
  Proof.
    iIntros "Hcomplete [_ Hdispose] Hauth Hfrag Hword Hcpu HR".
    iMod ("Hcomplete" with "Hfrag HR") as "[HD HOut]".
    iMod ("Hdispose" with "HD") as "_".
    iModIntro. by iFrame "Hword Hcpu HOut".
  Qed.

  (* [mem_pointsto]'s and [word4_pointsto]'s [Timeless] instances now live in
     RiscvPtsto.v, beside the definitions. *)
  Global Instance lock_word_timeless lk v : Timeless (lock_word lk v).
  Proof. rewrite /lock_word. apply _. Qed.

  (* ---- lock construction (the "newlock" ghost step) ------------------ *)

  (* THE lock body, built: a free physical lock (word 0, cpu word 0) plus the
     resource it protects.  Whether that body then goes into a permanent [inv]
     or a cancellable [cinv] is the caller's business -- this is the piece both
     constructions share, and a basic update, so it can be done before the
     invariant's namespace or gname exists (which is what an object whose
     resource mentions its OWN cancel gname needs; see [newlock_c_delayed]). *)
  (* A6.66: the free arm is now the parked record, so the creator DEPOSITS
     (honestly -- see [lock_pay_intro]) instead of wrapping the payload in a
     bare existential.  The token is taken and handed straight back. *)
  Lemma lock_inv_alloc `{CID : CpuId} (lk : mword 64) (s : string)
      (R : CtxId → iProp Σ) `{!CtxMorph R} :
    own_context cur_ctx -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lk_cpu_fresh lk -∗
    R cur_ctx ==∗ own_context cur_ctx ∗ ∃ γ : gname, lock_inv γ lk s R.
  Proof.
    iIntros "Hrun Hword [#Hc8 Hcpu] HR".
    iDestruct (lk_addr_claim_of4 with "Hword") as "#Hc4".
    iMod (lock_pay_intro R with "Hrun HR") as "[Hrun HR]".
    iFrame "Hrun".
    iMod (own_alloc ((●E (None : leibnizO lock_state) ⋅ ◯E (None : leibnizO lock_state))
                     : lockUR)) as (γ) "H"; [ apply excl_auth_valid | ].
    iDestruct (own_op with "H") as "[Ha Hf]".
    iModIntro. iExists γ. rewrite /lock_inv. iFrame "Hc4 Hc8".
    iExists (mword_of_int 0 : mword 32), None.
    iDestruct (lock_word_intro with "Hword") as "Hword".
    rewrite lk_cpu_res_free. iFrame "Hword Hcpu Ha".
    iLeft. iFrame "Hf HR". done.
  Qed.

  (* a FREE physical lock plus its resource become a lock that can DIE: the
     body carries the dead branch from the start, and the ghost name of the
     lock state is chosen FIRST, so [R] and [D] may both mention it -- which
     they do for any object whose dead state parks the lock's own state
     fragment (PipeInv.pipe_dead). *)
  Lemma newlock_d `{CID : CpuId} E (lk : mword 64) (s : string) :
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lk_cpu_fresh lk ==∗
    ∃ γ : gname, ∀ (R : CtxId → iProp Σ) (D : iProp Σ),
      ⌜CtxMorph R⌝ -∗ own_context cur_ctx -∗
      R cur_ctx ={E}=∗ own_context cur_ctx ∗ inv lockN (lock_inv γ lk s R ∨ D).
  Proof.
    iIntros "Hword [#Hc8 Hcpu]".
    iDestruct (lk_addr_claim_of4 with "Hword") as "#Hc4".
    iMod (own_alloc ((●E (None : leibnizO lock_state) ⋅ ◯E (None : leibnizO lock_state))
                     : lockUR)) as (γ) "H"; [ apply excl_auth_valid | ].
    iDestruct (own_op with "H") as "[Ha Hf]".
    iModIntro. iExists γ. iIntros (R D) "%HmR Hrun HR".
    iMod (lock_pay_intro (CtxMorph0 := HmR) R with "Hrun HR") as "[Hrun HR]".
    iFrame "Hrun".
    iApply (inv_alloc lockN E (lock_inv γ lk s R ∨ D)).
    iNext. iLeft. rewrite /lock_inv. iFrame "Hc4 Hc8". iExists (mword_of_int 0 : mword 32), None.
    iDestruct (lock_word_intro with "Hword") as "Hword".
    rewrite lk_cpu_res_free. iFrame "Hword Hcpu Ha".
    iLeft. iFrame "Hf HR". done.
  Qed.

  (* a FREE physical lock plus the resource it protects and its name become a
     (permanent) lock. *)
  Lemma newlock `{CID : CpuId} E (lk : mword 64) (s : string)
      (R : CtxId → iProp Σ) `{!CtxMorph R} :
    lock_name lk s -∗
    own_context cur_ctx -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lk_cpu_fresh lk -∗
    R cur_ctx ={E}=∗ own_context cur_ctx ∗ ∃ γ : gname, is_lock γ lk s R.
  Proof.
    iIntros "#Hnm Hrun Hword Hcpu HR".
    iMod (lock_inv_alloc lk s R with "Hrun Hword Hcpu HR") as "[Hrun Hbody]".
    iDestruct "Hbody" as (γ) "Hbody".
    iFrame "Hrun".
    iMod (inv_alloc lockN E (lock_inv γ lk s R) with "[Hbody]") as "#Hinv";
      [ by iNext | ].
    iModIntro. iExists γ.
    iApply (is_lock_intro with "Hnm Hinv").
  Qed.

  (* [newlock] with the two halves SEPARATED: the ghost name is chosen first
     and the resource is supplied afterwards, so [R] may mention the name -- or,
     which is what forced this lemma, the whole LIST of names an ARRAY of locks
     is being built with.  [SchedCtx.proc_lock_res] is indexed by the [γs] of
     all NPROC proc locks (through [p_sched]), so allocating the 64 locks with
     [newlock] is circular and [SpecProcinit.procs_inv_alloc] runs this instead:
     one pass to pick the 64 names, then one pass to pay each lock its
     resource.  [newlock_d] is the same trick for a lock whose resource
     mentions its own cancel gname; the difference is that this one lands on a
     plain [is_lock] rather than the [∨ D] body. *)
  Lemma newlock_delayed `{CID : CpuId} E (lk : mword 64) (s : string) :
    lock_name lk s -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lk_cpu_fresh lk ==∗
    ∃ γ : gname, ∀ R : CtxId → iProp Σ,
      ⌜CtxMorph R⌝ -∗ own_context cur_ctx -∗
      R cur_ctx ={E}=∗ own_context cur_ctx ∗ is_lock γ lk s R.
  Proof.
    iIntros "#Hnm Hword [#Hc8 Hcpu]".
    iDestruct (lk_addr_claim_of4 with "Hword") as "#Hc4".
    iMod (own_alloc ((●E (None : leibnizO lock_state) ⋅ ◯E (None : leibnizO lock_state))
                     : lockUR)) as (γ) "H"; [ apply excl_auth_valid | ].
    iDestruct (own_op with "H") as "[Ha Hf]".
    iModIntro. iExists γ. iIntros (R) "%HmR Hrun HR".
    iMod (lock_pay_intro (CtxMorph0 := HmR) R with "Hrun HR") as "[Hrun HR]".
    iFrame "Hrun".
    iMod (inv_alloc lockN E (lock_inv γ lk s R) with "[Hword Hcpu Ha Hf HR]") as "#Hinv".
    { iNext. rewrite /lock_inv. iFrame "Hc4 Hc8". iExists (mword_of_int 0 : mword 32), None.
      iDestruct (lock_word_intro with "Hword") as "Hword".
    rewrite lk_cpu_res_free. iFrame "Hword Hcpu Ha".
      iLeft. iFrame "Hf HR". done. }
    iModIntro. iApply (is_lock_intro with "Hnm Hinv").
  Qed.

End Lock.
