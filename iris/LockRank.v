(* LockRank.v -- THE SPINLOCK ORDER, as a rank on the lock's NAME.

   xv6 orders its spinlocks by FAMILY, and a family is exactly the string
   passed to [initlock].  A hart may acquire a lock only while every lock it
   already holds ranks strictly BELOW it ([locks_below]), which is the classic
   deadlock-freedom discipline: the held set is a chain in a fixed total order,
   so no cycle of waiting harts can form.

   WHY THE NAME IS ENOUGH, AND NO LOCK-ADDRESS TIEBREAKER IS NEEDED.  Three
   families have more than one instance -- "proc" (NPROC of them), "pipe" (one
   per pipe) and "sleep lock" (the inner spinlock of every [struct sleeplock])
   -- and an audit of every acquire / sleep_prepare / sleep / wakeup /
   acquiresleep site in the kernel says no execution ever holds two members of
   any of them at once.  So a rank on the name alone totally orders every pair
   xv6 can actually hold, and [gset string] is the whole state.  The reasons are
   per-family and two of them are load-bearing rather than incidental -- see
   claude-notes/completed/lock-set.md, which also carries the edge table this
   ranking extends.

   A rank of 0 is the default for a name not in the table: such a lock may be
   acquired only from the empty held set, which is the conservative reading and
   never wrong, only restrictive.

   THE PREMISE IS WHAT DISCHARGES FRESHNESS.  [locks_below S r -> r ∉ S] is
   the whole reason the held set can stay a [gset] with a conditional insert:
   without it, acquire would need the [lk->cpu] cell to derive [lk ∉ S] (see
   LockSet.v's header for the shape that replaced). *)
From Stdlib Require Import String List Lia.
From stdpp Require Import gmap sets.
Local Open Scope string_scope.
Local Open Scope nat_scope.

(* The order, as the topological extension of every simultaneous-hold edge in
   the kernel.  Reading it bottom-up: the FS caches first, then the console
   stack, then the sleeper machinery, then [proc] (which every [sleep_prepare]
   and every [wakeup] acquires, so it sits above all of them), then the
   allocators, and finally the two panic-path locks.

   [pr] and [uart] sit above everything a panic can fire under, because
   [panic] takes [pr.lock]: this
   revision has no [panicking] flag, so panic is [printk] + [printk] +
   self-jump and printk holds [pr.lock] across [consputc] -> [uartputc_sync]
   -> [acquire(&tx_lock)].  Panic fires under nearly every lock, so nothing
   BELOW the two leaves may sit above them.  [uart] has no outgoing edge at
   all: [uartwrite] calls [sleep_prepare] before acquiring [tx_lock] and
   [sleep] after releasing it, and [uartintr] takes no lock.  Neither does
   [bcache]: [bget] RELEASES bcache.lock before its [acquiresleep].  Those
   two facts are what keep the graph acyclic.

   THE ONE UNLICENSED EDGE is [iput]: it holds itable.lock (14) across
   [acquiresleep] (4).  With [proc] below [itable] (kfork) and [sleep lock]
   below [proc] ([acquiresleep] -> [sleep_prepare]), there is no room to
   place [itable] between them -- so that site is justified by an argument
   rather than by rank, namely xv6's own comment at kernel/fs.c:339, "ip->ref
   == 1 means no other process can have ip locked, so this acquiresleep()
   won't block (or deadlock)".  Owed: the icache REF-1 exclusivity theorem
   (design/fs-icache.md) and a non-blocking [acquiresleep] variant. *)
Definition lock_ranks : list (string * nat) :=
  [ ("log",          1)
  ; ("bcache",       2)   (* log_write -> bpin *)
  ; ("cons",         3)
  ; ("sleep lock",   4)
  ; ("pipe",         5)
  ; ("time",         6)
  ; ("virtio_disk",  7)
  ; ("wait_lock",    8)
  ; ("proc",         9)   (* every sleep_prepare / wakeup *)
  ; ("nextpid",     10)   (* allocproc -> allocpid *)
  ; ("kmem",        11)   (* allocproc -> kalloc, freeproc -> kfree *)
  ; ("pr",          12)   (* panic -> printk *)
  ; ("uart",        13)   (* printk -> consputc -> uartputc_sync *)
  (* THE TWO LEAVES, ABOVE [proc].  kfork takes np->lock from allocproc and
     then, STILL HOLDING IT, runs filedup over the fd table and idup on the
     cwd (kernel/proc.c:287-288), so there are real [proc -> ftable] and
     [proc -> itable] edges.  Both locks can carry a rank above [proc]
     because neither is ever held while anything else is acquired:
     filedup/filealloc are acquire-bump-release, fileclose RELEASES
     ftable.lock before it reaches pipeclose/begin_op/iput, and iget is
     acquire-scan-release. *)
  ; ("itable",      14)
  ; ("ftable",      15)
  ].

Fixpoint rank_lookup (l : list (string * nat)) (s : string) : nat :=
  match l with
  | nil => 0
  | cons (t, r) l' => if String.eqb s t then r else rank_lookup l' s
  end.

Definition lock_rank (s : string) : nat := rank_lookup lock_ranks s.

(* every rank a real xv6 lock can carry is computed by [vm_compute], so a
   caller's order premise at concrete names is a decision procedure. *)
Lemma lock_rank_proc : lock_rank "proc" = 9.
Proof. reflexivity. Qed.
Lemma lock_rank_kmem : lock_rank "kmem" = 11.
Proof. reflexivity. Qed.

(* ---- the order premise -------------------------------------------------- *)

(* "every lock this hart holds ranks strictly below [r]" -- acquire's whole
   precondition, and the only thing a caller ever has to prove about the held
   set.

   THE SET HOLDS NAMES, THE ORDER IS A RANK ON THEM.  [lock_rank] appears
   HERE, in the comparison, and nowhere inside the set -- which is what makes
   the set algebra cheap (see [locks_add_del]) and what makes a contract read
   [locks_below lks "log"] rather than [locks_below lks (lock_rank "log")].
   Two names with the same rank would still be distinguished by the set, so
   nothing is conflated; the ranks only ever order them. *)
Definition locks_below (S : gset string) (r : string) : Prop :=
  forall q, q ∈ S -> lock_rank q < lock_rank r.

Global Instance locks_below_dec S r : Decision (locks_below S r).
Proof.
  unfold locks_below.
  destruct (decide (set_Forall (fun q => lock_rank q < lock_rank r) S)) as [H | H].
  - left. exact H.
  - right. intros Hc. apply H. intros q Hq. exact (Hc q Hq).
Defined.

Lemma locks_below_empty (r : string) : locks_below ∅ r.
Proof. intros q Hq. set_solver. Qed.

(* THE FRESHNESS FACT.  This is what lets the held set be a [gset] with a
   conditional insert: a rank strictly above everything held is, in
   particular, not held. *)
Lemma locks_below_not_elem (S : gset string) (r : string) :
  locks_below S r -> r ∉ S.
Proof. intros Hb Hin. exact (Nat.lt_irrefl _ (Hb r Hin)). Qed.

(* threading: after acquiring at [r], the next acquire at [r'] needs the old
   set below [r'] and [r < r']. *)
Lemma locks_below_union_singleton (S : gset string) (r r' : string) :
  lock_rank r < lock_rank r' -> locks_below S r' -> locks_below ({[r]} ∪ S) r'.
Proof.
  intros Hlt Hb q Hq. apply elem_of_union in Hq as [Hq | Hq].
  - apply elem_of_singleton in Hq. subst q. exact Hlt.
  - exact (Hb q Hq).
Qed.

Lemma locks_below_mono (S : gset string) (r r' : string) :
  locks_below S r -> lock_rank r <= lock_rank r' -> locks_below S r'.
Proof. intros Hb Hle q Hq. specialize (Hb q Hq). lia. Qed.

(* releasing never invalidates an order premise *)
Lemma locks_below_difference (S : gset string) (X : gset string) (r : string) :
  locks_below S r -> locks_below (S ∖ X) r.
Proof. intros Hb q Hq. apply Hb. set_solver. Qed.

(* THE RELEASE CANCELLATION, PROVED ONCE AT AN ABSTRACT NAME.

   A balanced acquire/release pair leaves the held set where it started, and
   every such site needs [({[r]} ∪ lks) ∖ {[r]} = lks].  Prove it here, at an
   opaque [r], and the call sites become [apply locks_add_del] with no set
   reasoning at all.

   THE HAZARD THIS AVOIDS USED TO BE MUCH WORSE.  When the set held RANKS, a
   [set_solver] at a concrete lock met [lock_rank "name"] four times over,
   each an unfolding of [rank_lookup]'s 15-way [String.eqb] chain, and
   set_solver's membership case analysis normalised every one -- measured at
   minutes per site.  Names removed [rank_lookup] from the sets entirely, so
   an inline [set_solver] is now merely string comparisons rather than
   catastrophic.  Keep the discipline anyway: an abstract element is instant,
   and nothing here needs to know which lock it is. *)
Lemma locks_add_del (r : string) (lks : gset string) :
  r ∉ lks -> ({[r]} ∪ lks) ∖ {[r]} = lks.
Proof. intros Hnin. set_solver. Qed.

(* the cardinality step an acquire takes, proved once at an abstract name so
   no [set_solver] ever meets a concrete lock (see [locks_add_del]). *)
Lemma size_add (r : string) (lks : gset string) :
  r ∉ lks -> size ({[r]} ∪ lks) = S (size lks).
Proof.
  intros Hnin. rewrite size_union; [| set_solver ].
  rewrite size_singleton. lia.
Qed.

(* and the release counterpart: deleting never grows the set *)
Lemma size_del (r : string) (lks : gset string) : size (lks ∖ {[r]}) <= size lks.
Proof. apply subseteq_size. set_solver. Qed.

(* THE RELEASE STEP OF THE COUPLING: a set that CONTAINED the rank strictly
   shrinks, which is what takes [size lks <= S n] to [size (lks ∖ {[r]}) <= n]
   -- i.e. exactly pop_off's unwind premise. *)
Lemma size_del_lt (r : string) (lks : gset string) (n : nat) :
  r ∈ lks -> size lks <= S n -> size (lks ∖ {[r]}) <= n.
Proof.
  intros Hin Hle.
  rewrite size_difference; [| set_solver ].
  rewrite size_singleton.
  assert (0 < size lks).
  { destruct (decide (size lks = 0)) as [Hz | Hz]; [| lia ].
    apply size_empty_inv in Hz. set_solver. }
  lia.
Qed.

(* the coupling at level 0, as an equation -- pop_off's re-enable branch needs
   it in several places and it should not be re-derived at each *)
Lemma size_le_zero_empty (lks : gset string) : size lks <= 0 -> lks = ∅.
Proof. intros H. apply leibniz_equiv, size_empty_inv. lia. Qed.

(* the empty set fits under any level -- stated so a call site needs no
   [rewrite size_empty] whose LHS may not appear syntactically *)
Lemma size_empty_le (n : nat) : size (∅ : gset string) <= n.
Proof. rewrite size_empty. lia. Qed.

(* THE TWO COUPLING STEPS, stated so a call site needs no arithmetic of its
   own -- the proof files open [Z_scope], so a bare [lia] on these [nat] goals
   there is fighting the scope rather than the maths. *)
Lemma size_add_le (r : string) (lks : gset string) (n : nat) :
  r ∉ lks -> size lks <= n -> size ({[r]} ∪ lks) <= S n.
Proof. intros Hnin Hle. rewrite (size_add r lks Hnin). lia. Qed.

Lemma size_del_le (r : string) (lks : gset string) (n : nat) :
  size lks <= n -> size (lks ∖ {[r]}) <= n.
Proof. intros Hle. pose proof (size_del r lks). lia. Qed.

(* the two degenerate shapes the scheduler's literal singleton needs, for the
   same reason: keep [lock_rank] out of [set_solver]'s way. *)
Lemma locks_self_del (r : string) : ({[r]} : gset string) ∖ {[r]} = ∅.
Proof. set_solver. Qed.
Lemma locks_union_empty (r : string) : ({[r]} : gset string) ∪ ∅ = {[r]}.
Proof. set_solver. Qed.

(* the other half of the depth-0 story: a balanced release inside a body whose
   entry set is forced empty leaves [∅ ∖ {[r]}], which is [∅].  Proved at an
   ABSTRACT [X] so no call site ever runs [set_solver] against [lock_rank]'s
   fifteen-way [String.eqb] chain. *)
Lemma locks_empty_del (X : gset string) : (∅ : gset string) ∖ X = ∅.
Proof. set_solver. Qed.

(* the same at the premise a caller actually holds *)
Lemma locks_add_del_below (r : string) (lks : gset string) :
  locks_below lks r -> ({[r]} ∪ lks) ∖ {[r]} = lks.
Proof. intros Hb. apply locks_add_del, locks_below_not_elem, Hb. Qed.

(* the set a hart holds is a CHAIN: acquire's premise makes every new element
   strictly greater than everything present, so [locks_below] of the singleton
   below is all a nested caller ever states. *)
Lemma locks_below_singleton (r r' : string) :
  lock_rank r < lock_rank r' -> locks_below {[r]} r'.
Proof. intros Hlt q Hq. apply elem_of_singleton in Hq. subst q. exact Hlt. Qed.

(* THE CALL-SITE DISCHARGER.

   Every order premise a caller must supply has one of five shapes, and they
   nest: the held set is built by [∪ {[r]}] on acquire and [∖ {[r]}] on
   release, starting from either [∅] or the caller's own abstract [lks].  So
   the goal is always a tower of those constructors bottoming out in [∅] or in
   a [locks_below lks _] hypothesis already in scope, and the rank comparison
   at each layer is between two closed [lock_rank "..."] calls, which
   [vm_compute] settles.

   Do NOT reach for [set_solver] here.  [lock_rank] is a 15-way [String.eqb]
   chain and [set_solver]'s membership case analysis normalises every
   occurrence of it; see the note on [locks_add_del] above for what that
   costs.  This tactic never unfolds [lock_rank] except under [vm_compute] on
   a goal that is purely two numerals. *)
Ltac lkbelow_go :=
  first
    [ exact (locks_below_empty _)
    | assumption
    | apply locks_below_singleton; vm_compute; lia
    | apply locks_below_union_singleton; [ vm_compute; lia | lkbelow_go ]
    | apply locks_below_difference; lkbelow_go
    | match goal with
      | [ H : locks_below ?S ?r' |- locks_below ?S ?r ] =>
          apply (locks_below_mono S r' r H); vm_compute; lia
      end
      (* the depth-zero bodies keep [lks] in scope and carry [lks = ∅] as a
         hypothesis rather than substituting it away -- substituting breaks
         every later mention of [lks] in the script. *)
    | match goal with
      | [ H : ?S = ∅ |- locks_below ?S _ ] =>
          rewrite H; exact (locks_below_empty _)
      end ].

(* GUARDED, so that [all: try lkbelow] is a safe no-op on every goal that is
   not an order side-condition.  That is how the call sites use it: a caller
   whose callee raises the premise writes [all: try lkbelow.] after the
   [iApply], and a caller that already passed the premise as an explicit
   argument raises no such goal and is unaffected.  Without the guard the
   [assumption] branch above could close an unrelated goal. *)
Ltac lkbelow :=
  lazymatch goal with
  | |- locks_below _ _ => lkbelow_go
  end.
