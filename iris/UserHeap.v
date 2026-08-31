(* ===================================================================== *)
(* UserHeap.v -- A SEPARATION-LOGIC HEAP OVER USER MEMORY, IN TWO HALVES. *)
(*                                                                        *)
(* The U tier's memory has been an image VALUE ([M : gmap Z (bv 8)])*)
(* threaded through every contract as an equation.  That has no frame      *)
(* rule: a function touching ANY of it must say what happened to ALL of    *)
(* it, so a four-byte copyout propagates as [M' = umem_wr M a d bs]        *)
(* through every layer -- and the syscall dispatcher, which drops the      *)
(* window bounds SpecKwait and SpecSysWait both carry, makes `outside the  *)
(* window' empty, at which point nothing frames.  That is what blocks a    *)
(* verified [init]: it waits with a NULL status pointer, its text sits at  *)
(* address 0, and no layer above kwait says a null pointer wrote nothing.  *)
(*                                                                        *)
(* THE DESIGN: TWO ghost_maps per process, not one.                        *)
(*                                                                        *)
(*   the TEXT heap [γt]  -- every fragment PERSISTED at allocation, so its *)
(*     bytes are immutable and freely duplicable; the invariant knows its  *)
(*     addresses are on X pages, so holding [utext γt a b] IS the right to *)
(*     FETCH.                                                             *)
(*   the DATA heap [γd]  -- fragments EXCLUSIVE; the invariant knows its   *)
(*     addresses are on W pages, so holding [ubyte γd a b] IS the right to *)
(*     WRITE.                                                             *)
(*                                                                        *)
(* Splitting by SEGMENT rather than by ownership is what makes this        *)
(* simple, and it is honest about xv6: user programs never write their     *)
(* text and never execute their data -- no shared libraries, no dynamic    *)
(* code generation -- so the two halves are disjoint by construction and   *)
(* nothing is lost by refusing to mix them.  (An earlier cut used ONE heap *)
(* and recovered writability from a dfrac conflict against persisted       *)
(* fragments kept in the invariant.  It worked, but it had to prove what   *)
(* the gname now simply says, and it could not express FETCHABILITY at all *)
(* -- the split was by W, while a fetch needs X.)                          *)
(*                                                                        *)
(* THE PERMISSION MAP IS CONSUMED HERE AND NOWHERE ELSE.  It             *)
(* appears in this file, to decide the split at allocation and to state    *)
(* the two invariants; above it, a leaf takes [utext]/[ubyte] and never    *)
(* mentions a permission, a page, or a table.                             *)
(*                                                                        *)
(* WHAT THIS IS NOT YET.  [uheap] still names [M], so the image is   *)
(* not hidden; that is the next step, together with re-cutting the leaves  *)
(* so [uinstr]'s [uM_bytes M ...] clauses become [utext] and the load and  *)
(* store leaves' byte facts become [ubyte].  And the payoff for [init]     *)
(* needs the syscall arms to take the FOOTPRINT they write rather than     *)
(* state an equation -- separation logic LOCALIZES that obligation to each *)
(* syscall, it does not remove it, but a null pointer then hands over no   *)
(* fragments and init keeps its text by separation.                        *)
(*                                                                        *)
(* NO NEW GHOST CLASS: RiscvPtsto.v declares [riscvF_diskGS] the tree's    *)
(* unique [ghost_mapG Z (bv 8)], and both heaps are fresh                  *)
(* [ghost_map_alloc]s at it, so neither Σ nor adequacy moves.              *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvPtsto RiscvExtras.
Require Import UserPtTree.
Require Import UmodeMem UmodeArith UmodeAbi UmodeFetch.  (* [uva_canon] / [uint_moi] / [uva_canon_small] *)
Require Import UserPerm.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* §1 THE TWO ADDRESS CLASSES -- the only place the permission map is read.*)
(* ===================================================================== *)

Definition uw_addr (π : gmap (mword 27) uperm) (a : Z) : Prop :=
  exists q : uperm, uperm_at π (mword_of_int a : mword 64) = Some q /\ up_W q = true.

Definition ux_addr (π : gmap (mword 27) uperm) (a : Z) : Prop :=
  exists q : uperm, uperm_at π (mword_of_int a : mword 64) = Some q /\ up_X q = true.

Global Instance uw_addr_dec (π : gmap (mword 27) uperm) (a : Z) :
  Decision (uw_addr π a).
Proof.
  unfold uw_addr, uperm_at.
  destruct (π !! svpn_of (mword_of_int a : mword 64)) as [q |] eqn:E.
  - destruct (up_W q) eqn:Ew.
    + left. exists q. split; [ reflexivity | exact Ew ].
    + right. intros (q' & Hq' & Hw'). injection Hq' as <-.
      rewrite Ew in Hw'. discriminate.
  - right. intros (q' & Hq' & _). discriminate Hq'.
Defined.

Global Instance ux_addr_dec (π : gmap (mword 27) uperm) (a : Z) :
  Decision (ux_addr π a).
Proof.
  unfold ux_addr, uperm_at.
  destruct (π !! svpn_of (mword_of_int a : mword 64)) as [q |] eqn:E.
  - destruct (up_X q) eqn:Ex.
    + left. exists q. split; [ reflexivity | exact Ex ].
    + right. intros (q' & Hq' & Hx'). injection Hq' as <-.
      rewrite Ex in Hx'. discriminate.
  - right. intros (q' & Hq' & _). discriminate Hq'.
Defined.

(* THE SPLIT, made once at allocation.  Text is "executable and not
   writable" so the two halves are disjoint by construction; in xv6 that
   costs nothing, because exec maps text R+X and everything else R+W and no
   user page is ever both. *)
Definition utext_part (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) : gmap Z (bv 8) :=
  base.filter (fun kv : Z * bv 8 =>
                 ux_addr (pm) kv.1 /\ ~ uw_addr (pm) kv.1)
              (M).

Definition udata_part (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) : gmap Z (bv 8) :=
  base.filter (fun kv : Z * bv 8 => uw_addr (pm) kv.1) (M).

Lemma utext_part_sub (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) : utext_part M pm ⊆ M.
Proof. apply map_filter_subseteq. Qed.

Lemma udata_part_sub (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) : udata_part M pm ⊆ M.
Proof. apply map_filter_subseteq. Qed.

Lemma utext_udata_disjoint (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) : utext_part M pm ##ₘ udata_part M pm.
Proof.
  apply map_disjoint_spec. intros a b1 b2 H1 H2.
  apply map_lookup_filter_Some in H1 as [_ [_ Hn]].
  apply map_lookup_filter_Some in H2 as [_ Hy].
  exact (Hn Hy).
Qed.

Lemma utext_part_x (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (a : Z) :
  is_Some (utext_part M pm !! a) -> ux_addr (pm) a.
Proof.
  intros [b Hb]. apply map_lookup_filter_Some in Hb as [_ [Hx _]]. exact Hx.
Qed.

Lemma udata_part_w (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (a : Z) :
  is_Some (udata_part M pm !! a) -> uw_addr (pm) a.
Proof. intros [b Hb]. apply map_lookup_filter_Some in Hb as [_ Hw]. exact Hw. Qed.


(* THE DATA HALF SPLITS AT THE BREAK: what the process owns, and the SLACK
   the invariant keeps above it.  Same shape as the text/data split, and for
   the same reason -- a filter, so the big-op divides by [big_sepM_union]. *)
Definition udata_lo (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z) : gmap Z (bv 8) :=
  base.filter (fun kv : Z * bv 8 => kv.1 < sz) (udata_part M pm).

Definition udata_slack (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z) : gmap Z (bv 8) :=
  base.filter (fun kv : Z * bv 8 => sz <= kv.1) (udata_part M pm).

Lemma udata_lo_slack_disjoint (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z) :
  udata_lo M pm sz ##ₘ udata_slack M pm sz.
Proof.
  apply map_disjoint_spec. intros a b1 b2 H1 H2.
  apply map_lookup_filter_Some in H1 as [_ Hlt].
  apply map_lookup_filter_Some in H2 as [_ Hge].
  (* [lia] does not reduce the pair projection the filter's predicate is
     stated over; one [cbn] per hypothesis (durable-notes: [in H1, H2]
     reduces only in H1) *)
  cbn [fst] in Hlt. cbn [fst] in Hge. lia.
Qed.

Lemma udata_lo_slack_union (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z) :
  udata_lo M pm sz ∪ udata_slack M pm sz = udata_part M pm.
Proof.
  apply map_eq. intros a.
  destruct (udata_part M pm !! a) as [b |] eqn:Hb.
  - destruct (decide (a < sz)) as [Hlt | Hge].
    + rewrite lookup_union_l'.
      * apply map_lookup_filter_Some. split; [ exact Hb | exact Hlt ].
      * exists b. apply map_lookup_filter_Some. split; [ exact Hb | exact Hlt ].
    + rewrite lookup_union_r.
      * apply map_lookup_filter_Some. split; [ exact Hb | cbn [fst]; lia ].
      * apply map_lookup_filter_None. right. intros x Hx. rewrite Hb in Hx.
        injection Hx as <-. cbn [fst]. lia.
  - rewrite lookup_union_None. split; apply map_lookup_filter_None; left; exact Hb.
Qed.

Lemma udata_slack_above (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z) (a : Z) :
  is_Some (udata_slack M pm sz !! a) -> sz <= a.
Proof.
  intros [b Hb]. apply map_lookup_filter_Some in Hb as [_ Hge].
  cbn [fst] in Hge. exact Hge.
Qed.

(* One argv element: where the string is, how long it is, and what it says.
   A record rather than a triple so [uargv]'s list is readable and so the
   three fields can be named at a use site. *)
Record uarg : Type := UArg {
  ua_ptr   : Z;
  ua_len   : nat;
  ua_bytes : nat -> bv 8;
}.

Section UserHeap.
  Context `{!riscvGS Σ}.
  (* the break ghost's class.  It already exists in the tree --
     Xv6Cameras.uioG's [uio_brkG] is the same [ghost_varG Σ Z], introduced
     for the old tier's sbrk -- so nothing new enters Σ. *)
  Context `{!ghost_varG Σ Z}.

  (* ===================================================================== *)
  (* §2 THE TWO POINTS-TO FAMILIES.                                        *)
  (* ===================================================================== *)

  (* A TEXT byte.  PERSISTENT -- every text fragment is persisted when the
     heap is allocated -- so it is immutable and freely duplicable, which is
     exactly what an instruction fetch wants: the same bytes are read at
     every step, by every continuation, forever. *)
  Definition utext (γt : gname) (a : Z) (b : bv 8) : iProp Σ := (a ↪[γt]□ b)%I.

  (* A DATA byte AT A FRACTION.  [DfracOwn 1] is the right to WRITE it --
     [ubyte], what every store leaf and every stack word wants.
     [DfracDiscarded] is a permanent READ-ONLY view, and the argument
     vector is what needs it: two argv slots may legitimately point at the
     same string, and an exclusive byte cannot describe that at all.  With
     the read-only view the aliasing question simply does not arise, and
     the entry gate is spared a quadratic "the strings are pairwise
     disjoint" condition it would otherwise have to decide. *)
  Definition ubyteq (γd : gname) (dq : dfrac) (a : Z) (b : bv 8) : iProp Σ :=
    (a ↪[γd]{dq} b)%I.
  Definition ubyte (γd : gname) (a : Z) (b : bv 8) : iProp Σ :=
    ubyteq γd (DfracOwn 1) a b.

  Global Instance ubyteq_timeless γd dq a b : Timeless (ubyteq γd dq a b).
  Proof. apply _. Qed.
  Global Instance ubyteq_persistent γd a b :
    Persistent (ubyteq γd DfracDiscarded a b).
  Proof. apply _. Qed.

  Global Instance utext_persistent γt a b : Persistent (utext γt a b).
  Proof. apply _. Qed.

  Global Instance ubyte_timeless γd a b : Timeless (ubyte γd a b).
  Proof. apply _. Qed.

  (* ===================================================================== *)
  (* §2b WORDS AND STRINGS, over [ubyte].                                  *)
  (*                                                                       *)
  (* Everything a program says about its data is a run of bytes, so nothing *)
  (* here is primitive: a word is eight consecutive [ubyte]s and a string   *)
  (* is its bytes followed by the NUL.  Stating them this way rather than   *)
  (* as new resources is what makes them SPLIT and RECOMBINE for free --    *)
  (* which is what a syscall footprint needs, since the range the kernel is *)
  (* handed rarely coincides with a program-level object.                   *)
  (* ===================================================================== *)

  (* [n] consecutive bytes, the shape everything else is built from *)
  Definition ubytesq (γd : gname) (dq : dfrac) (a : Z) (n : nat)
      (f : nat -> bv 8) : iProp Σ :=
    ([∗ list] j ∈ seq 0 n, ubyteq γd dq (a + Z.of_nat j) (f j))%I.
  Definition ubytes (γd : gname) (a : Z) (n : nat) (f : nat -> bv 8) : iProp Σ :=
    ubytesq γd (DfracOwn 1) a n f.

  (* an 8-byte little-endian word, as the load and store leaves read it *)
  Definition uwordq (γd : gname) (dq : dfrac) (a : Z) (w : mword 64) : iProp Σ :=
    ubytesq γd dq a 8 (nth_byte w).
  Definition uword (γd : gname) (a : Z) (w : mword 64) : iProp Σ :=
    uwordq γd (DfracOwn 1) a w.

  Global Instance ubytesq_persistent γd a n f :
    Persistent (ubytesq γd DfracDiscarded a n f).
  Proof. apply _. Qed.
  Global Instance uwordq_persistent γd a w :
    Persistent (uwordq γd DfracDiscarded a w).
  Proof. apply _. Qed.

  (* A NUL-TERMINATED C STRING of length [len] at [a]: [len] bytes NONE of
     which is NUL, then the terminator.  The no-interior-NUL clause is part
     of the PREDICATE rather than a side condition on the functions that
     walk it, so [ustr γd a len f] pins the length: it is what makes
     "strlen returns len" a statement about the resource the caller holds
     rather than about an extra hypothesis it also had to supply. *)
  Definition ustr (γd : gname) (dq : dfrac) (a : Z) (len : nat)
      (f : nat -> bv 8) : iProp Σ :=
    (⌜ forall j : nat, (j < len)%nat -> f j <> ubyte0 ⌝ ∗
     (* ...and the length is REPRESENTABLE.  strlen computes it with a
        32-bit [subw], so a string longer than 2^31 is not one this ABI can
        measure; that belongs to what a string IS, not to strlen's caller. *)
     ⌜ Z.of_nat len < 2 ^ 31 ⌝ ∗
     ubytesq γd dq a len f ∗ ubyteq γd dq (a + Z.of_nat len) ubyte0)%I.

  Global Instance ustr_persistent γd a len f :
    Persistent (ustr γd DfracDiscarded a len f).
  Proof. apply _. Qed.

  Lemma ustr_len (γd : gname) (dq : dfrac) (a : Z) (len : nat) (f : nat -> bv 8) :
    ustr γd dq a len f -∗ ⌜ Z.of_nat len < 2 ^ 31 ⌝.
  Proof. iIntros "(_ & %H & _ & _)". iPureIntro. exact H. Qed.

  Lemma ustr_nonul (γd : gname) (dq : dfrac) (a : Z) (len : nat) (f : nat -> bv 8) :
    ustr γd dq a len f -∗ ⌜ forall j : nat, (j < len)%nat -> f j <> ubyte0 ⌝.
  Proof. iIntros "(%H & _ & _ & _)". iPureIntro. exact H. Qed.

  (* one body byte, out and back *)
  Lemma ustr_byte (γd : gname) (dq : dfrac) (a : Z) (len : nat)
      (f : nat -> bv 8) (j : nat) :
    (j < len)%nat ->
    ustr γd dq a len f -∗
      ubyteq γd dq (a + Z.of_nat j)%Z (f j) ∗
      (ubyteq γd dq (a + Z.of_nat j)%Z (f j) -∗ ustr γd dq a len f).
  Proof.
    intros Hj. iIntros "(#Hne & #Hlen & Hbs & Hnul)".
    rewrite /ustr /ubytesq.
    iDestruct (big_sepL_lookup_acc _ _ j j with "Hbs") as "[Hb Hcl]";
      [ apply lookup_seq; split; [ lia | exact Hj ] | ].
    iFrame "Hb". iIntros "Hb".
    iFrame "Hne Hlen Hnul". iApply ("Hcl" with "Hb").
  Qed.

  (* ...and the terminator *)
  Lemma ustr_nul (γd : gname) (dq : dfrac) (a : Z) (len : nat) (f : nat -> bv 8) :
    ustr γd dq a len f -∗
      ubyteq γd dq (a + Z.of_nat len)%Z ubyte0 ∗
      (ubyteq γd dq (a + Z.of_nat len)%Z ubyte0 -∗ ustr γd dq a len f).
  Proof.
    iIntros "(#Hne & #Hlen & Hbs & Hnul)". iFrame "Hnul". iIntros "Hnul".
    rewrite /ustr. iFrame "Hne Hlen Hbs Hnul".
  Qed.

  (* ===================================================================== *)
  (* A STRING IN THE TEXT HALF.  [ustr] is the DATA half's string, and a    *)
  (* program's string LITERALS are not there: .rodata shares the            *)
  (* executable segment's pages, so its bytes are X-and-not-W and belong to *)
  (* [γt].  init's four format strings live at 0x970..0x9e7, inside the R-X *)
  (* segment, and vprintf LOADS them one byte at a time -- so the tier      *)
  (* needs both this resource and [UkRunMem.wp_uk_lbu_text] to read it.     *)
  (*                                                                       *)
  (* It carries no dfrac: [utext] is [↪□], persistent outright, so there is *)
  (* nothing to give back and the accessors below hand out bytes without a  *)
  (* closing wand.                                                         *)
  (* ===================================================================== *)
  Definition utext_str (γt : gname) (a : Z) (len : nat)
      (f : nat -> bv 8) : iProp Σ :=
    (⌜ forall j : nat, (j < len)%nat -> f j <> ubyte0 ⌝ ∗
     ⌜ Z.of_nat len < 2 ^ 31 ⌝ ∗
     ([∗ list] j ∈ seq 0 len, utext γt (a + Z.of_nat j) (f j)) ∗
     utext γt (a + Z.of_nat len) ubyte0)%I.

  Global Instance utext_str_persistent γt a len f :
    Persistent (utext_str γt a len f).
  Proof. apply _. Qed.

  Lemma utext_str_len (γt : gname) (a : Z) (len : nat) (f : nat -> bv 8) :
    utext_str γt a len f -∗ ⌜ Z.of_nat len < 2 ^ 31 ⌝.
  Proof. iIntros "(_ & %H & _ & _)". iPureIntro. exact H. Qed.

  Lemma utext_str_nonul (γt : gname) (a : Z) (len : nat) (f : nat -> bv 8) :
    utext_str γt a len f -∗ ⌜ forall j : nat, (j < len)%nat -> f j <> ubyte0 ⌝.
  Proof. iIntros "(%H & _ & _ & _)". iPureIntro. exact H. Qed.

  (* one body byte -- no give-back, the resource is persistent *)
  Lemma utext_str_byte (γt : gname) (a : Z) (len : nat)
      (f : nat -> bv 8) (j : nat) :
    (j < len)%nat ->
    utext_str γt a len f -∗ utext γt (a + Z.of_nat j)%Z (f j).
  Proof.
    intros Hj. iIntros "(_ & _ & #Hbs & _)".
    iApply (big_sepL_lookup _ _ j j with "Hbs").
    apply lookup_seq. split; [ lia | exact Hj ].
  Qed.

  Lemma utext_str_nul (γt : gname) (a : Z) (len : nat) (f : nat -> bv 8) :
    utext_str γt a len f -∗ utext γt (a + Z.of_nat len)%Z ubyte0.
  Proof. iIntros "(_ & _ & _ & #H)". iExact "H". Qed.

  (* NOTE: the SPLIT of a run at an arbitrary point -- which is what a
     syscall footprint hand-over is -- is deliberately not here yet.  It is
     a step-3 tool and wants proving against its consumer, not before it. *)

  (* ===================================================================== *)
  (* §2b'' READ-ONLY VIEWS: persisting bytes, and reading them back.        *)
  (*                                                                        *)
  (* Once an area is persisted, ANY number of views of it may be handed     *)
  (* out and none of them has to be disjoint from any other.  That is the   *)
  (* whole reason the argument vector is read-only: exec may point two      *)
  (* argv slots at the same string, and nothing above has to decide         *)
  (* whether it did.                                                        *)
  (* ===================================================================== *)
  Lemma ubyte_persist (γd : gname) (a : Z) (b : bv 8) :
    ubyte γd a b ==∗ ubyteq γd DfracDiscarded a b.
  Proof. iIntros "H". iApply (ghost_map_elem_persist with "H"). Qed.

  Lemma uarea_persist (γd : gname) (A : gmap Z (bv 8)) :
    ([∗ map] k ↦ b ∈ A, ubyte γd k b) ==∗
    ([∗ map] k ↦ b ∈ A, ubyteq γd DfracDiscarded k b).
  Proof.
    iIntros "H". iApply big_sepM_bupd.
    iApply (big_sepM_impl with "H"). iIntros "!>" (k b _) "Hb".
    iApply (ghost_map_elem_persist with "Hb").
  Qed.

  Lemma ubytesq_of_pmap (γd : gname) (A : gmap Z (bv 8)) (a : Z) (n : nat)
      (f : nat -> bv 8) :
    (forall j : nat, (j < n)%nat -> A !! (a + Z.of_nat j)%Z = Some (f j)) ->
    ([∗ map] k ↦ b ∈ A, ubyteq γd DfracDiscarded k b) -∗
      ubytesq γd DfracDiscarded a n f.
  Proof.
    intros HA. iIntros "#HA". rewrite /ubytesq.
    iApply big_sepL_intro. iIntros "!>" (i j Hij).
    apply lookup_seq in Hij as [Hj Hlt].
    assert (Hji : j = i) by lia. subst j.
    iApply (big_sepM_lookup with "HA"). exact (HA i Hlt).
  Qed.

  Lemma uwordq_of_pmap (γd : gname) (A : gmap Z (bv 8)) (a : Z) (w : mword 64) :
    (forall j : nat, (j < 8)%nat ->
       A !! (a + Z.of_nat j)%Z = Some (nth_byte w j)) ->
    ([∗ map] k ↦ b ∈ A, ubyteq γd DfracDiscarded k b) -∗
      uwordq γd DfracDiscarded a w.
  Proof.
    intros HA. rewrite /uwordq.
    exact (ubytesq_of_pmap γd A a 8 (nth_byte w) HA).
  Qed.

  Lemma ustr_of_pmap (γd : gname) (A : gmap Z (bv 8)) (a : Z) (len : nat)
      (f : nat -> bv 8) :
    (forall j : nat, (j < len)%nat -> f j <> ubyte0) ->
    Z.of_nat len < 2 ^ 31 ->
    (forall j : nat, (j < len)%nat -> A !! (a + Z.of_nat j)%Z = Some (f j)) ->
    A !! (a + Z.of_nat len)%Z = Some ubyte0 ->
    ([∗ map] k ↦ b ∈ A, ubyteq γd DfracDiscarded k b) -∗
      ustr γd DfracDiscarded a len f.
  Proof.
    intros Hne Hlen HA Hnul. iIntros "#HA". rewrite /ustr.
    iSplit; [ iPureIntro; exact Hne | ].
    iSplit; [ iPureIntro; exact Hlen | ].
    iSplit; [ iApply (ubytesq_of_pmap γd A a len f HA with "HA") | ].
    iApply (big_sepM_lookup with "HA"). exact Hnul.
  Qed.

  (* THE CARVE, NON-LOSSY.  [ubytes_of_map] consumes the whole map; a
     program that wants BOTH a stack and an argument area needs the rest
     back.  Splitting at a decidable cut is what gives it: everything below
     the entry sp is frame territory, everything at or above it is where
     exec left the arguments ([UkAbi.uk_args]'s [uka_lo] is exactly that
     cut), and [big_sepM_union] divides the ownership along it. *)
  Lemma umap_split_at (γd : gname) (D : gmap Z (bv 8)) (c : Z) :
    ([∗ map] k ↦ b ∈ D, ubyte γd k b) -∗
      ([∗ map] k ↦ b ∈ base.filter (fun kv : Z * bv 8 => kv.1 < c) D,
         ubyte γd k b) ∗
      ([∗ map] k ↦ b ∈ base.filter (fun kv : Z * bv 8 => ~ (kv.1 < c)) D,
         ubyte γd k b).
  Proof.
    iIntros "H".
    rewrite -(big_sepM_union (fun k b => ubyte γd k b)
                (base.filter (fun kv : Z * bv 8 => kv.1 < c) D)
                (base.filter (fun kv : Z * bv 8 => ~ (kv.1 < c)) D)
                (map_disjoint_filter_complement _ D)).
    rewrite (map_filter_union_complement (fun kv : Z * bv 8 => kv.1 < c) D).
    iExact "H".
  Qed.

  Lemma umap_filter_lookup_lt (D : gmap Z (bv 8)) (c a : Z) (b : bv 8) :
    a < c -> D !! a = Some b ->
    base.filter (fun kv : Z * bv 8 => kv.1 < c) D !! a = Some b.
  Proof.
    intros Hlt Hb. apply map_lookup_filter_Some. split; [ exact Hb | ].
    cbn [fst]. exact Hlt.
  Qed.

  Lemma umap_filter_lookup_ge (D : gmap Z (bv 8)) (c a : Z) (b : bv 8) :
    ~ (a < c) -> D !! a = Some b ->
    base.filter (fun kv : Z * bv 8 => ~ (kv.1 < c)) D !! a = Some b.
  Proof.
    intros Hge Hb. apply map_lookup_filter_Some. split; [ exact Hb | ].
    cbn [fst]. exact Hge.
  Qed.

  (* ===================================================================== *)
  (* §2b' THE ARGUMENT VECTOR.                                             *)
  (*                                                                       *)
  (* [uargv γd av args] owns the argv ARRAY at [av] -- one 8-byte pointer   *)
  (* per element -- TOGETHER WITH the string each pointer points at.  That  *)
  (* pairing is the point: a program that walks argv reads a word out of    *)
  (* the array and immediately wants a [ustr] for it, and with the two      *)
  (* apart the caller would have to supply a side condition of its own      *)
  (* saying that every element points at a string.                          *)
  (*                                                                       *)
  (* The array's own alignment lives in the resource for the same reason    *)
  (* [ustack]'s does: the [ld] that reads a slot needs it, and it is a      *)
  (* property of the vector, not of the function reading it.               *)
  (* ===================================================================== *)
  Definition uargv (γd : gname) (av : Z) (args : list uarg) : iProp Σ :=
    (⌜ av mod 8 = 0 ⌝ ∗
     (* ...and the COUNT is representable.  main scales the index with a
        32-bit [addiw]/[slli]/[srli] idiom, so an argv longer than 2^31 is
        not one this ABI can describe -- the same reason [ustr] carries its
        own length bound rather than making every walker state it. *)
     ⌜ Z.of_nat (length args) < 2 ^ 31 ⌝ ∗
     [∗ list] i ↦ g ∈ args,
        uwordq γd DfracDiscarded (av + 8 * Z.of_nat i)
          (mword_of_int (ua_ptr g)) ∗
        ustr γd DfracDiscarded (ua_ptr g) (ua_len g) (ua_bytes g))%I.

  Global Instance uargv_persistent γd av args : Persistent (uargv γd av args).
  Proof. apply _. Qed.

  Lemma uargv_align (γd : gname) (av : Z) (args : list uarg) :
    uargv γd av args -∗
    ⌜ av mod 8 = 0 /\ Z.of_nat (length args) < 2 ^ 31 ⌝.
  Proof. iIntros "(%H & %H2 & _)". iPureIntro. split; assumption. Qed.

  (* one element, out and back *)
  Lemma uargv_acc (γd : gname) (av : Z) (args : list uarg) (i : nat) (g : uarg) :
    args !! i = Some g ->
    uargv γd av args -∗
      (uwordq γd DfracDiscarded (av + 8 * Z.of_nat i)
         (mword_of_int (ua_ptr g)) ∗
       ustr γd DfracDiscarded (ua_ptr g) (ua_len g) (ua_bytes g)) ∗
      ((uwordq γd DfracDiscarded (av + 8 * Z.of_nat i)
          (mword_of_int (ua_ptr g)) ∗
        ustr γd DfracDiscarded (ua_ptr g) (ua_len g) (ua_bytes g)) -∗
         uargv γd av args).
  Proof.
    intros Hi. iIntros "(#Hal & #Hn & Hl)".
    iDestruct (big_sepL_lookup_acc _ _ i g Hi with "Hl") as "[Hg Hcl]".
    iFrame "Hg". iIntros "Hg". iFrame "Hal Hn". iApply "Hcl". iExact "Hg".
  Qed.


  (* ===================================================================== *)
  (* §2c THE PROGRAM BREAK, as a ghost the caller can FRAME.               *)
  (*                                                                       *)
  (* Half here, half in [uheap]: the two must agree, and moving the break    *)
  (* takes both.  A ghost rather than an argument of [uheap] precisely so    *)
  (* that a function which does not call sbrk carries its half through      *)
  (* untouched and never mentions [sz] in its spec at all.                  *)
  (* ===================================================================== *)
  Definition usz (γs : gname) (sz : Z) : iProp Σ := ghost_var γs (1/2) sz.

  Lemma usz_agree (γs : gname) (sz sz' : Z) :
    usz γs sz -∗ usz γs sz' -∗ ⌜ sz = sz' ⌝.
  Proof.
    iIntros "H1 H2". iDestruct (ghost_var_agree with "H1 H2") as %->. done.
  Qed.

  Lemma usz_update (γs : gname) (sz sz' sz'' : Z) :
    usz γs sz -∗ usz γs sz' ==∗ usz γs sz'' ∗ usz γs sz''.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %->.
    iMod (ghost_var_update_2 sz'' with "H1 H2") as "[$ $]"; [ | done ].
    rewrite Qp.half_half. reflexivity.
  Qed.

  (* ===================================================================== *)
  (* §3 THE HEAP INVARIANT.                                             *)
  (*                                                                       *)
  (* Two authorities against one image, with the segment facts that make    *)
  (* each half's points-to mean what it means.                             *)
  (* ===================================================================== *)
  Definition uheap (γt γd γs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) : iProp Σ :=
    (∃ (Mt Md Mslack : gmap Z (bv 8)) (sz : Z),
       ⌜ Mt ⊆ M ⌝ ∗ ⌜ Md ⊆ M ⌝ ∗ ⌜ Mt ##ₘ Md ⌝ ∗
       (* CANONICITY, ONCE FOR THE WHOLE ADDRESS SPACE.  Every mapped user
          address is below MAXVA, hence Sv39-canonical.  Stating it here
          rather than per access is what stops [uinstr]'s [ui_canon] and the
          [uva_canon] output of every data reader ([uk_rd_byte],
          [uk_args_slot], [uk_stack_slot]) from each re-deriving it. *)
       ⌜ forall a : Z, is_Some (M !! a) -> 0 <= a < 2 ^ 38 ⌝ ∗
       ⌜ forall a : Z, is_Some (Mt !! a) -> ux_addr (pm) a ⌝ ∗
       ⌜ forall a : Z, is_Some (Md !! a) -> uw_addr (pm) a ⌝ ∗
       ghost_map_auth γt 1 Mt ∗ ghost_map_auth γd 1 Md ∗
       (* THE BREAK, and THE SLACK ABOVE IT.  NOTE [0 <= sz] is deliberately
          NOT asserted: the bundle carries only [usz_ok sz], which does not
          rule out a negative break, and nothing here needs it -- addresses
          are bounded by the canonicity clause above.  Add it back when a
          source for it appears (sbrk will want it).  The kernel's image grows and
          shrinks by whole PAGES while [sz] moves by bytes, so the invariant
          holds the bytes between the break and the next page boundary.
          That is what lets the user-facing sbrk be BYTE-granular: [sbrk 8]
          hands out eight bytes off the slack whether or not a fresh page
          came from the kernel, and [sbrk (-8)] takes eight back into it. *)
       ghost_var γs (1/2) sz ∗
       ⌜ forall a : Z, is_Some (Mslack !! a) -> sz <= a ⌝ ∗
       ([∗ map] a ↦ b ∈ Mslack, ubyte γd a b))%I.

  (* the canonicity fact in the shape an access wants: the address round-trips
     through [mword_of_int] and the word is Sv39-canonical *)
  Lemma ucanon_of_bound (a : Z) :
    0 <= a < 2 ^ 38 ->
    uint (mword_of_int a : mword 64) = a /\ uva_canon (mword_of_int a : mword 64).
  Proof.
    intros Hb. change (2 ^ 38) with 274877906944 in Hb.
    assert (Hu : uint (mword_of_int a : mword 64) = a)
      by (apply uint_moi; unfold Z64; lia).
    split; [ exact Hu | ].
    apply uva_canon_small. rewrite <- uint_unsigned, Hu. lia.
  Qed.

  (* A TEXT byte names the byte the image holds, and its page is FETCHABLE.
     Both come straight off the text half's invariant -- no dfrac argument,
     no permission in the statement. *)
  Lemma uheap_text (γt γd γs : gname) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (a : Z) (b : bv 8) :
    uheap γt γd γs M pm -∗ utext γt a b -∗
    ⌜ M !! a = Some b /\ ux_addr (pm) a /\ 0 <= a < 2 ^ 38 ⌝.
  Proof.
    iIntros "Hrun Hb".
    iDestruct "Hrun" as (Mt Md Mslack sz)
      "(%Hst & %Hsd & %Hdisj & %Hcan & %Hx & %Hw & Ht & Hd & Hszg & %Hsl & Hslack)".
    iDestruct (ghost_map_lookup with "Ht Hb") as %HMt.
    assert (HM : M !! a = Some b)
      by exact (proj1 (map_subseteq_spec Mt (M)) Hst a b HMt).
    (* NOTE: not [split_and!] -- it would split [0 <= a < 2 ^ 38] too *)
    iPureIntro. split; [ exact HM | ].
    split; [ exact (Hx a (mk_is_Some _ _ HMt)) | exact (Hcan a (mk_is_Some _ _ HM)) ].
  Qed.

  (* ...and a DATA byte names its byte and its page is WRITABLE. *)
  Lemma uheap_ubyte (γt γd γs : gname) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (dq : dfrac) (a : Z) (b : bv 8) :
    uheap γt γd γs M pm -∗ ubyteq γd dq a b -∗
    ⌜ M !! a = Some b /\ uw_addr (pm) a /\ 0 <= a < 2 ^ 38 ⌝.
  Proof.
    iIntros "Hrun Hb".
    iDestruct "Hrun" as (Mt Md Mslack sz)
      "(%Hst & %Hsd & %Hdisj & %Hcan & %Hx & %Hw & Ht & Hd & Hszg & %Hsl & Hslack)".
    iDestruct (ghost_map_lookup with "Hd Hb") as %HMd.
    assert (HM : M !! a = Some b)
      by exact (proj1 (map_subseteq_spec Md (M)) Hsd a b HMd).
    iPureIntro. split; [ exact HM | ].
    split; [ exact (Hw a (mk_is_Some _ _ HMd)) | exact (Hcan a (mk_is_Some _ _ HM)) ].
  Qed.

  (* THE STORE.  An exclusively-owned data byte may be replaced and the
     key's image moves with it.  The text half is untouched, and it stays a
     SUBMAP because the two halves are disjoint -- which is the whole reason
     they are two heaps. *)
  Lemma uheap_store (γt γd γs : gname) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (a : Z) (b b' : bv 8) :
    uheap γt γd γs M pm -∗ ubyte γd a b ==∗
      uheap γt γd γs (<[a := b']> M) pm ∗ ubyte γd a b'.
  Proof.
    iIntros "Hrun Hb".
    iDestruct "Hrun" as (Mt Md Mslack sz)
      "(%Hst & %Hsd & %Hdisj & %Hcan & %Hx & %Hw & Ht & Hd & Hszg & %Hsl & Hslack)".
    iDestruct (ghost_map_lookup with "Hd Hb") as %HMd.
    assert (Hnt : Mt !! a = None)
      by exact (map_disjoint_Some_r Mt Md a b Hdisj HMd).
    iMod (ghost_map_update b' with "Hd Hb") as "[Hd Hb]".
    iModIntro. iFrame "Hb". iExists Mt, (<[a := b']> Md), Mslack, sz.
        iFrame "Ht Hd Hszg Hslack". iPureIntro. split_and!.
    - apply insert_subseteq_r; [ exact Hnt | exact Hst ].
    - apply insert_mono. exact Hsd.
    - apply map_disjoint_insert_r_2; [ exact Hnt | exact Hdisj ].
    - (* a store replaces a key that is already there, so the domain -- and
         with it the canonicity fact -- does not move *)
      intros k Hk. apply Hcan.
      destruct (decide (k = a)) as [-> | Hne].
      + exact (mk_is_Some _ _ (proj1 (map_subseteq_spec Md (M)) Hsd a b HMd)).
      + rewrite lookup_insert_ne in Hk; [ exact Hk | exact (not_eq_sym Hne) ].
    - exact Hx.
    - intros k Hk. apply Hw.
      destruct (decide (k = a)) as [-> | Hne].
      + exact (mk_is_Some _ _ HMd).
      + rewrite lookup_insert_ne in Hk; [ exact Hk | exact (not_eq_sym Hne) ].
    (* the break and the slack are untouched: a store moves one DATA byte the
       process owns, and the slack is what the invariant owns above the break *)
    - exact Hsl.
  Qed.

  (* ===================================================================== *)
  (* §4 ALLOCATION -- the process's FIRST WP.                              *)
  (*                                                                       *)
  (* Two [ghost_map_alloc]s at the segment split, and the text half is      *)
  (* PERSISTED on the spot: after this step nothing can ever write it, and  *)
  (* every continuation may read it without owning anything.                *)
  (* ===================================================================== *)
  Lemma uheap_alloc (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z) :
    (* THE ONE PREMISE, and where it comes from: every mapped user address is
       below MAXVA.  At the call site (the process's first WP) [uvb] carries
       [usz_ok sz] and the lazy image over the sz-region, which is what bounds
       the image's keys; it is taken here rather than re-derived so that this
       file stays independent of the bundle. *)
    (forall a : Z, is_Some (M !! a) -> 0 <= a < 2 ^ 38) ->
    ⊢ |==> ∃ γt γd γs : gname,
        uheap γt γd γs M pm ∗ usz γs sz ∗
        ([∗ map] a ↦ b ∈ utext_part M pm, utext γt a b) ∗
        ([∗ map] a ↦ b ∈ udata_lo M pm sz, ubyte γd a b).
  Proof.
    intros Hcan.
    iMod (ghost_map_alloc (utext_part M pm)) as (γt) "[Htauth Htfrag]".
    iMod (ghost_map_alloc (udata_part M pm)) as (γd) "[Hdauth Hdfrag]".
    iMod (ghost_var_alloc sz) as (γs) "Hsz".
    iEval (rewrite -Qp.half_half) in "Hsz".
    iDestruct (ghost_var_split with "Hsz") as "[HszA HszF]".
    (* PERSIST the text half.  After this step nothing can ever write it, and
       every continuation may read it without owning anything. *)
    iAssert (|==> [∗ map] a ↦ b ∈ utext_part M pm, utext γt a b)%I
      with "[Htfrag]" as ">#Htp".
    { iApply big_sepM_bupd. iApply (big_sepM_impl with "Htfrag").
      iIntros "!>" (a b _) "H". rewrite /utext.
      iApply (ghost_map_elem_persist with "H"). }
    (* ...and divide the data half at the break: the process gets what is
       below it, the invariant keeps the slack above. *)
    iEval (rewrite -(udata_lo_slack_union M pm sz)) in "Hdfrag".
    rewrite big_sepM_union; [ | apply udata_lo_slack_disjoint ].
    iDestruct "Hdfrag" as "[Hlo Hslack]".
    iModIntro. iExists γt, γd, γs.
    iSplitL "Htauth Hdauth HszA Hslack";
      [ | iFrame "HszF"; iFrame "Hlo"; iFrame "Htp" ].
    iExists (utext_part M pm), (udata_part M pm), (udata_slack M pm sz), sz.
    iFrame "Htauth Hdauth HszA Hslack". iPureIntro. split_and!.
    - apply utext_part_sub.
    - apply udata_part_sub.
    - apply utext_udata_disjoint.
    - exact Hcan.
    - exact (utext_part_x M pm).
    - exact (udata_part_w M pm).
    - exact (udata_slack_above M pm sz).
  Qed.

  (* ===================================================================== *)
  (* §4c THE WINDOW STORE -- the re-assembly a syscall return is.           *)
  (*                                                                       *)
  (* This is the shape of the whole trap seam.  At a trap the kernel is     *)
  (* given back its [user_ptm_inv] over the same bytes; when it returns,    *)
  (* its own spec says PRECISELY how the image moved, and [uheap] has to be  *)
  (* re-established at the new one.  For a syscall that writes a window     *)
  (* that is exactly this lemma -- and it demands the caller OWNED the      *)
  (* window, which is why a program's spec for such a syscall asks for the  *)
  (* range up front.                                                        *)
  (*                                                                        *)
  (* THE FRAME IS THE POINT: nothing outside the window is mentioned, so    *)
  (* every other fact the process holds about its memory survives by        *)
  (* separation rather than by an equation someone has to keep precise.     *)
  (* A syscall handed a null pointer writes NO window, takes NO fragments,  *)
  (* and this lemma is not even needed.                                     *)
  (* ===================================================================== *)
  Lemma uheap_store_run (γt γd γs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (a : Z) (n : nat) (f g : nat -> bv 8) :
    uheap γt γd γs M pm -∗ ubytes γd a n f ==∗
      uheap γt γd γs (umem_write M a n g) pm ∗ ubytes γd a n g.
  Proof.
    iInduction n as [ | k IH ] "IH" forall (M).
    { iIntros "Hrun _". iModIntro. iFrame "Hrun". rewrite /ubytes /ubytesq /=. done. }
    iIntros "Hrun Hbs".
    (* peel the LAST byte -- [umem_write] writes it outermost.  [iEval ... in]
       rather than a bare [rewrite]: the proofmode's [rewrite] acts on the
       WHOLE entailment, and putting the goal in split form here would leave
       nothing to re-assemble at the end. *)
    iEval (rewrite /ubytes /ubytesq seq_S big_sepL_app /=) in "Hbs".
    iDestruct "Hbs" as "[Hlo [Hhi _]]".
    iMod ("IH" $! M with "Hrun Hlo") as "[Hrun Hlo]".
    iMod (uheap_store with "Hrun Hhi") as "[Hrun Hhi]".
    iModIntro. iFrame "Hrun".
    iEval (rewrite /ubytes /ubytesq seq_S big_sepL_app /=).
    iFrame "Hlo Hhi".
  Qed.

  (* ===================================================================== *)
  (* §5 THE INSTRUCTION RESOURCE.                                          *)
  (*                                                                       *)
  (* WHY NOT [uinstr].  This file imports UmodeMem, so that name would     *)
  (* SHADOW the Prop-level one, and any downstream file holding both        *)
  (* (UkStep.v uses it heavily) would silently pick up the wrong one -- so  *)
  (* the two have to coexist under distinct names until the re-cut is done, *)
  (* at which point the Prop is deleted and this can take the plain name.   *)
  (*                                                                       *)
  (* [UmodeMem.uinstr] is a five-clause PROP about a table and an image;    *)
  (* this is the same thing as an iProp over the text heap, and it is       *)
  (* SHORTER, because three of those clauses were only ever making up for   *)
  (* the absence of a per-byte permission:                                  *)
  (*                                                                       *)
  (*   ui_al2     kept -- the one piece of pure geometry left               *)
  (*   ui_canon   GONE -- [uheap]'s "every mapped address is below MAXVA"    *)
  (*                covers it, and covers data addresses at the same time   *)
  (*   ui_leaf    GONE -- [uheap_text] yields [ux_addr] PER FRAGMENT, so     *)
  (*                every byte brings its own fetchability                  *)
  (*   ui_inpage  GONE -- with per-byte evidence a fetch window that        *)
  (*                STRADDLES A PAGE needs nothing extra; that clause       *)
  (*                existed only so ONE table leaf could cover four bytes   *)
  (*   ui_code    the [uM_bytes] clauses become the fragments themselves    *)
  (*                                                                       *)
  (* This is the kernel's [InstrBytes.instr] shape with [utext] where it    *)
  (* has [↦ₓ□], and for the same reason: a fetchable-byte points-to is the  *)
  (* whole permission, one byte at a time.  Like the kernel's, it is        *)
  (* PERSISTENT -- the same bytes are read at every step, by every          *)
  (* continuation, forever, with nothing owned.                             *)
  (*                                                                       *)
  (* The RVC-at-4-ALIGNED case follows the kernel too: rather than          *)
  (* [uinstr]'s trailing "if 4-aligned there are two more bytes"            *)
  (* implication, the window IS a 4-byte word whose low half is the         *)
  (* halfword -- which is exactly what UmodeFetch's surviving [urvc4_word]  *)
  (* builds and [urvc4_low] projects.                                       *)
  (*                                                                       *)
  (* NOTE THE ADDRESSING: fragments are keyed at [uint pc + j] in [Z], not  *)
  (* at [uint (add_vec_int pc j)].  That sidesteps wrap inside the          *)
  (* definition, and it is where the page-crossing fetch gets the           *)
  (* [uint (add_vec_int pc 2) = uint pc + 2] it needs -- [uheap] bounds      *)
  (* those addresses, so the two agree.                                     *)
  (* ===================================================================== *)
  Definition uinstr_is (γt : gname) (pc : mword 64) (is_rvc : bool)
      (i : instruction) : iProp Σ :=
    (⌜ is_aligned_vaddr (Virtaddr pc) 2 = true ⌝ ∗
     (* TEMPORARY, and it is the LAST one.  Nothing in the fetch path needs
        this any more; its single remaining consumer is
        [UkStep.uk_instr_mapped], which transports the fetch bytes from the
        key's image to the MAPPED sub-image using the pc's one leaf.  Under
        the heap that transport has nothing to do -- each fragment carries
        its own page's evidence -- so the clause goes when the leaves stop
        routing through the Prop-level [uinstr].  It lives HERE rather than
        in a leaf statement because the decode lemmas discharge it for free,
        one [vm_compute] per pc. *)
     ⌜ Z.rem (uint pc) 4096 <= 4092 ⌝ ∗
     if is_rvc
     then ∃ h : mword 16,
            ⌜ isRVC h = true ⌝ ∗ ⌜ udecode_rvc h i ⌝ ∗
            if is_aligned_vaddr (Virtaddr pc) 4
            then ∃ w : mword 32, ⌜ subrange_vec_dec w 15 0 = h ⌝ ∗
                   [∗ list] j ∈ seq 0 4, utext γt (uint pc + Z.of_nat j) (nth_byte w j)
            else   [∗ list] j ∈ seq 0 2, utext γt (uint pc + Z.of_nat j) (nth_byte h j)
     else ∃ w : mword 32,
            ⌜ isRVC (subrange_vec_dec w 15 0) = false ⌝ ∗ ⌜ udecode_base w i ⌝ ∗
            [∗ list] j ∈ seq 0 4, utext γt (uint pc + Z.of_nat j) (nth_byte w j))%I.

  (* every byte of a text run is the byte the image holds -- the [uM_bytes]
     clause [uinstr] states, read off the fragments one at a time *)
  Lemma uheap_text_run {k : N} (γt γd γs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (a : Z) (n : nat) (w : bv k) :
    uheap γt γd γs M pm -∗
    ([∗ list] j ∈ seq 0 n, utext γt (a + Z.of_nat j) (nth_byte w j)) -∗
    ⌜ uM_bytes M a n w ⌝.
  Proof.
    iIntros "Hheap #Hbs".
    iInduction n as [ | k' IH ] "IH".
    { iPureIntro. intros j Hj. lia. }
    iEval (rewrite seq_S big_sepL_app /=) in "Hbs".
    iDestruct "Hbs" as "[#Hlo [#Hhi _]]".
    (* [iInduction] generalises the PERSISTENT hypothesis first, so the
       induction hypothesis takes the run before the heap *)
    iDestruct ("IH" with "Hlo Hheap") as %Hlo.
    iDestruct (uheap_text with "Hheap Hhi") as %(Hhi & _ & _).
    iPureIntro. intros j Hj.
    destruct (decide (j < k')%nat) as [Hlt | Hge]; [ exact (Hlo j Hlt) | ].
    assert (Hje : j = k') by lia. subst j. exact Hhi.
  Qed.

  Global Instance uinstr_is_persistent γt pc is_rvc i :
    Persistent (uinstr_is γt pc is_rvc i).
  Proof. rewrite /uinstr_is. destruct is_rvc; [ destruct (is_aligned_vaddr _ _) | ];
           apply _. Qed.


  (* ===================================================================== *)
  (* GETTING THE FRAGMENTS, and BUILDING [uinstr_is] OUT OF THEM.          *)
  (*                                                                       *)
  (* The entry hands a program [[∗ map] a ↦ b ∈ utext_part M pm, utext …]  *)
  (* -- its whole text, at once.  These are how a program turns that into  *)
  (* the per-instruction resource its leaves want, and they are the new    *)
  (* engine's replacement for the old [uk_instr_of_…] plumbing: one run    *)
  (* extraction plus one constructor per instruction.                      *)
  (*                                                                       *)
  (* [utext_part] wants X and NOT W, which is the disjointness that makes  *)
  (* the two heaps a partition.  A program with a concrete permission map  *)
  (* decides both.                                                         *)
  (* ===================================================================== *)
  (* A PROGRAM'S WHOLE TEXT, as one resource.  This is what the entry hands
     out and what a code catalog consumes; naming it keeps the [∗ map] out
     of every generated statement. *)
  Definition utext_all (γt : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) : iProp Σ :=
    ([∗ map] a ↦ b ∈ utext_part M pm, utext γt a b)%I.

  Global Instance utext_all_persistent γt M pm : Persistent (utext_all γt M pm).
  Proof. apply _. Qed.

  Lemma utext_frag (γt : gname) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm)
      (a : Z) (b : bv 8) :
    M !! a = Some b -> ux_addr pm a -> ~ uw_addr pm a ->
    utext_all γt M pm -∗ utext γt a b.
  Proof.
    intros HM Hx Hw. iIntros "Ht". rewrite /utext_all.
    iApply (big_sepM_lookup _ _ a b with "Ht").
    apply map_lookup_filter_Some. exact (conj HM (conj Hx Hw)).
  Qed.

  Lemma utext_run_of {k : N} (γt : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (a : Z) (n : nat) (w : bv k) :
    uM_bytes M a n w ->
    (forall j : nat, (j < n)%nat ->
       ux_addr pm (a + Z.of_nat j)%Z /\ ~ uw_addr pm (a + Z.of_nat j)%Z) ->
    utext_all γt M pm -∗
    ([∗ list] j ∈ seq 0 n, utext γt (a + Z.of_nat j) (nth_byte w j)).
  Proof.
    intros HM Hperm. iIntros "#Ht".
    iApply big_sepL_intro. iIntros "!>" (idx j Hj).
    apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l in Hlt |- *.
    destruct (Hperm idx Hlt) as [Hx Hw].
    iApply (utext_frag γt M pm _ _ (HM idx Hlt) Hx Hw with "Ht").
  Qed.

  (* ===================================================================== *)
  (* A PROGRAM'S TEXT KEYED BY ITS OWN DUMPED BYTE MAP.                     *)
  (*                                                                        *)
  (* [utext_all] names [M] and [pm], and a program proof cannot hold it:    *)
  (* [UkRun.urun] hides both existentially.  That is the whole reason the   *)
  (* code catalogs used to bundle their per-pc [uinstr_is] facts into ONE   *)
  (* wide separating conjunction -- and why a proof that fetches three      *)
  (* instructions paid a 369-way [iDestruct].                              *)
  (*                                                                        *)
  (* The kernel tier never had that problem, because [KernelText.kernel_text] *)
  (* is keyed by the CONSTANT [KernelInstrs.kernel_bytes] rather than by an  *)
  (* image variable, so its 23K bytes are one persistent resource and every  *)
  (* per-instruction lemma extracts from it by [big_sepM_lookup].  This is   *)
  (* that resource for the user tier: [utext_img γt T] at the program's      *)
  (* dumped [T].  [utext_all] converts into it ONCE, at the entry, where the *)
  (* image and permission facts are still in scope.                          *)
  (* ===================================================================== *)
  Definition utext_img (γt : gname) (T : gmap Z (bv 8)) : iProp Σ :=
    ([∗ map] a ↦ b ∈ T, utext γt a b)%I.

  Global Instance utext_img_persistent γt T : Persistent (utext_img γt T).
  Proof. apply _. Qed.

  (* the ONE conversion: the process's text heap covers the program's bytes,
     and every one of them is X-and-not-W (i.e. lands in the TEXT half) *)
  Lemma utext_img_of_all (γt : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (T : gmap Z (bv 8)) :
    (forall (a : Z) (b : bv 8), T !! a = Some b -> M !! a = Some b) ->
    (forall a : Z, is_Some (T !! a) -> ux_addr pm a /\ ~ uw_addr pm a) ->
    utext_all γt M pm -∗ utext_img γt T.
  Proof.
    intros HM Hperm. iIntros "#Ht". rewrite /utext_img.
    iApply big_sepM_intro. iIntros "!>" (a b Hab).
    destruct (Hperm a (mk_is_Some _ _ Hab)) as [Hx Hw].
    iApply (utext_frag γt M pm a b (HM a b Hab) Hx Hw with "Ht").
  Qed.

  (* a fetch window out of it, byte by byte -- the twin of
     [KernelText.kernel_window_pc], and what every per-pc decode lemma runs *)
  Lemma utext_img_run {k : N} (γt : gname) (T : gmap Z (bv 8))
      (a : Z) (n : nat) (w : bv k) :
    (forall j : nat, (j < n)%nat -> T !! (a + Z.of_nat j)%Z = Some (nth_byte w j)) ->
    utext_img γt T -∗
    ([∗ list] j ∈ seq 0 n, utext γt (a + Z.of_nat j) (nth_byte w j)).
  Proof.
    intros HT. iIntros "#Ht". iApply big_sepL_intro. iIntros "!>" (idx j Hj).
    apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l in Hlt |- *.
    rewrite /utext_img.
    iApply (big_sepM_lookup _ _ (a + Z.of_nat idx)%Z (nth_byte w idx) with "Ht").
    exact (HT idx Hlt).
  Qed.

  (* ...and where a literal comes from: the read-only image the entry hands
     out, at a CONCRETE base and length, so every side condition below is a
     [vm_compute] over the dumped map. *)
  Lemma utext_str_of_img (γt : gname) (T : gmap Z (bv 8)) (a : Z) (len : nat)
      (f : nat -> bv 8) :
    (forall j : nat, (j < len)%nat -> f j <> ubyte0) ->
    Z.of_nat len < 2 ^ 31 ->
    (forall j : nat, (j < len)%nat -> T !! (a + Z.of_nat j)%Z = Some (f j)) ->
    T !! (a + Z.of_nat len)%Z = Some ubyte0 ->
    utext_img γt T -∗ utext_str γt a len f.
  Proof.
    intros Hne Hlen Hbs Hnul. iIntros "#HT". rewrite /utext_str /utext_img.
    iSplit; [ iPureIntro; exact Hne | ]. iSplit; [ iPureIntro; exact Hlen | ].
    iSplitR.
    - iApply big_sepL_intro. iIntros "!>" (idx j Hj).
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l in Hlt |- *.
      iApply (big_sepM_lookup _ _ (a + Z.of_nat idx)%Z (f idx) with "HT").
      exact (Hbs idx Hlt).
    - iApply (big_sepM_lookup _ _ (a + Z.of_nat len)%Z ubyte0 with "HT").
      exact Hnul.
  Qed.

  (* ---- the three decode shapes ---------------------------------------- *)

  (* 4-alignment implies 2-alignment; [uinstr_is] carries the 2-aligned form
     because that is what the fetch path checks. *)
  Lemma ualign4_al2 (pc : mword 64) :
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    is_aligned_vaddr (Virtaddr pc) 2 = true.
  Proof.
    unfold is_aligned_vaddr. intros H%Z.eqb_eq. apply Z.eqb_eq.
    pose proof (proj1 (bv_unsigned_in_range _ pc)) as Hlo.
    rewrite uint_unsigned in H |- *.
    rewrite Z.rem_mod_nonneg in H; [ | exact Hlo | lia ].
    rewrite Z.rem_mod_nonneg; [ | exact Hlo | lia ].
    pose proof (Znumtheory.Zmod_div_mod 2 4 (bv_unsigned pc) ltac:(lia)
                  ltac:(lia) ltac:(exists 2; reflexivity)) as Hdd.
    rewrite Hdd. rewrite H. reflexivity.
  Qed.

  Lemma uinstr_is_base (γt : gname) (pc : mword 64) (w : mword 32)
      (i : instruction) :
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    Z.rem (uint pc) 4096 <= 4092 ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    udecode_base w i ->
    ([∗ list] j ∈ seq 0 4, utext γt (uint pc + Z.of_nat j) (nth_byte w j)) -∗
    uinstr_is γt pc false i.
  Proof.
    intros Hal Hpg Hn Hdec. iIntros "#Hbs".
    rewrite /uinstr_is. iSplit; [ done | ]. iSplit; [ done | ].
    iExists w. iSplit; [ done | ]. iSplit; [ done | ]. iExact "Hbs".
  Qed.

  (* a compressed instruction at a 4-ALIGNED pc: the fetch window is the
     whole 4-byte word, of which the halfword is the low half *)
  Lemma uinstr_is_rvc4 (γt : gname) (pc : mword 64) (h : mword 16)
      (w : mword 32) (i : instruction) :
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    Z.rem (uint pc) 4096 <= 4092 ->
    isRVC h = true -> udecode_rvc h i -> subrange_vec_dec w 15 0 = h ->
    ([∗ list] j ∈ seq 0 4, utext γt (uint pc + Z.of_nat j) (nth_byte w j)) -∗
    uinstr_is γt pc true i.
  Proof.
    intros Hal4 Hpg Hrvc Hdec Hlow. iIntros "#Hbs".
    rewrite /uinstr_is.
    iSplit; [ iPureIntro; exact (ualign4_al2 pc Hal4) | ].
    iSplit; [ done | ].
    iExists h. iSplit; [ done | ]. iSplit; [ done | ].
    rewrite Hal4. iExists w. iSplit; [ done | ]. iExact "Hbs".
  Qed.

  (* ...and at a 2-mod-4 pc: only the two bytes that are there *)
  Lemma uinstr_is_rvc2 (γt : gname) (pc : mword 64) (h : mword 16)
      (i : instruction) :
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    Z.rem (uint pc) 4096 <= 4092 ->
    isRVC h = true -> udecode_rvc h i ->
    ([∗ list] j ∈ seq 0 2, utext γt (uint pc + Z.of_nat j) (nth_byte h j)) -∗
    uinstr_is γt pc true i.
  Proof.
    intros Hal2 Hne Hpg Hrvc Hdec. iIntros "#Hbs".
    rewrite /uinstr_is. iSplit; [ done | ]. iSplit; [ done | ].
    iExists h. iSplit; [ done | ]. iSplit; [ done | ].
    rewrite Hne. iExact "Hbs".
  Qed.


  (* ---- THE CATALOG BRIDGE --------------------------------------------- *)
  (* [tools/gen_ucode.py] emits [uinstr]-shaped facts ([ui_sync_02] &c) and
     is the single source of decode truth for every user program, so it is
     NOT forked: this turns one of its facts into the resource a leaf wants,
     by pulling the bytes it names out of the program's own text.

     The 4-aligned compressed case is the only place the two shapes differ.
     [uinstr] carries the halfword and the two trailing bytes SEPARATELY
     (that is what the fetch path checks); [uinstr_is] carries the assembled
     word, because a fetch reads a word.  [urvc4_word] is that assembly. *)
  Lemma uinstr_is_of_uinstr (γt : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (pt : uptd)
      (pc : mword 64) (rvc : bool) (i : instruction) :
    uinstr pt M pc rvc i ->
    (forall j : nat, (j < 4)%nat ->
       ux_addr pm (uint pc + Z.of_nat j)%Z /\
       ~ uw_addr pm (uint pc + Z.of_nat j)%Z) ->
    ([∗ map] a ↦ b ∈ utext_part M pm, utext γt a b) -∗ uinstr_is γt pc rvc i.
  Proof.
    intros Hui Hperm. iIntros "#Ht".
    destruct Hui as [Hal2 Hcan Hleaf Hpg Hcode].
    destruct rvc.
    - destruct Hcode as (h & Hrvc & Hbytes & Hdec & Htrail).
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
      + destruct (Htrail eq_refl) as (b2 & b3 & Hb2 & Hb3).
        iApply (uinstr_is_rvc4 γt pc h (urvc4_word h b2 b3) i Hal4 Hpg Hrvc Hdec
                  (urvc4_low h b2 b3)).
        iApply (utext_run_of γt M pm (uint pc) 4 (urvc4_word h b2 b3)
                  ltac:(intros j Hj; rewrite (urvc4_byte h b2 b3 j Hj);
                        destruct j as [| [| [| [| j']]]]; cbn;
                        [ exact (Hbytes 0%nat ltac:(lia))
                        | exact (Hbytes 1%nat ltac:(lia))
                        | exact Hb2 | exact Hb3 | exfalso; lia ])
                  Hperm with "Ht").
      + iApply (uinstr_is_rvc2 γt pc h i Hal2 Hal4 Hpg Hrvc Hdec).
        iApply (utext_run_of γt M pm (uint pc) 2 h Hbytes
                  ltac:(intros j Hj; apply Hperm; lia) with "Ht").
    - destruct Hcode as (w & Hn & Hbytes & Hdec).
      iApply (uinstr_is_base γt pc w i Hal2 Hpg Hn Hdec).
      iApply (utext_run_of γt M pm (uint pc) 4 w Hbytes Hperm with "Ht").
  Qed.


  (* ===================================================================== *)
  (* THE FREE STACK.                                                       *)
  (*                                                                       *)
  (* [ustack γd sp n] is the n words BELOW sp -- at [sp-8], [sp-16], ...,  *)
  (* [sp-8n] -- owned, with their values existential.  It is the user-mode *)
  (* twin of [StackOwn.stack_own], and it lives inside [urun]: the process *)
  (* owns its own free stack, hands a frame out when sp moves down, and    *)
  (* takes it back when sp moves up.  A function's precondition is then a  *)
  (* NUMBER (how much headroom it needs) rather than a list of addresses.  *)
  (* ===================================================================== *)
  (* sp is 8-ALIGNED, inside the predicate.  The free stack is a stack of
     WORDS, so word alignment is part of what it means -- and every spill
     into a frame carved off it then has its [a mod 8 = 0] for free, instead
     of every function carrying the premise.

     The BODY is factored out so the splitting lemmas keep working on a
     plain [big_sepL]; the alignment rides alongside. *)
  Definition ustack_body (γd : gname) (sp : mword 64) (n : nat) : iProp Σ :=
    ([∗ list] i ∈ seq 0 n,
       ∃ w : mword 64, uword γd (uint sp - 8 * (Z.of_nat i + 1)) w)%I.

  Definition ustack (γd : gname) (sp : mword 64) (n : nat) : iProp Σ :=
    (⌜ uint sp mod 8 = 0 ⌝ ∗ ustack_body γd sp n)%I.

  Lemma ustack_align (γd : gname) (sp : mword 64) (n : nat) :
    ustack γd sp n -∗ ⌜ uint sp mod 8 = 0 ⌝.
  Proof. iIntros "[%H _]". iPureIntro. exact H. Qed.

  Lemma ustack_0 (γd : gname) (sp : mword 64) :
    ustack γd sp 0 ⊣⊢ ⌜ uint sp mod 8 = 0 ⌝.
  Proof.
    rewrite /ustack /ustack_body /=.
    iSplit; [ iIntros "[$ _]" | iIntros "$"; done ].
  Qed.

  (* ---- the body's algebra, unchanged from before the alignment ---- *)

  Lemma ustack_body_S (γd : gname) (sp sp' : mword 64) (n : nat) :
    uint sp' = uint sp - 8 ->
    ustack_body γd sp (S n)
    ⊣⊢ (∃ w : mword 64, uword γd (uint sp - 8) w) ∗ ustack_body γd sp' n.
  Proof.
    intros Hsp. rewrite /ustack_body.
    change (seq 0 (S n)) with (0%nat :: seq 1 n).
    rewrite big_sepL_cons.
    assert (E0 : uint sp - 8 * (Z.of_nat 0 + 1) = uint sp - 8) by lia.
    rewrite E0.
    apply bi.sep_proper; [ reflexivity | ].
    rewrite <- (seq_shift n 0). rewrite big_sepL_fmap.
    apply big_opL_proper. intros k j _.
    assert (Ej : uint sp - 8 * (Z.of_nat (S j) + 1)
                 = uint sp' - 8 * (Z.of_nat j + 1)) by (rewrite Hsp; lia).
    rewrite Ej. reflexivity.
  Qed.

  Lemma ustack_body_app (γd : gname) (sp sp' : mword 64) (k n : nat) :
    uint sp' = uint sp - 8 * Z.of_nat k ->
    ustack_body γd sp (k + n) ⊣⊢ ustack_body γd sp k ∗ ustack_body γd sp' n.
  Proof.
    revert sp sp'. induction k as [| k IH]; intros sp sp' Hsp.
    - assert (Hs : sp' = sp) by (apply bv_eq; rewrite <- !uint_unsigned; lia).
      (* [/=] already reduced [0 + n]; a following [Nat.add_0_l]
         would match nothing *)
      rewrite Hs /ustack_body /= bi.emp_sep. reflexivity.
    - assert (Hk : 8 * Z.of_nat (S k) <= uint sp).
      { pose proof (proj1 (bv_unsigned_in_range _ sp')) as H0.
        rewrite <- uint_unsigned in H0. lia. }
      pose proof (bv_unsigned_in_range _ sp) as Hr.
      rewrite Zmod64 in Hr. rewrite <- uint_unsigned in Hr.
      set (sp1 := (mword_of_int (uint sp - 8) : mword 64)).
      assert (Hu1 : uint sp1 = uint sp - 8).
      { unfold sp1. rewrite uint_unsigned moi64_unsigned. unfold bv_wrap.
        rewrite Zmod64. apply Z.mod_small. unfold Z64 in *. lia. }
      replace (S k + n)%nat with (S (k + n))%nat by lia.
      rewrite (ustack_body_S γd sp sp1 (k + n) Hu1).
      rewrite (ustack_body_S γd sp sp1 k Hu1).
      rewrite (IH sp1 sp' ltac:(rewrite Hu1; lia)).
      rewrite assoc. reflexivity.
  Qed.

  (* ---- ...and the alignment travels with it ---- *)

  Lemma ustack_app (γd : gname) (sp sp' : mword 64) (k n : nat) :
    uint sp' = uint sp - 8 * Z.of_nat k ->
    ustack γd sp (k + n) ⊣⊢ ustack γd sp k ∗ ustack γd sp' n.
  Proof.
    intros Hsp. rewrite /ustack (ustack_body_app γd sp sp' k n Hsp).
    (* lia does not do the mod-8 iff on its own *)
    assert (H8k : (8 * Z.of_nat k) mod 8 = 0)
      by (rewrite Z.mul_comm; apply Z_mod_mult).
    assert (Hal : uint sp mod 8 = 0 <-> uint sp' mod 8 = 0).
    { rewrite Hsp Zminus_mod H8k. split; intro H.
      - rewrite H. reflexivity.
      - rewrite Z.sub_0_r in H.
        rewrite (Z.mod_mod (uint sp) 8 ltac:(lia)) in H. exact H. }
    iSplit.
    - iIntros "(%Hal8 & Hlo & Hhi)".
      iSplitL "Hlo"; [ iSplitR; [ iPureIntro; exact Hal8 | iExact "Hlo" ] | ].
      iSplitR; [ iPureIntro; apply Hal; exact Hal8 | iExact "Hhi" ].
    - iIntros "((%Hal8 & Hlo) & (_ & Hhi))".
      iSplitR; [ iPureIntro; exact Hal8 | ]. iFrame "Hlo Hhi".
  Qed.

  Lemma ustack_2 (γd : gname) (sp : mword 64) :
    ustack γd sp 2 ⊣⊢ ⌜ uint sp mod 8 = 0 ⌝ ∗
                      (∃ w : mword 64, uword γd (uint sp - 8) w) ∗
                      (∃ w : mword 64, uword γd (uint sp - 16) w).
  Proof.
    rewrite /ustack /ustack_body /=.
    assert (E0 : uint sp - 8 * (Z.of_nat 0 + 1) = uint sp - 8) by lia.
    assert (E1 : uint sp - 8 * (Z.of_nat 1 + 1) = uint sp - 16) by lia.
    rewrite E0 E1 right_id. reflexivity.
  Qed.

  (* ONE SLOT of a frame, taken out and put back.  A prologue spills to
     slot i of the frame it just took; this is how it names that word. *)
  (* the eight-word form: a frame big enough for ra plus the callee-saved
     registers a real function body uses.  Spelled out like [ustack_2]
     rather than derived from it: the intermediate stack pointers a
     [ustack_app] chain would need are [mword]s whose [uint] the caller
     would then have to pin, which is more work than the eight rewrites. *)
  Lemma ustack_8 (γd : gname) (sp : mword 64) :
    ustack γd sp 8 ⊣⊢ ⌜ uint sp mod 8 = 0 ⌝ ∗
      (∃ w : mword 64, uword γd (uint sp - 8) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 16) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 24) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 32) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 40) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 48) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 56) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 64) w).
  Proof.
    rewrite /ustack /ustack_body /=.
    assert (E0 : uint sp - 8 * (Z.of_nat 0 + 1) = uint sp - 8) by lia.
    assert (E1 : uint sp - 8 * (Z.of_nat 1 + 1) = uint sp - 16) by lia.
    assert (E2 : uint sp - 8 * (Z.of_nat 2 + 1) = uint sp - 24) by lia.
    assert (E3 : uint sp - 8 * (Z.of_nat 3 + 1) = uint sp - 32) by lia.
    assert (E4 : uint sp - 8 * (Z.of_nat 4 + 1) = uint sp - 40) by lia.
    assert (E5 : uint sp - 8 * (Z.of_nat 5 + 1) = uint sp - 48) by lia.
    assert (E6 : uint sp - 8 * (Z.of_nat 6 + 1) = uint sp - 56) by lia.
    assert (E7 : uint sp - 8 * (Z.of_nat 7 + 1) = uint sp - 64) by lia.
    rewrite E0 E1 E2 E3 E4 E5 E6 E7 right_id. reflexivity.
  Qed.

  (* the four-word form: putc's frame (32 bytes). *)
  Lemma ustack_4 (γd : gname) (sp : mword 64) :
    ustack γd sp 4 ⊣⊢ ⌜ uint sp mod 8 = 0 ⌝ ∗
      (∃ w : mword 64, uword γd (uint sp - 8) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 16) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 24) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 32) w).
  Proof.
    rewrite /ustack /ustack_body /=.
    assert (E0 : uint sp - 8 * (Z.of_nat 0 + 1) = uint sp - 8) by lia.
    assert (E1 : uint sp - 8 * (Z.of_nat 1 + 1) = uint sp - 16) by lia.
    assert (E2 : uint sp - 8 * (Z.of_nat 2 + 1) = uint sp - 24) by lia.
    assert (E3 : uint sp - 8 * (Z.of_nat 3 + 1) = uint sp - 32) by lia.
    rewrite E0 E1 E2 E3 right_id. reflexivity.
  Qed.

  (* ...and the twelve-word form: printf's and vprintf's frame (96
     bytes).  printf spills seven argument registers into it. *)
  Lemma ustack_12 (γd : gname) (sp : mword 64) :
    ustack γd sp 12 ⊣⊢ ⌜ uint sp mod 8 = 0 ⌝ ∗
      (∃ w : mword 64, uword γd (uint sp - 8) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 16) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 24) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 32) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 40) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 48) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 56) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 64) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 72) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 80) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 88) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 96) w).
  Proof.
    rewrite /ustack /ustack_body /=.
    assert (E0 : uint sp - 8 * (Z.of_nat 0 + 1) = uint sp - 8) by lia.
    assert (E1 : uint sp - 8 * (Z.of_nat 1 + 1) = uint sp - 16) by lia.
    assert (E2 : uint sp - 8 * (Z.of_nat 2 + 1) = uint sp - 24) by lia.
    assert (E3 : uint sp - 8 * (Z.of_nat 3 + 1) = uint sp - 32) by lia.
    assert (E4 : uint sp - 8 * (Z.of_nat 4 + 1) = uint sp - 40) by lia.
    assert (E5 : uint sp - 8 * (Z.of_nat 5 + 1) = uint sp - 48) by lia.
    assert (E6 : uint sp - 8 * (Z.of_nat 6 + 1) = uint sp - 56) by lia.
    assert (E7 : uint sp - 8 * (Z.of_nat 7 + 1) = uint sp - 64) by lia.
    assert (E8 : uint sp - 8 * (Z.of_nat 8 + 1) = uint sp - 72) by lia.
    assert (E9 : uint sp - 8 * (Z.of_nat 9 + 1) = uint sp - 80) by lia.
    assert (E10 : uint sp - 8 * (Z.of_nat 10 + 1) = uint sp - 88) by lia.
    assert (E11 : uint sp - 8 * (Z.of_nat 11 + 1) = uint sp - 96) by lia.
    rewrite E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 right_id. reflexivity.
  Qed.

  (* ===================================================================== *)
  (* DIRECTED forms of the two splits above -- and they are not a           *)
  (* convenience.  A [⊣⊢] used under [rewrite] INSIDE a proofmode goal      *)
  (* fires on the whole [envs_entails Δ Q], context included (optimization  *)
  (* .md, "Directed entailments, not [⊣⊢] rewrites").  putc's frame split   *)
  (* written as [rewrite ustack_4] / [rewrite uword_8] at the call site was *)
  (* killed at eight minutes and 41 GB; the same steps behind these lemmas, *)
  (* where the goal is two lines long, are free.  Rule of thumb: if one of  *)
  (* the [⊣⊢] splits above appears under [rewrite] in a program proof, it   *)
  (* is a directed lemma waiting to be written.                             *)
  (* ===================================================================== *)
  Lemma ustack_4_open (γd : gname) (sp : mword 64) :
    ustack γd sp 4 -∗
      ⌜ uint sp mod 8 = 0 ⌝ ∗
      (∃ w : mword 64, uword γd (uint sp - 8) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 16) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 24) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 32) w).
  Proof. rewrite ustack_4. iIntros "H". iExact "H". Qed.

  Lemma ustack_4_close (γd : gname) (sp : mword 64) :
    uint sp mod 8 = 0 ->
    (∃ w : mword 64, uword γd (uint sp - 8) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 16) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 24) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 32) w) -∗
    ustack γd sp 4.
  Proof.
    intros Hal. iIntros "H0 H1 H2 H3". rewrite ustack_4.
    iSplit; [ iPureIntro; exact Hal | ]. iFrame.
  Qed.

  (* the twelve-word frame, directed -- printf's and vprintf's (96 bytes) *)
  Lemma ustack_12_open (γd : gname) (sp : mword 64) :
    ustack γd sp 12 -∗
      ⌜ uint sp mod 8 = 0 ⌝ ∗
      (∃ w : mword 64, uword γd (uint sp - 8) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 16) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 24) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 32) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 40) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 48) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 56) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 64) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 72) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 80) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 88) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 96) w).
  Proof. rewrite ustack_12. iIntros "H". iExact "H". Qed.

  Lemma ustack_12_close (γd : gname) (sp : mword 64) :
    uint sp mod 8 = 0 ->
    (∃ w : mword 64, uword γd (uint sp - 8) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 16) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 24) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 32) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 40) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 48) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 56) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 64) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 72) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 80) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 88) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 96) w) -∗
    ustack γd sp 12.
  Proof.
    intros Hal. iIntros "H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11".
    rewrite ustack_12. iSplit; [ iPureIntro; exact Hal | ]. iFrame.
  Qed.

  Lemma ustack_acc (γd : gname) (sp : mword 64) (n i : nat) :
    (i < n)%nat ->
    ustack γd sp n -∗
      (∃ w : mword 64, uword γd (uint sp - 8 * (Z.of_nat i + 1)) w) ∗
      ((∃ w : mword 64, uword γd (uint sp - 8 * (Z.of_nat i + 1)) w) -∗
         ustack γd sp n).
  Proof.
    intros Hi. iIntros "(%Hal & Hb)". rewrite /ustack /ustack_body.
    iDestruct (big_sepL_lookup_acc _ _ i i with "Hb") as "[Hw Hcl]";
      [ apply lookup_seq; split; [ lia | exact Hi ] | ].
    iFrame "Hw". iIntros "Hw".
    iSplitR; [ iPureIntro; exact Hal | ]. iApply ("Hcl" with "Hw").
  Qed.

  (* ...and the split at any depth: the first [k] words are the frame the
     caller is handing out, the rest is what remains below the moved sp *)


  (* ===================================================================== *)
  (* THE CARVE: turning the entry's data map into a free stack.            *)
  (*                                                                       *)
  (* [uslot_of_urun] hands a program its data as [[∗ map] a ↦ b ∈ D,       *)
  (* ubyte γd a b].  A process's stack is a contiguous run inside that,    *)
  (* and these four steps turn it into [ustack]: pull the run out of the   *)
  (* map, split it into 8-byte groups, assemble each group into a word,    *)
  (* and index the words downward from sp.                                 *)
  (* ===================================================================== *)

  (* (1) a contiguous run, out of a map that contains it *)
  Lemma ubytes_of_map (γd : gname) (D : gmap Z (bv 8)) (a : Z) (n : nat)
      (f : nat -> bv 8) :
    (forall j : nat, (j < n)%nat -> D !! (a + Z.of_nat j)%Z = Some (f j)) ->
    ([∗ map] k ↦ b ∈ D, ubyte γd k b) -∗ ubytes γd a n f.
  Proof.
    revert D. induction n as [| n IH]; intros D HD; iIntros "HD".
    - rewrite /ubytes /ubytesq /=. done.
    - iDestruct (big_sepM_delete _ D (a + Z.of_nat n)%Z (f n) with "HD")
        as "[Hb HD]"; [ exact (HD n ltac:(lia)) | ].
      (* hoisted, not [ltac:]: an inline side-condition is elaborated before
         the map argument is known, and runs against an evar *)
      assert (HD' : forall j : nat, (j < n)%nat ->
                delete (a + Z.of_nat n)%Z D !! (a + Z.of_nat j)%Z = Some (f j)).
      { intros j Hj. rewrite lookup_delete_ne; [ apply HD; lia | lia ]. }
      iDestruct (IH (delete (a + Z.of_nat n)%Z D) HD' with "HD") as "Hlo".
      rewrite /ubytes /ubytesq seq_S big_sepL_app /=.
      iFrame "Hlo Hb".
  Qed.

  (* (2) the split of a run *)
  Lemma ubytes_app (γd : gname) (a : Z) (k n : nat) (f : nat -> bv 8) :
    ubytes γd a (k + n) f ⊣⊢
    ubytes γd a k f ∗ ubytes γd (a + Z.of_nat k) n (fun j => f (k + j)%nat).
  Proof.
    rewrite /ubytes /ubytesq seq_app big_sepL_app.
    apply bi.sep_proper; [ reflexivity | ].
    replace (seq (0 + k) n) with (Nat.add k <$> seq 0 n)
      by (rewrite fmap_add_seq; f_equal; lia).
    rewrite big_sepL_fmap.
    apply big_opL_proper. intros i j _.
    assert (E : (a + Z.of_nat (k + j))%Z = (a + Z.of_nat k + Z.of_nat j)%Z) by lia.
    rewrite E. reflexivity.
  Qed.

  (* (3) eight bytes make a word.  Its value is the assembly of the bytes;
     [ustack] only ever needs SOME word, so the witness is never named by a
     caller. *)
  Lemma uword_of_ubytes (γd : gname) (a : Z) (f : nat -> bv 8) :
    ubytes γd a 8 f -∗ ∃ w : mword 64, uword γd a w.
  Proof.
    iIntros "Hb".
    iExists (Z_to_bv 64 (assemble_bytes
               [f 0%nat; f 1%nat; f 2%nat; f 3%nat;
                f 4%nat; f 5%nat; f 6%nat; f 7%nat]) : mword 64).
    rewrite /uword /uwordq /ubytes /ubytesq.
    iApply (big_sepL_mono with "Hb"). intros i j Hj.
    apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l in Hlt |- *.
    rewrite (nth_byte_assemble_len 64
               [f 0%nat; f 1%nat; f 2%nat; f 3%nat;
                f 4%nat; f 5%nat; f 6%nat; f 7%nat] i
               ltac:(cbn; lia) ltac:(cbn; lia)).
    destruct i as [| [| [| [| [| [| [| [| i']]]]]]]];
      cbn; try reflexivity; exfalso; cbn in Hlt; lia.
  Qed.

  (* ...and the other direction, spelled out.  A [uword] IS eight [ubyte]s
     (that is its definition), but the [∗ list] over [seq 0 8] and the
     [a + Z.of_nat j] addresses are not what a proof that writes ONE byte of
     a stack slot wants to see -- putc's [sb a1,-17(s0)] lands on byte 7 of
     the word at [sp-24].  Same shape as [ustack_8]: name the eight, once. *)
  Lemma ubytes_8 (γd : gname) (a : Z) (f : nat -> bv 8) :
    ubytes γd a 8 f ⊣⊢
      ubyte γd a (f 0%nat) ∗ ubyte γd (a + 1) (f 1%nat) ∗
      ubyte γd (a + 2) (f 2%nat) ∗ ubyte γd (a + 3) (f 3%nat) ∗
      ubyte γd (a + 4) (f 4%nat) ∗ ubyte γd (a + 5) (f 5%nat) ∗
      ubyte γd (a + 6) (f 6%nat) ∗ ubyte γd (a + 7) (f 7%nat).
  Proof.
    rewrite /ubytes /ubytesq /=.
    assert (E0 : (a + Z.of_nat 0)%Z = a) by lia.
    assert (E1 : (a + Z.of_nat 1)%Z = (a + 1)%Z) by lia.
    assert (E2 : (a + Z.of_nat 2)%Z = (a + 2)%Z) by lia.
    assert (E3 : (a + Z.of_nat 3)%Z = (a + 3)%Z) by lia.
    assert (E4 : (a + Z.of_nat 4)%Z = (a + 4)%Z) by lia.
    assert (E5 : (a + Z.of_nat 5)%Z = (a + 5)%Z) by lia.
    assert (E6 : (a + Z.of_nat 6)%Z = (a + 6)%Z) by lia.
    assert (E7 : (a + Z.of_nat 7)%Z = (a + 7)%Z) by lia.
    rewrite E0 E1 E2 E3 E4 E5 E6 E7 right_id. reflexivity.
  Qed.

  (* the word form of the same split, which is what a [ustack] slot hands
     over: eight named bytes in, SOME word back out *)
  Lemma uword_8 (γd : gname) (a : Z) (w : mword 64) :
    uword γd a w ⊣⊢
      ubyte γd a (nth_byte w 0%nat) ∗ ubyte γd (a + 1) (nth_byte w 1%nat) ∗
      ubyte γd (a + 2) (nth_byte w 2%nat) ∗ ubyte γd (a + 3) (nth_byte w 3%nat) ∗
      ubyte γd (a + 4) (nth_byte w 4%nat) ∗ ubyte γd (a + 5) (nth_byte w 5%nat) ∗
      ubyte γd (a + 6) (nth_byte w 6%nat) ∗ ubyte γd (a + 7) (nth_byte w 7%nat).
  Proof. exact (ubytes_8 γd a (nth_byte w)). Qed.

  (* the shape a one-byte store into a stack slot actually uses: hand the
     eight bytes over with the [i]th one REPLACED, get SOME word back.  The
     caller never names the resulting word, and [ustack] never asks. *)
  Lemma uword_of_bytes_8 (γd : gname) (a : Z) (b0 b1 b2 b3 b4 b5 b6 b7 : bv 8) :
    ubyte γd a b0 -∗ ubyte γd (a + 1) b1 -∗ ubyte γd (a + 2) b2 -∗
    ubyte γd (a + 3) b3 -∗ ubyte γd (a + 4) b4 -∗ ubyte γd (a + 5) b5 -∗
    ubyte γd (a + 6) b6 -∗ ubyte γd (a + 7) b7 -∗
    ∃ w : mword 64, uword γd a w.
  Proof.
    iIntros "H0 H1 H2 H3 H4 H5 H6 H7".
    iApply (uword_of_ubytes γd a
              (fun j => match j with
                        | 0%nat => b0 | 1%nat => b1 | 2%nat => b2 | 3%nat => b3
                        | 4%nat => b4 | 5%nat => b5 | 6%nat => b6 | _ => b7
                        end)).
    rewrite ubytes_8. iFrame.
  Qed.

  (* ONE BYTE OF A STACK SLOT, taken out and put back.  The address is a
     PREMISE rather than something the caller rewrites into shape, which is
     what keeps [uint sp - 24 + 7] out of the proofmode goal: putc's
     [sb a1,-17(s0)] names [sp0-17] and the arithmetic is discharged here. *)
  Lemma uword_byte7_acc (γd : gname) (a b : Z) (w : mword 64) :
    b = (a + 7)%Z ->
    uword γd a w -∗
      ubyte γd b (nth_byte w 7%nat) ∗
      (∀ c : bv 8, ubyte γd b c -∗ ∃ w' : mword 64, uword γd a w').
  Proof.
    intros ->. rewrite uword_8.
    iIntros "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7)".
    iFrame "H7". iIntros (c) "H7".
    iApply (uword_of_bytes_8 γd a with "H0 H1 H2 H3 H4 H5 H6 H7").
  Qed.

  (* (4) ...and n of them, indexed downward from sp *)
  Lemma ustack_body_of_ubytes (γd : gname) (sp : mword 64) (n : nat)
      (f : nat -> bv 8) :
    8 * Z.of_nat n <= uint sp ->
    ubytes γd (uint sp - 8 * Z.of_nat n) (8 * n) f -∗ ustack_body γd sp n.
  Proof.
    revert sp f. induction n as [| n IH]; intros sp f Hn.
    - iIntros "_". rewrite /ustack_body /=. done.
    - iIntros "Hb".
      pose proof (bv_unsigned_in_range _ sp) as Hr.
      rewrite Zmod64 in Hr. rewrite <- uint_unsigned in Hr.
      set (sp1 := (mword_of_int (uint sp - 8) : mword 64)).
      assert (Hu1 : uint sp1 = uint sp - 8).
      { unfold sp1. rewrite uint_unsigned moi64_unsigned. unfold bv_wrap.
        rewrite Zmod64. apply Z.mod_small. unfold Z64 in *. lia. }
      rewrite (ustack_body_S γd sp sp1 n Hu1).
      replace (8 * S n)%nat with (8 * n + 8)%nat by lia.
      assert (Ea : (uint sp - 8 * Z.of_nat (S n))%Z
                   = (uint sp1 - 8 * Z.of_nat n)%Z) by (rewrite Hu1; lia).
      rewrite Ea.
      rewrite (ubytes_app γd (uint sp1 - 8 * Z.of_nat n) (8 * n) 8 f).
      iDestruct "Hb" as "[Hlo Hhi]".
      assert (Eh : (uint sp1 - 8 * Z.of_nat n + Z.of_nat (8 * n))%Z
                   = (uint sp - 8)%Z) by (rewrite Hu1; lia).
      rewrite Eh.
      iSplitL "Hhi".
      + iApply (uword_of_ubytes with "Hhi").
      + assert (Hn' : 8 * Z.of_nat n <= uint sp1) by (rewrite Hu1; lia).
        iApply (IH sp1 f Hn' with "Hlo").
  Qed.

  (* ...and the alignment, which the entry's gate supplies *)
  Lemma ustack_of_ubytes (γd : gname) (sp : mword 64) (n : nat) (f : nat -> bv 8) :
    uint sp mod 8 = 0 ->
    8 * Z.of_nat n <= uint sp ->
    ubytes γd (uint sp - 8 * Z.of_nat n) (8 * n) f -∗ ustack γd sp n.
  Proof.
    intros Hal Hn. iIntros "Hb". rewrite /ustack.
    iSplitR; [ iPureIntro; exact Hal | ].
    iApply (ustack_body_of_ubytes γd sp n f Hn with "Hb").
  Qed.

End UserHeap.
