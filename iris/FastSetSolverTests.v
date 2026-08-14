(* ====================================================================== *)
(* FastSetSolverTests.v                                                    *)
(*                                                                         *)
(* The regression suite for the [set_solver] override (FastSetSolver.v).    *)
(*                                                                         *)
(* Every goal below is a shape this tree actually discharges with           *)
(* [set_solver], or WORKS AROUND with a hand-written named lemma because    *)
(* [set_solver] was too slow at the call site -- see the [bmset_*] block in *)
(* ProofBmap.v, [wiset_*] in ProofWritei.v, [cr_*] in ProofCreate.v,        *)
(* [gset_disj_*] in VirtioQueue.v, [ip_*] in ProofIput.v, and the rest.     *)
(* If the override ever stops proving one of these, a workaround block      *)
(* somewhere is about to become load-bearing again.                        *)
(*                                                                         *)
(* The two [Fail]s at the end are shapes UPSTREAM cannot prove either; they *)
(* are here so that a future improvement announces itself by breaking them. *)
(* ====================================================================== *)

(** Every goal shape the xv6iris tree currently discharges with [set_solver],
    or works around with a named lemma because [set_solver] is too slow.
    Sources are the file:line citations from the call-site inventory. *)
From stdpp Require Import sets gmap coPset fin_maps.
Require Import FastSetSolver.

Local Open Scope Z_scope.

(* ---- Family A: subset of a union / monotonicity (ProofBmap, ProofWritei) -- *)
Lemma bmset_sub_l3 (A B C : gset Z) : A ⊆ A ∪ B ∪ C.
Proof. set_solver. Qed.
Lemma bmset_sub_l4 (A B C D : gset Z) : A ⊆ A ∪ B ∪ C ∪ D.
Proof. set_solver. Qed.
Lemma bmset_add_r (A D : gset Z) : A ⊆ A ∪ D.
Proof. set_solver. Qed.
Lemma bmset_ceil3 (A : gset Z) (x y z : Z) :
  A ∪ {[x]} ∪ {[z]} ⊆ A ∪ {[x]} ∪ {[y]} ∪ {[z]}.
Proof. set_solver. Qed.
Lemma bmset_tail_ceiling (Sb SbI : gset Z) (bms ind blk : Z) :
  SbI ⊆ Sb ∪ {[bms]} ∪ {[ind]} ->
  SbI ∪ {[bms]} ∪ {[blk]} ∪ {[ind]} ⊆ Sb ∪ {[bms]} ∪ {[ind]} ∪ {[blk]}.
Proof. set_solver. Qed.
Lemma wiset_sub_add_r (A B D : gset Z) : A ⊆ B -> A ⊆ B ∪ D.
Proof. set_solver. Qed.
Lemma ip_diff_sub (X Y : gset Z) : X ∖ Y ⊆ X.
Proof. set_solver. Qed.
Lemma wb_diff_mono (F F' Sb : gset Z) : F' ⊆ F -> F' ∖ Sb ⊆ F ∖ Sb.
Proof. set_solver. Qed.
Lemma wb_diff_add (F Sb : gset Z) (b : Z) : F ∖ (Sb ∪ {[b]}) ⊆ F ∖ Sb.
Proof. set_solver. Qed.
Lemma wb_absorb (F Sb : gset Z) (b : Z) : b ∈ Sb -> ({[b]} ∪ F) ∖ Sb ⊆ F ∖ Sb.
Proof. set_solver. Qed.
Lemma wb_sing_in (F Sb : gset Z) (b : Z) : b ∈ F ∖ Sb -> {[b]} ⊆ F ∖ Sb.
Proof. set_solver. Qed.
Lemma wb_strict (F Sb : gset Z) (b : Z) : b ∈ F ∖ Sb -> F ∖ (Sb ∪ {[b]}) ⊂ F ∖ Sb.
Proof. set_solver. Qed.
Lemma cr_sub2 (A B C : gset Z) : A ⊆ B -> B ⊆ C -> A ⊆ C.
Proof. set_solver. Qed.
Lemma cr_sub3 (A B C D : gset Z) : A ⊆ B -> B ⊆ C -> C ⊆ D -> A ⊆ D.
Proof. set_solver. Qed.
Lemma bm_used_grow (uu uc : gset Z) (x : Z) : uu ⊆ uc -> uu ⊆ uc ∪ {[x]}.
Proof. set_solver. Qed.

(* ---- Family B: membership / non-membership ------------------------------ *)
Lemma bmset_sing_in (x : Z) (S : gset Z) : {[x]} ⊆ S -> x ∈ S.
Proof. set_solver. Qed.
Lemma bmset_sing_sub (x : Z) (S : gset Z) : x ∈ S -> {[x]} ⊆ S.
Proof. set_solver. Qed.
Lemma bmset_in_l3 (x : Z) (A B C : gset Z) : x ∈ A -> x ∈ A ∪ B ∪ C.
Proof. set_solver. Qed.
Lemma bmset_in_m4 (x : Z) (A C D : gset Z) : x ∈ A ∪ {[x]} ∪ C ∪ D.
Proof. set_solver. Qed.
Lemma bmset_in_c4 (x : Z) (A B D : gset Z) : x ∈ A ∪ B ∪ {[x]} ∪ D.
Proof. set_solver. Qed.
Lemma wiset_in_mono (x : Z) (A B : gset Z) : A ⊆ B -> x ∈ A -> x ∈ B.
Proof. set_solver. Qed.
Lemma ip_notin_diff (P S : gset Z) (z : Z) : z ∈ S -> z ∉ P ∖ S.
Proof. set_solver. Qed.
Lemma procinv_fd_empty (fd : nat) : fd ∉ (∅ : gset nat).
Proof. set_solver. Qed.
Lemma procinv_lend (fd : nat) (D : gset nat) : D ⊆ {[fd]} ∪ D.
Proof. set_solver. Qed.
Lemma procinv_in (fd : nat) (D : gset nat) : fd ∈ {[fd]} ∪ D.
Proof. set_solver. Qed.
Lemma bminv_notin (x bi : Z) (used : gset Z) : x ∉ used ∪ {[bi]} -> x ∉ used.
Proof. set_solver. Qed.
Lemma bminv_notin_del (x b : Z) (used : gset Z) :
  x ∉ used ∖ {[b]} -> x ≠ b -> x ∉ used.
Proof. set_solver. Qed.
Lemma wb_mem_diff (F Sb : gset Z) (b : Z) : b ∈ F -> b ∉ Sb -> b ∈ F ∖ Sb.
Proof. set_solver. Qed.
(* ProofKvmmake: elem_of over a LIST of numeric literals, not a gset *)
Lemma kvm_notin_list : (0%Z) ∉ [2;255]%Z.
Proof. set_solver. Qed.

(* ---- Family C: set equalities ------------------------------------------- *)
Lemma ig_pool_set (P S : gset Z) (z : Z) : P ∖ ({[z]} ∪ S) = (P ∖ S) ∖ {[z]}.
Proof. set_solver. Qed.
(* UPSTREAM CANNOT PROVE THIS EITHER (it reports "No matching clauses for
   match"); ProofIput.v:302 proves it by hand.  Kept as a tripwire. *)
Goal forall (P S : gset Z) (z : Z),
  z ∈ P -> z ∈ S -> P ∖ (S ∖ {[z]}) = {[z]} ∪ (P ∖ S).
Proof. Fail set_solver. Abort.
Lemma freed_pool_grow (used S : gset Z) (c : Z) :
  c <> 0 -> used ∖ S ∖ {[c]} = used ∖ (S ∪ ({[c]} ∖ {[0]})).
Proof. set_solver. Qed.
Lemma freed_pool_grow2 (used A B : gset Z) (c : Z) :
  c <> 0 -> used ∖ (A ∪ B) ∖ {[c]} = used ∖ (A ∪ (B ∪ ({[c]} ∖ {[0]}))).
Proof. set_solver. Qed.
Lemma bm_freed_step (X : gset Z) (c : Z) :
  (X ∪ {[c]}) ∖ {[0]} = (X ∖ {[0]}) ∪ ({[c]} ∖ {[0]}).
Proof. set_solver. Qed.
Lemma bm_freed_skip (X : gset Z) : X ∪ (({[0]} : gset Z) ∖ {[0]}) = X.
Proof. set_solver. Qed.
Lemma vdrwf_dom_delete (q : nat) (F P T : gset nat) :
  T = F ∪ P -> q ∉ F -> T ∖ {[q]} = F ∪ (P ∖ {[q]}).
Proof. set_solver. Qed.
Lemma gset_union_assoc' (X Y Z : gset Z) : X ∪ (Y ∪ Z) = (X ∪ Y) ∪ Z.
Proof. set_solver. Qed.
Lemma wb_diff_distr (F Sb : gset Z) (x : Z) :
  ({[x]} ∪ F) ∖ Sb = ({[x]} ∖ Sb) ∪ (F ∖ Sb).
Proof. set_solver. Qed.
(* UPSTREAM CANNOT PROVE THIS EITHER; VirtioQueue.v:98 says so in a comment
   and proves it by hand.  Kept as a tripwire. *)
Goal forall (X Y : gset Z) (a : Z),
  a ∈ X -> X ∪ Y = (X ∖ {[a]}) ∪ ({[a]} ∪ Y).
Proof. Fail set_solver. Abort.
(* dom-level facts, after the usual dom_* rewrite *)
Lemma dom_ins_regroup (np : nat) (fl pk : gmap nat bool) :
  {[np]} ∪ (dom fl ∪ dom pk) = ({[np]} ∪ dom fl) ∪ (dom pk : gset nat).
Proof. set_solver. Qed.
Lemma dom_union_absorb (w dma : gmap nat bool) :
  dom w ⊆ dom dma -> dom w ∪ dom dma = (dom dma : gset nat).
Proof. set_solver. Qed.
Lemma dom_empty_r (mm : gmap nat bool) : ∅ ∪ dom mm = (dom mm : gset nat).
Proof. set_solver. Qed.
Lemma issue163 : {[0%nat]} ∪ dom (∅ : gmap nat nat) ≠ ∅.
Proof. set_solver. Qed.

(* ---- Family D: disjointness --------------------------------------------- *)
Lemma disj_diff (X Y : gset Z) : X ## Y ∖ X.
Proof. set_solver. Qed.
Lemma disj_diff' (A R : gset Z) : A ## R ∖ A.
Proof. set_solver. Qed.
Lemma disj_sing (a b : Z) : a ≠ b -> ({[a]} : gset Z) ## {[b]}.
Proof. set_solver. Qed.
Lemma disj_sing3 (a b c : Z) :
  a ≠ b -> a ≠ c -> ({[a]} : gset Z) ## ({[b]} ∪ {[c]}).
Proof. set_solver. Qed.
Lemma gset_disj_mono {A} `{Countable A} (X X' Y Y' : gset A) :
  X ⊆ X' -> Y ⊆ Y' -> X' ## Y' -> X ## Y.
Proof. set_solver. Qed.
Lemma gset_disj_union_l {A} `{Countable A} (X Y Z : gset A) :
  X ## Z -> Y ## Z -> (X ∪ Y) ## Z.
Proof. set_solver. Qed.
Lemma gset_sub_diff {A} `{Countable A} (X D Y : gset A) :
  X ⊆ D -> X ## Y -> X ⊆ D ∖ Y.
Proof. set_solver. Qed.
Lemma fsboot_disj {A} `{Countable A} (X Y : gset A) : Y ## X ∖ Y.
Proof. set_solver. Qed.

(* ---- Family F: coPset masks (17 sites, all this one shape) -------------- *)
Lemma mask_empty_sub (E : coPset) : (∅ : coPset) ⊆ E.
Proof. set_solver. Qed.
Lemma mask_empty_top : (∅ : coPset) ⊆ (⊤ : coPset).
Proof. set_solver. Qed.

(* ---- Family G: gset CMRA glue ------------------------------------------- *)
Lemma loginv_incl (X : gset (nat * Z)) (e : nat) (b : Z) : X ⊆ X ∪ {[(e, b)]}.
Proof. set_solver. Qed.
Lemma loginv_mem (X : gset (nat * Z)) (e : nat) (b : Z) : {[(e, b)]} ⊆ X -> (e, b) ∈ X.
Proof. set_solver. Qed.

(* ---- set_seq / set_solver by lia (VirtioQueue:1205, :1306) --------------- *)
Lemma seq_snoc_comm (n : nat) : {[n]} ∪ set_seq 0%nat n = (set_seq 0%nat n ∪ {[n]} : gset nat).
Proof. set_solver. Qed.
Lemma seq_delete (nc np : nat) :
  (nc < np)%nat ->
  set_seq nc (np - nc) ∖ {[nc]} = (set_seq (S nc) (np - S nc) : gset nat).
Proof. set_solver by lia. Qed.

(* ---- set_Exists / set_Forall / monad (stdpp's own tests) ---------------- *)
Lemma set_Exists_ss : set_Exists (.= 10%nat) ({[ 10%nat ]} : gset nat).
Proof. set_solver. Qed.
Lemma set_Forall_ss `{Set_ A C} (X : C) x : set_Forall (.≠ x) X ↔ x ∉ X.
Proof. set_solver. Qed.
Lemma elem_of_list_bind_again {A B} (x : B) (l : list A) f :
  x ∈ l ≫= f ↔ ∃ y, x ∈ f y ∧ y ∈ l.
Proof. set_solver. Qed.
Lemma set_guard_case_guard `{MonadSet M} `{Decision P} A (x : A) (X : M A) :
  x ∈ (guard P;; X) ↔ P ∧ x ∈ X.
Proof. set_solver. Qed.

(* ---- the variant notations the tree uses -------------------------------- *)
Lemma variant_minus (A B : gset Z) (junk : nat) : A ⊆ A ∪ B.
Proof. set_solver - junk. Qed.
Lemma variant_plus (A B : gset Z) (H : A ⊆ B) : A ⊆ B ∪ A.
Proof. set_solver + H. Qed.
Lemma variant_by (A B : gset Z) : A ⊆ A ∪ B.
Proof. set_solver by eauto. Qed.
(* argument position, the ProcInv.v:374 shape *)
Lemma variant_ltac (fd : nat) (D : gset nat) :
  (D ⊆ {[fd]} ∪ D -> True) -> True.
Proof. intros HH. exact (HH ltac:(set_solver)). Qed.


(* ---- the property the whole exercise is about --------------------------- *)
(* A trivial set goal under a context of exactly the shape a whole-function
   proof builds: 80 register facts over depth-20 insert towers, none of them
   mentioning the goal's sets.  This is the benchmark quoted in
   FastSetSolver.v's header — upstream [set_solver] takes ~20 s on it, the
   override takes ~0.1 s.  The [Timeout] makes a regression FAIL the build
   instead of merely making it slow; the margin is ~100x either way, so it
   does not flake under a loaded parallel build. *)
Section context_insensitivity.
  Context (W M : Type) (Rx : nat -> nat) (rg : M -> nat -> W)
          (upd : M -> nat -> W -> M) (v0 v1 v2 v3 v4 v5 v6 v7 : W)
          (P0 P1 P2 P3 P4 P5 P6 : W -> Prop)
          (Q0 Q1 Q2 Q3 Q4 Q5 Q6 : W -> Prop).

  Goal forall
    (m0 : M) (w0 : W) (m1 : M) (w1 : W) (m2 : M) (w2 : W) (m3 : M) (w3 : W)
    (m4 : M) (w4 : W) (m5 : M) (w5 : W) (m6 : M) (w6 : W) (m7 : M) (w7 : W)
    (m8 : M) (w8 : W) (m9 : M) (w9 : W) (m10 : M) (w10 : W) (m11 : M)
    (w11 : W) (m12 : M) (w12 : W) (m13 : M) (w13 : W) (m14 : M) (w14 : W)
    (m15 : M) (w15 : W) (m16 : M) (w16 : W) (m17 : M) (w17 : W) (m18 : M)
    (w18 : W) (m19 : M) (w19 : W) (m20 : M) (w20 : W) (m21 : M) (w21 : W)
    (m22 : M) (w22 : W) (m23 : M) (w23 : W) (m24 : M) (w24 : W) (m25 : M)
    (w25 : W) (m26 : M) (w26 : W) (m27 : M) (w27 : W) (m28 : M) (w28 : W)
    (m29 : M) (w29 : W) (m30 : M) (w30 : W) (m31 : M) (w31 : W) (m32 : M)
    (w32 : W) (m33 : M) (w33 : W) (m34 : M) (w34 : W) (m35 : M) (w35 : W)
    (m36 : M) (w36 : W) (m37 : M) (w37 : W) (m38 : M) (w38 : W) (m39 : M)
    (w39 : W) (m40 : M) (w40 : W) (m41 : M) (w41 : W) (m42 : M) (w42 : W)
    (m43 : M) (w43 : W) (m44 : M) (w44 : W) (m45 : M) (w45 : W) (m46 : M)
    (w46 : W) (m47 : M) (w47 : W) (m48 : M) (w48 : W) (m49 : M) (w49 : W)
    (m50 : M) (w50 : W) (m51 : M) (w51 : W) (m52 : M) (w52 : W) (m53 : M)
    (w53 : W) (m54 : M) (w54 : W) (m55 : M) (w55 : W) (m56 : M) (w56 : W)
    (m57 : M) (w57 : W) (m58 : M) (w58 : W) (m59 : M) (w59 : W) (m60 : M)
    (w60 : W) (m61 : M) (w61 : W) (m62 : M) (w62 : W) (m63 : M) (w63 : W)
    (m64 : M) (w64 : W) (m65 : M) (w65 : W) (m66 : M) (w66 : W) (m67 : M)
    (w67 : W) (m68 : M) (w68 : W) (m69 : M) (w69 : W) (m70 : M) (w70 : W)
    (m71 : M) (w71 : W) (m72 : M) (w72 : W) (m73 : M) (w73 : W) (m74 : M)
    (w74 : W) (m75 : M) (w75 : W) (m76 : M) (w76 : W) (m77 : M) (w77 : W)
    (m78 : M) (w78 : W) (m79 : M) (w79 : W)
    (h0 : rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m0 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) = w0)
    (h1 : forall q, rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m1 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) q) (Rx 10) = q)
    (h2 : forall q, P2 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m2 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q) /\ Q2 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m2 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q))
    (h3 : P3 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m3 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 3)) -> Q3 w3)
    (h4 : rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m4 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) = w4)
    (h5 : forall q, rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m5 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) q) (Rx 10) = q)
    (h6 : forall q, P6 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m6 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q) /\ Q6 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m6 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q))
    (h7 : P0 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m7 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 3)) -> Q0 w7)
    (h8 : rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m8 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) = w8)
    (h9 : forall q, rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m9 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) q) (Rx 10) = q)
    (h10 : forall q, P3 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m10 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q) /\ Q3 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m10 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q))
    (h11 : P4 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m11 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 3)) -> Q4 w11)
    (h12 : rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m12 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) = w12)
    (h13 : forall q, rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m13 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) q) (Rx 10) = q)
    (h14 : forall q, P0 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m14 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q) /\ Q0 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m14 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q))
    (h15 : P1 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m15 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 3)) -> Q1 w15)
    (h16 : rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m16 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) = w16)
    (h17 : forall q, rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m17 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) q) (Rx 10) = q)
    (h18 : forall q, P4 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m18 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q) /\ Q4 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m18 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q))
    (h19 : P5 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m19 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 3)) -> Q5 w19)
    (h20 : rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m20 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) = w20)
    (h21 : forall q, rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m21 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) q) (Rx 10) = q)
    (h22 : forall q, P1 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m22 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q) /\ Q1 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m22 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q))
    (h23 : P2 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m23 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 3)) -> Q2 w23)
    (h24 : rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m24 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) = w24)
    (h25 : forall q, rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m25 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) q) (Rx 10) = q)
    (h26 : forall q, P5 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m26 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q) /\ Q5 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m26 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q))
    (h27 : P6 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m27 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 3)) -> Q6 w27)
    (h28 : rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m28 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) = w28)
    (h29 : forall q, rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m29 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) q) (Rx 10) = q)
    (h30 : forall q, P2 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m30 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q) /\ Q2 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m30 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q))
    (h31 : P3 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m31 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 3)) -> Q3 w31)
    (h32 : rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m32 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) = w32)
    (h33 : forall q, rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m33 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) q) (Rx 10) = q)
    (h34 : forall q, P6 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m34 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q) /\ Q6 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m34 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q))
    (h35 : P0 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m35 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 3)) -> Q0 w35)
    (h36 : rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m36 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) = w36)
    (h37 : forall q, rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m37 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) q) (Rx 10) = q)
    (h38 : forall q, P3 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m38 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q) /\ Q3 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m38 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q))
    (h39 : P4 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m39 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 3)) -> Q4 w39)
    (h40 : rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m40 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) = w40)
    (h41 : forall q, rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m41 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) q) (Rx 10) = q)
    (h42 : forall q, P0 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m42 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q) /\ Q0 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m42 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q))
    (h43 : P1 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m43 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 3)) -> Q1 w43)
    (h44 : rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m44 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) = w44)
    (h45 : forall q, rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m45 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) q) (Rx 10) = q)
    (h46 : forall q, P4 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m46 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q) /\ Q4 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m46 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q))
    (h47 : P5 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m47 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 3)) -> Q5 w47)
    (h48 : rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m48 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) = w48)
    (h49 : forall q, rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m49 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) q) (Rx 10) = q)
    (h50 : forall q, P1 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m50 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q) /\ Q1 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m50 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q))
    (h51 : P2 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m51 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 3)) -> Q2 w51)
    (h52 : rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m52 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) = w52)
    (h53 : forall q, rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m53 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) q) (Rx 10) = q)
    (h54 : forall q, P5 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m54 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q) /\ Q5 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m54 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q))
    (h55 : P6 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m55 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 3)) -> Q6 w55)
    (h56 : rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m56 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) = w56)
    (h57 : forall q, rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m57 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) q) (Rx 10) = q)
    (h58 : forall q, P2 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m58 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q) /\ Q2 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m58 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q))
    (h59 : P3 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m59 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 3)) -> Q3 w59)
    (h60 : rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m60 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) = w60)
    (h61 : forall q, rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m61 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) q) (Rx 10) = q)
    (h62 : forall q, P6 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m62 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q) /\ Q6 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m62 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q))
    (h63 : P0 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m63 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 3)) -> Q0 w63)
    (h64 : rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m64 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) = w64)
    (h65 : forall q, rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m65 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) q) (Rx 10) = q)
    (h66 : forall q, P3 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m66 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q) /\ Q3 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m66 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q))
    (h67 : P4 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m67 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 3)) -> Q4 w67)
    (h68 : rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m68 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) = w68)
    (h69 : forall q, rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m69 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) q) (Rx 10) = q)
    (h70 : forall q, P0 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m70 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q) /\ Q0 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m70 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q))
    (h71 : P1 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m71 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 3)) -> Q1 w71)
    (h72 : rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m72 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) = w72)
    (h73 : forall q, rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m73 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) q) (Rx 10) = q)
    (h74 : forall q, P4 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m74 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q) /\ Q4 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m74 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q))
    (h75 : P5 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m75 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 3)) -> Q5 w75)
    (h76 : rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m76 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) = w76)
    (h77 : forall q, rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m77 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 10) q) (Rx 10) = q)
    (h78 : forall q, P1 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m78 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q) /\ Q1 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m78 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) q))
    (h79 : P2 (rg (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m79 (Rx 0) v0) (Rx 1) v1) (Rx 2) v2) (Rx 3) v3) (Rx 4) v4) (Rx 5) v5) (Rx 6) v6) (Rx 7) v7) (Rx 8) v0) (Rx 9) v1) (Rx 10) v2) (Rx 11) v3) (Rx 12) v4) (Rx 13) v5) (Rx 14) v6) (Rx 15) v7) (Rx 16) v0) (Rx 17) v1) (Rx 18) v2) (Rx 19) v3) (Rx 3)) -> Q2 w79)
    (X Y : gset nat) (a : nat),
    a ∈ X -> a ∈ X ∪ Y.
  Proof. intros. Timeout 10 set_solver. Qed.

  (* The converse guarantee: a context that is contradictory ABOUT SETS still
     closes a goal it shares no variable with, even though the relevance
     filter has never heard of that goal's variables.  This is why the filter
     keeps every set-mentioning hypothesis unconditionally. *)
  Goal forall (m0 m1 : M) (w0 : W)
    (h0 : rg m0 (Rx 1) = w0) (h1 : rg m1 (Rx 2) = w0)
    (Z1 : gset nat) (z : nat) (hin : z ∈ Z1) (hout : z ∉ Z1)
    (X Y : gset nat) (a : nat), a ∈ X ∩ Y.
  Proof. intros. Timeout 10 set_solver. Qed.
End context_insensitivity.
