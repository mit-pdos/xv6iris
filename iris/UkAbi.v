(* ===================================================================== *)
(* UkAbi.v -- the GENERIC user-entry conditions, stated on the SLOT'S KEY. *)
(*                                                                         *)
(* What a user program needs to know about the argc/argv area [exec()]     *)
(* leaves on its stack is NOT program-specific: it is a property of what   *)
(* exec builds, so it is defined ONCE here and handed to any user-mode     *)
(* program at entry.  UmodeAbi.v §5's [uargs] is that predicate on the OLD *)
(* tier, stated over the TABLE ([uv_rd pt M a n]: every byte of the window *)
(* sits on a page whose LEAF the model's load check passes).  This file    *)
(* re-cuts it on the KEY -- the image [M] and the permission map [π] --    *)
(* which is the move [uk_stack] (§7 below, lifted here out of UkSync.v)    *)
(* already made from                                                       *)
(* UmodeAbi.v's [uv_stack]:                                                *)
(*                                                                         *)
(*   uv_rd pt M a n   ~~>   uk_rd π M a n     (the page is IN π)           *)
(*   uargs pt M av argc lo ~~> uk_args π M av argc lo alen                 *)
(*                                                                         *)
(* THE READABILITY NOTION IS UkLoad's, EXACTLY.  [uk_rpage π va] says the  *)
(* page of [va] is in the key's permission map, which is literally         *)
(* [UkLoad.uk_load_ok] -- R needs no bit of its own (UserPerm.v §1:        *)
(* [perm_leaf] is [None] unless both U and R are set), and                 *)
(* [UserPerm.perm_of_R] turns in-the-map plus the-table-maps-it into the   *)
(* model's [uleaf_ok (Load Data) w] at every table realizing the key.      *)
(* [uk_rpage_load_ok] is the (definitional) bridge, so a window fact       *)
(* discharges a load leaf's permission premise directly.                   *)
(*                                                                         *)
(* NOTE THE DIRECTION.  [uv_rd -> uk_rd] would need the leaf-bit transfer  *)
(* run BACKWARDS ([uleaf_ok (Load Data) w -> pte_bit w 4 = true]), which   *)
(* UserPerm.v deliberately does not have; and [uk_rd -> uv_rd] is FALSE    *)
(* under the lazy key -- a first-touched page is readable in [π] and       *)
(* absent from the table (that is exactly what the load leaf's transparent *)
(* FAULT arm is for).  The two tiers' windows are therefore not            *)
(* inter-derivable, and nothing here tries.                                *)
(*                                                                         *)
(* THE LENGTHS ARE AN EXPLICIT PARAMETER, AND THAT IS WHAT MAKES THE GATE  *)
(* DECIDABLE.  [uargs]'s pointer clause is doubly existential -- there is  *)
(* a pointer [p] and a length [len] with ...  Both existentials are in     *)
(* fact DETERMINED -- [p] by the eight image bytes of the array slot, and  *)
(* [len] by the first NUL -- so this file states them as FUNCTIONS instead: *)
(*                                                                         *)
(*   [uk_argv_w M av i] / [uk_argv_p M av i]  the i-th pointer, computed    *)
(*       from the image as [uM_word] -- WHICH IS THE SHAPE THE LOAD LEAF   *)
(*       LEAVES IN THE REGISTER ([UkLoad.wp_uk_ld]'s [wval]), so the       *)
(*       reader and the leaf line up with no glue;                          *)
(*   [alen : Z -> Z]  the string lengths, a parameter of [uk_args].        *)
(*                                                                         *)
(* Every clause is then a bounded quantification over a decidable body,    *)
(* and [uk_args_dec] follows.  DECIDABILITY IS LOAD-BEARING, not a         *)
(* nicety: a program's entry gate is decided the way UexecCond.v's         *)
(* [sync_gate] is ([cond_entry_slot] does [destruct (decide (...))] and     *)
(* falls back to the generic WP on the negative branch), so an undecidable *)
(* [uk_args] would mean no slot could be minted until exec's post stopped  *)
(* being existential in the image.                                         *)
(*                                                                         *)
(* And the parameter costs nothing at a gate, because there is a CANONICAL *)
(* choice: [uk_slen M a] scans the image for the first NUL (fuel [2^31],   *)
(* which is [uargs]'s own bound on a string length), [uk_slen_ucstr] says  *)
(* it agrees with any witness, and [uk_args_c] is [uk_args] at it.  So     *)
(* "there is some assignment of lengths" and "the canonical one works" are *)
(* the same claim ([uk_args_canon]), and the latter is decidable.          *)
(*                                                                         *)
(* THE ARRAY'S NULL TERMINATOR IS A SEPARATE, NAMED CONJUNCT.              *)
(* [uk_argv_null π M av argc] says [argv[argc] = 0] (and that the slot is  *)
(* readable).  It is TRUE of what exec builds (kernel/exec.c: [ustack[argc] *)
(* = 0] before the copyout) and another program may read it, so it belongs *)
(* in the generic entry bundle -- but [echo] does NOT need it (its loop     *)
(* compares the cursor against [av + 8*argc] and never dereferences that   *)
(* slot).  Keeping it separately named lets echo ignore it and a future    *)
(* program ask for it.                                                     *)
(*                                                                         *)
(* Everything in this file is PURE (a [Prop] about [M] and [π]); it is the *)
(* key-level counterpart of UmodeAbi.v, and it is program-generic --       *)
(* per-program facts live in echo's / sh's own files.                      *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From Stdlib Require Znumtheory.   (* [Zmod_div_mod], for §7's 8-vs-16 alignment step *)
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvPtsto RiscvExtras.
Require Import UserBits UserPtTree.
Require Import ProcPtOwn.
Require Import UmodeMem UmodeFetch UmodeArith UmodeAbi.
Require Import WpUmodeLoad.   (* [uM_word] and its byte-window readings *)
Require Import UserPerm.
Require Import UkLoad.        (* [uk_load_ok] -- the load leaf's key premise *)
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §0 Two bounded-quantifier decision helpers.                             *)
(*                                                                         *)
(* Every clause below quantifies over a FINITE index range, which is what  *)
(* keeps the whole bundle decidable.  §7's [uk_stack_bytes_dec] is         *)
(* the one-off version of the first of these.                             *)
(* ===================================================================== *)

Lemma zbound_dec (P : Z -> Prop) `{HP : forall j : Z, Decision (P j)} (n : Z) :
  Decision (forall j : Z, 0 <= j < n -> P j).
Proof.
  destruct (decide (Forall P (seqZ 0 n))) as [Hf | Hf].
  - left. intros j Hj. rewrite Forall_forall in Hf. apply Hf.
    rewrite <- elem_of_list_In. apply elem_of_seqZ. lia.
  - right. intros H. apply Hf. rewrite Forall_forall. intros j Hj.
    rewrite <- elem_of_list_In in Hj. apply elem_of_seqZ in Hj. apply H. lia.
Defined.

Lemma nbound_dec (P : nat -> Prop) `{HP : forall j : nat, Decision (P j)} (k : nat) :
  Decision (forall j : nat, (j < k)%nat -> P j).
Proof.
  destruct (decide (Forall P (seq 0 k))) as [Hf | Hf].
  - left. intros j Hj. rewrite Forall_forall in Hf. apply Hf.
    rewrite <- elem_of_list_In. apply elem_of_seq. lia.
  - right. intros H. apply Hf. rewrite Forall_forall. intros j Hj.
    rewrite <- elem_of_list_In in Hj. apply elem_of_seq in Hj. apply H. lia.
Defined.

(* "the image has a byte here" and "the image has a NON-NUL byte here" --
   the two bodies the windows and the strings quantify over.  Kept LOCAL:
   their head symbol is [ex], so exporting them would put them in the way
   of every downstream [Decision (exists _, _)] goal. *)
Local Instance umem_byte_dec (M : gmap Z (bv 8)) (k : Z) :
  Decision (exists b : bv 8, M !! k = Some b).
Proof.
  destruct (M !! k) as [b |].
  - left. exists b. reflexivity.
  - right. intros (b & Hb). discriminate Hb.
Defined.

Local Instance umem_byte_nn_dec (M : gmap Z (bv 8)) (k : Z) :
  Decision (exists b : bv 8, M !! k = Some b /\ b <> ubyte0).
Proof.
  destruct (M !! k) as [b |].
  - destruct (decide (b = ubyte0)) as [-> | Hne].
    + right. intros (b' & Hb' & Hne'). injection Hb' as <-.
      exact (Hne' eq_refl).
    + left. exists b. exact (conj eq_refl Hne).
  - right. intros (b' & Hb' & _). discriminate Hb'.
Defined.

(* ===================================================================== *)
(* §1 READABLE PAGES AND READABLE WINDOWS ON THE KEY.                      *)
(*                                                                         *)
(* [uk_rpage] is §1's own [uk_xpage] / [uk_wpage] with NO bit demanded     *)
(* at all -- presence in the map IS readability.  [uk_rd] is UmodeAbi.v's  *)
(* [uv_rd] with its [urd_leaf] clause read on the key.                     *)
(* ===================================================================== *)

(* the page of [va] is a readable page of the key *)
Definition uk_rpage (π : gmap (mword 27) uperm) (va : mword 64) : Prop :=
  exists q : uperm, uperm_at π va = Some q.

Global Instance uk_rpage_dec (π : gmap (mword 27) uperm) (va : mword 64) :
  Decision (uk_rpage π va).
Proof.
  unfold uk_rpage, uperm_at.
  destruct (π !! svpn_of va) as [q |].
  - left. exists q. reflexivity.
  - right. intros (q & Hq). discriminate Hq.
Defined.

(* THE POINT OF THE NOTION: it is the load leaf's own key premise. *)
Lemma uk_rpage_load_ok (π : gmap (mword 27) uperm) (va : mword 64) :
  uk_rpage π va -> uk_load_ok π va.
Proof. exact (fun H => H). Qed.

Lemma uk_load_ok_rpage (π : gmap (mword 27) uperm) (va : mword 64) :
  uk_load_ok π va -> uk_rpage π va.
Proof. exact (fun H => H). Qed.

(* THE BRIDGE to the table, at every table realizing the key -- the
   load-side twin of UkSync.v's [sync_layout_of_key].  (A readable page of
   the key need NOT be mapped: see the header.  This says only that IF the
   table maps it, the model's load check passes on the leaf.) *)
Lemma uk_rpage_leaf (pt : uptd) (sz : Z) (π : gmap (mword 27) uperm)
    (va w : mword 64) :
  proc_pt_wf pt -> perm_of (ud_um pt) sz = π ->
  uk_rpage π va -> ud_um pt !! svpn_of va = Some w ->
  uleaf_ok (Load Data) w.
Proof.
  intros Hwf Hpm (q & Hq) Hw. unfold uperm_at in Hq. rewrite <- Hpm in Hq.
  exact (perm_of_R pt sz _ q w Hwf Hq Hw).
Qed.


(* ... and the same notion with a BIT demanded.  [uk_xpage] is what a
   program's text page must be; [uk_wpage] is what a store's page must be
   (the store leaf's key premise, [UkStore.uk_store_ok]).  Both are
   [uk_rpage] plus one flag, and both are decidable for the same reason. *)
(* the page of [va] is an X page of the key *)
Definition uk_xpage (π : gmap (mword 27) uperm) (va : mword 64) : Prop :=
  exists q : uperm, uperm_at π va = Some q /\ up_X q = true.

(* the page of [va] is a W page of the key *)
Definition uk_wpage (π : gmap (mword 27) uperm) (va : mword 64) : Prop :=
  exists q : uperm, uperm_at π va = Some q /\ up_W q = true.

Global Instance uk_xpage_dec (π : gmap (mword 27) uperm) (va : mword 64) :
  Decision (uk_xpage π va).
Proof.
  unfold uk_xpage, uperm_at.
  destruct (π !! svpn_of va) as [q|] eqn:E.
  - destruct (up_X q) eqn:Ex.
    + left. exists q. split; [ reflexivity | exact Ex ].
    + right. intros (q' & Hq' & Hx'). injection Hq' as <-. rewrite Ex in Hx'. discriminate.
  - right. intros (q' & Hq' & _). discriminate Hq'.
Defined.

Global Instance uk_wpage_dec (π : gmap (mword 27) uperm) (va : mword 64) :
  Decision (uk_wpage π va).
Proof.
  unfold uk_wpage, uperm_at.
  destruct (π !! svpn_of va) as [q|] eqn:E.
  - destruct (up_W q) eqn:Ex.
    + left. exists q. split; [ reflexivity | exact Ex ].
    + right. intros (q' & Hq' & Hx'). injection Hq' as <-. rewrite Ex in Hx'. discriminate.
  - right. intros (q' & Hq' & _). discriminate Hq'.
Defined.
(* [UmodeAbi.uv_rd] on the key: the same window with its leaf clause a
   readable page of [π].  The mapping is quantified PER BYTE rather than
   stated as one leaf, exactly as [uv_rd] does, so a window may cross a
   page while an individual (naturally aligned) access never does. *)
Record uk_rd (π : gmap (mword 27) uperm) (M : gmap Z (bv 8)) (a n : Z)
    : Prop := UkRd {
  ukrd_lo    : 0 <= a;
  ukrd_n0    : 0 <= n;
  ukrd_hi    : a + n <= 2 ^ 38;
  ukrd_page  : forall j : Z, 0 <= j < n ->
                 uk_rpage π (mword_of_int (a + j) : mword 64);
  ukrd_bytes : forall j : Z, 0 <= j < n -> exists b : bv 8, M !! (a + j) = Some b
}.

Global Instance uk_rd_dec (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
    (a n : Z) : Decision (uk_rd π M a n).
Proof.
  destruct (decide (0 <= a)) as [H1 | H1]; [ | right; intros []; auto ].
  destruct (decide (0 <= n)) as [H2 | H2]; [ | right; intros []; auto ].
  destruct (decide (a + n <= 2 ^ 38)) as [H3 | H3]; [ | right; intros []; auto ].
  destruct (zbound_dec (fun j : Z => uk_rpage π (mword_of_int (a + j) : mword 64)) n)
    as [H4 | H4]; [ | right; intros []; auto ].
  destruct (zbound_dec (fun j : Z => exists b : bv 8, M !! (a + j) = Some b) n)
    as [H5 | H5]; [ | right; intros []; auto ].
  left. constructor; assumption.
Defined.

(* a sub-window is readable ([uv_rd_sub]) *)
Lemma uk_rd_sub (π : gmap (mword 27) uperm) (M : gmap Z (bv 8)) (a n a' n' : Z) :
  uk_rd π M a n -> a <= a' -> 0 <= n' -> a' + n' <= a + n ->
  uk_rd π M a' n'.
Proof.
  intros [Hlo Hn0 Hhi Hpg Hb] Ha Hn' Hhi'.
  constructor; try lia.
  - intros j Hj. replace (a' + j) with (a + (a' - a + j)) by lia.
    apply Hpg. lia.
  - intros j Hj. replace (a' + j) with (a + (a' - a + j)) by lia.
    apply Hb. lia.
Qed.

(* a dom-preserving image update keeps readability ([uv_rd_dom]) *)
Lemma uk_rd_dom (π : gmap (mword 27) uperm) (M M' : gmap Z (bv 8)) (a n : Z) :
  (forall k : Z, is_Some (M !! k) -> is_Some (M' !! k)) ->
  uk_rd π M a n -> uk_rd π M' a n.
Proof.
  intros Hdom [Hlo Hn0 Hhi Hpg Hb]. constructor; try assumption.
  intros j Hj. destruct (Hb j Hj) as [b HMb].
  destruct (Hdom (a + j) (mk_is_Some _ _ HMb)) as [b' Hb']. eauto.
Qed.

(* an update that leaves every byte at or above [lo] alone keeps a window
   that lives there ([uv_rd_above]) *)
Lemma uk_rd_above (π : gmap (mword 27) uperm) (M M' : gmap Z (bv 8))
    (a n lo : Z) :
  (forall k : Z, lo <= k -> M' !! k = M !! k) ->
  lo <= a -> uk_rd π M a n -> uk_rd π M' a n.
Proof.
  intros Heq Hlo [Hlo' Hn0 Hhi Hpg Hb]. constructor; try assumption.
  intros j Hj. rewrite (Heq (a + j) ltac:(lia)). exact (Hb j Hj).
Qed.

(* ===================================================================== *)
(* §2 C STRINGS.                                                           *)
(*                                                                         *)
(* [UmodeAbi.ucstr M a len] is already a fact about the IMAGE ALONE (it    *)
(* says nothing about mapping, which is why it is paired with a window),   *)
(* so it ports UNCHANGED and is REUSED here rather than restated.  What    *)
(* this section adds is its decision procedure and the canonical length.   *)
(* ===================================================================== *)

Global Instance ucstr_dec (M : gmap Z (bv 8)) (a len : Z) :
  Decision (ucstr M a len).
Proof.
  destruct (decide (0 <= len)) as [H1 | H1]; [ | right; intros []; auto ].
  destruct (zbound_dec
              (fun j : Z => exists b : bv 8, M !! (a + j) = Some b /\ b <> ubyte0) len)
    as [H2 | H2]; [ | right; intros []; auto ].
  destruct (decide (M !! (a + len) = Some ubyte0)) as [H3 | H3];
    [ | right; intros []; auto ].
  left. constructor; assumption.
Defined.

(* shifting a string one byte to the right *)
Lemma ucstr_shift (M : gmap Z (bv 8)) (a len : Z) :
  0 <= len -> ucstr M a (len + 1) -> ucstr M (a + 1) len.
Proof.
  intros Hlen [Hl Hb Hn]. constructor.
  - exact Hlen.
  - intros j Hj. replace (a + 1 + j) with (a + (j + 1)) by lia.
    apply Hb. lia.
  - replace (a + 1 + len) with (a + (len + 1)) by lia. exact Hn.
Qed.

(* THE CANONICAL LENGTH: scan for the first NUL.  The fuel is [uargs]'s own
   bound on a string length (2^31), so the scan never runs out on a string
   the ABI admits -- see [uk_slen_ucstr].  Nothing EVALUATES this: a gate
   [destruct]s its decision, it does not compute it. *)
Definition uk_slen_fuel : nat := Z.to_nat (2 ^ 31).

Fixpoint uscan (M : gmap Z (bv 8)) (a : Z) (f : nat) : nat :=
  match f with
  | O => O
  | S f' =>
      match M !! a with
      | Some b => if bool_decide (b = ubyte0) then O else S (uscan M (a + 1) f')
      | None => O
      end
  end.

Definition uk_slen (M : gmap Z (bv 8)) (a : Z) : Z :=
  Z.of_nat (uscan M a uk_slen_fuel).

Lemma uscan_ucstr (M : gmap Z (bv 8)) (f : nat) :
  forall (l : nat) (a : Z),
    (l < f)%nat -> ucstr M a (Z.of_nat l) -> uscan M a f = l.
Proof.
  induction f as [ | f IH ]; intros l a Hlf Hs.
  { exfalso. lia. }
  destruct l as [ | l ].
  - cbn [uscan].
    pose proof (ucs_nul _ _ _ Hs) as Hn.
    replace (a + Z.of_nat 0) with a in Hn by lia. rewrite Hn.
    rewrite (bool_decide_eq_true_2 (ubyte0 = ubyte0) eq_refl). reflexivity.
  - cbn [uscan].
    destruct (ucs_body _ _ _ Hs 0 ltac:(lia)) as (b & Hb & Hb0).
    rewrite Z.add_0_r in Hb. rewrite Hb.
    rewrite (bool_decide_eq_false_2 (b = ubyte0) Hb0).
    f_equal. apply IH; [ lia | ].
    apply (ucstr_shift M a (Z.of_nat l) ltac:(lia)).
    replace (Z.of_nat l + 1) with (Z.of_nat (S l)) by lia. exact Hs.
Qed.

(* the canonical length agrees with any witness the ABI admits *)
Lemma uk_slen_ucstr (M : gmap Z (bv 8)) (a len : Z) :
  0 <= len < 2 ^ 31 -> ucstr M a len -> uk_slen M a = len.
Proof.
  intros Hlen Hs. unfold uk_slen, uk_slen_fuel.
  change (2 ^ 31) with 2147483648 in Hlen |- *.
  assert (Hlt : (Z.to_nat len < Z.to_nat 2147483648)%nat) by lia.
  rewrite (uscan_ucstr M (Z.to_nat 2147483648) (Z.to_nat len) a Hlt
             ltac:(rewrite Z2Nat.id; [ exact Hs | lia ])).
  lia.
Qed.

(* ===================================================================== *)
(* §3 THE ARGUMENT AREA, ON THE KEY.                                       *)
(*                                                                         *)
(* [UmodeAbi.uargs pt M av argc lo], clause for clause:                    *)
(*                                                                         *)
(*   ua_al   : Z.rem av 8 = 0                    -> uka_al    (verbatim)   *)
(*   ua_lo   : lo <= av                          -> uka_lo    (verbatim)   *)
(*   ua_argc : 0 <= argc < 2 ^ 31                -> uka_argc  (verbatim)   *)
(*   ua_rd   : uv_rd pt M av (8 * argc)          -> uka_rd    (on [π])     *)
(*   ua_ptr  : forall i < argc, exists p len,                              *)
(*               uM_bytes M (av + 8*i) 8 (moi p)   -> [uk_argv_p] IS that  *)
(*                                                    word (see below)     *)
(*               /\ 0 <= p                         -> free ([uint] >= 0)   *)
(*               /\ lo <= p                        -> uka_ptr, 1st         *)
(*               /\ 0 <= len < 2 ^ 31              -> uka_ptr, 2nd         *)
(*               /\ ucstr M p len                  -> uka_ptr, 3rd         *)
(*               /\ uv_rd pt M p (len + 1)         -> uka_ptr, 4th (on π)  *)
(*                                                                         *)
(* The two existentials are gone and nothing was weakened: [p] is the      *)
(* eight image bytes of the slot read as a word ([uk_argv_ptr] recovers    *)
(* [uargs]'s [uM_bytes] clause), and [len] is the parameter [alen].        *)
(* ===================================================================== *)

(* the i-th argv pointer, as the image spells it -- and as the load leaf
   leaves it in a register ([UkLoad.wp_uk_ld]'s [wval = uM_word M (uint va) 8]) *)
Definition uk_argv_w (M : gmap Z (bv 8)) (av i : Z) : mword 64 :=
  uM_word M (av + 8 * i) 8.

Definition uk_argv_p (M : gmap Z (bv 8)) (av i : Z) : Z :=
  uint (uk_argv_w M av i).

Lemma uk_argv_p_range (M : gmap Z (bv 8)) (av i : Z) :
  0 <= uk_argv_p M av i < Z64.
Proof.
  unfold uk_argv_p.
  assert (Hm : uint (uk_argv_w M av i) = uint (uk_argv_w M av i) mod Z64).
  { pose proof (moi_unsigned (uint (uk_argv_w M av i))) as H.
    rewrite (moi_of_uint (uk_argv_w M av i)) in H.
    rewrite <- uint_unsigned in H. exact H. }
  pose proof (Z.mod_pos_bound (uint (uk_argv_w M av i)) Z64
                ltac:(unfold Z64; lia)) as Hb.
  lia.
Qed.

Lemma uk_argv_p_w (M : gmap Z (bv 8)) (av i : Z) :
  (mword_of_int (uk_argv_p M av i) : mword 64) = uk_argv_w M av i.
Proof. unfold uk_argv_p. apply moi_of_uint. Qed.

(* THE ARGUMENT AREA.  Everything -- the array and every string -- is at or
   above [lo], the single bound that makes the whole area disjoint from the
   frames a program carves BELOW its entry sp ([uk_args_above]).  In the
   image [exec()] builds, [lo] is the entry sp. *)
Record uk_args (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
    (av argc lo : Z) (alen : Z -> Z) : Prop := UkArgs {
  uka_al   : Z.rem av 8 = 0;
  uka_lo   : lo <= av;
  uka_argc : 0 <= argc < 2 ^ 31;
  uka_rd   : uk_rd π M av (8 * argc);
  uka_ptr  : forall i : Z, 0 <= i < argc ->
               lo <= uk_argv_p M av i /\
               0 <= alen i < 2 ^ 31 /\
               ucstr M (uk_argv_p M av i) (alen i) /\
               uk_rd π M (uk_argv_p M av i) (alen i + 1)
}.

Global Instance uk_args_dec (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
    (av argc lo : Z) (alen : Z -> Z) : Decision (uk_args π M av argc lo alen).
Proof.
  destruct (decide (Z.rem av 8 = 0)) as [H1 | H1]; [ | right; intros []; auto ].
  destruct (decide (lo <= av)) as [H2 | H2]; [ | right; intros []; auto ].
  destruct (decide (0 <= argc < 2 ^ 31)) as [H3 | H3]; [ | right; intros []; auto ].
  destruct (decide (uk_rd π M av (8 * argc))) as [H4 | H4]; [ | right; intros []; auto ].
  destruct (zbound_dec
              (fun i : Z =>
                 lo <= uk_argv_p M av i /\
                 0 <= alen i < 2 ^ 31 /\
                 ucstr M (uk_argv_p M av i) (alen i) /\
                 uk_rd π M (uk_argv_p M av i) (alen i + 1)) argc)
    as [H5 | H5]; [ | right; intros []; auto ].
  left. constructor; assumption.
Defined.

(* THE CANONICAL FORM -- [uk_args] at the scanned lengths.  This is what a
   gate decides: it names no [alen], and by [uk_args_canon] it is implied
   by every instance of the parametric form, so nothing is lost. *)
Definition uk_slens (M : gmap Z (bv 8)) (av : Z) : Z -> Z :=
  fun i : Z => uk_slen M (uk_argv_p M av i).

Definition uk_args_c (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
    (av argc lo : Z) : Prop := uk_args π M av argc lo (uk_slens M av).

Global Instance uk_args_c_dec (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
    (av argc lo : Z) : Decision (uk_args_c π M av argc lo).
Proof. unfold uk_args_c. apply uk_args_dec. Defined.

Lemma uk_args_canon (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
    (av argc lo : Z) (alen : Z -> Z) :
  uk_args π M av argc lo alen -> uk_args_c π M av argc lo.
Proof.
  intros [Hal Hlo Hargc Hrd Hptr]. unfold uk_args_c.
  constructor; try assumption.
  intros i Hi. destruct (Hptr i Hi) as (Hp & Hlen & Hs & Hr).
  unfold uk_slens.
  rewrite (uk_slen_ucstr M (uk_argv_p M av i) (alen i) Hlen Hs).
  exact (conj Hp (conj Hlen (conj Hs Hr))).
Qed.

Lemma uk_args_c_ex (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
    (av argc lo : Z) :
  uk_args_c π M av argc lo -> exists alen : Z -> Z, uk_args π M av argc lo alen.
Proof. intro H. exists (uk_slens M av). exact H. Qed.

(* ===================================================================== *)
(* §4 THE ARRAY'S NULL TERMINATOR -- a SEPARATE, NAMED conjunct.          *)
(*                                                                         *)
(* [exec()] writes [ustack[argc] = 0] before the copyout (kernel/exec.c),  *)
(* so this is true of every image exec builds; [echo] does not need it.    *)
(* The window clause is here too, so a program that DOES read the slot     *)
(* gets the access's permission and byte facts from the same conjunct.     *)
(* ===================================================================== *)

Record uk_argv_null (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
    (av argc : Z) : Prop := UkArgvNull {
  ukan_rd   : uk_rd π M (av + 8 * argc) 8;
  ukan_zero : uM_bytes M (av + 8 * argc) 8 (mword_of_int 0 : mword 64)
}.

Global Instance uk_argv_null_dec (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
    (av argc : Z) : Decision (uk_argv_null π M av argc).
Proof.
  destruct (decide (uk_rd π M (av + 8 * argc) 8)) as [H1 | H1];
    [ | right; intros []; auto ].
  destruct (nbound_dec
              (fun j : nat =>
                 M !! (av + 8 * argc + Z.of_nat j)
                 = Some (nth_byte (mword_of_int 0 : mword 64) j)) 8)
    as [H2 | H2]; [ | right; intros []; auto ].
  left. constructor; assumption.
Defined.

(* ===================================================================== *)
(* §5 FRAME LEMMAS: the area survives everything a program does below it.  *)
(* ===================================================================== *)

(* the eight bytes of one array slot determine the pointer, so an update
   that leaves them alone leaves the pointer alone *)
Lemma uk_argv_w_ext (M M' : gmap Z (bv 8)) (av i : Z) :
  (forall j : nat, (j < 8)%nat ->
     M' !! (av + 8 * i + Z.of_nat j) = M !! (av + 8 * i + Z.of_nat j)) ->
  (forall j : nat, (j < 8)%nat ->
     exists b : bv 8, M !! (av + 8 * i + Z.of_nat j) = Some b) ->
  uk_argv_w M' av i = uk_argv_w M av i.
Proof.
  intros Heq Hex. unfold uk_argv_w.
  assert (Hb : uM_bytes M (av + 8 * i) 8 (uM_word M (av + 8 * i) 8))
    by exact (uM_word_bytes M (av + 8 * i) 8 ltac:(lia) Hex).
  assert (Hb' : uM_bytes M' (av + 8 * i) 8 (uM_word M' (av + 8 * i) 8)).
  { apply (uM_word_bytes M' (av + 8 * i) 8 ltac:(lia)).
    intros j Hj. destruct (Hex j Hj) as (b & Hbb).
    exists b. rewrite (Heq j Hj). exact Hbb. }
  apply (uM_bytes_inj M' (av + 8 * i)); [ exact Hb' | ].
  intros j Hj. rewrite (Heq j Hj). exact (Hb j Hj).
Qed.

(* THE FRAME LEMMA ([uargs_above]): an image update that leaves every byte
   at or above [lo] alone keeps the whole argument area -- which is the
   shape every stack store BELOW the entry sp has. *)
Lemma uk_args_above (π : gmap (mword 27) uperm) (M M' : gmap Z (bv 8))
    (av argc lo : Z) (alen : Z -> Z) :
  (forall k : Z, lo <= k -> M' !! k = M !! k) ->
  uk_args π M av argc lo alen -> uk_args π M' av argc lo alen.
Proof.
  intros Heq HA.
  pose proof HA as [Hal Hlo Hargc Hrd Hptr].
  pose proof (ukrd_lo _ _ _ _ Hrd) as Hav0.
  assert (Hw : forall i : Z, 0 <= i < argc -> uk_argv_w M' av i = uk_argv_w M av i).
  { intros i Hi.
    apply uk_argv_w_ext.
    - intros j Hj. apply Heq. lia.
    - intros j Hj.
      destruct (ukrd_bytes _ _ _ _ Hrd (8 * i + Z.of_nat j) ltac:(lia)) as (b & Hb).
      exists b. replace (av + 8 * i + Z.of_nat j) with (av + (8 * i + Z.of_nat j)) by lia.
      exact Hb. }
  assert (Hp : forall i : Z, 0 <= i < argc -> uk_argv_p M' av i = uk_argv_p M av i).
  { intros i Hi. unfold uk_argv_p. rewrite (Hw i Hi). reflexivity. }
  constructor; try assumption.
  - exact (uk_rd_above π M M' av (8 * argc) lo Heq Hlo Hrd).
  - intros i Hi. rewrite (Hp i Hi).
    destruct (Hptr i Hi) as (Hlop & Hlen & Hs & Hr).
    split; [ exact Hlop | ]. split; [ exact Hlen | ]. split.
    + exact (ucstr_above M M' (uk_argv_p M av i) (alen i) lo Heq Hlop Hs).
    + exact (uk_rd_above π M M' (uk_argv_p M av i) (alen i + 1) lo Heq Hlop Hr).
Qed.

Lemma uk_argv_null_above (π : gmap (mword 27) uperm) (M M' : gmap Z (bv 8))
    (av argc lo : Z) :
  (forall k : Z, lo <= k -> M' !! k = M !! k) ->
  lo <= av -> 0 <= argc ->
  uk_argv_null π M av argc -> uk_argv_null π M' av argc.
Proof.
  intros Heq Hlo Hargc [Hrd Hz]. constructor.
  - exact (uk_rd_above π M M' (av + 8 * argc) 8 lo Heq ltac:(lia) Hrd).
  - intros j Hj. rewrite (Heq (av + 8 * argc + Z.of_nat j) ltac:(lia)).
    exact (Hz j Hj).
Qed.

(* the bound may always be lowered ([uargs_lo_le]) *)
Lemma uk_args_lo_le (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
    (av argc lo lo' : Z) (alen : Z -> Z) :
  lo' <= lo -> uk_args π M av argc lo alen -> uk_args π M av argc lo' alen.
Proof.
  intros Hle [Hal Hlo Hargc Hrd Hptr]. constructor; try assumption; try lia.
  intros i Hi. destruct (Hptr i Hi) as (Hlop & Hrest).
  split; [ lia | exact Hrest ].
Qed.

(* ===================================================================== *)
(* §6 THE READERS -- the argument area in the shape the LEAVES consume.    *)
(*                                                                         *)
(* Each of these hands back exactly the premise list of a UkLoad.v leaf,   *)
(* in its order, so a call site can pass them straight through.  They are  *)
(* the argument area's counterpart of §7's [uk_stack_slot].                *)
(* ===================================================================== *)

(* ONE BYTE anywhere in a readable window -- [wp_uk_lbu]'s premises (it
   discharges alignment and the in-page bound itself) *)
Lemma uk_rd_byte (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
    (a n k : Z) (va : mword 64) :
  uk_rd π M a n -> a <= k < a + n -> va = (mword_of_int k : mword 64) ->
  uint va = k /\
  uk_load_ok π va /\
  uva_canon va /\
  (exists b : bv 8, M !! (uint va) = Some b).
Proof.
  intros HR Hk Hva.
  pose proof (ukrd_lo _ _ _ _ HR) as Ha0.
  pose proof (ukrd_hi _ _ _ _ HR) as Hhi.
  change (2 ^ 38) with 274877906944 in Hhi.
  assert (Hu : uint va = k)
    by (rewrite Hva; apply uint_moi; unfold Z64; lia).
  split_and!.
  - exact Hu.
  - apply uk_rpage_load_ok.
    pose proof (ukrd_page _ _ _ _ HR (k - a) ltac:(lia)) as Hpg.
    replace (a + (k - a)) with k in Hpg by lia.
    rewrite Hva. exact Hpg.
  - apply uva_canon_small. rewrite <- uint_unsigned. rewrite Hu. lia.
  - destruct (ukrd_bytes _ _ _ _ HR (k - a) ltac:(lia)) as (b & Hb).
    replace (a + (k - a)) with k in Hb by lia.
    exists b. rewrite Hu. exact Hb.
Qed.

(* ONE 8-BYTE ARRAY SLOT: every side condition [wp_uk_ld] needs at
   [argv + 8*i], plus the value the load leaves in the register. *)
Lemma uk_args_slot (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
    (av argc lo : Z) (alen : Z -> Z) (i : Z) (va : mword 64) :
  uk_args π M av argc lo alen -> 0 <= i < argc ->
  va = (mword_of_int (av + 8 * i) : mword 64) ->
  uint va = av + 8 * i /\
  uk_load_ok π va /\
  uva_canon va /\
  Z.rem (uint va) 4096 <= 4088 /\
  is_aligned_vaddr (Virtaddr va) 8 = true /\
  (forall j : nat, (j < 8)%nat ->
     exists b : bv 8, M !! (uint va + Z.of_nat j) = Some b) /\
  uk_argv_w M av i = uM_word M (uint va) 8.
Proof.
  intros HA Hi Hva.
  pose proof HA as [Hal Hlo Hargc Hrd Hptr].
  pose proof (ukrd_lo _ _ _ _ Hrd) as Hav0.
  pose proof (ukrd_hi _ _ _ _ Hrd) as Hhi.
  rewrite Z.rem_mod_nonneg in Hal; [ | lia | lia ].
  assert (Ha8 : (av + 8 * i) mod 8 = 0).
  { rewrite Zplus_mod. rewrite Hal. rewrite (Z.mul_comm 8 i).
    rewrite Z_mod_mult. reflexivity. }
  destruct (uv_slot8_facts (av + 8 * i) va ltac:(lia) Ha8 ltac:(lia) Hva)
    as (Hu & Hcan & Hpg & Hali).
  split_and!; try assumption.
  - apply uk_rpage_load_ok.
    pose proof (ukrd_page _ _ _ _ Hrd (8 * i) ltac:(lia)) as Hp.
    rewrite Hva. exact Hp.
  - intros j Hj. rewrite Hu.
    destruct (ukrd_bytes _ _ _ _ Hrd (8 * i + Z.of_nat j) ltac:(lia)) as (b & Hb).
    exists b. replace (av + 8 * i + Z.of_nat j) with (av + (8 * i + Z.of_nat j)) by lia.
    exact Hb.
  - rewrite Hu. reflexivity.
Qed.

(* ...and [uargs]'s own [uM_bytes] clause, recovered *)
Lemma uk_args_ptr_bytes (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
    (av argc lo : Z) (alen : Z -> Z) (i : Z) :
  uk_args π M av argc lo alen -> 0 <= i < argc ->
  uM_bytes M (av + 8 * i) 8 (mword_of_int (uk_argv_p M av i) : mword 64).
Proof.
  intros HA Hi. rewrite uk_argv_p_w. unfold uk_argv_w.
  apply (uM_word_bytes M (av + 8 * i) 8 ltac:(lia)).
  intros j Hj.
  destruct (ukrd_bytes _ _ _ _ (uka_rd _ _ _ _ _ _ HA)
              (8 * i + Z.of_nat j) ltac:(lia)) as (b & Hb).
  exists b. replace (av + 8 * i + Z.of_nat j) with (av + (8 * i + Z.of_nat j)) by lia.
  exact Hb.
Qed.

(* THE STRING at [argv[i]]: the pointer's bound, the length's bound, the
   NUL-termination and the readable run -- [uargs]' pointer clause, minus
   the two existentials *)
Lemma uk_args_str (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
    (av argc lo : Z) (alen : Z -> Z) (i : Z) :
  uk_args π M av argc lo alen -> 0 <= i < argc ->
  lo <= uk_argv_p M av i /\
  0 <= alen i < 2 ^ 31 /\
  ucstr M (uk_argv_p M av i) (alen i) /\
  uk_rd π M (uk_argv_p M av i) (alen i + 1).
Proof. intros HA Hi. exact (uka_ptr _ _ _ _ _ _ HA i Hi). Qed.

(* ONE BYTE of the string at [argv[i]], WITH THE SCAN'S DICHOTOMY: this is
   what a [strlen] loop consumes -- the byte is there, it is loadable, and
   it is NUL exactly at the end (compare UProofEchoA's [Hbex]). *)
Lemma uk_args_str_byte (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
    (av argc lo : Z) (alen : Z -> Z) (i j : Z) (va : mword 64) :
  uk_args π M av argc lo alen -> 0 <= i < argc -> 0 <= j <= alen i ->
  va = (mword_of_int (uk_argv_p M av i + j) : mword 64) ->
  uint va = uk_argv_p M av i + j /\
  uk_load_ok π va /\
  uva_canon va /\
  (exists b : bv 8, M !! (uint va) = Some b /\ (b = ubyte0 <-> j = alen i)).
Proof.
  intros HA Hi Hj Hva.
  destruct (uk_args_str π M av argc lo alen i HA Hi) as (Hlop & Hlen & Hs & Hr).
  destruct (uk_rd_byte π M (uk_argv_p M av i) (alen i + 1)
              (uk_argv_p M av i + j) va Hr ltac:(lia) Hva)
    as (Hu & Hok & Hcan & _).
  split; [ exact Hu | ]. split; [ exact Hok | ]. split; [ exact Hcan | ].
  rewrite Hu.
  destruct (Z.eq_dec j (alen i)) as [He | Hne].
  - exists ubyte0. rewrite He.
    split; [ exact (ucs_nul _ _ _ Hs) | ].
    split; [ intros _; reflexivity | intros _; reflexivity ].
  - destruct (ucs_body _ _ _ Hs j ltac:(lia)) as (b & Hb & Hb0).
    exists b. split; [ exact Hb | ].
    split; [ intro He; exfalso; exact (Hb0 He)
           | intro He; exfalso; exact (Hne He) ].
Qed.

(* THE TERMINATOR's slot, for a program that does read it: [wp_uk_ld]'s
   premises at [argv + 8*argc], and the zero the load leaves. *)
Lemma uk_argv_null_slot (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
    (av argc : Z) (va : mword 64) :
  0 <= av -> Z.rem av 8 = 0 -> 0 <= argc ->
  uk_argv_null π M av argc ->
  va = (mword_of_int (av + 8 * argc) : mword 64) ->
  uint va = av + 8 * argc /\
  uk_load_ok π va /\
  uva_canon va /\
  Z.rem (uint va) 4096 <= 4088 /\
  is_aligned_vaddr (Virtaddr va) 8 = true /\
  (forall j : nat, (j < 8)%nat ->
     exists b : bv 8, M !! (uint va + Z.of_nat j) = Some b) /\
  (mword_of_int 0 : mword 64) = uM_word M (uint va) 8.
Proof.
  intros Hav Hal Hargc HN Hva.
  pose proof HN as [Hrd Hz].
  pose proof (ukrd_lo _ _ _ _ Hrd) as Hav0.
  pose proof (ukrd_hi _ _ _ _ Hrd) as Hhi.
  rewrite Z.rem_mod_nonneg in Hal; [ | lia | lia ].
  assert (Ha8 : (av + 8 * argc) mod 8 = 0).
  { rewrite Zplus_mod. rewrite Hal. rewrite (Z.mul_comm 8 argc).
    rewrite Z_mod_mult. reflexivity. }
  destruct (uv_slot8_facts (av + 8 * argc) va ltac:(lia) Ha8 ltac:(lia) Hva)
    as (Hu & Hcan & Hpg & Hali).
  split_and!; try assumption.
  - apply uk_rpage_load_ok.
    pose proof (ukrd_page _ _ _ _ Hrd 0 ltac:(lia)) as Hp.
    rewrite Z.add_0_r in Hp. rewrite Hva. exact Hp.
  - intros j Hj. rewrite Hu.
    destruct (ukrd_bytes _ _ _ _ Hrd (Z.of_nat j) ltac:(lia)) as (b & Hb).
    exists b. exact Hb.
  - rewrite Hu.
    apply (uM_bytes_inj M (av + 8 * argc)); [ exact Hz | ].
    apply (uM_word_bytes M (av + 8 * argc) 8 ltac:(lia)).
    intros j Hj.
    destruct (ukrd_bytes _ _ _ _ Hrd (Z.of_nat j) ltac:(lia)) as (b & Hb).
    exists b. exact Hb.
Qed.

(* ===================================================================== *)
(* §7 THE STACK BUDGET, on the key.                                       *)
(*                                                                        *)
(* [UmodeAbi.uv_stack]'s counterpart: the contiguous, 16-aligned, in-page *)
(* run of writable bytes BELOW a function's entry sp that its frames and  *)
(* its callees' frames live in.  The one clause that changes is           *)
(* [us_leaf] -- the page is a W page of the key ([uk_wpage]) rather than  *)
(* a table leaf the model's store check passes -- and the two budget      *)
(* lemmas ([uk_stack_split], [uk_stack_slot]) are UmodeAbi's re-read on   *)
(* that clause.                                                          *)
(*                                                                        *)
(* GENERIC, like everything else here: every verified program carves      *)
(* frames, and [UexecCond.v]'s entry gate decides this predicate about    *)
(* the key exactly as it decides [uk_args].                               *)
(* ===================================================================== *)

(* [UmodeAbi.uv_stack] on the key: the same budget with its leaf clause a
   W page of [π] *)
Record uk_stack (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
    (sp0 : mword 64) (n : Z) : Prop := UkStack {
  uks_al    : Z.rem (uint sp0) 16 = 0;
  uks_n0    : 0 <= n;
  uks_n16   : Z.rem n 16 = 0;
  uks_page  : Z.rem (uint sp0 - n) 4096 + n <= 4096;
  uks_lo    : 4096 <= uint sp0 - n;
  uks_canon : uint sp0 <= 2 ^ 38;
  uks_leaf  : 0 < n -> uk_wpage π (add_vec_int sp0 (- n));
  uks_bytes : forall j : Z, 0 <= j < n ->
                exists b : bv 8, M !! (uint sp0 - n + j) = Some b
}.

(* the byte clause, as a bounded decidable [Forall] *)
Lemma uk_stack_bytes_dec (M : gmap Z (bv 8)) (a n : Z) :
  Decision (forall j : Z, 0 <= j < n -> exists b : bv 8, M !! (a + j) = Some b).
Proof.
  destruct (decide (Forall (fun j : Z => is_Some (M !! (a + j))) (seqZ 0 n))) as [Hf | Hf].
  - left. intros j Hj.
    rewrite Forall_forall in Hf.
    destruct (Hf j) as [b Hb];
      [ rewrite <- elem_of_list_In; apply elem_of_seqZ; lia | ].
    exists b. exact Hb.
  - right. intros H. apply Hf. rewrite Forall_forall. intros j Hj.
    rewrite <- elem_of_list_In in Hj. apply elem_of_seqZ in Hj.
    destruct (H j ltac:(lia)) as [b Hb]. exists b. exact Hb.
Defined.

Global Instance uk_stack_dec (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
    (sp0 : mword 64) (n : Z) : Decision (uk_stack π M sp0 n).
Proof.
  destruct (decide (Z.rem (uint sp0) 16 = 0)) as [H1|H1]; [ | right; intros []; auto ].
  destruct (decide (0 <= n)) as [H2|H2]; [ | right; intros []; auto ].
  destruct (decide (Z.rem n 16 = 0)) as [H3|H3]; [ | right; intros []; auto ].
  destruct (decide (Z.rem (uint sp0 - n) 4096 + n <= 4096)) as [H4|H4]; [ | right; intros []; auto ].
  destruct (decide (4096 <= uint sp0 - n)) as [H5|H5]; [ | right; intros []; auto ].
  destruct (decide (uint sp0 <= 2 ^ 38)) as [H6|H6]; [ | right; intros []; auto ].
  destruct (decide (0 < n)) as [Hn|Hn].
  - destruct (decide (uk_wpage π (add_vec_int sp0 (- n)))) as [H7|H7];
      [ | right; intros []; auto ].
    destruct (uk_stack_bytes_dec M (uint sp0 - n) n) as [H8|H8]; [ | right; intros []; auto ].
    left. constructor; try assumption. intros _. exact H7.
  - destruct (uk_stack_bytes_dec M (uint sp0 - n) n) as [H8|H8]; [ | right; intros []; auto ].
    left. constructor; try assumption. intros Hc. exfalso. exact (Hn Hc).
Defined.

(* the budget is unmoved by an image update that keeps the keys *)
Lemma uk_stack_dom (π : gmap (mword 27) uperm) (M M' : gmap Z (bv 8))
    (sp0 : mword 64) (n : Z) :
  (forall a : Z, is_Some (M !! a) -> is_Some (M' !! a)) ->
  uk_stack π M sp0 n -> uk_stack π M' sp0 n.
Proof.
  intros Hdom [Hal Hn0 Hn16 Hpg Hlo Hc Hleaf Hb].
  constructor; try assumption.
  intros j Hj. destruct (Hb j Hj) as [b HMb].
  destruct (Hdom (uint sp0 - n + j) (mk_is_Some _ _ HMb)) as [b' Hb'].
  eauto.
Qed.

(* the split, verbatim [UmodeAbi.uv_stack_split] *)
Lemma uk_stack_split (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
    (sp0 : mword 64) (n n1 n2 : Z) :
  n1 + n2 = n ->
  0 <= n1 -> Z.rem n1 16 = 0 -> 0 <= n2 ->
  uk_stack π M sp0 n ->
  uk_stack π M sp0 n1 /\ uk_stack π M (add_vec_int sp0 (- n1)) n2.
Proof.
  intros Hn Hn1 Hn1r Hn2 HS. subst n.
  pose proof HS as [Hal Hn0 Hn16 Hpg Hlo Hc Hleaf Hb].
  rewrite !uint_unsigned in Hal, Hpg, Hlo, Hc, Hb.
  (* the word's range, as a LITERAL bound.  [bv_unsigned_in_range] states it
     at [bv_modulus n] with [n] the width [mword 64] elaborates to, whose
     spelling depends on the ambient imports, so the modulus is discharged
     by computation rather than by rewriting a guessed form. *)
  assert (Hrng : 0 <= bv_unsigned sp0 < 18446744073709551616).
  { pose proof (bv_unsigned_in_range _ sp0) as [Hr0 Hr1].
    split; [ exact Hr0 | ].
    eapply Z.lt_le_trans; [ exact Hr1 | ].
    apply Z.leb_le. vm_compute. reflexivity. }
  rewrite Z.rem_mod_nonneg in Hpg; [ | lia | lia ].
  rewrite Z.rem_mod_nonneg in Hn16; [ | lia | lia ].
  rewrite Z.rem_mod_nonneg in Hn1r; [ | lia | lia ].
  rewrite Z.rem_mod_nonneg in Hal; [ | lia | lia ].
  assert (Hn2r : n2 mod 16 = 0).
  { assert (E : n2 = (n1 + n2) - n1) by lia.
    rewrite E, Zminus_mod, Hn16, Hn1r. reflexivity. }
  assert (Hlow : bv_unsigned (add_vec_int sp0 (- n1)) = bv_unsigned sp0 - n1)
    by (apply uv_avi_neg; lia).
  (* the budget's page arithmetic: both halves stay inside it *)
  assert (Hpgs : (bv_unsigned sp0 - (n1 + n2)) mod 4096 + (n1 + n2) <= 4096) by exact Hpg.
  (* NB an INEQUALITY, not an equation: at [n1 = 0] the budget may end
     exactly on the page boundary ([X mod 4096 + n2 = 4096]), and then the
     left side wraps to 0.  The [<=] is all the page clause below needs. *)
  assert (Hm1 : (bv_unsigned sp0 - n1) mod 4096
                <= (bv_unsigned sp0 - (n1 + n2)) mod 4096 + n2).
  { replace (bv_unsigned sp0 - n1) with ((bv_unsigned sp0 - (n1 + n2)) + n2) by lia.
    rewrite <- Zplus_mod_idemp_l.
    pose proof (Z.mod_pos_bound (bv_unsigned sp0 - (n1 + n2)) 4096 ltac:(lia)) as Hmb.
    destruct (Z_lt_le_dec ((bv_unsigned sp0 - (n1 + n2)) mod 4096 + n2) 4096)
      as [Hlt | Hge].
    - rewrite Z.mod_small; lia.
    - pose proof (Z.mod_pos_bound
                    ((bv_unsigned sp0 - (n1 + n2)) mod 4096 + n2) 4096 ltac:(lia)).
      lia. }
  split.
  - constructor; try (rewrite !uint_unsigned; assumption); try lia.
    + rewrite uint_unsigned. rewrite Z.rem_mod_nonneg; [ | lia | lia ]. exact Hal.
    + rewrite Z.rem_mod_nonneg; [ | lia | lia ]. exact Hn1r.
    + rewrite uint_unsigned. rewrite Z.rem_mod_nonneg; [ | lia | lia ]. lia.
    + rewrite uint_unsigned. lia.
    + intros Hp. destruct (Hleaf ltac:(lia)) as (q & Hq & Hw). exists q. split; [ | exact Hw ].
      unfold uperm_at in Hq |- *.
      assert (Hv : svpn_of (add_vec_int sp0 (- n1)) = svpn_of (add_vec_int sp0 (- (n1 + n2)))).
      { assert (Hlow2 : bv_unsigned (add_vec_int sp0 (- (n1 + n2))) = bv_unsigned sp0 - (n1 + n2))
          by (apply uv_avi_neg; lia).
        assert (E : add_vec_int sp0 (- n1) = add_vec_int (add_vec_int sp0 (- (n1 + n2))) n2).
        { apply bv_eq. rewrite Hlow.
          rewrite (uint_add_vec_int_small (add_vec_int sp0 (- (n1 + n2))) n2 ltac:(lia)
                     ltac:(rewrite Hlow2; lia)).
          rewrite Hlow2. lia. }
        rewrite E. apply (usvpn_window (add_vec_int sp0 (- (n1 + n2))) n2 ltac:(lia)).
        rewrite Hlow2.
        pose proof (Z.mod_pos_bound (bv_unsigned sp0 - (n1 + n2)) 4096 ltac:(lia)). lia. }
      rewrite Hv. exact Hq.
    + intros j Hj. rewrite uint_unsigned.
      replace (bv_unsigned sp0 - n1 + j) with (bv_unsigned sp0 - (n1 + n2) + (n2 + j)) by lia.
      apply Hb. lia.
  - constructor; try lia.
    + rewrite uint_unsigned, Hlow. rewrite Z.rem_mod_nonneg; [ | lia | lia ].
      rewrite Zminus_mod, Hal, Hn1r. reflexivity.
    + rewrite Z.rem_mod_nonneg; [ | lia | lia ]. exact Hn2r.
    + rewrite uint_unsigned, Hlow. rewrite Z.rem_mod_nonneg; [ | lia | lia ].
      replace (bv_unsigned sp0 - n1 - n2) with (bv_unsigned sp0 - (n1 + n2)) by lia. lia.
    + rewrite uint_unsigned, Hlow. lia.
    + rewrite uint_unsigned, Hlow. lia.
    + intros Hp. destruct (Hleaf ltac:(lia)) as (q & Hq & Hw). exists q. split; [ | exact Hw ].
      unfold uperm_at in Hq |- *.
      assert (E : add_vec_int (add_vec_int sp0 (- n1)) (- n2) = add_vec_int sp0 (- (n1 + n2))).
      { apply bv_eq.
        assert (Hlow2 : bv_unsigned (add_vec_int sp0 (- (n1 + n2))) = bv_unsigned sp0 - (n1 + n2))
          by (apply uv_avi_neg; lia).
        rewrite Hlow2.
        rewrite (uv_avi_neg (add_vec_int sp0 (- n1)) n2 ltac:(lia) ltac:(rewrite Hlow; lia)).
        rewrite Hlow. lia. }
      rewrite E. exact Hq.
    + intros j Hj. rewrite uint_unsigned, Hlow.
      replace (bv_unsigned sp0 - n1 - n2 + j) with (bv_unsigned sp0 - (n1 + n2) + j) by lia.
      apply Hb. lia.
Qed.

(* ONE 8-byte slot: every side condition the store leaf needs, on the key
   -- [UmodeAbi.uv_stack_slot] with the leaf clause read on [π] *)
Lemma uk_stack_slot (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
    (sp0 : mword 64) (n d : Z) :
  uk_stack π M sp0 n -> 0 <= d -> d + 8 <= n -> Z.rem d 8 = 0 ->
  let tgt := add_vec_int (add_vec_int sp0 (- n)) d in
  uint tgt = uint sp0 - n + d /\
  uk_wpage π tgt /\
  uva_canon tgt /\
  Z.rem (uint tgt) 4096 <= 4088 /\
  is_aligned_vaddr (Virtaddr tgt) 8 = true /\
  (forall j : nat, (j < 8)%nat ->
     exists b : bv 8, M !! (uint tgt + Z.of_nat j) = Some b).
Proof.
  intros HS Hd0 Hdn Hd8 tgt.
  pose proof HS as [Hal Hn0 Hn16 Hpg Hlo Hc Hleaf Hb].
  rewrite !uint_unsigned in Hal, Hpg, Hlo, Hc, Hb.
  (* the word's range, as a LITERAL bound.  [bv_unsigned_in_range] states it
     at [bv_modulus n] with [n] the width [mword 64] elaborates to, whose
     spelling depends on the ambient imports, so the modulus is discharged
     by computation rather than by rewriting a guessed form. *)
  assert (Hrng : 0 <= bv_unsigned sp0 < 18446744073709551616).
  { pose proof (bv_unsigned_in_range _ sp0) as [Hr0 Hr1].
    split; [ exact Hr0 | ].
    eapply Z.lt_le_trans; [ exact Hr1 | ].
    apply Z.leb_le. vm_compute. reflexivity. }
  rewrite Z.rem_mod_nonneg in Hd8; [ | lia | lia ].
  rewrite Z.rem_mod_nonneg in Hpg; [ | lia | lia ].
  rewrite Z.rem_mod_nonneg in Hal; [ | lia | lia ].
  rewrite Z.rem_mod_nonneg in Hn16; [ | lia | lia ].
  assert (Hlow : bv_unsigned (add_vec_int sp0 (- n)) = bv_unsigned sp0 - n)
    by (apply uv_avi_neg; lia).
  assert (Htu : bv_unsigned tgt = bv_unsigned sp0 - n + d).
  { unfold tgt.
    rewrite (uint_add_vec_int_small (add_vec_int sp0 (- n)) d ltac:(lia)
               ltac:(rewrite Hlow; lia)).
    rewrite Hlow. reflexivity. }
  assert (Hpgd : (bv_unsigned sp0 - n) mod 4096 + d < 4096).
  { pose proof (Z.mod_pos_bound (bv_unsigned sp0 - n) 4096 ltac:(lia)). lia. }
  split_and!.
  - rewrite !uint_unsigned. exact Htu.
  - destruct (Hleaf ltac:(lia)) as (q & Hq & Hw). exists q. split; [ | exact Hw ].
    unfold uperm_at in Hq |- *.
    assert (Hv : svpn_of tgt = svpn_of (add_vec_int sp0 (- n))).
    { unfold tgt. apply (usvpn_window (add_vec_int sp0 (- n)) d ltac:(lia)).
      rewrite Hlow. exact Hpgd. }
    rewrite Hv. exact Hq.
  - apply uva_canon_small. rewrite Htu. lia.
  - rewrite uint_unsigned, Htu.
    rewrite Z.rem_mod_nonneg; [ | lia | lia ].
    assert (He : (bv_unsigned sp0 - n + d) mod 4096
                 = (bv_unsigned sp0 - n) mod 4096 + d).
    { rewrite <- Zplus_mod_idemp_l. apply Z.mod_small.
      pose proof (Z.mod_pos_bound (bv_unsigned sp0 - n) 4096 ltac:(lia)). lia. }
    rewrite He. lia.
  - unfold is_aligned_vaddr. apply Z.eqb_eq.
    cbn [bits_of_virtaddr]. rewrite uint_unsigned, Htu.
    rewrite Z.rem_mod_nonneg; [ | lia | lia ].
    assert (Hsp8 : bv_unsigned sp0 mod 8 = 0).
    { assert (Hdv : (8 | 16)) by (exists 2; reflexivity).
      rewrite (Znumtheory.Zmod_div_mod 8 16 (bv_unsigned sp0) ltac:(lia) ltac:(lia) Hdv).
      rewrite Hal. reflexivity. }
    assert (Hn8 : n mod 8 = 0).
    { assert (Hdv : (8 | 16)) by (exists 2; reflexivity).
      rewrite (Znumtheory.Zmod_div_mod 8 16 n ltac:(lia) ltac:(lia) Hdv).
      rewrite Hn16. reflexivity. }
    rewrite Zplus_mod, Zminus_mod, Hsp8, Hn8, Hd8. reflexivity.
  - intros j Hj. rewrite uint_unsigned, Htu.
    replace (bv_unsigned sp0 - n + d + Z.of_nat j)
      with (bv_unsigned sp0 - n + (d + Z.of_nat j)) by lia.
    apply Hb. lia.
Qed.
