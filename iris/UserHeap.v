(* ===================================================================== *)
(* UserHeap.v -- A SEPARATION-LOGIC HEAP OVER USER MEMORY, IN TWO HALVES. *)
(*                                                                        *)
(* The U tier's memory has been an image VALUE ([uvis_M W : gmap Z (bv 8)])*)
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
(* THE PERMISSION MAP IS CONSUMED HERE AND NOWHERE ELSE.  [uvis_perm]      *)
(* appears in this file, to decide the split at allocation and to state    *)
(* the two invariants; above it, a leaf takes [utext]/[ubyte] and never    *)
(* mentions a permission, a page, or a table.                             *)
(*                                                                        *)
(* WHAT THIS IS NOT YET.  [urun] still names [uvis_M W], so the image is   *)
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
From iris.base_logic.lib Require Import ghost_map.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvPtsto RiscvExtras.
Require Import UserPtTree.
Require Import UmodeMem UmodeArith UmodeAbi.  (* [uva_canon] / [uint_moi] / [uva_canon_small] *)
Require Import UserPerm.
Require Import UexecSlot.   (* [uvis] / [uvis_M] / [uvis_perm] *)
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
Definition utext_part (W : uvis) : gmap Z (bv 8) :=
  base.filter (fun kv : Z * bv 8 =>
                 ux_addr (uvis_perm W) kv.1 /\ ~ uw_addr (uvis_perm W) kv.1)
              (uvis_M W).

Definition udata_part (W : uvis) : gmap Z (bv 8) :=
  base.filter (fun kv : Z * bv 8 => uw_addr (uvis_perm W) kv.1) (uvis_M W).

Lemma utext_part_sub (W : uvis) : utext_part W ⊆ uvis_M W.
Proof. apply map_filter_subseteq. Qed.

Lemma udata_part_sub (W : uvis) : udata_part W ⊆ uvis_M W.
Proof. apply map_filter_subseteq. Qed.

Lemma utext_udata_disjoint (W : uvis) : utext_part W ##ₘ udata_part W.
Proof.
  apply map_disjoint_spec. intros a b1 b2 H1 H2.
  apply map_lookup_filter_Some in H1 as [_ [_ Hn]].
  apply map_lookup_filter_Some in H2 as [_ Hy].
  exact (Hn Hy).
Qed.

Lemma utext_part_x (W : uvis) (a : Z) :
  is_Some (utext_part W !! a) -> ux_addr (uvis_perm W) a.
Proof.
  intros [b Hb]. apply map_lookup_filter_Some in Hb as [_ [Hx _]]. exact Hx.
Qed.

Lemma udata_part_w (W : uvis) (a : Z) :
  is_Some (udata_part W !! a) -> uw_addr (uvis_perm W) a.
Proof. intros [b Hb]. apply map_lookup_filter_Some in Hb as [_ Hw]. exact Hw. Qed.

Section UserHeap.
  Context `{!riscvGS Σ}.

  (* ===================================================================== *)
  (* §2 THE TWO POINTS-TO FAMILIES.                                        *)
  (* ===================================================================== *)

  (* A TEXT byte.  PERSISTENT -- every text fragment is persisted when the
     heap is allocated -- so it is immutable and freely duplicable, which is
     exactly what an instruction fetch wants: the same bytes are read at
     every step, by every continuation, forever. *)
  Definition utext (γt : gname) (a : Z) (b : bv 8) : iProp Σ := (a ↪[γt]□ b)%I.

  (* A DATA byte, exclusively owned: the right to write it. *)
  Definition ubyte (γd : gname) (a : Z) (b : bv 8) : iProp Σ := (a ↪[γd] b)%I.

  Global Instance utext_persistent γt a b : Persistent (utext γt a b).
  Proof. apply _. Qed.

  Global Instance ubyte_timeless γd a b : Timeless (ubyte γd a b).
  Proof. apply _. Qed.

  (* ===================================================================== *)
  (* §3 THE RUNNING PREDICATE.                                             *)
  (*                                                                       *)
  (* Two authorities against one image, with the segment facts that make    *)
  (* each half's points-to mean what it means.                             *)
  (* ===================================================================== *)
  Definition urun (γt γd : gname) (W : uvis) : iProp Σ :=
    (∃ Mt Md : gmap Z (bv 8),
       ⌜ Mt ⊆ uvis_M W ⌝ ∗ ⌜ Md ⊆ uvis_M W ⌝ ∗ ⌜ Mt ##ₘ Md ⌝ ∗
       (* CANONICITY, ONCE FOR THE WHOLE ADDRESS SPACE.  Every mapped user
          address is below MAXVA, hence Sv39-canonical.  Stating it here
          rather than per access is what stops [uinstr]'s [ui_canon] and the
          [uva_canon] output of every data reader ([uk_rd_byte],
          [uk_args_slot], [uk_stack_slot]) from each re-deriving it. *)
       ⌜ forall a : Z, is_Some (uvis_M W !! a) -> 0 <= a < 2 ^ 38 ⌝ ∗
       ⌜ forall a : Z, is_Some (Mt !! a) -> ux_addr (uvis_perm W) a ⌝ ∗
       ⌜ forall a : Z, is_Some (Md !! a) -> uw_addr (uvis_perm W) a ⌝ ∗
       ghost_map_auth γt 1 Mt ∗ ghost_map_auth γd 1 Md)%I.

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
  Lemma urun_text (γt γd : gname) (W : uvis) (a : Z) (b : bv 8) :
    urun γt γd W -∗ utext γt a b -∗
    ⌜ uvis_M W !! a = Some b /\ ux_addr (uvis_perm W) a /\ 0 <= a < 2 ^ 38 ⌝.
  Proof.
    iIntros "Hrun Hb".
    iDestruct "Hrun" as (Mt Md) "(%Hst & %Hsd & %Hdisj & %Hcan & %Hx & %Hw & Ht & Hd)".
    iDestruct (ghost_map_lookup with "Ht Hb") as %HMt.
    assert (HM : uvis_M W !! a = Some b)
      by exact (proj1 (map_subseteq_spec Mt (uvis_M W)) Hst a b HMt).
    (* NOTE: not [split_and!] -- it would split [0 <= a < 2 ^ 38] too *)
    iPureIntro. split; [ exact HM | ].
    split; [ exact (Hx a (mk_is_Some _ _ HMt)) | exact (Hcan a (mk_is_Some _ _ HM)) ].
  Qed.

  (* ...and a DATA byte names its byte and its page is WRITABLE. *)
  Lemma urun_ubyte (γt γd : gname) (W : uvis) (a : Z) (b : bv 8) :
    urun γt γd W -∗ ubyte γd a b -∗
    ⌜ uvis_M W !! a = Some b /\ uw_addr (uvis_perm W) a /\ 0 <= a < 2 ^ 38 ⌝.
  Proof.
    iIntros "Hrun Hb".
    iDestruct "Hrun" as (Mt Md) "(%Hst & %Hsd & %Hdisj & %Hcan & %Hx & %Hw & Ht & Hd)".
    iDestruct (ghost_map_lookup with "Hd Hb") as %HMd.
    assert (HM : uvis_M W !! a = Some b)
      by exact (proj1 (map_subseteq_spec Md (uvis_M W)) Hsd a b HMd).
    iPureIntro. split; [ exact HM | ].
    split; [ exact (Hw a (mk_is_Some _ _ HMd)) | exact (Hcan a (mk_is_Some _ _ HM)) ].
  Qed.

  Definition uvis_wM (W : uvis) (M' : gmap Z (bv 8)) : uvis :=
    MkUvis (uvis_tf W) M' (uvis_perm W).

  (* THE STORE.  An exclusively-owned data byte may be replaced and the
     key's image moves with it.  The text half is untouched, and it stays a
     SUBMAP because the two halves are disjoint -- which is the whole reason
     they are two heaps. *)
  Lemma urun_store (γt γd : gname) (W : uvis) (a : Z) (b b' : bv 8) :
    urun γt γd W -∗ ubyte γd a b ==∗
      urun γt γd (uvis_wM W (<[a := b']> (uvis_M W))) ∗ ubyte γd a b'.
  Proof.
    iIntros "Hrun Hb".
    iDestruct "Hrun" as (Mt Md) "(%Hst & %Hsd & %Hdisj & %Hcan & %Hx & %Hw & Ht & Hd)".
    iDestruct (ghost_map_lookup with "Hd Hb") as %HMd.
    assert (Hnt : Mt !! a = None)
      by exact (map_disjoint_Some_r Mt Md a b Hdisj HMd).
    iMod (ghost_map_update b' with "Hd Hb") as "[Hd Hb]".
    iModIntro. iFrame "Hb". iExists Mt, (<[a := b']> Md).
    cbn [uvis_M uvis_perm uvis_wM].
    iFrame "Ht Hd". iPureIntro. split_and!.
    - apply insert_subseteq_r; [ exact Hnt | exact Hst ].
    - apply insert_mono. exact Hsd.
    - apply map_disjoint_insert_r_2; [ exact Hnt | exact Hdisj ].
    - (* a store replaces a key that is already there, so the domain -- and
         with it the canonicity fact -- does not move *)
      intros k Hk. apply Hcan.
      destruct (decide (k = a)) as [-> | Hne].
      + exact (mk_is_Some _ _ (proj1 (map_subseteq_spec Md (uvis_M W)) Hsd a b HMd)).
      + rewrite lookup_insert_ne in Hk; [ exact Hk | exact (not_eq_sym Hne) ].
    - exact Hx.
    - intros k Hk. apply Hw.
      destruct (decide (k = a)) as [-> | Hne].
      + exact (mk_is_Some _ _ HMd).
      + rewrite lookup_insert_ne in Hk; [ exact Hk | exact (not_eq_sym Hne) ].
  Qed.

  (* ===================================================================== *)
  (* §4 ALLOCATION -- the process's FIRST WP.                              *)
  (*                                                                       *)
  (* Two [ghost_map_alloc]s at the segment split, and the text half is      *)
  (* PERSISTED on the spot: after this step nothing can ever write it, and  *)
  (* every continuation may read it without owning anything.                *)
  (* ===================================================================== *)
  Lemma urun_alloc (W : uvis) :
    (* THE ONE PREMISE, and where it comes from: every mapped user address is
       below MAXVA.  At the call site (the process's first WP) [uvb] carries
       [usz_ok sz] and the lazy image over the sz-region, which is what bounds
       the image's keys; it is taken here rather than re-derived so that this
       file stays independent of the bundle. *)
    (forall a : Z, is_Some (uvis_M W !! a) -> 0 <= a < 2 ^ 38) ->
    ⊢ |==> ∃ γt γd : gname,
        urun γt γd W ∗
        ([∗ map] a ↦ b ∈ utext_part W, utext γt a b) ∗
        ([∗ map] a ↦ b ∈ udata_part W, ubyte γd a b).
  Proof.
    intros Hcan.
    iMod (ghost_map_alloc (utext_part W)) as (γt) "[Htauth Htfrag]".
    iMod (ghost_map_alloc (udata_part W)) as (γd) "[Hdauth Hdfrag]".
    iAssert (|==> [∗ map] a ↦ b ∈ utext_part W, utext γt a b)%I
      with "[Htfrag]" as ">#Htp".
    { iApply big_sepM_bupd. iApply (big_sepM_impl with "Htfrag").
      iIntros "!>" (a b _) "H". rewrite /utext.
      iApply (ghost_map_elem_persist with "H"). }
    iModIntro. iExists γt, γd.
    iSplitL "Htauth Hdauth"; [ | iFrame "Hdfrag"; iFrame "Htp" ].
    iExists (utext_part W), (udata_part W).
    iFrame "Htauth Hdauth". iPureIntro. split_and!.
    - apply utext_part_sub.
    - apply udata_part_sub.
    - apply utext_udata_disjoint.
    - exact Hcan.
    - exact (utext_part_x W).
    - exact (udata_part_w W).
  Qed.

  (* ===================================================================== *)
  (* §4b WORDS AND STRINGS, over [ubyte].                                  *)
  (*                                                                       *)
  (* Everything a program says about its data is a run of bytes, so nothing *)
  (* here is primitive: a word is eight consecutive [ubyte]s and a string   *)
  (* is its bytes followed by the NUL.  Stating them this way rather than   *)
  (* as new resources is what makes them SPLIT and RECOMBINE for free --    *)
  (* which is what a syscall footprint needs, since the range the kernel is *)
  (* handed rarely coincides with a program-level object.                   *)
  (* ===================================================================== *)

  (* [n] consecutive bytes, the shape everything else is built from *)
  Definition urun_bytes (γd : gname) (a : Z) (n : nat) (f : nat -> bv 8) : iProp Σ :=
    ([∗ list] j ∈ seq 0 n, ubyte γd (a + Z.of_nat j) (f j))%I.

  (* an 8-byte little-endian word, as the load and store leaves read it *)
  Definition uword (γd : gname) (a : Z) (w : mword 64) : iProp Σ :=
    urun_bytes γd a 8 (nth_byte w).

  (* a NUL-terminated C string of length [len]: the body, then the NUL.
     The body's bytes are NOT pinned to values here -- a program that cares
     which bytes they are owns them individually. *)
  Definition ustr (γd : gname) (a : Z) (len : nat) (f : nat -> bv 8) : iProp Σ :=
    (urun_bytes γd a len f ∗ ubyte γd (a + Z.of_nat len) ubyte0)%I.

  (* NOTE: the SPLIT of a run at an arbitrary point -- which is what a
     syscall footprint hand-over is -- is deliberately not here yet.  It is
     a step-3 tool and wants proving against its consumer, not before it. *)

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
  (*   ui_canon   GONE -- [urun]'s "every mapped address is below MAXVA"    *)
  (*                covers it, and covers data addresses at the same time   *)
  (*   ui_leaf    GONE -- [urun_text] yields [ux_addr] PER FRAGMENT, so     *)
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
  (* [uint (add_vec_int pc 2) = uint pc + 2] it needs -- [urun] bounds      *)
  (* those addresses, so the two agree.                                     *)
  (* ===================================================================== *)
  Definition uinstr_is (γt : gname) (pc : mword 64) (is_rvc : bool)
      (i : instruction) : iProp Σ :=
    (⌜ is_aligned_vaddr (Virtaddr pc) 2 = true ⌝ ∗
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

  Global Instance uinstr_is_persistent γt pc is_rvc i :
    Persistent (uinstr_is γt pc is_rvc i).
  Proof. rewrite /uinstr_is. destruct is_rvc; [ destruct (is_aligned_vaddr _ _) | ];
           apply _. Qed.

End UserHeap.
