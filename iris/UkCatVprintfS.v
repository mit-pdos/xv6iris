(* ===================================================================== *)
(* UkCatVprintfS.v -- vprintf's '%s' ARM.                                 *)
(*                                                                        *)
(* cat's other three diagnostics are literals with no directive in them,  *)
(* and [UkCatVprintf] walks those.  The one it cannot walk is             *)
(*                                                                        *)
(*     fprintf(2, "cat: cannot open %s\n", argv[i]);                      *)
(*                                                                        *)
(* which main issues when open() fails.  Reaching its [putc] takes three  *)
(* things this file supplies: a walk of the plain prefix that STOPS at    *)
(* the '%' instead of running to the terminator; the thirty-instruction   *)
(* dispatch chain that decides, one character class at a time, that this  *)
(* directive is an 's'; and the inner loop over the argument string.      *)
(*                                                                        *)
(* The dispatch is specialised to c0 = 's'.  That is not a shortcut       *)
(* around the branches -- every one of them is stepped -- but a choice of *)
(* what to state: with c0 fixed, each test's outcome is decided by one    *)
(* [vm_compute] on a concrete pair, where a proof general in c0 would     *)
(* have to carry the whole state machine's case analysis for arms cat     *)
(* never enters.                                                          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem.
Require Import UCodeCat.
Require Import TsoCtx.
Require User.CatSyms User.CatInstrs.
Local Open Scope Z_scope.
Import Defs.
Require Import UkProgAbi.
Require Import UkCatPutc.
Require Import UkCatVprintf.
Require Import UkRunBr.

Section UkCatVprintfS.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context (γt γd γs : gname).

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation s7_idx := (mword_of_int 23 : mword 5).
  Local Notation s8_idx := (mword_of_int 24 : mword 5).

  (* --------------------------------------------------------------------- *)
  (* A RUN OF PLAIN CHARACTERS, 0x566 -> 0x566.                             *)
  (*                                                                        *)
  (* [wp_kcat_vprintf_loop] walks a format string with no '%' from an index *)
  (* all the way to its terminator, and ends in the epilogue.  A format     *)
  (* that HAS a '%' needs the same walk stopped short -- at the '%', with   *)
  (* the frame still spilled and the loop still to run.  This is that walk. *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kcat_vprintf_seg (m0 : regfile) (sp0 fd ap : mword 64) (a : Z)
      (len : nat) (f : nat -> mword 8) (k : nat) :
    0 <= a -> a + Z.of_nat len + 2 < 2 ^ 31 ->
    forall (i0 : nat) (h : CpuId) (m : regfile) (n : nat),
      (i0 + k < len)%nat ->
      (forall j : nat, (i0 <= j < i0 + k)%nat -> bv_unsigned (f j) <> 37) ->
      vp_inv m0 m sp0 a fd ap i0 ->
      m !!! Regidx s1_idx = mword_of_int (bv_unsigned (f i0)) ->
      cat_code γt -∗
      utext_str γt a len f -∗
      urun γt γd γs h m (mword_of_int 0x566) (4 + n) -∗
      (∀ (h' : CpuId) (m' : regfile),
         ⌜ vp_inv m0 m' sp0 a fd ap (i0 + k)%nat ⌝ -∗
         ⌜ m' !!! Regidx s1_idx
           = mword_of_int (bv_unsigned (f (i0 + k)%nat)) ⌝ -∗
         urun γt γd γs h' m' (mword_of_int 0x566) (4 + n) -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd.
    induction k as [| k IH ];
      intros i0 h m n Hlt Hpct Hinv Hs1;
      iIntros "#Hcode #Hstr Hrun Hcont";
      iDestruct (utext_str_nonul with "Hstr") as %Hnn.
    - (* nothing to walk *)
      rewrite Nat.add_0_r.
      iApply ("Hcont" $! h m with "[] [] Hrun"); iPureIntro;
        [ exact Hinv | exact Hs1 ].
    - (* one plain round, then the rest *)
      assert (Hslt : (S i0 < len)%nat) by lia.
      iDestruct (utext_str_byte γt a len f (S i0) Hslt with "Hstr") as "#Hb1".
      iApply (wp_kcat_vprintf_step γt γd γs m0 sp0 fd ap a i0 (f i0)
                (f (S i0)) h m n Ha0 ltac:(lia) (Hpct i0 ltac:(lia)) Hinv Hs1
                with "Hcode Hb1 Hrun").
      iIntros (h1 m1) "%Hinv1 %Hs11 Hrun".
      (* ---- 0x562  beqz s1,0x736 -- NOT taken: a body byte is not NUL ---- *)
      assert (Hnz : bv_unsigned (f (S i0)) <> 0).
      { intro He. apply (Hnn (S i0) Hslt). apply bv_eq.
        rewrite He. vm_compute. reflexivity. }
      assert (Hb1r : 0 <= bv_unsigned (f (S i0)) < Z64).
      { assert (HH : 0 <= bv_unsigned (f (S i0)) < 256).
        { pose proof (bv_unsigned_in_range 8 (f (S i0))) as H0.
          assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
          rewrite Em8 in H0. exact H0. }
        unfold Z64. lia. }
      assert (Hnt : false = uv_btaken BEQ (m1 !!! Regidx s1_idx) zero_reg).
      { rewrite Hs11. cbn [uv_btaken].
        rewrite (moi_eq_zero (bv_unsigned (f (S i0))) Hb1r).
        destruct (Z.eqb_spec (bv_unsigned (f (S i0))) 0) as [He | _];
          [ exfalso; exact (Hnz He) | reflexivity ]. }
      iApply (wp_uk_btype0 γt γd γs h1 m1 (mword_of_int 0x562)
                (mword_of_int 468 : mword 13) s1_idx BEQ false
                (add_vec (mword_of_int 0x562 : mword 64)
                   (sign_extend' 64 (mword_of_int 468 : mword 13)))
                (4 + n) Hnt eq_refl ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_cat_562 with "Hcode"). }
      assert (E562 : add_vec_int (mword_of_int 0x562 : mword 64) 4
                     = mword_of_int 0x566)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E562.
      iIntros (h2) "Hrun".
      assert (Ek : (i0 + S k)%nat = (S i0 + k)%nat) by lia.
      rewrite Ek.
      iApply (IH (S i0) h2 m1 n ltac:(lia)
                ltac:(intros j Hj; apply Hpct; lia) Hinv1 Hs11
                with "Hcode Hstr Hrun Hcont").
  Qed.

  (* ===================================================================== *)
  (* SMALL ARITHMETIC THE DISPATCH NEEDS.                                   *)
  (* ===================================================================== *)

  Lemma ubyte_range (b : mword 8) : 0 <= bv_unsigned b < 256.
  Proof.
    pose proof (bv_unsigned_in_range 8 b) as H0.
    assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
    rewrite Em8 in H0. exact H0.
  Qed.

  (* Every test in the dispatch chain is [c - K] against zero, with [c] a
     byte and [K] one of 100, 108, 117, 120.  The difference is NEGATIVE
     whenever the byte is small, so [moi_eq_zero] -- which wants a
     nonnegative argument -- does not apply to it directly; the wrap has to
     be taken first, and then the divisibility says exactly [c = K]. *)
  Lemma moi_sub_ne_zero (v w : Z) :
    0 <= v < 256 -> 0 <= w < 256 -> v <> w ->
    neq_vec (mword_of_int (v - w) : mword 64) zero_reg = true.
  Proof.
    intros Hv Hw Hne.
    rewrite <- (moi_mod ((v - w) mod Z64) (v - w)
                 ltac:(rewrite Zmod_mod; reflexivity)).
    unfold neq_vec.
    rewrite (moi_eq_zero ((v - w) mod Z64)
               ltac:(apply Z.mod_pos_bound; unfold Z64; lia)).
    destruct (Z.eqb_spec ((v - w) mod Z64) 0) as [He | _]; [ | reflexivity ].
    exfalso. apply Hne.
    apply Z.mod_divide in He; [ | unfold Z64; lia ].
    destruct He as [q Hq]. unfold Z64 in Hq. lia.
  Qed.

  (* ===================================================================== *)
  (* WHERE THE HEAP'S OWN BOUNDS COME FROM.                                 *)
  (* ===================================================================== *)

  Local Lemma urun_ubyte_bnd (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (dq : dfrac) (a : Z) (b : bv 8) :
    urun γt γd γs h m pc avail -∗ ubyteq γd dq a b -∗ ⌜ 0 <= a < 2 ^ 38 ⌝.
  Proof.
    iIntros "Hrun Hb".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(_ & _ & Hh & _ & _)".
    iDestruct (uheap_ubyte with "Hh Hb") as %(_ & _ & Hbnd).
    iPureIntro. exact Hbnd.
  Qed.

  Local Lemma urun_ustr_bnd (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (dq : dfrac) (a : Z) (len : nat) (f : nat -> bv 8) :
    urun γt γd γs h m pc avail -∗ ustr γd dq a len f -∗
    ⌜ 0 <= a /\ a + Z.of_nat len < 2 ^ 38 ⌝.
  Proof.
    iIntros "Hrun Hs".
    iDestruct (ustr_nul with "Hs") as "[Hnul Hcl]".
    iDestruct (urun_ubyte_bnd with "Hrun Hnul") as %Hhi.
    iDestruct ("Hcl" with "Hnul") as "Hs".
    destruct len as [| len' ].
    - iPureIntro. lia.
    - iDestruct (ustr_byte γd dq a (S len') f 0%nat ltac:(lia) with "Hs")
        as "[Hb0 _]".
      iDestruct (urun_ubyte_bnd with "Hrun Hb0") as %Hlo.
      iPureIntro. lia.
  Qed.

  Local Lemma urun_uword_bnd (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (dq : dfrac) (a : Z) (w : mword 64) :
    urun γt γd γs h m pc avail -∗ uwordq γd dq a w -∗
    ⌜ 0 <= a /\ a + 8 <= 2 ^ 38 ⌝.
  Proof.
    iIntros "Hrun Hw". rewrite /uwordq /ubytesq.
    iDestruct (big_sepL_lookup_acc _ (seq 0 8) 0%nat 0%nat ltac:(reflexivity)
                 with "Hw") as "[H0 Hcl]".
    iDestruct (urun_ubyte_bnd with "Hrun H0") as %Hb0.
    iDestruct ("Hcl" with "H0") as "Hw".
    iDestruct (big_sepL_lookup_acc _ (seq 0 8) 7%nat 7%nat ltac:(reflexivity)
                 with "Hw") as "[H7 _]".
    iDestruct (urun_ubyte_bnd with "Hrun H7") as %Hb7.
    iPureIntro. lia.
  Qed.

  (* ===================================================================== *)
  (* [vp_inv] WITH s3 FREE.                                                 *)
  (*                                                                        *)
  (* From 0x6f2 to 0x712 the '%s' arm parks the BUMPED va_list in s3 -- the  *)
  (* same register the loop uses for its state -- and only the [li s3,0] at  *)
  (* 0x712 puts the state back.  For those thirty instructions the loop      *)
  (* invariant holds of every register but that one, so it is stated with    *)
  (* s3's value a parameter.  [vp_inv] is the instance at [zero_reg], and    *)
  (* the two conversions are definitional.                                   *)
  (* ===================================================================== *)
  Definition vp_inv3 (m0 m : regfile) (sp0 : mword 64) (a : Z)
      (fd ap v3 : mword 64) (i : nat) : Prop :=
    m !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 12)) /\
    m !!! Regidx s0_idx = sp0 /\
    m !!! Regidx s2_idx = mword_of_int (Z.of_nat i) /\
    m !!! Regidx s3_idx = v3 /\
    m !!! Regidx s4_idx = mword_of_int a /\
    m !!! Regidx s5_idx = mword_of_int 37 /\
    m !!! Regidx s6_idx = fd /\
    m !!! Regidx s7_idx = ap /\
    m !!! Regidx s8_idx = mword_of_int 100 /\
    (forall r : mword 5, ucallee_saved_idx r = true ->
       uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27) ->
       m !!! Regidx r = m0 !!! Regidx r).

  Lemma vp_inv_of3 (m0 m : regfile) (sp0 : mword 64) (a : Z)
      (fd ap : mword 64) (i : nat) :
    vp_inv3 m0 m sp0 a fd ap zero_reg i -> vp_inv m0 m sp0 a fd ap i.
  Proof. unfold vp_inv3, vp_inv. exact (fun H => H). Qed.

  Lemma vp_inv_to3 (m0 m : regfile) (sp0 : mword 64) (a : Z)
      (fd ap : mword 64) (i : nat) :
    vp_inv m0 m sp0 a fd ap i -> vp_inv3 m0 m sp0 a fd ap zero_reg i.
  Proof. unfold vp_inv3, vp_inv. exact (fun H => H). Qed.

  Lemma vp_inv3_call (m0 m m' : regfile) (sp0 : mword 64) (a : Z)
      (fd ap v3 : mword 64) (i : nat) :
    ucallee_saved m m' ->
    vp_inv3 m0 m sp0 a fd ap v3 i -> vp_inv3 m0 m' sp0 a fd ap v3 i.
  Proof.
    intros Hcs (Hsp & Hs0 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hfr).
    unfold vp_inv3.
    rewrite (Hcs csp_rs1 ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s0_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s2_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s3_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s4_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s5_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s6_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s7_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s8_idx ltac:(vm_compute; reflexivity)).
    repeat (split; [ assumption | ]).
    intros r Hr Hset. rewrite (Hcs r Hr). exact (Hfr r Hr Hset).
  Qed.

  Lemma vp_inv3_upd (m0 m : regfile) (sp0 : mword 64) (a : Z)
      (fd ap v3 : mword 64) (i : nat) (r : mword 5) (v : mword 64) :
    vp_writable r = true ->
    vp_inv3 m0 m sp0 a fd ap v3 i ->
    vp_inv3 m0 (<[Regidx r := regval_into_reg v]> m) sp0 a fd ap v3 i.
  Proof.
    intros Hw (Hsp & Hs0 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hfr).
    unfold vp_inv3.
    rewrite (upd_ne m (Regidx r) (Regidx csp_rs1) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint csp_rs1) with 2
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s0_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s0_idx) with 8
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s2_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s2_idx) with 18
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s3_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s3_idx) with 19
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s4_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s4_idx) with 20
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s5_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s5_idx) with 21
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s6_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s6_idx) with 22
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s7_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s7_idx) with 23
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s8_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s8_idx) with 24
                       by (vm_compute; reflexivity); lia)).
    repeat (split; [ assumption | ]).
    intros q Hq Hset.
    rewrite (upd_ne m (Regidx r) (Regidx q) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw); lia)).
    exact (Hfr q Hq Hset).
  Qed.

  (* --------------------------------------------------------------------- *)
  (* ONE TURN OF THE ARGUMENT STRING'S LOOP, 0x702 -> 0x70e:                *)
  (*                                                                        *)
  (*   c.mv a0,s6 ; jal putc ; c.addi s1,s1,1 ; lbu a1,0(s1)                 *)
  (*                                                                        *)
  (* s1 is the cursor and is callee-saved, which is the only reason it       *)
  (* survives the call; a0 and a1 are the arguments and are not.             *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kcat_vprintf_sstep (m0 : regfile) (sp0 fd ap v3 : mword 64) (a : Z)
      (i : nat) (dq : dfrac) (p : Z) (b1 : mword 8)
      (h : CpuId) (m : regfile) (n : nat) :
    0 <= p -> p + 1 < Z64 ->
    vp_inv3 m0 m sp0 a fd ap v3 i ->
    m !!! Regidx s1_idx = mword_of_int p ->
    cat_code γt -∗
    ubyteq γd dq (p + 1) b1 -∗
    urun γt γd γs h m (mword_of_int 0x702) (4 + n) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ubyteq γd dq (p + 1) b1 -∗
       ⌜ vp_inv3 m0 m' sp0 a fd ap v3 i ⌝ -∗
       ⌜ m' !!! Regidx s1_idx = mword_of_int (p + 1) ⌝ -∗
       ⌜ m' !!! Regidx a1_idx = zero_extend' 64 b1 ⌝ -∗
       urun γt γd γs h' m' (mword_of_int 0x70e) (4 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hp0 Hp1 Hinv Hs1.
    iIntros "#Hcode Hb1 Hrun Hcont".
    destruct cat_syms_pins
      as (_ & _ & _ & _ & _ & Hputc & _ & _ & _ & _ & _).
    (* ---- 0x702  c.mv a0,s6 ---- *)
    iApply (wp_uk_cmv γt γd γs h m (mword_of_int 0x702) a0_idx s6_idx
              (add_vec zero_reg (m !!! Regidx s6_idx)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_cat_702 with "Hcode"). }
    assert (E702 : add_vec_int (mword_of_int 0x702 : mword 64) 2
                   = mword_of_int 0x704)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E702.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a0_idx
                 := regval_into_reg (add_vec zero_reg (m !!! Regidx s6_idx))]> m).
    (* ---- 0x704  jal ra,0x454 <putc> ---- *)
    iApply (wp_uk_jal γt γd γs h1 m1 (mword_of_int 0x704)
              (mword_of_int 2096464 : mword 21) ra_idx
              (mword_of_int CatSyms.putc) (mword_of_int 0x708) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hputc; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hputc; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_704 with "Hcode"). }
    iIntros (h2) "Hrun".
    set (m2 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x708 : mword 64)]> m1).
    assert (Hra2 : m2 !!! Regidx ra_idx = (mword_of_int 0x708 : mword 64))
      by exact (upd_eq m1 (Regidx ra_idx) (regval_into_reg _)).
    iApply (wp_kcat_putc γt γd γs h2 m2 n with "Hcode Hrun").
    iIntros (h3 m3) "%Hcs Hrun".
    assert (Eret : ret_pc (m2 !!! Regidx ra_idx)
                   = (mword_of_int 0x708 : mword 64))
      by (rewrite Hra2; apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    assert (Hinv3 : vp_inv3 m0 m3 sp0 a fd ap v3 i).
    { apply (vp_inv3_call m0 m2 m3 sp0 a fd ap v3 i Hcs).
      apply (vp_inv3_upd _ _ _ _ _ _ _ _ ra_idx _
               ltac:(vm_compute; reflexivity)).
      apply (vp_inv3_upd _ _ _ _ _ _ _ _ a0_idx _
               ltac:(vm_compute; reflexivity)).
      exact Hinv. }
    assert (Hs1_3 : m3 !!! Regidx s1_idx = mword_of_int p).
    { rewrite (Hcs s1_idx ltac:(vm_compute; reflexivity)).
      rewrite /m2 (upd_ne m1 (Regidx ra_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m1 (upd_ne m (Regidx a0_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      exact Hs1. }
    (* ---- 0x708  c.addi s1,s1,1 ---- *)
    assert (Ei1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                  = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Eadd : add_vec (m3 !!! Regidx s1_idx)
                     (sign_extend' 64 (mword_of_int 1 : mword 6))
                   = mword_of_int (p + 1))
      by (rewrite Hs1_3 Ei1 moi_add; reflexivity).
    iApply (wp_uk_caddi γt γd γs h3 m3 (mword_of_int 0x708)
              (mword_of_int 1 : mword 6) s1_idx (mword_of_int (p + 1)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Eadd))
              with "[] Hrun").
    { iApply (uis_cat_708 with "Hcode"). }
    assert (E708 : add_vec_int (mword_of_int 0x708 : mword 64) 2
                   = mword_of_int 0x70a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E708.
    iIntros (h4) "Hrun".
    set (m4 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int (p + 1) : mword 64)]> m3).
    assert (Hs1_4 : m4 !!! Regidx s1_idx = mword_of_int (p + 1))
      by exact (upd_eq m3 (Regidx s1_idx) (regval_into_reg _)).
    assert (Hinv4 : vp_inv3 m0 m4 sp0 a fd ap v3 i)
      by exact (vp_inv3_upd m0 m3 sp0 a fd ap v3 i s1_idx _
                  ltac:(vm_compute; reflexivity) Hinv3).
    (* ---- 0x70a  lbu a1,0(s1) ---- *)
    assert (Hp1r : 0 <= p + 1 < Z64) by lia.
    assert (Haddr : (p + 1)%Z
                    = uint (m4 !!! Regidx s1_idx)
                      + uoff_i12 (mword_of_int 0 : mword 12)).
    { rewrite Hs1_4 (uint_moi (p + 1) Hp1r).
      replace (uoff_i12 (mword_of_int 0 : mword 12)) with 0
        by (vm_compute; reflexivity).
      lia. }
    iApply (wp_uk_lbu γt γd γs h4 m4 (mword_of_int 0x70a)
              (mword_of_int 0 : mword 12) s1_idx a1_idx dq (p + 1) b1 (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              Haddr ltac:(vm_compute; discriminate)
              with "[] Hb1 Hrun").
    { iApply (uis_cat_70a with "Hcode"). }
    assert (E70a : add_vec_int (mword_of_int 0x70a : mword 64) 4
                   = mword_of_int 0x70e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E70a.
    iIntros "Hb1" (h5) "Hrun".
    set (m5 := <[Regidx a1_idx
                 := regval_into_reg (zero_extend' 64 b1 : mword 64)]> m4).
    iApply ("Hcont" $! h5 m5 with "Hb1 [] [] [] Hrun").
    - iPureIntro.
      exact (vp_inv3_upd m0 m4 sp0 a fd ap v3 i a1_idx _
               ltac:(vm_compute; reflexivity) Hinv4).
    - iPureIntro. rewrite /m5 (upd_ne m4 (Regidx a1_idx) (Regidx s1_idx) _
                                ltac:(vm_compute; discriminate)).
      exact Hs1_4.
    - iPureIntro.
      exact (upd_eq m4 (Regidx a1_idx) (regval_into_reg _)).
  Qed.

  Lemma vp_inv3_bump (m0 m : regfile) (sp0 : mword 64) (a : Z)
      (fd ap v3 : mword 64) (i j : nat) (v : mword 64) :
    v = mword_of_int (Z.of_nat j) ->
    vp_inv3 m0 m sp0 a fd ap v3 i ->
    vp_inv3 m0 (<[Regidx s2_idx := regval_into_reg v]> m) sp0 a fd ap v3 j.
  Proof.
    intros -> (Hsp & Hs0 & _ & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hfr).
    unfold vp_inv3.
    rewrite (upd_ne m (Regidx s2_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s0_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s3_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s4_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s5_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s6_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s7_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s8_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_eq m (Regidx s2_idx) _).
    repeat (split; [ (assumption || reflexivity) | ]).
    intros q Hq Hset.
    rewrite (upd_ne m (Regidx s2_idx) (Regidx q) _
               ltac:(apply uidx_ne; replace (uint s2_idx) with 18
                       by (vm_compute; reflexivity); lia)).
    exact (Hfr q Hq Hset).
  Qed.

  (* ...and the two writes that MOVE the invariant: the state register and
     the va_list cursor.  Both are what the '%s' arm is for. *)
  Lemma vp_inv3_s3 (m0 m : regfile) (sp0 : mword 64) (a : Z)
      (fd ap v3 w3 : mword 64) (i : nat) :
    vp_inv3 m0 m sp0 a fd ap v3 i ->
    vp_inv3 m0 (<[Regidx s3_idx := regval_into_reg w3]> m) sp0 a fd ap w3 i.
  Proof.
    intros (Hsp & Hs0 & Hs2 & _ & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hfr).
    unfold vp_inv3.
    rewrite (upd_ne m (Regidx s3_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s3_idx) (Regidx s0_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s3_idx) (Regidx s2_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s3_idx) (Regidx s4_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s3_idx) (Regidx s5_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s3_idx) (Regidx s6_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s3_idx) (Regidx s7_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s3_idx) (Regidx s8_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_eq m (Regidx s3_idx) _).
    repeat (split; [ (assumption || reflexivity) | ]).
    intros q Hq Hset.
    rewrite (upd_ne m (Regidx s3_idx) (Regidx q) _
               ltac:(apply uidx_ne; replace (uint s3_idx) with 19
                       by (vm_compute; reflexivity); lia)).
    exact (Hfr q Hq Hset).
  Qed.

  Lemma vp_inv3_s7 (m0 m : regfile) (sp0 : mword 64) (a : Z)
      (fd ap ap' v3 : mword 64) (i : nat) :
    vp_inv3 m0 m sp0 a fd ap v3 i ->
    vp_inv3 m0 (<[Regidx s7_idx := regval_into_reg ap']> m) sp0 a fd ap' v3 i.
  Proof.
    intros (Hsp & Hs0 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & _ & Hs8 & Hfr).
    unfold vp_inv3.
    rewrite (upd_ne m (Regidx s7_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s7_idx) (Regidx s0_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s7_idx) (Regidx s2_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s7_idx) (Regidx s3_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s7_idx) (Regidx s4_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s7_idx) (Regidx s5_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s7_idx) (Regidx s6_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s7_idx) (Regidx s8_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_eq m (Regidx s7_idx) _).
    repeat (split; [ (assumption || reflexivity) | ]).
    intros q Hq Hset.
    rewrite (upd_ne m (Regidx s7_idx) (Regidx q) _
               ltac:(apply uidx_ne; replace (uint s7_idx) with 23
                       by (vm_compute; reflexivity); lia)).
    exact (Hfr q Hq Hset).
  Qed.

  (* --------------------------------------------------------------------- *)
  (* THE ARGUMENT STRING'S LOOP.  [k+1] bytes are left, the one in a1 is    *)
  (* [sf j], and the [c.bnez a1] at 0x70e decides -- exactly as the format  *)
  (* loop's [beqz s1] does -- whether what was just loaded is a body byte   *)
  (* or the terminator.  The argv string is [DfracDiscarded], so nothing    *)
  (* is threaded: every byte is persistent and taken again where needed.    *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kcat_vprintf_sloop (m0 : regfile) (sp0 fd ap v3 : mword 64) (a : Z)
      (i : nat) (sa : Z) (slen : nat) (sf : nat -> bv 8) (k : nat) :
    0 <= sa -> sa + Z.of_nat slen < 2 ^ 38 ->
    forall (j : nat) (h : CpuId) (m : regfile) (n : nat),
      (j + S k)%nat = slen ->
      vp_inv3 m0 m sp0 a fd ap v3 i ->
      m !!! Regidx s1_idx = mword_of_int (sa + Z.of_nat j) ->
      cat_code γt -∗
      ustr γd DfracDiscarded sa slen sf -∗
      urun γt γd γs h m (mword_of_int 0x702) (4 + n) -∗
      (∀ (h' : CpuId) (m' : regfile),
         ⌜ vp_inv3 m0 m' sp0 a fd ap v3 i ⌝ -∗
         urun γt γd γs h' m' (mword_of_int 0x710) (4 + n) -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    intros Hsa0 Hsahi.
    induction k as [| k IH ];
      intros j h m n Hjk Hinv Hs1;
      iIntros "#Hcode #Hstr Hrun Hcont";
      iDestruct (ustr_nonul with "Hstr") as %Hnn;
      assert (Hjlt : (j < slen)%nat) by lia;
      assert (Hp0 : 0 <= sa + Z.of_nat j) by lia;
      assert (Hp1 : sa + Z.of_nat j + 1 < Z64) by (unfold Z64; lia).
    - (* the LAST byte: what 0x70a loads is the terminator *)
      iDestruct (ustr_nul with "Hstr") as "[#Hnul _]".
      iApply (wp_kcat_vprintf_sstep m0 sp0 fd ap v3 a i
                DfracDiscarded (sa + Z.of_nat j) ubyte0 h m n Hp0 Hp1
                Hinv Hs1 with "Hcode [] Hrun").
      { replace (sa + Z.of_nat j + 1)%Z with (sa + Z.of_nat slen)%Z by lia.
        iExact "Hnul". }
      iIntros (h1 m1) "_ %Hinv1 %Hs11 %Ha11 Hrun".
      (* ---- 0x70e  c.bnez a1,0x702 -- NOT taken: the terminator ---- *)
      assert (Hnt : false = neq_vec (m1 !!! Regidx a1_idx) zero_reg).
      { rewrite Ha11 zext8_moi.
        replace (bv_unsigned ubyte0) with 0 by (vm_compute; reflexivity).
        unfold neq_vec. rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia)).
        reflexivity. }
      iApply (wp_uk_cbnez γt γd γs h1 m1 (mword_of_int 0x70e)
                (mword_of_int 250 : mword 8) (mword_of_int 3 : mword 3) a1_idx
                false
                (add_vec (mword_of_int 0x70e : mword 64)
                   (sign_extend' 64
                      (sign_extend' 13
                         (concat_vec (mword_of_int 250 : mword 8) ('b"0")))))
                (4 + n) ltac:(vm_compute; reflexivity) Hnt eq_refl
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_cat_70e with "Hcode"). }
      assert (E70e : add_vec_int (mword_of_int 0x70e : mword 64) 2
                     = mword_of_int 0x710)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E70e.
      iIntros (h2) "Hrun".
      iApply ("Hcont" $! h2 m1 with "[] Hrun"). iPureIntro. exact Hinv1.
    - (* a BODY byte follows: round again *)
      assert (Hsjlt : (S j < slen)%nat) by lia.
      iDestruct (ustr_byte γd DfracDiscarded sa slen sf (S j) Hsjlt with "Hstr")
        as "[#Hb1 _]".
      iApply (wp_kcat_vprintf_sstep m0 sp0 fd ap v3 a i
                DfracDiscarded (sa + Z.of_nat j) (sf (S j)) h m n Hp0 Hp1
                Hinv Hs1 with "Hcode [] Hrun").
      { replace (sa + Z.of_nat j + 1)%Z with (sa + Z.of_nat (S j))%Z by lia.
        iExact "Hb1". }
      iIntros (h1 m1) "_ %Hinv1 %Hs11 %Ha11 Hrun".
      (* ---- 0x70e  c.bnez a1,0x702 -- TAKEN: a body byte is not NUL ---- *)
      assert (Hnz : bv_unsigned (sf (S j)) <> 0).
      { intro He. apply (Hnn (S j) Hsjlt). apply bv_eq.
        rewrite He. vm_compute. reflexivity. }
      assert (Hsr : 0 <= bv_unsigned (sf (S j)) < Z64).
      { assert (HH : 0 <= bv_unsigned (sf (S j)) < 256).
        { pose proof (bv_unsigned_in_range 8 (sf (S j))) as H0.
          assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
          rewrite Em8 in H0. exact H0. }
        unfold Z64. lia. }
      assert (Ht : true = neq_vec (m1 !!! Regidx a1_idx) zero_reg).
      { rewrite Ha11 zext8_moi. unfold neq_vec.
        rewrite (moi_eq_zero (bv_unsigned (sf (S j))) Hsr).
        destruct (Z.eqb_spec (bv_unsigned (sf (S j))) 0) as [He | _];
          [ exfalso; exact (Hnz He) | reflexivity ]. }
      assert (Etgt : add_vec (mword_of_int 0x70e : mword 64)
                       (sign_extend' 64
                          (sign_extend' 13
                             (concat_vec (mword_of_int 250 : mword 8) ('b"0"))))
                     = mword_of_int 0x702)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_cbnez γt γd γs h1 m1 (mword_of_int 0x70e)
                (mword_of_int 250 : mword 8) (mword_of_int 3 : mword 3) a1_idx
                true (mword_of_int 0x702) (4 + n)
                ltac:(vm_compute; reflexivity) Ht (eq_sym Etgt)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_cat_70e with "Hcode"). }
      iIntros (h2) "Hrun".
      assert (Hs1' : m1 !!! Regidx s1_idx
                     = mword_of_int (sa + Z.of_nat (S j)))
        by (rewrite Hs11; f_equal; lia).
      iApply (IH (S j) h2 m1 n ltac:(lia) Hinv1 Hs1'
                with "Hcode Hstr Hrun Hcont").
  Qed.


  (* --------------------------------------------------------------------- *)
  (* THE TAIL OF EVERY ROUND, 0x554 -> 0x562:                               *)
  (*                                                                        *)
  (*   addiw a5,s2,1 ; c.mv s2,a5 ; c.mv a4,a5 ; c.add a5,a5,s4 ;           *)
  (*   lbu s1,0(a5)                                                          *)
  (*                                                                        *)
  (* The index advances, a4 keeps a copy of it, and the next format byte     *)
  (* lands in s1.  It is stated over [vp_inv3] rather than [vp_inv] because  *)
  (* the '%s' arm reaches it with the state register holding the va_list.    *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kcat_vprintf_bump (m0 : regfile) (sp0 fd ap v3 : mword 64) (a : Z)
      (i : nat) (b1 : mword 8) (h : CpuId) (m : regfile) (n : nat) :
    0 <= a -> a + Z.of_nat i + 2 < 2 ^ 31 ->
    vp_inv3 m0 m sp0 a fd ap v3 i ->
    cat_code γt -∗
    utext γt (a + Z.of_nat (S i)) b1 -∗
    urun γt γd γs h m (mword_of_int 0x554) (4 + n) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ vp_inv3 m0 m' sp0 a fd ap v3 (S i) ⌝ -∗
       ⌜ m' !!! Regidx s1_idx = mword_of_int (bv_unsigned b1) ⌝ -∗
       ⌜ m' !!! Regidx a4_idx = mword_of_int (Z.of_nat (S i)) ⌝ -∗
       urun γt γd γs h' m' (mword_of_int 0x562) (4 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd Hinv.
    pose proof Hinv as Hd.
    destruct Hd as (Hsp & Hs0 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hfr).
    iIntros "#Hcode #Hb1 Hrun Hcont".
    (* ---- 0x554  addiw a5,s2,1 ---- *)
    assert (Es1_12 : (sign_extend' 64 (mword_of_int 1 : mword 12) : mword 64)
                     = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Ea5n : sign_extend' 64
                     (subrange_vec_dec
                        (add_vec (m !!! Regidx s2_idx)
                           (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0)
                   = (mword_of_int (Z.of_nat (S i)) : mword 64)).
    { rewrite Hs2 Es1_12.
      rewrite (moi_addw (Z.of_nat i) 1 ltac:(unfold Z31; lia)).
      f_equal. lia. }
    iApply (wp_uk_addiw γt γd γs h m (mword_of_int 0x554)
              (mword_of_int 1 : mword 12) s2_idx a5_idx
              (mword_of_int (Z.of_nat (S i))) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ea5n))
              with "[] Hrun").
    { iApply (uis_cat_554 with "Hcode"). }
    assert (E554 : add_vec_int (mword_of_int 0x554 : mword 64) 4
                   = mword_of_int 0x558)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E554.
    iIntros (h6) "Hrun".
    set (m3 := <[Regidx a5_idx
                 := regval_into_reg
                      (mword_of_int (Z.of_nat (S i)) : mword 64)]> m).
    assert (Ha53 : m3 !!! Regidx a5_idx = mword_of_int (Z.of_nat (S i)))
      by exact (upd_eq m (Regidx a5_idx) (regval_into_reg _)).
    assert (Hinv3 : vp_inv3 m0 m3 sp0 a fd ap v3 i)
      by exact (vp_inv3_upd m0 m sp0 a fd ap v3 i a5_idx _
                  ltac:(vm_compute; reflexivity) Hinv).
    (* ---- 0x558  c.mv s2,a5 -- the index moves ---- *)
    iApply (wp_uk_cmv γt γd γs h6 m3 (mword_of_int 0x558) s2_idx a5_idx
              (mword_of_int (Z.of_nat (S i))) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha53; symmetry; apply add_vec_zero_l)
              with "[] Hrun").
    { iApply (uis_cat_558 with "Hcode"). }
    assert (E558 : add_vec_int (mword_of_int 0x558 : mword 64) 2
                   = mword_of_int 0x55a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E558.
    iIntros (h7) "Hrun".
    set (m4 := <[Regidx s2_idx
                 := regval_into_reg
                      (mword_of_int (Z.of_nat (S i)) : mword 64)]> m3).
    pose proof (vp_inv3_bump m0 m3 sp0 a fd ap v3 i (S i) _
                  eq_refl Hinv3) as Hinv4.
    assert (Ha54 : m4 !!! Regidx a5_idx = mword_of_int (Z.of_nat (S i))).
    { rewrite <- Ha53.
      exact (upd_ne m3 (Regidx s2_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x55a  c.mv a4,a5 ---- *)
    iApply (wp_uk_cmv γt γd γs h7 m4 (mword_of_int 0x55a) a4_idx a5_idx
              (mword_of_int (Z.of_nat (S i))) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha54; symmetry; apply add_vec_zero_l)
              with "[] Hrun").
    { iApply (uis_cat_55a with "Hcode"). }
    assert (E55a : add_vec_int (mword_of_int 0x55a : mword 64) 2
                   = mword_of_int 0x55c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E55a.
    iIntros (h8) "Hrun".
    set (m5 := <[Regidx a4_idx
                 := regval_into_reg
                      (mword_of_int (Z.of_nat (S i)) : mword 64)]> m4).
    assert (Hinv5 : vp_inv3 m0 m5 sp0 a fd ap v3 (S i))
      by exact (vp_inv3_upd m0 m4 sp0 a fd ap v3 (S i) a4_idx _
                  ltac:(vm_compute; reflexivity) Hinv4).
    pose proof Hinv5 as Hd5.
    destruct Hd5 as (Hsp5 & Hs05 & Hs25 & Hs35 & Hs45' & Hs55 & Hs65 & Hs75
                     & Hs85 & Hfr5).
    assert (Ha45 : m5 !!! Regidx a4_idx = mword_of_int (Z.of_nat (S i)))
      by exact (upd_eq m4 (Regidx a4_idx) (regval_into_reg _)).
    assert (Ha55 : m5 !!! Regidx a5_idx = mword_of_int (Z.of_nat (S i))).
    { rewrite <- Ha54.
      exact (upd_ne m4 (Regidx a4_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x55c  c.add a5,a5,s4 -- the pointer ---- *)
    assert (Eadd5 : add_vec (m5 !!! Regidx a5_idx) (m5 !!! Regidx s4_idx)
                    = mword_of_int (a + Z.of_nat (S i))).
    { rewrite Ha55 Hs45' moi_add. f_equal. lia. }
    iApply (wp_uk_cadd γt γd γs h8 m5 (mword_of_int 0x55c) a5_idx s4_idx
              (mword_of_int (a + Z.of_nat (S i))) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Eadd5))
              with "[] Hrun").
    { iApply (uis_cat_55c with "Hcode"). }
    assert (E55c : add_vec_int (mword_of_int 0x55c : mword 64) 2
                   = mword_of_int 0x55e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E55c.
    iIntros (h9) "Hrun".
    set (m6 := <[Regidx a5_idx
                 := regval_into_reg
                      (mword_of_int (a + Z.of_nat (S i)) : mword 64)]> m5).
    assert (Hinv6 : vp_inv3 m0 m6 sp0 a fd ap v3 (S i))
      by exact (vp_inv3_upd m0 m5 sp0 a fd ap v3 (S i) a5_idx _
                  ltac:(vm_compute; reflexivity) Hinv5).
    assert (Ha56 : m6 !!! Regidx a5_idx = mword_of_int (a + Z.of_nat (S i)))
      by exact (upd_eq m5 (Regidx a5_idx) (regval_into_reg _)).
    (* ---- 0x55e  lbu s1,0(a5) -- fmt[i+1], out of .rodata ---- *)
    assert (Hb64a : 0 <= a + Z.of_nat (S i) < Z64) by (unfold Z64; lia).
    assert (Haddr : (a + Z.of_nat (S i))%Z
                    = uint (m6 !!! Regidx a5_idx)
                      + uoff_i12 (mword_of_int 0 : mword 12)).
    { rewrite Ha56 (uint_moi (a + Z.of_nat (S i)) Hb64a).
      replace (uoff_i12 (mword_of_int 0 : mword 12)) with 0
        by (vm_compute; reflexivity).
      lia. }
    iApply (wp_uk_lbu_text γt γd γs h9 m6 (mword_of_int 0x55e)
              (mword_of_int 0 : mword 12) a5_idx s1_idx
              (a + Z.of_nat (S i)) b1 (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              Haddr ltac:(vm_compute; discriminate)
              with "[] Hb1 Hrun").
    { iApply (uis_cat_55e with "Hcode"). }
    assert (E55e : add_vec_int (mword_of_int 0x55e : mword 64) 4
                   = mword_of_int 0x562)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E55e.
    iIntros (h10) "Hrun".
    set (m7 := <[Regidx s1_idx
                 := regval_into_reg (zero_extend' 64 b1 : mword 64)]> m6).
    iApply ("Hcont" $! h10 m7 with "[] [] [] Hrun").
    - iPureIntro.
      exact (vp_inv3_upd m0 m6 sp0 a fd ap v3 (S i) s1_idx _
               ltac:(vm_compute; reflexivity) Hinv6).
    - iPureIntro. rewrite /m7 (upd_eq m6 (Regidx s1_idx) (regval_into_reg _)).
      exact (zext8_moi b1).
    - iPureIntro.
      rewrite /m7 (upd_ne m6 (Regidx s1_idx) (Regidx a4_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m6 (upd_ne m5 (Regidx a5_idx) (Regidx a4_idx) _
                     ltac:(vm_compute; discriminate)).
      exact Ha45.
  Qed.

  (* --------------------------------------------------------------------- *)
  (* THE ROUND THAT SEES THE '%', 0x566 -> 0x562.                           *)
  (*                                                                        *)
  (* It differs from a plain round at one instruction: at 0x56e the         *)
  (* character IS s5, so the branch to the putc arm is NOT taken and 0x572  *)
  (* sets the state register instead.  The index still advances, and a4     *)
  (* keeps a copy of it -- which is the only reason the directive's own     *)
  (* round, one turn later, can find fmt[i+1] at 0x576.                     *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kcat_vprintf_pct (m0 : regfile) (sp0 fd ap : mword 64) (a : Z)
      (i : nat) (b1 : mword 8) (h : CpuId) (m : regfile) (n : nat) :
    0 <= a -> a + Z.of_nat i + 2 < 2 ^ 31 ->
    vp_inv m0 m sp0 a fd ap i ->
    m !!! Regidx s1_idx = mword_of_int 37 ->
    cat_code γt -∗
    utext γt (a + Z.of_nat (S i)) b1 -∗
    urun γt γd γs h m (mword_of_int 0x566) (4 + n) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ vp_inv3 m0 m' sp0 a fd ap (mword_of_int 37) (S i) ⌝ -∗
       ⌜ m' !!! Regidx s1_idx = mword_of_int (bv_unsigned b1) ⌝ -∗
       ⌜ m' !!! Regidx a4_idx = mword_of_int (Z.of_nat (S i)) ⌝ -∗
       urun γt γd γs h' m' (mword_of_int 0x562) (4 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd Hinv0 Hs1.
    pose proof (vp_inv_to3 m0 m sp0 a fd ap i Hinv0) as Hinv.
    pose proof Hinv as Hd.
    destruct Hd as (Hsp & Hs0 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hfr).
    iIntros "#Hcode #Hb1 Hrun Hcont".
    assert (Hi31 : 0 <= Z.of_nat i + 1 < Z31) by (unfold Z31; lia).
    (* ---- 0x566  sext.w a5,s1 ---- *)
    assert (Ez0 : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                  = mword_of_int 0)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Ea5c : sign_extend' 64
                     (subrange_vec_dec
                        (add_vec (m !!! Regidx s1_idx)
                           (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0)
                   = (mword_of_int 37 : mword 64)).
    { rewrite Hs1 Ez0.
      rewrite (moi_addw 37 0 ltac:(unfold Z31; lia)). f_equal; lia. }
    iApply (wp_uk_addiw γt γd γs h m (mword_of_int 0x566)
              (mword_of_int 0 : mword 12) s1_idx a5_idx (mword_of_int 37) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ea5c))
              with "[] Hrun").
    { iApply (uis_cat_566 with "Hcode"). }
    assert (E566 : add_vec_int (mword_of_int 0x566 : mword 64) 4
                   = mword_of_int 0x56a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E566.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int 37 : mword 64)]> m).
    assert (Hinv1 : vp_inv3 m0 m1 sp0 a fd ap zero_reg i)
      by exact (vp_inv3_upd m0 m sp0 a fd ap zero_reg i a5_idx _
                  ltac:(vm_compute; reflexivity) Hinv).
    pose proof Hinv1 as Hd1.
    destruct Hd1 as (Hsp1 & Hs01 & Hs21 & Hs31 & Hs41 & Hs51 & Hs61 & Hs71
                     & Hs81 & Hfr1).
    assert (Ha5_1 : m1 !!! Regidx a5_idx = mword_of_int 37)
      by exact (upd_eq m (Regidx a5_idx) (regval_into_reg _)).
    (* ---- 0x56a  bnez s3,0x550 -- NOT taken, the state register is 0 ---- *)
    assert (Hnt : false = uv_btaken BNE (m1 !!! Regidx s3_idx) zero_reg)
      by (rewrite Hs31; vm_compute; reflexivity).
    iApply (wp_uk_btype0 γt γd γs h1 m1 (mword_of_int 0x56a)
              (mword_of_int 8166 : mword 13) s3_idx BNE false
              (add_vec (mword_of_int 0x56a : mword 64)
                 (sign_extend' 64 (mword_of_int 8166 : mword 13)))
              (4 + n) Hnt eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_cat_56a with "Hcode"). }
    assert (E56a : add_vec_int (mword_of_int 0x56a : mword 64) 4
                   = mword_of_int 0x56e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E56a.
    iIntros (h2) "Hrun".
    (* ---- 0x56e  bne a5,s5,0x546 -- NOT taken: the character IS '%' ---- *)
    assert (Hnt2 : false
                   = uv_btaken BNE (m1 !!! Regidx a5_idx) (m1 !!! Regidx s5_idx)).
    { rewrite Ha5_1 Hs51. cbn [uv_btaken].
      rewrite (moi_neq_vec 37 37 ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
      reflexivity. }
    iApply (wp_uk_btype γt γd γs h2 m1 (mword_of_int 0x56e)
              (mword_of_int 8152 : mword 13) s5_idx a5_idx BNE false
              (add_vec (mword_of_int 0x56e : mword 64)
                 (sign_extend' 64 (mword_of_int 8152 : mword 13)))
              (4 + n) Hnt2 eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_cat_56e with "Hcode"). }
    assert (E56e : add_vec_int (mword_of_int 0x56e : mword 64) 4
                   = mword_of_int 0x572)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E56e.
    iIntros (h3) "Hrun".
    (* ---- 0x572  c.mv s3,a5 -- state := '%' ---- *)
    iApply (wp_uk_cmv γt γd γs h3 m1 (mword_of_int 0x572) s3_idx a5_idx
              (mword_of_int 37) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_1; symmetry; apply add_vec_zero_l)
              with "[] Hrun").
    { iApply (uis_cat_572 with "Hcode"). }
    assert (E572 : add_vec_int (mword_of_int 0x572 : mword 64) 2
                   = mword_of_int 0x574)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E572.
    iIntros (h4) "Hrun".
    set (m2 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int 37 : mword 64)]> m1).
    pose proof (vp_inv3_s3 m0 m1 sp0 a fd ap zero_reg (mword_of_int 37) i
                  Hinv1) as Hinv2.
    pose proof Hinv2 as Hd2.
    destruct Hd2 as (Hsp2 & Hs02 & Hs22 & Hs32 & Hs42 & Hs52 & Hs62 & Hs72
                     & Hs82 & Hfr2).
    (* ---- 0x574  c.j 0x554 ---- *)
    assert (Etgt554 : (mword_of_int 0x554 : mword 64)
                      = add_vec (mword_of_int 0x574 : mword 64)
                          (sign_extend' 64
                             (sign_extend' 21
                                (concat_vec (mword_of_int 2032 : mword 11)
                                   ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cj γt γd γs h4 m2 (mword_of_int 0x574)
              (mword_of_int 2032 : mword 11) (mword_of_int 0x554) (4 + n)
              Etgt554 ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_574 with "Hcode"). }
    iIntros (h5) "Hrun".
    iApply (wp_kcat_vprintf_bump m0 sp0 fd ap (mword_of_int 37) a i b1
              h5 m2 n Ha0 Habnd Hinv2 with "Hcode Hb1 Hrun Hcont").
  Qed.

  (* --------------------------------------------------------------------- *)
  (* THE '%s' ARM PROPER, 0x6f2 -> 0x562.                                   *)
  (*                                                                        *)
  (*   addi s3,s7,8   the va_list is bumped -- into s3, because s7 must     *)
  (*                  still point at the argument for the [ld] that follows *)
  (*   ld   s1,0(s7)  the char* itself                                       *)
  (*   beqz s1,0x716  the "(null)" arm, excluded by [sa <> 0]                *)
  (*   lbu  a1,0(s1) ; beqz a1,0x730   the empty-string arm, which is the    *)
  (*                  same three instructions as the loop's exit             *)
  (*   0x702..0x70e   one putc per byte                                      *)
  (*   mv s7,s3 ; li s3,0 ; j 0x554    the bumped list is installed and the  *)
  (*                  state goes back to 0                                   *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kcat_vprintf_pcs3 (m0 : regfile) (sp0 fd : mword 64) (a : Z)
      (i : nat) (apz sa : Z) (dq : dfrac) (c1 : mword 8)
      (slen : nat) (sf : nat -> bv 8)
      (m : regfile) (h : CpuId) (n : nat) :
    0 <= a -> a + Z.of_nat i + 2 < 2 ^ 31 ->
    0 <= apz -> apz + 8 <= 2 ^ 38 -> apz mod 8 = 0 ->
    sa <> 0 ->
    vp_inv3 m0 m sp0 a fd (mword_of_int apz) (mword_of_int 37) i ->
    cat_code γt -∗
    utext γt (a + Z.of_nat (S i)) c1 -∗
    uwordq γd dq apz (mword_of_int sa) -∗
    ustr γd DfracDiscarded sa slen sf -∗
    urun γt γd γs h m (mword_of_int 0x6f2) (4 + n) -∗
    (∀ (h' : CpuId) (m' : regfile),
       uwordq γd dq apz (mword_of_int sa) -∗
       ⌜ vp_inv m0 m' sp0 a fd (mword_of_int (apz + 8)) (S i) ⌝ -∗
       ⌜ m' !!! Regidx s1_idx = mword_of_int (bv_unsigned c1) ⌝ -∗
       urun γt γd γs h' m' (mword_of_int 0x562) (4 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd Hap0 Haphi Hapal Hsanz Hinv.
    pose proof Hinv as Hd.
    destruct Hd as (Hsp & Hs0 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hfr).
    iIntros "#Hcode #Hc1 Hw #Hstr Hrun Hcont".
    iDestruct (urun_ustr_bnd with "Hrun Hstr") as %[Hsa0 Hsahi].
    assert (Ezr : (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64)
                  = zero_reg)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Etgt554 : (mword_of_int 0x554 : mword 64)
                      = add_vec (mword_of_int 0x714 : mword 64)
                          (sign_extend' 64
                             (sign_extend' 21
                                (concat_vec (mword_of_int 1824 : mword 11)
                                   ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Etgt554' : (mword_of_int 0x554 : mword 64)
                       = add_vec (mword_of_int 0x734 : mword 64)
                           (sign_extend' 64
                              (sign_extend' 21
                                 (concat_vec (mword_of_int 1808 : mword 11)
                                    ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0x6f2  addi s3,s7,8 -- the BUMPED va_list, parked in s3 ---- *)
    assert (E8 : (sign_extend' 64 (mword_of_int 8 : mword 12) : mword 64)
                 = mword_of_int 8)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Ebump : add_vec (m !!! Regidx s7_idx)
                      (sign_extend' 64 (mword_of_int 8 : mword 12))
                    = mword_of_int (apz + 8))
      by (rewrite Hs7 E8 moi_add; reflexivity).
    iApply (wp_uk_addi γt γd γs h m (mword_of_int 0x6f2)
              (mword_of_int 8 : mword 12) s7_idx s3_idx
              (mword_of_int (apz + 8)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ebump))
              with "[] Hrun").
    { iApply (uis_cat_6f2 with "Hcode"). }
    assert (E6f2 : add_vec_int (mword_of_int 0x6f2 : mword 64) 4
                   = mword_of_int 0x6f6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E6f2.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int (apz + 8) : mword 64)]> m).
    pose proof (vp_inv3_s3 m0 m sp0 a fd (mword_of_int apz) (mword_of_int 37)
                  (mword_of_int (apz + 8)) i Hinv) as Hinv1.
    pose proof Hinv1 as Hd1.
    destruct Hd1 as (Hsp1 & Hs01 & Hs21 & Hs31 & Hs41 & Hs51 & Hs61 & Hs71
                     & Hs81 & Hfr1).
    (* ---- 0x6f6  ld s1,0(s7) -- the char* out of the caller's frame ---- *)
    assert (Hapr : 0 <= apz < Z64) by (unfold Z64; lia).
    assert (Haddr : apz = uint (m1 !!! Regidx s7_idx)
                           + uoff_i12 (mword_of_int 0 : mword 12)).
    { rewrite Hs71 (uint_moi apz Hapr).
      replace (uoff_i12 (mword_of_int 0 : mword 12)) with 0
        by (vm_compute; reflexivity).
      lia. }
    iApply (wp_uk_ld γt γd γs h1 m1 (mword_of_int 0x6f6)
              (mword_of_int 0 : mword 12) s7_idx s1_idx dq apz
              (mword_of_int sa) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              Haddr Hapal ltac:(vm_compute; discriminate)
              with "[] Hw Hrun").
    { iApply (uis_cat_6f6 with "Hcode"). }
    assert (E6f6 : add_vec_int (mword_of_int 0x6f6 : mword 64) 4
                   = mword_of_int 0x6fa)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E6f6.
    iIntros "Hw" (h2) "Hrun".
    set (m2 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int sa : mword 64)]> m1).
    assert (Hinv2 : vp_inv3 m0 m2 sp0 a fd (mword_of_int apz) (mword_of_int (apz + 8)) i)
      by exact (vp_inv3_upd m0 m1 sp0 a fd (mword_of_int apz) (mword_of_int (apz + 8)) i s1_idx _
                  ltac:(vm_compute; reflexivity) Hinv1).
    assert (Hs1_2 : m2 !!! Regidx s1_idx = mword_of_int sa)
      by exact (upd_eq m1 (Regidx s1_idx) (regval_into_reg _)).
    (* ---- 0x6fa  c.beqz s1,0x716 -- NOT taken: the pointer is not null -- *)
    assert (Hsar : 0 <= sa < Z64) by (unfold Z64; lia).
    assert (Hn6fa : false = eq_vec (m2 !!! Regidx s1_idx) zero_reg).
    { rewrite Hs1_2 (moi_eq_zero sa Hsar).
      destruct (Z.eqb_spec sa 0) as [He | _];
        [ exfalso; exact (Hsanz He) | reflexivity ]. }
    iApply (wp_uk_cbeqz γt γd γs h2 m2 (mword_of_int 0x6fa)
              (mword_of_int 14 : mword 8) (mword_of_int 1 : mword 3) s1_idx
              false
              (add_vec (mword_of_int 0x6fa : mword 64)
                 (sign_extend' 64
                    (sign_extend' 13
                       (concat_vec (mword_of_int 14 : mword 8) ('b"0")))))
              (4 + n) ltac:(vm_compute; reflexivity) Hn6fa eq_refl
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_cat_6fa with "Hcode"). }
    assert (E6fa : add_vec_int (mword_of_int 0x6fa : mword 64) 2
                   = mword_of_int 0x6fc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E6fa.
    iIntros (h3) "Hrun".
    (* ---- 0x6fc  lbu a1,0(s1) -- the string's first byte ---- *)
    assert (Haddr0 : (sa + Z.of_nat 0%nat)%Z
                     = uint (m2 !!! Regidx s1_idx)
                       + uoff_i12 (mword_of_int 0 : mword 12)).
    { rewrite Hs1_2 (uint_moi sa Hsar).
      replace (uoff_i12 (mword_of_int 0 : mword 12)) with 0
        by (vm_compute; reflexivity).
      lia. }
    destruct slen as [| slen' ].
    - (* THE EMPTY STRING.  0x6fc reads the terminator, 0x700 is taken, and
         the arm at 0x730 is the loop's exit written out a second time. *)
      iDestruct (ustr_nul with "Hstr") as "[#Hnul _]".
      iApply (wp_uk_lbu γt γd γs h3 m2 (mword_of_int 0x6fc)
                (mword_of_int 0 : mword 12) s1_idx a1_idx DfracDiscarded
                (sa + Z.of_nat 0%nat)%Z ubyte0 (4 + n)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                Haddr0 ltac:(vm_compute; discriminate)
                with "[] [] Hrun").
      { iApply (uis_cat_6fc with "Hcode"). }
      { iExact "Hnul". }
      assert (E6fc : add_vec_int (mword_of_int 0x6fc : mword 64) 4
                     = mword_of_int 0x700)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E6fc.
      iIntros "_" (h4) "Hrun".
      set (m3 := <[Regidx a1_idx
                   := regval_into_reg (zero_extend' 64 (ubyte0 : mword 8) : mword 64)]> m2).
      assert (Hinv3 : vp_inv3 m0 m3 sp0 a fd (mword_of_int apz) (mword_of_int (apz + 8)) i)
        by exact (vp_inv3_upd m0 m2 sp0 a fd (mword_of_int apz) (mword_of_int (apz + 8)) i a1_idx _
                    ltac:(vm_compute; reflexivity) Hinv2).
      (* ---- 0x700  c.beqz a1,0x730 -- TAKEN ---- *)
      assert (Ht700 : true = eq_vec (m3 !!! Regidx a1_idx) zero_reg).
      { rewrite /m3 (upd_eq m2 (Regidx a1_idx) (regval_into_reg _)) zext8_moi.
        replace (bv_unsigned ubyte0) with 0 by (vm_compute; reflexivity).
        rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
      assert (Etgt730 : add_vec (mword_of_int 0x700 : mword 64)
                          (sign_extend' 64
                             (sign_extend' 13
                                (concat_vec (mword_of_int 24 : mword 8)
                                   ('b"0"))))
                        = mword_of_int 0x730)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_cbeqz γt γd γs h4 m3 (mword_of_int 0x700)
                (mword_of_int 24 : mword 8) (mword_of_int 3 : mword 3) a1_idx
                true (mword_of_int 0x730) (4 + n)
                ltac:(vm_compute; reflexivity) Ht700 (eq_sym Etgt730)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_cat_700 with "Hcode"). }
      iIntros (h5) "Hrun".
      (* ---- 0x730  c.mv s7,s3 ---- *)
      iApply (wp_uk_cmv γt γd γs h5 m3 (mword_of_int 0x730) s7_idx s3_idx
                (mword_of_int (apz + 8)) (4 + n)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(destruct Hinv3 as (_ & _ & _ & Hq & _); rewrite Hq;
                      symmetry; apply add_vec_zero_l)
                with "[] Hrun").
      { iApply (uis_cat_730 with "Hcode"). }
      assert (E730 : add_vec_int (mword_of_int 0x730 : mword 64) 2
                     = mword_of_int 0x732)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E730.
      iIntros (h6) "Hrun".
      set (m4 := <[Regidx s7_idx
                   := regval_into_reg
                        (mword_of_int (apz + 8) : mword 64)]> m3).
      pose proof (vp_inv3_s7 m0 m3 sp0 a fd (mword_of_int apz)
                    (mword_of_int (apz + 8)) (mword_of_int (apz + 8)) i
                    Hinv3) as Hinv4.
      (* ---- 0x732  c.li s3,0 -- the state goes back ---- *)
      iApply (wp_uk_cli γt γd γs h6 m4 (mword_of_int 0x732)
                (mword_of_int 0 : mword 6) s3_idx (4 + n)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                with "[] Hrun").
      { iApply (uis_cat_732 with "Hcode"). }
      assert (E732 : add_vec_int (mword_of_int 0x732 : mword 64) 2
                     = mword_of_int 0x734)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E732.
      iIntros (h7) "Hrun".
      assert (Hinv5 : vp_inv3 m0
                        (<[Regidx s3_idx
                           := regval_into_reg
                                (sign_extend' 64 (mword_of_int 0 : mword 6)
                                 : mword 64)]> m4)
                        sp0 a fd (mword_of_int (apz + 8)) zero_reg i).
      { rewrite <- Ezr.
        exact (vp_inv3_s3 m0 m4 sp0 a fd (mword_of_int (apz + 8))
                 (mword_of_int (apz + 8)) _ i Hinv4). }
      (* ---- 0x734  c.j 0x554 ---- *)
      iApply (wp_uk_cj γt γd γs h7 _ (mword_of_int 0x734)
                (mword_of_int 1808 : mword 11) (mword_of_int 0x554) (4 + n)
                Etgt554' ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_cat_734 with "Hcode"). }
      iIntros (h8) "Hrun".
      iApply (wp_kcat_vprintf_bump m0 sp0 fd (mword_of_int (apz + 8)) zero_reg
                a i c1 h8 _ n Ha0 Habnd Hinv5 with "Hcode Hc1 Hrun [Hw Hcont]").
      iIntros (h9 m9) "%Hinv9 %Hs19 _ Hrun".
      iApply ("Hcont" $! h9 m9 with "Hw [] [] Hrun").
      + iPureIntro. exact (vp_inv_of3 m0 m9 sp0 a fd
                             (mword_of_int (apz + 8)) (S i) Hinv9).
      + iPureIntro. exact Hs19.
    - (* AT LEAST ONE BYTE.  0x700 falls through into the loop. *)
      iDestruct (ustr_byte γd DfracDiscarded sa (S slen') sf 0%nat
                   ltac:(lia) with "Hstr") as "[#Hb0 _]".
      iDestruct (ustr_nonul with "Hstr") as %Hnn.
      iApply (wp_uk_lbu γt γd γs h3 m2 (mword_of_int 0x6fc)
                (mword_of_int 0 : mword 12) s1_idx a1_idx DfracDiscarded
                (sa + Z.of_nat 0%nat)%Z (sf 0%nat) (4 + n)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                Haddr0 ltac:(vm_compute; discriminate)
                with "[] [] Hrun").
      { iApply (uis_cat_6fc with "Hcode"). }
      { iExact "Hb0". }
      assert (E6fc : add_vec_int (mword_of_int 0x6fc : mword 64) 4
                     = mword_of_int 0x700)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E6fc.
      iIntros "_" (h4) "Hrun".
      set (m3 := <[Regidx a1_idx
                   := regval_into_reg
                        (zero_extend' 64 (sf 0%nat : mword 8)
                         : mword 64)]> m2).
      assert (Hinv3 : vp_inv3 m0 m3 sp0 a fd (mword_of_int apz) (mword_of_int (apz + 8)) i)
        by exact (vp_inv3_upd m0 m2 sp0 a fd (mword_of_int apz) (mword_of_int (apz + 8)) i a1_idx _
                    ltac:(vm_compute; reflexivity) Hinv2).
      (* ---- 0x700  c.beqz a1,0x730 -- NOT taken ---- *)
      assert (Hnz0 : bv_unsigned (sf 0%nat) <> 0).
      { intro He. apply (Hnn 0%nat ltac:(lia)). apply bv_eq.
        rewrite He. vm_compute. reflexivity. }
      assert (Hr0 : 0 <= bv_unsigned (sf 0%nat) < Z64).
      { assert (HH : 0 <= bv_unsigned (sf 0%nat) < 256).
        { pose proof (bv_unsigned_in_range 8 (sf 0%nat)) as H0.
          assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
          rewrite Em8 in H0. exact H0. }
        unfold Z64. lia. }
      assert (Hn700 : false = eq_vec (m3 !!! Regidx a1_idx) zero_reg).
      { rewrite /m3 (upd_eq m2 (Regidx a1_idx) (regval_into_reg _)) zext8_moi.
        rewrite (moi_eq_zero (bv_unsigned (sf 0%nat)) Hr0).
        destruct (Z.eqb_spec (bv_unsigned (sf 0%nat)) 0) as [He | _];
          [ exfalso; exact (Hnz0 He) | reflexivity ]. }
      iApply (wp_uk_cbeqz γt γd γs h4 m3 (mword_of_int 0x700)
                (mword_of_int 24 : mword 8) (mword_of_int 3 : mword 3) a1_idx
                false
                (add_vec (mword_of_int 0x700 : mword 64)
                   (sign_extend' 64
                      (sign_extend' 13
                         (concat_vec (mword_of_int 24 : mword 8) ('b"0")))))
                (4 + n) ltac:(vm_compute; reflexivity) Hn700 eq_refl
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_cat_700 with "Hcode"). }
      assert (E700 : add_vec_int (mword_of_int 0x700 : mword 64) 2
                     = mword_of_int 0x702)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E700.
      iIntros (h5) "Hrun".
      assert (Hs1_3 : m3 !!! Regidx s1_idx
                      = mword_of_int (sa + Z.of_nat 0%nat)).
      { rewrite /m3 (upd_ne m2 (Regidx a1_idx) (Regidx s1_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite Hs1_2. f_equal; lia. }
      iApply (wp_kcat_vprintf_sloop m0 sp0 fd (mword_of_int apz)
                (mword_of_int (apz + 8)) a i sa (S slen') sf slen'
                Hsa0 Hsahi 0%nat h5 m3 n ltac:(lia) Hinv3 Hs1_3
                with "Hcode Hstr Hrun [Hw Hcont]").
      iIntros (h6 m6) "%Hinv6 Hrun".
      pose proof Hinv6 as Hd6.
      destruct Hd6 as (_ & _ & _ & Hs36 & _).
      (* ---- 0x710  c.mv s7,s3 ---- *)
      iApply (wp_uk_cmv γt γd γs h6 m6 (mword_of_int 0x710) s7_idx s3_idx
                (mword_of_int (apz + 8)) (4 + n)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs36; symmetry; apply add_vec_zero_l)
                with "[] Hrun").
      { iApply (uis_cat_710 with "Hcode"). }
      assert (E710 : add_vec_int (mword_of_int 0x710 : mword 64) 2
                     = mword_of_int 0x712)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E710.
      iIntros (h7) "Hrun".
      set (m7 := <[Regidx s7_idx
                   := regval_into_reg
                        (mword_of_int (apz + 8) : mword 64)]> m6).
      pose proof (vp_inv3_s7 m0 m6 sp0 a fd (mword_of_int apz)
                    (mword_of_int (apz + 8)) (mword_of_int (apz + 8)) i
                    Hinv6) as Hinv7.
      (* ---- 0x712  c.li s3,0 ---- *)
      iApply (wp_uk_cli γt γd γs h7 m7 (mword_of_int 0x712)
                (mword_of_int 0 : mword 6) s3_idx (4 + n)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                with "[] Hrun").
      { iApply (uis_cat_712 with "Hcode"). }
      assert (E712 : add_vec_int (mword_of_int 0x712 : mword 64) 2
                     = mword_of_int 0x714)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E712.
      iIntros (h8) "Hrun".
      assert (Hinv8 : vp_inv3 m0
                        (<[Regidx s3_idx
                           := regval_into_reg
                                (sign_extend' 64 (mword_of_int 0 : mword 6)
                                 : mword 64)]> m7)
                        sp0 a fd (mword_of_int (apz + 8)) zero_reg i).
      { rewrite <- Ezr.
        exact (vp_inv3_s3 m0 m7 sp0 a fd (mword_of_int (apz + 8))
                 (mword_of_int (apz + 8)) _ i Hinv7). }
      (* ---- 0x714  c.j 0x554 ---- *)
      iApply (wp_uk_cj γt γd γs h8 _ (mword_of_int 0x714)
                (mword_of_int 1824 : mword 11) (mword_of_int 0x554) (4 + n)
                Etgt554 ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_cat_714 with "Hcode"). }
      iIntros (h9) "Hrun".
      iApply (wp_kcat_vprintf_bump m0 sp0 fd (mword_of_int (apz + 8)) zero_reg
                a i c1 h9 _ n Ha0 Habnd Hinv8 with "Hcode Hc1 Hrun [Hw Hcont]").
      iIntros (h10 m10) "%Hinv10 %Hs110 _ Hrun".
      iApply ("Hcont" $! h10 m10 with "Hw [] [] Hrun").
      + iPureIntro. exact (vp_inv_of3 m0 m10 sp0 a fd
                             (mword_of_int (apz + 8)) (S i) Hinv10).
      + iPureIntro. exact Hs110.
  Qed.

  (* --------------------------------------------------------------------- *)
  (* THE REST OF THE CHAIN, 0x762 -> 0x6f2.  Eight more tests: 'u', then    *)
  (* the two long forms of it, then 'x' and its two, then 'p', then 'c',    *)
  (* and finally 's'.  a0, a2, a1 and a4 are scratch throughout.            *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kcat_vprintf_pcs2 (m0 : regfile) (sp0 fd : mword 64) (a : Z)
      (i : nat) (apz sa : Z) (dq : dfrac) (c1 c2 : mword 8)
      (slen : nat) (sf : nat -> bv 8)
      (m : regfile) (h : CpuId) (n : nat) :
    0 <= a -> a + Z.of_nat i + 3 < 2 ^ 31 ->
    0 <= apz -> apz + 8 <= 2 ^ 38 -> apz mod 8 = 0 ->
    sa <> 0 ->
    0 <= bv_unsigned c1 < 256 -> 0 <= bv_unsigned c2 < 256 ->
    bv_unsigned c1 <> 117 -> bv_unsigned c1 <> 120 ->
    bv_unsigned c2 <> 117 -> bv_unsigned c2 <> 120 ->
    vp_inv3 m0 m sp0 a fd (mword_of_int apz) (mword_of_int 37) i ->
    m !!! Regidx a1_idx = mword_of_int (bv_unsigned c2) ->
    m !!! Regidx a2_idx = mword_of_int (bv_unsigned c1) ->
    m !!! Regidx a5_idx = mword_of_int 115 ->
    cat_code γt -∗
    utext γt (a + Z.of_nat (S i)) c1 -∗
    uwordq γd dq apz (mword_of_int sa) -∗
    ustr γd DfracDiscarded sa slen sf -∗
    urun γt γd γs h m (mword_of_int 0x762) (4 + n) -∗
    (∀ (h' : CpuId) (m' : regfile),
       uwordq γd dq apz (mword_of_int sa) -∗
       ⌜ vp_inv m0 m' sp0 a fd (mword_of_int (apz + 8)) (S i) ⌝ -∗
       ⌜ m' !!! Regidx s1_idx = mword_of_int (bv_unsigned c1) ⌝ -∗
       urun γt γd γs h' m' (mword_of_int 0x562) (4 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd Hap0 Haphi Hapal Hsanz Hr1 Hr2 Hc1u Hc1x Hc2u Hc2x
           Hinv Ha1 Ha2 Ha5.
    iIntros "#Hcode #Hc1 Hw #Hstr Hrun Hcont".
    assert (Em117 : (sign_extend' 64 (mword_of_int 3979 : mword 12) : mword 64)
                    = mword_of_int (-117))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em120 : (sign_extend' 64 (mword_of_int 3976 : mword 12) : mword 64)
                    = mword_of_int (-120))
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0x762  li a0,117 ---- *)
    iApply (wp_uk_li γt γd γs h m (mword_of_int 0x762)
              (mword_of_int 117 : mword 12) a0_idx (mword_of_int 117) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_762 with "Hcode"). }
    assert (E762 : add_vec_int (mword_of_int 0x762 : mword 64) 4
                   = mword_of_int 0x766)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E762.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 117 : mword 64)]> m).
    assert (Hinv1 : vp_inv3 m0 m1 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m sp0 a fd (mword_of_int apz) (mword_of_int 37) i a0_idx _
                  ltac:(vm_compute; reflexivity) Hinv).
    assert (Ha0_1 : m1 !!! Regidx a0_idx = mword_of_int 117)
      by exact (upd_eq m (Regidx a0_idx) (regval_into_reg _)).
    assert (Ha1_1 : m1 !!! Regidx a1_idx = (mword_of_int (bv_unsigned c2))).
    { rewrite <- Ha1.
      exact (upd_ne m (Regidx a0_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha2_1 : m1 !!! Regidx a2_idx = (mword_of_int (bv_unsigned c1))).
    { rewrite <- Ha2.
      exact (upd_ne m (Regidx a0_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha5_1 : m1 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha5.
      exact (upd_ne m (Regidx a0_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x766  beq a5,a0 -- NOT taken ---- *)
    assert (Hn766 : false
                    = uv_btaken BEQ (m1 !!! Regidx a5_idx)
                        (m1 !!! Regidx a0_idx))
      by (rewrite Ha5_1 Ha0_1; vm_compute; reflexivity).
    iApply (wp_uk_btype γt γd γs h1 m1 (mword_of_int 0x766)
              (mword_of_int 7832 : mword 13) a0_idx a5_idx BEQ false
              (add_vec (mword_of_int 0x766 : mword 64)
                 (sign_extend' 64 (mword_of_int 7832 : mword 13)))
              (4 + n) Hn766 eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_cat_766 with "Hcode"). }
    assert (E766 : add_vec_int (mword_of_int 0x766 : mword 64) 4
                   = mword_of_int 0x76a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E766.
    iIntros (h2) "Hrun".
    (* ---- 0x76a  addi a0,a2,-117 ---- *)
    assert (Ev76a : add_vec (m1 !!! Regidx a2_idx)
                     (sign_extend' 64 (mword_of_int 3979 : mword 12))
                   = mword_of_int (bv_unsigned c1 - 117))
      by (rewrite Ha2_1 Em117 moi_add; reflexivity).
    iApply (wp_uk_addi γt γd γs h2 m1 (mword_of_int 0x76a)
              (mword_of_int 3979 : mword 12) a2_idx a0_idx
              (mword_of_int (bv_unsigned c1 - 117)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ev76a))
              with "[] Hrun").
    { iApply (uis_cat_76a with "Hcode"). }
    assert (E76a : add_vec_int (mword_of_int 0x76a : mword 64) 4
                   = mword_of_int 0x76e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E76a.
    iIntros (h3) "Hrun".
    set (m2 := <[Regidx a0_idx
                 := regval_into_reg
                      (mword_of_int (bv_unsigned c1 - 117) : mword 64)]> m1).
    assert (Hinv2 : vp_inv3 m0 m2 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m1 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a0_idx _
                  ltac:(vm_compute; reflexivity) Hinv1).
    assert (Ha0_2 : m2 !!! Regidx a0_idx = mword_of_int (bv_unsigned c1 - 117))
      by exact (upd_eq m1 (Regidx a0_idx) (regval_into_reg _)).
    assert (Ha1_2 : m2 !!! Regidx a1_idx = (mword_of_int (bv_unsigned c2))).
    { rewrite <- Ha1_1.
      exact (upd_ne m1 (Regidx a0_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha2_2 : m2 !!! Regidx a2_idx = (mword_of_int (bv_unsigned c1))).
    { rewrite <- Ha2_1.
      exact (upd_ne m1 (Regidx a0_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha5_2 : m2 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha5_1.
      exact (upd_ne m1 (Regidx a0_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x76e  c.bnez a0,0x774 -- TAKEN ---- *)
    assert (Ht76e : true = neq_vec (m2 !!! Regidx a0_idx) zero_reg)
      by (rewrite Ha0_2;
          exact (eq_sym (moi_sub_ne_zero (bv_unsigned c1) 117 Hr1
                           ltac:(lia) Hc1u))).
    assert (Et76e : add_vec (mword_of_int 0x76e : mword 64)
                     (sign_extend' 64
                        (sign_extend' 13
                           (concat_vec (mword_of_int 3 : mword 8) ('b"0"))))
                   = mword_of_int 0x774)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cbnez γt γd γs h3 m2 (mword_of_int 0x76e)
              (mword_of_int 3 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              true (mword_of_int 0x774) (4 + n)
              ltac:(vm_compute; reflexivity) Ht76e (eq_sym Et76e)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_76e with "Hcode"). }
    iIntros (h4) "Hrun".
    (* ---- 0x774  addi a0,a1,-117 ---- *)
    assert (Ev774 : add_vec (m2 !!! Regidx a1_idx)
                     (sign_extend' 64 (mword_of_int 3979 : mword 12))
                   = mword_of_int (bv_unsigned c2 - 117))
      by (rewrite Ha1_2 Em117 moi_add; reflexivity).
    iApply (wp_uk_addi γt γd γs h4 m2 (mword_of_int 0x774)
              (mword_of_int 3979 : mword 12) a1_idx a0_idx
              (mword_of_int (bv_unsigned c2 - 117)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ev774))
              with "[] Hrun").
    { iApply (uis_cat_774 with "Hcode"). }
    assert (E774 : add_vec_int (mword_of_int 0x774 : mword 64) 4
                   = mword_of_int 0x778)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E774.
    iIntros (h5) "Hrun".
    set (m3 := <[Regidx a0_idx
                 := regval_into_reg
                      (mword_of_int (bv_unsigned c2 - 117) : mword 64)]> m2).
    assert (Hinv3 : vp_inv3 m0 m3 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m2 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a0_idx _
                  ltac:(vm_compute; reflexivity) Hinv2).
    assert (Ha0_3 : m3 !!! Regidx a0_idx = mword_of_int (bv_unsigned c2 - 117))
      by exact (upd_eq m2 (Regidx a0_idx) (regval_into_reg _)).
    assert (Ha1_3 : m3 !!! Regidx a1_idx = (mword_of_int (bv_unsigned c2))).
    { rewrite <- Ha1_2.
      exact (upd_ne m2 (Regidx a0_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha2_3 : m3 !!! Regidx a2_idx = (mword_of_int (bv_unsigned c1))).
    { rewrite <- Ha2_2.
      exact (upd_ne m2 (Regidx a0_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha5_3 : m3 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha5_2.
      exact (upd_ne m2 (Regidx a0_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x778  c.bnez a0,0x77e -- TAKEN ---- *)
    assert (Ht778 : true = neq_vec (m3 !!! Regidx a0_idx) zero_reg)
      by (rewrite Ha0_3;
          exact (eq_sym (moi_sub_ne_zero (bv_unsigned c2) 117 Hr2
                           ltac:(lia) Hc2u))).
    assert (Et778 : add_vec (mword_of_int 0x778 : mword 64)
                     (sign_extend' 64
                        (sign_extend' 13
                           (concat_vec (mword_of_int 3 : mword 8) ('b"0"))))
                   = mword_of_int 0x77e)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cbnez γt γd γs h5 m3 (mword_of_int 0x778)
              (mword_of_int 3 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              true (mword_of_int 0x77e) (4 + n)
              ltac:(vm_compute; reflexivity) Ht778 (eq_sym Et778)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_778 with "Hcode"). }
    iIntros (h6) "Hrun".
    (* ---- 0x77e  li a0,120 ---- *)
    iApply (wp_uk_li γt γd γs h6 m3 (mword_of_int 0x77e)
              (mword_of_int 120 : mword 12) a0_idx (mword_of_int 120) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_77e with "Hcode"). }
    assert (E77e : add_vec_int (mword_of_int 0x77e : mword 64) 4
                   = mword_of_int 0x782)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E77e.
    iIntros (h7) "Hrun".
    set (m4 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 120 : mword 64)]> m3).
    assert (Hinv4 : vp_inv3 m0 m4 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m3 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a0_idx _
                  ltac:(vm_compute; reflexivity) Hinv3).
    assert (Ha0_4 : m4 !!! Regidx a0_idx = mword_of_int 120)
      by exact (upd_eq m3 (Regidx a0_idx) (regval_into_reg _)).
    assert (Ha1_4 : m4 !!! Regidx a1_idx = (mword_of_int (bv_unsigned c2))).
    { rewrite <- Ha1_3.
      exact (upd_ne m3 (Regidx a0_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha2_4 : m4 !!! Regidx a2_idx = (mword_of_int (bv_unsigned c1))).
    { rewrite <- Ha2_3.
      exact (upd_ne m3 (Regidx a0_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha5_4 : m4 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha5_3.
      exact (upd_ne m3 (Regidx a0_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x782  beq a5,a0 -- NOT taken ---- *)
    assert (Hn782 : false
                    = uv_btaken BEQ (m4 !!! Regidx a5_idx)
                        (m4 !!! Regidx a0_idx))
      by (rewrite Ha5_4 Ha0_4; vm_compute; reflexivity).
    iApply (wp_uk_btype γt γd γs h7 m4 (mword_of_int 0x782)
              (mword_of_int 7880 : mword 13) a0_idx a5_idx BEQ false
              (add_vec (mword_of_int 0x782 : mword 64)
                 (sign_extend' 64 (mword_of_int 7880 : mword 13)))
              (4 + n) Hn782 eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_cat_782 with "Hcode"). }
    assert (E782 : add_vec_int (mword_of_int 0x782 : mword 64) 4
                   = mword_of_int 0x786)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E782.
    iIntros (h8) "Hrun".
    (* ---- 0x786  addi a2,a2,-120 ---- *)
    assert (Ev786 : add_vec (m4 !!! Regidx a2_idx)
                     (sign_extend' 64 (mword_of_int 3976 : mword 12))
                   = mword_of_int (bv_unsigned c1 - 120))
      by (rewrite Ha2_4 Em120 moi_add; reflexivity).
    iApply (wp_uk_addi γt γd γs h8 m4 (mword_of_int 0x786)
              (mword_of_int 3976 : mword 12) a2_idx a2_idx
              (mword_of_int (bv_unsigned c1 - 120)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ev786))
              with "[] Hrun").
    { iApply (uis_cat_786 with "Hcode"). }
    assert (E786 : add_vec_int (mword_of_int 0x786 : mword 64) 4
                   = mword_of_int 0x78a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E786.
    iIntros (h9) "Hrun".
    set (m5 := <[Regidx a2_idx
                 := regval_into_reg
                      (mword_of_int (bv_unsigned c1 - 120) : mword 64)]> m4).
    assert (Hinv5 : vp_inv3 m0 m5 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m4 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a2_idx _
                  ltac:(vm_compute; reflexivity) Hinv4).
    assert (Ha2_5 : m5 !!! Regidx a2_idx = mword_of_int (bv_unsigned c1 - 120))
      by exact (upd_eq m4 (Regidx a2_idx) (regval_into_reg _)).
    assert (Ha1_5 : m5 !!! Regidx a1_idx = (mword_of_int (bv_unsigned c2))).
    { rewrite <- Ha1_4.
      exact (upd_ne m4 (Regidx a2_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha5_5 : m5 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha5_4.
      exact (upd_ne m4 (Regidx a2_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x78a  c.bnez a2,0x790 -- TAKEN ---- *)
    assert (Ht78a : true = neq_vec (m5 !!! Regidx a2_idx) zero_reg)
      by (rewrite Ha2_5;
          exact (eq_sym (moi_sub_ne_zero (bv_unsigned c1) 120 Hr1
                           ltac:(lia) Hc1x))).
    assert (Et78a : add_vec (mword_of_int 0x78a : mword 64)
                     (sign_extend' 64
                        (sign_extend' 13
                           (concat_vec (mword_of_int 3 : mword 8) ('b"0"))))
                   = mword_of_int 0x790)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cbnez γt γd γs h9 m5 (mword_of_int 0x78a)
              (mword_of_int 3 : mword 8) (mword_of_int 4 : mword 3) a2_idx
              true (mword_of_int 0x790) (4 + n)
              ltac:(vm_compute; reflexivity) Ht78a (eq_sym Et78a)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_78a with "Hcode"). }
    iIntros (h10) "Hrun".
    (* ---- 0x790  addi a1,a1,-120 ---- *)
    assert (Ev790 : add_vec (m5 !!! Regidx a1_idx)
                     (sign_extend' 64 (mword_of_int 3976 : mword 12))
                   = mword_of_int (bv_unsigned c2 - 120))
      by (rewrite Ha1_5 Em120 moi_add; reflexivity).
    iApply (wp_uk_addi γt γd γs h10 m5 (mword_of_int 0x790)
              (mword_of_int 3976 : mword 12) a1_idx a1_idx
              (mword_of_int (bv_unsigned c2 - 120)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ev790))
              with "[] Hrun").
    { iApply (uis_cat_790 with "Hcode"). }
    assert (E790 : add_vec_int (mword_of_int 0x790 : mword 64) 4
                   = mword_of_int 0x794)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E790.
    iIntros (h11) "Hrun".
    set (m6 := <[Regidx a1_idx
                 := regval_into_reg
                      (mword_of_int (bv_unsigned c2 - 120) : mword 64)]> m5).
    assert (Hinv6 : vp_inv3 m0 m6 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m5 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a1_idx _
                  ltac:(vm_compute; reflexivity) Hinv5).
    assert (Ha1_6 : m6 !!! Regidx a1_idx = mword_of_int (bv_unsigned c2 - 120))
      by exact (upd_eq m5 (Regidx a1_idx) (regval_into_reg _)).
    assert (Ha5_6 : m6 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha5_5.
      exact (upd_ne m5 (Regidx a1_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x794  c.bnez a1,0x79a -- TAKEN ---- *)
    assert (Ht794 : true = neq_vec (m6 !!! Regidx a1_idx) zero_reg)
      by (rewrite Ha1_6;
          exact (eq_sym (moi_sub_ne_zero (bv_unsigned c2) 120 Hr2
                           ltac:(lia) Hc2x))).
    assert (Et794 : add_vec (mword_of_int 0x794 : mword 64)
                     (sign_extend' 64
                        (sign_extend' 13
                           (concat_vec (mword_of_int 3 : mword 8) ('b"0"))))
                   = mword_of_int 0x79a)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cbnez γt γd γs h11 m6 (mword_of_int 0x794)
              (mword_of_int 3 : mword 8) (mword_of_int 3 : mword 3) a1_idx
              true (mword_of_int 0x79a) (4 + n)
              ltac:(vm_compute; reflexivity) Ht794 (eq_sym Et794)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_794 with "Hcode"). }
    iIntros (h12) "Hrun".
    (* ---- 0x79a  li a4,112 ---- *)
    iApply (wp_uk_li γt γd γs h12 m6 (mword_of_int 0x79a)
              (mword_of_int 112 : mword 12) a4_idx (mword_of_int 112) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_79a with "Hcode"). }
    assert (E79a : add_vec_int (mword_of_int 0x79a : mword 64) 4
                   = mword_of_int 0x79e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E79a.
    iIntros (h13) "Hrun".
    set (m7 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 112 : mword 64)]> m6).
    assert (Hinv7 : vp_inv3 m0 m7 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m6 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a4_idx _
                  ltac:(vm_compute; reflexivity) Hinv6).
    assert (Ha4_7 : m7 !!! Regidx a4_idx = mword_of_int 112)
      by exact (upd_eq m6 (Regidx a4_idx) (regval_into_reg _)).
    assert (Ha5_7 : m7 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha5_6.
      exact (upd_ne m6 (Regidx a4_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x79e  beq a5,a4 -- NOT taken ---- *)
    assert (Hn79e : false
                    = uv_btaken BEQ (m7 !!! Regidx a5_idx)
                        (m7 !!! Regidx a4_idx))
      by (rewrite Ha5_7 Ha4_7; vm_compute; reflexivity).
    iApply (wp_uk_btype γt γd γs h13 m7 (mword_of_int 0x79e)
              (mword_of_int 7928 : mword 13) a4_idx a5_idx BEQ false
              (add_vec (mword_of_int 0x79e : mword 64)
                 (sign_extend' 64 (mword_of_int 7928 : mword 13)))
              (4 + n) Hn79e eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_cat_79e with "Hcode"). }
    assert (E79e : add_vec_int (mword_of_int 0x79e : mword 64) 4
                   = mword_of_int 0x7a2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E79e.
    iIntros (h14) "Hrun".
    (* ---- 0x7a2  li a4,99 ---- *)
    iApply (wp_uk_li γt γd γs h14 m7 (mword_of_int 0x7a2)
              (mword_of_int 99 : mword 12) a4_idx (mword_of_int 99) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_7a2 with "Hcode"). }
    assert (E7a2 : add_vec_int (mword_of_int 0x7a2 : mword 64) 4
                   = mword_of_int 0x7a6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7a2.
    iIntros (h15) "Hrun".
    set (m8 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 99 : mword 64)]> m7).
    assert (Hinv8 : vp_inv3 m0 m8 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m7 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a4_idx _
                  ltac:(vm_compute; reflexivity) Hinv7).
    assert (Ha4_8 : m8 !!! Regidx a4_idx = mword_of_int 99)
      by exact (upd_eq m7 (Regidx a4_idx) (regval_into_reg _)).
    assert (Ha5_8 : m8 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha5_7.
      exact (upd_ne m7 (Regidx a4_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x7a6  beq a5,a4 -- NOT taken ---- *)
    assert (Hn7a6 : false
                    = uv_btaken BEQ (m8 !!! Regidx a5_idx)
                        (m8 !!! Regidx a4_idx))
      by (rewrite Ha5_8 Ha4_8; vm_compute; reflexivity).
    iApply (wp_uk_btype γt γd γs h15 m8 (mword_of_int 0x7a6)
              (mword_of_int 7992 : mword 13) a4_idx a5_idx BEQ false
              (add_vec (mword_of_int 0x7a6 : mword 64)
                 (sign_extend' 64 (mword_of_int 7992 : mword 13)))
              (4 + n) Hn7a6 eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_cat_7a6 with "Hcode"). }
    assert (E7a6 : add_vec_int (mword_of_int 0x7a6 : mword 64) 4
                   = mword_of_int 0x7aa)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7a6.
    iIntros (h16) "Hrun".
    (* ---- 0x7aa  li a4,115 ---- *)
    iApply (wp_uk_li γt γd γs h16 m8 (mword_of_int 0x7aa)
              (mword_of_int 115 : mword 12) a4_idx (mword_of_int 115) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_7aa with "Hcode"). }
    assert (E7aa : add_vec_int (mword_of_int 0x7aa : mword 64) 4
                   = mword_of_int 0x7ae)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7aa.
    iIntros (h17) "Hrun".
    set (m9 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 115 : mword 64)]> m8).
    assert (Hinv9 : vp_inv3 m0 m9 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m8 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a4_idx _
                  ltac:(vm_compute; reflexivity) Hinv8).
    assert (Ha4_9 : m9 !!! Regidx a4_idx = mword_of_int 115)
      by exact (upd_eq m8 (Regidx a4_idx) (regval_into_reg _)).
    assert (Ha5_9 : m9 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha5_8.
      exact (upd_ne m8 (Regidx a4_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x7ae  beq a5,a4,0x6f2 -- TAKEN: the directive is 's' ---- *)
    assert (Ht7ae : true
                    = uv_btaken BEQ (m9 !!! Regidx a5_idx)
                        (m9 !!! Regidx a4_idx))
      by (rewrite Ha5_9 Ha4_9; vm_compute; reflexivity).
    assert (Et7ae : add_vec (mword_of_int 0x7ae : mword 64)
                      (sign_extend' 64 (mword_of_int 8004 : mword 13))
                    = mword_of_int 0x6f2)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_btype γt γd γs h17 m9 (mword_of_int 0x7ae)
              (mword_of_int 8004 : mword 13) a4_idx a5_idx BEQ true
              (mword_of_int 0x6f2) (4 + n) Ht7ae (eq_sym Et7ae)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_7ae with "Hcode"). }
    iIntros (h18) "Hrun".
    iApply (wp_kcat_vprintf_pcs3 m0 sp0 fd a i apz sa dq c1 slen sf
              m9 h18 n Ha0 ltac:(lia) Hap0 Haphi Hapal Hsanz Hinv9
              with "Hcode Hc1 Hw Hstr Hrun Hcont").
  Qed.

  (* ===================================================================== *)
  (* THE DIRECTIVE'S ROUND, 0x566 -> 0x562, for c0 = 's'.                   *)
  (*                                                                        *)
  (* The state register is '%', so 0x56a and 0x550 both go to 0x576 and the *)
  (* dispatch begins.  It is a chain of tests on three characters -- c0,    *)
  (* c1 = fmt[i+1] and c2 = fmt[i+2] -- and the arms it skips are the       *)
  (* multi-character directives (%ld, %lld, %lu, %llu, %lx, %llx), which is *)
  (* why c1 and c2 are read at all for a directive that uses neither.       *)
  (*                                                                        *)
  (* With c0 fixed at 's' the outcome of every test is decided by one       *)
  (* [vm_compute] on a concrete pair, or -- where a byte is involved -- by  *)
  (* [moi_sub_ne_zero] and the corresponding hypothesis.  a3 and a4 are     *)
  (* left as the opaque expressions the leaves produce: the two branches    *)
  (* that read them (0x770 and 0x796) are reached only when c1 or c2 IS the *)
  (* character just excluded, so no step in this path depends on them.      *)
  (* ===================================================================== *)
  Lemma wp_kcat_vprintf_pcs (m0 : regfile) (sp0 fd : mword 64) (a : Z)
      (i : nat) (apz sa : Z) (dq : dfrac) (c1 c2 : mword 8)
      (slen : nat) (sf : nat -> bv 8) (h : CpuId) (m : regfile) (n : nat) :
    0 <= a -> a + Z.of_nat i + 3 < 2 ^ 31 ->
    0 <= apz -> apz + 8 <= 2 ^ 38 -> apz mod 8 = 0 ->
    sa <> 0 ->
    bv_unsigned c1 <> 0 ->
    bv_unsigned c1 <> 100 -> bv_unsigned c1 <> 117 -> bv_unsigned c1 <> 120 ->
    bv_unsigned c2 <> 100 -> bv_unsigned c2 <> 117 -> bv_unsigned c2 <> 120 ->
    vp_inv3 m0 m sp0 a fd (mword_of_int apz) (mword_of_int 37) i ->
    m !!! Regidx s1_idx = mword_of_int 115 ->
    m !!! Regidx a4_idx = mword_of_int (Z.of_nat i) ->
    cat_code γt -∗
    utext γt (a + Z.of_nat (S i)) c1 -∗
    utext γt (a + Z.of_nat (S (S i))) c2 -∗
    uwordq γd dq apz (mword_of_int sa) -∗
    ustr γd DfracDiscarded sa slen sf -∗
    urun γt γd γs h m (mword_of_int 0x566) (4 + n) -∗
    (∀ (h' : CpuId) (m' : regfile),
       uwordq γd dq apz (mword_of_int sa) -∗
       ⌜ vp_inv m0 m' sp0 a fd (mword_of_int (apz + 8)) (S i) ⌝ -∗
       ⌜ m' !!! Regidx s1_idx = mword_of_int (bv_unsigned c1) ⌝ -∗
       urun γt γd γs h' m' (mword_of_int 0x562) (4 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd Hap0 Haphi Hapal Hsanz
           Hc1z Hc1d Hc1u Hc1x Hc2d Hc2u Hc2x Hinv Hs1 Ha4.
    pose proof Hinv as Hd.
    destruct Hd as (Hsp & Hs0 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hfr).
    iIntros "#Hcode #Hc1 #Hc2 Hw Hstr Hrun Hcont".
    iDestruct (urun_ustr_bnd with "Hrun Hstr") as %[Hsa0 Hsahi].
    (* the byte ranges, and the four negative immediates *)
    assert (Hr1 : 0 <= bv_unsigned c1 < 256).
    { pose proof (bv_unsigned_in_range 8 c1) as H0.
      assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
      rewrite Em8 in H0. exact H0. }
    assert (Hr2 : 0 <= bv_unsigned c2 < 256).
    { pose proof (bv_unsigned_in_range 8 c2) as H0.
      assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
      rewrite Em8 in H0. exact H0. }
    assert (Em100 : (sign_extend' 64 (mword_of_int 3996 : mword 12) : mword 64)
                    = mword_of_int (-100))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em117 : (sign_extend' 64 (mword_of_int 3979 : mword 12) : mword 64)
                    = mword_of_int (-117))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em120 : (sign_extend' 64 (mword_of_int 3976 : mword 12) : mword 64)
                    = mword_of_int (-120))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hai : 0 <= a + Z.of_nat i < Z64) by (unfold Z64; lia).
    (* ---- 0x566  sext.w a5,s1 ---- *)
    assert (Ez0 : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                  = mword_of_int 0)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Ea5c : sign_extend' 64
                     (subrange_vec_dec
                        (add_vec (m !!! Regidx s1_idx)
                           (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0)
                   = (mword_of_int 115 : mword 64)).
    { rewrite Hs1 Ez0.
      rewrite (moi_addw 115 0 ltac:(unfold Z31; lia)). f_equal; lia. }
    iApply (wp_uk_addiw γt γd γs h m (mword_of_int 0x566)
              (mword_of_int 0 : mword 12) s1_idx a5_idx (mword_of_int 115)
              (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ea5c))
              with "[] Hrun").
    { iApply (uis_cat_566 with "Hcode"). }
    assert (E566 : add_vec_int (mword_of_int 0x566 : mword 64) 4
                   = mword_of_int 0x56a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E566.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int 115 : mword 64)]> m).
    assert (Hinv1 : vp_inv3 m0 m1 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m sp0 a fd (mword_of_int apz) (mword_of_int 37) i a5_idx _
                  ltac:(vm_compute; reflexivity) Hinv).
    pose proof Hinv1 as Hd1.
    destruct Hd1 as (Hsp1 & Hs01 & Hs21 & Hs31 & Hs41 & Hs51 & Hs61 & Hs71
                     & Hs81 & Hfr1).
    assert (Ha51 : m1 !!! Regidx a5_idx = mword_of_int 115)
      by exact (upd_eq m (Regidx a5_idx) (regval_into_reg _)).
    assert (Ha41 : m1 !!! Regidx a4_idx = mword_of_int (Z.of_nat i)).
    { rewrite <- Ha4.
      exact (upd_ne m (Regidx a5_idx) (Regidx a4_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x56a  bnez s3,0x550 -- TAKEN: a directive is pending ---- *)
    assert (Ht56a : true = uv_btaken BNE (m1 !!! Regidx s3_idx) zero_reg)
      by (rewrite Hs31; vm_compute; reflexivity).
    assert (Etgt550 : add_vec (mword_of_int 0x56a : mword 64)
                        (sign_extend' 64 (mword_of_int 8166 : mword 13))
                      = mword_of_int 0x550)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_btype0 γt γd γs h1 m1 (mword_of_int 0x56a)
              (mword_of_int 8166 : mword 13) s3_idx BNE true
              (mword_of_int 0x550) (4 + n) Ht56a (eq_sym Etgt550)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_56a with "Hcode"). }
    iIntros (h2) "Hrun".
    (* ---- 0x550  beq s3,s5,0x576 -- TAKEN: the state IS '%' ---- *)
    assert (Ht550 : true
                    = uv_btaken BEQ (m1 !!! Regidx s3_idx) (m1 !!! Regidx s5_idx))
      by (rewrite Hs31 Hs51; vm_compute; reflexivity).
    assert (Etgt576 : add_vec (mword_of_int 0x550 : mword 64)
                        (sign_extend' 64 (mword_of_int 38 : mword 13))
                      = mword_of_int 0x576)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_btype γt γd γs h2 m1 (mword_of_int 0x550)
              (mword_of_int 38 : mword 13) s5_idx s3_idx BEQ true
              (mword_of_int 0x576) (4 + n) Ht550 (eq_sym Etgt576)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_550 with "Hcode"). }
    iIntros (h3) "Hrun".
    (* ---- 0x576  add a3,s4,a4 -- &fmt[i] ---- *)
    assert (Eadd3 : add_vec (m1 !!! Regidx s4_idx) (m1 !!! Regidx a4_idx)
                    = mword_of_int (a + Z.of_nat i))
      by (rewrite Hs41 Ha41 moi_add; reflexivity).
    iApply (wp_uk_add γt γd γs h3 m1 (mword_of_int 0x576) s4_idx a4_idx a3_idx
              (mword_of_int (a + Z.of_nat i)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Eadd3))
              with "[] Hrun").
    { iApply (uis_cat_576 with "Hcode"). }
    assert (E576 : add_vec_int (mword_of_int 0x576 : mword 64) 4
                   = mword_of_int 0x57a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E576.
    iIntros (h4) "Hrun".
    set (m2 := <[Regidx a3_idx
                 := regval_into_reg
                      (mword_of_int (a + Z.of_nat i) : mword 64)]> m1).
    assert (Hinv2 : vp_inv3 m0 m2 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m1 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a3_idx _
                  ltac:(vm_compute; reflexivity) Hinv1).
    assert (Ha32 : m2 !!! Regidx a3_idx = mword_of_int (a + Z.of_nat i))
      by exact (upd_eq m1 (Regidx a3_idx) (regval_into_reg _)).
    assert (Ha52 : m2 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha51.
      exact (upd_ne m1 (Regidx a3_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha42 : m2 !!! Regidx a4_idx = mword_of_int (Z.of_nat i)).
    { rewrite <- Ha41.
      exact (upd_ne m1 (Regidx a3_idx) (Regidx a4_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x57a  lbu a2,1(a3) -- c1 = fmt[i+1] ---- *)
    assert (Haddr1 : (a + Z.of_nat (S i))%Z
                     = uint (m2 !!! Regidx a3_idx)
                       + uoff_i12 (mword_of_int 1 : mword 12)).
    { rewrite Ha32 (uint_moi (a + Z.of_nat i) Hai).
      replace (uoff_i12 (mword_of_int 1 : mword 12)) with 1
        by (vm_compute; reflexivity).
      lia. }
    iApply (wp_uk_lbu_text γt γd γs h4 m2 (mword_of_int 0x57a)
              (mword_of_int 1 : mword 12) a3_idx a2_idx
              (a + Z.of_nat (S i)) c1 (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              Haddr1 ltac:(vm_compute; discriminate)
              with "[] Hc1 Hrun").
    { iApply (uis_cat_57a with "Hcode"). }
    assert (E57a : add_vec_int (mword_of_int 0x57a : mword 64) 4
                   = mword_of_int 0x57e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E57a.
    iIntros (h5) "Hrun".
    set (m3 := <[Regidx a2_idx
                 := regval_into_reg (zero_extend' 64 c1 : mword 64)]> m2).
    assert (Hinv3 : vp_inv3 m0 m3 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m2 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a2_idx _
                  ltac:(vm_compute; reflexivity) Hinv2).
    pose proof Hinv3 as Hd3.
    destruct Hd3 as (Hsp3 & Hs03 & Hs23 & Hs33 & Hs43 & Hs53 & Hs63 & Hs73
                     & Hs83 & Hfr3).
    assert (Ha23 : m3 !!! Regidx a2_idx = mword_of_int (bv_unsigned c1)).
    { rewrite (upd_eq m2 (Regidx a2_idx) (regval_into_reg _)).
      exact (zext8_moi c1). }
    assert (Ha53 : m3 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha52.
      exact (upd_ne m2 (Regidx a2_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha43 : m3 !!! Regidx a4_idx = mword_of_int (Z.of_nat i)).
    { rewrite <- Ha42.
      exact (upd_ne m2 (Regidx a2_idx) (Regidx a4_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x57e  beqz a2,0x74e -- NOT taken: c1 is not the terminator ---- *)
    assert (Hn57e : false = uv_btaken BEQ (m3 !!! Regidx a2_idx) zero_reg).
    { rewrite Ha23. cbn [uv_btaken].
      rewrite (moi_eq_zero (bv_unsigned c1) ltac:(unfold Z64; lia)).
      destruct (Z.eqb_spec (bv_unsigned c1) 0) as [He | _];
        [ exfalso; exact (Hc1z He) | reflexivity ]. }
    iApply (wp_uk_btype0 γt γd γs h5 m3 (mword_of_int 0x57e)
              (mword_of_int 464 : mword 13) a2_idx BEQ false
              (add_vec (mword_of_int 0x57e : mword 64)
                 (sign_extend' 64 (mword_of_int 464 : mword 13)))
              (4 + n) Hn57e eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_cat_57e with "Hcode"). }
    assert (E57e : add_vec_int (mword_of_int 0x57e : mword 64) 4
                   = mword_of_int 0x582)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E57e.
    iIntros (h6) "Hrun".
    (* ---- 0x582  beq a5,s8,0x5b0 -- NOT taken: 's' is not 'd' ---- *)
    assert (Hn582 : false
                    = uv_btaken BEQ (m3 !!! Regidx a5_idx) (m3 !!! Regidx s8_idx))
      by (rewrite Ha53 Hs83; vm_compute; reflexivity).
    iApply (wp_uk_btype γt γd γs h6 m3 (mword_of_int 0x582)
              (mword_of_int 46 : mword 13) s8_idx a5_idx BEQ false
              (add_vec (mword_of_int 0x582 : mword 64)
                 (sign_extend' 64 (mword_of_int 46 : mword 13)))
              (4 + n) Hn582 eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_cat_582 with "Hcode"). }
    assert (E582 : add_vec_int (mword_of_int 0x582 : mword 64) 4
                   = mword_of_int 0x586)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E582.
    iIntros (h7) "Hrun".
    (* ---- 0x586  addi a3,a5,-108 ; 0x58a  seqz a3,a3 -- a3 is dead ---- *)
    iApply (wp_uk_addi γt γd γs h7 m3 (mword_of_int 0x586)
              (mword_of_int 3988 : mword 12) a5_idx a3_idx
              (add_vec (m3 !!! Regidx a5_idx)
                 (sign_extend' 64 (mword_of_int 3988 : mword 12))) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_cat_586 with "Hcode"). }
    assert (E586 : add_vec_int (mword_of_int 0x586 : mword 64) 4
                   = mword_of_int 0x58a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E586.
    iIntros (h8) "Hrun".
    set (m4 := <[Regidx a3_idx
                 := regval_into_reg
                      (add_vec (m3 !!! Regidx a5_idx)
                         (sign_extend' 64
                            (mword_of_int 3988 : mword 12)))]> m3).
    assert (Hinv4 : vp_inv3 m0 m4 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m3 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a3_idx _
                  ltac:(vm_compute; reflexivity) Hinv3).
    iApply (wp_uk_sltiu γt γd γs h8 m4 (mword_of_int 0x58a)
              (mword_of_int 1 : mword 12) a3_idx a3_idx
              (zero_extend' 64
                 (bool_to_bit
                    (zopz0zI_u (m4 !!! Regidx a3_idx)
                       (sign_extend' 64 (mword_of_int 1 : mword 12)))))
              (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_cat_58a with "Hcode"). }
    assert (E58a : add_vec_int (mword_of_int 0x58a : mword 64) 4
                   = mword_of_int 0x58e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E58a.
    iIntros (h9) "Hrun".
    set (m5 := <[Regidx a3_idx
                 := regval_into_reg
                      (zero_extend' 64
                         (bool_to_bit
                            (zopz0zI_u (m4 !!! Regidx a3_idx)
                               (sign_extend' 64
                                  (mword_of_int 1 : mword 12)))))]> m4).
    assert (Hinv5 : vp_inv3 m0 m5 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m4 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a3_idx _
                  ltac:(vm_compute; reflexivity) Hinv4).
    assert (Ha25 : m5 !!! Regidx a2_idx = mword_of_int (bv_unsigned c1)).
    { rewrite <- Ha23.
      rewrite /m5 (upd_ne m4 (Regidx a3_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m4 (upd_ne m3 (Regidx a3_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate)).
      reflexivity. }
    assert (Ha55 : m5 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha53.
      rewrite /m5 (upd_ne m4 (Regidx a3_idx) (Regidx a5_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m4 (upd_ne m3 (Regidx a3_idx) (Regidx a5_idx) _
                     ltac:(vm_compute; discriminate)).
      reflexivity. }
    assert (Ha45 : m5 !!! Regidx a4_idx = mword_of_int (Z.of_nat i)).
    { rewrite <- Ha43.
      rewrite /m5 (upd_ne m4 (Regidx a3_idx) (Regidx a4_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m4 (upd_ne m3 (Regidx a3_idx) (Regidx a4_idx) _
                     ltac:(vm_compute; discriminate)).
      reflexivity. }
    (* ---- 0x58e  addi a1,a2,-100 ---- *)
    assert (Ea1 : add_vec (m5 !!! Regidx a2_idx)
                    (sign_extend' 64 (mword_of_int 3996 : mword 12))
                  = mword_of_int (bv_unsigned c1 - 100))
      by (rewrite Ha25 Em100 moi_add; reflexivity).
    iApply (wp_uk_addi γt γd γs h9 m5 (mword_of_int 0x58e)
              (mword_of_int 3996 : mword 12) a2_idx a1_idx
              (mword_of_int (bv_unsigned c1 - 100)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ea1))
              with "[] Hrun").
    { iApply (uis_cat_58e with "Hcode"). }
    assert (E58e : add_vec_int (mword_of_int 0x58e : mword 64) 4
                   = mword_of_int 0x592)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E58e.
    iIntros (h10) "Hrun".
    set (m6 := <[Regidx a1_idx
                 := regval_into_reg
                      (mword_of_int (bv_unsigned c1 - 100) : mword 64)]> m5).
    assert (Hinv6 : vp_inv3 m0 m6 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m5 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a1_idx _
                  ltac:(vm_compute; reflexivity) Hinv5).
    assert (Ha16 : m6 !!! Regidx a1_idx = mword_of_int (bv_unsigned c1 - 100))
      by exact (upd_eq m5 (Regidx a1_idx) (regval_into_reg _)).
    assert (Ha26 : m6 !!! Regidx a2_idx = mword_of_int (bv_unsigned c1)).
    { rewrite <- Ha25.
      exact (upd_ne m5 (Regidx a1_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha56 : m6 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha55.
      exact (upd_ne m5 (Regidx a1_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha46 : m6 !!! Regidx a4_idx = mword_of_int (Z.of_nat i)).
    { rewrite <- Ha45.
      exact (upd_ne m5 (Regidx a1_idx) (Regidx a4_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x592  c.bnez a1,0x5c8 -- TAKEN: c1 is not 'd' ---- *)
    assert (Ht592 : true = neq_vec (m6 !!! Regidx a1_idx) zero_reg)
      by (rewrite Ha16;
          exact (eq_sym (moi_sub_ne_zero (bv_unsigned c1) 100 Hr1
                           ltac:(lia) Hc1d))).
    assert (Etgt5c8 : add_vec (mword_of_int 0x592 : mword 64)
                        (sign_extend' 64
                           (sign_extend' 13
                              (concat_vec (mword_of_int 27 : mword 8) ('b"0"))))
                      = mword_of_int 0x5c8)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cbnez γt γd γs h10 m6 (mword_of_int 0x592)
              (mword_of_int 27 : mword 8) (mword_of_int 3 : mword 3) a1_idx
              true (mword_of_int 0x5c8) (4 + n)
              ltac:(vm_compute; reflexivity) Ht592 (eq_sym Etgt5c8)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_592 with "Hcode"). }
    iIntros (h11) "Hrun".
    (* ---- 0x5c8  c.add a4,a4,s4 -- &fmt[i] again ---- *)
    assert (Ea4c : add_vec (m6 !!! Regidx a4_idx) (m6 !!! Regidx s4_idx)
                   = mword_of_int (a + Z.of_nat i)).
    { rewrite Ha46.
      rewrite /m6 (upd_ne m5 (Regidx a1_idx) (Regidx s4_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m5 (upd_ne m4 (Regidx a3_idx) (Regidx s4_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m4 (upd_ne m3 (Regidx a3_idx) (Regidx s4_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite Hs43 moi_add. f_equal; lia. }
    iApply (wp_uk_cadd γt γd γs h11 m6 (mword_of_int 0x5c8) a4_idx s4_idx
              (mword_of_int (a + Z.of_nat i)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ea4c))
              with "[] Hrun").
    { iApply (uis_cat_5c8 with "Hcode"). }
    assert (E5c8 : add_vec_int (mword_of_int 0x5c8 : mword 64) 2
                   = mword_of_int 0x5ca)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E5c8.
    iIntros (h12) "Hrun".
    set (m7 := <[Regidx a4_idx
                 := regval_into_reg
                      (mword_of_int (a + Z.of_nat i) : mword 64)]> m6).
    assert (Hinv7 : vp_inv3 m0 m7 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m6 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a4_idx _
                  ltac:(vm_compute; reflexivity) Hinv6).
    assert (Ha47 : m7 !!! Regidx a4_idx = mword_of_int (a + Z.of_nat i))
      by exact (upd_eq m6 (Regidx a4_idx) (regval_into_reg _)).
    assert (Ha27 : m7 !!! Regidx a2_idx = mword_of_int (bv_unsigned c1)).
    { rewrite <- Ha26.
      exact (upd_ne m6 (Regidx a4_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha57 : m7 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha56.
      exact (upd_ne m6 (Regidx a4_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x5ca  lbu a1,2(a4) -- c2 = fmt[i+2] ---- *)
    assert (Haddr2 : (a + Z.of_nat (S (S i)))%Z
                     = uint (m7 !!! Regidx a4_idx)
                       + uoff_i12 (mword_of_int 2 : mword 12)).
    { rewrite Ha47 (uint_moi (a + Z.of_nat i) Hai).
      replace (uoff_i12 (mword_of_int 2 : mword 12)) with 2
        by (vm_compute; reflexivity).
      lia. }
    iApply (wp_uk_lbu_text γt γd γs h12 m7 (mword_of_int 0x5ca)
              (mword_of_int 2 : mword 12) a4_idx a1_idx
              (a + Z.of_nat (S (S i))) c2 (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              Haddr2 ltac:(vm_compute; discriminate)
              with "[] Hc2 Hrun").
    { iApply (uis_cat_5ca with "Hcode"). }
    assert (E5ca : add_vec_int (mword_of_int 0x5ca : mword 64) 4
                   = mword_of_int 0x5ce)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E5ca.
    iIntros (h13) "Hrun".
    set (m8 := <[Regidx a1_idx
                 := regval_into_reg (zero_extend' 64 c2 : mword 64)]> m7).
    assert (Hinv8 : vp_inv3 m0 m8 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m7 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a1_idx _
                  ltac:(vm_compute; reflexivity) Hinv7).
    assert (Ha18 : m8 !!! Regidx a1_idx = mword_of_int (bv_unsigned c2)).
    { rewrite (upd_eq m7 (Regidx a1_idx) (regval_into_reg _)).
      exact (zext8_moi c2). }
    assert (Ha28 : m8 !!! Regidx a2_idx = mword_of_int (bv_unsigned c1)).
    { rewrite <- Ha27.
      exact (upd_ne m7 (Regidx a1_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha58 : m8 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha57.
      exact (upd_ne m7 (Regidx a1_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x5ce  addi a4,a2,-108 ; 0x5d2  seqz a4,a4 ; 0x5d6  and a4,a4,a3
           -- a4 is dead on this path, so its value is left as written ---- *)
    iApply (wp_uk_addi γt γd γs h13 m8 (mword_of_int 0x5ce)
              (mword_of_int 3988 : mword 12) a2_idx a4_idx
              (add_vec (m8 !!! Regidx a2_idx)
                 (sign_extend' 64 (mword_of_int 3988 : mword 12))) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_cat_5ce with "Hcode"). }
    assert (E5ce : add_vec_int (mword_of_int 0x5ce : mword 64) 4
                   = mword_of_int 0x5d2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E5ce.
    iIntros (h14) "Hrun".
    set (m9 := <[Regidx a4_idx
                 := regval_into_reg
                      (add_vec (m8 !!! Regidx a2_idx)
                         (sign_extend' 64
                            (mword_of_int 3988 : mword 12)))]> m8).
    assert (Hinv9 : vp_inv3 m0 m9 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m8 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a4_idx _
                  ltac:(vm_compute; reflexivity) Hinv8).
    iApply (wp_uk_sltiu γt γd γs h14 m9 (mword_of_int 0x5d2)
              (mword_of_int 1 : mword 12) a4_idx a4_idx
              (zero_extend' 64
                 (bool_to_bit
                    (zopz0zI_u (m9 !!! Regidx a4_idx)
                       (sign_extend' 64 (mword_of_int 1 : mword 12)))))
              (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_cat_5d2 with "Hcode"). }
    assert (E5d2 : add_vec_int (mword_of_int 0x5d2 : mword 64) 4
                   = mword_of_int 0x5d6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E5d2.
    iIntros (h15) "Hrun".
    set (m10 := <[Regidx a4_idx
                  := regval_into_reg
                       (zero_extend' 64
                          (bool_to_bit
                             (zopz0zI_u (m9 !!! Regidx a4_idx)
                                (sign_extend' 64
                                   (mword_of_int 1 : mword 12)))))]> m9).
    assert (Hinv10 : vp_inv3 m0 m10 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m9 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a4_idx _
                  ltac:(vm_compute; reflexivity) Hinv9).
    iApply (wp_uk_cand γt γd γs h15 m10 (mword_of_int 0x5d6)
              (mword_of_int 6 : mword 3) (mword_of_int 5 : mword 3)
              a4_idx a3_idx
              (and_vec (m10 !!! Regidx a4_idx) (m10 !!! Regidx a3_idx)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_cat_5d6 with "Hcode"). }
    assert (E5d6 : add_vec_int (mword_of_int 0x5d6 : mword 64) 2
                   = mword_of_int 0x5d8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E5d6.
    iIntros (h16) "Hrun".
    set (m11 := <[Regidx a4_idx
                  := regval_into_reg
                       (and_vec (m10 !!! Regidx a4_idx)
                          (m10 !!! Regidx a3_idx))]> m10).
    assert (Hinv11 : vp_inv3 m0 m11 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m10 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a4_idx _
                  ltac:(vm_compute; reflexivity) Hinv10).
    assert (Hkeep : forall r : mword 5,
               Regidx r <> Regidx a4_idx -> Regidx r <> Regidx a1_idx ->
               m11 !!! Regidx r = m8 !!! Regidx r).
    { intros r Hr4 Hrx.
      rewrite /m11 (upd_ne m10 (Regidx a4_idx) (Regidx r) _
                      Hr4).
      rewrite /m10 (upd_ne m9 (Regidx a4_idx) (Regidx r) _
                      Hr4).
      rewrite /m9 (upd_ne m8 (Regidx a4_idx) (Regidx r) _
                      Hr4).
      reflexivity. }
    assert (Ha1_11 : m11 !!! Regidx a1_idx = mword_of_int (bv_unsigned c2)).
    { rewrite /m11 (upd_ne m10 (Regidx a4_idx) (Regidx a1_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /m10 (upd_ne m9 (Regidx a4_idx) (Regidx a1_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /m9 (upd_ne m8 (Regidx a4_idx) (Regidx a1_idx) _
                      ltac:(vm_compute; discriminate)).
      exact Ha18. }
    assert (Ha2_11 : m11 !!! Regidx a2_idx = mword_of_int (bv_unsigned c1))
      by (rewrite (Hkeep a2_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Ha28).
    assert (Ha5_11 : m11 !!! Regidx a5_idx = mword_of_int 115)
      by (rewrite (Hkeep a5_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Ha58).
    (* ---- 0x5d8  addi a0,a1,-100 ---- *)
    assert (Ea0d : add_vec (m11 !!! Regidx a1_idx)
                     (sign_extend' 64 (mword_of_int 3996 : mword 12))
                   = mword_of_int (bv_unsigned c2 - 100))
      by (rewrite Ha1_11 Em100 moi_add; reflexivity).
    iApply (wp_uk_addi γt γd γs h16 m11 (mword_of_int 0x5d8)
              (mword_of_int 3996 : mword 12) a1_idx a0_idx
              (mword_of_int (bv_unsigned c2 - 100)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ea0d))
              with "[] Hrun").
    { iApply (uis_cat_5d8 with "Hcode"). }
    assert (E5d8 : add_vec_int (mword_of_int 0x5d8 : mword 64) 4
                   = mword_of_int 0x5dc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E5d8.
    iIntros (h17) "Hrun".
    set (m12 := <[Regidx a0_idx
                  := regval_into_reg
                       (mword_of_int (bv_unsigned c2 - 100) : mword 64)]> m11).
    assert (Hinv12 : vp_inv3 m0 m12 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m11 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a0_idx _
                  ltac:(vm_compute; reflexivity) Hinv11).
    assert (Ha0_12 : m12 !!! Regidx a0_idx
                     = mword_of_int (bv_unsigned c2 - 100))
      by exact (upd_eq m11 (Regidx a0_idx) (regval_into_reg _)).
    (* ---- 0x5dc  bnez a0,0x762 -- TAKEN: c2 is not 'd' ---- *)
    assert (Ht5dc : true = uv_btaken BNE (m12 !!! Regidx a0_idx) zero_reg).
    { rewrite Ha0_12. cbn [uv_btaken].
      exact (eq_sym (moi_sub_ne_zero (bv_unsigned c2) 100 Hr2
                       ltac:(lia) Hc2d)). }
    assert (Etgt762 : add_vec (mword_of_int 0x5dc : mword 64)
                        (sign_extend' 64 (mword_of_int 390 : mword 13))
                      = mword_of_int 0x762)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_btype0 γt γd γs h17 m12 (mword_of_int 0x5dc)
              (mword_of_int 390 : mword 13) a0_idx BNE true
              (mword_of_int 0x762) (4 + n) Ht5dc (eq_sym Etgt762)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_5dc with "Hcode"). }
    iIntros (h18) "Hrun".
    iApply (wp_kcat_vprintf_pcs2 m0 sp0 fd a i apz sa dq c1 c2 slen sf
              m12 h18 n Ha0 Habnd Hap0 Haphi Hapal Hsanz Hr1 Hr2
              Hc1u Hc1x Hc2u Hc2x Hinv12
              ltac:(rewrite /m12 (upd_ne m11 (Regidx a0_idx) (Regidx a1_idx) _
                                   ltac:(vm_compute; discriminate)); exact Ha1_11)
              ltac:(rewrite /m12 (upd_ne m11 (Regidx a0_idx) (Regidx a2_idx) _
                                   ltac:(vm_compute; discriminate)); exact Ha2_11)
              ltac:(rewrite /m12 (upd_ne m11 (Regidx a0_idx) (Regidx a5_idx) _
                                   ltac:(vm_compute; discriminate)); exact Ha5_11)
              with "Hcode Hc1 Hw Hstr Hrun Hcont").
  Qed.

  (* ===================================================================== *)
  (* vprintf(fd, fmt, ap) FOR A FORMAT WITH ONE '%s' IN IT.                 *)
  (*                                                                        *)
  (* cat has exactly one such format -- "cat: cannot open %s\n", with the   *)
  (* directive at index 17 of 20 -- and the contract is that one's shape:   *)
  (* a prefix with no '%' at all, the directive, and at least one character *)
  (* after it.  The walk is [pro], then [seg] to the '%', then the two      *)
  (* rounds the directive takes, then [loop] for what is left.              *)
  (* ===================================================================== *)
  Lemma wp_kcat_vprintf_s (a : Z) (len q : nat) (f : nat -> mword 8)
      (apz sa : Z) (dq : dfrac) (slen : nat) (sf : nat -> bv 8)
      (h : CpuId) (m : regfile) (n : nat) :
    0 <= a -> a + Z.of_nat len + 2 < 2 ^ 31 ->
    (S (S q) < len)%nat ->
    bv_unsigned (f q) = 37 ->
    bv_unsigned (f (S q)) = 115 ->
    (forall j : nat, (j < len)%nat -> j <> q -> bv_unsigned (f j) <> 37) ->
    bv_unsigned (f (S (S q))) <> 100 ->
    bv_unsigned (f (S (S q))) <> 117 ->
    bv_unsigned (f (S (S q))) <> 120 ->
    ((S (S (S q)) < len)%nat ->
       bv_unsigned (f (S (S (S q)))) <> 100 /\
       bv_unsigned (f (S (S (S q)))) <> 117 /\
       bv_unsigned (f (S (S (S q)))) <> 120) ->
    apz mod 8 = 0 ->
    sa <> 0 ->
    m !!! Regidx a1_idx = mword_of_int a ->
    m !!! Regidx a2_idx = mword_of_int apz ->
    cat_code γt -∗
    utext_str γt a len f -∗
    uwordq γd dq apz (mword_of_int sa) -∗
    ustr γd DfracDiscarded sa slen sf -∗
    urun γt γd γs h m (mword_of_int CatSyms.vprintf) (12 + (4 + n)) -∗
    (∀ (h' : CpuId) (m' : regfile),
       uwordq γd dq apz (mword_of_int sa) -∗
       ⌜ ucallee_saved m m' ⌝ -∗
       urun γt γd γs h' m' (ret_pc (m !!! Regidx ra_idx)) (12 + (4 + n)) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd Hq2 Hfq Hfsq Hpct Hc1d Hc1u Hc1x Hc2set Hapal Hsanz Ha1 Ha2.
    iIntros "#Hcode #Hstr Hw #Hsstr Hrun Hcont".
    iDestruct (urun_uword_bnd with "Hrun Hw") as %[Hap0 Haphi].
    iDestruct (utext_str_nonul with "Hstr") as %Hnn.
    (* the byte two past the directive: a body byte if there is one, and
       otherwise the terminator, whose value clears every test by itself *)
    iAssert (∃ c2 : mword 8,
               utext γt (a + Z.of_nat (S (S (S q)))) c2
               ∗ ⌜ bv_unsigned c2 <> 100 ⌝ ∗ ⌜ bv_unsigned c2 <> 117 ⌝
               ∗ ⌜ bv_unsigned c2 <> 120 ⌝)%I as "#Hc2".
    { destruct (Nat.lt_ge_cases (S (S (S q))) len) as [Hlt | Hge].
      - iDestruct (utext_str_byte γt a len f (S (S (S q))) Hlt with "Hstr")
          as "#Hb".
        destruct (Hc2set Hlt) as (Hd & Hu & Hx).
        iExists (f (S (S (S q)))). iFrame "Hb". iPureIntro. done.
      - assert (Heq : (S (S (S q)))%nat = len) by lia.
        iDestruct (utext_str_nul with "Hstr") as "#Hnul".
        iExists (ubyte0 : mword 8). rewrite Heq. iFrame "Hnul".
        iPureIntro. repeat split; vm_compute; discriminate. }
    iDestruct "Hc2" as (c2) "(#Hc2b & %Hc2d & %Hc2u & %Hc2x)".
    (* ---- the prologue ---- *)
    iApply (wp_kcat_vprintf_pro γt γd γs a len f h m n Ha0 Habnd ltac:(lia) Ha1
              with "Hcode Hstr Hrun").
    iIntros (h0 mA fd ap) "%Hal8 %Hlo %Hinv0 %Hs1z %Hapeq
                           Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10
                           Hw11 Hw12 Hrun".
    assert (Hapz : ap = mword_of_int apz) by (rewrite Hapeq; exact Ha2).
    rewrite Hapz in Hinv0.
    (* ---- the prefix, up to the '%' ---- *)
    iApply (wp_kcat_vprintf_seg m (m !!! Regidx csp_rs1) fd
              (mword_of_int apz) a len f q Ha0 Habnd 0%nat h0 mA n
              ltac:(lia) ltac:(intros j Hj; apply Hpct; lia) Hinv0 Hs1z
              with "Hcode Hstr Hrun
                    [Hw Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12
                     Hcont]").
    iIntros (h1 mB) "%HinvB %Hs1B Hrun".
    rewrite Nat.add_0_l in HinvB, Hs1B.
    (* ---- the '%' round ---- *)
    iDestruct (utext_str_byte γt a len f (S q) ltac:(lia) with "Hstr")
      as "#Hbsq".
    iApply (wp_kcat_vprintf_pct m (m !!! Regidx csp_rs1) fd
              (mword_of_int apz) a q (f (S q)) h1 mB n Ha0 ltac:(lia) HinvB
              ltac:(rewrite Hs1B Hfq; reflexivity)
              with "Hcode Hbsq Hrun
                    [Hw Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12
                     Hcont]").
    iIntros (h2 mC) "%HinvC %Hs1C %Ha4C Hrun".
    (* ---- 0x562, not taken: 's' is not the terminator ---- *)
    assert (Hnt1 : false = uv_btaken BEQ (mC !!! Regidx s1_idx) zero_reg).
    { rewrite Hs1C Hfsq. cbn [uv_btaken].
      rewrite (moi_eq_zero 115 ltac:(unfold Z64; lia)). reflexivity. }
    iApply (wp_uk_btype0 γt γd γs h2 mC (mword_of_int 0x562)
              (mword_of_int 468 : mword 13) s1_idx BEQ false
              (add_vec (mword_of_int 0x562 : mword 64)
                 (sign_extend' 64 (mword_of_int 468 : mword 13)))
              (4 + n) Hnt1 eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_cat_562 with "Hcode"). }
    assert (E562 : add_vec_int (mword_of_int 0x562 : mword 64) 4
                   = mword_of_int 0x566)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E562.
    iIntros (h3) "Hrun".
    (* ---- the directive's round ---- *)
    iDestruct (utext_str_byte γt a len f (S (S q)) ltac:(lia) with "Hstr")
      as "#Hbssq".
    iApply (wp_kcat_vprintf_pcs m (m !!! Regidx csp_rs1) fd a (S q) apz sa dq
              (f (S (S q))) c2 slen sf h3 mC n Ha0 ltac:(lia) Hap0 Haphi Hapal
              Hsanz
              ltac:(intro He; apply (Hnn (S (S q)) ltac:(lia)); apply bv_eq;
                    rewrite He; vm_compute; reflexivity)
              Hc1d Hc1u Hc1x Hc2d Hc2u Hc2x HinvC
              ltac:(rewrite Hs1C Hfsq; reflexivity) Ha4C
              with "Hcode Hbssq Hc2b Hw Hsstr Hrun
                    [Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12
                     Hcont]").
    iIntros (h4 mD) "Hw %HinvD %Hs1D Hrun".
    (* ---- 0x562, not taken again: there IS a character after the "%s" ---- *)
    assert (Hnzc1 : bv_unsigned (f (S (S q))) <> 0).
    { intro He. apply (Hnn (S (S q)) ltac:(lia)). apply bv_eq.
      rewrite He. vm_compute. reflexivity. }
    assert (Hrc1 : 0 <= bv_unsigned (f (S (S q))) < Z64).
    { assert (HH : 0 <= bv_unsigned (f (S (S q))) < 256).
      { pose proof (bv_unsigned_in_range 8 (f (S (S q)))) as H0.
        assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
        rewrite Em8 in H0. exact H0. }
      unfold Z64. lia. }
    assert (Hnt2 : false = uv_btaken BEQ (mD !!! Regidx s1_idx) zero_reg).
    { rewrite Hs1D. cbn [uv_btaken].
      rewrite (moi_eq_zero (bv_unsigned (f (S (S q)))) Hrc1).
      destruct (Z.eqb_spec (bv_unsigned (f (S (S q)))) 0) as [He | _];
        [ exfalso; exact (Hnzc1 He) | reflexivity ]. }
    iApply (wp_uk_btype0 γt γd γs h4 mD (mword_of_int 0x562)
              (mword_of_int 468 : mword 13) s1_idx BEQ false
              (add_vec (mword_of_int 0x562 : mword 64)
                 (sign_extend' 64 (mword_of_int 468 : mword 13)))
              (4 + n) Hnt2 eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_cat_562 with "Hcode"). }
    rewrite E562.
    iIntros (h5) "Hrun".
    (* ---- and the rest of the string, which has no '%' left in it ---- *)
    iApply (wp_kcat_vprintf_loop γt γd γs m (m !!! Regidx csp_rs1) fd
              (mword_of_int (apz + 8)) a len f (S (S q))
              (len - S (S (S q)))%nat Ha0 Habnd
              ltac:(intros j Hj; apply Hpct; lia) eq_refl Hal8 Hlo
              (S (S q)) h5 mD n ltac:(lia) ltac:(lia) HinvD Hs1D
              with "Hcode Hstr Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10
                    Hw11 Hw12 Hrun [Hw Hcont]").
    iIntros (h6 mE) "%Hcs Hrun".
    iApply ("Hcont" $! h6 mE with "Hw [] Hrun"). iPureIntro. exact Hcs.
  Qed.

End UkCatVprintfS.
