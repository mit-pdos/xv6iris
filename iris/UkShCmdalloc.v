(* ===================================================================== *)
(* UkShCmdalloc.v -- sh's [cmdalloc], the one allocation every cmd        *)
(* constructor makes since upstream d66e41c (sh: panic when out of        *)
(* memory).                                                                *)
(*                                                                        *)
(*   void *cmdalloc(uint n) {                                             *)
(*     void *p = malloc(n);                                               *)
(*     if (p == 0) panic("out of memory");                                *)
(*     memset(p, 0, n);                                                   *)
(*     return p; }                                                        *)
(*                                                                        *)
(* TWENTY-THREE INSTRUCTIONS, 0x1d2..0x206, a FOUR-word frame (ra, s0,     *)
(* s1, s2 spilled, pushed with [c.addi sp,sp,-32] and popped with         *)
(* [c.addi16sp]).  The five constructors used to inline the allocation as *)
(* [malloc] + [memset] and never test the answer, so a NULL walked into    *)
(* memset's first store and the process was KILLED at the fault           *)
(* ([UkSh.wp_ksh_memset_null]).  Now the NULL is TESTED: [c.beqz a0] at    *)
(* 0x1e4 jumps to 0x1fe, which loads the address of the message         *)
(* (0x12c0, [ushp_oom_str]) and calls [panic] -- a death that PRINTS on fd *)
(* 2 and exits.                                                            *)
(*                                                                        *)
(* ONE WALK FOR ALL THE CONSTRUCTORS.  [wp_kshp_cmdalloc] is stated at any *)
(* request [0 < nb <= 168] (the bounded allocator contract's ceiling,     *)
(* [UkShParse.ushp_malloc_ty_le] at [B = 168]) and hands back the zeroed   *)
(* bytes; [execcmd] (168), [redircmd] (40) and [pipecmd] (24) are each a   *)
(* frame and a few field stores around one call to it.                     *)
(*                                                                        *)
(* THE NULL ARM IS AN ABSTRACT CONTINUATION.  What the panic prints and    *)
(* what the child's exit then pays is the CONSOLE's business, not the      *)
(* parser's, so the walk stops at [panic]'s ENTRY with a0 at the message   *)
(* and hands the run to [ushp_oom] -- a persistent law the caller          *)
(* supplies, carrying the same exit resource [Pex] the success arm hands   *)
(* back.  [UkShDiag]'s panic walk is what discharges it (lane SY1-P).      *)
(* The law is MONOTONE in the stack budget ([ushp_oom_mono]), so a walk    *)
(* that reaches [cmdalloc] from several constructors at several depths     *)
(* carries ONE copy at the shallowest.                                     *)
(*                                                                        *)
(* TAINT: [ushp_malloc_ok], and nothing else.                              *)
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
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem.
Require Import UCodeShK UCodeShP.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Local Open Scope Z_scope.
Require Import UserFd.
Require Import UkSh.
Require Import UkShParse.
Require Import UexecSG.
Import Defs.

(* the address of "out of memory", in sh's .rodata *)
Definition ushp_oom_str : Z := 0x12c0.

(* ...pinned by its bytes, so a relayout that moves the string fails HERE *)
Lemma ushp_oom_str_bytes :
  map (fun j : nat => bv_unsigned <$> (shk_ro !! (ushp_oom_str + Z.of_nat j)%Z))
      (seq 0 14)
  = Some <$> [111; 117; 116; 32; 111; 102; 32; 109; 101; 109; 111; 114; 121; 0].
Proof. vm_compute. reflexivity. Qed.

Section UkShCmdalloc.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  Context `{Hpay : !ukn_const N}.
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).

  (* ===================================================================== *)
  (* THE OUT-OF-MEMORY LAW.  What the caller promises to do with a run at   *)
  (* [panic]'s entry whose a0 is the message, given the exit resource       *)
  (* [Pex] it lent the walk -- at ANY budget from [K] up, which is what     *)
  (* lets one copy serve every call depth ([ushp_oom_mono]).                *)
  (* ===================================================================== *)
  Definition ushp_oom (Pex : iProp Σ) (K : nat) : iProp Σ :=
    □ (∀ (h : CpuId) (m : regfile) (k : nat),
         ⌜ (K <= k)%nat ⌝ -∗
         ⌜ uint (m !!! Regidx a0_idx) = ushp_oom_str ⌝ -∗
         Pex -∗
         urun N h m (mword_of_int ShSyms.panic) k -∗
         mWP (Loop : expr riscv_lang)).

  Global Instance ushp_oom_persistent Pex K : Persistent (ushp_oom Pex K).
  Proof using . rewrite /ushp_oom. apply _. Qed.

  Lemma ushp_oom_mono (Pex : iProp Σ) (K K' : nat) :
    (K <= K')%nat -> ushp_oom Pex K -∗ ushp_oom Pex K'.
  Proof using .
    intros HK. rewrite /ushp_oom. iIntros "#H !>" (h m k Hk).
    iApply "H". iPureIntro. lia.
  Qed.

  (* ...and CONTRAVARIANT in the lend: a law at [Pex] serves a walk that
     crosses the parse holding more (the child's ledger beside its lend) *)
  Lemma ushp_oom_wand (Pex Pex' : iProp Σ) (K : nat) :
    □ (Pex' -∗ Pex) -∗ ushp_oom Pex K -∗ ushp_oom Pex' K.
  Proof using .
    rewrite /ushp_oom. iIntros "#Hw #H !>" (h m k) "%Hk %Ha0 Hp Hrun".
    iApply ("H" $! h m k with "[%] [%] [Hp] Hrun");
      [ exact Hk | exact Ha0 | iApply ("Hw" with "Hp") ].
  Qed.

  Local Notation ushp_malloc_ty := (UkShParse.ushp_malloc_ty_le N 168).
  Local Notation wp_kshp_frame_pro_ci := (UkShParse.wp_kshp_frame_pro_ci N).
  Local Notation wp_kshp_frame_epi := (UkShParse.wp_kshp_frame_epi N).

  (* the allocator's contract, at the parser's bound (lane SH-MALLOC-3) *)
  Context (UMalloc UMalloc' : iProp Σ).
  Hypothesis ushp_malloc_ok : ushp_malloc_ty UMalloc UMalloc'.

  Lemma shpc_malloc : ShSyms.malloc = 0x1170.
  Proof using . unfold ShSyms.malloc. reflexivity. Qed.
  Lemma shpc_memset : ShSyms.memset = 0xa38.
  Proof using . unfold ShSyms.memset. reflexivity. Qed.
  Lemma shpc_panic : ShSyms.panic = 0x4a.
  Proof using . unfold ShSyms.panic. reflexivity. Qed.

  (* ===================================================================== *)
  (* THE WALK.  The budget is the call chain: four words of cmdalloc's own  *)
  (* frame on top of malloc's ten (its 64-byte frame plus [free]/[sbrk]'s   *)
  (* two); memset's two fit inside those ten, and [panic] is entered with   *)
  (* the ten still in hand.                                                 *)
  (* ===================================================================== *)
  Lemma wp_kshp_cmdalloc {Pex : iProp Σ} (h : CpuId) (m : regfile) (nb : Z)
      (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int nb ->
    0 < nb -> nb <= 168 ->
    shp_code γt -∗
    UMalloc -∗
    ushp_oom Pex (10 + nn) -∗
    Pex -∗
    urun N h m (mword_of_int ShSyms.cmdalloc) (4 + (10 + nn)) -∗
    (∀ (h' : CpuId) (m' : regfile) (p : Z),
       ⌜ ucallee_saved m m' ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
       ⌜ 0 < p /\ p mod 16 = 0 /\ p + nb < 2 ^ 38 ⌝ -∗
       ubytes γd p (Z.to_nat nb) (fun _ => ubyte0) -∗
       UMalloc' -∗
       Pex -∗
       urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (4 + (10 + nn)) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using ushp_malloc_ok.
    intros Ha0 Hnb0 Hnb.
    iIntros "#Hcode HM #Hoom Hpay Hrun Hcont".
    iDestruct (ushp_code_shk γt with "Hcode") as "#Hkcode".
    rewrite UkShParse.shpp_cmdalloc.
    set (rs := [(ra_idx, mword_of_int 3 : mword 6);
                (s0_idx, mword_of_int 2 : mword 6);
                (s1_idx, mword_of_int 1 : mword 6);
                (s2_idx, mword_of_int 0 : mword 6)]).
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | 1%nat => m !!! Regidx s0_idx
                   | 2%nat => m !!! Regidx s1_idx
                   | _ => m !!! Regidx s2_idx end).
    (* ---- 0x1d2..0x1dc  the prologue: k = 4, four spills, no pad ---- *)
    iApply (wp_kshp_frame_pro_ci 4 0 rs 0x1d2
              (fun i : nat => match i with
                              | 0%nat => 0x1d4 | 1%nat => 0x1d6
                              | 2%nat => 0x1d8 | 3%nat => 0x1da | _ => 0x1dc end)
              (mword_of_int 32 : mword 6) (mword_of_int 8 : mword 8)
              vals (10 + nn) h m
              ltac:(cbn [length]; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(cbn; lia)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| i ]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| i ]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ vm_compute; discriminate | reflexivity ] ]))
              with "[] [] [] Hrun").
    { iApply (uis_shp_1d2 with "Hcode"). }
    { unfold rs. rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_1d4 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_1d6 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_1d8 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_1da with "Hcode") | done ]. }
    { iApply (uis_shp_1dc with "Hcode"). }
    iIntros (h1 v) "%Hal8 %Hlo %Hhi Hsl Hloc Hrun". cbn [length].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 4))).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    set (m2 := <[Regidx s0_idx := regval_into_reg v]> m1).
    assert (Hm1 : forall r : mword 5, Regidx r <> Regidx csp_rs1 ->
                    m1 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr; exact (upd_ne m (Regidx csp_rs1) (Regidx r) _ Hr)).
    assert (Hm2 : forall r : mword 5, Regidx r <> Regidx s0_idx ->
                    m2 !!! Regidx r = m1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m1 (Regidx s0_idx) (Regidx r) _ Hr)).
    assert (Hsp2 : m2 !!! Regidx csp_rs1 = spn).
    { rewrite (Hm2 csp_rs1 ltac:(vm_compute; discriminate)).
      exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)). }
    (* ---- 0x1de  c.mv s2,a0  --  n ---- *)
    iApply (wp_uk_cmv N h1 m2 (mword_of_int 0x1de) s2_idx a0_idx
              (mword_of_int nb) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val nb))
              with "[] Hrun").
    { iApply (uis_shp_1de with "Hcode"). }
    rewrite (ushp_pc_step 0x1de 2). iIntros (h2) "Hrun".
    set (m3 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int nb : mword 64)]> m2).
    assert (Hm3 : forall r : mword 5, Regidx r <> Regidx s2_idx ->
                    m3 !!! Regidx r = m2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m2 (Regidx s2_idx) (Regidx r) _ Hr)).
    (* ---- 0x1e0  jal 1170 <malloc> ---- *)
    iApply (wp_uk_jal N h2 m3 (mword_of_int 0x1e0)
              (mword_of_int 3984 : mword 21) ra_idx
              (mword_of_int 0x1170) (mword_of_int 0x1e4) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_1e0 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x1e4 : mword 64)]> m3).
    assert (Hm4 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                    m4 !!! Regidx r = m3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m3 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Ha0_4 : m4 !!! Regidx a0_idx = mword_of_int nb).
    { rewrite (Hm4 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm3 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    assert (Eret1 : ret_pc (m4 !!! Regidx ra_idx) = mword_of_int 0x1e4).
    { rewrite (upd_eq m3 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x1e4 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    rewrite <- shpc_malloc.
    (* ---- malloc(n) -- THE HYPOTHESIS, and this lemma's only taint ---- *)
    iApply (ushp_malloc_ok h3 m4 nb nn Ha0_4 Hnb0 Hnb with "Hcode HM Hrun").
    iIntros (h4 m5) "%Hcs45 Hans Hrun".
    rewrite Eret1.
    iDestruct "Hans" as
      "[%Ha0_5 | (%p & %g & %Ha0_5 & %Hpb & Hbs & HM')]".
    { (* ===================================================================
         THE NULL ARM: [malloc] returned 0, the test at 0x1e4 is TAKEN, and
         the three instructions at 0x1fe load "out of memory" and call
         [panic].  The run at panic's entry goes to the caller's law.
         =================================================================== *)
      (* ---- 0x1e4  c.beqz a0,0x1fe -- TAKEN ---- *)
      iApply (wp_uk_cbeqz N h4 m5 (mword_of_int 0x1e4)
                (mword_of_int 13 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                true (mword_of_int 0x1fe) (10 + nn)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0_5; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_1e4 with "Hcode"). }
      cbn iota. iIntros (h5) "Hrun".
      (* ---- 0x1fe  auipc a0,0x1 ---- *)
      iApply (wp_uk_auipc N h5 m5 (mword_of_int 0x1fe)
                (mword_of_int 1 : mword 20) a0_idx
                (mword_of_int 0x11fe) (10 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_1fe with "Hcode"). }
      rewrite (ushp_pc_step 0x1fe 4). iIntros (h6) "Hrun".
      set (n1 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int 0x11fe : mword 64)]> m5).
      assert (Ha0_n1 : n1 !!! Regidx a0_idx = (mword_of_int 0x11fe : mword 64))
        by exact (upd_eq m5 (Regidx a0_idx) _).
      (* ---- 0x202  addi a0,a0,194  --  a0 = 0x12c0, "out of memory" ---- *)
      iApply (wp_uk_addi N h6 n1 (mword_of_int 0x202)
                (mword_of_int 194 : mword 12) a0_idx a0_idx
                (mword_of_int ushp_oom_str) (10 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha0_n1;
                      assert (Es : (sign_extend' 64
                                      (mword_of_int 194 : mword 12) : mword 64)
                                   = mword_of_int 194)
                        by (apply bv_eq; vm_compute; reflexivity);
                      rewrite Es moi_add; unfold ushp_oom_str; f_equal; lia)
                with "[] Hrun").
      { iApply (uis_shp_202 with "Hcode"). }
      rewrite (ushp_pc_step 0x202 4). iIntros (h7) "Hrun".
      set (n2 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int ushp_oom_str : mword 64)]> n1).
      (* ---- 0x206  jal 4a <panic> ---- *)
      iApply (wp_uk_jal N h7 n2 (mword_of_int 0x206)
                (mword_of_int 2096708 : mword 21) ra_idx
                (mword_of_int 0x4a) (mword_of_int 0x20a) (10 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_206 with "Hcode"). }
      iIntros (h8) "Hrun".
      set (n3 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x20a : mword 64)]> n2).
      assert (Hmsg : uint (n3 !!! Regidx a0_idx) = ushp_oom_str).
      { rewrite /n3 (upd_ne n2 (Regidx ra_idx) (Regidx a0_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /n2 (upd_eq n1 (Regidx a0_idx) _).
        apply uint_moi. unfold ushp_oom_str, Z64. lia. }
      rewrite <- shpc_panic.
      iApply ("Hoom" $! h8 n3 (10 + nn)%nat with "[%] [%] Hpay Hrun");
        [ lia | exact Hmsg ]. }
    destruct Hpb as [ Hp0 [ Hp16 Hpsz ] ].
    assert (H38 : (2:Z) ^ 38 = 274877906944) by (vm_compute; reflexivity).
    assert (Hp64 : 0 <= p < Z64)
      by (rewrite H38 in Hpsz; unfold Z64; lia).
    (* ---- 0x1e4  c.beqz a0,0x1fe -- NOT taken: the block is real ---- *)
    iApply (wp_uk_cbeqz N h4 m5 (mword_of_int 0x1e4)
              (mword_of_int 13 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              false (mword_of_int 0x1fe) (10 + nn)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_5 (moi_eq_zero p Hp64);
                    symmetry; apply Z.eqb_neq; lia)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_1e4 with "Hcode"). }
    cbn iota. rewrite (ushp_pc_step 0x1e4 2). iIntros (h5) "Hrun".
    (* ---- 0x1e6  c.mv s1,a0  --  p ---- *)
    iApply (wp_uk_cmv N h5 m5 (mword_of_int 0x1e6) s1_idx a0_idx
              (mword_of_int p) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_5; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_1e6 with "Hcode"). }
    rewrite (ushp_pc_step 0x1e6 2). iIntros (h6) "Hrun".
    set (m6 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> m5).
    assert (Hm6 : forall r : mword 5, Regidx r <> Regidx s1_idx ->
                    m6 !!! Regidx r = m5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m5 (Regidx s1_idx) (Regidx r) _ Hr)).
    assert (Hs1_6 : m6 !!! Regidx s1_idx = mword_of_int p)
      by exact (upd_eq m5 (Regidx s1_idx)
                  (regval_into_reg (mword_of_int p : mword 64))).
    (* s2 survived malloc: it is callee-saved *)
    assert (Hs2_5 : m5 !!! Regidx s2_idx = mword_of_int nb).
    { rewrite (Hcs45 s2_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hm4 s2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s2_idx)
               (regval_into_reg (mword_of_int nb : mword 64))). }
    (* ---- 0x1e8  c.mv a2,s2  --  n ---- *)
    iApply (wp_uk_cmv N h6 m6 (mword_of_int 0x1e8) a2_idx s2_idx
              (mword_of_int nb) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm6 s2_idx ltac:(vm_compute; discriminate)) Hs2_5;
                    symmetry; exact (ushp_mv_val nb))
              with "[] Hrun").
    { iApply (uis_shp_1e8 with "Hcode"). }
    rewrite (ushp_pc_step 0x1e8 2). iIntros (h7) "Hrun".
    set (m7 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int nb : mword 64)]> m6).
    assert (Hm7 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
                    m7 !!! Regidx r = m6 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m6 (Regidx a2_idx) (Regidx r) _ Hr)).
    (* ---- 0x1ea  c.li a1,0 ---- *)
    iApply (wp_uk_cli N h7 m7 (mword_of_int 0x1ea)
              (mword_of_int 0 : mword 6) a1_idx (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_1ea with "Hcode"). }
    rewrite (ushp_pc_step 0x1ea 2). iIntros (h8) "Hrun".
    set (m8 := <[Regidx a1_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 0 : mword 6)
                       : mword 64)]> m7).
    assert (Hm8 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                    m8 !!! Regidx r = m7 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m7 (Regidx a1_idx) (Regidx r) _ Hr)).
    (* ---- 0x1ec  jal a38 <memset> ---- *)
    iApply (wp_uk_jal N h8 m8 (mword_of_int 0x1ec)
              (mword_of_int 2124 : mword 21) ra_idx
              (mword_of_int 0xa38) (mword_of_int 0x1f0) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_1ec with "Hcode"). }
    iIntros (h9) "Hrun".
    set (m9 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x1f0 : mword 64)]> m8).
    assert (Hm9 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                    m9 !!! Regidx r = m8 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m8 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Ha1_9 : m9 !!! Regidx a1_idx = (mword_of_int 0 : mword 64)).
    { rewrite (Hm9 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m7 (Regidx a1_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_9 : m9 !!! Regidx a0_idx = mword_of_int p).
    { rewrite (Hm9 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_5. }
    assert (Ha2_9 : m9 !!! Regidx a2_idx
                    = mword_of_int (Z.of_nat (Z.to_nat nb))).
    { rewrite (Hm9 a2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 a2_idx ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m6 (Regidx a2_idx)
                 (regval_into_reg (mword_of_int nb : mword 64))).
      rewrite Z2Nat.id; [ reflexivity | lia ]. }
    assert (Eret2 : ret_pc (m9 !!! Regidx ra_idx) = mword_of_int 0x1f0).
    { rewrite (upd_eq m8 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x1f0 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    rewrite <- shpc_memset.
    (* ---- memset(p, 0, n) -- UkSh.v's, across the code bridge ---- *)
    iApply (wp_ksh_memset N h9 m9 p (Z.to_nat nb) g (8 + nn)
              Ha0_9 Ha2_9 ltac:(lia) ltac:(unfold Z31; lia)
              with "Hkcode Hbs Hrun").
    iIntros "Hbs" (h10 m10) "%Hcs910 Hrun".
    rewrite Eret2 Ha1_9.
    assert (Eb0 : nth_byte (mword_of_int 0 : mword 64) 0%nat = ubyte0)
      by (vm_compute; reflexivity).
    rewrite Eb0.
    assert (Hs1_10 : m10 !!! Regidx s1_idx = mword_of_int p).
    { rewrite (Hcs910 s1_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hm9 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_6. }
    (* ---- 0x1f0  c.mv a0,s1  --  return p ---- *)
    iApply (wp_uk_cmv N h10 m10 (mword_of_int 0x1f0) a0_idx s1_idx
              (mword_of_int p) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_10; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_1f0 with "Hcode"). }
    rewrite (ushp_pc_step 0x1f0 2). iIntros (h11) "Hrun".
    set (me := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> m10).
    assert (Hme : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    me !!! Regidx r = m10 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m10 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (Hspe : me !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite (Hme csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hcs910 csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite (Hm9 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm8 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm7 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm6 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hcs45 csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite (Hm4 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm3 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp2. }
    (* ---- 0x1f2..0x1fc  the epilogue ---- *)
    iApply (wp_kshp_frame_epi 4 0 rs (mword_of_int 3 : mword 6)
              (fun i : nat => match i with
                              | 0%nat => 0x1f2 | 1%nat => 0x1f4
                              | 2%nat => 0x1f6 | 3%nat => 0x1f8 | _ => 0x1fa end)
              (mword_of_int 2 : mword 6) sp0
              (mword_of_int (uint sp0 - 8 * Z.of_nat 4)) vals
              (10 + nn) h11 me
              ltac:(cbn [length]; reflexivity)
              Hal8 ltac:(cbn; lia) Hhi
              ltac:(apply uint_moi; cbn; lia)
              Hspe
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| i ]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| i ]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ unfold unot_sp; vm_compute; discriminate
                              | vm_compute; discriminate ] ]))
              ltac:(reflexivity)
              ltac:(ushp_ne_vm)
              with "Hcode [] [] [] Hsl Hloc Hrun").
    { unfold rs. rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_1f2 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_1f4 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_1f6 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_1f8 with "Hcode") | done ]. }
    { iApply (uis_shp_1fa with "Hcode"). }
    { iApply (uis_shp_1fc with "Hcode"). }
    iIntros (hf) "Hrun".
    iApply ("Hcont" $! hf _ p with "[] [] [] Hbs HM' Hpay Hrun").
    - iPureIntro.
      apply (ushp_frame_cs rs vals m me sp0 eq_refl).
      + intros i r u Hi.
        destruct i as [| [| [| [| i ]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; reflexivity.
      + intros r Hr Hrsp Hmiss.
        rewrite (Hme r (ushp_cs_ne r a0_idx Hr
                          ltac:(vm_compute; reflexivity))).
        rewrite (Hcs910 r Hr).
        rewrite (Hm9 r (Hmiss 0%nat ra_idx (mword_of_int 3 : mword 6)
                          eq_refl)).
        rewrite (Hm8 r (ushp_cs_ne r a1_idx Hr
                          ltac:(vm_compute; reflexivity))).
        rewrite (Hm7 r (ushp_cs_ne r a2_idx Hr
                          ltac:(vm_compute; reflexivity))).
        rewrite (Hm6 r (Hmiss 2%nat s1_idx (mword_of_int 1 : mword 6)
                          eq_refl)).
        rewrite (Hcs45 r Hr).
        rewrite (Hm4 r (Hmiss 0%nat ra_idx (mword_of_int 3 : mword 6)
                          eq_refl)).
        rewrite (Hm3 r (Hmiss 3%nat s2_idx (mword_of_int 0 : mword 6)
                          eq_refl)).
        rewrite (Hm2 r (Hmiss 1%nat s0_idx (mword_of_int 2 : mword 6)
                          eq_refl)).
        exact (Hm1 r Hrsp).
    - iPureIntro.
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      apply ushp_spillback_eq.
      + intros _.
        exact (upd_eq m10 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int p : mword 64))).
      + intros i r u Hi He.
        destruct i as [| [| [| [| i ]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
    - iPureIntro. exact (conj Hp0 (conj Hp16 Hpsz)).
  Qed.

End UkShCmdalloc.
