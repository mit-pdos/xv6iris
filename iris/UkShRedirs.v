(* ===================================================================== *)
(* UkShRedirs.v -- parseredirs AT THE REFERENCE PARSER, ONCE                *)
(* (design/user-once.md SS2, worklist A2b).                                *)
(*                                                                        *)
(*   struct cmd *parseredirs(struct cmd *cmd, char **ps, char *es) {      *)
(*     int tok; char *q, *eq;                                            *)
(*     while(peek(ps, es, <>)) {                                         *)
(*       tok = gettoken(ps, es, 0, 0);                                    *)
(*       if(gettoken(ps, es, &q, &eq) != a) panic(missing file ...);      *)
(*       switch(tok) {                                                    *)
(*       case '>': cmd = redircmd(cmd, q, eq, O_WRONLY|O_CREATE|O_TRUNC,  *)
(*                                1); break;                              *)
(*       ... } }                                                          *)
(*     return cmd;  }                                                     *)
(*                                                                        *)
(* sh's [parseredirs] used to be walked FOUR times: at zero turns under   *)
(* [ushp_no_symbols] (UkShParseRedir.wp_kshp_parseredirs), at zero turns  *)
(* with the byte at the cursor no symbol (UkShRedirPr.wp_kshp_parseredirs *)
(* _ns), at zero turns at the weakest premise -- peek's table does not    *)
(* contain the byte (UkShPipePr.wp_kshp_parseredirs_miss) -- and at ONE   *)
(* turn on the canonical redirect line (UkShRedirPr.wp_kshp_parseredirs_  *)
(* gtn, 1,600 lines).  This file is that walk once, stated at the         *)
(* reference parser [RefParse.ref_redirs]: the loop turns as many times   *)
(* as the reference consumes redirects, and the landed statements are     *)
(* corollaries (the general miss is SS6 here; _ns and _gtn are recovered   *)
(* in UkShRedirPr, the pipe tier's miss in UkShPipePr).                   *)
(*                                                                        *)
(* (0) [ushp_malloc_chain k UM UM']: [k] calls of malloc threaded, the    *)
(*     allocator credential a walk over a tree spends.  Here for now; it  *)
(*     moves to UkShParse beside [ushp_malloc_ty_le] when that file is    *)
(*     next edited.                                                       *)
(* (1) [ushp_redirs_at s0 t cmd rs]: the chain of REDIR nodes the turns   *)
(*     build around [cmd], outermost [t]; the first redirect consumed is  *)
(*     the innermost node, as [RefParse.ref_wrap] folds, and              *)
(*     [ushp_redirs_close] turns the chain into [ushp_tree] at the        *)
(*     wrapped tree.  [ushp_redirs_res rs]: what the turns spend and hand *)
(*     back -- nothing at zero turns; the symbol table and the exit       *)
(*     payment otherwise.                                                 *)
(* (2) the frame prologue at its frame pointer's VALUE (was UkShRedirPr's *)
(*     [wp_kshp_frame_pro_at]; this walk addresses its two locals through *)
(*     s0).                                                               *)
(* (3) the loop head: 0x502 to the peek's return, at [RefParse.ref_peek]. *)
(* (4) ONE TURN of the body: 0x512 (the guard was true) to the jump back  *)
(*     to 0x502 -- the '>' gettoken, the file-name gettoken, the switch,  *)
(*     [redircmd], the node store -- with the two gettoken answers taken   *)
(*     as the reference's equations (UkShGettoken.wp_ref_gettoken).       *)
(* (5) THE LOOP, by induction on the redirects the reference consumes:    *)
(*     the miss case is the head and the exit, the turn case is the head, *)
(*     the body and the induction hypothesis.                             *)
(* (6) [wp_ref_parseredirs], the whole function: the prologue, the loop,  *)
(*     the epilogue.  The premises a turn needs -- the symbol scope, the   *)
(*     eight extra words of stack for redircmd's malloc -- are guarded by  *)
(*     [rs <> []], and the resources a turn spends are [ushp_redirs_res    *)
(*     rs], so the zero-turn statements come back EXACTLY; [wp_ref_        *)
(*     parseredirs_full] is the same walk with everything unconditional,  *)
(*     the shape the argument loop (A2c) consumes.                        *)
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
Require Import UCodeShP.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Local Open Scope Z_scope.
Import Defs.
Require Import UserFd.
Require Import UkShParse.
Require Import UkShParseSym.
Require Import UkShParseLex.
Require Import UkShParseTok.
Require Import RefParse.
Require Import RefParseSym.
Require Import UkShGettoken.
Require Import UkShRedirCmd.

Require Import UexecSG.

Section UkShRedirs.
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

  Local Notation x0_idx := (mword_of_int 0 : mword 5).
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
  Local Notation s9_idx := (mword_of_int 25 : mword 5).
  Local Notation s10_idx := (mword_of_int 26 : mword 5).
  Local Notation s11_idx := (mword_of_int 27 : mword 5).

  (* ---- what the earlier files define, at this file's ghost names ---- *)
  Local Notation ushp_cell := (UkShParseTok.ushp_cell N).
  Local Notation ushp_frame_join := (UkShParse.ushp_frame_join N).
  Local Notation ushp_frame_split := (UkShParse.ushp_frame_split N).
  Local Notation ushp_lit_str := (UkShParseLex.ushp_lit_str N).
  Local Notation ushp_malloc_ty := (UkShParse.ushp_malloc_ty_le N 168).
  Local Notation ushp_tree := (UkShParse.ushp_tree N).
  Local Notation wp_kshp_frame_epi := (UkShParse.wp_kshp_frame_epi N).
  Local Notation wp_kshp_spill := (UkShParse.wp_kshp_spill N).
  Local Notation wp_ref_gettoken := (UkShGettoken.wp_ref_gettoken N).
  Local Notation wp_ref_peek := (UkShGettoken.wp_ref_peek N).
  Local Notation ushp_redir_node := (UkShRedirCmd.ushp_redir_node N).
  Local Notation ushp_redir_close := (UkShRedirCmd.ushp_redir_close N).


  (* ===================================================================== *)
  (* (0) THE ALLOCATOR CHAIN                                                *)
  (* ===================================================================== *)

  (* [k] calls of malloc at the bounded contract, threaded: the first spends
     [UM], the last leaves [UM'].  Zero calls is the identity. *)
  Fixpoint ushp_malloc_chain (k : nat) (UM UM' : iProp Σ) : Prop :=
    match k with
    | O => UM = UM'
    | S k' => exists UM1 : iProp Σ,
                ushp_malloc_ty UM UM1 /\ ushp_malloc_chain k' UM1 UM'
    end.

  Lemma ushp_malloc_chain_1 (UM UM' : iProp Σ) :
    ushp_malloc_ty UM UM' -> ushp_malloc_chain 1 UM UM'.
  Proof using . intro H. exists UM'. split; [ exact H | reflexivity ]. Qed.

  Lemma ushp_malloc_chain_app (k k' : nat) (UM UM1 UM' : iProp Σ) :
    ushp_malloc_chain k UM UM1 -> ushp_malloc_chain k' UM1 UM' ->
    ushp_malloc_chain (k + k') UM UM'.
  Proof using .
    revert UM. induction k as [| k IH ]; intros UM H1 H2.
    - cbn [ushp_malloc_chain] in H1. subst UM1. exact H2.
    - destruct H1 as (UM2 & Hty & Hrest).
      exists UM2. split; [ exact Hty | exact (IH UM2 Hrest H2) ].
  Qed.

  Lemma ushp_malloc_chain_split (k k' : nat) (UM UM' : iProp Σ) :
    ushp_malloc_chain (k + k') UM UM' ->
    exists UM1 : iProp Σ, ushp_malloc_chain k UM UM1 /\ ushp_malloc_chain k' UM1 UM'.
  Proof using .
    revert UM. induction k as [| k IH ]; intros UM H.
    - exists UM. split; [ reflexivity | exact H ].
    - destruct H as (UM2 & Hty & Hrest).
      destruct (IH UM2 Hrest) as (UM1 & H1 & H2).
      exists UM1. split; [ exists UM2; split; [ exact Hty | exact H1 ] | exact H2 ].
  Qed.


  (* ===================================================================== *)
  (* (1) THE NODE CHAIN, AND WHAT THE TURNS SPEND                           *)
  (* ===================================================================== *)

  (* the REDIR nodes the turns build around [cmd], outermost [t]: the first
     redirect consumed is the innermost node -- [redircmd] wraps the tree
     built so far -- and the rest of the chain wraps it *)
  Fixpoint ushp_redirs_at (s0 t cmd : Z) (rs : list rredir) : iProp Σ :=
    match rs with
    | [] => ⌜ t = cmd ⌝%I
    | r :: rs' =>
        (∃ p1 : Z,
           ushp_redir_node s0 p1 cmd (rr_q r) (rr_eq r) (rr_mode r) (rr_fd r)
           ∗ ushp_redirs_at s0 t p1 rs')%I
    end.

  (* ...read from the other end: the LAST redirect consumed is the
     outermost node *)
  Lemma ushp_redirs_at_snoc (s0 t cmd : Z) (rs : list rredir) (r : rredir) :
    ushp_redirs_at s0 t cmd (rs ++ [r])
    ⊣⊢ ∃ pc : Z, ushp_redir_node s0 t pc (rr_q r) (rr_eq r) (rr_mode r) (rr_fd r)
                 ∗ ushp_redirs_at s0 pc cmd rs.
  Proof using .
    revert cmd. induction rs as [| r0 rs IH ]; intro cmd; cbn [app ushp_redirs_at].
    - iSplit.
      + iIntros "(%p1 & Hn & %E)". subst t. iExists cmd. iFrame "Hn". done.
      + iIntros "(%pc & Hn & %E)". subst pc. iExists t. iFrame "Hn". done.
    - setoid_rewrite IH. iSplit.
      + iIntros "(%p1 & Hn0 & %pc & Hn & Hrest)".
        iExists pc. iFrame "Hn". iExists p1. iFrame "Hn0 Hrest".
      + iIntros "(%pc & Hn & %p1 & Hn0 & Hrest)".
        iExists p1. iFrame "Hn0". iExists pc. iFrame "Hn Hrest".
  Qed.

  (* the chain closes into the published tree at the wrapped command *)
  Lemma ushp_redirs_close (s0 t cmd : Z) (rs : list rredir) (c : ushp_cmd) :
    ushp_redirs_at s0 t cmd rs -∗ ushp_tree s0 cmd c -∗
    ushp_tree s0 t (ref_wrap c rs).
  Proof using .
    revert cmd c. induction rs as [| r rs IH ]; intros cmd c;
      cbn [ushp_redirs_at ref_wrap fold_left].
    - iIntros "%E Hc". subst t. iExact "Hc".
    - iIntros "(%p1 & Hn & Hrest) Hc".
      iDestruct (ushp_redir_close with "Hn Hc") as "Hc".
      iApply (IH with "Hrest Hc").
  Qed.

  (* what the turns spend and hand back: nothing at zero turns; the symbol
     table (gettoken's) and the exit payment with its door (redircmd's
     malloc may fail) otherwise *)
  Definition ushp_redirs_res (rs : list rredir) (dv : dfrac) (Pex : iProp Σ)
      : iProp Σ :=
    match rs with
    | [] => emp%I
    | _ :: _ => (ustr γd dv ushp_symbols 7 ushp_sym_f ∗ Pex
                 ∗ □ (Pex -∗ ukn_pay N (-1)))%I
    end.

  (* a caller holding the table and the payment lends them at any [rs] *)
  Lemma ushp_redirs_res_of (rs : list rredir) (dv : dfrac) (Pex : iProp Σ) :
    □ (Pex -∗ ukn_pay N (-1)) -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗ Pex -∗
    ushp_redirs_res rs dv Pex
    ∗ (ushp_redirs_res rs dv Pex -∗ ustr γd dv ushp_symbols 7 ushp_sym_f ∗ Pex).
  Proof using .
    iIntros "#Hpx Hsy Hpay". destruct rs as [| r rs ]; cbn [ushp_redirs_res].
    - iSplitR; [ done | ]. iIntros "_". iFrame "Hsy Hpay".
    - iSplitL "Hsy Hpay"; [ iFrame "Hsy Hpay Hpx" | ].
      iIntros "(Hsy & Hpay & _)". iFrame "Hsy Hpay".
  Qed.

  (* peek's table for the redirects, as the reference's list *)
  Lemma ushp_T_redir_tl : [rb_lt; rb_gt] = ushp_lit ushp_T_redir <$> seq 0%nat 2.
  Proof using . vm_compute. reflexivity. Qed.

  Lemma E62u : bv_unsigned rb_gt = 62.
  Proof using . vm_compute. reflexivity. Qed.


  (* ===================================================================== *)
  (* (2) THE FRAME PROLOGUE AT ITS FRAME POINTER'S VALUE                    *)
  (* ===================================================================== *)
  (* [UkShParse.wp_kshp_fp] quantifies the new frame pointer UNIVERSALLY --
     enough for a walk that never touches its own locals, and not enough
     here, because [q] and [eq] live at [s0-104] and [s0-112] while what
     the walk OWNS is the stack at [sp0].  This is [UkShParse.wp_kshp_
     frame_pro] with the frame pointer at its value; everything else about
     the prologue is unchanged. *)
  Lemma wp_kshp_frame_pro_at (k n : nat) (rs : list (mword 5 * mword 6))
      (p0 : Z) (pcs : nat -> Z) (imm : mword 6) (nz : mword 8)
      (vals : nat -> mword 64) (nn : nat) (h : CpuId) (m : regfile) :
    (length rs + n)%nat = k ->
    (sign_extend' 64 (caddi16sp_imm imm) : mword 64)
      = mword_of_int (- (8 * Z.of_nat k)) ->
    pcs 0%nat = p0 + 2 ->
    (forall i : nat, (i < length rs)%nat -> pcs (S i) = pcs i + 2) ->
    (forall (i : nat) (r : mword 5) (u : mword 6),
       rs !! i = Some (r, u) ->
       uoff_sdsp u = 8 * Z.of_nat k - 8 * (Z.of_nat i + 1) /\
       Regidx r <> Regidx csp_rs1 /\ vals i = m !!! Regidx r) ->
    uinstr_is γt (mword_of_int p0) true (C_ADDI16SP imm) -∗
    ([∗ list] i ↦ ru ∈ rs,
       uinstr_is γt (mword_of_int (pcs i)) true
         (C_SDSP (snd ru, Regidx (fst ru)))) -∗
    uinstr_is γt (mword_of_int (pcs (length rs))) true
      (C_ADDI4SPN (Cregidx (mword_of_int 0), nz)) -∗
    urun N h m (mword_of_int p0) (k + nn) -∗
    (∀ h' : CpuId,
       ⌜ uint (m !!! Regidx csp_rs1) mod 8 = 0 ⌝ -∗
       ⌜ 8 * Z.of_nat k <= uint (m !!! Regidx csp_rs1) ⌝ -∗
       ⌜ uint (m !!! Regidx csp_rs1) < Z64 ⌝ -∗
       ([∗ list] i ↦ _ ∈ rs,
          uword γd (uint (m !!! Regidx csp_rs1) - 8 * (Z.of_nat i + 1))
            (vals i)) -∗
       ustack γd
         (mword_of_int
            (uint (m !!! Regidx csp_rs1) - 8 * Z.of_nat (length rs)))
         n -∗
       urun N h'
         (<[Regidx s0_idx
            := regval_into_reg
                 (add_vec
                    (add_vec_int (m !!! Regidx csp_rs1)
                       (- (8 * Z.of_nat k)))
                    (sign_extend' 64 (caddi4spn_imm nz)))]>
            (<[Regidx csp_rs1
               := regval_into_reg
                    (add_vec_int (m !!! Regidx csp_rs1)
                       (- (8 * Z.of_nat k)))]> m))
         (mword_of_int (pcs (length rs) + 2)) nn -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ek Himm Hp0 Hpc Hoff.
    iIntros "#Hi0 #Hisp #Hifp Hrun Hcont".
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    assert (Hlo : 8 * Z.of_nat k <= uint sp0) by lia.
    assert (Hr0 : 0 <= uint sp0 < Z64).
    { rewrite uint_unsigned. pose proof (bv_unsigned_in_range 64 sp0) as Hr.
      assert (Em : bv_modulus 64 = Z64) by (vm_compute; reflexivity).
      rewrite Em in Hr. exact Hr. }
    (* ---- the push ---- *)
    iApply (wp_uk_caddi16sp_dn N h m (mword_of_int p0) imm k nn
              Himm with "Hi0 Hrun").
    rewrite (ushp_pc_step' p0 2 (pcs 0%nat) ltac:(lia)).
    iIntros "Hstk" (h1) "Hrun".
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat k))).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = spn)
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)).
    assert (Hspu : uint spn = uint sp0 - 8 * Z.of_nat k).
    { unfold spn. rewrite !uint_unsigned.
      exact (uv_avi_neg sp0 (8 * Z.of_nat k) ltac:(lia)
               ltac:(rewrite <- uint_unsigned; lia)). }
    set (spl := (mword_of_int (uint sp0 - 8 * Z.of_nat (length rs))
                 : mword 64)).
    assert (Hsplu : uint spl = uint sp0 - 8 * Z.of_nat (length rs)).
    { unfold spl. apply uint_moi.
      assert (H8 : 8 * Z.of_nat (length rs) <= 8 * Z.of_nat k) by lia. lia. }
    iDestruct (ushp_frame_split sp0 spl n rs Hsplu
                 with "[Hstk]") as "[Hsl Hloc]"; [ rewrite Ek; iExact "Hstk" | ].
    (* ---- the spills ---- *)
    iApply (wp_kshp_spill spn nn rs pcs
              (fun i : nat => uint sp0 - 8 * (Z.of_nat i + 1)) vals h1 m1
              Hsp1 Hpc
              ltac:(intros i r u Hi;
                    destruct (Hoff i r u Hi) as [ Hu [ Hnsp Hv ] ];
                    split;
                    [ rewrite Hspu Hu; lia
                    | split;
                      [ exact (ushp_slot_al (uint sp0) i Hal8)
                      | rewrite Hv;
                        exact (eq_sym
                                 (upd_ne m (Regidx csp_rs1) (Regidx r) _
                                    Hnsp)) ] ])
              with "Hisp Hsl Hrun").
    iIntros "Hsl" (h2) "Hrun".
    (* ---- the frame pointer, AT ITS VALUE.  [wp_kshp_fp] quantifies the
       new s0 universally, which is enough for every landed caller and not
       enough here: parseredirs addresses its two locals THROUGH s0, so the
       walk has to know s0 = sp0. ---- *)
    iApply (wp_uk_caddi4spn N h2 m1 (mword_of_int (pcs (length rs)))
              (mword_of_int 0 : mword 3) nz s0_idx
              (add_vec (m1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm nz))) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              eq_refl
              with "Hifp Hrun").
    rewrite (ushp_pc_step (pcs (length rs)) 2). iIntros (h3) "Hrun".
    rewrite Hsp1.
    iApply ("Hcont" $! h3 with "[] [] [] Hsl Hloc Hrun").
    - iPureIntro. exact Hal8.
    - iPureIntro. exact Hlo.
    - iPureIntro. lia.
  Qed.

  (* ===================================================================== *)
  (* (3) THE LOOP HEAD: 0x502 .. the peek's return                         *)
  (* ===================================================================== *)
  (* [li s5,60; mv a2,s6; mv a1,s2; mv a0,s3; jal peek].  The register file
     comes back with every callee-saved register but s5 as it was, s5 the
     '<' the switch compares against, and a0 the peek's bit. *)
  Lemma wp_kshp_parseredirs_head (h : CpuId) (m : regfile) (dq dw : dfrac)
      (ps s0 : Z) (len off s : nat) (f : nat -> bv 8) (hit : bool)
      (nn : nat) :
    m !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len) ->
    m !!! Regidx s3_idx = mword_of_int ps ->
    m !!! Regidx s6_idx = mword_of_int ushp_T_redir ->
    (off <= len)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    ref_peek len f off [rb_lt; rb_gt] = (hit, s) ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps (mword_of_int (s0 + Z.of_nat off)) -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    urun N h m (mword_of_int 0x502) (8 + (2 + nn)) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ forall r : mword 5, ucallee_saved_idx r = true ->
           Regidx r <> Regidx s5_idx -> m' !!! Regidx r = m !!! Regidx r ⌝ -∗
       ⌜ m' !!! Regidx s5_idx = mword_of_int 60 ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = mword_of_int (if hit then 1 else 0) ⌝ -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat s)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       urun N h' m' (mword_of_int 0x510) (8 + (2 + nn)) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Rs2 Rs3 Rs6 Hoffle Hs0 Hs64 Hps0 Hps8 Hpssz Hpk.
    iIntros "#Hcode #Hro Hcur Hstr Hws Hrun Hcont".
    (* ---- 0x502  li s5,60 -- the '<' the switch compares against ---- *)
    iApply (wp_uk_li N h m (mword_of_int 0x502)
              (mword_of_int 60 : mword 12) s5_idx (mword_of_int 60)
              (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(symmetry; exact (ushp_mv_val 60))
              with "[] Hrun").
    { iApply (uis_shp_502 with "Hcode"). }
    iIntros (h11) "Hrun".
    set (m11 := <[Regidx s5_idx
                  := regval_into_reg (mword_of_int 60 : mword 64)]> m).
    assert (Hm11 : forall q : mword 5, Regidx q <> Regidx s5_idx ->
                     m11 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx s5_idx) (Regidx q) _ Hq)).
    (* ---- 0x506  c.mv a2,s6 ---- *)
    assert (Hs6_11 : m11 !!! Regidx s6_idx = mword_of_int ushp_T_redir)
      by (rewrite (Hm11 s6_idx ltac:(vm_compute; discriminate)); exact Rs6).
    iApply (wp_uk_cmv N h11 m11 (mword_of_int 0x506) a2_idx s6_idx
              (mword_of_int ushp_T_redir) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs6_11; symmetry;
                    exact (ushp_mv_val ushp_T_redir))
              with "[] Hrun").
    { iApply (uis_shp_506 with "Hcode"). }
    iIntros (h12) "Hrun".
    set (m12 := <[Regidx a2_idx
                  := regval_into_reg
                       (mword_of_int ushp_T_redir : mword 64)]> m11).
    assert (Hm12 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                     m12 !!! Regidx q = m11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m11 (Regidx a2_idx) (Regidx q) _ Hq)).
    (* ---- 0x508  c.mv a1,s2 ---- *)
    assert (Hs2_12 : m12 !!! Regidx s2_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm12 s2_idx ltac:(vm_compute; discriminate))
              (Hm11 s2_idx ltac:(vm_compute; discriminate)).
      exact Rs2. }
    iApply (wp_uk_cmv N h12 m12 (mword_of_int 0x508) a1_idx s2_idx
              (mword_of_int (s0 + Z.of_nat len)) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2_12; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_508 with "Hcode"). }
    iIntros (h13) "Hrun".
    set (m13 := <[Regidx a1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m12).
    assert (Hm13 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                     m13 !!! Regidx q = m12 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m12 (Regidx a1_idx) (Regidx q) _ Hq)).
    (* ---- 0x50a  c.mv a0,s3 ---- *)
    assert (Hs3_13 : m13 !!! Regidx s3_idx = mword_of_int ps).
    { rewrite (Hm13 s3_idx ltac:(vm_compute; discriminate))
              (Hm12 s3_idx ltac:(vm_compute; discriminate))
              (Hm11 s3_idx ltac:(vm_compute; discriminate)).
      exact Rs3. }
    iApply (wp_uk_cmv N h13 m13 (mword_of_int 0x50a) a0_idx s3_idx
              (mword_of_int ps) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_13; symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_50a with "Hcode"). }
    iIntros (h14) "Hrun".
    set (m14 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int ps : mword 64)]> m13).
    assert (Hm14 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m14 !!! Regidx q = m13 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m13 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x50c  jal 448 <peek> ---- *)
    iApply (wp_uk_jal N h14 m14 (mword_of_int 0x50c)
              (mword_of_int 2096956 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x510) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_50c with "Hcode"). }
    iIntros (h15) "Hrun".
    set (m15 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x510 : mword 64)]> m14).
    assert (Hm15 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m15 !!! Regidx q = m14 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m14 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret : ret_pc (m15 !!! Regidx ra_idx) = mword_of_int 0x510).
    { rewrite (upd_eq m14 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x510 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_15 : m15 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm15 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m13 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Ha1_15 : m15 !!! Regidx a1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm15 a1_idx ltac:(vm_compute; discriminate))
              (Hm14 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m12 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Ha2_15 : m15 !!! Regidx a2_idx = mword_of_int ushp_T_redir).
    { rewrite (Hm15 a2_idx ltac:(vm_compute; discriminate))
              (Hm14 a2_idx ltac:(vm_compute; discriminate))
              (Hm13 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m11 (Regidx a2_idx)
               (regval_into_reg
                  (mword_of_int ushp_T_redir : mword 64))). }
    rewrite <- shpp_peek.
    (* ---- peek(ps, es, the two redirection bytes), at the reference ---- *)
    iApply (wp_ref_peek h15 m15 dq dw true DfracDiscarded ps s0
              ushp_T_redir len off 2 f (ushp_lit ushp_T_redir)
              (mword_of_int (s0 + Z.of_nat off)) nn [rb_lt; rb_gt] hit s
              Ha0_15 Ha1_15 Ha2_15 Hoffle eq_refl Hs0 Hs64
              ltac:(unfold ushp_T_redir; lia)
              ltac:(unfold ushp_T_redir, Z64; lia) Hps0 Hps8 Hpssz
              ushp_T_redir_tl Hpk
              with "Hcode Hcur Hstr Hws [] Hrun").
    { iApply (ushp_lit_str ushp_T_redir 2 DfracDiscarded
                ushp_T_redir_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Hcur Hstr Hws _" (h16 n0) "%Hcs %Ha0n0 Hrun".
    rewrite Eret.
    iApply ("Hcont" $! h16 n0 with "[%] [%] [%] Hcur Hstr Hws Hrun").
    - intros r Hr Hne.
      rewrite (Hcs r Hr)
              (Hm15 r (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)))
              (Hm14 r (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)))
              (Hm13 r (ushp_cs_ne r a1_idx Hr ltac:(vm_compute; reflexivity)))
              (Hm12 r (ushp_cs_ne r a2_idx Hr ltac:(vm_compute; reflexivity)))
              (Hm11 r Hne).
      reflexivity.
    - rewrite (Hcs s5_idx ltac:(vm_compute; reflexivity))
              (Hm15 s5_idx ltac:(vm_compute; discriminate))
              (Hm14 s5_idx ltac:(vm_compute; discriminate))
              (Hm13 s5_idx ltac:(vm_compute; discriminate))
              (Hm12 s5_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m (Regidx s5_idx)
               (regval_into_reg (mword_of_int 60 : mword 64))).
    - exact Ha0n0.
  Qed.


  (* ===================================================================== *)
  (* (4) ONE TURN OF THE BODY: 0x512 (the guard was true) .. back at 0x502  *)
  (* ===================================================================== *)
  (* The cursor sits at [s], where the reference's peek hit; the '>'
     gettoken answers [(62, s, S s, s1)] and the file-name gettoken
     [(97, q, e, s2)] -- both taken as the reference's equations.  The
     switch takes the '>' arm, [redircmd] builds the node over [cmd] with
     mode 0x601 and fd 1, and the jump lands back on the guard with s4 the
     new node and every other callee-saved register but s1 as it was.  The
     two locals come back holding what the second gettoken wrote. *)
  Lemma wp_kshp_parseredirs_turn {Pex : iProp Σ} (UM UM1 : iProp Σ)
      (Hty : ushp_malloc_ty UM UM1)
      (h : CpuId) (m : regfile) (dq dw dv : dfrac) (cmd ps s0 : Z)
      (len s s1 q e s2 : nat) (f : nat -> bv 8) (fp wB wC : mword 64)
      (nn : nat) :
    ref_sym_scope len f ->
    (s <= len)%nat -> (s1 <= len)%nat ->
    ref_gettoken len f s = (bv_unsigned rb_gt, s, S s, s1) ->
    ref_gettoken len f s1 = (rt_word, q, e, s2) ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    uint fp mod 8 = 0 -> 112 < uint fp -> uint fp < Z64 ->
    m !!! Regidx s0_idx = fp ->
    m !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len) ->
    m !!! Regidx s3_idx = mword_of_int ps ->
    m !!! Regidx s4_idx = mword_of_int cmd ->
    m !!! Regidx s5_idx = mword_of_int 60 ->
    m !!! Regidx s7_idx = mword_of_int 97 ->
    m !!! Regidx s8_idx = mword_of_int (uint fp - 104) ->
    m !!! Regidx s9_idx = mword_of_int (uint fp - 112) ->
    shp_code γt -∗
    UM -∗
    □ (Pex -∗ ukn_pay N (-1)) -∗
    Pex -∗
    uword γd ps (mword_of_int (s0 + Z.of_nat s)) -∗
    uword γd (uint fp - 104) wB -∗
    uword γd (uint fp - 112) wC -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    urun N h m (mword_of_int 0x512) (8 + (2 + (8 + nn))) -∗
    (∀ (t : Z) (h' : CpuId) (m' : regfile),
       ⌜ forall r : mword 5, ucallee_saved_idx r = true ->
           Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s4_idx ->
           m' !!! Regidx r = m !!! Regidx r ⌝ -∗
       ⌜ m' !!! Regidx s4_idx = mword_of_int t ⌝ -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat s2)) -∗
       uword γd (uint fp - 104) (mword_of_int (s0 + Z.of_nat q)) -∗
       uword γd (uint fp - 112) (mword_of_int (s0 + Z.of_nat e)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
       ushp_redir_node s0 t cmd q e 1537 1 -∗
       UM1 -∗
       Pex -∗
       urun N h' m' (mword_of_int 0x502) (8 + (2 + (8 + nn))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hscope Hsle Hs1le E1 E2 Hs0 Hs64 Hps0 Hps8 Hpssz Hfp8 Hfplo Hfphi
      Rs0 Rs2 Rs3 Rs4 Rs5 Rs7 Rs8 Rs9.
    iIntros "#Hcode HM #Hpx Hpay Hcur HB HC Hstr Hws Hsy Hrun Hcont".
    (* the two cells' address hygiene, once *)
    assert (Hqok : 0 < uint fp - 104 /\ (uint fp - 104) mod 8 = 0
                   /\ uint fp - 104 + 8 < Z64).
    { split; [ lia | ].
      split; [ | lia ].
      rewrite Zminus_mod Hfp8.
      assert (E : (104:Z) mod 8 = 0) by reflexivity. rewrite E. reflexivity. }
    assert (Heqok : 0 < uint fp - 112 /\ (uint fp - 112) mod 8 = 0
                    /\ uint fp - 112 + 8 < Z64).
    { split; [ lia | ].
      split; [ | lia ].
      rewrite Zminus_mod Hfp8.
      assert (E : (112:Z) mod 8 = 0) by reflexivity. rewrite E. reflexivity. }
    (* the 12-bit immediates this arm loads, as 64-bit values *)
    assert (E62 : (sign_extend' 64 (mword_of_int 62 : mword 12) : mword 64)
                  = mword_of_int 62)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (E1537 : (sign_extend' 64 (mword_of_int 1537 : mword 12) : mword 64)
                    = mword_of_int 1537)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Ezero : (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64)
                    = mword_of_int 0)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Eone : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                   = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0x512  c.li a3,0  -- the FIRST gettoken passes no out params -- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x512)
              (mword_of_int 0 : mword 6) a3_idx (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_512 with "Hcode"). }
    rewrite (ushp_pc_step 0x512 2). iIntros (h18) "Hrun".
    set (r1 := <[Regidx a3_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 0 : mword 6)
                       : mword 64)]> m).
    assert (Hr1 : forall r : mword 5, Regidx r <> Regidx a3_idx ->
                    r1 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr; exact (upd_ne m (Regidx a3_idx) (Regidx r) _ Hr)).
    (* ---- 0x514  c.li a2,0 ---- *)
    iApply (wp_uk_cli N h18 r1 (mword_of_int 0x514)
              (mword_of_int 0 : mword 6) a2_idx (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_514 with "Hcode"). }
    rewrite (ushp_pc_step 0x514 2). iIntros (h19) "Hrun".
    set (r2 := <[Regidx a2_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 0 : mword 6)
                       : mword 64)]> r1).
    assert (Hr2 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
                    r2 !!! Regidx r = r1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r1 (Regidx a2_idx) (Regidx r) _ Hr)).
    (* ---- 0x516  c.mv a1,s2 ---- *)
    iApply (wp_uk_cmv N h19 r2 (mword_of_int 0x516) a1_idx s2_idx
              (mword_of_int (s0 + Z.of_nat len)) (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hr2 s2_idx ltac:(vm_compute; discriminate))
                      (Hr1 s2_idx ltac:(vm_compute; discriminate)) Rs2;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_516 with "Hcode"). }
    rewrite (ushp_pc_step 0x516 2). iIntros (h20) "Hrun".
    set (r3 := <[Regidx a1_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64)]> r2).
    assert (Hr3 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                    r3 !!! Regidx r = r2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r2 (Regidx a1_idx) (Regidx r) _ Hr)).
    (* ---- 0x518  c.mv a0,s3 ---- *)
    iApply (wp_uk_cmv N h20 r3 (mword_of_int 0x518) a0_idx s3_idx
              (mword_of_int ps) (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hr3 s3_idx ltac:(vm_compute; discriminate))
                      (Hr2 s3_idx ltac:(vm_compute; discriminate))
                      (Hr1 s3_idx ltac:(vm_compute; discriminate)) Rs3;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_518 with "Hcode"). }
    rewrite (ushp_pc_step 0x518 2). iIntros (h21) "Hrun".
    set (r4 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> r3).
    assert (Hr4 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    r4 !!! Regidx r = r3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r3 (Regidx a0_idx) (Regidx r) _ Hr)).
    (* ---- 0x51a  jal 310 <gettoken> ---- *)
    iApply (wp_uk_jal N h21 r4 (mword_of_int 0x51a)
              (mword_of_int 2096630 : mword 21) ra_idx
              (mword_of_int 0x310) (mword_of_int 0x51e) (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_51a with "Hcode"). }
    iIntros (h22) "Hrun".
    set (r5 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x51e : mword 64)]> r4).
    assert (Hr5 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                    r5 !!! Regidx r = r4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r4 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Hr5cs : forall r : mword 5, ucallee_saved_idx r = true ->
              r5 !!! Regidx r = m !!! Regidx r).
    { intros r Hr.
      rewrite (Hr5 r (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)))
              (Hr4 r (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)))
              (Hr3 r (ushp_cs_ne r a1_idx Hr ltac:(vm_compute; reflexivity)))
              (Hr2 r (ushp_cs_ne r a2_idx Hr ltac:(vm_compute; reflexivity)))
              (Hr1 r (ushp_cs_ne r a3_idx Hr ltac:(vm_compute; reflexivity))).
      reflexivity. }
    assert (Ea0_r5 : r5 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hr5 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq r3 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Ea1_r5 : r5 !!! Regidx a1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hr5 a1_idx ltac:(vm_compute; discriminate))
              (Hr4 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq r2 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Ea2_r5 : r5 !!! Regidx a2_idx = mword_of_int 0).
    { rewrite (Hr5 a2_idx ltac:(vm_compute; discriminate))
              (Hr4 a2_idx ltac:(vm_compute; discriminate))
              (Hr3 a2_idx ltac:(vm_compute; discriminate)).
      rewrite (upd_eq r1 (Regidx a2_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64))).
      exact Ezero. }
    assert (Ea3_r5 : r5 !!! Regidx a3_idx = mword_of_int 0).
    { rewrite (Hr5 a3_idx ltac:(vm_compute; discriminate))
              (Hr4 a3_idx ltac:(vm_compute; discriminate))
              (Hr3 a3_idx ltac:(vm_compute; discriminate))
              (Hr2 a3_idx ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m (Regidx a3_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64))).
      exact Ezero. }
    assert (Eret1 : ret_pc (r5 !!! Regidx ra_idx) = mword_of_int 0x51e).
    { rewrite (upd_eq r4 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x51e : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    rewrite <- shpp_gettoken.
    (* ---- gettoken(ps, es, 0, 0) -- the reference says it answers '>' ---- *)
    iApply (wp_ref_gettoken h22 r5 dq dw dv ps 0 0 s0 len s f
              (mword_of_int (s0 + Z.of_nat s)) (mword_of_int 0)
              (mword_of_int 0) (8 + nn) (bv_unsigned rb_gt) s (S s) s1
              Ea0_r5 Ea1_r5 Ea2_r5 Ea3_r5 Hsle eq_refl Hscope
              Hs0 Hs64 Hps0 Hps8 Hpssz E1
              with "Hcode Hcur [] [] Hstr Hws Hsy Hrun").
    { iLeft. iPureIntro. reflexivity. }
    { iLeft. iPureIntro. reflexivity. }
    iIntros "Hcur _ _ Hstr Hws Hsy" (h23 g0) "%Hcsg0 %Ha0g0 Hrun".
    rewrite Eret1.
    rewrite E62u in Ha0g0.
    assert (Hg0cs : forall r : mword 5, ucallee_saved_idx r = true ->
              g0 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr; rewrite (Hcsg0 r Hr); exact (Hr5cs r Hr)).
    (* ---- 0x51e  c.mv s1,a0  --  tok = '>' ---- *)
    iApply (wp_uk_cmv N h23 g0 (mword_of_int 0x51e) s1_idx a0_idx
              (mword_of_int 62) (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0g0; symmetry; exact (ushp_mv_val 62))
              with "[] Hrun").
    { iApply (uis_shp_51e with "Hcode"). }
    rewrite (ushp_pc_step 0x51e 2). iIntros (h24) "Hrun".
    set (r6 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int 62 : mword 64)]> g0).
    assert (Hr6 : forall r : mword 5, Regidx r <> Regidx s1_idx ->
                    r6 !!! Regidx r = g0 !!! Regidx r)
      by (intros r Hr; exact (upd_ne g0 (Regidx s1_idx) (Regidx r) _ Hr)).
    assert (Hs1_r6 : r6 !!! Regidx s1_idx = mword_of_int 62)
      by exact (upd_eq g0 (Regidx s1_idx)
                  (regval_into_reg (mword_of_int 62 : mword 64))).
    (* ---- 0x520  c.mv a3,s9  --  &eq ---- *)
    iApply (wp_uk_cmv N h24 r6 (mword_of_int 0x520) a3_idx s9_idx
              (mword_of_int (uint fp - 112)) (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hr6 s9_idx ltac:(vm_compute; discriminate))
                      (Hg0cs s9_idx ltac:(vm_compute; reflexivity)) Rs9;
                    symmetry; exact (ushp_mv_val (uint fp - 112)))
              with "[] Hrun").
    { iApply (uis_shp_520 with "Hcode"). }
    rewrite (ushp_pc_step 0x520 2). iIntros (h25) "Hrun".
    set (r7 := <[Regidx a3_idx
                 := regval_into_reg
                      (mword_of_int (uint fp - 112) : mword 64)]> r6).
    assert (Hr7 : forall r : mword 5, Regidx r <> Regidx a3_idx ->
                    r7 !!! Regidx r = r6 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r6 (Regidx a3_idx) (Regidx r) _ Hr)).
    (* ---- 0x522  c.mv a2,s8  --  &q ---- *)
    iApply (wp_uk_cmv N h25 r7 (mword_of_int 0x522) a2_idx s8_idx
              (mword_of_int (uint fp - 104)) (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hr7 s8_idx ltac:(vm_compute; discriminate))
                      (Hr6 s8_idx ltac:(vm_compute; discriminate))
                      (Hg0cs s8_idx ltac:(vm_compute; reflexivity)) Rs8;
                    symmetry; exact (ushp_mv_val (uint fp - 104)))
              with "[] Hrun").
    { iApply (uis_shp_522 with "Hcode"). }
    rewrite (ushp_pc_step 0x522 2). iIntros (h26) "Hrun".
    set (r8 := <[Regidx a2_idx
                 := regval_into_reg
                      (mword_of_int (uint fp - 104) : mword 64)]> r7).
    assert (Hr8 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
                    r8 !!! Regidx r = r7 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r7 (Regidx a2_idx) (Regidx r) _ Hr)).
    (* ---- 0x524  c.mv a1,s2 ---- *)
    iApply (wp_uk_cmv N h26 r8 (mword_of_int 0x524) a1_idx s2_idx
              (mword_of_int (s0 + Z.of_nat len)) (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hr8 s2_idx ltac:(vm_compute; discriminate))
                      (Hr7 s2_idx ltac:(vm_compute; discriminate))
                      (Hr6 s2_idx ltac:(vm_compute; discriminate))
                      (Hg0cs s2_idx ltac:(vm_compute; reflexivity)) Rs2;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_524 with "Hcode"). }
    rewrite (ushp_pc_step 0x524 2). iIntros (h27) "Hrun".
    set (r9 := <[Regidx a1_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64)]> r8).
    assert (Hr9 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                    r9 !!! Regidx r = r8 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r8 (Regidx a1_idx) (Regidx r) _ Hr)).
    (* ---- 0x526  c.mv a0,s3 ---- *)
    iApply (wp_uk_cmv N h27 r9 (mword_of_int 0x526) a0_idx s3_idx
              (mword_of_int ps) (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hr9 s3_idx ltac:(vm_compute; discriminate))
                      (Hr8 s3_idx ltac:(vm_compute; discriminate))
                      (Hr7 s3_idx ltac:(vm_compute; discriminate))
                      (Hr6 s3_idx ltac:(vm_compute; discriminate))
                      (Hg0cs s3_idx ltac:(vm_compute; reflexivity)) Rs3;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_526 with "Hcode"). }
    rewrite (ushp_pc_step 0x526 2). iIntros (h28) "Hrun".
    set (r10 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int ps : mword 64)]> r9).
    assert (Hr10 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                     r10 !!! Regidx r = r9 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r9 (Regidx a0_idx) (Regidx r) _ Hr)).
    (* ---- 0x528  jal 310 <gettoken> -- with &q and &eq this time ---- *)
    iApply (wp_uk_jal N h28 r10 (mword_of_int 0x528)
              (mword_of_int 2096616 : mword 21) ra_idx
              (mword_of_int 0x310) (mword_of_int 0x52c) (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_528 with "Hcode"). }
    iIntros (h29) "Hrun".
    set (r11 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x52c : mword 64)]> r10).
    assert (Hr11 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                     r11 !!! Regidx r = r10 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r10 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Hr11cs : forall r : mword 5, ucallee_saved_idx r = true ->
              Regidx r <> Regidx s1_idx -> r11 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Hs1.
      rewrite (Hr11 r (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)))
              (Hr10 r (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)))
              (Hr9 r (ushp_cs_ne r a1_idx Hr ltac:(vm_compute; reflexivity)))
              (Hr8 r (ushp_cs_ne r a2_idx Hr ltac:(vm_compute; reflexivity)))
              (Hr7 r (ushp_cs_ne r a3_idx Hr ltac:(vm_compute; reflexivity)))
              (Hr6 r Hs1).
      exact (Hg0cs r Hr). }
    assert (Fa0 : r11 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hr11 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq r9 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Fa1 : r11 !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hr11 a1_idx ltac:(vm_compute; discriminate))
              (Hr10 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq r8 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Fa2 : r11 !!! Regidx a2_idx = mword_of_int (uint fp - 104)).
    { rewrite (Hr11 a2_idx ltac:(vm_compute; discriminate))
              (Hr10 a2_idx ltac:(vm_compute; discriminate))
              (Hr9 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq r7 (Regidx a2_idx)
               (regval_into_reg
                  (mword_of_int (uint fp - 104) : mword 64))). }
    assert (Fa3 : r11 !!! Regidx a3_idx = mword_of_int (uint fp - 112)).
    { rewrite (Hr11 a3_idx ltac:(vm_compute; discriminate))
              (Hr10 a3_idx ltac:(vm_compute; discriminate))
              (Hr9 a3_idx ltac:(vm_compute; discriminate))
              (Hr8 a3_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq r6 (Regidx a3_idx)
               (regval_into_reg
                  (mword_of_int (uint fp - 112) : mword 64))). }
    assert (Eret2 : ret_pc (r11 !!! Regidx ra_idx) = mword_of_int 0x52c).
    { rewrite (upd_eq r10 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x52c : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    rewrite <- shpp_gettoken.
    (* ---- gettoken(ps, es, &q, &eq) -- the FILE NAME: the reference says
            a word [[q, e)] and the cursor at [s2] ---- *)
    iApply (wp_ref_gettoken h29 r11 dq dw dv ps
              (uint fp - 104) (uint fp - 112) s0 len s1 f
              (mword_of_int (s0 + Z.of_nat s1)) wB wC (8 + nn)
              rt_word q e s2
              Fa0 Fa1 Fa2 Fa3 Hs1le eq_refl Hscope
              Hs0 Hs64 Hps0 Hps8 Hpssz E2
              with "Hcode Hcur [HB] [HC] Hstr Hws Hsy Hrun").
    { iRight. iSplitR; [ iPureIntro; exact Hqok | iExact "HB" ]. }
    { iRight. iSplitR; [ iPureIntro; exact Heqok | iExact "HC" ]. }
    iIntros "Hcur Hq Heq Hstr Hws Hsy" (h30 g1) "%Hcsg1 %Ha0g1 Hrun".
    rewrite Eret2.
    change rt_word with 97 in Ha0g1.
    iDestruct "Hq" as "[ %Hbad | [_ HB] ]"; [ exfalso; lia | ].
    iDestruct "Heq" as "[ %Hbad | [_ HC] ]"; [ exfalso; lia | ].
    assert (Hg1cs : forall r : mword 5, ucallee_saved_idx r = true ->
              Regidx r <> Regidx s1_idx -> g1 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr Hs1; rewrite (Hcsg1 r Hr); exact (Hr11cs r Hr Hs1)).
    assert (Hs1_g1 : g1 !!! Regidx s1_idx = mword_of_int 62).
    { rewrite (Hcsg1 s1_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hr11 s1_idx ltac:(vm_compute; discriminate))
              (Hr10 s1_idx ltac:(vm_compute; discriminate))
              (Hr9 s1_idx ltac:(vm_compute; discriminate))
              (Hr8 s1_idx ltac:(vm_compute; discriminate))
              (Hr7 s1_idx ltac:(vm_compute; discriminate)).
      exact Hs1_r6. }
    assert (Hs5_g1 : g1 !!! Regidx s5_idx = mword_of_int 60)
      by (rewrite (Hg1cs s5_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Rs5).
    assert (Hs7_g1 : g1 !!! Regidx s7_idx = mword_of_int 97)
      by (rewrite (Hg1cs s7_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Rs7).
    (* ---- 0x52c  bne a0,s7 -- NOT taken: the token IS 'a' ---- *)
    iApply (wp_uk_btype N h30 g1 (mword_of_int 0x52c)
              (mword_of_int 8118 : mword 13) s7_idx a0_idx BNE false
              (mword_of_int 0x4e2) (8 + (2 + (8 + nn)))
              ltac:(rewrite Ha0g1 Hs7_g1; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_52c with "Hcode"). }
    rewrite (ushp_pc_step 0x52c 4). iIntros (h31) "Hrun".
    (* ---- 0x530  beq s1,s5 -- NOT taken: the token is '>' not '<' ---- *)
    iApply (wp_uk_btype N h31 g1 (mword_of_int 0x530)
              (mword_of_int 8126 : mword 13) s5_idx s1_idx BEQ false
              (mword_of_int 0x4ee) (8 + (2 + (8 + nn)))
              ltac:(rewrite Hs1_g1 Hs5_g1; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_530 with "Hcode"). }
    rewrite (ushp_pc_step 0x530 4). iIntros (h32) "Hrun".
    (* ---- 0x534  li a5,62 ---- *)
    iApply (wp_uk_li N h32 g1 (mword_of_int 0x534)
              (mword_of_int 62 : mword 12) a5_idx (mword_of_int 62)
              (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite E62; symmetry; exact (ushp_mv_val 62))
              with "[] Hrun").
    { iApply (uis_shp_534 with "Hcode"). }
    rewrite (ushp_pc_step 0x534 4). iIntros (h33) "Hrun".
    set (r12 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int 62 : mword 64)]> g1).
    assert (Hr12 : forall r : mword 5, Regidx r <> Regidx a5_idx ->
                     r12 !!! Regidx r = g1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne g1 (Regidx a5_idx) (Regidx r) _ Hr)).
    assert (Ha5_r12 : r12 !!! Regidx a5_idx = mword_of_int 62)
      by exact (upd_eq g1 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int 62 : mword 64))).
    assert (Hs1_r12 : r12 !!! Regidx s1_idx = mword_of_int 62)
      by (rewrite (Hr12 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_g1).
    (* ---- 0x538  beq s1,a5 -- TAKEN: the '>' arm ---- *)
    iApply (wp_uk_btype N h33 r12 (mword_of_int 0x538)
              (mword_of_int 36 : mword 13) a5_idx s1_idx BEQ true
              (mword_of_int 0x55c) (8 + (2 + (8 + nn)))
              ltac:(rewrite Hs1_r12 Ha5_r12; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_538 with "Hcode"). }
    iIntros (h34) "Hrun".
    (* ---- 0x55c  c.li a4,1  --  fd = 1 ---- *)
    iApply (wp_uk_cli N h34 r12 (mword_of_int 0x55c)
              (mword_of_int 1 : mword 6) a4_idx (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_55c with "Hcode"). }
    rewrite (ushp_pc_step 0x55c 2). iIntros (h35) "Hrun".
    set (r13 := <[Regidx a4_idx
                  := regval_into_reg
                       (sign_extend' 64 (mword_of_int 1 : mword 6)
                        : mword 64)]> r12).
    assert (Hr13 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
                     r13 !!! Regidx r = r12 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r12 (Regidx a4_idx) (Regidx r) _ Hr)).
    (* ---- 0x55e  li a3,1537  --  O_WRONLY|O_CREATE|O_TRUNC ---- *)
    iApply (wp_uk_li N h35 r13 (mword_of_int 0x55e)
              (mword_of_int 1537 : mword 12) a3_idx (mword_of_int 1537)
              (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite E1537; symmetry; exact (ushp_mv_val 1537))
              with "[] Hrun").
    { iApply (uis_shp_55e with "Hcode"). }
    rewrite (ushp_pc_step 0x55e 4). iIntros (h36) "Hrun".
    set (r14 := <[Regidx a3_idx
                  := regval_into_reg (mword_of_int 1537 : mword 64)]> r13).
    assert (Hr14 : forall r : mword 5, Regidx r <> Regidx a3_idx ->
                     r14 !!! Regidx r = r13 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r13 (Regidx a3_idx) (Regidx r) _ Hr)).
    assert (Hs0_r14 : r14 !!! Regidx s0_idx = fp).
    { rewrite (Hr14 s0_idx ltac:(vm_compute; discriminate))
              (Hr13 s0_idx ltac:(vm_compute; discriminate))
              (Hr12 s0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hg1cs s0_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)).
      exact Rs0. }
    (* ---- 0x562  ld a2,-112(s0)  --  efile ---- *)
    iApply (wp_uk_ld N h36 r14 (mword_of_int 0x562)
              (mword_of_int 3984 : mword 12) s0_idx a2_idx (DfracOwn 1)
              (uint fp - 112) (mword_of_int (s0 + Z.of_nat e))
              (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs0_r14; vm_compute uoff_i12; lia)
              ltac:(exact (proj1 (proj2 Heqok)))
              ltac:(vm_compute; discriminate)
              with "[] HC Hrun").
    { iApply (uis_shp_562 with "Hcode"). }
    iIntros "HC" (h37) "Hrun".
    rewrite (ushp_pc_step 0x562 4).
    set (r15 := <[Regidx a2_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat e) : mword 64)]> r14).
    assert (Hr15 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
                     r15 !!! Regidx r = r14 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r14 (Regidx a2_idx) (Regidx r) _ Hr)).
    assert (Hs0_r15 : r15 !!! Regidx s0_idx = fp)
      by (rewrite (Hr15 s0_idx ltac:(vm_compute; discriminate)); exact Hs0_r14).
    (* ---- 0x566  ld a1,-104(s0)  --  file ---- *)
    iApply (wp_uk_ld N h37 r15 (mword_of_int 0x566)
              (mword_of_int 3992 : mword 12) s0_idx a1_idx (DfracOwn 1)
              (uint fp - 104) (mword_of_int (s0 + Z.of_nat q))
              (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs0_r15; vm_compute uoff_i12; lia)
              ltac:(exact (proj1 (proj2 Hqok)))
              ltac:(vm_compute; discriminate)
              with "[] HB Hrun").
    { iApply (uis_shp_566 with "Hcode"). }
    iIntros "HB" (h38) "Hrun".
    rewrite (ushp_pc_step 0x566 4).
    set (r16 := <[Regidx a1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat q)
                        : mword 64)]> r15).
    assert (Hr16 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                     r16 !!! Regidx r = r15 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r15 (Regidx a1_idx) (Regidx r) _ Hr)).
    assert (Hs4_r16 : r16 !!! Regidx s4_idx = mword_of_int cmd).
    { rewrite (Hr16 s4_idx ltac:(vm_compute; discriminate))
              (Hr15 s4_idx ltac:(vm_compute; discriminate))
              (Hr14 s4_idx ltac:(vm_compute; discriminate))
              (Hr13 s4_idx ltac:(vm_compute; discriminate))
              (Hr12 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hg1cs s4_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)).
      exact Rs4. }
    (* ---- 0x56a  c.mv a0,s4 ---- *)
    iApply (wp_uk_cmv N h38 r16 (mword_of_int 0x56a) a0_idx s4_idx
              (mword_of_int cmd) (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs4_r16; symmetry; exact (ushp_mv_val cmd))
              with "[] Hrun").
    { iApply (uis_shp_56a with "Hcode"). }
    rewrite (ushp_pc_step 0x56a 2). iIntros (h39) "Hrun".
    set (r17 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int cmd : mword 64)]> r16).
    assert (Hr17 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                     r17 !!! Regidx r = r16 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r16 (Regidx a0_idx) (Regidx r) _ Hr)).
    (* ---- 0x56c  jal 200 <redircmd> ---- *)
    iApply (wp_uk_jal N h39 r17 (mword_of_int 0x56c)
              (mword_of_int 2096276 : mword 21) ra_idx
              (mword_of_int 0x200) (mword_of_int 0x570) (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_56c with "Hcode"). }
    iIntros (h40) "Hrun".
    set (r18 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x570 : mword 64)]> r17).
    assert (Hr18 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                     r18 !!! Regidx r = r17 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r17 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Ga0 : r18 !!! Regidx a0_idx = mword_of_int cmd).
    { rewrite (Hr18 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq r16 (Regidx a0_idx)
               (regval_into_reg (mword_of_int cmd : mword 64))). }
    assert (Ga1 : r18 !!! Regidx a1_idx
                  = mword_of_int (s0 + Z.of_nat q)).
    { rewrite (Hr18 a1_idx ltac:(vm_compute; discriminate))
              (Hr17 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq r15 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat q) : mword 64))). }
    assert (Ga2 : r18 !!! Regidx a2_idx = mword_of_int (s0 + Z.of_nat e)).
    { rewrite (Hr18 a2_idx ltac:(vm_compute; discriminate))
              (Hr17 a2_idx ltac:(vm_compute; discriminate))
              (Hr16 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq r14 (Regidx a2_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat e) : mword 64))). }
    assert (Ga3 : r18 !!! Regidx a3_idx = mword_of_int 1537).
    { rewrite (Hr18 a3_idx ltac:(vm_compute; discriminate))
              (Hr17 a3_idx ltac:(vm_compute; discriminate))
              (Hr16 a3_idx ltac:(vm_compute; discriminate))
              (Hr15 a3_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq r13 (Regidx a3_idx)
               (regval_into_reg (mword_of_int 1537 : mword 64))). }
    assert (Ga4 : r18 !!! Regidx a4_idx = mword_of_int 1).
    { rewrite (Hr18 a4_idx ltac:(vm_compute; discriminate))
              (Hr17 a4_idx ltac:(vm_compute; discriminate))
              (Hr16 a4_idx ltac:(vm_compute; discriminate))
              (Hr15 a4_idx ltac:(vm_compute; discriminate))
              (Hr14 a4_idx ltac:(vm_compute; discriminate)).
      rewrite (upd_eq r12 (Regidx a4_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64))).
      exact Eone. }
    assert (Eret3 : ret_pc (r18 !!! Regidx ra_idx) = mword_of_int 0x570).
    { rewrite (upd_eq r17 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x570 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hr18cs : forall r : mword 5, ucallee_saved_idx r = true ->
              Regidx r <> Regidx s1_idx -> r18 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Hs1.
      rewrite (Hr18 r (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)))
              (Hr17 r (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)))
              (Hr16 r (ushp_cs_ne r a1_idx Hr ltac:(vm_compute; reflexivity)))
              (Hr15 r (ushp_cs_ne r a2_idx Hr ltac:(vm_compute; reflexivity)))
              (Hr14 r (ushp_cs_ne r a3_idx Hr ltac:(vm_compute; reflexivity)))
              (Hr13 r (ushp_cs_ne r a4_idx Hr ltac:(vm_compute; reflexivity)))
              (Hr12 r (ushp_cs_ne r a5_idx Hr ltac:(vm_compute; reflexivity))).
      exact (Hg1cs r Hr Hs1). }
    rewrite <- shpp_redircmd.
    (* ---- redircmd(cmd, q, eq, 0x601, 1) -- the REDIR node ---- *)
    iApply (UkShRedirCmd.wp_kshp_redircmd_n N UM UM1 Hty h40 r18 s0 cmd 1537 1
              emp%I q e nn Ga0 Ga1 Ga2 Ga3 Ga4
              ltac:(unfold Z31; lia) ltac:(unfold Z31; lia)
              with "Hcode HM Hpx Hpay [//] Hrun").
    iIntros (h41 g2 t) "%Hcsg2 %Ha0g2 %Hpb Htree _ HM' Hpay Hrun".
    rewrite Eret3.
    assert (Hg2cs : forall r : mword 5, ucallee_saved_idx r = true ->
              Regidx r <> Regidx s1_idx -> g2 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr Hs1; rewrite (Hcsg2 r Hr); exact (Hr18cs r Hr Hs1)).
    (* ---- 0x570  c.mv s4,a0  --  cmd = the new node ---- *)
    iApply (wp_uk_cmv N h41 g2 (mword_of_int 0x570) s4_idx a0_idx
              (mword_of_int t) (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0g2; symmetry; exact (ushp_mv_val t))
              with "[] Hrun").
    { iApply (uis_shp_570 with "Hcode"). }
    rewrite (ushp_pc_step 0x570 2). iIntros (h42) "Hrun".
    set (r19 := <[Regidx s4_idx
                  := regval_into_reg (mword_of_int t : mword 64)]> g2).
    assert (Hr19 : forall r : mword 5, Regidx r <> Regidx s4_idx ->
                     r19 !!! Regidx r = g2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne g2 (Regidx s4_idx) (Regidx r) _ Hr)).
    assert (Hs4_r19 : r19 !!! Regidx s4_idx = mword_of_int t)
      by exact (upd_eq g2 (Regidx s4_idx)
                  (regval_into_reg (mword_of_int t : mword 64))).
    (* ---- 0x572  c.j 0x502 -- back to the guard ---- *)
    iApply (wp_uk_cj N h42 r19 (mword_of_int 0x572)
              (mword_of_int 1992 : mword 11) (mword_of_int 0x502)
              (8 + (2 + (8 + nn)))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_572 with "Hcode"). }
    iIntros (h43) "Hrun".
    assert (Hr19cs : forall r : mword 5, ucallee_saved_idx r = true ->
              Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s4_idx ->
              r19 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr Hs1 Hs4; rewrite (Hr19 r Hs4); exact (Hg2cs r Hr Hs1)).
    iApply ("Hcont" $! t h43 r19 with "[%] [%] Hcur HB HC Hstr Hws Hsy Htree HM' Hpay Hrun").
    - exact Hr19cs.
    - exact Hs4_r19.
  Qed.


  (* ===================================================================== *)
  (* (5) THE LOOP, by induction on the redirects the reference consumes    *)
  (* ===================================================================== *)
  (* At the guard with the loop's registers in place ([fp] the frame
     pointer, s2/s3 the arguments, s4 the tree so far, s6 the table, s7 the
     'a', s8/s9 the two locals' addresses) and the cursor at [off].  The
     reference's answer [Some (rs, fin)] drives the case split: [[]] is a
     peek that misses and the exit at 0x574; [r :: rs'] is a peek that hit
     a '>', one turn, and the loop again at the file name's end.  The turn
     needs the symbol scope and eight more words (redircmd's malloc), so
     both are guarded by [rs <> []]; the resources it spends come and go
     as [ushp_redirs_res rs]. *)
  Lemma wp_kshp_parseredirs_loop {Pex : iProp Σ} (rs : list rredir) :
    forall (h : CpuId) (m : regfile) (dq dw dv : dfrac) (cmd ps s0 : Z)
      (len off n fin : nat) (f : nat -> bv 8) (fp wB wC : mword 64)
      (UM UM' : iProp Σ) (nn : nat),
    ref_redirs len f n off [] = Some (rs, fin) ->
    ushp_malloc_chain (length rs) UM UM' ->
    (rs <> [] -> ref_sym_scope len f) ->
    (rs <> [] -> (8 <= nn)%nat) ->
    (off <= len)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    uint fp mod 8 = 0 -> 112 < uint fp -> uint fp < Z64 ->
    m !!! Regidx s0_idx = fp ->
    m !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len) ->
    m !!! Regidx s3_idx = mword_of_int ps ->
    m !!! Regidx s4_idx = mword_of_int cmd ->
    m !!! Regidx s6_idx = mword_of_int ushp_T_redir ->
    m !!! Regidx s7_idx = mword_of_int 97 ->
    m !!! Regidx s8_idx = mword_of_int (uint fp - 104) ->
    m !!! Regidx s9_idx = mword_of_int (uint fp - 112) ->
    shp_code γt -∗
    shp_rodata γt -∗
    UM -∗
    ushp_redirs_res rs dv Pex -∗
    uword γd ps (mword_of_int (s0 + Z.of_nat off)) -∗
    uword γd (uint fp - 104) wB -∗
    uword γd (uint fp - 112) wC -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    urun N h m (mword_of_int 0x502) (8 + (2 + nn)) -∗
    (∀ (t : Z) (h' : CpuId) (m' : regfile) (wB' wC' : mword 64),
       ⌜ forall r : mword 5, ucallee_saved_idx r = true ->
           Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s4_idx ->
           Regidx r <> Regidx s5_idx -> m' !!! Regidx r = m !!! Regidx r ⌝ -∗
       ⌜ m' !!! Regidx s4_idx = mword_of_int t ⌝ -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat fin)) -∗
       uword γd (uint fp - 104) wB' -∗
       uword γd (uint fp - 112) wC' -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ushp_redirs_at s0 t cmd rs -∗
       UM' -∗
       ushp_redirs_res rs dv Pex -∗
       urun N h' m' (mword_of_int 0x574) (8 + (2 + nn)) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    induction rs as [| r rs' IH ];
      intros h m dq dw dv cmd ps s0 len off n fin f fp wB wC UM UM' nn
        Href Hchain Hscope Hnn Hoffle Hs0 Hs64 Hps0 Hps8 Hpssz Hfp8 Hfplo Hfphi
        Rs0 Rs2 Rs3 Rs4 Rs6 Rs7 Rs8 Rs9.
    - (* ---- ZERO turns: the peek misses ---- *)
      iIntros "#Hcode #Hro HM Hres Hcur HB HC Hstr Hws Hrun Hcont".
      pose proof (ref_redirs_nil_inv len f n off fin Href) as Hpk.
      iApply (wp_kshp_parseredirs_head h m dq dw ps s0 len off fin f false nn
                Rs2 Rs3 Rs6 Hoffle Hs0 Hs64 Hps0 Hps8 Hpssz Hpk
                with "Hcode Hro Hcur Hstr Hws Hrun").
      iIntros (h1 m1) "%Hm1 %Hs5 %Ha0 Hcur Hstr Hws Hrun".
      (* ---- 0x510  c.beqz a0 -- TAKEN: the loop is done ---- *)
      iApply (wp_uk_cbeqz N h1 m1 (mword_of_int 0x510)
                (mword_of_int 50 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                true (mword_of_int 0x574) (8 + (2 + nn))
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_510 with "Hcode"). }
      iIntros (h2) "Hrun".
      cbn [ushp_malloc_chain length] in Hchain. subst UM'.
      iApply ("Hcont" $! cmd h2 m1 wB wC
                with "[%] [%] Hcur HB HC Hstr Hws [] HM Hres Hrun").
      + intros r Hr H1 H4 H5. exact (Hm1 r Hr H5).
      + rewrite (Hm1 s4_idx ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; discriminate)).
        exact Rs4.
      + cbn [ushp_redirs_at]. iPureIntro. reflexivity.
    - (* ---- A TURN, then the loop again ---- *)
      iIntros "#Hcode #Hro HM Hres Hcur HB HC Hstr Hws Hrun Hcont".
      iDestruct (ustr_nonul with "Hstr") as %Hnonul.
      cbn [ushp_redirs_res]. iDestruct "Hres" as "(Hsy & Hpay & #Hpx)".
      destruct n as [| n ]; [ discriminate Href | ].
      assert (Hsc : ref_sym_scope len f) by (apply Hscope; discriminate).
      destruct (ref_redirs_cons_inv len f n off r rs' fin Hsc Hnonul Hoffle Href)
        as (s & s1 & q & e & s2 & Hpk & Hsle & E1 & Hs1le & E2 & Hs2le & -> & Href').
      cbn [ushp_malloc_chain length] in Hchain.
      destruct Hchain as (UM1 & Hty & Hchain').
      assert (Hnn' : exists nn' : nat, nn = (8 + nn')%nat)
        by (exists (nn - 8)%nat; pose proof (Hnn ltac:(discriminate)); lia).
      destruct Hnn' as (nn' & ->).
      iApply (wp_kshp_parseredirs_head h m dq dw ps s0 len off s f true (8 + nn')
                Rs2 Rs3 Rs6 Hoffle Hs0 Hs64 Hps0 Hps8 Hpssz Hpk
                with "Hcode Hro Hcur Hstr Hws Hrun").
      iIntros (h1 m1) "%Hm1 %Hs5 %Ha0 Hcur Hstr Hws Hrun".
      (* ---- 0x510  c.beqz a0 -- NOT taken: the guard is true ---- *)
      iApply (wp_uk_cbeqz N h1 m1 (mword_of_int 0x510)
                (mword_of_int 50 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                false (mword_of_int 0x574) (8 + (2 + (8 + nn')))
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_510 with "Hcode"). }
      rewrite (ushp_pc_step 0x510 2). iIntros (h2) "Hrun".
      (* the loop's registers, one head later *)
      assert (Hm1cs : forall r : mword 5, ucallee_saved_idx r = true ->
                Regidx r <> Regidx s5_idx -> m1 !!! Regidx r = m !!! Regidx r)
        by exact Hm1.
      iApply (wp_kshp_parseredirs_turn UM UM1 Hty h2 m1 dq dw dv cmd ps s0
                len s s1 q e s2 f fp wB wC nn'
                Hsc Hsle Hs1le E1 E2 Hs0 Hs64 Hps0 Hps8 Hpssz Hfp8 Hfplo Hfphi
                ltac:(rewrite (Hm1cs s0_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)); exact Rs0)
                ltac:(rewrite (Hm1cs s2_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)); exact Rs2)
                ltac:(rewrite (Hm1cs s3_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)); exact Rs3)
                ltac:(rewrite (Hm1cs s4_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)); exact Rs4)
                Hs5
                ltac:(rewrite (Hm1cs s7_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)); exact Rs7)
                ltac:(rewrite (Hm1cs s8_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)); exact Rs8)
                ltac:(rewrite (Hm1cs s9_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)); exact Rs9)
                with "Hcode HM Hpx Hpay Hcur HB HC Hstr Hws Hsy Hrun").
      iIntros (t1 h3 m3) "%Hm3 %Hs4_3 Hcur HB HC Hstr Hws Hsy Hnode HM1 Hpay Hrun".
      assert (Hm3cs : forall r : mword 5, ucallee_saved_idx r = true ->
                Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s4_idx ->
                Regidx r <> Regidx s5_idx -> m3 !!! Regidx r = m !!! Regidx r)
        by (intros r Hr H1 H4 H5; rewrite (Hm3 r Hr H1 H4); exact (Hm1cs r Hr H5)).
      iDestruct (ushp_redirs_res_of rs' dv Pex with "Hpx Hsy Hpay") as "[Hres Hback]".
      iApply (IH h3 m3 dq dw dv t1 ps s0 len s2 n fin f fp
                (mword_of_int (s0 + Z.of_nat q)) (mword_of_int (s0 + Z.of_nat e))
                UM1 UM' (8 + nn')%nat
                Href' Hchain' (fun _ => Hsc) (fun _ => ltac:(lia))
                Hs2le Hs0 Hs64 Hps0 Hps8 Hpssz Hfp8 Hfplo Hfphi
                ltac:(rewrite (Hm3cs s0_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)); exact Rs0)
                ltac:(rewrite (Hm3cs s2_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)); exact Rs2)
                ltac:(rewrite (Hm3cs s3_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)); exact Rs3)
                Hs4_3
                ltac:(rewrite (Hm3cs s6_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)); exact Rs6)
                ltac:(rewrite (Hm3cs s7_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)); exact Rs7)
                ltac:(rewrite (Hm3cs s8_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)); exact Rs8)
                ltac:(rewrite (Hm3cs s9_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)); exact Rs9)
                with "Hcode Hro HM1 Hres Hcur HB HC Hstr Hws Hrun").
      iIntros (t h4 m4 wB' wC') "%Hm4 %Hs4_4 Hcur HB HC Hstr Hws Hat HM' Hres Hrun".
      iDestruct ("Hback" with "Hres") as "[Hsy Hpay]".
      iApply ("Hcont" $! t h4 m4 wB' wC'
                with "[%] [%] Hcur HB HC Hstr Hws [Hnode Hat] HM' [Hsy Hpay] Hrun").
      + intros r Hr H1 H4 H5. rewrite (Hm4 r Hr H1 H4 H5). exact (Hm3cs r Hr H1 H4 H5).
      + exact Hs4_4.
      + cbn [ushp_redirs_at rr_q rr_eq rr_mode rr_fd]. unfold rr_mode_gt.
        iExists t1. iFrame "Hnode Hat".
      + cbn [ushp_redirs_res]. iFrame "Hsy Hpay Hpx".
  Qed.


  (* ===================================================================== *)
  (* (6) parseredirs, THE WHOLE FUNCTION, AT THE REFERENCE                  *)
  (* ===================================================================== *)
  (* The prologue (fourteen words, eleven spills, the frame pointer at its
     value), the loop, the epilogue.  [ref_redirs len f n off [] = Some
     (rs, fin)] is the whole shape premise: the code returns the chain of
     [length rs] REDIR nodes around [cmd] and leaves the cursor at [fin].
     Whatever a turn needs is guarded by [rs <> []] or bundled in
     [ushp_redirs_res rs], so at [rs = []] this is exactly the landed
     zero-turn statement. *)
  Lemma wp_ref_parseredirs {Pex : iProp Σ} (h : CpuId) (m : regfile)
      (dq dw dv : dfrac) (cmd ps s0 : Z) (len off n fin : nat)
      (f : nat -> bv 8) (rs : list rredir) (UM UM' : iProp Σ)
      (w0 : mword 64) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int cmd ->
    m !!! Regidx a1_idx = mword_of_int ps ->
    m !!! Regidx a2_idx = mword_of_int (s0 + Z.of_nat len) ->
    (off <= len)%nat ->
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    ref_redirs len f n off [] = Some (rs, fin) ->
    ushp_malloc_chain (length rs) UM UM' ->
    (rs <> [] -> ref_sym_scope len f) ->
    (rs <> [] -> (8 <= nn)%nat) ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    UM -∗
    ushp_redirs_res rs dv Pex -∗
    uword γd ps w0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    urun N h m (mword_of_int ShSyms.parseredirs) (14 + (8 + (2 + nn))) -∗
    (∀ (t : Z),
       uword γd ps (mword_of_int (s0 + Z.of_nat fin)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ushp_redirs_at s0 t cmd rs -∗
       UM' -∗
       ushp_redirs_res rs dv Pex -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int t ⌝ -∗
         urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (14 + (8 + (2 + nn))) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Ha1 Ha2 Hoffle Hw0 Href Hchain Hscope Hnn Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode #Hro HM Hres Hcur Hstr Hws Hrun Hcont".
    rewrite shpp_parseredirs.
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | 1%nat => m !!! Regidx s0_idx
                   | 2%nat => m !!! Regidx s1_idx
                   | 3%nat => m !!! Regidx s2_idx
                   | 4%nat => m !!! Regidx s3_idx
                   | 5%nat => m !!! Regidx s4_idx
                   | 6%nat => m !!! Regidx s5_idx
                   | 7%nat => m !!! Regidx s6_idx
                   | 8%nat => m !!! Regidx s7_idx
                   | 9%nat => m !!! Regidx s8_idx
                   | _ => m !!! Regidx s9_idx end).
    (* ---- 0x4ac..0x4c4  the prologue: k = 14, eleven spills ---- *)
    iApply (wp_kshp_frame_pro_at 14 3 [(ra_idx, mword_of_int 13 : mword 6);
               (s0_idx, mword_of_int 12 : mword 6);
               (s1_idx, mword_of_int 11 : mword 6);
               (s2_idx, mword_of_int 10 : mword 6);
               (s3_idx, mword_of_int 9 : mword 6);
               (s4_idx, mword_of_int 8 : mword 6);
               (s5_idx, mword_of_int 7 : mword 6);
               (s6_idx, mword_of_int 6 : mword 6);
               (s7_idx, mword_of_int 5 : mword 6);
               (s8_idx, mword_of_int 4 : mword 6);
               (s9_idx, mword_of_int 3 : mword 6)] 0x4ac
              (fun i : nat => match i with
                              | 0%nat => 0x4ae | 1%nat => 0x4b0
                              | 2%nat => 0x4b2 | 3%nat => 0x4b4
                              | 4%nat => 0x4b6 | 5%nat => 0x4b8
                              | 6%nat => 0x4ba | 7%nat => 0x4bc
                              | 8%nat => 0x4be | 9%nat => 0x4c0
                              | 10%nat => 0x4c2 | 11%nat => 0x4c4
                              | _ => 0x4c6 end)
              (mword_of_int 57 : mword 6) (mword_of_int 28 : mword 8)
              vals (8 + (2 + nn)) h m
              ltac:(cbn [length]; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(cbn; lia)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| [| [| [| [| [| i
                      ]]]]]]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| [| [| [| [| [| i
                      ]]]]]]]]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ vm_compute; discriminate | reflexivity ] ]))
              with "[] [] [] Hrun").
    { iApply (uis_shp_4ac with "Hcode"). }
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_4ae with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4b0 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4b2 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4b4 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4b6 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4b8 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4ba with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4bc with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4be with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4c0 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_4c2 with "Hcode") | done ]. }
    { iApply (uis_shp_4c4 with "Hcode"). }
    iIntros (h1) "%Hal8 %Hlo %Hhi Hsl Hloc Hrun". cbn [length].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 14))).
    set (v := add_vec spn
                (sign_extend' 64 (caddi4spn_imm (mword_of_int 28 : mword 8)))).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    set (m2 := <[Regidx s0_idx := regval_into_reg v]> m1).
    (* THE FRAME POINTER IS THE CALLER'S sp, and this walk needs to know it:
       its two locals -- the [q] and [eq] gettoken writes -- are addressed
       as [s0-104] and [s0-112], and what it OWNS is the stack at [sp0]. *)
    assert (Hspu : uint spn = uint sp0 - 112).
    { unfold spn. rewrite !uint_unsigned.
      replace (- (8 * Z.of_nat 14)) with (-112) by lia.
      exact (uv_avi_neg sp0 112 ltac:(lia)
               ltac:(rewrite <- uint_unsigned; lia)). }
    assert (E112 : (sign_extend' 64 (caddi4spn_imm (mword_of_int 28 : mword 8))
                    : mword 64) = mword_of_int 112)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hv : v = sp0).
    { unfold v. rewrite E112.
      change (add_vec spn (mword_of_int 112)) with (add_vec_int spn 112).
      apply bv_eq.
      rewrite (uv_avi_pos spn 112 ltac:(lia)
                 ltac:(rewrite <- uint_unsigned; lia)).
      rewrite <- !uint_unsigned. lia. }
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    assert (Hsp2 : m2 !!! Regidx csp_rs1 = spn).
    { rewrite (Hm2 csp_rs1 ltac:(vm_compute; discriminate)).
      exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)). }
    (* ---- 0x4c6  c.mv s4,a0 ---- *)
    iApply (wp_uk_cmv N h1 m2 (mword_of_int 0x4c6) s4_idx a0_idx
              (mword_of_int cmd) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val cmd))
              with "[] Hrun").
    { iApply (uis_shp_4c6 with "Hcode"). }
    iIntros (h2) "Hrun".
    set (m3 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int cmd : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx s4_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx s4_idx) (Regidx q) _ Hq)).
    (* ---- 0x4c8  c.mv s3,a1 ---- *)
    iApply (wp_uk_cmv N h2 m3 (mword_of_int 0x4c8) s3_idx a1_idx
              (mword_of_int ps) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate))
                      (Hm2 a1_idx ltac:(vm_compute; discriminate))
                      (Hm1 a1_idx ltac:(vm_compute; discriminate)) Ha1;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_4c8 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m4 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx s3_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx s3_idx) (Regidx q) _ Hq)).
    (* ---- 0x4ca  c.mv s2,a2 ---- *)
    iApply (wp_uk_cmv N h3 m4 (mword_of_int 0x4ca) s2_idx a2_idx
              (mword_of_int (s0 + Z.of_nat len)) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm4 a2_idx ltac:(vm_compute; discriminate))
                      (Hm3 a2_idx ltac:(vm_compute; discriminate))
                      (Hm2 a2_idx ltac:(vm_compute; discriminate))
                      (Hm1 a2_idx ltac:(vm_compute; discriminate)) Ha2;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_4ca with "Hcode"). }
    iIntros (h4) "Hrun".
    set (m5 := <[Regidx s2_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m4).
    assert (Hm5 : forall q : mword 5, Regidx q <> Regidx s2_idx ->
                    m5 !!! Regidx q = m4 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m4 (Regidx s2_idx) (Regidx q) _ Hq)).
    (* ---- 0x4cc  auipc s6,0x1 ---- *)
    iApply (wp_uk_auipc N h4 m5 (mword_of_int 0x4cc)
              (mword_of_int 1 : mword 20) s6_idx
              (mword_of_int 0x14cc) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_4cc with "Hcode"). }
    iIntros (h5) "Hrun".
    set (m6 := <[Regidx s6_idx
                 := regval_into_reg (mword_of_int 0x14cc : mword 64)]> m5).
    assert (Hm6 : forall q : mword 5, Regidx q <> Regidx s6_idx ->
                    m6 !!! Regidx q = m5 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m5 (Regidx s6_idx) (Regidx q) _ Hq)).
    assert (Hs6_6 : m6 !!! Regidx s6_idx = mword_of_int 0x14cc)
      by exact (upd_eq m5 (Regidx s6_idx)
                  (regval_into_reg (mword_of_int 0x14cc : mword 64))).
    (* ---- 0x4d0  addi s6,s6,-476 -- the table base 0x1300 ---- *)
    iApply (wp_uk_addi N h5 m6 (mword_of_int 0x4d0)
              (mword_of_int 3636 : mword 12) s6_idx s6_idx
              (mword_of_int ushp_T_redir) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs6_6; unfold ushp_T_redir;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_4d0 with "Hcode"). }
    iIntros (h6) "Hrun".
    set (m7 := <[Regidx s6_idx
                 := regval_into_reg
                      (mword_of_int ushp_T_redir : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx s6_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx s6_idx) (Regidx q) _ Hq)).
    assert (Hs6_7 : m7 !!! Regidx s6_idx = mword_of_int ushp_T_redir)
      by exact (upd_eq m6 (Regidx s6_idx)
                  (regval_into_reg (mword_of_int ushp_T_redir : mword 64))).
    (* ---- 0x4d4  addi s9,s0,-112 -- &q, dead on this path ---- *)
    iApply (wp_uk_addi N h6 m7 (mword_of_int 0x4d4)
              (mword_of_int 3984 : mword 12) s0_idx s9_idx
              (add_vec (m7 !!! Regidx s0_idx)
                 (sign_extend' 64 (mword_of_int 3984 : mword 12)))
              (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shp_4d4 with "Hcode"). }
    iIntros (h7) "Hrun".
    set (m8 := <[Regidx s9_idx
                 := regval_into_reg
                      (add_vec (m7 !!! Regidx s0_idx)
                         (sign_extend' 64
                            (mword_of_int 3984 : mword 12)))]> m7).
    assert (Hm8 : forall q : mword 5, Regidx q <> Regidx s9_idx ->
                    m8 !!! Regidx q = m7 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m7 (Regidx s9_idx) (Regidx q) _ Hq)).
    (* ---- 0x4d8  addi s8,s0,-104 -- &eq, dead ---- *)
    iApply (wp_uk_addi N h7 m8 (mword_of_int 0x4d8)
              (mword_of_int 3992 : mword 12) s0_idx s8_idx
              (add_vec (m8 !!! Regidx s0_idx)
                 (sign_extend' 64 (mword_of_int 3992 : mword 12)))
              (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shp_4d8 with "Hcode"). }
    iIntros (h8) "Hrun".
    set (m9 := <[Regidx s8_idx
                 := regval_into_reg
                      (add_vec (m8 !!! Regidx s0_idx)
                         (sign_extend' 64
                            (mword_of_int 3992 : mword 12)))]> m8).
    assert (Hm9 : forall q : mword 5, Regidx q <> Regidx s8_idx ->
                    m9 !!! Regidx q = m8 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m8 (Regidx s8_idx) (Regidx q) _ Hq)).
    (* ---- 0x4dc  li s7,97 -- the 'a' the dead arm compares against ---- *)
    iApply (wp_uk_li N h8 m9 (mword_of_int 0x4dc)
              (mword_of_int 97 : mword 12) s7_idx (mword_of_int 97)
              (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(symmetry; exact (ushp_mv_val 97))
              with "[] Hrun").
    { iApply (uis_shp_4dc with "Hcode"). }
    iIntros (h9) "Hrun".
    set (m10 := <[Regidx s7_idx
                  := regval_into_reg (mword_of_int 97 : mword 64)]> m9).
    assert (Hm10 : forall q : mword 5, Regidx q <> Regidx s7_idx ->
                     m10 !!! Regidx q = m9 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m9 (Regidx s7_idx) (Regidx q) _ Hq)).
    (* ---- 0x4e0  c.j 0x502 -- into the loop's GUARD ---- *)
    iApply (wp_uk_cj N h9 m10 (mword_of_int 0x4e0)
              (mword_of_int 17 : mword 11) (mword_of_int 0x502)
              (8 + (2 + nn))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_4e0 with "Hcode"). }
    iIntros (h10) "Hrun".
    (* ---- the loop's registers at the guard ---- *)
    assert (Hs0_m8 : m8 !!! Regidx s0_idx = v).
    { rewrite (Hm8 s0_idx ltac:(vm_compute; discriminate))
              (Hm7 s0_idx ltac:(vm_compute; discriminate))
              (Hm6 s0_idx ltac:(vm_compute; discriminate))
              (Hm5 s0_idx ltac:(vm_compute; discriminate))
              (Hm4 s0_idx ltac:(vm_compute; discriminate))
              (Hm3 s0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m1 (Regidx s0_idx) (regval_into_reg v)). }
    assert (Hs0_m7 : m7 !!! Regidx s0_idx = v).
    { rewrite <- Hs0_m8.
      exact (eq_sym (Hm8 s0_idx ltac:(vm_compute; discriminate))). }
    assert (Hs0_m10 : m10 !!! Regidx s0_idx = sp0).
    { rewrite (Hm10 s0_idx ltac:(vm_compute; discriminate))
              (Hm9 s0_idx ltac:(vm_compute; discriminate)) Hs0_m8.
      exact Hv. }
    assert (Hsp_m10 : m10 !!! Regidx csp_rs1 = spn).
    { rewrite (Hm10 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm9 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm8 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm7 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm6 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm5 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm4 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm3 csp_rs1 ltac:(vm_compute; discriminate)).
      exact Hsp2. }
    assert (Hs2_m10 : m10 !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm10 s2_idx ltac:(vm_compute; discriminate))
              (Hm9 s2_idx ltac:(vm_compute; discriminate))
              (Hm8 s2_idx ltac:(vm_compute; discriminate))
              (Hm7 s2_idx ltac:(vm_compute; discriminate))
              (Hm6 s2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m4 (Regidx s2_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Hs3_m10 : m10 !!! Regidx s3_idx = mword_of_int ps).
    { rewrite (Hm10 s3_idx ltac:(vm_compute; discriminate))
              (Hm9 s3_idx ltac:(vm_compute; discriminate))
              (Hm8 s3_idx ltac:(vm_compute; discriminate))
              (Hm7 s3_idx ltac:(vm_compute; discriminate))
              (Hm6 s3_idx ltac:(vm_compute; discriminate))
              (Hm5 s3_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m3 (Regidx s3_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Hs4_m10 : m10 !!! Regidx s4_idx = mword_of_int cmd).
    { rewrite (Hm10 s4_idx ltac:(vm_compute; discriminate))
              (Hm9 s4_idx ltac:(vm_compute; discriminate))
              (Hm8 s4_idx ltac:(vm_compute; discriminate))
              (Hm7 s4_idx ltac:(vm_compute; discriminate))
              (Hm6 s4_idx ltac:(vm_compute; discriminate))
              (Hm5 s4_idx ltac:(vm_compute; discriminate))
              (Hm4 s4_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s4_idx)
               (regval_into_reg (mword_of_int cmd : mword 64))). }
    assert (Hs6_m10 : m10 !!! Regidx s6_idx = mword_of_int ushp_T_redir).
    { rewrite (Hm10 s6_idx ltac:(vm_compute; discriminate))
              (Hm9 s6_idx ltac:(vm_compute; discriminate))
              (Hm8 s6_idx ltac:(vm_compute; discriminate)).
      exact Hs6_7. }
    assert (Hs7_m10 : m10 !!! Regidx s7_idx = mword_of_int 97)
      by exact (upd_eq m9 (Regidx s7_idx)
                  (regval_into_reg (mword_of_int 97 : mword 64))).
    (* ---- THE TWO LOCALS: [q] at sp0-104 and [eq] at sp0-112 ---- *)
    assert (Hq104 : add_vec v (sign_extend' 64 (mword_of_int 3992 : mword 12))
                    = mword_of_int (uint sp0 - 104)).
    { rewrite Hv.
      assert (E : (sign_extend' 64 (mword_of_int 3992 : mword 12) : mword 64)
                  = mword_of_int (-104))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E.
      change (add_vec sp0 (mword_of_int (-104)))
        with (add_vec_int sp0 (-104)).
      apply bv_eq.
      rewrite (uv_avi_neg sp0 104 ltac:(lia)
                 ltac:(rewrite <- uint_unsigned; lia)).
      rewrite (moi64_unsigned (uint sp0 - 104)) /bv_wrap /bv_modulus.
      rewrite <- uint_unsigned.
      rewrite (Z.mod_small (uint sp0 - 104) (2 ^ Z.of_N 64)
                 ltac:(change (2 ^ Z.of_N 64) with Z64;
                       unfold Z64 in *; lia)).
      reflexivity. }
    assert (Heq112 : add_vec v (sign_extend' 64 (mword_of_int 3984 : mword 12))
                     = mword_of_int (uint sp0 - 112)).
    { rewrite Hv.
      assert (E : (sign_extend' 64 (mword_of_int 3984 : mword 12) : mword 64)
                  = mword_of_int (-112))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E.
      change (add_vec sp0 (mword_of_int (-112)))
        with (add_vec_int sp0 (-112)).
      apply bv_eq.
      rewrite (uv_avi_neg sp0 112 ltac:(lia)
                 ltac:(rewrite <- uint_unsigned; lia)).
      rewrite (moi64_unsigned (uint sp0 - 112)) /bv_wrap /bv_modulus.
      rewrite <- uint_unsigned.
      rewrite (Z.mod_small (uint sp0 - 112) (2 ^ Z.of_N 64)
                 ltac:(change (2 ^ Z.of_N 64) with Z64;
                       unfold Z64 in *; lia)).
      reflexivity. }
    assert (Hs8_m10 : m10 !!! Regidx s8_idx = mword_of_int (uint sp0 - 104)).
    { rewrite (Hm10 s8_idx ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m8 (Regidx s8_idx)
                 (regval_into_reg
                    (add_vec (m8 !!! Regidx s0_idx)
                       (sign_extend' 64 (mword_of_int 3992 : mword 12))))).
      rewrite Hs0_m8. exact Hq104. }
    assert (Hs9_m10 : m10 !!! Regidx s9_idx = mword_of_int (uint sp0 - 112)).
    { rewrite (Hm10 s9_idx ltac:(vm_compute; discriminate))
              (Hm9 s9_idx ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m7 (Regidx s9_idx)
                 (regval_into_reg
                    (add_vec (m7 !!! Regidx s0_idx)
                       (sign_extend' 64 (mword_of_int 3984 : mword 12))))).
      rewrite Hs0_m7. exact Heq112. }
    (* the stack is DEEPER than the frame: [urun]'s own budget says so, and
       the loop needs it because its locals sit BELOW the spill slots. *)
    iDestruct (urun_stack with "Hrun") as %[_ Hroom2].
    rewrite Hsp_m10 Hspu in Hroom2.
    assert (Hdeep : 112 < uint sp0) by lia.
    (* the three local words, out of the frame's tail *)
    set (spl := (mword_of_int (uint sp0 - 8 * Z.of_nat 11) : mword 64)).
    assert (Hsplu : uint spl = uint sp0 - 88)
      by (unfold spl; apply uint_moi; lia).
    set (spb := (mword_of_int (uint sp0 - 112) : mword 64)).
    assert (Hspbu : uint spb = uint sp0 - 112)
      by (unfold spb; apply uint_moi; lia).
    iDestruct (ushp_frame_split spl spb 0
                 [(s10_idx, mword_of_int 0 : mword 6);
                  (s10_idx, mword_of_int 0 : mword 6);
                  (s10_idx, mword_of_int 0 : mword 6)]
                 ltac:(cbn [length]; rewrite Hsplu Hspbu; lia)
                 with "Hloc") as "[Hlocs Hbot]".
    rewrite !big_sepL_cons big_sepL_nil.
    iDestruct "Hlocs" as "[[%wA HA] [[%wB HB] [[%wC HC] _]]]".
    assert (EA : uint spl - 8 * (Z.of_nat 0 + 1) = uint sp0 - 96)
      by (rewrite Hsplu; lia).
    assert (EB : uint spl - 8 * (Z.of_nat 1 + 1) = uint sp0 - 104)
      by (rewrite Hsplu; lia).
    assert (EC : uint spl - 8 * (Z.of_nat 2 + 1) = uint sp0 - 112)
      by (rewrite Hsplu; lia).
    rewrite EA EB EC.
    (* ---- THE LOOP ---- *)
    iApply (wp_kshp_parseredirs_loop rs h10 m10 dq dw dv cmd ps s0 len off n fin f
              sp0 wB wC UM UM' nn Href Hchain Hscope Hnn Hoffle Hs0 Hs64
              Hps0 Hps8 Hpssz Hal8 Hdeep Hhi
              Hs0_m10 Hs2_m10 Hs3_m10 Hs4_m10 Hs6_m10 Hs7_m10 Hs8_m10 Hs9_m10
              with "Hcode Hro HM Hres [Hcur] HB HC Hstr Hws Hrun").
    { rewrite <- Hw0. iExact "Hcur". }
    iIntros (t h' m' wB' wC') "%Hm' %Hs4' Hcur HB HC Hstr Hws Hat HM' Hres Hrun".
    (* ---- 0x574  c.mv a0,s4 -- the tree is the answer ---- *)
    iApply (wp_uk_cmv N h' m' (mword_of_int 0x574) a0_idx s4_idx
              (mword_of_int t) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs4'; symmetry; exact (ushp_mv_val t))
              with "[] Hrun").
    { iApply (uis_shp_574 with "Hcode"). }
    iIntros (he) "Hrun".
    set (me := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int t : mword 64)]> m').
    assert (Hme : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    me !!! Regidx r = m' !!! Regidx r)
      by (intros r Hr; exact (upd_ne m' (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (Hspe : me !!! Regidx csp_rs1 = spn).
    { rewrite (Hme csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm' csp_rs1 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      exact Hsp_m10. }
    (* ---- the two locals go back into the frame ---- *)
    iAssert (ustack γd spl 3) with "[HA HB HC Hbot]" as "Hloc".
    { iApply (ushp_frame_join spl spb 0
                [(s10_idx, mword_of_int 0 : mword 6);
                 (s10_idx, mword_of_int 0 : mword 6);
                 (s10_idx, mword_of_int 0 : mword 6)]
                (fun i : nat =>
                   match i with
                   | 0%nat => wA
                   | 1%nat => wB'
                   | _ => wC' end)
                ltac:(cbn [length]; rewrite Hsplu Hspbu; lia)
                with "[HA HB HC] Hbot").
      rewrite !big_sepL_cons big_sepL_nil.
      rewrite EA EB EC. iFrame "HA HB HC". }
    assert (Hsplu' : uint spl = uint sp0 - 8 * Z.of_nat 11)
      by (rewrite Hsplu; lia).
    (* ---- 0x576..0x58e  the epilogue ---- *)
    iApply (wp_kshp_frame_epi 14 3 [(ra_idx, mword_of_int 13 : mword 6);
               (s0_idx, mword_of_int 12 : mword 6);
               (s1_idx, mword_of_int 11 : mword 6);
               (s2_idx, mword_of_int 10 : mword 6);
               (s3_idx, mword_of_int 9 : mword 6);
               (s4_idx, mword_of_int 8 : mword 6);
               (s5_idx, mword_of_int 7 : mword 6);
               (s6_idx, mword_of_int 6 : mword 6);
               (s7_idx, mword_of_int 5 : mword 6);
               (s8_idx, mword_of_int 4 : mword 6);
               (s9_idx, mword_of_int 3 : mword 6)] (mword_of_int 13 : mword 6)
              (fun i : nat => match i with
                              | 0%nat => 0x576 | 1%nat => 0x578
                              | 2%nat => 0x57a | 3%nat => 0x57c
                              | 4%nat => 0x57e | 5%nat => 0x580
                              | 6%nat => 0x582 | 7%nat => 0x584
                              | 8%nat => 0x586 | 9%nat => 0x588
                              | 10%nat => 0x58a | 11%nat => 0x58c
                              | _ => 0x58e end)
              (mword_of_int 7 : mword 6) sp0 spl vals
              (8 + (2 + nn)) he me
              ltac:(cbn [length]; reflexivity)
              Hal8 ltac:(cbn; lia) Hhi
              Hsplu'
              Hspe
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| [| [| [| [| [| i
                      ]]]]]]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| [| [| [| [| [| i
                      ]]]]]]]]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ unfold unot_sp; vm_compute; discriminate
                              | vm_compute; discriminate ] ]))
              ltac:(reflexivity)
              ltac:(ushp_ne_vm)
              with "Hcode [] [] [] Hsl Hloc Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_576 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_578 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_57a with "Hcode") | ].
      iSplit; [ iApply (uis_shp_57c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_57e with "Hcode") | ].
      iSplit; [ iApply (uis_shp_580 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_582 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_584 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_586 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_588 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_58a with "Hcode") | done ]. }
    { iApply (uis_shp_58c with "Hcode"). }
    { iApply (uis_shp_58e with "Hcode"). }
    iIntros (hf) "Hrun".
    iApply ("Hcont" $! t with "Hcur Hstr Hws Hat HM' Hres [] [] Hrun").
    - iPureIntro.
      apply (ushp_frame_cs _ vals m me sp0 eq_refl).
      + intros i r u Hi.
        destruct i as [| [| [| [| [| [| [| [| [| [| [| i ]]]]]]]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; reflexivity.
      + intros r Hr Hrsp Hmiss.
        rewrite (Hme r (ushp_cs_ne r a0_idx Hr
                          ltac:(vm_compute; reflexivity))).
        rewrite (Hm' r Hr
                   (Hmiss 2%nat s1_idx (mword_of_int 11 : mword 6) eq_refl)
                   (Hmiss 5%nat s4_idx (mword_of_int 8 : mword 6) eq_refl)
                   (Hmiss 6%nat s5_idx (mword_of_int 7 : mword 6) eq_refl)).
        rewrite (Hm10 r (Hmiss 8%nat s7_idx (mword_of_int 5 : mword 6)
                           eq_refl))
                (Hm9 r (Hmiss 9%nat s8_idx (mword_of_int 4 : mword 6)
                          eq_refl))
                (Hm8 r (Hmiss 10%nat s9_idx (mword_of_int 3 : mword 6)
                          eq_refl))
                (Hm7 r (Hmiss 7%nat s6_idx (mword_of_int 6 : mword 6)
                          eq_refl))
                (Hm6 r (Hmiss 7%nat s6_idx (mword_of_int 6 : mword 6)
                          eq_refl))
                (Hm5 r (Hmiss 3%nat s2_idx (mword_of_int 10 : mword 6)
                          eq_refl))
                (Hm4 r (Hmiss 4%nat s3_idx (mword_of_int 9 : mword 6)
                          eq_refl))
                (Hm3 r (Hmiss 5%nat s4_idx (mword_of_int 8 : mword 6)
                          eq_refl))
                (Hm2 r (Hmiss 1%nat s0_idx (mword_of_int 12 : mword 6)
                          eq_refl))
                (Hm1 r Hrsp).
        reflexivity.
    - iPureIntro.
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      apply ushp_spillback_eq.
      + intros _.
        exact (upd_eq m' (Regidx a0_idx)
                 (regval_into_reg (mword_of_int t : mword 64))).
      + intros i r u Hi He.
        destruct i as [| [| [| [| [| [| [| [| [| [| [| i ]]]]]]]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
  Qed.

  (* the same walk with a turn's premises and resources unconditional: the
     shape a caller that always holds them -- parseexec's argument loop --
     consumes.  The budget is the one-turn budget. *)
  Lemma wp_ref_parseredirs_full {Pex : iProp Σ} (h : CpuId) (m : regfile)
      (dq dw dv : dfrac) (cmd ps s0 : Z) (len off n fin : nat)
      (f : nat -> bv 8) (rs : list rredir) (UM UM' : iProp Σ)
      (w0 : mword 64) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int cmd ->
    m !!! Regidx a1_idx = mword_of_int ps ->
    m !!! Regidx a2_idx = mword_of_int (s0 + Z.of_nat len) ->
    (off <= len)%nat ->
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    ref_sym_scope len f ->
    ref_redirs len f n off [] = Some (rs, fin) ->
    ushp_malloc_chain (length rs) UM UM' ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    UM -∗
    □ (Pex -∗ ukn_pay N (-1)) -∗
    Pex -∗
    uword γd ps w0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    urun N h m (mword_of_int ShSyms.parseredirs)
      (14 + (8 + (2 + (8 + nn)))) -∗
    (∀ (t : Z),
       uword γd ps (mword_of_int (s0 + Z.of_nat fin)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
       ushp_redirs_at s0 t cmd rs -∗
       UM' -∗
       Pex -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int t ⌝ -∗
         urun N h' m' (ret_pc (m !!! Regidx ra_idx))
           (14 + (8 + (2 + (8 + nn)))) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Ha1 Ha2 Hoffle Hw0 Hscope Href Hchain Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode #Hro HM #Hpx Hpay Hcur Hstr Hws Hsy Hrun Hcont".
    iDestruct (ushp_redirs_res_of rs dv Pex with "Hpx Hsy Hpay") as "[Hres Hback]".
    iApply (wp_ref_parseredirs h m dq dw dv cmd ps s0 len off n fin f rs UM UM'
              w0 (8 + nn) Ha0 Ha1 Ha2 Hoffle Hw0 Href Hchain
              (fun _ => Hscope) (fun _ => ltac:(lia)) Hs0 Hs64 Hps0 Hps8 Hpssz
              with "Hcode Hro HM Hres Hcur Hstr Hws Hrun").
    iIntros (t) "Hcur Hstr Hws Hat HM' Hres".
    iDestruct ("Hback" with "Hres") as "[Hsy Hpay]".
    iApply ("Hcont" $! t with "Hcur Hstr Hws Hsy Hat HM' Hpay").
  Qed.


  (* ===================================================================== *)
  (* (7) THE GENERAL ZERO-TURN CASE, in the landed spelling                  *)
  (* ===================================================================== *)
  (* What was UkShPipePr.wp_kshp_parseredirs_miss, the weakest of the three
     zero-turn statements: peek's table at 0x1300 does not contain the byte
     at the blank-scanned cursor, said as [ushp_peek_res .. = 0].  It is
     the walk at [rs = []] through the peek bridge. *)
  Lemma wp_kshp_parseredirs_miss (h : CpuId) (m : regfile) (dq dw : dfrac)
      (cmd ps s0 : Z) (len off : nat) (f : nat -> bv 8)
      (w0 : mword 64) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int cmd ->
    m !!! Regidx a1_idx = mword_of_int ps ->
    m !!! Regidx a2_idx = mword_of_int (s0 + Z.of_nat len) ->
    (off <= len)%nat ->
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    ushp_peek_res len f (off + ushp_skipws (len - off) off f)%nat 2
      (ushp_lit ushp_T_redir) = 0 ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps w0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    urun N h m (mword_of_int ShSyms.parseredirs)
      (14 + (8 + (2 + nn))) -∗
    (uword γd ps
       (mword_of_int (s0 + Z.of_nat (off + ushp_skipws (len - off) off f))) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int cmd ⌝ -∗
         urun N h' m' (ret_pc (m !!! Regidx ra_idx))
           (14 + (8 + (2 + nn))) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Ha1 Ha2 Hoffle Hw0 Hpmiss Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode #Hro Hcur Hstr Hws Hrun Hcont".
    iDestruct (ustr_nonul with "Hstr") as %Hnonul.
    assert (Hpk : ref_peek len f off [rb_lt; rb_gt]
                  = (false, (off + ushp_skipws (len - off) off f)%nat)).
    { rewrite (UkShGettoken.ref_peek_ushp len off 2 f (ushp_lit ushp_T_redir)
                 [rb_lt; rb_gt] Hnonul Hoffle ushp_T_redir_tl).
      rewrite Hpmiss. rewrite (bool_decide_eq_false_2 (0 = 1) ltac:(lia)).
      reflexivity. }
    iApply (wp_ref_parseredirs (Pex := emp%I) h m dq dw dq cmd ps s0 len off 1
              (off + ushp_skipws (len - off) off f)%nat f [] emp%I emp%I w0 nn
              Ha0 Ha1 Ha2 Hoffle Hw0 (ref_redirs_of_peek_miss len f 0 off _ [] Hpk)
              eq_refl
              ltac:(intro H; exfalso; exact (H eq_refl))
              ltac:(intro H; exfalso; exact (H eq_refl))
              Hs0 Hs64 Hps0 Hps8 Hpssz
              with "Hcode Hro [] [] Hcur Hstr Hws Hrun").
    { done. }
    { done. }
    iIntros (t) "Hcur Hstr Hws Hat _ _".
    cbn [ushp_redirs_at]. iDestruct "Hat" as %->.
    iApply ("Hcont" with "Hcur Hstr Hws").
  Qed.

End UkShRedirs.
