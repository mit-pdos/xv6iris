(* ===================================================================== *)
(* UkShRedirPr.v -- parseredirs TURNING ONCE, lane SH-PARSE               *)
(* (design/app-file.md SS5.1, deliverable 2).                             *)
(*                                                                        *)
(*   struct cmd *parseredirs(struct cmd *cmd, char **ps, char *es) {      *)
(*     int tok; char *q, *eq;                                            *)
(*     while(peek(ps, es, "<>")) {                                       *)
(*       tok = gettoken(ps, es, 0, 0);                                    *)
(*       if(gettoken(ps, es, &q, &eq) != 'a') panic("missing file ...");  *)
(*       switch(tok) {                                                    *)
(*       case '<': cmd = redircmd(cmd, q, eq, O_RDONLY, 0); break;        *)
(*       case '>': cmd = redircmd(cmd, q, eq, O_WRONLY|O_CREATE|O_TRUNC,  *)
(*                                1); break;                              *)
(*       case '+': ... } }                                                *)
(*     return cmd;  }                                                     *)
(*                                                                        *)
(* [UkShParseRedir.wp_kshp_parseredirs] is this function at ZERO turns:   *)
(* [ushp_no_symbols] refutes the guard at the [c.beqz], so 45 of the 85   *)
(* instructions are never fetched.  On the canonical redirect line        *)
(* ([UkShParseSym.ushs_redir]) the guard is TRUE exactly once, and this   *)
(* file is that walk: the '>' [gettoken], the file-name [gettoken], the   *)
(* switch, [redircmd], and then the SECOND [peek], which answers 0        *)
(* because the cursor has reached the end of the line.                    *)
(*                                                                        *)
(* WHAT THE LANDED WALK COULD NOT SEE, AND WHY THERE IS A SECOND FRAME    *)
(* PROLOGUE HERE.  [UkShParse.wp_kshp_fp] quantifies the new frame        *)
(* pointer UNIVERSALLY -- enough for a walk that never touches its own    *)
(* locals, and not enough here, because [q] and [eq] live at [s0-104] and *)
(* [s0-112] while what the walk OWNS is the stack at [sp0].               *)
(* [wp_kshp_frame_pro_at] is [UkShParse.wp_kshp_frame_pro] with the frame *)
(* pointer at its value; everything else about the prologue is unchanged. *)
(*                                                                        *)
(* TAINT: [ushp_malloc_ok], through [redircmd].                           *)
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
Require Import UkShRedirLex.
Require Import UkShRedirGtk.
Require Import UkShRedirCmd.

Require Import UexecSG.

Section UkShRedirPr.
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

  Local Notation urun_x0 := (UkShParse.urun_x0 N).
  Local Notation ushp_cell := (UkShParseTok.ushp_cell N).
  Local Notation ushp_frame_join := (UkShParse.ushp_frame_join N).
  Local Notation ushp_frame_split := (UkShParse.ushp_frame_split N).
  Local Notation ushp_lit_str := (UkShParseLex.ushp_lit_str N).
  Local Notation ushp_malloc_ty := (UkShParse.ushp_malloc_ty_le N 168).
  Local Notation ushp_tree := (UkShParse.ushp_tree N).
  Local Notation ushp_type_at := (UkShParse.ushp_type_at N).
  Local Notation wp_kshp_frame_epi := (UkShParse.wp_kshp_frame_epi N).
  Local Notation wp_kshp_gettoken_sym := (UkShRedirGtk.wp_kshp_gettoken_sym N).
  Local Notation wp_kshp_peek := (UkShParseLex.wp_kshp_peek N).
  Local Notation wp_kshp_spill := (UkShParse.wp_kshp_spill N).

  Context (UMalloc UMalloc' : iProp Σ).
  Hypothesis ushp_malloc_ok : ushp_malloc_ty UMalloc UMalloc'.

  Local Notation wp_kshp_redircmd :=
    (UkShRedirCmd.wp_kshp_redircmd N UMalloc UMalloc' ushp_malloc_ok).
  Local Notation wp_kshp_redircmd_n :=
    (UkShRedirCmd.wp_kshp_redircmd_n N UMalloc UMalloc' ushp_malloc_ok).
  Local Notation ushp_redir_node := (UkShRedirCmd.ushp_redir_node N).
  Local Notation ushp_redir_close := (UkShRedirCmd.ushp_redir_close N).

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


  (* ---- the peek that MISSES, at the premise it uses -------------------- *)
  (* [UkShParseLex.ushp_peek_res_sym] takes [ushp_no_symbols] over the whole
     line to say a peek for a table of symbol bytes answers 0.  It only ever
     looks at the byte AT THE CURSOR, and on a redirect line that byte is
     symbol-free everywhere except at the one '>'.  So this is the same
     three-line computation at the local premise. *)
  Lemma ushs_peek_res_nsym (len : nat) (f : nat -> bv 8) (k tlen : nat)
      (base : Z) :
    ((k < len)%nat -> ushp_is_sym (f k) = false) ->
    ushp_lit_sym base tlen = true ->
    ushp_peek_res len f k tlen (ushp_lit base) = 0.
  Proof using .
    intros Hnos Hsym. rewrite /ushp_peek_res.
    destruct (bool_decide (k < len)%nat) eqn:Hk; [ | reflexivity ].
    apply bool_decide_eq_true in Hk.
    rewrite (ushp_find_none tlen 0%nat (ushp_lit base) (f k)).
    - reflexivity.
    - intros j Hj He.
      rewrite /ushp_lit_sym forallb_forall in Hsym.
      specialize (Hsym j ltac:(apply in_seq; lia)).
      rewrite He (Hnos Hk) in Hsym. discriminate.
  Qed.

  (* ===================================================================== *)
  (* §11 parseredirs @0x4ac, ONE TURN.                                      *)
  (*                                                                       *)
  (* The premise is the canonical redirect of design/app-file.md SS5.1: the *)
  (* line's ONE symbol byte is a '>' at [p], the blank scan from the        *)
  (* cursor lands exactly on it, and the file name is the run [[p+2, e)].   *)
  (* What comes back is the REDIR node over the caller's tree, with the     *)
  (* file name's two boundaries as the node's [q] / [eq], mode 0x601        *)
  (* (O_WRONLY|O_CREATE|O_TRUNC) and fd 1 -- the two constants sh's '>'     *)
  (* arm passes -- and the cursor at the end of the line, which is what     *)
  (* makes the SECOND [peek] answer 0 and the loop stop.                    *)
  (*                                                                       *)
  (* THE BUDGET IS TEN WORDS DEEPER than the landed zero-turn walk's: the   *)
  (* turn calls [redircmd], and [redircmd] calls [malloc].                  *)
  (* ===================================================================== *)

  Lemma wp_kshp_parseredirs_gtn {Pex : iProp Σ} (h : CpuId) (m : regfile)
      (dq dw dv : dfrac) (cmd ps s0 : Z) (len off p e : nat)
      (f : nat -> bv 8) (Sub : iProp Σ) (w0 : mword 64) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int cmd ->
    m !!! Regidx a1_idx = mword_of_int ps ->
    m !!! Regidx a2_idx = mword_of_int (s0 + Z.of_nat len) ->
    (off <= len)%nat ->
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    ushs_redir len f p e ->
    (off + ushp_skipws (len - off) off f)%nat = p ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    UMalloc -∗
    □ (Pex -∗ ukn_pay N (-1)) -∗
    Pex -∗
    Sub -∗
    uword γd ps w0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    urun N h m (mword_of_int ShSyms.parseredirs)
      (14 + (8 + (2 + (8 + nn)))) -∗
    (∀ (t : Z),
       uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
       ushp_redir_node s0 t cmd (S (S p)) e 1537 1 -∗
       Sub -∗
       UMalloc' -∗
       Pex -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int t ⌝ -∗
         urun N h' m' (ret_pc (m !!! Regidx ra_idx))
           (14 + (8 + (2 + (8 + nn)))) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using ushp_malloc_ok.
    intros Ha0 Ha1 Ha2 Hoffle Hw0 Hred Hp Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode #Hro HM #Hpx Hpay Hsub Hcur Hstr Hws Hsy Hrun Hcont".
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
              vals (8 + (2 + (8 + nn))) h m
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
              (mword_of_int cmd) (8 + (2 + (8 + nn)))
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
              (mword_of_int ps) (8 + (2 + (8 + nn)))
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
              (mword_of_int (s0 + Z.of_nat len)) (8 + (2 + (8 + nn)))
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
              (mword_of_int 0x14cc) (8 + (2 + (8 + nn)))
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
    (* ---- 0x4d0  addi s6,s6,-460 -- the table base 0x1300 ---- *)
    iApply (wp_uk_addi N h5 m6 (mword_of_int 0x4d0)
              (mword_of_int 3636 : mword 12) s6_idx s6_idx
              (mword_of_int ushp_T_redir) (8 + (2 + (8 + nn)))
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
              (8 + (2 + (8 + nn)))
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
              (8 + (2 + (8 + nn)))
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
              (8 + (2 + (8 + nn)))
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
              (8 + (2 + (8 + nn)))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_4e0 with "Hcode"). }
    iIntros (h10) "Hrun".
    (* ---- 0x502  li s5,60 -- the '<' the dead switch compares against ---- *)
    iApply (wp_uk_li N h10 m10 (mword_of_int 0x502)
              (mword_of_int 60 : mword 12) s5_idx (mword_of_int 60)
              (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(symmetry; exact (ushp_mv_val 60))
              with "[] Hrun").
    { iApply (uis_shp_502 with "Hcode"). }
    iIntros (h11) "Hrun".
    set (m11 := <[Regidx s5_idx
                  := regval_into_reg (mword_of_int 60 : mword 64)]> m10).
    assert (Hm11 : forall q : mword 5, Regidx q <> Regidx s5_idx ->
                     m11 !!! Regidx q = m10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m10 (Regidx s5_idx) (Regidx q) _ Hq)).
    (* ---- 0x506  c.mv a2,s6 ---- *)
    assert (Hs6_11 : m11 !!! Regidx s6_idx = mword_of_int ushp_T_redir).
    { rewrite (Hm11 s6_idx ltac:(vm_compute; discriminate))
              (Hm10 s6_idx ltac:(vm_compute; discriminate))
              (Hm9 s6_idx ltac:(vm_compute; discriminate))
              (Hm8 s6_idx ltac:(vm_compute; discriminate)). exact Hs6_7. }
    iApply (wp_uk_cmv N h11 m11 (mword_of_int 0x506) a2_idx s6_idx
              (mword_of_int ushp_T_redir) (8 + (2 + (8 + nn)))
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
              (Hm11 s2_idx ltac:(vm_compute; discriminate))
              (Hm10 s2_idx ltac:(vm_compute; discriminate))
              (Hm9 s2_idx ltac:(vm_compute; discriminate))
              (Hm8 s2_idx ltac:(vm_compute; discriminate))
              (Hm7 s2_idx ltac:(vm_compute; discriminate))
              (Hm6 s2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m4 (Regidx s2_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    iApply (wp_uk_cmv N h12 m12 (mword_of_int 0x508) a1_idx s2_idx
              (mword_of_int (s0 + Z.of_nat len)) (8 + (2 + (8 + nn)))
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
              (Hm11 s3_idx ltac:(vm_compute; discriminate))
              (Hm10 s3_idx ltac:(vm_compute; discriminate))
              (Hm9 s3_idx ltac:(vm_compute; discriminate))
              (Hm8 s3_idx ltac:(vm_compute; discriminate))
              (Hm7 s3_idx ltac:(vm_compute; discriminate))
              (Hm6 s3_idx ltac:(vm_compute; discriminate))
              (Hm5 s3_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m3 (Regidx s3_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    iApply (wp_uk_cmv N h13 m13 (mword_of_int 0x50a) a0_idx s3_idx
              (mword_of_int ps) (8 + (2 + (8 + nn)))
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
              (mword_of_int 0x448) (mword_of_int 0x510) (8 + (2 + (8 + nn)))
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
    (* ---- peek(ps, es, the two redirection bytes) ---- *)
    iApply (wp_kshp_peek h15 m15 dq dw true DfracDiscarded ps s0
              ushp_T_redir len off 2 f (ushp_lit ushp_T_redir)
              (mword_of_int (s0 + Z.of_nat off)) (8 + nn)
              Ha0_15 Ha1_15 Ha2_15 Hoffle eq_refl Hs0 Hs64
              ltac:(unfold ushp_T_redir; lia)
              ltac:(unfold ushp_T_redir, Z64; lia) Hps0 Hps8 Hpssz
              with "Hcode [Hcur] Hstr Hws [] Hrun").
    { rewrite <- Hw0. iExact "Hcur". }
    { iApply (ushp_lit_str ushp_T_redir 2 DfracDiscarded
                ushp_T_redir_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Hcur Hstr Hws _" (h16 n0) "%Hcs %Ha0n0 Hrun".
    rewrite Eret.
    rewrite Hp in Ha0n0.
    rewrite (ushp_peek_redir_hit len f p (ushs_redir_lt len f p e Hred)
               (ushs_redir_gt len f p e Hred)) in Ha0n0.
    (* the cursor cell the peek left, read at the '>' it landed on *)
    rewrite Hp.
    (* ---- 0x510  c.beqz a0 -- NOT taken: the guard is true ONCE ---- *)
    iApply (wp_uk_cbeqz N h16 n0 (mword_of_int 0x510)
              (mword_of_int 50 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              false (mword_of_int 0x574) (8 + (2 + (8 + nn)))
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0n0; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_510 with "Hcode"). }
    rewrite (ushp_pc_step 0x510 2). iIntros (h17) "Hrun".
    (* ---- what the loop body sees, once, in the callee-saved file ---- *)
    assert (Hthru15_11 : forall r : mword 5,
              Regidx r <> Regidx ra_idx -> Regidx r <> Regidx a0_idx ->
              Regidx r <> Regidx a1_idx -> Regidx r <> Regidx a2_idx ->
              m15 !!! Regidx r = m11 !!! Regidx r).
    { intros r H1 H2 H3 H4.
      rewrite (Hm15 r H1) (Hm14 r H2) (Hm13 r H3) (Hm12 r H4). reflexivity. }
    assert (Hthru11_2 : forall r : mword 5,
              Regidx r <> Regidx s5_idx -> Regidx r <> Regidx s7_idx ->
              Regidx r <> Regidx s8_idx -> Regidx r <> Regidx s9_idx ->
              Regidx r <> Regidx s6_idx -> Regidx r <> Regidx s2_idx ->
              Regidx r <> Regidx s3_idx -> Regidx r <> Regidx s4_idx ->
              m11 !!! Regidx r = m2 !!! Regidx r).
    { intros r H5 H7 H8 H9 H6 Hq2 Hq3 Hq4.
      rewrite (Hm11 r H5) (Hm10 r H7) (Hm9 r H8) (Hm8 r H9) (Hm7 r H6)
              (Hm6 r H6) (Hm5 r Hq2) (Hm4 r Hq3) (Hm3 r Hq4). reflexivity. }
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
    assert (Hs0_n0 : n0 !!! Regidx s0_idx = v).
    { rewrite (Hcs s0_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hthru15_11 s0_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      rewrite (Hthru11_2 s0_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq m1 (Regidx s0_idx) (regval_into_reg v)). }
    assert (Hsp_n0 : n0 !!! Regidx csp_rs1 = spn).
    { rewrite (Hcs csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite (Hthru15_11 csp_rs1 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      rewrite (Hthru11_2 csp_rs1 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      rewrite (Hm2 csp_rs1 ltac:(vm_compute; discriminate)).
      exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)). }
    (* the stack is DEEPER than the frame: [urun]'s own budget says so, and
       this walk needs it because its locals sit BELOW the spill slots. *)
    iDestruct (urun_stack with "Hrun") as %[_ Hroom2].
    rewrite Hsp_n0 Hspu in Hroom2.
    assert (Hdeep : 256 <= uint sp0) by lia.
    assert (Hs2_n0 : n0 !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hcs s2_idx ltac:(vm_compute; reflexivity))
              (Hm15 s2_idx ltac:(vm_compute; discriminate))
              (Hm14 s2_idx ltac:(vm_compute; discriminate))
              (Hm13 s2_idx ltac:(vm_compute; discriminate)).
      exact Hs2_12. }
    assert (Hs3_n0 : n0 !!! Regidx s3_idx = mword_of_int ps).
    { rewrite (Hcs s3_idx ltac:(vm_compute; reflexivity))
              (Hm15 s3_idx ltac:(vm_compute; discriminate))
              (Hm14 s3_idx ltac:(vm_compute; discriminate)).
      exact Hs3_13. }
    assert (Hs4_n0 : n0 !!! Regidx s4_idx = mword_of_int cmd).
    { rewrite (Hcs s4_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hthru15_11 s4_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      rewrite (Hm11 s4_idx ltac:(vm_compute; discriminate))
              (Hm10 s4_idx ltac:(vm_compute; discriminate))
              (Hm9 s4_idx ltac:(vm_compute; discriminate))
              (Hm8 s4_idx ltac:(vm_compute; discriminate))
              (Hm7 s4_idx ltac:(vm_compute; discriminate))
              (Hm6 s4_idx ltac:(vm_compute; discriminate))
              (Hm5 s4_idx ltac:(vm_compute; discriminate))
              (Hm4 s4_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s4_idx)
               (regval_into_reg (mword_of_int cmd : mword 64))). }
    assert (Hs5_n0 : n0 !!! Regidx s5_idx = mword_of_int 60).
    { rewrite (Hcs s5_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hthru15_11 s5_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq m10 (Regidx s5_idx)
               (regval_into_reg (mword_of_int 60 : mword 64))). }
    assert (Hs6_n0 : n0 !!! Regidx s6_idx = mword_of_int ushp_T_redir).
    { rewrite (Hcs s6_idx ltac:(vm_compute; reflexivity))
              (Hm15 s6_idx ltac:(vm_compute; discriminate))
              (Hm14 s6_idx ltac:(vm_compute; discriminate))
              (Hm13 s6_idx ltac:(vm_compute; discriminate))
              (Hm12 s6_idx ltac:(vm_compute; discriminate)).
      exact Hs6_11. }
    assert (Hs7_n0 : n0 !!! Regidx s7_idx = mword_of_int 97).
    { rewrite (Hcs s7_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hthru15_11 s7_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      rewrite (Hm11 s7_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m9 (Regidx s7_idx)
               (regval_into_reg (mword_of_int 97 : mword 64))). }
    assert (Hs8_n0 : n0 !!! Regidx s8_idx
                     = add_vec v (sign_extend' 64
                                    (mword_of_int 3992 : mword 12))).
    { rewrite (Hcs s8_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hthru15_11 s8_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      rewrite (Hm11 s8_idx ltac:(vm_compute; discriminate))
              (Hm10 s8_idx ltac:(vm_compute; discriminate)).
      rewrite <- Hs0_m8.
      exact (upd_eq m8 (Regidx s8_idx)
               (regval_into_reg
                  (add_vec (m8 !!! Regidx s0_idx)
                     (sign_extend' 64 (mword_of_int 3992 : mword 12))))). }
    assert (Hs9_n0 : n0 !!! Regidx s9_idx
                     = add_vec v (sign_extend' 64
                                    (mword_of_int 3984 : mword 12))).
    { rewrite (Hcs s9_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hthru15_11 s9_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      rewrite (Hm11 s9_idx ltac:(vm_compute; discriminate))
              (Hm10 s9_idx ltac:(vm_compute; discriminate))
              (Hm9 s9_idx ltac:(vm_compute; discriminate)).
      rewrite <- Hs0_m7.
      exact (upd_eq m7 (Regidx s9_idx)
               (regval_into_reg
                  (add_vec (m7 !!! Regidx s0_idx)
                     (sign_extend' 64 (mword_of_int 3984 : mword 12))))). }
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
    rewrite Hq104 in Hs8_n0. rewrite Heq112 in Hs9_n0.
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
    (* the two cells' address hygiene, once *)
    assert (Hqok : 0 < uint sp0 - 104 /\ (uint sp0 - 104) mod 8 = 0
                   /\ uint sp0 - 104 + 8 < Z64).
    { split; [ lia | ].
      split; [ | lia ].
      rewrite Zminus_mod Hal8.
      assert (E : (104:Z) mod 8 = 0) by reflexivity. rewrite E. reflexivity. }
    assert (Heqok : 0 < uint sp0 - 112 /\ (uint sp0 - 112) mod 8 = 0
                    /\ uint sp0 - 112 + 8 < Z64).
    { split; [ lia | ].
      split; [ | lia ].
      rewrite Zminus_mod Hal8.
      assert (E : (112:Z) mod 8 = 0) by reflexivity. rewrite E. reflexivity. }
    (* the two 12-bit immediates this arm loads, as 64-bit values *)
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
    (* the LINE's two gettoken facts, at the cursor the peek left *)
    assert (Hgtok : ushs_gt_ok len f) by exact (ushs_gt_ok_redir len f p e Hred).
    assert (HK1 : (p + ushp_skipws (len - p) p f)%nat = p)
      by (rewrite (ushs_skipws_at_gt len f p e (len - p) Hred); lia).
    assert (HK2 : (S (S p) + ushp_skipws (len - S (S p)) (S (S p)) f)%nat
                  = S (S p)).
    { rewrite (ushp_skipws_stop (len - S (S p)) (S (S p)) f
                 (proj1 (ushs_redir_file_byte len f p e (S (S p)) Hred
                           ltac:(destruct Hred as (_ & _ & _ & _ & H1 & _); lia)))).
      lia. }
    (* ---- 0x512  c.li a3,0  -- the FIRST gettoken passes no out params -- *)
    iApply (wp_uk_cli N h17 n0 (mword_of_int 0x512)
              (mword_of_int 0 : mword 6) a3_idx (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_512 with "Hcode"). }
    rewrite (ushp_pc_step 0x512 2). iIntros (h18) "Hrun".
    set (r1 := <[Regidx a3_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 0 : mword 6)
                       : mword 64)]> n0).
    assert (Hr1 : forall r : mword 5, Regidx r <> Regidx a3_idx ->
                    r1 !!! Regidx r = n0 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n0 (Regidx a3_idx) (Regidx r) _ Hr)).
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
                      (Hr1 s2_idx ltac:(vm_compute; discriminate)) Hs2_n0;
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
                      (Hr1 s3_idx ltac:(vm_compute; discriminate)) Hs3_n0;
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
              r5 !!! Regidx r = n0 !!! Regidx r).
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
      rewrite (upd_eq n0 (Regidx a3_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64))).
      exact Ezero. }
    assert (Eret1 : ret_pc (r5 !!! Regidx ra_idx) = mword_of_int 0x51e).
    { rewrite (upd_eq r4 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x51e : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    rewrite <- shpp_gettoken.
    (* ---- gettoken(ps, es, 0, 0) -- it answers '>' ---- *)
    iApply (wp_kshp_gettoken_sym h22 r5 dq dw dv ps 0 0 s0 len p f
              (mword_of_int (s0 + Z.of_nat p)) (mword_of_int 0)
              (mword_of_int 0) (8 + nn)
              Ea0_r5 Ea1_r5 Ea2_r5 Ea3_r5
              ltac:(exact (Nat.lt_le_incl _ _ (ushs_redir_lt len f p e Hred)))
              eq_refl Hgtok Hs0 Hs64 Hps0 Hps8 Hpssz
              with "Hcode Hcur [] [] Hstr Hws Hsy Hrun").
    { iLeft. iPureIntro. reflexivity. }
    { iLeft. iPureIntro. reflexivity. }
    iIntros "Hcur _ _ Hstr Hws Hsy" (h23 g0) "%Hcsg0 %Ha0g0 Hrun".
    rewrite Eret1.
    rewrite HK1 in Ha0g0. rewrite HK1.
    rewrite (ushs_gettok_res_gt len f p e Hred) in Ha0g0.
    rewrite (ushs_gettok_fin_gt len f p e Hred).
    assert (Hg0cs : forall r : mword 5, ucallee_saved_idx r = true ->
              g0 !!! Regidx r = n0 !!! Regidx r)
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
              (mword_of_int (uint sp0 - 112)) (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hr6 s9_idx ltac:(vm_compute; discriminate))
                      (Hg0cs s9_idx ltac:(vm_compute; reflexivity)) Hs9_n0;
                    symmetry; exact (ushp_mv_val (uint sp0 - 112)))
              with "[] Hrun").
    { iApply (uis_shp_520 with "Hcode"). }
    rewrite (ushp_pc_step 0x520 2). iIntros (h25) "Hrun".
    set (r7 := <[Regidx a3_idx
                 := regval_into_reg
                      (mword_of_int (uint sp0 - 112) : mword 64)]> r6).
    assert (Hr7 : forall r : mword 5, Regidx r <> Regidx a3_idx ->
                    r7 !!! Regidx r = r6 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r6 (Regidx a3_idx) (Regidx r) _ Hr)).
    (* ---- 0x522  c.mv a2,s8  --  &q ---- *)
    iApply (wp_uk_cmv N h25 r7 (mword_of_int 0x522) a2_idx s8_idx
              (mword_of_int (uint sp0 - 104)) (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hr7 s8_idx ltac:(vm_compute; discriminate))
                      (Hr6 s8_idx ltac:(vm_compute; discriminate))
                      (Hg0cs s8_idx ltac:(vm_compute; reflexivity)) Hs8_n0;
                    symmetry; exact (ushp_mv_val (uint sp0 - 104)))
              with "[] Hrun").
    { iApply (uis_shp_522 with "Hcode"). }
    rewrite (ushp_pc_step 0x522 2). iIntros (h26) "Hrun".
    set (r8 := <[Regidx a2_idx
                 := regval_into_reg
                      (mword_of_int (uint sp0 - 104) : mword 64)]> r7).
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
                      (Hg0cs s2_idx ltac:(vm_compute; reflexivity)) Hs2_n0;
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
                      (Hg0cs s3_idx ltac:(vm_compute; reflexivity)) Hs3_n0;
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
              Regidx r <> Regidx s1_idx -> r11 !!! Regidx r = n0 !!! Regidx r).
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
    assert (Fa2 : r11 !!! Regidx a2_idx = mword_of_int (uint sp0 - 104)).
    { rewrite (Hr11 a2_idx ltac:(vm_compute; discriminate))
              (Hr10 a2_idx ltac:(vm_compute; discriminate))
              (Hr9 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq r7 (Regidx a2_idx)
               (regval_into_reg
                  (mword_of_int (uint sp0 - 104) : mword 64))). }
    assert (Fa3 : r11 !!! Regidx a3_idx = mword_of_int (uint sp0 - 112)).
    { rewrite (Hr11 a3_idx ltac:(vm_compute; discriminate))
              (Hr10 a3_idx ltac:(vm_compute; discriminate))
              (Hr9 a3_idx ltac:(vm_compute; discriminate))
              (Hr8 a3_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq r6 (Regidx a3_idx)
               (regval_into_reg
                  (mword_of_int (uint sp0 - 112) : mword 64))). }
    assert (Eret2 : ret_pc (r11 !!! Regidx ra_idx) = mword_of_int 0x52c).
    { rewrite (upd_eq r10 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x52c : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    rewrite <- shpp_gettoken.
    (* ---- gettoken(ps, es, &q, &eq) -- the FILE NAME, an ordinary token - *)
    iApply (wp_kshp_gettoken_sym h29 r11 dq dw dv ps
              (uint sp0 - 104) (uint sp0 - 112) s0 len (S (S p)) f
              (mword_of_int (s0 + Z.of_nat (S (S p)))) wB wC (8 + nn)
              Fa0 Fa1 Fa2 Fa3
              ltac:(destruct Hred as (_ & _ & _ & _ & H1 & H2 & _); lia)
              eq_refl Hgtok Hs0 Hs64 Hps0 Hps8 Hpssz
              with "Hcode Hcur [HB] [HC] Hstr Hws Hsy Hrun").
    { iRight. iSplitR; [ iPureIntro; exact Hqok | iExact "HB" ]. }
    { iRight. iSplitR; [ iPureIntro; exact Heqok | iExact "HC" ]. }
    iIntros "Hcur Hq Heq Hstr Hws Hsy" (h30 g1) "%Hcsg1 %Ha0g1 Hrun".
    rewrite Eret2.
    rewrite HK2 in Ha0g1. rewrite HK2.
    rewrite (ushs_gettok_res_file len f p e Hred) in Ha0g1.
    rewrite (ushs_gettok_end_file len f p e Hred)
            (ushs_gettok_fin_file len f p e Hred).
    iDestruct "Hq" as "[ %Hbad | [_ HB] ]"; [ exfalso; lia | ].
    iDestruct "Heq" as "[ %Hbad | [_ HC] ]"; [ exfalso; lia | ].
    assert (Hg1cs : forall r : mword 5, ucallee_saved_idx r = true ->
              Regidx r <> Regidx s1_idx -> g1 !!! Regidx r = n0 !!! Regidx r)
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
                     ltac:(vm_compute; discriminate)); exact Hs5_n0).
    assert (Hs7_g1 : g1 !!! Regidx s7_idx = mword_of_int 97)
      by (rewrite (Hg1cs s7_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs7_n0).
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
    assert (Hs0_r14 : r14 !!! Regidx s0_idx = sp0).
    { rewrite (Hr14 s0_idx ltac:(vm_compute; discriminate))
              (Hr13 s0_idx ltac:(vm_compute; discriminate))
              (Hr12 s0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hg1cs s0_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)).
      rewrite Hs0_n0. exact Hv. }
    (* ---- 0x562  ld a2,-112(s0)  --  efile ---- *)
    iApply (wp_uk_ld N h36 r14 (mword_of_int 0x562)
              (mword_of_int 3984 : mword 12) s0_idx a2_idx (DfracOwn 1)
              (uint sp0 - 112) (mword_of_int (s0 + Z.of_nat e))
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
    assert (Hs0_r15 : r15 !!! Regidx s0_idx = sp0)
      by (rewrite (Hr15 s0_idx ltac:(vm_compute; discriminate)); exact Hs0_r14).
    (* ---- 0x566  ld a1,-104(s0)  --  file ---- *)
    iApply (wp_uk_ld N h37 r15 (mword_of_int 0x566)
              (mword_of_int 3992 : mword 12) s0_idx a1_idx (DfracOwn 1)
              (uint sp0 - 104) (mword_of_int (s0 + Z.of_nat (S (S p))))
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
                       (mword_of_int (s0 + Z.of_nat (S (S p)))
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
      exact Hs4_n0. }
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
                  = mword_of_int (s0 + Z.of_nat (S (S p)))).
    { rewrite (Hr18 a1_idx ltac:(vm_compute; discriminate))
              (Hr17 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq r15 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat (S (S p))) : mword 64))). }
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
              Regidx r <> Regidx s1_idx -> r18 !!! Regidx r = n0 !!! Regidx r).
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
    iApply (wp_kshp_redircmd_n h40 r18 s0 cmd 1537 1 Sub (S (S p)) e nn
              Ga0 Ga1 Ga2 Ga3 Ga4
              ltac:(unfold Z31; lia) ltac:(unfold Z31; lia)
              with "Hcode HM Hpx Hpay Hsub Hrun").
    iIntros (h41 g2 t) "%Hcsg2 %Ha0g2 %Hpb Htree Hsub HM' Hpay Hrun".
    rewrite Eret3.
    assert (Hg2cs : forall r : mword 5, ucallee_saved_idx r = true ->
              Regidx r <> Regidx s1_idx -> g2 !!! Regidx r = n0 !!! Regidx r)
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
              r19 !!! Regidx r = n0 !!! Regidx r)
      by (intros r Hr Hs1 Hs4; rewrite (Hr19 r Hs4); exact (Hg2cs r Hr Hs1)).
    (* ---- 0x502  li s5,60 -- the SECOND turn of the guard ---- *)
    iApply (wp_uk_li N h43 r19 (mword_of_int 0x502)
              (mword_of_int 60 : mword 12) s5_idx (mword_of_int 60)
              (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(symmetry; exact (ushp_mv_val 60))
              with "[] Hrun").
    { iApply (uis_shp_502 with "Hcode"). }
    rewrite (ushp_pc_step 0x502 4). iIntros (h44) "Hrun".
    set (r20 := <[Regidx s5_idx
                  := regval_into_reg (mword_of_int 60 : mword 64)]> r19).
    assert (Hr20 : forall r : mword 5, Regidx r <> Regidx s5_idx ->
                     r20 !!! Regidx r = r19 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r19 (Regidx s5_idx) (Regidx r) _ Hr)).
    (* ---- 0x506  c.mv a2,s6 ---- *)
    assert (Hs6_r20 : r20 !!! Regidx s6_idx = mword_of_int ushp_T_redir).
    { rewrite (Hr20 s6_idx ltac:(vm_compute; discriminate)).
      rewrite (Hr19cs s6_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      exact Hs6_n0. }
    iApply (wp_uk_cmv N h44 r20 (mword_of_int 0x506) a2_idx s6_idx
              (mword_of_int ushp_T_redir) (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs6_r20; symmetry;
                    exact (ushp_mv_val ushp_T_redir))
              with "[] Hrun").
    { iApply (uis_shp_506 with "Hcode"). }
    rewrite (ushp_pc_step 0x506 2). iIntros (h45) "Hrun".
    set (r21 := <[Regidx a2_idx
                  := regval_into_reg
                       (mword_of_int ushp_T_redir : mword 64)]> r20).
    assert (Hr21 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
                     r21 !!! Regidx r = r20 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r20 (Regidx a2_idx) (Regidx r) _ Hr)).
    (* ---- 0x508  c.mv a1,s2 ---- *)
    assert (Hs2_r21 : r21 !!! Regidx s2_idx
                      = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hr21 s2_idx ltac:(vm_compute; discriminate))
              (Hr20 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hr19cs s2_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      exact Hs2_n0. }
    iApply (wp_uk_cmv N h45 r21 (mword_of_int 0x508) a1_idx s2_idx
              (mword_of_int (s0 + Z.of_nat len)) (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2_r21; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_508 with "Hcode"). }
    rewrite (ushp_pc_step 0x508 2). iIntros (h46) "Hrun".
    set (r22 := <[Regidx a1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len) : mword 64)]> r21).
    assert (Hr22 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                     r22 !!! Regidx r = r21 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r21 (Regidx a1_idx) (Regidx r) _ Hr)).
    (* ---- 0x50a  c.mv a0,s3 ---- *)
    assert (Hs3_r22 : r22 !!! Regidx s3_idx = mword_of_int ps).
    { rewrite (Hr22 s3_idx ltac:(vm_compute; discriminate))
              (Hr21 s3_idx ltac:(vm_compute; discriminate))
              (Hr20 s3_idx ltac:(vm_compute; discriminate)).
      rewrite (Hr19cs s3_idx ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      exact Hs3_n0. }
    iApply (wp_uk_cmv N h46 r22 (mword_of_int 0x50a) a0_idx s3_idx
              (mword_of_int ps) (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_r22; symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_50a with "Hcode"). }
    rewrite (ushp_pc_step 0x50a 2). iIntros (h47) "Hrun".
    set (r23 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int ps : mword 64)]> r22).
    assert (Hr23 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                     r23 !!! Regidx r = r22 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r22 (Regidx a0_idx) (Regidx r) _ Hr)).
    (* ---- 0x50c  jal 448 <peek> ---- *)
    iApply (wp_uk_jal N h47 r23 (mword_of_int 0x50c)
              (mword_of_int 2096956 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x510) (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_50c with "Hcode"). }
    iIntros (h48) "Hrun".
    set (r24 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x510 : mword 64)]> r23).
    assert (Hr24 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                     r24 !!! Regidx r = r23 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r23 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Ja0 : r24 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hr24 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq r22 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Ja1 : r24 !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hr24 a1_idx ltac:(vm_compute; discriminate))
              (Hr23 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq r21 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Ja2 : r24 !!! Regidx a2_idx = mword_of_int ushp_T_redir).
    { rewrite (Hr24 a2_idx ltac:(vm_compute; discriminate))
              (Hr23 a2_idx ltac:(vm_compute; discriminate))
              (Hr22 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq r20 (Regidx a2_idx)
               (regval_into_reg
                  (mword_of_int ushp_T_redir : mword 64))). }
    assert (Eret4 : ret_pc (r24 !!! Regidx ra_idx) = mword_of_int 0x510).
    { rewrite (upd_eq r23 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x510 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hr24cs : forall r : mword 5, ucallee_saved_idx r = true ->
              Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s4_idx ->
              Regidx r <> Regidx s5_idx -> r24 !!! Regidx r = n0 !!! Regidx r).
    { intros r Hr Hs1 Hs4 Hs5.
      rewrite (Hr24 r (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)))
              (Hr23 r (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)))
              (Hr22 r (ushp_cs_ne r a1_idx Hr ltac:(vm_compute; reflexivity)))
              (Hr21 r (ushp_cs_ne r a2_idx Hr ltac:(vm_compute; reflexivity)))
              (Hr20 r Hs5).
      exact (Hr19cs r Hr Hs1 Hs4). }
    assert (Hs4_r24 : r24 !!! Regidx s4_idx = mword_of_int t).
    { rewrite (Hr24 s4_idx ltac:(vm_compute; discriminate))
              (Hr23 s4_idx ltac:(vm_compute; discriminate))
              (Hr22 s4_idx ltac:(vm_compute; discriminate))
              (Hr21 s4_idx ltac:(vm_compute; discriminate))
              (Hr20 s4_idx ltac:(vm_compute; discriminate)).
      exact Hs4_r19. }
    assert (Hsp_r24 : r24 !!! Regidx csp_rs1 = spn).
    { rewrite (Hr24cs csp_rs1 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      exact Hsp_n0. }
    rewrite <- shpp_peek.
    (* ---- peek(ps, es, "<>") a second time -- the cursor is at [es] ---- *)
    iApply (wp_kshp_peek h48 r24 dq dw true DfracDiscarded ps s0
              ushp_T_redir len len 2 f (ushp_lit ushp_T_redir)
              (mword_of_int (s0 + Z.of_nat len)) (8 + nn)
              Ja0 Ja1 Ja2 ltac:(lia) eq_refl Hs0 Hs64
              ltac:(unfold ushp_T_redir; lia)
              ltac:(unfold ushp_T_redir, Z64; lia) Hps0 Hps8 Hpssz
              with "Hcode Hcur Hstr Hws [] Hrun").
    { iApply (ushp_lit_str ushp_T_redir 2 DfracDiscarded
                ushp_T_redir_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Hcur Hstr Hws _" (h49 g3) "%Hcsg3 %Ha0g3 Hrun".
    rewrite Eret4.
    assert (Hend0 : (len + ushp_skipws (len - len) len f)%nat = len).
    { assert (Ez : (len - len)%nat = 0%nat) by lia. rewrite Ez.
      rewrite (ushp_skipws_zero len f). lia. }
    rewrite Hend0 in Ha0g3. rewrite Hend0.
    assert (Hpk0 : ushp_peek_res len f len 2 (ushp_lit ushp_T_redir) = 0).
    { unfold ushp_peek_res.
      rewrite (bool_decide_eq_false_2 (len < len)%nat ltac:(lia)).
      reflexivity. }
    rewrite Hpk0 in Ha0g3.
    (* ---- 0x510  c.beqz a0 -- TAKEN: the loop is done ---- *)
    iApply (wp_uk_cbeqz N h49 g3 (mword_of_int 0x510)
              (mword_of_int 50 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              true (mword_of_int 0x574) (8 + (2 + (8 + nn)))
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0g3; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_510 with "Hcode"). }
    iIntros (h50) "Hrun".
    (* ---- 0x574  c.mv a0,s4 -- the REDIR node is the answer ---- *)
    assert (Hs4_g3 : g3 !!! Regidx s4_idx = mword_of_int t)
      by (rewrite (Hcsg3 s4_idx ltac:(vm_compute; reflexivity));
          exact Hs4_r24).
    iApply (wp_uk_cmv N h50 g3 (mword_of_int 0x574) a0_idx s4_idx
              (mword_of_int t) (8 + (2 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs4_g3; symmetry; exact (ushp_mv_val t))
              with "[] Hrun").
    { iApply (uis_shp_574 with "Hcode"). }
    iIntros (h51) "Hrun".
    set (me := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int t : mword 64)]> g3).
    assert (Hme : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    me !!! Regidx r = g3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne g3 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (Hspe : me !!! Regidx csp_rs1 = spn).
    { rewrite (Hme csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hcsg3 csp_rs1 ltac:(vm_compute; reflexivity)).
      exact Hsp_r24. }
    (* ---- the two locals go back into the frame ---- *)
    iAssert (ustack γd spl 3) with "[HA HB HC Hbot]" as "Hloc".
    { iApply (ushp_frame_join spl spb 0
                [(s10_idx, mword_of_int 0 : mword 6);
                 (s10_idx, mword_of_int 0 : mword 6);
                 (s10_idx, mword_of_int 0 : mword 6)]
                (fun i : nat =>
                   match i with
                   | 0%nat => wA
                   | 1%nat => mword_of_int (s0 + Z.of_nat (S (S p)))
                   | _ => mword_of_int (s0 + Z.of_nat e) end)
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
              (8 + (2 + (8 + nn))) h51 me
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
    iApply ("Hcont" $! t with "Hcur Hstr Hws Hsy Htree Hsub HM' Hpay [] [] Hrun").
    - iPureIntro.
      apply (ushp_frame_cs _ vals m me sp0 eq_refl).
      + intros i r u Hi.
        destruct i as [| [| [| [| [| [| [| [| [| [| [| i ]]]]]]]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; reflexivity.
      + intros r Hr Hrsp Hmiss.
        rewrite (Hme r (ushp_cs_ne r a0_idx Hr
                          ltac:(vm_compute; reflexivity))).
        rewrite (Hcsg3 r Hr).
        rewrite (Hr24cs r Hr
                   (Hmiss 2%nat s1_idx (mword_of_int 11 : mword 6) eq_refl)
                   (Hmiss 5%nat s4_idx (mword_of_int 8 : mword 6) eq_refl)
                   (Hmiss 6%nat s5_idx (mword_of_int 7 : mword 6) eq_refl)).
        rewrite (Hcs r Hr).
        rewrite (Hm15 r (ushp_cs_ne r ra_idx Hr
                           ltac:(vm_compute; reflexivity)))
                (Hm14 r (ushp_cs_ne r a0_idx Hr
                           ltac:(vm_compute; reflexivity)))
                (Hm13 r (ushp_cs_ne r a1_idx Hr
                           ltac:(vm_compute; reflexivity)))
                (Hm12 r (ushp_cs_ne r a2_idx Hr
                           ltac:(vm_compute; reflexivity)))
                (Hm11 r (Hmiss 6%nat s5_idx (mword_of_int 7 : mword 6)
                           eq_refl))
                (Hm10 r (Hmiss 8%nat s7_idx (mword_of_int 5 : mword 6)
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
        exact (upd_eq g3 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int t : mword 64))).
      + intros i r u Hi He.
        destruct i as [| [| [| [| [| [| [| [| [| [| [| i ]]]]]]]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
  Qed.


  (* ---- the landed statement, which is that walk at a TREE -------------- *)
  (* [wp_kshp_parseredirs_gtn] says nothing about the sub-command and hands  *)
  (* the REDIR node back with its child POINTER named -- which is what       *)
  (* [parseexec] needs, because the argv terminator is still to be stored    *)
  (* through the exec node the turn has just swallowed.  Supply a tree for   *)
  (* that pointer and the node closes into [ushp_tree]; that is this         *)
  (* corollary and nothing else.                                             *)
  Lemma wp_kshp_parseredirs_gt {Pex : iProp Σ} (h : CpuId) (m : regfile)
      (dq dw dv : dfrac) (cmd ps s0 : Z) (len off p e : nat)
      (f : nat -> bv 8) (c : ushp_cmd) (w0 : mword 64) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int cmd ->
    m !!! Regidx a1_idx = mword_of_int ps ->
    m !!! Regidx a2_idx = mword_of_int (s0 + Z.of_nat len) ->
    (off <= len)%nat ->
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    ushs_redir len f p e ->
    (off + ushp_skipws (len - off) off f)%nat = p ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    UMalloc -∗
    □ (Pex -∗ ukn_pay N (-1)) -∗
    Pex -∗
    ushp_tree s0 cmd c -∗
    uword γd ps w0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    urun N h m (mword_of_int ShSyms.parseredirs)
      (14 + (8 + (2 + (8 + nn)))) -∗
    (∀ (t : Z),
       uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
       ushp_tree s0 t (UshpRedir c (S (S p)) e 1537 1) -∗
       UMalloc' -∗
       Pex -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int t ⌝ -∗
         urun N h' m' (ret_pc (m !!! Regidx ra_idx))
           (14 + (8 + (2 + (8 + nn)))) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using ushp_malloc_ok.
    intros Ha0 Ha1 Ha2 Hoffle Hw0 Hred Hp Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode #Hro HM #Hpx Hpay Hsub Hcur Hstr Hws Hsy Hrun Hcont".
    iApply (wp_kshp_parseredirs_gtn h m dq dw dv cmd ps s0 len off p e f
              (ushp_tree s0 cmd c) w0 nn
              Ha0 Ha1 Ha2 Hoffle Hw0 Hred Hp Hs0 Hs64 Hps0 Hps8 Hpssz
              with "Hcode Hro HM Hpx Hpay Hsub Hcur Hstr Hws Hsy Hrun").
    iIntros (t) "Hcur Hstr Hws Hsy Hnode Hsub HM' Hpay".
    iApply ("Hcont" $! t with "Hcur Hstr Hws Hsy [Hnode Hsub] HM' Hpay").
    iApply (ushp_redir_close s0 t cmd (S (S p)) e 1537 1 c with "Hnode Hsub").
  Qed.


  (* ===================================================================== *)
  (* §12 parseredirs at ZERO turns, ON A LINE THAT HAS A '>' SOMEWHERE.     *)
  (*                                                                       *)
  (* [UkShParseRedir.wp_kshp_parseredirs] is the same 40 instructions, and  *)
  (* the ONLY thing it uses [ushp_no_symbols] for is to know the byte at    *)
  (* the blank-scanned cursor is not in the two-byte redirect table -- one  *)
  (* line of its 550.  [parseexec]'s argument loop calls [parseredirs]      *)
  (* after EVERY token, and on a redirect line all but the last of those    *)
  (* calls is a zero-turn call at a cursor sitting on an ordinary word, so  *)
  (* the loop needs exactly this: the same walk at the premise it uses.     *)
  (* The landed lemma is its [ushp_no_symbols] instance.                    *)
  (* ===================================================================== *)

  Lemma wp_kshp_parseredirs_ns (h : CpuId) (m : regfile) (dq dw : dfrac)
      (cmd ps s0 : Z) (len off : nat) (f : nat -> bv 8)
      (w0 : mword 64) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int cmd ->
    m !!! Regidx a1_idx = mword_of_int ps ->
    m !!! Regidx a2_idx = mword_of_int (s0 + Z.of_nat len) ->
    (off <= len)%nat ->
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    ((off + ushp_skipws (len - off) off f < len)%nat ->
     ushp_is_sym (f (off + ushp_skipws (len - off) off f)%nat) = false) ->
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
    intros Ha0 Ha1 Ha2 Hoffle Hw0 Hnsk Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode #Hro Hcur Hstr Hws Hrun Hcont".
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
    (* ---- 0x4d0  addi s6,s6,-460 -- the table base 0x1300 ---- *)
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
    (* ---- 0x502  li s5,60 -- the '<' the dead switch compares against ---- *)
    iApply (wp_uk_li N h10 m10 (mword_of_int 0x502)
              (mword_of_int 60 : mword 12) s5_idx (mword_of_int 60)
              (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(symmetry; exact (ushp_mv_val 60))
              with "[] Hrun").
    { iApply (uis_shp_502 with "Hcode"). }
    iIntros (h11) "Hrun".
    set (m11 := <[Regidx s5_idx
                  := regval_into_reg (mword_of_int 60 : mword 64)]> m10).
    assert (Hm11 : forall q : mword 5, Regidx q <> Regidx s5_idx ->
                     m11 !!! Regidx q = m10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m10 (Regidx s5_idx) (Regidx q) _ Hq)).
    (* ---- 0x506  c.mv a2,s6 ---- *)
    assert (Hs6_11 : m11 !!! Regidx s6_idx = mword_of_int ushp_T_redir).
    { rewrite (Hm11 s6_idx ltac:(vm_compute; discriminate))
              (Hm10 s6_idx ltac:(vm_compute; discriminate))
              (Hm9 s6_idx ltac:(vm_compute; discriminate))
              (Hm8 s6_idx ltac:(vm_compute; discriminate)). exact Hs6_7. }
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
              (Hm11 s2_idx ltac:(vm_compute; discriminate))
              (Hm10 s2_idx ltac:(vm_compute; discriminate))
              (Hm9 s2_idx ltac:(vm_compute; discriminate))
              (Hm8 s2_idx ltac:(vm_compute; discriminate))
              (Hm7 s2_idx ltac:(vm_compute; discriminate))
              (Hm6 s2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m4 (Regidx s2_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
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
              (Hm11 s3_idx ltac:(vm_compute; discriminate))
              (Hm10 s3_idx ltac:(vm_compute; discriminate))
              (Hm9 s3_idx ltac:(vm_compute; discriminate))
              (Hm8 s3_idx ltac:(vm_compute; discriminate))
              (Hm7 s3_idx ltac:(vm_compute; discriminate))
              (Hm6 s3_idx ltac:(vm_compute; discriminate))
              (Hm5 s3_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m3 (Regidx s3_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
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
    (* ---- peek(ps, es, the two redirection bytes) ---- *)
    iApply (wp_kshp_peek h15 m15 dq dw true DfracDiscarded ps s0
              ushp_T_redir len off 2 f (ushp_lit ushp_T_redir)
              (mword_of_int (s0 + Z.of_nat off)) nn
              Ha0_15 Ha1_15 Ha2_15 Hoffle eq_refl Hs0 Hs64
              ltac:(unfold ushp_T_redir; lia)
              ltac:(unfold ushp_T_redir, Z64; lia) Hps0 Hps8 Hpssz
              with "Hcode [Hcur] Hstr Hws [] Hrun").
    { rewrite <- Hw0. iExact "Hcur". }
    { iApply (ushp_lit_str ushp_T_redir 2 DfracDiscarded
                ushp_T_redir_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Hcur Hstr Hws _" (h16 n0) "%Hcs %Ha0n0 Hrun".
    rewrite Eret.
    rewrite (ushs_peek_res_nsym len f
               (off + ushp_skipws (len - off) off f) 2 ushp_T_redir
               Hnsk ushp_T_redir_sym) in Ha0n0.
    (* ---- 0x510  c.beqz a0 -- TAKEN: the loop never turns ---- *)
    iApply (wp_uk_cbeqz N h16 n0 (mword_of_int 0x510)
              (mword_of_int 50 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              true (mword_of_int 0x574) (8 + (2 + nn))
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0n0; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_510 with "Hcode"). }
    iIntros (h17) "Hrun".
    (* ---- 0x574  c.mv a0,s4 -- the answer is the cmd we were handed ---- *)
    assert (Hs4_n0 : n0 !!! Regidx s4_idx = mword_of_int cmd).
    { rewrite (Hcs s4_idx ltac:(vm_compute; reflexivity))
              (Hm15 s4_idx ltac:(vm_compute; discriminate))
              (Hm14 s4_idx ltac:(vm_compute; discriminate))
              (Hm13 s4_idx ltac:(vm_compute; discriminate))
              (Hm12 s4_idx ltac:(vm_compute; discriminate))
              (Hm11 s4_idx ltac:(vm_compute; discriminate))
              (Hm10 s4_idx ltac:(vm_compute; discriminate))
              (Hm9 s4_idx ltac:(vm_compute; discriminate))
              (Hm8 s4_idx ltac:(vm_compute; discriminate))
              (Hm7 s4_idx ltac:(vm_compute; discriminate))
              (Hm6 s4_idx ltac:(vm_compute; discriminate))
              (Hm5 s4_idx ltac:(vm_compute; discriminate))
              (Hm4 s4_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s4_idx)
               (regval_into_reg (mword_of_int cmd : mword 64))). }
    iApply (wp_uk_cmv N h17 n0 (mword_of_int 0x574) a0_idx s4_idx
              (mword_of_int cmd) (8 + (2 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs4_n0; symmetry; exact (ushp_mv_val cmd))
              with "[] Hrun").
    { iApply (uis_shp_574 with "Hcode"). }
    iIntros (h18) "Hrun".
    set (me := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int cmd : mword 64)]> n0).
    assert (Hme : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    me !!! Regidx q = n0 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n0 (Regidx a0_idx) (Regidx q) _ Hq)).
    assert (Hspe : me !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 14))).
    { rewrite (Hme csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm15 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm14 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm13 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm12 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm11 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm10 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm9 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm8 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm7 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm6 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm5 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm4 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm3 csp_rs1 ltac:(vm_compute; discriminate)).
      exact Hsp2. }
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
              (mword_of_int 7 : mword 6) sp0
              (mword_of_int (uint sp0 - 8 * Z.of_nat 11)) vals
              (8 + (2 + nn)) h18 me
              ltac:(cbn [length]; reflexivity)
              Hal8 ltac:(cbn; lia) Hhi
              ltac:(apply uint_moi; cbn; lia)
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
    iApply ("Hcont" with "Hcur Hstr Hws [] [] Hrun").
    - iPureIntro.
      apply (ushp_frame_cs _ vals m me sp0 eq_refl).
      + intros i r u Hi.
        destruct i as [| [| [| [| [| [| [| [| [| [| [| i ]]]]]]]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; reflexivity.
      + intros q Hq Hqsp Hmiss.
        rewrite (Hme q (ushp_cs_ne q a0_idx Hq
                          ltac:(vm_compute; reflexivity)))
                (Hcs q Hq)
                (Hm15 q (Hmiss 0%nat ra_idx (mword_of_int 13 : mword 6)
                           eq_refl))
                (Hm14 q (ushp_cs_ne q a0_idx Hq
                           ltac:(vm_compute; reflexivity)))
                (Hm13 q (ushp_cs_ne q a1_idx Hq
                           ltac:(vm_compute; reflexivity)))
                (Hm12 q (ushp_cs_ne q a2_idx Hq
                           ltac:(vm_compute; reflexivity)))
                (Hm11 q (Hmiss 6%nat s5_idx (mword_of_int 7 : mword 6)
                           eq_refl))
                (Hm10 q (Hmiss 8%nat s7_idx (mword_of_int 5 : mword 6)
                           eq_refl))
                (Hm9 q (Hmiss 9%nat s8_idx (mword_of_int 4 : mword 6)
                          eq_refl))
                (Hm8 q (Hmiss 10%nat s9_idx (mword_of_int 3 : mword 6)
                          eq_refl))
                (Hm7 q (Hmiss 7%nat s6_idx (mword_of_int 6 : mword 6)
                          eq_refl))
                (Hm6 q (Hmiss 7%nat s6_idx (mword_of_int 6 : mword 6)
                          eq_refl))
                (Hm5 q (Hmiss 3%nat s2_idx (mword_of_int 10 : mword 6)
                          eq_refl))
                (Hm4 q (Hmiss 4%nat s3_idx (mword_of_int 9 : mword 6)
                          eq_refl))
                (Hm3 q (Hmiss 5%nat s4_idx (mword_of_int 8 : mword 6)
                          eq_refl))
                (Hm2 q (Hmiss 1%nat s0_idx (mword_of_int 12 : mword 6)
                          eq_refl))
                (Hm1 q Hqsp).
        reflexivity.
    - iPureIntro.
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      apply ushp_spillback_eq.
      + intros _.
        exact (upd_eq n0 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int cmd : mword 64))).
      + intros i r u Hi He.
        destruct i as [| [| [| [| [| [| [| [| [| [| [| i ]]]]]]]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
  Qed.


End UkShRedirPr.
