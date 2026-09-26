(* ===================================================================== *)
(* UkShPipeEx2.v -- parseexec's ARGUMENT LOOP on the pipe line,           *)
(* lane SH-PARSE-PIPE part 2 (design/app-pipe.md SS5.1).                   *)
(*                                                                        *)
(* [UkShRedirEx.wp_kshp_pex_loop_gt] is this loop on the redirect line and *)
(* its LAST round is special: there [parseredirs] turns and builds the     *)
(* REDIR node, so the induction splits on the tail and the two arms differ *)
(* in which [parseredirs] closes the round.  On the PIPE line NO round     *)
(* turns -- [parseredirs]' peek is for the two redirection bytes and the   *)
(* byte it lands on is either a word or the '|' -- so this loop is UNIFORM *)
(* and needs no tail split:                                               *)
(*                                                                        *)
(*   Nil   the blank scan reaches the '|', the loop's own peek HITS, and   *)
(*         [UkShPipeEx.wp_kshp_pex_bar] leaves at 0x63e with the cursor    *)
(*         AT the '|' -- which is exactly what the guard in [parsepipe]    *)
(*         then reads;                                                    *)
(*   Cons  the round -- peek miss, [gettoken] answering 'a', the two       *)
(*         stores, argc++ -- then                                          *)
(*         [UkShPipePr.wp_kshp_parseredirs_miss] and round again.          *)
(*                                                                        *)
(* IT CARRIES TWO PREMISES FEWER than the redirect loop, and no allocator  *)
(* capability at all.  The landed one takes a not-a-symbol premise at the  *)
(* scanned cursor and a positive-length one on the token list; the first   *)
(* is                                                                     *)
(* DERIVED at each [Cons] (a token of positive length starts at a byte     *)
(* that is neither blank nor symbol) and the second is not wanted, because *)
(* the empty list is the loop's EXIT rather than an impossibility.  And    *)
(* the pipe line's rounds allocate nothing: [execcmd] ran before the loop  *)
(* and no [redircmd] is ever reached.                                      *)
(* ===================================================================== *)
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
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem.
Require Import UCodeShP.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.
Require Import UserFd.
Require Import UkShParse.
Require Import UkShParseSym.
Require Import UkShParseLex.
Require Import UkShRedirGtk.
Require Import UkShRedirCmd.
Require Import UkShRedirPr.

Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)
Require Import UkShPipeLex.
Require Import UkShPipesLex.  (* [ushq_barw]: a bar read locally (lane PIPES-C3) *)
Require Import UkShPipeTok.
Require Import UkShPipeEx.
Require Import UkShPipePr.

Section UkShPipeEx2.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  (* THIS PROGRAM'S EXIT OWES ITS PARENT NOTHING at this lane, as a
     CLASS so that it reaches the exit ecall without an argument at every
     call site ([UkRun.ukn_const]). *)
  Context `{Hpay : !ukn_const N}.
  (* the fields, under the names the engine has always used *)
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Local Notation γfd := (ukn_fd N).
  Local Notation γcwd := (ukn_cwd N).
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
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


(*ALIASES-BEGIN*)
  (* ---- what the earlier files of the parser define, at this
         file's own ghost names.  Everything else they export is a
         PURE constant and comes in with the [Require Import]. ---- *)
  Local Notation urun_x0 := (UkShParse.urun_x0 N).
  Local Notation ushp_exec_at := (UkShParse.ushp_exec_at N).
  Local Notation ushp_exec_pre := (UkShParse.ushp_exec_pre N).
  Local Notation ushp_exec_pre_at := (UkShParse.ushp_exec_pre_at N).
  Local Notation ushp_frame_join := (UkShParse.ushp_frame_join N).
  Local Notation ushp_frame_split := (UkShParse.ushp_frame_split N).
  Local Notation ushp_lit_str := (UkShParseLex.ushp_lit_str N).
  Local Notation ushp_malloc_ty := (UkShParse.ushp_malloc_ty_le N 168).
  Local Notation ushp_slots_cap := (UkShParse.ushp_slots_cap N).
  Local Notation ushp_slots_upd := (UkShParse.ushp_slots_upd N).
  Local Notation ushp_type_at := (UkShParse.ushp_type_at N).
  Local Notation wp_kshp_frame_epi := (UkShParse.wp_kshp_frame_epi N).
  Local Notation wp_kshp_frame_pro := (UkShParse.wp_kshp_frame_pro N).
  Local Notation wp_kshp_gettoken_sym := (UkShRedirGtk.wp_kshp_gettoken_sym N).
  Local Notation ushp_redir_node := (UkShRedirCmd.ushp_redir_node N).
  Local Notation ushp_redir_close := (UkShRedirCmd.ushp_redir_close N).
  Local Notation wp_kshp_peek := (UkShParseLex.wp_kshp_peek N).
  Local Notation wp_kshp_restore := (UkShParse.wp_kshp_restore N).
  Local Notation wp_kshp_spill := (UkShParse.wp_kshp_spill N).

  (* NO allocator capability: this loop allocates nothing (see the header). *)


  (* ===================================================================== *)
  (* THE ARGUMENT LOOP ON THE PIPE LINE                                     *)
  (*                                                                        *)
  (* [UkShRedirEx.wp_kshp_pex_loop_gt] is this loop on the redirect line,    *)
  (* and its LAST round is where that line's [parseredirs] turns and builds  *)
  (* the REDIR node.  On the pipe line NO round turns -- [parseredirs]' peek *)
  (* is for "<>" and the byte it lands on is either a word or the '|' -- so  *)
  (* the loop is UNIFORM and the induction needs no tail split at all:       *)
  (*                                                                        *)
  (*   Nil   the cursor's blank scan reaches the '|', the loop's own peek     *)
  (*         HITS, and [UkShPipeEx.wp_kshp_pex_bar] leaves at 0x63e;          *)
  (*   Cons  the round (peek miss, gettoken 'a', the two stores, argc++),     *)
  (*         then [UkShPipePr.wp_kshp_parseredirs_miss] and round again.      *)
  (*                                                                        *)
  (* It also needs TWO PREMISES FEWER than the redirect loop: the landed one  *)
  (* carries "the byte at the scanned cursor is not a symbol" and            *)
  (* "0 < length rest", and both are DERIVABLE here -- the first from the     *)
  (* token list at a [Cons] (a token of positive length starts at a byte     *)
  (* that is neither blank nor symbol) and the second not needed, because    *)
  (* the empty list is the exit rather than an impossibility.                *)
  (* ===================================================================== *)

  (* AT A BAR READ LOCALLY (lane PIPES-C3): the loop reads the line at its
     bar only through [ushq_barw] -- the byte, its place, and that every
     symbol of the line is one gettoken takes -- so a line with MORE bars
     after this one is walked by the same proof.  [wp_kshp_pex_loop_bar]
     below is the one-bar line's instance. *)
  Lemma wp_kshp_pex_loop_barw (dq dw dv : dfrac)
      (s0 ps p fp : Z) (len : nat) (f : nat -> bv 8) (gp : nat)
      (nn : nat) :
    forall (rest done : list (nat * nat)) (cur : nat) (h : CpuId)
           (mc : regfile) (wq weq : mword 64),
    ushq_barw len f gp ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    0 < fp - 128 -> (fp - 128) mod 8 = 0 -> 0 <= fp -> fp < Z64 ->
    0 < p -> p mod 8 = 0 -> p + 168 < Z64 ->
    (cur <= len)%nat ->
    (length done + length rest < 10)%nat ->
    ushs_toks len f gp cur rest ->
    mc !!! Regidx s0_idx = mword_of_int fp ->
    mc !!! Regidx s1_idx = mword_of_int p ->
    mc !!! Regidx s2_idx = mword_of_int (Z.of_nat (length done)) ->
    mc !!! Regidx s3_idx
      = mword_of_int (p + 8 + 8 * Z.of_nat (length done)) ->
    mc !!! Regidx s4_idx = mword_of_int ps ->
    mc !!! Regidx s5_idx = mword_of_int (s0 + Z.of_nat len) ->
    mc !!! Regidx s6_idx = mword_of_int ushp_T_arg ->
    mc !!! Regidx s7_idx = mword_of_int (fp - 120) ->
    mc !!! Regidx s8_idx = mword_of_int (fp - 128) ->
    mc !!! Regidx s9_idx = mword_of_int 10 ->
    mc !!! Regidx s10_idx = mword_of_int 97 ->
    mc !!! Regidx s11_idx = mword_of_int p ->
    shp_code γt -∗
    shp_rodata γt -∗
    ushp_exec_pre s0 p done -∗
    uword γd ps (mword_of_int (s0 + Z.of_nat cur)) -∗
    uword γd (fp - 120) wq -∗
    uword γd (fp - 128) weq -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    urun N h mc (mword_of_int 0x5fe) (24 + (8 + nn)) -∗
    (ushp_exec_pre s0 p (done ++ rest) -∗
     uword γd ps (mword_of_int (s0 + Z.of_nat gp)) -∗
     (∃ w : mword 64, uword γd (fp - 120) w) -∗
     (∃ w : mword 64, uword γd (fp - 128) w) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
     ustr γd dv ushp_symbols 7 ushp_sym_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall r : mword 5, ucallee_saved_idx r = true ->
             Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
             Regidx r <> Regidx s3_idx ->
             mc' !!! Regidx r = mc !!! Regidx r ⌝ -∗
         ⌜ mc' !!! Regidx s2_idx
             = mword_of_int (Z.of_nat (length done + length rest)) ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx = mword_of_int p ⌝ -∗
         urun N h' mc' (mword_of_int 0x63e) (24 + (8 + nn)) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intro rest.
    induction rest as [| tk rest IH ];
      intros done cur h mc wq weq Hpq Hs0 Hs64 Hps0 Hps8 Hpssz
        Hfp0 Hfp8 Hfpl Hfph Hp0 Hp8 Hpsz Hcur Hcnt Htoks
        Hs0v Hs1v Hs2v Hs3v Hs4v Hs5v Hs6v Hs7v Hs8v Hs9v Hs10v Hs11v;
      iIntros "#Hcode #Hro Hnode Hcur Hq Heq Hstr Hws Hsy Hrun Hcont".
    (* ---- THE EXIT: no argument left, so the scan reaches the '|' ---- *)
    1: { assert (Hgpe : (cur + ushp_skipws (len - cur) cur f)%nat = gp)
           by exact (ushs_toks_nil_inv len gp cur f Htoks).
         iApply (UkShPipeEx.wp_kshp_pex_bar N dq dw s0 ps len f (8 + nn) cur
                   h mc Hcur
                   ltac:(rewrite Hgpe; exact (ushq_barw_lt len f gp Hpq))
                   ltac:(rewrite Hgpe; exact (ushq_barw_bar len f gp Hpq))
                   Hs0 Hs64 Hps0 Hps8 Hpssz Hs4v Hs5v Hs6v
                   with "Hcode Hro Hcur Hstr Hws Hrun").
         iIntros "Hcur Hstr Hws" (h' mc') "%Hpres Hrun".
         rewrite Hgpe. rewrite app_nil_r.
         iApply ("Hcont" with "Hnode Hcur [Hq] [Heq] Hstr Hws Hsy [] [] [] Hrun").
         - iExists wq. iExact "Hq".
         - iExists weq. iExact "Heq".
         - iPureIntro. intros r Hr Hr1 Hr2 Hr3. exact (Hpres r Hr).
         - iPureIntro.
           rewrite (Hpres s2_idx ltac:(vm_compute; reflexivity)) Hs2v.
           f_equal. cbn [length]. lia.
         - iPureIntro.
           rewrite (Hpres s1_idx ltac:(vm_compute; reflexivity)). exact Hs1v. }
    (* ---- and the round, at the two facts the token list gives ---- *)
    assert (Hsymok : ushq_sym_ok len f)
      by exact (ushq_barw_sym_ok len f gp Hpq).
    assert (Hnsk : ((cur + ushp_skipws (len - cur) cur f)%nat < len)%nat ->
              ushp_is_sym (f (cur + ushp_skipws (len - cur) cur f)%nat)
              = false).
    { intros _.
      destruct (ushs_toks_cons_inv len gp cur f tk rest Htoks) as (Hn & _ & _).
      exact (ushs_toklen_pos_nosym _ _ f Hn). }
    (* ---- the frame's two out-cells are hygienic wherever the frame is -- *)
    assert (Hq0 : 0 < fp - 120) by lia.
    assert (Hq8 : (fp - 120) mod 8 = 0);
      [ replace (fp - 120) with (fp - 128 + 8) by lia;
        rewrite Zplus_mod Hfp8; reflexivity | ].
    assert (Hqz : fp - 120 + 8 < Z64) by lia.
    assert (Hez : fp - 128 + 8 < Z64) by lia.
    assert (Hfp64 : 0 <= fp < Z64) by lia.
    assert (Hnodelen : (length done < 10)%nat)
      by (cbn [length] in Hcnt; lia).
    (* ---- and the position peek is about to leave the cursor at -------- *)
    pose (cur' := (cur + ushp_skipws (len - cur) cur f)%nat).
    assert (Hcure : cur' = (cur + ushp_skipws (len - cur) cur f)%nat)
      by reflexivity.
    assert (Hcur' : (cur' <= len)%nat);
      [ rewrite Hcure; pose proof (ushp_skipws_le (len - cur) cur f); lia | ].
    assert (Hz' : ushp_skipws (len - cur') cur' f = 0%nat)
      by exact (ushp_skipws_idem len cur f Hcur).
    assert (Ekk : (cur' + ushp_skipws (len - cur') cur' f)%nat = cur')
      by (rewrite Hz'; lia).
    (* ---- 0x5fe  c.mv a2,s6 ---- *)
    iApply (wp_uk_cmv N h mc (mword_of_int 0x5fe) a2_idx
                   s6_idx (mword_of_int ushp_T_arg) (24 + (8 + nn))
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(rewrite Hs6v; symmetry;
                         exact (ushp_mv_val ushp_T_arg))
                   with "[] Hrun");
      [ iApply (uis_shp_5fe with "Hcode") | ].
    iIntros (h1) "Hrun".
    set (n1 := <[Regidx a2_idx
                      := regval_into_reg
                           (mword_of_int ushp_T_arg : mword 64)]> mc).
    assert (Hk1 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n1 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          exact (upd_ne mc (Regidx a2_idx) (Regidx r) _
                   (ushp_cs_ne r a2_idx Hr ltac:(vm_compute; reflexivity)))).
    (* ---- 0x600  c.mv a1,s5 ---- *)
    iApply (wp_uk_cmv N h1 n1 (mword_of_int 0x600) a1_idx
                   s5_idx (mword_of_int (s0 + Z.of_nat len)) (24 + (8 + nn))
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(rewrite (Hk1 s5_idx ltac:(vm_compute; reflexivity))
                           Hs5v; symmetry;
                         exact (ushp_mv_val (s0 + Z.of_nat len)))
                   with "[] Hrun");
      [ iApply (uis_shp_600 with "Hcode") | ].
    iIntros (h2) "Hrun".
    set (n2 := <[Regidx a1_idx
                      := regval_into_reg
                           (mword_of_int (s0 + Z.of_nat len)
                            : mword 64)]> n1).
    assert (Hk2 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n2 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n1 (Regidx a1_idx) (Regidx r) _
                     (ushp_cs_ne r a1_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk1 r Hr)).
    (* ---- 0x602  c.mv a0,s4 ---- *)
    iApply (wp_uk_cmv N h2 n2 (mword_of_int 0x602) a0_idx
                   s4_idx (mword_of_int ps) (24 + (8 + nn))
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(rewrite (Hk2 s4_idx ltac:(vm_compute; reflexivity))
                           Hs4v; symmetry; exact (ushp_mv_val ps))
                   with "[] Hrun");
      [ iApply (uis_shp_602 with "Hcode") | ].
    iIntros (h3) "Hrun".
    set (n3 := <[Regidx a0_idx
                      := regval_into_reg (mword_of_int ps : mword 64)]> n2).
    assert (Hk3 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n3 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n2 (Regidx a0_idx) (Regidx r) _
                     (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk2 r Hr)).
    (* ---- 0x604  jal 424 <peek> ---- *)
    iApply (wp_uk_jal N h3 n3 (mword_of_int 0x604)
                   (mword_of_int 2096672 : mword 21) ra_idx
                   (mword_of_int 0x424) (mword_of_int 0x608) (24 + (8 + nn))
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(apply bv_eq; vm_compute; reflexivity)
                   ltac:(apply bv_eq; vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity)
                   with "[] Hrun");
      [ iApply (uis_shp_604 with "Hcode") | ].
    iIntros (h4) "Hrun".
    set (n4 := <[Regidx ra_idx
                      := regval_into_reg
                           (mword_of_int 0x608 : mword 64)]> n3).
    assert (Hk4 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n4 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n3 (Regidx ra_idx) (Regidx r) _
                     (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk3 r Hr)).
    assert (Eret4 : ret_pc (n4 !!! Regidx ra_idx) = mword_of_int 0x608);
      [ rewrite (upd_eq n3 (Regidx ra_idx)
                   (regval_into_reg (mword_of_int 0x608 : mword 64)));
        apply bv_eq; vm_compute; reflexivity | ].
    assert (Ha0_4 : n4 !!! Regidx a0_idx = mword_of_int ps);
      [ rewrite (upd_ne n3 (Regidx ra_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq n2 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int ps : mword 64))) | ].
    assert (Ha1_4 : n4 !!! Regidx a1_idx
                         = mword_of_int (s0 + Z.of_nat len));
      [ rewrite (upd_ne n3 (Regidx ra_idx) (Regidx a1_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n2 (Regidx a0_idx) (Regidx a1_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq n1 (Regidx a1_idx)
                 (regval_into_reg
                    (mword_of_int (s0 + Z.of_nat len) : mword 64))) | ].
    assert (Ha2_4 : n4 !!! Regidx a2_idx = mword_of_int ushp_T_arg);
      [ rewrite (upd_ne n3 (Regidx ra_idx) (Regidx a2_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n2 (Regidx a0_idx) (Regidx a2_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n1 (Regidx a1_idx) (Regidx a2_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq mc (Regidx a2_idx)
                 (regval_into_reg
                    (mword_of_int ushp_T_arg : mword 64))) | ].
    rewrite <- shpp_peek.
    iApply (wp_kshp_peek h4 n4 dq dw true DfracDiscarded ps s0
                   ushp_T_arg len cur 4 f (ushp_lit ushp_T_arg)
                   (mword_of_int (s0 + Z.of_nat cur)) (14 + (8 + nn))
                   Ha0_4 Ha1_4 Ha2_4 Hcur eq_refl Hs0 Hs64
                   ltac:(unfold ushp_T_arg; lia)
                   ltac:(unfold ushp_T_arg, Z64; lia) Hps0 Hps8 Hpssz
                   with "Hcode Hcur Hstr Hws [] Hrun");
      [ iApply (ushp_lit_str ushp_T_arg 4 DfracDiscarded
                  ushp_T_arg_ok ltac:(cbn; lia) with "Hro") | ].
    iIntros "Hcur Hstr Hws _" (h5 n5) "%Hcs45 %Ha0_5 Hrun".
    rewrite Eret4.
    rewrite (ushs_peek_res_nsym len f
                    (cur + ushp_skipws (len - cur) cur f)%nat 4 ushp_T_arg
                    Hnsk ushp_T_arg_sym) in Ha0_5.
    assert (Hk5 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n5 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr; rewrite (Hcs45 r Hr); exact (Hk4 r Hr)).
    (* ---- 0x608  c.bnez a0 -- NOT taken: the guard is refuted ---- *)
    iApply (wp_uk_cbnez N h5 n5 (mword_of_int 0x608)
                   (mword_of_int 27 : mword 8) (mword_of_int 2 : mword 3)
                   a0_idx false (mword_of_int 0x63e) (24 + (8 + nn))
                   ltac:(vm_compute; reflexivity)
                   ltac:(rewrite Ha0_5; vm_compute; reflexivity)
                   ltac:(apply bv_eq; vm_compute; reflexivity)
                   ltac:(discriminate)
                   with "[] Hrun");
      [ iApply (uis_shp_608 with "Hcode") | ].
    iIntros (h6) "Hrun".
    (* ---- 0x60a..0x610  the four argument moves ---- *)
    iApply (wp_uk_cmv N h6 n5 (mword_of_int 0x60a) a3_idx
                   s8_idx (mword_of_int (fp - 128)) (24 + (8 + nn))
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(rewrite (Hk5 s8_idx ltac:(vm_compute; reflexivity))
                           Hs8v; symmetry; exact (ushp_mv_val (fp - 128)))
                   with "[] Hrun");
      [ iApply (uis_shp_60a with "Hcode") | ].
    iIntros (h7) "Hrun".
    set (n6 := <[Regidx a3_idx
                      := regval_into_reg
                           (mword_of_int (fp - 128) : mword 64)]> n5).
    assert (Hk6 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n6 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n5 (Regidx a3_idx) (Regidx r) _
                     (ushp_cs_ne r a3_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk5 r Hr)).
    iApply (wp_uk_cmv N h7 n6 (mword_of_int 0x60c) a2_idx
                   s7_idx (mword_of_int (fp - 120)) (24 + (8 + nn))
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(rewrite (Hk6 s7_idx ltac:(vm_compute; reflexivity))
                           Hs7v; symmetry; exact (ushp_mv_val (fp - 120)))
                   with "[] Hrun");
      [ iApply (uis_shp_60c with "Hcode") | ].
    iIntros (h8) "Hrun".
    set (n7 := <[Regidx a2_idx
                      := regval_into_reg
                           (mword_of_int (fp - 120) : mword 64)]> n6).
    assert (Hk7 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n7 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n6 (Regidx a2_idx) (Regidx r) _
                     (ushp_cs_ne r a2_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk6 r Hr)).
    iApply (wp_uk_cmv N h8 n7 (mword_of_int 0x60e) a1_idx
                   s5_idx (mword_of_int (s0 + Z.of_nat len)) (24 + (8 + nn))
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(rewrite (Hk7 s5_idx ltac:(vm_compute; reflexivity))
                           Hs5v; symmetry;
                         exact (ushp_mv_val (s0 + Z.of_nat len)))
                   with "[] Hrun");
      [ iApply (uis_shp_60e with "Hcode") | ].
    iIntros (h9) "Hrun".
    set (n8 := <[Regidx a1_idx
                      := regval_into_reg
                           (mword_of_int (s0 + Z.of_nat len)
                            : mword 64)]> n7).
    assert (Hk8 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n8 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n7 (Regidx a1_idx) (Regidx r) _
                     (ushp_cs_ne r a1_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk7 r Hr)).
    iApply (wp_uk_cmv N h9 n8 (mword_of_int 0x610) a0_idx
                   s4_idx (mword_of_int ps) (24 + (8 + nn))
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(rewrite (Hk8 s4_idx ltac:(vm_compute; reflexivity))
                           Hs4v; symmetry; exact (ushp_mv_val ps))
                   with "[] Hrun");
      [ iApply (uis_shp_610 with "Hcode") | ].
    iIntros (h10) "Hrun".
    set (n9 := <[Regidx a0_idx
                      := regval_into_reg (mword_of_int ps : mword 64)]> n8).
    assert (Hk9 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n9 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n8 (Regidx a0_idx) (Regidx r) _
                     (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk8 r Hr)).
    (* ---- 0x612  jal 2ec <gettoken> ---- *)
    iApply (wp_uk_jal N h10 n9 (mword_of_int 0x612)
                   (mword_of_int 2096346 : mword 21) ra_idx
                   (mword_of_int 0x2ec) (mword_of_int 0x616) (24 + (8 + nn))
                   ltac:(unfold unot_sp; vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(apply bv_eq; vm_compute; reflexivity)
                   ltac:(apply bv_eq; vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity)
                   with "[] Hrun");
      [ iApply (uis_shp_612 with "Hcode") | ].
    iIntros (h11) "Hrun".
    set (n10 := <[Regidx ra_idx
                       := regval_into_reg
                            (mword_of_int 0x616 : mword 64)]> n9).
    assert (Hk10 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n10 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n9 (Regidx ra_idx) (Regidx r) _
                     (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk9 r Hr)).
    assert (Eret10 : ret_pc (n10 !!! Regidx ra_idx)
                          = mword_of_int 0x616);
      [ rewrite (upd_eq n9 (Regidx ra_idx)
                   (regval_into_reg (mword_of_int 0x616 : mword 64)));
        apply bv_eq; vm_compute; reflexivity | ].
    assert (Ha0_10 : n10 !!! Regidx a0_idx = mword_of_int ps);
      [ rewrite (upd_ne n9 (Regidx ra_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq n8 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int ps : mword 64))) | ].
    assert (Ha1_10 : n10 !!! Regidx a1_idx
                          = mword_of_int (s0 + Z.of_nat len));
      [ rewrite (upd_ne n9 (Regidx ra_idx) (Regidx a1_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n8 (Regidx a0_idx) (Regidx a1_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq n7 (Regidx a1_idx)
                 (regval_into_reg
                    (mword_of_int (s0 + Z.of_nat len) : mword 64))) | ].
    assert (Ha2_10 : n10 !!! Regidx a2_idx = mword_of_int (fp - 120));
      [ rewrite (upd_ne n9 (Regidx ra_idx) (Regidx a2_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n8 (Regidx a0_idx) (Regidx a2_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n7 (Regidx a1_idx) (Regidx a2_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq n6 (Regidx a2_idx)
                 (regval_into_reg
                    (mword_of_int (fp - 120) : mword 64))) | ].
    assert (Ha3_10 : n10 !!! Regidx a3_idx = mword_of_int (fp - 128));
      [ rewrite (upd_ne n9 (Regidx ra_idx) (Regidx a3_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n8 (Regidx a0_idx) (Regidx a3_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n7 (Regidx a1_idx) (Regidx a3_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n6 (Regidx a2_idx) (Regidx a3_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq n5 (Regidx a3_idx)
                 (regval_into_reg
                    (mword_of_int (fp - 128) : mword 64))) | ].
    rewrite <- shpp_gettoken.
    iApply (UkShPipeTok.wp_kshp_gettoken_syms N h11 n10 dq dw dv ps (fp - 120) (fp - 128)
                   s0 len cur' f (mword_of_int (s0 + Z.of_nat cur'))
                   wq weq (14 + (8 + nn))
                   Ha0_10 Ha1_10 Ha2_10 Ha3_10 Hcur' eq_refl Hsymok Hs0 Hs64
                   Hps0 Hps8 Hpssz
                   with "Hcode Hcur [Hq] [Heq] Hstr Hws Hsy Hrun");
      [ iRight; iSplitR;
        [ iPureIntro; exact (conj Hq0 (conj Hq8 Hqz)) | iExact "Hq" ]
      | iRight; iSplitR;
        [ iPureIntro; exact (conj Hfp0 (conj Hfp8 Hez)) | iExact "Heq" ]
      | ].
    iIntros "Hcur Hq Heq Hstr Hws Hsy" (h12 n11) "%Hcs1011 %Ha0_11 Hrun".
    rewrite Eret10.
    rewrite Ekk.
    rewrite Ekk in Ha0_11.
    iDestruct "Hq" as "[%Hbadq | [_ Hq]]"; [ exfalso; lia | ].
    iDestruct "Heq" as "[%Hbade | [_ Heq]]"; [ exfalso; lia | ].
    assert (Hk11 : forall r : mword 5, ucallee_saved_idx r = true ->
                   n11 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr; rewrite (Hcs1011 r Hr); exact (Hk10 r Hr)).
      pose (q := ushp_toklen (len - cur') cur' f).
      assert (Hqe : q = ushp_toklen (len - cur') cur' f) by reflexivity.
      destruct (ushs_toks_cons_inv' len gp cur cur' q f tk rest
                  Hcure Hqe Htoks) as (Hn & Htkeq & Hrest).
      pose (e := (cur' + q)%nat).
      assert (Hee : e = (cur' + q)%nat) by reflexivity.
      assert (Hele : (e <= len)%nat);
        [ rewrite Hee Hqe;
          pose proof (ushp_toklen_le (len - cur') cur' f); lia | ].
      pose (nxt := (e + ushp_skipws (len - e) e f)%nat).
      assert (Hnxte : nxt = (e + ushp_skipws (len - e) e f)%nat)
        by reflexivity.
      assert (Hnxt : (nxt <= len)%nat);
        [ rewrite Hnxte; pose proof (ushp_skipws_le (len - e) e f); lia | ].
      (* the token is a WORD: its first byte is neither blank nor symbol,
         so gettoken takes its default arm and answers 'a' *)
      assert (Hnq : (0 < ushp_toklen (len - cur') cur' f)%nat)
        by (rewrite <- Hqe; exact Hn).
      assert (Hnsym : ushp_is_sym (f cur') = false)
        by exact (ushs_toklen_pos_nosym (len - cur')%nat cur' f Hnq).
      assert (Hcurlt : (cur' < len)%nat);
        [ pose proof (ushp_toklen_le (len - cur') cur' f); lia | ].
      assert (Hres97 : ushs_gettok_res len f cur' = 97)
        by exact (ushs_gettok_res_word len f cur' Hcurlt Hnsym).
      rewrite Hres97 in Ha0_11.
      assert (Hendv : ushs_gettok_end len f cur' = e);
        [ rewrite (ushs_gettok_end_word len f cur' Hcurlt Hnsym) Hee Hqe;
          reflexivity | ].
      assert (Hfin : ushs_gettok_fin len f cur' = nxt);
        [ rewrite /ushs_gettok_fin; cbv zeta; rewrite Hendv;
          exact (eq_sym Hnxte) | ].
      rewrite Hendv Hfin.
      (* ---- 0x616  c.beqz a0 -- NOT taken ---- *)
      iApply (wp_uk_cbeqz N h12 n11 (mword_of_int 0x616)
                (mword_of_int 20 : mword 8) (mword_of_int 2 : mword 3)
                a0_idx false (mword_of_int 0x63e) (24 + (8 + nn))
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0_11; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_616 with "Hcode"). }
      iIntros (h13) "Hrun".
      (* ---- 0x618  bne a0,s10 -- NOT taken: the token IS a word ---- *)
      iApply (wp_uk_btype N h13 n11 (mword_of_int 0x618)
                (mword_of_int 8140 : mword 13) s10_idx a0_idx BNE false
                (mword_of_int 0x5e4) (24 + (8 + nn))
                ltac:(cbn [uv_btaken]; rewrite Ha0_11
                        (Hk11 s10_idx ltac:(vm_compute; reflexivity)) Hs10v;
                      vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_618 with "Hcode"). }
      iIntros (h14) "Hrun".
      (* ---- 0x61c  ld a5,-120(s0) -- q ---- *)
      assert (Hs0_11 : n11 !!! Regidx s0_idx = mword_of_int fp)
        by (rewrite (Hk11 s0_idx ltac:(vm_compute; reflexivity)); exact Hs0v).
      iApply (wp_uk_ld N h14 n11 (mword_of_int 0x61c)
                (mword_of_int 3976 : mword 12) s0_idx a5_idx (DfracOwn 1)
                (fp - 120) (mword_of_int (s0 + Z.of_nat cur')) (24 + (8 + nn))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Hs0_11 (uint_moi fp Hfp64);
                      vm_compute uoff_i12; lia)
                Hq8
                ltac:(vm_compute; discriminate)
                with "[] Hq Hrun").
      { iApply (uis_shp_61c with "Hcode"). }
      iIntros "Hq" (h15) "Hrun".
      set (n12 := <[Regidx a5_idx
                    := regval_into_reg
                         (mword_of_int (s0 + Z.of_nat cur')
                          : mword 64)]> n11).
      assert (Hk12 : forall r : mword 5, ucallee_saved_idx r = true ->
                 n12 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr;
            rewrite (upd_ne n11 (Regidx a5_idx) (Regidx r) _
                       (ushp_cs_ne r a5_idx Hr
                          ltac:(vm_compute; reflexivity)));
            exact (Hk11 r Hr)).
      assert (Ha5_12 : n12 !!! Regidx a5_idx
                       = mword_of_int (s0 + Z.of_nat cur'))
        by exact (upd_eq n11 (Regidx a5_idx)
                    (regval_into_reg
                       (mword_of_int (s0 + Z.of_nat cur') : mword 64))).
      assert (Hs3_12 : n12 !!! Regidx s3_idx
                       = mword_of_int (p + 8 + 8 * Z.of_nat (length done)))
        by (rewrite (Hk12 s3_idx ltac:(vm_compute; reflexivity)); exact Hs3v).
      (* ---- 0x620  sd a5,0(s3) -- argv[argc] = q ---- *)
      iDestruct "Hnode" as "(%Hdl & _ & _ & Hty & Hav & Hev)".
      iDestruct (ushp_slots_upd s0 (p + 8) done tk fst Hnodelen with "Hav")
        as "[Hav0 Havc]".
      iApply (wp_uk_sd N h15 n12 (mword_of_int 0x620)
                (mword_of_int 0 : mword 12) s3_idx a5_idx
                (p + 8 + 8 * Z.of_nat (length done)) (mword_of_int 0)
                (24 + (8 + nn))
                ltac:(rewrite Hs3_12
                        (uint_moi (p + 8 + 8 * Z.of_nat (length done))
                           ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_i12; lia)
                ltac:(exact (ushp_slot_al8 p 1 (length done) Hp8))
                with "[] [Hav0] Hrun").
      { iApply (uis_shp_620 with "Hcode"). }
      { iExact "Hav0". }
      iIntros "Hav0" (h16) "Hrun".
      rewrite Ha5_12.
      iDestruct ("Havc" with "[Hav0]") as "Hav";
        [ rewrite Htkeq; iExact "Hav0" | ].
      (* ---- 0x624  ld a5,-128(s0) -- eq ---- *)
      assert (Hs0_12 : n12 !!! Regidx s0_idx = mword_of_int fp)
        by (rewrite (Hk12 s0_idx ltac:(vm_compute; reflexivity)); exact Hs0v).
      iApply (wp_uk_ld N h16 n12 (mword_of_int 0x624)
                (mword_of_int 3968 : mword 12) s0_idx a5_idx (DfracOwn 1)
                (fp - 128) (mword_of_int (s0 + Z.of_nat e)) (24 + (8 + nn))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Hs0_12 (uint_moi fp Hfp64);
                      vm_compute uoff_i12; lia)
                Hfp8
                ltac:(vm_compute; discriminate)
                with "[] Heq Hrun").
      { iApply (uis_shp_624 with "Hcode"). }
      iIntros "Heq" (h17) "Hrun".
      set (n13 := <[Regidx a5_idx
                    := regval_into_reg
                         (mword_of_int (s0 + Z.of_nat e) : mword 64)]> n12).
      assert (Hk13 : forall r : mword 5, ucallee_saved_idx r = true ->
                 n13 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr;
            rewrite (upd_ne n12 (Regidx a5_idx) (Regidx r) _
                       (ushp_cs_ne r a5_idx Hr
                          ltac:(vm_compute; reflexivity)));
            exact (Hk12 r Hr)).
      assert (Ha5_13 : n13 !!! Regidx a5_idx
                       = mword_of_int (s0 + Z.of_nat e))
        by exact (upd_eq n12 (Regidx a5_idx)
                    (regval_into_reg
                       (mword_of_int (s0 + Z.of_nat e) : mword 64))).
      assert (Hs3_13 : n13 !!! Regidx s3_idx
                       = mword_of_int (p + 8 + 8 * Z.of_nat (length done)))
        by (rewrite (Hk13 s3_idx ltac:(vm_compute; reflexivity)); exact Hs3v).
      (* ---- 0x628  sd a5,80(s3) -- eargv[argc] = eq ---- *)
      iDestruct (ushp_slots_upd s0 (p + 88) done tk snd Hnodelen with "Hev")
        as "[Hev0 Hevc]".
      iApply (wp_uk_sd N h17 n13 (mword_of_int 0x628)
                (mword_of_int 80 : mword 12) s3_idx a5_idx
                (p + 88 + 8 * Z.of_nat (length done)) (mword_of_int 0)
                (24 + (8 + nn))
                ltac:(rewrite Hs3_13
                        (uint_moi (p + 8 + 8 * Z.of_nat (length done))
                           ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_i12; lia)
                ltac:(exact (ushp_slot_al8 p 11 (length done) Hp8))
                with "[] [Hev0] Hrun").
      { iApply (uis_shp_628 with "Hcode"). }
      { iExact "Hev0". }
      iIntros "Hev0" (h18) "Hrun".
      rewrite Ha5_13.
      iDestruct ("Hevc" with "[Hev0]") as "Hev";
        [ rewrite Htkeq; iExact "Hev0" | ].
      (* ---- 0x62c  c.addiw s2,s2,1 -- argc++ ---- *)
      assert (Hs2_13 : n13 !!! Regidx s2_idx
                       = mword_of_int (Z.of_nat (length done)))
        by (rewrite (Hk13 s2_idx ltac:(vm_compute; reflexivity)); exact Hs2v).
      assert (Esx : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                    = mword_of_int 1)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_caddiw N h18 n13 (mword_of_int 0x62c)
                (mword_of_int 1 : mword 6) s2_idx
                (mword_of_int (Z.of_nat (length done) + 1)) (24 + (8 + nn))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs2_13 Esx; symmetry;
                      exact (moi_addw (Z.of_nat (length done)) 1
                               ltac:(unfold Z31; lia)))
                with "[] Hrun").
      { iApply (uis_shp_62c with "Hcode"). }
      iIntros (h19) "Hrun".
      set (n14 := <[Regidx s2_idx
                    := regval_into_reg
                         (mword_of_int (Z.of_nat (length done) + 1)
                          : mword 64)]> n13).
      assert (Hk14 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s2_idx ->
                 n14 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr2;
            rewrite (upd_ne n13 (Regidx s2_idx) (Regidx r) _ Hr2);
            exact (Hk13 r Hr)).
      assert (Hs2_14 : n14 !!! Regidx s2_idx
                       = mword_of_int (Z.of_nat (length done) + 1))
        by exact (upd_eq n13 (Regidx s2_idx)
                    (regval_into_reg
                       (mword_of_int (Z.of_nat (length done) + 1)
                        : mword 64))).
      (* ---- 0x62e  bne s2,s9 -- TAKEN: MAXARGS is not reached ---- *)
      iApply (wp_uk_btype N h19 n14 (mword_of_int 0x62e)
                (mword_of_int 8130 : mword 13) s9_idx s2_idx BNE true
                (mword_of_int 0x5f0) (24 + (8 + nn))
                ltac:(cbn [uv_btaken]; rewrite Hs2_14
                        (Hk14 s9_idx ltac:(vm_compute; reflexivity)
                           ltac:(vm_compute; discriminate)) Hs9v;
                      rewrite (moi_neq_vec (Z.of_nat (length done) + 1) 10
                                 ltac:(unfold Z64; cbn [length] in Hcnt; lia)
                                 ltac:(unfold Z64; lia));
                      assert (Hne : (Z.of_nat (length done) + 1 =? 10)
                                    = false)
                        by (apply Z.eqb_neq; cbn [length] in Hcnt; lia);
                      rewrite Hne; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_62e with "Hcode"). }
      iIntros (h20) "Hrun".
      (* ---- 0x5f0  c.addi s3,s3,8 ---- *)
      assert (Hs3_14 : n14 !!! Regidx s3_idx
                       = mword_of_int (p + 8 + 8 * Z.of_nat (length done)))
        by (rewrite (Hk14 s3_idx ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; discriminate)); exact Hs3v).
      assert (Esx8 : (sign_extend' 64 (mword_of_int 8 : mword 6) : mword 64)
                     = mword_of_int 8)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_caddi N h20 n14 (mword_of_int 0x5f0)
                (mword_of_int 8 : mword 6) s3_idx
                (mword_of_int (p + 8 + 8 * Z.of_nat (length done) + 8))
                (24 + (8 + nn))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs3_14 Esx8; symmetry; apply moi_add)
                with "[] Hrun").
      { iApply (uis_shp_5f0 with "Hcode"). }
      iIntros (h21) "Hrun".
      set (n15 := <[Regidx s3_idx
                    := regval_into_reg
                         (mword_of_int
                            (p + 8 + 8 * Z.of_nat (length done) + 8)
                          : mword 64)]> n14).
      assert (Hk15 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s2_idx -> Regidx r <> Regidx s3_idx ->
                 n15 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr2 Hr3;
            rewrite (upd_ne n14 (Regidx s3_idx) (Regidx r) _ Hr3);
            exact (Hk14 r Hr Hr2)).
      (* ---- 0x5f2..0x5f6  parseredirs(ret, ps, es) ---- *)
      iApply (wp_uk_cmv N h21 n15 (mword_of_int 0x5f2) a2_idx
                s5_idx (mword_of_int (s0 + Z.of_nat len)) (24 + (8 + nn))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hk15 s5_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)) Hs5v;
                      symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
                with "[] Hrun").
      { iApply (uis_shp_5f2 with "Hcode"). }
      iIntros (h22) "Hrun".
      set (n16 := <[Regidx a2_idx
                    := regval_into_reg
                         (mword_of_int (s0 + Z.of_nat len)
                          : mword 64)]> n15).
      assert (Hk16 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s2_idx -> Regidx r <> Regidx s3_idx ->
                 n16 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr2 Hr3;
            rewrite (upd_ne n15 (Regidx a2_idx) (Regidx r) _
                       (ushp_cs_ne r a2_idx Hr
                          ltac:(vm_compute; reflexivity)));
            exact (Hk15 r Hr Hr2 Hr3)).
      iApply (wp_uk_cmv N h22 n16 (mword_of_int 0x5f4) a1_idx
                s4_idx (mword_of_int ps) (24 + (8 + nn))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hk16 s4_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)) Hs4v;
                      symmetry; exact (ushp_mv_val ps))
                with "[] Hrun").
      { iApply (uis_shp_5f4 with "Hcode"). }
      iIntros (h23) "Hrun".
      set (n17 := <[Regidx a1_idx
                    := regval_into_reg (mword_of_int ps : mword 64)]> n16).
      assert (Hk17 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s2_idx -> Regidx r <> Regidx s3_idx ->
                 n17 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr2 Hr3;
            rewrite (upd_ne n16 (Regidx a1_idx) (Regidx r) _
                       (ushp_cs_ne r a1_idx Hr
                          ltac:(vm_compute; reflexivity)));
            exact (Hk16 r Hr Hr2 Hr3)).
      iApply (wp_uk_cmv N h23 n17 (mword_of_int 0x5f6) a0_idx
                s1_idx (mword_of_int p) (24 + (8 + nn))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hk17 s1_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)) Hs1v;
                      symmetry; exact (ushp_mv_val p))
                with "[] Hrun").
      { iApply (uis_shp_5f6 with "Hcode"). }
      iIntros (h24) "Hrun".
      set (n18 := <[Regidx a0_idx
                    := regval_into_reg (mword_of_int p : mword 64)]> n17).
      assert (Hk18 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s2_idx -> Regidx r <> Regidx s3_idx ->
                 n18 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr2 Hr3;
            rewrite (upd_ne n17 (Regidx a0_idx) (Regidx r) _
                       (ushp_cs_ne r a0_idx Hr
                          ltac:(vm_compute; reflexivity)));
            exact (Hk17 r Hr Hr2 Hr3)).
      (* ---- 0x5f8  jal 488 <parseredirs> ---- *)
      iApply (wp_uk_jal N h24 n18 (mword_of_int 0x5f8)
                (mword_of_int 2096784 : mword 21) ra_idx
                (mword_of_int 0x488) (mword_of_int 0x5fc) (24 + (8 + nn))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_5f8 with "Hcode"). }
      iIntros (h25) "Hrun".
      set (n19 := <[Regidx ra_idx
                    := regval_into_reg
                         (mword_of_int 0x5fc : mword 64)]> n18).
      assert (Hk19 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s2_idx -> Regidx r <> Regidx s3_idx ->
                 n19 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr2 Hr3;
            rewrite (upd_ne n18 (Regidx ra_idx) (Regidx r) _
                       (ushp_cs_ne r ra_idx Hr
                          ltac:(vm_compute; reflexivity)));
            exact (Hk18 r Hr Hr2 Hr3)).
      assert (Eret19 : ret_pc (n19 !!! Regidx ra_idx)
                       = mword_of_int 0x5fc);
        [ rewrite (upd_eq n18 (Regidx ra_idx)
                     (regval_into_reg (mword_of_int 0x5fc : mword 64)));
          apply bv_eq; vm_compute; reflexivity | ].
      assert (Ha0_19 : n19 !!! Regidx a0_idx = mword_of_int p);
        [ rewrite (upd_ne n18 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate));
          exact (upd_eq n17 (Regidx a0_idx)
                   (regval_into_reg (mword_of_int p : mword 64))) | ].
      assert (Ha1_19 : n19 !!! Regidx a1_idx = mword_of_int ps);
        [ rewrite (upd_ne n18 (Regidx ra_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate));
          rewrite (upd_ne n17 (Regidx a0_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate));
          exact (upd_eq n16 (Regidx a1_idx)
                   (regval_into_reg (mword_of_int ps : mword 64))) | ].
      assert (Ha2_19 : n19 !!! Regidx a2_idx
                       = mword_of_int (s0 + Z.of_nat len));
        [ rewrite (upd_ne n18 (Regidx ra_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate));
          rewrite (upd_ne n17 (Regidx a0_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate));
          rewrite (upd_ne n16 (Regidx a1_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate));
          exact (upd_eq n15 (Regidx a2_idx)
                   (regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64))) | ].
      rewrite <- shpp_parseredirs.
      (* NO SPLIT: on the pipe line every round closes the same way. *)
      assert (Hnz : ushp_skipws (len - nxt) nxt f = 0%nat)
        by exact (ushp_skipws_idem len e f Hele).
      assert (Htnxt : ushs_toks len f gp nxt rest)
        by exact (ushs_toks_skip len gp f e rest Hele Hrest).
      (* THE ONE THING THAT DIFFERS FROM THE REDIRECT LOOP, and it is
         uniform: [parseredirs]' peek MISSES wherever this round leaves the
         cursor.  Either an argument is still to come, and the byte there is
         a word byte (so no symbol at all), or none is, and the byte is the
         '|' -- which is not one of the two redirection bytes either.  The
         landed walk asks for "no symbol", which the second case falsifies;
         [UkShPipePr.wp_kshp_parseredirs_miss] asks only for the miss. *)
      assert (Hmiss2 : ushp_peek_res len f
                         (nxt + ushp_skipws (len - nxt) nxt f)%nat 2
                         (ushp_lit ushp_T_redir) = 0).
      { destruct rest as [| tk2 rest2 ].
        - assert (Hgpn : (nxt + ushp_skipws (len - nxt) nxt f)%nat = gp)
            by exact (ushs_toks_nil_inv len gp nxt f Htnxt).
          rewrite Hgpn.
          exact (UkShPipeEx.ushp_peek_redir_miss_bar len f gp
                   (ushq_barw_bar len f gp Hpq)).
        - apply (UkShRedirPr.ushs_peek_res_nsym len f
                   (nxt + ushp_skipws (len - nxt) nxt f)%nat 2
                   ushp_T_redir).
          + intros _.
            destruct (ushs_toks_cons_inv len gp nxt f tk2 rest2 Htnxt)
              as (Hn2 & _ & _).
            exact (ushs_toklen_pos_nosym _ _ f Hn2).
          + exact ushp_T_redir_sym. }
      iApply (UkShPipePr.wp_kshp_parseredirs_miss N h25 n19 dq dw p ps s0
                len nxt f (mword_of_int (s0 + Z.of_nat nxt)) (8 + nn)
                Ha0_19 Ha1_19 Ha2_19 Hnxt eq_refl Hmiss2 Hs0 Hs64
                Hps0 Hps8 Hpssz
                with "Hcode Hro Hcur Hstr Hws Hrun").
      iIntros "Hcur Hstr Hws" (h26 n20) "%Hcs1920 %Ha0_20 Hrun".
      rewrite Eret19.
      assert (Enx : (nxt + ushp_skipws (len - nxt) nxt f)%nat = nxt)
        by (rewrite Hnz; lia).
      rewrite Enx.
      assert (Hk20 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s2_idx -> Regidx r <> Regidx s3_idx ->
                 n20 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr2 Hr3; rewrite (Hcs1920 r Hr);
            exact (Hk19 r Hr Hr2 Hr3)).
      (* ---- 0x5fc  c.mv s1,a0 ---- *)
      iApply (wp_uk_cmv N h26 n20 (mword_of_int 0x5fc) s1_idx
                a0_idx (mword_of_int p) (24 + (8 + nn))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha0_20; symmetry; exact (ushp_mv_val p))
                with "[] Hrun").
      { iApply (uis_shp_5fc with "Hcode"). }
      iIntros (h27) "Hrun".
      set (n21 := <[Regidx s1_idx
                    := regval_into_reg (mword_of_int p : mword 64)]> n20).
      assert (Hk21 : forall r : mword 5, ucallee_saved_idx r = true ->
                 Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
                 Regidx r <> Regidx s3_idx ->
                 n21 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr Hr1 Hr2 Hr3;
            rewrite (upd_ne n20 (Regidx s1_idx) (Regidx r) _ Hr1);
            exact (Hk20 r Hr Hr2 Hr3)).
      assert (Hs3_15 : n15 !!! Regidx s3_idx
                       = mword_of_int
                           (p + 8 + 8 * Z.of_nat (length done) + 8))
        by exact (upd_eq n14 (Regidx s3_idx)
                    (regval_into_reg
                       (mword_of_int
                          (p + 8 + 8 * Z.of_nat (length done) + 8)
                        : mword 64))).
      assert (HIs3 : n21 !!! Regidx s3_idx
                     = mword_of_int
                         (p + 8 + 8 * Z.of_nat (length (done ++ [tk])))).
      { rewrite ushp_len_app1.
        rewrite (upd_ne n20 (Regidx s1_idx) (Regidx s3_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (Hcs1920 s3_idx ltac:(vm_compute; reflexivity)).
        rewrite (upd_ne n18 (Regidx ra_idx) (Regidx s3_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne n17 (Regidx a0_idx) (Regidx s3_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne n16 (Regidx a1_idx) (Regidx s3_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne n15 (Regidx a2_idx) (Regidx s3_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite Hs3_15. f_equal. rewrite Nat2Z.inj_succ. lia. }
      (* ---- and round again, with the token banked ---- *)
      iApply (IH (done ++ [tk]) nxt h27 n21
                (mword_of_int (s0 + Z.of_nat cur'))
                (mword_of_int (s0 + Z.of_nat e))
                Hpq Hs0 Hs64 Hps0 Hps8 Hpssz Hfp0 Hfp8 Hfpl Hfph
                Hp0 Hp8 Hpsz Hnxt
                ltac:(rewrite ushp_len_app1; cbn [length] in Hcnt |- *; lia)
                ltac:(exact Htnxt)
                ltac:(rewrite (Hk21 s0_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs0v)
                ltac:(exact (upd_eq n20 (Regidx s1_idx)
                               (regval_into_reg (mword_of_int p : mword 64))))
                ltac:(rewrite ushp_len_app1;
                      rewrite (upd_ne n20 (Regidx s1_idx) (Regidx s2_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (Hcs1920 s2_idx ltac:(vm_compute; reflexivity));
                      rewrite (upd_ne n18 (Regidx ra_idx) (Regidx s2_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne n17 (Regidx a0_idx) (Regidx s2_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne n16 (Regidx a1_idx) (Regidx s2_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne n15 (Regidx a2_idx) (Regidx s2_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne n14 (Regidx s3_idx) (Regidx s2_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite Hs2_14; f_equal; lia)
                HIs3
                ltac:(rewrite (Hk21 s4_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs4v)
                ltac:(rewrite (Hk21 s5_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs5v)
                ltac:(rewrite (Hk21 s6_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs6v)
                ltac:(rewrite (Hk21 s7_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs7v)
                ltac:(rewrite (Hk21 s8_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs8v)
                ltac:(rewrite (Hk21 s9_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs9v)
                ltac:(rewrite (Hk21 s10_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs10v)
                ltac:(rewrite (Hk21 s11_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs11v)
                with "Hcode Hro [Hty Hav Hev] Hcur Hq Heq Hstr Hws Hsy Hrun").
      { rewrite /ushp_exec_pre.
        iSplitR; [ iPureIntro; rewrite ushp_len_app1;
                   cbn [length] in Hcnt; lia | ].
        iSplitR; [ iPureIntro; exact Hp0 | ].
        iSplitR; [ iPureIntro; exact Hp8 | ].
        iFrame "Hav Hev". rewrite /ushp_type_at. iExact "Hty". }      iIntros "Hnode Hcur Hq Heq Hstr Hws Hsy".
      iIntros (hf mf) "%Hpres %Hs2f %Hs1f Hrun".
      rewrite ushp_app_cons.
      iApply ("Hcont" with "Hnode Hcur Hq Heq Hstr Hws Hsy [] [] [] Hrun").
      - iPureIntro. intros r Hr Hr1 Hr2 Hr3.
        rewrite (Hpres r Hr Hr1 Hr2 Hr3). exact (Hk21 r Hr Hr1 Hr2 Hr3).
      - iPureIntro. rewrite Hs2f ushp_len_app1. f_equal. cbn [length]. lia.
      - iPureIntro. exact Hs1f.
  Qed.

  Lemma wp_kshp_pex_loop_bar (dq dw dv : dfrac)
      (s0 ps p fp : Z) (len : nat) (f : nat -> bv 8) (gp ge : nat)
      (nn : nat) :
    forall (rest done : list (nat * nat)) (cur : nat) (h : CpuId)
           (mc : regfile) (wq weq : mword 64),
    ushq_pipe len f gp ge ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    0 < fp - 128 -> (fp - 128) mod 8 = 0 -> 0 <= fp -> fp < Z64 ->
    0 < p -> p mod 8 = 0 -> p + 168 < Z64 ->
    (cur <= len)%nat ->
    (length done + length rest < 10)%nat ->
    ushs_toks len f gp cur rest ->
    mc !!! Regidx s0_idx = mword_of_int fp ->
    mc !!! Regidx s1_idx = mword_of_int p ->
    mc !!! Regidx s2_idx = mword_of_int (Z.of_nat (length done)) ->
    mc !!! Regidx s3_idx
      = mword_of_int (p + 8 + 8 * Z.of_nat (length done)) ->
    mc !!! Regidx s4_idx = mword_of_int ps ->
    mc !!! Regidx s5_idx = mword_of_int (s0 + Z.of_nat len) ->
    mc !!! Regidx s6_idx = mword_of_int ushp_T_arg ->
    mc !!! Regidx s7_idx = mword_of_int (fp - 120) ->
    mc !!! Regidx s8_idx = mword_of_int (fp - 128) ->
    mc !!! Regidx s9_idx = mword_of_int 10 ->
    mc !!! Regidx s10_idx = mword_of_int 97 ->
    mc !!! Regidx s11_idx = mword_of_int p ->
    shp_code γt -∗
    shp_rodata γt -∗
    ushp_exec_pre s0 p done -∗
    uword γd ps (mword_of_int (s0 + Z.of_nat cur)) -∗
    uword γd (fp - 120) wq -∗
    uword γd (fp - 128) weq -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    urun N h mc (mword_of_int 0x5fe) (24 + (8 + nn)) -∗
    (ushp_exec_pre s0 p (done ++ rest) -∗
     uword γd ps (mword_of_int (s0 + Z.of_nat gp)) -∗
     (∃ w : mword 64, uword γd (fp - 120) w) -∗
     (∃ w : mword 64, uword γd (fp - 128) w) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
     ustr γd dv ushp_symbols 7 ushp_sym_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall r : mword 5, ucallee_saved_idx r = true ->
             Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
             Regidx r <> Regidx s3_idx ->
             mc' !!! Regidx r = mc !!! Regidx r ⌝ -∗
         ⌜ mc' !!! Regidx s2_idx
             = mword_of_int (Z.of_nat (length done + length rest)) ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx = mword_of_int p ⌝ -∗
         urun N h' mc' (mword_of_int 0x63e) (24 + (8 + nn)) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros rest done cur h mc wq weq Hpq.
    exact (wp_kshp_pex_loop_barw dq dw dv s0 ps p fp len f gp nn
             rest done cur h mc wq weq (ushq_barw_of_pipe len f gp ge Hpq)).
  Qed.

End UkShPipeEx2.
