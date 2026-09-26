(* ===================================================================== *)
(* UkShRedirEx.v -- parseexec's ARGUMENT LOOP on the REDIRECT LINE,       *)
(* lane SH-PARSE-2 (design/app-file.md SS5.1) -- AS COROLLARIES of the    *)
(* general walk (design/user-once.md SS2, worklist A2c).                   *)
(*                                                                        *)
(* The two statements here are the landed ones, unchanged:                *)
(*                                                                        *)
(*   [wp_kshp_pex_end]      the round that finds the line exhausted --    *)
(*                          UkShArgs.wp_ref_pex_exit at the peek that    *)
(*                          missed at the end and gettoken's NUL there;   *)
(*   [wp_kshp_pex_loop_gt]  the loop at [ushs_toks] ending in the '>'     *)
(*                          with the REDIR node re-rooting [ret] --        *)
(*                          UkShArgs.wp_ref_pex_loop at the reference's    *)
(*                          answer on the redirect line                    *)
(*                          (RefParseSym.ref_args_of_toks_redir: the       *)
(*                          tokens, ONE redirect, cursor at the end), the  *)
(*                          one allocation as a chain of length one.       *)
(*                                                                        *)
(* The walks that used to live here -- the exhausted round, the loop with *)
(* its tail split into the turning and the non-turning parseredirs -- are *)
(* UkShArgs's, once.  Consumer: UkShRedirPex.                              *)
(*                                                                        *)
(* TAINT: [ushp_malloc_ok], through [redircmd] inside the turn.           *)
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
Require UkShCmdalloc.
Require Import UkShParseSym.
Require Import UkShParseLex.
Require Import UkShRedirCmd.
Require Import RefParse.
Require Import RefParseSym.
Require Import UkShRedirs.
Require Import UkShArgs.

Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Section UkShRedirEx.
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
  Local Notation ushp_redir_node := (UkShRedirCmd.ushp_redir_node N).
  Local Notation ushp_redir_close := (UkShRedirCmd.ushp_redir_close N).
  Local Notation wp_kshp_peek := (UkShParseLex.wp_kshp_peek N).
  Local Notation wp_kshp_restore := (UkShParse.wp_kshp_restore N).
  Local Notation wp_kshp_spill := (UkShParse.wp_kshp_spill N).

  (* stage 4's one Hypothesis, at the type the base file names *)
  Context (UMalloc UMalloc' : iProp Σ).
  Hypothesis ushp_malloc_ok : ushp_malloc_ty UMalloc UMalloc'.
  Local Notation ushp_oom := (UkShCmdalloc.ushp_oom N).


  (* ===================================================================== *)
  (* §11a THE ROUND THAT LEAVES THE LOOP, at the end of the line.           *)
  (* ===================================================================== *)

  Lemma wp_kshp_pex_end (dq dw dv : dfrac) (s0 ps fp : Z)
      (len : nat) (f : nat -> bv 8) (nn cur : nat) (h : CpuId)
      (mc : regfile) (wq weq : mword 64) :
    ushs_gt_ok len f ->
    (cur <= len)%nat ->
    (cur + ushp_skipws (len - cur) cur f)%nat = len ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    0 < fp - 128 -> (fp - 128) mod 8 = 0 -> 0 <= fp -> fp < Z64 ->
    mc !!! Regidx s4_idx = mword_of_int ps ->
    mc !!! Regidx s5_idx = mword_of_int (s0 + Z.of_nat len) ->
    mc !!! Regidx s6_idx = mword_of_int ushp_T_arg ->
    mc !!! Regidx s7_idx = mword_of_int (fp - 120) ->
    mc !!! Regidx s8_idx = mword_of_int (fp - 128) ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps (mword_of_int (s0 + Z.of_nat cur)) -∗
    uword γd (fp - 120) wq -∗
    uword γd (fp - 128) weq -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    urun N h mc (mword_of_int 0x5fe) (24 + nn) -∗
    (uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
     (∃ w : mword 64, uword γd (fp - 120) w) -∗
     (∃ w : mword 64, uword γd (fp - 128) w) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
     ustr γd dv ushp_symbols 7 ushp_sym_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall r : mword 5, ucallee_saved_idx r = true ->
             mc' !!! Regidx r = mc !!! Regidx r ⌝ -∗
         urun N h' mc' (mword_of_int 0x63e) (24 + nn) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hgtok Hcur Hstop Hs0 Hs64 Hps0 Hps8 Hpssz
      Hfp0 Hfp8 Hfpl Hfph Hs4v Hs5v Hs6v Hs7v Hs8v.
    iIntros "#Hcode #Hro Hcur Hq Heq Hstr Hws Hsy Hrun Hcont".
    (* the blank scan reaches the end: peek misses every set there, and
       gettoken answers NUL at the end *)
    assert (Hskip : ref_skip len f cur = len) by exact Hstop.
    iApply (UkShArgs.wp_ref_pex_exit N dq dw dv s0 ps fp len f nn cur h mc wq weq
              false len len len len Hcur
              (ref_peek_end len f cur _ Hskip ref_symtoks_stop)
              (fun _ => ushs_gt_ok_scope len f Hgtok)
              (fun _ => ref_gettoken_nul len f len (ref_skip_at_len len f))
              Hs0 Hs64 Hps0 Hps8 Hpssz
              (fun _ => conj Hfp0 (conj Hfp8 (conj Hfpl Hfph))) Hs4v Hs5v Hs6v
              (fun _ => Hs7v) (fun _ => Hs8v)
              with "Hcode Hro Hcur [Hq Heq Hsy] Hstr Hws Hrun").
    { rewrite /UkShArgs.ushp_pex_gtk_in. iFrame "Hq Heq Hsy". }
    iIntros "Hcur Hout Hstr Hws" (h' mc') "%Hpres Hrun".
    rewrite /UkShArgs.ushp_pex_gtk_out. iDestruct "Hout" as "(Hq & Heq & Hsy)".
    iApply ("Hcont" with "Hcur Hq Heq Hstr Hws Hsy [] Hrun").
    iPureIntro. exact Hpres.
  Qed.


  (* ===================================================================== *)
  (* §11b THE ARGUMENT LOOP, on the redirect line.                          *)
  (* ===================================================================== *)

  Lemma wp_kshp_pex_loop_gt {Pex : iProp Σ} (dq dw dv : dfrac)
      (s0 ps p fp : Z) (len : nat) (f : nat -> bv 8) (gp fe : nat)
      (nn : nat) :
    forall (rest done : list (nat * nat)) (cur : nat) (h : CpuId)
           (mc : regfile) (wq weq : mword 64),
    ushs_redir len f gp fe ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    0 < fp - 128 -> (fp - 128) mod 8 = 0 -> 0 <= fp -> fp < Z64 ->
    0 < p -> p mod 8 = 0 -> p + 168 < Z64 ->
    (cur <= len)%nat ->
    (length done + length rest < 10)%nat ->
    (0 < length rest)%nat ->
    ushs_toks len f gp cur rest ->
    (((cur + ushp_skipws (len - cur) cur f)%nat < len)%nat ->
     ushp_is_sym (f (cur + ushp_skipws (len - cur) cur f)%nat) = false) ->
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
    UMalloc -∗
    ushp_oom Pex (10 + nn) -∗
    Pex -∗
    ushp_exec_pre s0 p done -∗
    uword γd ps (mword_of_int (s0 + Z.of_nat cur)) -∗
    uword γd (fp - 120) wq -∗
    uword γd (fp - 128) weq -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    urun N h mc (mword_of_int 0x5fe) (24 + (12 + nn)) -∗
    (∀ t : Z,
     ushp_exec_pre s0 p (done ++ rest) -∗
     ushp_redir_node s0 t p (S (S gp)) fe 1537 1 -∗
     uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
     (∃ w : mword 64, uword γd (fp - 120) w) -∗
     (∃ w : mword 64, uword γd (fp - 128) w) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
     ustr γd dv ushp_symbols 7 ushp_sym_f -∗
     UMalloc' -∗
     Pex -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall r : mword 5, ucallee_saved_idx r = true ->
             Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
             Regidx r <> Regidx s3_idx ->
             mc' !!! Regidx r = mc !!! Regidx r ⌝ -∗
         ⌜ mc' !!! Regidx s2_idx
             = mword_of_int (Z.of_nat (length done + length rest)) ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx = mword_of_int t ⌝ -∗
         urun N h' mc' (mword_of_int 0x63e) (24 + (12 + nn)) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using ushp_malloc_ok.
    intros rest done cur h mc wq weq Hred Hs0 Hs64 Hps0 Hps8 Hpssz
      Hfp0 Hfp8 Hfpl Hfph Hp0 Hp8 Hpsz Hcur Hcnt Hpos Htoks _
      Hs0v Hs1v Hs2v Hs3v Hs4v Hs5v Hs6v Hs7v Hs8v Hs9v Hs10v Hs11v.
    iIntros "#Hcode #Hro HM #Hpx Hpay Hnode Hcur Hq Heq Hstr Hws Hsy Hrun Hcont".
    iDestruct (ustr_nonul with "Hstr") as %Hnonul.
    (* the reference on this line: the tokens, then the last argument's
       parseredirs consumes `> file', and the line is exhausted *)
    assert (Href : ref_args len f (length rest + 2) cur done []
                   = Some (done ++ rest,
                           [] ++ ({| rr_q := S (S gp); rr_eq := fe;
                                     rr_mode := rr_mode_gt; rr_fd := 1 |} :: []),
                           len))
      by exact (ref_args_of_toks_redir len f cur gp fe rest done [] (length rest + 2)
                  Hnonul Hred (ushs_toks_le _ _ _ _ _ Htoks) Htoks Hpos Hcnt
                  ltac:(lia)).
    iApply (UkShArgs.wp_ref_pex_loop N (Pex := Pex) dq dw dv s0 ps p fp len f (12 + nn)
              (length rest + 2) done (done ++ rest) []
              ({| rr_q := S (S gp); rr_eq := fe; rr_mode := rr_mode_gt; rr_fd := 1 |} :: [])
              p cur len UMalloc UMalloc' h mc wq weq
              (ushs_gt_ok_scope len f (ushs_gt_ok_redir len f gp fe Hred)) Href
              (UkShRedirs.ushp_malloc_chain_1 N UMalloc UMalloc' ushp_malloc_ok)
              (fun _ => ltac:(lia))
              Hs0 Hs64 Hps0 Hps8 Hpssz Hfp0 Hfp8 Hfpl Hfph Hp0 Hp8 Hpsz Hcur
              Hs0v Hs1v Hs2v Hs3v Hs4v Hs5v Hs6v Hs7v Hs8v Hs9v Hs10v Hs11v
              with "Hcode Hro HM [Hpay] Hnode [] Hcur Hq Heq Hstr Hws Hsy Hrun").
    { cbn [UkShArgs.ushp_pex_res]. iFrame "Hpay Hpx". }
    { cbn [UkShRedirs.ushp_redirs_at]. done. }
    iIntros (t) "Hnode Hrat Hcur Hq Heq Hstr Hws Hsy HM' Hres".
    iIntros (h' mc') "%Hpres %Hs2f %Hs1f Hrun".
    iEval (cbn [app UkShRedirs.ushp_redirs_at rr_q rr_eq rr_mode rr_fd rr_mode_gt])
      in "Hrat".
    iDestruct "Hrat" as (p1) "[Hrnode %Et]". subst p1.
    iEval (cbn [UkShArgs.ushp_pex_res]) in "Hres". iDestruct "Hres" as "[Hpay _]".
    iApply ("Hcont" $! t
              with "Hnode Hrnode Hcur Hq Heq Hstr Hws Hsy HM' Hpay [] [] [] Hrun").
    - iPureIntro. exact Hpres.
    - iPureIntro. rewrite Hs2f length_app. reflexivity.
    - iPureIntro. exact Hs1f.
  Qed.

End UkShRedirEx.
