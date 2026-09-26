(* ===================================================================== *)
(*  LinkRec.v -- THE LINK RECORD: the console-side program tier, off the  *)
(*  echo application's own links.                                        *)
(*                                                                       *)
(*  Lane LINK-GEN (claude-notes/reviews/app-file-review.md sectionD3;    *)
(*  claude-notes/design/app-file.md section 4, REVERSED).  The seven      *)
(*  console files above the links -- [UShLine], [UShPanic], [UShRest],    *)
(*  [UShEchoPay], [UEchoOut], [UInitBanner], [UInitConsK] -- were about   *)
(*  to be twinned at the FILE application, ~8,000 lines maintained twice. *)
(*  They are not: what they take from [EchoLinks]/[EchoLinksLine] is a    *)
(*  BUNDLE OF FAMILIES AND LAWS, and this file names that bundle.         *)
(*                                                                       *)
(*  THE PATTERN IS TL-7's ([UInitCons] off [echo_names],                  *)
(*  claude-notes/design/user-tree.md section 9.6(1)): every field of the  *)
(*  record is set DEFINITIONALLY by the echo instance                     *)
(*  ([echo_link_inst] below), so every landed echo lemma IS the generic   *)
(*  one at that instance -- recovered by [Definition f := f_gen           *)
(*  echo_link_inst] with no proof text -- and the echo theorem's audit    *)
(*  does not move.                                                       *)
(*                                                                       *)
(*  WHAT IS ABSTRACTED, and only this:                                   *)
(*                                                                       *)
(*   - THE TAINT [lk_T] and the era's PIN [lk_pin].  The file            *)
(*     application's pin is echo's pin AND the era's file pin            *)
(*     ([FileOut.file_era_pin]), which is why the pin is a field and not *)
(*     [EchoOut.era_pin].                                                *)
(*   - THE LINE MODEL: the alternatives a line admits and their          *)
(*     continuations.  echo's is [EchoDisc.line_alts_of (last_ws I)] with *)
(*     [a < 4]; the file's is [FileDisc.cont] at [fstate_upto] with          *)
(*     [ralt_ok].  The record exposes [lk_ab I a] (alternative [a]'s      *)
(*     output at input [I]) and [lk_apr I a] (it ends with the prompt).   *)
(*     A file alternative whose output depends on the era's FILE STATE    *)
(*     ([RCRan] at a present f) is NOT in [lk_ab]'s range -- the file     *)
(*     instance sends it to [[]] -- because a program above the links     *)
(*     names no state; cat's own round does not go through this family.   *)
(*   - THE ERA'S EXTRA STATE.  It never appears: it is hidden inside the  *)
(*     credential families, which are fields.  echo's instance sets them  *)
(*     to [EchoLinks]/[EchoLinksLine]'s own; the file's adds              *)
(*     [f0_lb vf s0] under the same existentials.                        *)
(*                                                                       *)
(*  WHAT IS NOT ABSTRACTED, because both applications share it: the era's *)
(*  ghost algebra ([EchoOut.turn] / [ps_lb] / [cs_lb] / [inp_lb] /        *)
(*  [dl_cnt] / [turn_lb] -- the file application reuses it verbatim), the *)
(*  PROLOGUE ([EchoDisc.pro_alts], /init's banner [u_banner], the prompt  *)
(*  [u_prompt]) and the two constant diagnostics [alt_panic] /            *)
(*  [alt_execfail], which [FileDisc.cont] returns at [RFFork] / [RFExec]  *)
(*  verbatim.                                                            *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import LineWords.
Require Import EchoDisc.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import EchoOut.
Require Import EchoLinks.
Require Import EchoLinksLine.
Require Import EchoLinksPro.   (* /init's prologue diagnostics *)
(* as in EchoDisc / EchoOut / EchoLinks: the Sail imports leave
   string_scope on top and [++] would elaborate as String.append. *)
Local Open Scope list_scope.

Section linkrec.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  Context `{HRg : !riscvGS Σ}.

  (* =================================================================== *)
  (*  THE RECORD                                                          *)
  (* =================================================================== *)
  Record LinkRec := MkLinkRec {
    (* ---- the era ---- *)
    lk_T : iProp Σ;
    lk_pin : nat -> era_pins -> iProp Σ;
    (* THE ECHO-SIDE ERA PIN ON ITS OWN.  [UShLine.ush_mid] and every
       read-side shape carry [EchoOut.era_pin] and NOT the era's file pin
       (the file application reuses [EchoOut]'s ghost algebra verbatim), so
       the two pins are separate fields and [lk_pin_epin] is the one-way
       projection.  At the echo application they are the same. *)
    lk_epin : nat -> era_pins -> iProp Σ;
    lk_links : iProp Σ;

    (* ---- the LINE MODEL ---- *)
    lk_ab : list (bv 8) -> nat -> list (bv 8);
    lk_apr : list (bv 8) -> nat -> Prop;
    (* THE WILD LINES (seccomp design 10.7): an input whose last line may
       have made the era's claim wild.  A block-first byte there is refused,
       so the five laws that can write one take [⌜¬ lk_wild I⌝ ∨ lk_T].
       [fun _ => False] at every era but the union's. *)
    lk_wild : list (bv 8) -> Prop;
    (* THE SHELL'S OWN TWO ALTERNATIVES ARE PER-LINE (lane LINK-GEN-2).
       At the echo application there is one line shape and the fork panic
       is the constant 3; [FileDisc.ralt_ok] admits [RFFork] only at an
       [LEchoF] line, [RCFork] only at an [LCat] one and [REcho 3] only at
       an [LEcho] one.  The panic's BYTES are uniform ([alt_panic] at all
       three); the exec-failed child's are NOT -- sh prints
       "exec %s failed" with the command name -- hence [lk_exfb]. *)
    lk_pan : list (bv 8) -> nat;
    lk_exf : list (bv 8) -> nat;
    lk_exfb : list (bv 8) -> list (bv 8);
    lk_noc : nat;

    (* ---- the credential families ---- *)
    lk_ban : nat -> era_pins -> list (bv 8) -> nat -> iProp Σ;
    lk_owed : nat -> era_pins -> list (bv 8) -> iProp Σ;
    lk_sp : nat -> era_pins -> list (bv 8) -> iProp Σ;
    lk_open : nat -> era_pins -> list (bv 8) -> iProp Σ;
    lk_blk : nat -> era_pins -> list (bv 8) -> nat -> nat -> iProp Σ;
    lk_pro : nat -> era_pins -> list (bv 8) -> iProp Σ;
    lk_sp_t : nat -> era_pins -> list (bv 8) -> iProp Σ;
    lk_open_t : nat -> era_pins -> list (bv 8) -> iProp Σ;
    lk_line : nat -> era_pins -> list (bv 8) -> iProp Σ;
    (* the two PROMPT-INDEXED families.  They are FIELDS and not a [match]
       over the four above, because a consumer names them PARTIALLY APPLIED
       ([UShKernel.sh_prompt_law (ewc_lcred T γ k)]) and a [match] on the
       index does not reduce under a binder -- the echo instance would then
       not recover the landed statement by conversion. *)
    lk_pr : nat -> era_pins -> list (bv 8) -> nat -> iProp Σ;
    lk_lpr : nat -> era_pins -> list (bv 8) -> nat -> iProp Σ;
    lk_lend : nat -> era_pins -> list (bv 8) -> iProp Σ;
    lk_rr : nat -> era_pins -> nat -> list (list mobs * bv 8) -> iProp Σ;
    (* THE READER'S RESIDUE ([UShLine.rd_res]): what the era's read link
       hands back at a window's far end beyond the delivered count -- the
       reader's two bounds on the transcript's resolution and the WRITER's
       cursor bound at the stream those bounds compute.  It is what refutes
       a credential that still owes the round's banner at a boundary the
       reader is past. *)
    lk_rres : era_pins -> list (bv 8) -> iProp Σ;
    (* THE ERA'S TURN: what [App.al_programs] hands /init's first
       instruction ([EchoOut.eturn]; the file application's
       [FileOut.fturn] is that plus the era's file pin). *)
    lk_turn : nat -> iProp Σ;

    (* ---- structure ---- *)
    lk_T_pers : Persistent lk_T;
    lk_T_tl : Timeless lk_T;
    lk_links_pers : Persistent lk_links;
    lk_pin_pers : forall k v, Persistent (lk_pin k v);
    lk_pin_tl : forall k v, Timeless (lk_pin k v);
    lk_pin_agr : forall k v v', ⊢ lk_pin k v -∗ lk_pin k v' -∗ ⌜v = v'⌝;
    lk_epin_pers : forall k v, Persistent (lk_epin k v);
    lk_epin_tl : forall k v, Timeless (lk_epin k v);
    lk_epin_agr : forall k v v', ⊢ lk_epin k v -∗ lk_epin k v' -∗ ⌜v = v'⌝;
    lk_pin_epin : forall k v, ⊢ lk_pin k v -∗ lk_epin k v;
    lk_ban_tl : forall k v I i, Timeless (lk_ban k v I i);
    lk_owed_tl : forall k v I, Timeless (lk_owed k v I);
    lk_sp_tl : forall k v I, Timeless (lk_sp k v I);
    lk_open_tl : forall k v I, Timeless (lk_open k v I);
    lk_blk_tl : forall k v I a i, Timeless (lk_blk k v I a i);
    lk_pro_tl : forall k v I, Timeless (lk_pro k v I);
    lk_sp_t_tl : forall k v I, Timeless (lk_sp_t k v I);
    lk_open_t_tl : forall k v I, Timeless (lk_open_t k v I);
    lk_line_tl : forall k v I, Timeless (lk_line k v I);
    lk_pr_tl : forall k v I p, Timeless (lk_pr k v I p);
    lk_lpr_tl : forall k v I p, Timeless (lk_lpr k v I p);
    lk_lend_tl : forall k v I, Timeless (lk_lend k v I);
    lk_rres_pers : forall v I, Persistent (lk_rres v I);
    lk_rres_tl : forall v I, Timeless (lk_rres v I);

    (* ---- the two indexed families, read at their four indices ---- *)
    lk_pr_0 : forall k v I, lk_pr k v I 0%nat = lk_owed k v I;
    lk_pr_1 : forall k v I, lk_pr k v I 1%nat = lk_sp k v I;
    lk_pr_S2 : forall k v I p, lk_pr k v I (S (S p)) = lk_open k v I;
    lk_lpr_0 : forall k v I, lk_lpr k v I 0%nat = lk_line k v I;
    lk_lpr_1 : forall k v I, lk_lpr k v I 1%nat = lk_sp_t k v I;
    lk_lpr_2 : forall k v I, lk_lpr k v I 2%nat = lk_open_t k v I;
    lk_lpr_S3 : forall k v I p,
      lk_lpr k v I (S (S (S p))) = lk_blk k v I 0%nat 0%nat;

    (* ---- the taint inhabits every shape ---- *)
    lk_ban_taint : forall k v I i, ⊢ lk_T -∗ lk_ban k v I i;
    lk_owed_taint : forall k v I, ⊢ lk_T -∗ lk_owed k v I;
    lk_sp_taint : forall k v I, ⊢ lk_T -∗ lk_sp k v I;
    lk_open_taint : forall k v I, ⊢ lk_T -∗ lk_open k v I;
    lk_blk_taint : forall k v I a i, ⊢ lk_T -∗ lk_blk k v I a i;
    lk_pro_taint : forall k v I, ⊢ lk_T -∗ lk_pro k v I;
    lk_sp_t_taint : forall k v I, ⊢ lk_T -∗ lk_sp_t k v I;
    lk_open_t_taint : forall k v I, ⊢ lk_T -∗ lk_open_t k v I;
    lk_line_taint : forall k v I, ⊢ lk_T -∗ lk_line k v I;
    lk_lend_taint : forall k v I, ⊢ lk_T -∗ lk_lend k v I;

    (* ---- the loose shapes and the tight ones ---- *)
    lk_pro_owed : forall k v I, ⊢ lk_pro k v I -∗ lk_owed k v I;
    lk_blk_owed : forall k v I a, ⊢ lk_blk k v I a 0%nat -∗ lk_owed k v I;
    lk_sp_t_sp : forall k v I, ⊢ lk_sp_t k v I -∗ lk_sp k v I;
    lk_open_t_open : forall k v I, ⊢ lk_open_t k v I -∗ lk_open k v I;
    lk_blk_0 : forall k v I a a',
      ⊢ lk_blk k v I a 0%nat -∗ lk_blk k v I a' 0%nat;
    lk_line_of_blk0 : forall k v I a,
      ⊢ lk_blk k v I a 0%nat -∗ lk_line k v I;
    lk_line_of_post : forall k v I a, lk_apr I a ->
      ⊢ lk_blk k v I a (length (lk_ab I a) - 2)%nat -∗ lk_line k v I;
    lk_line_of_pro : forall k v I, ⊢ lk_pro k v I -∗ lk_line k v I;
    lk_lend_of_blk0 : forall k v I a,
      ⊢ lk_blk k v I a 0%nat -∗ lk_lend k v I;

    (* ---- /init's banner ---- *)
    lk_ban_step : forall k v I i b Φ,
      u_banner !! i = Some b ->
      ⊢ lk_pin k v -∗ lk_links -∗ lk_ban k v I i -∗
      (lk_ban k v I (S i) -∗ Φ) -∗ out_link Uart0 k b Φ;
    lk_ban_owed : forall k v I, ⊢ lk_ban k v I 0%nat -∗ lk_owed k v I;
    (* the banner-owed credential is the round's OPEN-PROLOGUE shape, which
       is the TIGHT reading [UInitBoot]'s [Hsh_wbwc] spends
       ([EchoLinks.ewc_ban_pro]) *)
    lk_ban_pro : forall k v I, ⊢ lk_ban k v I 0%nat -∗ lk_pro k v I;
    lk_ban_done : forall k v I,
      ⊢ lk_ban k v I (length u_banner) -∗ lk_owed k v I;
    lk_ban_done_line : forall k v I,
      ⊢ lk_ban k v I (length u_banner) -∗ lk_line k v I;
    lk_ban_inp : forall k v I,
      ⊢ lk_ban k v I 0%nat -∗
      lk_ban k v I 0%nat ∗ ((inp_lb v I ∗ ⌜rest_of I = []⌝) ∨ lk_T);

    (* ---- the shell's prompt, at the loose shapes ---- *)
    lk_prompt_dollar : forall k v I b Φ,
      b = u_prompt !!! 0%nat ->
      ⊢ (⌜¬ lk_wild I⌝ ∨ lk_T) -∗ lk_pin k v -∗ lk_links -∗ lk_owed k v I -∗
      (lk_sp k v I -∗ Φ) -∗ out_link Uart0 k b Φ;
    lk_prompt_space : forall k v I b Φ,
      b = u_prompt !!! 1%nat ->
      ⊢ lk_pin k v -∗ lk_links -∗ lk_sp k v I -∗
      (lk_open k v I -∗ Φ) -∗ out_link Uart0 k b Φ;
    lk_prompt_dollar_ban : forall k v I b Φ,
      b = u_prompt !!! 0%nat ->
      ⊢ (⌜¬ lk_wild I⌝ ∨ lk_T) -∗ lk_pin k v -∗ lk_links -∗ lk_ban k v I 0%nat -∗
      (lk_sp k v I -∗ Φ) -∗ out_link Uart0 k b Φ;
    lk_read : forall k v I l,
      wl_nl ∉ l ->
      ⊢ inp_lb v (I ++ l ++ [wl_nl]) -∗ lk_open k v I -∗
      lk_owed k v (I ++ l ++ [wl_nl]);
    lk_owed_read_taint : forall k v n I ws,
      length I = n -> (0 < length ws)%nat ->
      ⊢ lk_owed k v I -∗ lk_rr k v n ws -∗ lk_T;

    (* ---- one byte of a block, and the block's end ---- *)
    lk_blk_step : forall k v I a i b Φ,
      lk_ab I a !! i = Some b ->
      ⊢ (⌜¬ lk_wild I⌝ ∨ lk_T) -∗ lk_pin k v -∗ lk_links -∗ lk_blk k v I a i -∗
      (lk_blk k v I a (S i) -∗ Φ) -∗ out_link Uart0 k b Φ;
    lk_blk_sp : forall k v I a, lk_apr I a ->
      ⊢ lk_blk k v I a (length (lk_ab I a) - 1)%nat -∗ lk_sp_t k v I;

    (* ---- the shell's prompt, at the tight shapes ---- *)
    lk_prompt_dollar_post : forall k v I a b Φ,
      lk_apr I a -> b = u_prompt !!! 0%nat ->
      ⊢ (⌜¬ lk_wild I⌝ ∨ lk_T) -∗ lk_pin k v -∗ lk_links -∗
      lk_blk k v I a (length (lk_ab I a) - 2)%nat -∗
      (lk_sp_t k v I -∗ Φ) -∗ out_link Uart0 k b Φ;
    lk_prompt_space_t : forall k v I b Φ,
      b = u_prompt !!! 1%nat ->
      ⊢ lk_pin k v -∗ lk_links -∗ lk_sp_t k v I -∗
      (lk_open_t k v I -∗ Φ) -∗ out_link Uart0 k b Φ;
    lk_prompt_dollar_line : forall k v I b Φ,
      b = u_prompt !!! 0%nat ->
      ⊢ (⌜¬ lk_wild I⌝ ∨ lk_T) -∗ lk_pin k v -∗ lk_links -∗ lk_line k v I -∗
      (lk_sp_t k v I -∗ Φ) -∗ out_link Uart0 k b Φ;
    lk_read_t : forall k v I a l,
      wl_nl ∉ l ->
      ⊢ inp_lb v (I ++ l ++ [wl_nl]) -∗ lk_open_t k v I -∗
      lk_blk k v (I ++ l ++ [wl_nl]) a 0%nat;

    (* ---- the two CONSTANT alternatives, and the panic's banner ---- *)
    lk_ab_pan : forall I, lk_ab I (lk_pan I) = alt_panic;
    lk_ab_exf : forall I, lk_ab I (lk_exf I) = lk_exfb I;
    lk_apr_exf : forall I, lk_apr I (lk_exf I);

    (* ---- the turn comes apart into the read half and round 0's
            banner-owed credential ([UInitBanner.kinit_ban0_of_eturn]) ---- *)
    (* ---- a read PAST a banner-owed boundary is the taint
            ([UShLine.ush_wb_read_holds], and lane SKELETON's [Hwbr]) ---- *)
    lk_ban_read_taint : forall k v I l, wl_nl ∉ l ->
      ⊢ lk_ban k v I 0%nat -∗ lk_rres v (I ++ l ++ [wl_nl]) -∗ lk_T;

    lk_turn0 : forall k,
      ⊢ lk_turn k -∗
        (∃ v : era_pins, lk_pin k v ∗ dl_cnt v (1/2) 0%nat ∗ inp_lb v [])
        ∗ (∃ v : era_pins, lk_pin k v ∗ lk_ban k v [] 0%nat);
    lk_panic_done : forall k v I,
      ⊢ lk_blk k v I (lk_pan I) (length (lk_ab I (lk_pan I))) -∗
        lk_ban k v I 0%nat;

    (* ---- /init's PROLOGUE DIAGNOSTICS (lane INIT-FILE).                 *)
    (*                                                                     *)
    (*  [UInitDiag] prints "init: exec sh failed" and "init: fork failed"   *)
    (*  through a family indexed by the round's CHOICE [a] and the bytes    *)
    (*  out.  The BASE is a field of its own and NOT [lk_pro], and that is  *)
    (*  a real difference between the two eras rather than a convenience:   *)
    (*  echo's base [EchoLinksPro.ewc_pro] is [wr_pban] -- [wr_pro] plus    *)
    (*  [pro_from ... = pro_fail j ++ [3]] -- and that [j] is exactly what  *)
    (*  [lk_pdiag_done_1] needs to land back in the banner-owed shape,      *)
    (*  while the FILE era's [gwc_pro] is [lm_wr_pro], which says only     *)
    (*  that the prologue is not done and loses [j] at its banner's end.    *)
    (*  So the family enters at [lk_pban], which is what the last banner    *)
    (*  byte leaves ([lk_pban_of_ban_done]), and [lk_pro_of_pban] is the    *)
    (*  sound projection back.                                             *)
    lk_pban : nat -> era_pins -> list (bv 8) -> iProp Σ;
    lk_pdiag : nat -> era_pins -> list (bv 8) -> nat -> nat -> iProp Σ;
    lk_pban_tl : forall k v I, Timeless (lk_pban k v I);
    lk_pdiag_tl : forall k v I a i, Timeless (lk_pdiag k v I a i);
    lk_pban_taint : forall k v I, ⊢ lk_T -∗ lk_pban k v I;
    lk_pdiag_taint : forall k v I a i, ⊢ lk_T -∗ lk_pdiag k v I a i;
    lk_pdiag_0 : forall k v I a, ⊢ lk_pban k v I -∗ lk_pdiag k v I a 0%nat;
    lk_pban_of_ban_done : forall k v I,
      ⊢ lk_ban k v I (length u_banner) -∗ lk_pban k v I;
    lk_pro_of_pban : forall k v I, ⊢ lk_pban k v I -∗ lk_pro k v I;
    lk_pdiag_step : forall k v I a i b Φ,
      pro_alts !!! a !! i = Some b ->
      ⊢ lk_pin k v -∗ lk_links -∗ lk_pdiag k v I a i -∗
      (lk_pdiag k v I a (S i) -∗ Φ) -∗ out_link Uart0 k b Φ;
    lk_pdiag_done_1 : forall k v I i,
      i = length (pro_alts !!! 1%nat) ->
      ⊢ lk_pdiag k v I 1%nat i -∗ lk_ban k v I 0%nat;
  }.

End linkrec.

Global Arguments LinkRec Σ {_ _}.



Global Existing Instance lk_T_pers.
Global Existing Instance lk_T_tl.
Global Existing Instance lk_links_pers.
Global Existing Instance lk_pin_pers.
Global Existing Instance lk_pin_tl.
Global Existing Instance lk_epin_pers.
Global Existing Instance lk_epin_tl.
Global Existing Instance lk_ban_tl.
Global Existing Instance lk_owed_tl.
Global Existing Instance lk_sp_tl.
Global Existing Instance lk_open_tl.
Global Existing Instance lk_blk_tl.
Global Existing Instance lk_pro_tl.
Global Existing Instance lk_sp_t_tl.
Global Existing Instance lk_open_t_tl.
Global Existing Instance lk_line_tl.
Global Existing Instance lk_pr_tl.
Global Existing Instance lk_lpr_tl.
Global Existing Instance lk_lend_tl.
Global Existing Instance lk_rres_pers.
Global Existing Instance lk_rres_tl.
Global Existing Instance lk_pban_tl.
Global Existing Instance lk_pdiag_tl.

(* ===================================================================== *)
(*  THE DERIVED FAMILIES AND LAWS -- everything a console program uses    *)
(*  beyond the record's own fields, proved ONCE over an arbitrary [L].    *)
(*                                                                       *)
(*  Each one is [EchoLinks]/[EchoLinksLine]'s landed name, and at         *)
(*  [echo_link_inst] it is CONVERTIBLE to it (the families are the        *)
(*  instance's fields, so the [match] on the prompt index and the         *)
(*  existential over the era pin are the same terms).                     *)
(* ===================================================================== *)
Section linkgen.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  Context `{HRg : !riscvGS Σ}.
  Context (L : LinkRec Σ).

  (* the block written up to its prompt; [EchoLinksLine.ewc_post] *)
  Definition lk_post (k : nat) (v : era_pins) (I : list (bv 8)) (a : nat)
    : iProp Σ := lk_blk L k v I a (length (lk_ab L I a) - 2)%nat.

  (* the shell's own panic line, [i] of its bytes out *)
  Definition lk_panic (k : nat) (v : era_pins) (I : list (bv 8)) (i : nat)
    : iProp Σ := lk_blk L k v I (lk_pan L I) i.

  (* the two with the era's pin inside, [ewc_cred] / [ewc_lcred] *)
  Definition lk_cred (k : nat) (I : list (bv 8)) (p : nat) : iProp Σ :=
    (∃ v : era_pins, lk_pin L k v ∗ lk_pr L k v I p)%I.

  Definition lk_lcred (k : nat) (I : list (bv 8)) (p : nat) : iProp Σ :=
    (∃ v : era_pins, lk_pin L k v ∗ lk_lpr L k v I p)%I.

  (* NAME THE RECORD'S OWN FIELD, do not search.  The tree carries 455
     [Timeless] instances under mostly transparent definitions, so the
     hint net cannot discriminate and one [apply _] here tries nearly all
     of them (~1.2s a site).  The field instances are exactly the leaves
     these four bottom out in. *)
  Global Instance lk_post_timeless k v I a : Timeless (lk_post k v I a).
  Proof using . rewrite /lk_post. apply lk_blk_tl. Qed.
  Global Instance lk_panic_timeless k v I i : Timeless (lk_panic k v I i).
  Proof using . rewrite /lk_panic. apply lk_blk_tl. Qed.
  Global Instance lk_cred_timeless k I p : Timeless (lk_cred k I p).
  Proof using .
    rewrite /lk_cred. apply bi.exist_timeless; intro.
    apply bi.sep_timeless; [apply lk_pin_tl | apply lk_pr_tl].
  Qed.
  Global Instance lk_lcred_timeless k I p : Timeless (lk_lcred k I p).
  Proof using .
    rewrite /lk_lcred. apply bi.exist_timeless; intro.
    apply bi.sep_timeless; [apply lk_pin_tl | apply lk_lpr_tl].
  Qed.

  (* ---- the taint inhabits the derived shapes too ---- *)
  Lemma lk_lpr_taint k v I p : lk_T L -∗ lk_lpr L k v I p.
  Proof using .
    iIntros "HT". destruct p as [| [| [| p]]];
      [ rewrite lk_lpr_0; by iApply lk_line_taint
      | rewrite lk_lpr_1; by iApply lk_sp_t_taint
      | rewrite lk_lpr_2; by iApply lk_open_t_taint
      | rewrite lk_lpr_S3; by iApply lk_blk_taint ].
  Qed.

  Lemma lk_pr_taint k v I p : lk_T L -∗ lk_pr L k v I p.
  Proof using .
    iIntros "HT". destruct p as [| [| p]];
      [ rewrite lk_pr_0; by iApply lk_owed_taint
      | rewrite lk_pr_1; by iApply lk_sp_taint
      | rewrite lk_pr_S2; by iApply lk_open_taint ].
  Qed.

  Lemma lk_lcred_taint k I p v : lk_pin L k v -∗ lk_T L -∗ lk_lcred k I p.
  Proof using .
    iIntros "#Hpin #HT". rewrite /lk_lcred. iExists v. iFrame "Hpin".
    iApply (lk_lpr_taint with "HT").
  Qed.

  (* ---- the prompt's two bytes, as ONE step family ---- *)
  Lemma lk_lpr_step k v I p b Φ :
    u_prompt !! p = Some b -> (p < 2)%nat ->
    (⌜¬ lk_wild L I⌝ ∨ lk_T L) -∗
    lk_pin L k v -∗ lk_links L -∗ lk_lpr L k v I p -∗
    (lk_lpr L k v I (S p) -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb Hp. destruct p as [| [| p]]; [| | exfalso; lia].
    - assert (Hb0 : b = u_prompt !!! 0%nat).
      { rewrite wr_prompt_head in Hb. by injection Hb. }
      iIntros "Hnw #Hpin #Hlk Hc HΦ".
      rewrite (lk_lpr_0 L) (lk_lpr_1 L).
      iApply (lk_prompt_dollar_line L k v I b Φ Hb0 with "Hnw Hpin Hlk Hc HΦ").
    - assert (Hb1 : b = u_prompt !!! 1%nat).
      { rewrite wr_prompt_tail in Hb. by injection Hb. }
      iIntros "_ #Hpin #Hlk Hc HΦ".
      rewrite (lk_lpr_1 L) (lk_lpr_2 L).
      iApply (lk_prompt_space_t L k v I b Φ Hb1 with "Hpin Hlk Hc HΦ").
  Qed.

  (* ---- the read of a line lands on the BLOCK-OWED shape ---- *)
  Lemma lk_lpr_read v I l k :
    wl_nl ∉ l ->
    inp_lb v (I ++ l ++ [wl_nl]) -∗ lk_lpr L k v I 2%nat -∗
    lk_lpr L k v (I ++ l ++ [wl_nl]) 3%nat.
  Proof using .
    intros Hl. iIntros "#HE' Hc".
    rewrite (lk_lpr_2 L) (lk_lpr_S3 L k v (I ++ l ++ [wl_nl]) 0%nat).
    iApply (lk_read_t L k v I 0%nat l Hl with "HE' Hc").
  Qed.

  (* THE READ THAT COMPLETED A LINE.  The era pin it takes is the ECHO-side
     one, because that is what [UShLine.ush_mid] carries: the credential's
     own (full) pin is read OUT of it and projected down to compare. *)
  Lemma lk_lcred_read k I l v :
    wl_nl ∉ l ->
    lk_epin L k v -∗ inp_lb v (I ++ l ++ [wl_nl]) -∗
    lk_lcred k I 2%nat -∗ lk_lcred k (I ++ l ++ [wl_nl]) 3%nat.
  Proof using .
    intros Hl. iIntros "#Hpin #HE' Hc". rewrite /lk_lcred.
    iDestruct "Hc" as (v') "[#Hpin' Hc]".
    iDestruct (lk_pin_epin L k v' with "Hpin'") as "#Hep'".
    iDestruct (lk_epin_agr L k v v' with "Hpin Hep'") as %<-.
    iExists v. iFrame "Hpin'". iApply (lk_lpr_read v I l k Hl with "HE' Hc").
  Qed.

  (* THE BANNER-OWED CREDENTIAL IS A BOUNDARY ONE ([UInitBoot]'s
     [Hsh_wbwc], and lane SKELETON's [Hwbwc]). *)
  Lemma lk_lcred_of_ban k I :
    (∃ v : era_pins, lk_pin L k v ∗ lk_ban L k v I 0%nat) -∗
    lk_lcred k I 0%nat.
  Proof using .
    iIntros "Hc". iDestruct "Hc" as (v) "[#Hpin Hb]".
    rewrite /lk_lcred. iExists v. iFrame "Hpin". rewrite (lk_lpr_0 L).
    iApply (lk_line_of_pro L k v I). iApply (lk_ban_pro L k v I with "Hb").
  Qed.

  (* ---- the block owed IS a boundary credential ---- *)
  Lemma lk_lpr_blk_line k v I : lk_lpr L k v I 3%nat -∗ lk_lpr L k v I 0%nat.
  Proof using .
    rewrite (lk_lpr_S3 L k v I 0%nat) (lk_lpr_0 L).
    iApply (lk_line_of_blk0 L k v I 0%nat).
  Qed.

  Lemma lk_lcred_blk_line k I : lk_lcred k I 3%nat -∗ lk_lcred k I 0%nat.
  Proof using .
    rewrite /lk_lcred. iIntros "Hc". iDestruct "Hc" as (v) "[#Hpin Hc]".
    iExists v. iFrame "Hpin". iApply (lk_lpr_blk_line with "Hc").
  Qed.

  (* ---- what a child's block hands back: at whatever alternative the
         child took ([EchoLinksLine.ewc_lcred_of_post_a]; echo's own is
         [a = 0], the exec-failed child's [a = lk_exf]) ---- *)
  Lemma lk_lcred_of_post_a k I a v :
    lk_apr L I a ->
    lk_pin L k v -∗ lk_post k v I a -∗ lk_lcred k I 0%nat.
  Proof using .
    intros Ha. iIntros "#Hpin Hc". rewrite /lk_lcred. iExists v.
    iFrame "Hpin". rewrite (lk_lpr_0 L) /lk_post.
    iApply (lk_line_of_post L k v I a Ha with "Hc").
  Qed.

  (* ---- the block owed opens at ANY alternative ---- *)
  Lemma lk_lcred_blk_open k I a :
    lk_lcred k I 3%nat -∗ ∃ v : era_pins, lk_pin L k v ∗ lk_blk L k v I a 0%nat.
  Proof using .
    rewrite /lk_lcred. iIntros "Hc". iDestruct "Hc" as (v) "[#Hpin Hc]".
    iExists v. iFrame "Hpin". rewrite (lk_lpr_S3 L k v I 0%nat).
    iApply (lk_blk_0 L k v I 0%nat a with "Hc").
  Qed.

  Lemma lk_lcred_blk_lend k I :
    lk_lcred k I 3%nat -∗ ∃ v : era_pins, lk_pin L k v ∗ lk_lend L k v I.
  Proof using .
    rewrite /lk_lcred. iIntros "Hc". iDestruct "Hc" as (v) "[#Hpin Hc]".
    iExists v. iFrame "Hpin". rewrite (lk_lpr_S3 L k v I 0%nat).
    iApply (lk_lend_of_blk0 L k v I 0%nat with "Hc").
  Qed.

  Lemma lk_lcred_blk_panic k I :
    lk_lcred k I 3%nat -∗ ∃ v : era_pins, lk_pin L k v ∗ lk_panic k v I 0%nat.
  Proof using .
    rewrite /lk_lcred. iIntros "Hc". iDestruct "Hc" as (v) "[#Hpin Hc]".
    iExists v. iFrame "Hpin". rewrite (lk_lpr_S3 L k v I 0%nat) /lk_panic.
    iApply (lk_blk_0 L k v I 0%nat (lk_pan L I) with "Hc").
  Qed.

  (* ---- one byte of the panic line ---- *)
  Lemma lk_panic_step k v I i b Φ :
    alt_panic !! i = Some b ->
    (⌜¬ lk_wild L I⌝ ∨ lk_T L) -∗
    lk_pin L k v -∗ lk_links L -∗ lk_panic k v I i -∗
    (lk_panic k v I (S i) -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. rewrite /lk_panic.
    iApply (lk_blk_step L k v I (lk_pan L I) i b Φ).
    by rewrite (lk_ab_pan L I).
  Qed.

  (* ---- the banner-owed credential is a boundary credential ---- *)
  Lemma lk_cred_of_ban k I v : lk_pin L k v -∗ lk_ban L k v I 0%nat -∗ lk_cred k I 0%nat.
  Proof using .
    iIntros "#Hpin Hc". rewrite /lk_cred. iExists v. iFrame "Hpin".
    rewrite (lk_pr_0 L). iApply (lk_ban_owed L k v I with "Hc").
  Qed.

End linkgen.



(* ===================================================================== *)
(*  THE ECHO INSTANCE, DEFINITIONALLY (TL-7's pattern).                   *)
(*                                                                       *)
(*  Every data field is set to the landed [EchoLinks]/[EchoLinksLine]     *)
(*  name, so that a generic lemma at this instance IS the landed echo     *)
(*  lemma up to beta-delta and the echo audit does not move.  The era's   *)
(*  extra state is [emp]: it is not a field, it is the absence of one --  *)
(*  the credential families ARE echo's, and there is nothing under the    *)
(*  existentials but the three bounds.                                   *)
(* ===================================================================== *)
(* a law that needs no premise answers one it is given *)
Lemma lk_wand_drop {Σ : gFunctors} (P X : iProp Σ) : (⊢ X) -> ⊢ P -∗ X.
Proof using . intros HX. iIntros "_". iApply HX. Qed.

Section echo_inst.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{HPT : !Persistent T} `{HTT : !Timeless T}.
  Context `{HRg : !riscvGS Σ}.

  (* THE LEND: what sh's fork hands its child, [EchoLinksLine.
     ewc_blk_0_lend]'s conclusion given a name.  It is the ONE shape a
     paid child's entry reads directly ([UEchoOut.echo_uexec_slot_at]
     through [wr_blk_t_stage]), so the record carries it rather than
     letting every program re-open [ewc_blk]. *)
  Definition echo_lend (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ ps cs P : _, ⌜EchoLinksLine.wr_blk_t ps cs I P⌝ ∗ turn v P
        ∗ ps_lb v ps ∗ cs_lb v cs ∗ inp_lb v I) ∨ T)%I.

  Global Instance echo_lend_timeless v I : Timeless (echo_lend v I).
  Proof using HTT.
    rewrite /echo_lend.
    apply bi.or_timeless; [| assumption].
    apply bi.exist_timeless; intro. apply bi.exist_timeless; intro.
    apply bi.exist_timeless; intro.
    apply bi.sep_timeless; [apply bi.pure_timeless |].
    apply bi.sep_timeless; [apply turn_timeless |].
    apply bi.sep_timeless; [apply ps_lb_timeless |].
    apply bi.sep_timeless; [apply cs_lb_timeless | apply inp_lb_timeless].
  Qed.

  Local Lemma ei_lend_taint (k : nat) (v : era_pins) (I : list (bv 8)) :
    T -∗ echo_lend v I.
  Proof using . iIntros "HT". rewrite /echo_lend. by iRight. Qed.

  Local Lemma ei_lend_of_blk0 (k : nat) (v : era_pins) (I : list (bv 8))
      (a : nat) :
    EchoLinksLine.ewc_blk T v I a 0%nat -∗ echo_lend v I.
  Proof using HPT. rewrite /echo_lend. iApply EchoLinksLine.ewc_blk_0_lend. Qed.

  (* THE BANNER-OWED CREDENTIAL CARRIES ITS INPUT AND THE BOUNDARY
     ([UShLine.ush_wb_inp_ban]'s content, which is the seam between
     /init's position-indexed payload and sh's input-indexed one). *)
  Local Lemma ei_ban_inp (k : nat) (v : era_pins) (I : list (bv 8)) :
    EchoLinks.ewc_ban T v I 0%nat -∗
    EchoLinks.ewc_ban T v I 0%nat ∗ ((inp_lb v I ∗ ⌜rest_of I = []⌝) ∨ T).
  Proof using HPT.
    rewrite /EchoLinks.ewc_ban.
    iIntros "[Hl | #HT]"; last first.
    { iSplit; [ by iRight | iRight; iExact "HT" ]. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iSplitL "Htn".
    - iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE". by iPureIntro.
    - iLeft. iFrame "HE". iPureIntro. exact (proj1 (proj2 Hw)).
  Qed.

  Local Lemma ei_sp_taint (k : nat) (v : era_pins) (I : list (bv 8)) :
    T -∗ EchoLinks.ewc_sp T v I.
  Proof using . iIntros "HT". rewrite /EchoLinks.ewc_sp. by iRight. Qed.

  (* THE READER'S RESIDUE, spelled ([UShLine.rd_res]'s body: it is stated
     here so that [UShLine]'s own definition is [lk_rres] at this instance
     when that file is swept). *)
  Definition echo_rres (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    (∃ ps0 cs0 : list nat,
       ⌜rd_stage ps0 cs0 I⌝ ∗ turn_lb v (length (proc_before ps0 cs0 I))
       ∗ ps_lb v ps0 ∗ cs_lb v cs0)%I.

  Global Instance echo_rres_persistent v I : Persistent (echo_rres v I).
  Proof using .
    rewrite /echo_rres.
    apply bi.exist_persistent; intro. apply bi.exist_persistent; intro.
    apply bi.sep_persistent; [apply bi.pure_persistent |].
    apply bi.sep_persistent; [apply turn_lb_persistent |].
    apply bi.sep_persistent; [apply ps_lb_persistent | apply cs_lb_persistent].
  Qed.
  Global Instance echo_rres_timeless v I : Timeless (echo_rres v I).
  Proof using .
    rewrite /echo_rres.
    apply bi.exist_timeless; intro. apply bi.exist_timeless; intro.
    apply bi.sep_timeless; [apply bi.pure_timeless |].
    apply bi.sep_timeless; [apply turn_lb_timeless |].
    apply bi.sep_timeless; [apply ps_lb_timeless | apply cs_lb_timeless].
  Qed.

  (* [UShLine.ush_wb_read_holds]'s content: a credential that still owes
     the round's banner at a boundary the reader is strictly past is the
     taint ([EchoLinks.wr_owed_read_refute] at [wr_ban_pro]). *)
  Local Lemma ei_ban_read_taint (k : nat) (v : era_pins)
      (I l : list (bv 8)) :
    wl_nl ∉ l ->
    EchoLinks.ewc_ban T v I 0%nat -∗ echo_rres v (I ++ l ++ [wl_nl]) -∗ T.
  Proof using HPT.
    intro Hnl. iIntros "Hb #Hres".
    rewrite /EchoLinks.ewc_ban.
    iDestruct "Hb" as "[Hl | #HT]"; [ | iExact "HT" ].
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & _)".
    rewrite /echo_rres.
    iDestruct "Hres" as (ps0 cs0) "(%Hrd & #Htlb & #Hps0 & #Hcs0)".
    iDestruct (turn_lb_le v (P + 0)%nat _ with "Htn Htlb") as %Hle.
    iDestruct (ps_lb_cmp v ps ps0 with "Hps Hps0") as %Hpsc.
    iDestruct (cs_lb_cmp v cs cs0 with "Hcs Hcs0") as %Hcsc.
    iExFalso. iPureIntro.
    assert (Hpre : I `prefix_of` (I ++ l ++ [wl_nl])) by (by eexists).
    assert (Hne : I <> I ++ l ++ [wl_nl]).
    { intro Heq. apply (f_equal length) in Heq.
      rewrite !length_app length_cons in Heq. lia. }
    exact (EchoLinks.wr_owed_read_refute ps cs ps0 cs0 I
             (I ++ l ++ [wl_nl]) P
             (or_introl (EchoLinks.wr_ban_pro ps cs I P Hw))
             Hpre Hne Hrd Hpsc Hcsc ltac:(lia)).
  Qed.

  Local Lemma ei_pin_epin (k : nat) (v : era_pins) :
    era_pin γ k v -∗ era_pin γ k v.
  Proof using . by iIntros "$". Qed.

  Local Lemma ei_apr_exf (I : list (bv 8)) : (1 < 3)%nat.
  Proof using . lia. Qed.

  (* THE ERA'S TURN AT STAGE 0 IS ROUND 0's BANNER-OWED CREDENTIAL
     ([UInitBanner.kinit_ban0_of_eturn]'s content, which is where the two
     halves of [EchoOut.eturn] come apart). *)
  Local Lemma ei_turn0 (k : nat) :
    eturn γ k -∗
    (∃ v : era_pins, era_pin γ k v ∗ dl_cnt v (1/2) 0%nat ∗ inp_lb v [])
    ∗ (∃ v : era_pins, era_pin γ k v ∗ EchoLinks.ewc_ban T v [] 0%nat).
  Proof using .
    iIntros "Hturn".
    iDestruct "Hturn" as (v) "(#Hpin & Htn & Hdl & #Hcs & #Hps & #HE)".
    iSplitL "Hdl"; [ iExists v; by iFrame "Hpin Hdl HE" | ].
    iExists v. iFrame "Hpin".
    rewrite /EchoLinks.ewc_ban. iLeft. iExists [], [], 0%nat.
    rewrite Nat.add_0_r. iFrame "Htn Hps Hcs HE".
    iPureIntro. exact EchoLinks.wr_ban_round0.
  Qed.

  (* ---- THE PROLOGUE DIAGNOSTICS' two conversions (lane INIT-FILE) ----
     The first is the six lines [UInitBoot]'s [Hpw] used to do inline; the
     second is [EchoLinksPro.ewc_pdiag_done_1] with the index taken as a
     premise, which is the shape the record's field is at (the FILE era's
     twin cannot state it at the literal length). *)
  Local Lemma ei_pro_of_pban (k : nat) (v : era_pins) (I : list (bv 8)) :
    ⊢ EchoLinksPro.ewc_pro T v I -∗ EchoLinksLine.ewc_pro T v I.
  Proof using HPT.
    rewrite /EchoLinksPro.ewc_pro /EchoLinksLine.ewc_pro.
    iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE".
    iPureIntro. exact (proj1 Hw).
  Qed.

  Local Lemma ei_pdiag_done_1 (k : nat) (v : era_pins) (I : list (bv 8))
      (i : nat) :
    i = length (pro_alts !!! 1%nat) ->
    ⊢ EchoLinksPro.ewc_pdiag T v I 1%nat i -∗ EchoLinks.ewc_ban T v I 0%nat.
  Proof using HPT.
    intros Hi. rewrite Hi.
    iApply (EchoLinksPro.ewc_pdiag_done_1 T v I).
  Qed.

  Definition echo_link_inst : LinkRec Σ :=
    {| lk_T := T;
       lk_pin := era_pin γ;
       lk_epin := era_pin γ;
       lk_links := EchoLinks.echo_links T γ;
       lk_ab := fun I a => line_alts_of (last_ws I) !!! a;
       lk_wild := fun _ => False;
       lk_apr := fun _ a => (a < 3)%nat;
       lk_pan := fun _ => 3%nat;
       lk_exf := fun _ => 1%nat;
       lk_exfb := fun _ => alt_execfail;
       lk_noc := 2%nat;
       lk_ban := fun _ v I i => EchoLinks.ewc_ban T v I i;
       lk_owed := fun _ v I => EchoLinks.ewc_owed T v I;
       lk_sp := fun _ v I => EchoLinks.ewc_sp T v I;
       lk_open := fun _ v I => EchoLinks.ewc_open T v I;
       lk_blk := fun _ v I a i => EchoLinksLine.ewc_blk T v I a i;
       lk_pro := fun _ v I => EchoLinksLine.ewc_pro T v I;
       lk_sp_t := fun _ v I => EchoLinksLine.ewc_sp_t T v I;
       lk_open_t := fun _ v I => EchoLinksLine.ewc_open_t T v I;
       lk_line := fun _ v I => EchoLinksLine.ewc_line T v I;
       lk_pr := fun _ v I p => EchoLinks.ewc_pr T v I p;
       lk_lpr := fun _ v I p => EchoLinksLine.ewc_lpr T v I p;
       lk_lend := fun _ v I => echo_lend v I;
       lk_rr := fun k v n ws => EchoOut.read_ret T k v n ws;
       lk_turn := fun k => eturn γ k;
       lk_rres := echo_rres;

       lk_T_pers := HPT;
       lk_T_tl := HTT;
       lk_links_pers := EchoLinks.echo_links_persistent T γ;
       lk_pin_pers := era_pin_persistent γ;
       lk_pin_tl := era_pin_timeless γ;
       lk_pin_agr := era_pin_agree γ;
       lk_epin_pers := era_pin_persistent γ;
       lk_epin_tl := era_pin_timeless γ;
       lk_epin_agr := era_pin_agree γ;
       lk_pin_epin := ei_pin_epin;
       lk_ban_tl := fun _ v I i => EchoLinks.ewc_ban_timeless T v I i;
       lk_owed_tl := fun _ v I => EchoLinks.ewc_owed_timeless T v I;
       lk_sp_tl := fun _ v I => EchoLinks.ewc_sp_timeless T v I;
       lk_open_tl := fun _ v I => EchoLinks.ewc_open_timeless T v I;
       lk_blk_tl := fun _ v I a i => EchoLinksLine.ewc_blk_timeless T v I a i;
       lk_pro_tl := fun _ v I => EchoLinksLine.ewc_pro_timeless T v I;
       lk_sp_t_tl := fun _ v I => EchoLinksLine.ewc_sp_t_timeless T v I;
       lk_open_t_tl := fun _ v I => EchoLinksLine.ewc_open_t_timeless T v I;
       lk_line_tl := fun _ v I => EchoLinksLine.ewc_line_timeless T v I;
       lk_pr_tl := fun _ v I p => EchoLinks.ewc_pr_timeless T v I p;
       lk_lpr_tl := fun _ v I p => EchoLinksLine.ewc_lpr_timeless T v I p;
       lk_lend_tl := fun _ v I => echo_lend_timeless v I;
       lk_rres_pers := echo_rres_persistent;
       lk_rres_tl := echo_rres_timeless;

       lk_pr_0 := fun _ v I => eq_refl;
       lk_pr_1 := fun _ v I => eq_refl;
       lk_pr_S2 := fun _ v I p => eq_refl;
       lk_lpr_0 := fun _ v I => eq_refl;
       lk_lpr_1 := fun _ v I => eq_refl;
       lk_lpr_2 := fun _ v I => eq_refl;
       lk_lpr_S3 := fun _ v I p => eq_refl;

       lk_ban_taint := fun _ v I i => EchoLinks.ewc_ban_taint T v I i;
       lk_owed_taint := fun _ v I => EchoLinks.ewc_owed_taint T v I;
       lk_sp_taint := ei_sp_taint;
       lk_open_taint := fun _ v I => EchoLinks.ewc_open_taint T v I;
       lk_blk_taint := fun _ v I a i => EchoLinksLine.ewc_blk_taint T v I a i;
       lk_pro_taint := fun _ v I => EchoLinksLine.ewc_pro_taint T v I;
       lk_sp_t_taint := fun _ v I => EchoLinksLine.ewc_sp_t_taint T v I;
       lk_open_t_taint := fun _ v I => EchoLinksLine.ewc_open_t_taint T v I;
       lk_line_taint := fun _ v I => EchoLinksLine.ewc_line_taint T v I;
       lk_lend_taint := ei_lend_taint;

       lk_pro_owed := fun _ v I => EchoLinksLine.ewc_pro_owed T v I;
       lk_blk_owed := fun _ v I a => EchoLinksLine.ewc_blk_owed T v I a;
       lk_sp_t_sp := fun _ v I => EchoLinksLine.ewc_sp_t_sp T v I;
       lk_open_t_open := fun _ v I => EchoLinksLine.ewc_open_t_open T v I;
       lk_blk_0 := fun _ v I a a' => EchoLinksLine.ewc_blk_0 T v I a a';
       lk_line_of_blk0 := fun _ v I a => EchoLinksLine.ewc_line_of_blk0 T v I a;
       lk_line_of_post := fun _ v I a Ha => EchoLinksLine.ewc_line_of_post T v I a Ha;
       lk_line_of_pro := fun _ v I => EchoLinksLine.ewc_line_of_pro T v I;
       lk_lend_of_blk0 := ei_lend_of_blk0;

       lk_ban_step := fun k v I i b Φ Hb => EchoLinks.echo_banner_step T γ k v I i b Φ Hb;
       lk_ban_owed := fun _ v I => EchoLinks.ewc_ban_owed T v I;
       lk_ban_pro := fun _ v I => EchoLinks.ewc_ban_pro T v I;
       lk_ban_done := fun _ v I => EchoLinks.ewc_ban_done T v I;
       lk_ban_done_line := fun _ v I => EchoLinksLine.ewc_ban_done_line T v I;
       lk_ban_inp := ei_ban_inp;

       lk_prompt_dollar := fun k v I b Φ Hb =>
         lk_wand_drop _ _ (EchoLinks.echo_prompt_dollar T γ k v I b Φ Hb);
       lk_prompt_space := fun k v I b Φ Hb => EchoLinks.echo_prompt_space T γ k v I b Φ Hb;
       lk_prompt_dollar_ban := fun k v I b Φ Hb =>
         lk_wand_drop _ _ (EchoLinks.echo_prompt_dollar_ban T γ k v I b Φ Hb);
       lk_read := fun _ v I l Hl => EchoLinks.ewc_read T v I l Hl;
       lk_owed_read_taint := fun k v n I ws H1 H2 => EchoLinks.ewc_owed_read_taint T k v n I ws H1 H2;

       lk_blk_step := fun k v I a i b Φ Hb =>
         lk_wand_drop _ _ (EchoLinksLine.echo_blk_step T γ k v I a i b Φ Hb);
       lk_blk_sp := fun _ v I a Ha => EchoLinksLine.ewc_blk_sp T v I a Ha;

       lk_prompt_dollar_post := fun k v I a b Φ Ha Hb =>
         lk_wand_drop _ _ (EchoLinksLine.echo_prompt_dollar_post T γ k v I a b Φ Ha Hb);
       lk_prompt_space_t := fun k v I b Φ Hb =>
         EchoLinksLine.echo_prompt_space_t T γ k v I b Φ Hb;
       lk_prompt_dollar_line := fun k v I b Φ Hb =>
         lk_wand_drop _ _ (EchoLinksLine.echo_prompt_dollar_line T γ k v I b Φ Hb);
       lk_read_t := fun _ v I a l Hl => EchoLinksLine.ewc_read_t T v I a l Hl;

       lk_ab_pan := fun I => line_alts_of_3 (last_ws I);
       lk_ab_exf := fun I => line_alts_of_1 (last_ws I);
       lk_apr_exf := ei_apr_exf;
       lk_turn0 := ei_turn0;
       lk_ban_read_taint := ei_ban_read_taint;
       lk_panic_done := fun _ v I => EchoLinksLine.ewc_panic_done T v I;
           lk_pban := fun _ v I => EchoLinksPro.ewc_pro T v I;
       lk_pdiag := fun _ v I a i => EchoLinksPro.ewc_pdiag T v I a i;
       lk_pban_tl := fun _ v I => EchoLinksPro.ewc_pro_timeless T v I;
       lk_pdiag_tl := fun _ v I a i => EchoLinksPro.ewc_pdiag_timeless T v I a i;
       lk_pban_taint := fun _ v I => EchoLinksPro.ewc_pro_taint T v I;
       lk_pdiag_taint := fun _ v I a i => EchoLinksPro.ewc_pdiag_taint T v I a i;
       lk_pdiag_0 := fun _ v I a => EchoLinksPro.ewc_pdiag_0 T v I a;
       lk_pban_of_ban_done := fun _ v I => EchoLinksPro.ewc_ban_done_pro T v I;
       lk_pro_of_pban := ei_pro_of_pban;
       lk_pdiag_step := fun k v I a i b Φ Hb =>
         EchoLinksPro.echo_pdiag_step T γ k v I a i b Φ Hb;
       lk_pdiag_done_1 := ei_pdiag_done_1;
|}.


  (* =================================================================== *)
  (*  THE DEFINITIONAL CHECK (durable-notes, the section on writing a     *)
  (*  checker for a refactor's silent failure mode).  Every family         *)
  (*  the record exposes IS the landed echo family at this instance, BY    *)
  (*  CONVERSION.  If any of these ever needs a tactic, an echo statement  *)
  (*  has moved and [make audit-echo-only] is about to change.            *)
  (* =================================================================== *)
  Lemma echo_inst_T : lk_T echo_link_inst = T.
  Proof using . reflexivity. Qed.
  Lemma echo_inst_pin : lk_pin echo_link_inst = era_pin γ.
  Proof using . reflexivity. Qed.
  Lemma echo_inst_links : lk_links echo_link_inst = EchoLinks.echo_links T γ.
  Proof using . reflexivity. Qed.
  Lemma echo_inst_ban k v I i :
    lk_ban echo_link_inst k v I i = EchoLinks.ewc_ban T v I i.
  Proof using . reflexivity. Qed.
  Lemma echo_inst_owed k v I :
    lk_owed echo_link_inst k v I = EchoLinks.ewc_owed T v I.
  Proof using . reflexivity. Qed.
  Lemma echo_inst_blk k v I a i :
    lk_blk echo_link_inst k v I a i = EchoLinksLine.ewc_blk T v I a i.
  Proof using . reflexivity. Qed.
  Lemma echo_inst_post k v I a :
    lk_post echo_link_inst k v I a = EchoLinksLine.ewc_post T v I a.
  Proof using . reflexivity. Qed.
  Lemma echo_inst_panic k v I i :
    lk_panic echo_link_inst k v I i = EchoLinksLine.ewc_panic T v I i.
  Proof using . reflexivity. Qed.
  Lemma echo_inst_pr : lk_pr echo_link_inst = fun k => EchoLinks.ewc_pr T.
  Proof using . reflexivity. Qed.
  Lemma echo_inst_lpr :
    lk_lpr echo_link_inst = fun k => EchoLinksLine.ewc_lpr T.
  Proof using . reflexivity. Qed.
  Lemma echo_inst_cred k I p :
    lk_cred echo_link_inst k I p = EchoLinks.ewc_cred T γ k I p.
  Proof using . reflexivity. Qed.
  Lemma echo_inst_lcred_eta k :
    lk_lcred echo_link_inst k = EchoLinksLine.ewc_lcred T γ k.
  Proof using . reflexivity. Qed.
  Lemma echo_inst_cred_eta k :
    lk_cred echo_link_inst k = EchoLinks.ewc_cred T γ k.
  Proof using . reflexivity. Qed.
  Lemma echo_inst_lcred k I p :
    lk_lcred echo_link_inst k I p = EchoLinksLine.ewc_lcred T γ k I p.
  Proof using . reflexivity. Qed.

End echo_inst.
