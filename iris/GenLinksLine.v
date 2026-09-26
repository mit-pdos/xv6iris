(* ===================================================================== *)
(*  GenLinksLine.v -- THE CONSOLE CREDENTIAL FAMILIES OF A LINE MODEL,    *)
(*  once (app-both milestone M2b).                                       *)
(*                                                                       *)
(*  Every family of [FileLinksLine] S8, [PipeLinksLine] S5 and            *)
(*  [EchoLinks]/[EchoLinksLine] is                                        *)
(*                                                                       *)
(*     (∃ ps cs s0 P, ⌜wr_X ps cs s0 I P⌝ ∗ CURSOR) ∨ [HEAD] ∨ T           *)
(*                                                                       *)
(*  with the cursor the era's ghosts ([EchoOut.turn], the three lower    *)
(*  bounds) beside a STATE WITNESS ([W k s0]: the file's boot-ledger     *)
(*  entry; [emp] where no line touches the file system), and the head   *)
(*  arm the era before its first byte ([H k v I]: the file's [fhead];    *)
(*  absent elsewhere).  This file states the families ONCE over a line   *)
(*  model and those parameters, and proves the record's laws            *)
(*  ([LinkRec]) from a LINKS INTERFACE ([glinks]): the tier's write      *)
(*  links with the state witness in and out, plus the head's first byte. *)
(*  A tier instantiates it by naming its taint, pin, witness, head and   *)
(*  read receipt, and proving its own links entail [glinks].             *)
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
Require Import LineBytes.
Require Import LineModel.
Require Import LineModelLinks.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import EchoOut.
Require Import EchoLinks.        (* [wr_ban_head], [wr_prompt_head] *)
Require Import EchoLinksPro.     (* [pro_alts_lt_of_lookup] *)
Require Import LinkRec.
Local Open Scope list_scope.
Local Open Scope nat_scope.

(* THE PARAMETERS: what a tier names.  One record, so that every family
   and law below depends on the one section variable [G] (the laws that
   are used only in proofs -- the head's readings, the witness agreement
   -- ride in it too). *)
Record gen_params {Σ : gFunctors} `{!echoOutG Σ} (M : lmodel) := MkGP {
  gL : lm_laws M;
  gK : lm_hooks M;
  (* the era's taint *)
  gT : iProp Σ;
  gT_pers : Persistent gT;
  gT_tl : Timeless gT;
  (* the era's pin *)
  gPIN : nat -> era_pins -> iProp Σ;
  gPIN_pers : forall k v, Persistent (gPIN k v);
  gPIN_tl : forall k v, Timeless (gPIN k v);
  gPIN_agree : forall k v v', gPIN k v -∗ gPIN k v' -∗ ⌜v = v'⌝;
  (* the writer's state witness, and the reader's (the boot-ledger entry
     alone, which exists at the era's head) *)
  gW : nat -> lm_st M -> iProp Σ;
  gW_pers : forall k s, Persistent (gW k s);
  gW_tl : forall k s, Timeless (gW k s);
  gWb : nat -> lm_st M -> iProp Σ;
  gWb_pers : forall k s, Persistent (gWb k s);
  gWb_tl : forall k s, Timeless (gWb k s);
  (* the reader's residue is pinned to ONE era ([S gen_id] at the file):
     the writer's witness at any era projects to the reader's at its own
     and at that one, and two readers' witnesses of one era agree *)
  gk0 : nat;
  gW_bw : forall k s, gW k s -∗ gWb k s;
  gW_bw0 : forall k s, gW k s -∗ gWb gk0 s;
  gWb_agree : forall k s s', gWb k s -∗ gWb k s' -∗ ⌜s = s'⌝;
  (* the era's head: nothing written, the cursor at zero *)
  gH : nat -> era_pins -> list (bv 8) -> iProp Σ;
  gH_tl : forall k v I, Timeless (gH k v I);
  gH_cur : forall k v I,
    gH k v I -∗ ⌜I = []⌝ ∗ turn v 0 ∗ ps_lb v [] ∗ cs_lb v [] ∗ inp_lb v [];
  gH_inp : forall k v I, gH k v I -∗ gH k v I ∗ ⌜I = []⌝ ∗ inp_lb v [];
  (* THE WILD LINES (seccomp design 10.7): an input whose last line is one
     after which the era's claim may have gone wild; a block-first byte
     there is refused ([gl_blk]'s premise).  [fun _ => False] at every
     instance but the union. *)
  gwild : list (bv 8) -> Prop;
}.
Global Arguments MkGP {Σ _} M.
Global Arguments gL {Σ _ M} _.
Global Arguments gK {Σ _ M} _.
Global Arguments gT {Σ _ M} _.
Global Arguments gT_pers {Σ _ M} _.
Global Arguments gT_tl {Σ _ M} _.
Global Arguments gPIN {Σ _ M} _ _ _.
Global Arguments gPIN_pers {Σ _ M} _ _ _.
Global Arguments gPIN_tl {Σ _ M} _ _ _.
Global Arguments gPIN_agree {Σ _ M} _ _ _ _.
Global Arguments gW {Σ _ M} _ _ _.
Global Arguments gW_pers {Σ _ M} _ _ _.
Global Arguments gW_tl {Σ _ M} _ _ _.
Global Arguments gWb {Σ _ M} _ _ _.
Global Arguments gWb_pers {Σ _ M} _ _ _.
Global Arguments gWb_tl {Σ _ M} _ _ _.
Global Arguments gk0 {Σ _ M} _.
Global Arguments gW_bw {Σ _ M} _ _ _.
Global Arguments gW_bw0 {Σ _ M} _ _ _.
Global Arguments gWb_agree {Σ _ M} _ _ _ _.
Global Arguments gH {Σ _ M} _ _ _ _.
Global Arguments gH_tl {Σ _ M} _ _ _ _.
Global Arguments gH_cur {Σ _ M} _ _ _ _.
Global Arguments gH_inp {Σ _ M} _ _ _ _.
Global Arguments gwild {Σ _ M} _ _.
Global Existing Instances gT_pers gT_tl gPIN_pers gPIN_tl gW_pers gW_tl gWb_pers gWb_tl gH_tl.

Section gen_links_line.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  Context `{HRg : !riscvGS Σ}.
  Context (M : lmodel).

  Context (G : gen_params M).
  Local Notation L := (gL G).
  Local Notation K := (gK G).
  Local Notation T := (gT G).
  Local Notation PIN := (gPIN G).
  Local Notation W := (gW G).
  Local Notation Wb := (gWb G).
  Local Notation k0 := (gk0 G).
  Local Notation H := (gH G).
  Local Notation WL := (gwild G).

  (* ================================================================== *)
  (*  1.  THE CURSOR AND THE FAMILIES                                    *)
  (* ================================================================== *)
  Definition gcur (v : era_pins) (ps cs : list nat) (s0 : lm_st M)
      (I : list (bv 8)) (P k : nat) : iProp Σ :=
    (turn v P ∗ ps_lb v ps ∗ cs_lb v cs ∗ inp_lb v I ∗ W k s0)%I.

  Global Instance gcur_timeless v ps cs s0 I P k : Timeless (gcur v ps cs s0 I P k).
  Proof using. rewrite /gcur. apply _. Qed.

  Definition gwc_pro (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ (ps cs : list nat) (s0 : lm_st M) (P : nat),
        ⌜lm_wr_pro M ps cs s0 I P⌝ ∗ gcur v ps cs s0 I P k)
     ∨ H k v I ∨ T)%I.

  Definition gwc_blk (k : nat) (v : era_pins) (I : list (bv 8)) (a i : nat)
    : iProp Σ :=
    ((∃ (ps cs : list nat) (s0 : lm_st M) (P : nat),
        ⌜lm_wr_blk_t M ps cs s0 I P⌝
        ∗ turn v (P + i) ∗ ps_lb v ps ∗ cs_lb v (lm_blkcs cs a i)
        ∗ inp_lb v I ∗ W k s0)
     ∨ T)%I.

  Definition gwc_owed (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ (ps cs : list nat) (s0 : lm_st M) (P : nat),
        ⌜lm_wr_owed M ps cs s0 I P⌝ ∗ gcur v ps cs s0 I P k)
     ∨ H k v I ∨ T)%I.

  Definition gwc_sp (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ (ps cs : list nat) (s0 : lm_st M) (P : nat),
        ⌜lm_wr_sp M ps cs s0 I P⌝ ∗ gcur v ps cs s0 I P k) ∨ T)%I.

  Definition gwc_open (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ (ps cs : list nat) (s0 : lm_st M) (P : nat),
        ⌜lm_wr_open M ps cs s0 I P⌝ ∗ gcur v ps cs s0 I P k) ∨ T)%I.

  Definition gwc_sp_t (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ (ps cs : list nat) (s0 : lm_st M) (P : nat),
        ⌜lm_wr_sp_t M ps cs s0 I P⌝ ∗ gcur v ps cs s0 I P k) ∨ T)%I.

  Definition gwc_open_t (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ (ps cs : list nat) (s0 : lm_st M) (P : nat),
        ⌜lm_wr_open_t M ps cs s0 I P⌝ ∗ gcur v ps cs s0 I P k) ∨ T)%I.

  Definition gwc_ban (k : nat) (v : era_pins) (I : list (bv 8)) (i : nat)
    : iProp Σ :=
    ((∃ (ps cs : list nat) (s0 : lm_st M) (P : nat),
        ⌜lm_wr_banp M ps cs s0 I P i⌝
        ∗ turn v (P + i) ∗ ps_lb v ps ∗ cs_lb v cs ∗ inp_lb v I ∗ W k s0)
     ∨ (⌜i = 0⌝ ∗ H k v I) ∨ T)%I.

  (* a block written up to its prompt, at the round's OWN state: the index
     is computed INSIDE, from the choice list the credential holds *)
  Definition gwc_post (k : nat) (v : era_pins) (I : list (bv 8)) (a : nat)
    : iProp Σ :=
    ((∃ (ps cs : list nat) (s0 : lm_st M) (P : nat),
        ⌜lm_wr_blk_t M ps cs s0 I P⌝
        ∗ turn v (P + (length (lm_abs M s0 cs I a) - 2)) ∗ ps_lb v ps
        ∗ cs_lb v (lm_blkcs cs a (length (lm_abs M s0 cs I a) - 2))
        ∗ inp_lb v I ∗ W k s0)
     ∨ T)%I.

  (* THE PER-SHAPE BLOCK ARM: how the line credential looks while a shape's
     continuation is being written by something other than this layer's
     one writer (the pipeline's two-writer terminal round, [PipeBoth]);
     [False] where every shape writes through the block family *)
  Context (X : nat -> era_pins -> list (bv 8) -> iProp Σ)
          (X_tl : forall k v I, Timeless (X k v I)).
  #[local] Existing Instance X_tl.

  Definition gwc_line (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    (gwc_pro k v I ∨ (∃ a : nat, ⌜lm_aprs M I a⌝ ∗ gwc_post k v I a) ∨ X k v I)%I.

  Definition gwc_lend (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ (ps cs : list nat) (s0 : lm_st M) (P : nat),
        ⌜lm_wr_blk_t M ps cs s0 I P⌝ ∗ gcur v ps cs s0 I P k) ∨ T)%I.

  Definition gwc_pr (k : nat) (v : era_pins) (I : list (bv 8)) (p : nat)
    : iProp Σ :=
    match p with
    | O => gwc_owed k v I
    | S O => gwc_sp k v I
    | _ => gwc_open k v I
    end.

  Definition gwc_lpr (k : nat) (v : era_pins) (I : list (bv 8)) (p : nat)
    : iProp Σ :=
    match p with
    | O => gwc_line k v I
    | S O => gwc_sp_t k v I
    | S (S O) => gwc_open_t k v I
    | _ => gwc_blk k v I 0 0
    end.

  (* THE READER'S RESIDUE: the two bounds on the transcript's resolution
     and the writer's cursor bound at the stream they compute, with the
     reader's witness of the boot state *)
  Definition gwc_rres (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    (∃ (ps0 cs0 : list nat) (s0 : lm_st M),
       ⌜lm_rd_stage M ps0 cs0 s0 I⌝
       ∗ turn_lb v (length (lm_proc_before M ps0 cs0 s0 I))
       ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ Wb k0 s0)%I.

  (* /init's prologue diagnostics *)
  Definition gwc_pban (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    ((∃ (ps cs : list nat) (s0 : lm_st M) (P : nat),
        ⌜lm_wr_pban M ps cs s0 I P⌝ ∗ gcur v ps cs s0 I P k) ∨ T)%I.

  Definition gwc_pdg (k : nat) (v : era_pins) (I : list (bv 8)) (a i : nat)
    : iProp Σ :=
    ((∃ (ps cs : list nat) (s0 : lm_st M) (P : nat),
        ⌜lm_wr_pdiag M ps cs s0 I P a i⌝ ∗ gcur v ps cs s0 I P k) ∨ T)%I.

  Definition gwc_pdiag (k : nat) (v : era_pins) (I : list (bv 8)) (a i : nat)
    : iProp Σ :=
    match i with
    | O => gwc_pban k v I
    | S _ => gwc_pdg k v I a i
    end.

  (* THE DISPATCH, NOT [apply _]: descend through the connectives and name
     the leaf instance (the tree's 455 [Timeless] instances make a search
     at this altitude cost seconds a goal). *)
  Local Ltac tl_leaf :=
    lazymatch goal with
    | |- Timeless (bi_exist _) => apply bi.exist_timeless; intro; tl_leaf
    | |- Timeless (bi_sep _ _) => apply bi.sep_timeless; [tl_leaf | tl_leaf]
    | |- Timeless (bi_or _ _) => apply bi.or_timeless; [tl_leaf | tl_leaf]
    | |- Timeless (bi_pure _) => apply bi.pure_timeless
    | |- Timeless (gcur _ _ _ _ _ _ _) => apply gcur_timeless
    | |- Timeless (H _ _ _) => apply (gH_tl G)
    | |- Timeless (X _ _ _) => apply X_tl
    | |- Timeless (W _ _) => apply (gW_tl G)
    | |- Timeless (Wb _ _) => apply (gWb_tl G)
    | |- Timeless T => apply (gT_tl G)
    | |- Timeless (turn _ _) => apply turn_timeless
    | |- Timeless (turn_lb _ _) => apply turn_lb_timeless
    | |- Timeless (ps_lb _ _) => apply ps_lb_timeless
    | |- Timeless (cs_lb _ _) => apply cs_lb_timeless
    | |- Timeless (inp_lb _ _) => apply inp_lb_timeless
    | |- Persistent (bi_exist _) => apply bi.exist_persistent; intro; tl_leaf
    | |- Persistent (bi_sep _ _) => apply bi.sep_persistent; [tl_leaf | tl_leaf]
    | |- Persistent (bi_pure _) => apply bi.pure_persistent
    | |- Persistent (turn_lb _ _) => apply turn_lb_persistent
    | |- Persistent (ps_lb _ _) => apply ps_lb_persistent
    | |- Persistent (cs_lb _ _) => apply cs_lb_persistent
    | |- Persistent (Wb _ _) => apply (gWb_pers G)
    | |- _ => apply _
    end.

  Global Instance gwc_pro_timeless k v I : Timeless (gwc_pro k v I).
  Proof using. rewrite /gwc_pro. tl_leaf. Qed.
  Global Instance gwc_blk_timeless k v I a i : Timeless (gwc_blk k v I a i).
  Proof using. rewrite /gwc_blk. tl_leaf. Qed.
  Global Instance gwc_owed_timeless k v I : Timeless (gwc_owed k v I).
  Proof using. rewrite /gwc_owed. tl_leaf. Qed.
  Global Instance gwc_sp_timeless k v I : Timeless (gwc_sp k v I).
  Proof using. rewrite /gwc_sp. tl_leaf. Qed.
  Global Instance gwc_open_timeless k v I : Timeless (gwc_open k v I).
  Proof using. rewrite /gwc_open. tl_leaf. Qed.
  Global Instance gwc_sp_t_timeless k v I : Timeless (gwc_sp_t k v I).
  Proof using. rewrite /gwc_sp_t. tl_leaf. Qed.
  Global Instance gwc_open_t_timeless k v I : Timeless (gwc_open_t k v I).
  Proof using. rewrite /gwc_open_t. tl_leaf. Qed.
  Global Instance gwc_ban_timeless k v I i : Timeless (gwc_ban k v I i).
  Proof using. rewrite /gwc_ban. tl_leaf. Qed.
  Global Instance gwc_post_timeless k v I a : Timeless (gwc_post k v I a).
  Proof using. rewrite /gwc_post. tl_leaf. Qed.
  Global Instance gwc_line_timeless k v I : Timeless (gwc_line k v I).
  Proof using X_tl.
    rewrite /gwc_line.
    apply bi.or_timeless; [apply gwc_pro_timeless |].
    apply bi.or_timeless; [| apply X_tl].
    apply bi.exist_timeless; intro.
    apply bi.sep_timeless; [apply bi.pure_timeless | apply gwc_post_timeless].
  Qed.
  Global Instance gwc_lend_timeless k v I : Timeless (gwc_lend k v I).
  Proof using. rewrite /gwc_lend. tl_leaf. Qed.
  Global Instance gwc_pr_timeless k v I p : Timeless (gwc_pr k v I p).
  Proof using.
    rewrite /gwc_pr. destruct p as [| [| p]];
      [apply gwc_owed_timeless | apply gwc_sp_timeless | apply gwc_open_timeless].
  Qed.
  Global Instance gwc_lpr_timeless k v I p : Timeless (gwc_lpr k v I p).
  Proof using X_tl.
    rewrite /gwc_lpr. destruct p as [| [| [| p]]];
      [apply gwc_line_timeless | apply gwc_sp_t_timeless
      | apply gwc_open_t_timeless | apply gwc_blk_timeless].
  Qed.
  Global Instance gwc_rres_persistent v I : Persistent (gwc_rres v I).
  Proof using. rewrite /gwc_rres. tl_leaf. Qed.
  Global Instance gwc_rres_timeless v I : Timeless (gwc_rres v I).
  Proof using. rewrite /gwc_rres. tl_leaf. Qed.
  Global Instance gwc_pban_timeless k v I : Timeless (gwc_pban k v I).
  Proof using. rewrite /gwc_pban. tl_leaf. Qed.
  Global Instance gwc_pdg_timeless k v I a i : Timeless (gwc_pdg k v I a i).
  Proof using. rewrite /gwc_pdg. tl_leaf. Qed.
  Global Instance gwc_pdiag_timeless k v I a i : Timeless (gwc_pdiag k v I a i).
  Proof using.
    rewrite /gwc_pdiag. destruct i; [apply gwc_pban_timeless | apply gwc_pdg_timeless].
  Qed.

  (* ================================================================== *)
  (*  2.  STRUCTURE: the taint, the loose and the tight shapes, the      *)
  (*      banner's readings, the read of a line, the panic's five bytes  *)
  (* ================================================================== *)
  Lemma gwc_pro_taint k v I : T -∗ gwc_pro k v I.
  Proof using. iIntros "H". rewrite /gwc_pro. iRight. by iRight. Qed.
  Lemma gwc_blk_taint k v I a i : T -∗ gwc_blk k v I a i.
  Proof using. iIntros "H". rewrite /gwc_blk. by iRight. Qed.
  Lemma gwc_owed_taint k v I : T -∗ gwc_owed k v I.
  Proof using. iIntros "H". rewrite /gwc_owed. iRight. by iRight. Qed.
  Lemma gwc_sp_taint k v I : T -∗ gwc_sp k v I.
  Proof using. iIntros "H". rewrite /gwc_sp. by iRight. Qed.
  Lemma gwc_open_taint k v I : T -∗ gwc_open k v I.
  Proof using. iIntros "H". rewrite /gwc_open. by iRight. Qed.
  Lemma gwc_sp_t_taint k v I : T -∗ gwc_sp_t k v I.
  Proof using. iIntros "H". rewrite /gwc_sp_t. by iRight. Qed.
  Lemma gwc_open_t_taint k v I : T -∗ gwc_open_t k v I.
  Proof using. iIntros "H". rewrite /gwc_open_t. by iRight. Qed.
  Lemma gwc_ban_taint k v I i : T -∗ gwc_ban k v I i.
  Proof using. iIntros "H". rewrite /gwc_ban. iRight. by iRight. Qed.
  Lemma gwc_post_taint k v I a : T -∗ gwc_post k v I a.
  Proof using. iIntros "H". rewrite /gwc_post. by iRight. Qed.
  Lemma gwc_line_taint k v I : T -∗ gwc_line k v I.
  Proof using. iIntros "H". rewrite /gwc_line. iLeft. by iApply gwc_pro_taint. Qed.
  Lemma gwc_lend_taint k v I : T -∗ gwc_lend k v I.
  Proof using. iIntros "H". rewrite /gwc_lend. by iRight. Qed.
  Lemma gwc_pban_taint k v I : T -∗ gwc_pban k v I.
  Proof using. iIntros "H". rewrite /gwc_pban. by iRight. Qed.
  Lemma gwc_pdg_taint k v I a i : T -∗ gwc_pdg k v I a i.
  Proof using. iIntros "H". rewrite /gwc_pdg. by iRight. Qed.
  Lemma gwc_pdiag_taint k v I a i : T -∗ gwc_pdiag k v I a i.
  Proof using.
    iIntros "H". rewrite /gwc_pdiag. destruct i;
      [by iApply gwc_pban_taint | by iApply gwc_pdg_taint].
  Qed.
  Lemma gwc_lpr_taint k v I p : T -∗ gwc_lpr k v I p.
  Proof using.
    iIntros "H". rewrite /gwc_lpr. destruct p as [| [| [| p]]];
      [by iApply gwc_line_taint | by iApply gwc_sp_t_taint
      | by iApply gwc_open_t_taint | by iApply gwc_blk_taint].
  Qed.

  Lemma gwc_pro_owed k v I : gwc_pro k v I -∗ gwc_owed k v I.
  Proof using.
    rewrite /gwc_pro /gwc_owed.
    iIntros "[Hc | [Hc | Hc]]"; [| by iRight; iLeft | by iRight; iRight].
    iDestruct "Hc" as (ps cs s0 P) "[%Hw Hc]".
    iLeft. iExists ps, cs, s0, P. iFrame "Hc". iPureIntro. by left.
  Qed.

  Lemma gwc_blk_owed k v I a : gwc_blk k v I a 0 -∗ gwc_owed k v I.
  Proof using.
    rewrite /gwc_blk /gwc_owed.
    iIntros "[Hc | Hc]"; [| by iRight; iRight].
    iDestruct "Hc" as (ps cs s0 P) "(%Hw & Htn & Hps & Hcs & HE & Hf)".
    cbn [lm_blkcs]. rewrite Nat.add_0_r.
    iLeft. iExists ps, cs, s0, P. rewrite /gcur. iFrame "Htn Hps Hcs HE Hf".
    iPureIntro. right. exact (proj1 Hw).
  Qed.

  Lemma gwc_sp_t_sp k v I : gwc_sp_t k v I -∗ gwc_sp k v I.
  Proof using.
    rewrite /gwc_sp_t /gwc_sp. iIntros "[Hc | Hc]"; [| by iRight].
    iDestruct "Hc" as (ps cs s0 P) "[%Hw Hc]".
    iLeft. iExists ps, cs, s0, P. iFrame "Hc". iPureIntro. exact (proj1 Hw).
  Qed.

  Lemma gwc_open_t_open k v I : gwc_open_t k v I -∗ gwc_open k v I.
  Proof using.
    rewrite /gwc_open_t /gwc_open. iIntros "[Hc | Hc]"; [| by iRight].
    iDestruct "Hc" as (ps cs s0 P) "[%Hw Hc]".
    iLeft. iExists ps, cs, s0, P. iFrame "Hc". iPureIntro. exact (proj1 Hw).
  Qed.

  Lemma gwc_blk_0 k v I a a' : gwc_blk k v I a 0 -∗ gwc_blk k v I a' 0.
  Proof using. rewrite /gwc_blk. cbn [lm_blkcs]. iIntros "Hc". iExact "Hc". Qed.

  (* the landed post shape is the instance at a state-free alternative *)
  Lemma gwc_post_of_blk k v I a :
    lm_apr M K I a ->
    gwc_blk k v I a (length (lm_ab M K I a) - 2) -∗ gwc_post k v I a.
  Proof using.
    intros Ha. rewrite /gwc_blk /gwc_post. iIntros "[Hc | Hc]"; [| by iRight].
    iDestruct "Hc" as (ps cs s0 P) "(%Hw & Htn & Hps & Hcs & HE & Hf)".
    iLeft. iExists ps, cs, s0, P. rewrite (lm_abs_ab M K s0 cs I a Ha).
    iFrame "Htn Hps Hcs HE Hf". by iPureIntro.
  Qed.

  Lemma gwc_line_of_blk0 k v I a : gwc_blk k v I a 0 -∗ gwc_line k v I.
  Proof using.
    iIntros "Hc". rewrite /gwc_line. iRight. iLeft.
    iExists (lmh_noc K (lm_line_at M I)).
    iSplitR; [iPureIntro; exact (lm_apr_aprs M K _ _ (lm_apr_noc M K I)) |].
    iApply (gwc_post_of_blk k v I _ (lm_apr_noc M K I)).
    rewrite (lm_ab_noc M K I) ll_prompt_len.
    cbn [Nat.sub]. iApply (gwc_blk_0 with "Hc").
  Qed.

  Lemma gwc_line_of_post k v I a :
    lm_apr M K I a ->
    gwc_blk k v I a (length (lm_ab M K I a) - 2) -∗ gwc_line k v I.
  Proof using.
    intros Ha. iIntros "Hc". rewrite /gwc_line. iRight. iLeft. iExists a.
    iSplitR; [iPureIntro; exact (lm_apr_aprs M K I a Ha) |].
    iApply (gwc_post_of_blk k v I a Ha with "Hc").
  Qed.

  Lemma gwc_line_of_posts k v I a :
    lm_aprs M I a -> gwc_post k v I a -∗ gwc_line k v I.
  Proof using.
    intros Ha. iIntros "Hc". rewrite /gwc_line. iRight. iLeft. iExists a.
    iSplitR; [by iPureIntro |]. iExact "Hc".
  Qed.

  Lemma gwc_line_of_pro k v I : gwc_pro k v I -∗ gwc_line k v I.
  Proof using. iIntros "Hc". rewrite /gwc_line. by iLeft. Qed.

  Lemma gwc_lend_of_blk0 k v I a : gwc_blk k v I a 0 -∗ gwc_lend k v I.
  Proof using.
    rewrite /gwc_blk /gwc_lend. cbn [lm_blkcs].
    iIntros "[Hc | Hc]"; [| by iRight].
    iDestruct "Hc" as (ps cs s0 P) "(%Hw & Htn & Hps & Hcs & HE & Hf)".
    rewrite Nat.add_0_r. iLeft. iExists ps, cs, s0, P.
    rewrite /gcur. by iFrame "Htn Hps Hcs HE Hf".
  Qed.

  Lemma gwc_blk_sp k v I a :
    lm_apr M K I a ->
    gwc_blk k v I a (length (lm_ab M K I a) - 1) -∗ gwc_sp_t k v I.
  Proof using.
    intros Ha. rewrite /gwc_blk /gwc_sp_t. iIntros "[Hc | Hc]"; [| by iRight].
    iDestruct "Hc" as (ps cs s0 P) "(%Hw & Htn & Hps & Hcs & HE & Hf)".
    pose proof (lm_ab_len_ge2 M K I a Ha) as Hlen.
    assert (Hbc : lm_blkcs cs a (length (lm_ab M K I a) - 1) = cs ++ [a]).
    { destruct (length (lm_ab M K I a) - 1) as [| kk] eqn:Hk;
        [exfalso; lia | reflexivity]. }
    rewrite Hbc.
    iLeft. iExists ps, (cs ++ [a]), s0, (P + (length (lm_ab M K I a) - 1)).
    rewrite /gcur. iFrame "Htn Hps Hcs HE Hf". iPureIntro.
    exact (lm_wr_blk_sp M K ps cs s0 I P a Hw Ha).
  Qed.

  (* ---- the banner's readings ---- *)
  Lemma gwc_ban_pro k v I : gwc_ban k v I 0 -∗ gwc_pro k v I.
  Proof using.
    rewrite /gwc_ban /gwc_pro.
    iIntros "[Hc | [[_ Hc] | Hc]]"; [| by iRight; iLeft | by iRight; iRight].
    iDestruct "Hc" as (ps cs s0 P) "(%Hw & Htn & Hps & Hcs & HE & Hf)".
    cbn [lm_wr_banp] in Hw. rewrite Nat.add_0_r.
    iLeft. iExists ps, cs, s0, P. rewrite /gcur.
    iFrame "Htn Hps Hcs HE Hf". iPureIntro.
    exact (lm_wr_ban_pro M L ps cs s0 I P Hw).
  Qed.

  Lemma gwc_ban_owed k v I : gwc_ban k v I 0 -∗ gwc_owed k v I.
  Proof using.
    iIntros "Hc". iApply gwc_pro_owed. iApply (gwc_ban_pro with "Hc").
  Qed.

  Lemma gwc_ban_done_pro k v I : gwc_ban k v I (length u_banner) -∗ gwc_pro k v I.
  Proof using.
    rewrite /gwc_ban /gwc_pro.
    assert (H18 : length u_banner = 18) by (vm_compute; reflexivity).
    rewrite H18.
    iIntros "[Hc | [[%Hq _] | Hc]]"; [| discriminate Hq | by iRight; iRight].
    iDestruct "Hc" as (ps cs s0 P) "(%Hw & Htn & Hps & Hcs & HE & Hf)".
    cbn [lm_wr_banp] in Hw. destruct Hw as (ps' & -> & Hw).
    iLeft. iExists (ps' ++ [3]), cs, s0, (P + 18). rewrite /gcur.
    iFrame "Htn Hps Hcs HE Hf". iPureIntro.
    pose proof (lm_wr_ban_done M L ps' cs s0 I P Hw) as Hd. by rewrite H18 in Hd.
  Qed.

  Lemma gwc_ban_done k v I : gwc_ban k v I (length u_banner) -∗ gwc_owed k v I.
  Proof using.
    iIntros "Hc". iApply gwc_pro_owed. iApply (gwc_ban_done_pro with "Hc").
  Qed.

  Lemma gwc_ban_done_line k v I : gwc_ban k v I (length u_banner) -∗ gwc_line k v I.
  Proof using.
    iIntros "Hc". iApply gwc_line_of_pro. iApply (gwc_ban_done_pro with "Hc").
  Qed.

  Lemma gwc_ban_inp k v I :
    gwc_ban k v I 0 -∗ gwc_ban k v I 0 ∗ ((inp_lb v I ∗ ⌜rest_of I = []⌝) ∨ T).
  Proof using.
    rewrite /gwc_ban.
    iIntros "[Hc | [[%Hi Hh] | #Hc]]"; last first.
    { iSplitR; [iRight; by iRight | iRight; iExact "Hc"]. }
    { iDestruct (gH_inp G with "Hh") as "(Hh & %HI & #HE)".
      iSplitL "Hh".
      - iRight. iLeft. iSplitR; [by iPureIntro |]. iExact "Hh".
      - iLeft. subst I. iFrame "HE". iPureIntro. exact rest_of_nil. }
    iDestruct "Hc" as (ps cs s0 P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    cbn [lm_wr_banp] in Hw.
    iSplitL "Htn".
    - iLeft. iExists ps, cs, s0, P. by iFrame "Htn Hps Hcs HE Hf".
    - iLeft. iFrame "HE". iPureIntro. exact (proj1 (proj2 Hw)).
  Qed.

  (* ---- the read of a completed line ---- *)
  Lemma gwc_read k v I l :
    wl_nl ∉ l ->
    inp_lb v (I ++ l ++ [wl_nl]) -∗ gwc_open k v I -∗ gwc_owed k v (I ++ l ++ [wl_nl]).
  Proof using.
    intros Hl. iIntros "#HE' Hc". rewrite /gwc_open /gwc_owed.
    iDestruct "Hc" as "[Hc | Hc]"; [| by iRight; iRight].
    iDestruct "Hc" as (ps cs s0 P) "(%Hw & Htn & Hps & Hcs & _ & Hf)".
    iLeft. iExists ps, cs, s0, P. rewrite /gcur.
    iFrame "Htn Hps Hcs HE' Hf". iPureIntro. right.
    exact (lm_wr_open_read M ps cs s0 I P l Hw Hl).
  Qed.

  Lemma gwc_read_t k v I a l :
    wl_nl ∉ l ->
    inp_lb v (I ++ l ++ [wl_nl]) -∗ gwc_open_t k v I -∗
    gwc_blk k v (I ++ l ++ [wl_nl]) a 0.
  Proof using.
    intros Hl. iIntros "#HE' Hc". rewrite /gwc_open_t /gwc_blk.
    iDestruct "Hc" as "[Hc | Hc]"; [| by iRight].
    iDestruct "Hc" as (ps cs s0 P) "(%Hw & Htn & Hps & Hcs & _ & Hf)".
    iLeft. iExists ps, cs, s0, P. cbn [lm_blkcs]. rewrite Nat.add_0_r.
    iFrame "Htn Hps Hcs HE' Hf". iPureIntro.
    exact (lm_wr_open_read_t M ps cs s0 I P l Hw Hl).
  Qed.

  (* ---- the panic's five bytes leave the next round's banner ---- *)
  Lemma gwc_panic_done k v I :
    gwc_blk k v I (lmh_pan K (lm_line_at M I))
      (length (lm_ab M K I (lmh_pan K (lm_line_at M I)))) -∗ gwc_ban k v I 0.
  Proof using.
    rewrite /gwc_blk /gwc_ban.
    iIntros "[Hc | Hc]"; [| by iRight; iRight].
    iDestruct "Hc" as (ps cs s0 P) "(%Hw & Htn & Hps & Hcs & HE & Hf)".
    assert (Hbc : lm_blkcs cs (lmh_pan K (lm_line_at M I))
                    (length (lm_ab M K I (lmh_pan K (lm_line_at M I))))
                  = cs ++ [lmh_pan K (lm_line_at M I)]).
    { rewrite (lm_ab_pan M L K I) lb_panic_len. reflexivity. }
    rewrite Hbc.
    iLeft. iExists ps, (cs ++ [lmh_pan K (lm_line_at M I)]), s0,
      (P + length (lm_ab M K I (lmh_pan K (lm_line_at M I)))).
    rewrite Nat.add_0_r. iFrame "Htn Hps Hcs HE Hf". iPureIntro. cbn [lm_wr_banp].
    exact (lm_wr_blk_ban M L K ps cs s0 I P Hw).
  Qed.

  (* ---- the prologue diagnostics' readings ---- *)
  Lemma gwc_pdiag_0 k v I a : gwc_pban k v I -∗ gwc_pdiag k v I a 0.
  Proof using. by iIntros "$". Qed.

  Lemma gwc_pban_of_ban_done k v I :
    gwc_ban k v I (length u_banner) -∗ gwc_pban k v I.
  Proof using.
    rewrite /gwc_ban /gwc_pban.
    assert (H18 : length u_banner = 18) by (vm_compute; reflexivity).
    rewrite H18.
    iIntros "[Hc | [[%Hq _] | Hc]]"; [| discriminate Hq | by iRight].
    iDestruct "Hc" as (ps cs s0 P) "(%Hw & Htn & Hps & Hcs & HE & Hf)".
    cbn [lm_wr_banp] in Hw. destruct Hw as (ps' & -> & Hw).
    iLeft. iExists (ps' ++ [3]), cs, s0, (P + 18). rewrite /gcur.
    iFrame "Htn Hps Hcs HE Hf". iPureIntro.
    pose proof (lm_wr_pban_of_ban M L ps' cs s0 I P Hw) as Hd. by rewrite H18 in Hd.
  Qed.

  Lemma gwc_pro_of_pban k v I : gwc_pban k v I -∗ gwc_pro k v I.
  Proof using.
    rewrite /gwc_pban /gwc_pro. iIntros "[Hc | Hc]"; [| by iRight; iRight].
    iDestruct "Hc" as (ps cs s0 P) "[%Hw Hc]".
    iLeft. iExists ps, cs, s0, P. iFrame "Hc". iPureIntro. exact (proj1 Hw).
  Qed.

  Lemma gwc_pdiag_done_1 k v I i :
    i = length (pro_alts !!! 1) -> gwc_pdiag k v I 1 i -∗ gwc_ban k v I 0.
  Proof using.
    intros Hi. subst i. rewrite /gwc_pdiag /gwc_pdg /gwc_ban.
    assert (H21 : length (pro_alts !!! 1) = 21) by (vm_compute; reflexivity).
    rewrite H21. iIntros "[Hc | Hc]"; [| by iRight; iRight].
    iDestruct "Hc" as (ps cs s0 P) "[%Hw Hc]".
    iLeft. iExists ps, cs, s0, P. rewrite Nat.add_0_r /gcur. iFrame "Hc".
    iPureIntro. cbn [lm_wr_banp].
    exact (lm_wr_pdiag_done_1 M ps cs s0 I P 21 ltac:(by rewrite H21) Hw).
  Qed.

  (* ================================================================== *)
  (*  3.  THE LINKS INTERFACE                                            *)
  (* ================================================================== *)

  (* (W) a byte of the stream at the cursor *)
  Definition gl_w : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (P : nat) (b : bv 8)
         (ps0 cs0 : list nat) (s0 : lm_st M) (I0 : list (bv 8)) (Φ : iProp Σ),
        ⌜nlines I0 <= length cs0⌝ -∗
        ⌜lm_pro_pin M ps0 cs0 I0⌝ -∗
        ⌜lm_proc_stream M ps0 cs0 s0 I0 !! P = Some b⌝ -∗
        PIN k v -∗ W k s0 -∗ turn v P -∗
        ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
        (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0) ∨ T) -∗ Φ) -∗
        out_link Uart0 k b Φ)%I.

  (* (B) the block-first byte files the round's alternative, at the
     round's own state *)
  Definition gl_blk : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
         (ps0 cs0 : list nat) (s0 : lm_st M) (I0 : list (bv 8)) (Φ : iProp Σ),
        ⌜¬ WL I0⌝ -∗
        ⌜I0 <> []⌝ -∗
        ⌜rest_of I0 = []⌝ -∗
        ⌜nlines I0 <= S (length cs0)⌝ -∗
        ⌜lm_pro_pin M ps0 cs0 I0⌝ -∗
        ⌜P = length (lm_proc_before M ps0 cs0 s0 I0)⌝ -∗
        ⌜lm_ok M (lm_upto M cs0 s0 (bodies_of I0) (nlines I0 - 1)) (lm_line_at M I0)
           (lm_dec M a)⌝ -∗
        ⌜lm_term M (lm_dec M a) = false⌝ -∗
        ⌜lm_abs M s0 cs0 I0 a !! 0 = Some b⌝ -∗
        PIN k v -∗ W k s0 -∗ turn v P -∗
        ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
        (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0) ∨ T)
         -∗ Φ) -∗
        out_link Uart0 k b Φ)%I.

  (* (P) a prologue round's choice byte files the round's alternative *)
  Definition gl_pro : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
         (ps0 cs0 : list nat) (s0 : lm_st M) (I0 : list (bv 8)) (Φ : iProp Σ),
        ⌜rest_of I0 = []⌝ -∗
        ⌜I0 = [] \/ lm_panic M (lm_at M cs0 (nlines I0 - 1)) = true⌝ -∗
        ⌜nlines I0 <= length cs0⌝ -∗
        ⌜lm_pro_pin M ps0 cs0 I0⌝ -∗
        ⌜~ pro_done (pro_from (lm_pro_idx M cs0 (nlines I0)) ps0)⌝ -∗
        ⌜P = length (lm_proc_stream M ps0 cs0 s0 I0)⌝ -∗
        ⌜a < length pro_alts⌝ -∗
        ⌜pro_alts !!! a !! 0 = Some b⌝ -∗
        PIN k v -∗ W k s0 -∗ turn v P -∗
        ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
        (((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ inp_lb v I0) ∨ T)
         -∗ Φ) -∗
        out_link Uart0 k b Φ)%I.

  (* (H) the era's FIRST byte, from the head: it files the boot state *)
  Definition gl_head : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (I : list (bv 8)) (a : nat) (b : bv 8)
         (Φ : iProp Σ),
        ⌜a < length pro_alts⌝ -∗
        ⌜pro_alts !!! a !! 0 = Some b⌝ -∗
        PIN k v -∗ H k v I -∗
        (((∃ s0 : lm_st M,
             turn v 1 ∗ ps_lb v [a] ∗ cs_lb v [] ∗ inp_lb v [] ∗ W k s0) ∨ T)
         -∗ Φ) -∗
        out_link Uart0 k b Φ)%I.

  (* THE TAINT'S BYTE, at the family's own ERA: the taint may license one
     era only (the union's wild token -- seccomp design 10.7), and every
     family step holds the era's pin *)
  Definition gl_taint : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (b : bv 8) (Φ : iProp Σ),
        PIN k v -∗ T -∗ (T -∗ Φ) -∗ out_link Uart0 k b Φ)%I.

  (* ...and at a NAMED era, for a device that is at one and holds no pin
     on its taint arm ([UkConsOut.cons_dev_at]) *)
  Definition gl_taint_at (k : nat) : iProp Σ :=
    (□ ∀ (b : bv 8) (Φ : iProp Σ), T -∗ (T -∗ Φ) -∗ out_link Uart0 k b Φ)%I.

  Definition glinks : iProp Σ := (gl_w ∗ gl_blk ∗ gl_pro ∗ gl_head ∗ gl_taint)%I.

  Global Instance gl_w_persistent : Persistent gl_w.
  Proof using. rewrite /gl_w. apply _. Qed.
  (* [gl_blk] and [gl_pro] name the [□] instance: [apply _] reaches it only
     after trying every [Persistent] instance in scope against the whole
     body, 11 s apiece. *)
  Global Instance gl_blk_persistent : Persistent gl_blk.
  Proof using. rewrite /gl_blk. apply bi.intuitionistically_persistent. Qed.
  Global Instance gl_pro_persistent : Persistent gl_pro.
  Proof using. rewrite /gl_pro. apply bi.intuitionistically_persistent. Qed.
  Global Instance gl_head_persistent : Persistent gl_head.
  Proof using. rewrite /gl_head. apply _. Qed.
  Global Instance gl_taint_persistent : Persistent gl_taint.
  Proof using. rewrite /gl_taint. apply _. Qed.
  Global Instance gl_taint_at_persistent k : Persistent (gl_taint_at k).
  Proof using. rewrite /gl_taint_at. apply _. Qed.
  Global Instance glinks_persistent : Persistent glinks.
  Proof using. rewrite /glinks. apply _. Qed.

  (* the tier's own links resource, which entails the interface *)
  Context (LINKS : iProp Σ) (LINKS_pers : Persistent LINKS)
          (LINKS_gl : LINKS -∗ glinks).
  #[local] Existing Instance LINKS_pers.
  (* ...and the extra arm's own prompt step, which the module proves *)
  Context (X_dollar : forall (k : nat) (v : era_pins) (I : list (bv 8))
                             (b : bv 8) (Φ : iProp Σ),
             b = u_prompt !!! 0 ->
             PIN k v -∗ LINKS -∗ X k v I -∗
             (gwc_sp_t k v I -∗ Φ) -∗ out_link Uart0 k b Φ).

  (* ================================================================== *)
  (*  4.  THE STEPS                                                      *)
  (* ================================================================== *)

  (* ---- /init's banner ---- *)
  Lemma gban_step (k : nat) (v : era_pins) (I : list (bv 8)) (i : nat)
      (b : bv 8) (Φ : iProp Σ) :
    u_banner !! i = Some b ->
    PIN k v -∗ LINKS -∗ gwc_ban k v I i -∗
    (gwc_ban k v I (S i) -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using LINKS_gl LINKS_pers.
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (LINKS_gl with "Hlk") as "#(Hw & _ & Hpro & Hhd & Ht)".
    rewrite {1}/gwc_ban.
    iDestruct "Hc" as "[Hl | [[%Hi0 Hh] | #HT]]"; last first.
    { iApply ("Ht" $! k v b Φ with "Hpin HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply gwc_ban_taint. }
    { (* THE ERA'S HEAD: the first byte files the boot state *)
      subst i. iDestruct (gH_inp G with "Hh") as "(Hh & -> & _)".
      iApply ("Hhd" $! k v [] 3 b Φ with "[%] [%] Hpin Hh [HΦ]").
      { rewrite pro_alts_length. lia. }
      { exact (EchoLinks.wr_ban_head b Hb). }
      iIntros "Hres". iApply "HΦ". rewrite /gwc_ban.
      iDestruct "Hres" as "[Hres | #HT]"; last by (iRight; iRight).
      iDestruct "Hres" as (s0) "(Htn' & Hps' & Hcs' & HE' & #Hf)".
      iLeft. iExists [3], [], s0, 0.
      rewrite Nat.add_0_l. iFrame "Htn' Hps' Hcs' HE' Hf".
      iPureIntro. cbn [lm_wr_banp]. exists []. split; [reflexivity |].
      exact (lm_wr_ban_round0 M s0). }
    iDestruct "Hl" as (ps cs s0 P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    destruct i as [| i'].
    - (* the first byte FILES the banner letter *)
      cbn [lm_wr_banp] in Hw.
      pose proof (lm_wr_ban_pro M L ps cs s0 I P Hw) as Hpr.
      pose proof Hw as (Hpin0 & Hm & Hdv & Hr & _).
      destruct Hpr as (_ & _ & _ & _ & Hnd & HP).
      rewrite Nat.add_0_r.
      iApply ("Hpro" $! k v P 3 b ps cs s0 I Φ
                with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Hf Htn Hps Hcs HE [HΦ]").
      { exact Hm. } { exact Hr. } { lia. } { exact Hpin0. }
      { exact Hnd. } { exact HP. }
      { rewrite pro_alts_length. lia. }
      { exact (EchoLinks.wr_ban_head b Hb). }
      iIntros "Hres". iApply "HΦ". rewrite /gwc_ban.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]";
        last by (iRight; iRight).
      iLeft. iExists (ps ++ [3]), cs, s0, P.
      replace (P + 1) with (S P) by lia.
      iFrame "Htn' Hps' Hcs' HE' Hf".
      iPureIntro. cbn [lm_wr_banp]. by exists ps.
    - (* every later byte is an ordinary write of the filed letter *)
      cbn [lm_wr_banp] in Hw. destruct Hw as (ps' & -> & Hw).
      pose proof (lm_wr_ban_byte M L ps' cs s0 I P (S i') b Hw Hb) as Hby.
      pose proof Hw as (Hpin0 & Hm & Hdv & Hr & _).
      iApply ("Hw" $! k v (P + S i') b (ps' ++ [3]) cs s0 I Φ
                with "[%] [%] [%] Hpin Hf Htn Hps Hcs HE [HΦ]").
      { lia. }
      { exact (lm_pro_pin_mono M ps' (ps' ++ [3]) cs I ltac:(by eexists) Hpin0). }
      { exact Hby. }
      iIntros "Hres". iApply "HΦ". rewrite /gwc_ban.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]";
        last by (iRight; iRight).
      iLeft. iExists (ps' ++ [3]), cs, s0, P.
      replace (P + S (S i')) with (S (P + S i')) by lia.
      iFrame "Htn' Hps' Hcs' HE' Hf".
      iPureIntro. cbn [lm_wr_banp]. by exists ps'.
  Qed.

  (* ---- a block's bytes ---- *)
  Lemma gblk_step (k : nat) (v : era_pins) (I : list (bv 8)) (a i : nat)
      (b : bv 8) (Φ : iProp Σ) :
    lm_ab M K I a !! i = Some b ->
    (⌜¬ WL I⌝ ∨ T) -∗
    PIN k v -∗ LINKS -∗ gwc_blk k v I a i -∗
    (gwc_blk k v I a (S i) -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using LINKS_gl LINKS_pers.
    intros Hb. iIntros "Hnw #Hpin #Hlk Hc HΦ".
    iDestruct (LINKS_gl with "Hlk") as "#(Hw & Hblk & _ & _ & Ht)".
    destruct (lm_ab_ok M K I a i b Hb) as [Hok Hfr].
    iDestruct "Hnw" as "[%Hnw | #HT]".
    2: { iApply ("Ht" $! k v b Φ with "Hpin HT [HΦ]").
         iIntros "#HT'". iApply "HΦ". by iApply gwc_blk_taint. }
    rewrite {1}/gwc_blk. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k v b Φ with "Hpin HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply gwc_blk_taint. }
    iDestruct "Hl" as (ps cs s0 P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    pose proof (proj1 Hw) as Hwb.
    pose proof Hwb as (Hpin0 & Hr & Hn & HP).
    pose proof (lm_wr_blk_nonnil M ps cs s0 I P Hwb) as Hne.
    destruct i as [| i'].
    - (* THE BLOCK-FIRST BYTE files the alternative *)
      cbn [lm_blkcs]. rewrite Nat.add_0_r.
      iApply ("Hblk" $! k v P a b ps cs s0 I Φ
                with "[%] [%] [%] [%] [%] [%] [%] [%] [%] Hpin Hf Htn Hps Hcs HE [HΦ]").
      { exact Hnw. }
      { exact Hne. }
      { exact Hr. }
      { rewrite Hn. lia. }
      { exact Hpin0. }
      { exact HP. }
      { exact (lmh_free_ok K _ _ _ _ Hfr Hok). }
      { exact (lmh_free_term K _ Hfr). }
      { rewrite /lm_abs -(lm_ab_at M K I a _ Hok Hfr). exact Hb. }
      iIntros "Hres". iApply "HΦ". rewrite /gwc_blk.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists ps, cs, s0, P. cbn [lm_blkcs].
      replace (P + 1) with (S P) by lia.
      iFrame "Htn' Hps' Hcs' HE' Hf". by iPureIntro.
    - (* every byte after it, at the choice list the first one extended *)
      cbn [lm_blkcs].
      iApply ("Hw" $! k v (P + S i') b ps (cs ++ [a]) s0 I Φ
                with "[%] [%] [%] Hpin Hf Htn Hps Hcs HE [HΦ]").
      { rewrite length_app Hn. cbn [length]. lia. }
      { exact (lm_wr_blk_pin_snoc M ps cs s0 I P a Hwb). }
      { pose proof (lm_wr_blk_pending_pre M K ps cs s0 I P a Hwb Hok Hfr) as Hpre.
        rewrite /lm_proc_stream (lm_wr_blk_low M ps cs s0 I P a Hwb)
                lookup_app_r; [| lia].
        replace (P + S i' - length (lm_proc_before M ps cs s0 I)) with (S i') by lia.
        exact (prefix_lookup_Some _ _ _ _ Hb Hpre). }
      iIntros "Hres". iApply "HΦ". rewrite /gwc_blk.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists ps, cs, s0, P. cbn [lm_blkcs].
      replace (P + S (S i')) with (S (P + S i')) by lia.
      iFrame "Htn' Hps' Hcs' HE' Hf". by iPureIntro.
  Qed.

  (* ---- the shell's prompt: the '$' from the era's head ---- *)
  Lemma ghead_dollar (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 0 ->
    PIN k v -∗ LINKS -∗ H k v I -∗
    (gwc_sp k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using LINKS_gl LINKS_pers.
    intros Hb. iIntros "#Hpin #Hlk Hh HΦ".
    iDestruct (LINKS_gl with "Hlk") as "#(_ & _ & _ & Hhd & _)".
    iDestruct (gH_inp G with "Hh") as "(Hh & -> & _)".
    iApply ("Hhd" $! k v [] 0 b Φ with "[%] [%] Hpin [Hh] [HΦ]").
    { rewrite pro_alts_length. lia. }
    { rewrite ll_pro_alts_0 Hb. exact EchoLinks.wr_prompt_head. }
    { iExact "Hh". }
    iIntros "Hres". iApply "HΦ". rewrite /gwc_sp.
    iDestruct "Hres" as "[Hres | #HT]"; last by iRight.
    iDestruct "Hres" as (s0) "(Htn' & Hps' & Hcs' & HE' & #Hf)".
    iLeft. iExists [0], [], s0, 1. rewrite /gcur.
    iFrame "Htn' Hps' Hcs' HE' Hf". iPureIntro. exact (lm_wr_sp_head M L s0).
  Qed.
  (* ---- the shell's prompt at the loose shapes ---- *)
  Lemma gprompt_dollar (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 0 ->
    (⌜¬ WL I⌝ ∨ T) -∗
    PIN k v -∗ LINKS -∗ gwc_owed k v I -∗
    (gwc_sp k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using LINKS_gl LINKS_pers.
    intros Hb. iIntros "Hnw #Hpin #Hlk Hc HΦ".
    iDestruct (LINKS_gl with "Hlk") as "#(_ & Hblk & Hpro & _ & Ht)".
    iDestruct "Hnw" as "[%Hnw | #HT]".
    2: { iApply ("Ht" $! k v b Φ with "Hpin HT [HΦ]").
         iIntros "#HT'". iApply "HΦ". by iApply gwc_sp_taint. }
    rewrite {1}/gwc_owed.
    iDestruct "Hc" as "[Hl | [Hh | #HT]]"; last first.
    { iApply ("Ht" $! k v b Φ with "Hpin HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply gwc_sp_taint. }
    { iApply (ghead_dollar k v I b Φ Hb with "Hpin Hlk Hh HΦ"). }
    iDestruct "Hl" as (ps cs s0 P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    destruct Hw as [Hw | Hw].
    - (* the round's prologue is open: the '$' files alternative 0 *)
      pose proof (lm_wr_pro_dollar M L ps cs s0 I P Hw) as Hsp.
      destruct Hw as (Hpin0 & Hm & Hdv & Hr & Hnd & HP).
      iApply ("Hpro" $! k v P 0 b ps cs s0 I Φ
                with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Hf Htn Hps Hcs HE [HΦ]").
      { exact Hm. } { exact Hr. } { lia. } { exact Hpin0. }
      { exact Hnd. } { exact HP. }
      { rewrite pro_alts_length. lia. }
      { rewrite ll_pro_alts_0 Hb. exact EchoLinks.wr_prompt_head. }
      iIntros "Hres". iApply "HΦ". rewrite /gwc_sp.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists (ps ++ [0]), cs, s0, (S P). rewrite /gcur.
      iFrame "Htn' Hps' Hcs' HE' Hf". by iPureIntro.
    - (* the round is settled: the '$' is the line's block-first byte *)
      pose proof (lm_wr_blk_dollar M K ps cs s0 I P Hw) as Hsp.
      pose proof (lm_wr_blk_nonnil M ps cs s0 I P Hw) as Hne.
      pose proof Hw as (Hpin0 & Hm & Hdv & HP).
      iApply ("Hblk" $! k v P (lmh_noc K (lm_line_at M I)) b ps cs s0 I Φ
                with "[%] [%] [%] [%] [%] [%] [%] [%] [%] Hpin Hf Htn Hps Hcs HE [HΦ]").
      { exact Hnw. } { exact Hne. } { exact Hm. } { rewrite Hdv. lia. } { exact Hpin0. }
      { exact HP. }
      { exact (lmh_noc_ok K _ (lm_line_at M I)). }
      { exact (lmh_free_term K _ (lmh_noc_free K (lm_line_at M I))). }
      { rewrite /lm_abs (lmh_noc_cont K _ (lm_line_at M I)) Hb.
        exact EchoLinks.wr_prompt_head. }
      iIntros "Hres". iApply "HΦ". rewrite /gwc_sp.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists ps, (cs ++ [lmh_noc K (lm_line_at M I)]), s0, (S P).
      rewrite /gcur. iFrame "Htn' Hps' Hcs' HE' Hf". by iPureIntro.
  Qed.

  Lemma gprompt_space (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 1 ->
    PIN k v -∗ LINKS -∗ gwc_sp k v I -∗
    (gwc_open k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using LINKS_gl LINKS_pers.
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (LINKS_gl with "Hlk") as "#(Hw & _ & _ & _ & Ht)".
    rewrite {1}/gwc_sp. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k v b Φ with "Hpin HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply gwc_open_taint. }
    iDestruct "Hl" as (ps cs s0 P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    destruct Hw as [Hop Hby].
    pose proof Hop as (Hpin0 & Hm & Hdv & Hrd & HP).
    iApply ("Hw" $! k v P b ps cs s0 I Φ
              with "[%] [%] [%] Hpin Hf Htn Hps Hcs HE [HΦ]").
    { lia. } { exact Hpin0. } { rewrite Hby Hb. reflexivity. }
    iIntros "Hres". iApply "HΦ". rewrite /gwc_open.
    iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
    iLeft. iExists ps, cs, s0, (S P). rewrite /gcur.
    iFrame "Htn' Hps' Hcs' HE' Hf".
    iPureIntro. exact (lm_wr_sp_open M ps cs s0 I P (conj Hop Hby)).
  Qed.

  Lemma gprompt_dollar_ban (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 0 ->
    (⌜¬ WL I⌝ ∨ T) -∗
    PIN k v -∗ LINKS -∗ gwc_ban k v I 0 -∗
    (gwc_sp k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using LINKS_gl LINKS_pers.
    intros Hb. iIntros "Hnw #Hpin #Hlk Hc HΦ".
    iApply (gprompt_dollar k v I b Φ Hb with "Hnw Hpin Hlk [Hc] HΦ").
    iApply (gwc_ban_owed with "Hc").
  Qed.

  (* ---- the prompt at the TIGHT shapes ---- *)
  Lemma gprompt_dollar_post (k : nat) (v : era_pins) (I : list (bv 8))
      (a : nat) (b : bv 8) (Φ : iProp Σ) :
    lm_apr M K I a -> b = u_prompt !!! 0 ->
    (⌜¬ WL I⌝ ∨ T) -∗
    PIN k v -∗ LINKS -∗
    gwc_blk k v I a (length (lm_ab M K I a) - 2) -∗
    (gwc_sp_t k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using LINKS_gl LINKS_pers.
    intros Ha Hb. iIntros "Hnw #Hpin #Hlk Hc HΦ".
    pose proof (lm_ab_len_ge2 M K I a Ha) as Hlen.
    assert (Hby : lm_ab M K I a !! (length (lm_ab M K I a) - 2) = Some b)
      by (rewrite Hb; exact (lm_ab_dollar M K I a Ha)).
    iApply (gblk_step k v I a (length (lm_ab M K I a) - 2) b Φ Hby
              with "Hnw Hpin Hlk Hc [HΦ]").
    iIntros "Hc". iApply "HΦ".
    replace (S (length (lm_ab M K I a) - 2)) with (length (lm_ab M K I a) - 1) by lia.
    iApply (gwc_blk_sp k v I a Ha with "Hc").
  Qed.

  Lemma gprompt_space_t (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 1 ->
    PIN k v -∗ LINKS -∗ gwc_sp_t k v I -∗
    (gwc_open_t k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using LINKS_gl LINKS_pers.
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (LINKS_gl with "Hlk") as "#(Hw & _ & _ & _ & Ht)".
    rewrite {1}/gwc_sp_t. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k v b Φ with "Hpin HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply gwc_open_t_taint. }
    iDestruct "Hl" as (ps cs s0 P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    destruct Hw as [[Hop Hby] Htl].
    pose proof Hop as (Hpin0 & Hm & Hdv & Hrd & HP).
    iApply ("Hw" $! k v P b ps cs s0 I Φ
              with "[%] [%] [%] Hpin Hf Htn Hps Hcs HE [HΦ]").
    { lia. } { exact Hpin0. } { rewrite Hby Hb. reflexivity. }
    iIntros "Hres". iApply "HΦ". rewrite /gwc_open_t.
    iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
    iLeft. iExists ps, cs, s0, (S P). rewrite /gcur.
    iFrame "Htn' Hps' Hcs' HE' Hf". iPureIntro.
    exact (lm_wr_sp_open_t M ps cs s0 I P (conj (conj Hop Hby) Htl)).
  Qed.

  (* THE PROMPT'S DOLLAR AT THE STATE-AWARE POST: the block step's two arms
     at the block's last-but-one byte, read off the round's own state *)
  Lemma gprompt_dollar_posts (k : nat) (v : era_pins) (I : list (bv 8))
      (a : nat) (b : bv 8) (Φ : iProp Σ) :
    lm_aprs M I a -> b = u_prompt !!! 0 ->
    (⌜¬ WL I⌝ ∨ T) -∗
    PIN k v -∗ LINKS -∗ gwc_post k v I a -∗
    (gwc_sp_t k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using LINKS_gl LINKS_pers.
    intros Ha Hb. iIntros "Hnw #Hpin #Hlk Hc HΦ".
    iDestruct (LINKS_gl with "Hlk") as "#(Hw & Hblk & _ & _ & Ht)".
    pose proof Ha as (Hok & Hnp & Hnt).
    iDestruct "Hnw" as "[%Hnw | #HT]".
    2: { iApply ("Ht" $! k v b Φ with "Hpin HT [HΦ]").
         iIntros "#HT'". iApply "HΦ". rewrite /gwc_sp_t. by iRight. }
    rewrite {1}/gwc_post. iDestruct "Hc" as "[Hl | #HT]"; last first.
    { iApply ("Ht" $! k v b Φ with "Hpin HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". rewrite /gwc_sp_t. by iRight. }
    iDestruct "Hl" as (ps cs s0 P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    pose proof (proj1 Hw) as Hwb.
    pose proof Hwb as (Hpin0 & Hr & Hn & HP).
    pose proof (lm_wr_blk_nonnil M ps cs s0 I P Hwb) as Hne.
    pose proof (lm_abs_len_ge2 M K s0 cs I a Ha) as Hlen.
    pose proof (lm_abs_dollar M K s0 cs I a Ha) as Hby. rewrite -Hb in Hby.
    pose proof (lm_wr_blk_sp_s M K ps cs s0 I P a Hw Ha) as Hsp.
    destruct (length (lm_abs M s0 cs I a) - 2) as [| i'] eqn:Hi.
    - (* the prompt IS the block's first byte: it files the alternative *)
      cbn [lm_blkcs]. rewrite Nat.add_0_r.
      iApply ("Hblk" $! k v P a b ps cs s0 I Φ
                with "[%] [%] [%] [%] [%] [%] [%] [%] [%] Hpin Hf Htn Hps Hcs HE [HΦ]").
      { exact Hnw. } { exact Hne. } { exact Hr. } { rewrite Hn. lia. } { exact Hpin0. }
      { exact HP. } { exact (Hok _). } { exact Hnt. }
      { exact Hby. }
      iIntros "Hres". iApply "HΦ". rewrite /gwc_sp_t.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists ps, (cs ++ [a]), s0, (S P).
      replace (P + (length (lm_abs M s0 cs I a) - 1)) with (S P) in Hsp by lia.
      replace (P + 1) with (S P) by lia.
      rewrite /gcur. iFrame "Htn' Hps' Hcs' HE' Hf". by iPureIntro.
    - (* an ordinary byte of a block already filed *)
      cbn [lm_blkcs].
      iApply ("Hw" $! k v (P + S i') b ps (cs ++ [a]) s0 I Φ
                with "[%] [%] [%] Hpin Hf Htn Hps Hcs HE [HΦ]").
      { rewrite length_app Hn. cbn [length]. lia. }
      { exact (lm_wr_blk_pin_snoc M ps cs s0 I P a Hwb). }
      { exact (lm_wr_blk_byte_s M ps cs s0 I P a (S i') b Hwb Hnp Hby). }
      iIntros "Hres". iApply "HΦ". rewrite /gwc_sp_t.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists ps, (cs ++ [a]), s0, (S (P + S i')).
      replace (P + (length (lm_abs M s0 cs I a) - 1)) with (S (P + S i')) in Hsp by lia.
      rewrite /gcur. iFrame "Htn' Hps' Hcs' HE' Hf". by iPureIntro.
  Qed.

  Lemma gprompt_dollar_line (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 0 ->
    (⌜¬ WL I⌝ ∨ T) -∗
    PIN k v -∗ LINKS -∗ gwc_line k v I -∗
    (gwc_sp_t k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using LINKS_gl LINKS_pers X_dollar.
    intros Hb. iIntros "Hnw #Hpin #Hlk Hc HΦ".
    rewrite {1}/gwc_line. iDestruct "Hc" as "[Hc | [Hc | Hx]]"; last first.
    { iApply (X_dollar k v I b Φ Hb with "Hpin Hlk Hx HΦ"). }
    { iDestruct "Hc" as (a) "[%Ha Hc]".
      iApply (gprompt_dollar_posts k v I a b Φ Ha Hb with "Hnw Hpin Hlk Hc HΦ"). }
    iDestruct (LINKS_gl with "Hlk") as "#(_ & _ & Hpro & Hhd & Ht)".
    rewrite {1}/gwc_pro. iDestruct "Hc" as "[Hl | [Hh | #HT]]"; last first.
    { iApply ("Ht" $! k v b Φ with "Hpin HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply gwc_sp_t_taint. }
    { (* the era's head: the '$' is its first byte, and it lands TIGHT *)
      iDestruct (gH_inp G with "Hh") as "(Hh & -> & _)".
      iApply ("Hhd" $! k v [] 0 b Φ with "[%] [%] Hpin Hh [HΦ]").
      { rewrite pro_alts_length. lia. }
      { rewrite ll_pro_alts_0 Hb. exact EchoLinks.wr_prompt_head. }
      iIntros "Hres". iApply "HΦ". rewrite /gwc_sp_t.
      iDestruct "Hres" as "[Hres | #HT]"; last by iRight.
      iDestruct "Hres" as (s0) "(Htn' & Hps' & Hcs' & HE' & #Hf)".
      iLeft. iExists [0], [], s0, 1. rewrite /gcur.
      iFrame "Htn' Hps' Hcs' HE' Hf". iPureIntro.
      exact (conj (lm_wr_sp_head M L s0) (lm_wr_tail_head M)). }
    iDestruct "Hl" as (ps cs s0 P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    pose proof (lm_wr_pro_dollar_t M L ps cs s0 I P Hw) as Hsp.
    destruct Hw as (Hpin0 & Hm & Hdv & Hr & Hnd & HP).
    iApply ("Hpro" $! k v P 0 b ps cs s0 I Φ
              with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Hf Htn Hps Hcs HE [HΦ]").
    { exact Hm. } { exact Hr. } { lia. } { exact Hpin0. }
    { exact Hnd. } { exact HP. }
    { rewrite pro_alts_length. lia. }
    { rewrite ll_pro_alts_0 Hb. exact EchoLinks.wr_prompt_head. }
    iIntros "Hres". iApply "HΦ". rewrite /gwc_sp_t.
    iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
    iLeft. iExists (ps ++ [0]), cs, s0, (S P). rewrite /gcur.
    iFrame "Htn' Hps' Hcs' HE' Hf". by iPureIntro.
  Qed.

  (* ---- /init's prologue diagnostics, one byte at either link ---- *)
  Lemma gpdiag_step (k : nat) (v : era_pins) (I : list (bv 8)) (a i : nat)
      (b : bv 8) (Φ : iProp Σ) :
    pro_alts !!! a !! i = Some b ->
    PIN k v -∗ LINKS -∗ gwc_pdiag k v I a i -∗
    (gwc_pdiag k v I a (S i) -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using LINKS_gl LINKS_pers.
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (LINKS_gl with "Hlk") as "#(Hw & _ & Hpro & _ & Ht)".
    destruct i as [| i'].
    - (* the choice byte files [a] *)
      rewrite {1}/gwc_pdiag /gwc_pban.
      iDestruct "Hc" as "[Hl | #HT]"; last first.
      { iApply ("Ht" $! k v b Φ with "Hpin HT [HΦ]").
        iIntros "#HT'". iApply "HΦ". by iApply gwc_pdiag_taint. }
      iDestruct "Hl" as (ps cs s0 P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
      pose proof (lm_wr_pdiag_1_of_pro M L ps cs s0 I P a Hw) as Hnext.
      destruct Hw as ((Hpin0 & Hm & Hdv & Hr & Hnd & HP) & _).
      assert (Ha : a < length pro_alts)
        by exact (EchoLinksPro.pro_alts_lt_of_lookup a 0 b Hb).
      iApply ("Hpro" $! k v P a b ps cs s0 I Φ
                with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Hf Htn Hps Hcs HE [HΦ]").
      { exact Hm. } { exact Hr. } { lia. } { exact Hpin0. }
      { exact Hnd. } { exact HP. } { exact Ha. } { exact Hb. }
      iIntros "Hres". iApply "HΦ". rewrite /gwc_pdiag /gwc_pdg.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists (ps ++ [a]), cs, s0, (S P). rewrite /gcur.
      iFrame "Htn' Hps' Hcs' HE' Hf". by iPureIntro.
    - (* a later byte of the diagnostic already chosen *)
      rewrite {1}/gwc_pdiag /gwc_pdg.
      iDestruct "Hc" as "[Hl | #HT]"; last first.
      { iApply ("Ht" $! k v b Φ with "Hpin HT [HΦ]").
        iIntros "#HT'". iApply "HΦ". by iApply gwc_pdiag_taint. }
      iDestruct "Hl" as (ps cs s0 P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
      pose proof (lm_wr_pdiag_byte M L ps cs s0 I P a (S i') b Hw Hb) as Hby.
      pose proof (lm_wr_pdiag_S M ps cs s0 I P a (S i') Hw) as Hnext.
      pose proof Hw as (Hpin0 & Hm & Hdv & Hr & _).
      iApply ("Hw" $! k v P b ps cs s0 I Φ
                with "[%] [%] [%] Hpin Hf Htn Hps Hcs HE [HΦ]").
      { lia. } { exact Hpin0. } { exact Hby. }
      iIntros "Hres". iApply "HΦ". rewrite /gwc_pdiag /gwc_pdg.
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists ps, cs, s0, (S P). rewrite /gcur.
      iFrame "Htn' Hps' Hcs' HE' Hf". by iPureIntro.
  Qed.

  (* ================================================================== *)
  (*  5.  THE READ SIDE: a read past a boundary whose prompt is unwritten *)
  (*      is the taint                                                   *)
  (* ================================================================== *)

  (* the tier's read receipt, and what it exposes when something was read:
     the taint, or the reader's residue at the input it delivered *)
  Context (RR : nat -> era_pins -> nat -> list (list mobs * bv 8) -> iProp Σ).
  Context (RR_res : forall k v n ws,
    0 < length ws ->
    RR k v n ws -∗
    T ∨ (∃ (ps0 cs0 : list nat) (s0 : lm_st M) (J : list (bv 8)),
           ⌜length J = (n + length ws)%nat⌝ ∗ ⌜lm_rd_stage M ps0 cs0 s0 J⌝
           ∗ inp_lb v J ∗ turn_lb v (length (lm_proc_before M ps0 cs0 s0 J))
           ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ Wb k s0)).

  Lemma gowed_read_taint (k : nat) (v : era_pins) (n : nat)
      (I : list (bv 8)) (ws : list (list mobs * bv 8)) :
    length I = n -> 0 < length ws ->
    gwc_owed k v I -∗ RR k v n ws -∗ T.
  Proof using RR_res.
    intros HIn Hws. iIntros "Hc Hr".
    iDestruct (RR_res k v n ws Hws with "Hr") as "[#HT | Hres]"; [iExact "HT" |].
    iDestruct "Hres" as (ps0 cs0 s0 J) "(%Hlen & %Hrs & #Hinp & #Htlb & #Hps0 & #Hcs0 & #Hb0)".
    rewrite /gwc_owed.
    iDestruct "Hc" as "[Hl | [Hh | #HT]]"; last by iExact "HT".
    - iDestruct "Hl" as (ps cs s1 P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
      iDestruct (gW_bw G with "Hf") as "#Hb1".
      iDestruct (gWb_agree G k with "Hb1 Hb0") as %<-.
      iDestruct (ps_lb_cmp with "Hps Hps0") as %Hpsc.
      iDestruct (cs_lb_cmp with "Hcs Hcs0") as %Hcsc.
      iDestruct (turn_lb_le with "Htn Htlb") as %Hle.
      iDestruct (inp_lb_cmp with "HE Hinp") as %Hic.
      iExFalso. iPureIntro.
      assert (HI : I `prefix_of` J).
      { destruct Hic as [Hc | Hc]; [exact Hc |].
        exfalso. apply prefix_length in Hc. lia. }
      assert (Hne : I <> J) by (intros Hq; rewrite Hq Hlen in HIn; lia).
      exact (lm_wr_owed_read_refute M L K ps cs ps0 cs0 s1 I J P Hw HI Hne Hrs
               Hpsc Hcsc Hle).
    - iDestruct (gH_cur G with "Hh") as "(-> & Htn & #Hps & #Hcs & #HE)".
      iDestruct (turn_lb_le with "Htn Htlb") as %Hle.
      iExFalso. iPureIntro.
      assert (HI : ([] : list (bv 8)) `prefix_of` J) by apply prefix_nil.
      assert (Hne : ([] : list (bv 8)) <> J).
      { intros Hq. rewrite -Hq in Hlen. cbn [length] in Hlen. lia. }
      refine (lm_wr_owed_read_refute M L K [] [] ps0 cs0 s0 [] J 0
                (or_introl (lm_wr_pro_head M s0)) HI Hne Hrs
                ltac:(left; apply prefix_nil) ltac:(left; apply prefix_nil)
                ltac:(lia)).
  Qed.

  Lemma gban_read_taint (k : nat) (v : era_pins) (I l : list (bv 8)) :
    wl_nl ∉ l ->
    gwc_ban k v I 0 -∗ gwc_rres v (I ++ l ++ [wl_nl]) -∗ T.
  Proof using.
    intros Hnl. iIntros "Hc #Hres".
    rewrite /gwc_rres.
    iDestruct "Hres" as (ps0 cs0 s0) "(%Hrs & #Htlb & #Hps0 & #Hcs0 & #Hb0)".
    assert (Hpre : I `prefix_of` (I ++ l ++ [wl_nl])) by (by eexists).
    assert (Hne : I <> I ++ l ++ [wl_nl]).
    { intro Heq. apply (f_equal length) in Heq.
      rewrite !length_app length_cons in Heq. lia. }
    rewrite /gwc_ban.
    iDestruct "Hc" as "[Hl | [[_ Hh] | #HT]]"; last by iExact "HT".
    - iDestruct "Hl" as (ps cs s1 P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
      cbn [lm_wr_banp] in Hw.
      iDestruct (gW_bw0 G with "Hf") as "#Hb1".
      iDestruct (gWb_agree G k0 with "Hb1 Hb0") as %<-.
      iDestruct (ps_lb_cmp with "Hps Hps0") as %Hpsc.
      iDestruct (cs_lb_cmp with "Hcs Hcs0") as %Hcsc.
      rewrite Nat.add_0_r.
      iDestruct (turn_lb_le with "Htn Htlb") as %Hle.
      iExFalso. iPureIntro.
      exact (lm_wr_owed_read_refute M L K ps cs ps0 cs0 s1 I (I ++ l ++ [wl_nl]) P
               (or_introl (lm_wr_ban_pro M L ps cs s1 I P Hw)) Hpre Hne Hrs
               Hpsc Hcsc Hle).
    - iDestruct (gH_cur G with "Hh") as "(-> & Htn & #Hps & #Hcs & #HE)".
      iDestruct (turn_lb_le with "Htn Htlb") as %Hle.
      rewrite app_nil_l in Hle.
      iExFalso. iPureIntro.
      refine (lm_wr_owed_read_refute M L K [] [] ps0 cs0 s0 [] (l ++ [wl_nl]) 0
                (or_introl (lm_wr_pro_head M s0)) ltac:(apply prefix_nil) _ Hrs
                ltac:(left; apply prefix_nil) ltac:(left; apply prefix_nil)
                ltac:(lia)).
      intro Hq. apply (f_equal length) in Hq.
      rewrite length_app length_cons in Hq. cbn [length] in Hq. lia.
  Qed.
  (* ================================================================== *)
  (*  6.  THE RECORD                                                     *)
  (* ================================================================== *)

  (* the era's turn, and what it comes apart into (stage-side; a tier
     proves it of its own turn) *)
  Context (TURN : nat -> iProp Σ)
          (turn0 : forall k,
             TURN k -∗
             (∃ v : era_pins, PIN k v ∗ dl_cnt v (1/2) 0 ∗ inp_lb v [])
             ∗ (∃ v : era_pins, PIN k v ∗ gwc_ban k v [] 0)).
  (* the record's residue: the generic one, possibly with a module's extra
     persistent conjunct beside it (the file's typed-lines witness) *)
  Context (RRES : era_pins -> list (bv 8) -> iProp Σ)
          (RRES_pers : forall v I, Persistent (RRES v I))
          (RRES_tl : forall v I, Timeless (RRES v I))
          (RRES_res : forall v I, RRES v I -∗ gwc_rres v I).
  (* the silent alternative's code, which the record carries as a
     constant and nothing reads *)
  Context (NOC : nat).

  Lemma gpin_epin (k : nat) (v : era_pins) : PIN k v -∗ PIN k v.
  Proof using. by iIntros "$". Qed.

  Lemma gban_read_taint_rres (k : nat) (v : era_pins) (I l : list (bv 8)) :
    wl_nl ∉ l -> gwc_ban k v I 0 -∗ RRES v (I ++ l ++ [wl_nl]) -∗ T.
  Proof using RRES_res.
    intros Hnl. iIntros "Hc Hr". iDestruct (RRES_res with "Hr") as "#Hr'".
    iApply (gban_read_taint k v I l Hnl with "Hc Hr'").
  Qed.

  Definition gen_link_inst : LinkRec Σ :=
    {| lk_T := T;
       lk_pin := PIN;
       lk_epin := PIN;
       lk_links := LINKS;
       lk_ab := lm_ab M K;
       lk_wild := WL;
       lk_apr := lm_apr M K;
       lk_pan := fun I => lmh_pan K (lm_line_at M I);
       lk_exf := fun I => lmh_exf K (lm_line_at M I);
       lk_exfb := fun I => lmh_exfb K (lm_line_at M I);
       lk_noc := NOC;
       lk_ban := gwc_ban;
       lk_owed := gwc_owed;
       lk_sp := gwc_sp;
       lk_open := gwc_open;
       lk_blk := gwc_blk;
       lk_pro := gwc_pro;
       lk_sp_t := gwc_sp_t;
       lk_open_t := gwc_open_t;
       lk_line := gwc_line;
       lk_pr := gwc_pr;
       lk_lpr := gwc_lpr;
       lk_lend := gwc_lend;
       lk_rr := RR;
       lk_rres := RRES;
       lk_turn := TURN;

       lk_T_pers := gT_pers G;
       lk_T_tl := gT_tl G;
       lk_links_pers := LINKS_pers;
       lk_pin_pers := gPIN_pers G;
       lk_pin_tl := gPIN_tl G;
       lk_pin_agr := gPIN_agree G;
       lk_epin_pers := gPIN_pers G;
       lk_epin_tl := gPIN_tl G;
       lk_epin_agr := gPIN_agree G;
       lk_pin_epin := gpin_epin;
       lk_ban_tl := gwc_ban_timeless;
       lk_owed_tl := gwc_owed_timeless;
       lk_sp_tl := gwc_sp_timeless;
       lk_open_tl := gwc_open_timeless;
       lk_blk_tl := gwc_blk_timeless;
       lk_pro_tl := gwc_pro_timeless;
       lk_sp_t_tl := gwc_sp_t_timeless;
       lk_open_t_tl := gwc_open_t_timeless;
       lk_line_tl := gwc_line_timeless;
       lk_pr_tl := gwc_pr_timeless;
       lk_lpr_tl := gwc_lpr_timeless;
       lk_lend_tl := gwc_lend_timeless;
       lk_rres_pers := RRES_pers;
       lk_rres_tl := RRES_tl;
       lk_pr_0 := fun _ _ _ => eq_refl;
       lk_pr_1 := fun _ _ _ => eq_refl;
       lk_pr_S2 := fun _ _ _ _ => eq_refl;
       lk_lpr_0 := fun _ _ _ => eq_refl;
       lk_lpr_1 := fun _ _ _ => eq_refl;
       lk_lpr_2 := fun _ _ _ => eq_refl;
       lk_lpr_S3 := fun _ _ _ _ => eq_refl;
       lk_ban_taint := gwc_ban_taint;
       lk_owed_taint := gwc_owed_taint;
       lk_sp_taint := gwc_sp_taint;
       lk_open_taint := gwc_open_taint;
       lk_blk_taint := gwc_blk_taint;
       lk_pro_taint := gwc_pro_taint;
       lk_sp_t_taint := gwc_sp_t_taint;
       lk_open_t_taint := gwc_open_t_taint;
       lk_line_taint := gwc_line_taint;
       lk_lend_taint := gwc_lend_taint;
       lk_pro_owed := gwc_pro_owed;
       lk_blk_owed := gwc_blk_owed;
       lk_sp_t_sp := gwc_sp_t_sp;
       lk_open_t_open := gwc_open_t_open;
       lk_blk_0 := gwc_blk_0;
       lk_line_of_blk0 := gwc_line_of_blk0;
       lk_line_of_post := gwc_line_of_post;
       lk_line_of_pro := gwc_line_of_pro;
       lk_lend_of_blk0 := gwc_lend_of_blk0;
       lk_ban_step := gban_step;
       lk_ban_owed := gwc_ban_owed;
       lk_ban_pro := gwc_ban_pro;
       lk_ban_done := gwc_ban_done;
       lk_ban_done_line := gwc_ban_done_line;
       lk_ban_inp := gwc_ban_inp;
       lk_prompt_dollar := gprompt_dollar;
       lk_prompt_space := gprompt_space;
       lk_prompt_dollar_ban := gprompt_dollar_ban;
       lk_read := gwc_read;
       lk_owed_read_taint := gowed_read_taint;
       lk_blk_step := gblk_step;
       lk_blk_sp := gwc_blk_sp;
       lk_prompt_dollar_post := gprompt_dollar_post;
       lk_prompt_space_t := gprompt_space_t;
       lk_prompt_dollar_line := gprompt_dollar_line;
       lk_read_t := gwc_read_t;
       lk_ab_pan := lm_ab_pan M L K;
       lk_ab_exf := lm_ab_exf M K;
       lk_apr_exf := lm_apr_exf M K;
       lk_ban_read_taint := gban_read_taint_rres;
       lk_turn0 := turn0;
       lk_panic_done := gwc_panic_done;
       lk_pban := gwc_pban;
       lk_pdiag := gwc_pdiag;
       lk_pban_tl := gwc_pban_timeless;
       lk_pdiag_tl := gwc_pdiag_timeless;
       lk_pban_taint := gwc_pban_taint;
       lk_pdiag_taint := gwc_pdiag_taint;
       lk_pdiag_0 := gwc_pdiag_0;
       lk_pban_of_ban_done := gwc_pban_of_ban_done;
       lk_pro_of_pban := gwc_pro_of_pban;
       lk_pdiag_step := gpdiag_step;
       lk_pdiag_done_1 := gwc_pdiag_done_1;
    |}.
End gen_links_line.
