(* ===================================================================== *)
(*  UkShShape.v -- SHAPE MODULES: THE BODY LAW OVER A LIST OF LINE SHAPES *)
(*  (shape-modules S1; design: claude-notes/design/shape-modules.md,      *)
(*  sections 1-2).                                                         *)
(*                                                                        *)
(*  sh's fork-arm body law [UkShFork.ushf_body_law] is built per line    *)
(*  shape by one of three body walks, told apart by the line's first      *)
(*  bytes: [UkShPipeForkTwin.wp_kshm_body_pipe] (first byte 'e'),         *)
(*  [UkShPipeForkTwin.wp_kshm_body_pipe_nc] (first byte not 'c') and      *)
(*  [UkShRedirBody.wp_kshm_body_ca_with] (first bytes 'c' 'a').  A SHAPE  *)
(*  MODULE [shape_mod] is what the round needs of one line-shape family   *)
(*  and nothing else: its constructor family, the child law's line        *)
(*  predicate and room, which walk its first bytes select, and the two    *)
(*  pure facts linking them.  [ushf_body_law_of_mod] is the one wrapper   *)
(*  (the three walks behind one [match]); [ushf_body_law_mods] folds the  *)
(*  body law over a LIST of modules, so the round admits the union of     *)
(*  their families given each module's child law.                         *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import UkRun.
Require Import UserFd.
Require Import FileDisc.
Require Import UkSh.
Require Import UkShDiag.
Require Import UkShFork.
Require Import UkShPipeForkTwin.
Require Import UkShRedirBody.
Require Import CtxIdDefs.
Require Import UexecSG.
Require Import UserPerm.
Require Import UserPtTree.
Require Import Xv6Cameras.
Local Open Scope Z_scope.
Import Defs.
Require Import UkShCatForkTwin.
Local Open Scope Z_scope.
Import Defs.

(* the first-byte class: which of the three body walks a shape goes through *)
Inductive head_class := HeadE | HeadNotC | HeadCA.

Definition head_ok (c : head_class) (g : nat -> bv 8) (k len : nat) : Prop :=
  match c with
  | HeadE => bv_unsigned (g k) = 101%Z
  | HeadNotC => bv_unsigned (g k) <> 99%Z
  | HeadCA => bv_unsigned (g k) = 99%Z /\ bv_unsigned (g (k + 1)%nat) = 97%Z /\ (2 <= len)%nat
  end.

(* A SHAPE MODULE: what the round needs of one line-shape family, and nothing else *)
Record shape_mod := MkShapeMod {
  sm_D : FileDisc.uline -> Prop;                 (* the constructor family *)
  sm_Lp : list (list (bv 8)) -> (nat -> bv 8) -> nat -> nat -> Prop;   (* the child law's line predicate *)
  sm_head : head_class;
  sm_Dc : nat;
  sm_Dc_le : (sm_Dc <= 68 + UkSh.ush_Dpipe)%nat;
  sm_lp0 : forall (ws : list (list (bv 8))) (g : nat -> bv 8) (k len : nat),
      sm_Lp ws g k len -> head_ok sm_head g k len;
  sm_lp_at : forall (lu : FileDisc.uline) (f : nat -> bv 8) (k len : nat),
      sm_D lu -> UkSh.ush_line_at lu f k len ->
      sm_Lp (FileDisc.uline_ws lu) (fun j : nat => f (k + j)%nat) 0%nat len;
}.

Definition mods_D (ms : list shape_mod) (l : FileDisc.uline) : Prop :=
  exists M : shape_mod, M ∈ ms /\ sm_D M l.

Section UkShShape.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  Context `{Hpay : !ukn_const N}.
  Context `{!uartGhostG Σ}.
  Context (γp : gname).
  Context (T : iProp Σ).
  Context `{HT : !Persistent T}.
  Context (Wc : list (bv 8) -> nat -> iProp Σ).
  Context (Wb : list (bv 8) -> iProp Σ).
  Context (Pm : list (bv 8) -> iProp Σ).
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  (* the pipe era's fork twin IS the fork law *)

  Definition sm_law (M : shape_mod) : iProp Σ :=
    UkShFork.ushf_child_law_at T Wc (sm_Lp M) (sm_Dc M).

  (* NOT [apply _] on the unfolded body: the line predicate is a variable *)
  Global Instance sm_law_persistent M : Persistent (sm_law M).
  Proof using .
    rewrite /sm_law. apply UkShFork.ushf_child_law_at_persistent.
  Qed.

  Lemma ushf_body_law_mono (D D' : FileDisc.uline -> Prop) (sz : Z) :
    (forall l, D' l -> D l) ->
    UkShFork.ushf_body_law N γp T Wc Wb Pm D sz -∗
    UkShFork.ushf_body_law N γp T Wc Wb Pm D' sz.
  Proof using .
    intros HDD. rewrite /UkShFork.ushf_body_law.
    iIntros "#Hb !>" (lu h m f k len l n) "%Hd".
    iApply "Hb". iPureIntro. exact (HDD lu Hd).
  Qed.

  Lemma ushf_body_law_or (D1 D2 : FileDisc.uline -> Prop) (sz : Z) :
    UkShFork.ushf_body_law N γp T Wc Wb Pm D1 sz -∗
    UkShFork.ushf_body_law N γp T Wc Wb Pm D2 sz -∗
    UkShFork.ushf_body_law N γp T Wc Wb Pm (fun l => (D1 l \/ D2 l)%type) sz.
  Proof using .
    rewrite /UkShFork.ushf_body_law.
    iIntros "#Hb1 #Hb2 !>" (lu h m f k len l n) "%Hd".
    destruct Hd as [Hd | Hd].
    - iApply "Hb1". by iPureIntro.
    - iApply "Hb2". by iPureIntro.
  Qed.

  Lemma ushf_body_law_false (sz : Z) :
    ⊢ UkShFork.ushf_body_law N γp T Wc Wb Pm (fun _ : FileDisc.uline => False%type) sz.
  Proof using .
    rewrite /UkShFork.ushf_body_law.
    iIntros "!>" (lu h m f k len l n) "%Hd". destruct Hd.
  Qed.

  Lemma ushf_body_law_of_mod (M : shape_mod) (sz : Z) :
    8344 <= sz -> UserPtTree.pgroundup sz = sz -> usz_ok (sz + 65536) ->
    UkShFork.ushf_kill_law Wc -∗ sm_law M -∗ UkShDiag.ush_panic_law Wc Wb -∗
    UkShFork.ushf_body_law N γp T Wc Wb Pm (sm_D M) sz.
  Proof using HT Hpay Hpsok_free.
    intros Hszlo Hszal Hszok.
    iIntros "#Hkl #Hchl #Hplaw".
    rewrite /UkShFork.ushf_body_law /sm_law.
    iIntros "!>" (lu h m f k len l n)
      "%Hd %Hlat %Hregs %Hs1 %Ha5 %Hnn %Hnul %Hkl2 %Hpm1 %Hpmwb %Hfd0
       #Hgen #Hcode #Hjt Hhead Hstd Hdat Hsz Hbuf Hrun".
    pose proof (sm_lp_at M lu f k len Hd Hlat) as Hlp.
    pose proof (sm_Dc_le M) as HDc.
    iDestruct (UkSh.ush_jtab_ro γt with "Hjt") as "#Hro".
    pose proof (sm_lp0 M) as Hlp0.
    destruct M as [D Lp hc Dc HDcle lp0 lpat]; cbn [sm_D sm_Lp sm_head sm_Dc] in *.
    destruct hc; cbn [head_ok] in Hlp0.
    - iApply (UkShPipeForkTwin.wp_kshm_body_pipe N γp T Wc Wb Pm Hpsok_free
                Lp Dc h m f k len (FileDisc.uline_ws lu) sz l n
                HDc Hlp0 Hregs Hs1 Ha5 Hnn Hnul Hkl2 Hlp
                Hszlo Hszal Hszok Hpm1 Hpmwb
                with "Hgen Hhead Hcode Hro [] Hjt Hkl Hchl Hplaw [%] Hstd
                      Hdat Hsz Hbuf Hrun").
      + iApply (UkShFork.ushf_code_shp with "Hcode").
      + exact Hfd0.
    - iApply (UkShPipeForkTwin.wp_kshm_body_pipe_nc N γp T Wc Wb Pm Hpsok_free
                Lp Dc h m f k len (FileDisc.uline_ws lu) sz l n
                HDc Hlp0 Hregs Hs1 Ha5 Hnn Hnul Hkl2 Hlp
                Hszlo Hszal Hszok Hpm1 Hpmwb
                with "Hgen Hhead Hcode Hro [] Hjt Hkl Hchl Hplaw [%] Hstd
                      Hdat Hsz Hbuf Hrun").
      + iApply (UkShFork.ushf_code_shp with "Hcode").
      + exact Hfd0.
    - pose proof (Hlp0 _ _ _ _ Hlp) as (Hb0 & Hb1 & Hlen2).
      cbn beta in Hb0, Hb1. rewrite Nat.add_0_r in Hb0.
      rewrite Nat.add_0_l in Hb1.
      iApply (UkShRedirBody.wp_kshm_body_ca_with N γp T Wc Wb Pm
                (UkShCatForkTwin.kshf_fork_law_pipe N γp T Wc Wb Pm Hpsok_free)
                Lp Dc h m f k len (FileDisc.uline_ws lu) sz l n
                HDc Hregs Hs1 Ha5 Hnn Hnul Hkl2 Hlp Hb0 Hb1 Hlen2
                Hszlo Hszal Hszok Hpm1 Hpmwb
                with "Hgen Hhead Hcode Hro [] Hjt Hkl Hchl Hplaw [%] Hstd
                      Hdat Hsz Hbuf Hrun").
      + iApply (UkShFork.ushf_code_shp with "Hcode").
      + exact Hfd0.
  Qed.

  Lemma ushf_body_law_mods (ms : list shape_mod) (sz : Z) :
    8344 <= sz -> UserPtTree.pgroundup sz = sz -> usz_ok (sz + 65536) ->
    UkShFork.ushf_kill_law Wc -∗ ([∗ list] M ∈ ms, sm_law M) -∗
    UkShDiag.ush_panic_law Wc Wb -∗
    UkShFork.ushf_body_law N γp T Wc Wb Pm (mods_D ms) sz.
  Proof using HT Hpay Hpsok_free.
    intros Hszlo Hszal Hszok.
    iIntros "#Hkl Hms #Hplaw".
    iInduction ms as [ | M ms ] "IH".
    - iApply (ushf_body_law_mono (fun _ : FileDisc.uline => False%type)).
      + intros l [M [HM _]]. by apply not_elem_of_nil in HM.
      + iApply ushf_body_law_false.
    - iDestruct "Hms" as "[#HM Hms]".
      iApply (ushf_body_law_mono (fun l => (sm_D M l \/ mods_D ms l)%type)).
      + intros l [M' [HM' Hd]]. apply elem_of_cons in HM' as [-> | HM'].
        * by left.
        * right. by exists M'.
      + iApply (ushf_body_law_or with "[] [Hms]").
        * iApply (ushf_body_law_of_mod M sz Hszlo Hszal Hszok with "Hkl HM Hplaw").
        * iApply ("IH" with "Hms").
  Qed.

End UkShShape.
