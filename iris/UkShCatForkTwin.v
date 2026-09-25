(* ===================================================================== *)
(*  UkShCatForkTwin.v -- THE [cat f] BODY AT THE WIDENED CREDENTIAL       *)
(*  (cut C9f1; design: claude-notes/design/union.md section 3,            *)
(*  'Dispatch').                                                           *)
(*                                                                        *)
(*  [UkShRedirBody.wp_kshm_body_cat] is the [cd] test's two instructions  *)
(*  in front of the fork, and its ONE fork call is now a parameter        *)
(*  ([UkShRedirBody.kshf_fork_law], [wp_kshm_body_cat_with]).  This is    *)
(*  that walk at the pipe era's fork twin                                 *)
(*  [UkShPipeForkTwin.wp_kshf_fork_pipe], whose credential need not be    *)
(*  timeless -- the union's widened credential is not.  Nothing of the   *)
(*  body is copied.                                                       *)
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
Require Import RegFile.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf.
Require Import FdSlots UserFd.
Require Import UCodeShK UCodeShP.
Require Import FileDisc.
Require Import UkSh.
Require Import UkShParse.
Require Import UkShDiag.
Require Import UkShMalloc.
Require Import UkShLoop.
Require Import UkShFork.
Require Import UkShPipeForkTwin.
Require Import UkShRedirBody.
Require Import CtxIdDefs.
Require Import UexecSG.
Require Import UserCwd.
Require Import UserChildren.
Require Import UserPerm.
Require Import UserPtTree.
Require Import Xv6Cameras.
Local Open Scope Z_scope.
Import Defs.

Section UkShCatForkTwin.
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
  Lemma kshf_fork_law_pipe : UkShRedirBody.kshf_fork_law N γp T Wc Wb Pm.
  Proof using HT Hpay Hpsok_free.
    exact (UkShPipeForkTwin.wp_kshf_fork_pipe N γp T Wc Wb Pm Hpsok_free).
  Qed.

  Lemma wp_kshm_body_cat_pipe
      (Dc : nat)
      (h : CpuId) (m : regfile) (f : nat -> bv 8) (k len : nat)
      (sz : Z) (l : list fdstate) (n : nat) :
    (Dc <= 68 + UkSh.ush_Dpipe)%nat ->
    UkSh.ush_regs m ->
    m !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (sh_buf + Z.of_nat k) ->
    m !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int (bv_unsigned (f k)) ->
    (forall j : nat, (j < len)%nat -> f (k + j)%nat <> ubyte0) ->
    f (k + len)%nat = ubyte0 ->
    (k + len < sh_nbuf)%nat ->
    UkSh.ush_line_at FileDisc.LCat_f f k len ->
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    (forall n' : nat,
       ⊢ UkSh.ush_at N γp n' -∗
         ∃ I : list (bv 8), ⌜length I = n'⌝ ∗ UkSh.ush_lease N γp T Pm I) ->
    (forall I : list (bv 8),
       ⊢ Pm I -∗ Wb I -∗ UkSh.ush_at N γp (length I)) ->
    (forall I : list (bv 8), ⊢ Wc I 3%nat -∗ Wc I 0%nat) ->
    UkSh.ush_gen_slot N T -∗
    UkShLoop.ushl_head N γp T Wc Wb Pm l sz -∗
    UCodeShK.shk_code γt -∗
    UCodeShK.shk_rodata γt -∗ UCodeShP.shp_code γt -∗ UkSh.ush_jtab γt -∗
    UkShFork.ushf_kill_law Wc -∗
    UkShFork.ushf_child_law_at Wc UkShRedirBody.ushs_lp_cat Dc -∗
    UkShDiag.ush_panic_law Wc Wb -∗
    ⌜ UkSh.ush_fd0p l ⌝ -∗
    UkSh.ush_bstate N γp T Wc Wb Pm l (FileDisc.uline_ws FileDisc.LCat_f) -∗
    UkShLoop.ushl_dat γd -∗ usz γs sz -∗
    ubytes γd sh_buf sh_nbuf f -∗
    urun N h m (mword_of_int 0x97a) (16 + (UkSh.ush_Dbody + n)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using HT Hpay Hpsok_free.
    exact (UkShRedirBody.wp_kshm_body_cat_with N γp T Wc Wb Pm kshf_fork_law_pipe
             Dc h m f k len sz l n).
  Qed.

  (* ...as the body law at the cat line *)
  Lemma ushf_body_law_cat_pipe (sz : Z) :
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    (forall I : list (bv 8), ⊢ Wc I 3%nat -∗ Wc I 0%nat) ->
    UkShFork.ushf_kill_law Wc -∗
    UkShFork.ushf_child_law_at Wc UkShRedirBody.ushs_lp_cat 68 -∗
    UkShDiag.ush_panic_law Wc Wb -∗
    UkShFork.ushf_body_law N γp T Wc Wb Pm (fun l : uline => l = LCat_f) sz.
  Proof using HT Hpay Hpsok_free.
    intros Hszlo Hszal Hszok Hwbl.
    iIntros "#Hkl #Hchl #Hplaw".
    rewrite /UkShFork.ushf_body_law.
    iIntros "!>" (lu h m f k len l n)
      "%Hd %Hlat %Hregs %Hs1 %Ha5 %Hnn %Hnul %Hkl2 %Hpm1 %Hpmwb %Hfd0
       #Hgen #Hcode #Hjt Hhead Hstd Hdat Hsz Hbuf Hrun".
    subst lu.
    iDestruct (UkSh.ush_jtab_ro γt with "Hjt") as "#Hro".
    iApply (wp_kshm_body_cat_pipe 68 h m f k len sz l n ltac:(lia)
              Hregs Hs1 Ha5 Hnn Hnul Hkl2 Hlat Hszlo Hszal Hszok
              Hpm1 Hpmwb Hwbl
              with "Hgen Hhead Hcode Hro [] Hjt Hkl Hchl Hplaw [%] Hstd
                    Hdat Hsz Hbuf Hrun").
    - iApply (UkShFork.ushf_code_shp with "Hcode").
    - exact Hfd0.
  Qed.
End UkShCatForkTwin.
