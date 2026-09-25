(* ===================================================================== *)
(* UkShRedirCmd.v -- redircmd @0x200, lane SH-PARSE                       *)
(* (design/app-file.md SS5.1, deliverable 3).                              *)
(*                                                                        *)
(*   struct cmd *redircmd(struct cmd *subcmd, char *file, char *efile,    *)
(*                        int mode, int fd) {                             *)
(*     struct redircmd *cmd;                                              *)
(*     cmd = malloc(sizeof( *cmd));                                        *)
(*     memset(cmd, 0, sizeof( *cmd));                                      *)
(*     cmd->type = REDIR;  cmd->cmd = subcmd;                             *)
(*     cmd->file = file;   cmd->efile = efile;                            *)
(*     cmd->mode = mode;   cmd->fd = fd;                                  *)
(*     return (struct cmd * )cmd;  }                                       *)
(*                                                                        *)
(* IT WAS NOT IN THE CATALOG, and that is the point.  tools/ucode_shp.txt  *)
(* listed it as [skipfunc redircmd] with the reason: reached only from     *)
(* parseredirs' switch, which runs only when the redirect peek is true --  *)
(* excluded by [ushp_no_symbols].  Lane SH-PARSE widens the line model     *)
(* ([UkShParseSym.ushs_redir] admits ONE '>'), so the switch runs and the  *)
(* constructor is fetched.  The coverage change is an edit to the SPEC     *)
(* file and a re-run of [make gen-ucode] -- never a hand edit to           *)
(* iris/UCodeShP.v (design/code-organization.md).                          *)
(*                                                                        *)
(* THE WALK IS execcmd's, ONE STRUCT WIDER.  Same three parts -- a frame,  *)
(* [malloc] through the one named Hypothesis [ushp_malloc_ok], [memset]    *)
(* across the [shp_code]/[shk_code] bridge -- and then SEVEN field stores  *)
(* instead of one.  The frame is eight words rather than four because five *)
(* arguments have to survive the two calls, and it is [gettoken]'s frame   *)
(* instruction for instruction, so [wp_kshp_frame_pro] / [_epi] drive both *)
(* ends and nothing here is hand-stepped but the body.                     *)
(*                                                                        *)
(* THE NULL ARM IS execcmd's TOO: [redircmd] does not test [malloc]'s      *)
(* answer either, so a failed allocation walks into [memset(0, 0, 40)],    *)
(* whose first store faults on sh's own read-only first text byte and      *)
(* kills the process.  That branch spends the exit payload and has no      *)
(* continuation.                                                           *)
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
Require Import UCodeShP.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Local Open Scope Z_scope.
Import Defs.
Require Import UserFd.
Require Import UkSh.
Require Import UkShParse.
Require Import UkShParseLex.

Require Import UexecSG.

Section UkShRedirCmd.
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

  Local Notation ushp_malloc_ty := (UkShParse.ushp_malloc_ty_le N 168).
  Local Notation ushp_peel0 := (UkShParse.ushp_peel0 N).
  Local Notation ushp_tree := (UkShParse.ushp_tree N).
  Local Notation ushp_type_at := (UkShParse.ushp_type_at N).
  Local Notation ushp_ubytes_ext := (UkShParse.ushp_ubytes_ext N).
  Local Notation wp_kshp_frame_epi := (UkShParse.wp_kshp_frame_epi N).
  Local Notation wp_kshp_frame_pro := (UkShParse.wp_kshp_frame_pro N).

  (* the capability is stated at [B = 168] like every other file's, even
     though the call below asks for 40: a capability good for requests up
     to 168 serves a request of 40, and the site's own [ltac:(lia)]
     discharges [40 <= 168].  One bound, no weakening lemma anywhere
     (lane SH-MALLOC-3). *)
  Context (UMalloc UMalloc' : iProp Σ).
  Hypothesis ushp_malloc_ok : ushp_malloc_ty UMalloc UMalloc'.

  (* ---- the one pure byte fact the two [sw]s need ---------------------- *)
  (* [ushp_tree]'s REDIR arm states the two [int] fields at [mword 32] --
     that is what the struct holds -- while the store writes the low four
     bytes of the 64-bit register.  For a value that fits in 31 bits the
     two agree byte for byte, and this is the one line that says so. *)
  Lemma ushp_nth_byte_32_64 (v : Z) (j : nat) :
    0 <= v < Z31 -> (j < 4)%nat ->
    nth_byte (mword_of_int v : mword 64) j
    = nth_byte (mword_of_int v : mword 32) j.
  Proof using .
    intros Hv Hj. apply bv_eq. rewrite !nth_byte_unsigned.
    rewrite (moi64_unsigned v) (moi32_unsigned v).
    rewrite /bv_wrap /bv_modulus.
    rewrite (Z.mod_small v (2 ^ Z.of_N 64) ltac:(unfold Z31 in Hv; lia)).
    rewrite (Z.mod_small v (2 ^ Z.of_N 32) ltac:(unfold Z31 in Hv; lia)).
    reflexivity.
  Qed.

  Lemma shpp_redircmd : ShSyms.redircmd = 0x200.
  Proof using . unfold ShSyms.redircmd. reflexivity. Qed.

  (* ===================================================================== *)
  (* THE REDIR NODE WITH ITS SUB-POINTER NAMED.                             *)
  (*                                                                       *)
  (* [ushp_tree]'s REDIR row hides the child pointer under an existential.  *)
  (* That is the right reading of a FINISHED tree and the wrong             *)
  (* postcondition for a CONSTRUCTOR, because [parseexec] still has to      *)
  (* store the argv terminator THROUGH the exec node it has just handed to  *)
  (* [redircmd] -- and an existential pointer cannot address a cell.  So    *)
  (* the walk's own answer names the pointer and says nothing at all about  *)
  (* what lives there; [ushp_redir_close] is the one-way door to the        *)
  (* published form, and [wp_kshp_redircmd] below is exactly that door      *)
  (* applied once.                                                          *)
  (* ===================================================================== *)
  Definition ushp_redir_node (s0 t pc : Z) (q eq : nat) (mode fd : Z)
      : iProp Σ :=
    (⌜ 0 < t ⌝ ∗ ⌜ t mod 8 = 0 ⌝ ∗ ⌜ t + 40 < Z64 ⌝ ∗
     (ubytes γd t 4 (nth_byte (mword_of_int 2 : mword 32)) ∗
      (∃ g : nat -> bv 8, ubytes γd (t + 4) 4 g)) ∗
     uword γd (t + 8) (mword_of_int pc) ∗
     uword γd (t + 16) (mword_of_int (s0 + Z.of_nat q)) ∗
     uword γd (t + 24) (mword_of_int (s0 + Z.of_nat eq)) ∗
     ubytes γd (t + 32) 4 (nth_byte (mword_of_int mode : mword 32)) ∗
     ubytes γd (t + 36) 4 (nth_byte (mword_of_int fd : mword 32)))%I.

  Lemma ushp_redir_close (s0 t pc : Z) (q eq : nat) (mode fd : Z)
      (c : ushp_cmd) :
    ushp_redir_node s0 t pc q eq mode fd -∗ ushp_tree s0 pc c -∗
    ushp_tree s0 t (UshpRedir c q eq mode fd).
  Proof using .
    iIntros "Hn Hsub". rewrite /ushp_redir_node.
    iDestruct "Hn" as "(%Ht0 & %Ht8 & %Htz & Hty & Hcmd & Hfile & Hefile & Hmode & Hfd)".
    cbn [ushp_tree ushp_ty]. rewrite /ushp_type_at.
    iSplitR; [ iPureIntro; exact Ht0 | ].
    iSplitR; [ iPureIntro; exact Ht8 | ].
    iSplitL "Hty"; [ iExact "Hty" | ].
    iSplitL "Hcmd Hsub"; [ iExists pc; iFrame "Hcmd Hsub" | ].
    iFrame "Hfile Hefile Hmode Hfd".
  Qed.

  Lemma wp_kshp_redircmd_n {Pex : iProp Σ} (h : CpuId) (m : regfile)
      (s0 sub mode fd : Z) (Sub : iProp Σ) (q eq : nat) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int sub ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat q) ->
    m !!! Regidx a2_idx = mword_of_int (s0 + Z.of_nat eq) ->
    m !!! Regidx a3_idx = mword_of_int mode ->
    m !!! Regidx a4_idx = mword_of_int fd ->
    0 <= mode < Z31 -> 0 <= fd < Z31 ->
    shp_code γt -∗
    UMalloc -∗
    □ (Pex -∗ ukn_pay N (-1)) -∗
    Pex -∗
    Sub -∗
    urun N h m (mword_of_int ShSyms.redircmd) (8 + (10 + nn)) -∗
    (∀ (h' : CpuId) (m' : regfile) (p : Z),
       ⌜ ucallee_saved m m' ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
       ⌜ 0 < p /\ p mod 16 = 0 /\ p + 40 < 2 ^ 38 ⌝ -∗
       ushp_redir_node s0 p sub q eq mode fd -∗
       Sub -∗
       UMalloc' -∗
       Pex -∗
       urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (8 + (10 + nn)) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using ushp_malloc_ok.
    intros Ha0 Ha1 Ha2 Ha3 Ha4 Hmode Hfd.
    iIntros "#Hcode HM #Hpx Hpay Hsub Hrun Hcont".
    iDestruct (ushp_code_shk γt with "Hcode") as "#Hkcode".
    rewrite shpp_redircmd.
    set (rs := [(ra_idx, mword_of_int 7 : mword 6);
                (s0_idx, mword_of_int 6 : mword 6);
                (s1_idx, mword_of_int 5 : mword 6);
                (s2_idx, mword_of_int 4 : mword 6);
                (s3_idx, mword_of_int 3 : mword 6);
                (s4_idx, mword_of_int 2 : mword 6);
                (s5_idx, mword_of_int 1 : mword 6);
                (s6_idx, mword_of_int 0 : mword 6)]).
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | 1%nat => m !!! Regidx s0_idx
                   | 2%nat => m !!! Regidx s1_idx
                   | 3%nat => m !!! Regidx s2_idx
                   | 4%nat => m !!! Regidx s3_idx
                   | 5%nat => m !!! Regidx s4_idx
                   | 6%nat => m !!! Regidx s5_idx
                   | _ => m !!! Regidx s6_idx end).
    (* ---- 0x200..0x212  the prologue: k = 8, eight spills ---- *)
    iApply (wp_kshp_frame_pro 8 0 rs 0x200
              (fun i : nat => match i with
                              | 0%nat => 0x202 | 1%nat => 0x204
                              | 2%nat => 0x206 | 3%nat => 0x208
                              | 4%nat => 0x20a | 5%nat => 0x20c
                              | 6%nat => 0x20e | 7%nat => 0x210
                              | _ => 0x212 end)
              (mword_of_int 60 : mword 6) (mword_of_int 16 : mword 8)
              vals (10 + nn) h m
              ltac:(cbn [length]; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(cbn; lia)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| [| [| i ]]]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ vm_compute; discriminate | reflexivity ] ]))
              with "[] [] [] Hrun").
    { iApply (uis_shp_200 with "Hcode"). }
    { unfold rs. rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_202 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_204 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_206 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_208 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_20a with "Hcode") | ].
      iSplit; [ iApply (uis_shp_20c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_20e with "Hcode") | ].
      iSplit; [ iApply (uis_shp_210 with "Hcode") | done ]. }
    { iApply (uis_shp_212 with "Hcode"). }
    iIntros (h1 v) "%Hal8 %Hlo %Hhi Hsl Hloc Hrun". cbn [length].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 8))).
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
    (* ---- 0x214  c.mv s2,a0 ---- *)
    iApply (wp_uk_cmv N h1 m2 (mword_of_int 0x214) s2_idx a0_idx
              (mword_of_int sub) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val sub))
              with "[] Hrun").
    { iApply (uis_shp_214 with "Hcode"). }
    rewrite (ushp_pc_step 0x214 2). iIntros (h2) "Hrun".
    set (m3 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int sub : mword 64)]> m2).
    assert (Hm3 : forall r : mword 5, Regidx r <> Regidx s2_idx ->
                    m3 !!! Regidx r = m2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m2 (Regidx s2_idx) (Regidx r) _ Hr)).
    (* ---- 0x216  c.mv s3,a1 ---- *)
    iApply (wp_uk_cmv N h2 m3 (mword_of_int 0x216) s3_idx a1_idx
              (mword_of_int (s0 + Z.of_nat q)) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate))
                      (Hm2 a1_idx ltac:(vm_compute; discriminate))
                      (Hm1 a1_idx ltac:(vm_compute; discriminate)) Ha1;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat q)))
              with "[] Hrun").
    { iApply (uis_shp_216 with "Hcode"). }
    rewrite (ushp_pc_step 0x216 2). iIntros (h3) "Hrun".
    set (m4 := <[Regidx s3_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat q) : mword 64)]> m3).
    assert (Hm4 : forall r : mword 5, Regidx r <> Regidx s3_idx ->
                    m4 !!! Regidx r = m3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m3 (Regidx s3_idx) (Regidx r) _ Hr)).
    (* ---- 0x218  c.mv s4,a2 ---- *)
    iApply (wp_uk_cmv N h3 m4 (mword_of_int 0x218) s4_idx a2_idx
              (mword_of_int (s0 + Z.of_nat eq)) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm4 a2_idx ltac:(vm_compute; discriminate))
                      (Hm3 a2_idx ltac:(vm_compute; discriminate))
                      (Hm2 a2_idx ltac:(vm_compute; discriminate))
                      (Hm1 a2_idx ltac:(vm_compute; discriminate)) Ha2;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat eq)))
              with "[] Hrun").
    { iApply (uis_shp_218 with "Hcode"). }
    rewrite (ushp_pc_step 0x218 2). iIntros (h4) "Hrun".
    set (m5 := <[Regidx s4_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat eq) : mword 64)]> m4).
    assert (Hm5 : forall r : mword 5, Regidx r <> Regidx s4_idx ->
                    m5 !!! Regidx r = m4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m4 (Regidx s4_idx) (Regidx r) _ Hr)).
    (* ---- 0x21a  c.mv s5,a3 ---- *)
    iApply (wp_uk_cmv N h4 m5 (mword_of_int 0x21a) s5_idx a3_idx
              (mword_of_int mode) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm5 a3_idx ltac:(vm_compute; discriminate))
                      (Hm4 a3_idx ltac:(vm_compute; discriminate))
                      (Hm3 a3_idx ltac:(vm_compute; discriminate))
                      (Hm2 a3_idx ltac:(vm_compute; discriminate))
                      (Hm1 a3_idx ltac:(vm_compute; discriminate)) Ha3;
                    symmetry; exact (ushp_mv_val mode))
              with "[] Hrun").
    { iApply (uis_shp_21a with "Hcode"). }
    rewrite (ushp_pc_step 0x21a 2). iIntros (h5) "Hrun".
    set (m6 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int mode : mword 64)]> m5).
    assert (Hm6 : forall r : mword 5, Regidx r <> Regidx s5_idx ->
                    m6 !!! Regidx r = m5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m5 (Regidx s5_idx) (Regidx r) _ Hr)).
    (* ---- 0x21c  c.mv s6,a4 ---- *)
    iApply (wp_uk_cmv N h5 m6 (mword_of_int 0x21c) s6_idx a4_idx
              (mword_of_int fd) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm6 a4_idx ltac:(vm_compute; discriminate))
                      (Hm5 a4_idx ltac:(vm_compute; discriminate))
                      (Hm4 a4_idx ltac:(vm_compute; discriminate))
                      (Hm3 a4_idx ltac:(vm_compute; discriminate))
                      (Hm2 a4_idx ltac:(vm_compute; discriminate))
                      (Hm1 a4_idx ltac:(vm_compute; discriminate)) Ha4;
                    symmetry; exact (ushp_mv_val fd))
              with "[] Hrun").
    { iApply (uis_shp_21c with "Hcode"). }
    rewrite (ushp_pc_step 0x21c 2). iIntros (h6) "Hrun".
    set (m7 := <[Regidx s6_idx
                 := regval_into_reg (mword_of_int fd : mword 64)]> m6).
    assert (Hm7 : forall r : mword 5, Regidx r <> Regidx s6_idx ->
                    m7 !!! Regidx r = m6 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m6 (Regidx s6_idx) (Regidx r) _ Hr)).
    (* ---- 0x21e  li a0,40 ---- *)
    assert (E40 : (sign_extend' 64 (mword_of_int 40 : mword 12) : mword 64)
                  = mword_of_int 40)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_li N h6 m7 (mword_of_int 0x21e)
              (mword_of_int 40 : mword 12) a0_idx (mword_of_int 40) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite E40; symmetry; exact (ushp_mv_val 40))
              with "[] Hrun").
    { iApply (uis_shp_21e with "Hcode"). }
    rewrite (ushp_pc_step 0x21e 4). iIntros (h7) "Hrun".
    set (m8 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 40 : mword 64)]> m7).
    assert (Hm8 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    m8 !!! Regidx r = m7 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m7 (Regidx a0_idx) (Regidx r) _ Hr)).
    (* ---- 0x222  jal 118c <malloc> ---- *)
    iApply (wp_uk_jal N h7 m8 (mword_of_int 0x222)
              (mword_of_int 3954 : mword 21) ra_idx
              (mword_of_int 0x1194) (mword_of_int 0x226) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_222 with "Hcode"). }
    iIntros (h8) "Hrun".
    set (m9 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x226 : mword 64)]> m8).
    assert (Hm9 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                    m9 !!! Regidx r = m8 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m8 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Ha0_9 : m9 !!! Regidx a0_idx = mword_of_int 40).
    { rewrite (Hm9 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m7 (Regidx a0_idx)
               (regval_into_reg (mword_of_int 40 : mword 64))). }
    assert (Eret1 : ret_pc (m9 !!! Regidx ra_idx) = mword_of_int 0x226).
    { rewrite (upd_eq m8 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x226 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    rewrite <- UkShParseLex.shpp_malloc.
    (* ---- malloc(40) -- THE HYPOTHESIS, and this lemma's only taint ---- *)
    iApply (ushp_malloc_ok h8 m9 40 nn Ha0_9 ltac:(lia) ltac:(lia)
              with "Hcode HM Hrun").
    iIntros (h9 m10) "%Hcs910 Hans Hrun".
    rewrite Eret1.
    iDestruct "Hans" as
      "[%Ha0_10 | (%p & %g & %Ha0_10 & %Hpb & Hbs & HM')]".
    { (* ---- THE NULL ARM: memset(0, 0, 40) faults and the child dies -- *)
      iApply (wp_uk_cmv N h9 m10 (mword_of_int 0x226) s1_idx a0_idx
                (mword_of_int 0) (10 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha0_10; symmetry; exact (ushp_mv_val 0))
                with "[] Hrun").
      { iApply (uis_shp_226 with "Hcode"). }
      rewrite (ushp_pc_step 0x226 2). iIntros (h10) "Hrun".
      set (n1 := <[Regidx s1_idx
                   := regval_into_reg (mword_of_int 0 : mword 64)]> m10).
      assert (Hn1 : forall r : mword 5, Regidx r <> Regidx s1_idx ->
                      n1 !!! Regidx r = m10 !!! Regidx r)
        by (intros r Hr; exact (upd_ne m10 (Regidx s1_idx) (Regidx r) _ Hr)).
      iApply (wp_uk_li N h10 n1 (mword_of_int 0x228)
                (mword_of_int 40 : mword 12) a2_idx (mword_of_int 40)
                (10 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite E40; symmetry; exact (ushp_mv_val 40))
                with "[] Hrun").
      { iApply (uis_shp_228 with "Hcode"). }
      rewrite (ushp_pc_step 0x228 4). iIntros (h11) "Hrun".
      set (n2 := <[Regidx a2_idx
                   := regval_into_reg (mword_of_int 40 : mword 64)]> n1).
      assert (Hn2 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
                      n2 !!! Regidx r = n1 !!! Regidx r)
        by (intros r Hr; exact (upd_ne n1 (Regidx a2_idx) (Regidx r) _ Hr)).
      iApply (wp_uk_cli N h11 n2 (mword_of_int 0x22c)
                (mword_of_int 0 : mword 6) a1_idx (10 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                with "[] Hrun").
      { iApply (uis_shp_22c with "Hcode"). }
      rewrite (ushp_pc_step 0x22c 2). iIntros (h12) "Hrun".
      set (n3 := <[Regidx a1_idx
                   := regval_into_reg
                        (sign_extend' 64 (mword_of_int 0 : mword 6)
                         : mword 64)]> n2).
      assert (Hn3 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                      n3 !!! Regidx r = n2 !!! Regidx r)
        by (intros r Hr; exact (upd_ne n2 (Regidx a1_idx) (Regidx r) _ Hr)).
      iApply (wp_uk_jal N h12 n3 (mword_of_int 0x22e)
                (mword_of_int 2094 : mword 21) ra_idx
                (mword_of_int 0xa5c) (mword_of_int 0x232) (10 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_22e with "Hcode"). }
      iIntros (h13) "Hrun".
      set (n4 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x232 : mword 64)]> n3).
      assert (Hn4 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                      n4 !!! Regidx r = n3 !!! Regidx r)
        by (intros r Hr; exact (upd_ne n3 (Regidx ra_idx) (Regidx r) _ Hr)).
      assert (Hna0 : n4 !!! Regidx a0_idx = mword_of_int 0).
      { rewrite (Hn4 a0_idx ltac:(vm_compute; discriminate)).
        rewrite (Hn3 a0_idx ltac:(vm_compute; discriminate)).
        rewrite (Hn2 a0_idx ltac:(vm_compute; discriminate)).
        rewrite (Hn1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_10. }
      assert (Hna2 : n4 !!! Regidx a2_idx = mword_of_int (Z.of_nat 40)).
      { rewrite (Hn4 a2_idx ltac:(vm_compute; discriminate)).
        rewrite (Hn3 a2_idx ltac:(vm_compute; discriminate)).
        rewrite (upd_eq n1 (Regidx a2_idx)
                   (regval_into_reg (mword_of_int 40 : mword 64))).
        now f_equal. }
      rewrite <- UkShParseLex.shpp_memset.
      iDestruct (ush_text0 γt with "Hkcode") as (btx) "#Ht0".
      iApply (wp_ksh_memset_null N h13 n4 0 40%nat btx (8 + nn)
                ltac:(lia) ltac:(vm_compute; reflexivity)
                Hna0 Hna2 ltac:(lia) ltac:(unfold Z31; lia)
                with "Hkcode Ht0 [Hpay] Hrun").
      iApply ("Hpx" with "Hpay"). }
    destruct Hpb as [ Hp0 [ Hp16 Hpsz ] ].
    assert (H38 : (2:Z) ^ 38 = 274877906944) by (vm_compute; reflexivity).
    assert (Hp64 : 0 <= p < Z64)
      by (rewrite H38 in Hpsz; unfold Z64; lia).
    assert (Hp8 : p mod 8 = 0).
    { apply Z.mod_divide; [ lia | ].
      apply (Z.divide_trans 8 16 p); [ exists 2; lia | ].
      apply Z.mod_divide; [ lia | exact Hp16 ]. }
    assert (Hp4 : p mod 4 = 0).
    { apply Z.mod_divide; [ lia | ].
      apply (Z.divide_trans 4 8 p); [ exists 2; lia | ].
      apply Z.mod_divide; [ lia | exact Hp8 ]. }
    assert (E40n : Z.to_nat 40 = 40%nat) by (vm_compute; reflexivity).
    rewrite E40n.
    (* ---- 0x226  c.mv s1,a0 ---- *)
    iApply (wp_uk_cmv N h9 m10 (mword_of_int 0x226) s1_idx a0_idx
              (mword_of_int p) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_10; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_226 with "Hcode"). }
    rewrite (ushp_pc_step 0x226 2). iIntros (h10) "Hrun".
    set (m11 := <[Regidx s1_idx
                  := regval_into_reg (mword_of_int p : mword 64)]> m10).
    assert (Hm11 : forall r : mword 5, Regidx r <> Regidx s1_idx ->
                     m11 !!! Regidx r = m10 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m10 (Regidx s1_idx) (Regidx r) _ Hr)).
    assert (Hs1_11 : m11 !!! Regidx s1_idx = mword_of_int p)
      by exact (upd_eq m10 (Regidx s1_idx)
                  (regval_into_reg (mword_of_int p : mword 64))).
    (* ---- 0x228  li a2,40 ---- *)
    iApply (wp_uk_li N h10 m11 (mword_of_int 0x228)
              (mword_of_int 40 : mword 12) a2_idx (mword_of_int 40) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite E40; symmetry; exact (ushp_mv_val 40))
              with "[] Hrun").
    { iApply (uis_shp_228 with "Hcode"). }
    rewrite (ushp_pc_step 0x228 4). iIntros (h11) "Hrun".
    set (m12 := <[Regidx a2_idx
                  := regval_into_reg (mword_of_int 40 : mword 64)]> m11).
    assert (Hm12 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
                     m12 !!! Regidx r = m11 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m11 (Regidx a2_idx) (Regidx r) _ Hr)).
    (* ---- 0x22c  c.li a1,0 ---- *)
    iApply (wp_uk_cli N h11 m12 (mword_of_int 0x22c)
              (mword_of_int 0 : mword 6) a1_idx (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_22c with "Hcode"). }
    rewrite (ushp_pc_step 0x22c 2). iIntros (h12) "Hrun".
    set (m13 := <[Regidx a1_idx
                  := regval_into_reg
                       (sign_extend' 64 (mword_of_int 0 : mword 6)
                        : mword 64)]> m12).
    assert (Hm13 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                     m13 !!! Regidx r = m12 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m12 (Regidx a1_idx) (Regidx r) _ Hr)).
    (* ---- 0x22e  jal a5c <memset> ---- *)
    iApply (wp_uk_jal N h12 m13 (mword_of_int 0x22e)
              (mword_of_int 2094 : mword 21) ra_idx
              (mword_of_int 0xa5c) (mword_of_int 0x232) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_22e with "Hcode"). }
    iIntros (h13) "Hrun".
    set (m14 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x232 : mword 64)]> m13).
    assert (Hm14 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                     m14 !!! Regidx r = m13 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m13 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Ha1_14 : m14 !!! Regidx a1_idx = (mword_of_int 0 : mword 64)).
    { rewrite (Hm14 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m12 (Regidx a1_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_14 : m14 !!! Regidx a0_idx = mword_of_int p).
    { rewrite (Hm14 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm13 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm12 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm11 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_10. }
    assert (Ha2_14 : m14 !!! Regidx a2_idx = mword_of_int (Z.of_nat 40)).
    { rewrite (Hm14 a2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm13 a2_idx ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m11 (Regidx a2_idx)
                 (regval_into_reg (mword_of_int 40 : mword 64))).
      now f_equal. }
    assert (Eret2 : ret_pc (m14 !!! Regidx ra_idx) = mword_of_int 0x232).
    { rewrite (upd_eq m13 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x232 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    rewrite <- UkShParseLex.shpp_memset.
    (* ---- memset(cmd, 0, 40) -- UkSh.v's, across the code bridge ---- *)
    iApply (wp_ksh_memset N h13 m14 p 40%nat g (8 + nn)
              Ha0_14 Ha2_14 ltac:(lia) ltac:(unfold Z31; lia)
              with "Hkcode Hbs Hrun").
    iIntros "Hbs" (h14 m15) "%Hcs1415 Hrun".
    rewrite Eret2 Ha1_14.
    assert (Eb0 : nth_byte (mword_of_int 0 : mword 64) 0%nat = ubyte0)
      by (vm_compute; reflexivity).
    rewrite Eb0.
    (* ---- the node's seven slices ---- *)
    iDestruct (ushp_peel0 p (p + 4) 4 36 ltac:(lia) with "Hbs")
      as "[Hty Hbs]".
    iDestruct (ushp_peel0 (p + 4) (p + 8) 4 32 ltac:(lia) with "Hbs")
      as "[Hpad Hbs]".
    iDestruct (ushp_peel0 (p + 8) (p + 16) 8 24 ltac:(lia) with "Hbs")
      as "[Hcmd Hbs]".
    iDestruct (ushp_peel0 (p + 16) (p + 24) 8 16 ltac:(lia) with "Hbs")
      as "[Hfile Hbs]".
    iDestruct (ushp_peel0 (p + 24) (p + 32) 8 8 ltac:(lia) with "Hbs")
      as "[Hefile Hbs]".
    iDestruct (ushp_peel0 (p + 32) (p + 36) 4 4 ltac:(lia) with "Hbs")
      as "[Hmode Hfd]".
    (* the three 8-byte slices as words *)
    iAssert (uword γd (p + 8) (mword_of_int 0)) with "[Hcmd]" as "Hcmd".
    { rewrite /uword /uwordq.
      iApply (ushp_ubytes_ext (p + 8) 8 (fun _ : nat => ubyte0)
                (nth_byte (mword_of_int 0 : mword 64)) with "Hcmd").
      intros j Hj. rewrite (ushp_nth_byte_zero j Hj). reflexivity. }
    iAssert (uword γd (p + 16) (mword_of_int 0)) with "[Hfile]" as "Hfile".
    { rewrite /uword /uwordq.
      iApply (ushp_ubytes_ext (p + 16) 8 (fun _ : nat => ubyte0)
                (nth_byte (mword_of_int 0 : mword 64)) with "Hfile").
      intros j Hj. rewrite (ushp_nth_byte_zero j Hj). reflexivity. }
    iAssert (uword γd (p + 24) (mword_of_int 0)) with "[Hefile]" as "Hefile".
    { rewrite /uword /uwordq.
      iApply (ushp_ubytes_ext (p + 24) 8 (fun _ : nat => ubyte0)
                (nth_byte (mword_of_int 0 : mword 64)) with "Hefile").
      intros j Hj. rewrite (ushp_nth_byte_zero j Hj). reflexivity. }
    (* ---- 0x232  c.li a5,2 ---- *)
    iApply (wp_uk_cli N h14 m15 (mword_of_int 0x232)
              (mword_of_int 2 : mword 6) a5_idx (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_232 with "Hcode"). }
    rewrite (ushp_pc_step 0x232 2). iIntros (h15) "Hrun".
    set (m16 := <[Regidx a5_idx
                  := regval_into_reg
                       (sign_extend' 64 (mword_of_int 2 : mword 6)
                        : mword 64)]> m15).
    assert (Hm16 : forall r : mword 5, Regidx r <> Regidx a5_idx ->
                     m16 !!! Regidx r = m15 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m15 (Regidx a5_idx) (Regidx r) _ Hr)).
    assert (Ha5_16 : m16 !!! Regidx a5_idx = (mword_of_int 2 : mword 64)).
    { rewrite (upd_eq m15 (Regidx a5_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 2 : mword 6) : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hs1_16 : m16 !!! Regidx s1_idx = mword_of_int p).
    { rewrite (Hm16 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hcs1415 s1_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hm14 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm13 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm12 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_11. }
    assert (Hs2_16 : m16 !!! Regidx s2_idx = mword_of_int sub).
    { rewrite (Hm16 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hcs1415 s2_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hm14 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm13 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm12 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm11 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hcs910 s2_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hm9 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 s2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s2_idx)
               (regval_into_reg (mword_of_int sub : mword 64))). }
    assert (Hs3_16 : m16 !!! Regidx s3_idx
                     = mword_of_int (s0 + Z.of_nat q)).
    { rewrite (Hm16 s3_idx ltac:(vm_compute; discriminate)).
      rewrite (Hcs1415 s3_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hm14 s3_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm13 s3_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm12 s3_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm11 s3_idx ltac:(vm_compute; discriminate)).
      rewrite (Hcs910 s3_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hm9 s3_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 s3_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s3_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 s3_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 s3_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m3 (Regidx s3_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat q) : mword 64))). }
    assert (Hs4_16 : m16 !!! Regidx s4_idx
                     = mword_of_int (s0 + Z.of_nat eq)).
    { rewrite (Hm16 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hcs1415 s4_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hm14 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm13 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm12 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm11 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hcs910 s4_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hm9 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 s4_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m4 (Regidx s4_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat eq) : mword 64))). }
    assert (Hs5_16 : m16 !!! Regidx s5_idx = mword_of_int mode).
    { rewrite (Hm16 s5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hcs1415 s5_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hm14 s5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm13 s5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm12 s5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm11 s5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hcs910 s5_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hm9 s5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 s5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s5_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m5 (Regidx s5_idx)
               (regval_into_reg (mword_of_int mode : mword 64))). }
    assert (Hs6_16 : m16 !!! Regidx s6_idx = mword_of_int fd).
    { rewrite (Hm16 s6_idx ltac:(vm_compute; discriminate)).
      rewrite (Hcs1415 s6_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hm14 s6_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm13 s6_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm12 s6_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm11 s6_idx ltac:(vm_compute; discriminate)).
      rewrite (Hcs910 s6_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hm9 s6_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 s6_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m6 (Regidx s6_idx)
               (regval_into_reg (mword_of_int fd : mword 64))). }
    (* ---- 0x234  c.sw a5,0(s1)  --  cmd->type = REDIR ---- *)
    iApply (wp_uk_csw N h15 m16 (mword_of_int 0x234)
              (mword_of_int 0 : mword 5) (mword_of_int 1 : mword 3)
              (mword_of_int 7 : mword 3) s1_idx a5_idx p
              (mword_of_int 0 : mword 64) (10 + nn)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs1_16 (uint_moi p Hp64);
                    vm_compute uoff_c4; lia)
              Hp4
              with "[] [Hty] Hrun").
    { iApply (uis_shp_234 with "Hcode"). }
    { iApply (ushp_ubytes_ext p 4 (fun _ : nat => ubyte0)
                (nth_byte (mword_of_int 0 : mword 64)) with "Hty").
      intros j Hj. rewrite (ushp_nth_byte_zero j ltac:(lia)). reflexivity. }
    iIntros "Hty". rewrite Ha5_16.
    rewrite (ushp_pc_step 0x234 2). iIntros (h16) "Hrun".
    (* ---- 0x236  sd s2,8(s1)  --  cmd->cmd = subcmd ---- *)
    iApply (wp_uk_sd N h16 m16 (mword_of_int 0x236)
              (mword_of_int 8 : mword 12) s1_idx s2_idx (p + 8)
              (mword_of_int 0) (10 + nn)
              ltac:(rewrite Hs1_16 (uint_moi p Hp64);
                    vm_compute uoff_i12; lia)
              ltac:(rewrite <- Z.add_mod_idemp_l by lia; rewrite Hp8;
                    reflexivity)
              with "[] Hcmd Hrun").
    { iApply (uis_shp_236 with "Hcode"). }
    iIntros "Hcmd". rewrite Hs2_16.
    rewrite (ushp_pc_step 0x236 4). iIntros (h17) "Hrun".
    (* ---- 0x23a  sd s3,16(s1)  --  cmd->file = file ---- *)
    iApply (wp_uk_sd N h17 m16 (mword_of_int 0x23a)
              (mword_of_int 16 : mword 12) s1_idx s3_idx (p + 16)
              (mword_of_int 0) (10 + nn)
              ltac:(rewrite Hs1_16 (uint_moi p Hp64);
                    vm_compute uoff_i12; lia)
              ltac:(rewrite <- Z.add_mod_idemp_l by lia; rewrite Hp8;
                    reflexivity)
              with "[] Hfile Hrun").
    { iApply (uis_shp_23a with "Hcode"). }
    iIntros "Hfile". rewrite Hs3_16.
    rewrite (ushp_pc_step 0x23a 4). iIntros (h18) "Hrun".
    (* ---- 0x23e  sd s4,24(s1)  --  cmd->efile = efile ---- *)
    iApply (wp_uk_sd N h18 m16 (mword_of_int 0x23e)
              (mword_of_int 24 : mword 12) s1_idx s4_idx (p + 24)
              (mword_of_int 0) (10 + nn)
              ltac:(rewrite Hs1_16 (uint_moi p Hp64);
                    vm_compute uoff_i12; lia)
              ltac:(rewrite <- Z.add_mod_idemp_l by lia; rewrite Hp8;
                    reflexivity)
              with "[] Hefile Hrun").
    { iApply (uis_shp_23e with "Hcode"). }
    iIntros "Hefile". rewrite Hs4_16.
    rewrite (ushp_pc_step 0x23e 4). iIntros (h19) "Hrun".
    (* ---- 0x242  sw s5,32(s1)  --  cmd->mode = mode ---- *)
    iApply (wp_uk_sw N h19 m16 (mword_of_int 0x242)
              (mword_of_int 32 : mword 12) s1_idx s5_idx (p + 32)
              (mword_of_int 0 : mword 64) (10 + nn)
              ltac:(rewrite Hs1_16 (uint_moi p Hp64);
                    vm_compute uoff_i12; lia)
              ltac:(rewrite <- Z.add_mod_idemp_l by lia; rewrite Hp4;
                    reflexivity)
              with "[] [Hmode] Hrun").
    { iApply (uis_shp_242 with "Hcode"). }
    { iApply (ushp_ubytes_ext (p + 32) 4 (fun _ : nat => ubyte0)
                (nth_byte (mword_of_int 0 : mword 64)) with "Hmode").
      intros j Hj. rewrite (ushp_nth_byte_zero j ltac:(lia)). reflexivity. }
    iIntros "Hmode". rewrite Hs5_16.
    rewrite (ushp_pc_step 0x242 4). iIntros (h20) "Hrun".
    (* ---- 0x246  sw s6,36(s1)  --  cmd->fd = fd ---- *)
    iApply (wp_uk_sw N h20 m16 (mword_of_int 0x246)
              (mword_of_int 36 : mword 12) s1_idx s6_idx (p + 36)
              (mword_of_int 0 : mword 64) (10 + nn)
              ltac:(rewrite Hs1_16 (uint_moi p Hp64);
                    vm_compute uoff_i12; lia)
              ltac:(rewrite <- Z.add_mod_idemp_l by lia; rewrite Hp4;
                    reflexivity)
              with "[] [Hfd] Hrun").
    { iApply (uis_shp_246 with "Hcode"). }
    { iApply (ushp_ubytes_ext (p + 36) 4 (fun _ : nat => ubyte0)
                (nth_byte (mword_of_int 0 : mword 64)) with "Hfd").
      intros j Hj. rewrite (ushp_nth_byte_zero j ltac:(lia)). reflexivity. }
    iIntros "Hfd". rewrite Hs6_16.
    rewrite (ushp_pc_step 0x246 4). iIntros (h21) "Hrun".
    (* ---- 0x24a  c.mv a0,s1 ---- *)
    iApply (wp_uk_cmv N h21 m16 (mword_of_int 0x24a) a0_idx s1_idx
              (mword_of_int p) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_16; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_24a with "Hcode"). }
    rewrite (ushp_pc_step 0x24a 2). iIntros (h22) "Hrun".
    set (me := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> m16).
    assert (Hme : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    me !!! Regidx r = m16 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m16 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (Hspe : me !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 8))).
    { rewrite (Hme csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm16 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hcs1415 csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite (Hm14 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm13 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm12 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm11 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hcs910 csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite (Hm9 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm8 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm7 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm6 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm5 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm4 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm3 csp_rs1 ltac:(vm_compute; discriminate)).
      exact Hsp2. }
    (* ---- 0x24c..0x25e  the epilogue ---- *)
    iApply (wp_kshp_frame_epi 8 0 rs (mword_of_int 7 : mword 6)
              (fun i : nat => match i with
                              | 0%nat => 0x24c | 1%nat => 0x24e
                              | 2%nat => 0x250 | 3%nat => 0x252
                              | 4%nat => 0x254 | 5%nat => 0x256
                              | 6%nat => 0x258 | 7%nat => 0x25a
                              | _ => 0x25c end)
              (mword_of_int 4 : mword 6) sp0
              (mword_of_int (uint sp0 - 8 * Z.of_nat 8)) vals
              (10 + nn) h22 me
              ltac:(cbn [length]; reflexivity)
              Hal8 ltac:(cbn; lia) Hhi
              ltac:(apply uint_moi; cbn; lia)
              Hspe
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| [| [| i ]]]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
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
      iSplit; [ iApply (uis_shp_24c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_24e with "Hcode") | ].
      iSplit; [ iApply (uis_shp_250 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_252 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_254 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_256 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_258 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_25a with "Hcode") | done ]. }
    { iApply (uis_shp_25c with "Hcode"). }
    { iApply (uis_shp_25e with "Hcode"). }
    iIntros (hf) "Hrun".
    iApply ("Hcont" $! hf _ p with "[] [] [] [Hty Hpad Hcmd Hfile Hefile Hmode Hfd] Hsub HM' Hpay Hrun").
    - iPureIntro.
      apply (ushp_frame_cs rs vals m me sp0 eq_refl).
      + intros i r u Hi.
        destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; reflexivity.
      + intros r Hr Hrsp Hmiss.
        rewrite (Hme r (ushp_cs_ne r a0_idx Hr
                          ltac:(vm_compute; reflexivity))).
        rewrite (Hm16 r (ushp_cs_ne r a5_idx Hr
                           ltac:(vm_compute; reflexivity))).
        rewrite (Hcs1415 r Hr).
        rewrite (Hm14 r (Hmiss 0%nat ra_idx (mword_of_int 7 : mword 6)
                           eq_refl)).
        rewrite (Hm13 r (ushp_cs_ne r a1_idx Hr
                           ltac:(vm_compute; reflexivity))).
        rewrite (Hm12 r (ushp_cs_ne r a2_idx Hr
                           ltac:(vm_compute; reflexivity))).
        rewrite (Hm11 r (Hmiss 2%nat s1_idx (mword_of_int 5 : mword 6)
                           eq_refl)).
        rewrite (Hcs910 r Hr).
        rewrite (Hm9 r (Hmiss 0%nat ra_idx (mword_of_int 7 : mword 6)
                          eq_refl)).
        rewrite (Hm8 r (ushp_cs_ne r a0_idx Hr
                          ltac:(vm_compute; reflexivity))).
        rewrite (Hm7 r (Hmiss 7%nat s6_idx (mword_of_int 0 : mword 6)
                          eq_refl)).
        rewrite (Hm6 r (Hmiss 6%nat s5_idx (mword_of_int 1 : mword 6)
                          eq_refl)).
        rewrite (Hm5 r (Hmiss 5%nat s4_idx (mword_of_int 2 : mword 6)
                          eq_refl)).
        rewrite (Hm4 r (Hmiss 4%nat s3_idx (mword_of_int 3 : mword 6)
                          eq_refl)).
        rewrite (Hm3 r (Hmiss 3%nat s2_idx (mword_of_int 4 : mword 6)
                          eq_refl)).
        rewrite (Hm2 r (Hmiss 1%nat s0_idx (mword_of_int 6 : mword 6)
                          eq_refl)).
        exact (Hm1 r Hrsp).
    - iPureIntro.
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      apply ushp_spillback_eq.
      + intros _.
        exact (upd_eq m16 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int p : mword 64))).
      + intros i r u Hi He.
        destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
    - iPureIntro. exact (conj Hp0 (conj Hp16 Hpsz)).
    - rewrite /ushp_redir_node.
      iSplitR; [ iPureIntro; exact Hp0 | ].
      iSplitR; [ iPureIntro; exact Hp8 | ].
      iSplitR;
        [ iPureIntro;
          assert (H38' : (2:Z) ^ 38 = 274877906944) by (vm_compute; reflexivity);
          rewrite H38' in Hpsz; unfold Z64; lia | ].
      iSplitL "Hty Hpad".
      + iSplitL "Hty".
        * iApply (ushp_ubytes_ext p 4
                    (nth_byte (mword_of_int 2 : mword 64))
                    (nth_byte (mword_of_int 2 : mword 32)) with "Hty").
          intros j Hj. destruct j as [| [| [| [| j ]]]];
            [ vm_compute; reflexivity | vm_compute; reflexivity
            | vm_compute; reflexivity | vm_compute; reflexivity | lia ].
        * iExists (fun _ : nat => ubyte0). iExact "Hpad".
      + iFrame "Hcmd Hfile Hefile".
        iSplitL "Hmode".
        * iApply (ushp_ubytes_ext (p + 32) 4
                    (nth_byte (mword_of_int mode : mword 64))
                    (nth_byte (mword_of_int mode : mword 32)) with "Hmode").
          intros j Hj. exact (ushp_nth_byte_32_64 mode j Hmode Hj).
        * iApply (ushp_ubytes_ext (p + 36) 4
                    (nth_byte (mword_of_int fd : mword 64))
                    (nth_byte (mword_of_int fd : mword 32)) with "Hfd").
          intros j Hj. exact (ushp_nth_byte_32_64 fd j Hfd Hj).
  Qed.


  (* ---- the landed statement, which is that walk at a TREE -------------- *)
  (* [wp_kshp_redircmd_n] says nothing about the sub-command, so the node it *)
  (* builds is complete only once a tree is supplied for the pointer it      *)
  (* names.  That is [ushp_redir_close], and this is the whole derivation.   *)
  Lemma wp_kshp_redircmd {Pex : iProp Σ} (h : CpuId) (m : regfile)
      (s0 sub mode fd : Z) (c : ushp_cmd) (q eq : nat) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int sub ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat q) ->
    m !!! Regidx a2_idx = mword_of_int (s0 + Z.of_nat eq) ->
    m !!! Regidx a3_idx = mword_of_int mode ->
    m !!! Regidx a4_idx = mword_of_int fd ->
    0 <= mode < Z31 -> 0 <= fd < Z31 ->
    shp_code γt -∗
    UMalloc -∗
    □ (Pex -∗ ukn_pay N (-1)) -∗
    Pex -∗
    ushp_tree s0 sub c -∗
    urun N h m (mword_of_int ShSyms.redircmd) (8 + (10 + nn)) -∗
    (∀ (h' : CpuId) (m' : regfile) (p : Z),
       ⌜ ucallee_saved m m' ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
       ⌜ 0 < p /\ p mod 16 = 0 /\ p + 40 < 2 ^ 38 ⌝ -∗
       ushp_tree s0 p (UshpRedir c q eq mode fd) -∗
       UMalloc' -∗
       Pex -∗
       urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (8 + (10 + nn)) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using ushp_malloc_ok.
    intros Ha0 Ha1 Ha2 Ha3 Ha4 Hmode Hfd.
    iIntros "#Hcode HM #Hpx Hpay Hsub Hrun Hcont".
    iApply (wp_kshp_redircmd_n h m s0 sub mode fd (ushp_tree s0 sub c) q eq nn
              Ha0 Ha1 Ha2 Ha3 Ha4 Hmode Hfd
              with "Hcode HM Hpx Hpay Hsub Hrun").
    iIntros (h' m' p) "%Hcs %Ha0' %Hp Hnode Hsub HM' Hpay Hrun".
    iApply ("Hcont" $! h' m' p with "[%//] [%//] [%//] [Hnode Hsub] HM' Hpay Hrun").
    iApply (ushp_redir_close s0 p sub q eq mode fd c with "Hnode Hsub").
  Qed.

End UkShRedirCmd.
