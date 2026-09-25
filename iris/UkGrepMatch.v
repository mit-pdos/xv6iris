(* ===================================================================== *)
(* UkGrepMatch.v -- grep's Kernighan-Pike matcher on the separation-logic *)
(* heap: [matchhere], [matchstar], [match].                               *)
(* (design: claude-notes/design/grep.md, section 3)                        *)
(*                                                                        *)
(* RECURSION IS REAL.  matchhere calls itself at [re+1]/[text+1] (a       *)
(* [jal] followed by the epilogue, not a tail call) and calls matchstar   *)
(* at [re+2]; matchstar calls matchhere in its loop at the same [re].    *)
(* So the two contracts are proved together, by strong induction on the  *)
(* pattern's length: [mh_spec lr] from [mh_spec] below [lr] and          *)
(* [ms_spec] below [lr - 1], and [ms_spec lr] from [mh_spec lr] by        *)
(* induction on the text matchstar still has to try.                    *)
(*                                                                        *)
(* THE STACK A MATCH NEEDS IS A FUNCTION OF THE PATTERN ([mh_words]):     *)
(* matchhere's two-word frame is allocated only after its [re[0] == 0]   *)
(* test, so the empty pattern returns frameless; a [c*] prefix costs     *)
(* matchhere's frame plus matchstar's six.  Each contract takes its need *)
(* against the free-stack count and hands the stack back at that count.  *)
(*                                                                        *)
(* The strings travel as [ustr]s and each recursive call gets the SUFFIX *)
(* ([UkGrepLib.ustr_cons_split]) and hands it back; the lists the pure   *)
(* matcher reads are [map f (seq 0 len)] of the two strings.             *)
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
Require Import UserBits UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunBr.
Require Import UCodeGrep.
Require Import UkGrepLib.
Require GrepTree.
Require Import CtxIdDefs.
Require User.GrepSyms User.GrepInstrs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.

Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)
Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Set Printing Depth 40.

(* ===================================================================== *)
(* §1 THE STACK A PATTERN NEEDS (grep.md section 3).                      *)
(* ===================================================================== *)
Fixpoint mh_words (re : list (bv 8)) : nat :=
  match re with
  | [] => 0%nat
  | c :: r =>
      match r with
      | s :: r' =>
          if GrepTree.bdec s GrepTree.c_star then (2 + 6 + mh_words r')%nat
          else (2 + mh_words r)%nat
      | [] => (2 + mh_words r)%nat
      end
  end.

Definition ms_words (re : list (bv 8)) : nat := (6 + mh_words re)%nat.

Lemma mh_words_star (c s : bv 8) (r : list (bv 8)) :
  GrepTree.bdec s GrepTree.c_star = true ->
  mh_words (c :: s :: r) = (2 + 6 + mh_words r)%nat.
Proof. intros Hs. cbn [mh_words]. rewrite Hs. reflexivity. Qed.

(* a head that is not followed by a star costs its frame and the rest *)
Lemma mh_words_lit (c : bv 8) (r : list (bv 8)) :
  match r with s :: _ => GrepTree.bdec s GrepTree.c_star = false | [] => True end ->
  mh_words (c :: r) = (2 + mh_words r)%nat.
Proof. intros Hs. destruct r as [| s r']; [ reflexivity | ]. cbn [mh_words]. rewrite Hs. reflexivity. Qed.

(* ===================================================================== *)
(* §2 THE MATCHER, ONE STEP AT A TIME -- each lemma is one arm of the C.  *)
(* ===================================================================== *)

(* [ *text != '\0' && (re[0] == '.' || re[0] == *text) ] then recurse *)
Definition mh_lit (c : bv 8) (r text : list (bv 8)) : bool :=
  match text with
  | t :: ts => if GrepTree.bdec c GrepTree.c_dot || GrepTree.bdec c t
               then GrepTree.matchhere r ts else false
  | [] => false
  end.

Lemma mh_cons_lit (c s : bv 8) (r text : list (bv 8)) :
  GrepTree.bdec s GrepTree.c_star = false ->
  GrepTree.matchhere (c :: s :: r) text = mh_lit c (s :: r) text.
Proof.
  intros Hs. rewrite /mh_lit. cbn [GrepTree.matchhere]. rewrite Hs.
  destruct text; reflexivity.
Qed.

Lemma mh_one (c : bv 8) (text : list (bv 8)) :
  GrepTree.matchhere [c] text
  = if GrepTree.bdec c GrepTree.c_dollar
    then match text with [] => true | _ :: _ => false end
    else mh_lit c [] text.
Proof.
  rewrite /mh_lit. cbn [GrepTree.matchhere].
  destruct (GrepTree.bdec c GrepTree.c_dollar); destruct text; reflexivity.
Qed.

Lemma ms_cons (c : bv 8) (re : list (bv 8)) (t : bv 8) (ts : list (bv 8)) :
  GrepTree.matchstar c re (t :: ts)
  = GrepTree.matchhere re (t :: ts)
    || ((GrepTree.bdec t c || GrepTree.bdec c GrepTree.c_dot) && GrepTree.matchstar c re ts).
Proof. reflexivity. Qed.

Lemma ms_nil (c : bv 8) (re : list (bv 8)) :
  GrepTree.matchstar c re [] = GrepTree.matchhere re [].
Proof. cbn [GrepTree.matchstar]. destruct (GrepTree.matchhere re []); reflexivity. Qed.

Lemma ma_cons (re : list (bv 8)) (t : bv 8) (ts : list (bv 8)) :
  GrepTree.match_any re (t :: ts)
  = GrepTree.matchhere re (t :: ts) || GrepTree.match_any re ts.
Proof. reflexivity. Qed.

Lemma ma_nil (re : list (bv 8)) :
  GrepTree.match_any re [] = GrepTree.matchhere re [].
Proof. cbn [GrepTree.match_any]. destruct (GrepTree.matchhere re []); reflexivity. Qed.

(* the literal arm, when re[1] is not a star and not the end after a '$' *)
Lemma mh_lit_case (c : bv 8) (r text : list (bv 8)) :
  match r with
  | s :: _ => GrepTree.bdec s GrepTree.c_star = false
  | [] => GrepTree.bdec c GrepTree.c_dollar = false
  end ->
  GrepTree.matchhere (c :: r) text = mh_lit c r text.
Proof.
  intros Hr. destruct r as [| s r'].
  - rewrite mh_one Hr. reflexivity.
  - exact (mh_cons_lit c s r' text Hr).
Qed.

Lemma mh_words_ge2 (c : bv 8) (r : list (bv 8)) : (2 <= mh_words (c :: r))%nat.
Proof.
  destruct r as [| s r']; cbn [mh_words]; [ lia | ].
  destruct (GrepTree.bdec s GrepTree.c_star); lia.
Qed.

(* the four byte literals the matcher tests, as the pure spec names them *)
Lemma bdec_lit (a : bv 8) (k : Z) :
  0 <= k < 256 -> (bv_unsigned a =? k) = GrepTree.bdec a (GrepTree.ch k).
Proof. intros Hk. rewrite /GrepTree.bdec /GrepTree.ch. apply byte_eqb_lit. exact Hk. Qed.

(* ===================================================================== *)
(* §3 THE WALKS.                                                          *)
(* ===================================================================== *)
Section UkGrepMatch.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  (* the fields, under the names the engine has always used *)
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  (* NO DEPOSIT, NO [psok], NO PAYLOAD CLASS: the matcher is pure
     computation over memory the caller owns. *)

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

  (* THE TWO CONTRACTS, as propositions indexed by the pattern's length,
     for the strong induction.  [wp_kgrep_matchhere] and
     [wp_kgrep_matchstar] below are these, stated out. *)
  Definition mh_spec (lr : nat) : Prop :=
    forall (h : CpuId) (m : regfile) (dqr dqt : dfrac) (ar ax : Z) (lt : nat)
           (fr ft : nat -> bv 8) (n : nat),
      m !!! Regidx a0_idx = mword_of_int ar ->
      m !!! Regidx a1_idx = mword_of_int ax ->
      (mh_words (map fr (seq 0 lr)) <= n)%nat ->
      ⊢ grep_code γt -∗
        ustr γd dqr ar lr fr -∗
        ustr γd dqt ax lt ft -∗
        urun N h m (mword_of_int GrepSyms.matchhere) n -∗
        (ustr γd dqr ar lr fr -∗
         ustr γd dqt ax lt ft -∗
           ∀ (h' : CpuId) (m' : regfile),
             ⌜ ucallee_saved m m' ⌝ -∗
             ⌜ m' !!! Regidx a0_idx
               = mword_of_int (if GrepTree.matchhere (map fr (seq 0 lr)) (map ft (seq 0 lt))
                               then 1 else 0) ⌝ -∗
             urun N h' m' (ret_pc (m !!! Regidx ra_idx)) n -∗
             mWP (Loop : expr riscv_lang)) -∗
        mWP (Loop : expr riscv_lang).

  Definition ms_spec (lr : nat) : Prop :=
    forall (h : CpuId) (m : regfile) (c : bv 8) (dqr dqt : dfrac) (ar ax : Z) (lt : nat)
           (fr ft : nat -> bv 8) (n : nat),
      m !!! Regidx a0_idx = mword_of_int (bv_unsigned c) ->
      m !!! Regidx a1_idx = mword_of_int ar ->
      m !!! Regidx a2_idx = mword_of_int ax ->
      (ms_words (map fr (seq 0 lr)) <= n)%nat ->
      ⊢ grep_code γt -∗
        ustr γd dqr ar lr fr -∗
        ustr γd dqt ax lt ft -∗
        urun N h m (mword_of_int GrepSyms.matchstar) n -∗
        (ustr γd dqr ar lr fr -∗
         ustr γd dqt ax lt ft -∗
           ∀ (h' : CpuId) (m' : regfile),
             ⌜ ucallee_saved m m' ⌝ -∗
             ⌜ m' !!! Regidx a0_idx
               = mword_of_int (if GrepTree.matchstar c (map fr (seq 0 lr)) (map ft (seq 0 lt))
                               then 1 else 0) ⌝ -∗
             urun N h' m' (ret_pc (m !!! Regidx ra_idx)) n -∗
             mWP (Loop : expr riscv_lang)) -∗
        mWP (Loop : expr riscv_lang).

  (* a register the program never names is not callee-saved-clobbered by
     a call: what [rkeep_call] needs of the write set *)
  Local Lemma rin_caller (S : list Z) :
    forall r : mword 5, ucallee_saved_idx r = false -> rin (S ++ Wcaller) r = true.
  Proof using . intros r Hr. exact (rin_app_caller S r Hr). Qed.

  (* ------------------------------------------------------------------- *)
  (* ...and its RECURSIVE CALL, 0xa2..0xac, reached from both tests:      *)
  (*   c.addi a1,a1,1 ; addi a0,a5,1 ; jal matchhere ; c.j 0x82          *)
  (* ------------------------------------------------------------------- *)
  Local Lemma wp_kgrep_mh_call (lr1 : nat) :
    mh_spec lr1 ->
    forall (h : CpuId) (mx : regfile) (dqr dqt : dfrac) (ar ax : Z) (lt1 : nat)
           (c : bv 8) (fr1 ft : nat -> bv 8) (n : nat),
    GrepTree.bdec c GrepTree.c_dot || GrepTree.bdec c (ft 0%nat) = true ->
    mx !!! Regidx a5_idx = mword_of_int ar ->
    mx !!! Regidx a1_idx = mword_of_int ax ->
    (mh_words (map fr1 (seq 0 lr1)) <= n)%nat ->
    grep_code γt -∗
    ustr γd dqr (ar + 1) lr1 fr1 -∗
    ustr γd dqt ax (S lt1) ft -∗
    urun N h mx (mword_of_int 0xa2) n -∗
    (ustr γd dqr (ar + 1) lr1 fr1 -∗
     ustr γd dqt ax (S lt1) ft -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ m' !!! Regidx a0_idx
           = mword_of_int (if mh_lit c (map fr1 (seq 0 lr1)) (map ft (seq 0 (S lt1)))
                           then 1 else 0) ⌝ -∗
         ⌜ rkeep Wcaller mx m' ⌝ -∗
         urun N h' m' (mword_of_int 0x82) n -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros IH h' mx dqr dqt ar ax lt1 c fr1 ft n Htest Ha5x Ha1x Hn.
    iIntros "#Hcode Hre Htx Hrun Hcont".

    (* ---- 0xa2  c.addi a1,a1,1 ---- *)
    iApply (wp_uk_caddi N h' mx (mword_of_int 0xa2)
              (mword_of_int 1 : mword 6) a1_idx (mword_of_int (ax + 1)) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha1x;
                    replace (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                      with (mword_of_int 1 : mword 64)
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite moi_add; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_a2 with "Hcode"). }
    iIntros (h5) "Hrun". pcn.
    set (mx1 := <[Regidx a1_idx := regval_into_reg (mword_of_int (ax + 1) : mword 64)]> mx).
    (* ---- 0xa4  addi a0,a5,1 ---- *)
    iApply (wp_uk_addi N h5 mx1 (mword_of_int 0xa4)
              (mword_of_int 1 : mword 12) a5_idx a0_idx (mword_of_int (ar + 1)) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /mx1; rgl; rewrite Ha5x;
                    replace (sign_extend' 64 (mword_of_int 1 : mword 12) : mword 64)
                      with (mword_of_int 1 : mword 64)
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite moi_add; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_a4 with "Hcode"). }
    iIntros (h6) "Hrun". pcn.
    set (mx2 := <[Regidx a0_idx := regval_into_reg (mword_of_int (ar + 1) : mword 64)]> mx1).
    (* ---- 0xa8  jal matchhere ---- *)
    iApply (wp_uk_jal N h6 mx2 (mword_of_int 0xa8)
              (mword_of_int 2097060 : mword 21) ra_idx
              (mword_of_int GrepSyms.matchhere) (mword_of_int 0xac) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /GrepSyms.matchhere; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite /GrepSyms.matchhere; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_a8 with "Hcode"). }
    iIntros (h7) "Hrun".
    set (mx3 := <[Regidx ra_idx := regval_into_reg (mword_of_int 0xac : mword 64)]> mx2).
    iDestruct (ustr_nonul with "Htx") as %Htne'.
    iDestruct (ustr_len with "Htx") as %Htlen'.
    iDestruct (ustr_cons_split with "Htx") as "[Ht0 Htx]".
    iApply (IH h7 mx3 dqr dqt (ar + 1) (ax + 1) lt1 fr1 (fun j => ft (S j)) n
              ltac:(rewrite /mx3 /mx2; rgl; reflexivity)
              ltac:(rewrite /mx3 /mx2 /mx1; rgl; reflexivity)
              Hn
              with "Hcode Hre Htx Hrun").
    iIntros "Hre Htx" (h8 mx4) "%Hcs4 %Ha04 Hrun".
    assert (Eret : ret_pc (mx3 !!! Regidx ra_idx) = (mword_of_int 0xac : mword 64))
      by (rewrite /mx3; rgl; apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    (* ---- 0xac  c.j 0x82 ---- *)
    iApply (wp_uk_cj N h8 mx4 (mword_of_int 0xac)
              (mword_of_int 2027 : mword 11) (mword_of_int 0x82) n
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_ac with "Hcode"). }
    iIntros (h9) "Hrun".
    iDestruct (ustr_cons_join with "Ht0 Htx") as "Htx";
      [ exact (Htne' 0%nat ltac:(lia)) | exact Htlen' | ].
    iApply ("Hcont" with "Hre Htx [] [] Hrun").
    - iPureIntro. rewrite Ha04. rewrite /mh_lit. rewrite map_seq_S. rewrite Htest. reflexivity.
    - iPureIntro. eapply (rkeep_call Wcaller mx mx3 mx4 (rin_caller [])); [ | exact Hcs4 ].
      rewrite /mx3 /mx2 /mx1. rk.
Qed.

  (* ------------------------------------------------------------------- *)
  (* matchhere's LITERAL ARM, 0x70..0xac:                                *)
  (*   lbu a3,0(a1) ; c.li a0,0 ; c.beqz a3,0x82 ; beq a4,a3,0xa2 ;      *)
  (*   addi a4,a4,-46 ; c.beqz a4,0xa2 ; (0x82)                          *)
  (*   0xa2: c.addi a1,a1,1 ; addi a0,a5,1 ; jal matchhere ; c.j 0x82    *)
  (* a4 holds [re[0]] and a5 [re]; the pattern's first byte stays with   *)
  (* the caller, which hands over only the suffix the recursive call     *)
  (* reads.  Leaves at 0x82 (matchhere's epilogue) with the arm's answer.*)
  (* ------------------------------------------------------------------- *)
  Local Lemma wp_kgrep_mh_lit (lr1 : nat) :
    mh_spec lr1 ->
    forall (h : CpuId) (m : regfile) (dqr dqt : dfrac) (ar ax : Z) (lt : nat)
           (c : bv 8) (fr1 ft : nat -> bv 8) (n : nat),
    m !!! Regidx a4_idx = mword_of_int (bv_unsigned c) ->
    m !!! Regidx a5_idx = mword_of_int ar ->
    m !!! Regidx a1_idx = mword_of_int ax ->
    (mh_words (map fr1 (seq 0 lr1)) <= n)%nat ->
    grep_code γt -∗
    ustr γd dqr (ar + 1) lr1 fr1 -∗
    ustr γd dqt ax lt ft -∗
    urun N h m (mword_of_int 0x70) n -∗
    (ustr γd dqr (ar + 1) lr1 fr1 -∗
     ustr γd dqt ax lt ft -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ m' !!! Regidx a0_idx
           = mword_of_int (if mh_lit c (map fr1 (seq 0 lr1)) (map ft (seq 0 lt)) then 1 else 0) ⌝ -∗
         ⌜ rkeep Wcaller m m' ⌝ -∗
         urun N h' m' (mword_of_int 0x82) n -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros IH h m dqr dqt ar ax lt c fr1 ft n Ha4 Ha5 Ha1 Hn.
    iIntros "#Hcode Hre Htx Hrun Hcont".
    iDestruct (urun_ustr_bnd with "Hrun Htx") as %[Hax0 Hax38].
    change (2 ^ 38) with 274877906944 in Hax38.
    iDestruct (ustr_nonul with "Htx") as %Htne.
    iDestruct (ustr_len with "Htx") as %Htlen.
    assert (Hux : uint (mword_of_int ax : mword 64) = ax) by (apply uint_moi; unfold Z64; lia).
    assert (Eoff0 : uoff_i12 (mword_of_int 0 : mword 12) = 0) by (vm_compute; reflexivity).
    (* ---- 0x70  lbu a3,0(a1) -- the text's first byte ---- *)
    iDestruct (ustr_hd_acc with "Htx") as "[Hb Hcl]".
    iApply (wp_uk_lbu N h m (mword_of_int 0x70)
              (mword_of_int 0 : mword 12) a1_idx a3_idx dqt ax (ustr_hd lt ft) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Ha1 Hux Eoff0; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_grep_70 with "Hcode"). }
    iIntros "Hb" (h1) "Hrun". pcn.
    iDestruct ("Hcl" with "Hb") as "Htx".
    set (m1 := <[Regidx a3_idx := regval_into_reg (zero_extend' 64 (ustr_hd lt ft : mword 8) : mword 64)]> m).
    (* ---- 0x74  c.li a0,0 ---- *)
    iApply (wp_uk_cli N h1 m1 (mword_of_int 0x74)
              (mword_of_int 0 : mword 6) a0_idx n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_grep_74 with "Hcode"). }
    iIntros (h2) "Hrun". pcn.
    set (m2 := <[Regidx a0_idx := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64)]> m1).
    assert (Ha32 : m2 !!! Regidx a3_idx = mword_of_int (bv_unsigned (ustr_hd lt ft)))
      by (rewrite /m2 /m1; rgl; apply zext8_byte).
    assert (Hk2 : rkeep Wcaller m m2) by (rewrite /m2 /m1; rk).
    assert (Ha02 : m2 !!! Regidx a0_idx = mword_of_int 0)
      by (rewrite /m2; rgl; apply bv_eq; vm_compute; reflexivity).
    (* ---- 0x76  c.beqz a3,0x82 -- the empty text ---- *)
    iApply (wp_uk_cbeqz N h2 m2 (mword_of_int 0x76)
              (mword_of_int 6 : mword 8) (mword_of_int 5 : mword 3) a3_idx
              (bool_decide (ustr_hd lt ft = ubyte0)) (mword_of_int 0x82) n
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha32 moi_byte_eqz; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_76 with "Hcode"). }
    iIntros (h3) "Hrun".
    destruct lt as [| lt1].
    { (* no text: the arm answers 0 *)
      rewrite (bool_decide_eq_true_2 _ (eq_refl : ustr_hd 0 ft = ubyte0)).
      iApply ("Hcont" with "Hre Htx [] [] Hrun").
      - iPureIntro. rewrite Ha02. reflexivity.
      - iPureIntro. exact Hk2. }
    assert (Hft0 : ft 0%nat <> ubyte0) by (apply Htne; lia).
    rewrite (bool_decide_eq_false_2 _ Hft0). pcn.
    (* ---- 0x78  beq a4,a3,0xa2 -- re[0] == *text ---- *)
    assert (Hbeq : uv_btaken BEQ (m2 !!! Regidx a4_idx) (m2 !!! Regidx a3_idx)
                   = GrepTree.bdec c (ft 0%nat)).
    { cbn [uv_btaken]. rewrite Ha32. rewrite /m2 /m1. rgl. rewrite Ha4.
      exact (moi_byte_eq c (ft 0%nat)). }
    iApply (wp_uk_btype N h3 m2 (mword_of_int 0x78)
              (mword_of_int 42 : mword 13) a3_idx a4_idx BEQ (GrepTree.bdec c (ft 0%nat))
              (mword_of_int 0xa2) n
              ltac:(rewrite Hbeq; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_78 with "Hcode"). }
    iIntros (h4) "Hrun".
    destruct (GrepTree.bdec c (ft 0%nat)) eqn:Ect.
    { (* re[0] == *text *)
      iApply (wp_kgrep_mh_call lr1 IH h4 m2 dqr dqt ar ax lt1 c fr1 ft n
                ltac:(rewrite Ect orb_true_r; reflexivity)
                ltac:(rewrite /m2 /m1; rgl; exact Ha5)
                ltac:(rewrite /m2 /m1; rgl; exact Ha1)
                Hn with "Hcode Hre Htx Hrun").
      iIntros "Hre Htx" (h' m') "%Ha0' %Hk' Hrun".
      iApply ("Hcont" with "Hre Htx [] [] Hrun").
      - iPureIntro. exact Ha0'.
      - iPureIntro. exact (rkeep_trans _ _ _ _ Hk2 Hk'). }
    pcn.
    (* ---- 0x7c  addi a4,a4,-46 ---- *)
    pose proof (byte_range c) as Hcr.
    iApply (wp_uk_addi N h4 m2 (mword_of_int 0x7c)
              (mword_of_int 4050 : mword 12) a4_idx a4_idx
              (mword_of_int (bv_unsigned c - 46)) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m2 /m1; rgl; rewrite Ha4;
                    replace (sign_extend' 64 (mword_of_int 4050 : mword 12) : mword 64)
                      with (mword_of_int (-46) : mword 64)
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite moi_add; f_equal; lia)
              with "[] Hrun").
    { iApply (uis_grep_7c with "Hcode"). }
    iIntros (h5) "Hrun". pcn.
    set (m3 := <[Regidx a4_idx := regval_into_reg (mword_of_int (bv_unsigned c - 46) : mword 64)]> m2).
    (* ---- 0x80  c.beqz a4,0xa2 -- re[0] == '.' ---- *)
    iApply (wp_uk_cbeqz N h5 m3 (mword_of_int 0x80)
              (mword_of_int 17 : mword 8) (mword_of_int 6 : mword 3) a4_idx
              (GrepTree.bdec c GrepTree.c_dot) (mword_of_int 0xa2) n
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite /m3; rgl; rewrite (moi_sub_eqz (bv_unsigned c) 46 Hcr ltac:(lia));
                    symmetry; apply bdec_lit; lia)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_80 with "Hcode"). }
    iIntros (h6) "Hrun".
    destruct (GrepTree.bdec c GrepTree.c_dot) eqn:Ecd.
    { (* re[0] == '.' *)
      iApply (wp_kgrep_mh_call lr1 IH h6 m3 dqr dqt ar ax lt1 c fr1 ft n
                ltac:(rewrite Ecd; reflexivity)
                ltac:(rewrite /m3 /m2 /m1; rgl; exact Ha5)
                ltac:(rewrite /m3 /m2 /m1; rgl; exact Ha1)
                Hn with "Hcode Hre Htx Hrun").
      iIntros "Hre Htx" (h' m') "%Ha0' %Hk' Hrun".
      iApply ("Hcont" with "Hre Htx [] [] Hrun").
      - iPureIntro. exact Ha0'.
      - iPureIntro. assert (Hk3 : rkeep Wcaller m m3) by (rewrite /m3; rk).
        exact (rkeep_trans _ _ _ _ Hk3 Hk'). }
    (* neither: 0 *)
    pcn.
    iApply ("Hcont" with "Hre Htx [] [] Hrun").
    - iPureIntro.
      assert (Ha03 : m3 !!! Regidx a0_idx = mword_of_int 0)
        by (rewrite /m3; exact (eq_trans (upd_ne m2 (Regidx a4_idx) (Regidx a0_idx) _
                                            ltac:(vm_compute; discriminate)) Ha02)).
      rewrite Ha03 /mh_lit map_seq_S Ect Ecd. reflexivity.
    - iPureIntro. rewrite /m3. rk.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* matchhere's STAR ARM, 0x8a..0x96:                                   *)
  (*   c.mv a2,a1 ; addi a1,a0,2 ; c.mv a0,a4 ; jal matchstar ; c.j 0x82 *)
  (* re[1] is the star; matchstar gets re[0] (in a4), [re+2] and text.   *)
  (* ------------------------------------------------------------------- *)
  Local Lemma wp_kgrep_mh_star (lr2 : nat) :
    ms_spec lr2 ->
    forall (h : CpuId) (m : regfile) (dqr dqt : dfrac) (ar ax : Z) (lt : nat)
           (c : bv 8) (fr2 ft : nat -> bv 8) (n : nat),
    m !!! Regidx a4_idx = mword_of_int (bv_unsigned c) ->
    m !!! Regidx a0_idx = mword_of_int ar ->
    m !!! Regidx a1_idx = mword_of_int ax ->
    (ms_words (map fr2 (seq 0 lr2)) <= n)%nat ->
    grep_code γt -∗
    ustr γd dqr (ar + 1 + 1) lr2 fr2 -∗
    ustr γd dqt ax lt ft -∗
    urun N h m (mword_of_int 0x8a) n -∗
    (ustr γd dqr (ar + 1 + 1) lr2 fr2 -∗
     ustr γd dqt ax lt ft -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ m' !!! Regidx a0_idx
           = mword_of_int (if GrepTree.matchstar c (map fr2 (seq 0 lr2)) (map ft (seq 0 lt))
                           then 1 else 0) ⌝ -∗
         ⌜ rkeep Wcaller m m' ⌝ -∗
         urun N h' m' (mword_of_int 0x82) n -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros IH h m dqr dqt ar ax lt c fr2 ft n Ha4 Ha0 Ha1 Hn.
    iIntros "#Hcode Hre Htx Hrun Hcont".
    (* ---- 0x8a  c.mv a2,a1 ---- *)
    iApply (wp_uk_cmv N h m (mword_of_int 0x8a) a2_idx a1_idx (mword_of_int ax) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha1 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_8a with "Hcode"). }
    iIntros (h1) "Hrun". pcn.
    set (m1 := <[Regidx a2_idx := regval_into_reg (mword_of_int ax : mword 64)]> m).
    (* ---- 0x8c  addi a1,a0,2 ---- *)
    iApply (wp_uk_addi N h1 m1 (mword_of_int 0x8c)
              (mword_of_int 2 : mword 12) a0_idx a1_idx (mword_of_int (ar + 1 + 1)) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m1; rgl; rewrite Ha0;
                    replace (sign_extend' 64 (mword_of_int 2 : mword 12) : mword 64)
                      with (mword_of_int 2 : mword 64)
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite moi_add; f_equal; lia)
              with "[] Hrun").
    { iApply (uis_grep_8c with "Hcode"). }
    iIntros (h2) "Hrun". pcn.
    set (m2 := <[Regidx a1_idx := regval_into_reg (mword_of_int (ar + 1 + 1) : mword 64)]> m1).
    (* ---- 0x90  c.mv a0,a4 ---- *)
    iApply (wp_uk_cmv N h2 m2 (mword_of_int 0x90) a0_idx a4_idx
              (mword_of_int (bv_unsigned c)) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m2 /m1; rgl; rewrite Ha4 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_90 with "Hcode"). }
    iIntros (h3) "Hrun". pcn.
    set (m3 := <[Regidx a0_idx := regval_into_reg (mword_of_int (bv_unsigned c) : mword 64)]> m2).
    (* ---- 0x92  jal matchstar ---- *)
    iApply (wp_uk_jal N h3 m3 (mword_of_int 0x92)
              (mword_of_int 2097006 : mword 21) ra_idx
              (mword_of_int GrepSyms.matchstar) (mword_of_int 0x96) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /GrepSyms.matchstar; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite /GrepSyms.matchstar; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_92 with "Hcode"). }
    iIntros (h4) "Hrun".
    set (m4 := <[Regidx ra_idx := regval_into_reg (mword_of_int 0x96 : mword 64)]> m3).
    iApply (IH h4 m4 c dqr dqt (ar + 1 + 1) ax lt fr2 ft n
              ltac:(rewrite /m4 /m3; rgl; reflexivity)
              ltac:(rewrite /m4 /m3 /m2; rgl; reflexivity)
              ltac:(rewrite /m4 /m3 /m2 /m1; rgl; reflexivity)
              Hn
              with "Hcode Hre Htx Hrun").
    iIntros "Hre Htx" (h5 m5) "%Hcs5 %Ha05 Hrun".
    assert (Eret : ret_pc (m4 !!! Regidx ra_idx) = (mword_of_int 0x96 : mword 64))
      by (rewrite /m4; rgl; apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    (* ---- 0x96  c.j 0x82 ---- *)
    iApply (wp_uk_cj N h5 m5 (mword_of_int 0x96)
              (mword_of_int 2038 : mword 11) (mword_of_int 0x82) n
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_96 with "Hcode"). }
    iIntros (h6) "Hrun".
    iApply ("Hcont" with "Hre Htx [] [] Hrun").
    - iPureIntro. exact Ha05.
    - iPureIntro. eapply (rkeep_call Wcaller m m4 m5 (rin_caller [])); [ | exact Hcs5 ].
      rewrite /m4 /m3 /m2 /m1. rk.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* matchstar's LOOP, 0x1e..0x3a:                                       *)
  (*   c.mv a1,s1 ; c.mv a0,s3 ; jal matchhere ; c.bnez a0,0x3a ;        *)
  (*   lbu a5,0(s1) ; c.beqz a5,0x3c ; c.addi s1,s1,1 ;                  *)
  (*   beq a5,s2,0x1e ; bnez s4,0x1e ; c.j 0x3c    (0x3a: c.li a0,1)     *)
  (* s1 is the text still to try, s2 the character [c], s3 the pattern,  *)
  (* s4 the [c == '.'] flag.  By induction on the text left.            *)
  (* ------------------------------------------------------------------- *)
  Local Lemma wp_kgrep_ms_loop (lr : nat) :
    mh_spec lr ->
    forall (lt : nat) (h : CpuId) (mc : regfile) (c : bv 8) (dqr dqt : dfrac)
           (ar ax : Z) (fr ft : nat -> bv 8) (n : nat),
    mc !!! Regidx s1_idx = mword_of_int ax ->
    mc !!! Regidx s2_idx = mword_of_int (bv_unsigned c) ->
    mc !!! Regidx s3_idx = mword_of_int ar ->
    mc !!! Regidx s4_idx = mword_of_int (if bv_unsigned c =? 46 then 1 else 0) ->
    (mh_words (map fr (seq 0 lr)) <= n)%nat ->
    grep_code γt -∗
    ustr γd dqr ar lr fr -∗
    ustr γd dqt ax lt ft -∗
    urun N h mc (mword_of_int 0x1e) n -∗
    (ustr γd dqr ar lr fr -∗
     ustr γd dqt ax lt ft -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ mc' !!! Regidx a0_idx
           = mword_of_int (if GrepTree.matchstar c (map fr (seq 0 lr)) (map ft (seq 0 lt))
                           then 1 else 0) ⌝ -∗
         ⌜ rkeep (9 :: Wcaller) mc mc' ⌝ -∗
         urun N h' mc' (mword_of_int 0x3c) n -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros IH lt. induction lt as [lt IHt] using lt_wf_ind.
    intros h mc c dqr dqt ar ax fr ft n Hs1 Hs2 Hs3 Hs4 Hn.
    iIntros "#Hcode Hre Htx Hrun Hcont".
    iDestruct (urun_ustr_bnd with "Hrun Htx") as %[Hax0 Hax38].
    change (2 ^ 38) with 274877906944 in Hax38.
    iDestruct (ustr_nonul with "Htx") as %Htne.
    iDestruct (ustr_len with "Htx") as %Htlen.
    (* ---- 0x1e  c.mv a1,s1 ---- *)
    iApply (wp_uk_cmv N h mc (mword_of_int 0x1e) a1_idx s1_idx (mword_of_int ax) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_1e with "Hcode"). }
    iIntros (h1) "Hrun". pcn.
    set (m1 := <[Regidx a1_idx := regval_into_reg (mword_of_int ax : mword 64)]> mc).
    (* ---- 0x20  c.mv a0,s3 ---- *)
    iApply (wp_uk_cmv N h1 m1 (mword_of_int 0x20) a0_idx s3_idx (mword_of_int ar) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m1; rgl; rewrite Hs3 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_20 with "Hcode"). }
    iIntros (h2) "Hrun". pcn.
    set (m2 := <[Regidx a0_idx := regval_into_reg (mword_of_int ar : mword 64)]> m1).
    (* ---- 0x22  jal matchhere ---- *)
    iApply (wp_uk_jal N h2 m2 (mword_of_int 0x22)
              (mword_of_int 42 : mword 21) ra_idx
              (mword_of_int GrepSyms.matchhere) (mword_of_int 0x26) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /GrepSyms.matchhere; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite /GrepSyms.matchhere; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_22 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx ra_idx := regval_into_reg (mword_of_int 0x26 : mword 64)]> m2).
    iApply (IH h3 m3 dqr dqt ar ax lt fr ft n
              ltac:(rewrite /m3 /m2; rgl; reflexivity)
              ltac:(rewrite /m3 /m2 /m1; rgl; reflexivity)
              Hn
              with "Hcode Hre Htx Hrun").
    iIntros "Hre Htx" (h4 m4) "%Hcs4 %Ha04 Hrun".
    assert (Eret : ret_pc (m3 !!! Regidx ra_idx) = (mword_of_int 0x26 : mword 64))
      by (rewrite /m3; rgl; apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    assert (Hk4 : rkeep (9 :: Wcaller) mc m4).
    { eapply (rkeep_call (9 :: Wcaller) mc m3 m4 (rin_caller [9])); [ | exact Hcs4 ].
      rewrite /m3 /m2 /m1. rk. }
    (* the callee-saved registers the loop runs on survive the call *)
    assert (Hs14 : m4 !!! Regidx s1_idx = mword_of_int ax)
      by (rewrite (Hcs4 s1_idx ltac:(vm_compute; reflexivity)) /m3 /m2 /m1; rgl; exact Hs1).
    assert (Hs24 : m4 !!! Regidx s2_idx = mword_of_int (bv_unsigned c))
      by (rewrite (Hcs4 s2_idx ltac:(vm_compute; reflexivity)) /m3 /m2 /m1; rgl; exact Hs2).
    assert (Hs34 : m4 !!! Regidx s3_idx = mword_of_int ar)
      by (rewrite (Hcs4 s3_idx ltac:(vm_compute; reflexivity)) /m3 /m2 /m1; rgl; exact Hs3).
    assert (Hs44 : m4 !!! Regidx s4_idx = mword_of_int (if bv_unsigned c =? 46 then 1 else 0))
      by (rewrite (Hcs4 s4_idx ltac:(vm_compute; reflexivity)) /m3 /m2 /m1; rgl; exact Hs4).
    (* ---- 0x26  c.bnez a0,0x3a ---- *)
    iApply (wp_uk_cbnez N h4 m4 (mword_of_int 0x26)
              (mword_of_int 10 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              (GrepTree.matchhere (map fr (seq 0 lr)) (map ft (seq 0 lt))) (mword_of_int 0x3a) n
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha04 moi_b01_neqz; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_26 with "Hcode"). }
    iIntros (h5) "Hrun".
    destruct (GrepTree.matchhere (map fr (seq 0 lr)) (map ft (seq 0 lt))) eqn:Ebh.
    { (* matchhere(re, text) held: 1 *)
      (* ---- 0x3a  c.li a0,1 ---- *)
      iApply (wp_uk_cli N h5 m4 (mword_of_int 0x3a)
                (mword_of_int 1 : mword 6) a0_idx n
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) with "[] Hrun").
      { iApply (uis_grep_3a with "Hcode"). }
      iIntros (h6) "Hrun". pcn.
      iApply ("Hcont" with "Hre Htx [] [] Hrun").
      - iPureIntro. rgl.
        assert (Hms : GrepTree.matchstar c (map fr (seq 0 lr)) (map ft (seq 0 lt)) = true).
        { destruct lt as [| lt1].
          - rewrite ms_nil. exact Ebh.
          - rewrite map_seq_S ms_cons. rewrite map_seq_S in Ebh. rewrite Ebh. reflexivity. }
        rewrite Hms. apply bv_eq; vm_compute; reflexivity.
      - iPureIntro. rk. }
    pcn.
    (* ---- 0x28  lbu a5,0(s1) -- the text's first byte ---- *)
    assert (Hux : uint (mword_of_int ax : mword 64) = ax) by (apply uint_moi; unfold Z64; lia).
    assert (Eoff0 : uoff_i12 (mword_of_int 0 : mword 12) = 0) by (vm_compute; reflexivity).
    iDestruct (ustr_hd_acc with "Htx") as "[Hb Hcl]".
    iApply (wp_uk_lbu N h5 m4 (mword_of_int 0x28)
              (mword_of_int 0 : mword 12) s1_idx a5_idx dqt ax (ustr_hd lt ft) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs14 Hux Eoff0; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_grep_28 with "Hcode"). }
    iIntros "Hb" (h6) "Hrun". pcn.
    iDestruct ("Hcl" with "Hb") as "Htx".
    set (m5 := <[Regidx a5_idx := regval_into_reg (zero_extend' 64 (ustr_hd lt ft : mword 8) : mword 64)]> m4).
    assert (Ha55 : m5 !!! Regidx a5_idx = mword_of_int (bv_unsigned (ustr_hd lt ft)))
      by (rewrite /m5; rgl; apply zext8_byte).
    (* ---- 0x2c  c.beqz a5,0x3c ---- *)
    iApply (wp_uk_cbeqz N h6 m5 (mword_of_int 0x2c)
              (mword_of_int 8 : mword 8) (mword_of_int 7 : mword 3) a5_idx
              (bool_decide (ustr_hd lt ft = ubyte0)) (mword_of_int 0x3c) n
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha55 moi_byte_eqz; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_2c with "Hcode"). }
    iIntros (h7) "Hrun".
    destruct lt as [| lt1].
    { (* the text is used up: 0 *)
      rewrite (bool_decide_eq_true_2 _ (eq_refl : ustr_hd 0 ft = ubyte0)).
      iApply ("Hcont" with "Hre Htx [] [] Hrun").
      - iPureIntro. rewrite /m5; rgl. rewrite Ha04 ms_nil.
        rewrite (_ : GrepTree.matchhere (map fr (seq 0 lr)) [] = false); [ reflexivity | exact Ebh ].
      - iPureIntro. rewrite /m5. rk. }
    assert (Hft0 : ft 0%nat <> ubyte0) by (apply Htne; lia).
    rewrite (bool_decide_eq_false_2 _ Hft0). pcn.
    cbn [ustr_hd] in Ha55.
    (* ---- 0x2e  c.addi s1,s1,1 ---- *)
    iApply (wp_uk_caddi N h7 m5 (mword_of_int 0x2e)
              (mword_of_int 1 : mword 6) s1_idx (mword_of_int (ax + 1)) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m5; rgl; rewrite Hs14;
                    replace (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                      with (mword_of_int 1 : mword 64)
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite moi_add; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_2e with "Hcode"). }
    iIntros (h8) "Hrun". pcn.
    set (m6 := <[Regidx s1_idx := regval_into_reg (mword_of_int (ax + 1) : mword 64)]> m5).
    assert (Hk6 : rkeep (9 :: Wcaller) mc m6) by (rewrite /m6 /m5; rk).
    assert (Hs16 : m6 !!! Regidx s1_idx = mword_of_int (ax + 1)) by (rewrite /m6; rgl; reflexivity).
    assert (Hs26 : m6 !!! Regidx s2_idx = mword_of_int (bv_unsigned c)) by (rewrite /m6 /m5; rgl; exact Hs24).
    assert (Hs36 : m6 !!! Regidx s3_idx = mword_of_int ar) by (rewrite /m6 /m5; rgl; exact Hs34).
    assert (Hs46 : m6 !!! Regidx s4_idx = mword_of_int (if bv_unsigned c =? 46 then 1 else 0))
      by (rewrite /m6 /m5; rgl; exact Hs44).
    assert (Hbeq : uv_btaken BEQ (m6 !!! Regidx a5_idx) (m6 !!! Regidx s2_idx)
                   = GrepTree.bdec (ft 0%nat) c).
    { cbn [uv_btaken]. rewrite /m6 /m5. rgl. cbn [ustr_hd]. rewrite zext8_byte Hs24.
      exact (moi_byte_eq (ft 0%nat) c). }
    assert (Hbnez : uv_btaken BNE (m6 !!! Regidx s4_idx) zero_reg
                    = GrepTree.bdec c GrepTree.c_dot).
    { cbn [uv_btaken]. rewrite Hs46 moi_b01_neqz. apply bdec_lit.
      pose proof (byte_range c). lia. }
    destruct (GrepTree.bdec (ft 0%nat) c || GrepTree.bdec c GrepTree.c_dot) eqn:Etest.
    - (* one of the two tests holds: the next round, at [text + 1] *)
      iAssert (∀ (h' : CpuId),
                 urun N h' m6 (mword_of_int 0x1e) n -∗
                 mWP (Loop : expr riscv_lang))%I
        with "[Hcont Hre Htx]" as "Hnext".
      { iIntros (h') "Hrun".
        iDestruct (ustr_cons_split with "Htx") as "[Ht0 Htx]".
        iApply (IHt lt1 ltac:(lia) h' m6 c dqr dqt ar (ax + 1) fr (fun j => ft (S j)) n
                  Hs16 Hs26 Hs36 Hs46 Hn
                  with "Hcode Hre Htx Hrun").
        iIntros "Hre Htx" (h'' mx') "%Ha0x %Hkx' Hrun".
        iDestruct (ustr_cons_join with "Ht0 Htx") as "Htx";
          [ exact Hft0 | exact Htlen | ].
        iApply ("Hcont" with "Hre Htx [] [] Hrun").
        - iPureIntro. rewrite Ha0x. rewrite (map_seq_S ft lt1) ms_cons.
          rewrite (map_seq_S ft lt1) in Ebh. rewrite Ebh Etest. reflexivity.
        - iPureIntro. exact (rkeep_trans _ _ _ _ Hk6 Hkx'). }
      (* ---- 0x30  beq a5,s2,0x1e -- *text == c ---- *)
      iApply (wp_uk_btype N h8 m6 (mword_of_int 0x30)
                (mword_of_int 8174 : mword 13) s2_idx a5_idx BEQ (GrepTree.bdec (ft 0%nat) c)
                (mword_of_int 0x1e) n
                ltac:(rewrite Hbeq; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_30 with "Hcode"). }
      iIntros (h9) "Hrun".
      destruct (GrepTree.bdec (ft 0%nat) c) eqn:Etc.
      { iApply ("Hnext" with "Hrun"). }
      pcn.
      (* ---- 0x34  bnez s4,0x1e -- c == '.' ---- *)
      cbn [orb] in Etest.
      iApply (wp_uk_btype0 N h9 m6 (mword_of_int 0x34)
                (mword_of_int 8170 : mword 13) s4_idx BNE true
                (mword_of_int 0x1e) n
                ltac:(rewrite Hbnez; symmetry; exact Etest)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_34 with "Hcode"). }
      iIntros (h10) "Hrun".
      iApply ("Hnext" with "Hrun").
    - (* neither: 0 *)
      apply orb_false_iff in Etest as [Etc Ecd].
      iApply (wp_uk_btype N h8 m6 (mword_of_int 0x30)
                (mword_of_int 8174 : mword 13) s2_idx a5_idx BEQ false
                (mword_of_int 0x1e) n
                ltac:(rewrite Hbeq Etc; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros He; discriminate He)
                with "[] Hrun").
      { iApply (uis_grep_30 with "Hcode"). }
      iIntros (h9) "Hrun". pcn.
      iApply (wp_uk_btype0 N h9 m6 (mword_of_int 0x34)
                (mword_of_int 8170 : mword 13) s4_idx BNE false
                (mword_of_int 0x1e) n
                ltac:(rewrite Hbnez Ecd; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros He; discriminate He)
                with "[] Hrun").
      { iApply (uis_grep_34 with "Hcode"). }
      iIntros (h10) "Hrun". pcn.
      (* ---- 0x38  c.j 0x3c ---- *)
      iApply (wp_uk_cj N h10 m6 (mword_of_int 0x38)
                (mword_of_int 2 : mword 11) (mword_of_int 0x3c) n
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_38 with "Hcode"). }
      iIntros (h11) "Hrun".
      iApply ("Hcont" with "Hre Htx [] [] Hrun").
      + iPureIntro.
        assert (Ha06 : m6 !!! Regidx a0_idx = mword_of_int 0).
        { rewrite /m6 /m5. rgl. rewrite Ha04. reflexivity. }
        rewrite Ha06.
        rewrite (map_seq_S ft lt1) ms_cons. rewrite (map_seq_S ft lt1) in Ebh.
        rewrite Ebh Etc Ecd. reflexivity.
      + iPureIntro. exact Hk6.
  Qed.

  (* ===================================================================== *)
  (* matchstar(c, re, text) from matchhere's contract at [re]: the six-word *)
  (* frame (ra, s0..s4), the loop's registers, the loop, the epilogue.      *)
  (* ===================================================================== *)
  Local Lemma ms_of_mh (lr : nat) : mh_spec lr -> ms_spec lr.
  Proof using .
    intros IH h m c dqr dqt ar ax lt fr ft n Ha0 Ha1 Ha2 Hn.
    iIntros "#Hcode Hre Htx Hrun Hcont".
    rewrite /ms_words in Hn.
    replace n with (6 + (n - 6))%nat by lia.
    assert (Hn1 : (mh_words (map fr (seq 0 lr)) <= n - 6)%nat) by lia.
    remember (n - 6)%nat as n1 eqn:En1. clear En1.
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    assert (Hlo : 48 <= uint sp0) by lia.
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 6)))
                   = bv_unsigned sp0 - 48).
    { replace (- (8 * Z.of_nat 6)) with (-48) by lia.
      exact (uv_avi_neg sp0 48 ltac:(lia) ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp48 : uint (add_vec_int sp0 (- (8 * Z.of_nat 6))) = uint sp0 - 48)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Ho40 : uoff_sdsp (mword_of_int 5 : mword 6) = 40) by (vm_compute; reflexivity).
    assert (Ho32 : uoff_sdsp (mword_of_int 4 : mword 6) = 32) by (vm_compute; reflexivity).
    assert (Ho24 : uoff_sdsp (mword_of_int 3 : mword 6) = 24) by (vm_compute; reflexivity).
    assert (Ho16 : uoff_sdsp (mword_of_int 2 : mword 6) = 16) by (vm_compute; reflexivity).
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8) by (vm_compute; reflexivity).
    assert (Ho0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0) by (vm_compute; reflexivity).
    rewrite /GrepSyms.matchstar.
    (* ---- 0x0  c.addi16sp sp,sp,-48 -- THE PUSH ---- *)
    iApply (wp_uk_caddi16sp_dn N h m (mword_of_int 0x0) (mword_of_int 61 : mword 6) 6 n1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_00 with "Hcode"). }
    rewrite Hsp. iIntros "Hst" (h1) "Hrun". pcn.
    iDestruct (ustack_6_open with "Hst")
      as "(_ & [%w1 Hw1] & [%w2 Hw2] & [%w3 Hw3] & [%w4 Hw4] & [%w5 Hw5] & [%w6 Hw6])".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 6)))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 6)))
      by (rewrite /m1; rgl; reflexivity).
    assert (Hra1 : m1 !!! Regidx ra_idx = m !!! Regidx ra_idx) by (rewrite /m1; rgl; reflexivity).
    assert (Hs01 : m1 !!! Regidx s0_idx = m !!! Regidx s0_idx) by (rewrite /m1; rgl; reflexivity).
    assert (Hs11 : m1 !!! Regidx s1_idx = m !!! Regidx s1_idx) by (rewrite /m1; rgl; reflexivity).
    assert (Hs21 : m1 !!! Regidx s2_idx = m !!! Regidx s2_idx) by (rewrite /m1; rgl; reflexivity).
    assert (Hs31 : m1 !!! Regidx s3_idx = m !!! Regidx s3_idx) by (rewrite /m1; rgl; reflexivity).
    assert (Hs41 : m1 !!! Regidx s4_idx = m !!! Regidx s4_idx) by (rewrite /m1; rgl; reflexivity).
    (* ---- 0x2..0xc  the six spills ---- *)
    iApply (wp_uk_csdsp N h1 m1 (mword_of_int 0x2) (mword_of_int 5 : mword 6) ra_idx
              (uint sp0 - 8) w1 n1
              ltac:(rewrite Hsp1 Hsp48 Ho40; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw1 Hrun").
    { iApply (uis_grep_02 with "Hcode"). }
    iIntros "Hw1" (h2) "Hrun". pcn.
    iApply (wp_uk_csdsp N h2 m1 (mword_of_int 0x4) (mword_of_int 4 : mword 6) s0_idx
              (uint sp0 - 16) w2 n1
              ltac:(rewrite Hsp1 Hsp48 Ho32; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw2 Hrun").
    { iApply (uis_grep_04 with "Hcode"). }
    iIntros "Hw2" (h3) "Hrun". pcn.
    iApply (wp_uk_csdsp N h3 m1 (mword_of_int 0x6) (mword_of_int 3 : mword 6) s1_idx
              (uint sp0 - 24) w3 n1
              ltac:(rewrite Hsp1 Hsp48 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw3 Hrun").
    { iApply (uis_grep_06 with "Hcode"). }
    iIntros "Hw3" (h4) "Hrun". pcn.
    iApply (wp_uk_csdsp N h4 m1 (mword_of_int 0x8) (mword_of_int 2 : mword 6) s2_idx
              (uint sp0 - 32) w4 n1
              ltac:(rewrite Hsp1 Hsp48 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw4 Hrun").
    { iApply (uis_grep_08 with "Hcode"). }
    iIntros "Hw4" (h5) "Hrun". pcn.
    iApply (wp_uk_csdsp N h5 m1 (mword_of_int 0xa) (mword_of_int 1 : mword 6) s3_idx
              (uint sp0 - 40) w5 n1
              ltac:(rewrite Hsp1 Hsp48 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw5 Hrun").
    { iApply (uis_grep_0a with "Hcode"). }
    iIntros "Hw5" (h6) "Hrun". pcn.
    iApply (wp_uk_csdsp N h6 m1 (mword_of_int 0xc) (mword_of_int 0 : mword 6) s4_idx
              (uint sp0 - 48) w6 n1
              ltac:(rewrite Hsp1 Hsp48 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw6 Hrun").
    { iApply (uis_grep_0c with "Hcode"). }
    iIntros "Hw6" (h7) "Hrun". pcn.
    rewrite Hra1 Hs01 Hs11 Hs21 Hs31 Hs41.
    (* ---- 0xe  c.addi4spn s0,sp,48 ---- *)
    iApply (wp_uk_caddi4spn N h7 m1 (mword_of_int 0xe)
              (mword_of_int 0 : mword 3) (mword_of_int 12 : mword 8) s0_idx
              (add_vec (m1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8)))) n1
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_0e with "Hcode"). }
    iIntros (h8) "Hrun". pcn.
    set (m2 := <[Regidx s0_idx := regval_into_reg
                   (add_vec (m1 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> m1).
    (* ---- 0x10  c.mv s2,a0 ; 0x12  c.mv s3,a1 ; 0x14  c.mv s1,a2 ---- *)
    iApply (wp_uk_cmv N h8 m2 (mword_of_int 0x10) s2_idx a0_idx
              (mword_of_int (bv_unsigned c)) n1
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m2 /m1; rgl; rewrite Ha0 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_10 with "Hcode"). }
    iIntros (h9) "Hrun". pcn.
    set (m3 := <[Regidx s2_idx := regval_into_reg (mword_of_int (bv_unsigned c) : mword 64)]> m2).
    iApply (wp_uk_cmv N h9 m3 (mword_of_int 0x12) s3_idx a1_idx (mword_of_int ar) n1
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m3 /m2 /m1; rgl; rewrite Ha1 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_12 with "Hcode"). }
    iIntros (h10) "Hrun". pcn.
    set (m4 := <[Regidx s3_idx := regval_into_reg (mword_of_int ar : mword 64)]> m3).
    iApply (wp_uk_cmv N h10 m4 (mword_of_int 0x14) s1_idx a2_idx (mword_of_int ax) n1
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m4 /m3 /m2 /m1; rgl; rewrite Ha2 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_14 with "Hcode"). }
    iIntros (h11) "Hrun". pcn.
    set (m5 := <[Regidx s1_idx := regval_into_reg (mword_of_int ax : mword 64)]> m4).
    (* ---- 0x16  addi s4,a0,-46 ; 0x1a  seqz s4,s4 -- the '.' flag ---- *)
    pose proof (byte_range c) as Hcr.
    iApply (wp_uk_addi N h11 m5 (mword_of_int 0x16)
              (mword_of_int 4050 : mword 12) a0_idx s4_idx
              (mword_of_int (bv_unsigned c - 46)) n1
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m5 /m4 /m3 /m2 /m1; rgl; rewrite Ha0;
                    replace (sign_extend' 64 (mword_of_int 4050 : mword 12) : mword 64)
                      with (mword_of_int (-46) : mword 64)
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite moi_add; f_equal; lia)
              with "[] Hrun").
    { iApply (uis_grep_16 with "Hcode"). }
    iIntros (h12) "Hrun". pcn.
    set (m6 := <[Regidx s4_idx := regval_into_reg (mword_of_int (bv_unsigned c - 46) : mword 64)]> m5).
    iApply (wp_uk_sltiu N h12 m6 (mword_of_int 0x1a)
              (mword_of_int 1 : mword 12) s4_idx s4_idx
              (mword_of_int (if bv_unsigned c =? 46 then 1 else 0)) n1
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m6; rgl; symmetry; apply moi_seqz_sub; lia)
              with "[] Hrun").
    { iApply (uis_grep_1a with "Hcode"). }
    iIntros (h13) "Hrun". pcn.
    set (m7 := <[Regidx s4_idx := regval_into_reg
                   (mword_of_int (if bv_unsigned c =? 46 then 1 else 0) : mword 64)]> m6).
    (* ---- 0x1e..0x3a  THE LOOP ---- *)
    iApply (wp_kgrep_ms_loop lr IH lt h13 m7 c dqr dqt ar ax fr ft n1
              ltac:(rewrite /m7 /m6 /m5; rgl; reflexivity)
              ltac:(rewrite /m7 /m6 /m5 /m4 /m3; rgl; reflexivity)
              ltac:(rewrite /m7 /m6 /m5 /m4; rgl; reflexivity)
              ltac:(rewrite /m7; rgl; reflexivity)
              Hn1
              with "Hcode Hre Htx Hrun").
    iIntros "Hre Htx" (h14 mc) "%Ha0c %Hkc Hrun".
    assert (Hspc : mc !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 6))).
    { rewrite (Hkc csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /m7 /m6 /m5 /m4 /m3 /m2. rgl. exact Hsp1. }
    (* ---- 0x3c..0x46  the six reloads ---- *)
    iApply (wp_uk_cldsp N h14 mc (mword_of_int 0x3c) (mword_of_int 5 : mword 6) ra_idx
              (uint sp0 - 8) (m !!! Regidx ra_idx) n1
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspc Hsp48 Ho40; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw1 Hrun").
    { iApply (uis_grep_3c with "Hcode"). }
    iIntros "Hw1" (h15) "Hrun". pcn.
    set (mc1 := <[Regidx ra_idx := regval_into_reg (m !!! Regidx ra_idx)]> mc).
    iApply (wp_uk_cldsp N h15 mc1 (mword_of_int 0x3e) (mword_of_int 4 : mword 6) s0_idx
              (uint sp0 - 16) (m !!! Regidx s0_idx) n1
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite /mc1; rgl; rewrite Hspc Hsp48 Ho32; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw2 Hrun").
    { iApply (uis_grep_3e with "Hcode"). }
    iIntros "Hw2" (h16) "Hrun". pcn.
    set (mc2 := <[Regidx s0_idx := regval_into_reg (m !!! Regidx s0_idx)]> mc1).
    iApply (wp_uk_cldsp N h16 mc2 (mword_of_int 0x40) (mword_of_int 3 : mword 6) s1_idx
              (uint sp0 - 24) (m !!! Regidx s1_idx) n1
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite /mc2 /mc1; rgl; rewrite Hspc Hsp48 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw3 Hrun").
    { iApply (uis_grep_40 with "Hcode"). }
    iIntros "Hw3" (h17) "Hrun". pcn.
    set (mc3 := <[Regidx s1_idx := regval_into_reg (m !!! Regidx s1_idx)]> mc2).
    iApply (wp_uk_cldsp N h17 mc3 (mword_of_int 0x42) (mword_of_int 2 : mword 6) s2_idx
              (uint sp0 - 32) (m !!! Regidx s2_idx) n1
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite /mc3 /mc2 /mc1; rgl; rewrite Hspc Hsp48 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw4 Hrun").
    { iApply (uis_grep_42 with "Hcode"). }
    iIntros "Hw4" (h18) "Hrun". pcn.
    set (mc4 := <[Regidx s2_idx := regval_into_reg (m !!! Regidx s2_idx)]> mc3).
    iApply (wp_uk_cldsp N h18 mc4 (mword_of_int 0x44) (mword_of_int 1 : mword 6) s3_idx
              (uint sp0 - 40) (m !!! Regidx s3_idx) n1
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite /mc4 /mc3 /mc2 /mc1; rgl; rewrite Hspc Hsp48 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw5 Hrun").
    { iApply (uis_grep_44 with "Hcode"). }
    iIntros "Hw5" (h19) "Hrun". pcn.
    set (mc5 := <[Regidx s3_idx := regval_into_reg (m !!! Regidx s3_idx)]> mc4).
    iApply (wp_uk_cldsp N h19 mc5 (mword_of_int 0x46) (mword_of_int 0 : mword 6) s4_idx
              (uint sp0 - 48) (m !!! Regidx s4_idx) n1
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite /mc5 /mc4 /mc3 /mc2 /mc1; rgl; rewrite Hspc Hsp48 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw6 Hrun").
    { iApply (uis_grep_46 with "Hcode"). }
    iIntros "Hw6" (h20) "Hrun". pcn.
    set (mc6 := <[Regidx s4_idx := regval_into_reg (m !!! Regidx s4_idx)]> mc5).
    assert (Hsp6 : mc6 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 6)))
      by (rewrite /mc6 /mc5 /mc4 /mc3 /mc2 /mc1; rgl; exact Hspc).
    (* ---- 0x48  c.addi16sp sp,sp,48 -- THE POP ---- *)
    assert (HR : 0 <= bv_unsigned sp0 < 18446744073709551616).
    { pose proof (bv_unsigned_in_range 64 sp0) as H0.
      assert (Em : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
      rewrite Em in H0. exact H0. }
    assert (Hd6 : 0 <= 8 * Z.of_nat 6) by lia.
    assert (Hlt6 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 6))) + 8 * Z.of_nat 6 < Z64)
      by (rewrite Hbsp; unfold Z64; lia).
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 6))) (8 * Z.of_nat 6) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 6))) (8 * Z.of_nat 6) Hd6 Hlt6).
      rewrite Hbsp. lia. }
    iApply (wp_uk_caddi16sp_up N h20 mc6 (mword_of_int 0x48) (mword_of_int 3 : mword 6) 6 n1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hw1 Hw2 Hw3 Hw4 Hw5 Hw6] Hrun").
    { iApply (uis_grep_48 with "Hcode"). }
    { rewrite Hsp6 Hup.
      iApply (ustack_6_close with "[Hw1] [Hw2] [Hw3] [Hw4] [Hw5] [Hw6]"); [ exact Hal8 | .. ];
        iExists _; iFrame. }
    rewrite Hsp6 Hup. iIntros (h21) "Hrun". pcn.
    set (mc7 := <[Regidx csp_rs1 := regval_into_reg sp0]> mc6).
    (* ---- 0x4a  c.jr ra ---- *)
    iApply (wp_uk_cjr N h21 mc7 (mword_of_int 0x4a) ra_idx (ret_pc (m !!! Regidx ra_idx)) (6 + n1)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /mc7 /mc6 /mc5 /mc4 /mc3 /mc2 /mc1; rgl; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_4a with "Hcode"). }
    iIntros (h22) "Hrun".
    iApply ("Hcont" with "Hre Htx [] [] Hrun").
    - iPureIntro.
      set (W := [2; 8; 9; 18; 19; 20] ++ Wcaller).
      assert (Hk7 : rkeep W m m7) by (rewrite /m7 /m6 /m5 /m4 /m3 /m2 /m1; rk).
      assert (Hkc' : rkeep W m7 mc)
        by (refine (rkeep_weaken_dec _ _ _ _ _ Hkc); vm_compute; reflexivity).
      assert (Hkmc : rkeep W mc mc7) by (rewrite /mc7 /mc6 /mc5 /mc4 /mc3 /mc2 /mc1; rk).
      apply (rkeep_ucs_dec W [2; 8; 9; 18; 19; 20] m mc7 ltac:(vm_compute; reflexivity)
               (rkeep_trans _ _ _ _ (rkeep_trans _ _ _ _ Hk7 Hkc') Hkmc)).
      intros z Hz.
      destruct Hz as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
        try change (Regidx (mword_of_int 2)) with (Regidx csp_rs1);
        rewrite /mc7 /mc6 /mc5 /mc4 /mc3 /mc2 /mc1; rgl; first [ reflexivity | symmetry; exact Hsp ].
    - iPureIntro. rewrite /mc7 /mc6 /mc5 /mc4 /mc3 /mc2 /mc1. rgl. exact Ha0c.
  Qed.

  (* ===================================================================== *)
  (* matchhere(re, text): ONE STEP OF THE STRONG INDUCTION.  From the       *)
  (* contract at every shorter pattern -- the literal arm recurses at      *)
  (* [re+1], the star arm hands matchstar [re+2] -- to the contract here.  *)
  (* ===================================================================== *)
  Local Lemma mh_step (lr : nat) :
    (forall l : nat, (l < lr)%nat -> mh_spec l) -> mh_spec lr.
  Proof using .
    intros IHall h m dqr dqt ar ax lt fr ft n Ha0 Ha1 Hn.
    iIntros "#Hcode Hre Htx Hrun Hcont".
    iDestruct (urun_ustr_bnd with "Hrun Hre") as %[Har0 Har38].
    change (2 ^ 38) with 274877906944 in Har38.
    iDestruct (urun_ustr_bnd with "Hrun Htx") as %[Hax0 Hax38].
    change (2 ^ 38) with 274877906944 in Hax38.
    iDestruct (ustr_nonul with "Hre") as %Hrne.
    iDestruct (ustr_len with "Hre") as %Hrlen.
    iDestruct (ustr_nonul with "Htx") as %Htne.
    assert (Hur : uint (mword_of_int ar : mword 64) = ar) by (apply uint_moi; unfold Z64; lia).
    assert (Hux : uint (mword_of_int ax : mword 64) = ax) by (apply uint_moi; unfold Z64; lia).
    assert (Eoff0 : uoff_i12 (mword_of_int 0 : mword 12) = 0) by (vm_compute; reflexivity).
    rewrite /GrepSyms.matchhere.
    (* ---- 0x4c  lbu a4,0(a0) -- re[0] ---- *)
    iDestruct (ustr_hd_acc with "Hre") as "[Hb Hcl]".
    iApply (wp_uk_lbu N h m (mword_of_int 0x4c)
              (mword_of_int 0 : mword 12) a0_idx a4_idx dqr ar (ustr_hd lr fr) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Ha0 Hur Eoff0; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_grep_4c with "Hcode"). }
    iIntros "Hb" (h1) "Hrun". pcn.
    iDestruct ("Hcl" with "Hb") as "Hre".
    set (m1 := <[Regidx a4_idx := regval_into_reg (zero_extend' 64 (ustr_hd lr fr : mword 8) : mword 64)]> m).
    assert (Ha41 : m1 !!! Regidx a4_idx = mword_of_int (bv_unsigned (ustr_hd lr fr)))
      by (rewrite /m1; rgl; apply zext8_byte).
    (* ---- 0x50  c.beqz a4,0xae ---- *)
    iApply (wp_uk_cbeqz N h1 m1 (mword_of_int 0x50)
              (mword_of_int 47 : mword 8) (mword_of_int 6 : mword 3) a4_idx
              (bool_decide (ustr_hd lr fr = ubyte0)) (mword_of_int 0xae) n
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha41 moi_byte_eqz; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_50 with "Hcode"). }
    iIntros (h2) "Hrun".
    destruct lr as [| lr1].
    { (* the empty pattern: 1, and no frame *)
      rewrite (bool_decide_eq_true_2 _ (eq_refl : ustr_hd 0 fr = ubyte0)).
      (* ---- 0xae  c.li a0,1 ---- *)
      iApply (wp_uk_cli N h2 m1 (mword_of_int 0xae)
                (mword_of_int 1 : mword 6) a0_idx n
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) with "[] Hrun").
      { iApply (uis_grep_ae with "Hcode"). }
      iIntros (h3) "Hrun". pcn.
      set (m2 := <[Regidx a0_idx := regval_into_reg (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)]> m1).
      (* ---- 0xb0  c.jr ra ---- *)
      iApply (wp_uk_cjr N h3 m2 (mword_of_int 0xb0) ra_idx (ret_pc (m !!! Regidx ra_idx)) n
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /m2 /m1; rgl; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_b0 with "Hcode"). }
      iIntros (h4) "Hrun".
      iApply ("Hcont" with "Hre Htx [] [] Hrun").
      - iPureIntro. apply (rkeep_ucs_dec Wcaller [] m m2 ltac:(vm_compute; reflexivity)).
        + rewrite /m2 /m1. rk.
        + intros z [].
      - iPureIntro. rewrite /m2; rgl.
        change (GrepTree.matchhere (map fr (seq 0 0)) (map ft (seq 0 lt))) with true.
        apply bv_eq; vm_compute; reflexivity. }
    (* a nonempty pattern: re[0] is not the NUL *)
    assert (Hfr0 : fr 0%nat <> ubyte0) by (apply Hrne; lia).
    cbn [ustr_hd] in Ha41.
    rewrite (bool_decide_eq_false_2 _ Hfr0). pcn.
    assert (Hn2 : (2 <= n)%nat).
    { rewrite map_seq_S in Hn.
      pose proof (mh_words_ge2 (fr 0%nat) (map (fun j => fr (S j)) (seq 0 lr1))). lia. }
    replace n with (2 + (n - 2))%nat by lia.
    remember (n - 2)%nat as n1 eqn:En1.
    assert (Hsp1m : m1 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1) by (rewrite /m1; rgl; reflexivity).
    assert (Hra1m : m1 !!! Regidx ra_idx = m !!! Regidx ra_idx) by (rewrite /m1; rgl; reflexivity).
    assert (Hs01m : m1 !!! Regidx s0_idx = m !!! Regidx s0_idx) by (rewrite /m1; rgl; reflexivity).
    (* ---- 0x52..0x58  THE FRAME ---- *)
    iApply (wp_kgrep_pro2 N h2 m1 (mword_of_int 0x52) (mword_of_int 0x54)
              (mword_of_int 0x56) (mword_of_int 0x58) (mword_of_int 0x5a) n1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [] [] [] Hrun").
    { iApply (uis_grep_52 with "Hcode"). }
    { iApply (uis_grep_54 with "Hcode"). }
    { iApply (uis_grep_56 with "Hcode"). }
    { iApply (uis_grep_58 with "Hcode"). }
    iIntros (h3 m2) "%Hal8 %Hlo %Hsp2 %Hk2 Hwra Hws0 Hrun".
    iDestruct (ustr_cons_split with "Hre") as "[Hr0 Hre1]".
    (* THE EPILOGUE at 0x82, shared by every arm that took the frame *)
    iAssert (∀ (h' : CpuId) (mc : regfile),
               ustr γd dqr ar (S lr1) fr -∗
               ustr γd dqt ax lt ft -∗
               ⌜ mc !!! Regidx a0_idx
                 = mword_of_int (if GrepTree.matchhere (map fr (seq 0 (S lr1))) (map ft (seq 0 lt))
                                 then 1 else 0) ⌝ -∗
               ⌜ rkeep ([2; 8] ++ Wcaller) m1 mc ⌝ -∗
               ⌜ mc !!! Regidx csp_rs1
                 = add_vec_int (m1 !!! Regidx csp_rs1) (- (8 * Z.of_nat 2)) ⌝ -∗
               urun N h' mc (mword_of_int 0x82) n1 -∗
               mWP (Loop : expr riscv_lang))%I
      with "[Hwra Hws0 Hcont]" as "Htail".
    { iIntros (h' mc) "Hre Htx %Ha0c %Hkc %Hspc Hrun".
      iApply (wp_kgrep_epi2 N h' mc (m1 !!! Regidx csp_rs1) (m1 !!! Regidx ra_idx)
                (m1 !!! Regidx s0_idx) (mword_of_int 0x82) (mword_of_int 0x84)
                (mword_of_int 0x86) (mword_of_int 0x88) n1
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                Hspc Hal8 Hlo
                with "[] [] [] [] Hwra Hws0 Hrun").
      { iApply (uis_grep_82 with "Hcode"). }
      { iApply (uis_grep_84 with "Hcode"). }
      { iApply (uis_grep_86 with "Hcode"). }
      { iApply (uis_grep_88 with "Hcode"). }
      iIntros (h'' m') "%Hsp' %Hs0' %Hk' Hrun".
      rewrite Hra1m.
      iApply ("Hcont" with "Hre Htx [] [] Hrun").
      - iPureIntro.
        assert (Hkm1 : rkeep ([2; 8] ++ Wcaller) m m1) by (rewrite /m1; rk).
        assert (Hkm : rkeep ([2; 8] ++ Wcaller) m m').
        { eapply rkeep_trans; [ exact Hkm1 | ].
          eapply rkeep_trans; [ exact Hkc | ].
          refine (rkeep_weaken_dec _ _ _ _ _ Hk'); vm_compute; reflexivity. }
        apply (rkeep_ucs_dec ([2; 8] ++ Wcaller) [2; 8] m m'
                 ltac:(vm_compute; reflexivity) Hkm).
        intros z [<- | [<- | []]].
        + rewrite Hsp'. exact Hsp1m.
        + rewrite Hs0'. exact Hs01m.
      - iPureIntro. rewrite (Hk' a0_idx ltac:(vm_compute; reflexivity)). exact Ha0c. }
    assert (Hk2' : rkeep ([2; 8] ++ Wcaller) m1 m2)
      by (refine (rkeep_weaken_dec _ _ _ _ _ Hk2); vm_compute; reflexivity).
    assert (Ha02 : m2 !!! Regidx a0_idx = mword_of_int ar)
      by (rewrite (Hk2 a0_idx ltac:(vm_compute; reflexivity)) /m1; rgl; exact Ha0).
    assert (Ha12 : m2 !!! Regidx a1_idx = mword_of_int ax)
      by (rewrite (Hk2 a1_idx ltac:(vm_compute; reflexivity)) /m1; rgl; exact Ha1).
    assert (Ha42 : m2 !!! Regidx a4_idx = mword_of_int (bv_unsigned (fr 0%nat)))
      by (rewrite (Hk2 a4_idx ltac:(vm_compute; reflexivity)); exact Ha41).
    (* ---- 0x5a  c.mv a5,a0 ---- *)
    iApply (wp_uk_cmv N h3 m2 (mword_of_int 0x5a) a5_idx a0_idx (mword_of_int ar) n1
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha02 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_5a with "Hcode"). }
    iIntros (h4) "Hrun". pcn.
    set (m3 := <[Regidx a5_idx := regval_into_reg (mword_of_int ar : mword 64)]> m2).
    (* ---- 0x5c  lbu a3,1(a0) -- re[1] ---- *)
    assert (Eoff1 : uoff_i12 (mword_of_int 1 : mword 12) = 1) by (vm_compute; reflexivity).
    iDestruct (ustr_hd_acc with "Hre1") as "[Hb Hcl]".
    iApply (wp_uk_lbu N h4 m3 (mword_of_int 0x5c)
              (mword_of_int 1 : mword 12) a0_idx a3_idx dqr (ar + 1)
              (ustr_hd lr1 (fun j => fr (S j))) n1
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite /m3; rgl; rewrite Ha02 Hur Eoff1; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_grep_5c with "Hcode"). }
    iIntros "Hb" (h5) "Hrun". pcn.
    iDestruct ("Hcl" with "Hb") as "Hre1".
    set (m4 := <[Regidx a3_idx := regval_into_reg
                   (zero_extend' 64 (ustr_hd lr1 (fun j => fr (S j)) : mword 8) : mword 64)]> m3).
    (* ---- 0x60  li a2,42 ---- *)
    iApply (wp_uk_li N h5 m4 (mword_of_int 0x60)
              (mword_of_int 42 : mword 12) a2_idx (mword_of_int 42) n1
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_60 with "Hcode"). }
    iIntros (h6) "Hrun". pcn.
    set (m5 := <[Regidx a2_idx := regval_into_reg (mword_of_int 42 : mword 64)]> m4).
    assert (Hk5 : rkeep ([2; 8] ++ Wcaller) m1 m5) by (rewrite /m5 /m4 /m3; rk).
    assert (Hsp5 : m5 !!! Regidx csp_rs1
                   = add_vec_int (m1 !!! Regidx csp_rs1) (- (8 * Z.of_nat 2)))
      by (rewrite /m5 /m4 /m3; rgl; exact Hsp2).
    assert (Ha35 : m5 !!! Regidx a3_idx
                   = mword_of_int (bv_unsigned (ustr_hd lr1 (fun j => fr (S j)))))
      by (rewrite /m5 /m4; rgl; apply zext8_byte).
    assert (Ha45 : m5 !!! Regidx a4_idx = mword_of_int (bv_unsigned (fr 0%nat)))
      by (rewrite /m5 /m4 /m3; rgl; exact Ha42).
    assert (Ha55 : m5 !!! Regidx a5_idx = mword_of_int ar) by (rewrite /m5 /m4 /m3; rgl; reflexivity).
    assert (Ha05 : m5 !!! Regidx a0_idx = mword_of_int ar) by (rewrite /m5 /m4 /m3; rgl; exact Ha02).
    assert (Ha15 : m5 !!! Regidx a1_idx = mword_of_int ax) by (rewrite /m5 /m4 /m3; rgl; exact Ha12).
    (* ---- 0x64  beq a3,a2,0x8a -- re[1] == '*' ---- *)
    assert (Hbeq : uv_btaken BEQ (m5 !!! Regidx a3_idx) (m5 !!! Regidx a2_idx)
                   = GrepTree.bdec (ustr_hd lr1 (fun j => fr (S j))) GrepTree.c_star).
    { cbn [uv_btaken]. rewrite Ha35.
      assert (Ha25 : m5 !!! Regidx a2_idx = mword_of_int 42) by (rewrite /m5; rgl; reflexivity).
      rewrite Ha25.
      pose proof (byte_range (ustr_hd lr1 (fun j => fr (S j)))).
      rewrite (moi_eq_vec (bv_unsigned (ustr_hd lr1 (fun j => fr (S j)))) 42
                 ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
      apply bdec_lit. lia. }
    iApply (wp_uk_btype N h6 m5 (mword_of_int 0x64)
              (mword_of_int 38 : mword 13) a2_idx a3_idx BEQ
              (GrepTree.bdec (ustr_hd lr1 (fun j => fr (S j))) GrepTree.c_star)
              (mword_of_int 0x8a) n1
              ltac:(rewrite Hbeq; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_64 with "Hcode"). }
    iIntros (h7) "Hrun".
    destruct (GrepTree.bdec (ustr_hd lr1 (fun j => fr (S j))) GrepTree.c_star) eqn:Estar.
    - (* ================= re[1] == '*': matchstar(re[0], re+2, text) ================= *)
      destruct lr1 as [| lr2].
      { exfalso. cbn [ustr_hd] in Estar. vm_compute in Estar. discriminate Estar. }
      cbn [ustr_hd] in Estar.
      assert (Hf1 : fr 1%nat = GrepTree.c_star) by (apply GrepTree.bdec_spec; exact Estar).
      iDestruct (ustr_nonul with "Hre1") as %Hne1.
      iDestruct (ustr_len with "Hre1") as %Hlen1.
      iDestruct (ustr_cons_split with "Hre1") as "[Hr1 Hre2]".
      assert (Hms : (ms_words (map (fun j => fr (S (S j))) (seq 0 lr2)) <= n1)%nat).
      { rewrite map_seq_S map_seq_S in Hn. cbv beta in Hn.
        rewrite (mh_words_star (fr 0%nat) (fr 1%nat) _ Estar) in Hn.
        rewrite /ms_words. lia. }
      iApply (wp_kgrep_mh_star lr2 (ms_of_mh lr2 (IHall lr2 ltac:(lia)))
                h7 m5 dqr dqt ar ax lt (fr 0%nat) (fun j => fr (S (S j))) ft n1
                Ha45 Ha05 Ha15 Hms
                with "Hcode Hre2 Htx Hrun").
      iIntros "Hre2 Htx" (h8 mc) "%Ha0c %Hkc Hrun".
      iDestruct (ustr_cons_join γd dqr (ar + 1) lr2 (fun j => fr (S j))
                   (Hne1 0%nat ltac:(lia)) Hlen1 with "Hr1 Hre2") as "Hre1".
      iDestruct (ustr_cons_join γd dqr ar (S lr2) fr Hfr0 Hrlen with "Hr0 Hre1") as "Hre".
      iApply ("Htail" $! h8 mc with "Hre Htx [] [] [] Hrun").
      + iPureIntro. rewrite Ha0c. rewrite map_seq_S map_seq_S. cbv beta.
        rewrite Hf1 GrepTree.matchhere_star. reflexivity.
      + iPureIntro. eapply rkeep_trans; [ exact Hk5 | ].
        refine (rkeep_weaken_dec _ _ _ _ _ Hkc); vm_compute; reflexivity.
      + iPureIntro. rewrite (Hkc csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp5.
    - (* ================= re[1] is not '*' ================= *)
      pcn.
      (* ---- 0x68  c.bnez a3,0x70 -- re[1] != 0 ---- *)
      iApply (wp_uk_cbnez N h7 m5 (mword_of_int 0x68)
                (mword_of_int 4 : mword 8) (mword_of_int 5 : mword 3) a3_idx
                (negb (bool_decide (ustr_hd lr1 (fun j => fr (S j)) = ubyte0)))
                (mword_of_int 0x70) n1
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha35 moi_byte_neqz; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_68 with "Hcode"). }
      iIntros (h8) "Hrun".
      destruct lr1 as [| lr1'].
      + (* ---------- re = [c]: the '$' test ---------- *)
        rewrite (bool_decide_eq_true_2 _ (eq_refl : ustr_hd 0 (fun j => fr (S j)) = ubyte0)).
        cbn [negb]. pcn.
        pose proof (byte_range (fr 0%nat)) as Hcr.
        (* ---- 0x6a  addi a3,a4,-36 ---- *)
        iApply (wp_uk_addi N h8 m5 (mword_of_int 0x6a)
                  (mword_of_int 4060 : mword 12) a4_idx a3_idx
                  (mword_of_int (bv_unsigned (fr 0%nat) - 36)) n1
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; discriminate)
                  ltac:(rewrite Ha45;
                        replace (sign_extend' 64 (mword_of_int 4060 : mword 12) : mword 64)
                          with (mword_of_int (-36) : mword 64)
                          by (apply bv_eq; vm_compute; reflexivity);
                        rewrite moi_add; f_equal; lia)
                  with "[] Hrun").
        { iApply (uis_grep_6a with "Hcode"). }
        iIntros (h9) "Hrun". pcn.
        set (m6 := <[Regidx a3_idx := regval_into_reg
                       (mword_of_int (bv_unsigned (fr 0%nat) - 36) : mword 64)]> m5).
        (* ---- 0x6e  c.beqz a3,0x98 -- re[0] == '$' ---- *)
        iApply (wp_uk_cbeqz N h9 m6 (mword_of_int 0x6e)
                  (mword_of_int 21 : mword 8) (mword_of_int 5 : mword 3) a3_idx
                  (GrepTree.bdec (fr 0%nat) GrepTree.c_dollar) (mword_of_int 0x98) n1
                  ltac:(vm_compute; reflexivity)
                  ltac:(rewrite /m6; rgl;
                        rewrite (moi_sub_eqz (bv_unsigned (fr 0%nat)) 36 Hcr ltac:(lia));
                        symmetry; apply bdec_lit; lia)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(intros _; vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_grep_6e with "Hcode"). }
        iIntros (h10) "Hrun".
        assert (Hk6 : rkeep ([2; 8] ++ Wcaller) m1 m6) by (rewrite /m6; rk).
        assert (Hsp6 : m6 !!! Regidx csp_rs1
                       = add_vec_int (m1 !!! Regidx csp_rs1) (- (8 * Z.of_nat 2)))
          by (rewrite /m6; rgl; first [ reflexivity | assumption ]).
        destruct (GrepTree.bdec (fr 0%nat) GrepTree.c_dollar) eqn:Edol.
        * (* re = "$": *text == 0 *)
          (* ---- 0x98  lbu a0,0(a1) ---- *)
          iDestruct (ustr_hd_acc with "Htx") as "[Hb Hcl]".
          iApply (wp_uk_lbu N h10 m6 (mword_of_int 0x98)
                    (mword_of_int 0 : mword 12) a1_idx a0_idx dqt ax (ustr_hd lt ft) n1
                    ltac:(unfold unot_sp; vm_compute; discriminate)
                    ltac:(rewrite /m6; rgl; rewrite Ha12 Hux Eoff0; lia)
                    ltac:(vm_compute; discriminate)
                    with "[] Hb Hrun").
          { iApply (uis_grep_98 with "Hcode"). }
          iIntros "Hb" (h11) "Hrun". pcn.
          iDestruct ("Hcl" with "Hb") as "Htx".
          set (m7 := <[Regidx a0_idx := regval_into_reg
                         (zero_extend' 64 (ustr_hd lt ft : mword 8) : mword 64)]> m6).
          (* ---- 0x9c  seqz a0,a0 ---- *)
          pose proof (byte_range (ustr_hd lt ft)) as Htr.
          iApply (wp_uk_sltiu N h11 m7 (mword_of_int 0x9c)
                    (mword_of_int 1 : mword 12) a0_idx a0_idx
                    (mword_of_int (if bv_unsigned (ustr_hd lt ft) =? 0 then 1 else 0)) n1
                    ltac:(unfold unot_sp; vm_compute; discriminate)
                    ltac:(vm_compute; discriminate)
                    ltac:(rewrite /m7; rgl; rewrite zext8_byte; symmetry; apply moi_seqz; lia)
                    with "[] Hrun").
          { iApply (uis_grep_9c with "Hcode"). }
          iIntros (h12) "Hrun". pcn.
          set (m8 := <[Regidx a0_idx := regval_into_reg
                         (mword_of_int (if bv_unsigned (ustr_hd lt ft) =? 0 then 1 else 0) : mword 64)]> m7).
          (* ---- 0xa0  c.j 0x82 ---- *)
          iApply (wp_uk_cj N h12 m8 (mword_of_int 0xa0)
                    (mword_of_int 2033 : mword 11) (mword_of_int 0x82) n1
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(vm_compute; reflexivity)
                    with "[] Hrun").
          { iApply (uis_grep_a0 with "Hcode"). }
          iIntros (h13) "Hrun".
          iDestruct (ustr_cons_join γd dqr ar 0 fr Hfr0 Hrlen with "Hr0 Hre1") as "Hre".
          iApply ("Htail" $! h13 m8 with "Hre Htx [] [] [] Hrun").
          -- iPureIntro. rewrite /m8; rgl.
             change (map fr (seq 0 1)) with [fr 0%nat].
             rewrite mh_one Edol (ustr_hd_eqb0 lt ft Htne).
             destruct lt; reflexivity.
          -- iPureIntro. rewrite /m8 /m7. rk.
          -- iPureIntro. rewrite /m8 /m7; rgl. exact Hsp6.
        * (* re = [c], c <> '$': the literal arm *)
          pcn.
          iApply (wp_kgrep_mh_lit 0 (IHall 0%nat ltac:(lia))
                    h10 m6 dqr dqt ar ax lt (fr 0%nat) (fun j => fr (S j)) ft n1
                    ltac:(rewrite /m6; rgl; first [ reflexivity | assumption ])
                    ltac:(rewrite /m6; rgl; first [ reflexivity | assumption ])
                    ltac:(rewrite /m6; rgl; first [ reflexivity | assumption ])
                    ltac:(cbn; lia)
                    with "Hcode Hre1 Htx Hrun").
          iIntros "Hre1 Htx" (h11 mc) "%Ha0c %Hkc Hrun".
          iDestruct (ustr_cons_join γd dqr ar 0 fr Hfr0 Hrlen with "Hr0 Hre1") as "Hre".
          iApply ("Htail" $! h11 mc with "Hre Htx [] [] [] Hrun").
          -- iPureIntro. rewrite Ha0c. rewrite (map_seq_S fr 0).
             rewrite (mh_lit_case (fr 0%nat) (map (fun j => fr (S j)) (seq 0 0))
                        (map ft (seq 0 lt)) Edol). reflexivity.
          -- iPureIntro. eapply rkeep_trans; [ exact Hk6 | ].
             refine (rkeep_weaken_dec _ _ _ _ _ Hkc); vm_compute; reflexivity.
          -- iPureIntro. rewrite (Hkc csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp6.
      + (* ---------- re[1] is a body byte, not '*': the literal arm ---------- *)
        cbn [ustr_hd] in Estar.
        assert (Hf1 : fr 1%nat <> ubyte0) by (apply Hrne; lia).
        cbn [ustr_hd].
        rewrite (bool_decide_eq_false_2 _ Hf1). cbn [negb].
        assert (Hcond : match map (fun j => fr (S j)) (seq 0 (S lr1')) with
                        | s :: _ => GrepTree.bdec s GrepTree.c_star = false
                        | [] => GrepTree.bdec (fr 0%nat) GrepTree.c_dollar = false
                        end) by (rewrite map_seq_S; exact Estar).
        assert (Hcond' : match map (fun j => fr (S j)) (seq 0 (S lr1')) with
                         | s :: _ => GrepTree.bdec s GrepTree.c_star = false
                         | [] => True
                         end) by (rewrite map_seq_S; exact Estar).
        assert (Hnl : (mh_words (map (fun j => fr (S j)) (seq 0 (S lr1'))) <= n1)%nat).
        { rewrite (map_seq_S fr (S lr1')) in Hn.
          rewrite (mh_words_lit (fr 0%nat) (map (fun j => fr (S j)) (seq 0 (S lr1'))) Hcond') in Hn. lia. }
        iApply (wp_kgrep_mh_lit (S lr1') (IHall (S lr1') ltac:(lia))
                  h8 m5 dqr dqt ar ax lt (fr 0%nat) (fun j => fr (S j)) ft n1
                  Ha45 Ha55 Ha15 Hnl
                  with "Hcode Hre1 Htx Hrun").
        iIntros "Hre1 Htx" (h9 mc) "%Ha0c %Hkc Hrun".
        iDestruct (ustr_cons_join γd dqr ar (S lr1') fr Hfr0 Hrlen with "Hr0 Hre1") as "Hre".
        iApply ("Htail" $! h9 mc with "Hre Htx [] [] [] Hrun").
        * iPureIntro. rewrite Ha0c. rewrite (map_seq_S fr (S lr1')).
          rewrite (mh_lit_case (fr 0%nat) (map (fun j => fr (S j)) (seq 0 (S lr1')))
                   (map ft (seq 0 lt)) Hcond). reflexivity.
        * iPureIntro. eapply rkeep_trans; [ exact Hk5 | ].
          refine (rkeep_weaken_dec _ _ _ _ _ Hkc); vm_compute; reflexivity.
        * iPureIntro. rewrite (Hkc csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp5.
  Qed.

  Lemma mh_all (lr : nat) : mh_spec lr.
  Proof using .
    induction lr as [lr IH] using lt_wf_ind. apply mh_step. exact IH.
  Qed.

  (* ===================================================================== *)
  (* matchhere(re, text) -- the contract.                                   *)
  (*                                                                        *)
  (* Both strings are [ustr]s at the caller's fractions and come back       *)
  (* untouched; the answer is the pure matcher's on the two byte lists; the *)
  (* free stack must hold the pattern's need ([mh_words]) and is handed     *)
  (* back at the same count.                                               *)
  (* ===================================================================== *)
  Lemma wp_kgrep_matchhere (h : CpuId) (m : regfile) (dqr dqt : dfrac) (ar ax : Z)
      (lr lt : nat) (fr ft : nat -> bv 8) (n : nat) :
    m !!! Regidx a0_idx = mword_of_int ar ->
    m !!! Regidx a1_idx = mword_of_int ax ->
    (mh_words (map fr (seq 0 lr)) <= n)%nat ->
    grep_code γt -∗
    ustr γd dqr ar lr fr -∗
    ustr γd dqt ax lt ft -∗
    urun N h m (mword_of_int GrepSyms.matchhere) n -∗
    (ustr γd dqr ar lr fr -∗
     ustr γd dqt ax lt ft -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx
           = mword_of_int (if GrepTree.matchhere (map fr (seq 0 lr)) (map ft (seq 0 lt))
                           then 1 else 0) ⌝ -∗
         urun N h' m' (ret_pc (m !!! Regidx ra_idx)) n -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Ha1 Hn. iIntros "Hcode Hre Htx Hrun Hcont".
    iApply (mh_all lr h m dqr dqt ar ax lt fr ft n Ha0 Ha1 Hn
              with "Hcode Hre Htx Hrun Hcont").
  Qed.

  (* ===================================================================== *)
  (* matchstar(c, re, text) -- the contract.  [c] arrives as the byte's     *)
  (* value in a0 (the C's [int c], from an unsigned [char]); the need is    *)
  (* matchstar's own six words over matchhere's at [re] ([ms_words]).       *)
  (* ===================================================================== *)
  Lemma wp_kgrep_matchstar (h : CpuId) (m : regfile) (c : bv 8) (dqr dqt : dfrac)
      (ar ax : Z) (lr lt : nat) (fr ft : nat -> bv 8) (n : nat) :
    m !!! Regidx a0_idx = mword_of_int (bv_unsigned c) ->
    m !!! Regidx a1_idx = mword_of_int ar ->
    m !!! Regidx a2_idx = mword_of_int ax ->
    (ms_words (map fr (seq 0 lr)) <= n)%nat ->
    grep_code γt -∗
    ustr γd dqr ar lr fr -∗
    ustr γd dqt ax lt ft -∗
    urun N h m (mword_of_int GrepSyms.matchstar) n -∗
    (ustr γd dqr ar lr fr -∗
     ustr γd dqt ax lt ft -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx
           = mword_of_int (if GrepTree.matchstar c (map fr (seq 0 lr)) (map ft (seq 0 lt))
                           then 1 else 0) ⌝ -∗
         urun N h' m' (ret_pc (m !!! Regidx ra_idx)) n -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Ha1 Ha2 Hn. iIntros "Hcode Hre Htx Hrun Hcont".
    iApply (ms_of_mh lr (mh_all lr) h m c dqr dqt ar ax lt fr ft n Ha0 Ha1 Ha2 Hn
              with "Hcode Hre Htx Hrun Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* match's LOOP, 0xce..0xea -- [do { if (matchhere(re, text)) return 1; *)
  (* } while ( *text++ != 0)]:                                           *)
  (*   c.mv a1,s1 ; c.mv a0,s2 ; jal matchhere ; c.bnez a0,0xea ;        *)
  (*   c.addi s1,s1,1 ; lbu a5,-1(s1) ; c.bnez a5,0xce ; c.j 0xec        *)
  (*   (0xea: c.li a0,1)                                                 *)
  (* s1 is the text still to try, s2 the pattern.  By induction on the   *)
  (* text left.                                                         *)
  (* ------------------------------------------------------------------- *)
  Local Lemma wp_kgrep_ma_loop (lr : nat) :
    forall (lt : nat) (h : CpuId) (mc : regfile) (dqr dqt : dfrac)
           (ar ax : Z) (fr ft : nat -> bv 8) (n : nat),
    mc !!! Regidx s1_idx = mword_of_int ax ->
    mc !!! Regidx s2_idx = mword_of_int ar ->
    (mh_words (map fr (seq 0 lr)) <= n)%nat ->
    grep_code γt -∗
    ustr γd dqr ar lr fr -∗
    ustr γd dqt ax lt ft -∗
    urun N h mc (mword_of_int 0xce) n -∗
    (ustr γd dqr ar lr fr -∗
     ustr γd dqt ax lt ft -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ mc' !!! Regidx a0_idx
           = mword_of_int (if GrepTree.match_any (map fr (seq 0 lr)) (map ft (seq 0 lt))
                           then 1 else 0) ⌝ -∗
         ⌜ rkeep (9 :: Wcaller) mc mc' ⌝ -∗
         urun N h' mc' (mword_of_int 0xec) n -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros lt. induction lt as [lt IHt] using lt_wf_ind.
    intros h mc dqr dqt ar ax fr ft n Hs1 Hs2 Hn.
    iIntros "#Hcode Hre Htx Hrun Hcont".
    iDestruct (urun_ustr_bnd with "Hrun Htx") as %[Hax0 Hax38].
    change (2 ^ 38) with 274877906944 in Hax38.
    iDestruct (ustr_nonul with "Htx") as %Htne.
    iDestruct (ustr_len with "Htx") as %Htlen.
    (* ---- 0xce  c.mv a1,s1 ; 0xd0  c.mv a0,s2 ---- *)
    iApply (wp_uk_cmv N h mc (mword_of_int 0xce) a1_idx s1_idx (mword_of_int ax) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_ce with "Hcode"). }
    iIntros (h1) "Hrun". pcn.
    set (m1 := <[Regidx a1_idx := regval_into_reg (mword_of_int ax : mword 64)]> mc).
    iApply (wp_uk_cmv N h1 m1 (mword_of_int 0xd0) a0_idx s2_idx (mword_of_int ar) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m1; rgl; rewrite Hs2 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_d0 with "Hcode"). }
    iIntros (h2) "Hrun". pcn.
    set (m2 := <[Regidx a0_idx := regval_into_reg (mword_of_int ar : mword 64)]> m1).
    (* ---- 0xd2  jal matchhere ---- *)
    iApply (wp_uk_jal N h2 m2 (mword_of_int 0xd2)
              (mword_of_int 2097018 : mword 21) ra_idx
              (mword_of_int GrepSyms.matchhere) (mword_of_int 0xd6) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /GrepSyms.matchhere; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite /GrepSyms.matchhere; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_d2 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx ra_idx := regval_into_reg (mword_of_int 0xd6 : mword 64)]> m2).
    iApply (wp_kgrep_matchhere h3 m3 dqr dqt ar ax lr lt fr ft n
              ltac:(rewrite /m3 /m2; rgl; reflexivity)
              ltac:(rewrite /m3 /m2 /m1; rgl; reflexivity)
              Hn
              with "Hcode Hre Htx Hrun").
    iIntros "Hre Htx" (h4 m4) "%Hcs4 %Ha04 Hrun".
    assert (Eret : ret_pc (m3 !!! Regidx ra_idx) = (mword_of_int 0xd6 : mword 64))
      by (rewrite /m3; rgl; apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    assert (Hk4 : rkeep (9 :: Wcaller) mc m4).
    { eapply (rkeep_call (9 :: Wcaller) mc m3 m4 (rin_caller [9])); [ | exact Hcs4 ].
      rewrite /m3 /m2 /m1. rk. }
    assert (Hs14 : m4 !!! Regidx s1_idx = mword_of_int ax)
      by (rewrite (Hcs4 s1_idx ltac:(vm_compute; reflexivity)) /m3 /m2 /m1; rgl; exact Hs1).
    assert (Hs24 : m4 !!! Regidx s2_idx = mword_of_int ar)
      by (rewrite (Hcs4 s2_idx ltac:(vm_compute; reflexivity)) /m3 /m2 /m1; rgl; exact Hs2).
    (* ---- 0xd6  c.bnez a0,0xea ---- *)
    iApply (wp_uk_cbnez N h4 m4 (mword_of_int 0xd6)
              (mword_of_int 10 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              (GrepTree.matchhere (map fr (seq 0 lr)) (map ft (seq 0 lt))) (mword_of_int 0xea) n
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha04 moi_b01_neqz; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_d6 with "Hcode"). }
    iIntros (h5) "Hrun".
    destruct (GrepTree.matchhere (map fr (seq 0 lr)) (map ft (seq 0 lt))) eqn:Ebh.
    { (* matchhere(re, text) held: 1 *)
      (* ---- 0xea  c.li a0,1 ---- *)
      iApply (wp_uk_cli N h5 m4 (mword_of_int 0xea)
                (mword_of_int 1 : mword 6) a0_idx n
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) with "[] Hrun").
      { iApply (uis_grep_ea with "Hcode"). }
      iIntros (h6) "Hrun". pcn.
      iApply ("Hcont" with "Hre Htx [] [] Hrun").
      - iPureIntro. rgl.
        assert (Hma : GrepTree.match_any (map fr (seq 0 lr)) (map ft (seq 0 lt)) = true).
        { destruct lt as [| lt1].
          - rewrite ma_nil. exact Ebh.
          - rewrite map_seq_S ma_cons. rewrite map_seq_S in Ebh. rewrite Ebh. reflexivity. }
        rewrite Hma. apply bv_eq; vm_compute; reflexivity.
      - iPureIntro. rk. }
    pcn.
    (* ---- 0xd8  c.addi s1,s1,1 ---- *)
    iApply (wp_uk_caddi N h5 m4 (mword_of_int 0xd8)
              (mword_of_int 1 : mword 6) s1_idx (mword_of_int (ax + 1)) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs14;
                    replace (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                      with (mword_of_int 1 : mword 64)
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite moi_add; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_d8 with "Hcode"). }
    iIntros (h6) "Hrun". pcn.
    set (m5 := <[Regidx s1_idx := regval_into_reg (mword_of_int (ax + 1) : mword 64)]> m4).
    (* ---- 0xda  lbu a5,-1(s1) -- the byte just passed ---- *)
    assert (Hux1 : uint (mword_of_int (ax + 1) : mword 64) = ax + 1)
      by (apply uint_moi; unfold Z64; lia).
    assert (Eoffm1 : uoff_i12 (mword_of_int 4095 : mword 12) = -1) by (vm_compute; reflexivity).
    iDestruct (ustr_hd_acc with "Htx") as "[Hb Hcl]".
    iApply (wp_uk_lbu N h6 m5 (mword_of_int 0xda)
              (mword_of_int 4095 : mword 12) s1_idx a5_idx dqt ax (ustr_hd lt ft) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite /m5; rgl; rewrite Hux1 Eoffm1; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_grep_da with "Hcode"). }
    iIntros "Hb" (h7) "Hrun". pcn.
    iDestruct ("Hcl" with "Hb") as "Htx".
    set (m6 := <[Regidx a5_idx := regval_into_reg (zero_extend' 64 (ustr_hd lt ft : mword 8) : mword 64)]> m5).
    assert (Ha56 : m6 !!! Regidx a5_idx = mword_of_int (bv_unsigned (ustr_hd lt ft)))
      by (rewrite /m6; rgl; apply zext8_byte).
    assert (Hk6 : rkeep (9 :: Wcaller) mc m6) by (rewrite /m6 /m5; rk).
    (* ---- 0xde  c.bnez a5,0xce ---- *)
    iApply (wp_uk_cbnez N h7 m6 (mword_of_int 0xde)
              (mword_of_int 248 : mword 8) (mword_of_int 7 : mword 3) a5_idx
              (negb (bool_decide (ustr_hd lt ft = ubyte0))) (mword_of_int 0xce) n
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha56 moi_byte_neqz; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_de with "Hcode"). }
    iIntros (h8) "Hrun".
    destruct lt as [| lt1].
    { (* the text is used up: 0 *)
      rewrite (bool_decide_eq_true_2 _ (eq_refl : ustr_hd 0 ft = ubyte0)).
      cbn [negb]. pcn.
      (* ---- 0xe0  c.j 0xec ---- *)
      iApply (wp_uk_cj N h8 m6 (mword_of_int 0xe0)
                (mword_of_int 6 : mword 11) (mword_of_int 0xec) n
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_e0 with "Hcode"). }
      iIntros (h9) "Hrun".
      iApply ("Hcont" with "Hre Htx [] [] Hrun").
      - iPureIntro. rewrite /m6 /m5; rgl. rewrite Ha04 ma_nil.
        rewrite (_ : GrepTree.matchhere (map fr (seq 0 lr)) [] = false); [ reflexivity | exact Ebh ].
      - iPureIntro. exact Hk6. }
    assert (Hft0 : ft 0%nat <> ubyte0) by (apply Htne; lia).
    cbn [ustr_hd].
    rewrite (bool_decide_eq_false_2 _ Hft0). cbn [negb].
    (* the next round, at [text + 1] *)
    iDestruct (ustr_cons_split with "Htx") as "[Ht0 Htx]".
    iApply (IHt lt1 ltac:(lia) h8 m6 dqr dqt ar (ax + 1) fr (fun j => ft (S j)) n
              ltac:(rewrite /m6 /m5; rgl; reflexivity)
              ltac:(rewrite /m6 /m5; rgl; exact Hs24)
              Hn
              with "Hcode Hre Htx Hrun").
    iIntros "Hre Htx" (h9 mc') "%Ha0x %Hkx Hrun".
    iDestruct (ustr_cons_join with "Ht0 Htx") as "Htx"; [ exact Hft0 | exact Htlen | ].
    iApply ("Hcont" with "Hre Htx [] [] Hrun").
    - iPureIntro. rewrite Ha0x. rewrite (map_seq_S ft lt1) ma_cons.
      rewrite (map_seq_S ft lt1) in Ebh. rewrite Ebh. reflexivity.
    - iPureIntro. exact (rkeep_trans _ _ _ _ Hk6 Hkx).
  Qed.

  (* ===================================================================== *)
  (* match(re, text) -- the contract.  A leading '^' anchors the pattern    *)
  (* (one call of matchhere at [re+1]); otherwise every suffix of the text  *)
  (* is tried, the empty one last.  The frame is four words, so the need    *)
  (* is those four over matchhere's at the pattern matchhere is handed.     *)
  (* ===================================================================== *)
  Lemma wp_kgrep_match (h : CpuId) (m : regfile) (dqr dqt : dfrac) (ar ax : Z)
      (lr lt : nat) (fr ft : nat -> bv 8) (n : nat) :
    m !!! Regidx a0_idx = mword_of_int ar ->
    m !!! Regidx a1_idx = mword_of_int ax ->
    (4 + mh_words (match map fr (seq 0 lr) with
                   | c :: r => if GrepTree.bdec c GrepTree.c_caret then r else c :: r
                   | [] => []
                   end) <= n)%nat ->
    grep_code γt -∗
    ustr γd dqr ar lr fr -∗
    ustr γd dqt ax lt ft -∗
    urun N h m (mword_of_int GrepSyms.match_) n -∗
    (ustr γd dqr ar lr fr -∗
     ustr γd dqt ax lt ft -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx
           = mword_of_int (if GrepTree.match_re (map fr (seq 0 lr)) (map ft (seq 0 lt))
                           then 1 else 0) ⌝ -∗
         urun N h' m' (ret_pc (m !!! Regidx ra_idx)) n -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Ha1 Hn. iIntros "#Hcode Hre Htx Hrun Hcont".
    iDestruct (urun_ustr_bnd with "Hrun Hre") as %[Har0 Har38].
    change (2 ^ 38) with 274877906944 in Har38.
    iDestruct (ustr_nonul with "Hre") as %Hrne.
    iDestruct (ustr_len with "Hre") as %Hrlen.
    replace n with (4 + (n - 4))%nat by lia.
    remember (n - 4)%nat as n1 eqn:En1.
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    assert (Hlo : 32 <= uint sp0) by lia.
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                   = bv_unsigned sp0 - 32).
    { replace (- (8 * Z.of_nat 4)) with (-32) by lia.
      exact (uv_avi_neg sp0 32 ltac:(lia) ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp32 : uint (add_vec_int sp0 (- (8 * Z.of_nat 4))) = uint sp0 - 32)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Ho24 : uoff_sdsp (mword_of_int 3 : mword 6) = 24) by (vm_compute; reflexivity).
    assert (Ho16 : uoff_sdsp (mword_of_int 2 : mword 6) = 16) by (vm_compute; reflexivity).
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8) by (vm_compute; reflexivity).
    assert (Ho0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0) by (vm_compute; reflexivity).
    assert (Hur : uint (mword_of_int ar : mword 64) = ar) by (apply uint_moi; unfold Z64; lia).
    assert (Eoff0 : uoff_i12 (mword_of_int 0 : mword 12) = 0) by (vm_compute; reflexivity).
    rewrite /GrepSyms.match_.
    (* ---- 0xb2  c.addi sp,sp,-32 -- THE PUSH ---- *)
    iApply (wp_uk_caddi_sp_dn N h m (mword_of_int 0xb2) (mword_of_int 32 : mword 6) 4 n1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_b2 with "Hcode"). }
    rewrite Hsp. iIntros "Hst" (h1) "Hrun". pcn.
    iDestruct (ustack_4_open with "Hst")
      as "(_ & [%w1 Hw1] & [%w2 Hw2] & [%w3 Hw3] & [%w4 Hw4])".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 4)))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 4)))
      by (rewrite /m1; rgl; reflexivity).
    assert (Hra1 : m1 !!! Regidx ra_idx = m !!! Regidx ra_idx) by (rewrite /m1; rgl; reflexivity).
    assert (Hs01 : m1 !!! Regidx s0_idx = m !!! Regidx s0_idx) by (rewrite /m1; rgl; reflexivity).
    assert (Hs11 : m1 !!! Regidx s1_idx = m !!! Regidx s1_idx) by (rewrite /m1; rgl; reflexivity).
    assert (Hs21 : m1 !!! Regidx s2_idx = m !!! Regidx s2_idx) by (rewrite /m1; rgl; reflexivity).
    (* ---- 0xb4..0xba  the four spills ---- *)
    iApply (wp_uk_csdsp N h1 m1 (mword_of_int 0xb4) (mword_of_int 3 : mword 6) ra_idx
              (uint sp0 - 8) w1 n1
              ltac:(rewrite Hsp1 Hsp32 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw1 Hrun").
    { iApply (uis_grep_b4 with "Hcode"). }
    iIntros "Hw1" (h2) "Hrun". pcn.
    iApply (wp_uk_csdsp N h2 m1 (mword_of_int 0xb6) (mword_of_int 2 : mword 6) s0_idx
              (uint sp0 - 16) w2 n1
              ltac:(rewrite Hsp1 Hsp32 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw2 Hrun").
    { iApply (uis_grep_b6 with "Hcode"). }
    iIntros "Hw2" (h3) "Hrun". pcn.
    iApply (wp_uk_csdsp N h3 m1 (mword_of_int 0xb8) (mword_of_int 1 : mword 6) s1_idx
              (uint sp0 - 24) w3 n1
              ltac:(rewrite Hsp1 Hsp32 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw3 Hrun").
    { iApply (uis_grep_b8 with "Hcode"). }
    iIntros "Hw3" (h4) "Hrun". pcn.
    iApply (wp_uk_csdsp N h4 m1 (mword_of_int 0xba) (mword_of_int 0 : mword 6) s2_idx
              (uint sp0 - 32) w4 n1
              ltac:(rewrite Hsp1 Hsp32 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw4 Hrun").
    { iApply (uis_grep_ba with "Hcode"). }
    iIntros "Hw4" (h5) "Hrun". pcn.
    rewrite Hra1 Hs01 Hs11 Hs21.
    (* ---- 0xbc  c.addi4spn s0,sp,32 ---- *)
    iApply (wp_uk_caddi4spn N h5 m1 (mword_of_int 0xbc)
              (mword_of_int 0 : mword 3) (mword_of_int 8 : mword 8) s0_idx
              (add_vec (m1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8)))) n1
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_bc with "Hcode"). }
    iIntros (h6) "Hrun". pcn.
    set (m2 := <[Regidx s0_idx := regval_into_reg
                   (add_vec (m1 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> m1).
    (* ---- 0xbe  c.mv s2,a0 ; 0xc0  c.mv s1,a1 ---- *)
    iApply (wp_uk_cmv N h6 m2 (mword_of_int 0xbe) s2_idx a0_idx (mword_of_int ar) n1
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m2 /m1; rgl; rewrite Ha0 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_be with "Hcode"). }
    iIntros (h7) "Hrun". pcn.
    set (m3 := <[Regidx s2_idx := regval_into_reg (mword_of_int ar : mword 64)]> m2).
    iApply (wp_uk_cmv N h7 m3 (mword_of_int 0xc0) s1_idx a1_idx (mword_of_int ax) n1
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite /m3 /m2 /m1; rgl; rewrite Ha1 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_c0 with "Hcode"). }
    iIntros (h8) "Hrun". pcn.
    set (m4 := <[Regidx s1_idx := regval_into_reg (mword_of_int ax : mword 64)]> m3).
    (* ---- 0xc2  lbu a4,0(a0) -- re[0] ---- *)
    iDestruct (ustr_hd_acc with "Hre") as "[Hb Hcl]".
    iApply (wp_uk_lbu N h8 m4 (mword_of_int 0xc2)
              (mword_of_int 0 : mword 12) a0_idx a4_idx dqr ar (ustr_hd lr fr) n1
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite /m4 /m3 /m2 /m1; rgl; rewrite Ha0 Hur Eoff0; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_grep_c2 with "Hcode"). }
    iIntros "Hb" (h9) "Hrun". pcn.
    iDestruct ("Hcl" with "Hb") as "Hre".
    set (m5 := <[Regidx a4_idx := regval_into_reg (zero_extend' 64 (ustr_hd lr fr : mword 8) : mword 64)]> m4).
    (* ---- 0xc6  li a5,94 ---- *)
    iApply (wp_uk_li N h9 m5 (mword_of_int 0xc6)
              (mword_of_int 94 : mword 12) a5_idx (mword_of_int 94) n1
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_c6 with "Hcode"). }
    iIntros (h10) "Hrun". pcn.
    set (m6 := <[Regidx a5_idx := regval_into_reg (mword_of_int 94 : mword 64)]> m5).
    set (W := [2; 8; 9; 18] ++ Wcaller).
    assert (Hk6 : rkeep W m m6) by (rewrite /m6 /m5 /m4 /m3 /m2 /m1; rk).
    assert (Hsp6 : m6 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 4)))
      by (rewrite /m6 /m5 /m4 /m3 /m2; rgl; exact Hsp1).
    (* THE EPILOGUE at 0xec, shared by both arms *)
    iAssert (∀ (h' : CpuId) (mc : regfile),
               ustr γd dqr ar lr fr -∗
               ustr γd dqt ax lt ft -∗
               ⌜ mc !!! Regidx a0_idx
                 = mword_of_int (if GrepTree.match_re (map fr (seq 0 lr)) (map ft (seq 0 lt))
                                 then 1 else 0) ⌝ -∗
               ⌜ rkeep (9 :: Wcaller) m6 mc ⌝ -∗
               urun N h' mc (mword_of_int 0xec) n1 -∗
               mWP (Loop : expr riscv_lang))%I
      with "[Hw1 Hw2 Hw3 Hw4 Hcont]" as "Htail".
    { iIntros (h' mc) "Hre Htx %Ha0c %Hkc Hrun".
      assert (Hspc : mc !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 4)))
        by (rewrite (Hkc csp_rs1 ltac:(vm_compute; reflexivity)); exact Hsp6).
      (* ---- 0xec..0xf2  the four reloads ---- *)
      iApply (wp_uk_cldsp N h' mc (mword_of_int 0xec) (mword_of_int 3 : mword 6) ra_idx
                (uint sp0 - 8) (m !!! Regidx ra_idx) n1
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Hspc Hsp32 Ho24; lia)
                ltac:(rewrite Zminus_mod Hal8; reflexivity)
                ltac:(vm_compute; discriminate)
                with "[] Hw1 Hrun").
      { iApply (uis_grep_ec with "Hcode"). }
      iIntros "Hw1" (h11) "Hrun". pcn.
      set (mc1 := <[Regidx ra_idx := regval_into_reg (m !!! Regidx ra_idx)]> mc).
      iApply (wp_uk_cldsp N h11 mc1 (mword_of_int 0xee) (mword_of_int 2 : mword 6) s0_idx
                (uint sp0 - 16) (m !!! Regidx s0_idx) n1
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite /mc1; rgl; rewrite Hspc Hsp32 Ho16; lia)
                ltac:(rewrite Zminus_mod Hal8; reflexivity)
                ltac:(vm_compute; discriminate)
                with "[] Hw2 Hrun").
      { iApply (uis_grep_ee with "Hcode"). }
      iIntros "Hw2" (h12) "Hrun". pcn.
      set (mc2 := <[Regidx s0_idx := regval_into_reg (m !!! Regidx s0_idx)]> mc1).
      iApply (wp_uk_cldsp N h12 mc2 (mword_of_int 0xf0) (mword_of_int 1 : mword 6) s1_idx
                (uint sp0 - 24) (m !!! Regidx s1_idx) n1
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite /mc2 /mc1; rgl; rewrite Hspc Hsp32 Ho8; lia)
                ltac:(rewrite Zminus_mod Hal8; reflexivity)
                ltac:(vm_compute; discriminate)
                with "[] Hw3 Hrun").
      { iApply (uis_grep_f0 with "Hcode"). }
      iIntros "Hw3" (h13) "Hrun". pcn.
      set (mc3 := <[Regidx s1_idx := regval_into_reg (m !!! Regidx s1_idx)]> mc2).
      iApply (wp_uk_cldsp N h13 mc3 (mword_of_int 0xf2) (mword_of_int 0 : mword 6) s2_idx
                (uint sp0 - 32) (m !!! Regidx s2_idx) n1
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite /mc3 /mc2 /mc1; rgl; rewrite Hspc Hsp32 Ho0; lia)
                ltac:(rewrite Zminus_mod Hal8; reflexivity)
                ltac:(vm_compute; discriminate)
                with "[] Hw4 Hrun").
      { iApply (uis_grep_f2 with "Hcode"). }
      iIntros "Hw4" (h14) "Hrun". pcn.
      set (mc4 := <[Regidx s2_idx := regval_into_reg (m !!! Regidx s2_idx)]> mc3).
      assert (Hsp4 : mc4 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 4)))
        by (rewrite /mc4 /mc3 /mc2 /mc1; rgl; exact Hspc).
      (* ---- 0xf4  c.addi16sp sp,sp,32 -- THE POP ---- *)
      assert (HR : 0 <= bv_unsigned sp0 < 18446744073709551616).
      { pose proof (bv_unsigned_in_range 64 sp0) as H0.
        assert (Em : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
        rewrite Em in H0. exact H0. }
      assert (Hd4 : 0 <= 8 * Z.of_nat 4) by lia.
      assert (Hlt4 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 4))) + 8 * Z.of_nat 4 < Z64)
        by (rewrite Hbsp; unfold Z64; lia).
      assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 4))) (8 * Z.of_nat 4) = sp0).
      { apply bv_eq.
        rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 4))) (8 * Z.of_nat 4) Hd4 Hlt4).
        rewrite Hbsp. lia. }
      iApply (wp_uk_caddi16sp_up N h14 mc4 (mword_of_int 0xf4) (mword_of_int 2 : mword 6) 4 n1
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "[] [Hw1 Hw2 Hw3 Hw4] Hrun").
      { iApply (uis_grep_f4 with "Hcode"). }
      { rewrite Hsp4 Hup.
        iApply (ustack_4_close with "[Hw1] [Hw2] [Hw3] [Hw4]"); [ exact Hal8 | .. ];
          iExists _; iFrame. }
      rewrite Hsp4 Hup. iIntros (h15) "Hrun". pcn.
      set (mc5 := <[Regidx csp_rs1 := regval_into_reg sp0]> mc4).
      (* ---- 0xf6  c.jr ra ---- *)
      iApply (wp_uk_cjr N h15 mc5 (mword_of_int 0xf6) ra_idx (ret_pc (m !!! Regidx ra_idx)) (4 + n1)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /mc5 /mc4 /mc3 /mc2 /mc1; rgl; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_f6 with "Hcode"). }
      iIntros (h16) "Hrun".
      iApply ("Hcont" with "Hre Htx [] [] Hrun").
      - iPureIntro.
        assert (Hkmc : rkeep W mc mc5) by (rewrite /mc5 /mc4 /mc3 /mc2 /mc1; rk).
        assert (Hkc' : rkeep W m6 mc)
          by (refine (rkeep_weaken_dec _ _ _ _ _ Hkc); vm_compute; reflexivity).
        apply (rkeep_ucs_dec W [2; 8; 9; 18] m mc5 ltac:(vm_compute; reflexivity)
                 (rkeep_trans _ _ _ _ (rkeep_trans _ _ _ _ Hk6 Hkc') Hkmc)).
        intros z Hz.
        destruct Hz as [<- | [<- | [<- | [<- | []]]]];
          try change (Regidx (mword_of_int 2)) with (Regidx csp_rs1);
          rewrite /mc5 /mc4 /mc3 /mc2 /mc1; rgl; first [ reflexivity | symmetry; exact Hsp ].
      - iPureIntro. rewrite /mc5 /mc4 /mc3 /mc2 /mc1. rgl. exact Ha0c. }
    (* ---- 0xca  beq a4,a5,0xe2 -- re[0] == '^' ---- *)
    assert (Hbeq : uv_btaken BEQ (m6 !!! Regidx a4_idx) (m6 !!! Regidx a5_idx)
                   = GrepTree.bdec (ustr_hd lr fr) GrepTree.c_caret).
    { cbn [uv_btaken]. rewrite /m6 /m5. rgl. rewrite zext8_byte.
      pose proof (byte_range (ustr_hd lr fr)).
      rewrite (moi_eq_vec (bv_unsigned (ustr_hd lr fr)) 94
                 ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
      apply bdec_lit. lia. }
    iApply (wp_uk_btype N h10 m6 (mword_of_int 0xca)
              (mword_of_int 24 : mword 13) a5_idx a4_idx BEQ
              (GrepTree.bdec (ustr_hd lr fr) GrepTree.c_caret)
              (mword_of_int 0xe2) n1
              ltac:(rewrite Hbeq; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_ca with "Hcode"). }
    iIntros (h11) "Hrun".
    destruct (GrepTree.bdec (ustr_hd lr fr) GrepTree.c_caret) eqn:Ecar.
    - (* ================= '^': matchhere(re+1, text) ================= *)
      destruct lr as [| lr1].
      { exfalso. cbn [ustr_hd] in Ecar. vm_compute in Ecar. discriminate Ecar. }
      cbn [ustr_hd] in Ecar.
      assert (Hfr0 : fr 0%nat <> ubyte0) by (apply Hrne; lia).
      iDestruct (ustr_cons_split with "Hre") as "[Hr0 Hre1]".
      (* ---- 0xe2  c.addi a0,a0,1 ---- *)
      iApply (wp_uk_caddi N h11 m6 (mword_of_int 0xe2)
                (mword_of_int 1 : mword 6) a0_idx (mword_of_int (ar + 1)) n1
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /m6 /m5 /m4 /m3 /m2 /m1; rgl; rewrite Ha0;
                      replace (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                        with (mword_of_int 1 : mword 64)
                        by (apply bv_eq; vm_compute; reflexivity);
                      rewrite moi_add; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_e2 with "Hcode"). }
      iIntros (h12) "Hrun". pcn.
      set (m7 := <[Regidx a0_idx := regval_into_reg (mword_of_int (ar + 1) : mword 64)]> m6).
      (* ---- 0xe4  jal matchhere ---- *)
      iApply (wp_uk_jal N h12 m7 (mword_of_int 0xe4)
                (mword_of_int 2097000 : mword 21) ra_idx
                (mword_of_int GrepSyms.matchhere) (mword_of_int 0xe8) n1
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite /GrepSyms.matchhere; apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite /GrepSyms.matchhere; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_e4 with "Hcode"). }
      iIntros (h13) "Hrun".
      set (m8 := <[Regidx ra_idx := regval_into_reg (mword_of_int 0xe8 : mword 64)]> m7).
      assert (Hnr : (mh_words (map (fun j => fr (S j)) (seq 0 lr1)) <= n1)%nat).
      { rewrite map_seq_S Ecar in Hn. lia. }
      iApply (wp_kgrep_matchhere h13 m8 dqr dqt (ar + 1) ax lr1 lt (fun j => fr (S j)) ft n1
                ltac:(rewrite /m8; rgl; reflexivity)
                ltac:(rewrite /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1; rgl; exact Ha1)
                Hnr
                with "Hcode Hre1 Htx Hrun").
      iIntros "Hre1 Htx" (h14 m9) "%Hcs9 %Ha09 Hrun".
      assert (Eret : ret_pc (m8 !!! Regidx ra_idx) = (mword_of_int 0xe8 : mword 64))
        by (rewrite /m8; rgl; apply bv_eq; vm_compute; reflexivity).
      rewrite Eret.
      (* ---- 0xe8  c.j 0xec ---- *)
      iApply (wp_uk_cj N h14 m9 (mword_of_int 0xe8)
                (mword_of_int 2 : mword 11) (mword_of_int 0xec) n1
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_grep_e8 with "Hcode"). }
      iIntros (h15) "Hrun".
      iDestruct (ustr_cons_join γd dqr ar lr1 fr Hfr0 Hrlen with "Hr0 Hre1") as "Hre".
      iApply ("Htail" $! h15 m9 with "Hre Htx [] [] Hrun").
      + iPureIntro. rewrite Ha09. rewrite map_seq_S. rewrite /GrepTree.match_re Ecar. reflexivity.
      + iPureIntro. eapply (rkeep_call (9 :: Wcaller) m6 m8 m9 (rin_caller [9])); [ | exact Hcs9 ].
        rewrite /m8 /m7. rk.
    - (* ================= no anchor: every suffix ================= *)
      pcn.
      assert (Hnr : (mh_words (map fr (seq 0 lr)) <= n1)%nat).
      { destruct lr as [| lr1]; [ cbn; lia | ].
        rewrite map_seq_S in Hn |- *. cbn [ustr_hd] in Ecar. rewrite Ecar in Hn. lia. }
      iApply (wp_kgrep_ma_loop lr lt h11 m6 dqr dqt ar ax fr ft n1
                ltac:(rewrite /m6 /m5; rgl; reflexivity)
                ltac:(rewrite /m6 /m5 /m4; rgl; reflexivity)
                Hnr
                with "Hcode Hre Htx Hrun").
      iIntros "Hre Htx" (h12 mc) "%Ha0c %Hkc Hrun".
      iApply ("Htail" $! h12 mc with "Hre Htx [] [] Hrun").
      + iPureIntro. rewrite Ha0c.
        assert (Hmr : GrepTree.match_re (map fr (seq 0 lr)) (map ft (seq 0 lt))
                      = GrepTree.match_any (map fr (seq 0 lr)) (map ft (seq 0 lt))).
        { destruct lr as [| lr1]; [ reflexivity | ].
          rewrite map_seq_S. cbn [ustr_hd] in Ecar. rewrite /GrepTree.match_re Ecar. reflexivity. }
        rewrite Hmr. reflexivity.
      + iPureIntro. exact Hkc.
  Qed.
End UkGrepMatch.
