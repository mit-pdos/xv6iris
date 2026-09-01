(* ===================================================================== *)
(* UkShDiag.v -- sh's DIAGNOSTIC SUBTREE on the urun engine, and the      *)
(* discharge of UkShRun.v's [ush_diag_leaf].                              *)
(*                                                                       *)
(* Three pcs in stage 5's walk hand control to sh's printer and none of   *)
(* them returns: [panic] (0x4a -- from fork1's -1 arm and from PIPE's     *)
(* failing [pipe]), the "exec ... failed" tail at 0xda and the            *)
(* "open ... failed" tail at 0x10e.  Each is                              *)
(*                                                                       *)
(*     fprintf(2, <a format with exactly one %s>, <a C string>); exit(k)  *)
(*                                                                       *)
(* and the cone under [fprintf] is 279 instructions: fprintf (0x10aa, 17) *)
(* marshalling the varargs it will not read, vprintf (0xdea, 250) walking *)
(* the format one byte at a time, and putc (0xd2e, 12) writing each byte  *)
(* with [write(fd,&c,1)].  Above them panic's own 11.                     *)
(*                                                                       *)
(* THE WALK IS UPSTREAM'S, AT SH'S ADDRESSES.  sh and cat contain the     *)
(* SAME ulib printf, and the two images agree on it BYTE FOR BYTE: every  *)
(* instruction of putc, vprintf and fprintf has the same width and the    *)
(* same encoding in both dumps, and sh's copies sit exactly 0x8da above   *)
(* cat's -- so every decoded immediate, every branch displacement and     *)
(* every jal target is identical and only the pcs move.  The two          *)
(* exceptions are the [addi] halves of two [auipc]/[addi] pairs that name *)
(* .rodata ("(null)" and [digits]), and both sit on arms a '%s' format    *)
(* cannot reach.  So §§1-5 below are UkCatLit / UkCatPutc / UkCatVprintf  *)
(* / UkCatVprintfS / UkCatFprintf shifted onto sh's catalog, one section  *)
(* each, with the changes recorded in §0 and §0a.                         *)
(*                                                                       *)
(* §0a IS THE ONE REAL GENERALISATION, and it is what sh needs that cat   *)
(* did not.  cat's only '%s' argument is [argv[i]], a string in the DATA  *)
(* half; sh's [panic] prints a .rodata literal ("fork", "runcmd",         *)
(* "pipe"), which is X-and-not-W and therefore lives in the TEXT half.    *)
(* The walk reads such a string in exactly one way -- one byte at a time  *)
(* at a known index -- so rather than duplicate 2 000 lines of the '%s'   *)
(* arm, [shd_sb] / [shd_str] / [wp_shd_lbu] abstract over WHICH HALF, the *)
(* '%s' section takes the choice as a section variable [tx : bool], and   *)
(* the two callers instantiate it.  [shd_str γt γd false] is [ustr γd     *)
(* DfracDiscarded] and [shd_str γt γd true] is [utext_str γt], both by    *)
(* conversion, so neither producer had to move.                           *)
(*                                                                       *)
(* WHAT THE DISCHARGE COSTS ITS CALLER.  [ush_diag_leaf] as stage 5       *)
(* landed it is NOT dischargeable: it quantifies over the gname triple    *)
(* (a forked child runs the same premise at FRESH gnames) and hands the   *)
(* walk only [shk_code γt], which is [ShInstrs.sh_bytes] -- the           *)
(* instructions.  The format strings are at 0x1290..0x12c7, inside        *)
(* [ShData.sh_data], i.e. [shk_ro], and no amount of [shk_code] produces  *)
(* them.  The fix-forward is one conjunct, threaded exactly where         *)
(* [ush_jtab] already goes: [UkShRun.ush_jtab] now carries [shk_rodata]   *)
(* beside the five jump-table rows, so every site that reaches the        *)
(* printer already holds it and no fork payload, arm lemma or budget      *)
(* moved.  [wp_kshr_fork1] is the one exception -- it has no [ush_jtab]   *)
(* of its own -- and takes [shk_rodata γt] as a premise, forwarding it to *)
(* the child through the payload it already carries.                      *)
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
Require Import RegFile WpGpr.
Require Import AlignBits WpMmodeLeafBase.
Require Import UserBits UserPtTree UserExec ProcPtOwn.
Require Import WpUmodeBranch.
Require Import UmodeMem UmodeFetch UmodeArith UmodeAbi.
Require Import UserPerm UsysMemOk UexecWp UexecSlot UexecRet.
Require Import UkStep.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys UkRunBr.
Require UkLoad.
Require Import UkFork.
Require Import UCodeShK.
Require Import UkSh.
Require Import TsoCtx.
Require User.ShSyms User.ShInstrs.
Require Import UkProgAbi.
Require Import UkShRun.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §0 THE SYMBOL PINS.  [ShSyms.<f>] is a [Definition] holding a literal, *)
(* so each of these is a [reflexivity] -- the same route [UkShRun.v]'s    *)
(* [shr_panic] takes, and it does not move when the catalog's             *)
(* [shk_syms_pins] grows a conjunct.                                     *)
(* ===================================================================== *)
Lemma shd_pin_panic   : ShSyms.panic   = 0x4a.   Proof. reflexivity. Qed.
Lemma shd_pin_putc    : ShSyms.putc    = 0xd2e.  Proof. reflexivity. Qed.
Lemma shd_pin_vprintf : ShSyms.vprintf = 0xdea.  Proof. reflexivity. Qed.
Lemma shd_pin_fprintf : ShSyms.fprintf = 0x10aa. Proof. reflexivity. Qed.
Lemma shd_pin_write   : ShSyms.write   = 0xca6.  Proof. reflexivity. Qed.
Lemma shd_pin_exit    : ShSyms.exit    = 0xc86.  Proof. reflexivity. Qed.

(* ===================================================================== *)
(* §0a A C STRING IN EITHER HALF OF THE HEAP.                             *)
(*                                                                       *)
(* [UserHeap.ustr] is the DATA half's string and [UserHeap.utext_str] the *)
(* TEXT half's; they have the SAME four conjuncts and differ only in      *)
(* which points-to carries a byte.  vprintf's '%s' arm reads its argument *)
(* through exactly one instruction shape ([lbu a1,0(s1)]), so one boolean *)
(* covers both -- and with it the arm is proved once for cat's heap       *)
(* strings and sh's .rodata literals alike.                              *)
(*                                                                       *)
(* NOTE THE SHAPES.  [shd_str_byte] and [shd_str_nul] hand the byte out   *)
(* WITH a closing wand and [wp_shd_lbu] gives its byte back, though both  *)
(* resources are persistent and neither has to: they are stated at        *)
(* [ustr_byte]'s and [wp_uk_lbu]'s shapes so the '%s' walk below is the   *)
(* upstream text with the resource's NAME changed and nothing else.       *)
(* ===================================================================== *)
Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)
Section UkShDiagStr.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.

  Definition shd_sb (γt γd : gname) (tx : bool) (a : Z) (b : bv 8) : iProp Σ :=
    (if tx then utext γt a b else ubyteq γd DfracDiscarded a b)%I.

  Global Instance shd_sb_persistent γt γd tx a b :
    Persistent (shd_sb γt γd tx a b).
  Proof. rewrite /shd_sb. destruct tx; apply _. Qed.

  Definition shd_str (γt γd : gname) (tx : bool) (a : Z) (len : nat)
      (f : nat -> bv 8) : iProp Σ :=
    (⌜ forall j : nat, (j < len)%nat -> f j <> ubyte0 ⌝ ∗
     ⌜ Z.of_nat len < 2 ^ 31 ⌝ ∗
     ([∗ list] j ∈ seq 0 len, shd_sb γt γd tx (a + Z.of_nat j) (f j)) ∗
     shd_sb γt γd tx (a + Z.of_nat len) ubyte0)%I.

  Global Instance shd_str_persistent γt γd tx a len f :
    Persistent (shd_str γt γd tx a len f).
  Proof. apply _. Qed.

  (* the two producers, both by CONVERSION: [ustr]'s [ubytesq] IS the
     big-op this predicate spells, and [utext_str]'s body is the same one
     over [utext] *)
  Lemma shd_str_of_ustr (γt γd : gname) (a : Z) (len : nat) (f : nat -> bv 8) :
    ustr γd DfracDiscarded a len f -∗ shd_str γt γd false a len f.
  Proof. iIntros "H". iExact "H". Qed.

  Lemma shd_str_of_text (γt γd : gname) (a : Z) (len : nat) (f : nat -> bv 8) :
    utext_str γt a len f -∗ shd_str γt γd true a len f.
  Proof. iIntros "H". iExact "H". Qed.

  Lemma shd_str_nonul (γt γd : gname) (tx : bool) (a : Z) (len : nat)
      (f : nat -> bv 8) :
    shd_str γt γd tx a len f -∗
    ⌜ forall j : nat, (j < len)%nat -> f j <> ubyte0 ⌝.
  Proof. iIntros "(%H & _ & _ & _)". iPureIntro. exact H. Qed.

  Lemma shd_str_byte (γt γd : gname) (tx : bool) (a : Z) (len : nat)
      (f : nat -> bv 8) (j : nat) :
    (j < len)%nat ->
    shd_str γt γd tx a len f -∗
      shd_sb γt γd tx (a + Z.of_nat j)%Z (f j) ∗
      (shd_sb γt γd tx (a + Z.of_nat j)%Z (f j) -∗ shd_str γt γd tx a len f).
  Proof.
    (* NOT [iFrame]: [shd_str] is transparent and its LAST conjunct is a
       [shd_sb], so [iFrame] resolves the byte into the copy of [shd_str]
       sitting under the closing wand and leaves a goal that no longer says
       what it should.  Split by hand. *)
    intros Hj. iIntros "#Hs". iSplitR.
    - iDestruct "Hs" as "(_ & _ & Hbs & _)".
      iApply (big_sepL_lookup _ _ j j with "Hbs").
      apply lookup_seq. split; [ lia | exact Hj ].
    - iIntros "_". iExact "Hs".
  Qed.

  Lemma shd_str_nul (γt γd : gname) (tx : bool) (a : Z) (len : nat)
      (f : nat -> bv 8) :
    shd_str γt γd tx a len f -∗
      shd_sb γt γd tx (a + Z.of_nat len)%Z ubyte0 ∗
      (shd_sb γt γd tx (a + Z.of_nat len)%Z ubyte0 -∗ shd_str γt γd tx a len f).
  Proof.
    iIntros "#Hs". iSplitR.
    - iDestruct "Hs" as "(_ & _ & _ & Hn)". iExact "Hn".
    - iIntros "_". iExact "Hs".
  Qed.

  (* the one load, at either half.  Stated at [wp_uk_lbu]'s shape, dfrac
     replaced by the half. *)
  Lemma wp_shd_lbu (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (imm : mword 12) (rs1 rd : mword 5) (tx : bool)
      (a : Z) (b0 : mword 8) (avail : nat) :
    unot_sp rd ->
    a = uint (m !!! Regidx rs1) + uoff_i12 imm ->
    uint rd <> 0 ->
    uinstr_is γt pc false (LOAD (imm, Regidx rs1, Regidx rd, true, 1)) -∗
    shd_sb γt γd tx a b0 -∗
    urun γt γd γs γfd h m pc avail -∗
    (shd_sb γt γd tx a b0 -∗
       ∀ h' : CpuId,
         urun γt γd γs γfd h'
           (<[Regidx rd := regval_into_reg (zero_extend' 64 b0)]> m)
           (add_vec_int pc 4) avail -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hrd Ha Hne. iIntros "#Hi #Hb Hrun Hcont".
    destruct tx.
    - iApply (wp_uk_lbu_text γt γd γs γfd h m pc imm rs1 rd a b0 avail
                Hrd Ha Hne with "Hi Hb Hrun").
      iApply ("Hcont" with "Hb").
    - iApply (wp_uk_lbu γt γd γs γfd h m pc imm rs1 rd DfracDiscarded a b0 avail
                Hrd Ha Hne with "Hi Hb Hrun").
      iExact "Hcont".
  Qed.

  (* the heap's own bounds, read off whichever half the string is in *)
  Lemma urun_shd_sb_bnd (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (tx : bool) (a : Z) (b : bv 8) :
    urun γt γd γs γfd h m pc avail -∗ shd_sb γt γd tx a b -∗ ⌜ 0 <= a < 2 ^ 38 ⌝.
  Proof.
    iIntros "Hrun #Hb".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(_ & _ & Hh & _ & _)".
    destruct tx.
    - iDestruct (uheap_text with "Hh Hb") as %(_ & _ & Hbnd).
      iPureIntro. exact Hbnd.
    - iDestruct (uheap_ubyte with "Hh Hb") as %(_ & _ & Hbnd).
      iPureIntro. exact Hbnd.
  Qed.

  Lemma urun_shd_str_bnd (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (tx : bool) (a : Z) (len : nat)
      (f : nat -> bv 8) :
    urun γt γd γs γfd h m pc avail -∗ shd_str γt γd tx a len f -∗
    ⌜ 0 <= a /\ a + Z.of_nat len < 2 ^ 38 ⌝.
  Proof.
    iIntros "Hrun #Hs".
    iDestruct (shd_str_nul with "Hs") as "[#Hnul _]".
    iDestruct (urun_shd_sb_bnd with "Hrun Hnul") as %Hhi.
    destruct len as [| len' ].
    - iPureIntro. lia.
    - iDestruct (shd_str_byte γt γd tx a (S len') f 0%nat ltac:(lia) with "Hs")
        as "[#Hb0 _]".
      iDestruct (urun_shd_sb_bnd with "Hrun Hb0") as %Hlo.
      iPureIntro. lia.
  Qed.

End UkShDiagStr.
(* ===================================================================== *)
(* §1 A STRING LITERAL WITH NO DIRECTIVE IN IT, cut out of the read-only    *)
(* image at a concrete base and length.  (§6's [shd_fmt_ok] is the same    *)
(* predicate WITHOUT the no-'%' clause, which is what a format needs.)     *)
(*                                                                         *)
(* Everything a caller needs about a literal -- that its body bytes are     *)
(* non-NUL, that none of them is '%', and that a NUL follows -- is DECIDED  *)
(* by [shd_lit_ok], one [vm_compute] per literal.  The alternative is a    *)
(* [destruct j] chain as long as the string at every use site.              *)
(* ===================================================================== *)

Local Open Scope Z_scope.

(* the byte function of the literal based at [base] *)
Definition shd_lit (base : Z) : nat -> mword 8 :=
  fun j => default (bv_0 8) (shk_ro !! (base + Z.of_nat j)%Z).

(* ...and the whole of what makes it a printable C string *)
Definition shd_lit_ok (base : Z) (len : nat) : bool :=
  forallb (fun j => match shk_ro !! (base + Z.of_nat j)%Z with
                    | Some b => negb (Z.eqb (bv_unsigned b) 0)
                                && negb (Z.eqb (bv_unsigned b) 37)
                    | None => false
                    end)
          (seq 0 len)
  && match shk_ro !! (base + Z.of_nat len)%Z with
     | Some b => Z.eqb (bv_unsigned b) 0
     | None => false
     end.

Lemma shd_lit_ok_body (base : Z) (len : nat) (j : nat) :
  shd_lit_ok base len = true -> (j < len)%nat ->
  shk_ro !! (base + Z.of_nat j)%Z = Some (shd_lit base j)
  /\ bv_unsigned (shd_lit base j) <> 0
  /\ bv_unsigned (shd_lit base j) <> 37.
Proof.
  unfold shd_lit_ok, shd_lit. intros H Hj.
  apply andb_true_iff in H as [H _].
  rewrite forallb_forall in H.
  specialize (H j ltac:(apply in_seq; lia)).
  destruct (shk_ro !! (base + Z.of_nat j)%Z) as [b | ] eqn:Hb;
    [ | discriminate ].
  apply andb_true_iff in H as [H0 H37].
  apply negb_true_iff, Z.eqb_neq in H0.
  apply negb_true_iff, Z.eqb_neq in H37.
  cbn [default]. split; [ reflexivity | ]. split; assumption.
Qed.

Lemma shd_lit_ok_nul (base : Z) (len : nat) :
  shd_lit_ok base len = true ->
  shk_ro !! (base + Z.of_nat len)%Z = Some ubyte0.
Proof.
  unfold shd_lit_ok. intro H.
  apply andb_true_iff in H as [_ H].
  destruct (shk_ro !! (base + Z.of_nat len)%Z) as [b | ] eqn:Hb;
    [ | discriminate ].
  apply Z.eqb_eq in H. f_equal. apply bv_eq. rewrite H.
  vm_compute. reflexivity.
Qed.

Section UkShDiagLit.
  Context `{!riscvGS Σ}.

  Context `{!ufdG Σ}.
  (* the literal, as the resource vprintf reads *)
  Lemma shd_lit_str (γt : gname) (base : Z) (len : nat) :
    shd_lit_ok base len = true ->
    Z.of_nat len < 2 ^ 31 ->
    shk_rodata γt -∗ utext_str γt base len (shd_lit base).
  Proof.
    intros Hok Hlen. iIntros "#Hro". rewrite /shk_rodata.
    iApply (utext_str_of_img γt shk_ro base len (shd_lit base)).
    - intros j Hj. intro He.
      destruct (shd_lit_ok_body base len j Hok Hj) as (_ & Hnz & _).
      apply Hnz. rewrite He. vm_compute. reflexivity.
    - exact Hlen.
    - intros j Hj. exact (proj1 (shd_lit_ok_body base len j Hok Hj)).
    - exact (shd_lit_ok_nul base len Hok).
    - iExact "Hro".
  Qed.

  Lemma shd_lit_nopct (base : Z) (len : nat) (j : nat) :
    shd_lit_ok base len = true -> (j < len)%nat ->
    bv_unsigned (shd_lit base j) <> 37.
  Proof.
    intros Hok Hj.
    exact (proj2 (proj2 (shd_lit_ok_body base len j Hok Hj))).
  Qed.

End UkShDiagLit.

(* ===================================================================== *)
(* §2 ulib's [putc(fd, c)], the bottom of sh's fprintf cone.                *)
(* ===================================================================== *)

Section UkShDiagPutc.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context (γt γd γs γfd : gname).

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation s7_idx := (mword_of_int 23 : mword 5).
  Local Notation s8_idx := (mword_of_int 24 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).

  (* ===================================================================== *)
  (* THE PRINTF CONE.  [fprintf(fd,fmt,...)] is [write(fd,c,1)] spelled    *)
  (* out one character at a time: fprintf marshals the varargs, vprintf    *)
  (* walks the format and hands each byte to putc, and putc spills that    *)
  (* byte into its own frame and writes ONE byte.  Nothing in the cone     *)
  (* touches the caller's memory: every store lands in a frame the         *)
  (* function took off the free stack and gave back, and write is the      *)
  (* QUIET row.                                                            *)
  (* ===================================================================== *)

  (* a callee-saved register is none of the ones a caller may clobber *)

  (* --------------------------------------------------------------------- *)
  (* putc(fd, c) @0xd2e -- ulib's one-byte write.                            *)
  (*                                                                        *)
  (*   c.addi sp,sp,-32 ; c.sdsp ra,24(sp) ; c.sdsp s0,16(sp)                *)
  (*   c.addi4spn s0,sp,32 ; sb a1,-17(s0) ; c.li a2,1 ; addi a1,s0,-17      *)
  (*   jal <write> ; c.ldsp ra,24(sp) ; c.ldsp s0,16(sp)                     *)
  (*   c.addi16sp sp,sp,32 ; c.jr ra                                         *)
  (*                                                                        *)
  (* THE BYTE GOES IN THE FRAME.  [sb a1,-17(s0)] with s0 = the entry sp     *)
  (* lands at [sp0-17], which is byte 7 of the frame word at [sp0-24] --     *)
  (* hence the [uword_8] split and the [uword_of_bytes_8] reassembly, and    *)
  (* hence the fact that putc's whole memory effect is INSIDE the four       *)
  (* words it borrowed.  The caller gets its free stack back at the same     *)
  (* [avail] and learns nothing about the frame's contents, which is why     *)
  (* the post is [ucallee_saved] and nothing else.                           *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kshd_putc (h : CpuId) (m : regfile) (n : nat) :
    shk_code γt -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.putc) (4 + n) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ ucallee_saved m m' ⌝ -∗
       urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (4 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun Hcont".
    pose proof shd_pin_putc as Hputc.
    pose proof shd_pin_write as Hwrite.
    rewrite Hputc.
    iDestruct (urun_stack with "Hrun") as %[Hal8' Hroom'].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    assert (Hal8 : uint sp0 mod 8 = 0) by exact Hal8'.
    assert (Hlo : 32 <= uint sp0) by (clear -Hroom'; lia).
    (* the frame's bottom, and the round trip back up *)
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                   = bv_unsigned sp0 - 32).
    { replace (- (8 * Z.of_nat 4)) with (-32) by lia.
      exact (uv_avi_neg sp0 32 ltac:(apply Z.leb_le; reflexivity)
               ltac:(rewrite <- uint_unsigned; exact Hlo)). }
    assert (Hsp32 : uint (add_vec_int sp0 (- (8 * Z.of_nat 4))) = uint sp0 - 32)
      by (rewrite !uint_unsigned; exact Hbsp).
    (* HR IS ITS OWN ASSERT, and [Hlt4]'s [lia] runs under [clear -].  Both
       matter.  [bv_unsigned_in_range 64 sp0] fixes the width index at [64 :
       N] while the goal's [bv_unsigned sp0] carries [sp0]'s own [Z_idx 64]
       -- convertible, but TWO ATOMS to [lia], which is why splicing the
       range in directly makes the goal unprovable rather than slow.  And a
       bare [lia] here reifies the whole [envs_entails Δ Q]: this one ran
       four minutes before failing. *)
    assert (HR : 0 <= bv_unsigned sp0 < 18446744073709551616).
    { pose proof (bv_unsigned_in_range 64 sp0) as H0.
      assert (Em : bv_modulus 64 = 18446744073709551616)
        by (vm_compute; reflexivity).
      rewrite Em in H0. exact H0. }
    assert (Hd4 : (0 <= 8 * Z.of_nat 4)%Z) by (apply Z.leb_le; reflexivity).
    assert (Hlt4 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                   + 8 * Z.of_nat 4 < Z64)
      by (clear -Hbsp HR; rewrite Hbsp; unfold Z64; lia).
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                    (8 * Z.of_nat 4) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                 (8 * Z.of_nat 4) Hd4 Hlt4).
      clear -Hbsp. rewrite Hbsp. lia. }
    assert (Eb7 : (uint sp0 - 17)%Z = (uint sp0 - 24 + 7)%Z) by lia.
    assert (Ho24 : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
      by (vm_compute; reflexivity).
    assert (Ho16 : uoff_sdsp (mword_of_int 2 : mword 6) = 16)
      by (vm_compute; reflexivity).
    (* ---- 0xd2e  c.addi sp,sp,-32 -- THE PUSH ---- *)
    iApply (wp_uk_caddi_sp_dn γt γd γs γfd h m (mword_of_int 0xd2e)
              (mword_of_int 32 : mword 6) 4 n
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_d2e with "Hcode"). }
    iIntros "Hframe".
    assert (E41a : add_vec_int (mword_of_int 0xd2e : mword 64) 2
                   = mword_of_int 0xd30)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp E41a.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 4)))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 4)))
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg _)).
    (* the four words of the frame, by name -- DIRECTED, never [rewrite
       ustack_4]: that fires on the whole [envs_entails Δ Q] *)
    iDestruct (ustack_4_open with "Hframe")
      as "(_ & [%vra Hwra] & [%vs0 Hws0] & [%vb Hwb] & Hw32)".
    (* ---- 0xd30  c.sdsp ra,24(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd h1 m1 (mword_of_int 0xd30)
              (mword_of_int 3 : mword 6) ra_idx (uint sp0 - 8) vra n
              ltac:(rewrite Hsp1 Hsp32 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hwra Hrun").
    { iApply (uis_shk_d30 with "Hcode"). }
    iIntros "Hwra".
    assert (E41c : add_vec_int (mword_of_int 0xd30 : mword 64) 2
                   = mword_of_int 0xd32)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E41c.
    iIntros (h2) "Hrun".
    (* ---- 0xd32  c.sdsp s0,16(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd h2 m1 (mword_of_int 0xd32)
              (mword_of_int 2 : mword 6) s0_idx (uint sp0 - 16) vs0 n
              ltac:(rewrite Hsp1 Hsp32 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hws0 Hrun").
    { iApply (uis_shk_d32 with "Hcode"). }
    iIntros "Hws0".
    assert (E41e : add_vec_int (mword_of_int 0xd32 : mword 64) 2
                   = mword_of_int 0xd34)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E41e.
    iIntros (h3) "Hrun".
    (* the two spilled values, as they will come back out *)
    assert (Hra1 : m1 !!! Regidx ra_idx = m !!! Regidx ra_idx)
      by exact (upd_ne m (Regidx csp_rs1) (Regidx ra_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Hs01 : m1 !!! Regidx s0_idx = m !!! Regidx s0_idx)
      by exact (upd_ne m (Regidx csp_rs1) (Regidx s0_idx) _
                  ltac:(vm_compute; discriminate)).
    (* ---- 0xd34  c.addi4spn s0,sp,32 -- s0 := the ENTRY sp ---- *)
    assert (Ec4 : (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))
                   : mword 64) = mword_of_int (8 * Z.of_nat 4))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi4spn γt γd γs γfd h3 m1 (mword_of_int 0xd34)
              (mword_of_int 0 : mword 3) (mword_of_int 8 : mword 8) s0_idx sp0 n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hsp1 Ec4; exact (eq_sym Hup))
              with "[] Hrun").
    { iApply (uis_shk_d34 with "Hcode"). }
    assert (E420 : add_vec_int (mword_of_int 0xd34 : mword 64) 2
                   = mword_of_int 0xd36)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E420.
    iIntros (h4) "Hrun".
    set (m2 := <[Regidx s0_idx := regval_into_reg sp0]> m1).
    assert (Hs02 : m2 !!! Regidx s0_idx = sp0)
      by exact (upd_eq m1 (Regidx s0_idx) (regval_into_reg sp0)).
    assert (Hsp2 : m2 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite <- Hsp1.
      exact (upd_ne m1 (Regidx s0_idx) (Regidx csp_rs1) (regval_into_reg sp0)
               ltac:(vm_compute; discriminate)). }
    (* ---- 0xd36  sb a1,-17(s0) -- the byte, into BYTE 7 of the third word ---- *)
    assert (Hoff17 : uoff_i12 (mword_of_int 4079 : mword 12) = -17)
      by (vm_compute; reflexivity).
    iDestruct (uword_byte7_acc γd (uint sp0 - 24) (uint sp0 - 17) vb Eb7
                 with "Hwb") as "(Hb7 & Hwbc)".
    iApply (wp_uk_sb γt γd γs γfd h4 m2 (mword_of_int 0xd36)
              (mword_of_int 4079 : mword 12) s0_idx a1_idx
              (uint sp0 - 17) (nth_byte vb 7%nat) n
              ltac:(rewrite Hs02 Hoff17; lia)
              with "[] Hb7 Hrun").
    { iApply (uis_shk_d36 with "Hcode"). }
    iIntros "Hb7".
    assert (E422 : add_vec_int (mword_of_int 0xd36 : mword 64) 4
                   = mword_of_int 0xd3a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E422.
    iIntros (h5) "Hrun".
    (* ...and the frame word is whole again, at SOME value *)
    iDestruct ("Hwbc" with "Hb7") as "Hwb".
    (* ---- 0xd3a  c.li a2,1 ---- *)
    iApply (wp_uk_cli γt γd γs γfd h5 m2 (mword_of_int 0xd3a)
              (mword_of_int 1 : mword 6) a2_idx n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_d3a with "Hcode"). }
    assert (E426 : add_vec_int (mword_of_int 0xd3a : mword 64) 2
                   = mword_of_int 0xd3c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E426.
    iIntros (h6) "Hrun".
    set (m3 := <[Regidx a2_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)]> m2).
    assert (Hs03 : m3 !!! Regidx s0_idx = sp0).
    { rewrite <- Hs02.
      exact (upd_ne m2 (Regidx a2_idx) (Regidx s0_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0xd3c  addi a1,s0,-17 ---- *)
    iApply (wp_uk_addi γt γd γs γfd h6 m3 (mword_of_int 0xd3c)
              (mword_of_int 4079 : mword 12) s0_idx a1_idx
              (add_vec (m3 !!! Regidx s0_idx)
                 (sign_extend' 64 (mword_of_int 4079 : mword 12))) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_d3c with "Hcode"). }
    assert (E428 : add_vec_int (mword_of_int 0xd3c : mword 64) 4
                   = mword_of_int 0xd40)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E428.
    iIntros (h7) "Hrun".
    set (m4 := <[Regidx a1_idx
                 := regval_into_reg
                      (add_vec (m3 !!! Regidx s0_idx)
                         (sign_extend' 64 (mword_of_int 4079 : mword 12)))]> m3).
    (* ---- 0xd40  jal ra,0xca6 <write> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h7 m4 (mword_of_int 0xd40)
              (mword_of_int 2096998 : mword 21) ra_idx
              (mword_of_int ShSyms.write) (mword_of_int 0xd44) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hwrite; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hwrite; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_d40 with "Hcode"). }
    iIntros (h8) "Hrun".
    set (m5 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0xd44 : mword 64)]> m4).
    assert (Hra5 : m5 !!! Regidx ra_idx = (mword_of_int 0xd44 : mword 64))
      by exact (upd_eq m4 (Regidx ra_idx) (regval_into_reg _)).
    (* ---- write(fd, sp0-17, 1) -- the QUIET row: no heap effect at all ---- *)
    iApply (wp_ksh_write γt γd γs γfd h8 m5 n with "Hcode Hrun").
    iIntros (h9 ret) "Hrun".
    assert (Eret : ret_pc (m5 !!! Regidx ra_idx) = (mword_of_int 0xd44 : mword 64))
      by (rewrite Hra5; apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    set (m6 := <[Regidx a0_idx := ret]>
                 (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m5)).
    (* every callee-saved register still holds its ENTRY value: the walk
       has written sp, s0, a2, a1, ra, a7 and a0, and of those only sp and
       s0 are callee-saved -- and both are about to be restored *)
    assert (Hsp6 : m6 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite /m6 (upd_ne _ (Regidx a0_idx) (Regidx csp_rs1) ret
                     ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx a7_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite /m5 (upd_ne _ (Regidx ra_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m4 (upd_ne _ (Regidx a1_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m3 (upd_ne _ (Regidx a2_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      exact Hsp2. }
    assert (Hcs6 : forall r : mword 5, ucallee_saved_idx r = true ->
                     Regidx r <> Regidx csp_rs1 -> Regidx r <> Regidx s0_idx ->
                     m6 !!! Regidx r = m !!! Regidx r).
    (* NAMED disequalities, and [apply] before [vm_compute].  Written the
       obvious way -- [upd_ne _ (Regidx a0_idx) (Regidx r) ret ltac:(exact
       (ucs_ne r _ Hr ltac:(vm_compute; reflexivity)))] -- the INNER tactic
       runs while [ucs_ne]'s second register is still an evar, so
       [vm_compute] is handed [ucallee_saved_idx ?q = false].  That is the
       "inline [ltac:] in argument position" trap, and it cost two kills at
       41 GB and 49 GB before it was read as one.  [apply] first fixes the
       register from the goal; nothing here is spliced into a term. *)
    { intros r Hr Hrsp Hrs0.
      assert (Na0 : Regidx r <> Regidx a0_idx)
        by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
      assert (Na7 : Regidx r <> Regidx a7_idx)
        by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
      assert (Nra : Regidx r <> Regidx ra_idx)
        by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
      assert (Na1 : Regidx r <> Regidx a1_idx)
        by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
      assert (Na2 : Regidx r <> Regidx a2_idx)
        by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
      rewrite /m6 (upd_ne (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m5)
                     (Regidx a0_idx) (Regidx r) ret Na0).
      rewrite (upd_ne m5 (Regidx a7_idx) (Regidx r)
                 (mword_of_int 16 : mword 64) Na7).
      rewrite /m5 (upd_ne m4 (Regidx ra_idx) (Regidx r)
                     (regval_into_reg (mword_of_int 0xd44 : mword 64)) Nra).
      rewrite /m4 (upd_ne m3 (Regidx a1_idx) (Regidx r)
                     (regval_into_reg
                        (add_vec (m3 !!! Regidx s0_idx)
                           (sign_extend' 64 (mword_of_int 4079 : mword 12)))) Na1).
      rewrite /m3 (upd_ne m2 (Regidx a2_idx) (Regidx r)
                     (regval_into_reg
                        (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)) Na2).
      rewrite /m2 (upd_ne m1 (Regidx s0_idx) (Regidx r)
                     (regval_into_reg sp0) Hrs0).
      rewrite /m1 (upd_ne m (Regidx csp_rs1) (Regidx r)
                     (regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 4))))
                     Hrsp).
      reflexivity. }
    (* ---- 0xd44  c.ldsp ra,24(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h9 m6 (mword_of_int 0xd44)
              (mword_of_int 3 : mword 6) ra_idx (uint sp0 - 8)
              (m1 !!! Regidx ra_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp6 Hsp32 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hwra Hrun").
    { iApply (uis_shk_d44 with "Hcode"). }
    iIntros "Hwra".
    assert (E430 : add_vec_int (mword_of_int 0xd44 : mword 64) 2
                   = mword_of_int 0xd46)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E430.
    iIntros (h10) "Hrun".
    set (m7 := <[Regidx ra_idx := regval_into_reg (m1 !!! Regidx ra_idx)]> m6).
    assert (Hsp7 : m7 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite <- Hsp6.
      exact (upd_ne m6 (Regidx ra_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0xd46  c.ldsp s0,16(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h10 m7 (mword_of_int 0xd46)
              (mword_of_int 2 : mword 6) s0_idx (uint sp0 - 16)
              (m1 !!! Regidx s0_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp7 Hsp32 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hws0 Hrun").
    { iApply (uis_shk_d46 with "Hcode"). }
    iIntros "Hws0".
    assert (E432 : add_vec_int (mword_of_int 0xd46 : mword 64) 2
                   = mword_of_int 0xd48)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E432.
    iIntros (h11) "Hrun".
    set (m8 := <[Regidx s0_idx := regval_into_reg (m1 !!! Regidx s0_idx)]> m7).
    assert (Hsp8 : m8 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite <- Hsp7.
      exact (upd_ne m7 (Regidx s0_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0xd48  c.addi16sp sp,sp,32 -- THE POP: the frame goes back ---- *)
    iApply (wp_uk_caddi16sp_up γt γd γs γfd h11 m8 (mword_of_int 0xd48)
              (mword_of_int 2 : mword 6) 4 n
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hwra Hws0 Hwb Hw32] Hrun").
    { iApply (uis_shk_d48 with "Hcode"). }
    { rewrite Hsp8 Hup.
      iApply (ustack_4_close γd sp0 Hal8 with "[Hwra] [Hws0] Hwb Hw32").
      { iExists (m1 !!! Regidx ra_idx). iExact "Hwra". }
      { iExists (m1 !!! Regidx s0_idx). iExact "Hws0". } }
    assert (E434 : add_vec_int (mword_of_int 0xd48 : mword 64) 2
                   = mword_of_int 0xd4a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp8 Hup E434.
    iIntros (h12) "Hrun".
    set (m9 := <[Regidx csp_rs1 := regval_into_reg sp0]> m8).
    assert (Hra9 : m9 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite /m9 (upd_ne m8 (Regidx csp_rs1) (Regidx ra_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m8 (upd_ne m7 (Regidx s0_idx) (Regidx ra_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m7 (upd_eq m6 (Regidx ra_idx) (regval_into_reg _)).
      exact Hra1. }
    (* ---- 0xd4a  c.jr ra ---- *)
    iApply (wp_uk_cjr γt γd γs γfd h12 m9 (mword_of_int 0xd4a) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) (4 + n)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra9; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_d4a with "Hcode"). }
    iIntros (h13) "Hrun".
    iApply ("Hcont" $! h13 m9 with "[] Hrun").
    iPureIntro. intros r Hr.
    destruct (decide (Regidx r = Regidx csp_rs1)) as [Hrsp | Hrsp].
    { rewrite Hrsp /m9 (upd_eq m8 (Regidx csp_rs1) (regval_into_reg sp0)).
      rewrite <- Hsp. reflexivity. }
    rewrite /m9 (upd_ne m8 (Regidx csp_rs1) (Regidx r)
                   (regval_into_reg sp0) Hrsp).
    destruct (decide (Regidx r = Regidx s0_idx)) as [Hrs0 | Hrs0].
    { rewrite Hrs0 /m8
        (upd_eq m7 (Regidx s0_idx) (regval_into_reg (m1 !!! Regidx s0_idx))).
      rewrite Hs01. reflexivity. }
    rewrite /m8 (upd_ne m7 (Regidx s0_idx) (Regidx r)
                   (regval_into_reg (m1 !!! Regidx s0_idx)) Hrs0).
    assert (Nra : Regidx r <> Regidx ra_idx)
      by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
    rewrite /m7 (upd_ne m6 (Regidx ra_idx) (Regidx r)
                   (regval_into_reg (m1 !!! Regidx ra_idx)) Nra).
    exact (Hcs6 r Hr Hrsp Hrs0).
  Qed.


  (* --------------------------------------------------------------------- *)
  (* vprintf's SHARED TAIL @0xfe4: restore ra, s0, s1; pop the 96-byte      *)
  (* frame; return.  The empty-string arm jumps straight here from 0xdbe    *)
  (* -- it never spilled s2..s8, so those nine slots are still whatever the *)
  (* free stack had in them, and the statement says so by taking them as    *)
  (* [∃ w].                                                                  *)
End UkShDiagPutc.

(* ===================================================================== *)
(* §3 ulib's [vprintf(fd, fmt, ap)] for a format string containing no '%'. *)
(* None of sh's three diagnostics is one -- every one of them has a '%s',  *)
(* which is §4 -- but §4 is stated ON TOP of this file's [pro], [loop] and *)
(* [epi], so the plain walk is what the '%s' walk is built out of.         *)
(* ===================================================================== *)

Section UkShDiagVprintf.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context (γt γd γs γfd : gname).

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation s7_idx := (mword_of_int 23 : mword 5).
  Local Notation s8_idx := (mword_of_int 24 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).

  Lemma wp_kshd_vprintf_epi0 (h : CpuId) (m : regfile)
      (sp0 vra vs0 vs1 : mword 64) (n : nat) :
    m !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 12)) ->
    uint sp0 mod 8 = 0 ->
    96 <= uint sp0 ->
    shk_code γt -∗
    uword γd (uint sp0 - 8) vra -∗
    uword γd (uint sp0 - 16) vs0 -∗
    uword γd (uint sp0 - 24) vs1 -∗
    (∃ w : mword 64, uword γd (uint sp0 - 32) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 40) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 48) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 56) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 64) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 72) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 80) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 88) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 96) w) -∗
    urun γt γd γs γfd h m (mword_of_int 0x101e) n -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ m' !!! Regidx csp_rs1 = sp0 ⌝ -∗
       ⌜ m' !!! Regidx s0_idx = vs0 ⌝ -∗
       ⌜ m' !!! Regidx s1_idx = vs1 ⌝ -∗
       ⌜ forall r : mword 5,
           Regidx r <> Regidx csp_rs1 -> Regidx r <> Regidx s0_idx ->
           Regidx r <> Regidx s1_idx -> Regidx r <> Regidx ra_idx ->
           m' !!! Regidx r = m !!! Regidx r ⌝ -∗
       urun γt γd γs γfd h' m' (ret_pc vra) (12 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hsp Hal8 Hlo. iIntros "#Hcode Hwra Hws0 Hws1 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hrun Hcont".
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                   = bv_unsigned sp0 - 96).
    { replace (- (8 * Z.of_nat 12)) with (-96) by lia.
      exact (uv_avi_neg sp0 96 ltac:(apply Z.leb_le; reflexivity)
               ltac:(rewrite <- uint_unsigned; exact Hlo)). }
    assert (Hsp96 : uint (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                    = uint sp0 - 96)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (HR : 0 <= bv_unsigned sp0 < 18446744073709551616).
    { pose proof (bv_unsigned_in_range 64 sp0) as H0.
      assert (Em : bv_modulus 64 = 18446744073709551616)
        by (vm_compute; reflexivity).
      rewrite Em in H0. exact H0. }
    assert (Hd12 : (0 <= 8 * Z.of_nat 12)%Z) by (apply Z.leb_le; reflexivity).
    assert (Hlt12 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                    + 8 * Z.of_nat 12 < Z64)
      by (clear -Hbsp HR; rewrite Hbsp; unfold Z64; lia).
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                    (8 * Z.of_nat 12) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                 (8 * Z.of_nat 12) Hd12 Hlt12).
      clear -Hbsp. rewrite Hbsp. lia. }
    assert (Ho88 : uoff_sdsp (mword_of_int 11 : mword 6) = 88)
      by (vm_compute; reflexivity).
    assert (Ho80 : uoff_sdsp (mword_of_int 10 : mword 6) = 80)
      by (vm_compute; reflexivity).
    assert (Ho72 : uoff_sdsp (mword_of_int 9 : mword 6) = 72)
      by (vm_compute; reflexivity).
    (* ---- 0x101e  c.ldsp ra,88(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h m (mword_of_int 0x101e)
              (mword_of_int 11 : mword 6) ra_idx (uint sp0 - 8) vra n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp Hsp96 Ho88; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hwra Hrun").
    { iApply (uis_shk_101e with "Hcode"). }
    iIntros "Hwra".
    assert (E70a : add_vec_int (mword_of_int 0x101e : mword 64) 2
                 = mword_of_int 0x1020)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E70a.
    iIntros (h1) "Hrun".
    set (mm1 := <[Regidx ra_idx := regval_into_reg vra]> m).
    assert (Hsp1 : mm1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp.
      exact (upd_ne m (Regidx ra_idx) (Regidx csp_rs1) (regval_into_reg vra)
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x1020  c.ldsp s0,80(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h1 mm1 (mword_of_int 0x1020)
              (mword_of_int 10 : mword 6) s0_idx (uint sp0 - 16) vs0 n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp1 Hsp96 Ho80; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hws0 Hrun").
    { iApply (uis_shk_1020 with "Hcode"). }
    iIntros "Hws0".
    assert (E70c : add_vec_int (mword_of_int 0x1020 : mword 64) 2
                 = mword_of_int 0x1022)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E70c.
    iIntros (h2) "Hrun".
    set (mm2 := <[Regidx s0_idx := regval_into_reg vs0]> mm1).
    assert (Hsp2 : mm2 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp1.
      exact (upd_ne mm1 (Regidx s0_idx) (Regidx csp_rs1) (regval_into_reg vs0)
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x1022  c.ldsp s1,72(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h2 mm2 (mword_of_int 0x1022)
              (mword_of_int 9 : mword 6) s1_idx (uint sp0 - 24) vs1 n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp2 Hsp96 Ho72; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hws1 Hrun").
    { iApply (uis_shk_1022 with "Hcode"). }
    iIntros "Hws1".
    assert (E70e : add_vec_int (mword_of_int 0x1022 : mword 64) 2
                 = mword_of_int 0x1024)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E70e.
    iIntros (h3) "Hrun".
    set (mm3 := <[Regidx s1_idx := regval_into_reg vs1]> mm2).
    assert (Hsp3 : mm3 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp2.
      exact (upd_ne mm2 (Regidx s1_idx) (Regidx csp_rs1) (regval_into_reg vs1)
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x1024  c.addi16sp sp,sp,96 -- THE POP ---- *)
    iApply (wp_uk_caddi16sp_up γt γd γs γfd h3 mm3 (mword_of_int 0x1024)
              (mword_of_int 6 : mword 6) 12 n
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hwra Hws0 Hws1 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12] Hrun").
    { iApply (uis_shk_1024 with "Hcode"). }
    { rewrite Hsp3 Hup.
      iApply (ustack_12_close γd sp0 Hal8
                with "[Hwra] [Hws0] [Hws1] Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12").
      { iExists vra. iExact "Hwra". }
      { iExists vs0. iExact "Hws0". }
      { iExists vs1. iExact "Hws1". } }
    assert (E710 : add_vec_int (mword_of_int 0x1024 : mword 64) 2
                   = mword_of_int 0x1026)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp3 Hup E710.
    iIntros (h4) "Hrun".
    set (mm4 := <[Regidx csp_rs1 := regval_into_reg sp0]> mm3).
    assert (Hra4 : mm4 !!! Regidx ra_idx = vra).
    { rewrite /mm4 (upd_ne mm3 (Regidx csp_rs1) (Regidx ra_idx)
                     (regval_into_reg sp0) ltac:(vm_compute; discriminate)).
      rewrite /mm3 (upd_ne mm2 (Regidx s1_idx) (Regidx ra_idx)
                     (regval_into_reg vs1) ltac:(vm_compute; discriminate)).
      rewrite /mm2 (upd_ne mm1 (Regidx s0_idx) (Regidx ra_idx)
                     (regval_into_reg vs0) ltac:(vm_compute; discriminate)).
      rewrite /mm1. exact (upd_eq m (Regidx ra_idx) (regval_into_reg vra)). }
    (* ---- 0x1026  c.jr ra ---- *)
    iApply (wp_uk_cjr γt γd γs γfd h4 mm4 (mword_of_int 0x1026) ra_idx
              (ret_pc vra) (12 + n)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra4; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_1026 with "Hcode"). }
    iIntros (h5) "Hrun".
    iApply ("Hcont" $! h5 mm4 with "[] [] [] [] Hrun").
    { iPureIntro. rewrite /mm4.
      exact (upd_eq mm3 (Regidx csp_rs1) (regval_into_reg sp0)). }
    { iPureIntro.
      rewrite /mm4 (upd_ne mm3 (Regidx csp_rs1) (Regidx s0_idx)
                     (regval_into_reg sp0) ltac:(vm_compute; discriminate)).
      rewrite /mm3 (upd_ne mm2 (Regidx s1_idx) (Regidx s0_idx)
                     (regval_into_reg vs1) ltac:(vm_compute; discriminate)).
      rewrite /mm2. exact (upd_eq mm1 (Regidx s0_idx) (regval_into_reg vs0)). }
    { iPureIntro.
      rewrite /mm4 (upd_ne mm3 (Regidx csp_rs1) (Regidx s1_idx)
                     (regval_into_reg sp0) ltac:(vm_compute; discriminate)).
      rewrite /mm3. exact (upd_eq mm2 (Regidx s1_idx) (regval_into_reg vs1)). }
    { iPureIntro. intros r Hrsp Hrs0 Hrs1 Hrra.
      rewrite /mm4 (upd_ne mm3 (Regidx csp_rs1) (Regidx r)
                     (regval_into_reg sp0) Hrsp).
      rewrite /mm3 (upd_ne mm2 (Regidx s1_idx) (Regidx r)
                     (regval_into_reg vs1) Hrs1).
      rewrite /mm2 (upd_ne mm1 (Regidx s0_idx) (Regidx r)
                     (regval_into_reg vs0) Hrs0).
      rewrite /mm1. exact (upd_ne m (Regidx ra_idx) (Regidx r)
                             (regval_into_reg vra) Hrra). }
  Qed.





  (* --------------------------------------------------------------------- *)
  (* vprintf's FULL EPILOGUE @0x1010: restore s2..s8, then fall into the      *)
  (* shared tail.  This is where [ucallee_saved] is assembled, because this  *)
  (* is where every spilled register is back at its entry value: the ten     *)
  (* frame words are PINNED to [m0]'s registers in the statement, [sp0] is   *)
  (* [m0]'s sp, and [Hfree] covers the five callee-saved registers vprintf   *)
  (* never touches (gp, tp, s9, s10, s11).  [ucs_cases] says there is no      *)
  (* sixteenth.                                                              *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kshd_vprintf_epi (h : CpuId) (m m0 : regfile) (sp0 : mword 64)
      (n : nat) :
    m !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 12)) ->
    m0 !!! Regidx csp_rs1 = sp0 ->
    uint sp0 mod 8 = 0 ->
    96 <= uint sp0 ->
    (forall r : mword 5, ucallee_saved_idx r = true ->
       uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27) ->
       m !!! Regidx r = m0 !!! Regidx r) ->
    shk_code γt -∗
    uword γd (uint sp0 - 8) (m0 !!! Regidx ra_idx) -∗
    uword γd (uint sp0 - 16) (m0 !!! Regidx s0_idx) -∗
    uword γd (uint sp0 - 24) (m0 !!! Regidx s1_idx) -∗
    uword γd (uint sp0 - 32) (m0 !!! Regidx s2_idx) -∗
    uword γd (uint sp0 - 40) (m0 !!! Regidx s3_idx) -∗
    uword γd (uint sp0 - 48) (m0 !!! Regidx s4_idx) -∗
    uword γd (uint sp0 - 56) (m0 !!! Regidx s5_idx) -∗
    uword γd (uint sp0 - 64) (m0 !!! Regidx s6_idx) -∗
    uword γd (uint sp0 - 72) (m0 !!! Regidx s7_idx) -∗
    uword γd (uint sp0 - 80) (m0 !!! Regidx s8_idx) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 88) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 96) w) -∗
    urun γt γd γs γfd h m (mword_of_int 0x1010) n -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ ucallee_saved m0 m' ⌝ -∗
       urun γt γd γs γfd h' m' (ret_pc (m0 !!! Regidx ra_idx)) (12 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hsp Hsp0 Hal8 Hlo Hfree.
    iIntros "#Hcode Hwra Hws0 Hws1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw11 Hw12 Hrun Hcont".
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                   = bv_unsigned sp0 - 96).
    { replace (- (8 * Z.of_nat 12)) with (-96) by lia.
      exact (uv_avi_neg sp0 96 ltac:(apply Z.leb_le; reflexivity)
               ltac:(rewrite <- uint_unsigned; exact Hlo)). }
    assert (Hsp96 : uint (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                    = uint sp0 - 96)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Ho64 : uoff_sdsp (mword_of_int 8 : mword 6) = 64)
      by (vm_compute; reflexivity).
    assert (Ho56 : uoff_sdsp (mword_of_int 7 : mword 6) = 56)
      by (vm_compute; reflexivity).
    assert (Ho48 : uoff_sdsp (mword_of_int 6 : mword 6) = 48)
      by (vm_compute; reflexivity).
    assert (Ho40 : uoff_sdsp (mword_of_int 5 : mword 6) = 40)
      by (vm_compute; reflexivity).
    assert (Ho32 : uoff_sdsp (mword_of_int 4 : mword 6) = 32)
      by (vm_compute; reflexivity).
    assert (Ho24 : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
      by (vm_compute; reflexivity).
    assert (Ho16 : uoff_sdsp (mword_of_int 2 : mword 6) = 16)
      by (vm_compute; reflexivity).
    (* ---- 0x1010  c.ldsp s2,64(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h m (mword_of_int 0x1010)
              (mword_of_int 8 : mword 6) s2_idx (uint sp0 - 32)
              (m0 !!! Regidx s2_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp Hsp96 Ho64; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw2 Hrun").
    { iApply (uis_shk_1010 with "Hcode"). }
    iIntros "Hw2".
    assert (E6fc : add_vec_int (mword_of_int 0x1010 : mword 64) 2
                 = mword_of_int 0x1012)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E6fc.
    iIntros (h1) "Hrun".
    set (me1 := <[Regidx s2_idx := regval_into_reg (m0 !!! Regidx s2_idx)]> m).
    assert (Hsp1 : me1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp.
      exact (upd_ne m (Regidx s2_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s2_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x1012  c.ldsp s3,56(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h1 me1 (mword_of_int 0x1012)
              (mword_of_int 7 : mword 6) s3_idx (uint sp0 - 40)
              (m0 !!! Regidx s3_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp1 Hsp96 Ho56; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw3 Hrun").
    { iApply (uis_shk_1012 with "Hcode"). }
    iIntros "Hw3".
    assert (E6fe : add_vec_int (mword_of_int 0x1012 : mword 64) 2
                 = mword_of_int 0x1014)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E6fe.
    iIntros (h2) "Hrun".
    set (me2 := <[Regidx s3_idx := regval_into_reg (m0 !!! Regidx s3_idx)]> me1).
    assert (Hsp2 : me2 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp1.
      exact (upd_ne me1 (Regidx s3_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s3_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x1014  c.ldsp s4,48(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h2 me2 (mword_of_int 0x1014)
              (mword_of_int 6 : mword 6) s4_idx (uint sp0 - 48)
              (m0 !!! Regidx s4_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp2 Hsp96 Ho48; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw4 Hrun").
    { iApply (uis_shk_1014 with "Hcode"). }
    iIntros "Hw4".
    assert (E700 : add_vec_int (mword_of_int 0x1014 : mword 64) 2
                 = mword_of_int 0x1016)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E700.
    iIntros (h3) "Hrun".
    set (me3 := <[Regidx s4_idx := regval_into_reg (m0 !!! Regidx s4_idx)]> me2).
    assert (Hsp3 : me3 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp2.
      exact (upd_ne me2 (Regidx s4_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s4_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x1016  c.ldsp s5,40(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h3 me3 (mword_of_int 0x1016)
              (mword_of_int 5 : mword 6) s5_idx (uint sp0 - 56)
              (m0 !!! Regidx s5_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp3 Hsp96 Ho40; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw5 Hrun").
    { iApply (uis_shk_1016 with "Hcode"). }
    iIntros "Hw5".
    assert (E702 : add_vec_int (mword_of_int 0x1016 : mword 64) 2
                 = mword_of_int 0x1018)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E702.
    iIntros (h4) "Hrun".
    set (me4 := <[Regidx s5_idx := regval_into_reg (m0 !!! Regidx s5_idx)]> me3).
    assert (Hsp4 : me4 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp3.
      exact (upd_ne me3 (Regidx s5_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s5_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x1018  c.ldsp s6,32(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h4 me4 (mword_of_int 0x1018)
              (mword_of_int 4 : mword 6) s6_idx (uint sp0 - 64)
              (m0 !!! Regidx s6_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp4 Hsp96 Ho32; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw6 Hrun").
    { iApply (uis_shk_1018 with "Hcode"). }
    iIntros "Hw6".
    assert (E704 : add_vec_int (mword_of_int 0x1018 : mword 64) 2
                 = mword_of_int 0x101a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E704.
    iIntros (h5) "Hrun".
    set (me5 := <[Regidx s6_idx := regval_into_reg (m0 !!! Regidx s6_idx)]> me4).
    assert (Hsp5 : me5 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp4.
      exact (upd_ne me4 (Regidx s6_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s6_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x101a  c.ldsp s7,24(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h5 me5 (mword_of_int 0x101a)
              (mword_of_int 3 : mword 6) s7_idx (uint sp0 - 72)
              (m0 !!! Regidx s7_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp5 Hsp96 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw7 Hrun").
    { iApply (uis_shk_101a with "Hcode"). }
    iIntros "Hw7".
    assert (E706 : add_vec_int (mword_of_int 0x101a : mword 64) 2
                 = mword_of_int 0x101c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E706.
    iIntros (h6) "Hrun".
    set (me6 := <[Regidx s7_idx := regval_into_reg (m0 !!! Regidx s7_idx)]> me5).
    assert (Hsp6 : me6 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp5.
      exact (upd_ne me5 (Regidx s7_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s7_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x101c  c.ldsp s8,16(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h6 me6 (mword_of_int 0x101c)
              (mword_of_int 2 : mword 6) s8_idx (uint sp0 - 80)
              (m0 !!! Regidx s8_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp6 Hsp96 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw8 Hrun").
    { iApply (uis_shk_101c with "Hcode"). }
    iIntros "Hw8".
    assert (E708 : add_vec_int (mword_of_int 0x101c : mword 64) 2
                 = mword_of_int 0x101e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E708.
    iIntros (h7) "Hrun".
    set (me7 := <[Regidx s8_idx := regval_into_reg (m0 !!! Regidx s8_idx)]> me6).
    assert (Hsp7 : me7 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp6.
      exact (upd_ne me6 (Regidx s8_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s8_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x101e..0x1026: the shared tail ---- *)
    iApply (wp_kshd_vprintf_epi0 h7 me7 sp0 (m0 !!! Regidx ra_idx)
              (m0 !!! Regidx s0_idx) (m0 !!! Regidx s1_idx) n Hsp7 Hal8 Hlo
              with "Hcode Hwra Hws0 Hws1 [Hw2] [Hw3] [Hw4] [Hw5] [Hw6] [Hw7] [Hw8] Hw11 Hw12 Hrun").
    { iExists (m0 !!! Regidx s2_idx). iExact "Hw2". }
    { iExists (m0 !!! Regidx s3_idx). iExact "Hw3". }
    { iExists (m0 !!! Regidx s4_idx). iExact "Hw4". }
    { iExists (m0 !!! Regidx s5_idx). iExact "Hw5". }
    { iExists (m0 !!! Regidx s6_idx). iExact "Hw6". }
    { iExists (m0 !!! Regidx s7_idx). iExact "Hw7". }
    { iExists (m0 !!! Regidx s8_idx). iExact "Hw8". }
    assert (Hme2 : me7 !!! Regidx s2_idx = m0 !!! Regidx s2_idx).
    {
      rewrite /me7 (upd_ne me6 (Regidx s8_idx) (Regidx s2_idx)
                     (regval_into_reg (m0 !!! Regidx s8_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me6 (upd_ne me5 (Regidx s7_idx) (Regidx s2_idx)
                     (regval_into_reg (m0 !!! Regidx s7_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me5 (upd_ne me4 (Regidx s6_idx) (Regidx s2_idx)
                     (regval_into_reg (m0 !!! Regidx s6_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me4 (upd_ne me3 (Regidx s5_idx) (Regidx s2_idx)
                     (regval_into_reg (m0 !!! Regidx s5_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me3 (upd_ne me2 (Regidx s4_idx) (Regidx s2_idx)
                     (regval_into_reg (m0 !!! Regidx s4_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me2 (upd_ne me1 (Regidx s3_idx) (Regidx s2_idx)
                     (regval_into_reg (m0 !!! Regidx s3_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me1.
      exact (upd_eq m (Regidx s2_idx) (regval_into_reg (m0 !!! Regidx s2_idx))). }
    assert (Hme3 : me7 !!! Regidx s3_idx = m0 !!! Regidx s3_idx).
    {
      rewrite /me7 (upd_ne me6 (Regidx s8_idx) (Regidx s3_idx)
                     (regval_into_reg (m0 !!! Regidx s8_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me6 (upd_ne me5 (Regidx s7_idx) (Regidx s3_idx)
                     (regval_into_reg (m0 !!! Regidx s7_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me5 (upd_ne me4 (Regidx s6_idx) (Regidx s3_idx)
                     (regval_into_reg (m0 !!! Regidx s6_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me4 (upd_ne me3 (Regidx s5_idx) (Regidx s3_idx)
                     (regval_into_reg (m0 !!! Regidx s5_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me3 (upd_ne me2 (Regidx s4_idx) (Regidx s3_idx)
                     (regval_into_reg (m0 !!! Regidx s4_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me2.
      exact (upd_eq me1 (Regidx s3_idx) (regval_into_reg (m0 !!! Regidx s3_idx))). }
    assert (Hme4 : me7 !!! Regidx s4_idx = m0 !!! Regidx s4_idx).
    {
      rewrite /me7 (upd_ne me6 (Regidx s8_idx) (Regidx s4_idx)
                     (regval_into_reg (m0 !!! Regidx s8_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me6 (upd_ne me5 (Regidx s7_idx) (Regidx s4_idx)
                     (regval_into_reg (m0 !!! Regidx s7_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me5 (upd_ne me4 (Regidx s6_idx) (Regidx s4_idx)
                     (regval_into_reg (m0 !!! Regidx s6_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me4 (upd_ne me3 (Regidx s5_idx) (Regidx s4_idx)
                     (regval_into_reg (m0 !!! Regidx s5_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me3.
      exact (upd_eq me2 (Regidx s4_idx) (regval_into_reg (m0 !!! Regidx s4_idx))). }
    assert (Hme5 : me7 !!! Regidx s5_idx = m0 !!! Regidx s5_idx).
    {
      rewrite /me7 (upd_ne me6 (Regidx s8_idx) (Regidx s5_idx)
                     (regval_into_reg (m0 !!! Regidx s8_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me6 (upd_ne me5 (Regidx s7_idx) (Regidx s5_idx)
                     (regval_into_reg (m0 !!! Regidx s7_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me5 (upd_ne me4 (Regidx s6_idx) (Regidx s5_idx)
                     (regval_into_reg (m0 !!! Regidx s6_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me4.
      exact (upd_eq me3 (Regidx s5_idx) (regval_into_reg (m0 !!! Regidx s5_idx))). }
    assert (Hme6 : me7 !!! Regidx s6_idx = m0 !!! Regidx s6_idx).
    {
      rewrite /me7 (upd_ne me6 (Regidx s8_idx) (Regidx s6_idx)
                     (regval_into_reg (m0 !!! Regidx s8_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me6 (upd_ne me5 (Regidx s7_idx) (Regidx s6_idx)
                     (regval_into_reg (m0 !!! Regidx s7_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me5.
      exact (upd_eq me4 (Regidx s6_idx) (regval_into_reg (m0 !!! Regidx s6_idx))). }
    assert (Hme7 : me7 !!! Regidx s7_idx = m0 !!! Regidx s7_idx).
    {
      rewrite /me7 (upd_ne me6 (Regidx s8_idx) (Regidx s7_idx)
                     (regval_into_reg (m0 !!! Regidx s8_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me6.
      exact (upd_eq me5 (Regidx s7_idx) (regval_into_reg (m0 !!! Regidx s7_idx))). }
    assert (Hme8 : me7 !!! Regidx s8_idx = m0 !!! Regidx s8_idx).
    {
      rewrite /me7.
      exact (upd_eq me6 (Regidx s8_idx) (regval_into_reg (m0 !!! Regidx s8_idx))). }
    assert (Hmeo : forall r : mword 5,
               (uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27)) ->
               me7 !!! Regidx r = m !!! Regidx r).
    { intros r Hr.
      (* NOT [vm_compute] on these: the goal carries the free [r], and
         [vm_compute] against a free variable is the documented hang.
         Compute the CONCRETE index only, then [lia] against [Hr]. *)
      assert (N18 : Regidx r <> Regidx s2_idx)
        by (apply uidx_ne;
            replace (uint s2_idx) with 18 by (vm_compute; reflexivity);
            lia).
      assert (N19 : Regidx r <> Regidx s3_idx)
        by (apply uidx_ne;
            replace (uint s3_idx) with 19 by (vm_compute; reflexivity);
            lia).
      assert (N20 : Regidx r <> Regidx s4_idx)
        by (apply uidx_ne;
            replace (uint s4_idx) with 20 by (vm_compute; reflexivity);
            lia).
      assert (N21 : Regidx r <> Regidx s5_idx)
        by (apply uidx_ne;
            replace (uint s5_idx) with 21 by (vm_compute; reflexivity);
            lia).
      assert (N22 : Regidx r <> Regidx s6_idx)
        by (apply uidx_ne;
            replace (uint s6_idx) with 22 by (vm_compute; reflexivity);
            lia).
      assert (N23 : Regidx r <> Regidx s7_idx)
        by (apply uidx_ne;
            replace (uint s7_idx) with 23 by (vm_compute; reflexivity);
            lia).
      assert (N24 : Regidx r <> Regidx s8_idx)
        by (apply uidx_ne;
            replace (uint s8_idx) with 24 by (vm_compute; reflexivity);
            lia).
      rewrite /me7 (upd_ne me6 (Regidx s8_idx) (Regidx r)
                     (regval_into_reg (m0 !!! Regidx s8_idx)) N24).
      rewrite /me6 (upd_ne me5 (Regidx s7_idx) (Regidx r)
                     (regval_into_reg (m0 !!! Regidx s7_idx)) N23).
      rewrite /me5 (upd_ne me4 (Regidx s6_idx) (Regidx r)
                     (regval_into_reg (m0 !!! Regidx s6_idx)) N22).
      rewrite /me4 (upd_ne me3 (Regidx s5_idx) (Regidx r)
                     (regval_into_reg (m0 !!! Regidx s5_idx)) N21).
      rewrite /me3 (upd_ne me2 (Regidx s4_idx) (Regidx r)
                     (regval_into_reg (m0 !!! Regidx s4_idx)) N20).
      rewrite /me2 (upd_ne me1 (Regidx s3_idx) (Regidx r)
                     (regval_into_reg (m0 !!! Regidx s3_idx)) N19).
      rewrite /me1 (upd_ne m (Regidx s2_idx) (Regidx r)
                     (regval_into_reg (m0 !!! Regidx s2_idx)) N18).
      reflexivity. }
    iIntros (h8 m2) "%Hspx %Hs0x %Hs1x %Hpres Hrun".
    iApply ("Hcont" $! h8 m2 with "[] Hrun").
    iPureIntro. intros r Hr.
    assert (Hpresx : uint r <> 2 -> uint r <> 8 -> uint r <> 9 -> uint r <> 1 ->
                       m2 !!! Regidx r = me7 !!! Regidx r).
    { intros H2 H8 H9 H1. apply Hpres; apply uidx_ne;
        [ replace (uint csp_rs1) with 2 by (vm_compute; reflexivity)
        | replace (uint s0_idx) with 8 by (vm_compute; reflexivity)
        | replace (uint s1_idx) with 9 by (vm_compute; reflexivity)
        | replace (uint ra_idx) with 1 by (vm_compute; reflexivity) ];
        assumption. }
    destruct (ucs_cases r Hr) as [E2 | [E3 | [E4 | [E8 | [E9 | E18]]]]].
    - assert (Er : Regidx r = Regidx csp_rs1)
        by (apply (uidx_eq r 2); [ exact E2 | vm_compute; reflexivity ]).
      rewrite Er Hspx. exact (eq_sym Hsp0).
    -
      assert (K2 : uint r <> 2) by lia.
      assert (K8 : uint r <> 8) by lia.
      assert (K9 : uint r <> 9) by lia.
      assert (K1 : uint r <> 1) by lia.
      rewrite (Hpresx K2 K8 K9 K1).
      assert (Hd : uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27)) by lia.
      rewrite (Hmeo r Hd). exact (Hfree r Hr Hd).
    -
      assert (K2 : uint r <> 2) by lia.
      assert (K8 : uint r <> 8) by lia.
      assert (K9 : uint r <> 9) by lia.
      assert (K1 : uint r <> 1) by lia.
      rewrite (Hpresx K2 K8 K9 K1).
      assert (Hd : uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27)) by lia.
      rewrite (Hmeo r Hd). exact (Hfree r Hr Hd).
    - assert (Er : Regidx r = Regidx s0_idx)
        by (apply (uidx_eq r 8); [ exact E8 | vm_compute; reflexivity ]).
      rewrite Er. exact Hs0x.
    - assert (Er : Regidx r = Regidx s1_idx)
        by (apply (uidx_eq r 9); [ exact E9 | vm_compute; reflexivity ]).
      rewrite Er. exact Hs1x.
    -
      assert (K2 : uint r <> 2) by lia.
      assert (K8 : uint r <> 8) by lia.
      assert (K9 : uint r <> 9) by lia.
      assert (K1 : uint r <> 1) by lia.
      rewrite (Hpresx K2 K8 K9 K1).
      assert (Ecase : uint r = 18 \/ uint r = 19 \/ uint r = 20 \/ uint r = 21 \/
                      uint r = 22 \/ uint r = 23 \/ uint r = 24 \/
                      uint r = 25 \/ uint r = 26 \/ uint r = 27) by lia.
      destruct Ecase as [E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]].
      + assert (Er : Regidx r = Regidx s2_idx)
          by (apply (uidx_eq r 18); [ exact E | vm_compute; reflexivity ]).
        rewrite Er. exact Hme2.
      + assert (Er : Regidx r = Regidx s3_idx)
          by (apply (uidx_eq r 19); [ exact E | vm_compute; reflexivity ]).
        rewrite Er. exact Hme3.
      + assert (Er : Regidx r = Regidx s4_idx)
          by (apply (uidx_eq r 20); [ exact E | vm_compute; reflexivity ]).
        rewrite Er. exact Hme4.
      + assert (Er : Regidx r = Regidx s5_idx)
          by (apply (uidx_eq r 21); [ exact E | vm_compute; reflexivity ]).
        rewrite Er. exact Hme5.
      + assert (Er : Regidx r = Regidx s6_idx)
          by (apply (uidx_eq r 22); [ exact E | vm_compute; reflexivity ]).
        rewrite Er. exact Hme6.
      + assert (Er : Regidx r = Regidx s7_idx)
          by (apply (uidx_eq r 23); [ exact E | vm_compute; reflexivity ]).
        rewrite Er. exact Hme7.
      + assert (Er : Regidx r = Regidx s8_idx)
          by (apply (uidx_eq r 24); [ exact E | vm_compute; reflexivity ]).
        rewrite Er. exact Hme8.
      + assert (Hd : uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27)) by lia.
        rewrite (Hmeo r Hd). exact (Hfree r Hr Hd).
      + assert (Hd : uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27)) by lia.
        rewrite (Hmeo r Hd). exact (Hfree r Hr Hd).
      + assert (Hd : uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27)) by lia.
        rewrite (Hmeo r Hd). exact (Hfree r Hr Hd).
  Qed.

  (* ===================================================================== *)
  (* THE LOOP.  For a format string with no '%', vprintf is                 *)
  (*                                                                        *)
  (*   0xe40  sext.w a5,s1        ; a5 := the current character             *)
  (*   0xe44  bnez  s3,0xe2a      ; NOT taken: s3 is the pending-% state    *)
  (*   0xe48  bne   a5,s5,0xe20   ; taken: the character is not '%'          *)
  (*   0xe20  mv a1,s1 ; mv a0,s6 ; jal putc ; j 0xe2e                       *)
  (*   0xe2e  addiw a5,s2,1 ; mv s2,a5 ; mv a4,a5 ; add a5,a5,s4             *)
  (*   0xe38  lbu   s1,0(a5)      ; the NEXT character                       *)
  (*   0xe3c  beqz  s1,0x1010      ; taken at the terminator                  *)
  (*                                                                        *)
  (* [vp_inv] is what survives a round: the frame pointer, the index, and    *)
  (* the four values the prologue parked in callee-saved registers.  It      *)
  (* survives the putc CALL for free -- every register it names is           *)
  (* callee-saved, which is the whole reason ulib parks them there.          *)
  (* ===================================================================== *)

  Definition vp_inv (m0 m : regfile) (sp0 : mword 64) (a : Z) (fd ap : mword 64)
      (i : nat) : Prop :=
    m !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 12)) /\
    m !!! Regidx s0_idx = sp0 /\
    m !!! Regidx s2_idx = mword_of_int (Z.of_nat i) /\
    m !!! Regidx s3_idx = zero_reg /\
    m !!! Regidx s4_idx = mword_of_int a /\
    m !!! Regidx s5_idx = mword_of_int 37 /\
    m !!! Regidx s6_idx = fd /\
    m !!! Regidx s7_idx = ap /\
    m !!! Regidx s8_idx = mword_of_int 100 /\
    (forall r : mword 5, ucallee_saved_idx r = true ->
       uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27) ->
       m !!! Regidx r = m0 !!! Regidx r).

  (* every register [vp_inv] names is callee-saved, so a call preserves it *)
  Lemma vp_inv_call (m0 m m' : regfile) (sp0 : mword 64) (a : Z)
      (fd ap : mword 64) (i : nat) :
    ucallee_saved m m' -> vp_inv m0 m sp0 a fd ap i -> vp_inv m0 m' sp0 a fd ap i.
  Proof.
    intros Hcs (Hsp & Hs0 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hfr).
    unfold vp_inv.
    rewrite (Hcs csp_rs1 ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s0_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s2_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s3_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s4_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s5_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s6_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s7_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s8_idx ltac:(vm_compute; reflexivity)).
    repeat (split; [ assumption | ]).
    intros r Hr Hset. rewrite (Hcs r Hr). exact (Hfr r Hr Hset).
  Qed.


  (* which registers a step may write without disturbing [vp_inv]: anything
     that is neither one of the seven the invariant names (sp, s0, s2..s6)
     nor one of the five [Hfree] covers (gp, tp, s9..s11).  One
     [vm_compute] per call site instead of twelve. *)
  Definition vp_writable (r : mword 5) : bool :=
    negb (Z.eqb (uint r) 2 || Z.eqb (uint r) 3 || Z.eqb (uint r) 4 ||
          Z.eqb (uint r) 8 ||
          ((18 <=? uint r) && (uint r <=? 24)) ||
          ((25 <=? uint r) && (uint r <=? 27))).

  Lemma vp_writable_ne (r : mword 5) (z : Z) :
    vp_writable r = true ->
    (z = 2 \/ z = 3 \/ z = 4 \/ z = 8 \/ (18 <= z <= 24) \/ (25 <= z <= 27)) ->
    uint r <> z.
  Proof.
    unfold vp_writable. intro H. apply negb_true_iff in H.
    rewrite !orb_false_iff in H.
    destruct H as [[[[[H1 H2] H3] H4] H5] H6].
    apply Z.eqb_neq in H1. apply Z.eqb_neq in H2.
    apply Z.eqb_neq in H3. apply Z.eqb_neq in H4.
    apply andb_false_iff in H5. apply andb_false_iff in H6.
    intros Hz He. rewrite He in H1, H2, H3, H4, H5, H6.
    destruct H5 as [H5 | H5]; try apply Z.leb_gt in H5;
      destruct H6 as [H6 | H6]; try apply Z.leb_gt in H6; lia.
  Qed.

  Lemma vp_inv_upd (m0 m : regfile) (sp0 : mword 64) (a : Z) (fd ap : mword 64)
      (i : nat) (r : mword 5) (v : mword 64) :
    vp_writable r = true ->
    vp_inv m0 m sp0 a fd ap i ->
    vp_inv m0 (<[Regidx r := regval_into_reg v]> m) sp0 a fd ap i.
  Proof.
    intros Hw (Hsp & Hs0 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hfr).
    unfold vp_inv.
    rewrite (upd_ne m (Regidx r) (Regidx csp_rs1) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint csp_rs1) with 2
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s0_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s0_idx) with 8
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s2_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s2_idx) with 18
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s3_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s3_idx) with 19
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s4_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s4_idx) with 20
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s5_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s5_idx) with 21
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s6_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s6_idx) with 22
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s7_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s7_idx) with 23
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s8_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s8_idx) with 24
                       by (vm_compute; reflexivity); lia)).
    repeat (split; [ assumption | ]).
    intros q Hq Hset.
    rewrite (upd_ne m (Regidx r) (Regidx q) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw); lia)).
    exact (Hfr q Hq Hset).
  Qed.

  (* ...and the ONE write that changes it: s2, the loop index *)
  Lemma vp_inv_bump (m0 m : regfile) (sp0 : mword 64) (a : Z) (fd ap : mword 64)
      (i j : nat) (v : mword 64) :
    v = mword_of_int (Z.of_nat j) ->
    vp_inv m0 m sp0 a fd ap i ->
    vp_inv m0 (<[Regidx s2_idx := regval_into_reg v]> m) sp0 a fd ap j.
  Proof.
    intros -> (Hsp & Hs0 & _ & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hfr).
    unfold vp_inv.
    rewrite (upd_ne m (Regidx s2_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s0_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s3_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s4_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s5_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s6_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s7_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s8_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_eq m (Regidx s2_idx) _).
    repeat (split; [ (assumption || reflexivity) | ]).
    intros q Hq Hset.
    rewrite (upd_ne m (Regidx s2_idx) (Regidx q) _
               ltac:(apply uidx_ne; replace (uint s2_idx) with 18
                       by (vm_compute; reflexivity); lia)).
    exact (Hfr q Hq Hset).
  Qed.

  (* --------------------------------------------------------------------- *)
  (* ONE ROUND, 0xe40 -> 0xe3c.  It owns no frame word: putc's four are     *)
  (* BELOW sp, and the twelve vprintf spilled are untouched here.            *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kshd_vprintf_step (m0 : regfile) (sp0 fd ap : mword 64) (a : Z)
      (i : nat) (b0 b1 : mword 8) (h : CpuId) (m : regfile) (n : nat) :
    0 <= a -> a + Z.of_nat i + 2 < 2 ^ 31 ->
    bv_unsigned b0 <> 37 ->
    vp_inv m0 m sp0 a fd ap i ->
    m !!! Regidx s1_idx = mword_of_int (bv_unsigned b0) ->
    shk_code γt -∗
    utext γt (a + Z.of_nat (S i)) b1 -∗
    urun γt γd γs γfd h m (mword_of_int 0xe40) (4 + n) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ vp_inv m0 m' sp0 a fd ap (S i) ⌝ -∗
       ⌜ m' !!! Regidx s1_idx = mword_of_int (bv_unsigned b1) ⌝ -∗
       urun γt γd γs γfd h' m' (mword_of_int 0xe3c) (4 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd Hpct Hinv Hs1.
    destruct Hinv as (Hsp & Hs0 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hfr).
    iIntros "#Hcode #Hb1 Hrun Hcont".
    assert (Hb0 : 0 <= bv_unsigned b0 < 256).
    { pose proof (bv_unsigned_in_range 8 b0) as HH.
      assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
      rewrite Em8 in HH. exact HH. }
    assert (Hi31 : 0 <= Z.of_nat i + 1 < Z31) by (unfold Z31; lia).
    (* ---- 0xe40  sext.w a5,s1 ---- *)
    assert (Es0 : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                  = mword_of_int 0)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Ea5c : sign_extend' 64
                     (subrange_vec_dec
                        (add_vec (m !!! Regidx s1_idx)
                           (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0)
                   = (mword_of_int (bv_unsigned b0) : mword 64)).
    { rewrite Hs1 Es0.
      assert (Hbw : 0 <= bv_unsigned b0 + 0 < Z31) by (unfold Z31; lia).
      rewrite (moi_addw (bv_unsigned b0) 0 Hbw).
      f_equal. lia. }
    iApply (wp_uk_addiw γt γd γs γfd h m (mword_of_int 0xe40)
              (mword_of_int 0 : mword 12) s1_idx a5_idx
              (mword_of_int (bv_unsigned b0)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ea5c))
              with "[] Hrun").
    { iApply (uis_shk_e40 with "Hcode"). }
    assert (E52c : add_vec_int (mword_of_int 0xe40 : mword 64) 4
                   = mword_of_int 0xe44)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E52c.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int (bv_unsigned b0) : mword 64)]> m).
    assert (Ha5_1 : m1 !!! Regidx a5_idx = mword_of_int (bv_unsigned b0))
      by exact (upd_eq m (Regidx a5_idx) (regval_into_reg _)).
    assert (Hs3_1 : m1 !!! Regidx s3_idx = zero_reg).
    { rewrite <- Hs3.
      exact (upd_ne m (Regidx a5_idx) (Regidx s3_idx) (regval_into_reg _)
               ltac:(vm_compute; discriminate)). }
    assert (Hs5_1 : m1 !!! Regidx s5_idx = mword_of_int 37).
    { rewrite <- Hs5.
      exact (upd_ne m (Regidx a5_idx) (Regidx s5_idx) (regval_into_reg _)
               ltac:(vm_compute; discriminate)). }
    assert (Hs1_1 : m1 !!! Regidx s1_idx = mword_of_int (bv_unsigned b0)).
    { rewrite <- Hs1.
      exact (upd_ne m (Regidx a5_idx) (Regidx s1_idx) (regval_into_reg _)
               ltac:(vm_compute; discriminate)). }
    assert (Hs6_1 : m1 !!! Regidx s6_idx = fd).
    { rewrite <- Hs6.
      exact (upd_ne m (Regidx a5_idx) (Regidx s6_idx) (regval_into_reg _)
               ltac:(vm_compute; discriminate)). }
    (* ---- 0xe44  bnez s3,0xe2a -- NOT taken, the state register is 0 ---- *)
    assert (Hnt : false = uv_btaken BNE (m1 !!! Regidx s3_idx) zero_reg)
      by (rewrite Hs3_1; vm_compute; reflexivity).
    iApply (wp_uk_btype0 γt γd γs γfd h1 m1 (mword_of_int 0xe44)
              (mword_of_int 8166 : mword 13) s3_idx BNE false
              (add_vec (mword_of_int 0xe44 : mword 64)
                 (sign_extend' 64 (mword_of_int 8166 : mword 13)))
              (4 + n) Hnt eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shk_e44 with "Hcode"). }
    assert (E530 : add_vec_int (mword_of_int 0xe44 : mword 64) 4
                   = mword_of_int 0xe48)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E530.
    iIntros (h2) "Hrun".
    (* ---- 0xe48  bne a5,s5,0xe20 -- TAKEN, the character is not '%' ---- *)
    assert (Ht : true = uv_btaken BNE (m1 !!! Regidx a5_idx) (m1 !!! Regidx s5_idx)).
    { rewrite Ha5_1 Hs5_1. cbn [uv_btaken].
      assert (Hb64 : 0 <= bv_unsigned b0 < Z64) by (unfold Z64; lia).
      assert (H3764 : 0 <= 37 < Z64) by (unfold Z64; lia).
      rewrite (moi_neq_vec (bv_unsigned b0) 37 Hb64 H3764).
      destruct (Z.eqb_spec (bv_unsigned b0) 37) as [He | _];
        [ exfalso; exact (Hpct He) | reflexivity ]. }
    assert (Etgt534 : add_vec (mword_of_int 0xe48 : mword 64)
                        (sign_extend' 64 (mword_of_int 8152 : mword 13))
                      = mword_of_int 0xe20)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_btype γt γd γs γfd h2 m1 (mword_of_int 0xe48)
              (mword_of_int 8152 : mword 13) s5_idx a5_idx BNE true
              (mword_of_int 0xe20) (4 + n) Ht (eq_sym Etgt534)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_e48 with "Hcode"). }
    iIntros (h3) "Hrun".
    (* ---- 0xe20  c.mv a1,s1 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h3 m1 (mword_of_int 0xe20) a1_idx s1_idx
              (add_vec zero_reg (m1 !!! Regidx s1_idx)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_e20 with "Hcode"). }
    assert (E50c : add_vec_int (mword_of_int 0xe20 : mword 64) 2
                   = mword_of_int 0xe22)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E50c.
    iIntros (h4) "Hrun".
    set (m2 := <[Regidx a1_idx
                 := regval_into_reg (add_vec zero_reg (m1 !!! Regidx s1_idx))]> m1).
    (* ---- 0xe22  c.mv a0,s6 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h4 m2 (mword_of_int 0xe22) a0_idx s6_idx
              (add_vec zero_reg (m2 !!! Regidx s6_idx)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_e22 with "Hcode"). }
    assert (E50e : add_vec_int (mword_of_int 0xe22 : mword 64) 2
                   = mword_of_int 0xe24)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E50e.
    iIntros (h5) "Hrun".
    set (m3 := <[Regidx a0_idx
                 := regval_into_reg (add_vec zero_reg (m2 !!! Regidx s6_idx))]> m2).
    (* ---- 0xe24  jal ra,0xd2e <putc> ---- *)
    pose proof shd_pin_putc as Hputc.
    iApply (wp_uk_jal γt γd γs γfd h5 m3 (mword_of_int 0xe24)
              (mword_of_int 2096906 : mword 21) ra_idx
              (mword_of_int ShSyms.putc) (mword_of_int 0xe28) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hputc; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hputc; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_e24 with "Hcode"). }
    iIntros (h6) "Hrun".
    set (m4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0xe28 : mword 64)]> m3).
    assert (Hra4 : m4 !!! Regidx ra_idx = (mword_of_int 0xe28 : mword 64))
      by exact (upd_eq m3 (Regidx ra_idx) (regval_into_reg _)).
    (* ---- putc(fd, c) ---- *)
    iApply (wp_kshd_putc γt γd γs γfd h6 m4 n with "Hcode Hrun").
    iIntros (h7 m5) "%Hcs Hrun".
    assert (Eret : ret_pc (m4 !!! Regidx ra_idx) = (mword_of_int 0xe28 : mword 64))
      by (rewrite Hra4; apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    (* the invariant crossed the call, because every register it names is
       callee-saved -- which is why ulib parked them there *)
    assert (Hinv5 : vp_inv m0 m5 sp0 a fd ap i).
    { apply (vp_inv_call m0 m4 m5 sp0 a fd ap i Hcs).
      apply (vp_inv_upd _ _ _ _ _ _ _ ra_idx _ ltac:(vm_compute; reflexivity)).
      apply (vp_inv_upd _ _ _ _ _ _ _ a0_idx _ ltac:(vm_compute; reflexivity)).
      apply (vp_inv_upd _ _ _ _ _ _ _ a1_idx _ ltac:(vm_compute; reflexivity)).
      apply (vp_inv_upd _ _ _ _ _ _ _ a5_idx _ ltac:(vm_compute; reflexivity)).
      unfold vp_inv. repeat (split; [ assumption | ]). exact Hfr. }
    destruct Hinv5 as (Hsp5 & Hs05 & Hs25 & Hs35 & Hs45 & Hs55 & Hs65 & Hs75 & Hs85 & Hfr5).
    (* ---- 0xe28  c.j 0xe2e ---- *)
    assert (Etgt514 : (mword_of_int 0xe2e : mword 64)
                      = add_vec (mword_of_int 0xe28 : mword 64)
                          (sign_extend' 64
                             (sign_extend' 21
                                (concat_vec (mword_of_int 3 : mword 11) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cj γt γd γs γfd h7 m5 (mword_of_int 0xe28)
              (mword_of_int 3 : mword 11) (mword_of_int 0xe2e) (4 + n)
              Etgt514 ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_e28 with "Hcode"). }
    iIntros (h8) "Hrun".
    (* ---- 0xe2e  addiw a5,s2,1 ---- *)
    assert (Es1_12 : (sign_extend' 64 (mword_of_int 1 : mword 12) : mword 64)
                     = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Ea5n : sign_extend' 64
                     (subrange_vec_dec
                        (add_vec (m5 !!! Regidx s2_idx)
                           (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0)
                   = (mword_of_int (Z.of_nat (S i)) : mword 64)).
    { rewrite Hs25 Es1_12.
      assert (Hiw : 0 <= Z.of_nat i + 1 < Z31) by (unfold Z31; lia).
      rewrite (moi_addw (Z.of_nat i) 1 Hiw).
      f_equal. lia. }
    iApply (wp_uk_addiw γt γd γs γfd h8 m5 (mword_of_int 0xe2e)
              (mword_of_int 1 : mword 12) s2_idx a5_idx
              (mword_of_int (Z.of_nat (S i))) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ea5n))
              with "[] Hrun").
    { iApply (uis_shk_e2e with "Hcode"). }
    assert (E51a : add_vec_int (mword_of_int 0xe2e : mword 64) 4
                   = mword_of_int 0xe32)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E51a.
    iIntros (h9) "Hrun".
    set (m6 := <[Regidx a5_idx
                 := regval_into_reg
                      (mword_of_int (Z.of_nat (S i)) : mword 64)]> m5).
    assert (Ha56 : m6 !!! Regidx a5_idx = mword_of_int (Z.of_nat (S i)))
      by exact (upd_eq m5 (Regidx a5_idx) (regval_into_reg _)).
    assert (Hinv6 : vp_inv m0 m6 sp0 a fd ap i)
      by (apply (vp_inv_upd _ _ _ _ _ _ _ a5_idx _ ltac:(vm_compute; reflexivity));
          unfold vp_inv; repeat (split; [ assumption | ]); exact Hfr5).
    (* ---- 0xe32  c.mv s2,a5 -- the index moves ---- *)
    assert (Ez6 : add_vec zero_reg (m6 !!! Regidx a5_idx)
                  = mword_of_int (Z.of_nat (S i)))
      by (rewrite Ha56; apply add_vec_zero_l).
    iApply (wp_uk_cmv γt γd γs γfd h9 m6 (mword_of_int 0xe32) s2_idx a5_idx
              (add_vec zero_reg (m6 !!! Regidx a5_idx)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_e32 with "Hcode"). }
    assert (E51e : add_vec_int (mword_of_int 0xe32 : mword 64) 2
                   = mword_of_int 0xe34)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E51e.
    iIntros (h10) "Hrun".
    set (m7 := <[Regidx s2_idx
                 := regval_into_reg (add_vec zero_reg (m6 !!! Regidx a5_idx))]> m6).
    assert (Hinv7 : vp_inv m0 m7 sp0 a fd ap (S i))
      by exact (vp_inv_bump m0 m6 sp0 a fd ap i (S i) _ Ez6 Hinv6).
    assert (Ha57 : m7 !!! Regidx a5_idx = mword_of_int (Z.of_nat (S i))).
    { rewrite <- Ha56.
      exact (upd_ne m6 (Regidx s2_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0xe34  c.mv a4,a5 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h10 m7 (mword_of_int 0xe34) a4_idx a5_idx
              (add_vec zero_reg (m7 !!! Regidx a5_idx)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_e34 with "Hcode"). }
    assert (E520 : add_vec_int (mword_of_int 0xe34 : mword 64) 2
                   = mword_of_int 0xe36)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E520.
    iIntros (h11) "Hrun".
    set (m8 := <[Regidx a4_idx
                 := regval_into_reg (add_vec zero_reg (m7 !!! Regidx a5_idx))]> m7).
    assert (Hinv8 : vp_inv m0 m8 sp0 a fd ap (S i))
      by exact (vp_inv_upd m0 m7 sp0 a fd ap (S i) a4_idx _
                  ltac:(vm_compute; reflexivity) Hinv7).
    assert (Ha58 : m8 !!! Regidx a5_idx = mword_of_int (Z.of_nat (S i))).
    { rewrite <- Ha57.
      exact (upd_ne m7 (Regidx a4_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    destruct Hinv8 as (Hsp8 & Hs08 & Hs28 & Hs38 & Hs48 & Hs58 & Hs68 & Hs78 & Hs88 & Hfr8).
    (* ---- 0xe36  c.add a5,a5,s4 -- the pointer ---- *)
    assert (Eadd8 : add_vec (m8 !!! Regidx a5_idx) (m8 !!! Regidx s4_idx)
                    = mword_of_int (a + Z.of_nat (S i))).
    { rewrite Ha58 Hs48. rewrite moi_add. f_equal. lia. }
    iApply (wp_uk_cadd γt γd γs γfd h11 m8 (mword_of_int 0xe36) a5_idx s4_idx
              (add_vec (m8 !!! Regidx a5_idx) (m8 !!! Regidx s4_idx)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_e36 with "Hcode"). }
    assert (E522 : add_vec_int (mword_of_int 0xe36 : mword 64) 2
                   = mword_of_int 0xe38)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E522.
    iIntros (h12) "Hrun".
    set (m9 := <[Regidx a5_idx
                 := regval_into_reg
                      (add_vec (m8 !!! Regidx a5_idx)
                         (m8 !!! Regidx s4_idx))]> m8).
    assert (Hinv9 : vp_inv m0 m9 sp0 a fd ap (S i)).
    { apply (vp_inv_upd _ _ _ _ _ _ _ a5_idx _ ltac:(vm_compute; reflexivity)).
      unfold vp_inv. repeat (split; [ assumption | ]). exact Hfr8. }
    assert (Ha59 : m9 !!! Regidx a5_idx = mword_of_int (a + Z.of_nat (S i))).
    { rewrite (upd_eq m8 (Regidx a5_idx) (regval_into_reg _)). exact Eadd8. }
    (* ---- 0xe38  lbu s1,0(a5) -- the NEXT character, out of .rodata ---- *)
    assert (Haddr : (a + Z.of_nat (S i))%Z
                    = uint (m9 !!! Regidx a5_idx)
                      + uoff_i12 (mword_of_int 0 : mword 12)).
    { rewrite Ha59.
      assert (Hb64a : 0 <= a + Z.of_nat (S i) < Z64) by (unfold Z64; lia).
      rewrite (uint_moi (a + Z.of_nat (S i)) Hb64a).
      replace (uoff_i12 (mword_of_int 0 : mword 12)) with 0
        by (vm_compute; reflexivity).
      lia. }
    iApply (wp_uk_lbu_text γt γd γs γfd h12 m9 (mword_of_int 0xe38)
              (mword_of_int 0 : mword 12) a5_idx s1_idx
              (a + Z.of_nat (S i)) b1 (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              Haddr ltac:(vm_compute; discriminate)
              with "[] Hb1 Hrun").
    { iApply (uis_shk_e38 with "Hcode"). }
    assert (E524 : add_vec_int (mword_of_int 0xe38 : mword 64) 4
                   = mword_of_int 0xe3c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E524.
    iIntros (h13) "Hrun".
    set (m10 := <[Regidx s1_idx
                  := regval_into_reg (zero_extend' 64 b1 : mword 64)]> m9).
    iApply ("Hcont" $! h13 m10 with "[] [] Hrun").
    { iPureIntro.
      exact (vp_inv_upd m0 m9 sp0 a fd ap (S i) s1_idx _
               ltac:(vm_compute; reflexivity) Hinv9). }
    { iPureIntro. rewrite /m10 (upd_eq m9 (Regidx s1_idx) (regval_into_reg _)).
      exact (zext8_moi b1). }
  Qed.


  (* --------------------------------------------------------------------- *)
  (* THE LOOP, by induction on the characters LEFT.  [k+1] of them remain,   *)
  (* the current one is [f i], and the round's own [beqz s1] at 0xe3c is     *)
  (* what decides: at [k = 0] the byte it just loaded is the terminator, so  *)
  (* the branch is taken and the walk falls into the epilogue; otherwise it  *)
  (* is a body byte, the branch is not taken, and the head at 0xe40 comes    *)
  (* round again one character further on.                                   *)
  (*                                                                        *)
  (* NOTE this is an ORDINARY induction, not a Löb: the string is finite and *)
  (* [utext_str] carries its length.  It is echo's [strlen] mold.            *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kshd_vprintf_loop (m0 : regfile) (sp0 fd ap : mword 64) (a : Z)
      (len : nat) (f : nat -> mword 8) (lo : nat) (k : nat) :
    0 <= a -> a + Z.of_nat len + 2 < 2 ^ 31 ->
    (* only the SUFFIX the walk covers has to be free of '%'.  A format
       string with a directive in it is walked by this same loop once the
       directive is behind it, and everything before [lo] is then somebody
       else's business. *)
    (forall j : nat, (lo <= j < len)%nat -> bv_unsigned (f j) <> 37) ->
    m0 !!! Regidx csp_rs1 = sp0 ->
    uint sp0 mod 8 = 0 ->
    96 <= uint sp0 ->
    forall (i : nat) (h : CpuId) (m : regfile) (n : nat),
      (lo <= i)%nat ->
      (i + S k)%nat = len ->
      vp_inv m0 m sp0 a fd ap i ->
      m !!! Regidx s1_idx = mword_of_int (bv_unsigned (f i)) ->
      shk_code γt -∗
      utext_str γt a len f -∗
      uword γd (uint sp0 - 8) (m0 !!! Regidx ra_idx) -∗
      uword γd (uint sp0 - 16) (m0 !!! Regidx s0_idx) -∗
      uword γd (uint sp0 - 24) (m0 !!! Regidx s1_idx) -∗
      uword γd (uint sp0 - 32) (m0 !!! Regidx s2_idx) -∗
      uword γd (uint sp0 - 40) (m0 !!! Regidx s3_idx) -∗
      uword γd (uint sp0 - 48) (m0 !!! Regidx s4_idx) -∗
      uword γd (uint sp0 - 56) (m0 !!! Regidx s5_idx) -∗
      uword γd (uint sp0 - 64) (m0 !!! Regidx s6_idx) -∗
      uword γd (uint sp0 - 72) (m0 !!! Regidx s7_idx) -∗
      uword γd (uint sp0 - 80) (m0 !!! Regidx s8_idx) -∗
      (∃ w : mword 64, uword γd (uint sp0 - 88) w) -∗
      (∃ w : mword 64, uword γd (uint sp0 - 96) w) -∗
      urun γt γd γs γfd h m (mword_of_int 0xe40) (4 + n) -∗
      (∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m0 m' ⌝ -∗
         urun γt γd γs γfd h' m' (ret_pc (m0 !!! Regidx ra_idx)) (12 + (4 + n)) -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd Hpct Hsp0 Hal8 Hlo.
    induction k as [| k IH ];
      intros i h m n Hlo_i Hik Hinv Hs1;
      iIntros "#Hcode #Hstr Hwra Hws0 Hws1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw11 Hw12 Hrun Hcont";
      iDestruct (utext_str_nonul with "Hstr") as %Hnn;
      assert (Hilt : (i < len)%nat) by lia.
    - (* the LAST character: the byte after it is the terminator *)
      assert (Ei : (S i)%nat = len) by lia.
      iDestruct (utext_str_nul with "Hstr") as "#Hnul".
      iApply (wp_kshd_vprintf_step m0 sp0 fd ap a i (f i) ubyte0 h m n
                Ha0 ltac:(lia) (Hpct i ltac:(lia)) Hinv Hs1
                with "Hcode [] Hrun").
      { rewrite Ei. iExact "Hnul". }
      iIntros (h1 m1) "%Hinv1 %Hs11 Hrun".
      (* ---- 0xe3c  beqz s1,0x1010 -- TAKEN: this was the terminator ---- *)
      assert (Ht : true = uv_btaken BEQ (m1 !!! Regidx s1_idx) zero_reg).
      { rewrite Hs11. cbn [uv_btaken].
        replace (bv_unsigned ubyte0) with 0 by (vm_compute; reflexivity).
        rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
      assert (Etgt : add_vec (mword_of_int 0xe3c : mword 64)
                       (sign_extend' 64 (mword_of_int 468 : mword 13))
                     = mword_of_int 0x1010)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_btype0 γt γd γs γfd h1 m1 (mword_of_int 0xe3c)
                (mword_of_int 468 : mword 13) s1_idx BEQ true
                (mword_of_int 0x1010) (4 + n) Ht (eq_sym Etgt)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_e3c with "Hcode"). }
      iIntros (h2) "Hrun".
      destruct Hinv1 as (Hsp1 & _ & _ & _ & _ & _ & _ & _ & _ & Hfr1).
      iApply (wp_kshd_vprintf_epi h2 m1 m0 sp0 (4 + n)
                Hsp1 Hsp0 Hal8 Hlo Hfr1
                with "Hcode Hwra Hws0 Hws1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw11 Hw12 Hrun Hcont").
    - (* a BODY character: the byte after it is one too *)
      assert (Hslt : (S i < len)%nat) by lia.
      iDestruct (utext_str_byte γt a len f (S i) Hslt with "Hstr") as "#Hb1".
      iApply (wp_kshd_vprintf_step m0 sp0 fd ap a i (f i) (f (S i)) h m n
                Ha0 ltac:(lia) (Hpct i ltac:(lia)) Hinv Hs1
                with "Hcode Hb1 Hrun").
      iIntros (h1 m1) "%Hinv1 %Hs11 Hrun".
      (* ---- 0xe3c  beqz s1,0x1010 -- NOT taken: a body byte is not NUL ---- *)
      assert (Hnz : bv_unsigned (f (S i)) <> 0).
      { intro He. apply (Hnn (S i) Hslt). apply bv_eq.
        rewrite He. vm_compute. reflexivity. }
      (* the inner assert is stated in the GOAL's spelling and closed by
         [exact]: [bv_unsigned_in_range 8] fixes the width index at [8 : N]
         while [f (S i) : mword 8] carries [Z_idx 8], and [lia] would see
         two atoms. *)
      assert (Hb1r : 0 <= bv_unsigned (f (S i)) < Z64).
      { assert (HH : 0 <= bv_unsigned (f (S i)) < 256).
        { pose proof (bv_unsigned_in_range 8 (f (S i))) as H0.
          assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
          rewrite Em8 in H0. exact H0. }
        unfold Z64. lia. }
      assert (Hnt : false = uv_btaken BEQ (m1 !!! Regidx s1_idx) zero_reg).
      { rewrite Hs11. cbn [uv_btaken].
        rewrite (moi_eq_zero (bv_unsigned (f (S i))) Hb1r).
        destruct (Z.eqb_spec (bv_unsigned (f (S i))) 0) as [He | _];
          [ exfalso; exact (Hnz He) | reflexivity ]. }
      iApply (wp_uk_btype0 γt γd γs γfd h1 m1 (mword_of_int 0xe3c)
                (mword_of_int 468 : mword 13) s1_idx BEQ false
                (add_vec (mword_of_int 0xe3c : mword 64)
                   (sign_extend' 64 (mword_of_int 468 : mword 13)))
                (4 + n) Hnt eq_refl ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shk_e3c with "Hcode"). }
      assert (E528 : add_vec_int (mword_of_int 0xe3c : mword 64) 4
                     = mword_of_int 0xe40)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E528.
      iIntros (h2) "Hrun".
      iApply (IH (S i) h2 m1 n ltac:(lia) ltac:(lia) Hinv1 Hs11
                with "Hcode Hstr Hwra Hws0 Hws1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw11 Hw12 Hrun Hcont").
  Qed.


  (* --------------------------------------------------------------------- *)
  (* THE PROLOGUE, 0xdea -> 0xe40.  Forty instructions that say nothing     *)
  (* about the format string: the frame is carved, twelve callee-saved      *)
  (* words are spilled, the four registers the loop reads are parked, and    *)
  (* fmt[0] is in s1.  Both top-level entries -- the plain one below and     *)
  (* the one that walks a '%s' -- start here, so it is proved once.          *)
  (*                                                                        *)
  (* The contract asks for a NON-EMPTY string.  None of sh's three formats  *)
  (* is empty, and taking [0 < len] deletes the whole                        *)
  (* 0xdf8 arm -- the one that jumps straight to the shared tail with s2..s8 *)
  (* never spilled.  [wp_kshd_vprintf_epi0] still states that arm's shape,  *)
  (* so re-admitting it later is a branch, not a rewrite.                    *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kshd_vprintf_pro (a : Z) (len : nat) (f : nat -> mword 8)
      (h : CpuId) (m : regfile) (n : nat) :
    0 <= a -> a + Z.of_nat len + 2 < 2 ^ 31 ->
    (0 < len)%nat ->
    m !!! Regidx a1_idx = mword_of_int a ->
    shk_code γt -∗
    utext_str γt a len f -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.vprintf) (12 + (4 + n)) -∗
    (∀ (h' : CpuId) (m' : regfile) (fd ap : mword 64),
       ⌜ uint (m !!! Regidx csp_rs1) mod 8 = 0 ⌝ -∗
       ⌜ 96 <= uint (m !!! Regidx csp_rs1) ⌝ -∗
       ⌜ vp_inv m m' (m !!! Regidx csp_rs1) a fd ap 0%nat ⌝ -∗
       ⌜ m' !!! Regidx s1_idx = mword_of_int (bv_unsigned (f 0%nat)) ⌝ -∗
       ⌜ ap = m !!! Regidx a2_idx ⌝ -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 8) (m !!! Regidx ra_idx) -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 16) (m !!! Regidx s0_idx) -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 24) (m !!! Regidx s1_idx) -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 32) (m !!! Regidx s2_idx) -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 40) (m !!! Regidx s3_idx) -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 48) (m !!! Regidx s4_idx) -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 56) (m !!! Regidx s5_idx) -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 64) (m !!! Regidx s6_idx) -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 72) (m !!! Regidx s7_idx) -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 80) (m !!! Regidx s8_idx) -∗
       (∃ w : mword 64, uword γd (uint (m !!! Regidx csp_rs1) - 88) w) -∗
       (∃ w : mword 64, uword γd (uint (m !!! Regidx csp_rs1) - 96) w) -∗
       urun γt γd γs γfd h' m' (mword_of_int 0xe40) (4 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd Hlen Ha1.
    iIntros "#Hcode #Hstr Hrun Hcont".
    iDestruct (utext_str_nonul with "Hstr") as %Hnn.
    pose proof shd_pin_vprintf as Hvprintf.
    rewrite Hvprintf.
    iDestruct (urun_stack with "Hrun") as %[Hal8' Hroom'].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0e.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0e).
    clear Hsp0e.
    assert (Hal8 : uint sp0 mod 8 = 0) by exact Hal8'.
    assert (Hlo : 96 <= uint sp0) by (clear -Hroom'; lia).
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                   = bv_unsigned sp0 - 96).
    { replace (- (8 * Z.of_nat 12)) with (-96) by lia.
      exact (uv_avi_neg sp0 96 ltac:(apply Z.leb_le; reflexivity)
               ltac:(rewrite <- uint_unsigned; exact Hlo)). }
    assert (Hsp96 : uint (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                    = uint sp0 - 96)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Ho88 : uoff_sdsp (mword_of_int 11 : mword 6) = 88)
      by (vm_compute; reflexivity).
    assert (Ho80 : uoff_sdsp (mword_of_int 10 : mword 6) = 80)
      by (vm_compute; reflexivity).
    assert (Ho72 : uoff_sdsp (mword_of_int 9 : mword 6) = 72)
      by (vm_compute; reflexivity).
    assert (Ho64 : uoff_sdsp (mword_of_int 8 : mword 6) = 64)
      by (vm_compute; reflexivity).
    assert (Ho56 : uoff_sdsp (mword_of_int 7 : mword 6) = 56)
      by (vm_compute; reflexivity).
    assert (Ho48 : uoff_sdsp (mword_of_int 6 : mword 6) = 48)
      by (vm_compute; reflexivity).
    assert (Ho40 : uoff_sdsp (mword_of_int 5 : mword 6) = 40)
      by (vm_compute; reflexivity).
    assert (Ho32 : uoff_sdsp (mword_of_int 4 : mword 6) = 32)
      by (vm_compute; reflexivity).
    assert (Ho24 : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
      by (vm_compute; reflexivity).
    assert (Ho16 : uoff_sdsp (mword_of_int 2 : mword 6) = 16)
      by (vm_compute; reflexivity).
    (* ---- 0xdea  c.addi16sp sp,sp,-96 -- THE PUSH ---- *)
    iApply (wp_uk_caddi16sp_dn γt γd γs γfd h m (mword_of_int 0xdea)
              (mword_of_int 58 : mword 6) 12 (4 + n)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_dea with "Hcode"). }
    iIntros "Hframe".
    assert (E4d6 : add_vec_int (mword_of_int 0xdea : mword 64) 2
                   = mword_of_int 0xdec)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp E4d6.
    iIntros (h0) "Hrun".
    set (mp1 := <[Regidx csp_rs1
                  := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 12)))]> m).
    assert (Hspp1 : mp1 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 12)))
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg _)).
    iDestruct (ustack_12_open with "Hframe")
      as "(_ & [%w1 Hw1] & [%w2 Hw2] & [%w3 Hw3] & [%w4 Hw4] & [%w5 Hw5]
            & [%w6 Hw6] & [%w7 Hw7] & [%w8 Hw8] & [%w9 Hw9] & [%w10 Hw10]
            & Hw11 & Hw12)".
    (* ---- 0xdec  c.sdsp ra,88(sp) ---- *)
    assert (Hrra_idx : mp1 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite /mp1. exact (upd_ne m (Regidx csp_rs1) (Regidx ra_idx) _
               ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_csdsp γt γd γs γfd h0 mp1 (mword_of_int 0xdec)
              (mword_of_int 11 : mword 6) ra_idx (uint sp0 - 8) w1 (4 + n)
              ltac:(rewrite Hspp1 Hsp96 Ho88; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw1 Hrun").
    { iApply (uis_shk_dec with "Hcode"). }
    iIntros "Hw1". rewrite Hrra_idx.
    assert (E4d8 : add_vec_int (mword_of_int 0xdec : mword 64) 2
                 = mword_of_int 0xdee)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4d8.
    iIntros (h1) "Hrun".
    (* ---- 0xdee  c.sdsp s0,80(sp) ---- *)
    assert (Hrs0_idx : mp1 !!! Regidx s0_idx = m !!! Regidx s0_idx).
    { rewrite /mp1. exact (upd_ne m (Regidx csp_rs1) (Regidx s0_idx) _
               ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_csdsp γt γd γs γfd h1 mp1 (mword_of_int 0xdee)
              (mword_of_int 10 : mword 6) s0_idx (uint sp0 - 16) w2 (4 + n)
              ltac:(rewrite Hspp1 Hsp96 Ho80; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw2 Hrun").
    { iApply (uis_shk_dee with "Hcode"). }
    iIntros "Hw2". rewrite Hrs0_idx.
    assert (E4da : add_vec_int (mword_of_int 0xdee : mword 64) 2
                 = mword_of_int 0xdf0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4da.
    iIntros (h2) "Hrun".
    (* ---- 0xdf0  c.sdsp s1,72(sp) ---- *)
    assert (Hrs1_idx : mp1 !!! Regidx s1_idx = m !!! Regidx s1_idx).
    { rewrite /mp1. exact (upd_ne m (Regidx csp_rs1) (Regidx s1_idx) _
               ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_csdsp γt γd γs γfd h2 mp1 (mword_of_int 0xdf0)
              (mword_of_int 9 : mword 6) s1_idx (uint sp0 - 24) w3 (4 + n)
              ltac:(rewrite Hspp1 Hsp96 Ho72; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw3 Hrun").
    { iApply (uis_shk_df0 with "Hcode"). }
    iIntros "Hw3". rewrite Hrs1_idx.
    assert (E4dc : add_vec_int (mword_of_int 0xdf0 : mword 64) 2
                 = mword_of_int 0xdf2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4dc.
    iIntros (h3) "Hrun".
    (* ---- 0xdf2  c.addi4spn s0,sp,96 -- s0 := the ENTRY sp ---- *)
    assert (Hlt12 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                    + 8 * Z.of_nat 12 < Z64).
    { assert (HR : 0 <= bv_unsigned sp0 < 18446744073709551616).
      { pose proof (bv_unsigned_in_range 64 sp0) as H0.
        assert (Em : bv_modulus 64 = 18446744073709551616)
          by (vm_compute; reflexivity).
        rewrite Em in H0. exact H0. }
      clear -Hbsp HR. rewrite Hbsp. unfold Z64. lia. }
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                    (8 * Z.of_nat 12) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                 (8 * Z.of_nat 12) ltac:(apply Z.leb_le; reflexivity) Hlt12).
      clear -Hbsp. rewrite Hbsp. lia. }
    assert (Ec4 : (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8))
                   : mword 64) = mword_of_int (8 * Z.of_nat 12))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi4spn γt γd γs γfd h3 mp1 (mword_of_int 0xdf2)
              (mword_of_int 0 : mword 3) (mword_of_int 24 : mword 8) s0_idx sp0
              (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hspp1 Ec4; exact (eq_sym Hup))
              with "[] Hrun").
    { iApply (uis_shk_df2 with "Hcode"). }
    assert (E4de : add_vec_int (mword_of_int 0xdf2 : mword 64) 2
                   = mword_of_int 0xdf4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4de.
    iIntros (h4) "Hrun".
    set (mp2 := <[Regidx s0_idx := regval_into_reg sp0]> mp1).
    (* ---- 0xdf4  lbu s1,0(a1) -- the FIRST character, out of .rodata ---- *)
    assert (Ha1p : mp2 !!! Regidx a1_idx = mword_of_int a).
    { rewrite <- Ha1. rewrite /mp2
        (upd_ne mp1 (Regidx s0_idx) (Regidx a1_idx) _
           ltac:(vm_compute; discriminate)).
      rewrite /mp1. exact (upd_ne m (Regidx csp_rs1) (Regidx a1_idx) _
                             ltac:(vm_compute; discriminate)). }
    assert (Ha64 : 0 <= a < Z64) by (unfold Z64; lia).
    assert (Haddr0 : a = uint (mp2 !!! Regidx a1_idx)
                         + uoff_i12 (mword_of_int 0 : mword 12)).
    { rewrite Ha1p (uint_moi a Ha64).
      replace (uoff_i12 (mword_of_int 0 : mword 12)) with 0
        by (vm_compute; reflexivity).
      lia. }
    iDestruct (utext_str_byte γt a len f 0%nat ltac:(lia) with "Hstr") as "#Hb0".
    replace (a + Z.of_nat 0)%Z with a in * by lia.
    iApply (wp_uk_lbu_text γt γd γs γfd h4 mp2 (mword_of_int 0xdf4)
              (mword_of_int 0 : mword 12) a1_idx s1_idx a (f 0%nat) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              Haddr0 ltac:(vm_compute; discriminate)
              with "[] Hb0 Hrun").
    { iApply (uis_shk_df4 with "Hcode"). }
    assert (E4e0 : add_vec_int (mword_of_int 0xdf4 : mword 64) 4
                   = mword_of_int 0xdf8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4e0.
    iIntros (h5) "Hrun".
    set (mp3 := <[Regidx s1_idx
                  := regval_into_reg (zero_extend' 64 (f 0%nat) : mword 64)]> mp2).
    assert (Hs1p : mp3 !!! Regidx s1_idx = mword_of_int (bv_unsigned (f 0%nat))).
    { rewrite /mp3 (upd_eq mp2 (Regidx s1_idx) (regval_into_reg _)).
      exact (zext8_moi (f 0%nat)). }
    (* ---- 0xdf8  beqz s1,0x101e -- NOT taken: the string is non-empty ---- *)
    assert (Hnz0 : bv_unsigned (f 0%nat) <> 0).
    { intro He. apply (Hnn 0%nat ltac:(lia)). apply bv_eq.
      rewrite He. vm_compute. reflexivity. }
    assert (Hb0r : 0 <= bv_unsigned (f 0%nat) < Z64).
    { assert (HH : 0 <= bv_unsigned (f 0%nat) < 256).
      { pose proof (bv_unsigned_in_range 8 (f 0%nat)) as H0.
        assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
        rewrite Em8 in H0. exact H0. }
      unfold Z64. lia. }
    assert (Hnt0 : false = uv_btaken BEQ (mp3 !!! Regidx s1_idx) zero_reg).
    { rewrite Hs1p. cbn [uv_btaken].
      rewrite (moi_eq_zero (bv_unsigned (f 0%nat)) Hb0r).
      destruct (Z.eqb_spec (bv_unsigned (f 0%nat)) 0) as [He | _];
        [ exfalso; exact (Hnz0 He) | reflexivity ]. }
    iApply (wp_uk_btype0 γt γd γs γfd h5 mp3 (mword_of_int 0xdf8)
              (mword_of_int 550 : mword 13) s1_idx BEQ false
              (add_vec (mword_of_int 0xdf8 : mword 64)
                 (sign_extend' 64 (mword_of_int 550 : mword 13)))
              (4 + n) Hnt0 eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shk_df8 with "Hcode"). }
    assert (E4e4 : add_vec_int (mword_of_int 0xdf8 : mword 64) 4
                   = mword_of_int 0xdfc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4e4.
    iIntros (h6) "Hrun".
    assert (Hspp3 : mp3 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hspp1.
      rewrite /mp3 (upd_ne mp2 (Regidx s1_idx) (Regidx csp_rs1) _
                      ltac:(vm_compute; discriminate)).
      rewrite /mp2. exact (upd_ne mp1 (Regidx s0_idx) (Regidx csp_rs1) _
                             ltac:(vm_compute; discriminate)). }
    (* ---- 0xdfc  c.sdsp s2,64(sp) ---- *)
    assert (Hrs2_idx : mp3 !!! Regidx s2_idx = m !!! Regidx s2_idx).
    { rewrite /mp3 (upd_ne mp2 (Regidx s1_idx) (Regidx s2_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp2 (upd_ne mp1 (Regidx s0_idx) (Regidx s2_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp1. exact (upd_ne m (Regidx csp_rs1) (Regidx s2_idx) _
               ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_csdsp γt γd γs γfd h6 mp3 (mword_of_int 0xdfc)
              (mword_of_int 8 : mword 6) s2_idx (uint sp0 - 32) w4 (4 + n)
              ltac:(rewrite Hspp3 Hsp96 Ho64; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw4 Hrun").
    { iApply (uis_shk_dfc with "Hcode"). }
    iIntros "Hw4". rewrite Hrs2_idx.
    assert (E4e8 : add_vec_int (mword_of_int 0xdfc : mword 64) 2
                 = mword_of_int 0xdfe)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4e8.
    iIntros (h7) "Hrun".
    (* ---- 0xdfe  c.sdsp s3,56(sp) ---- *)
    assert (Hrs3_idx : mp3 !!! Regidx s3_idx = m !!! Regidx s3_idx).
    { rewrite /mp3 (upd_ne mp2 (Regidx s1_idx) (Regidx s3_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp2 (upd_ne mp1 (Regidx s0_idx) (Regidx s3_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp1. exact (upd_ne m (Regidx csp_rs1) (Regidx s3_idx) _
               ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_csdsp γt γd γs γfd h7 mp3 (mword_of_int 0xdfe)
              (mword_of_int 7 : mword 6) s3_idx (uint sp0 - 40) w5 (4 + n)
              ltac:(rewrite Hspp3 Hsp96 Ho56; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw5 Hrun").
    { iApply (uis_shk_dfe with "Hcode"). }
    iIntros "Hw5". rewrite Hrs3_idx.
    assert (E4ea : add_vec_int (mword_of_int 0xdfe : mword 64) 2
                 = mword_of_int 0xe00)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4ea.
    iIntros (h8) "Hrun".
    (* ---- 0xe00  c.sdsp s4,48(sp) ---- *)
    assert (Hrs4_idx : mp3 !!! Regidx s4_idx = m !!! Regidx s4_idx).
    { rewrite /mp3 (upd_ne mp2 (Regidx s1_idx) (Regidx s4_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp2 (upd_ne mp1 (Regidx s0_idx) (Regidx s4_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp1. exact (upd_ne m (Regidx csp_rs1) (Regidx s4_idx) _
               ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_csdsp γt γd γs γfd h8 mp3 (mword_of_int 0xe00)
              (mword_of_int 6 : mword 6) s4_idx (uint sp0 - 48) w6 (4 + n)
              ltac:(rewrite Hspp3 Hsp96 Ho48; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw6 Hrun").
    { iApply (uis_shk_e00 with "Hcode"). }
    iIntros "Hw6". rewrite Hrs4_idx.
    assert (E4ec : add_vec_int (mword_of_int 0xe00 : mword 64) 2
                 = mword_of_int 0xe02)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4ec.
    iIntros (h9) "Hrun".
    (* ---- 0xe02  c.sdsp s5,40(sp) ---- *)
    assert (Hrs5_idx : mp3 !!! Regidx s5_idx = m !!! Regidx s5_idx).
    { rewrite /mp3 (upd_ne mp2 (Regidx s1_idx) (Regidx s5_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp2 (upd_ne mp1 (Regidx s0_idx) (Regidx s5_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp1. exact (upd_ne m (Regidx csp_rs1) (Regidx s5_idx) _
               ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_csdsp γt γd γs γfd h9 mp3 (mword_of_int 0xe02)
              (mword_of_int 5 : mword 6) s5_idx (uint sp0 - 56) w7 (4 + n)
              ltac:(rewrite Hspp3 Hsp96 Ho40; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw7 Hrun").
    { iApply (uis_shk_e02 with "Hcode"). }
    iIntros "Hw7". rewrite Hrs5_idx.
    assert (E4ee : add_vec_int (mword_of_int 0xe02 : mword 64) 2
                 = mword_of_int 0xe04)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4ee.
    iIntros (h10) "Hrun".
    (* ---- 0xe04  c.sdsp s6,32(sp) ---- *)
    assert (Hrs6_idx : mp3 !!! Regidx s6_idx = m !!! Regidx s6_idx).
    { rewrite /mp3 (upd_ne mp2 (Regidx s1_idx) (Regidx s6_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp2 (upd_ne mp1 (Regidx s0_idx) (Regidx s6_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp1. exact (upd_ne m (Regidx csp_rs1) (Regidx s6_idx) _
               ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_csdsp γt γd γs γfd h10 mp3 (mword_of_int 0xe04)
              (mword_of_int 4 : mword 6) s6_idx (uint sp0 - 64) w8 (4 + n)
              ltac:(rewrite Hspp3 Hsp96 Ho32; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw8 Hrun").
    { iApply (uis_shk_e04 with "Hcode"). }
    iIntros "Hw8". rewrite Hrs6_idx.
    assert (E4f0 : add_vec_int (mword_of_int 0xe04 : mword 64) 2
                 = mword_of_int 0xe06)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4f0.
    iIntros (h11) "Hrun".
    (* ---- 0xe06  c.sdsp s7,24(sp) ---- *)
    assert (Hrs7_idx : mp3 !!! Regidx s7_idx = m !!! Regidx s7_idx).
    { rewrite /mp3 (upd_ne mp2 (Regidx s1_idx) (Regidx s7_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp2 (upd_ne mp1 (Regidx s0_idx) (Regidx s7_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp1. exact (upd_ne m (Regidx csp_rs1) (Regidx s7_idx) _
               ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_csdsp γt γd γs γfd h11 mp3 (mword_of_int 0xe06)
              (mword_of_int 3 : mword 6) s7_idx (uint sp0 - 72) w9 (4 + n)
              ltac:(rewrite Hspp3 Hsp96 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw9 Hrun").
    { iApply (uis_shk_e06 with "Hcode"). }
    iIntros "Hw9". rewrite Hrs7_idx.
    assert (E4f2 : add_vec_int (mword_of_int 0xe06 : mword 64) 2
                 = mword_of_int 0xe08)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4f2.
    iIntros (h12) "Hrun".
    (* ---- 0xe08  c.sdsp s8,16(sp) ---- *)
    assert (Hrs8_idx : mp3 !!! Regidx s8_idx = m !!! Regidx s8_idx).
    { rewrite /mp3 (upd_ne mp2 (Regidx s1_idx) (Regidx s8_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp2 (upd_ne mp1 (Regidx s0_idx) (Regidx s8_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp1. exact (upd_ne m (Regidx csp_rs1) (Regidx s8_idx) _
               ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_csdsp γt γd γs γfd h12 mp3 (mword_of_int 0xe08)
              (mword_of_int 2 : mword 6) s8_idx (uint sp0 - 80) w10 (4 + n)
              ltac:(rewrite Hspp3 Hsp96 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw10 Hrun").
    { iApply (uis_shk_e08 with "Hcode"). }
    iIntros "Hw10". rewrite Hrs8_idx.
    assert (E4f4 : add_vec_int (mword_of_int 0xe08 : mword 64) 2
                 = mword_of_int 0xe0a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4f4.
    iIntros (h13) "Hrun".
    (* ---- 0xe0a  c.mv s6,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h13 mp3 (mword_of_int 0xe0a) s6_idx a0_idx
              (add_vec zero_reg (mp3 !!! Regidx a0_idx)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_e0a with "Hcode"). }
    assert (E4f6 : add_vec_int (mword_of_int 0xe0a : mword 64) 2
                 = mword_of_int 0xe0c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4f6.
    iIntros (h14) "Hrun".
    set (mp4 := <[Regidx s6_idx := regval_into_reg (add_vec zero_reg (mp3 !!! Regidx a0_idx))]> mp3).
    (* ---- 0xe0c  c.mv s4,a1 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h14 mp4 (mword_of_int 0xe0c) s4_idx a1_idx
              (add_vec zero_reg (mp4 !!! Regidx a1_idx)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_e0c with "Hcode"). }
    assert (E4f8 : add_vec_int (mword_of_int 0xe0c : mword 64) 2
                 = mword_of_int 0xe0e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4f8.
    iIntros (h15) "Hrun".
    set (mp5 := <[Regidx s4_idx := regval_into_reg (add_vec zero_reg (mp4 !!! Regidx a1_idx))]> mp4).
    (* ---- 0xe0e  c.mv s7,a2 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h15 mp5 (mword_of_int 0xe0e) s7_idx a2_idx
              (add_vec zero_reg (mp5 !!! Regidx a2_idx)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_e0e with "Hcode"). }
    assert (E4fa : add_vec_int (mword_of_int 0xe0e : mword 64) 2
                 = mword_of_int 0xe10)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4fa.
    iIntros (h16) "Hrun".
    set (mp6 := <[Regidx s7_idx := regval_into_reg (add_vec zero_reg (mp5 !!! Regidx a2_idx))]> mp5).
    (* ---- 0xe10  c.li s3,0 ---- *)
    iApply (wp_uk_cli γt γd γs γfd h16 mp6 (mword_of_int 0xe10)
              (mword_of_int 0 : mword 6) s3_idx (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_e10 with "Hcode"). }
    assert (E4fc : add_vec_int (mword_of_int 0xe10 : mword 64) 2
                 = mword_of_int 0xe12)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4fc.
    iIntros (h17) "Hrun".
    set (mp7 := <[Regidx s3_idx := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64)]> mp6).
    (* ---- 0xe12  c.li s2,0 ---- *)
    iApply (wp_uk_cli γt γd γs γfd h17 mp7 (mword_of_int 0xe12)
              (mword_of_int 0 : mword 6) s2_idx (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_e12 with "Hcode"). }
    assert (E4fe : add_vec_int (mword_of_int 0xe12 : mword 64) 2
                 = mword_of_int 0xe14)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4fe.
    iIntros (h18) "Hrun".
    set (mp8 := <[Regidx s2_idx := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64)]> mp7).
    (* ---- 0xe14  c.li a4,0 ---- *)
    iApply (wp_uk_cli γt γd γs γfd h18 mp8 (mword_of_int 0xe14)
              (mword_of_int 0 : mword 6) a4_idx (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_e14 with "Hcode"). }
    assert (E500 : add_vec_int (mword_of_int 0xe14 : mword 64) 2
                 = mword_of_int 0xe16)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E500.
    iIntros (h19) "Hrun".
    set (mp9 := <[Regidx a4_idx := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64)]> mp8).
    (* ---- 0xe16  li s5,37 ---- *)
    iApply (wp_uk_li γt γd γs γfd h19 mp9 (mword_of_int 0xe16)
              (mword_of_int 37 : mword 12) s5_idx
              (add_vec zero_reg (sign_extend' 64 (mword_of_int 37 : mword 12))) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_shk_e16 with "Hcode"). }
    assert (E502 : add_vec_int (mword_of_int 0xe16 : mword 64) 4
                 = mword_of_int 0xe1a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E502.
    iIntros (h20) "Hrun".
    set (mp10 := <[Regidx s5_idx := regval_into_reg (add_vec zero_reg (sign_extend' 64 (mword_of_int 37 : mword 12)))]> mp9).
    (* ---- 0xe1a  li s8,100 ---- *)
    iApply (wp_uk_li γt γd γs γfd h20 mp10 (mword_of_int 0xe1a)
              (mword_of_int 100 : mword 12) s8_idx
              (add_vec zero_reg (sign_extend' 64 (mword_of_int 100 : mword 12))) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_shk_e1a with "Hcode"). }
    assert (E506 : add_vec_int (mword_of_int 0xe1a : mword 64) 4
                 = mword_of_int 0xe1e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E506.
    iIntros (h21) "Hrun".
    set (mp11 := <[Regidx s8_idx := regval_into_reg (add_vec zero_reg (sign_extend' 64 (mword_of_int 100 : mword 12)))]> mp10).
    (* ---- 0xe1e  c.j 0xe40 -- into the loop ---- *)
    assert (Etgt50a : (mword_of_int 0xe40 : mword 64)
                      = add_vec (mword_of_int 0xe1e : mword 64)
                          (sign_extend' 64
                             (sign_extend' 21
                                (concat_vec (mword_of_int 17 : mword 11) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cj γt γd γs γfd h21 mp11 (mword_of_int 0xe1e)
              (mword_of_int 17 : mword 11) (mword_of_int 0xe40) (4 + n)
              Etgt50a ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_e1e with "Hcode"). }
    iIntros (h22) "Hrun".

    (* the argument registers, as they stand when the moves read them *)
    assert (Ha1p4 : mp4 !!! Regidx a1_idx = mword_of_int a).
    { rewrite <- Ha1p.
      rewrite /mp4. exact (upd_ne mp3 (Regidx s6_idx) (Regidx a1_idx) _
                             ltac:(vm_compute; discriminate)). }
    assert (Hz_csp_rs1 : mp11 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    {
      rewrite /mp11 (upd_ne mp10 (Regidx s8_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp10 (upd_ne mp9 (Regidx s5_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp9 (upd_ne mp8 (Regidx a4_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp8 (upd_ne mp7 (Regidx s2_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp7 (upd_ne mp6 (Regidx s3_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp6 (upd_ne mp5 (Regidx s7_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp5 (upd_ne mp4 (Regidx s4_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp4 (upd_ne mp3 (Regidx s6_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp3 (upd_ne mp2 (Regidx s1_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp2 (upd_ne mp1 (Regidx s0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp1 (upd_eq m (Regidx csp_rs1) _).
      reflexivity.
    }
    assert (Hz_s0_idx : mp11 !!! Regidx s0_idx = sp0).
    {
      rewrite /mp11 (upd_ne mp10 (Regidx s8_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp10 (upd_ne mp9 (Regidx s5_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp9 (upd_ne mp8 (Regidx a4_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp8 (upd_ne mp7 (Regidx s2_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp7 (upd_ne mp6 (Regidx s3_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp6 (upd_ne mp5 (Regidx s7_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp5 (upd_ne mp4 (Regidx s4_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp4 (upd_ne mp3 (Regidx s6_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp3 (upd_ne mp2 (Regidx s1_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp2 (upd_eq mp1 (Regidx s0_idx) _).
      reflexivity.
    }
    assert (Hz_s2_idx : mp11 !!! Regidx s2_idx = mword_of_int (Z.of_nat 0)).
    {
      rewrite /mp11 (upd_ne mp10 (Regidx s8_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp10 (upd_ne mp9 (Regidx s5_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp9 (upd_ne mp8 (Regidx a4_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp8 (upd_eq mp7 (Regidx s2_idx) _).
      apply bv_eq; vm_compute; reflexivity.
    }
    assert (Hz_s3_idx : mp11 !!! Regidx s3_idx = zero_reg).
    {
      rewrite /mp11 (upd_ne mp10 (Regidx s8_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp10 (upd_ne mp9 (Regidx s5_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp9 (upd_ne mp8 (Regidx a4_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp8 (upd_ne mp7 (Regidx s2_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp7 (upd_eq mp6 (Regidx s3_idx) _).
      rewrite zero_reg_moi. apply bv_eq; vm_compute; reflexivity.
    }
    assert (Hz_s4_idx : mp11 !!! Regidx s4_idx = mword_of_int a).
    {
      rewrite /mp11 (upd_ne mp10 (Regidx s8_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp10 (upd_ne mp9 (Regidx s5_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp9 (upd_ne mp8 (Regidx a4_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp8 (upd_ne mp7 (Regidx s2_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp7 (upd_ne mp6 (Regidx s3_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp6 (upd_ne mp5 (Regidx s7_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp5 (upd_eq mp4 (Regidx s4_idx) _).
      rewrite Ha1p4. apply add_vec_zero_l.
    }
    assert (Hz_s5_idx : mp11 !!! Regidx s5_idx = mword_of_int 37).
    {
      rewrite /mp11 (upd_ne mp10 (Regidx s8_idx) (Regidx s5_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp10 (upd_eq mp9 (Regidx s5_idx) _).
      rewrite add_vec_zero_l. apply bv_eq; vm_compute; reflexivity.
    }
    assert (Hz_s6_idx : mp11 !!! Regidx s6_idx = add_vec zero_reg (mp3 !!! Regidx a0_idx)).
    {
      rewrite /mp11 (upd_ne mp10 (Regidx s8_idx) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp10 (upd_ne mp9 (Regidx s5_idx) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp9 (upd_ne mp8 (Regidx a4_idx) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp8 (upd_ne mp7 (Regidx s2_idx) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp7 (upd_ne mp6 (Regidx s3_idx) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp6 (upd_ne mp5 (Regidx s7_idx) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp5 (upd_ne mp4 (Regidx s4_idx) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp4 (upd_eq mp3 (Regidx s6_idx) _).
      reflexivity.
    }
    assert (Hz_s7_idx : mp11 !!! Regidx s7_idx
                        = add_vec zero_reg (mp5 !!! Regidx a2_idx)).
    {
      rewrite /mp11 (upd_ne mp10 (Regidx s8_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp10 (upd_ne mp9 (Regidx s5_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp9 (upd_ne mp8 (Regidx a4_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp8 (upd_ne mp7 (Regidx s2_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp7 (upd_ne mp6 (Regidx s3_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp6 (upd_eq mp5 (Regidx s7_idx) _).
      reflexivity.
    }
    assert (Hz_s8_idx : mp11 !!! Regidx s8_idx = mword_of_int 100).
    {
      rewrite /mp11 (upd_eq mp10 (Regidx s8_idx) _).
      rewrite add_vec_zero_l. apply bv_eq; vm_compute; reflexivity.
    }
    assert (Hinv0 : vp_inv m mp11 sp0 a
                      (add_vec zero_reg (mp3 !!! Regidx a0_idx))
                      (add_vec zero_reg (mp5 !!! Regidx a2_idx)) 0%nat).
    { unfold vp_inv.
      split; [ exact Hz_csp_rs1 | ].
      split; [ exact Hz_s0_idx | ].
      split; [ exact Hz_s2_idx | ].
      split; [ exact Hz_s3_idx | ].
      split; [ exact Hz_s4_idx | ].
      split; [ exact Hz_s5_idx | ].
      split; [ exact Hz_s6_idx | ].
      split; [ exact Hz_s7_idx | ].
      split; [ exact Hz_s8_idx | ].
      intros r Hr Hset.
      rewrite /mp11 (upd_ne mp10 (Regidx s8_idx) (Regidx r) _
                 ltac:(apply not_eq_sym; apply uidx_ne;
                       replace (uint s8_idx) with 24
                         by (vm_compute; reflexivity); lia)).
      rewrite /mp10 (upd_ne mp9 (Regidx s5_idx) (Regidx r) _
                 ltac:(apply not_eq_sym; apply uidx_ne;
                       replace (uint s5_idx) with 21
                         by (vm_compute; reflexivity); lia)).
      rewrite /mp9 (upd_ne mp8 (Regidx a4_idx) (Regidx r) _
                 ltac:(apply not_eq_sym; apply uidx_ne;
                       replace (uint a4_idx) with 14
                         by (vm_compute; reflexivity); lia)).
      rewrite /mp8 (upd_ne mp7 (Regidx s2_idx) (Regidx r) _
                 ltac:(apply not_eq_sym; apply uidx_ne;
                       replace (uint s2_idx) with 18
                         by (vm_compute; reflexivity); lia)).
      rewrite /mp7 (upd_ne mp6 (Regidx s3_idx) (Regidx r) _
                 ltac:(apply not_eq_sym; apply uidx_ne;
                       replace (uint s3_idx) with 19
                         by (vm_compute; reflexivity); lia)).
      rewrite /mp6 (upd_ne mp5 (Regidx s7_idx) (Regidx r) _
                 ltac:(apply not_eq_sym; apply uidx_ne;
                       replace (uint s7_idx) with 23
                         by (vm_compute; reflexivity); lia)).
      rewrite /mp5 (upd_ne mp4 (Regidx s4_idx) (Regidx r) _
                 ltac:(apply not_eq_sym; apply uidx_ne;
                       replace (uint s4_idx) with 20
                         by (vm_compute; reflexivity); lia)).
      rewrite /mp4 (upd_ne mp3 (Regidx s6_idx) (Regidx r) _
                 ltac:(apply not_eq_sym; apply uidx_ne;
                       replace (uint s6_idx) with 22
                         by (vm_compute; reflexivity); lia)).
      rewrite /mp3 (upd_ne mp2 (Regidx s1_idx) (Regidx r) _
                 ltac:(apply not_eq_sym; apply uidx_ne;
                       replace (uint s1_idx) with 9
                         by (vm_compute; reflexivity); lia)).
      rewrite /mp2 (upd_ne mp1 (Regidx s0_idx) (Regidx r) _
                 ltac:(apply not_eq_sym; apply uidx_ne;
                       replace (uint s0_idx) with 8
                         by (vm_compute; reflexivity); lia)).
      rewrite /mp1 (upd_ne m (Regidx csp_rs1) (Regidx r) _
                 ltac:(apply not_eq_sym; apply uidx_ne;
                       replace (uint csp_rs1) with 2
                         by (vm_compute; reflexivity); lia)).
      reflexivity. }
    assert (Hs1z : mp11 !!! Regidx s1_idx = mword_of_int (bv_unsigned (f 0%nat))).
    { rewrite <- Hs1p.
      rewrite /mp11 (upd_ne mp10 (Regidx s8_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp10 (upd_ne mp9 (Regidx s5_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp9 (upd_ne mp8 (Regidx a4_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp8 (upd_ne mp7 (Regidx s2_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp7 (upd_ne mp6 (Regidx s3_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp6 (upd_ne mp5 (Regidx s7_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp5 (upd_ne mp4 (Regidx s4_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp4 (upd_ne mp3 (Regidx s6_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      reflexivity. }
    iApply ("Hcont" $! h22 mp11
              (add_vec zero_reg (mp3 !!! Regidx a0_idx))
              (add_vec zero_reg (mp5 !!! Regidx a2_idx))
              with "[] [] [] [] [] Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10
                    Hw11 Hw12 Hrun").
    - iPureIntro. exact Hal8.
    - iPureIntro. exact Hlo.
    - iPureIntro. exact Hinv0.
    - iPureIntro. exact Hs1z.
    - iPureIntro.
      rewrite /mp5 (upd_ne mp4 (Regidx s4_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp4 (upd_ne mp3 (Regidx s6_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp3 (upd_ne mp2 (Regidx s1_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp2 (upd_ne mp1 (Regidx s0_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp1 (upd_ne m (Regidx csp_rs1) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      apply add_vec_zero_l.
  Qed.


  (* --------------------------------------------------------------------- *)
  (* vprintf(fd, fmt, ap) @0xdea, for a format string with no '%'.           *)
  (*                                                                        *)
  (* The contract asks for a NON-EMPTY string.  None of sh's three formats  *)
  (* is empty, and taking [0 < len] deletes the whole                        *)
  (* 0xdf8 arm -- the one that jumps straight to the shared tail with s2..s8 *)
  (* never spilled.  [wp_kshd_vprintf_epi0] still states that arm's shape,  *)
  (* so re-admitting it later is a branch, not a rewrite.                    *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kshd_vprintf (a : Z) (len : nat) (f : nat -> mword 8)
      (h : CpuId) (m : regfile) (n : nat) :
    0 <= a -> a + Z.of_nat len + 2 < 2 ^ 31 ->
    (0 < len)%nat ->
    (forall j : nat, (j < len)%nat -> bv_unsigned (f j) <> 37) ->
    m !!! Regidx a1_idx = mword_of_int a ->
    shk_code γt -∗
    utext_str γt a len f -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.vprintf) (12 + (4 + n)) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ ucallee_saved m m' ⌝ -∗
       urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (12 + (4 + n)) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd Hlen Hpct Ha1.
    iIntros "#Hcode #Hstr Hrun Hcont".
    iApply (wp_kshd_vprintf_pro a len f h m n Ha0 Habnd Hlen Ha1
              with "Hcode Hstr Hrun").
    iIntros (h' m' fd ap) "%Hal8 %Hlo %Hinv0 %Hs1z %Hap
                           Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10
                           Hw11 Hw12 Hrun".
    assert (Hk0 : (0 + S (len - 1))%nat = len) by lia.
    iApply (wp_kshd_vprintf_loop m (m !!! Regidx csp_rs1) fd ap a len f
              0%nat (len - 1)%nat Ha0 Habnd ltac:(intros j Hj; apply Hpct; lia)
              eq_refl Hal8 Hlo 0%nat h' m' n ltac:(lia) Hk0 Hinv0 Hs1z
              with "Hcode Hstr Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hrun Hcont").
  Qed.


End UkShDiagVprintf.

(* ===================================================================== *)
(* §4 vprintf's '%s' ARM, which is the one ALL THREE of sh's diagnostics  *)
(* take:                                                                  *)
(*                                                                        *)
(*     fprintf(2, "%s\n", s);                    -- panic                 *)
(*     fprintf(2, "exec %s failed\n", argv[0]);   -- runcmd's EXEC arm     *)
(*     fprintf(2, "open %s failed\n", file);      -- runcmd's REDIR arm    *)
(*                                                                        *)
(* Reaching its [putc] takes three                                        *)
(* things this file supplies: a walk of the plain prefix that STOPS at    *)
(* the '%' instead of running to the terminator; the thirty-instruction   *)
(* dispatch chain that decides, one character class at a time, that this  *)
(* directive is an 's'; and the inner loop over the argument string.      *)
(*                                                                        *)
(* The dispatch is specialised to c0 = 's'.  That is not a shortcut       *)
(* around the branches -- every one of them is stepped -- but a choice of *)
(* what to state: with c0 fixed, each test's outcome is decided by one    *)
(* [vm_compute] on a concrete pair, where a proof general in c0 would     *)
(* have to carry the whole state machine's case analysis for arms sh      *)
(* never enters.                                                          *)
(* ===================================================================== *)

Section UkShDiagVprintfS.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context (γt γd γs γfd : gname).

  (* WHICH HALF OF THE HEAP THE '%s' ARGUMENT LIVES IN.  cat's is a heap
     string ([ustr] at γd); sh's [panic] prints a .rodata literal
     ([utext_str] at γt).  The walk reads it in exactly one way -- one byte
     at a time at a known index -- so the two are ONE proof over this
     boolean; see UkShDiag.v §0a. *)
  Context (tx : bool).

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

  (* --------------------------------------------------------------------- *)
  (* A RUN OF PLAIN CHARACTERS, 0xe40 -> 0xe40.                             *)
  (*                                                                        *)
  (* [wp_kshd_vprintf_loop] walks a format string with no '%' from an index *)
  (* all the way to its terminator, and ends in the epilogue.  A format     *)
  (* that HAS a '%' needs the same walk stopped short -- at the '%', with   *)
  (* the frame still spilled and the loop still to run.  This is that walk. *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kshd_vprintf_seg (m0 : regfile) (sp0 fd ap : mword 64) (a : Z)
      (len : nat) (f : nat -> mword 8) (k : nat) :
    0 <= a -> a + Z.of_nat len + 2 < 2 ^ 31 ->
    forall (i0 : nat) (h : CpuId) (m : regfile) (n : nat),
      (i0 + k < len)%nat ->
      (forall j : nat, (i0 <= j < i0 + k)%nat -> bv_unsigned (f j) <> 37) ->
      vp_inv m0 m sp0 a fd ap i0 ->
      m !!! Regidx s1_idx = mword_of_int (bv_unsigned (f i0)) ->
      shk_code γt -∗
      utext_str γt a len f -∗
      urun γt γd γs γfd h m (mword_of_int 0xe40) (4 + n) -∗
      (∀ (h' : CpuId) (m' : regfile),
         ⌜ vp_inv m0 m' sp0 a fd ap (i0 + k)%nat ⌝ -∗
         ⌜ m' !!! Regidx s1_idx
           = mword_of_int (bv_unsigned (f (i0 + k)%nat)) ⌝ -∗
         urun γt γd γs γfd h' m' (mword_of_int 0xe40) (4 + n) -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd.
    induction k as [| k IH ];
      intros i0 h m n Hlt Hpct Hinv Hs1;
      iIntros "#Hcode #Hstr Hrun Hcont";
      iDestruct (utext_str_nonul with "Hstr") as %Hnn.
    - (* nothing to walk *)
      rewrite Nat.add_0_r.
      iApply ("Hcont" $! h m with "[] [] Hrun"); iPureIntro;
        [ exact Hinv | exact Hs1 ].
    - (* one plain round, then the rest *)
      assert (Hslt : (S i0 < len)%nat) by lia.
      iDestruct (utext_str_byte γt a len f (S i0) Hslt with "Hstr") as "#Hb1".
      iApply (wp_kshd_vprintf_step γt γd γs γfd m0 sp0 fd ap a i0 (f i0)
                (f (S i0)) h m n Ha0 ltac:(lia) (Hpct i0 ltac:(lia)) Hinv Hs1
                with "Hcode Hb1 Hrun").
      iIntros (h1 m1) "%Hinv1 %Hs11 Hrun".
      (* ---- 0xe3c  beqz s1,0x1010 -- NOT taken: a body byte is not NUL ---- *)
      assert (Hnz : bv_unsigned (f (S i0)) <> 0).
      { intro He. apply (Hnn (S i0) Hslt). apply bv_eq.
        rewrite He. vm_compute. reflexivity. }
      assert (Hb1r : 0 <= bv_unsigned (f (S i0)) < Z64).
      { assert (HH : 0 <= bv_unsigned (f (S i0)) < 256).
        { pose proof (bv_unsigned_in_range 8 (f (S i0))) as H0.
          assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
          rewrite Em8 in H0. exact H0. }
        unfold Z64. lia. }
      assert (Hnt : false = uv_btaken BEQ (m1 !!! Regidx s1_idx) zero_reg).
      { rewrite Hs11. cbn [uv_btaken].
        rewrite (moi_eq_zero (bv_unsigned (f (S i0))) Hb1r).
        destruct (Z.eqb_spec (bv_unsigned (f (S i0))) 0) as [He | _];
          [ exfalso; exact (Hnz He) | reflexivity ]. }
      iApply (wp_uk_btype0 γt γd γs γfd h1 m1 (mword_of_int 0xe3c)
                (mword_of_int 468 : mword 13) s1_idx BEQ false
                (add_vec (mword_of_int 0xe3c : mword 64)
                   (sign_extend' 64 (mword_of_int 468 : mword 13)))
                (4 + n) Hnt eq_refl ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shk_e3c with "Hcode"). }
      assert (E562 : add_vec_int (mword_of_int 0xe3c : mword 64) 4
                     = mword_of_int 0xe40)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E562.
      iIntros (h2) "Hrun".
      assert (Ek : (i0 + S k)%nat = (S i0 + k)%nat) by lia.
      rewrite Ek.
      iApply (IH (S i0) h2 m1 n ltac:(lia)
                ltac:(intros j Hj; apply Hpct; lia) Hinv1 Hs11
                with "Hcode Hstr Hrun Hcont").
  Qed.

  (* ===================================================================== *)
  (* SMALL ARITHMETIC THE DISPATCH NEEDS.                                   *)
  (* ===================================================================== *)

  Lemma ubyte_range (b : mword 8) : 0 <= bv_unsigned b < 256.
  Proof.
    pose proof (bv_unsigned_in_range 8 b) as H0.
    assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
    rewrite Em8 in H0. exact H0.
  Qed.

  (* Every test in the dispatch chain is [c - K] against zero, with [c] a
     byte and [K] one of 100, 108, 117, 120.  The difference is NEGATIVE
     whenever the byte is small, so [moi_eq_zero] -- which wants a
     nonnegative argument -- does not apply to it directly; the wrap has to
     be taken first, and then the divisibility says exactly [c = K]. *)
  Lemma moi_sub_ne_zero (v w : Z) :
    0 <= v < 256 -> 0 <= w < 256 -> v <> w ->
    neq_vec (mword_of_int (v - w) : mword 64) zero_reg = true.
  Proof.
    intros Hv Hw Hne.
    rewrite <- (moi_mod ((v - w) mod Z64) (v - w)
                 ltac:(rewrite Zmod_mod; reflexivity)).
    unfold neq_vec.
    rewrite (moi_eq_zero ((v - w) mod Z64)
               ltac:(apply Z.mod_pos_bound; unfold Z64; lia)).
    destruct (Z.eqb_spec ((v - w) mod Z64) 0) as [He | _]; [ | reflexivity ].
    exfalso. apply Hne.
    apply Z.mod_divide in He; [ | unfold Z64; lia ].
    destruct He as [q Hq]. unfold Z64 in Hq. lia.
  Qed.

  (* ===================================================================== *)
  (* WHERE THE HEAP'S OWN BOUNDS COME FROM.                                 *)
  (* ===================================================================== *)

  Local Lemma urun_ubyte_bnd (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (dq : dfrac) (a : Z) (b : bv 8) :
    urun γt γd γs γfd h m pc avail -∗ ubyteq γd dq a b -∗ ⌜ 0 <= a < 2 ^ 38 ⌝.
  Proof.
    iIntros "Hrun Hb".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(_ & _ & Hh & _ & _)".
    iDestruct (uheap_ubyte with "Hh Hb") as %(_ & _ & Hbnd).
    iPureIntro. exact Hbnd.
  Qed.

  Local Lemma urun_uword_bnd (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (dq : dfrac) (a : Z) (w : mword 64) :
    urun γt γd γs γfd h m pc avail -∗ uwordq γd dq a w -∗
    ⌜ 0 <= a /\ a + 8 <= 2 ^ 38 ⌝.
  Proof.
    iIntros "Hrun Hw". rewrite /uwordq /ubytesq.
    iDestruct (big_sepL_lookup_acc _ (seq 0 8) 0%nat 0%nat ltac:(reflexivity)
                 with "Hw") as "[H0 Hcl]".
    iDestruct (urun_ubyte_bnd with "Hrun H0") as %Hb0.
    iDestruct ("Hcl" with "H0") as "Hw".
    iDestruct (big_sepL_lookup_acc _ (seq 0 8) 7%nat 7%nat ltac:(reflexivity)
                 with "Hw") as "[H7 _]".
    iDestruct (urun_ubyte_bnd with "Hrun H7") as %Hb7.
    iPureIntro. lia.
  Qed.

  (* ===================================================================== *)
  (* [vp_inv] WITH s3 FREE.                                                 *)
  (*                                                                        *)
  (* From 0xfcc to 0xfec the '%s' arm parks the BUMPED va_list in s3 -- the  *)
  (* same register the loop uses for its state -- and only the [li s3,0] at  *)
  (* 0xfec puts the state back.  For those thirty instructions the loop      *)
  (* invariant holds of every register but that one, so it is stated with    *)
  (* s3's value a parameter.  [vp_inv] is the instance at [zero_reg], and    *)
  (* the two conversions are definitional.                                   *)
  (* ===================================================================== *)
  Definition vp_inv3 (m0 m : regfile) (sp0 : mword 64) (a : Z)
      (fd ap v3 : mword 64) (i : nat) : Prop :=
    m !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 12)) /\
    m !!! Regidx s0_idx = sp0 /\
    m !!! Regidx s2_idx = mword_of_int (Z.of_nat i) /\
    m !!! Regidx s3_idx = v3 /\
    m !!! Regidx s4_idx = mword_of_int a /\
    m !!! Regidx s5_idx = mword_of_int 37 /\
    m !!! Regidx s6_idx = fd /\
    m !!! Regidx s7_idx = ap /\
    m !!! Regidx s8_idx = mword_of_int 100 /\
    (forall r : mword 5, ucallee_saved_idx r = true ->
       uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27) ->
       m !!! Regidx r = m0 !!! Regidx r).

  Lemma vp_inv_of3 (m0 m : regfile) (sp0 : mword 64) (a : Z)
      (fd ap : mword 64) (i : nat) :
    vp_inv3 m0 m sp0 a fd ap zero_reg i -> vp_inv m0 m sp0 a fd ap i.
  Proof. unfold vp_inv3, vp_inv. exact (fun H => H). Qed.

  Lemma vp_inv_to3 (m0 m : regfile) (sp0 : mword 64) (a : Z)
      (fd ap : mword 64) (i : nat) :
    vp_inv m0 m sp0 a fd ap i -> vp_inv3 m0 m sp0 a fd ap zero_reg i.
  Proof. unfold vp_inv3, vp_inv. exact (fun H => H). Qed.

  Lemma vp_inv3_call (m0 m m' : regfile) (sp0 : mword 64) (a : Z)
      (fd ap v3 : mword 64) (i : nat) :
    ucallee_saved m m' ->
    vp_inv3 m0 m sp0 a fd ap v3 i -> vp_inv3 m0 m' sp0 a fd ap v3 i.
  Proof.
    intros Hcs (Hsp & Hs0 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hfr).
    unfold vp_inv3.
    rewrite (Hcs csp_rs1 ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s0_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s2_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s3_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s4_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s5_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s6_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s7_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s8_idx ltac:(vm_compute; reflexivity)).
    repeat (split; [ assumption | ]).
    intros r Hr Hset. rewrite (Hcs r Hr). exact (Hfr r Hr Hset).
  Qed.

  Lemma vp_inv3_upd (m0 m : regfile) (sp0 : mword 64) (a : Z)
      (fd ap v3 : mword 64) (i : nat) (r : mword 5) (v : mword 64) :
    vp_writable r = true ->
    vp_inv3 m0 m sp0 a fd ap v3 i ->
    vp_inv3 m0 (<[Regidx r := regval_into_reg v]> m) sp0 a fd ap v3 i.
  Proof.
    intros Hw (Hsp & Hs0 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hfr).
    unfold vp_inv3.
    rewrite (upd_ne m (Regidx r) (Regidx csp_rs1) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint csp_rs1) with 2
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s0_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s0_idx) with 8
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s2_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s2_idx) with 18
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s3_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s3_idx) with 19
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s4_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s4_idx) with 20
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s5_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s5_idx) with 21
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s6_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s6_idx) with 22
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s7_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s7_idx) with 23
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s8_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s8_idx) with 24
                       by (vm_compute; reflexivity); lia)).
    repeat (split; [ assumption | ]).
    intros q Hq Hset.
    rewrite (upd_ne m (Regidx r) (Regidx q) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw); lia)).
    exact (Hfr q Hq Hset).
  Qed.

  (* --------------------------------------------------------------------- *)
  (* ONE TURN OF THE ARGUMENT STRING'S LOOP, 0xfdc -> 0xfe8:                *)
  (*                                                                        *)
  (*   c.mv a0,s6 ; jal putc ; c.addi s1,s1,1 ; lbu a1,0(s1)                 *)
  (*                                                                        *)
  (* s1 is the cursor and is callee-saved, which is the only reason it       *)
  (* survives the call; a0 and a1 are the arguments and are not.             *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kshd_vprintf_sstep (m0 : regfile) (sp0 fd ap v3 : mword 64) (a : Z)
      (i : nat) (p : Z) (b1 : mword 8)
      (h : CpuId) (m : regfile) (n : nat) :
    0 <= p -> p + 1 < Z64 ->
    vp_inv3 m0 m sp0 a fd ap v3 i ->
    m !!! Regidx s1_idx = mword_of_int p ->
    shk_code γt -∗
    shd_sb γt γd tx (p + 1) b1 -∗
    urun γt γd γs γfd h m (mword_of_int 0xfdc) (4 + n) -∗
    (∀ (h' : CpuId) (m' : regfile),
       shd_sb γt γd tx (p + 1) b1 -∗
       ⌜ vp_inv3 m0 m' sp0 a fd ap v3 i ⌝ -∗
       ⌜ m' !!! Regidx s1_idx = mword_of_int (p + 1) ⌝ -∗
       ⌜ m' !!! Regidx a1_idx = zero_extend' 64 b1 ⌝ -∗
       urun γt γd γs γfd h' m' (mword_of_int 0xfe8) (4 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hp0 Hp1 Hinv Hs1.
    iIntros "#Hcode Hb1 Hrun Hcont".
    pose proof shd_pin_putc as Hputc.
    (* ---- 0xfdc  c.mv a0,s6 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h m (mword_of_int 0xfdc) a0_idx s6_idx
              (add_vec zero_reg (m !!! Regidx s6_idx)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_fdc with "Hcode"). }
    assert (E702 : add_vec_int (mword_of_int 0xfdc : mword 64) 2
                   = mword_of_int 0xfde)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E702.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a0_idx
                 := regval_into_reg (add_vec zero_reg (m !!! Regidx s6_idx))]> m).
    (* ---- 0xfde  jal ra,0xd2e <putc> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h1 m1 (mword_of_int 0xfde)
              (mword_of_int 2096464 : mword 21) ra_idx
              (mword_of_int ShSyms.putc) (mword_of_int 0xfe2) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hputc; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hputc; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_fde with "Hcode"). }
    iIntros (h2) "Hrun".
    set (m2 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0xfe2 : mword 64)]> m1).
    assert (Hra2 : m2 !!! Regidx ra_idx = (mword_of_int 0xfe2 : mword 64))
      by exact (upd_eq m1 (Regidx ra_idx) (regval_into_reg _)).
    iApply (wp_kshd_putc γt γd γs γfd h2 m2 n with "Hcode Hrun").
    iIntros (h3 m3) "%Hcs Hrun".
    assert (Eret : ret_pc (m2 !!! Regidx ra_idx)
                   = (mword_of_int 0xfe2 : mword 64))
      by (rewrite Hra2; apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    assert (Hinv3 : vp_inv3 m0 m3 sp0 a fd ap v3 i).
    { apply (vp_inv3_call m0 m2 m3 sp0 a fd ap v3 i Hcs).
      apply (vp_inv3_upd _ _ _ _ _ _ _ _ ra_idx _
               ltac:(vm_compute; reflexivity)).
      apply (vp_inv3_upd _ _ _ _ _ _ _ _ a0_idx _
               ltac:(vm_compute; reflexivity)).
      exact Hinv. }
    assert (Hs1_3 : m3 !!! Regidx s1_idx = mword_of_int p).
    { rewrite (Hcs s1_idx ltac:(vm_compute; reflexivity)).
      rewrite /m2 (upd_ne m1 (Regidx ra_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m1 (upd_ne m (Regidx a0_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      exact Hs1. }
    (* ---- 0xfe2  c.addi s1,s1,1 ---- *)
    assert (Ei1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                  = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Eadd : add_vec (m3 !!! Regidx s1_idx)
                     (sign_extend' 64 (mword_of_int 1 : mword 6))
                   = mword_of_int (p + 1))
      by (rewrite Hs1_3 Ei1 moi_add; reflexivity).
    iApply (wp_uk_caddi γt γd γs γfd h3 m3 (mword_of_int 0xfe2)
              (mword_of_int 1 : mword 6) s1_idx (mword_of_int (p + 1)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Eadd))
              with "[] Hrun").
    { iApply (uis_shk_fe2 with "Hcode"). }
    assert (E708 : add_vec_int (mword_of_int 0xfe2 : mword 64) 2
                   = mword_of_int 0xfe4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E708.
    iIntros (h4) "Hrun".
    set (m4 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int (p + 1) : mword 64)]> m3).
    assert (Hs1_4 : m4 !!! Regidx s1_idx = mword_of_int (p + 1))
      by exact (upd_eq m3 (Regidx s1_idx) (regval_into_reg _)).
    assert (Hinv4 : vp_inv3 m0 m4 sp0 a fd ap v3 i)
      by exact (vp_inv3_upd m0 m3 sp0 a fd ap v3 i s1_idx _
                  ltac:(vm_compute; reflexivity) Hinv3).
    (* ---- 0xfe4  lbu a1,0(s1) ---- *)
    assert (Hp1r : 0 <= p + 1 < Z64) by lia.
    assert (Haddr : (p + 1)%Z
                    = uint (m4 !!! Regidx s1_idx)
                      + uoff_i12 (mword_of_int 0 : mword 12)).
    { rewrite Hs1_4 (uint_moi (p + 1) Hp1r).
      replace (uoff_i12 (mword_of_int 0 : mword 12)) with 0
        by (vm_compute; reflexivity).
      lia. }
    iApply (wp_shd_lbu γt γd γs γfd h4 m4 (mword_of_int 0xfe4)
              (mword_of_int 0 : mword 12) s1_idx a1_idx tx (p + 1) b1 (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              Haddr ltac:(vm_compute; discriminate)
              with "[] Hb1 Hrun").
    { iApply (uis_shk_fe4 with "Hcode"). }
    assert (E70a : add_vec_int (mword_of_int 0xfe4 : mword 64) 4
                   = mword_of_int 0xfe8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E70a.
    iIntros "Hb1" (h5) "Hrun".
    set (m5 := <[Regidx a1_idx
                 := regval_into_reg (zero_extend' 64 b1 : mword 64)]> m4).
    iApply ("Hcont" $! h5 m5 with "Hb1 [] [] [] Hrun").
    - iPureIntro.
      exact (vp_inv3_upd m0 m4 sp0 a fd ap v3 i a1_idx _
               ltac:(vm_compute; reflexivity) Hinv4).
    - iPureIntro. rewrite /m5 (upd_ne m4 (Regidx a1_idx) (Regidx s1_idx) _
                                ltac:(vm_compute; discriminate)).
      exact Hs1_4.
    - iPureIntro.
      exact (upd_eq m4 (Regidx a1_idx) (regval_into_reg _)).
  Qed.

  Lemma vp_inv3_bump (m0 m : regfile) (sp0 : mword 64) (a : Z)
      (fd ap v3 : mword 64) (i j : nat) (v : mword 64) :
    v = mword_of_int (Z.of_nat j) ->
    vp_inv3 m0 m sp0 a fd ap v3 i ->
    vp_inv3 m0 (<[Regidx s2_idx := regval_into_reg v]> m) sp0 a fd ap v3 j.
  Proof.
    intros -> (Hsp & Hs0 & _ & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hfr).
    unfold vp_inv3.
    rewrite (upd_ne m (Regidx s2_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s0_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s3_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s4_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s5_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s6_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s7_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s8_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_eq m (Regidx s2_idx) _).
    repeat (split; [ (assumption || reflexivity) | ]).
    intros q Hq Hset.
    rewrite (upd_ne m (Regidx s2_idx) (Regidx q) _
               ltac:(apply uidx_ne; replace (uint s2_idx) with 18
                       by (vm_compute; reflexivity); lia)).
    exact (Hfr q Hq Hset).
  Qed.

  (* ...and the two writes that MOVE the invariant: the state register and
     the va_list cursor.  Both are what the '%s' arm is for. *)
  Lemma vp_inv3_s3 (m0 m : regfile) (sp0 : mword 64) (a : Z)
      (fd ap v3 w3 : mword 64) (i : nat) :
    vp_inv3 m0 m sp0 a fd ap v3 i ->
    vp_inv3 m0 (<[Regidx s3_idx := regval_into_reg w3]> m) sp0 a fd ap w3 i.
  Proof.
    intros (Hsp & Hs0 & Hs2 & _ & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hfr).
    unfold vp_inv3.
    rewrite (upd_ne m (Regidx s3_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s3_idx) (Regidx s0_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s3_idx) (Regidx s2_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s3_idx) (Regidx s4_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s3_idx) (Regidx s5_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s3_idx) (Regidx s6_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s3_idx) (Regidx s7_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s3_idx) (Regidx s8_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_eq m (Regidx s3_idx) _).
    repeat (split; [ (assumption || reflexivity) | ]).
    intros q Hq Hset.
    rewrite (upd_ne m (Regidx s3_idx) (Regidx q) _
               ltac:(apply uidx_ne; replace (uint s3_idx) with 19
                       by (vm_compute; reflexivity); lia)).
    exact (Hfr q Hq Hset).
  Qed.

  Lemma vp_inv3_s7 (m0 m : regfile) (sp0 : mword 64) (a : Z)
      (fd ap ap' v3 : mword 64) (i : nat) :
    vp_inv3 m0 m sp0 a fd ap v3 i ->
    vp_inv3 m0 (<[Regidx s7_idx := regval_into_reg ap']> m) sp0 a fd ap' v3 i.
  Proof.
    intros (Hsp & Hs0 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & _ & Hs8 & Hfr).
    unfold vp_inv3.
    rewrite (upd_ne m (Regidx s7_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s7_idx) (Regidx s0_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s7_idx) (Regidx s2_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s7_idx) (Regidx s3_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s7_idx) (Regidx s4_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s7_idx) (Regidx s5_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s7_idx) (Regidx s6_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s7_idx) (Regidx s8_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_eq m (Regidx s7_idx) _).
    repeat (split; [ (assumption || reflexivity) | ]).
    intros q Hq Hset.
    rewrite (upd_ne m (Regidx s7_idx) (Regidx q) _
               ltac:(apply uidx_ne; replace (uint s7_idx) with 23
                       by (vm_compute; reflexivity); lia)).
    exact (Hfr q Hq Hset).
  Qed.

  (* --------------------------------------------------------------------- *)
  (* THE ARGUMENT STRING'S LOOP.  [k+1] bytes are left, the one in a1 is    *)
  (* [sf j], and the [c.bnez a1] at 0xfe8 decides -- exactly as the format  *)
  (* loop's [beqz s1] does -- whether what was just loaded is a body byte   *)
  (* or the terminator.  The argv string is [DfracDiscarded], so nothing    *)
  (* is threaded: every byte is persistent and taken again where needed.    *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kshd_vprintf_sloop (m0 : regfile) (sp0 fd ap v3 : mword 64) (a : Z)
      (i : nat) (sa : Z) (slen : nat) (sf : nat -> bv 8) (k : nat) :
    0 <= sa -> sa + Z.of_nat slen < 2 ^ 38 ->
    forall (j : nat) (h : CpuId) (m : regfile) (n : nat),
      (j + S k)%nat = slen ->
      vp_inv3 m0 m sp0 a fd ap v3 i ->
      m !!! Regidx s1_idx = mword_of_int (sa + Z.of_nat j) ->
      shk_code γt -∗
      shd_str γt γd tx sa slen sf -∗
      urun γt γd γs γfd h m (mword_of_int 0xfdc) (4 + n) -∗
      (∀ (h' : CpuId) (m' : regfile),
         ⌜ vp_inv3 m0 m' sp0 a fd ap v3 i ⌝ -∗
         urun γt γd γs γfd h' m' (mword_of_int 0xfea) (4 + n) -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    intros Hsa0 Hsahi.
    induction k as [| k IH ];
      intros j h m n Hjk Hinv Hs1;
      iIntros "#Hcode #Hstr Hrun Hcont";
      iDestruct (shd_str_nonul with "Hstr") as %Hnn;
      assert (Hjlt : (j < slen)%nat) by lia;
      assert (Hp0 : 0 <= sa + Z.of_nat j) by lia;
      assert (Hp1 : sa + Z.of_nat j + 1 < Z64) by (unfold Z64; lia).
    - (* the LAST byte: what 0xfe4 loads is the terminator *)
      iDestruct (shd_str_nul with "Hstr") as "[#Hnul _]".
      iApply (wp_kshd_vprintf_sstep m0 sp0 fd ap v3 a i
                (sa + Z.of_nat j) ubyte0 h m n Hp0 Hp1
                Hinv Hs1 with "Hcode [] Hrun").
      { replace (sa + Z.of_nat j + 1)%Z with (sa + Z.of_nat slen)%Z by lia.
        iExact "Hnul". }
      iIntros (h1 m1) "_ %Hinv1 %Hs11 %Ha11 Hrun".
      (* ---- 0xfe8  c.bnez a1,0xfdc -- NOT taken: the terminator ---- *)
      assert (Hnt : false = neq_vec (m1 !!! Regidx a1_idx) zero_reg).
      { rewrite Ha11 zext8_moi.
        replace (bv_unsigned ubyte0) with 0 by (vm_compute; reflexivity).
        unfold neq_vec. rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia)).
        reflexivity. }
      iApply (wp_uk_cbnez γt γd γs γfd h1 m1 (mword_of_int 0xfe8)
                (mword_of_int 250 : mword 8) (mword_of_int 3 : mword 3) a1_idx
                false
                (add_vec (mword_of_int 0xfe8 : mword 64)
                   (sign_extend' 64
                      (sign_extend' 13
                         (concat_vec (mword_of_int 250 : mword 8) ('b"0")))))
                (4 + n) ltac:(vm_compute; reflexivity) Hnt eq_refl
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shk_fe8 with "Hcode"). }
      assert (E70e : add_vec_int (mword_of_int 0xfe8 : mword 64) 2
                     = mword_of_int 0xfea)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E70e.
      iIntros (h2) "Hrun".
      iApply ("Hcont" $! h2 m1 with "[] Hrun"). iPureIntro. exact Hinv1.
    - (* a BODY byte follows: round again *)
      assert (Hsjlt : (S j < slen)%nat) by lia.
      iDestruct (shd_str_byte γt γd tx sa slen sf (S j) Hsjlt with "Hstr")
        as "[#Hb1 _]".
      iApply (wp_kshd_vprintf_sstep m0 sp0 fd ap v3 a i
                (sa + Z.of_nat j) (sf (S j)) h m n Hp0 Hp1
                Hinv Hs1 with "Hcode [] Hrun").
      { replace (sa + Z.of_nat j + 1)%Z with (sa + Z.of_nat (S j))%Z by lia.
        iExact "Hb1". }
      iIntros (h1 m1) "_ %Hinv1 %Hs11 %Ha11 Hrun".
      (* ---- 0xfe8  c.bnez a1,0xfdc -- TAKEN: a body byte is not NUL ---- *)
      assert (Hnz : bv_unsigned (sf (S j)) <> 0).
      { intro He. apply (Hnn (S j) Hsjlt). apply bv_eq.
        rewrite He. vm_compute. reflexivity. }
      assert (Hsr : 0 <= bv_unsigned (sf (S j)) < Z64).
      { assert (HH : 0 <= bv_unsigned (sf (S j)) < 256).
        { pose proof (bv_unsigned_in_range 8 (sf (S j))) as H0.
          assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
          rewrite Em8 in H0. exact H0. }
        unfold Z64. lia. }
      assert (Ht : true = neq_vec (m1 !!! Regidx a1_idx) zero_reg).
      { rewrite Ha11 zext8_moi. unfold neq_vec.
        rewrite (moi_eq_zero (bv_unsigned (sf (S j))) Hsr).
        destruct (Z.eqb_spec (bv_unsigned (sf (S j))) 0) as [He | _];
          [ exfalso; exact (Hnz He) | reflexivity ]. }
      assert (Etgt : add_vec (mword_of_int 0xfe8 : mword 64)
                       (sign_extend' 64
                          (sign_extend' 13
                             (concat_vec (mword_of_int 250 : mword 8) ('b"0"))))
                     = mword_of_int 0xfdc)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_cbnez γt γd γs γfd h1 m1 (mword_of_int 0xfe8)
                (mword_of_int 250 : mword 8) (mword_of_int 3 : mword 3) a1_idx
                true (mword_of_int 0xfdc) (4 + n)
                ltac:(vm_compute; reflexivity) Ht (eq_sym Etgt)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_fe8 with "Hcode"). }
      iIntros (h2) "Hrun".
      assert (Hs1' : m1 !!! Regidx s1_idx
                     = mword_of_int (sa + Z.of_nat (S j)))
        by (rewrite Hs11; f_equal; lia).
      iApply (IH (S j) h2 m1 n ltac:(lia) Hinv1 Hs1'
                with "Hcode Hstr Hrun Hcont").
  Qed.


  (* --------------------------------------------------------------------- *)
  (* THE TAIL OF EVERY ROUND, 0xe2e -> 0xe3c:                               *)
  (*                                                                        *)
  (*   addiw a5,s2,1 ; c.mv s2,a5 ; c.mv a4,a5 ; c.add a5,a5,s4 ;           *)
  (*   lbu s1,0(a5)                                                          *)
  (*                                                                        *)
  (* The index advances, a4 keeps a copy of it, and the next format byte     *)
  (* lands in s1.  It is stated over [vp_inv3] rather than [vp_inv] because  *)
  (* the '%s' arm reaches it with the state register holding the va_list.    *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kshd_vprintf_bump (m0 : regfile) (sp0 fd ap v3 : mword 64) (a : Z)
      (i : nat) (b1 : mword 8) (h : CpuId) (m : regfile) (n : nat) :
    0 <= a -> a + Z.of_nat i + 2 < 2 ^ 31 ->
    vp_inv3 m0 m sp0 a fd ap v3 i ->
    shk_code γt -∗
    utext γt (a + Z.of_nat (S i)) b1 -∗
    urun γt γd γs γfd h m (mword_of_int 0xe2e) (4 + n) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ vp_inv3 m0 m' sp0 a fd ap v3 (S i) ⌝ -∗
       ⌜ m' !!! Regidx s1_idx = mword_of_int (bv_unsigned b1) ⌝ -∗
       ⌜ m' !!! Regidx a4_idx = mword_of_int (Z.of_nat (S i)) ⌝ -∗
       urun γt γd γs γfd h' m' (mword_of_int 0xe3c) (4 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd Hinv.
    pose proof Hinv as Hd.
    destruct Hd as (Hsp & Hs0 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hfr).
    iIntros "#Hcode #Hb1 Hrun Hcont".
    (* ---- 0xe2e  addiw a5,s2,1 ---- *)
    assert (Es1_12 : (sign_extend' 64 (mword_of_int 1 : mword 12) : mword 64)
                     = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Ea5n : sign_extend' 64
                     (subrange_vec_dec
                        (add_vec (m !!! Regidx s2_idx)
                           (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0)
                   = (mword_of_int (Z.of_nat (S i)) : mword 64)).
    { rewrite Hs2 Es1_12.
      rewrite (moi_addw (Z.of_nat i) 1 ltac:(unfold Z31; lia)).
      f_equal. lia. }
    iApply (wp_uk_addiw γt γd γs γfd h m (mword_of_int 0xe2e)
              (mword_of_int 1 : mword 12) s2_idx a5_idx
              (mword_of_int (Z.of_nat (S i))) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ea5n))
              with "[] Hrun").
    { iApply (uis_shk_e2e with "Hcode"). }
    assert (E554 : add_vec_int (mword_of_int 0xe2e : mword 64) 4
                   = mword_of_int 0xe32)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E554.
    iIntros (h6) "Hrun".
    set (m3 := <[Regidx a5_idx
                 := regval_into_reg
                      (mword_of_int (Z.of_nat (S i)) : mword 64)]> m).
    assert (Ha53 : m3 !!! Regidx a5_idx = mword_of_int (Z.of_nat (S i)))
      by exact (upd_eq m (Regidx a5_idx) (regval_into_reg _)).
    assert (Hinv3 : vp_inv3 m0 m3 sp0 a fd ap v3 i)
      by exact (vp_inv3_upd m0 m sp0 a fd ap v3 i a5_idx _
                  ltac:(vm_compute; reflexivity) Hinv).
    (* ---- 0xe32  c.mv s2,a5 -- the index moves ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h6 m3 (mword_of_int 0xe32) s2_idx a5_idx
              (mword_of_int (Z.of_nat (S i))) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha53; symmetry; apply add_vec_zero_l)
              with "[] Hrun").
    { iApply (uis_shk_e32 with "Hcode"). }
    assert (E558 : add_vec_int (mword_of_int 0xe32 : mword 64) 2
                   = mword_of_int 0xe34)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E558.
    iIntros (h7) "Hrun".
    set (m4 := <[Regidx s2_idx
                 := regval_into_reg
                      (mword_of_int (Z.of_nat (S i)) : mword 64)]> m3).
    pose proof (vp_inv3_bump m0 m3 sp0 a fd ap v3 i (S i) _
                  eq_refl Hinv3) as Hinv4.
    assert (Ha54 : m4 !!! Regidx a5_idx = mword_of_int (Z.of_nat (S i))).
    { rewrite <- Ha53.
      exact (upd_ne m3 (Regidx s2_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0xe34  c.mv a4,a5 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h7 m4 (mword_of_int 0xe34) a4_idx a5_idx
              (mword_of_int (Z.of_nat (S i))) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha54; symmetry; apply add_vec_zero_l)
              with "[] Hrun").
    { iApply (uis_shk_e34 with "Hcode"). }
    assert (E55a : add_vec_int (mword_of_int 0xe34 : mword 64) 2
                   = mword_of_int 0xe36)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E55a.
    iIntros (h8) "Hrun".
    set (m5 := <[Regidx a4_idx
                 := regval_into_reg
                      (mword_of_int (Z.of_nat (S i)) : mword 64)]> m4).
    assert (Hinv5 : vp_inv3 m0 m5 sp0 a fd ap v3 (S i))
      by exact (vp_inv3_upd m0 m4 sp0 a fd ap v3 (S i) a4_idx _
                  ltac:(vm_compute; reflexivity) Hinv4).
    pose proof Hinv5 as Hd5.
    destruct Hd5 as (Hsp5 & Hs05 & Hs25 & Hs35 & Hs45' & Hs55 & Hs65 & Hs75
                     & Hs85 & Hfr5).
    assert (Ha45 : m5 !!! Regidx a4_idx = mword_of_int (Z.of_nat (S i)))
      by exact (upd_eq m4 (Regidx a4_idx) (regval_into_reg _)).
    assert (Ha55 : m5 !!! Regidx a5_idx = mword_of_int (Z.of_nat (S i))).
    { rewrite <- Ha54.
      exact (upd_ne m4 (Regidx a4_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0xe36  c.add a5,a5,s4 -- the pointer ---- *)
    assert (Eadd5 : add_vec (m5 !!! Regidx a5_idx) (m5 !!! Regidx s4_idx)
                    = mword_of_int (a + Z.of_nat (S i))).
    { rewrite Ha55 Hs45' moi_add. f_equal. lia. }
    iApply (wp_uk_cadd γt γd γs γfd h8 m5 (mword_of_int 0xe36) a5_idx s4_idx
              (mword_of_int (a + Z.of_nat (S i))) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Eadd5))
              with "[] Hrun").
    { iApply (uis_shk_e36 with "Hcode"). }
    assert (E55c : add_vec_int (mword_of_int 0xe36 : mword 64) 2
                   = mword_of_int 0xe38)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E55c.
    iIntros (h9) "Hrun".
    set (m6 := <[Regidx a5_idx
                 := regval_into_reg
                      (mword_of_int (a + Z.of_nat (S i)) : mword 64)]> m5).
    assert (Hinv6 : vp_inv3 m0 m6 sp0 a fd ap v3 (S i))
      by exact (vp_inv3_upd m0 m5 sp0 a fd ap v3 (S i) a5_idx _
                  ltac:(vm_compute; reflexivity) Hinv5).
    assert (Ha56 : m6 !!! Regidx a5_idx = mword_of_int (a + Z.of_nat (S i)))
      by exact (upd_eq m5 (Regidx a5_idx) (regval_into_reg _)).
    (* ---- 0xe38  lbu s1,0(a5) -- fmt[i+1], out of .rodata ---- *)
    assert (Hb64a : 0 <= a + Z.of_nat (S i) < Z64) by (unfold Z64; lia).
    assert (Haddr : (a + Z.of_nat (S i))%Z
                    = uint (m6 !!! Regidx a5_idx)
                      + uoff_i12 (mword_of_int 0 : mword 12)).
    { rewrite Ha56 (uint_moi (a + Z.of_nat (S i)) Hb64a).
      replace (uoff_i12 (mword_of_int 0 : mword 12)) with 0
        by (vm_compute; reflexivity).
      lia. }
    iApply (wp_uk_lbu_text γt γd γs γfd h9 m6 (mword_of_int 0xe38)
              (mword_of_int 0 : mword 12) a5_idx s1_idx
              (a + Z.of_nat (S i)) b1 (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              Haddr ltac:(vm_compute; discriminate)
              with "[] Hb1 Hrun").
    { iApply (uis_shk_e38 with "Hcode"). }
    assert (E55e : add_vec_int (mword_of_int 0xe38 : mword 64) 4
                   = mword_of_int 0xe3c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E55e.
    iIntros (h10) "Hrun".
    set (m7 := <[Regidx s1_idx
                 := regval_into_reg (zero_extend' 64 b1 : mword 64)]> m6).
    iApply ("Hcont" $! h10 m7 with "[] [] [] Hrun").
    - iPureIntro.
      exact (vp_inv3_upd m0 m6 sp0 a fd ap v3 (S i) s1_idx _
               ltac:(vm_compute; reflexivity) Hinv6).
    - iPureIntro. rewrite /m7 (upd_eq m6 (Regidx s1_idx) (regval_into_reg _)).
      exact (zext8_moi b1).
    - iPureIntro.
      rewrite /m7 (upd_ne m6 (Regidx s1_idx) (Regidx a4_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m6 (upd_ne m5 (Regidx a5_idx) (Regidx a4_idx) _
                     ltac:(vm_compute; discriminate)).
      exact Ha45.
  Qed.

  (* --------------------------------------------------------------------- *)
  (* THE ROUND THAT SEES THE '%', 0xe40 -> 0xe3c.                           *)
  (*                                                                        *)
  (* It differs from a plain round at one instruction: at 0xe48 the         *)
  (* character IS s5, so the branch to the putc arm is NOT taken and 0xe4c  *)
  (* sets the state register instead.  The index still advances, and a4     *)
  (* keeps a copy of it -- which is the only reason the directive's own     *)
  (* round, one turn later, can find fmt[i+1] at 0xe50.                     *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kshd_vprintf_pct (m0 : regfile) (sp0 fd ap : mword 64) (a : Z)
      (i : nat) (b1 : mword 8) (h : CpuId) (m : regfile) (n : nat) :
    0 <= a -> a + Z.of_nat i + 2 < 2 ^ 31 ->
    vp_inv m0 m sp0 a fd ap i ->
    m !!! Regidx s1_idx = mword_of_int 37 ->
    shk_code γt -∗
    utext γt (a + Z.of_nat (S i)) b1 -∗
    urun γt γd γs γfd h m (mword_of_int 0xe40) (4 + n) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ vp_inv3 m0 m' sp0 a fd ap (mword_of_int 37) (S i) ⌝ -∗
       ⌜ m' !!! Regidx s1_idx = mword_of_int (bv_unsigned b1) ⌝ -∗
       ⌜ m' !!! Regidx a4_idx = mword_of_int (Z.of_nat (S i)) ⌝ -∗
       urun γt γd γs γfd h' m' (mword_of_int 0xe3c) (4 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd Hinv0 Hs1.
    pose proof (vp_inv_to3 m0 m sp0 a fd ap i Hinv0) as Hinv.
    pose proof Hinv as Hd.
    destruct Hd as (Hsp & Hs0 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hfr).
    iIntros "#Hcode #Hb1 Hrun Hcont".
    assert (Hi31 : 0 <= Z.of_nat i + 1 < Z31) by (unfold Z31; lia).
    (* ---- 0xe40  sext.w a5,s1 ---- *)
    assert (Ez0 : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                  = mword_of_int 0)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Ea5c : sign_extend' 64
                     (subrange_vec_dec
                        (add_vec (m !!! Regidx s1_idx)
                           (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0)
                   = (mword_of_int 37 : mword 64)).
    { rewrite Hs1 Ez0.
      rewrite (moi_addw 37 0 ltac:(unfold Z31; lia)). f_equal; lia. }
    iApply (wp_uk_addiw γt γd γs γfd h m (mword_of_int 0xe40)
              (mword_of_int 0 : mword 12) s1_idx a5_idx (mword_of_int 37) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ea5c))
              with "[] Hrun").
    { iApply (uis_shk_e40 with "Hcode"). }
    assert (E566 : add_vec_int (mword_of_int 0xe40 : mword 64) 4
                   = mword_of_int 0xe44)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E566.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int 37 : mword 64)]> m).
    assert (Hinv1 : vp_inv3 m0 m1 sp0 a fd ap zero_reg i)
      by exact (vp_inv3_upd m0 m sp0 a fd ap zero_reg i a5_idx _
                  ltac:(vm_compute; reflexivity) Hinv).
    pose proof Hinv1 as Hd1.
    destruct Hd1 as (Hsp1 & Hs01 & Hs21 & Hs31 & Hs41 & Hs51 & Hs61 & Hs71
                     & Hs81 & Hfr1).
    assert (Ha5_1 : m1 !!! Regidx a5_idx = mword_of_int 37)
      by exact (upd_eq m (Regidx a5_idx) (regval_into_reg _)).
    (* ---- 0xe44  bnez s3,0xe2a -- NOT taken, the state register is 0 ---- *)
    assert (Hnt : false = uv_btaken BNE (m1 !!! Regidx s3_idx) zero_reg)
      by (rewrite Hs31; vm_compute; reflexivity).
    iApply (wp_uk_btype0 γt γd γs γfd h1 m1 (mword_of_int 0xe44)
              (mword_of_int 8166 : mword 13) s3_idx BNE false
              (add_vec (mword_of_int 0xe44 : mword 64)
                 (sign_extend' 64 (mword_of_int 8166 : mword 13)))
              (4 + n) Hnt eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shk_e44 with "Hcode"). }
    assert (E56a : add_vec_int (mword_of_int 0xe44 : mword 64) 4
                   = mword_of_int 0xe48)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E56a.
    iIntros (h2) "Hrun".
    (* ---- 0xe48  bne a5,s5,0xe20 -- NOT taken: the character IS '%' ---- *)
    assert (Hnt2 : false
                   = uv_btaken BNE (m1 !!! Regidx a5_idx) (m1 !!! Regidx s5_idx)).
    { rewrite Ha5_1 Hs51. cbn [uv_btaken].
      rewrite (moi_neq_vec 37 37 ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
      reflexivity. }
    iApply (wp_uk_btype γt γd γs γfd h2 m1 (mword_of_int 0xe48)
              (mword_of_int 8152 : mword 13) s5_idx a5_idx BNE false
              (add_vec (mword_of_int 0xe48 : mword 64)
                 (sign_extend' 64 (mword_of_int 8152 : mword 13)))
              (4 + n) Hnt2 eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shk_e48 with "Hcode"). }
    assert (E56e : add_vec_int (mword_of_int 0xe48 : mword 64) 4
                   = mword_of_int 0xe4c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E56e.
    iIntros (h3) "Hrun".
    (* ---- 0xe4c  c.mv s3,a5 -- state := '%' ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h3 m1 (mword_of_int 0xe4c) s3_idx a5_idx
              (mword_of_int 37) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_1; symmetry; apply add_vec_zero_l)
              with "[] Hrun").
    { iApply (uis_shk_e4c with "Hcode"). }
    assert (E572 : add_vec_int (mword_of_int 0xe4c : mword 64) 2
                   = mword_of_int 0xe4e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E572.
    iIntros (h4) "Hrun".
    set (m2 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int 37 : mword 64)]> m1).
    pose proof (vp_inv3_s3 m0 m1 sp0 a fd ap zero_reg (mword_of_int 37) i
                  Hinv1) as Hinv2.
    pose proof Hinv2 as Hd2.
    destruct Hd2 as (Hsp2 & Hs02 & Hs22 & Hs32 & Hs42 & Hs52 & Hs62 & Hs72
                     & Hs82 & Hfr2).
    (* ---- 0xe4e  c.j 0xe2e ---- *)
    assert (Etgt554 : (mword_of_int 0xe2e : mword 64)
                      = add_vec (mword_of_int 0xe4e : mword 64)
                          (sign_extend' 64
                             (sign_extend' 21
                                (concat_vec (mword_of_int 2032 : mword 11)
                                   ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cj γt γd γs γfd h4 m2 (mword_of_int 0xe4e)
              (mword_of_int 2032 : mword 11) (mword_of_int 0xe2e) (4 + n)
              Etgt554 ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_e4e with "Hcode"). }
    iIntros (h5) "Hrun".
    iApply (wp_kshd_vprintf_bump m0 sp0 fd ap (mword_of_int 37) a i b1
              h5 m2 n Ha0 Habnd Hinv2 with "Hcode Hb1 Hrun Hcont").
  Qed.

  (* --------------------------------------------------------------------- *)
  (* THE '%s' ARM PROPER, 0xfcc -> 0xe3c.                                   *)
  (*                                                                        *)
  (*   addi s3,s7,8   the va_list is bumped -- into s3, because s7 must     *)
  (*                  still point at the argument for the [ld] that follows *)
  (*   ld   s1,0(s7)  the char* itself                                       *)
  (*   beqz s1,0xff0  the "(null)" arm, excluded by [sa <> 0]                *)
  (*   lbu  a1,0(s1) ; beqz a1,0x100a   the empty-string arm, which is the    *)
  (*                  same three instructions as the loop's exit             *)
  (*   0xfdc..0xfe8   one putc per byte                                      *)
  (*   mv s7,s3 ; li s3,0 ; j 0xe2e    the bumped list is installed and the  *)
  (*                  state goes back to 0                                   *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kshd_vprintf_pcs3 (m0 : regfile) (sp0 fd : mword 64) (a : Z)
      (i : nat) (apz sa : Z) (dq : dfrac) (c1 : mword 8)
      (slen : nat) (sf : nat -> bv 8)
      (m : regfile) (h : CpuId) (n : nat) :
    0 <= a -> a + Z.of_nat i + 2 < 2 ^ 31 ->
    0 <= apz -> apz + 8 <= 2 ^ 38 -> apz mod 8 = 0 ->
    sa <> 0 ->
    vp_inv3 m0 m sp0 a fd (mword_of_int apz) (mword_of_int 37) i ->
    shk_code γt -∗
    utext γt (a + Z.of_nat (S i)) c1 -∗
    uwordq γd dq apz (mword_of_int sa) -∗
    shd_str γt γd tx sa slen sf -∗
    urun γt γd γs γfd h m (mword_of_int 0xfcc) (4 + n) -∗
    (∀ (h' : CpuId) (m' : regfile),
       uwordq γd dq apz (mword_of_int sa) -∗
       ⌜ vp_inv m0 m' sp0 a fd (mword_of_int (apz + 8)) (S i) ⌝ -∗
       ⌜ m' !!! Regidx s1_idx = mword_of_int (bv_unsigned c1) ⌝ -∗
       urun γt γd γs γfd h' m' (mword_of_int 0xe3c) (4 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd Hap0 Haphi Hapal Hsanz Hinv.
    pose proof Hinv as Hd.
    destruct Hd as (Hsp & Hs0 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hfr).
    iIntros "#Hcode #Hc1 Hw #Hstr Hrun Hcont".
    iDestruct (urun_shd_str_bnd with "Hrun Hstr") as %[Hsa0 Hsahi].
    assert (Ezr : (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64)
                  = zero_reg)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Etgt554 : (mword_of_int 0xe2e : mword 64)
                      = add_vec (mword_of_int 0xfee : mword 64)
                          (sign_extend' 64
                             (sign_extend' 21
                                (concat_vec (mword_of_int 1824 : mword 11)
                                   ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Etgt554' : (mword_of_int 0xe2e : mword 64)
                       = add_vec (mword_of_int 0x100e : mword 64)
                           (sign_extend' 64
                              (sign_extend' 21
                                 (concat_vec (mword_of_int 1808 : mword 11)
                                    ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0xfcc  addi s3,s7,8 -- the BUMPED va_list, parked in s3 ---- *)
    assert (E8 : (sign_extend' 64 (mword_of_int 8 : mword 12) : mword 64)
                 = mword_of_int 8)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Ebump : add_vec (m !!! Regidx s7_idx)
                      (sign_extend' 64 (mword_of_int 8 : mword 12))
                    = mword_of_int (apz + 8))
      by (rewrite Hs7 E8 moi_add; reflexivity).
    iApply (wp_uk_addi γt γd γs γfd h m (mword_of_int 0xfcc)
              (mword_of_int 8 : mword 12) s7_idx s3_idx
              (mword_of_int (apz + 8)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ebump))
              with "[] Hrun").
    { iApply (uis_shk_fcc with "Hcode"). }
    assert (E6f2 : add_vec_int (mword_of_int 0xfcc : mword 64) 4
                   = mword_of_int 0xfd0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E6f2.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int (apz + 8) : mword 64)]> m).
    pose proof (vp_inv3_s3 m0 m sp0 a fd (mword_of_int apz) (mword_of_int 37)
                  (mword_of_int (apz + 8)) i Hinv) as Hinv1.
    pose proof Hinv1 as Hd1.
    destruct Hd1 as (Hsp1 & Hs01 & Hs21 & Hs31 & Hs41 & Hs51 & Hs61 & Hs71
                     & Hs81 & Hfr1).
    (* ---- 0xfd0  ld s1,0(s7) -- the char* out of the caller's frame ---- *)
    assert (Hapr : 0 <= apz < Z64) by (unfold Z64; lia).
    assert (Haddr : apz = uint (m1 !!! Regidx s7_idx)
                           + uoff_i12 (mword_of_int 0 : mword 12)).
    { rewrite Hs71 (uint_moi apz Hapr).
      replace (uoff_i12 (mword_of_int 0 : mword 12)) with 0
        by (vm_compute; reflexivity).
      lia. }
    iApply (wp_uk_ld γt γd γs γfd h1 m1 (mword_of_int 0xfd0)
              (mword_of_int 0 : mword 12) s7_idx s1_idx dq apz
              (mword_of_int sa) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              Haddr Hapal ltac:(vm_compute; discriminate)
              with "[] Hw Hrun").
    { iApply (uis_shk_fd0 with "Hcode"). }
    assert (E6f6 : add_vec_int (mword_of_int 0xfd0 : mword 64) 4
                   = mword_of_int 0xfd4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E6f6.
    iIntros "Hw" (h2) "Hrun".
    set (m2 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int sa : mword 64)]> m1).
    assert (Hinv2 : vp_inv3 m0 m2 sp0 a fd (mword_of_int apz) (mword_of_int (apz + 8)) i)
      by exact (vp_inv3_upd m0 m1 sp0 a fd (mword_of_int apz) (mword_of_int (apz + 8)) i s1_idx _
                  ltac:(vm_compute; reflexivity) Hinv1).
    assert (Hs1_2 : m2 !!! Regidx s1_idx = mword_of_int sa)
      by exact (upd_eq m1 (Regidx s1_idx) (regval_into_reg _)).
    (* ---- 0xfd4  c.beqz s1,0xff0 -- NOT taken: the pointer is not null -- *)
    assert (Hsar : 0 <= sa < Z64) by (unfold Z64; lia).
    assert (Hn6fa : false = eq_vec (m2 !!! Regidx s1_idx) zero_reg).
    { rewrite Hs1_2 (moi_eq_zero sa Hsar).
      destruct (Z.eqb_spec sa 0) as [He | _];
        [ exfalso; exact (Hsanz He) | reflexivity ]. }
    iApply (wp_uk_cbeqz γt γd γs γfd h2 m2 (mword_of_int 0xfd4)
              (mword_of_int 14 : mword 8) (mword_of_int 1 : mword 3) s1_idx
              false
              (add_vec (mword_of_int 0xfd4 : mword 64)
                 (sign_extend' 64
                    (sign_extend' 13
                       (concat_vec (mword_of_int 14 : mword 8) ('b"0")))))
              (4 + n) ltac:(vm_compute; reflexivity) Hn6fa eq_refl
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shk_fd4 with "Hcode"). }
    assert (E6fa : add_vec_int (mword_of_int 0xfd4 : mword 64) 2
                   = mword_of_int 0xfd6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E6fa.
    iIntros (h3) "Hrun".
    (* ---- 0xfd6  lbu a1,0(s1) -- the string's first byte ---- *)
    assert (Haddr0 : (sa + Z.of_nat 0%nat)%Z
                     = uint (m2 !!! Regidx s1_idx)
                       + uoff_i12 (mword_of_int 0 : mword 12)).
    { rewrite Hs1_2 (uint_moi sa Hsar).
      replace (uoff_i12 (mword_of_int 0 : mword 12)) with 0
        by (vm_compute; reflexivity).
      lia. }
    destruct slen as [| slen' ].
    - (* THE EMPTY STRING.  0xfd6 reads the terminator, 0xfda is taken, and
         the arm at 0x100a is the loop's exit written out a second time. *)
      iDestruct (shd_str_nul with "Hstr") as "[#Hnul _]".
      iApply (wp_shd_lbu γt γd γs γfd h3 m2 (mword_of_int 0xfd6)
                (mword_of_int 0 : mword 12) s1_idx a1_idx tx
                (sa + Z.of_nat 0%nat)%Z ubyte0 (4 + n)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                Haddr0 ltac:(vm_compute; discriminate)
                with "[] [] Hrun").
      { iApply (uis_shk_fd6 with "Hcode"). }
      { iExact "Hnul". }
      assert (E6fc : add_vec_int (mword_of_int 0xfd6 : mword 64) 4
                     = mword_of_int 0xfda)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E6fc.
      iIntros "_" (h4) "Hrun".
      set (m3 := <[Regidx a1_idx
                   := regval_into_reg (zero_extend' 64 (ubyte0 : mword 8) : mword 64)]> m2).
      assert (Hinv3 : vp_inv3 m0 m3 sp0 a fd (mword_of_int apz) (mword_of_int (apz + 8)) i)
        by exact (vp_inv3_upd m0 m2 sp0 a fd (mword_of_int apz) (mword_of_int (apz + 8)) i a1_idx _
                    ltac:(vm_compute; reflexivity) Hinv2).
      (* ---- 0xfda  c.beqz a1,0x100a -- TAKEN ---- *)
      assert (Ht700 : true = eq_vec (m3 !!! Regidx a1_idx) zero_reg).
      { rewrite /m3 (upd_eq m2 (Regidx a1_idx) (regval_into_reg _)) zext8_moi.
        replace (bv_unsigned ubyte0) with 0 by (vm_compute; reflexivity).
        rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
      assert (Etgt730 : add_vec (mword_of_int 0xfda : mword 64)
                          (sign_extend' 64
                             (sign_extend' 13
                                (concat_vec (mword_of_int 24 : mword 8)
                                   ('b"0"))))
                        = mword_of_int 0x100a)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_cbeqz γt γd γs γfd h4 m3 (mword_of_int 0xfda)
                (mword_of_int 24 : mword 8) (mword_of_int 3 : mword 3) a1_idx
                true (mword_of_int 0x100a) (4 + n)
                ltac:(vm_compute; reflexivity) Ht700 (eq_sym Etgt730)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_fda with "Hcode"). }
      iIntros (h5) "Hrun".
      (* ---- 0x100a  c.mv s7,s3 ---- *)
      iApply (wp_uk_cmv γt γd γs γfd h5 m3 (mword_of_int 0x100a) s7_idx s3_idx
                (mword_of_int (apz + 8)) (4 + n)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(destruct Hinv3 as (_ & _ & _ & Hq & _); rewrite Hq;
                      symmetry; apply add_vec_zero_l)
                with "[] Hrun").
      { iApply (uis_shk_100a with "Hcode"). }
      assert (E730 : add_vec_int (mword_of_int 0x100a : mword 64) 2
                     = mword_of_int 0x100c)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E730.
      iIntros (h6) "Hrun".
      set (m4 := <[Regidx s7_idx
                   := regval_into_reg
                        (mword_of_int (apz + 8) : mword 64)]> m3).
      pose proof (vp_inv3_s7 m0 m3 sp0 a fd (mword_of_int apz)
                    (mword_of_int (apz + 8)) (mword_of_int (apz + 8)) i
                    Hinv3) as Hinv4.
      (* ---- 0x100c  c.li s3,0 -- the state goes back ---- *)
      iApply (wp_uk_cli γt γd γs γfd h6 m4 (mword_of_int 0x100c)
                (mword_of_int 0 : mword 6) s3_idx (4 + n)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                with "[] Hrun").
      { iApply (uis_shk_100c with "Hcode"). }
      assert (E732 : add_vec_int (mword_of_int 0x100c : mword 64) 2
                     = mword_of_int 0x100e)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E732.
      iIntros (h7) "Hrun".
      assert (Hinv5 : vp_inv3 m0
                        (<[Regidx s3_idx
                           := regval_into_reg
                                (sign_extend' 64 (mword_of_int 0 : mword 6)
                                 : mword 64)]> m4)
                        sp0 a fd (mword_of_int (apz + 8)) zero_reg i).
      { rewrite <- Ezr.
        exact (vp_inv3_s3 m0 m4 sp0 a fd (mword_of_int (apz + 8))
                 (mword_of_int (apz + 8)) _ i Hinv4). }
      (* ---- 0x100e  c.j 0xe2e ---- *)
      iApply (wp_uk_cj γt γd γs γfd h7 _ (mword_of_int 0x100e)
                (mword_of_int 1808 : mword 11) (mword_of_int 0xe2e) (4 + n)
                Etgt554' ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_100e with "Hcode"). }
      iIntros (h8) "Hrun".
      iApply (wp_kshd_vprintf_bump m0 sp0 fd (mword_of_int (apz + 8)) zero_reg
                a i c1 h8 _ n Ha0 Habnd Hinv5 with "Hcode Hc1 Hrun [Hw Hcont]").
      iIntros (h9 m9) "%Hinv9 %Hs19 _ Hrun".
      iApply ("Hcont" $! h9 m9 with "Hw [] [] Hrun").
      + iPureIntro. exact (vp_inv_of3 m0 m9 sp0 a fd
                             (mword_of_int (apz + 8)) (S i) Hinv9).
      + iPureIntro. exact Hs19.
    - (* AT LEAST ONE BYTE.  0xfda falls through into the loop. *)
      iDestruct (shd_str_byte γt γd tx sa (S slen') sf 0%nat
                   ltac:(lia) with "Hstr") as "[#Hb0 _]".
      iDestruct (shd_str_nonul with "Hstr") as %Hnn.
      iApply (wp_shd_lbu γt γd γs γfd h3 m2 (mword_of_int 0xfd6)
                (mword_of_int 0 : mword 12) s1_idx a1_idx tx
                (sa + Z.of_nat 0%nat)%Z (sf 0%nat) (4 + n)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                Haddr0 ltac:(vm_compute; discriminate)
                with "[] [] Hrun").
      { iApply (uis_shk_fd6 with "Hcode"). }
      { iExact "Hb0". }
      assert (E6fc : add_vec_int (mword_of_int 0xfd6 : mword 64) 4
                     = mword_of_int 0xfda)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E6fc.
      iIntros "_" (h4) "Hrun".
      set (m3 := <[Regidx a1_idx
                   := regval_into_reg
                        (zero_extend' 64 (sf 0%nat : mword 8)
                         : mword 64)]> m2).
      assert (Hinv3 : vp_inv3 m0 m3 sp0 a fd (mword_of_int apz) (mword_of_int (apz + 8)) i)
        by exact (vp_inv3_upd m0 m2 sp0 a fd (mword_of_int apz) (mword_of_int (apz + 8)) i a1_idx _
                    ltac:(vm_compute; reflexivity) Hinv2).
      (* ---- 0xfda  c.beqz a1,0x100a -- NOT taken ---- *)
      assert (Hnz0 : bv_unsigned (sf 0%nat) <> 0).
      { intro He. apply (Hnn 0%nat ltac:(lia)). apply bv_eq.
        rewrite He. vm_compute. reflexivity. }
      assert (Hr0 : 0 <= bv_unsigned (sf 0%nat) < Z64).
      { assert (HH : 0 <= bv_unsigned (sf 0%nat) < 256).
        { pose proof (bv_unsigned_in_range 8 (sf 0%nat)) as H0.
          assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
          rewrite Em8 in H0. exact H0. }
        unfold Z64. lia. }
      assert (Hn700 : false = eq_vec (m3 !!! Regidx a1_idx) zero_reg).
      { rewrite /m3 (upd_eq m2 (Regidx a1_idx) (regval_into_reg _)) zext8_moi.
        rewrite (moi_eq_zero (bv_unsigned (sf 0%nat)) Hr0).
        destruct (Z.eqb_spec (bv_unsigned (sf 0%nat)) 0) as [He | _];
          [ exfalso; exact (Hnz0 He) | reflexivity ]. }
      iApply (wp_uk_cbeqz γt γd γs γfd h4 m3 (mword_of_int 0xfda)
                (mword_of_int 24 : mword 8) (mword_of_int 3 : mword 3) a1_idx
                false
                (add_vec (mword_of_int 0xfda : mword 64)
                   (sign_extend' 64
                      (sign_extend' 13
                         (concat_vec (mword_of_int 24 : mword 8) ('b"0")))))
                (4 + n) ltac:(vm_compute; reflexivity) Hn700 eq_refl
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shk_fda with "Hcode"). }
      assert (E700 : add_vec_int (mword_of_int 0xfda : mword 64) 2
                     = mword_of_int 0xfdc)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E700.
      iIntros (h5) "Hrun".
      assert (Hs1_3 : m3 !!! Regidx s1_idx
                      = mword_of_int (sa + Z.of_nat 0%nat)).
      { rewrite /m3 (upd_ne m2 (Regidx a1_idx) (Regidx s1_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite Hs1_2. f_equal; lia. }
      iApply (wp_kshd_vprintf_sloop m0 sp0 fd (mword_of_int apz)
                (mword_of_int (apz + 8)) a i sa (S slen') sf slen'
                Hsa0 Hsahi 0%nat h5 m3 n ltac:(lia) Hinv3 Hs1_3
                with "Hcode Hstr Hrun [Hw Hcont]").
      iIntros (h6 m6) "%Hinv6 Hrun".
      pose proof Hinv6 as Hd6.
      destruct Hd6 as (_ & _ & _ & Hs36 & _).
      (* ---- 0xfea  c.mv s7,s3 ---- *)
      iApply (wp_uk_cmv γt γd γs γfd h6 m6 (mword_of_int 0xfea) s7_idx s3_idx
                (mword_of_int (apz + 8)) (4 + n)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs36; symmetry; apply add_vec_zero_l)
                with "[] Hrun").
      { iApply (uis_shk_fea with "Hcode"). }
      assert (E710 : add_vec_int (mword_of_int 0xfea : mword 64) 2
                     = mword_of_int 0xfec)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E710.
      iIntros (h7) "Hrun".
      set (m7 := <[Regidx s7_idx
                   := regval_into_reg
                        (mword_of_int (apz + 8) : mword 64)]> m6).
      pose proof (vp_inv3_s7 m0 m6 sp0 a fd (mword_of_int apz)
                    (mword_of_int (apz + 8)) (mword_of_int (apz + 8)) i
                    Hinv6) as Hinv7.
      (* ---- 0xfec  c.li s3,0 ---- *)
      iApply (wp_uk_cli γt γd γs γfd h7 m7 (mword_of_int 0xfec)
                (mword_of_int 0 : mword 6) s3_idx (4 + n)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                with "[] Hrun").
      { iApply (uis_shk_fec with "Hcode"). }
      assert (E712 : add_vec_int (mword_of_int 0xfec : mword 64) 2
                     = mword_of_int 0xfee)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E712.
      iIntros (h8) "Hrun".
      assert (Hinv8 : vp_inv3 m0
                        (<[Regidx s3_idx
                           := regval_into_reg
                                (sign_extend' 64 (mword_of_int 0 : mword 6)
                                 : mword 64)]> m7)
                        sp0 a fd (mword_of_int (apz + 8)) zero_reg i).
      { rewrite <- Ezr.
        exact (vp_inv3_s3 m0 m7 sp0 a fd (mword_of_int (apz + 8))
                 (mword_of_int (apz + 8)) _ i Hinv7). }
      (* ---- 0xfee  c.j 0xe2e ---- *)
      iApply (wp_uk_cj γt γd γs γfd h8 _ (mword_of_int 0xfee)
                (mword_of_int 1824 : mword 11) (mword_of_int 0xe2e) (4 + n)
                Etgt554 ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_fee with "Hcode"). }
      iIntros (h9) "Hrun".
      iApply (wp_kshd_vprintf_bump m0 sp0 fd (mword_of_int (apz + 8)) zero_reg
                a i c1 h9 _ n Ha0 Habnd Hinv8 with "Hcode Hc1 Hrun [Hw Hcont]").
      iIntros (h10 m10) "%Hinv10 %Hs110 _ Hrun".
      iApply ("Hcont" $! h10 m10 with "Hw [] [] Hrun").
      + iPureIntro. exact (vp_inv_of3 m0 m10 sp0 a fd
                             (mword_of_int (apz + 8)) (S i) Hinv10).
      + iPureIntro. exact Hs110.
  Qed.

  (* --------------------------------------------------------------------- *)
  (* THE REST OF THE CHAIN, 0x103c -> 0xfcc.  Eight more tests: 'u', then    *)
  (* the two long forms of it, then 'x' and its two, then 'p', then 'c',    *)
  (* and finally 's'.  a0, a2, a1 and a4 are scratch throughout.            *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kshd_vprintf_pcs2 (m0 : regfile) (sp0 fd : mword 64) (a : Z)
      (i : nat) (apz sa : Z) (dq : dfrac) (c1 c2 : mword 8)
      (slen : nat) (sf : nat -> bv 8)
      (m : regfile) (h : CpuId) (n : nat) :
    0 <= a -> a + Z.of_nat i + 3 < 2 ^ 31 ->
    0 <= apz -> apz + 8 <= 2 ^ 38 -> apz mod 8 = 0 ->
    sa <> 0 ->
    0 <= bv_unsigned c1 < 256 -> 0 <= bv_unsigned c2 < 256 ->
    bv_unsigned c1 <> 117 -> bv_unsigned c1 <> 120 ->
    bv_unsigned c2 <> 117 -> bv_unsigned c2 <> 120 ->
    vp_inv3 m0 m sp0 a fd (mword_of_int apz) (mword_of_int 37) i ->
    m !!! Regidx a1_idx = mword_of_int (bv_unsigned c2) ->
    m !!! Regidx a2_idx = mword_of_int (bv_unsigned c1) ->
    m !!! Regidx a5_idx = mword_of_int 115 ->
    shk_code γt -∗
    utext γt (a + Z.of_nat (S i)) c1 -∗
    uwordq γd dq apz (mword_of_int sa) -∗
    shd_str γt γd tx sa slen sf -∗
    urun γt γd γs γfd h m (mword_of_int 0x103c) (4 + n) -∗
    (∀ (h' : CpuId) (m' : regfile),
       uwordq γd dq apz (mword_of_int sa) -∗
       ⌜ vp_inv m0 m' sp0 a fd (mword_of_int (apz + 8)) (S i) ⌝ -∗
       ⌜ m' !!! Regidx s1_idx = mword_of_int (bv_unsigned c1) ⌝ -∗
       urun γt γd γs γfd h' m' (mword_of_int 0xe3c) (4 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd Hap0 Haphi Hapal Hsanz Hr1 Hr2 Hc1u Hc1x Hc2u Hc2x
           Hinv Ha1 Ha2 Ha5.
    iIntros "#Hcode #Hc1 Hw #Hstr Hrun Hcont".
    assert (Em117 : (sign_extend' 64 (mword_of_int 3979 : mword 12) : mword 64)
                    = mword_of_int (-117))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em120 : (sign_extend' 64 (mword_of_int 3976 : mword 12) : mword 64)
                    = mword_of_int (-120))
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0x103c  li a0,117 ---- *)
    iApply (wp_uk_li γt γd γs γfd h m (mword_of_int 0x103c)
              (mword_of_int 117 : mword 12) a0_idx (mword_of_int 117) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_103c with "Hcode"). }
    assert (E762 : add_vec_int (mword_of_int 0x103c : mword 64) 4
                   = mword_of_int 0x1040)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E762.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 117 : mword 64)]> m).
    assert (Hinv1 : vp_inv3 m0 m1 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m sp0 a fd (mword_of_int apz) (mword_of_int 37) i a0_idx _
                  ltac:(vm_compute; reflexivity) Hinv).
    assert (Ha0_1 : m1 !!! Regidx a0_idx = mword_of_int 117)
      by exact (upd_eq m (Regidx a0_idx) (regval_into_reg _)).
    assert (Ha1_1 : m1 !!! Regidx a1_idx = (mword_of_int (bv_unsigned c2))).
    { rewrite <- Ha1.
      exact (upd_ne m (Regidx a0_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha2_1 : m1 !!! Regidx a2_idx = (mword_of_int (bv_unsigned c1))).
    { rewrite <- Ha2.
      exact (upd_ne m (Regidx a0_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha5_1 : m1 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha5.
      exact (upd_ne m (Regidx a0_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x1040  beq a5,a0 -- NOT taken ---- *)
    assert (Hn766 : false
                    = uv_btaken BEQ (m1 !!! Regidx a5_idx)
                        (m1 !!! Regidx a0_idx))
      by (rewrite Ha5_1 Ha0_1; vm_compute; reflexivity).
    iApply (wp_uk_btype γt γd γs γfd h1 m1 (mword_of_int 0x1040)
              (mword_of_int 7832 : mword 13) a0_idx a5_idx BEQ false
              (add_vec (mword_of_int 0x1040 : mword 64)
                 (sign_extend' 64 (mword_of_int 7832 : mword 13)))
              (4 + n) Hn766 eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shk_1040 with "Hcode"). }
    assert (E766 : add_vec_int (mword_of_int 0x1040 : mword 64) 4
                   = mword_of_int 0x1044)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E766.
    iIntros (h2) "Hrun".
    (* ---- 0x1044  addi a0,a2,-117 ---- *)
    assert (Ev76a : add_vec (m1 !!! Regidx a2_idx)
                     (sign_extend' 64 (mword_of_int 3979 : mword 12))
                   = mword_of_int (bv_unsigned c1 - 117))
      by (rewrite Ha2_1 Em117 moi_add; reflexivity).
    iApply (wp_uk_addi γt γd γs γfd h2 m1 (mword_of_int 0x1044)
              (mword_of_int 3979 : mword 12) a2_idx a0_idx
              (mword_of_int (bv_unsigned c1 - 117)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ev76a))
              with "[] Hrun").
    { iApply (uis_shk_1044 with "Hcode"). }
    assert (E76a : add_vec_int (mword_of_int 0x1044 : mword 64) 4
                   = mword_of_int 0x1048)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E76a.
    iIntros (h3) "Hrun".
    set (m2 := <[Regidx a0_idx
                 := regval_into_reg
                      (mword_of_int (bv_unsigned c1 - 117) : mword 64)]> m1).
    assert (Hinv2 : vp_inv3 m0 m2 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m1 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a0_idx _
                  ltac:(vm_compute; reflexivity) Hinv1).
    assert (Ha0_2 : m2 !!! Regidx a0_idx = mword_of_int (bv_unsigned c1 - 117))
      by exact (upd_eq m1 (Regidx a0_idx) (regval_into_reg _)).
    assert (Ha1_2 : m2 !!! Regidx a1_idx = (mword_of_int (bv_unsigned c2))).
    { rewrite <- Ha1_1.
      exact (upd_ne m1 (Regidx a0_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha2_2 : m2 !!! Regidx a2_idx = (mword_of_int (bv_unsigned c1))).
    { rewrite <- Ha2_1.
      exact (upd_ne m1 (Regidx a0_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha5_2 : m2 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha5_1.
      exact (upd_ne m1 (Regidx a0_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x1048  c.bnez a0,0x104e -- TAKEN ---- *)
    assert (Ht76e : true = neq_vec (m2 !!! Regidx a0_idx) zero_reg)
      by (rewrite Ha0_2;
          exact (eq_sym (moi_sub_ne_zero (bv_unsigned c1) 117 Hr1
                           ltac:(lia) Hc1u))).
    assert (Et76e : add_vec (mword_of_int 0x1048 : mword 64)
                     (sign_extend' 64
                        (sign_extend' 13
                           (concat_vec (mword_of_int 3 : mword 8) ('b"0"))))
                   = mword_of_int 0x104e)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cbnez γt γd γs γfd h3 m2 (mword_of_int 0x1048)
              (mword_of_int 3 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              true (mword_of_int 0x104e) (4 + n)
              ltac:(vm_compute; reflexivity) Ht76e (eq_sym Et76e)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_1048 with "Hcode"). }
    iIntros (h4) "Hrun".
    (* ---- 0x104e  addi a0,a1,-117 ---- *)
    assert (Ev774 : add_vec (m2 !!! Regidx a1_idx)
                     (sign_extend' 64 (mword_of_int 3979 : mword 12))
                   = mword_of_int (bv_unsigned c2 - 117))
      by (rewrite Ha1_2 Em117 moi_add; reflexivity).
    iApply (wp_uk_addi γt γd γs γfd h4 m2 (mword_of_int 0x104e)
              (mword_of_int 3979 : mword 12) a1_idx a0_idx
              (mword_of_int (bv_unsigned c2 - 117)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ev774))
              with "[] Hrun").
    { iApply (uis_shk_104e with "Hcode"). }
    assert (E774 : add_vec_int (mword_of_int 0x104e : mword 64) 4
                   = mword_of_int 0x1052)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E774.
    iIntros (h5) "Hrun".
    set (m3 := <[Regidx a0_idx
                 := regval_into_reg
                      (mword_of_int (bv_unsigned c2 - 117) : mword 64)]> m2).
    assert (Hinv3 : vp_inv3 m0 m3 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m2 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a0_idx _
                  ltac:(vm_compute; reflexivity) Hinv2).
    assert (Ha0_3 : m3 !!! Regidx a0_idx = mword_of_int (bv_unsigned c2 - 117))
      by exact (upd_eq m2 (Regidx a0_idx) (regval_into_reg _)).
    assert (Ha1_3 : m3 !!! Regidx a1_idx = (mword_of_int (bv_unsigned c2))).
    { rewrite <- Ha1_2.
      exact (upd_ne m2 (Regidx a0_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha2_3 : m3 !!! Regidx a2_idx = (mword_of_int (bv_unsigned c1))).
    { rewrite <- Ha2_2.
      exact (upd_ne m2 (Regidx a0_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha5_3 : m3 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha5_2.
      exact (upd_ne m2 (Regidx a0_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x1052  c.bnez a0,0x1058 -- TAKEN ---- *)
    assert (Ht778 : true = neq_vec (m3 !!! Regidx a0_idx) zero_reg)
      by (rewrite Ha0_3;
          exact (eq_sym (moi_sub_ne_zero (bv_unsigned c2) 117 Hr2
                           ltac:(lia) Hc2u))).
    assert (Et778 : add_vec (mword_of_int 0x1052 : mword 64)
                     (sign_extend' 64
                        (sign_extend' 13
                           (concat_vec (mword_of_int 3 : mword 8) ('b"0"))))
                   = mword_of_int 0x1058)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cbnez γt γd γs γfd h5 m3 (mword_of_int 0x1052)
              (mword_of_int 3 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              true (mword_of_int 0x1058) (4 + n)
              ltac:(vm_compute; reflexivity) Ht778 (eq_sym Et778)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_1052 with "Hcode"). }
    iIntros (h6) "Hrun".
    (* ---- 0x1058  li a0,120 ---- *)
    iApply (wp_uk_li γt γd γs γfd h6 m3 (mword_of_int 0x1058)
              (mword_of_int 120 : mword 12) a0_idx (mword_of_int 120) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_1058 with "Hcode"). }
    assert (E77e : add_vec_int (mword_of_int 0x1058 : mword 64) 4
                   = mword_of_int 0x105c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E77e.
    iIntros (h7) "Hrun".
    set (m4 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 120 : mword 64)]> m3).
    assert (Hinv4 : vp_inv3 m0 m4 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m3 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a0_idx _
                  ltac:(vm_compute; reflexivity) Hinv3).
    assert (Ha0_4 : m4 !!! Regidx a0_idx = mword_of_int 120)
      by exact (upd_eq m3 (Regidx a0_idx) (regval_into_reg _)).
    assert (Ha1_4 : m4 !!! Regidx a1_idx = (mword_of_int (bv_unsigned c2))).
    { rewrite <- Ha1_3.
      exact (upd_ne m3 (Regidx a0_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha2_4 : m4 !!! Regidx a2_idx = (mword_of_int (bv_unsigned c1))).
    { rewrite <- Ha2_3.
      exact (upd_ne m3 (Regidx a0_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha5_4 : m4 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha5_3.
      exact (upd_ne m3 (Regidx a0_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x105c  beq a5,a0 -- NOT taken ---- *)
    assert (Hn782 : false
                    = uv_btaken BEQ (m4 !!! Regidx a5_idx)
                        (m4 !!! Regidx a0_idx))
      by (rewrite Ha5_4 Ha0_4; vm_compute; reflexivity).
    iApply (wp_uk_btype γt γd γs γfd h7 m4 (mword_of_int 0x105c)
              (mword_of_int 7880 : mword 13) a0_idx a5_idx BEQ false
              (add_vec (mword_of_int 0x105c : mword 64)
                 (sign_extend' 64 (mword_of_int 7880 : mword 13)))
              (4 + n) Hn782 eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shk_105c with "Hcode"). }
    assert (E782 : add_vec_int (mword_of_int 0x105c : mword 64) 4
                   = mword_of_int 0x1060)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E782.
    iIntros (h8) "Hrun".
    (* ---- 0x1060  addi a2,a2,-120 ---- *)
    assert (Ev786 : add_vec (m4 !!! Regidx a2_idx)
                     (sign_extend' 64 (mword_of_int 3976 : mword 12))
                   = mword_of_int (bv_unsigned c1 - 120))
      by (rewrite Ha2_4 Em120 moi_add; reflexivity).
    iApply (wp_uk_addi γt γd γs γfd h8 m4 (mword_of_int 0x1060)
              (mword_of_int 3976 : mword 12) a2_idx a2_idx
              (mword_of_int (bv_unsigned c1 - 120)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ev786))
              with "[] Hrun").
    { iApply (uis_shk_1060 with "Hcode"). }
    assert (E786 : add_vec_int (mword_of_int 0x1060 : mword 64) 4
                   = mword_of_int 0x1064)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E786.
    iIntros (h9) "Hrun".
    set (m5 := <[Regidx a2_idx
                 := regval_into_reg
                      (mword_of_int (bv_unsigned c1 - 120) : mword 64)]> m4).
    assert (Hinv5 : vp_inv3 m0 m5 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m4 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a2_idx _
                  ltac:(vm_compute; reflexivity) Hinv4).
    assert (Ha2_5 : m5 !!! Regidx a2_idx = mword_of_int (bv_unsigned c1 - 120))
      by exact (upd_eq m4 (Regidx a2_idx) (regval_into_reg _)).
    assert (Ha1_5 : m5 !!! Regidx a1_idx = (mword_of_int (bv_unsigned c2))).
    { rewrite <- Ha1_4.
      exact (upd_ne m4 (Regidx a2_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha5_5 : m5 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha5_4.
      exact (upd_ne m4 (Regidx a2_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x1064  c.bnez a2,0x106a -- TAKEN ---- *)
    assert (Ht78a : true = neq_vec (m5 !!! Regidx a2_idx) zero_reg)
      by (rewrite Ha2_5;
          exact (eq_sym (moi_sub_ne_zero (bv_unsigned c1) 120 Hr1
                           ltac:(lia) Hc1x))).
    assert (Et78a : add_vec (mword_of_int 0x1064 : mword 64)
                     (sign_extend' 64
                        (sign_extend' 13
                           (concat_vec (mword_of_int 3 : mword 8) ('b"0"))))
                   = mword_of_int 0x106a)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cbnez γt γd γs γfd h9 m5 (mword_of_int 0x1064)
              (mword_of_int 3 : mword 8) (mword_of_int 4 : mword 3) a2_idx
              true (mword_of_int 0x106a) (4 + n)
              ltac:(vm_compute; reflexivity) Ht78a (eq_sym Et78a)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_1064 with "Hcode"). }
    iIntros (h10) "Hrun".
    (* ---- 0x106a  addi a1,a1,-120 ---- *)
    assert (Ev790 : add_vec (m5 !!! Regidx a1_idx)
                     (sign_extend' 64 (mword_of_int 3976 : mword 12))
                   = mword_of_int (bv_unsigned c2 - 120))
      by (rewrite Ha1_5 Em120 moi_add; reflexivity).
    iApply (wp_uk_addi γt γd γs γfd h10 m5 (mword_of_int 0x106a)
              (mword_of_int 3976 : mword 12) a1_idx a1_idx
              (mword_of_int (bv_unsigned c2 - 120)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ev790))
              with "[] Hrun").
    { iApply (uis_shk_106a with "Hcode"). }
    assert (E790 : add_vec_int (mword_of_int 0x106a : mword 64) 4
                   = mword_of_int 0x106e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E790.
    iIntros (h11) "Hrun".
    set (m6 := <[Regidx a1_idx
                 := regval_into_reg
                      (mword_of_int (bv_unsigned c2 - 120) : mword 64)]> m5).
    assert (Hinv6 : vp_inv3 m0 m6 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m5 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a1_idx _
                  ltac:(vm_compute; reflexivity) Hinv5).
    assert (Ha1_6 : m6 !!! Regidx a1_idx = mword_of_int (bv_unsigned c2 - 120))
      by exact (upd_eq m5 (Regidx a1_idx) (regval_into_reg _)).
    assert (Ha5_6 : m6 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha5_5.
      exact (upd_ne m5 (Regidx a1_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x106e  c.bnez a1,0x1074 -- TAKEN ---- *)
    assert (Ht794 : true = neq_vec (m6 !!! Regidx a1_idx) zero_reg)
      by (rewrite Ha1_6;
          exact (eq_sym (moi_sub_ne_zero (bv_unsigned c2) 120 Hr2
                           ltac:(lia) Hc2x))).
    assert (Et794 : add_vec (mword_of_int 0x106e : mword 64)
                     (sign_extend' 64
                        (sign_extend' 13
                           (concat_vec (mword_of_int 3 : mword 8) ('b"0"))))
                   = mword_of_int 0x1074)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cbnez γt γd γs γfd h11 m6 (mword_of_int 0x106e)
              (mword_of_int 3 : mword 8) (mword_of_int 3 : mword 3) a1_idx
              true (mword_of_int 0x1074) (4 + n)
              ltac:(vm_compute; reflexivity) Ht794 (eq_sym Et794)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_106e with "Hcode"). }
    iIntros (h12) "Hrun".
    (* ---- 0x1074  li a4,112 ---- *)
    iApply (wp_uk_li γt γd γs γfd h12 m6 (mword_of_int 0x1074)
              (mword_of_int 112 : mword 12) a4_idx (mword_of_int 112) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_1074 with "Hcode"). }
    assert (E79a : add_vec_int (mword_of_int 0x1074 : mword 64) 4
                   = mword_of_int 0x1078)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E79a.
    iIntros (h13) "Hrun".
    set (m7 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 112 : mword 64)]> m6).
    assert (Hinv7 : vp_inv3 m0 m7 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m6 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a4_idx _
                  ltac:(vm_compute; reflexivity) Hinv6).
    assert (Ha4_7 : m7 !!! Regidx a4_idx = mword_of_int 112)
      by exact (upd_eq m6 (Regidx a4_idx) (regval_into_reg _)).
    assert (Ha5_7 : m7 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha5_6.
      exact (upd_ne m6 (Regidx a4_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x1078  beq a5,a4 -- NOT taken ---- *)
    assert (Hn79e : false
                    = uv_btaken BEQ (m7 !!! Regidx a5_idx)
                        (m7 !!! Regidx a4_idx))
      by (rewrite Ha5_7 Ha4_7; vm_compute; reflexivity).
    iApply (wp_uk_btype γt γd γs γfd h13 m7 (mword_of_int 0x1078)
              (mword_of_int 7928 : mword 13) a4_idx a5_idx BEQ false
              (add_vec (mword_of_int 0x1078 : mword 64)
                 (sign_extend' 64 (mword_of_int 7928 : mword 13)))
              (4 + n) Hn79e eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shk_1078 with "Hcode"). }
    assert (E79e : add_vec_int (mword_of_int 0x1078 : mword 64) 4
                   = mword_of_int 0x107c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E79e.
    iIntros (h14) "Hrun".
    (* ---- 0x107c  li a4,99 ---- *)
    iApply (wp_uk_li γt γd γs γfd h14 m7 (mword_of_int 0x107c)
              (mword_of_int 99 : mword 12) a4_idx (mword_of_int 99) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_107c with "Hcode"). }
    assert (E7a2 : add_vec_int (mword_of_int 0x107c : mword 64) 4
                   = mword_of_int 0x1080)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7a2.
    iIntros (h15) "Hrun".
    set (m8 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 99 : mword 64)]> m7).
    assert (Hinv8 : vp_inv3 m0 m8 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m7 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a4_idx _
                  ltac:(vm_compute; reflexivity) Hinv7).
    assert (Ha4_8 : m8 !!! Regidx a4_idx = mword_of_int 99)
      by exact (upd_eq m7 (Regidx a4_idx) (regval_into_reg _)).
    assert (Ha5_8 : m8 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha5_7.
      exact (upd_ne m7 (Regidx a4_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x1080  beq a5,a4 -- NOT taken ---- *)
    assert (Hn7a6 : false
                    = uv_btaken BEQ (m8 !!! Regidx a5_idx)
                        (m8 !!! Regidx a4_idx))
      by (rewrite Ha5_8 Ha4_8; vm_compute; reflexivity).
    iApply (wp_uk_btype γt γd γs γfd h15 m8 (mword_of_int 0x1080)
              (mword_of_int 7992 : mword 13) a4_idx a5_idx BEQ false
              (add_vec (mword_of_int 0x1080 : mword 64)
                 (sign_extend' 64 (mword_of_int 7992 : mword 13)))
              (4 + n) Hn7a6 eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shk_1080 with "Hcode"). }
    assert (E7a6 : add_vec_int (mword_of_int 0x1080 : mword 64) 4
                   = mword_of_int 0x1084)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7a6.
    iIntros (h16) "Hrun".
    (* ---- 0x1084  li a4,115 ---- *)
    iApply (wp_uk_li γt γd γs γfd h16 m8 (mword_of_int 0x1084)
              (mword_of_int 115 : mword 12) a4_idx (mword_of_int 115) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_1084 with "Hcode"). }
    assert (E7aa : add_vec_int (mword_of_int 0x1084 : mword 64) 4
                   = mword_of_int 0x1088)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7aa.
    iIntros (h17) "Hrun".
    set (m9 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 115 : mword 64)]> m8).
    assert (Hinv9 : vp_inv3 m0 m9 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m8 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a4_idx _
                  ltac:(vm_compute; reflexivity) Hinv8).
    assert (Ha4_9 : m9 !!! Regidx a4_idx = mword_of_int 115)
      by exact (upd_eq m8 (Regidx a4_idx) (regval_into_reg _)).
    assert (Ha5_9 : m9 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha5_8.
      exact (upd_ne m8 (Regidx a4_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x1088  beq a5,a4,0xfcc -- TAKEN: the directive is 's' ---- *)
    assert (Ht7ae : true
                    = uv_btaken BEQ (m9 !!! Regidx a5_idx)
                        (m9 !!! Regidx a4_idx))
      by (rewrite Ha5_9 Ha4_9; vm_compute; reflexivity).
    assert (Et7ae : add_vec (mword_of_int 0x1088 : mword 64)
                      (sign_extend' 64 (mword_of_int 8004 : mword 13))
                    = mword_of_int 0xfcc)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_btype γt γd γs γfd h17 m9 (mword_of_int 0x1088)
              (mword_of_int 8004 : mword 13) a4_idx a5_idx BEQ true
              (mword_of_int 0xfcc) (4 + n) Ht7ae (eq_sym Et7ae)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_1088 with "Hcode"). }
    iIntros (h18) "Hrun".
    iApply (wp_kshd_vprintf_pcs3 m0 sp0 fd a i apz sa dq c1 slen sf
              m9 h18 n Ha0 ltac:(lia) Hap0 Haphi Hapal Hsanz Hinv9
              with "Hcode Hc1 Hw Hstr Hrun Hcont").
  Qed.

  (* ===================================================================== *)
  (* THE DIRECTIVE'S ROUND, 0xe40 -> 0xe3c, for c0 = 's'.                   *)
  (*                                                                        *)
  (* The state register is '%', so 0xe44 and 0xe2a both go to 0xe50 and the *)
  (* dispatch begins.  It is a chain of tests on three characters -- c0,    *)
  (* c1 = fmt[i+1] and c2 = fmt[i+2] -- and the arms it skips are the       *)
  (* multi-character directives (%ld, %lld, %lu, %llu, %lx, %llx), which is *)
  (* why c1 and c2 are read at all for a directive that uses neither.       *)
  (*                                                                        *)
  (* With c0 fixed at 's' the outcome of every test is decided by one       *)
  (* [vm_compute] on a concrete pair, or -- where a byte is involved -- by  *)
  (* [moi_sub_ne_zero] and the corresponding hypothesis.  a3 and a4 are     *)
  (* left as the opaque expressions the leaves produce: the two branches    *)
  (* that read them (0x104a and 0x1070) are reached only when c1 or c2 IS the *)
  (* character just excluded, so no step in this path depends on them.      *)
  (* ===================================================================== *)
  Lemma wp_kshd_vprintf_pcs (m0 : regfile) (sp0 fd : mword 64) (a : Z)
      (i : nat) (apz sa : Z) (dq : dfrac) (c1 c2 : mword 8)
      (slen : nat) (sf : nat -> bv 8) (h : CpuId) (m : regfile) (n : nat) :
    0 <= a -> a + Z.of_nat i + 3 < 2 ^ 31 ->
    0 <= apz -> apz + 8 <= 2 ^ 38 -> apz mod 8 = 0 ->
    sa <> 0 ->
    bv_unsigned c1 <> 0 ->
    bv_unsigned c1 <> 100 -> bv_unsigned c1 <> 117 -> bv_unsigned c1 <> 120 ->
    bv_unsigned c2 <> 100 -> bv_unsigned c2 <> 117 -> bv_unsigned c2 <> 120 ->
    vp_inv3 m0 m sp0 a fd (mword_of_int apz) (mword_of_int 37) i ->
    m !!! Regidx s1_idx = mword_of_int 115 ->
    m !!! Regidx a4_idx = mword_of_int (Z.of_nat i) ->
    shk_code γt -∗
    utext γt (a + Z.of_nat (S i)) c1 -∗
    utext γt (a + Z.of_nat (S (S i))) c2 -∗
    uwordq γd dq apz (mword_of_int sa) -∗
    shd_str γt γd tx sa slen sf -∗
    urun γt γd γs γfd h m (mword_of_int 0xe40) (4 + n) -∗
    (∀ (h' : CpuId) (m' : regfile),
       uwordq γd dq apz (mword_of_int sa) -∗
       ⌜ vp_inv m0 m' sp0 a fd (mword_of_int (apz + 8)) (S i) ⌝ -∗
       ⌜ m' !!! Regidx s1_idx = mword_of_int (bv_unsigned c1) ⌝ -∗
       urun γt γd γs γfd h' m' (mword_of_int 0xe3c) (4 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd Hap0 Haphi Hapal Hsanz
           Hc1z Hc1d Hc1u Hc1x Hc2d Hc2u Hc2x Hinv Hs1 Ha4.
    pose proof Hinv as Hd.
    destruct Hd as (Hsp & Hs0 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hfr).
    iIntros "#Hcode #Hc1 #Hc2 Hw Hstr Hrun Hcont".
    iDestruct (urun_shd_str_bnd with "Hrun Hstr") as %[Hsa0 Hsahi].
    (* the byte ranges, and the four negative immediates *)
    assert (Hr1 : 0 <= bv_unsigned c1 < 256).
    { pose proof (bv_unsigned_in_range 8 c1) as H0.
      assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
      rewrite Em8 in H0. exact H0. }
    assert (Hr2 : 0 <= bv_unsigned c2 < 256).
    { pose proof (bv_unsigned_in_range 8 c2) as H0.
      assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
      rewrite Em8 in H0. exact H0. }
    assert (Em100 : (sign_extend' 64 (mword_of_int 3996 : mword 12) : mword 64)
                    = mword_of_int (-100))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em117 : (sign_extend' 64 (mword_of_int 3979 : mword 12) : mword 64)
                    = mword_of_int (-117))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em120 : (sign_extend' 64 (mword_of_int 3976 : mword 12) : mword 64)
                    = mword_of_int (-120))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hai : 0 <= a + Z.of_nat i < Z64) by (unfold Z64; lia).
    (* ---- 0xe40  sext.w a5,s1 ---- *)
    assert (Ez0 : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                  = mword_of_int 0)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Ea5c : sign_extend' 64
                     (subrange_vec_dec
                        (add_vec (m !!! Regidx s1_idx)
                           (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0)
                   = (mword_of_int 115 : mword 64)).
    { rewrite Hs1 Ez0.
      rewrite (moi_addw 115 0 ltac:(unfold Z31; lia)). f_equal; lia. }
    iApply (wp_uk_addiw γt γd γs γfd h m (mword_of_int 0xe40)
              (mword_of_int 0 : mword 12) s1_idx a5_idx (mword_of_int 115)
              (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ea5c))
              with "[] Hrun").
    { iApply (uis_shk_e40 with "Hcode"). }
    assert (E566 : add_vec_int (mword_of_int 0xe40 : mword 64) 4
                   = mword_of_int 0xe44)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E566.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int 115 : mword 64)]> m).
    assert (Hinv1 : vp_inv3 m0 m1 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m sp0 a fd (mword_of_int apz) (mword_of_int 37) i a5_idx _
                  ltac:(vm_compute; reflexivity) Hinv).
    pose proof Hinv1 as Hd1.
    destruct Hd1 as (Hsp1 & Hs01 & Hs21 & Hs31 & Hs41 & Hs51 & Hs61 & Hs71
                     & Hs81 & Hfr1).
    assert (Ha51 : m1 !!! Regidx a5_idx = mword_of_int 115)
      by exact (upd_eq m (Regidx a5_idx) (regval_into_reg _)).
    assert (Ha41 : m1 !!! Regidx a4_idx = mword_of_int (Z.of_nat i)).
    { rewrite <- Ha4.
      exact (upd_ne m (Regidx a5_idx) (Regidx a4_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0xe44  bnez s3,0xe2a -- TAKEN: a directive is pending ---- *)
    assert (Ht56a : true = uv_btaken BNE (m1 !!! Regidx s3_idx) zero_reg)
      by (rewrite Hs31; vm_compute; reflexivity).
    assert (Etgt550 : add_vec (mword_of_int 0xe44 : mword 64)
                        (sign_extend' 64 (mword_of_int 8166 : mword 13))
                      = mword_of_int 0xe2a)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_btype0 γt γd γs γfd h1 m1 (mword_of_int 0xe44)
              (mword_of_int 8166 : mword 13) s3_idx BNE true
              (mword_of_int 0xe2a) (4 + n) Ht56a (eq_sym Etgt550)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_e44 with "Hcode"). }
    iIntros (h2) "Hrun".
    (* ---- 0xe2a  beq s3,s5,0xe50 -- TAKEN: the state IS '%' ---- *)
    assert (Ht550 : true
                    = uv_btaken BEQ (m1 !!! Regidx s3_idx) (m1 !!! Regidx s5_idx))
      by (rewrite Hs31 Hs51; vm_compute; reflexivity).
    assert (Etgt576 : add_vec (mword_of_int 0xe2a : mword 64)
                        (sign_extend' 64 (mword_of_int 38 : mword 13))
                      = mword_of_int 0xe50)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_btype γt γd γs γfd h2 m1 (mword_of_int 0xe2a)
              (mword_of_int 38 : mword 13) s5_idx s3_idx BEQ true
              (mword_of_int 0xe50) (4 + n) Ht550 (eq_sym Etgt576)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_e2a with "Hcode"). }
    iIntros (h3) "Hrun".
    (* ---- 0xe50  add a3,s4,a4 -- &fmt[i] ---- *)
    assert (Eadd3 : add_vec (m1 !!! Regidx s4_idx) (m1 !!! Regidx a4_idx)
                    = mword_of_int (a + Z.of_nat i))
      by (rewrite Hs41 Ha41 moi_add; reflexivity).
    iApply (wp_uk_add γt γd γs γfd h3 m1 (mword_of_int 0xe50) s4_idx a4_idx a3_idx
              (mword_of_int (a + Z.of_nat i)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Eadd3))
              with "[] Hrun").
    { iApply (uis_shk_e50 with "Hcode"). }
    assert (E576 : add_vec_int (mword_of_int 0xe50 : mword 64) 4
                   = mword_of_int 0xe54)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E576.
    iIntros (h4) "Hrun".
    set (m2 := <[Regidx a3_idx
                 := regval_into_reg
                      (mword_of_int (a + Z.of_nat i) : mword 64)]> m1).
    assert (Hinv2 : vp_inv3 m0 m2 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m1 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a3_idx _
                  ltac:(vm_compute; reflexivity) Hinv1).
    assert (Ha32 : m2 !!! Regidx a3_idx = mword_of_int (a + Z.of_nat i))
      by exact (upd_eq m1 (Regidx a3_idx) (regval_into_reg _)).
    assert (Ha52 : m2 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha51.
      exact (upd_ne m1 (Regidx a3_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha42 : m2 !!! Regidx a4_idx = mword_of_int (Z.of_nat i)).
    { rewrite <- Ha41.
      exact (upd_ne m1 (Regidx a3_idx) (Regidx a4_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0xe54  lbu a2,1(a3) -- c1 = fmt[i+1] ---- *)
    assert (Haddr1 : (a + Z.of_nat (S i))%Z
                     = uint (m2 !!! Regidx a3_idx)
                       + uoff_i12 (mword_of_int 1 : mword 12)).
    { rewrite Ha32 (uint_moi (a + Z.of_nat i) Hai).
      replace (uoff_i12 (mword_of_int 1 : mword 12)) with 1
        by (vm_compute; reflexivity).
      lia. }
    iApply (wp_uk_lbu_text γt γd γs γfd h4 m2 (mword_of_int 0xe54)
              (mword_of_int 1 : mword 12) a3_idx a2_idx
              (a + Z.of_nat (S i)) c1 (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              Haddr1 ltac:(vm_compute; discriminate)
              with "[] Hc1 Hrun").
    { iApply (uis_shk_e54 with "Hcode"). }
    assert (E57a : add_vec_int (mword_of_int 0xe54 : mword 64) 4
                   = mword_of_int 0xe58)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E57a.
    iIntros (h5) "Hrun".
    set (m3 := <[Regidx a2_idx
                 := regval_into_reg (zero_extend' 64 c1 : mword 64)]> m2).
    assert (Hinv3 : vp_inv3 m0 m3 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m2 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a2_idx _
                  ltac:(vm_compute; reflexivity) Hinv2).
    pose proof Hinv3 as Hd3.
    destruct Hd3 as (Hsp3 & Hs03 & Hs23 & Hs33 & Hs43 & Hs53 & Hs63 & Hs73
                     & Hs83 & Hfr3).
    assert (Ha23 : m3 !!! Regidx a2_idx = mword_of_int (bv_unsigned c1)).
    { rewrite (upd_eq m2 (Regidx a2_idx) (regval_into_reg _)).
      exact (zext8_moi c1). }
    assert (Ha53 : m3 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha52.
      exact (upd_ne m2 (Regidx a2_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha43 : m3 !!! Regidx a4_idx = mword_of_int (Z.of_nat i)).
    { rewrite <- Ha42.
      exact (upd_ne m2 (Regidx a2_idx) (Regidx a4_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0xe58  beqz a2,0x1028 -- NOT taken: c1 is not the terminator ---- *)
    assert (Hn57e : false = uv_btaken BEQ (m3 !!! Regidx a2_idx) zero_reg).
    { rewrite Ha23. cbn [uv_btaken].
      rewrite (moi_eq_zero (bv_unsigned c1) ltac:(unfold Z64; lia)).
      destruct (Z.eqb_spec (bv_unsigned c1) 0) as [He | _];
        [ exfalso; exact (Hc1z He) | reflexivity ]. }
    iApply (wp_uk_btype0 γt γd γs γfd h5 m3 (mword_of_int 0xe58)
              (mword_of_int 464 : mword 13) a2_idx BEQ false
              (add_vec (mword_of_int 0xe58 : mword 64)
                 (sign_extend' 64 (mword_of_int 464 : mword 13)))
              (4 + n) Hn57e eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shk_e58 with "Hcode"). }
    assert (E57e : add_vec_int (mword_of_int 0xe58 : mword 64) 4
                   = mword_of_int 0xe5c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E57e.
    iIntros (h6) "Hrun".
    (* ---- 0xe5c  beq a5,s8,0xe8a -- NOT taken: 's' is not 'd' ---- *)
    assert (Hn582 : false
                    = uv_btaken BEQ (m3 !!! Regidx a5_idx) (m3 !!! Regidx s8_idx))
      by (rewrite Ha53 Hs83; vm_compute; reflexivity).
    iApply (wp_uk_btype γt γd γs γfd h6 m3 (mword_of_int 0xe5c)
              (mword_of_int 46 : mword 13) s8_idx a5_idx BEQ false
              (add_vec (mword_of_int 0xe5c : mword 64)
                 (sign_extend' 64 (mword_of_int 46 : mword 13)))
              (4 + n) Hn582 eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shk_e5c with "Hcode"). }
    assert (E582 : add_vec_int (mword_of_int 0xe5c : mword 64) 4
                   = mword_of_int 0xe60)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E582.
    iIntros (h7) "Hrun".
    (* ---- 0xe60  addi a3,a5,-108 ; 0xe64  seqz a3,a3 -- a3 is dead ---- *)
    iApply (wp_uk_addi γt γd γs γfd h7 m3 (mword_of_int 0xe60)
              (mword_of_int 3988 : mword 12) a5_idx a3_idx
              (add_vec (m3 !!! Regidx a5_idx)
                 (sign_extend' 64 (mword_of_int 3988 : mword 12))) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_e60 with "Hcode"). }
    assert (E586 : add_vec_int (mword_of_int 0xe60 : mword 64) 4
                   = mword_of_int 0xe64)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E586.
    iIntros (h8) "Hrun".
    set (m4 := <[Regidx a3_idx
                 := regval_into_reg
                      (add_vec (m3 !!! Regidx a5_idx)
                         (sign_extend' 64
                            (mword_of_int 3988 : mword 12)))]> m3).
    assert (Hinv4 : vp_inv3 m0 m4 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m3 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a3_idx _
                  ltac:(vm_compute; reflexivity) Hinv3).
    iApply (wp_uk_sltiu γt γd γs γfd h8 m4 (mword_of_int 0xe64)
              (mword_of_int 1 : mword 12) a3_idx a3_idx
              (zero_extend' 64
                 (bool_to_bit
                    (zopz0zI_u (m4 !!! Regidx a3_idx)
                       (sign_extend' 64 (mword_of_int 1 : mword 12)))))
              (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_e64 with "Hcode"). }
    assert (E58a : add_vec_int (mword_of_int 0xe64 : mword 64) 4
                   = mword_of_int 0xe68)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E58a.
    iIntros (h9) "Hrun".
    set (m5 := <[Regidx a3_idx
                 := regval_into_reg
                      (zero_extend' 64
                         (bool_to_bit
                            (zopz0zI_u (m4 !!! Regidx a3_idx)
                               (sign_extend' 64
                                  (mword_of_int 1 : mword 12)))))]> m4).
    assert (Hinv5 : vp_inv3 m0 m5 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m4 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a3_idx _
                  ltac:(vm_compute; reflexivity) Hinv4).
    assert (Ha25 : m5 !!! Regidx a2_idx = mword_of_int (bv_unsigned c1)).
    { rewrite <- Ha23.
      rewrite /m5 (upd_ne m4 (Regidx a3_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m4 (upd_ne m3 (Regidx a3_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate)).
      reflexivity. }
    assert (Ha55 : m5 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha53.
      rewrite /m5 (upd_ne m4 (Regidx a3_idx) (Regidx a5_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m4 (upd_ne m3 (Regidx a3_idx) (Regidx a5_idx) _
                     ltac:(vm_compute; discriminate)).
      reflexivity. }
    assert (Ha45 : m5 !!! Regidx a4_idx = mword_of_int (Z.of_nat i)).
    { rewrite <- Ha43.
      rewrite /m5 (upd_ne m4 (Regidx a3_idx) (Regidx a4_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m4 (upd_ne m3 (Regidx a3_idx) (Regidx a4_idx) _
                     ltac:(vm_compute; discriminate)).
      reflexivity. }
    (* ---- 0xe68  addi a1,a2,-100 ---- *)
    assert (Ea1 : add_vec (m5 !!! Regidx a2_idx)
                    (sign_extend' 64 (mword_of_int 3996 : mword 12))
                  = mword_of_int (bv_unsigned c1 - 100))
      by (rewrite Ha25 Em100 moi_add; reflexivity).
    iApply (wp_uk_addi γt γd γs γfd h9 m5 (mword_of_int 0xe68)
              (mword_of_int 3996 : mword 12) a2_idx a1_idx
              (mword_of_int (bv_unsigned c1 - 100)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ea1))
              with "[] Hrun").
    { iApply (uis_shk_e68 with "Hcode"). }
    assert (E58e : add_vec_int (mword_of_int 0xe68 : mword 64) 4
                   = mword_of_int 0xe6c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E58e.
    iIntros (h10) "Hrun".
    set (m6 := <[Regidx a1_idx
                 := regval_into_reg
                      (mword_of_int (bv_unsigned c1 - 100) : mword 64)]> m5).
    assert (Hinv6 : vp_inv3 m0 m6 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m5 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a1_idx _
                  ltac:(vm_compute; reflexivity) Hinv5).
    assert (Ha16 : m6 !!! Regidx a1_idx = mword_of_int (bv_unsigned c1 - 100))
      by exact (upd_eq m5 (Regidx a1_idx) (regval_into_reg _)).
    assert (Ha26 : m6 !!! Regidx a2_idx = mword_of_int (bv_unsigned c1)).
    { rewrite <- Ha25.
      exact (upd_ne m5 (Regidx a1_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha56 : m6 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha55.
      exact (upd_ne m5 (Regidx a1_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha46 : m6 !!! Regidx a4_idx = mword_of_int (Z.of_nat i)).
    { rewrite <- Ha45.
      exact (upd_ne m5 (Regidx a1_idx) (Regidx a4_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0xe6c  c.bnez a1,0xea2 -- TAKEN: c1 is not 'd' ---- *)
    assert (Ht592 : true = neq_vec (m6 !!! Regidx a1_idx) zero_reg)
      by (rewrite Ha16;
          exact (eq_sym (moi_sub_ne_zero (bv_unsigned c1) 100 Hr1
                           ltac:(lia) Hc1d))).
    assert (Etgt5c8 : add_vec (mword_of_int 0xe6c : mword 64)
                        (sign_extend' 64
                           (sign_extend' 13
                              (concat_vec (mword_of_int 27 : mword 8) ('b"0"))))
                      = mword_of_int 0xea2)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cbnez γt γd γs γfd h10 m6 (mword_of_int 0xe6c)
              (mword_of_int 27 : mword 8) (mword_of_int 3 : mword 3) a1_idx
              true (mword_of_int 0xea2) (4 + n)
              ltac:(vm_compute; reflexivity) Ht592 (eq_sym Etgt5c8)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_e6c with "Hcode"). }
    iIntros (h11) "Hrun".
    (* ---- 0xea2  c.add a4,a4,s4 -- &fmt[i] again ---- *)
    assert (Ea4c : add_vec (m6 !!! Regidx a4_idx) (m6 !!! Regidx s4_idx)
                   = mword_of_int (a + Z.of_nat i)).
    { rewrite Ha46.
      rewrite /m6 (upd_ne m5 (Regidx a1_idx) (Regidx s4_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m5 (upd_ne m4 (Regidx a3_idx) (Regidx s4_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m4 (upd_ne m3 (Regidx a3_idx) (Regidx s4_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite Hs43 moi_add. f_equal; lia. }
    iApply (wp_uk_cadd γt γd γs γfd h11 m6 (mword_of_int 0xea2) a4_idx s4_idx
              (mword_of_int (a + Z.of_nat i)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ea4c))
              with "[] Hrun").
    { iApply (uis_shk_ea2 with "Hcode"). }
    assert (E5c8 : add_vec_int (mword_of_int 0xea2 : mword 64) 2
                   = mword_of_int 0xea4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E5c8.
    iIntros (h12) "Hrun".
    set (m7 := <[Regidx a4_idx
                 := regval_into_reg
                      (mword_of_int (a + Z.of_nat i) : mword 64)]> m6).
    assert (Hinv7 : vp_inv3 m0 m7 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m6 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a4_idx _
                  ltac:(vm_compute; reflexivity) Hinv6).
    assert (Ha47 : m7 !!! Regidx a4_idx = mword_of_int (a + Z.of_nat i))
      by exact (upd_eq m6 (Regidx a4_idx) (regval_into_reg _)).
    assert (Ha27 : m7 !!! Regidx a2_idx = mword_of_int (bv_unsigned c1)).
    { rewrite <- Ha26.
      exact (upd_ne m6 (Regidx a4_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha57 : m7 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha56.
      exact (upd_ne m6 (Regidx a4_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0xea4  lbu a1,2(a4) -- c2 = fmt[i+2] ---- *)
    assert (Haddr2 : (a + Z.of_nat (S (S i)))%Z
                     = uint (m7 !!! Regidx a4_idx)
                       + uoff_i12 (mword_of_int 2 : mword 12)).
    { rewrite Ha47 (uint_moi (a + Z.of_nat i) Hai).
      replace (uoff_i12 (mword_of_int 2 : mword 12)) with 2
        by (vm_compute; reflexivity).
      lia. }
    iApply (wp_uk_lbu_text γt γd γs γfd h12 m7 (mword_of_int 0xea4)
              (mword_of_int 2 : mword 12) a4_idx a1_idx
              (a + Z.of_nat (S (S i))) c2 (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              Haddr2 ltac:(vm_compute; discriminate)
              with "[] Hc2 Hrun").
    { iApply (uis_shk_ea4 with "Hcode"). }
    assert (E5ca : add_vec_int (mword_of_int 0xea4 : mword 64) 4
                   = mword_of_int 0xea8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E5ca.
    iIntros (h13) "Hrun".
    set (m8 := <[Regidx a1_idx
                 := regval_into_reg (zero_extend' 64 c2 : mword 64)]> m7).
    assert (Hinv8 : vp_inv3 m0 m8 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m7 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a1_idx _
                  ltac:(vm_compute; reflexivity) Hinv7).
    assert (Ha18 : m8 !!! Regidx a1_idx = mword_of_int (bv_unsigned c2)).
    { rewrite (upd_eq m7 (Regidx a1_idx) (regval_into_reg _)).
      exact (zext8_moi c2). }
    assert (Ha28 : m8 !!! Regidx a2_idx = mword_of_int (bv_unsigned c1)).
    { rewrite <- Ha27.
      exact (upd_ne m7 (Regidx a1_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha58 : m8 !!! Regidx a5_idx = mword_of_int 115).
    { rewrite <- Ha57.
      exact (upd_ne m7 (Regidx a1_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0xea8  addi a4,a2,-108 ; 0xeac  seqz a4,a4 ; 0xeb0  and a4,a4,a3
           -- a4 is dead on this path, so its value is left as written ---- *)
    iApply (wp_uk_addi γt γd γs γfd h13 m8 (mword_of_int 0xea8)
              (mword_of_int 3988 : mword 12) a2_idx a4_idx
              (add_vec (m8 !!! Regidx a2_idx)
                 (sign_extend' 64 (mword_of_int 3988 : mword 12))) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_ea8 with "Hcode"). }
    assert (E5ce : add_vec_int (mword_of_int 0xea8 : mword 64) 4
                   = mword_of_int 0xeac)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E5ce.
    iIntros (h14) "Hrun".
    set (m9 := <[Regidx a4_idx
                 := regval_into_reg
                      (add_vec (m8 !!! Regidx a2_idx)
                         (sign_extend' 64
                            (mword_of_int 3988 : mword 12)))]> m8).
    assert (Hinv9 : vp_inv3 m0 m9 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m8 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a4_idx _
                  ltac:(vm_compute; reflexivity) Hinv8).
    iApply (wp_uk_sltiu γt γd γs γfd h14 m9 (mword_of_int 0xeac)
              (mword_of_int 1 : mword 12) a4_idx a4_idx
              (zero_extend' 64
                 (bool_to_bit
                    (zopz0zI_u (m9 !!! Regidx a4_idx)
                       (sign_extend' 64 (mword_of_int 1 : mword 12)))))
              (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_eac with "Hcode"). }
    assert (E5d2 : add_vec_int (mword_of_int 0xeac : mword 64) 4
                   = mword_of_int 0xeb0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E5d2.
    iIntros (h15) "Hrun".
    set (m10 := <[Regidx a4_idx
                  := regval_into_reg
                       (zero_extend' 64
                          (bool_to_bit
                             (zopz0zI_u (m9 !!! Regidx a4_idx)
                                (sign_extend' 64
                                   (mword_of_int 1 : mword 12)))))]> m9).
    assert (Hinv10 : vp_inv3 m0 m10 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m9 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a4_idx _
                  ltac:(vm_compute; reflexivity) Hinv9).
    iApply (wp_uk_cand γt γd γs γfd h15 m10 (mword_of_int 0xeb0)
              (mword_of_int 6 : mword 3) (mword_of_int 5 : mword 3)
              a4_idx a3_idx
              (and_vec (m10 !!! Regidx a4_idx) (m10 !!! Regidx a3_idx)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_eb0 with "Hcode"). }
    assert (E5d6 : add_vec_int (mword_of_int 0xeb0 : mword 64) 2
                   = mword_of_int 0xeb2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E5d6.
    iIntros (h16) "Hrun".
    set (m11 := <[Regidx a4_idx
                  := regval_into_reg
                       (and_vec (m10 !!! Regidx a4_idx)
                          (m10 !!! Regidx a3_idx))]> m10).
    assert (Hinv11 : vp_inv3 m0 m11 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m10 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a4_idx _
                  ltac:(vm_compute; reflexivity) Hinv10).
    assert (Hkeep : forall r : mword 5,
               Regidx r <> Regidx a4_idx -> Regidx r <> Regidx a1_idx ->
               m11 !!! Regidx r = m8 !!! Regidx r).
    { intros r Hr4 Hrx.
      rewrite /m11 (upd_ne m10 (Regidx a4_idx) (Regidx r) _
                      Hr4).
      rewrite /m10 (upd_ne m9 (Regidx a4_idx) (Regidx r) _
                      Hr4).
      rewrite /m9 (upd_ne m8 (Regidx a4_idx) (Regidx r) _
                      Hr4).
      reflexivity. }
    assert (Ha1_11 : m11 !!! Regidx a1_idx = mword_of_int (bv_unsigned c2)).
    { rewrite /m11 (upd_ne m10 (Regidx a4_idx) (Regidx a1_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /m10 (upd_ne m9 (Regidx a4_idx) (Regidx a1_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /m9 (upd_ne m8 (Regidx a4_idx) (Regidx a1_idx) _
                      ltac:(vm_compute; discriminate)).
      exact Ha18. }
    assert (Ha2_11 : m11 !!! Regidx a2_idx = mword_of_int (bv_unsigned c1))
      by (rewrite (Hkeep a2_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Ha28).
    assert (Ha5_11 : m11 !!! Regidx a5_idx = mword_of_int 115)
      by (rewrite (Hkeep a5_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Ha58).
    (* ---- 0xeb2  addi a0,a1,-100 ---- *)
    assert (Ea0d : add_vec (m11 !!! Regidx a1_idx)
                     (sign_extend' 64 (mword_of_int 3996 : mword 12))
                   = mword_of_int (bv_unsigned c2 - 100))
      by (rewrite Ha1_11 Em100 moi_add; reflexivity).
    iApply (wp_uk_addi γt γd γs γfd h16 m11 (mword_of_int 0xeb2)
              (mword_of_int 3996 : mword 12) a1_idx a0_idx
              (mword_of_int (bv_unsigned c2 - 100)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ea0d))
              with "[] Hrun").
    { iApply (uis_shk_eb2 with "Hcode"). }
    assert (E5d8 : add_vec_int (mword_of_int 0xeb2 : mword 64) 4
                   = mword_of_int 0xeb6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E5d8.
    iIntros (h17) "Hrun".
    set (m12 := <[Regidx a0_idx
                  := regval_into_reg
                       (mword_of_int (bv_unsigned c2 - 100) : mword 64)]> m11).
    assert (Hinv12 : vp_inv3 m0 m12 sp0 a fd (mword_of_int apz) (mword_of_int 37) i)
      by exact (vp_inv3_upd m0 m11 sp0 a fd (mword_of_int apz) (mword_of_int 37) i a0_idx _
                  ltac:(vm_compute; reflexivity) Hinv11).
    assert (Ha0_12 : m12 !!! Regidx a0_idx
                     = mword_of_int (bv_unsigned c2 - 100))
      by exact (upd_eq m11 (Regidx a0_idx) (regval_into_reg _)).
    (* ---- 0xeb6  bnez a0,0x103c -- TAKEN: c2 is not 'd' ---- *)
    assert (Ht5dc : true = uv_btaken BNE (m12 !!! Regidx a0_idx) zero_reg).
    { rewrite Ha0_12. cbn [uv_btaken].
      exact (eq_sym (moi_sub_ne_zero (bv_unsigned c2) 100 Hr2
                       ltac:(lia) Hc2d)). }
    assert (Etgt762 : add_vec (mword_of_int 0xeb6 : mword 64)
                        (sign_extend' 64 (mword_of_int 390 : mword 13))
                      = mword_of_int 0x103c)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_btype0 γt γd γs γfd h17 m12 (mword_of_int 0xeb6)
              (mword_of_int 390 : mword 13) a0_idx BNE true
              (mword_of_int 0x103c) (4 + n) Ht5dc (eq_sym Etgt762)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_eb6 with "Hcode"). }
    iIntros (h18) "Hrun".
    iApply (wp_kshd_vprintf_pcs2 m0 sp0 fd a i apz sa dq c1 c2 slen sf
              m12 h18 n Ha0 Habnd Hap0 Haphi Hapal Hsanz Hr1 Hr2
              Hc1u Hc1x Hc2u Hc2x Hinv12
              ltac:(rewrite /m12 (upd_ne m11 (Regidx a0_idx) (Regidx a1_idx) _
                                   ltac:(vm_compute; discriminate)); exact Ha1_11)
              ltac:(rewrite /m12 (upd_ne m11 (Regidx a0_idx) (Regidx a2_idx) _
                                   ltac:(vm_compute; discriminate)); exact Ha2_11)
              ltac:(rewrite /m12 (upd_ne m11 (Regidx a0_idx) (Regidx a5_idx) _
                                   ltac:(vm_compute; discriminate)); exact Ha5_11)
              with "Hcode Hc1 Hw Hstr Hrun Hcont").
  Qed.

  (* ===================================================================== *)
  (* vprintf(fd, fmt, ap) FOR A FORMAT WITH ONE '%s' IN IT.                 *)
  (*                                                                        *)
  (* All three of sh's formats are of this shape -- a prefix with no '%'    *)
  (* at all, the directive, and at least one character after it ('\n' for   *)
  (* panic's, " failed\n" for the other two).  The walk is [pro], then      *)
  (* [seg] to the '%', then the two rounds the directive takes, then        *)
  (* [loop] for what is left.                                               *)
  (* ===================================================================== *)
  Lemma wp_kshd_vprintf_s (a : Z) (len q : nat) (f : nat -> mword 8)
      (apz sa : Z) (dq : dfrac) (slen : nat) (sf : nat -> bv 8)
      (h : CpuId) (m : regfile) (n : nat) :
    0 <= a -> a + Z.of_nat len + 2 < 2 ^ 31 ->
    (S (S q) < len)%nat ->
    bv_unsigned (f q) = 37 ->
    bv_unsigned (f (S q)) = 115 ->
    (forall j : nat, (j < len)%nat -> j <> q -> bv_unsigned (f j) <> 37) ->
    bv_unsigned (f (S (S q))) <> 100 ->
    bv_unsigned (f (S (S q))) <> 117 ->
    bv_unsigned (f (S (S q))) <> 120 ->
    ((S (S (S q)) < len)%nat ->
       bv_unsigned (f (S (S (S q)))) <> 100 /\
       bv_unsigned (f (S (S (S q)))) <> 117 /\
       bv_unsigned (f (S (S (S q)))) <> 120) ->
    apz mod 8 = 0 ->
    sa <> 0 ->
    m !!! Regidx a1_idx = mword_of_int a ->
    m !!! Regidx a2_idx = mword_of_int apz ->
    shk_code γt -∗
    utext_str γt a len f -∗
    uwordq γd dq apz (mword_of_int sa) -∗
    shd_str γt γd tx sa slen sf -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.vprintf) (12 + (4 + n)) -∗
    (∀ (h' : CpuId) (m' : regfile),
       uwordq γd dq apz (mword_of_int sa) -∗
       ⌜ ucallee_saved m m' ⌝ -∗
       urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (12 + (4 + n)) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd Hq2 Hfq Hfsq Hpct Hc1d Hc1u Hc1x Hc2set Hapal Hsanz Ha1 Ha2.
    iIntros "#Hcode #Hstr Hw #Hsstr Hrun Hcont".
    iDestruct (urun_uword_bnd with "Hrun Hw") as %[Hap0 Haphi].
    iDestruct (utext_str_nonul with "Hstr") as %Hnn.
    (* the byte two past the directive: a body byte if there is one, and
       otherwise the terminator, whose value clears every test by itself *)
    iAssert (∃ c2 : mword 8,
               utext γt (a + Z.of_nat (S (S (S q)))) c2
               ∗ ⌜ bv_unsigned c2 <> 100 ⌝ ∗ ⌜ bv_unsigned c2 <> 117 ⌝
               ∗ ⌜ bv_unsigned c2 <> 120 ⌝)%I as "#Hc2".
    { destruct (Nat.lt_ge_cases (S (S (S q))) len) as [Hlt | Hge].
      - iDestruct (utext_str_byte γt a len f (S (S (S q))) Hlt with "Hstr")
          as "#Hb".
        destruct (Hc2set Hlt) as (Hd & Hu & Hx).
        iExists (f (S (S (S q)))). iFrame "Hb". iPureIntro. done.
      - assert (Heq : (S (S (S q)))%nat = len) by lia.
        iDestruct (utext_str_nul with "Hstr") as "#Hnul".
        iExists (ubyte0 : mword 8). rewrite Heq. iFrame "Hnul".
        iPureIntro. repeat split; vm_compute; discriminate. }
    iDestruct "Hc2" as (c2) "(#Hc2b & %Hc2d & %Hc2u & %Hc2x)".
    (* ---- the prologue ---- *)
    iApply (wp_kshd_vprintf_pro γt γd γs γfd a len f h m n Ha0 Habnd ltac:(lia) Ha1
              with "Hcode Hstr Hrun").
    iIntros (h0 mA fd ap) "%Hal8 %Hlo %Hinv0 %Hs1z %Hapeq
                           Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10
                           Hw11 Hw12 Hrun".
    assert (Hapz : ap = mword_of_int apz) by (rewrite Hapeq; exact Ha2).
    rewrite Hapz in Hinv0.
    (* ---- the prefix, up to the '%' ---- *)
    iApply (wp_kshd_vprintf_seg m (m !!! Regidx csp_rs1) fd
              (mword_of_int apz) a len f q Ha0 Habnd 0%nat h0 mA n
              ltac:(lia) ltac:(intros j Hj; apply Hpct; lia) Hinv0 Hs1z
              with "Hcode Hstr Hrun
                    [Hw Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12
                     Hcont]").
    iIntros (h1 mB) "%HinvB %Hs1B Hrun".
    rewrite Nat.add_0_l in HinvB, Hs1B.
    (* ---- the '%' round ---- *)
    iDestruct (utext_str_byte γt a len f (S q) ltac:(lia) with "Hstr")
      as "#Hbsq".
    iApply (wp_kshd_vprintf_pct m (m !!! Regidx csp_rs1) fd
              (mword_of_int apz) a q (f (S q)) h1 mB n Ha0 ltac:(lia) HinvB
              ltac:(rewrite Hs1B Hfq; reflexivity)
              with "Hcode Hbsq Hrun
                    [Hw Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12
                     Hcont]").
    iIntros (h2 mC) "%HinvC %Hs1C %Ha4C Hrun".
    (* ---- 0xe3c, not taken: 's' is not the terminator ---- *)
    assert (Hnt1 : false = uv_btaken BEQ (mC !!! Regidx s1_idx) zero_reg).
    { rewrite Hs1C Hfsq. cbn [uv_btaken].
      rewrite (moi_eq_zero 115 ltac:(unfold Z64; lia)). reflexivity. }
    iApply (wp_uk_btype0 γt γd γs γfd h2 mC (mword_of_int 0xe3c)
              (mword_of_int 468 : mword 13) s1_idx BEQ false
              (add_vec (mword_of_int 0xe3c : mword 64)
                 (sign_extend' 64 (mword_of_int 468 : mword 13)))
              (4 + n) Hnt1 eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shk_e3c with "Hcode"). }
    assert (E562 : add_vec_int (mword_of_int 0xe3c : mword 64) 4
                   = mword_of_int 0xe40)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E562.
    iIntros (h3) "Hrun".
    (* ---- the directive's round ---- *)
    iDestruct (utext_str_byte γt a len f (S (S q)) ltac:(lia) with "Hstr")
      as "#Hbssq".
    iApply (wp_kshd_vprintf_pcs m (m !!! Regidx csp_rs1) fd a (S q) apz sa dq
              (f (S (S q))) c2 slen sf h3 mC n Ha0 ltac:(lia) Hap0 Haphi Hapal
              Hsanz
              ltac:(intro He; apply (Hnn (S (S q)) ltac:(lia)); apply bv_eq;
                    rewrite He; vm_compute; reflexivity)
              Hc1d Hc1u Hc1x Hc2d Hc2u Hc2x HinvC
              ltac:(rewrite Hs1C Hfsq; reflexivity) Ha4C
              with "Hcode Hbssq Hc2b Hw Hsstr Hrun
                    [Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12
                     Hcont]").
    iIntros (h4 mD) "Hw %HinvD %Hs1D Hrun".
    (* ---- 0xe3c, not taken again: there IS a character after the "%s" ---- *)
    assert (Hnzc1 : bv_unsigned (f (S (S q))) <> 0).
    { intro He. apply (Hnn (S (S q)) ltac:(lia)). apply bv_eq.
      rewrite He. vm_compute. reflexivity. }
    assert (Hrc1 : 0 <= bv_unsigned (f (S (S q))) < Z64).
    { assert (HH : 0 <= bv_unsigned (f (S (S q))) < 256).
      { pose proof (bv_unsigned_in_range 8 (f (S (S q)))) as H0.
        assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
        rewrite Em8 in H0. exact H0. }
      unfold Z64. lia. }
    assert (Hnt2 : false = uv_btaken BEQ (mD !!! Regidx s1_idx) zero_reg).
    { rewrite Hs1D. cbn [uv_btaken].
      rewrite (moi_eq_zero (bv_unsigned (f (S (S q)))) Hrc1).
      destruct (Z.eqb_spec (bv_unsigned (f (S (S q)))) 0) as [He | _];
        [ exfalso; exact (Hnzc1 He) | reflexivity ]. }
    iApply (wp_uk_btype0 γt γd γs γfd h4 mD (mword_of_int 0xe3c)
              (mword_of_int 468 : mword 13) s1_idx BEQ false
              (add_vec (mword_of_int 0xe3c : mword 64)
                 (sign_extend' 64 (mword_of_int 468 : mword 13)))
              (4 + n) Hnt2 eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shk_e3c with "Hcode"). }
    rewrite E562.
    iIntros (h5) "Hrun".
    (* ---- and the rest of the string, which has no '%' left in it ---- *)
    iApply (wp_kshd_vprintf_loop γt γd γs γfd m (m !!! Regidx csp_rs1) fd
              (mword_of_int (apz + 8)) a len f (S (S q))
              (len - S (S (S q)))%nat Ha0 Habnd
              ltac:(intros j Hj; apply Hpct; lia) eq_refl Hal8 Hlo
              (S (S q)) h5 mD n ltac:(lia) ltac:(lia) HinvD Hs1D
              with "Hcode Hstr Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10
                    Hw11 Hw12 Hrun [Hw Hcont]").
    iIntros (h6 mE) "%Hcs Hrun".
    iApply ("Hcont" $! h6 mE with "Hw [] Hrun"). iPureIntro. exact Hcs.
  Qed.

End UkShDiagVprintfS.

(* ===================================================================== *)
(* UkShDiagFprintf.v -- ulib's [fprintf(fd, fmt, ...)], for a format string   *)
(* with no '%'.                                                            *)
(*                                                                        *)
(* fprintf is printf without the two moves: (fd, fmt) are ALREADY a0 and   *)
(* a1 on entry, so it only marshals the varargs it will not read and tail- *)
(* calls vprintf.  Its frame is ten words, not printf's twelve, and s0     *)
(* sits at sp0-48 rather than sp0-64 -- the spill area is [0(s0)]..        *)
(* [40(s0)] and the va_list is parked at [-24(s0)].                        *)
(* ===================================================================== *)

Section UkShDiagFprintf.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context (γt γd γs γfd : gname).

  (* WHICH HALF OF THE HEAP THE '%s' ARGUMENT LIVES IN.  cat's is a heap
     string ([ustr] at γd); sh's [panic] prints a .rodata literal
     ([utext_str] at γt).  The walk reads it in exactly one way -- one byte
     at a time at a known index -- so the two are ONE proof over this
     boolean; see UkShDiag.v §0a. *)
  Context (tx : bool).

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation s7_idx := (mword_of_int 23 : mword 5).
  Local Notation s8_idx := (mword_of_int 24 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).

  Lemma wp_kshd_fprintf_epi0 (h : CpuId) (m : regfile)
      (sp0 vra vs0 vs1 : mword 64) (n : nat) :
    m !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 12)) ->
    uint sp0 mod 8 = 0 ->
    96 <= uint sp0 ->
    shk_code γt -∗
    uword γd (uint sp0 - 8) vra -∗
    uword γd (uint sp0 - 16) vs0 -∗
    uword γd (uint sp0 - 24) vs1 -∗
    (∃ w : mword 64, uword γd (uint sp0 - 32) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 40) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 48) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 56) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 64) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 72) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 80) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 88) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 96) w) -∗
    urun γt γd γs γfd h m (mword_of_int 0x101e) n -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ m' !!! Regidx csp_rs1 = sp0 ⌝ -∗
       ⌜ m' !!! Regidx s0_idx = vs0 ⌝ -∗
       ⌜ m' !!! Regidx s1_idx = vs1 ⌝ -∗
       ⌜ forall r : mword 5,
           Regidx r <> Regidx csp_rs1 -> Regidx r <> Regidx s0_idx ->
           Regidx r <> Regidx s1_idx -> Regidx r <> Regidx ra_idx ->
           m' !!! Regidx r = m !!! Regidx r ⌝ -∗
       urun γt γd γs γfd h' m' (ret_pc vra) (12 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hsp Hal8 Hlo. iIntros "#Hcode Hwra Hws0 Hws1 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hrun Hcont".
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                   = bv_unsigned sp0 - 96).
    { replace (- (8 * Z.of_nat 12)) with (-96) by lia.
      exact (uv_avi_neg sp0 96 ltac:(apply Z.leb_le; reflexivity)
               ltac:(rewrite <- uint_unsigned; exact Hlo)). }
    assert (Hsp96 : uint (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                    = uint sp0 - 96)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (HR : 0 <= bv_unsigned sp0 < 18446744073709551616).
    { pose proof (bv_unsigned_in_range 64 sp0) as H0.
      assert (Em : bv_modulus 64 = 18446744073709551616)
        by (vm_compute; reflexivity).
      rewrite Em in H0. exact H0. }
    assert (Hd12 : (0 <= 8 * Z.of_nat 12)%Z) by (apply Z.leb_le; reflexivity).
    assert (Hlt12 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                    + 8 * Z.of_nat 12 < Z64)
      by (clear -Hbsp HR; rewrite Hbsp; unfold Z64; lia).
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                    (8 * Z.of_nat 12) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                 (8 * Z.of_nat 12) Hd12 Hlt12).
      clear -Hbsp. rewrite Hbsp. lia. }
    assert (Ho88 : uoff_sdsp (mword_of_int 11 : mword 6) = 88)
      by (vm_compute; reflexivity).
    assert (Ho80 : uoff_sdsp (mword_of_int 10 : mword 6) = 80)
      by (vm_compute; reflexivity).
    assert (Ho72 : uoff_sdsp (mword_of_int 9 : mword 6) = 72)
      by (vm_compute; reflexivity).
    (* ---- 0x101e  c.ldsp ra,88(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h m (mword_of_int 0x101e)
              (mword_of_int 11 : mword 6) ra_idx (uint sp0 - 8) vra n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp Hsp96 Ho88; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hwra Hrun").
    { iApply (uis_shk_101e with "Hcode"). }
    iIntros "Hwra".
    assert (E70a : add_vec_int (mword_of_int 0x101e : mword 64) 2
                 = mword_of_int 0x1020)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E70a.
    iIntros (h1) "Hrun".
    set (mm1 := <[Regidx ra_idx := regval_into_reg vra]> m).
    assert (Hsp1 : mm1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp.
      exact (upd_ne m (Regidx ra_idx) (Regidx csp_rs1) (regval_into_reg vra)
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x1020  c.ldsp s0,80(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h1 mm1 (mword_of_int 0x1020)
              (mword_of_int 10 : mword 6) s0_idx (uint sp0 - 16) vs0 n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp1 Hsp96 Ho80; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hws0 Hrun").
    { iApply (uis_shk_1020 with "Hcode"). }
    iIntros "Hws0".
    assert (E70c : add_vec_int (mword_of_int 0x1020 : mword 64) 2
                 = mword_of_int 0x1022)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E70c.
    iIntros (h2) "Hrun".
    set (mm2 := <[Regidx s0_idx := regval_into_reg vs0]> mm1).
    assert (Hsp2 : mm2 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp1.
      exact (upd_ne mm1 (Regidx s0_idx) (Regidx csp_rs1) (regval_into_reg vs0)
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x1022  c.ldsp s1,72(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h2 mm2 (mword_of_int 0x1022)
              (mword_of_int 9 : mword 6) s1_idx (uint sp0 - 24) vs1 n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp2 Hsp96 Ho72; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hws1 Hrun").
    { iApply (uis_shk_1022 with "Hcode"). }
    iIntros "Hws1".
    assert (E70e : add_vec_int (mword_of_int 0x1022 : mword 64) 2
                 = mword_of_int 0x1024)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E70e.
    iIntros (h3) "Hrun".
    set (mm3 := <[Regidx s1_idx := regval_into_reg vs1]> mm2).
    assert (Hsp3 : mm3 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp2.
      exact (upd_ne mm2 (Regidx s1_idx) (Regidx csp_rs1) (regval_into_reg vs1)
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x1024  c.addi16sp sp,sp,96 -- THE POP ---- *)
    iApply (wp_uk_caddi16sp_up γt γd γs γfd h3 mm3 (mword_of_int 0x1024)
              (mword_of_int 6 : mword 6) 12 n
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hwra Hws0 Hws1 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12] Hrun").
    { iApply (uis_shk_1024 with "Hcode"). }
    { rewrite Hsp3 Hup.
      iApply (ustack_12_close γd sp0 Hal8
                with "[Hwra] [Hws0] [Hws1] Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12").
      { iExists vra. iExact "Hwra". }
      { iExists vs0. iExact "Hws0". }
      { iExists vs1. iExact "Hws1". } }
    assert (E710 : add_vec_int (mword_of_int 0x1024 : mword 64) 2
                   = mword_of_int 0x1026)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp3 Hup E710.
    iIntros (h4) "Hrun".
    set (mm4 := <[Regidx csp_rs1 := regval_into_reg sp0]> mm3).
    assert (Hra4 : mm4 !!! Regidx ra_idx = vra).
    { rewrite /mm4 (upd_ne mm3 (Regidx csp_rs1) (Regidx ra_idx)
                     (regval_into_reg sp0) ltac:(vm_compute; discriminate)).
      rewrite /mm3 (upd_ne mm2 (Regidx s1_idx) (Regidx ra_idx)
                     (regval_into_reg vs1) ltac:(vm_compute; discriminate)).
      rewrite /mm2 (upd_ne mm1 (Regidx s0_idx) (Regidx ra_idx)
                     (regval_into_reg vs0) ltac:(vm_compute; discriminate)).
      rewrite /mm1. exact (upd_eq m (Regidx ra_idx) (regval_into_reg vra)). }
    (* ---- 0x1026  c.jr ra ---- *)
    iApply (wp_uk_cjr γt γd γs γfd h4 mm4 (mword_of_int 0x1026) ra_idx
              (ret_pc vra) (12 + n)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra4; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_1026 with "Hcode"). }
    iIntros (h5) "Hrun".
    iApply ("Hcont" $! h5 mm4 with "[] [] [] [] Hrun").
    { iPureIntro. rewrite /mm4.
      exact (upd_eq mm3 (Regidx csp_rs1) (regval_into_reg sp0)). }
    { iPureIntro.
      rewrite /mm4 (upd_ne mm3 (Regidx csp_rs1) (Regidx s0_idx)
                     (regval_into_reg sp0) ltac:(vm_compute; discriminate)).
      rewrite /mm3 (upd_ne mm2 (Regidx s1_idx) (Regidx s0_idx)
                     (regval_into_reg vs1) ltac:(vm_compute; discriminate)).
      rewrite /mm2. exact (upd_eq mm1 (Regidx s0_idx) (regval_into_reg vs0)). }
    { iPureIntro.
      rewrite /mm4 (upd_ne mm3 (Regidx csp_rs1) (Regidx s1_idx)
                     (regval_into_reg sp0) ltac:(vm_compute; discriminate)).
      rewrite /mm3. exact (upd_eq mm2 (Regidx s1_idx) (regval_into_reg vs1)). }
    { iPureIntro. intros r Hrsp Hrs0 Hrs1 Hrra.
      rewrite /mm4 (upd_ne mm3 (Regidx csp_rs1) (Regidx r)
                     (regval_into_reg sp0) Hrsp).
      rewrite /mm3 (upd_ne mm2 (Regidx s1_idx) (Regidx r)
                     (regval_into_reg vs1) Hrs1).
      rewrite /mm2 (upd_ne mm1 (Regidx s0_idx) (Regidx r)
                     (regval_into_reg vs0) Hrs0).
      rewrite /mm1. exact (upd_ne m (Regidx ra_idx) (Regidx r)
                             (regval_into_reg vra) Hrra). }
  Qed.





  (* --------------------------------------------------------------------- *)
  (* vprintf's FULL EPILOGUE @0x1010: restore s2..s8, then fall into the      *)
  (* shared tail.  This is where [ucallee_saved] is assembled, because this  *)
  (* is where every spilled register is back at its entry value: the ten     *)
  (* frame words are PINNED to [m0]'s registers in the statement, [sp0] is   *)
  (* [m0]'s sp, and [Hfree] covers the five callee-saved registers vprintf   *)
  (* never touches (gp, tp, s9, s10, s11).  [ucs_cases] says there is no      *)
  (* sixteenth.                                                              *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kshd_fprintf_epi (h : CpuId) (m m0 : regfile) (sp0 : mword 64)
      (n : nat) :
    m !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 12)) ->
    m0 !!! Regidx csp_rs1 = sp0 ->
    uint sp0 mod 8 = 0 ->
    96 <= uint sp0 ->
    (forall r : mword 5, ucallee_saved_idx r = true ->
       uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27) ->
       m !!! Regidx r = m0 !!! Regidx r) ->
    shk_code γt -∗
    uword γd (uint sp0 - 8) (m0 !!! Regidx ra_idx) -∗
    uword γd (uint sp0 - 16) (m0 !!! Regidx s0_idx) -∗
    uword γd (uint sp0 - 24) (m0 !!! Regidx s1_idx) -∗
    uword γd (uint sp0 - 32) (m0 !!! Regidx s2_idx) -∗
    uword γd (uint sp0 - 40) (m0 !!! Regidx s3_idx) -∗
    uword γd (uint sp0 - 48) (m0 !!! Regidx s4_idx) -∗
    uword γd (uint sp0 - 56) (m0 !!! Regidx s5_idx) -∗
    uword γd (uint sp0 - 64) (m0 !!! Regidx s6_idx) -∗
    uword γd (uint sp0 - 72) (m0 !!! Regidx s7_idx) -∗
    uword γd (uint sp0 - 80) (m0 !!! Regidx s8_idx) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 88) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 96) w) -∗
    urun γt γd γs γfd h m (mword_of_int 0x1010) n -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ ucallee_saved m0 m' ⌝ -∗
       urun γt γd γs γfd h' m' (ret_pc (m0 !!! Regidx ra_idx)) (12 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hsp Hsp0 Hal8 Hlo Hfree.
    iIntros "#Hcode Hwra Hws0 Hws1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw11 Hw12 Hrun Hcont".
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                   = bv_unsigned sp0 - 96).
    { replace (- (8 * Z.of_nat 12)) with (-96) by lia.
      exact (uv_avi_neg sp0 96 ltac:(apply Z.leb_le; reflexivity)
               ltac:(rewrite <- uint_unsigned; exact Hlo)). }
    assert (Hsp96 : uint (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                    = uint sp0 - 96)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Ho64 : uoff_sdsp (mword_of_int 8 : mword 6) = 64)
      by (vm_compute; reflexivity).
    assert (Ho56 : uoff_sdsp (mword_of_int 7 : mword 6) = 56)
      by (vm_compute; reflexivity).
    assert (Ho48 : uoff_sdsp (mword_of_int 6 : mword 6) = 48)
      by (vm_compute; reflexivity).
    assert (Ho40 : uoff_sdsp (mword_of_int 5 : mword 6) = 40)
      by (vm_compute; reflexivity).
    assert (Ho32 : uoff_sdsp (mword_of_int 4 : mword 6) = 32)
      by (vm_compute; reflexivity).
    assert (Ho24 : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
      by (vm_compute; reflexivity).
    assert (Ho16 : uoff_sdsp (mword_of_int 2 : mword 6) = 16)
      by (vm_compute; reflexivity).
    (* ---- 0x1010  c.ldsp s2,64(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h m (mword_of_int 0x1010)
              (mword_of_int 8 : mword 6) s2_idx (uint sp0 - 32)
              (m0 !!! Regidx s2_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp Hsp96 Ho64; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw2 Hrun").
    { iApply (uis_shk_1010 with "Hcode"). }
    iIntros "Hw2".
    assert (E6fc : add_vec_int (mword_of_int 0x1010 : mword 64) 2
                 = mword_of_int 0x1012)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E6fc.
    iIntros (h1) "Hrun".
    set (me1 := <[Regidx s2_idx := regval_into_reg (m0 !!! Regidx s2_idx)]> m).
    assert (Hsp1 : me1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp.
      exact (upd_ne m (Regidx s2_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s2_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x1012  c.ldsp s3,56(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h1 me1 (mword_of_int 0x1012)
              (mword_of_int 7 : mword 6) s3_idx (uint sp0 - 40)
              (m0 !!! Regidx s3_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp1 Hsp96 Ho56; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw3 Hrun").
    { iApply (uis_shk_1012 with "Hcode"). }
    iIntros "Hw3".
    assert (E6fe : add_vec_int (mword_of_int 0x1012 : mword 64) 2
                 = mword_of_int 0x1014)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E6fe.
    iIntros (h2) "Hrun".
    set (me2 := <[Regidx s3_idx := regval_into_reg (m0 !!! Regidx s3_idx)]> me1).
    assert (Hsp2 : me2 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp1.
      exact (upd_ne me1 (Regidx s3_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s3_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x1014  c.ldsp s4,48(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h2 me2 (mword_of_int 0x1014)
              (mword_of_int 6 : mword 6) s4_idx (uint sp0 - 48)
              (m0 !!! Regidx s4_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp2 Hsp96 Ho48; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw4 Hrun").
    { iApply (uis_shk_1014 with "Hcode"). }
    iIntros "Hw4".
    assert (E700 : add_vec_int (mword_of_int 0x1014 : mword 64) 2
                 = mword_of_int 0x1016)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E700.
    iIntros (h3) "Hrun".
    set (me3 := <[Regidx s4_idx := regval_into_reg (m0 !!! Regidx s4_idx)]> me2).
    assert (Hsp3 : me3 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp2.
      exact (upd_ne me2 (Regidx s4_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s4_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x1016  c.ldsp s5,40(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h3 me3 (mword_of_int 0x1016)
              (mword_of_int 5 : mword 6) s5_idx (uint sp0 - 56)
              (m0 !!! Regidx s5_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp3 Hsp96 Ho40; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw5 Hrun").
    { iApply (uis_shk_1016 with "Hcode"). }
    iIntros "Hw5".
    assert (E702 : add_vec_int (mword_of_int 0x1016 : mword 64) 2
                 = mword_of_int 0x1018)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E702.
    iIntros (h4) "Hrun".
    set (me4 := <[Regidx s5_idx := regval_into_reg (m0 !!! Regidx s5_idx)]> me3).
    assert (Hsp4 : me4 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp3.
      exact (upd_ne me3 (Regidx s5_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s5_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x1018  c.ldsp s6,32(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h4 me4 (mword_of_int 0x1018)
              (mword_of_int 4 : mword 6) s6_idx (uint sp0 - 64)
              (m0 !!! Regidx s6_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp4 Hsp96 Ho32; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw6 Hrun").
    { iApply (uis_shk_1018 with "Hcode"). }
    iIntros "Hw6".
    assert (E704 : add_vec_int (mword_of_int 0x1018 : mword 64) 2
                 = mword_of_int 0x101a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E704.
    iIntros (h5) "Hrun".
    set (me5 := <[Regidx s6_idx := regval_into_reg (m0 !!! Regidx s6_idx)]> me4).
    assert (Hsp5 : me5 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp4.
      exact (upd_ne me4 (Regidx s6_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s6_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x101a  c.ldsp s7,24(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h5 me5 (mword_of_int 0x101a)
              (mword_of_int 3 : mword 6) s7_idx (uint sp0 - 72)
              (m0 !!! Regidx s7_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp5 Hsp96 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw7 Hrun").
    { iApply (uis_shk_101a with "Hcode"). }
    iIntros "Hw7".
    assert (E706 : add_vec_int (mword_of_int 0x101a : mword 64) 2
                 = mword_of_int 0x101c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E706.
    iIntros (h6) "Hrun".
    set (me6 := <[Regidx s7_idx := regval_into_reg (m0 !!! Regidx s7_idx)]> me5).
    assert (Hsp6 : me6 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp5.
      exact (upd_ne me5 (Regidx s7_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s7_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x101c  c.ldsp s8,16(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h6 me6 (mword_of_int 0x101c)
              (mword_of_int 2 : mword 6) s8_idx (uint sp0 - 80)
              (m0 !!! Regidx s8_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp6 Hsp96 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw8 Hrun").
    { iApply (uis_shk_101c with "Hcode"). }
    iIntros "Hw8".
    assert (E708 : add_vec_int (mword_of_int 0x101c : mword 64) 2
                 = mword_of_int 0x101e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E708.
    iIntros (h7) "Hrun".
    set (me7 := <[Regidx s8_idx := regval_into_reg (m0 !!! Regidx s8_idx)]> me6).
    assert (Hsp7 : me7 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp6.
      exact (upd_ne me6 (Regidx s8_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s8_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x101e..0x1026: the shared tail ---- *)
    iApply (wp_kshd_fprintf_epi0 h7 me7 sp0 (m0 !!! Regidx ra_idx)
              (m0 !!! Regidx s0_idx) (m0 !!! Regidx s1_idx) n Hsp7 Hal8 Hlo
              with "Hcode Hwra Hws0 Hws1 [Hw2] [Hw3] [Hw4] [Hw5] [Hw6] [Hw7] [Hw8] Hw11 Hw12 Hrun").
    { iExists (m0 !!! Regidx s2_idx). iExact "Hw2". }
    { iExists (m0 !!! Regidx s3_idx). iExact "Hw3". }
    { iExists (m0 !!! Regidx s4_idx). iExact "Hw4". }
    { iExists (m0 !!! Regidx s5_idx). iExact "Hw5". }
    { iExists (m0 !!! Regidx s6_idx). iExact "Hw6". }
    { iExists (m0 !!! Regidx s7_idx). iExact "Hw7". }
    { iExists (m0 !!! Regidx s8_idx). iExact "Hw8". }
    assert (Hme2 : me7 !!! Regidx s2_idx = m0 !!! Regidx s2_idx).
    {
      rewrite /me7 (upd_ne me6 (Regidx s8_idx) (Regidx s2_idx)
                     (regval_into_reg (m0 !!! Regidx s8_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me6 (upd_ne me5 (Regidx s7_idx) (Regidx s2_idx)
                     (regval_into_reg (m0 !!! Regidx s7_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me5 (upd_ne me4 (Regidx s6_idx) (Regidx s2_idx)
                     (regval_into_reg (m0 !!! Regidx s6_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me4 (upd_ne me3 (Regidx s5_idx) (Regidx s2_idx)
                     (regval_into_reg (m0 !!! Regidx s5_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me3 (upd_ne me2 (Regidx s4_idx) (Regidx s2_idx)
                     (regval_into_reg (m0 !!! Regidx s4_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me2 (upd_ne me1 (Regidx s3_idx) (Regidx s2_idx)
                     (regval_into_reg (m0 !!! Regidx s3_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me1.
      exact (upd_eq m (Regidx s2_idx) (regval_into_reg (m0 !!! Regidx s2_idx))). }
    assert (Hme3 : me7 !!! Regidx s3_idx = m0 !!! Regidx s3_idx).
    {
      rewrite /me7 (upd_ne me6 (Regidx s8_idx) (Regidx s3_idx)
                     (regval_into_reg (m0 !!! Regidx s8_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me6 (upd_ne me5 (Regidx s7_idx) (Regidx s3_idx)
                     (regval_into_reg (m0 !!! Regidx s7_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me5 (upd_ne me4 (Regidx s6_idx) (Regidx s3_idx)
                     (regval_into_reg (m0 !!! Regidx s6_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me4 (upd_ne me3 (Regidx s5_idx) (Regidx s3_idx)
                     (regval_into_reg (m0 !!! Regidx s5_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me3 (upd_ne me2 (Regidx s4_idx) (Regidx s3_idx)
                     (regval_into_reg (m0 !!! Regidx s4_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me2.
      exact (upd_eq me1 (Regidx s3_idx) (regval_into_reg (m0 !!! Regidx s3_idx))). }
    assert (Hme4 : me7 !!! Regidx s4_idx = m0 !!! Regidx s4_idx).
    {
      rewrite /me7 (upd_ne me6 (Regidx s8_idx) (Regidx s4_idx)
                     (regval_into_reg (m0 !!! Regidx s8_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me6 (upd_ne me5 (Regidx s7_idx) (Regidx s4_idx)
                     (regval_into_reg (m0 !!! Regidx s7_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me5 (upd_ne me4 (Regidx s6_idx) (Regidx s4_idx)
                     (regval_into_reg (m0 !!! Regidx s6_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me4 (upd_ne me3 (Regidx s5_idx) (Regidx s4_idx)
                     (regval_into_reg (m0 !!! Regidx s5_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me3.
      exact (upd_eq me2 (Regidx s4_idx) (regval_into_reg (m0 !!! Regidx s4_idx))). }
    assert (Hme5 : me7 !!! Regidx s5_idx = m0 !!! Regidx s5_idx).
    {
      rewrite /me7 (upd_ne me6 (Regidx s8_idx) (Regidx s5_idx)
                     (regval_into_reg (m0 !!! Regidx s8_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me6 (upd_ne me5 (Regidx s7_idx) (Regidx s5_idx)
                     (regval_into_reg (m0 !!! Regidx s7_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me5 (upd_ne me4 (Regidx s6_idx) (Regidx s5_idx)
                     (regval_into_reg (m0 !!! Regidx s6_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me4.
      exact (upd_eq me3 (Regidx s5_idx) (regval_into_reg (m0 !!! Regidx s5_idx))). }
    assert (Hme6 : me7 !!! Regidx s6_idx = m0 !!! Regidx s6_idx).
    {
      rewrite /me7 (upd_ne me6 (Regidx s8_idx) (Regidx s6_idx)
                     (regval_into_reg (m0 !!! Regidx s8_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me6 (upd_ne me5 (Regidx s7_idx) (Regidx s6_idx)
                     (regval_into_reg (m0 !!! Regidx s7_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me5.
      exact (upd_eq me4 (Regidx s6_idx) (regval_into_reg (m0 !!! Regidx s6_idx))). }
    assert (Hme7 : me7 !!! Regidx s7_idx = m0 !!! Regidx s7_idx).
    {
      rewrite /me7 (upd_ne me6 (Regidx s8_idx) (Regidx s7_idx)
                     (regval_into_reg (m0 !!! Regidx s8_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me6.
      exact (upd_eq me5 (Regidx s7_idx) (regval_into_reg (m0 !!! Regidx s7_idx))). }
    assert (Hme8 : me7 !!! Regidx s8_idx = m0 !!! Regidx s8_idx).
    {
      rewrite /me7.
      exact (upd_eq me6 (Regidx s8_idx) (regval_into_reg (m0 !!! Regidx s8_idx))). }
    assert (Hmeo : forall r : mword 5,
               (uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27)) ->
               me7 !!! Regidx r = m !!! Regidx r).
    { intros r Hr.
      (* NOT [vm_compute] on these: the goal carries the free [r], and
         [vm_compute] against a free variable is the documented hang.
         Compute the CONCRETE index only, then [lia] against [Hr]. *)
      assert (N18 : Regidx r <> Regidx s2_idx)
        by (apply uidx_ne;
            replace (uint s2_idx) with 18 by (vm_compute; reflexivity);
            lia).
      assert (N19 : Regidx r <> Regidx s3_idx)
        by (apply uidx_ne;
            replace (uint s3_idx) with 19 by (vm_compute; reflexivity);
            lia).
      assert (N20 : Regidx r <> Regidx s4_idx)
        by (apply uidx_ne;
            replace (uint s4_idx) with 20 by (vm_compute; reflexivity);
            lia).
      assert (N21 : Regidx r <> Regidx s5_idx)
        by (apply uidx_ne;
            replace (uint s5_idx) with 21 by (vm_compute; reflexivity);
            lia).
      assert (N22 : Regidx r <> Regidx s6_idx)
        by (apply uidx_ne;
            replace (uint s6_idx) with 22 by (vm_compute; reflexivity);
            lia).
      assert (N23 : Regidx r <> Regidx s7_idx)
        by (apply uidx_ne;
            replace (uint s7_idx) with 23 by (vm_compute; reflexivity);
            lia).
      assert (N24 : Regidx r <> Regidx s8_idx)
        by (apply uidx_ne;
            replace (uint s8_idx) with 24 by (vm_compute; reflexivity);
            lia).
      rewrite /me7 (upd_ne me6 (Regidx s8_idx) (Regidx r)
                     (regval_into_reg (m0 !!! Regidx s8_idx)) N24).
      rewrite /me6 (upd_ne me5 (Regidx s7_idx) (Regidx r)
                     (regval_into_reg (m0 !!! Regidx s7_idx)) N23).
      rewrite /me5 (upd_ne me4 (Regidx s6_idx) (Regidx r)
                     (regval_into_reg (m0 !!! Regidx s6_idx)) N22).
      rewrite /me4 (upd_ne me3 (Regidx s5_idx) (Regidx r)
                     (regval_into_reg (m0 !!! Regidx s5_idx)) N21).
      rewrite /me3 (upd_ne me2 (Regidx s4_idx) (Regidx r)
                     (regval_into_reg (m0 !!! Regidx s4_idx)) N20).
      rewrite /me2 (upd_ne me1 (Regidx s3_idx) (Regidx r)
                     (regval_into_reg (m0 !!! Regidx s3_idx)) N19).
      rewrite /me1 (upd_ne m (Regidx s2_idx) (Regidx r)
                     (regval_into_reg (m0 !!! Regidx s2_idx)) N18).
      reflexivity. }
    iIntros (h8 m2) "%Hspx %Hs0x %Hs1x %Hpres Hrun".
    iApply ("Hcont" $! h8 m2 with "[] Hrun").
    iPureIntro. intros r Hr.
    assert (Hpresx : uint r <> 2 -> uint r <> 8 -> uint r <> 9 -> uint r <> 1 ->
                       m2 !!! Regidx r = me7 !!! Regidx r).
    { intros H2 H8 H9 H1. apply Hpres; apply uidx_ne;
        [ replace (uint csp_rs1) with 2 by (vm_compute; reflexivity)
        | replace (uint s0_idx) with 8 by (vm_compute; reflexivity)
        | replace (uint s1_idx) with 9 by (vm_compute; reflexivity)
        | replace (uint ra_idx) with 1 by (vm_compute; reflexivity) ];
        assumption. }
    destruct (ucs_cases r Hr) as [E2 | [E3 | [E4 | [E8 | [E9 | E18]]]]].
    - assert (Er : Regidx r = Regidx csp_rs1)
        by (apply (uidx_eq r 2); [ exact E2 | vm_compute; reflexivity ]).
      rewrite Er Hspx. exact (eq_sym Hsp0).
    -
      assert (K2 : uint r <> 2) by lia.
      assert (K8 : uint r <> 8) by lia.
      assert (K9 : uint r <> 9) by lia.
      assert (K1 : uint r <> 1) by lia.
      rewrite (Hpresx K2 K8 K9 K1).
      assert (Hd : uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27)) by lia.
      rewrite (Hmeo r Hd). exact (Hfree r Hr Hd).
    -
      assert (K2 : uint r <> 2) by lia.
      assert (K8 : uint r <> 8) by lia.
      assert (K9 : uint r <> 9) by lia.
      assert (K1 : uint r <> 1) by lia.
      rewrite (Hpresx K2 K8 K9 K1).
      assert (Hd : uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27)) by lia.
      rewrite (Hmeo r Hd). exact (Hfree r Hr Hd).
    - assert (Er : Regidx r = Regidx s0_idx)
        by (apply (uidx_eq r 8); [ exact E8 | vm_compute; reflexivity ]).
      rewrite Er. exact Hs0x.
    - assert (Er : Regidx r = Regidx s1_idx)
        by (apply (uidx_eq r 9); [ exact E9 | vm_compute; reflexivity ]).
      rewrite Er. exact Hs1x.
    -
      assert (K2 : uint r <> 2) by lia.
      assert (K8 : uint r <> 8) by lia.
      assert (K9 : uint r <> 9) by lia.
      assert (K1 : uint r <> 1) by lia.
      rewrite (Hpresx K2 K8 K9 K1).
      assert (Ecase : uint r = 18 \/ uint r = 19 \/ uint r = 20 \/ uint r = 21 \/
                      uint r = 22 \/ uint r = 23 \/ uint r = 24 \/
                      uint r = 25 \/ uint r = 26 \/ uint r = 27) by lia.
      destruct Ecase as [E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]].
      + assert (Er : Regidx r = Regidx s2_idx)
          by (apply (uidx_eq r 18); [ exact E | vm_compute; reflexivity ]).
        rewrite Er. exact Hme2.
      + assert (Er : Regidx r = Regidx s3_idx)
          by (apply (uidx_eq r 19); [ exact E | vm_compute; reflexivity ]).
        rewrite Er. exact Hme3.
      + assert (Er : Regidx r = Regidx s4_idx)
          by (apply (uidx_eq r 20); [ exact E | vm_compute; reflexivity ]).
        rewrite Er. exact Hme4.
      + assert (Er : Regidx r = Regidx s5_idx)
          by (apply (uidx_eq r 21); [ exact E | vm_compute; reflexivity ]).
        rewrite Er. exact Hme5.
      + assert (Er : Regidx r = Regidx s6_idx)
          by (apply (uidx_eq r 22); [ exact E | vm_compute; reflexivity ]).
        rewrite Er. exact Hme6.
      + assert (Er : Regidx r = Regidx s7_idx)
          by (apply (uidx_eq r 23); [ exact E | vm_compute; reflexivity ]).
        rewrite Er. exact Hme7.
      + assert (Er : Regidx r = Regidx s8_idx)
          by (apply (uidx_eq r 24); [ exact E | vm_compute; reflexivity ]).
        rewrite Er. exact Hme8.
      + assert (Hd : uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27)) by lia.
        rewrite (Hmeo r Hd). exact (Hfree r Hr Hd).
      + assert (Hd : uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27)) by lia.
        rewrite (Hmeo r Hd). exact (Hfree r Hr Hd).
      + assert (Hd : uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27)) by lia.
        rewrite (Hmeo r Hd). exact (Hfree r Hr Hd).
  Qed.
  Local Notation a6_idx := (mword_of_int 16 : mword 5).

  (* --------------------------------------------------------------------- *)
  (* fprintf(fd, fmt) @0x10aa.  The frame, down from the entry sp:            *)
  (*                                                                        *)
  (*   sp0-8  a7   sp0-16 a6   sp0-24 a5   sp0-32 a4   sp0-40 a3            *)
  (*   sp0-48 a2   sp0-56 ra   sp0-64 s0   sp0-72 ap   sp0-80 --            *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kshd_fprintf_gen (a : Z) (h : CpuId) (m : regfile) (n : nat) :
    m !!! Regidx a1_idx = mword_of_int a ->
    shk_code γt -∗
    (* the call at 0x10c8, left to the caller.  fprintf's own instructions
       say nothing about the format string -- they carve the frame, spill
       a2..a7 into it, point a2 at the spill area and jump -- and two
       callers want two different things out of that jump.  The word at
       sp0-48 is the a2 slot, which IS the va_list's first element, so it
       goes to the callee and comes back. *)
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ m' !!! Regidx a1_idx = mword_of_int a ⌝ -∗
       ⌜ m' !!! Regidx a2_idx
         = mword_of_int (uint (m !!! Regidx csp_rs1) - 48) ⌝ -∗
       ⌜ m' !!! Regidx ra_idx = (mword_of_int 0x10cc : mword 64) ⌝ -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 48) (m !!! Regidx a2_idx) -∗
       urun γt γd γs γfd h' m' (mword_of_int ShSyms.vprintf) (12 + (4 + n)) -∗
       (∀ (h'' : CpuId) (m'' : regfile),
          ⌜ ucallee_saved m' m'' ⌝ -∗
          uword γd (uint (m !!! Regidx csp_rs1) - 48) (m !!! Regidx a2_idx) -∗
          urun γt γd γs γfd h'' m'' (mword_of_int 0x10cc) (12 + (4 + n)) -∗
          WP (Loop : expr riscv_lang)) -∗
       WP (Loop : expr riscv_lang)) -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.fprintf) (10 + (12 + (4 + n))) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ ucallee_saved m m' ⌝ -∗
       urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (10 + (12 + (4 + n))) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha1r.
    iIntros "#Hcode Hvp Hrun Hcont".
    pose proof shd_pin_fprintf as Hfprintf.
    pose proof shd_pin_vprintf as Hvprintf.
    rewrite Hfprintf.
    iDestruct (urun_stack with "Hrun") as %[Hal8' Hroom'].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0e.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0e).
    clear Hsp0e.
    assert (Hal8 : uint sp0 mod 8 = 0) by exact Hal8'.
    assert (Hlo : 80 <= uint sp0) by (clear -Hroom'; lia).
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 10)))
                   = bv_unsigned sp0 - 80).
    { replace (- (8 * Z.of_nat 10)) with (-80) by lia.
      exact (uv_avi_neg sp0 80 ltac:(apply Z.leb_le; reflexivity)
               ltac:(rewrite <- uint_unsigned; exact Hlo)). }
    assert (Hsp80 : uint (add_vec_int sp0 (- (8 * Z.of_nat 10)))
                    = uint sp0 - 80)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (HR : 0 <= bv_unsigned sp0 < 18446744073709551616).
    { pose proof (bv_unsigned_in_range 64 sp0) as H0.
      assert (Em : bv_modulus 64 = 18446744073709551616)
        by (vm_compute; reflexivity).
      rewrite Em in H0. exact H0. }
    assert (Hlt10 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 10)))
                    + 8 * Z.of_nat 10 < Z64)
      by (clear -Hbsp HR; rewrite Hbsp; unfold Z64; lia).
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 10)))
                    (8 * Z.of_nat 10) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 10)))
                 (8 * Z.of_nat 10) ltac:(apply Z.leb_le; reflexivity) Hlt10).
      clear -Hbsp. rewrite Hbsp. lia. }
    assert (Ho24 : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
      by (vm_compute; reflexivity).
    assert (Ho16 : uoff_sdsp (mword_of_int 2 : mword 6) = 16)
      by (vm_compute; reflexivity).
    (* ---- 0x10aa  c.addi16sp sp,sp,-80 ---- *)
    iApply (wp_uk_caddi16sp_dn γt γd γs γfd h m (mword_of_int 0x10aa)
              (mword_of_int 59 : mword 6) 10 (12 + (4 + n))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_10aa with "Hcode"). }
    iIntros "Hframe".
    assert (E7d0 : add_vec_int (mword_of_int 0x10aa : mword 64) 2
                   = mword_of_int 0x10ac)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp E7d0.
    iIntros (h0) "Hrun".
    set (mq1 := <[Regidx csp_rs1
                  := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 10)))]> m).
    assert (Hspq1 : mq1 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 10)))
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg _)).
    iDestruct (ustack_10_open with "Hframe")
      as "(_ & [%u1 Hu1] & [%u2 Hu2] & [%u3 Hu3] & [%u4 Hu4] & [%u5 Hu5]
            & [%u6 Hu6] & [%u7 Hu7] & [%u8 Hu8] & [%u9 Hu9] & Hu10)".
    (* ---- 0x10ac  c.sdsp ra,24(sp) ---- *)
    assert (Hraq1 : mq1 !!! Regidx ra_idx = m !!! Regidx ra_idx)
      by exact (upd_ne m (Regidx csp_rs1) (Regidx ra_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Hs0q1 : mq1 !!! Regidx s0_idx = m !!! Regidx s0_idx)
      by exact (upd_ne m (Regidx csp_rs1) (Regidx s0_idx) _
                  ltac:(vm_compute; discriminate)).
    iApply (wp_uk_csdsp γt γd γs γfd h0 mq1 (mword_of_int 0x10ac)
              (mword_of_int 3 : mword 6) ra_idx (uint sp0 - 56) u7 (12 + (4 + n))
              ltac:(rewrite Hspq1 Hsp80 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu7 Hrun").
    { iApply (uis_shk_10ac with "Hcode"). }
    iIntros "Hu7". rewrite Hraq1.
    assert (E7d2 : add_vec_int (mword_of_int 0x10ac : mword 64) 2
                   = mword_of_int 0x10ae)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7d2.
    iIntros (h1) "Hrun".
    (* ---- 0x10ae  c.sdsp s0,16(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd h1 mq1 (mword_of_int 0x10ae)
              (mword_of_int 2 : mword 6) s0_idx (uint sp0 - 64) u8 (12 + (4 + n))
              ltac:(rewrite Hspq1 Hsp80 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu8 Hrun").
    { iApply (uis_shk_10ae with "Hcode"). }
    iIntros "Hu8". rewrite Hs0q1.
    assert (E7d4 : add_vec_int (mword_of_int 0x10ae : mword 64) 2
                   = mword_of_int 0x10b0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7d4.
    iIntros (h2) "Hrun".
    (* ---- 0x10b0  c.addi4spn s0,sp,32 -- s0 sits at sp0-48 ---- *)
    assert (Hs048 : add_vec (mq1 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8)))
                    = add_vec_int sp0 (- 48)).
    { rewrite Hspq1.
      assert (Ec32 : (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))
                      : mword 64) = mword_of_int 32)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ec32.
      assert (Efold : add_vec (add_vec_int sp0 (- (8 * Z.of_nat 10)))
                        (mword_of_int 32)
                      = add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 10))) 32)
        by reflexivity.
      rewrite Efold. apply bv_eq.
      assert (H32 : (0 <= 32)%Z) by lia.
      assert (Hlt32 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 10))) + 32
                      < Z64)
        by (clear -Hbsp HR; rewrite Hbsp; unfold Z64; lia).
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 10))) 32 H32 Hlt32).
      assert (Hlo48 : 48 <= bv_unsigned sp0)
        by (clear -Hlo; rewrite <- uint_unsigned; lia).
      assert (Eneg : bv_unsigned (add_vec_int sp0 (- 48)) = bv_unsigned sp0 - 48)
        by (exact (uv_avi_neg sp0 48 ltac:(apply Z.leb_le; reflexivity) Hlo48)).
      rewrite Eneg Hbsp. lia. }
    iApply (wp_uk_caddi4spn γt γd γs γfd h2 mq1 (mword_of_int 0x10b0)
              (mword_of_int 0 : mword 3) (mword_of_int 8 : mword 8) s0_idx
              (add_vec_int sp0 (- 48)) (12 + (4 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Hs048))
              with "[] Hrun").
    { iApply (uis_shk_10b0 with "Hcode"). }
    assert (E7d6 : add_vec_int (mword_of_int 0x10b0 : mword 64) 2
                   = mword_of_int 0x10b2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7d6.
    iIntros (h3) "Hrun".
    set (mq2 := <[Regidx s0_idx
                  := regval_into_reg (add_vec_int sp0 (- 48))]> mq1).
    assert (Hs0q2 : uint (mq2 !!! Regidx s0_idx) = uint sp0 - 48).
    { rewrite (upd_eq mq1 (Regidx s0_idx) (regval_into_reg _)).
      rewrite !uint_unsigned.
      exact (uv_avi_neg sp0 48 ltac:(apply Z.leb_le; reflexivity)
               ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hspq2 : mq2 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 10))).
    { rewrite <- Hspq1.
      exact (upd_ne mq1 (Regidx s0_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x10b2  c.sd a2,0(s0) ---- *)
    assert (Hoc0 : uoff_c8 (mword_of_int 0 : mword 5) = 0)
      by (vm_compute; reflexivity).
    iApply (wp_uk_csd γt γd γs γfd h3 mq2 (mword_of_int 0x10b2)
              (mword_of_int 0 : mword 5) (mword_of_int 0 : mword 3)
              (mword_of_int 4 : mword 3) s0_idx a2_idx
              (uint sp0 - 48) u6 (12 + (4 + n))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs0q2 Hoc0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu6 Hrun").
    { iApply (uis_shk_10b2 with "Hcode"). }
    iIntros "Hu6".
    assert (E7d8 : add_vec_int (mword_of_int 0x10b2 : mword 64) 2
                 = mword_of_int 0x10b4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7d8.
    iIntros (h4) "Hrun".
    (* ---- 0x10b4  c.sd a3,8(s0) ---- *)
    assert (Hoc8 : uoff_c8 (mword_of_int 1 : mword 5) = 8)
      by (vm_compute; reflexivity).
    iApply (wp_uk_csd γt γd γs γfd h4 mq2 (mword_of_int 0x10b4)
              (mword_of_int 1 : mword 5) (mword_of_int 0 : mword 3)
              (mword_of_int 5 : mword 3) s0_idx a3_idx
              (uint sp0 - 40) u5 (12 + (4 + n))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs0q2 Hoc8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu5 Hrun").
    { iApply (uis_shk_10b4 with "Hcode"). }
    iIntros "Hu5".
    assert (E7da : add_vec_int (mword_of_int 0x10b4 : mword 64) 2
                 = mword_of_int 0x10b6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7da.
    iIntros (h5) "Hrun".
    (* ---- 0x10b6  c.sd a4,16(s0) ---- *)
    assert (Hoc16 : uoff_c8 (mword_of_int 2 : mword 5) = 16)
      by (vm_compute; reflexivity).
    iApply (wp_uk_csd γt γd γs γfd h5 mq2 (mword_of_int 0x10b6)
              (mword_of_int 2 : mword 5) (mword_of_int 0 : mword 3)
              (mword_of_int 6 : mword 3) s0_idx a4_idx
              (uint sp0 - 32) u4 (12 + (4 + n))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs0q2 Hoc16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu4 Hrun").
    { iApply (uis_shk_10b6 with "Hcode"). }
    iIntros "Hu4".
    assert (E7dc : add_vec_int (mword_of_int 0x10b6 : mword 64) 2
                 = mword_of_int 0x10b8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7dc.
    iIntros (h6) "Hrun".
    (* ---- 0x10b8  c.sd a5,24(s0) ---- *)
    assert (Hoc24 : uoff_c8 (mword_of_int 3 : mword 5) = 24)
      by (vm_compute; reflexivity).
    iApply (wp_uk_csd γt γd γs γfd h6 mq2 (mword_of_int 0x10b8)
              (mword_of_int 3 : mword 5) (mword_of_int 0 : mword 3)
              (mword_of_int 7 : mword 3) s0_idx a5_idx
              (uint sp0 - 24) u3 (12 + (4 + n))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs0q2 Hoc24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu3 Hrun").
    { iApply (uis_shk_10b8 with "Hcode"). }
    iIntros "Hu3".
    assert (E7de : add_vec_int (mword_of_int 0x10b8 : mword 64) 2
                 = mword_of_int 0x10ba)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7de.
    iIntros (h7) "Hrun".
    (* ---- 0x10ba  sd a6,32(s0) ---- *)
    assert (Hoi32 : uoff_i12 (mword_of_int 32 : mword 12) = 32)
      by (vm_compute; reflexivity).
    iApply (wp_uk_sd γt γd γs γfd h7 mq2 (mword_of_int 0x10ba)
              (mword_of_int 32 : mword 12) s0_idx a6_idx
              (uint sp0 - 16) u2 (12 + (4 + n))
              ltac:(rewrite Hs0q2 Hoi32; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu2 Hrun").
    { iApply (uis_shk_10ba with "Hcode"). }
    iIntros "Hu2".
    assert (E7e0 : add_vec_int (mword_of_int 0x10ba : mword 64) 4
                 = mword_of_int 0x10be)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7e0.
    iIntros (h8) "Hrun".
    (* ---- 0x10be  sd a7,40(s0) ---- *)
    assert (Hoi40 : uoff_i12 (mword_of_int 40 : mword 12) = 40)
      by (vm_compute; reflexivity).
    iApply (wp_uk_sd γt γd γs γfd h8 mq2 (mword_of_int 0x10be)
              (mword_of_int 40 : mword 12) s0_idx a7_idx
              (uint sp0 - 8) u1 (12 + (4 + n))
              ltac:(rewrite Hs0q2 Hoi40; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu1 Hrun").
    { iApply (uis_shk_10be with "Hcode"). }
    iIntros "Hu1".
    assert (E7e4 : add_vec_int (mword_of_int 0x10be : mword 64) 4
                 = mword_of_int 0x10c2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7e4.
    iIntros (h9) "Hrun".
    (* ---- 0x10c2  c.mv a2,s0 -- the va_list ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h9 mq2 (mword_of_int 0x10c2) a2_idx s0_idx
              (add_vec zero_reg (mq2 !!! Regidx s0_idx)) (12 + (4 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_10c2 with "Hcode"). }
    assert (E7e8 : add_vec_int (mword_of_int 0x10c2 : mword 64) 2
                   = mword_of_int 0x10c4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7e8.
    iIntros (h10) "Hrun".
    set (mq3 := <[Regidx a2_idx
                  := regval_into_reg
                       (add_vec zero_reg (mq2 !!! Regidx s0_idx))]> mq2).
    assert (Hs0q3 : uint (mq3 !!! Regidx s0_idx) = uint sp0 - 48).
    { rewrite <- Hs0q2. f_equal;
        exact (upd_ne mq2 (Regidx a2_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)). }
    (* ---- 0x10c4  sd s0,-24(s0) -- park it ---- *)
    assert (Hoim24 : uoff_i12 (mword_of_int 4072 : mword 12) = -24)
      by (vm_compute; reflexivity).
    iApply (wp_uk_sd γt γd γs γfd h10 mq3 (mword_of_int 0x10c4)
              (mword_of_int 4072 : mword 12) s0_idx s0_idx
              (uint sp0 - 72) u9 (12 + (4 + n))
              ltac:(rewrite Hs0q3 Hoim24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu9 Hrun").
    { iApply (uis_shk_10c4 with "Hcode"). }
    iIntros "Hu9".
    assert (E7ea : add_vec_int (mword_of_int 0x10c4 : mword 64) 4
                   = mword_of_int 0x10c8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7ea.
    iIntros (h11) "Hrun".
    (* ---- 0x10c8  jal ra,0xdea <vprintf> ---- *)
    assert (Ha1q3 : mq3 !!! Regidx a1_idx = mword_of_int a).
    { rewrite <- Ha1r.
      rewrite /mq3 (upd_ne mq2 (Regidx a2_idx) (Regidx a1_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /mq2 (upd_ne mq1 (Regidx s0_idx) (Regidx a1_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /mq1. exact (upd_ne m (Regidx csp_rs1) (Regidx a1_idx) _
                             ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_jal γt γd γs γfd h11 mq3 (mword_of_int 0x10c8)
              (mword_of_int 2096418 : mword 21) ra_idx
              (mword_of_int ShSyms.vprintf) (mword_of_int 0x10cc) (12 + (4 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hvprintf; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hvprintf; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_10c8 with "Hcode"). }
    iIntros (h12) "Hrun".
    set (mq4 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x10cc : mword 64)]> mq3).
    assert (Hraq4 : mq4 !!! Regidx ra_idx = (mword_of_int 0x10cc : mword 64))
      by exact (upd_eq mq3 (Regidx ra_idx) (regval_into_reg _)).
    assert (Ha1q4 : mq4 !!! Regidx a1_idx = mword_of_int a).
    { rewrite <- Ha1q3.
      exact (upd_ne mq3 (Regidx ra_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- vprintf(fd, fmt, ap) -- whichever one the caller brought ---- *)
    assert (Ha2q2 : mq2 !!! Regidx a2_idx = m !!! Regidx a2_idx).
    { rewrite /mq2 (upd_ne mq1 (Regidx s0_idx) (Regidx a2_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /mq1. exact (upd_ne m (Regidx csp_rs1) (Regidx a2_idx) _
                             ltac:(vm_compute; discriminate)). }
    iEval (rewrite Ha2q2) in "Hu6".
    assert (Ha2q4 : mq4 !!! Regidx a2_idx = mword_of_int (uint sp0 - 48)).
    { rewrite /mq4 (upd_ne mq3 (Regidx ra_idx) (Regidx a2_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /mq3 (upd_eq mq2 (Regidx a2_idx) (regval_into_reg _)).
      rewrite add_vec_zero_l.
      rewrite <- Hs0q2. symmetry.
      exact (moi_of_uint (mq2 !!! Regidx s0_idx)). }
    iApply ("Hvp" $! h12 mq4 with "[] [] [] Hu6 Hrun
              [Hu1 Hu2 Hu3 Hu4 Hu5 Hu7 Hu8 Hu9 Hu10 Hcont]").
    { iPureIntro. exact Ha1q4. }
    { iPureIntro. exact Ha2q4. }
    { iPureIntro. exact Hraq4. }
    iIntros (h13 mq5) "%Hcs Hu6 Hrun".
    (* ---- 0x10cc  c.ldsp ra,24(sp) ---- *)
    assert (Hspq5 : mq5 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 10))).
    { rewrite (Hcs csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite <- Hspq2.
      rewrite /mq4 (upd_ne mq3 (Regidx ra_idx) (Regidx csp_rs1) _
                      ltac:(vm_compute; discriminate)).
      rewrite /mq3. exact (upd_ne mq2 (Regidx a2_idx) (Regidx csp_rs1) _
                             ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_cldsp γt γd γs γfd h13 mq5 (mword_of_int 0x10cc)
              (mword_of_int 3 : mword 6) ra_idx (uint sp0 - 56)
              (m !!! Regidx ra_idx) (12 + (4 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspq5 Hsp80 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hu7 Hrun").
    { iApply (uis_shk_10cc with "Hcode"). }
    iIntros "Hu7".
    assert (E7f2 : add_vec_int (mword_of_int 0x10cc : mword 64) 2
                   = mword_of_int 0x10ce)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7f2.
    iIntros (h14) "Hrun".
    set (mq6 := <[Regidx ra_idx
                  := regval_into_reg (m !!! Regidx ra_idx)]> mq5).
    assert (Hspq6 : mq6 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 10))).
    { rewrite <- Hspq5.
      exact (upd_ne mq5 (Regidx ra_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x10ce  c.ldsp s0,16(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h14 mq6 (mword_of_int 0x10ce)
              (mword_of_int 2 : mword 6) s0_idx (uint sp0 - 64)
              (m !!! Regidx s0_idx) (12 + (4 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspq6 Hsp80 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hu8 Hrun").
    { iApply (uis_shk_10ce with "Hcode"). }
    iIntros "Hu8".
    assert (E7f4 : add_vec_int (mword_of_int 0x10ce : mword 64) 2
                   = mword_of_int 0x10d0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7f4.
    iIntros (h15) "Hrun".
    set (mq7 := <[Regidx s0_idx
                  := regval_into_reg (m !!! Regidx s0_idx)]> mq6).
    assert (Hspq7 : mq7 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 10))).
    { rewrite <- Hspq6.
      exact (upd_ne mq6 (Regidx s0_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x10d0  c.addi16sp sp,sp,80 -- the frame goes back ---- *)
    iApply (wp_uk_caddi16sp_up γt γd γs γfd h15 mq7 (mword_of_int 0x10d0)
              (mword_of_int 5 : mword 6) 10 (12 + (4 + n))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hu1 Hu2 Hu3 Hu4 Hu5 Hu6 Hu7 Hu8 Hu9 Hu10] Hrun").
    { iApply (uis_shk_10d0 with "Hcode"). }
    { rewrite Hspq7 Hup.
      iApply (ustack_10_close γd sp0 Hal8
                with "[Hu1] [Hu2] [Hu3] [Hu4] [Hu5] [Hu6] [Hu7] [Hu8] [Hu9] Hu10").
      { iExists (mq2 !!! Regidx a7_idx). iExact "Hu1". }
      { iExists (mq2 !!! Regidx a6_idx). iExact "Hu2". }
      { iExists (mq2 !!! Regidx a5_idx). iExact "Hu3". }
      { iExists (mq2 !!! Regidx a4_idx). iExact "Hu4". }
      { iExists (mq2 !!! Regidx a3_idx). iExact "Hu5". }
      { iExists (m !!! Regidx a2_idx). iExact "Hu6". }
      { iExists (m !!! Regidx ra_idx). iExact "Hu7". }
      { iExists (m !!! Regidx s0_idx). iExact "Hu8". }
      { iExists (mq3 !!! Regidx s0_idx). iExact "Hu9". } }
    assert (E7f6 : add_vec_int (mword_of_int 0x10d0 : mword 64) 2
                   = mword_of_int 0x10d2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hspq7 Hup E7f6.
    iIntros (h16) "Hrun".
    set (mq8 := <[Regidx csp_rs1 := regval_into_reg sp0]> mq7).
    assert (Hraq8 : mq8 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite /mq8 (upd_ne mq7 (Regidx csp_rs1) (Regidx ra_idx) _
                       ltac:(vm_compute; discriminate)).
      rewrite /mq7 (upd_ne mq6 (Regidx s0_idx) (Regidx ra_idx) _
                       ltac:(vm_compute; discriminate)).
      rewrite /mq6. exact (upd_eq mq5 (Regidx ra_idx) (regval_into_reg _)). }
    (* ---- 0x10d2  c.jr ra ---- *)
    iApply (wp_uk_cjr γt γd γs γfd h16 mq8 (mword_of_int 0x10d2) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) (10 + (12 + (4 + n)))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hraq8; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_10d2 with "Hcode"). }
    iIntros (h17) "Hrun".
    iApply ("Hcont" $! h17 mq8 with "[] Hrun").
    iPureIntro. intros r Hr.
    assert (Kne : forall (q : mword 5) (z : Z),
               uint q = z -> uint r <> z -> Regidx r <> Regidx q).
    { intros q z Hq Hz. apply uidx_ne. rewrite Hq. exact Hz. }
    assert (Huntouched : uint r <> 1 -> uint r <> 2 -> uint r <> 8 ->
                         uint r <> 12 ->
                         mq8 !!! Regidx r = m !!! Regidx r).
    { intros K1 K2 K8 K12.
      rewrite /mq8 (upd_ne mq7 (Regidx csp_rs1) (Regidx r) _
                       (Kne csp_rs1 2 ltac:(vm_compute; reflexivity) K2)).
      rewrite /mq7 (upd_ne mq6 (Regidx s0_idx) (Regidx r) _
                       (Kne s0_idx 8 ltac:(vm_compute; reflexivity) K8)).
      rewrite /mq6 (upd_ne mq5 (Regidx ra_idx) (Regidx r) _
                       (Kne ra_idx 1 ltac:(vm_compute; reflexivity) K1)).
      rewrite (Hcs r Hr).
      rewrite /mq4 (upd_ne mq3 (Regidx ra_idx) (Regidx r) _
                       (Kne ra_idx 1 ltac:(vm_compute; reflexivity) K1)).
      rewrite /mq3 (upd_ne mq2 (Regidx a2_idx) (Regidx r) _
                       (Kne a2_idx 12 ltac:(vm_compute; reflexivity) K12)).
      rewrite /mq2 (upd_ne mq1 (Regidx s0_idx) (Regidx r) _
                       (Kne s0_idx 8 ltac:(vm_compute; reflexivity) K8)).
      rewrite /mq1. exact (upd_ne m (Regidx csp_rs1) (Regidx r) _
                             (Kne csp_rs1 2 ltac:(vm_compute; reflexivity) K2)). }
    destruct (ucs_cases r Hr) as [E2 | [E3 | [E4 | [E8 | [E9 | E18]]]]].
    - assert (Er : Regidx r = Regidx csp_rs1)
        by (apply (uidx_eq r 2); [ exact E2 | vm_compute; reflexivity ]).
      rewrite Er /mq8 (upd_eq mq7 (Regidx csp_rs1) (regval_into_reg sp0)).
      rewrite <- Hsp. reflexivity.
    - apply Huntouched; lia.
    - apply Huntouched; lia.
    - assert (Er : Regidx r = Regidx s0_idx)
        by (apply (uidx_eq r 8); [ exact E8 | vm_compute; reflexivity ]).
      rewrite Er /mq8 (upd_ne mq7 (Regidx csp_rs1) (Regidx s0_idx) _
                          ltac:(vm_compute; discriminate)).
      rewrite /mq7. exact (upd_eq mq6 (Regidx s0_idx) (regval_into_reg _)).
    - apply Huntouched; lia.
    - apply Huntouched; lia.
  Qed.

  (* --------------------------------------------------------------------- *)
  (* fprintf for a format with no directive, and for one that has a '%s'.   *)
  (* sh only ever issues the second; the first is kept because it is what   *)
  (* the plain [vprintf] walk of §3 is for, and it costs one [iApply].      *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kshd_fprintf (a : Z) (len : nat) (f : nat -> mword 8)
      (h : CpuId) (m : regfile) (n : nat) :
    0 <= a -> a + Z.of_nat len + 2 < 2 ^ 31 ->
    (0 < len)%nat ->
    (forall j : nat, (j < len)%nat -> bv_unsigned (f j) <> 37) ->
    m !!! Regidx a1_idx = mword_of_int a ->
    shk_code γt -∗
    utext_str γt a len f -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.fprintf) (10 + (12 + (4 + n))) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ ucallee_saved m m' ⌝ -∗
       urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (10 + (12 + (4 + n))) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd Hlen Hpct Ha1.
    iIntros "#Hcode #Hstr Hrun Hcont".
    iApply (wp_kshd_fprintf_gen a h m n Ha1 with "Hcode [] Hrun Hcont").
    iIntros (h' m') "%Ha1' %Ha2' %Hra' Hu6 Hrun Hk".
    iApply (wp_kshd_vprintf γt γd γs γfd a len f h' m' n
              Ha0 Habnd Hlen Hpct Ha1' with "Hcode Hstr Hrun").
    iIntros (h'' m'') "%Hcs Hrun".
    assert (Eret : ret_pc (m' !!! Regidx ra_idx)
                   = (mword_of_int 0x10cc : mword 64))
      by (rewrite Hra'; apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    iApply ("Hk" $! h'' m'' with "[] Hu6 Hrun"). iPureIntro. exact Hcs.
  Qed.

  Lemma wp_kshd_fprintf_s (a : Z) (len q : nat) (f : nat -> mword 8)
      (sa : Z) (slen : nat) (sf : nat -> bv 8)
      (h : CpuId) (m : regfile) (n : nat) :
    0 <= a -> a + Z.of_nat len + 2 < 2 ^ 31 ->
    (S (S q) < len)%nat ->
    bv_unsigned (f q) = 37 ->
    bv_unsigned (f (S q)) = 115 ->
    (forall j : nat, (j < len)%nat -> j <> q -> bv_unsigned (f j) <> 37) ->
    bv_unsigned (f (S (S q))) <> 100 ->
    bv_unsigned (f (S (S q))) <> 117 ->
    bv_unsigned (f (S (S q))) <> 120 ->
    ((S (S (S q)) < len)%nat ->
       bv_unsigned (f (S (S (S q)))) <> 100 /\
       bv_unsigned (f (S (S (S q)))) <> 117 /\
       bv_unsigned (f (S (S (S q)))) <> 120) ->
    sa <> 0 ->
    m !!! Regidx a1_idx = mword_of_int a ->
    m !!! Regidx a2_idx = mword_of_int sa ->
    shk_code γt -∗
    utext_str γt a len f -∗
    shd_str γt γd tx sa slen sf -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.fprintf) (10 + (12 + (4 + n))) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ ucallee_saved m m' ⌝ -∗
       urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (10 + (12 + (4 + n))) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd Hq2 Hfq Hfsq Hpct Hc1d Hc1u Hc1x Hc2set Hsanz Ha1 Ha2.
    iIntros "#Hcode #Hstr #Hsstr Hrun Hcont".
    iDestruct (urun_stack with "Hrun") as %[Hal8 _].
    assert (Hapal : (uint (m !!! Regidx csp_rs1) - 48) mod 8 = 0)
      by (rewrite Zminus_mod Hal8; reflexivity).
    iApply (wp_kshd_fprintf_gen a h m n Ha1 with "Hcode [] Hrun Hcont").
    iIntros (h' m') "%Ha1' %Ha2' %Hra' Hu6 Hrun Hk".
    rewrite Ha2.
    iApply (wp_kshd_vprintf_s γt γd γs γfd tx a len q f
              (uint (m !!! Regidx csp_rs1) - 48) sa (DfracOwn 1) slen sf
              h' m' n Ha0 Habnd Hq2 Hfq Hfsq Hpct Hc1d Hc1u Hc1x Hc2set
              Hapal Hsanz Ha1' Ha2'
              with "Hcode Hstr Hu6 Hsstr Hrun").
    iIntros (h'' m'') "Hu6 %Hcs Hrun".
    assert (Eret : ret_pc (m' !!! Regidx ra_idx)
                   = (mword_of_int 0x10cc : mword 64))
      by (rewrite Hra'; apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    iApply ("Hk" $! h'' m'' with "[] Hu6 Hrun"). iPureIntro. exact Hcs.
  Qed.

End UkShDiagFprintf.

(* ===================================================================== *)
(* §6 THE THREE ENTRY PCS.                                                *)
(*                                                                       *)
(* All three end in the SAME six-instruction block with a different       *)
(* format string and a different exit code, so that block is ONE lemma    *)
(* parameterised by its pcs ([wp_kshd_die]).  What differs above it:      *)
(*                                                                       *)
(*   panic  @0x4a  pushes a 16-byte frame, spills ra and s0, and moves    *)
(*                 its argument into a2; the '%s' argument is a .rodata   *)
(*                 literal, so [tx = true].                              *)
(*   0xda          [c.ld a2,8(s1)] -- ecmd->argv[0], a HEAP string, so    *)
(*                 [tx = false] -- then the block, then exit(0).          *)
(*   0x10e         [c.ld a2,16(s1)] -- rcmd->file, ditto, exit(1).        *)
(* ===================================================================== *)

(* A .rodata C string, DECIDED from the image: no NUL in the body, a NUL
   at [len].  §1's [shd_lit_ok] is this plus "and no '%' either", which is
   exactly what a FORMAT string is not -- hence the second predicate. *)
Definition shd_fmt_ok (base : Z) (len : nat) : bool :=
  forallb (fun j => match shk_ro !! (base + Z.of_nat j)%Z with
                    | Some b => negb (Z.eqb (bv_unsigned b) 0)
                    | None => false
                    end)
          (seq 0 len)
  && match shk_ro !! (base + Z.of_nat len)%Z with
     | Some b => Z.eqb (bv_unsigned b) 0
     | None => false
     end.

(* ...and "the only '%' in it is the one at [q]" *)
Definition shd_nopct (base : Z) (len q : nat) : bool :=
  forallb (fun j => Nat.eqb j q
                    || negb (Z.eqb (bv_unsigned (shd_lit base j)) 37))
          (seq 0 len).

Lemma shd_nopct_ok (base : Z) (len q j : nat) :
  shd_nopct base len q = true -> (j < len)%nat -> j <> q ->
  bv_unsigned (shd_lit base j) <> 37.
Proof.
  intros H Hj Hne. unfold shd_nopct in H. rewrite forallb_forall in H.
  specialize (H j ltac:(apply in_seq; lia)).
  apply orb_true_iff in H as [H | H].
  - apply Nat.eqb_eq in H. exfalso. exact (Hne H).
  - apply negb_true_iff, Z.eqb_neq in H. exact H.
Qed.

Section UkShDiagFmt.
  Context `{!riscvGS Σ}.

  Context `{!ufdG Σ}.
  (* the literal, cut out of the image the caller holds *)
  Lemma shd_fmt_str (γt : gname) (base : Z) (len : nat) :
    shd_fmt_ok base len = true ->
    Z.of_nat len < 2 ^ 31 ->
    shk_rodata γt -∗ utext_str γt base len (shd_lit base).
  Proof.
    intros Hok Hlen.
    unfold shd_fmt_ok in Hok. apply andb_true_iff in Hok as [Hbody Hnul].
    rewrite forallb_forall in Hbody.
    iIntros "#Hro". rewrite /shk_rodata.
    iApply (utext_str_of_img γt shk_ro base len (shd_lit base)).
    - intros j Hj.
      specialize (Hbody j ltac:(apply in_seq; lia)).
      unfold shd_lit.
      destruct (shk_ro !! (base + Z.of_nat j)%Z) as [b | ] eqn:Hb;
        [ | discriminate ].
      apply negb_true_iff, Z.eqb_neq in Hbody.
      intro He. apply Hbody.
      assert (Hbe : b = ubyte0) by (rewrite <- He; reflexivity).
      rewrite Hbe. vm_compute. reflexivity.
    - exact Hlen.
    - intros j Hj.
      specialize (Hbody j ltac:(apply in_seq; lia)).
      unfold shd_lit.
      destruct (shk_ro !! (base + Z.of_nat j)%Z) as [b | ] eqn:Hb;
        [ | discriminate ].
      reflexivity.
    - destruct (shk_ro !! (base + Z.of_nat len)%Z) as [b | ] eqn:Hb;
        [ | discriminate ].
      apply Z.eqb_eq in Hnul. f_equal. apply bv_eq. rewrite Hnul.
      vm_compute. reflexivity.
    - iExact "Hro".
  Qed.

End UkShDiagFmt.

Section UkShDiagRun.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context (γt γd γs γfd : gname).

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).

  (* --------------------------------------------------------------------- *)
  (* THE BLOCK gcc EMITTED THREE TIMES, at 0x54 / 0xdc / 0x110:              *)
  (*                                                                        *)
  (*   auipc a1,0x1 ; addi a1,a1,<K> ; c.li a0,2 ; jal <fprintf>            *)
  (*   c.li a0,<k>  ; jal <exit>                                            *)
  (*                                                                        *)
  (* a2 already holds the '%s' argument and nothing here writes it.          *)
  (* PARAMETERISED BY ITS PCS as literals, per the recipe: an [instr] fact   *)
  (* whose address had to be CONVERTED to match would make every [iApply]    *)
  (* reduce a [Z_to_bv] over a program address.                              *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kshd_die (tx : bool) (p0 p1 p2 p3 p4 p5 : Z)
      (hi : mword 20) (lo : mword 12) (j3 j5 : mword 21) (kx : mword 6)
      (fa : Z) (flen fq : nat) (sa : Z) (slen : nat) (sf : nat -> bv 8)
      (h : CpuId) (m : regfile) (n : nat) :
    (* the format, all of it decided from the image *)
    shd_fmt_ok fa flen = true ->
    shd_nopct fa flen fq = true ->
    0 <= fa -> fa + Z.of_nat flen + 2 < 2 ^ 31 ->
    (S (S fq) < flen)%nat ->
    bv_unsigned (shd_lit fa fq) = 37 ->
    bv_unsigned (shd_lit fa (S fq)) = 115 ->
    bv_unsigned (shd_lit fa (S (S fq))) <> 100 ->
    bv_unsigned (shd_lit fa (S (S fq))) <> 117 ->
    bv_unsigned (shd_lit fa (S (S fq))) <> 120 ->
    ((S (S (S fq)) < flen)%nat ->
       bv_unsigned (shd_lit fa (S (S (S fq)))) <> 100 /\
       bv_unsigned (shd_lit fa (S (S (S fq)))) <> 117 /\
       bv_unsigned (shd_lit fa (S (S (S fq)))) <> 120) ->
    (* the pc chain, and the three addresses the block computes *)
    add_vec_int (mword_of_int p0 : mword 64) 4 = mword_of_int p1 ->
    add_vec_int (mword_of_int p1 : mword 64) 4 = mword_of_int p2 ->
    add_vec_int (mword_of_int p2 : mword 64) 2 = mword_of_int p3 ->
    add_vec_int (mword_of_int p3 : mword 64) 4 = mword_of_int p4 ->
    add_vec_int (mword_of_int p4 : mword 64) 2 = mword_of_int p5 ->
    add_vec (add_vec (mword_of_int p0 : mword 64) (auipc_off hi))
            (sign_extend' 64 lo) = mword_of_int fa ->
    add_vec (mword_of_int p3 : mword 64) (sign_extend' 64 j3)
      = mword_of_int ShSyms.fprintf ->
    add_vec (mword_of_int p5 : mword 64) (sign_extend' 64 j5)
      = mword_of_int ShSyms.exit ->
    ret_pc (mword_of_int p4 : mword 64) = mword_of_int p4 ->
    (* the argument *)
    sa <> 0 ->
    m !!! Regidx a2_idx = mword_of_int sa ->
    shk_code γt -∗
    shk_rodata γt -∗
    shd_str γt γd tx sa slen sf -∗
    uinstr_is γt (mword_of_int p0) false (UTYPE (hi, Regidx a1_idx, AUIPC)) -∗
    uinstr_is γt (mword_of_int p1) false
      (ITYPE (lo, Regidx a1_idx, Regidx a1_idx, ADDI)) -∗
    uinstr_is γt (mword_of_int p2) true
      (C_LI (mword_of_int 2 : mword 6, Regidx a0_idx)) -∗
    uinstr_is γt (mword_of_int p3) false (JAL (j3, Regidx ra_idx)) -∗
    uinstr_is γt (mword_of_int p4) true (C_LI (kx, Regidx a0_idx)) -∗
    uinstr_is γt (mword_of_int p5) false (JAL (j5, Regidx ra_idx)) -∗
    urun γt γd γs γfd h m (mword_of_int p0) (10 + (12 + (4 + n))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hok Hnp Hfa0 Hfahi Hq2 Hpq Hps Hc1d Hc1u Hc1x Hc2set
           E0 E1 E2 E3 E4 Efa Ejf Eje Eret Hsanz Ha2.
    iIntros "#Hcode #Hro #Hsstr #Ci0 #Ci1 #Ci2 #Ci3 #Ci4 #Ci5 Hrun".
    iDestruct (shd_fmt_str γt fa flen Hok ltac:(lia) with "Hro") as "#Hfstr".
    (* ---- p0  auipc a1,0x1 ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h m (mword_of_int p0) hi a1_idx
              (add_vec (mword_of_int p0 : mword 64) (auipc_off hi))
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              eq_refl
              with "Ci0 Hrun").
    rewrite E0. iIntros (h1) "Hrun".
    set (m1 := <[Regidx a1_idx
                 := regval_into_reg
                      (add_vec (mword_of_int p0 : mword 64)
                         (auipc_off hi))]> m).
    (* ---- p1  addi a1,a1,<K> ---- *)
    assert (Hva1 : add_vec (m1 !!! Regidx a1_idx) (sign_extend' 64 lo)
                   = mword_of_int fa).
    { rewrite /m1 (upd_eq m (Regidx a1_idx) (regval_into_reg _)). exact Efa. }
    iApply (wp_uk_addi γt γd γs γfd h1 m1 (mword_of_int p1) lo a1_idx a1_idx
              (mword_of_int fa) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              (eq_sym Hva1)
              with "Ci1 Hrun").
    rewrite E1. iIntros (h2) "Hrun".
    set (m2 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int fa : mword 64)]> m1).
    (* ---- p2  c.li a0,2 -- fd = stderr ---- *)
    iApply (wp_uk_cli γt γd γs γfd h2 m2 (mword_of_int p2)
              (mword_of_int 2 : mword 6) a0_idx (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "Ci2 Hrun").
    rewrite E2. iIntros (h3) "Hrun".
    set (m3 := <[Regidx a0_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 2 : mword 6)
                       : mword 64)]> m2).
    (* ---- p3  jal ra,<fprintf> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h3 m3 (mword_of_int p3) j3 ra_idx
              (mword_of_int ShSyms.fprintf) (mword_of_int p4)
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              (eq_sym Ejf) (eq_sym E3)
              ltac:(vm_compute; reflexivity)
              with "Ci3 Hrun").
    iIntros (h4) "Hrun".
    set (m4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int p4 : mword 64)]> m3).
    assert (Hra4 : m4 !!! Regidx ra_idx = (mword_of_int p4 : mword 64))
      by exact (upd_eq m3 (Regidx ra_idx) (regval_into_reg _)).
    assert (Ha1_4 : m4 !!! Regidx a1_idx = mword_of_int fa).
    { rewrite /m4 (upd_ne m3 (Regidx ra_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m3 (upd_ne m2 (Regidx a0_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m2. exact (upd_eq m1 (Regidx a1_idx) (regval_into_reg _)). }
    assert (Ha2_4 : m4 !!! Regidx a2_idx = mword_of_int sa).
    { rewrite /m4 (upd_ne m3 (Regidx ra_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m3 (upd_ne m2 (Regidx a0_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m2 (upd_ne m1 (Regidx a1_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m1 (upd_ne m (Regidx a1_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate)).
      exact Ha2. }
    (* ---- fprintf(2, <fmt>, <the string>) ---- *)
    iApply (wp_kshd_fprintf_s γt γd γs γfd tx fa flen fq (shd_lit fa)
              sa slen sf h4 m4 n
              Hfa0 Hfahi Hq2 Hpq Hps
              (fun j Hj Hne => shd_nopct_ok fa flen fq j Hnp Hj Hne)
              Hc1d Hc1u Hc1x Hc2set Hsanz Ha1_4 Ha2_4
              with "Hcode Hfstr Hsstr Hrun").
    iIntros (h5 m5) "_ Hrun".
    rewrite Hra4 Eret.
    (* ---- p4  c.li a0,<k> ---- *)
    iApply (wp_uk_cli γt γd γs γfd h5 m5 (mword_of_int p4) kx a0_idx
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "Ci4 Hrun").
    rewrite E4. iIntros (h6) "Hrun".
    set (m6 := <[Regidx a0_idx
                 := regval_into_reg
                      (sign_extend' 64 kx : mword 64)]> m5).
    (* ---- p5  jal ra,<exit> -- and it never returns ---- *)
    iApply (wp_uk_jal γt γd γs γfd h6 m6 (mword_of_int p5) j5 ra_idx
              (mword_of_int ShSyms.exit)
              (add_vec_int (mword_of_int p5 : mword 64) 4)
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              (eq_sym Eje) eq_refl
              ltac:(vm_compute; reflexivity)
              with "Ci5 Hrun").
    iIntros (h7) "Hrun".
    iApply (wp_ksh_exit γt γd γs γfd h7 _ (10 + (12 + (4 + n)))
              with "Hcode Hrun").
  Qed.

  (* --------------------------------------------------------------------- *)
  (* panic(s) @0x4a -- fprintf(2, "%s\n", s) ; exit(1).                     *)
  (*                                                                        *)
  (*   c.addi sp,sp,-16 ; c.sdsp ra,8(sp) ; c.sdsp s0,0(sp)                 *)
  (*   c.addi4spn s0,sp,16 ; c.mv a2,a0 ; <the block>                        *)
  (*                                                                        *)
  (* The frame is never given back -- the block ends in [exit] -- so the     *)
  (* two words the push handed over are simply kept, and the ra and s0       *)
  (* it spills are never read.  It is fork1's prologue instruction for       *)
  (* instruction, which is why the two share every constant.                 *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kshd_panic (tx : bool) (sa : Z) (slen : nat) (sf : nat -> bv 8)
      (h : CpuId) (m : regfile) (n : nat) :
    sa <> 0 ->
    m !!! Regidx a0_idx = mword_of_int sa ->
    shk_code γt -∗
    shk_rodata γt -∗
    shd_str γt γd tx sa slen sf -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.panic)
      (2 + (10 + (12 + (4 + n)))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hsanz Ha0.
    iIntros "#Hcode #Hro #Hsstr Hrun".
    rewrite shd_pin_panic.
    iDestruct (urun_stack with "Hrun") as %[Hal8' Hroom'].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0e.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0e).
    clear Hsp0e.
    assert (Hal8 : uint sp0 mod 8 = 0) by exact Hal8'.
    assert (Hlo : 16 <= uint sp0) by (clear -Hroom'; lia).
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                   = bv_unsigned sp0 - 16).
    { replace (- (8 * Z.of_nat 2)) with (-16) by lia.
      exact (uv_avi_neg sp0 16 ltac:(apply Z.leb_le; reflexivity)
               ltac:(rewrite <- uint_unsigned; exact Hlo)). }
    assert (Hsp16 : uint (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                    = uint sp0 - 16)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    assert (Ho0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    (* ---- 0x4a  c.addi sp,sp,-16 ---- *)
    iApply (wp_uk_caddi_sp_dn γt γd γs γfd h m (mword_of_int 0x4a)
              (mword_of_int 48 : mword 6) 2 (10 + (12 + (4 + n)))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_4a with "Hcode"). }
    assert (E4a : add_vec_int (mword_of_int 0x4a : mword 64) 2
                  = mword_of_int 0x4c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp ustack_2 E4a.
    iIntros "(_ & [%v8 Hw8] & [%v16 Hw16])".
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg
                      (add_vec_int sp0 (- (8 * Z.of_nat 2)))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by exact (upd_eq m (Regidx csp_rs1) _).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    (* ---- 0x4c  c.sdsp ra,8(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd h1 m1 (mword_of_int 0x4c)
              (mword_of_int 1 : mword 6) ra_idx (uint sp0 - 8) v8
              (10 + (12 + (4 + n)))
              ltac:(rewrite Hsp1 Hsp16 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw8 Hrun").
    { iApply (uis_shk_4c with "Hcode"). }
    iIntros "Hw8".
    assert (E4c : add_vec_int (mword_of_int 0x4c : mword 64) 2
                  = mword_of_int 0x4e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4c. iIntros (h2) "Hrun".
    (* ---- 0x4e  c.sdsp s0,0(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd h2 m1 (mword_of_int 0x4e)
              (mword_of_int 0 : mword 6) s0_idx (uint sp0 - 16) v16
              (10 + (12 + (4 + n)))
              ltac:(rewrite Hsp1 Hsp16 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw16 Hrun").
    { iApply (uis_shk_4e with "Hcode"). }
    iIntros "Hw16".
    assert (E4e : add_vec_int (mword_of_int 0x4e : mword 64) 2
                  = mword_of_int 0x50)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4e. iIntros (h3) "Hrun".
    (* ---- 0x50  c.addi4spn s0,sp,16 -- s0 is dead from here on ---- *)
    iApply (wp_uk_caddi4spn γt γd γs γfd h3 m1 (mword_of_int 0x50)
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8) s0_idx
              (add_vec (m1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              eq_refl
              with "[] Hrun").
    { iApply (uis_shk_50 with "Hcode"). }
    assert (E50 : add_vec_int (mword_of_int 0x50 : mword 64) 2
                  = mword_of_int 0x52)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E50. iIntros (h4) "Hrun".
    set (m2 := <[Regidx s0_idx
                 := regval_into_reg
                      (add_vec (m1 !!! Regidx csp_rs1)
                         (sign_extend' 64
                            (caddi4spn_imm (mword_of_int 4 : mword 8))))]> m1).
    (* ---- 0x52  c.mv a2,a0 -- the message becomes the vararg ---- *)
    assert (Ha0_2 : m2 !!! Regidx a0_idx = mword_of_int sa).
    { rewrite /m2 (upd_ne m1 (Regidx s0_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    iApply (wp_uk_cmv γt γd γs γfd h4 m2 (mword_of_int 0x52) a2_idx a0_idx
              (add_vec zero_reg (m2 !!! Regidx a0_idx))
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_52 with "Hcode"). }
    assert (E52 : add_vec_int (mword_of_int 0x52 : mword 64) 2
                  = mword_of_int 0x54)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E52. iIntros (h5) "Hrun".
    set (m3 := <[Regidx a2_idx
                 := regval_into_reg
                      (add_vec zero_reg (m2 !!! Regidx a0_idx))]> m2).
    assert (Ha2_3 : m3 !!! Regidx a2_idx = mword_of_int sa).
    { rewrite /m3 (upd_eq m2 (Regidx a2_idx) (regval_into_reg _)).
      rewrite Ha0_2. apply add_vec_zero_l. }
    (* ---- 0x54..0x64  the block: fprintf(2, "%s\n", s) ; exit(1) ---- *)
    iApply (wp_kshd_die tx 0x54 0x58 0x5c 0x5e 0x62 0x64
              (mword_of_int 1 : mword 20) (mword_of_int 572 : mword 12)
              (mword_of_int 4172 : mword 21) (mword_of_int 3106 : mword 21)
              (mword_of_int 1 : mword 6)
              0x1290 3%nat 0%nat sa slen sf h5 m3 n
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(intros HH; exfalso; lia)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hsanz Ha2_3
              with "Hcode Hro Hsstr [] [] [] [] [] [] Hrun").
    { iApply (uis_shk_54 with "Hcode"). }
    { iApply (uis_shk_58 with "Hcode"). }
    { iApply (uis_shk_5c with "Hcode"). }
    { iApply (uis_shk_5e with "Hcode"). }
    { iApply (uis_shk_62 with "Hcode"). }
    { iApply (uis_shk_64 with "Hcode"). }
  Qed.

End UkShDiagRun.

(* ===================================================================== *)
(* §7 THE DISCHARGE, AND THE UNCONDITIONAL COROLLARIES.                   *)
(*                                                                       *)
(* The gname triple is UNIVERSALLY QUANTIFIED here and that is the whole  *)
(* point: three of runcmd's five arms fork, and a child runs its subtree  *)
(* -- diagnostics included -- under a FRESH triple.  So this section      *)
(* binds the gnames rather than taking them from a [Context], exactly as  *)
(* [UkSh.v]'s [UkShLeaf] does for the read leaf.                          *)
(* ===================================================================== *)
Section UkShDiagLeaf.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.

  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).

  (* THE DIAGNOSTIC SUBTREE'S OWN STACK NEED, as the sum of its parts and
     not as a round number: panic's two words, on top of fprintf's ten,
     on top of vprintf's twelve, on top of putc's four.  Nothing below
     putc allocates -- [write] is a three-instruction stub. *)
  Definition ush_Dg : nat := (2 + (10 + (12 + 4)))%nat.

  (* a panic message, as a string in the TEXT half *)
  Local Lemma shd_msg_str (γt γd : gname) (a : Z) (len : nat) :
    shd_fmt_ok a len = true -> Z.of_nat len < 2 ^ 31 ->
    shk_rodata γt -∗ shd_str γt γd true a len (shd_lit a).
  Proof.
    intros Hok Hlen. iIntros "#Hro".
    iApply (shd_str_of_text γt γd a len (shd_lit a)).
    iApply (shd_fmt_str γt a len Hok Hlen with "Hro").
  Qed.

  Lemma ush_diag_leaf_holds :
    forall (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : Z) (n : nat),
      ush_diag_at pc m ->
      shk_code γt -∗
      shk_rodata γt -∗
      ush_diag_res γd pc m -∗
      urun γt γd γs γfd h m (mword_of_int pc) (ush_Dg + n) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    intros γt γd γs h m pc n Hat.
    iIntros "#Hcode #Hro Hres Hrun".
    destruct Hat as [ [-> Hmsg] | [ [-> Hal] | [-> Hal] ] ].
    - (* =============== panic, at one of the three messages =============== *)
      rewrite ush_diag_res_panic.
      replace (ush_Dg + n)%nat with (2 + (10 + (12 + (4 + n))))%nat
        by (unfold ush_Dg; lia).
      (* the message's address is a literal, so its length and its bytes are
         decided; the three cases differ only in which literal it is *)
      assert (Hmoi : forall z : Z,
                       uint (m !!! Regidx a0_idx) = z ->
                       m !!! Regidx a0_idx = (mword_of_int z : mword 64)).
      { intros z Hu. rewrite <- Hu. symmetry. apply moi_of_uint. }
      destruct Hmsg as [Hm1 | [Hm1 | Hm1]].
      + iDestruct (shd_msg_str γt γd 0x1298 4%nat
                     ltac:(vm_compute; reflexivity) ltac:(lia)
                     with "Hro") as "#Hs".
        iApply (wp_kshd_panic γt γd γs γfd true 0x1298 4%nat (shd_lit 0x1298)
                  h m n ltac:(lia)
                  (Hmoi 0x1298 Hm1)
                  with "Hcode Hro Hs Hrun").
      + iDestruct (shd_msg_str γt γd 0x12a0 6%nat
                     ltac:(vm_compute; reflexivity) ltac:(lia)
                     with "Hro") as "#Hs".
        iApply (wp_kshd_panic γt γd γs γfd true 0x12a0 6%nat (shd_lit 0x12a0)
                  h m n ltac:(lia)
                  (Hmoi 0x12a0 Hm1)
                  with "Hcode Hro Hs Hrun").
      + iDestruct (shd_msg_str γt γd 0x12c8 4%nat
                     ltac:(vm_compute; reflexivity) ltac:(lia)
                     with "Hro") as "#Hs".
        iApply (wp_kshd_panic γt γd γs γfd true 0x12c8 4%nat (shd_lit 0x12c8)
                  h m n ltac:(lia)
                  (Hmoi 0x12c8 Hm1)
                  with "Hcode Hro Hs Hrun").
    - (* ================ 0xda: "exec %s failed" ================ *)
      rewrite /ush_diag_res.
      destruct (decide ((0xda : Z) = 0xda)) as [_ | Hc];
        [ | exfalso; exact (Hc eq_refl) ].
      iDestruct "Hres" as (x) "[#Hw [%Hxr #Hxs]]".
      replace (ush_Dg + n)%nat with (10 + (12 + (4 + (n + 2))))%nat
        by (unfold ush_Dg; lia).
      (* ---- 0xda  c.ld a2,8(s1) -- ecmd->argv[0] ---- *)
      iApply (UkShRun.wp_uk_cldq γt γd γs γfd h m (mword_of_int 0xda)
                (mword_of_int 1 : mword 5) (mword_of_int 1 : mword 3)
                (mword_of_int 4 : mword 3) s1_idx a2_idx DfracDiscarded
                (uint (m !!! Regidx s1_idx) + 8) (mword_of_int (ua_ptr x))
                (10 + (12 + (4 + (n + 2))))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute uoff_c8; lia)
                ltac:(rewrite Zplus_mod Hal; reflexivity)
                ltac:(vm_compute; discriminate)
                with "[] Hw Hrun").
      { iApply (uis_shk_da with "Hcode"). }
      iIntros "_".
      assert (Eda : add_vec_int (mword_of_int 0xda : mword 64) 2
                    = mword_of_int 0xdc)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Eda. iIntros (h1) "Hrun".
      set (m1 := <[Regidx a2_idx
                   := regval_into_reg
                        (mword_of_int (ua_ptr x) : mword 64)]> m).
      iDestruct (shd_str_of_ustr γt γd (ua_ptr x) (ua_len x) (ua_bytes x)
                   with "Hxs") as "#Hs".
      iApply (wp_kshd_die γt γd γs γfd false 0xdc 0xe0 0xe4 0xe6 0xea 0xec
                (mword_of_int 1 : mword 20) (mword_of_int 460 : mword 12)
                (mword_of_int 4036 : mword 21) (mword_of_int 2970 : mword 21)
                (mword_of_int 0 : mword 6)
                0x12a8 15%nat 5%nat
                (ua_ptr x) (ua_len x) (ua_bytes x) h1 m1 (n + 2)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(intros _; vm_compute; split_and!; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(lia)
                ltac:(exact (upd_eq m (Regidx a2_idx) (regval_into_reg _)))
                with "Hcode Hro Hs [] [] [] [] [] [] Hrun").
      { iApply (uis_shk_dc with "Hcode"). }
      { iApply (uis_shk_e0 with "Hcode"). }
      { iApply (uis_shk_e4 with "Hcode"). }
      { iApply (uis_shk_e6 with "Hcode"). }
      { iApply (uis_shk_ea with "Hcode"). }
      { iApply (uis_shk_ec with "Hcode"). }
    - (* ================ 0x10e: "open %s failed" ================ *)
      rewrite /ush_diag_res.
      destruct (decide ((0x10e : Z) = 0xda)) as [Hc | _];
        [ exfalso; discriminate Hc | ].
      destruct (decide ((0x10e : Z) = 0x10e)) as [_ | Hc];
        [ | exfalso; exact (Hc eq_refl) ].
      iDestruct "Hres" as (x) "[#Hw [%Hxr #Hxs]]".
      replace (ush_Dg + n)%nat with (10 + (12 + (4 + (n + 2))))%nat
        by (unfold ush_Dg; lia).
      (* ---- 0x10e  c.ld a2,16(s1) -- rcmd->file ---- *)
      iApply (UkShRun.wp_uk_cldq γt γd γs γfd h m (mword_of_int 0x10e)
                (mword_of_int 2 : mword 5) (mword_of_int 1 : mword 3)
                (mword_of_int 4 : mword 3) s1_idx a2_idx DfracDiscarded
                (uint (m !!! Regidx s1_idx) + 16) (mword_of_int (ua_ptr x))
                (10 + (12 + (4 + (n + 2))))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute uoff_c8; lia)
                ltac:(rewrite Zplus_mod Hal; reflexivity)
                ltac:(vm_compute; discriminate)
                with "[] Hw Hrun").
      { iApply (uis_shk_10e with "Hcode"). }
      iIntros "_".
      assert (E10e : add_vec_int (mword_of_int 0x10e : mword 64) 2
                     = mword_of_int 0x110)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E10e. iIntros (h1) "Hrun".
      set (m1 := <[Regidx a2_idx
                   := regval_into_reg
                        (mword_of_int (ua_ptr x) : mword 64)]> m).
      iDestruct (shd_str_of_ustr γt γd (ua_ptr x) (ua_len x) (ua_bytes x)
                   with "Hxs") as "#Hs".
      iApply (wp_kshd_die γt γd γs γfd false 0x110 0x114 0x118 0x11a 0x11e 0x120
                (mword_of_int 1 : mword 20) (mword_of_int 424 : mword 12)
                (mword_of_int 3984 : mword 21) (mword_of_int 2918 : mword 21)
                (mword_of_int 1 : mword 6)
                0x12b8 15%nat 5%nat
                (ua_ptr x) (ua_len x) (ua_bytes x) h1 m1 (n + 2)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(intros _; vm_compute; split_and!; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(lia)
                ltac:(exact (upd_eq m (Regidx a2_idx) (regval_into_reg _)))
                with "Hcode Hro Hs [] [] [] [] [] [] Hrun").
      { iApply (uis_shk_110 with "Hcode"). }
      { iApply (uis_shk_114 with "Hcode"). }
      { iApply (uis_shk_118 with "Hcode"). }
      { iApply (uis_shk_11a with "Hcode"). }
      { iApply (uis_shk_11e with "Hcode"). }
      { iApply (uis_shk_120 with "Hcode"). }
  Qed.

  (* --------------------------------------------------------------------- *)
  (* AND THE TWO STAGE-5 THEOREMS, UNCONDITIONAL.  Both are the landed      *)
  (* lemma applied to [ush_Dg] and to the discharge above; nothing else in  *)
  (* [UkShRun.v] ever carried the Hypothesis.                              *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kshr_runcmd_final (c : ushcmd) :
    forall (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (t szv : Z) (n : nat),
      m !!! Regidx a0_idx = (mword_of_int t : mword 64) ->
      shk_code γt -∗ ush_jtab γt -∗ ush_cmd γd t c -∗ usz γs szv -∗
      urun γt γd γs γfd h m (mword_of_int ShSyms.runcmd)
        (6 * ush_ht c + (2 + (ush_Dg + n))) -∗
      WP (Loop : expr riscv_lang).
  Proof. exact (wp_kshr_runcmd ush_Dg ush_diag_leaf_holds c). Qed.

  Lemma wp_kshr_fork1_final (γt γd γs γfd : gname)
      (P : gname -> gname -> gname -> iProp Σ) `{FP : !Forkable P}
      (szv : Z) (h : CpuId) (m : regfile) (n : nat) :
    shk_code γt -∗ shk_rodata γt -∗ P γt γd γs -∗ usz γs szv -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.fork1) (2 + (ush_Dg + n)) -∗
    ((∀ (h' : CpuId) (m' : regfile) (r : mword 64),
        ⌜ r <> (mword_of_int 0 : mword 64) ⌝ -∗
        ⌜ ucallee_saved m m' ⌝ -∗
        ⌜ m' !!! Regidx a0_idx = r ⌝ -∗
        P γt γd γs -∗ usz γs szv -∗
        urun γt γd γs γfd h' m'
          (ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)))
          (2 + (ush_Dg + n)) -∗
        WP (Loop : expr riscv_lang)) ∗
     (∀ (gt gd gs gfd : gname) (h' : CpuId) (m' : regfile),
        ⌜ ucallee_saved m m' ⌝ -∗
        ⌜ m' !!! Regidx a0_idx = (mword_of_int 0 : mword 64) ⌝ -∗
        shk_code gt -∗ P gt gd gs gfd -∗ usz gs szv -∗
        urun gt gd gs gfd h' m'
          (ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)))
          (2 + (ush_Dg + n)) -∗
        WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    exact (wp_kshr_fork1 ush_Dg ush_diag_leaf_holds γt γd γs γfd P szv h m n).
  Qed.

End UkShDiagLeaf.
