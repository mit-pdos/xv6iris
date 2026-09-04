(* ===================================================================== *)
(* UkShRun.v -- sh's [runcmd] on the urun engine, SH LANE STAGE 5: the     *)
(* COMMAND TREE walk.  [runcmd] (0x8e, 102 instructions) dispatches on the *)
(* node type through the 0x1398 jump table and never returns; its five     *)
(* arms are EXEC, REDIR, PIPE, LIST and BACK, and four of the five call    *)
(* [runcmd] again on a SUBTREE.  [fork1] (0x68) is fork with a panic on    *)
(* -1, and LIST, PIPE and BACK all go through it.                         *)
(*                                                                        *)
(* THE RECURSION IS ORDINARY STRUCTURAL INDUCTION, not an [iLob].  The     *)
(* argument is a FINITE tree -- [ushcmd] below -- so [wp_kshr_runcmd] is   *)
(* proved by [induction c], and each arm applies the induction hypothesis  *)
(* to its child.  What the recursion costs is STACK: one 48-byte frame per *)
(* level, so the budget is [6 * ush_ht c] words plus a constant, and the   *)
(* child's instance of the theorem is the parent's with the surplus rolled *)
(* into the caller-supplied tail [n].                                      *)
(*                                                                        *)
(* THE TREE IS A PREMISE, NOT A PARSE.  [ush_cmd g t c] says: a well-formed *)
(* node of shape [c] sits at address [t].  Stage 4 BUILDS such a node;    *)
(* this file only consumes one, and stage 6 reconciles the two lanes      *)
(* predicates.  Two design points about it:                                *)
(*                                                                        *)
(*  - IT IS PERSISTENT.  Every byte it names is [DfracDiscarded].  That is *)
(*    what the code allows (nothing in runcmd writes a node) and what the  *)
(*    proof NEEDS: three of the five arms fork, and after a fork the child *)
(*    runs a subtree under a FRESH gname triple, so the tree has to cross  *)
(*    as a [UkFork.Forkable] payload -- [ush_cmd_forkable], proved by the  *)
(*    same induction as the walk.                                          *)
(*  - IT PINS THE TYPE WORD, which is what makes the DEFAULT arm dead: the *)
(*    [bltu a5,a4] at 0xa0 tests [5 <u type], and the predicate says the   *)
(*    type is one of 1..5, so [panic("runcmd")] is refuted rather than     *)
(*    walked.                                                             *)
(*                                                                        *)
(* THE DIAGNOSTIC CODE IS CUT HERE AND WALKED IN [UkShDiag.v].  Three      *)
(* places hand control to sh's printer: [panic] (from fork1's -1 arm and   *)
(* from PIPE's [pipe] failure), and the two per-cent-s failed tails inside *)
(* runcmd itself (0xda after a returning [exec], 0x10e after a failing     *)
(* [open]).  All three END IN [exit] and none of them returns, and all     *)
(* three run [fprintf] -- 279 instructions of printf.  [ush_diag_leaf] is  *)
(* that whole subtree as one premise, at the three entry pcs, with exactly *)
(* what each site has in hand; [UkShDiag.ush_diag_leaf_holds] proves it    *)
(* and [UkShDiag.wp_kshr_runcmd_final] / [_fork1_final] are the two        *)
(* theorems below with it supplied.                                        *)
(*                                                                        *)
(* WHAT DISCHARGING IT COST THIS FILE, and it is worth knowing why: the    *)
(* premise as first written handed the walk only [shk_code], which is      *)
(* [ShInstrs.sh_bytes] -- the INSTRUCTIONS.  The format strings are at     *)
(* 0x1290..0x12c7, i.e. in [ShData.sh_data], and panic's own '%s' argument *)
(* is a .rodata literal too, so no amount of [shk_code] produces them: the *)
(* premise was not dischargeable, and its ∀ over the gname triple (a       *)
(* forked child runs it at FRESH names) meant no caller could supply the   *)
(* image from outside either.  The fix is one conjunct threaded where      *)
(* [ush_jtab] already goes -- [ush_jtab] now carries [shk_rodata] beside   *)
(* the five rows, so [wp_kshr_runcmd]'s statement, all four fork payloads  *)
(* and every budget are exactly where stage 5 left them.  [wp_kshr_fork1]  *)
(* is the one exception: it has no [ush_jtab] of its own, so it takes      *)
(* [shk_rodata γt] as a premise and forwards it to the child through the   *)
(* payload it already carries.  The second short conjunct was the two      *)
(* tails' first instruction, [c.ld a2,<k>(s1)], which is 8-aligned or it   *)
(* is not a step at all -- so [ush_diag_at] now names the node's alignment *)
(* alongside the pc, which both sites read off [ush_cmd].                  *)
(*                                                                        *)
(* FOUR LANE LEAVES, all of them one-line generalisations of UkRunMem's.   *)
(* [wp_uk_cldq]/[wp_uk_clwq]/[wp_uk_lwuq] are [wp_uk_cld]/[wp_uk_clw]/     *)
(* [wp_uk_lwu] at a DFRAC: those three are stated at [DfracOwn 1] though   *)
(* their proofs are dfrac-generic ([uheap_access] already takes a [dq],    *)
(* and [wp_uk_ld]/[wp_uk_lbu] already expose it), and a persistent tree    *)
(* cannot be read without them.  [wp_uk_clw_text] is the FOURTH, and it is *)
(* a real gap rather than a spelling: the jump table at 0x1398 is .rodata, *)
(* which the heap files under [gt] as X-and-not-W, and the tier's only     *)
(* text reader is [wp_uk_lbu_text] -- one byte wide.  RELOCATION ASK,      *)
(* beside [UkRunBr.wp_uk_btype0]'s.                                        *)
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
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 THE COMMAND TREE, AS DATA.                                          *)
(*                                                                        *)
(* sh.c's five node kinds, with exactly the fields runcmd READS.  An EXEC  *)
(* node's argument vector is [UserHeap.uarg]s -- the tier's own            *)
(* pointer-and-string record, which is what [uargv] and its [Forkable]     *)
(* instance are already written for; runcmd itself only ever looks at      *)
(* [argv[0]], but the whole vector is what the node IS and what stage 6's  *)
(* exec statement will want.                                              *)
(* ===================================================================== *)
Inductive ushcmd : Type :=
  | UExec  (args : list uarg)
  | URedir (c : ushcmd) (file : uarg) (mode fd : Z)
  | UPipe  (l r : ushcmd)
  | UList  (l r : ushcmd)
  | UBack  (c : ushcmd).

(* THE MEASURE: the tree's height, which is the depth of the runcmd call
   chain and so the number of 48-byte frames the walk needs.  BACK and the
   child arm of LIST/PIPE recurse without returning, so nothing is ever
   given back -- the budget is a height, not a size. *)
Fixpoint ush_ht (c : ushcmd) : nat :=
  match c with
  | UExec _ => 1%nat
  | URedir c1 _ _ _ => S (ush_ht c1)
  | UPipe l r => S (Nat.max (ush_ht l) (ush_ht r))
  | UList l r => S (Nat.max (ush_ht l) (ush_ht r))
  | UBack c1 => S (ush_ht c1)
  end.

Lemma ush_ht_pos (c : ushcmd) : (1 <= ush_ht c)%nat.
Proof. destruct c; cbn; lia. Qed.

(* the [int] the node's type word holds, one per constructor -- sh.c's
   EXEC 1, REDIR 2, PIPE 3, LIST 4, BACK 5 *)
Definition ush_ty (c : ushcmd) : Z :=
  match c with
  | UExec _ => 1 | URedir _ _ _ _ => 2 | UPipe _ _ => 3
  | UList _ _ => 4 | UBack _ => 5
  end.

Lemma ush_ty_range (c : ushcmd) : 1 <= ush_ty c <= 5.
Proof. destruct c; cbn; lia. Qed.

(* THE JUMP TABLE at 0x1398 (.rodata), read as six SIGNED 32-bit
   displacements from the table's own base.  The six values are the dump's
   ([user-rocq/ShData.v], 0x1398..0x13af); the arm each one names is
   [ush_jarm] below and every one of those is checked by [vm_compute]
   against the pc the walk actually continues at. *)
Definition SH_JTAB : Z := 0x1398.

Definition ush_jent (k : Z) : mword 32 :=
  mword_of_int
    (if Z.eqb k 1 then 0xffffed36
     else if Z.eqb k 2 then 0xffffed5e
     else if Z.eqb k 3 then 0xffffeda4
     else if Z.eqb k 4 then 0xffffed8c
     else if Z.eqb k 5 then 0xffffee2c
     else 0xffffed2a).

(* ...and the pc the [add a5,a5,a4 ; jr a5] pair lands on. *)
Definition ush_jarm (c : ushcmd) : Z :=
  match c with
  | UExec _ => 0xce | URedir _ _ _ _ => 0xf6 | UPipe _ _ => 0x13c
  | UList _ _ => 0x124 | UBack _ => 0x1c4
  end.

Require Import FdSlots.   (* [fdstate] / [fdtype] -- pipe's two ends *)
Require Import ProcGeom.  (* [NOFILE] -- pipe's two slots are slots *)
Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)
Section UkShRun.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.

  (* THE DIAGNOSTIC CODE'S OWN STACK NEED.  [ush_diag_leaf] below is the      *)
  (* whole printf-and-exit subtree as one premise; whoever discharges it      *)
  (* fixes this constant, and every budget in the file carries it.           *)
  Context (Dg : nat).

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* ===================================================================== *)
  (* §1a THE SYMBOL PINS.  [shk_syms_pins] grows a clause per stage, so it  *)
  (* is destructed ONCE, here, exactly as UkSh.v does for stages 1-2.       *)
  (* ===================================================================== *)
  Local Lemma shr_exit   : ShSyms.exit   = 0xc86.
  Proof. destruct shk_syms_pins as (_&_&_&_&_&_&_&H&_). exact H. Qed.
  Local Lemma shr_runcmd : ShSyms.runcmd = 0x8e.
  Proof. destruct shk_syms_pins as (_&_&_&_&_&_&_&_&_&_&H&_). exact H. Qed.
  Local Lemma shr_fork1  : ShSyms.fork1  = 0x68.
  Proof. destruct shk_syms_pins as (_&_&_&_&_&_&_&_&_&_&_&H&_). exact H. Qed.
  Local Lemma shr_fork   : ShSyms.fork   = 0xc7e.
  Proof. destruct shk_syms_pins as (_&_&_&_&_&_&_&_&_&_&_&_&H&_). exact H. Qed.
  Local Lemma shr_exec   : ShSyms.exec   = 0xcbe.
  Proof. destruct shk_syms_pins as (_&_&_&_&_&_&_&_&_&_&_&_&_&H&_). exact H. Qed.
  Local Lemma shr_pipe   : ShSyms.pipe   = 0xc96.
  Proof. destruct shk_syms_pins as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&H&_). exact H. Qed.
  Local Lemma shr_wait   : ShSyms.wait   = 0xc8e.
  Proof. destruct shk_syms_pins as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&H&_). exact H. Qed.
  Local Lemma shr_dup    : ShSyms.dup    = 0xcfe.
  Proof. destruct shk_syms_pins as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&H&_). exact H. Qed.
  Local Lemma shr_panic  : ShSyms.panic  = 0x4a.
  Proof. reflexivity. Qed.

  (* ===================================================================== *)
  (* §2 THE NODE PREDICATE.                                                 *)
  (* ===================================================================== *)

  (* a 4-byte field, read-only: the type word, and REDIR's mode and fd *)
  Definition ush_w32 (g : gname) (a v : Z) : iProp Σ :=
    ubytesq g DfracDiscarded a 4 (nth_byte (mword_of_int v : mword 32)).

  (* a read-only pointer slot *)
  Definition ush_ptr (g : gname) (a p : Z) : iProp Σ :=
    uwordq g DfracDiscarded a (mword_of_int p).

  (* a read-only NUL-terminated string, at an address a program may test *)
  Definition ush_str (g : gname) (x : uarg) : iProp Σ :=
    (⌜ 0 < ua_ptr x < 2 ^ 38 ⌝ ∗
     ustr g DfracDiscarded (ua_ptr x) (ua_len x) (ua_bytes x))%I.

  (* THE TREE.  Structural in [c]; every byte [DfracDiscarded], so the whole
     thing is persistent and crosses a fork as a payload. *)
  Fixpoint ush_cmd (g : gname) (t : Z) (c : ushcmd) : iProp Σ :=
    (⌜ 0 < t < 2 ^ 38 ⌝ ∗ ⌜ t mod 8 = 0 ⌝ ∗
     ush_w32 g t (ush_ty c) ∗
     match c with
     | UExec args =>
         (* [argv] at t+8, [eargv] at t+88; runcmd reads argv[0] and hands
            [&argv[0]] to exec, so the vector and its NUL are the node. *)
         uargv g (t + 8) args ∗
         ush_ptr g (t + 8 + 8 * Z.of_nat (length args)) 0 ∗
         ([∗ list] x ∈ args, ush_str g x)
     | URedir c1 file mode fd =>
         (∃ q : Z, ush_ptr g (t + 8) q ∗ ush_cmd g q c1) ∗
         ush_ptr g (t + 16) (ua_ptr file) ∗ ush_str g file ∗
         ush_w32 g (t + 32) mode ∗ ush_w32 g (t + 36) fd
     | UPipe l r =>
         (∃ q : Z, ush_ptr g (t + 8) q ∗ ush_cmd g q l) ∗
         (∃ q : Z, ush_ptr g (t + 16) q ∗ ush_cmd g q r)
     | UList l r =>
         (∃ q : Z, ush_ptr g (t + 8) q ∗ ush_cmd g q l) ∗
         (∃ q : Z, ush_ptr g (t + 16) q ∗ ush_cmd g q r)
     | UBack c1 =>
         (∃ q : Z, ush_ptr g (t + 8) q ∗ ush_cmd g q c1)
     end)%I.

  Global Instance ush_w32_persistent g a v : Persistent (ush_w32 g a v).
  Proof. apply _. Qed.
  Global Instance ush_ptr_persistent g a p : Persistent (ush_ptr g a p).
  Proof. apply _. Qed.
  Global Instance ush_str_persistent g x : Persistent (ush_str g x).
  Proof. apply _. Qed.

  Global Instance ush_cmd_persistent g t c : Persistent (ush_cmd g t c).
  Proof.
    revert t. induction c as [ args | c1 IH file mode fd | l IHl r IHr
                             | l IHl r IHr | c1 IH ]; intros t; cbn; apply _.
  Qed.

  Lemma ush_cmd_addr (g : gname) (t : Z) (c : ushcmd) :
    ush_cmd g t c -∗ ⌜ 0 < t < 2 ^ 38 /\ t mod 8 = 0 ⌝.
  Proof. destruct c; iIntros "(%H1 & %H2 & _)"; iPureIntro; done. Qed.

  Lemma ush_cmd_type (g : gname) (t : Z) (c : ushcmd) :
    ush_cmd g t c -∗ ush_w32 g t (ush_ty c).
  Proof. destruct c; iIntros "(_ & _ & #H & _)"; iExact "H". Qed.

  (* ===================================================================== *)
  (* §2a THE TREE CROSSES A FORK.  Every conjunct is one of the class's     *)
  (* read-only instances, so the induction is mechanical -- but it IS an    *)
  (* induction, which is why this cannot be an [Instance].                  *)
  (* ===================================================================== *)
  Lemma forkable_ush_w32 (a v : Z) :
    Forkable (fun _ g _ => ush_w32 g a v).
  Proof. apply forkable_ubytesq_disc. Qed.

  Lemma forkable_ush_ptr (a p : Z) :
    Forkable (fun _ g _ => ush_ptr g a p).
  Proof. apply forkable_uwordq_disc. Qed.

  Lemma forkable_ush_str (x : uarg) :
    Forkable (fun _ g _ => ush_str g x).
  Proof.
    apply forkable_sep; [ apply forkable_pure | apply forkable_ustr_disc ].
  Qed.

  Lemma ush_cmd_forkable (t : Z) (c : ushcmd) :
    Forkable (fun _ g _ => ush_cmd g t c).
  Proof.
    revert t.
    induction c as [ args | c1 IH file mode fd | l IHl r IHr
                   | l IHl r IHr | c1 IH ]; intros t.
    - apply forkable_sep; [ apply forkable_pure | ].
      apply forkable_sep; [ apply forkable_pure | ].
      apply forkable_sep; [ apply forkable_ush_w32 | ].
      apply forkable_sep; [ apply forkable_uargv | ].
      apply forkable_sep; [ apply forkable_ush_ptr | ].
      apply (forkable_big_sepL args (fun _ x _ g _ => ush_str g x)).
      intros _ x. apply forkable_ush_str.
    - apply forkable_sep; [ apply forkable_pure | ].
      apply forkable_sep; [ apply forkable_pure | ].
      apply forkable_sep; [ apply forkable_ush_w32 | ].
      apply forkable_sep.
      { apply forkable_exist. intros q.
        apply forkable_sep; [ apply forkable_ush_ptr | apply IH ]. }
      apply forkable_sep; [ apply forkable_ush_ptr | ].
      apply forkable_sep; [ apply forkable_ush_str | ].
      apply forkable_sep; apply forkable_ush_w32.
    - apply forkable_sep; [ apply forkable_pure | ].
      apply forkable_sep; [ apply forkable_pure | ].
      apply forkable_sep; [ apply forkable_ush_w32 | ].
      apply forkable_sep;
        (apply forkable_exist; intros q;
         apply forkable_sep; [ apply forkable_ush_ptr | ]);
        [ apply IHl | apply IHr ].
    - apply forkable_sep; [ apply forkable_pure | ].
      apply forkable_sep; [ apply forkable_pure | ].
      apply forkable_sep; [ apply forkable_ush_w32 | ].
      apply forkable_sep;
        (apply forkable_exist; intros q;
         apply forkable_sep; [ apply forkable_ush_ptr | ]);
        [ apply IHl | apply IHr ].
    - apply forkable_sep; [ apply forkable_pure | ].
      apply forkable_sep; [ apply forkable_pure | ].
      apply forkable_sep; [ apply forkable_ush_w32 | ].
      apply forkable_exist. intros q.
      apply forkable_sep; [ apply forkable_ush_ptr | apply IH ].
  Qed.

  (* ===================================================================== *)
  (* §2b THE JUMP TABLE, as a resource: five rows of four TEXT bytes.  Only *)
  (* the five rows a well-formed node can select are here; row 0 is the     *)
  (* default arm's, and the node predicate makes it unreachable.            *)
  (* ===================================================================== *)
  Definition ush_jrow (g : gname) (k : Z) : iProp Σ :=
    ([∗ list] j ∈ seq 0 4,
       utext g (SH_JTAB + 4 * k + Z.of_nat j) (nth_byte (ush_jent k) j))%I.

  (* ...AND SH'S READ-ONLY IMAGE BESIDE THEM.  The jump table IS .rodata
     (0x1398 is inside [ShData.sh_data]), so the two belong together, and
     what makes it worth saying is the DIAGNOSTIC CUT below: every site that
     reaches sh's printer needs the three format strings, which are .rodata
     too, and every one of those sites already carries [ush_jtab] -- through
     the recursion, through each arm, and across every fork, since the whole
     thing is [Forkable].  Carrying the image here rather than as a sixth
     premise is what keeps [wp_kshr_runcmd]'s statement, all four fork
     payloads and every budget exactly where stage 5 left them. *)
  Definition ush_jtab (g : gname) : iProp Σ :=
    (ush_jrow g 1 ∗ ush_jrow g 2 ∗ ush_jrow g 3 ∗
     ush_jrow g 4 ∗ ush_jrow g 5 ∗ shk_rodata g)%I.

  Global Instance ush_jrow_persistent g k : Persistent (ush_jrow g k).
  Proof. apply _. Qed.
  Global Instance ush_jtab_persistent g : Persistent (ush_jtab g).
  Proof. apply _. Qed.

  Lemma forkable_ush_jrow (k : Z) :
    Forkable (fun g _ _ => ush_jrow g k).
  Proof. apply forkable_utext_run. Qed.

  Lemma forkable_shk_code : Forkable (fun g _ _ => shk_code g).
  Proof.
    eapply Forkable_ext; [ | apply (forkable_utext_map ShInstrs.sh_bytes) ].
    intros g gd gs. rewrite /shk_code /utext_img. reflexivity.
  Qed.

  Lemma forkable_shk_rodata : Forkable (fun g _ _ => shk_rodata g).
  Proof.
    eapply Forkable_ext; [ | apply (forkable_utext_map shk_ro) ].
    intros g gd gs. rewrite /shk_rodata /utext_img. reflexivity.
  Qed.

  Lemma forkable_ush_jtab : Forkable (fun g _ _ => ush_jtab g).
  Proof.
    apply forkable_sep; [ apply forkable_ush_jrow | ].
    apply forkable_sep; [ apply forkable_ush_jrow | ].
    apply forkable_sep; [ apply forkable_ush_jrow | ].
    apply forkable_sep; [ apply forkable_ush_jrow | ].
    apply forkable_sep; [ apply forkable_ush_jrow | ].
    apply forkable_shk_rodata.
  Qed.

  (* the row a node selects, and the entry it holds *)
  Lemma ush_jtab_row (g : gname) (c : ushcmd) :
    ush_jtab g -∗ ush_jrow g (ush_ty c).
  Proof.
    destruct c; cbn [ush_ty];
      iIntros "(#H1 & #H2 & #H3 & #H4 & #H5 & _)";
      [ iExact "H1" | iExact "H2" | iExact "H3" | iExact "H4" | iExact "H5" ].
  Qed.

  (* ...and the image it carries *)
  Lemma ush_jtab_ro (g : gname) : ush_jtab g -∗ shk_rodata g.
  Proof. iIntros "(_ & _ & _ & _ & _ & #H)". iExact "H". Qed.

  (* ===================================================================== *)
  (* §3 FOUR LANE LEAVES.                                                   *)
  (*                                                                        *)
  (* The first three are UkRunMem's [wp_uk_cld]/[wp_uk_clw]/[wp_uk_lwu] at  *)
  (* an arbitrary DFRAC.  Those three are stated at [DfracOwn 1] though     *)
  (* their bridge ([uheap_access]) already takes a [dq] and their base-form *)
  (* siblings ([wp_uk_ld], [wp_uk_lbu]) already expose it -- so the         *)
  (* generalisation is the same proof with [dq] threaded, and without it a  *)
  (* READ-ONLY data structure cannot be read at all.  RELOCATION ASK.       *)
  (* ===================================================================== *)
  Local Lemma wp_uk_cldq (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (uimm : mword 5) (crs1 crd : mword 3) (rs1 rd : mword 5) (dq : dfrac)
      (a : Z) (w : mword 64) (avail : nat) :
    unot_sp rd ->
    creg2reg_idx (Cregidx crs1) = Regidx rs1 ->
    creg2reg_idx (Cregidx crd) = Regidx rd ->
    a = uint (m !!! Regidx rs1) + uoff_c8 uimm ->
    a mod 8 = 0 ->
    uint rd <> 0 ->
    uinstr_is γt pc true (C_LD (uimm, Cregidx crs1, Cregidx crd)) -∗
    uwordq γd dq a w -∗
    urun γt γd γs γfd h m pc avail -∗
    (uwordq γd dq a w -∗
       ∀ h' : CpuId,
         urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg w]> m)
           (add_vec_int pc 2) avail -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns He1 He2 Ha Hal Hrd. iIntros "#Hi Hw Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uheap_access γt γd γs M pm dq a 8 (nth_byte w)
                 ltac:(lia) ltac:(right; right; right; reflexivity) Hal
                 with "Hheap Hw")
      as %(Hua & Hcan & Hok & Hpg & Hal8 & Hmap).
    assert (Htgt : (mword_of_int a : mword 64)
                   = add_vec (m !!! Regidx rs1)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec uimm ('b"000"))))).
    { rewrite Ha /uoff_c8. rewrite <- moi_add. rewrite !moi_of_uint.
      reflexivity. }
    iApply (UkLoad.wp_uk_cld C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv cw uimm crs1 crd rs1 rd
              (mword_of_int a) w Hui He1 He2 Hrd Htgt
              ltac:(destruct Hok as (q & Hq & _); exists q; exact Hq)
              Hcan Hpg Hal8
              ltac:(rewrite Hua; exact Hmap)
              with "Hb [Hheap Hstk Hufd Hw Hcont]").
    iApply (urun_close_upd _ _ _ _ _ _ m rd _ _ _ _ _ _ Hns with "Hheap Hstk Hufd").
    iApply ("Hcont" with "Hw").
  Qed.

  Local Lemma wp_uk_clwq (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (uimm : mword 5) (crs1 crd : mword 3) (rs1 rd : mword 5) (dq : dfrac)
      (a : Z) (wv : mword 32) (avail : nat) :
    unot_sp rd ->
    creg2reg_idx (Cregidx crs1) = Regidx rs1 ->
    creg2reg_idx (Cregidx crd) = Regidx rd ->
    a = uint (m !!! Regidx rs1) + uoff_c4 uimm ->
    a mod 4 = 0 ->
    uint rd <> 0 ->
    uinstr_is γt pc true (C_LW (uimm, Cregidx crs1, Cregidx crd)) -∗
    ubytesq γd dq a 4 (nth_byte wv) -∗
    urun γt γd γs γfd h m pc avail -∗
    (ubytesq γd dq a 4 (nth_byte wv) -∗
       ∀ h' : CpuId,
         urun γt γd γs γfd h'
           (<[Regidx rd := regval_into_reg (sign_extend' 64 wv)]> m)
           (add_vec_int pc 2) avail -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns He1 He2 Ha Hal Hrd. iIntros "#Hi Hw Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uheap_access γt γd γs M pm dq a 4 (nth_byte wv)
                 ltac:(lia) ltac:(right; right; left; reflexivity) Hal
                 with "Hheap Hw")
      as %(Hua & Hcan & Hok & Hpg & Hal8 & Hmap).
    assert (Htgt : (mword_of_int a : mword 64)
                   = add_vec (m !!! Regidx rs1)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec uimm ('b"00"))))).
    { rewrite Ha /uoff_c4. rewrite <- moi_add. rewrite !moi_of_uint.
      reflexivity. }
    iApply (UkLoad.wp_uk_clw C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv cw uimm crs1 crd rs1 rd
              (mword_of_int a) (sign_extend' 64 wv) wv Hui He1 He2 Hrd Htgt
              ltac:(destruct Hok as (q & Hq & _); exists q; exact Hq)
              Hcan Hpg Hal8
              ltac:(rewrite Hua; exact Hmap) eq_refl
              with "Hb [Hheap Hstk Hufd Hw Hcont]").
    iApply (urun_close_upd _ _ _ _ _ _ m rd _ _ _ _ _ _ Hns with "Hheap Hstk Hufd").
    iApply ("Hcont" with "Hw").
  Qed.

  Local Lemma wp_uk_lwuq (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (dq : dfrac) (a : Z)
      (wv : mword 32) (avail : nat) :
    unot_sp rd ->
    a = uint (m !!! Regidx rs1) + uoff_i12 imm ->
    a mod 4 = 0 ->
    uint rd <> 0 ->
    uinstr_is γt pc false (LOAD (imm, Regidx rs1, Regidx rd, true, 4)) -∗
    ubytesq γd dq a 4 (nth_byte wv) -∗
    urun γt γd γs γfd h m pc avail -∗
    (ubytesq γd dq a 4 (nth_byte wv) -∗
       ∀ h' : CpuId,
         urun γt γd γs γfd h'
           (<[Regidx rd := regval_into_reg (zero_extend' 64 wv)]> m)
           (add_vec_int pc 4) avail -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns Ha Hal Hrd. iIntros "#Hi Hw Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uheap_access γt γd γs M pm dq a 4 (nth_byte wv)
                 ltac:(lia) ltac:(right; right; left; reflexivity) Hal
                 with "Hheap Hw")
      as %(Hua & Hcan & Hok & Hpg & Hal8 & Hmap).
    assert (Htgt : (mword_of_int a : mword 64)
                   = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
    { exact (umoi_add_i12 _ imm a Ha). }
    iApply (UkLoad.wp_uk_lwu C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv cw imm rs1 rd
              (mword_of_int a) (zero_extend' 64 wv) wv Hui Hrd Htgt
              ltac:(destruct Hok as (q & Hq & _); exists q; exact Hq)
              Hcan Hpg Hal8
              ltac:(rewrite Hua; exact Hmap) eq_refl
              with "Hb [Hheap Hstk Hufd Hw Hcont]").
    iApply (urun_close_upd _ _ _ _ _ _ m rd _ _ _ _ _ _ Hns with "Hheap Hstk Hufd").
    iApply ("Hcont" with "Hw").
  Qed.

  (* ...and the FOURTH, which is not a spelling but a gap: a FOUR-byte load
     out of the TEXT half.  .rodata shares the executable segment's pages,
     so the heap files it under [γt] as X-and-not-W, and the only text
     reader the tier has is [wp_uk_lbu_text] -- one byte.  runcmd's jump
     table is four bytes wide and is read by a COMPRESSED lw. *)
  Local Lemma wp_uk_clw_text (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (uimm : mword 5) (crs1 crd : mword 3) (rs1 rd : mword 5) (a : Z)
      (wv : mword 32) (avail : nat) :
    unot_sp rd ->
    creg2reg_idx (Cregidx crs1) = Regidx rs1 ->
    creg2reg_idx (Cregidx crd) = Regidx rd ->
    a = uint (m !!! Regidx rs1) + uoff_c4 uimm ->
    a mod 4 = 0 ->
    uint rd <> 0 ->
    uinstr_is γt pc true (C_LW (uimm, Cregidx crs1, Cregidx crd)) -∗
    ([∗ list] j ∈ seq 0 4, utext γt (a + Z.of_nat j) (nth_byte wv j)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h'
         (<[Regidx rd := regval_into_reg (sign_extend' 64 wv)]> m)
         (add_vec_int pc 2) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns He1 He2 Ha Hal Hrd. iIntros "#Hi #Hw Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uheap_text_run γt γd γs M pm a 4%nat wv with "Hheap Hw")
      as %Hmap.
    iAssert (utext γt (a + Z.of_nat 0%nat) (nth_byte wv 0%nat)) as "Hw0".
    { iApply (big_sepL_lookup _ (seq 0 4) 0%nat 0%nat with "Hw").
      reflexivity. }
    assert (Ea0 : (a + Z.of_nat 0%nat)%Z = a) by lia.
    iEval (rewrite Ea0) in "Hw0".
    iDestruct (uheap_text with "Hheap Hw0") as %(_ & Hok & Hbnd).
    destruct (ucanon_of_bound a Hbnd) as [Hua Hcan].
    destruct (uaccess_arith a 4 ltac:(lia)
                ltac:(right; right; left; reflexivity) Hal) as [Hpg Hrm].
    assert (Htgt : (mword_of_int a : mword 64)
                   = add_vec (m !!! Regidx rs1)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec uimm ('b"00"))))).
    { rewrite Ha /uoff_c4. rewrite <- moi_add. rewrite !moi_of_uint.
      reflexivity. }
    iApply (UkLoad.wp_uk_clw C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv cw uimm crs1 crd rs1 rd
              (mword_of_int a) (sign_extend' 64 wv) wv Hui He1 He2 Hrd Htgt
              ltac:(destruct Hok as (q & Hq & _); exists q; exact Hq) Hcan
              ltac:(rewrite Hua; exact Hpg)
              ltac:(unfold is_aligned_vaddr; apply Z.eqb_eq; rewrite Hua;
                    exact Hrm)
              ltac:(rewrite Hua; exact Hmap) eq_refl
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close_upd _ _ _ _ _ _ m rd _ _ _ _ _ _ Hns with "Hheap Hstk Hufd").
    iApply "Hcont".
  Qed.

  (* ===================================================================== *)
  (* §4 CALLS.  Every call in runcmd and fork1 is [jal ra,<sym>] followed   *)
  (* by a three-instruction usys.S stub or by a function that never         *)
  (* returns, so two combinators cover the file: the [jal] itself, and      *)
  (* [jal] + a QUIET stub + its [c.jr ra], which is the whole ABI a caller  *)
  (* sees (callee-saved registers preserved, the result in a0).             *)
  (* ===================================================================== *)
  Local Lemma ushr_ridx_ne (r q : mword 5) :
    uint r <> uint q -> Regidx r <> Regidx q.
  Proof.
    intros H He. apply H.
    assert (Hrq : r = q) by (injection He; trivial). rewrite Hrq. reflexivity.
  Qed.

  Local Lemma ushr_ridx_eq (r q : mword 5) :
    uint r = uint q -> Regidx r = Regidx q.
  Proof.
    intros H. f_equal. apply bv_eq. rewrite <- !(uint_unsigned_n 5). exact H.
  Qed.

  Local Lemma ushr_cs_bounds (q : mword 5) :
    ucallee_saved_idx q = true ->
    uint q = 2 \/ uint q = 3 \/ uint q = 4 \/ uint q = 8 \/ uint q = 9 \/
    (18 <= uint q <= 27).
  Proof.
    unfold ucallee_saved_idx. cbv zeta. intros H.
    repeat (apply orb_true_iff in H as [H | H]).
    all: first [ apply Z.eqb_eq in H; lia
               | apply andb_true_iff in H as [H1 H2];
                 apply Z.leb_le in H1; apply Z.leb_le in H2; lia ].
  Qed.

  (* a callee-saved index is none of ra, a0, a1, a2, a7 -- the five a call
     sequence writes.  Stated over the VALUE so the caller says which. *)
  Local Lemma ushr_cs_ne (q r : mword 5) :
    ucallee_saved_idx q = true ->
    (uint r = 1 \/ uint r = 10 \/ uint r = 11 \/ uint r = 12 \/ uint r = 17) ->
    Regidx q <> Regidx r.
  Proof.
    intros Hq Hr. apply ushr_ridx_ne.
    destruct (ushr_cs_bounds q Hq) as [E | [E | [E | [E | [E | E]]]]];
      destruct Hr as [Er | [Er | [Er | [Er | Er]]]]; lia.
  Qed.

  Local Lemma wp_kshr_jal (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc tgt ret : Z)
      (imm : mword 21) (avail : nat) :
    (mword_of_int tgt : mword 64)
      = add_vec (mword_of_int pc : mword 64) (sign_extend' 64 imm) ->
    (mword_of_int ret : mword 64) = add_vec_int (mword_of_int pc : mword 64) 4 ->
    eq_vec (access_vec_dec (mword_of_int tgt : mword 64) 0) ('b"0") = true ->
    uinstr_is γt (mword_of_int pc) false (JAL (imm, Regidx ra_idx)) -∗
    urun γt γd γs γfd h m (mword_of_int pc) avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h'
         (<[Regidx ra_idx := (mword_of_int ret : mword 64)]> m)
         (mword_of_int tgt) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Htgt Hret Hal. iIntros "#Hi Hrun Hcont".
    iApply (wp_uk_jal γt γd γs γfd h m (mword_of_int pc) imm ra_idx
              (mword_of_int tgt) (mword_of_int ret) avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              Htgt Hret Hal with "Hi Hrun Hcont").
  Qed.

  (* the ABI, off a quiet stub's exact postcondition *)
  Local Lemma wp_kshr_qcall (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc sym ret num : Z)
      (imm : mword 21) (avail : nat)
      (Hstub : forall (h0 : CpuId) (m0 : regfile) (av : nat),
         shk_code γt -∗
         urun γt γd γs γfd h0 m0 (mword_of_int sym) av -∗
         (∀ (h1 : CpuId) (r : mword 64),
            urun γt γd γs γfd h1
              (<[Regidx a0_idx := r]>
                 (<[Regidx a7_idx := (mword_of_int num : mword 64)]> m0))
              (ret_pc (m0 !!! Regidx ra_idx)) av -∗
            WP (Loop : expr riscv_lang)) -∗
         WP (Loop : expr riscv_lang)) :
    (mword_of_int sym : mword 64)
      = add_vec (mword_of_int pc : mword 64) (sign_extend' 64 imm) ->
    (mword_of_int ret : mword 64) = add_vec_int (mword_of_int pc : mword 64) 4 ->
    eq_vec (access_vec_dec (mword_of_int sym : mword 64) 0) ('b"0") = true ->
    ret_pc (mword_of_int ret : mword 64) = mword_of_int ret ->
    shk_code γt -∗
    uinstr_is γt (mword_of_int pc) false (JAL (imm, Regidx ra_idx)) -∗
    urun γt γd γs γfd h m (mword_of_int pc) avail -∗
    (∀ (h' : CpuId) (m' : regfile) (r : mword 64),
       ⌜ ucallee_saved m m' ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = r ⌝ -∗
       urun γt γd γs γfd h' m' (mword_of_int ret) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hsym Hret Hal Hrp. iIntros "#Hcode #Hi Hrun Hcont".
    iApply (wp_kshr_jal γt γd γs γfd h m pc sym ret imm avail Hsym Hret Hal
              with "Hi Hrun").
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx ra_idx := (mword_of_int ret : mword 64)]> m).
    assert (Hra1 : m1 !!! Regidx ra_idx = (mword_of_int ret : mword 64))
      by exact (upd_eq m (Regidx ra_idx) _).
    iApply (Hstub h1 m1 avail with "Hcode Hrun").
    iIntros (h2 r) "Hrun". rewrite Hra1 Hrp.
    iApply ("Hcont" $! h2 _ r with "[%] [%] Hrun").
    - intros q Hq.
      rewrite (upd_ne _ (Regidx a0_idx) (Regidx q) r
                 (ushr_cs_ne q a0_idx Hq
                    ltac:(right; left; vm_compute; reflexivity))).
      rewrite (upd_ne _ (Regidx a7_idx) (Regidx q) _
                 (ushr_cs_ne q a7_idx Hq
                    ltac:(right; right; right; right;
                          vm_compute; reflexivity))).
      rewrite /m1 (upd_ne m (Regidx ra_idx) (Regidx q) _
                     (ushr_cs_ne q ra_idx Hq
                        ltac:(left; vm_compute; reflexivity))).
      reflexivity.
    - exact (upd_eq _ (Regidx a0_idx) r).
  Qed.

  (* ===================================================================== *)
  (* §4' THE SAME CALL, CARRYING A RESOURCE.                                *)
  (*                                                                       *)
  (* [wp_kshr_qcall]'s [Hstub] has a type with no room for one, which is    *)
  (* right for the quiet stubs -- open, write, dup all take the run in and  *)
  (* give the run back -- and wrong for CLOSE, which SPENDS a handle        *)
  (* ([UkSh.wp_ksh_close]).  A caller closing an inherited descriptor has   *)
  (* to hand one in, so the stub's type needs an [R] going in and an [S r]  *)
  (* coming back.                                                          *)
  (*                                                                       *)
  (* THE STUB IS STATED AT THE ONE REGISTER FILE IT IS APPLIED TO, not at   *)
  (* a ∀-bound [m0] as [wp_kshr_qcall]'s is.  That is forced by close: its  *)
  (* precondition reads a0 ("the argument register IS the descriptor the    *)
  (* handle is for"), and a fact about a0 cannot be supplied for an         *)
  (* arbitrary register file -- only for the one this call actually builds, *)
  (* [m] with ra re-armed.                                                  *)
  (* ===================================================================== *)
  Local Lemma wp_kshr_rcall (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc sym ret num : Z) (imm : mword 21) (avail : nat)
      (R : iProp Σ) (S : mword 64 -> iProp Σ)
      (Hstub : forall (h0 : CpuId) (av : nat),
         shk_code γt -∗
         R -∗
         urun γt γd γs γfd h0
           (<[Regidx ra_idx := (mword_of_int ret : mword 64)]> m)
           (mword_of_int sym) av -∗
         (∀ (h1 : CpuId) (r : mword 64),
            S r -∗
            urun γt γd γs γfd h1
              (<[Regidx a0_idx := r]>
                 (<[Regidx a7_idx := (mword_of_int num : mword 64)]>
                    (<[Regidx ra_idx := (mword_of_int ret : mword 64)]> m)))
              (ret_pc ((<[Regidx ra_idx := (mword_of_int ret : mword 64)]> m)
                         !!! Regidx ra_idx)) av -∗
            WP (Loop : expr riscv_lang)) -∗
         WP (Loop : expr riscv_lang)) :
    (mword_of_int sym : mword 64)
      = add_vec (mword_of_int pc : mword 64) (sign_extend' 64 imm) ->
    (mword_of_int ret : mword 64) = add_vec_int (mword_of_int pc : mword 64) 4 ->
    eq_vec (access_vec_dec (mword_of_int sym : mword 64) 0) ('b"0") = true ->
    ret_pc (mword_of_int ret : mword 64) = mword_of_int ret ->
    shk_code γt -∗
    uinstr_is γt (mword_of_int pc) false (JAL (imm, Regidx ra_idx)) -∗
    R -∗
    urun γt γd γs γfd h m (mword_of_int pc) avail -∗
    (∀ (h' : CpuId) (m' : regfile) (r : mword 64),
       ⌜ ucallee_saved m m' ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = r ⌝ -∗
       S r -∗
       urun γt γd γs γfd h' m' (mword_of_int ret) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hsym Hret Hal Hrp. iIntros "#Hcode #Hi HR Hrun Hcont".
    iApply (wp_kshr_jal γt γd γs γfd h m pc sym ret imm avail Hsym Hret Hal
              with "Hi Hrun").
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx ra_idx := (mword_of_int ret : mword 64)]> m).
    assert (Hra1 : m1 !!! Regidx ra_idx = (mword_of_int ret : mword 64))
      by exact (upd_eq m (Regidx ra_idx) _).
    iApply (Hstub h1 avail with "Hcode HR Hrun").
    iIntros (h2 r) "HS Hrun". rewrite Hra1 Hrp.
    iApply ("Hcont" $! h2 _ r with "[%] [%] HS Hrun").
    - intros q Hq.
      rewrite (upd_ne _ (Regidx a0_idx) (Regidx q) r
                 (ushr_cs_ne q a0_idx Hq
                    ltac:(right; left; vm_compute; reflexivity))).
      rewrite (upd_ne _ (Regidx a7_idx) (Regidx q) _
                 (ushr_cs_ne q a7_idx Hq
                    ltac:(right; right; right; right;
                          vm_compute; reflexivity))).
      rewrite /m1 (upd_ne m (Regidx ra_idx) (Regidx q) _
                     (ushr_cs_ne q ra_idx Hq
                        ltac:(left; vm_compute; reflexivity))).
      reflexivity.
    - exact (upd_eq _ (Regidx a0_idx) r).
  Qed.

  (* ===================================================================== *)
  (* §4a THE QUIET STUB SHAPE, again.  UkSh.v's [wp_ksh_qstub] is [Local]   *)
  (* and stages 1-2 instantiated it at open, close and write; stage 5 needs *)
  (* it at dup, so here it is once more.  The eight [n <> USYS_*] premises  *)
  (* are the program paying for not being in any row that writes user       *)
  (* memory.                                                                *)
  (* ===================================================================== *)
  Local Lemma wp_kshr_qstub (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc0 pc1 pc2 : Z)
      (imm : mword 6) (n : Z) (avail : nat) :
    (sign_extend' 64 imm : mword 64) = mword_of_int n ->
    usysno (<[Regidx a7_idx := (mword_of_int n : mword 64)]> m) = n ->
    n <> USYS_exit -> n <> USYS_fork ->
    n <> USYS_exec -> n <> USYS_sbrk ->
    n <> USYS_wait -> n <> USYS_pipe -> n <> USYS_read -> n <> USYS_fstat ->
    (* ...and the three that move the descriptor table: this stub re-closes
       the run at the view it opened at, so it is for calls that leave
       [p->ofile[]] alone.  open / close / dup have their own leaves. *)
    n <> USYS_close -> n <> USYS_dup -> n <> USYS_open ->
    add_vec_int (mword_of_int pc0 : mword 64) 2 = mword_of_int pc1 ->
    add_vec_int (mword_of_int pc1 : mword 64) 4 = mword_of_int pc2 ->
    is_aligned_vaddr (Virtaddr (mword_of_int pc2 : mword 64)) 2 = true ->
    uinstr_is γt (mword_of_int pc0) true (C_LI (imm, Regidx a7_idx)) -∗
    uinstr_is γt (mword_of_int pc1) false (ECALL tt) -∗
    uinstr_is γt (mword_of_int pc2) true (C_JR (Regidx ra_idx)) -∗
    urun γt γd γs γfd h m (mword_of_int pc0) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun γt γd γs γfd h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int n : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Himm Hno He Hf Hx Hs Hw Hp Hr Hst Hcl Hdp Hop E01 E12 Hal2.
    iIntros "#Ci0 #Ci1 #Ci2 Hrun Hcont".
    iApply (wp_uk_cli γt γd γs γfd h m (mword_of_int pc0) imm a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "Ci0 Hrun").
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 imm : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int n : mword 64)]> m)
      by (f_equal; exact Himm).
    rewrite E01 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int n : mword 64)]> m).
    iApply (wp_uk_ecall_quiet γt γd γs γfd h1 m1 (mword_of_int pc1) n avail
              Hno He Hf Hx Hs Hw Hp Hr Hst Hcl Hdp Hop
              ltac:(rewrite E12; exact Hal2)
              with "Ci1 Hrun").
    rewrite E12.
    iIntros (h2 ret) "Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int n : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr γt γd γs γfd h2 m2 (mword_of_int pc2) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "Ci2 Hrun").
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hrun").
  Qed.

  (* the QUIET stub's twin at DUP.  sh does not track the descriptors it
     duplicates (they are pipe ends it will close later), so this is the
     UNTRACKED leaf: it moves the program's authority and hands back no
     handle.  See [UkRunSys.wp_uk_ecall_dup_untracked]. *)
  Local Lemma wp_kshr_dstub (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc0 pc1 pc2 : Z)
      (imm : mword 6) (avail : nat) :
    (sign_extend' 64 imm : mword 64) = mword_of_int USYS_dup ->
    usysno (<[Regidx a7_idx := (mword_of_int USYS_dup : mword 64)]> m) = USYS_dup ->
    add_vec_int (mword_of_int pc0 : mword 64) 2 = mword_of_int pc1 ->
    add_vec_int (mword_of_int pc1 : mword 64) 4 = mword_of_int pc2 ->
    is_aligned_vaddr (Virtaddr (mword_of_int pc2 : mword 64)) 2 = true ->
    uinstr_is γt (mword_of_int pc0) true (C_LI (imm, Regidx a7_idx)) -∗
    uinstr_is γt (mword_of_int pc1) false (ECALL tt) -∗
    uinstr_is γt (mword_of_int pc2) true (C_JR (Regidx ra_idx)) -∗
    urun γt γd γs γfd h m (mword_of_int pc0) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun γt γd γs γfd h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int USYS_dup : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Himm Hno E01 E12 Hal2.
    iIntros "#Ci0 #Ci1 #Ci2 Hrun Hcont".
    iApply (wp_uk_cli γt γd γs γfd h m (mword_of_int pc0) imm a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "Ci0 Hrun").
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 imm : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int USYS_dup : mword 64)]> m)
      by (f_equal; exact Himm).
    rewrite E01 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int USYS_dup : mword 64)]> m).
    iApply (wp_uk_ecall_dup_untracked γt γd γs γfd h1 m1 (mword_of_int pc1)
              avail Hno ltac:(rewrite E12; exact Hal2)
              with "Ci1 Hrun").
    rewrite E12.
    iIntros (h2 ret) "Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int USYS_dup : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr γt γd γs γfd h2 m2 (mword_of_int pc2) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "Ci2 Hrun").
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hrun").
  Qed.

  (* ---- dup @0xcfe, SYS_dup = 10 -- the PIPE arm's fd plumbing ---------- *)
  Lemma wp_kshr_dup (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (avail : nat) :
    shk_code γt -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.dup) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun γt γd γs γfd h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun Hcont".
    rewrite shr_dup.
    iApply (wp_kshr_dstub γt γd γs γfd h m 0xcfe 0xd00 0xd04
              (mword_of_int 10 : mword 6) avail
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(unfold usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 10 : mword 64));
                    vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] [] [] Hrun Hcont").
    { iApply (uis_shk_cfe with "Hcode"). }
    { iApply (uis_shk_d00 with "Hcode"). }
    { iApply (uis_shk_d04 with "Hcode"). }
  Qed.

  (* ---- wait @0xc8e, SYS_wait = 3, AT A NULL STATUS POINTER ------------- *)
  (* sh calls [wait] with a0 = 0 at all three of its call sites, so the      *)
  (* row's null-guard arm is the one that fires and the heap crosses         *)
  (* untouched -- the quiet shape, at a syscall that is not quiet.           *)
  Lemma wp_kshr_wait (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (avail : nat) :
    uint (m !!! Regidx a0_idx) = 0 ->
    shk_code γt -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.wait) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun γt γd γs γfd h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 3 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0. iIntros "#Hcode Hrun Hcont".
    rewrite shr_wait.
    (* ---- 0xc8e  c.li a7,3 ---- *)
    iApply (wp_uk_cli γt γd γs γfd h m (mword_of_int 0xc8e)
              (mword_of_int 3 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_c8e with "Hcode"). }
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64
                        (mword_of_int 3 : mword 6) : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 3 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (E0 : add_vec_int (mword_of_int 0xc8e : mword 64) 2
                 = mword_of_int 0xc90)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em. iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 3 : mword 64)]> m).
    assert (Ha0_1 : uint (m1 !!! Regidx a0_idx) = 0).
    { rewrite /m1 (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)). exact Ha0. }
    (* ---- 0xc90  ecall -- the wait row at a null status pointer ---- *)
    iApply (wp_uk_ecall_wait_null γt γd γs γfd h1 m1 (mword_of_int 0xc90) avail
              ltac:(rewrite /m1 /usysno
                      (upd_eq m (Regidx a7_idx) (mword_of_int 3 : mword 64));
                    vm_compute; reflexivity)
              Ha0_1
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_c90 with "Hcode"). }
    assert (E1 : add_vec_int (mword_of_int 0xc90 : mword 64) 4
                 = mword_of_int 0xc94)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1. iIntros (h2 ret) "Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 3 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr γt γd γs γfd h2 m2 (mword_of_int 0xc94) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_c94 with "Hcode"). }
    iIntros (h3) "Hrun". iApply ("Hcont" $! h3 ret with "Hrun").
  Qed.

  (* ---- exec @0xcbe, SYS_exec = 7 -- THE ARM THAT RETURNS --------------- *)
  (* A successful exec never comes back to this WP: the new program's is     *)
  (* minted from the new image.  So the stub's ONLY continuation is the      *)
  (* failure, and the row pins it: -1, and not one byte moved.               *)
  Lemma wp_kshr_exec (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (avail : nat) :
    shk_code γt -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.exec) avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h'
         (<[Regidx a0_idx := (mword_of_int (-1) : mword 64)]>
            (<[Regidx a7_idx := (mword_of_int 7 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun Hcont".
    rewrite shr_exec.
    iApply (wp_uk_cli γt γd γs γfd h m (mword_of_int 0xcbe)
              (mword_of_int 7 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_cbe with "Hcode"). }
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64
                        (mword_of_int 7 : mword 6) : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 7 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (E0 : add_vec_int (mword_of_int 0xcbe : mword 64) 2
                 = mword_of_int 0xcc0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em. iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 7 : mword 64)]> m).
    iApply (wp_uk_ecall_exec γt γd γs γfd h1 m1 (mword_of_int 0xcc0) avail
              ltac:(rewrite /m1 /usysno
                      (upd_eq m (Regidx a7_idx) (mword_of_int 7 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_cc0 with "Hcode"). }
    assert (E1 : add_vec_int (mword_of_int 0xcc0 : mword 64) 4
                 = mword_of_int 0xcc4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1. iIntros (h2) "Hrun".
    set (m2 := <[Regidx a0_idx := (mword_of_int (-1) : mword 64)]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) _
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 7 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr γt γd γs γfd h2 m2 (mword_of_int 0xcc4) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_cc4 with "Hcode"). }
    iIntros (h3) "Hrun". iApply ("Hcont" $! h3 with "Hrun").
  Qed.

  (* ---- pipe @0xc96, SYS_pipe = 4 -- THE JOINED ROW -------------------- *)
  (* [pipe] writes TWO ints at the address a0 names, and this stub is the
     one place sh learns which descriptors it got: the return value is only
     0 or -1.  So it is NOT the window leaf -- that one re-closes the run at
     the descriptor view it opened at and is explicitly barred from pipe --
     but [UkRunSys.wp_uk_ecall_pipe], which hands back the two HANDLES
     beside the eight bytes and says the bytes spell the handles.  That tie
     is what PIPE's six closes below are paid for with; see
     [UsysMemOk.usys_pipe_ok]. *)
  Lemma wp_kshr_pipe (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (a : Z) (f : nat -> bv 8)
      (avail : nat) :
    uint (m !!! Regidx a0_idx) = a ->
    shk_code γt -∗
    ubytes γd a 8 f -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.pipe) avail -∗
    (∀ (h' : CpuId) (ret : mword 64) (g : nat -> bv 8),
       ((∃ p0 p1 : nat,
           ⌜ uint ret = 0 /\ p0 <> p1 /\ (p0 < NOFILE)%nat /\ (p1 < NOFILE)%nat
             /\ (forall i : nat, (i < 8)%nat ->
                   g i = if (i <? 4)%nat
                         then nth_byte
                                (trunc32 (mword_of_int (Z.of_nat p0) : mword 64)) i
                         else nth_byte
                                (trunc32 (mword_of_int (Z.of_nat p1) : mword 64))
                                (i - 4)%nat) ⌝ ∗
           ufd γfd p0 (FdOpen true false FdPipe) ∗
           ufd γfd p1 (FdOpen false true FdPipe))
        ∨ ⌜ uint ret <> 0 ⌝) -∗
       ubytes γd a 8 g -∗
       urun γt γd γs γfd h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 4 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0. iIntros "#Hcode Hbuf Hrun Hcont".
    rewrite shr_pipe.
    iApply (wp_uk_cli γt γd γs γfd h m (mword_of_int 0xc96)
              (mword_of_int 4 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_c96 with "Hcode"). }
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64
                        (mword_of_int 4 : mword 6) : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 4 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (E0 : add_vec_int (mword_of_int 0xc96 : mword 64) 2
                 = mword_of_int 0xc98)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em. iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 4 : mword 64)]> m).
    assert (Ha0_1 : m1 !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                  ltac:(vm_compute; discriminate)).
    (* the leaf owns the buffer at the register's own spelling, which is a0
       of the frame the ecall traps at -- and [c.li a7] did not touch it *)
    assert (Habuf : uint (m1 !!! Regidx (mword_of_int 10)) = a)
      by (rewrite Ha0_1; exact Ha0).
    iApply (wp_uk_ecall_pipe γt γd γs γfd h1 m1 (mword_of_int 0xc98) f avail
              ltac:(rewrite /m1 /usysno
                      (upd_eq m (Regidx a7_idx) (mword_of_int 4 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun [Hbuf]").
    { iApply (uis_shk_c98 with "Hcode"). }
    { rewrite Habuf. iExact "Hbuf". }
    assert (E1 : add_vec_int (mword_of_int 0xc98 : mword 64) 4
                 = mword_of_int 0xc9c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1. iIntros (h2 ret g) "Hhs Hrun Hbuf".
    rewrite Habuf.
    set (m2 := <[Regidx a0_idx := ret]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 4 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr γt γd γs γfd h2 m2 (mword_of_int 0xc9c) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_c9c with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret g with "Hhs Hbuf Hrun").
  Qed.

  (* ---- fork @0xc7e, SYS_fork = 1 -- THE STUB THAT RETURNS TWICE -------- *)
  (* Both arms come back through the same [c.jr ra] at 0xc84, the child's    *)
  (* under fresh names -- which is why the payload has to carry the CODE:    *)
  (* without [shk_code γt'] the child cannot walk its own return.            *)
  (* [D] rides through exactly as it does at the leaf: sh's descriptors are
     the point of the PIPE and REDIR arms, and both processes get them. *)
  Lemma wp_kshr_fork (γt γd γs γfd : gname) (P : gname -> gname -> gname -> iProp Σ)
      `{FP : !Forkable P} (szv : Z) (D : gmap nat fdstate)
      (h : CpuId) (m : regfile) (avail : nat) :
    shk_code γt -∗ P γt γd γs -∗ usz γs szv -∗
    ([∗ map] fd ↦ st ∈ D, UserFd.ufd γfd fd st) -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.fork) avail -∗
    ((∀ (h' : CpuId) (r : mword 64),
        ⌜ r <> (mword_of_int 0 : mword 64) ⌝ -∗
        P γt γd γs -∗ usz γs szv -∗
        ([∗ map] fd ↦ st ∈ D, UserFd.ufd γfd fd st) -∗
        urun γt γd γs γfd h'
          (<[Regidx a0_idx := r]>
             (<[Regidx a7_idx := (mword_of_int 1 : mword 64)]> m))
          (ret_pc (m !!! Regidx ra_idx)) avail -∗
        WP (Loop : expr riscv_lang)) ∗
     (∀ (gt gd gs gfd : gname) (h' : CpuId),
        shk_code gt -∗ P gt gd gs -∗ usz gs szv -∗
        ([∗ map] fd ↦ st ∈ D, UserFd.ufd gfd fd st) -∗
        urun gt gd gs gfd h'
          (<[Regidx a0_idx := (mword_of_int 0 : mword 64)]>
             (<[Regidx a7_idx := (mword_of_int 1 : mword 64)]> m))
          (ret_pc (m !!! Regidx ra_idx)) avail -∗
        WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode HP Hsz HD Hrun [Hpar Hchi]".
    rewrite shr_fork.
    iApply (wp_uk_cli γt γd γs γfd h m (mword_of_int 0xc7e)
              (mword_of_int 1 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_c7e with "Hcode"). }
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64
                        (mword_of_int 1 : mword 6) : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 1 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (E0 : add_vec_int (mword_of_int 0xc7e : mword 64) 2
                 = mword_of_int 0xc80)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em. iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 1 : mword 64)]> m).
    iApply (wp_uk_ecall_fork γt γd γs γfd h1 m1 (mword_of_int 0xc80) avail szv D
              (fun gt gd gs => (shk_code gt ∗ P gt gd gs)%I)
              (FP := forkable_sep (fun gt _ _ => shk_code gt) P
                       forkable_shk_code FP)
              ltac:(rewrite /m1 /usysno
                      (upd_eq m (Regidx a7_idx) (mword_of_int 1 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] [HP] Hsz HD Hrun").
    { iApply (uis_shk_c80 with "Hcode"). }
    { iSplitR; [ iExact "Hcode" | iExact "HP" ]. }
    assert (E1 : add_vec_int (mword_of_int 0xc80 : mword 64) 4
                 = mword_of_int 0xc84)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    assert (Hraf : forall (r : mword 64),
              (<[Regidx a0_idx := r]> m1) !!! Regidx ra_idx
              = m !!! Regidx ra_idx).
    { intros r. rewrite /m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) r
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 1 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iSplitL "Hpar".
    - iIntros (hp r) "%Hr [#Hcp HP] Hsz HD Hrun".
      iApply (wp_uk_cjr γt γd γs γfd hp (<[Regidx a0_idx := r]> m1)
                (mword_of_int 0xc84) ra_idx
                (ret_pc (m !!! Regidx ra_idx)) avail
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hraf r); reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_c84 with "Hcp"). }
      iIntros (hp2) "Hrun".
      iApply ("Hpar" $! hp2 r with "[%] HP Hsz HD Hrun"). exact Hr.
    - iIntros (gt gd gs gfd' hc) "[#Hck HP] Hsz HD Hrun".
      iApply (wp_uk_cjr gt gd gs gfd' hc
                (<[Regidx a0_idx := (mword_of_int 0 : mword 64)]> m1)
                (mword_of_int 0xc84) ra_idx
                (ret_pc (m !!! Regidx ra_idx)) avail
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Hraf (mword_of_int 0 : mword 64)); reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_c84 with "Hck"). }
      iIntros (hc2) "Hrun".
      iApply ("Hchi" $! gt gd gs gfd' hc2 with "Hck HP Hsz HD Hrun").
  Qed.

  (* ===================================================================== *)
  (* §5 THE DIAGNOSTIC CUT -- THE FILE'S ONE HYPOTHESIS.                    *)
  (*                                                                       *)
  (* Three pcs hand control to sh's printer and none of them comes back:    *)
  (*                                                                       *)
  (*   0x4a  panic(s)                     -- fork1's -1 arm, PIPE's failure *)
  (*   0xda  the exec-failed tail          -- inside runcmd's EXEC arm      *)
  (*   0x10e the open-failed tail          -- inside runcmd's REDIR arm     *)
  (*                                                                       *)
  (* Each runs [fprintf] (0x10aa, 279 instructions with vprintf and putc    *)
  (* under it) and then [exit].  The walk is [UkShDiag.v]'s, so the cut     *)
  (* here is the subtree as ONE premise, at those three pcs, with exactly   *)
  (* what each site has in hand:                                            *)
  (*                                                                       *)
  (*  - panic is entered with a0 naming one of sh's THREE panic messages    *)
  (*    (fork, runcmd, pipe), and needs nothing but the image: its own      *)
  (*    string is .rodata, and so is the "%s\n" it prints it through;       *)
  (*  - the two tails are entered with s1 still on the node, and each reads *)
  (*    ONE heap string through it, so each is handed that pointer word,    *)
  (*    that string and the node's 8-alignment -- all three [DfracDiscarded] *)
  (*    or pure, and all three straight out of [ush_cmd].                   *)
  (*                                                                       *)
  (* Nothing here is quantified away: every premise is satisfied by a       *)
  (* resource a real caller holds, and [UkShDiag.ush_diag_leaf_holds] is    *)
  (* the proof of it.  TAINT SET: every lemma below carries it --           *)
  (* [wp_kshr_fork1], [wp_kshr_runcmd] and the five arm lemmas -- and says  *)
  (* so in its header; [UkShDiag.wp_kshr_runcmd_final] and                  *)
  (* [_fork1_final] are those two with it supplied.                         *)
  (* ===================================================================== *)
  Definition ush_panic_msg (z : Z) : Prop :=
    z = 0x1298 \/ z = 0x12a0 \/ z = 0x12c8.

  (* The two tails' first instruction is [c.ld a2,<k>(s1)], and a [c.ld] is
     8-aligned or it is not a step at all -- so the node's own alignment,
     which every caller has out of [ush_cmd], is part of what the site
     hands over. *)
  Definition ush_diag_at (pc : Z) (m : regfile) : Prop :=
    (pc = ShSyms.panic /\ ush_panic_msg (uint (m !!! Regidx a0_idx)))
    \/ (pc = 0xda /\ uint (m !!! Regidx s1_idx) mod 8 = 0)
    \/ (pc = 0x10e /\ uint (m !!! Regidx s1_idx) mod 8 = 0).

  Definition ush_diag_res (g : gname) (pc : Z) (m : regfile) : iProp Σ :=
    (if decide (pc = 0xda) then
       ∃ x : uarg, ush_ptr g (uint (m !!! Regidx s1_idx) + 8) (ua_ptr x)
                   ∗ ush_str g x
     else if decide (pc = 0x10e) then
       ∃ x : uarg, ush_ptr g (uint (m !!! Regidx s1_idx) + 16) (ua_ptr x)
                   ∗ ush_str g x
     else emp)%I.

  Lemma ush_diag_res_panic (g : gname) (m : regfile) :
    ush_diag_res g ShSyms.panic m = emp%I.
  Proof.
    rewrite /ush_diag_res.
    destruct (decide (ShSyms.panic = 0xda)) as [Hc | _];
      [ exfalso; unfold ShSyms.panic in Hc; discriminate Hc | ].
    destruct (decide (ShSyms.panic = 0x10e)) as [Hc | _];
      [ exfalso; unfold ShSyms.panic in Hc; discriminate Hc | ].
    reflexivity.
  Qed.

  (* [shk_rodata γt] IS NOT DECORATION.  All three sites read a format
     string out of .rodata (0x1290, 0x12a8, 0x12b8) and panic's own '%s'
     argument is a .rodata literal too; none of them is in
     [ShInstrs.sh_bytes], so [shk_code] cannot produce them and the premise
     is not dischargeable without this conjunct.  It costs its callers
     nothing: [ush_jtab] carries it and every site already holds one. *)
  Hypothesis ush_diag_leaf :
    forall (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : Z) (n : nat),
      ush_diag_at pc m ->
      shk_code γt -∗
      shk_rodata γt -∗
      ush_diag_res γd pc m -∗
      urun γt γd γs γfd h m (mword_of_int pc) (Dg + n) -∗
      WP (Loop : expr riscv_lang).

  (* ===================================================================== *)
  (* §6 fork1 @0x68 -- fork, and panic if it failed.                        *)
  (*                                                                       *)
  (* TWO-WORD FRAME, spilled and restored, and it CROSSES THE FORK: the     *)
  (* child returns through the same epilogue, so it needs its own copy of   *)
  (* the two words AT THEIR VALUES -- which is why the payload carries      *)
  (* [uword] at [vra] and [vs0] and not an existential [ustack].  (An       *)
  (* [ustack] would forget the spilled ra and the child would return to an  *)
  (* unnamed address.)                                                      *)
  (*                                                                       *)
  (* DEPENDS ON [ush_diag_leaf] (the -1 arm's panic).                       *)
  (* ===================================================================== *)

  (* the shared tail, 0x74..0x80 plus the panic branch, at WHATEVER gname
     triple the arm that reached it is running under *)
  Local Lemma wp_kshr_fork1_tail (γt γd γs γfd : gname) (h : CpuId) (mt : regfile)
      (sp0 vra vs0 : mword 64) (n : nat) :
    uint sp0 mod 8 = 0 ->
    16 <= uint sp0 ->
    mt !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 2)) ->
    shk_code γt -∗
    shk_rodata γt -∗
    uword γd (uint sp0 - 8) vra -∗
    uword γd (uint sp0 - 16) vs0 -∗
    urun γt γd γs γfd h mt (mword_of_int 0x74) (Dg + n) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ forall q : mword 5, uint q <> 1 -> uint q <> 2 -> uint q <> 8 ->
           uint q <> 15 -> m' !!! Regidx q = mt !!! Regidx q ⌝ -∗
       ⌜ m' !!! Regidx ra_idx = vra ⌝ -∗
       ⌜ m' !!! Regidx s0_idx = vs0 ⌝ -∗
       ⌜ m' !!! Regidx csp_rs1 = sp0 ⌝ -∗
       urun γt γd γs γfd h' m' (ret_pc vra) (2 + (Dg + n)) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hal8 Hlo Hsp. iIntros "#Hcode #Hro Hw8 Hw0 Hrun Hcont".
    assert (Hbsp1 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                    = bv_unsigned sp0 - 16).
    { replace (- (8 * Z.of_nat 2)) with (-16) by lia.
      exact (uv_avi_neg sp0 16 ltac:(lia)
               ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp16 : uint (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                    = uint sp0 - 16)
      by (rewrite !uint_unsigned; exact Hbsp1).
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    assert (Ho0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    (* ---- 0x74  c.li a5,-1 ---- *)
    iApply (wp_uk_cli γt γd γs γfd h mt (mword_of_int 0x74)
              (mword_of_int 63 : mword 6) a5_idx (Dg + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_74 with "Hcode"). }
    assert (E74 : add_vec_int (mword_of_int 0x74 : mword 64) 2
                  = mword_of_int 0x76)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E74. iIntros (h1) "Hrun".
    set (t1 := <[Regidx a5_idx
                 := regval_into_reg (sign_extend' 64
                      (mword_of_int 63 : mword 6) : mword 64)]> mt).
    assert (Ht1 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    t1 !!! Regidx q = mt !!! Regidx q)
      by (intros q Hq; exact (upd_ne mt (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Hsp1 : t1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by (rewrite (Ht1 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp).
    (* ---- 0x76  beq a0,a5,0x82 -- the -1 test ---- *)
    iApply (wp_uk_btype γt γd γs γfd h1 t1 (mword_of_int 0x76)
              (mword_of_int 12 : mword 13) a5_idx a0_idx BEQ
              (uv_btaken BEQ (t1 !!! Regidx a0_idx) (t1 !!! Regidx a5_idx))
              (mword_of_int 0x82) (Dg + n)
              eq_refl
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_76 with "Hcode"). }
    assert (E76 : add_vec_int (mword_of_int 0x76 : mword 64) 4
                  = mword_of_int 0x7a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E76. iIntros (h2) "Hrun".
    destruct (uv_btaken BEQ (t1 !!! Regidx a0_idx) (t1 !!! Regidx a5_idx)).
    { (* ---- fork returned -1: panic("fork") ---- *)
      (* 0x82  auipc a0,0x1 *)
      iApply (wp_uk_auipc γt γd γs γfd h2 t1 (mword_of_int 0x82)
                (mword_of_int 1 : mword 20) a0_idx
                (mword_of_int 0x1082) (Dg + n)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_82 with "Hcode"). }
      assert (E82 : add_vec_int (mword_of_int 0x82 : mword 64) 4
                    = mword_of_int 0x86)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E82. iIntros (h3) "Hrun".
      set (t2 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int 0x1082 : mword 64)]> t1).
      assert (Ha0_2 : t2 !!! Regidx a0_idx = (mword_of_int 0x1082 : mword 64))
        by exact (upd_eq t1 (Regidx a0_idx) _).
      (* 0x86  addi a0,a0,534 *)
      iApply (wp_uk_addi γt γd γs γfd h3 t2 (mword_of_int 0x86)
                (mword_of_int 534 : mword 12) a0_idx a0_idx
                (mword_of_int 0x1298) (Dg + n)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha0_2;
                      assert (Es : (sign_extend' 64
                                      (mword_of_int 534 : mword 12) : mword 64)
                                   = mword_of_int 534)
                        by (apply bv_eq; vm_compute; reflexivity);
                      rewrite Es moi_add; f_equal; lia)
                with "[] Hrun").
      { iApply (uis_shk_86 with "Hcode"). }
      assert (E86 : add_vec_int (mword_of_int 0x86 : mword 64) 4
                    = mword_of_int 0x8a)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E86. iIntros (h4) "Hrun".
      set (t3 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int 0x1298 : mword 64)]> t2).
      (* 0x8a  jal ra,0x4a <panic> -- and the diagnostic cut takes over *)
      iApply (wp_kshr_jal γt γd γs γfd h4 t3 0x8a 0x4a 0x8e
                (mword_of_int 2097088 : mword 21) (Dg + n)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_8a with "Hcode"). }
      iIntros (h5) "Hrun".
      set (t4 := <[Regidx ra_idx := (mword_of_int 0x8e : mword 64)]> t3).
      assert (Hmsg : uint (t4 !!! Regidx a0_idx) = 0x1298).
      { rewrite /t4 (upd_ne t3 (Regidx ra_idx) (Regidx a0_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /t3 (upd_eq t2 (Regidx a0_idx)
                       (mword_of_int 0x1298 : mword 64)).
        apply uint_moi. unfold Z64. lia. }
      iApply (ush_diag_leaf γt γd γs γfd h5 t4 ShSyms.panic n
                ltac:(left; split; [ reflexivity | left; exact Hmsg ])
                with "Hcode Hro [] Hrun").
      rewrite ush_diag_res_panic. done. }
    (* ---- fork succeeded: pop and return ---- *)
    (* 0x7a  c.ldsp ra,8(sp) *)
    iApply (wp_uk_cldsp γt γd γs γfd h2 t1 (mword_of_int 0x7a)
              (mword_of_int 1 : mword 6) ra_idx (uint sp0 - 8) vra (Dg + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp1 Hsp16 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw8 Hrun").
    { iApply (uis_shk_7a with "Hcode"). }
    iIntros "Hw8".
    assert (E7a : add_vec_int (mword_of_int 0x7a : mword 64) 2
                  = mword_of_int 0x7c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7a. iIntros (h3) "Hrun".
    set (e1 := <[Regidx ra_idx := regval_into_reg vra]> t1).
    assert (Hspe1 : e1 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by (rewrite (upd_ne t1 (Regidx ra_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)); exact Hsp1).
    (* 0x7c  c.ldsp s0,0(sp) *)
    iApply (wp_uk_cldsp γt γd γs γfd h3 e1 (mword_of_int 0x7c)
              (mword_of_int 0 : mword 6) s0_idx (uint sp0 - 16) vs0 (Dg + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspe1 Hsp16 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw0 Hrun").
    { iApply (uis_shk_7c with "Hcode"). }
    iIntros "Hw0".
    assert (E7c : add_vec_int (mword_of_int 0x7c : mword 64) 2
                  = mword_of_int 0x7e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7c. iIntros (h4) "Hrun".
    set (e2 := <[Regidx s0_idx := regval_into_reg vs0]> e1).
    assert (Hspe2 : e2 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by (rewrite (upd_ne e1 (Regidx s0_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)); exact Hspe1).
    (* 0x7e  c.addi sp,sp,16 -- THE POP *)
    assert (HR : 0 <= bv_unsigned sp0 < 18446744073709551616).
    { pose proof (bv_unsigned_in_range 64 sp0) as H0.
      assert (Em : bv_modulus 64 = 18446744073709551616)
        by (vm_compute; reflexivity).
      rewrite Em in H0. exact H0. }
    assert (Hlt2 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                   + 8 * Z.of_nat 2 < Z64)
      by (rewrite Hbsp1; unfold Z64; lia).
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                    (8 * Z.of_nat 2) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                 (8 * Z.of_nat 2) ltac:(lia) Hlt2).
      rewrite Hbsp1. lia. }
    iApply (wp_uk_caddi_sp_up γt γd γs γfd h4 e2 (mword_of_int 0x7e)
              (mword_of_int 16 : mword 6) 2 (Dg + n)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hw8 Hw0] Hrun").
    { iApply (uis_shk_7e with "Hcode"). }
    { rewrite Hspe2 Hup ustack_2.
      iSplit; [ iPureIntro; exact Hal8 | ].
      iSplitL "Hw8"; [ iExists vra; iFrame | iExists vs0; iFrame ]. }
    assert (E7e : add_vec_int (mword_of_int 0x7e : mword 64) 2
                  = mword_of_int 0x80)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hspe2 Hup E7e. iIntros (h5) "Hrun".
    set (e3 := <[Regidx csp_rs1 := regval_into_reg sp0]> e2).
    assert (Hra3 : e3 !!! Regidx ra_idx = vra).
    { rewrite (upd_ne e2 (Regidx csp_rs1) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne e1 (Regidx s0_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq t1 (Regidx ra_idx) (regval_into_reg vra)). }
    assert (Hs03 : e3 !!! Regidx s0_idx = vs0).
    { rewrite (upd_ne e2 (Regidx csp_rs1) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq e1 (Regidx s0_idx) (regval_into_reg vs0)). }
    (* 0x80  c.jr ra *)
    iApply (wp_uk_cjr γt γd γs γfd h5 e3 (mword_of_int 0x80) ra_idx
              (ret_pc vra) (2 + (Dg + n))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra3; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_80 with "Hcode"). }
    iIntros (h6) "Hrun".
    iApply ("Hcont" $! h6 e3 with "[%] [%] [%] [%] Hrun");
      [ | exact Hra3 | exact Hs03
        | exact (upd_eq e2 (Regidx csp_rs1) (regval_into_reg sp0)) ].
    intros q H1 H2 H8 H15.
    assert (Hc1 : uint ra_idx = 1) by (vm_compute; reflexivity).
    assert (Hc2 : uint csp_rs1 = 2) by (vm_compute; reflexivity).
    assert (Hc8 : uint s0_idx = 8) by (vm_compute; reflexivity).
    assert (Hc15 : uint a5_idx = 15) by (vm_compute; reflexivity).
    rewrite /e3 (upd_ne e2 (Regidx csp_rs1) (Regidx q) _
                   (ushr_ridx_ne q csp_rs1 ltac:(rewrite Hc2; exact H2))).
    rewrite /e2 (upd_ne e1 (Regidx s0_idx) (Regidx q) _
                   (ushr_ridx_ne q s0_idx ltac:(rewrite Hc8; exact H8))).
    rewrite /e1 (upd_ne t1 (Regidx ra_idx) (Regidx q) _
                   (ushr_ridx_ne q ra_idx ltac:(rewrite Hc1; exact H1))).
    exact (Ht1 q (ushr_ridx_ne q a5_idx ltac:(rewrite Hc15; exact H15))).
  Qed.

  (* ---- fork1, whole.  DEPENDS ON [ush_diag_leaf]. --------------------- *)
  Lemma wp_kshr_fork1 (γt γd γs γfd : gname)
      (P : gname -> gname -> gname -> iProp Σ) `{FP : !Forkable P}
      (szv : Z) (D : gmap nat fdstate)
      (h : CpuId) (m : regfile) (n : nat) :
    shk_code γt -∗ shk_rodata γt -∗ P γt γd γs -∗ usz γs szv -∗
    (* the caller's descriptors, which BOTH processes come back holding --
       see [UkFork.wp_uk_ecall_fork].  This is what PIPE's six closes and
       REDIR's close-and-reopen are paid for with. *)
    ([∗ map] fd ↦ st ∈ D, UserFd.ufd γfd fd st) -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.fork1) (2 + (Dg + n)) -∗
    ((∀ (h' : CpuId) (m' : regfile) (r : mword 64),
        ⌜ r <> (mword_of_int 0 : mword 64) ⌝ -∗
        ⌜ ucallee_saved m m' ⌝ -∗
        ⌜ m' !!! Regidx a0_idx = r ⌝ -∗
        P γt γd γs -∗ usz γs szv -∗
        ([∗ map] fd ↦ st ∈ D, UserFd.ufd γfd fd st) -∗
        urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (2 + (Dg + n)) -∗
        WP (Loop : expr riscv_lang)) ∗
     (∀ (gt gd gs gfd : gname) (h' : CpuId) (m' : regfile),
        ⌜ ucallee_saved m m' ⌝ -∗
        ⌜ m' !!! Regidx a0_idx = (mword_of_int 0 : mword 64) ⌝ -∗
        shk_code gt -∗ P gt gd gs -∗ usz gs szv -∗
        ([∗ map] fd ↦ st ∈ D, UserFd.ufd gfd fd st) -∗
        urun gt gd gs gfd h' m' (ret_pc (m !!! Regidx ra_idx)) (2 + (Dg + n)) -∗
        WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode #Hro HP Hsz HD Hrun [Hpar Hchi]".
    rewrite shr_fork1.
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    assert (Hlo : 16 <= uint sp0) by lia.
    set (vra := m !!! Regidx ra_idx).
    set (vs0 := m !!! Regidx s0_idx).
    assert (Hbsp1 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                    = bv_unsigned sp0 - 16).
    { replace (- (8 * Z.of_nat 2)) with (-16) by lia.
      exact (uv_avi_neg sp0 16 ltac:(lia)
               ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp16 : uint (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                    = uint sp0 - 16)
      by (rewrite !uint_unsigned; exact Hbsp1).
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    assert (Ho0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    (* ---- 0x68  c.addi sp,sp,-16 -- THE PUSH ---- *)
    iApply (wp_uk_caddi_sp_dn γt γd γs γfd h m (mword_of_int 0x68)
              (mword_of_int 48 : mword 6) 2 (Dg + n)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_68 with "Hcode"). }
    assert (E68 : add_vec_int (mword_of_int 0x68 : mword 64) 2
                  = mword_of_int 0x6a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp ustack_2 E68.
    iIntros "(_ & [%v8 Hw8] & [%v0 Hw0])".
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 2)))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by exact (upd_eq m (Regidx csp_rs1) _).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    (* ---- 0x6a  c.sdsp ra,8(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd h1 m1 (mword_of_int 0x6a)
              (mword_of_int 1 : mword 6) ra_idx (uint sp0 - 8) v8 (Dg + n)
              ltac:(rewrite Hsp1 Hsp16 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw8 Hrun").
    { iApply (uis_shk_6a with "Hcode"). }
    iIntros "Hw8".
    rewrite (Hm1 ra_idx ltac:(vm_compute; discriminate)).
    assert (E6a : add_vec_int (mword_of_int 0x6a : mword 64) 2
                  = mword_of_int 0x6c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E6a. iIntros (h2) "Hrun".
    (* ---- 0x6c  c.sdsp s0,0(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd h2 m1 (mword_of_int 0x6c)
              (mword_of_int 0 : mword 6) s0_idx (uint sp0 - 16) v0 (Dg + n)
              ltac:(rewrite Hsp1 Hsp16 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw0 Hrun").
    { iApply (uis_shk_6c with "Hcode"). }
    iIntros "Hw0".
    rewrite (Hm1 s0_idx ltac:(vm_compute; discriminate)).
    assert (E6c : add_vec_int (mword_of_int 0x6c : mword 64) 2
                  = mword_of_int 0x6e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E6c. iIntros (h3) "Hrun".
    (* ---- 0x6e  c.addi4spn s0,sp,16 (s0 is dead until the epilogue) ---- *)
    iApply (wp_uk_caddi4spn γt γd γs γfd h3 m1 (mword_of_int 0x6e)
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8) s0_idx
              (add_vec (m1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))
              (Dg + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              eq_refl
              with "[] Hrun").
    { iApply (uis_shk_6e with "Hcode"). }
    assert (E6e : add_vec_int (mword_of_int 0x6e : mword 64) 2
                  = mword_of_int 0x70)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E6e. iIntros (h4) "Hrun".
    set (m2 := <[Regidx s0_idx
                 := regval_into_reg
                      (add_vec (m1 !!! Regidx csp_rs1)
                         (sign_extend' 64
                            (caddi4spn_imm (mword_of_int 4 : mword 8))))]> m1).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    assert (Hsp2 : m2 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by (rewrite (Hm2 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp1).
    (* ---- 0x70  jal ra,0xc7e <fork> ---- *)
    iApply (wp_kshr_jal γt γd γs γfd h4 m2 0x70 0xc7e 0x74
              (mword_of_int 3086 : mword 21) (Dg + n)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_70 with "Hcode"). }
    iIntros (h5) "Hrun".
    set (m3 := <[Regidx ra_idx := (mword_of_int 0x74 : mword 64)]> m2).
    assert (Hra3 : m3 !!! Regidx ra_idx = (mword_of_int 0x74 : mword 64))
      by exact (upd_eq m2 (Regidx ra_idx) _).
    assert (Hsp3 : m3 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by (rewrite (upd_ne m2 (Regidx ra_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)); exact Hsp2).
    assert (Hret3 : ret_pc (m3 !!! Regidx ra_idx)
                    = (mword_of_int 0x74 : mword 64))
      by (rewrite Hra3; apply bv_eq; vm_compute; reflexivity).
    (* ---- the fork stub, and the frame crosses with the payload ---- *)
    (* THE IMAGE RIDES THE PAYLOAD, because the CHILD's -1 arm needs it at
       ITS gname triple and nothing else at those names carries it: the
       caller's [P] is abstract here.  It is one more [Forkable] conjunct,
       and the caller's [P] is untouched. *)
    iApply (wp_kshr_fork γt γd γs γfd
              (fun gt gd gs => (shk_rodata gt
                                ∗ P gt gd gs
                                ∗ uword gd (uint sp0 - 8) vra
                                ∗ uword gd (uint sp0 - 16) vs0)%I)
              (FP := forkable_sep
                       (fun g _ _ => shk_rodata g)
                       (fun gt gd gs => (P gt gd gs
                                         ∗ uword gd (uint sp0 - 8) vra
                                         ∗ uword gd (uint sp0 - 16) vs0)%I)
                       forkable_shk_rodata
                       (forkable_sep P
                          (fun _ gd _ => (uword gd (uint sp0 - 8) vra
                                          ∗ uword gd (uint sp0 - 16) vs0)%I)
                          FP
                          (forkable_sep
                             (fun _ gd _ => uword gd (uint sp0 - 8) vra)
                             (fun _ gd _ => uword gd (uint sp0 - 16) vs0)
                             (forkable_uword (uint sp0 - 8) vra)
                             (forkable_uword (uint sp0 - 16) vs0))))
              szv D h5 m3 (Dg + n)
              with "Hcode [HP Hw8 Hw0] Hsz HD Hrun").
    { iFrame "Hro HP Hw8 Hw0". }
    rewrite Hret3.
    (* the register file both arms resume under, and its sp *)
    assert (Hspf : forall r : mword 64,
              (<[Regidx a0_idx := r]>
                 (<[Regidx a7_idx := (mword_of_int 1 : mword 64)]> m3))
                !!! Regidx csp_rs1
              = add_vec_int sp0 (- (8 * Z.of_nat 2))).
    { intros r.
      rewrite (upd_ne _ (Regidx a0_idx) (Regidx csp_rs1) r
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m3 (Regidx a7_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      exact Hsp3. }
    (* what the tail's "everything else is untouched" clause gives back
       about the CALLER's registers *)
    assert (Hback : forall (r : mword 64) (m' : regfile) (q : mword 5),
              (forall p : mword 5, uint p <> 1 -> uint p <> 2 -> uint p <> 8 ->
                 uint p <> 15 ->
                 m' !!! Regidx p
                 = (<[Regidx a0_idx := r]>
                      (<[Regidx a7_idx := (mword_of_int 1 : mword 64)]> m3))
                     !!! Regidx p) ->
              m' !!! Regidx ra_idx = vra ->
              m' !!! Regidx s0_idx = vs0 ->
              m' !!! Regidx csp_rs1 = sp0 ->
              ucallee_saved_idx q = true ->
              m' !!! Regidx q = m !!! Regidx q).
    { intros r m' q Hq Hra Hs0 Hsps Hcs.
      assert (Hc2 : uint csp_rs1 = 2) by (vm_compute; reflexivity).
      assert (Hc8 : uint s0_idx = 8) by (vm_compute; reflexivity).
      destruct (Z.eq_dec (uint q) 2) as [E2 | E2].
      { rewrite (ushr_ridx_eq q csp_rs1 ltac:(rewrite E2 Hc2; reflexivity)).
        rewrite Hsps Hsp. reflexivity. }
      destruct (Z.eq_dec (uint q) 8) as [E8 | E8].
      { rewrite (ushr_ridx_eq q s0_idx ltac:(rewrite E8 Hc8; reflexivity)).
        rewrite Hs0. reflexivity. }
      destruct (ushr_cs_bounds q Hcs) as [E | [E | [E | [E | [E | E]]]]];
        try lia.
      all: rewrite (Hq q ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia));
           rewrite (upd_ne _ (Regidx a0_idx) (Regidx q) r
                      (ushr_ridx_ne q a0_idx
                         ltac:(assert (Hz : uint a0_idx = 10)
                                 by (vm_compute; reflexivity); lia)));
           rewrite (upd_ne m3 (Regidx a7_idx) (Regidx q) _
                      (ushr_ridx_ne q a7_idx
                         ltac:(assert (Hz : uint a7_idx = 17)
                                 by (vm_compute; reflexivity); lia)));
           rewrite /m3 (upd_ne m2 (Regidx ra_idx) (Regidx q) _
                      (ushr_ridx_ne q ra_idx
                         ltac:(assert (Hz : uint ra_idx = 1)
                                 by (vm_compute; reflexivity); lia)));
           rewrite (Hm2 q (ushr_ridx_ne q s0_idx ltac:(lia)));
           exact (Hm1 q (ushr_ridx_ne q csp_rs1 ltac:(lia))). }
    iSplitL "Hpar".
    - (* ---- THE PARENT ---- *)
      iIntros (hp r) "%Hr (_ & HP & Hw8 & Hw0) Hsz HD Hrun".
      iApply (wp_kshr_fork1_tail γt γd γs γfd hp
                (<[Regidx a0_idx := r]>
                   (<[Regidx a7_idx := (mword_of_int 1 : mword 64)]> m3))
                sp0 vra vs0 n Hal8 Hlo (Hspf r)
                with "Hcode Hro Hw8 Hw0 Hrun").
      iIntros (hp2 m') "%Hq %Hra %Hs0 %Hsps Hrun".
      iApply ("Hpar" $! hp2 m' r with "[%] [%] [%] HP Hsz HD [Hrun]").
      + exact Hr.
      + exact (fun q => Hback r m' q Hq Hra Hs0 Hsps).
      + rewrite (Hq a0_idx ltac:(vm_compute; lia) ltac:(vm_compute; lia)
                   ltac:(vm_compute; lia) ltac:(vm_compute; lia)).
        exact (upd_eq _ (Regidx a0_idx) r).
      + iExact "Hrun".
    - (* ---- THE CHILD, under fresh names ---- *)
      iIntros (gt gd gs gfd' hc) "#Hck (#Hcro & HP & Hw8 & Hw0) Hsz HD Hrun".
      iApply (wp_kshr_fork1_tail gt gd gs gfd' hc
                (<[Regidx a0_idx := (mword_of_int 0 : mword 64)]>
                   (<[Regidx a7_idx := (mword_of_int 1 : mword 64)]> m3))
                sp0 vra vs0 n Hal8 Hlo (Hspf (mword_of_int 0 : mword 64))
                with "Hck Hcro Hw8 Hw0 Hrun").
      iIntros (hc2 m') "%Hq %Hra %Hs0 %Hsps Hrun".
      iApply ("Hchi" $! gt gd gs gfd' hc2 m' with "[%] [%] Hck HP Hsz HD [Hrun]").
      + exact (fun q => Hback (mword_of_int 0 : mword 64) m' q Hq Hra Hs0 Hsps).
      + rewrite (Hq a0_idx ltac:(vm_compute; lia) ltac:(vm_compute; lia)
                   ltac:(vm_compute; lia) ltac:(vm_compute; lia)).
        exact (upd_eq _ (Regidx a0_idx) (mword_of_int 0 : mword 64)).
      + iExact "Hrun".
  Qed.

  (* ===================================================================== *)
  (* §7 runcmd's PROLOGUE AND DISPATCH, 0x8e..0xb8.                         *)
  (*                                                                       *)
  (*   push 48 ; spill ra,s0 ; s0 = fp ; if(cmd==0) exit(1) ; spill s1 ;    *)
  (*   s1 = cmd ; a4 = cmd->type ; if(5 <u a4) panic ;                      *)
  (*   a5 = 0x1398 + the signed word at 0x1398 + 4*type ; jr a5            *)
  (*                                                                       *)
  (* TWO BRANCHES ARE REFUTED HERE, and the node predicate is what refutes  *)
  (* them: [ush_cmd] says the node's address is positive (so the null test  *)
  (* falls through) and that its type word is one of 1..5 (so the           *)
  (* unsigned-above-5 test does).  The DEFAULT arm -- [panic("runcmd")] at  *)
  (* 0xc2 -- is therefore dead code under this precondition, and so is the  *)
  (* [exit(1)] at 0xba, which is [wp_kshr_runcmd_null]'s subject instead.   *)
  (*                                                                       *)
  (* THE JUMP TABLE IS A TEXT READ.  .rodata shares the executable          *)
  (* segment, so the [c.lw a5,0(a5)] at 0xb4 goes through [wp_uk_clw_text]  *)
  (* and the row comes out of [ush_jtab], not out of the data heap.         *)
  (* ===================================================================== *)

  (* the four closed identities the dispatch needs, one per node kind *)
  Lemma ush_bltu_false (c : ushcmd) :
    uv_btaken BLTU (sign_extend' 64 (mword_of_int 5 : mword 6) : mword 64)
      (sign_extend' 64 (mword_of_int (ush_ty c) : mword 32) : mword 64)
    = false.
  Proof. destruct c; vm_compute; reflexivity. Qed.

  Lemma ush_slli_eq (c : ushcmd) :
    shift_bits_left
      (zero_extend' 64 (mword_of_int (ush_ty c) : mword 32) : mword 64)
      (subrange_vec_dec (mword_of_int 2 : mword 6) (Z.sub log2_xlen 1) 0)
    = mword_of_int (4 * ush_ty c).
  Proof. destruct c; apply bv_eq; vm_compute; reflexivity. Qed.

  Lemma ush_jarm_eq (c : ushcmd) :
    add_vec (sign_extend' 64 (ush_jent (ush_ty c)) : mword 64)
      (mword_of_int SH_JTAB)
    = mword_of_int (ush_jarm c).
  Proof. destruct c; apply bv_eq; vm_compute; reflexivity. Qed.

  Lemma ush_jarm_even (c : ushcmd) :
    ret_pc (mword_of_int (ush_jarm c) : mword 64) = mword_of_int (ush_jarm c).
  Proof. destruct c; apply bv_eq; vm_compute; reflexivity. Qed.

  Lemma ush_jtab_align (c : ushcmd) : (SH_JTAB + 4 * ush_ty c) mod 4 = 0.
  Proof. destruct c; vm_compute; reflexivity. Qed.

  Lemma ush_jtab_bnd (c : ushcmd) : 0 <= SH_JTAB + 4 * ush_ty c < Z64.
  Proof. destruct c; unfold Z64; cbn [ush_ty]; unfold SH_JTAB; lia. Qed.

  Local Lemma wp_kshr_entry (γt γd γs γfd : gname) (c : ushcmd)
      (h : CpuId) (m : regfile) (t : Z) (n : nat) :
    m !!! Regidx a0_idx = (mword_of_int t : mword 64) ->
    shk_code γt -∗ ush_jtab γt -∗ ush_cmd γd t c -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.runcmd) (6 + n) -∗
    (∀ (h' : CpuId) (m' : regfile) (sp0 : mword 64),
       ⌜ uint sp0 mod 8 = 0 ⌝ -∗
       ⌜ 48 <= uint sp0 ⌝ -∗
       ⌜ m' !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 6)) ⌝ -∗
       ⌜ m' !!! Regidx s0_idx = sp0 ⌝ -∗
       ⌜ m' !!! Regidx s1_idx = (mword_of_int t : mword 64) ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int t : mword 64) ⌝ -∗
       (∃ w : mword 64, uword γd (uint sp0 - 40) w) -∗
       urun γt γd γs γfd h' m' (mword_of_int (ush_jarm c)) n -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0. iIntros "#Hcode #Hjt #Htree Hrun Hcont".
    rewrite shr_runcmd.
    iDestruct (ush_cmd_addr with "Htree") as %[Htr Ht8].
    iDestruct (ush_cmd_type with "Htree") as "#Hty".
    iDestruct (ush_jtab_row γt c with "Hjt") as "#Hrow".
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    assert (Hlo : 48 <= uint sp0) by lia.
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 6)))
                   = bv_unsigned sp0 - 48).
    { replace (- (8 * Z.of_nat 6)) with (-48) by lia.
      exact (uv_avi_neg sp0 48 ltac:(lia)
               ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp48 : uint (add_vec_int sp0 (- (8 * Z.of_nat 6)))
                    = uint sp0 - 48)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (HR : 0 <= bv_unsigned sp0 < 18446744073709551616).
    { pose proof (bv_unsigned_in_range 64 sp0) as H0.
      assert (Em : bv_modulus 64 = 18446744073709551616)
        by (vm_compute; reflexivity).
      rewrite Em in H0. exact H0. }
    assert (Hlt6 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 6)))
                   + 8 * Z.of_nat 6 < Z64)
      by (rewrite Hbsp; unfold Z64; lia).
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 6)))
                    (8 * Z.of_nat 6) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 6)))
                 (8 * Z.of_nat 6) ltac:(lia) Hlt6).
      rewrite Hbsp. lia. }
    assert (Go5 : uoff_sdsp (mword_of_int 5 : mword 6) = 40)
      by (vm_compute; reflexivity).
    assert (Go4 : uoff_sdsp (mword_of_int 4 : mword 6) = 32)
      by (vm_compute; reflexivity).
    assert (Go3 : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
      by (vm_compute; reflexivity).
    (* ---- 0x8e  c.addi16sp sp,sp,-48 -- THE PUSH ---- *)
    iApply (wp_uk_caddi16sp_dn γt γd γs γfd h m (mword_of_int 0x8e)
              (mword_of_int 61 : mword 6) 6 n
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_8e with "Hcode"). }
    assert (E8e : add_vec_int (mword_of_int 0x8e : mword 64) 2
                  = mword_of_int 0x90)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp ustack_6 E8e.
    iIntros "(_ & [%v1 Hw1] & [%v2 Hw2] & [%v3 Hw3] & [%v4 Hw4]
              & [%v5 Hw5] & [%v6 Hw6])".
    iIntros (h1) "Hrun".
    set (n1 := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 6)))]> m).
    assert (Hsp1 : n1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 6)))
      by exact (upd_eq m (Regidx csp_rs1) _).
    assert (Hn1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    n1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    (* ---- 0x90  c.sdsp ra,40(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd h1 n1 (mword_of_int 0x90)
              (mword_of_int 5 : mword 6) ra_idx (uint sp0 - 8) v1 n
              ltac:(rewrite Hsp1 Hsp48 Go5; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw1 Hrun").
    { iApply (uis_shk_90 with "Hcode"). }
    iIntros "Hw1".
    assert (E90 : add_vec_int (mword_of_int 0x90 : mword 64) 2
                  = mword_of_int 0x92)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E90. iIntros (h2) "Hrun".
    (* ---- 0x92  c.sdsp s0,32(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd h2 n1 (mword_of_int 0x92)
              (mword_of_int 4 : mword 6) s0_idx (uint sp0 - 16) v2 n
              ltac:(rewrite Hsp1 Hsp48 Go4; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw2 Hrun").
    { iApply (uis_shk_92 with "Hcode"). }
    iIntros "Hw2".
    assert (E92 : add_vec_int (mword_of_int 0x92 : mword 64) 2
                  = mword_of_int 0x94)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E92. iIntros (h3) "Hrun".
    (* ---- 0x94  c.addi4spn s0,sp,48 -- THE FRAME POINTER ---- *)
    iApply (wp_uk_caddi4spn γt γd γs γfd h3 n1 (mword_of_int 0x94)
              (mword_of_int 0 : mword 3) (mword_of_int 12 : mword 8) s0_idx
              sp0 n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hsp1;
                    assert (Ei : (sign_extend' 64
                                    (caddi4spn_imm (mword_of_int 12 : mword 8))
                                  : mword 64) = mword_of_int (8 * Z.of_nat 6))
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite Ei; symmetry; exact Hup)
              with "[] Hrun").
    { iApply (uis_shk_94 with "Hcode"). }
    assert (E94 : add_vec_int (mword_of_int 0x94 : mword 64) 2
                  = mword_of_int 0x96)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E94. iIntros (h4) "Hrun".
    set (n2 := <[Regidx s0_idx := regval_into_reg sp0]> n1).
    assert (Hn2 : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    n2 !!! Regidx q = n1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n1 (Regidx s0_idx) (Regidx q) _ Hq)).
    assert (Hs0_2 : n2 !!! Regidx s0_idx = sp0)
      by exact (upd_eq n1 (Regidx s0_idx) (regval_into_reg sp0)).
    assert (Hsp2 : n2 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 6)))
      by (rewrite (Hn2 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp1).
    assert (Ha0_2 : n2 !!! Regidx a0_idx = (mword_of_int t : mword 64)).
    { rewrite (Hn2 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    (* ---- 0x96  c.beqz a0,0xba -- REFUTED: the node's address is > 0 ---- *)
    iApply (wp_uk_cbeqz γt γd γs γfd h4 n2 (mword_of_int 0x96)
              (mword_of_int 18 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              false (mword_of_int 0xba) n
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_2 (moi_eq_zero t ltac:(unfold Z64; lia));
                    symmetry; apply Z.eqb_neq; lia)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shk_96 with "Hcode"). }
    assert (E96 : add_vec_int (mword_of_int 0x96 : mword 64) 2
                  = mword_of_int 0x98)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E96. iIntros (h5) "Hrun".
    (* ---- 0x98  c.sdsp s1,24(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd h5 n2 (mword_of_int 0x98)
              (mword_of_int 3 : mword 6) s1_idx (uint sp0 - 24) v3 n
              ltac:(rewrite Hsp2 Hsp48 Go3; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw3 Hrun").
    { iApply (uis_shk_98 with "Hcode"). }
    iIntros "Hw3".
    assert (E98 : add_vec_int (mword_of_int 0x98 : mword 64) 2
                  = mword_of_int 0x9a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E98. iIntros (h6) "Hrun".
    (* ---- 0x9a  c.mv s1,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h6 n2 (mword_of_int 0x9a) s1_idx a0_idx
              (mword_of_int t) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_2 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_9a with "Hcode"). }
    assert (E9a : add_vec_int (mword_of_int 0x9a : mword 64) 2
                  = mword_of_int 0x9c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E9a. iIntros (h7) "Hrun".
    set (n3 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int t : mword 64)]> n2).
    assert (Hn3 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    n3 !!! Regidx q = n2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n2 (Regidx s1_idx) (Regidx q) _ Hq)).
    assert (Hs1_3 : n3 !!! Regidx s1_idx = (mword_of_int t : mword 64))
      by exact (upd_eq n2 (Regidx s1_idx) _).
    assert (Ha0_3 : n3 !!! Regidx a0_idx = (mword_of_int t : mword 64))
      by (rewrite (Hn3 a0_idx ltac:(vm_compute; discriminate)); exact Ha0_2).
    (* ---- 0x9c  c.lw a4,0(a0) -- the TYPE word ---- *)
    iApply (wp_uk_clwq γt γd γs γfd h7 n3 (mword_of_int 0x9c)
              (mword_of_int 0 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 6 : mword 3) a0_idx a4_idx DfracDiscarded
              t (mword_of_int (ush_ty c)) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_3 (uint_moi t ltac:(unfold Z64; lia));
                    vm_compute uoff_c4; lia)
              ltac:(pose proof (Z.mod_divide t 8 ltac:(lia)) as Hd;
                    apply Z.mod_divide; [ lia | ];
                    destruct (proj1 Hd Ht8) as [kq Hkq]; exists (2 * kq); lia)
              ltac:(vm_compute; discriminate)
              with "[] Hty Hrun").
    { iApply (uis_shk_9c with "Hcode"). }
    iIntros "_".
    assert (E9c : add_vec_int (mword_of_int 0x9c : mword 64) 2
                  = mword_of_int 0x9e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E9c. iIntros (h8) "Hrun".
    set (n4 := <[Regidx a4_idx
                 := regval_into_reg (sign_extend'
                      64 (mword_of_int (ush_ty c) : mword 32))]> n3).
    assert (Hn4 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                    n4 !!! Regidx q = n3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n3 (Regidx a4_idx) (Regidx q) _ Hq)).
    assert (Ha4_4 : n4 !!! Regidx a4_idx
                    = sign_extend' 64 (mword_of_int (ush_ty c) : mword 32))
      by exact (upd_eq n3 (Regidx a4_idx) _).
    (* ---- 0x9e  c.li a5,5 ---- *)
    iApply (wp_uk_cli γt γd γs γfd h8 n4 (mword_of_int 0x9e)
              (mword_of_int 5 : mword 6) a5_idx n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_9e with "Hcode"). }
    assert (E9e : add_vec_int (mword_of_int 0x9e : mword 64) 2
                  = mword_of_int 0xa0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E9e. iIntros (h9) "Hrun".
    set (n5 := <[Regidx a5_idx
                 := regval_into_reg (sign_extend'
                      64 (mword_of_int 5 : mword 6) : mword 64)]> n4).
    assert (Hn5 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    n5 !!! Regidx q = n4 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n4 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_5 : n5 !!! Regidx a5_idx
                    = (sign_extend' 64 (mword_of_int 5 : mword 6) : mword 64))
      by exact (upd_eq n4 (Regidx a5_idx) _).
    assert (Ha4_5 : n5 !!! Regidx a4_idx
                    = sign_extend' 64 (mword_of_int (ush_ty c) : mword 32))
      by (rewrite (Hn5 a4_idx ltac:(vm_compute; discriminate)); exact Ha4_4).
    (* ---- 0xa0  bltu a5,a4,0xc2 -- REFUTED: the type is at most 5 ---- *)
    iApply (wp_uk_btype γt γd γs γfd h9 n5 (mword_of_int 0xa0)
              (mword_of_int 34 : mword 13) a4_idx a5_idx BLTU false
              (mword_of_int 0xc2) n
              ltac:(rewrite Ha5_5 Ha4_5; symmetry; exact (ush_bltu_false c))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shk_a0 with "Hcode"). }
    assert (Ea0e : add_vec_int (mword_of_int 0xa0 : mword 64) 4
                   = mword_of_int 0xa4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea0e. iIntros (h10) "Hrun".
    assert (Ha0_5 : n5 !!! Regidx a0_idx = (mword_of_int t : mword 64)).
    { rewrite (Hn5 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn4 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_3. }
    (* ---- 0xa4  lwu a5,0(a0) -- the type again, ZERO-extended ---- *)
    iApply (wp_uk_lwuq γt γd γs γfd h10 n5 (mword_of_int 0xa4)
              (mword_of_int 0 : mword 12) a0_idx a5_idx DfracDiscarded
              t (mword_of_int (ush_ty c)) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Ha0_5 (uint_moi t ltac:(unfold Z64; lia));
                    vm_compute uoff_i12; lia)
              ltac:(pose proof (Z.mod_divide t 8 ltac:(lia)) as Hd;
                    apply Z.mod_divide; [ lia | ];
                    destruct (proj1 Hd Ht8) as [kq Hkq]; exists (2 * kq); lia)
              ltac:(vm_compute; discriminate)
              with "[] Hty Hrun").
    { iApply (uis_shk_a4 with "Hcode"). }
    iIntros "_".
    assert (Ea4 : add_vec_int (mword_of_int 0xa4 : mword 64) 4
                  = mword_of_int 0xa8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea4. iIntros (h11) "Hrun".
    set (n6 := <[Regidx a5_idx
                 := regval_into_reg (zero_extend'
                      64 (mword_of_int (ush_ty c) : mword 32))]> n5).
    assert (Hn6 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    n6 !!! Regidx q = n5 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n5 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_6 : n6 !!! Regidx a5_idx
                    = zero_extend' 64 (mword_of_int (ush_ty c) : mword 32))
      by exact (upd_eq n5 (Regidx a5_idx) _).
    (* ---- 0xa8  c.slli a5,a5,2 ---- *)
    iApply (wp_uk_cslli γt γd γs γfd h11 n6 (mword_of_int 0xa8)
              (mword_of_int 2 : mword 6) a5_idx
              (mword_of_int (4 * ush_ty c)) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_6; symmetry; exact (ush_slli_eq c))
              with "[] Hrun").
    { iApply (uis_shk_a8 with "Hcode"). }
    assert (Ea8 : add_vec_int (mword_of_int 0xa8 : mword 64) 2
                  = mword_of_int 0xaa)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea8. iIntros (h12) "Hrun".
    set (n7 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int (4 * ush_ty c)
                                     : mword 64)]> n6).
    assert (Hn7 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    n7 !!! Regidx q = n6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n6 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_7 : n7 !!! Regidx a5_idx
                    = (mword_of_int (4 * ush_ty c) : mword 64))
      by exact (upd_eq n6 (Regidx a5_idx) _).
    (* ---- 0xaa  auipc a4,0x1 ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h12 n7 (mword_of_int 0xaa)
              (mword_of_int 1 : mword 20) a4_idx (mword_of_int 0x10aa) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_aa with "Hcode"). }
    assert (Eaa : add_vec_int (mword_of_int 0xaa : mword 64) 4
                  = mword_of_int 0xae)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eaa. iIntros (h13) "Hrun".
    set (n8 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 0x10aa : mword 64)]> n7).
    assert (Hn8 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                    n8 !!! Regidx q = n7 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n7 (Regidx a4_idx) (Regidx q) _ Hq)).
    assert (Ha4_8 : n8 !!! Regidx a4_idx = (mword_of_int 0x10aa : mword 64))
      by exact (upd_eq n7 (Regidx a4_idx) _).
    (* ---- 0xae  addi a4,a4,750 -- a4 = 0x1398, the table ---- *)
    iApply (wp_uk_addi γt γd γs γfd h13 n8 (mword_of_int 0xae)
              (mword_of_int 750 : mword 12) a4_idx a4_idx
              (mword_of_int SH_JTAB) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha4_8;
                    assert (Es : (sign_extend' 64
                                    (mword_of_int 750 : mword 12) : mword 64)
                                 = mword_of_int 750)
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite Es moi_add; unfold SH_JTAB; f_equal; lia)
              with "[] Hrun").
    { iApply (uis_shk_ae with "Hcode"). }
    assert (Eae : add_vec_int (mword_of_int 0xae : mword 64) 4
                  = mword_of_int 0xb2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eae. iIntros (h14) "Hrun".
    set (n9 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int SH_JTAB : mword 64)]> n8).
    assert (Hn9 : forall q : mword 5, Regidx q <> Regidx a4_idx ->
                    n9 !!! Regidx q = n8 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n8 (Regidx a4_idx) (Regidx q) _ Hq)).
    assert (Ha4_9 : n9 !!! Regidx a4_idx = (mword_of_int SH_JTAB : mword 64))
      by exact (upd_eq n8 (Regidx a4_idx) _).
    assert (Ha5_9 : n9 !!! Regidx a5_idx
                    = (mword_of_int (4 * ush_ty c) : mword 64)).
    { rewrite (Hn9 a5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn8 a5_idx ltac:(vm_compute; discriminate)). exact Ha5_7. }
    (* ---- 0xb2  c.add a5,a5,a4 -- the ROW's address ---- *)
    iApply (wp_uk_cadd γt γd γs γfd h14 n9 (mword_of_int 0xb2) a5_idx a4_idx
              (mword_of_int (SH_JTAB + 4 * ush_ty c)) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_9 Ha4_9 moi_add; f_equal; lia)
              with "[] Hrun").
    { iApply (uis_shk_b2 with "Hcode"). }
    assert (Eb2 : add_vec_int (mword_of_int 0xb2 : mword 64) 2
                  = mword_of_int 0xb4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eb2. iIntros (h15) "Hrun".
    set (n10 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int (SH_JTAB + 4 * ush_ty c)
                                      : mword 64)]> n9).
    assert (Hn10 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                     n10 !!! Regidx q = n9 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n9 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_10 : n10 !!! Regidx a5_idx
                     = (mword_of_int (SH_JTAB + 4 * ush_ty c) : mword 64))
      by exact (upd_eq n9 (Regidx a5_idx) _).
    (* ---- 0xb4  c.lw a5,0(a5) -- THE TABLE READ, out of the TEXT ---- *)
    iApply (wp_uk_clw_text γt γd γs γfd h15 n10 (mword_of_int 0xb4)
              (mword_of_int 0 : mword 5) (mword_of_int 7 : mword 3)
              (mword_of_int 7 : mword 3) a5_idx a5_idx
              (SH_JTAB + 4 * ush_ty c) (ush_jent (ush_ty c)) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha5_10
                      (uint_moi (SH_JTAB + 4 * ush_ty c) (ush_jtab_bnd c));
                    vm_compute uoff_c4; lia)
              (ush_jtab_align c)
              ltac:(vm_compute; discriminate)
              with "[] Hrow Hrun").
    { iApply (uis_shk_b4 with "Hcode"). }
    assert (Eb4 : add_vec_int (mword_of_int 0xb4 : mword 64) 2
                  = mword_of_int 0xb6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eb4. iIntros (h16) "Hrun".
    set (n11 := <[Regidx a5_idx
                  := regval_into_reg (sign_extend'
                       64 (ush_jent (ush_ty c)))]> n10).
    assert (Hn11 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                     n11 !!! Regidx q = n10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n10 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_11 : n11 !!! Regidx a5_idx
                     = sign_extend' 64 (ush_jent (ush_ty c)))
      by exact (upd_eq n10 (Regidx a5_idx) _).
    assert (Ha4_11 : n11 !!! Regidx a4_idx
                     = (mword_of_int SH_JTAB : mword 64)).
    { rewrite (Hn11 a4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn10 a4_idx ltac:(vm_compute; discriminate)). exact Ha4_9. }
    (* ---- 0xb6  c.add a5,a5,a4 -- the ARM's pc ---- *)
    iApply (wp_uk_cadd γt γd γs γfd h16 n11 (mword_of_int 0xb6) a5_idx a4_idx
              (mword_of_int (ush_jarm c)) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_11 Ha4_11; symmetry; exact (ush_jarm_eq c))
              with "[] Hrun").
    { iApply (uis_shk_b6 with "Hcode"). }
    assert (Eb6 : add_vec_int (mword_of_int 0xb6 : mword 64) 2
                  = mword_of_int 0xb8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eb6. iIntros (h17) "Hrun".
    set (n12 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int (ush_jarm c)
                                      : mword 64)]> n11).
    assert (Hn12 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                     n12 !!! Regidx q = n11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n11 (Regidx a5_idx) (Regidx q) _ Hq)).
    (* ---- 0xb8  c.jr a5 -- INTO THE ARM ---- *)
    iApply (wp_uk_cjr γt γd γs γfd h17 n12 (mword_of_int 0xb8) a5_idx
              (mword_of_int (ush_jarm c)) n
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq n11 (Regidx a5_idx)
                               (regval_into_reg (mword_of_int (ush_jarm c)
                                                 : mword 64)));
                    symmetry; exact (ush_jarm_even c))
              with "[] Hrun").
    { iApply (uis_shk_b8 with "Hcode"). }
    iIntros (h18) "Hrun".
    (* ---- and what the arm is handed ---- *)
    assert (Hchain : forall q : mword 5,
              Regidx q <> Regidx a4_idx -> Regidx q <> Regidx a5_idx ->
              n12 !!! Regidx q = n3 !!! Regidx q).
    { intros q H4 H5.
      rewrite (Hn12 q H5) (Hn11 q H5) (Hn10 q H5) (Hn9 q H4) (Hn8 q H4)
              (Hn7 q H5) (Hn6 q H5) (Hn5 q H5) (Hn4 q H4). reflexivity. }
    iApply ("Hcont" $! h18 n12 sp0 with "[%] [%] [%] [%] [%] [%] [Hw5] Hrun").
    - exact Hal8.
    - exact Hlo.
    - rewrite (Hchain csp_rs1 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      rewrite (Hn3 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp2.
    - rewrite (Hchain s0_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      rewrite (Hn3 s0_idx ltac:(vm_compute; discriminate)). exact Hs0_2.
    - rewrite (Hchain s1_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). exact Hs1_3.
    - rewrite (Hchain a0_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). exact Ha0_3.
    - iExists v5. iExact "Hw5".
  Qed.

  (* ===================================================================== *)
  (* §8 WHAT EACH NODE KIND HANDS ITS ARM.                                  *)
  (* ===================================================================== *)
  Lemma ush_cmd_exec (g : gname) (t : Z) (args : list uarg) :
    ush_cmd g t (UExec args) -∗
    uargv g (t + 8) args ∗
    ush_ptr g (t + 8 + 8 * Z.of_nat (length args)) 0 ∗
    ([∗ list] x ∈ args, ush_str g x).
  Proof.
    cbn [ush_cmd]. iIntros "(_ & _ & _ & #A & #B & #C)". iFrame "A B C".
  Qed.

  Lemma ush_cmd_redir (g : gname) (t : Z) (c1 : ushcmd) (file : uarg)
      (mode fd : Z) :
    ush_cmd g t (URedir c1 file mode fd) -∗
    (∃ q : Z, ush_ptr g (t + 8) q ∗ ush_cmd g q c1) ∗
    ush_ptr g (t + 16) (ua_ptr file) ∗ ush_str g file ∗
    ush_w32 g (t + 32) mode ∗ ush_w32 g (t + 36) fd.
  Proof.
    cbn [ush_cmd]. iIntros "(_ & _ & _ & #A & #B & #C & #D & #E)".
    iFrame "A B C D E".
  Qed.

  Lemma ush_cmd_pipe (g : gname) (t : Z) (l r : ushcmd) :
    ush_cmd g t (UPipe l r) -∗
    (∃ q : Z, ush_ptr g (t + 8) q ∗ ush_cmd g q l) ∗
    (∃ q : Z, ush_ptr g (t + 16) q ∗ ush_cmd g q r).
  Proof. cbn [ush_cmd]. iIntros "(_ & _ & _ & #A & #B)". iFrame "A B". Qed.

  Lemma ush_cmd_list (g : gname) (t : Z) (l r : ushcmd) :
    ush_cmd g t (UList l r) -∗
    (∃ q : Z, ush_ptr g (t + 8) q ∗ ush_cmd g q l) ∗
    (∃ q : Z, ush_ptr g (t + 16) q ∗ ush_cmd g q r).
  Proof. cbn [ush_cmd]. iIntros "(_ & _ & _ & #A & #B)". iFrame "A B". Qed.

  Lemma ush_cmd_back (g : gname) (t : Z) (c1 : ushcmd) :
    ush_cmd g t (UBack c1) -∗ ∃ q : Z, ush_ptr g (t + 8) q ∗ ush_cmd g q c1.
  Proof. cbn [ush_cmd]. iIntros "(_ & _ & _ & #A)". iFrame "A". Qed.

  (* argv[0], which is what the EXEC arm's null test looks at: the NUL cap
     when the vector is empty, and the first string's pointer otherwise. *)
  Lemma ush_argv0 (g : gname) (t : Z) (args : list uarg) :
    ush_cmd g t (UExec args) -∗
    match args with
    | [] => ush_ptr g (t + 8) 0
    | x :: _ => ush_ptr g (t + 8) (ua_ptr x) ∗ ush_str g x
    end.
  Proof.
    iIntros "#Ht". iDestruct (ush_cmd_exec with "Ht") as "(#Hv & #Hn & #Hs)".
    destruct args as [| x rest ].
    - rewrite /ush_ptr. cbn [length]. rewrite Z.mul_0_r Z.add_0_r.
      iExact "Hn".
    - iDestruct (uargv_acc g (t + 8) (x :: rest) 0%nat x eq_refl with "Hv")
        as "[[#Hw #Hstr] _]".
      rewrite Z.mul_0_r Z.add_0_r.
      iSplitR; [ iExact "Hw" | ].
      iDestruct (big_sepL_lookup _ (x :: rest) 0%nat x eq_refl with "Hs")
        as "#Hs0". iExact "Hs0".
  Qed.

  (* ===================================================================== *)
  (* §8a FOUR BYTES OF THE FRAME, NAMED AS A WORD.  The [int p[2]] the PIPE *)
  (* arm hands to [pipe] comes back as an unnamed run; the [lw]s that read  *)
  (* p[0] and p[1] want each half as [nth_byte] of a 32-bit word, and any   *)
  (* four bytes are.                                                        *)
  (* ===================================================================== *)
  Local Lemma ush_bytes_as_word (g : gname) (a : Z) (f : nat -> bv 8) :
    ubytes g a 4 f -∗ ∃ wv : mword 32, ubytes g a 4 (nth_byte wv).
  Proof.
    iIntros "Hbs".
    iExists (Z_to_bv 32 (assemble_bytes
                           [f 0%nat; f 1%nat; f 2%nat; f 3%nat])).
    iApply (ubytes_ext g a 4 f _ with "Hbs").
    intros j Hj.
    rewrite (nth_byte_assemble_len 32
               [f 0%nat; f 1%nat; f 2%nat; f 3%nat] j
               ltac:(cbn [length]; lia) ltac:(cbn [length]; lia)).
    destruct j as [| [| [| [| j ]]]]; cbn [list_lookup_total];
      [ reflexivity | reflexivity | reflexivity | reflexivity | lia ].
  Qed.

  Local Lemma ush_pipe_halves (g : gname) (a : Z) (f : nat -> bv 8) :
    ubytes g a 8 f -∗
    ∃ w0 w1 : mword 32,
      ubytes g a 4 (nth_byte w0) ∗ ubytes g (a + 4) 4 (nth_byte w1).
  Proof.
    iIntros "Hbs".
    rewrite (ubytes_split g a 4 8 f ltac:(lia)).
    iDestruct "Hbs" as "[Hlo Hhi]".
    iDestruct (ush_bytes_as_word g a f with "Hlo") as (w0) "Hlo".
    iDestruct (ush_bytes_as_word g (a + Z.of_nat 4)
                 (fun j => f (4 + j)%nat) with "Hhi") as (w1) "Hhi".
    iExists w0, w1. iFrame "Hlo".
    replace (a + 4) with (a + Z.of_nat 4) by lia. iFrame "Hhi".
  Qed.

  (* ===================================================================== *)
  (* §8b [wait(0)] AS A CALL: [c.li a0,0] then [jal ra,<wait>].  All three  *)
  (* of sh's wait sites are this pair, and the row's null-status arm is     *)
  (* what makes the heap cross untouched.                                   *)
  (* ===================================================================== *)
  Local Lemma wp_kshr_wait0 (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc0 pc1 ret : Z) (imm : mword 21) (avail : nat) :
    add_vec_int (mword_of_int pc0 : mword 64) 2 = mword_of_int pc1 ->
    (mword_of_int ShSyms.wait : mword 64)
      = add_vec (mword_of_int pc1 : mword 64) (sign_extend' 64 imm) ->
    (mword_of_int ret : mword 64)
      = add_vec_int (mword_of_int pc1 : mword 64) 4 ->
    eq_vec (access_vec_dec (mword_of_int ShSyms.wait : mword 64) 0) ('b"0")
      = true ->
    ret_pc (mword_of_int ret : mword 64) = mword_of_int ret ->
    shk_code γt -∗
    uinstr_is γt (mword_of_int pc0) true
      (C_LI (mword_of_int 0 : mword 6, Regidx a0_idx)) -∗
    uinstr_is γt (mword_of_int pc1) false (JAL (imm, Regidx ra_idx)) -∗
    urun γt γd γs γfd h m (mword_of_int pc0) avail -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ ucallee_saved m m' ⌝ -∗
       urun γt γd γs γfd h' m' (mword_of_int ret) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros E01 Hsym Hret Hal Hrp. iIntros "#Hcode #Hi0 #Hi1 Hrun Hcont".
    iApply (wp_uk_cli γt γd γs γfd h m (mword_of_int pc0)
              (mword_of_int 0 : mword 6) a0_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "Hi0 Hrun").
    rewrite E01. iIntros (h1) "Hrun".
    set (m1 := <[Regidx a0_idx
                 := regval_into_reg (sign_extend' 64
                      (mword_of_int 0 : mword 6) : mword 64)]> m).
    iApply (wp_kshr_jal γt γd γs γfd h1 m1 pc1 ShSyms.wait ret imm avail
              Hsym Hret Hal with "Hi1 Hrun").
    iIntros (h2) "Hrun".
    set (m2 := <[Regidx ra_idx := (mword_of_int ret : mword 64)]> m1).
    assert (Ha0_2 : uint (m2 !!! Regidx a0_idx) = 0).
    { rewrite /m2 (upd_ne m1 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m1 (upd_eq m (Regidx a0_idx)
                     (regval_into_reg (sign_extend' 64
                        (mword_of_int 0 : mword 6) : mword 64))).
      vm_compute. reflexivity. }
    assert (Hra2 : m2 !!! Regidx ra_idx = (mword_of_int ret : mword 64))
      by exact (upd_eq m1 (Regidx ra_idx) _).
    iApply (wp_kshr_wait γt γd γs γfd h2 m2 avail Ha0_2 with "Hcode Hrun").
    iIntros (h3 ret') "Hrun". rewrite Hra2 Hrp.
    iApply ("Hcont" $! h3 _ with "[%] Hrun").
    intros q Hq.
    rewrite (upd_ne _ (Regidx a0_idx) (Regidx q) ret'
               (ushr_cs_ne q a0_idx Hq
                  ltac:(right; left; vm_compute; reflexivity))).
    rewrite (upd_ne _ (Regidx a7_idx) (Regidx q) _
               (ushr_cs_ne q a7_idx Hq
                  ltac:(right; right; right; right; vm_compute; reflexivity))).
    rewrite /m2 (upd_ne m1 (Regidx ra_idx) (Regidx q) _
                   (ushr_cs_ne q ra_idx Hq
                      ltac:(left; vm_compute; reflexivity))).
    rewrite /m1 (upd_ne m (Regidx a0_idx) (Regidx q) _
                   (ushr_cs_ne q a0_idx Hq
                      ltac:(right; left; vm_compute; reflexivity))).
    reflexivity.
  Qed.

  (* ---- [exit(k)] AS A CALL: [c.li a0,k] then [jal ra,<exit>] ---------- *)
  Local Lemma wp_kshr_exit0 (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc0 pc1 ret : Z) (k : mword 6) (imm : mword 21) (avail : nat) :
    add_vec_int (mword_of_int pc0 : mword 64) 2 = mword_of_int pc1 ->
    (mword_of_int ShSyms.exit : mword 64)
      = add_vec (mword_of_int pc1 : mword 64) (sign_extend' 64 imm) ->
    (mword_of_int ret : mword 64)
      = add_vec_int (mword_of_int pc1 : mword 64) 4 ->
    eq_vec (access_vec_dec (mword_of_int ShSyms.exit : mword 64) 0) ('b"0")
      = true ->
    shk_code γt -∗
    uinstr_is γt (mword_of_int pc0) true (C_LI (k, Regidx a0_idx)) -∗
    uinstr_is γt (mword_of_int pc1) false (JAL (imm, Regidx ra_idx)) -∗
    urun γt γd γs γfd h m (mword_of_int pc0) avail -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros E01 Hsym Hret Hal. iIntros "#Hcode #Hi0 #Hi1 Hrun".
    iApply (wp_uk_cli γt γd γs γfd h m (mword_of_int pc0) k a0_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "Hi0 Hrun").
    rewrite E01. iIntros (h1) "Hrun".
    iApply (wp_kshr_jal γt γd γs γfd h1 _ pc1 ShSyms.exit ret imm avail
              Hsym Hret Hal with "Hi1 Hrun").
    iIntros (h2) "Hrun".
    iApply (wp_ksh_exit γt γd γs γfd h2 _ avail with "Hcode Hrun").
  Qed.

  (* ===================================================================== *)
  (* §9 runcmd AT A NULL COMMAND.  [runcmd(0)] is [exit(1)] and nothing     *)
  (* else; it is a separate lemma because the walk below is about a node    *)
  (* that EXISTS, and [ush_cmd] refutes the test this one takes.            *)
  (* ===================================================================== *)
  Lemma wp_kshr_runcmd_null (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (n : nat) :
    m !!! Regidx a0_idx = (mword_of_int 0 : mword 64) ->
    shk_code γt -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.runcmd) (6 + n) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0. iIntros "#Hcode Hrun".
    rewrite shr_runcmd.
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    assert (Hlo : 48 <= uint sp0) by lia.
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 6)))
                   = bv_unsigned sp0 - 48).
    { replace (- (8 * Z.of_nat 6)) with (-48) by lia.
      exact (uv_avi_neg sp0 48 ltac:(lia)
               ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp48 : uint (add_vec_int sp0 (- (8 * Z.of_nat 6)))
                    = uint sp0 - 48)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Go5 : uoff_sdsp (mword_of_int 5 : mword 6) = 40)
      by (vm_compute; reflexivity).
    assert (Go4 : uoff_sdsp (mword_of_int 4 : mword 6) = 32)
      by (vm_compute; reflexivity).
    assert (Go3 : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
      by (vm_compute; reflexivity).
    iApply (wp_uk_caddi16sp_dn γt γd γs γfd h m (mword_of_int 0x8e)
              (mword_of_int 61 : mword 6) 6 n
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_8e with "Hcode"). }
    assert (E8e : add_vec_int (mword_of_int 0x8e : mword 64) 2
                  = mword_of_int 0x90)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp ustack_6 E8e.
    iIntros "(_ & [%v1 Hw1] & [%v2 Hw2] & [%v3 Hw3] & _ & _ & _)".
    iIntros (h1) "Hrun".
    set (n1 := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 6)))]> m).
    assert (Hsp1 : n1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 6)))
      by exact (upd_eq m (Regidx csp_rs1) _).
    assert (Hn1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    n1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    iApply (wp_uk_csdsp γt γd γs γfd h1 n1 (mword_of_int 0x90)
              (mword_of_int 5 : mword 6) ra_idx (uint sp0 - 8) v1 n
              ltac:(rewrite Hsp1 Hsp48 Go5; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw1 Hrun").
    { iApply (uis_shk_90 with "Hcode"). }
    iIntros "_".
    assert (E90 : add_vec_int (mword_of_int 0x90 : mword 64) 2
                  = mword_of_int 0x92)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E90. iIntros (h2) "Hrun".
    iApply (wp_uk_csdsp γt γd γs γfd h2 n1 (mword_of_int 0x92)
              (mword_of_int 4 : mword 6) s0_idx (uint sp0 - 16) v2 n
              ltac:(rewrite Hsp1 Hsp48 Go4; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw2 Hrun").
    { iApply (uis_shk_92 with "Hcode"). }
    iIntros "_".
    assert (E92 : add_vec_int (mword_of_int 0x92 : mword 64) 2
                  = mword_of_int 0x94)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E92. iIntros (h3) "Hrun".
    iApply (wp_uk_caddi4spn γt γd γs γfd h3 n1 (mword_of_int 0x94)
              (mword_of_int 0 : mword 3) (mword_of_int 12 : mword 8) s0_idx
              (add_vec (n1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))
              n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              eq_refl
              with "[] Hrun").
    { iApply (uis_shk_94 with "Hcode"). }
    assert (E94 : add_vec_int (mword_of_int 0x94 : mword 64) 2
                  = mword_of_int 0x96)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E94. iIntros (h4) "Hrun".
    set (n2 := <[Regidx s0_idx
                 := regval_into_reg
                      (add_vec (n1 !!! Regidx csp_rs1)
                         (sign_extend' 64
                            (caddi4spn_imm (mword_of_int 12 : mword 8))))]> n1).
    assert (Hn2 : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    n2 !!! Regidx q = n1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n1 (Regidx s0_idx) (Regidx q) _ Hq)).
    assert (Hsp2 : n2 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 6)))
      by (rewrite (Hn2 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp1).
    assert (Ha0_2 : n2 !!! Regidx a0_idx = (mword_of_int 0 : mword 64)).
    { rewrite (Hn2 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    (* ---- 0x96  c.beqz a0,0xba -- TAKEN ---- *)
    iApply (wp_uk_cbeqz γt γd γs γfd h4 n2 (mword_of_int 0x96)
              (mword_of_int 18 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              true (mword_of_int 0xba) n
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_2; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_96 with "Hcode"). }
    iIntros (h5) "Hrun".
    (* ---- 0xba  c.sdsp s1,24(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd h5 n2 (mword_of_int 0xba)
              (mword_of_int 3 : mword 6) s1_idx (uint sp0 - 24) v3 n
              ltac:(rewrite Hsp2 Hsp48 Go3; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw3 Hrun").
    { iApply (uis_shk_ba with "Hcode"). }
    iIntros "_".
    assert (Eba : add_vec_int (mword_of_int 0xba : mword 64) 2
                  = mword_of_int 0xbc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eba. iIntros (h6) "Hrun".
    (* ---- 0xbc  c.li a0,1 ; 0xbe  jal ra,0xc86 <exit> ---- *)
    iApply (wp_kshr_exit0 γt γd γs γfd h6 n2 0xbc 0xbe 0xc2
              (mword_of_int 1 : mword 6) (mword_of_int 3016 : mword 21) n
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcode [] [] Hrun").
    { iApply (uis_shk_bc with "Hcode"). }
    { iApply (uis_shk_be with "Hcode"). }
  Qed.

  (* WHAT AN ARM CARRIES IN REGISTERS: the frame pointer and the node.
     Both are callee-saved, so every call in every arm preserves them and
     the plumbing is two lemmas rather than one rewrite per call. *)
  Definition ush_st (m : regfile) (sp0 : mword 64) (t : Z) : Prop :=
    m !!! Regidx s0_idx = sp0 /\
    m !!! Regidx s1_idx = (mword_of_int t : mword 64).

  Lemma ush_st_cs (m m' : regfile) (sp0 : mword 64) (t : Z) :
    ush_st m sp0 t -> ucallee_saved m m' -> ush_st m' sp0 t.
  Proof.
    intros [H0 H1] Hcs. split.
    - rewrite (Hcs s0_idx ltac:(vm_compute; reflexivity)). exact H0.
    - rewrite (Hcs s1_idx ltac:(vm_compute; reflexivity)). exact H1.
  Qed.

  Lemma ush_st_upd (m : regfile) (sp0 : mword 64) (t : Z) (q : mword 5)
      (v : mword 64) :
    ush_st m sp0 t -> uint q <> 8 -> uint q <> 9 ->
    ush_st (<[Regidx q := v]> m) sp0 t.
  Proof.
    intros [H0 H1] H8 H9. split.
    - rewrite (upd_ne m (Regidx q) (Regidx s0_idx) v
                 (ushr_ridx_ne s0_idx q
                    ltac:(assert (Hz : uint s0_idx = 8)
                            by (vm_compute; reflexivity); lia))).
      exact H0.
    - rewrite (upd_ne m (Regidx q) (Regidx s1_idx) v
                 (ushr_ridx_ne s1_idx q
                    ltac:(assert (Hz : uint s1_idx = 9)
                            by (vm_compute; reflexivity); lia))).
      exact H1.
  Qed.

  (* ===================================================================== *)
  (* [lw a0,<off>(s0)] then [jal ra,<a quiet stub>] -- the PIPE arm's fd    *)
  (* plumbing, six times over with two different callees.                   *)
  (* ===================================================================== *)
  Local Lemma wp_kshr_fd_call (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc0 pc1 ret sym num : Z) (imm12 : mword 12) (imm : mword 21)
      (sp0 : mword 64) (a : Z) (wv : mword 32) (avail : nat)
      (Hstub : forall (h0 : CpuId) (m0 : regfile) (av : nat),
         shk_code γt -∗
         urun γt γd γs γfd h0 m0 (mword_of_int sym) av -∗
         (∀ (h1 : CpuId) (r : mword 64),
            urun γt γd γs γfd h1
              (<[Regidx a0_idx := r]>
                 (<[Regidx a7_idx := (mword_of_int num : mword 64)]> m0))
              (ret_pc (m0 !!! Regidx ra_idx)) av -∗
            WP (Loop : expr riscv_lang)) -∗
         WP (Loop : expr riscv_lang)) :
    m !!! Regidx s0_idx = sp0 ->
    a = uint sp0 + uoff_i12 imm12 ->
    a mod 4 = 0 ->
    add_vec_int (mword_of_int pc0 : mword 64) 4 = mword_of_int pc1 ->
    (mword_of_int sym : mword 64)
      = add_vec (mword_of_int pc1 : mword 64) (sign_extend' 64 imm) ->
    (mword_of_int ret : mword 64)
      = add_vec_int (mword_of_int pc1 : mword 64) 4 ->
    eq_vec (access_vec_dec (mword_of_int sym : mword 64) 0) ('b"0") = true ->
    ret_pc (mword_of_int ret : mword 64) = mword_of_int ret ->
    shk_code γt -∗
    uinstr_is γt (mword_of_int pc0) false
      (LOAD (imm12, Regidx s0_idx, Regidx a0_idx, false, 4)) -∗
    uinstr_is γt (mword_of_int pc1) false (JAL (imm, Regidx ra_idx)) -∗
    ubytes γd a 4 (nth_byte wv) -∗
    urun γt γd γs γfd h m (mword_of_int pc0) avail -∗
    (ubytes γd a 4 (nth_byte wv) -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         urun γt γd γs γfd h' m' (mword_of_int ret) avail -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hs0 Ha Hal E01 Hsym Hret Halv Hrp.
    iIntros "#Hcode #Hi0 #Hi1 Hbs Hrun Hcont".
    iApply (wp_uk_lw γt γd γs γfd h m (mword_of_int pc0) imm12 s0_idx a0_idx
              a wv avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs0; exact Ha) Hal
              ltac:(vm_compute; discriminate)
              with "Hi0 Hbs Hrun").
    iIntros "Hbs". rewrite E01. iIntros (h1) "Hrun".
    iApply (wp_kshr_qcall γt γd γs γfd h1 _ pc1 sym ret num imm avail Hstub
              Hsym Hret Halv Hrp with "Hcode Hi1 Hrun").
    iIntros (h2 m' r) "%Hcs _ Hrun".
    iApply ("Hcont" with "Hbs [%] Hrun").
    intros q Hq.
    rewrite (Hcs q Hq).
    exact (upd_ne m (Regidx a0_idx) (Regidx q) _
             (ushr_cs_ne q a0_idx Hq
                ltac:(right; left; vm_compute; reflexivity))).
  Qed.

  (* fork's return value tested against zero, at the abstract pid the leaf
     hands back: the parent's is non-zero by the leaf's own arm. *)
  Local Lemma ush_neqv_true (x : mword 64) :
    x <> (mword_of_int 0 : mword 64) -> neq_vec x zero_reg = true.
  Proof.
    intros H. unfold neq_vec.
    rewrite (proj2 (eq_vec_false_iff x zero_reg)
               ltac:(rewrite zero_reg_moi; exact H)).
    reflexivity.
  Qed.

  (* the two payload shapes the three forking arms carry across [fork] *)
  Local Lemma forkable_ush_pay (t : Z) (c : ushcmd) :
    Forkable (fun gt gd _ => (ush_jtab gt ∗ ush_cmd gd t c)%I).
  Proof.
    apply forkable_sep; [ apply forkable_ush_jtab | apply ush_cmd_forkable ].
  Qed.

  Local Lemma forkable_ush_paypipe (t a b : Z) (c : ushcmd) (w0 w1 : mword 32) :
    Forkable (fun gt gd _ => (ush_jtab gt ∗ ush_cmd gd t c
                              ∗ ubytes gd a 4 (nth_byte w0)
                              ∗ ubytes gd b 4 (nth_byte w1))%I).
  Proof.
    apply forkable_sep; [ apply forkable_ush_jtab | ].
    apply forkable_sep; [ apply ush_cmd_forkable | ].
    apply forkable_sep; apply forkable_ubytes.
  Qed.

  (* ===================================================================== *)
  (* §10 runcmd, WHOLE -- THE TREE WALK.                                    *)
  (*                                                                       *)
  (* ORDINARY STRUCTURAL INDUCTION on the command tree.  Four of the five   *)
  (* arms recurse, and each recursion is one 48-byte frame deeper, so the   *)
  (* budget is [6 * ush_ht c] words plus the constant every arm needs       *)
  (* ([2] for fork1's own frame, [Dg] for the diagnostic subtree) plus the  *)
  (* caller's tail.  A child's instance of the theorem is this one with the *)
  (* surplus rolled into that tail, which is what makes the induction       *)
  (* hypothesis applicable at a SMALLER height without weakening the        *)
  (* statement.                                                             *)
  (*                                                                       *)
  (* WHAT EACH ARM CONSUMES:                                                *)
  (*   EXEC  -- [wp_kshr_exec] (the -1 arm), [wp_kshr_exit0].               *)
  (*   REDIR -- [wp_ksh_close], [wp_ksh_open] (both quiet), then ITSELF.    *)
  (*   LIST  -- [wp_kshr_fork1] (two continuations), [wp_kshr_wait0],       *)
  (*            then ITSELF twice, once in each process.                    *)
  (*   PIPE  -- [wp_kshr_pipe] (the window row at a0, cap 8), two           *)
  (*            [wp_kshr_fork1]s, [wp_ksh_close] x6, [wp_kshr_dup] x2,      *)
  (*            [wp_kshr_wait0] x2, then ITSELF twice.                      *)
  (*   BACK  -- [wp_kshr_fork1], then ITSELF in the child.                  *)
  (*                                                                       *)
  (* DEPENDS ON [ush_diag_leaf]: EXEC's returning exec, REDIR's failing     *)
  (* open, PIPE's failing pipe, and fork1's -1 all end in the printer.      *)
  (* ===================================================================== *)
  Lemma wp_kshr_runcmd (c : ushcmd) :
    forall (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (t szv : Z) (n : nat),
      m !!! Regidx a0_idx = (mword_of_int t : mword 64) ->
      shk_code γt -∗ ush_jtab γt -∗ ush_cmd γd t c -∗ usz γs szv -∗
      urun γt γd γs γfd h m (mword_of_int ShSyms.runcmd)
        (6 * ush_ht c + (2 + (Dg + n))) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    induction c as [ args | c1 IH file mode fd | l IHl r IHr
                   | l IHl r IHr | c1 IH ];
      intros γt γd γs γfd h m t szv n Ha0;
      iIntros "#Hcode #Hjt #Htree Hsz Hrun";
      iDestruct (ush_jtab_ro with "Hjt") as "#Hro";
      iDestruct (ush_cmd_addr with "Htree") as %[Htr Ht8];
      assert (Ht4 : t mod 4 = 0)
        by (pose proof (Z.mod_divide t 8 ltac:(lia)) as Hd;
            apply Z.mod_divide; [ lia | ];
            destruct (proj1 Hd Ht8) as [kq Hkq]; exists (2 * kq); lia).

    - (* =================== EXEC =================== *)
      iDestruct (ush_argv0 with "Htree") as "#Hav".
      replace (6 * ush_ht (UExec args) + (2 + (Dg + n)))%nat
        with (6 + (2 + (Dg + n)))%nat by (cbn [ush_ht]; lia).
      iApply (wp_kshr_entry γt γd γs γfd (UExec args) h m t (2 + (Dg + n)) Ha0
                with "Hcode Hjt Htree Hrun").
      iIntros (h1 m1 sp0) "%Hal8 %Hlo %Hsp1 %Hs0_1 %Hs1_1 %Ha0_1 _ Hrun".
      assert (E8 : (t + 8) mod 8 = 0)
        by (rewrite Zplus_mod Ht8; reflexivity).
      assert (Ece : add_vec_int (mword_of_int 0xce : mword 64) 2
                    = mword_of_int 0xd0)
        by (apply bv_eq; vm_compute; reflexivity).
      destruct args as [| x rest ].
      + (* ---- argv[0] is the NUL cap: exit(1) ---- *)
        iApply (wp_uk_cldq γt γd γs γfd h1 m1 (mword_of_int 0xce)
                  (mword_of_int 1 : mword 5) (mword_of_int 2 : mword 3)
                  (mword_of_int 2 : mword 3) a0_idx a0_idx DfracDiscarded
                  (t + 8) (mword_of_int 0) (2 + (Dg + n))
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(rewrite Ha0_1 (uint_moi t ltac:(unfold Z64; lia));
                        vm_compute uoff_c8; lia)
                  E8 ltac:(vm_compute; discriminate)
                  with "[] Hav Hrun").
        { iApply (uis_shk_ce with "Hcode"). }
        iIntros "_". rewrite Ece. iIntros (h2) "Hrun".
        set (k1 := <[Regidx a0_idx
                     := regval_into_reg (mword_of_int 0 : mword 64)]> m1).
        iApply (wp_uk_cbeqz γt γd γs γfd h2 k1 (mword_of_int 0xd0)
                  (mword_of_int 16 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                  true (mword_of_int 0xf0) (2 + (Dg + n))
                  ltac:(vm_compute; reflexivity)
                  ltac:(rewrite /k1 (upd_eq m1 (Regidx a0_idx)
                                       (mword_of_int 0 : mword 64));
                        vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(intros _; vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_shk_d0 with "Hcode"). }
        iIntros (h3) "Hrun".
        iApply (wp_kshr_exit0 γt γd γs γfd h3 k1 0xf0 0xf2 0xf6
                  (mword_of_int 1 : mword 6) (mword_of_int 2964 : mword 21)
                  (2 + (Dg + n))
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcode [] [] Hrun").
        { iApply (uis_shk_f0 with "Hcode"). }
        { iApply (uis_shk_f2 with "Hcode"). }
      + (* ---- argv[0] is a string: exec, and it can only come back -1 ---- *)
        iDestruct "Hav" as "[#Hw0 #Hstr]".
        iDestruct "Hstr" as "[%Hxr #Hxs]".
        iApply (wp_uk_cldq γt γd γs γfd h1 m1 (mword_of_int 0xce)
                  (mword_of_int 1 : mword 5) (mword_of_int 2 : mword 3)
                  (mword_of_int 2 : mword 3) a0_idx a0_idx DfracDiscarded
                  (t + 8) (mword_of_int (ua_ptr x)) (2 + (Dg + n))
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(rewrite Ha0_1 (uint_moi t ltac:(unfold Z64; lia));
                        vm_compute uoff_c8; lia)
                  E8 ltac:(vm_compute; discriminate)
                  with "[] Hw0 Hrun").
        { iApply (uis_shk_ce with "Hcode"). }
        iIntros "_". rewrite Ece. iIntros (h2) "Hrun".
        set (k1 := <[Regidx a0_idx
                     := regval_into_reg (mword_of_int (ua_ptr x)
                                         : mword 64)]> m1).
        assert (Hk1 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                        k1 !!! Regidx q = m1 !!! Regidx q)
          by (intros q Hq; exact (upd_ne m1 (Regidx a0_idx) (Regidx q) _ Hq)).
        assert (Hs1_k : k1 !!! Regidx s1_idx = (mword_of_int t : mword 64))
          by (rewrite (Hk1 s1_idx ltac:(vm_compute; discriminate));
              exact Hs1_1).
        iApply (wp_uk_cbeqz γt γd γs γfd h2 k1 (mword_of_int 0xd0)
                  (mword_of_int 16 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                  false (mword_of_int 0xf0) (2 + (Dg + n))
                  ltac:(vm_compute; reflexivity)
                  ltac:(rewrite /k1 (upd_eq m1 (Regidx a0_idx)
                                       (mword_of_int (ua_ptr x) : mword 64));
                        rewrite (moi_eq_zero (ua_ptr x)
                                   ltac:(unfold Z64; lia));
                        symmetry; apply Z.eqb_neq; lia)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(discriminate)
                  with "[] Hrun").
        { iApply (uis_shk_d0 with "Hcode"). }
        assert (Ed0 : add_vec_int (mword_of_int 0xd0 : mword 64) 2
                      = mword_of_int 0xd2)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite Ed0. iIntros (h3) "Hrun".
        (* ---- 0xd2  addi a1,s1,8 -- &argv[0] ---- *)
        iApply (wp_uk_addi γt γd γs γfd h3 k1 (mword_of_int 0xd2)
                  (mword_of_int 8 : mword 12) s1_idx a1_idx
                  (mword_of_int (t + 8)) (2 + (Dg + n))
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; discriminate)
                  ltac:(rewrite Hs1_k;
                        assert (Es : (sign_extend' 64
                                        (mword_of_int 8 : mword 12) : mword 64)
                                     = mword_of_int 8)
                          by (apply bv_eq; vm_compute; reflexivity);
                        rewrite Es moi_add; reflexivity)
                  with "[] Hrun").
        { iApply (uis_shk_d2 with "Hcode"). }
        assert (Ed2 : add_vec_int (mword_of_int 0xd2 : mword 64) 4
                      = mword_of_int 0xd6)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite Ed2. iIntros (h4) "Hrun".
        set (k2 := <[Regidx a1_idx
                     := regval_into_reg (mword_of_int (t + 8)
                                         : mword 64)]> k1).
        (* ---- 0xd6  jal ra,0xcbe <exec> ---- *)
        iApply (wp_kshr_jal γt γd γs γfd h4 k2 0xd6 ShSyms.exec 0xda
                  (mword_of_int 3048 : mword 21) (2 + (Dg + n))
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_shk_d6 with "Hcode"). }
        iIntros (h5) "Hrun".
        set (k3 := <[Regidx ra_idx := (mword_of_int 0xda : mword 64)]> k2).
        assert (Hrk3 : ret_pc (k3 !!! Regidx ra_idx)
                       = (mword_of_int 0xda : mword 64))
          by (rewrite /k3 (upd_eq k2 (Regidx ra_idx) _);
              apply bv_eq; vm_compute; reflexivity).
        iApply (wp_kshr_exec γt γd γs γfd h5 k3 (2 + (Dg + n))
                  with "Hcode Hrun").
        rewrite Hrk3. iIntros (h6) "Hrun".
        (* ---- 0xda: "exec %s failed" -- THE DIAGNOSTIC CUT ---- *)
        set (k4 := <[Regidx a0_idx := (mword_of_int (-1) : mword 64)]>
                     (<[Regidx a7_idx := (mword_of_int 7 : mword 64)]> k3)).
        assert (Hs1_k4 : uint (k4 !!! Regidx s1_idx) = t).
        { rewrite /k4 (upd_ne _ (Regidx a0_idx) (Regidx s1_idx) _
                         ltac:(vm_compute; discriminate)).
          rewrite (upd_ne k3 (Regidx a7_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
          rewrite /k3 (upd_ne k2 (Regidx ra_idx) (Regidx s1_idx) _
                         ltac:(vm_compute; discriminate)).
          rewrite /k2 (upd_ne k1 (Regidx a1_idx) (Regidx s1_idx) _
                         ltac:(vm_compute; discriminate)).
          rewrite Hs1_k. apply uint_moi. unfold Z64. lia. }
        replace (2 + (Dg + n))%nat with (Dg + (2 + n))%nat by lia.
        iApply (ush_diag_leaf γt γd γs γfd h6 k4 0xda (2 + n)
                  ltac:(right; left; split;
                        [ reflexivity | rewrite Hs1_k4; exact Ht8 ])
                  with "Hcode Hro [] Hrun").
        rewrite /ush_diag_res.
        destruct (decide ((0xda : Z) = 0xda)) as [_ | Hc];
          [ | exfalso; exact (Hc eq_refl) ].
        iExists x. rewrite Hs1_k4. iSplitR; [ iExact "Hw0" | ].
        iSplitR; [ iPureIntro; exact Hxr | iExact "Hxs" ].

    - (* =================== REDIR =================== *)
      iDestruct (ush_cmd_redir with "Htree") as "(#Hsub & #Hfp & #Hfs & #Hmo & #Hfd)".
      iDestruct "Hsub" as (q) "[#Hqp #Hqc]".
      iDestruct "Hfs" as "[%Hfr #Hfsb]".
      replace (6 * ush_ht (URedir c1 file mode fd) + (2 + (Dg + n)))%nat
        with (6 + (6 * ush_ht c1 + (2 + (Dg + n))))%nat
        by (cbn [ush_ht]; lia).
      iApply (wp_kshr_entry γt γd γs γfd (URedir c1 file mode fd) h m t
                (6 * ush_ht c1 + (2 + (Dg + n))) Ha0
                with "Hcode Hjt Htree Hrun").
      iIntros (h1 m1 sp0) "%Hal8 %Hlo %Hsp1 %Hs0_1 %Hs1_1 %Ha0_1 _ Hrun".
      set (av := (6 * ush_ht c1 + (2 + (Dg + n)))%nat).
      (* ---- 0xf6  c.lw a0,36(a0) -- rcmd->fd ---- *)
      iApply (wp_uk_clwq γt γd γs γfd h1 m1 (mword_of_int 0xf6)
                (mword_of_int 9 : mword 5) (mword_of_int 2 : mword 3)
                (mword_of_int 2 : mword 3) a0_idx a0_idx DfracDiscarded
                (t + 36) (mword_of_int fd) av
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0_1 (uint_moi t ltac:(unfold Z64; lia));
                      vm_compute uoff_c4; lia)
                ltac:(rewrite Zplus_mod Ht4; reflexivity)
                ltac:(vm_compute; discriminate)
                with "[] Hfd Hrun").
      { iApply (uis_shk_f6 with "Hcode"). }
      iIntros "_".
      assert (Ef6 : add_vec_int (mword_of_int 0xf6 : mword 64) 2
                    = mword_of_int 0xf8)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ef6. iIntros (h2) "Hrun".
      set (k1 := <[Regidx a0_idx
                   := regval_into_reg (sign_extend'
                        64 (mword_of_int fd : mword 32))]> m1).
      assert (Hs1_k1 : k1 !!! Regidx s1_idx = (mword_of_int t : mword 64))
        by (rewrite /k1 (upd_ne m1 (Regidx a0_idx) (Regidx s1_idx) _
                           ltac:(vm_compute; discriminate)); exact Hs1_1).
      (* ---- 0xf8  jal ra,0xcae <close> ---- *)
      iApply (wp_kshr_qcall γt γd γs γfd h2 k1 0xf8 ShSyms.close 0xfc 21
                (mword_of_int 2998 : mword 21) av
                (wp_ksh_close γt γd γs γfd)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcode [] Hrun").
      { iApply (uis_shk_f8 with "Hcode"). }
      iIntros (h3 k2 r1) "%Hcs2 _ Hrun".
      assert (Hs1_k2 : k2 !!! Regidx s1_idx = (mword_of_int t : mword 64))
        by (rewrite (Hcs2 s1_idx ltac:(vm_compute; reflexivity)); exact Hs1_k1).
      (* ---- 0xfc  c.lw a1,32(s1) -- rcmd->mode ---- *)
      iApply (wp_uk_clwq γt γd γs γfd h3 k2 (mword_of_int 0xfc)
                (mword_of_int 8 : mword 5) (mword_of_int 1 : mword 3)
                (mword_of_int 3 : mword 3) s1_idx a1_idx DfracDiscarded
                (t + 32) (mword_of_int mode) av
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(rewrite Hs1_k2 (uint_moi t ltac:(unfold Z64; lia));
                      vm_compute uoff_c4; lia)
                ltac:(rewrite Zplus_mod Ht4; reflexivity)
                ltac:(vm_compute; discriminate)
                with "[] Hmo Hrun").
      { iApply (uis_shk_fc with "Hcode"). }
      iIntros "_".
      assert (Efc : add_vec_int (mword_of_int 0xfc : mword 64) 2
                    = mword_of_int 0xfe)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Efc. iIntros (h4) "Hrun".
      set (k3 := <[Regidx a1_idx
                   := regval_into_reg (sign_extend'
                        64 (mword_of_int mode : mword 32))]> k2).
      assert (Hs1_k3 : k3 !!! Regidx s1_idx = (mword_of_int t : mword 64))
        by (rewrite /k3 (upd_ne k2 (Regidx a1_idx) (Regidx s1_idx) _
                           ltac:(vm_compute; discriminate)); exact Hs1_k2).
      (* ---- 0xfe  c.ld a0,16(s1) -- rcmd->file ---- *)
      iApply (wp_uk_cldq γt γd γs γfd h4 k3 (mword_of_int 0xfe)
                (mword_of_int 2 : mword 5) (mword_of_int 1 : mword 3)
                (mword_of_int 2 : mword 3) s1_idx a0_idx DfracDiscarded
                (t + 16) (mword_of_int (ua_ptr file)) av
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(rewrite Hs1_k3 (uint_moi t ltac:(unfold Z64; lia));
                      vm_compute uoff_c8; lia)
                ltac:(rewrite Zplus_mod Ht8; reflexivity)
                ltac:(vm_compute; discriminate)
                with "[] Hfp Hrun").
      { iApply (uis_shk_fe with "Hcode"). }
      iIntros "_".
      assert (Efe : add_vec_int (mword_of_int 0xfe : mword 64) 2
                    = mword_of_int 0x100)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Efe. iIntros (h5) "Hrun".
      set (k4 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int (ua_ptr file)
                                       : mword 64)]> k3).
      assert (Hs1_k4 : k4 !!! Regidx s1_idx = (mword_of_int t : mword 64))
        by (rewrite /k4 (upd_ne k3 (Regidx a0_idx) (Regidx s1_idx) _
                           ltac:(vm_compute; discriminate)); exact Hs1_k3).
      (* ---- 0x100  jal ra,0xcc6 <open> ---- *)
      iApply (wp_kshr_qcall γt γd γs γfd h5 k4 0x100 ShSyms.open 0x104 15
                (mword_of_int 3014 : mword 21) av
                (wp_ksh_open γt γd γs γfd)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcode [] Hrun").
      { iApply (uis_shk_100 with "Hcode"). }
      iIntros (h6 k5 r2) "%Hcs5 _ Hrun".
      assert (Hs1_k5 : k5 !!! Regidx s1_idx = (mword_of_int t : mword 64))
        by (rewrite (Hcs5 s1_idx ltac:(vm_compute; reflexivity)); exact Hs1_k4).
      (* ---- 0x104  bltz a0,0x10e -- open failed? ---- *)
      iApply (wp_uk_btype0 γt γd γs γfd h6 k5 (mword_of_int 0x104)
                (mword_of_int 10 : mword 13) a0_idx BLT
                (uv_btaken BLT (k5 !!! Regidx a0_idx) zero_reg)
                (mword_of_int 0x10e) av
                eq_refl
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_104 with "Hcode"). }
      assert (E104 : add_vec_int (mword_of_int 0x104 : mword 64) 4
                     = mword_of_int 0x108)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E104. iIntros (h7) "Hrun".
      destruct (uv_btaken BLT (k5 !!! Regidx a0_idx) zero_reg).
      + (* ---- open failed: "open %s failed" ; exit(1) ---- *)
        assert (Hs1u : uint (k5 !!! Regidx s1_idx) = t)
          by (rewrite Hs1_k5; apply uint_moi; unfold Z64; lia).
        replace av with (Dg + (6 * ush_ht c1 + (2 + n)))%nat
          by (unfold av; lia).
        iApply (ush_diag_leaf γt γd γs γfd h7 k5 0x10e
                  (6 * ush_ht c1 + (2 + n))
                  ltac:(right; right; split;
                        [ reflexivity | rewrite Hs1u; exact Ht8 ])
                  with "Hcode Hro [] Hrun").
        rewrite /ush_diag_res.
        destruct (decide ((0x10e : Z) = 0xda)) as [Hc | _];
          [ exfalso; discriminate Hc | ].
        destruct (decide ((0x10e : Z) = 0x10e)) as [_ | Hc];
          [ | exfalso; exact (Hc eq_refl) ].
        iExists file. rewrite Hs1u. iSplitR; [ iExact "Hfp" | ].
        iSplitR; [ iPureIntro; exact Hfr | iExact "Hfsb" ].
      + (* ---- open succeeded: runcmd(rcmd->cmd) ---- *)
        iApply (wp_uk_cldq γt γd γs γfd h7 k5 (mword_of_int 0x108)
                  (mword_of_int 1 : mword 5) (mword_of_int 1 : mword 3)
                  (mword_of_int 2 : mword 3) s1_idx a0_idx DfracDiscarded
                  (t + 8) (mword_of_int q) av
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(rewrite Hs1_k5 (uint_moi t ltac:(unfold Z64; lia));
                        vm_compute uoff_c8; lia)
                  ltac:(rewrite Zplus_mod Ht8; reflexivity)
                  ltac:(vm_compute; discriminate)
                  with "[] Hqp Hrun").
        { iApply (uis_shk_108 with "Hcode"). }
        iIntros "_".
        assert (E108 : add_vec_int (mword_of_int 0x108 : mword 64) 2
                       = mword_of_int 0x10a)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite E108. iIntros (h8) "Hrun".
        set (k6 := <[Regidx a0_idx
                     := regval_into_reg (mword_of_int q : mword 64)]> k5).
        iApply (wp_kshr_jal γt γd γs γfd h8 k6 0x10a ShSyms.runcmd 0x10e
                  (mword_of_int 2097028 : mword 21) av
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_shk_10a with "Hcode"). }
        iIntros (h9) "Hrun".
        set (k7 := <[Regidx ra_idx := (mword_of_int 0x10e : mword 64)]> k6).
        assert (Ha0_k7 : k7 !!! Regidx a0_idx = (mword_of_int q : mword 64)).
        { rewrite /k7 (upd_ne k6 (Regidx ra_idx) (Regidx a0_idx) _
                         ltac:(vm_compute; discriminate)).
          exact (upd_eq k5 (Regidx a0_idx) (mword_of_int q : mword 64)). }
        iApply (IH γt γd γs h9 k7 q szv n Ha0_k7
                  with "Hcode Hjt Hqc Hsz Hrun").

    - (* =================== PIPE =================== *)
      iDestruct (ush_cmd_pipe with "Htree") as "[#Hsl #Hsr]".
      iDestruct "Hsl" as (ql) "[#Hqlp #Hqlc]".
      iDestruct "Hsr" as (qr) "[#Hqrp #Hqrc]".
      pose proof (Nat.le_max_l (ush_ht l) (ush_ht r)) as HM1.
      pose proof (Nat.le_max_r (ush_ht l) (ush_ht r)) as HM2.
      replace (6 * ush_ht (UPipe l r) + (2 + (Dg + n)))%nat
        with (6 + (6 * Nat.max (ush_ht l) (ush_ht r) + (2 + (Dg + n))))%nat
        by (cbn [ush_ht]; lia).
      iApply (wp_kshr_entry γt γd γs γfd (UPipe l r) h m t
                (6 * Nat.max (ush_ht l) (ush_ht r) + (2 + (Dg + n))) Ha0
                with "Hcode Hjt Htree Hrun").
      iIntros (h1 m1 sp0) "%Hal8 %Hlo %Hsp1 %Hs0_1 %Hs1_1 %Ha0_1 Hp Hrun".
      iDestruct "Hp" as (wp0) "Hp".
      set (av := (6 * Nat.max (ush_ht l) (ush_ht r) + (2 + (Dg + n)))%nat).
      assert (Hsu : uint sp0 < Z64).
      { rewrite uint_unsigned.
        pose proof (bv_unsigned_in_range 64 sp0) as H0.
        assert (Em : bv_modulus 64 = 18446744073709551616)
          by (vm_compute; reflexivity).
        rewrite Em in H0. unfold Z64. exact (proj2 H0). }
      assert (Hspb : 0 <= uint sp0 - 40 < Z64) by lia.
      (* ---- 0x13c  addi a0,s0,-40 -- &p[0] ---- *)
      iApply (wp_uk_addi γt γd γs γfd h1 m1 (mword_of_int 0x13c)
                (mword_of_int 4056 : mword 12) s0_idx a0_idx
                (mword_of_int (uint sp0 - 40)) av
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs0_1;
                      apply (umoi_add_i12 sp0 (mword_of_int 4056 : mword 12));
                      vm_compute uoff_i12; lia)
                with "[] Hrun").
      { iApply (uis_shk_13c with "Hcode"). }
      assert (E13c : add_vec_int (mword_of_int 0x13c : mword 64) 4
                     = mword_of_int 0x140)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E13c. iIntros (h2) "Hrun".
      set (p1 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int (uint sp0 - 40)
                                       : mword 64)]> m1).
      assert (Hp1 : forall qq : mword 5, Regidx qq <> Regidx a0_idx ->
                      p1 !!! Regidx qq = m1 !!! Regidx qq)
        by (intros qq Hq; exact (upd_ne m1 (Regidx a0_idx) (Regidx qq) _ Hq)).
      (* ---- 0x140  jal ra,0xc96 <pipe> -- THE JOINED ROW ---- *)
      iApply (wp_kshr_jal γt γd γs γfd h2 p1 0x140 ShSyms.pipe 0x144
                (mword_of_int 2902 : mword 21) av
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_140 with "Hcode"). }
      iIntros (h3) "Hrun".
      set (p2 := <[Regidx ra_idx := (mword_of_int 0x144 : mword 64)]> p1).
      assert (Ha0_p2 : uint (p2 !!! Regidx a0_idx) = uint sp0 - 40).
      { rewrite /p2 (upd_ne p1 (Regidx ra_idx) (Regidx a0_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /p1 (upd_eq m1 (Regidx a0_idx)
                       (mword_of_int (uint sp0 - 40) : mword 64)).
        apply uint_moi. exact Hspb. }
      assert (Hra_p2 : ret_pc (p2 !!! Regidx ra_idx)
                       = (mword_of_int 0x144 : mword 64))
        by (rewrite /p2 (upd_eq p1 (Regidx ra_idx) _);
            apply bv_eq; vm_compute; reflexivity).
      iApply (wp_kshr_pipe γt γd γs γfd h3 p2 (uint sp0 - 40) (nth_byte wp0) av
                Ha0_p2 with "Hcode Hp Hrun").
      rewrite Hra_p2. iIntros (h4 rp gp) "Hphs Hp Hrun".
      set (p3 := <[Regidx a0_idx := rp]>
                   (<[Regidx a7_idx := (mword_of_int 4 : mword 64)]> p2)).
      assert (Hcs_p3 : forall qq : mword 5, ucallee_saved_idx qq = true ->
                p3 !!! Regidx qq = m1 !!! Regidx qq).
      { intros qq Hq.
        rewrite /p3 (upd_ne _ (Regidx a0_idx) (Regidx qq) rp
                       (ushr_cs_ne qq a0_idx Hq
                          ltac:(right; left; vm_compute; reflexivity))).
        rewrite (upd_ne p2 (Regidx a7_idx) (Regidx qq) _
                   (ushr_cs_ne qq a7_idx Hq
                      ltac:(right; right; right; right;
                            vm_compute; reflexivity))).
        rewrite /p2 (upd_ne p1 (Regidx ra_idx) (Regidx qq) _
                       (ushr_cs_ne qq ra_idx Hq
                          ltac:(left; vm_compute; reflexivity))).
        exact (Hp1 qq (ushr_cs_ne qq a0_idx Hq
                         ltac:(right; left; vm_compute; reflexivity))). }
      (* ---- 0x144  bltz a0,0x172 -- pipe failed? ---- *)
      iApply (wp_uk_btype0 γt γd γs γfd h4 p3 (mword_of_int 0x144)
                (mword_of_int 46 : mword 13) a0_idx BLT
                (uv_btaken BLT (p3 !!! Regidx a0_idx) zero_reg)
                (mword_of_int 0x172) av
                eq_refl
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_144 with "Hcode"). }
      assert (E144 : add_vec_int (mword_of_int 0x144 : mword 64) 4
                     = mword_of_int 0x148)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E144. iIntros (h5) "Hrun".
      destruct (uv_btaken BLT (p3 !!! Regidx a0_idx) zero_reg).
      + (* ---- pipe failed: panic("pipe") ---- *)
        iApply (wp_uk_auipc γt γd γs γfd h5 p3 (mword_of_int 0x172)
                  (mword_of_int 1 : mword 20) a0_idx
                  (mword_of_int 0x1172) av
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; discriminate)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_shk_172 with "Hcode"). }
        assert (E172 : add_vec_int (mword_of_int 0x172 : mword 64) 4
                       = mword_of_int 0x176)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite E172. iIntros (h6) "Hrun".
        set (p4 := <[Regidx a0_idx
                     := regval_into_reg (mword_of_int 0x1172
                                         : mword 64)]> p3).
        iApply (wp_uk_addi γt γd γs γfd h6 p4 (mword_of_int 0x176)
                  (mword_of_int 342 : mword 12) a0_idx a0_idx
                  (mword_of_int 0x12c8) av
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; discriminate)
                  ltac:(rewrite /p4 (upd_eq p3 (Regidx a0_idx)
                                       (mword_of_int 0x1172 : mword 64));
                        assert (Es : (sign_extend' 64
                                        (mword_of_int 342 : mword 12)
                                      : mword 64) = mword_of_int 342)
                          by (apply bv_eq; vm_compute; reflexivity);
                        rewrite Es moi_add; f_equal; lia)
                  with "[] Hrun").
        { iApply (uis_shk_176 with "Hcode"). }
        assert (E176 : add_vec_int (mword_of_int 0x176 : mword 64) 4
                       = mword_of_int 0x17a)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite E176. iIntros (h7) "Hrun".
        set (p5 := <[Regidx a0_idx
                     := regval_into_reg (mword_of_int 0x12c8
                                         : mword 64)]> p4).
        iApply (wp_kshr_jal γt γd γs γfd h7 p5 0x17a ShSyms.panic 0x17e
                  (mword_of_int 2096848 : mword 21) av
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_shk_17a with "Hcode"). }
        iIntros (h8) "Hrun".
        set (p6 := <[Regidx ra_idx := (mword_of_int 0x17e : mword 64)]> p5).
        assert (Hmsg : uint (p6 !!! Regidx a0_idx) = 0x1298 \/
                       uint (p6 !!! Regidx a0_idx) = 0x12a0 \/
                       uint (p6 !!! Regidx a0_idx) = 0x12c8).
        { right. right.
          rewrite /p6 (upd_ne p5 (Regidx ra_idx) (Regidx a0_idx) _
                         ltac:(vm_compute; discriminate)).
          rewrite /p5 (upd_eq p4 (Regidx a0_idx)
                         (mword_of_int 0x12c8 : mword 64)).
          apply uint_moi. unfold Z64. lia. }
        replace av
          with (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + (2 + n)))%nat
          by (unfold av; lia).
        iApply (ush_diag_leaf γt γd γs γfd h8 p6 ShSyms.panic
                  (6 * Nat.max (ush_ht l) (ush_ht r) + (2 + n))
                  ltac:(left; split; [ reflexivity | exact Hmsg ])
                  with "Hcode Hro [] Hrun").
        rewrite ush_diag_res_panic. done.
      + (* ---- pipe succeeded: two forks, four closes, two waits ---- *)
        iDestruct (ush_pipe_halves γd (uint sp0 - 40) gp with "Hp")
          as (w0 w1) "[Hp0 Hp1]".
        assert (Eh : (uint sp0 - 40 + 4) = uint sp0 - 36) by lia.
        rewrite Eh.
        assert (Hst_p3 : ush_st p3 sp0 t).
        { split;
            [ rewrite (Hcs_p3 s0_idx ltac:(vm_compute; reflexivity));
              exact Hs0_1
            | rewrite (Hcs_p3 s1_idx ltac:(vm_compute; reflexivity));
              exact Hs1_1 ]. }
        replace av
          with (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))%nat
          by (unfold av; lia).
        iApply (wp_kshr_jal γt γd γs γfd h5 p3 0x148 ShSyms.fork1 0x14c
                  (mword_of_int 2096928 : mword 21)
                  (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_shk_148 with "Hcode"). }
        iIntros (h6) "Hrun".
        set (f1 := <[Regidx ra_idx := (mword_of_int 0x14c : mword 64)]> p3).
        assert (Hra_f1 : ret_pc (f1 !!! Regidx ra_idx)
                         = (mword_of_int 0x14c : mword 64))
          by (rewrite /f1 (upd_eq p3 (Regidx ra_idx) _);
              apply bv_eq; vm_compute; reflexivity).
        iApply (wp_kshr_fork1 γt γd γs γfd
                  (fun gt gd _ => (ush_jtab gt ∗ ush_cmd gd t (UPipe l r)
                                   ∗ ubytes gd (uint sp0 - 40) 4 (nth_byte w0)
                                   ∗ ubytes gd (uint sp0 - 36) 4
                                       (nth_byte w1))%I)
                  (FP := forkable_ush_paypipe t (uint sp0 - 40)
                           (uint sp0 - 36) (UPipe l r) w0 w1)
                  szv h6 f1 (6 * Nat.max (ush_ht l) (ush_ht r) + n)
                  with "Hcode Hro [Hp0 Hp1] Hsz Hrun").
        { iFrame "Hjt Htree Hp0 Hp1". }
        assert (Hst_f1 : ush_st f1 sp0 t)
          by (apply ush_st_upd;
              [ exact Hst_p3 | vm_compute; lia | vm_compute; lia ]).
        assert (Halq : (uint sp0 - 40) mod 4 = 0).
        { pose proof (Z.mod_divide (uint sp0) 8 ltac:(lia)) as Hd.
          destruct (proj1 Hd Hal8) as [kq Hkq].
          apply Z.mod_divide; [ lia | ]. exists (2 * kq - 10). lia. }
        assert (Halq' : (uint sp0 - 36) mod 4 = 0).
        { pose proof (Z.mod_divide (uint sp0) 8 ltac:(lia)) as Hd.
          destruct (proj1 Hd Hal8) as [kq Hkq].
          apply Z.mod_divide; [ lia | ]. exists (2 * kq - 9). lia. }
        assert (Ho40 : uoff_i12 (mword_of_int 4056 : mword 12) = -40)
          by (vm_compute; reflexivity).
        assert (Ho36 : uoff_i12 (mword_of_int 4060 : mword 12) = -36)
          by (vm_compute; reflexivity).
        rewrite Hra_f1.
        iSplitL "".
        * (* ---- PARENT of the first fork: fork again, then reap ---- *)
          iIntros (hA mA rA) "%HrA %HcsA %Ha0A (Hjt2 & Ht2 & Hp0 & Hp1)
                   Hsz Hrun".
          iDestruct "Hjt2" as "#Hjt2". iDestruct "Ht2" as "#Ht2".
          pose proof (ush_st_cs f1 mA sp0 t Hst_f1 HcsA) as HstA.
          (* 0x14c  c.bnez a0,0x17e -- TAKEN: this is the parent *)
          iApply (wp_uk_cbnez γt γd γs γfd hA mA (mword_of_int 0x14c)
                    (mword_of_int 25 : mword 8) (mword_of_int 2 : mword 3)
                    a0_idx true (mword_of_int 0x17e)
                    (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))
                    ltac:(vm_compute; reflexivity)
                    ltac:(rewrite Ha0A; symmetry; exact (ush_neqv_true rA HrA))
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(intros _; vm_compute; reflexivity)
                    with "[] Hrun").
          { iApply (uis_shk_14c with "Hcode"). }
          iIntros (hB) "Hrun".
          (* 0x17e  jal ra,0x68 <fork1> -- the SECOND fork *)
          iApply (wp_kshr_jal γt γd γs γfd hB mA 0x17e ShSyms.fork1 0x182
                    (mword_of_int 2096874 : mword 21)
                    (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(vm_compute; reflexivity)
                    with "[] Hrun").
          { iApply (uis_shk_17e with "Hcode"). }
          iIntros (hC) "Hrun".
          set (f2 := <[Regidx ra_idx := (mword_of_int 0x182 : mword 64)]> mA).
          assert (Hra_f2 : ret_pc (f2 !!! Regidx ra_idx)
                           = (mword_of_int 0x182 : mword 64))
            by (rewrite /f2 (upd_eq mA (Regidx ra_idx) _);
                apply bv_eq; vm_compute; reflexivity).
          assert (Hst_f2 : ush_st f2 sp0 t)
            by (apply ush_st_upd;
                [ exact HstA | vm_compute; lia | vm_compute; lia ]).
          iApply (wp_kshr_fork1 γt γd γs γfd
                    (fun gt gd _ => (ush_jtab gt ∗ ush_cmd gd t (UPipe l r)
                                     ∗ ubytes gd (uint sp0 - 40) 4
                                         (nth_byte w0)
                                     ∗ ubytes gd (uint sp0 - 36) 4
                                         (nth_byte w1))%I)
                    (FP := forkable_ush_paypipe t (uint sp0 - 40)
                             (uint sp0 - 36) (UPipe l r) w0 w1)
                    szv hC f2 (6 * Nat.max (ush_ht l) (ush_ht r) + n)
                    with "Hcode Hro [Hp0 Hp1] Hsz Hrun").
          { iFrame "Hjt2 Ht2 Hp0 Hp1". }
          rewrite Hra_f2.
          iSplitL "".
          -- (* ---- the parent of BOTH forks: close, wait, wait, exit ---- *)
             iIntros (hD mD rD) "%HrD %HcsD %Ha0D (Hjt3 & Ht3 & Hp0 & Hp1)
                      Hsz Hrun".
             pose proof (ush_st_cs f2 mD sp0 t Hst_f2 HcsD) as HstD.
             (* 0x182  c.bnez a0,0x1a6 -- TAKEN *)
             iApply (wp_uk_cbnez γt γd γs γfd hD mD (mword_of_int 0x182)
                       (mword_of_int 18 : mword 8) (mword_of_int 2 : mword 3)
                       a0_idx true (mword_of_int 0x1a6)
                       (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))
                       ltac:(vm_compute; reflexivity)
                       ltac:(rewrite Ha0D; symmetry;
                             exact (ush_neqv_true rD HrD))
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(intros _; vm_compute; reflexivity)
                       with "[] Hrun").
             { iApply (uis_shk_182 with "Hcode"). }
             iIntros (hE) "Hrun".
             (* 0x1a6..0x1ae  close(p[0]) *)
             iApply (wp_kshr_fd_call γt γd γs γfd hE mD 0x1a6 0x1aa 0x1ae
                       ShSyms.close 21 (mword_of_int 4056 : mword 12)
                       (mword_of_int 2820 : mword 21) sp0 (uint sp0 - 40) w0
                       _ (wp_ksh_close γt γd γs γfd)
                       (proj1 HstD) ltac:(rewrite Ho40; lia) Halq
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       with "Hcode [] [] Hp0 Hrun").
             { iApply (uis_shk_1a6 with "Hcode"). }
             { iApply (uis_shk_1aa with "Hcode"). }
             iIntros "Hp0" (hF mF) "%HcsF Hrun".
             pose proof (ush_st_cs mD mF sp0 t HstD HcsF) as HstF.
             (* 0x1ae..0x1b6  close(p[1]) *)
             iApply (wp_kshr_fd_call γt γd γs γfd hF mF 0x1ae 0x1b2 0x1b6
                       ShSyms.close 21 (mword_of_int 4060 : mword 12)
                       (mword_of_int 2812 : mword 21) sp0 (uint sp0 - 36) w1
                       _ (wp_ksh_close γt γd γs γfd)
                       (proj1 HstF) ltac:(rewrite Ho36; lia) Halq'
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       with "Hcode [] [] Hp1 Hrun").
             { iApply (uis_shk_1ae with "Hcode"). }
             { iApply (uis_shk_1b2 with "Hcode"). }
             iIntros "Hp1" (hG mG) "%HcsG Hrun".
             (* 0x1b6..0x1bc  wait(0) *)
             iApply (wp_kshr_wait0 γt γd γs γfd hG mG 0x1b6 0x1b8 0x1bc
                       (mword_of_int 2774 : mword 21)
                       (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       with "Hcode [] [] Hrun").
             { iApply (uis_shk_1b6 with "Hcode"). }
             { iApply (uis_shk_1b8 with "Hcode"). }
             iIntros (hH mH) "_ Hrun".
             (* 0x1bc..0x1c2  wait(0) again *)
             iApply (wp_kshr_wait0 γt γd γs γfd hH mH 0x1bc 0x1be 0x1c2
                       (mword_of_int 2768 : mword 21)
                       (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       with "Hcode [] [] Hrun").
             { iApply (uis_shk_1bc with "Hcode"). }
             { iApply (uis_shk_1be with "Hcode"). }
             iIntros (hI mI) "_ Hrun".
             (* 0x1c2  c.j 0xea -- into the shared exit(0) *)
             iApply (wp_uk_cj γt γd γs γfd hI mI (mword_of_int 0x1c2)
                       (mword_of_int 1940 : mword 11) (mword_of_int 0xea)
                       (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity)
                       with "[] Hrun").
             { iApply (uis_shk_1c2 with "Hcode"). }
             iIntros (hJ) "Hrun".
             iApply (wp_kshr_exit0 γt γd γs γfd hJ mI 0xea 0xec 0xf0
                       (mword_of_int 0 : mword 6)
                       (mword_of_int 2970 : mword 21)
                       (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity)
                       with "Hcode [] [] Hrun").
             { iApply (uis_shk_ea with "Hcode"). }
             { iApply (uis_shk_ec with "Hcode"). }
          -- (* ---- the SECOND child: stdin <- p[0], then runcmd(right) ---- *)
             iIntros (gt gd gs hD mD) "%HcsD %Ha0D #Hck
                      (Hjt3 & Ht3 & Hp0 & Hp1) Hsz Hrun".
             iDestruct "Hjt3" as "#Hjt3". iDestruct "Ht3" as "#Ht3".
             iDestruct (ush_cmd_pipe with "Ht3") as "[_ #Hsr3]".
             iDestruct "Hsr3" as (qr3) "[#Hqrp3 #Hqrc3]".
             pose proof (ush_st_cs f2 mD sp0 t Hst_f2 HcsD) as HstD.
             (* 0x182  c.bnez a0,0x1a6 -- NOT taken *)
             iApply (wp_uk_cbnez gt gd gs gfd hD mD (mword_of_int 0x182)
                       (mword_of_int 18 : mword 8) (mword_of_int 2 : mword 3)
                       a0_idx false (mword_of_int 0x1a6)
                       (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))
                       ltac:(vm_compute; reflexivity)
                       ltac:(rewrite Ha0D; vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(discriminate)
                       with "[] Hrun").
             { iApply (uis_shk_182 with "Hck"). }
             assert (E182 : add_vec_int (mword_of_int 0x182 : mword 64) 2
                            = mword_of_int 0x184)
               by (apply bv_eq; vm_compute; reflexivity).
             rewrite E182. iIntros (hE) "Hrun".
             (* 0x184  jal ra,0xcae <close> -- close(0), a0 is fork1's 0 *)
             iApply (wp_kshr_qcall gt gd gs gfd hE mD 0x184 ShSyms.close 0x188 21
                       (mword_of_int 2858 : mword 21)
                       (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))
                       (wp_ksh_close gt gd gs)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       with "Hck [] Hrun").
             { iApply (uis_shk_184 with "Hck"). }
             iIntros (hF mF rF) "%HcsF _ Hrun".
             pose proof (ush_st_cs mD mF sp0 t HstD HcsF) as HstF.
             (* 0x188..0x190  dup(p[0]) *)
             iApply (wp_kshr_fd_call gt gd gs gfd hF mF 0x188 0x18c 0x190
                       ShSyms.dup 10 (mword_of_int 4056 : mword 12)
                       (mword_of_int 2930 : mword 21) sp0 (uint sp0 - 40) w0
                       _ (wp_kshr_dup gt gd gs)
                       (proj1 HstF) ltac:(rewrite Ho40; lia) Halq
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       with "Hck [] [] Hp0 Hrun").
             { iApply (uis_shk_188 with "Hck"). }
             { iApply (uis_shk_18c with "Hck"). }
             iIntros "Hp0" (hG mG) "%HcsG Hrun".
             pose proof (ush_st_cs mF mG sp0 t HstF HcsG) as HstG.
             (* 0x190..0x198  close(p[0]) *)
             iApply (wp_kshr_fd_call gt gd gs gfd hG mG 0x190 0x194 0x198
                       ShSyms.close 21 (mword_of_int 4056 : mword 12)
                       (mword_of_int 2842 : mword 21) sp0 (uint sp0 - 40) w0
                       _ (wp_ksh_close gt gd gs)
                       (proj1 HstG) ltac:(rewrite Ho40; lia) Halq
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       with "Hck [] [] Hp0 Hrun").
             { iApply (uis_shk_190 with "Hck"). }
             { iApply (uis_shk_194 with "Hck"). }
             iIntros "Hp0" (hH mH) "%HcsH Hrun".
             pose proof (ush_st_cs mG mH sp0 t HstG HcsH) as HstH.
             (* 0x198..0x1a0  close(p[1]) *)
             iApply (wp_kshr_fd_call gt gd gs gfd hH mH 0x198 0x19c 0x1a0
                       ShSyms.close 21 (mword_of_int 4060 : mword 12)
                       (mword_of_int 2834 : mword 21) sp0 (uint sp0 - 36) w1
                       _ (wp_ksh_close gt gd gs)
                       (proj1 HstH) ltac:(rewrite Ho36; lia) Halq'
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       with "Hck [] [] Hp1 Hrun").
             { iApply (uis_shk_198 with "Hck"). }
             { iApply (uis_shk_19c with "Hck"). }
             iIntros "Hp1" (hI mI) "%HcsI Hrun".
             pose proof (ush_st_cs mH mI sp0 t HstH HcsI) as HstI.
             destruct HstI as [Hs0I Hs1I].
             (* 0x1a0  c.ld a0,16(s1) -- pcmd->right *)
             iApply (wp_uk_cldq gt gd gs gfd hI mI (mword_of_int 0x1a0)
                       (mword_of_int 2 : mword 5) (mword_of_int 1 : mword 3)
                       (mword_of_int 2 : mword 3) s1_idx a0_idx DfracDiscarded
                       (t + 16) (mword_of_int qr3)
                       (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))
                       ltac:(unfold unot_sp; vm_compute; discriminate)
                       ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity)
                       ltac:(rewrite Hs1I (uint_moi t ltac:(unfold Z64; lia));
                             vm_compute uoff_c8; lia)
                       ltac:(rewrite Zplus_mod Ht8; reflexivity)
                       ltac:(vm_compute; discriminate)
                       with "[] Hqrp3 Hrun").
             { iApply (uis_shk_1a0 with "Hck"). }
             iIntros "_".
             assert (E1a0 : add_vec_int (mword_of_int 0x1a0 : mword 64) 2
                            = mword_of_int 0x1a2)
               by (apply bv_eq; vm_compute; reflexivity).
             rewrite E1a0. iIntros (hJ) "Hrun".
             set (d1 := <[Regidx a0_idx
                          := regval_into_reg (mword_of_int qr3
                                              : mword 64)]> mI).
             (* 0x1a2  jal ra,0x8e <runcmd> -- the RIGHT subtree *)
             iApply (wp_kshr_jal gt gd gs gfd hJ d1 0x1a2 ShSyms.runcmd 0x1a6
                       (mword_of_int 2096876 : mword 21)
                       (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity)
                       with "[] Hrun").
             { iApply (uis_shk_1a2 with "Hck"). }
             iIntros (hK) "Hrun".
             set (d2 := <[Regidx ra_idx
                          := (mword_of_int 0x1a6 : mword 64)]> d1).
             assert (Ha0_d2 : d2 !!! Regidx a0_idx
                              = (mword_of_int qr3 : mword 64)).
             { rewrite /d2 (upd_ne d1 (Regidx ra_idx) (Regidx a0_idx) _
                              ltac:(vm_compute; discriminate)).
               exact (upd_eq mI (Regidx a0_idx)
                        (mword_of_int qr3 : mword 64)). }
             replace (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))%nat
               with (6 * ush_ht r
                     + (2 + (Dg + (6 * (Nat.max (ush_ht l) (ush_ht r)
                                        - ush_ht r) + n))))%nat by lia.
             iApply (IHr gt gd gs gfd hK d2 qr3 szv
                       ((6 * (Nat.max (ush_ht l) (ush_ht r) - ush_ht r) + n)%nat)
                       Ha0_d2 with "Hck Hjt3 Hqrc3 Hsz Hrun").
        * (* ---- CHILD of the first fork: stdout <- p[1], runcmd(left) ---- *)
          iIntros (gt gd gs hA mA) "%HcsA %Ha0A #Hck
                   (Hjt2 & Ht2 & Hp0 & Hp1) Hsz Hrun".
          iDestruct "Hjt2" as "#Hjt2". iDestruct "Ht2" as "#Ht2".
          iDestruct (ush_cmd_pipe with "Ht2") as "[#Hsl2 _]".
          iDestruct "Hsl2" as (ql2) "[#Hqlp2 #Hqlc2]".
          pose proof (ush_st_cs f1 mA sp0 t Hst_f1 HcsA) as HstA.
          (* 0x14c  c.bnez a0,0x17e -- NOT taken *)
          iApply (wp_uk_cbnez gt gd gs gfd hA mA (mword_of_int 0x14c)
                    (mword_of_int 25 : mword 8) (mword_of_int 2 : mword 3)
                    a0_idx false (mword_of_int 0x17e)
                    (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))
                    ltac:(vm_compute; reflexivity)
                    ltac:(rewrite Ha0A; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(discriminate)
                    with "[] Hrun").
          { iApply (uis_shk_14c with "Hck"). }
          assert (E14c : add_vec_int (mword_of_int 0x14c : mword 64) 2
                         = mword_of_int 0x14e)
            by (apply bv_eq; vm_compute; reflexivity).
          rewrite E14c. iIntros (hB) "Hrun".
          (* 0x14e  c.li a0,1 *)
          iApply (wp_uk_cli gt gd gs gfd hB mA (mword_of_int 0x14e)
                    (mword_of_int 1 : mword 6) a0_idx
                    (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))
                    ltac:(unfold unot_sp; vm_compute; discriminate)
                    ltac:(vm_compute; discriminate) with "[] Hrun").
          { iApply (uis_shk_14e with "Hck"). }
          assert (E14e : add_vec_int (mword_of_int 0x14e : mword 64) 2
                         = mword_of_int 0x150)
            by (apply bv_eq; vm_compute; reflexivity).
          rewrite E14e. iIntros (hC) "Hrun".
          set (e1 := <[Regidx a0_idx
                       := regval_into_reg (sign_extend' 64
                            (mword_of_int 1 : mword 6) : mword 64)]> mA).
          assert (Hst_e1 : ush_st e1 sp0 t)
            by (apply ush_st_upd;
                [ exact HstA | vm_compute; lia | vm_compute; lia ]).
          (* 0x150  jal ra,0xcae <close> -- close(1) *)
          iApply (wp_kshr_qcall gt gd gs gfd hC e1 0x150 ShSyms.close 0x154 21
                    (mword_of_int 2910 : mword 21)
                    (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))
                    (wp_ksh_close gt gd gs)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    with "Hck [] Hrun").
          { iApply (uis_shk_150 with "Hck"). }
          iIntros (hD mD rD) "%HcsD _ Hrun".
          pose proof (ush_st_cs e1 mD sp0 t Hst_e1 HcsD) as HstD.
          (* 0x154..0x15c  dup(p[1]) *)
          iApply (wp_kshr_fd_call gt gd gs gfd hD mD 0x154 0x158 0x15c
                    ShSyms.dup 10 (mword_of_int 4060 : mword 12)
                    (mword_of_int 2982 : mword 21) sp0 (uint sp0 - 36) w1
                    _ (wp_kshr_dup gt gd gs)
                    (proj1 HstD) ltac:(rewrite Ho36; lia) Halq'
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    with "Hck [] [] Hp1 Hrun").
          { iApply (uis_shk_154 with "Hck"). }
          { iApply (uis_shk_158 with "Hck"). }
          iIntros "Hp1" (hE mE) "%HcsE Hrun".
          pose proof (ush_st_cs mD mE sp0 t HstD HcsE) as HstE.
          (* 0x15c..0x164  close(p[0]) *)
          iApply (wp_kshr_fd_call gt gd gs gfd hE mE 0x15c 0x160 0x164
                    ShSyms.close 21 (mword_of_int 4056 : mword 12)
                    (mword_of_int 2894 : mword 21) sp0 (uint sp0 - 40) w0
                    _ (wp_ksh_close gt gd gs)
                    (proj1 HstE) ltac:(rewrite Ho40; lia) Halq
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    with "Hck [] [] Hp0 Hrun").
          { iApply (uis_shk_15c with "Hck"). }
          { iApply (uis_shk_160 with "Hck"). }
          iIntros "Hp0" (hF mF) "%HcsF Hrun".
          pose proof (ush_st_cs mE mF sp0 t HstE HcsF) as HstF.
          (* 0x164..0x16c  close(p[1]) *)
          iApply (wp_kshr_fd_call gt gd gs gfd hF mF 0x164 0x168 0x16c
                    ShSyms.close 21 (mword_of_int 4060 : mword 12)
                    (mword_of_int 2886 : mword 21) sp0 (uint sp0 - 36) w1
                    _ (wp_ksh_close gt gd gs)
                    (proj1 HstF) ltac:(rewrite Ho36; lia) Halq'
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    with "Hck [] [] Hp1 Hrun").
          { iApply (uis_shk_164 with "Hck"). }
          { iApply (uis_shk_168 with "Hck"). }
          iIntros "Hp1" (hG mG) "%HcsG Hrun".
          pose proof (ush_st_cs mF mG sp0 t HstF HcsG) as HstG.
          destruct HstG as [Hs0G Hs1G].
          (* 0x16c  c.ld a0,8(s1) -- pcmd->left *)
          iApply (wp_uk_cldq gt gd gs gfd hG mG (mword_of_int 0x16c)
                    (mword_of_int 1 : mword 5) (mword_of_int 1 : mword 3)
                    (mword_of_int 2 : mword 3) s1_idx a0_idx DfracDiscarded
                    (t + 8) (mword_of_int ql2)
                    (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))
                    ltac:(unfold unot_sp; vm_compute; discriminate)
                    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                    ltac:(rewrite Hs1G (uint_moi t ltac:(unfold Z64; lia));
                          vm_compute uoff_c8; lia)
                    ltac:(rewrite Zplus_mod Ht8; reflexivity)
                    ltac:(vm_compute; discriminate)
                    with "[] Hqlp2 Hrun").
          { iApply (uis_shk_16c with "Hck"). }
          iIntros "_".
          assert (E16c : add_vec_int (mword_of_int 0x16c : mword 64) 2
                         = mword_of_int 0x16e)
            by (apply bv_eq; vm_compute; reflexivity).
          rewrite E16c. iIntros (hH) "Hrun".
          set (e2 := <[Regidx a0_idx
                       := regval_into_reg (mword_of_int ql2
                                           : mword 64)]> mG).
          (* 0x16e  jal ra,0x8e <runcmd> -- the LEFT subtree *)
          iApply (wp_kshr_jal gt gd gs gfd hH e2 0x16e ShSyms.runcmd 0x172
                    (mword_of_int 2096928 : mword 21)
                    (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(vm_compute; reflexivity)
                    with "[] Hrun").
          { iApply (uis_shk_16e with "Hck"). }
          iIntros (hI) "Hrun".
          set (e3 := <[Regidx ra_idx := (mword_of_int 0x172 : mword 64)]> e2).
          assert (Ha0_e3 : e3 !!! Regidx a0_idx
                           = (mword_of_int ql2 : mword 64)).
          { rewrite /e3 (upd_ne e2 (Regidx ra_idx) (Regidx a0_idx) _
                           ltac:(vm_compute; discriminate)).
            exact (upd_eq mG (Regidx a0_idx) (mword_of_int ql2 : mword 64)). }
          replace (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))%nat
            with (6 * ush_ht l
                  + (2 + (Dg + (6 * (Nat.max (ush_ht l) (ush_ht r)
                                     - ush_ht l) + n))))%nat by lia.
          iApply (IHl gt gd gs gfd hI e3 ql2 szv
                    ((6 * (Nat.max (ush_ht l) (ush_ht r) - ush_ht l) + n)%nat)
                    Ha0_e3 with "Hck Hjt2 Hqlc2 Hsz Hrun").

    - (* =================== LIST =================== *)
      iDestruct (ush_cmd_list with "Htree") as "[#Hsl #Hsr]".
      iDestruct "Hsl" as (ql) "[#Hqlp #Hqlc]".
      iDestruct "Hsr" as (qr) "[#Hqrp #Hqrc]".
      pose proof (Nat.le_max_l (ush_ht l) (ush_ht r)) as HM1.
      pose proof (Nat.le_max_r (ush_ht l) (ush_ht r)) as HM2.
      replace (6 * ush_ht (UList l r) + (2 + (Dg + n)))%nat
        with (6 + (6 * Nat.max (ush_ht l) (ush_ht r) + (2 + (Dg + n))))%nat
        by (cbn [ush_ht]; lia).
      iApply (wp_kshr_entry γt γd γs γfd (UList l r) h m t
                (6 * Nat.max (ush_ht l) (ush_ht r) + (2 + (Dg + n))) Ha0
                with "Hcode Hjt Htree Hrun").
      iIntros (h1 m1 sp0) "%Hal8 %Hlo %Hsp1 %Hs0_1 %Hs1_1 %Ha0_1 _ Hrun".
      assert (Hst_m1 : ush_st m1 sp0 t) by (split; assumption).
      replace (6 * Nat.max (ush_ht l) (ush_ht r) + (2 + (Dg + n)))%nat
        with (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))%nat by lia.
      (* ---- 0x124  jal ra,0x68 <fork1> ---- *)
      iApply (wp_kshr_jal γt γd γs γfd h1 m1 0x124 ShSyms.fork1 0x128
                (mword_of_int 2096964 : mword 21)
                (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_124 with "Hcode"). }
      iIntros (h2) "Hrun".
      set (g1 := <[Regidx ra_idx := (mword_of_int 0x128 : mword 64)]> m1).
      assert (Hra_g1 : ret_pc (g1 !!! Regidx ra_idx)
                       = (mword_of_int 0x128 : mword 64))
        by (rewrite /g1 (upd_eq m1 (Regidx ra_idx) _);
            apply bv_eq; vm_compute; reflexivity).
      assert (Hst_g1 : ush_st g1 sp0 t)
        by (apply ush_st_upd;
            [ exact Hst_m1 | vm_compute; lia | vm_compute; lia ]).
      iApply (wp_kshr_fork1 γt γd γs γfd
                (fun gt gd _ => (ush_jtab gt ∗ ush_cmd gd t (UList l r))%I)
                (FP := forkable_ush_pay t (UList l r))
                szv h2 g1 (6 * Nat.max (ush_ht l) (ush_ht r) + n)
                with "Hcode Hro [] Hsz Hrun").
      { iFrame "Hjt Htree". }
      rewrite Hra_g1.
      iSplitL "".
      + (* ---- the PARENT: wait(0), then runcmd(lcmd->right) ---- *)
        iIntros (hA mA rA) "%HrA %HcsA %Ha0A (#Hjt2 & #Ht2) Hsz Hrun".
        pose proof (ush_st_cs g1 mA sp0 t Hst_g1 HcsA) as HstA.
        iApply (wp_uk_cbnez γt γd γs γfd hA mA (mword_of_int 0x128)
                  (mword_of_int 4 : mword 8) (mword_of_int 2 : mword 3)
                  a0_idx true (mword_of_int 0x130)
                  (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))
                  ltac:(vm_compute; reflexivity)
                  ltac:(rewrite Ha0A; symmetry; exact (ush_neqv_true rA HrA))
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(intros _; vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_shk_128 with "Hcode"). }
        iIntros (hB) "Hrun".
        (* 0x130..0x136  wait(0) *)
        iApply (wp_kshr_wait0 γt γd γs γfd hB mA 0x130 0x132 0x136
                  (mword_of_int 2908 : mword 21)
                  (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcode [] [] Hrun").
        { iApply (uis_shk_130 with "Hcode"). }
        { iApply (uis_shk_132 with "Hcode"). }
        iIntros (hC mC) "%HcsC Hrun".
        pose proof (ush_st_cs mA mC sp0 t HstA HcsC) as HstC.
        destruct HstC as [Hs0C Hs1C].
        (* 0x136  c.ld a0,16(s1) *)
        iApply (wp_uk_cldq γt γd γs γfd hC mC (mword_of_int 0x136)
                  (mword_of_int 2 : mword 5) (mword_of_int 1 : mword 3)
                  (mword_of_int 2 : mword 3) s1_idx a0_idx DfracDiscarded
                  (t + 16) (mword_of_int qr)
                  (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(rewrite Hs1C (uint_moi t ltac:(unfold Z64; lia));
                        vm_compute uoff_c8; lia)
                  ltac:(rewrite Zplus_mod Ht8; reflexivity)
                  ltac:(vm_compute; discriminate)
                  with "[] Hqrp Hrun").
        { iApply (uis_shk_136 with "Hcode"). }
        iIntros "_".
        assert (E136 : add_vec_int (mword_of_int 0x136 : mword 64) 2
                       = mword_of_int 0x138)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite E136. iIntros (hD) "Hrun".
        set (g2 := <[Regidx a0_idx
                     := regval_into_reg (mword_of_int qr : mword 64)]> mC).
        iApply (wp_kshr_jal γt γd γs γfd hD g2 0x138 ShSyms.runcmd 0x13c
                  (mword_of_int 2096982 : mword 21)
                  (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_shk_138 with "Hcode"). }
        iIntros (hE) "Hrun".
        set (g3 := <[Regidx ra_idx := (mword_of_int 0x13c : mword 64)]> g2).
        assert (Ha0_g3 : g3 !!! Regidx a0_idx = (mword_of_int qr : mword 64)).
        { rewrite /g3 (upd_ne g2 (Regidx ra_idx) (Regidx a0_idx) _
                         ltac:(vm_compute; discriminate)).
          exact (upd_eq mC (Regidx a0_idx) (mword_of_int qr : mword 64)). }
        replace (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))%nat
          with (6 * ush_ht r
                + (2 + (Dg + (6 * (Nat.max (ush_ht l) (ush_ht r)
                                   - ush_ht r) + n))))%nat by lia.
        iApply (IHr γt γd γs hE g3 qr szv
                  ((6 * (Nat.max (ush_ht l) (ush_ht r) - ush_ht r) + n)%nat)
                  Ha0_g3 with "Hcode Hjt2 Hqrc Hsz Hrun").
      + (* ---- the CHILD: runcmd(lcmd->left) ---- *)
        iIntros (gt gd gs hA mA) "%HcsA %Ha0A #Hck (#Hjt2 & #Ht2) Hsz Hrun".
        iDestruct (ush_cmd_list with "Ht2") as "[#Hsl2 _]".
        iDestruct "Hsl2" as (ql2) "[#Hqlp2 #Hqlc2]".
        pose proof (ush_st_cs g1 mA sp0 t Hst_g1 HcsA) as HstA.
        destruct HstA as [Hs0A Hs1A].
        iApply (wp_uk_cbnez gt gd gs gfd hA mA (mword_of_int 0x128)
                  (mword_of_int 4 : mword 8) (mword_of_int 2 : mword 3)
                  a0_idx false (mword_of_int 0x130)
                  (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))
                  ltac:(vm_compute; reflexivity)
                  ltac:(rewrite Ha0A; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(discriminate)
                  with "[] Hrun").
        { iApply (uis_shk_128 with "Hck"). }
        assert (E128 : add_vec_int (mword_of_int 0x128 : mword 64) 2
                       = mword_of_int 0x12a)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite E128. iIntros (hB) "Hrun".
        (* 0x12a  c.ld a0,8(s1) *)
        iApply (wp_uk_cldq gt gd gs gfd hB mA (mword_of_int 0x12a)
                  (mword_of_int 1 : mword 5) (mword_of_int 1 : mword 3)
                  (mword_of_int 2 : mword 3) s1_idx a0_idx DfracDiscarded
                  (t + 8) (mword_of_int ql2)
                  (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(rewrite Hs1A (uint_moi t ltac:(unfold Z64; lia));
                        vm_compute uoff_c8; lia)
                  ltac:(rewrite Zplus_mod Ht8; reflexivity)
                  ltac:(vm_compute; discriminate)
                  with "[] Hqlp2 Hrun").
        { iApply (uis_shk_12a with "Hck"). }
        iIntros "_".
        assert (E12a : add_vec_int (mword_of_int 0x12a : mword 64) 2
                       = mword_of_int 0x12c)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite E12a. iIntros (hC) "Hrun".
        set (g2 := <[Regidx a0_idx
                     := regval_into_reg (mword_of_int ql2 : mword 64)]> mA).
        iApply (wp_kshr_jal gt gd gs gfd hC g2 0x12c ShSyms.runcmd 0x130
                  (mword_of_int 2096994 : mword 21)
                  (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_shk_12c with "Hck"). }
        iIntros (hD) "Hrun".
        set (g3 := <[Regidx ra_idx := (mword_of_int 0x130 : mword 64)]> g2).
        assert (Ha0_g3 : g3 !!! Regidx a0_idx = (mword_of_int ql2 : mword 64)).
        { rewrite /g3 (upd_ne g2 (Regidx ra_idx) (Regidx a0_idx) _
                         ltac:(vm_compute; discriminate)).
          exact (upd_eq mA (Regidx a0_idx) (mword_of_int ql2 : mword 64)). }
        replace (2 + (Dg + (6 * Nat.max (ush_ht l) (ush_ht r) + n)))%nat
          with (6 * ush_ht l
                + (2 + (Dg + (6 * (Nat.max (ush_ht l) (ush_ht r)
                                   - ush_ht l) + n))))%nat by lia.
        iApply (IHl gt gd gs gfd hD g3 ql2 szv
                  ((6 * (Nat.max (ush_ht l) (ush_ht r) - ush_ht l) + n)%nat)
                  Ha0_g3 with "Hck Hjt2 Hqlc2 Hsz Hrun").

    - (* =================== BACK =================== *)
      iDestruct (ush_cmd_back with "Htree") as (q) "[#Hqp #Hqc]".
      replace (6 * ush_ht (UBack c1) + (2 + (Dg + n)))%nat
        with (6 + (6 * ush_ht c1 + (2 + (Dg + n))))%nat by (cbn [ush_ht]; lia).
      iApply (wp_kshr_entry γt γd γs γfd (UBack c1) h m t
                (6 * ush_ht c1 + (2 + (Dg + n))) Ha0
                with "Hcode Hjt Htree Hrun").
      iIntros (h1 m1 sp0) "%Hal8 %Hlo %Hsp1 %Hs0_1 %Hs1_1 %Ha0_1 _ Hrun".
      assert (Hst_m1 : ush_st m1 sp0 t) by (split; assumption).
      replace (6 * ush_ht c1 + (2 + (Dg + n)))%nat
        with (2 + (Dg + (6 * ush_ht c1 + n)))%nat by lia.
      (* ---- 0x1c4  jal ra,0x68 <fork1> ---- *)
      iApply (wp_kshr_jal γt γd γs γfd h1 m1 0x1c4 ShSyms.fork1 0x1c8
                (mword_of_int 2096804 : mword 21)
                (2 + (Dg + (6 * ush_ht c1 + n)))
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_1c4 with "Hcode"). }
      iIntros (h2) "Hrun".
      set (b1 := <[Regidx ra_idx := (mword_of_int 0x1c8 : mword 64)]> m1).
      assert (Hra_b1 : ret_pc (b1 !!! Regidx ra_idx)
                       = (mword_of_int 0x1c8 : mword 64))
        by (rewrite /b1 (upd_eq m1 (Regidx ra_idx) _);
            apply bv_eq; vm_compute; reflexivity).
      assert (Hst_b1 : ush_st b1 sp0 t)
        by (apply ush_st_upd;
            [ exact Hst_m1 | vm_compute; lia | vm_compute; lia ]).
      iApply (wp_kshr_fork1 γt γd γs γfd
                (fun gt gd _ => (ush_jtab gt ∗ ush_cmd gd t (UBack c1))%I)
                (FP := forkable_ush_pay t (UBack c1))
                szv h2 b1 (6 * ush_ht c1 + n)
                with "Hcode Hro [] Hsz Hrun").
      { iFrame "Hjt Htree". }
      rewrite Hra_b1.
      iSplitL "".
      + (* ---- the PARENT: exit(0) immediately ---- *)
        iIntros (hA mA rA) "%HrA %HcsA %Ha0A (#Hjt2 & #Ht2) Hsz Hrun".
        iApply (wp_uk_btype0 γt γd γs γfd hA mA (mword_of_int 0x1c8)
                  (mword_of_int 7970 : mword 13) a0_idx BNE
                  true (mword_of_int 0xea)
                  (2 + (Dg + (6 * ush_ht c1 + n)))
                  ltac:(cbn [uv_btaken]; rewrite Ha0A; symmetry;
                        exact (ush_neqv_true rA HrA))
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(intros _; vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_shk_1c8 with "Hcode"). }
        iIntros (hB) "Hrun".
        iApply (wp_kshr_exit0 γt γd γs γfd hB mA 0xea 0xec 0xf0
                  (mword_of_int 0 : mword 6) (mword_of_int 2970 : mword 21)
                  (2 + (Dg + (6 * ush_ht c1 + n)))
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcode [] [] Hrun").
        { iApply (uis_shk_ea with "Hcode"). }
        { iApply (uis_shk_ec with "Hcode"). }
      + (* ---- the CHILD: runcmd(bcmd->cmd), in the background ---- *)
        iIntros (gt gd gs hA mA) "%HcsA %Ha0A #Hck (#Hjt2 & #Ht2) Hsz Hrun".
        iDestruct (ush_cmd_back with "Ht2") as (q2) "[#Hqp2 #Hqc2]".
        pose proof (ush_st_cs b1 mA sp0 t Hst_b1 HcsA) as HstA.
        destruct HstA as [Hs0A Hs1A].
        iApply (wp_uk_btype0 gt gd gs gfd hA mA (mword_of_int 0x1c8)
                  (mword_of_int 7970 : mword 13) a0_idx BNE
                  false (mword_of_int 0xea)
                  (2 + (Dg + (6 * ush_ht c1 + n)))
                  ltac:(cbn [uv_btaken]; rewrite Ha0A;
                        vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(discriminate)
                  with "[] Hrun").
        { iApply (uis_shk_1c8 with "Hck"). }
        assert (E1c8 : add_vec_int (mword_of_int 0x1c8 : mword 64) 4
                       = mword_of_int 0x1cc)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite E1c8. iIntros (hB) "Hrun".
        (* 0x1cc  c.ld a0,8(s1) *)
        iApply (wp_uk_cldq gt gd gs gfd hB mA (mword_of_int 0x1cc)
                  (mword_of_int 1 : mword 5) (mword_of_int 1 : mword 3)
                  (mword_of_int 2 : mword 3) s1_idx a0_idx DfracDiscarded
                  (t + 8) (mword_of_int q2)
                  (2 + (Dg + (6 * ush_ht c1 + n)))
                  ltac:(unfold unot_sp; vm_compute; discriminate)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(rewrite Hs1A (uint_moi t ltac:(unfold Z64; lia));
                        vm_compute uoff_c8; lia)
                  ltac:(rewrite Zplus_mod Ht8; reflexivity)
                  ltac:(vm_compute; discriminate)
                  with "[] Hqp2 Hrun").
        { iApply (uis_shk_1cc with "Hck"). }
        iIntros "_".
        assert (E1cc : add_vec_int (mword_of_int 0x1cc : mword 64) 2
                       = mword_of_int 0x1ce)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite E1cc. iIntros (hC) "Hrun".
        set (b2 := <[Regidx a0_idx
                     := regval_into_reg (mword_of_int q2 : mword 64)]> mA).
        iApply (wp_kshr_jal gt gd gs gfd hC b2 0x1ce ShSyms.runcmd 0x1d2
                  (mword_of_int 2096832 : mword 21)
                  (2 + (Dg + (6 * ush_ht c1 + n)))
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_shk_1ce with "Hck"). }
        iIntros (hD) "Hrun".
        set (b3 := <[Regidx ra_idx := (mword_of_int 0x1d2 : mword 64)]> b2).
        assert (Ha0_b3 : b3 !!! Regidx a0_idx = (mword_of_int q2 : mword 64)).
        { rewrite /b3 (upd_ne b2 (Regidx ra_idx) (Regidx a0_idx) _
                         ltac:(vm_compute; discriminate)).
          exact (upd_eq mA (Regidx a0_idx) (mword_of_int q2 : mword 64)). }
        replace (2 + (Dg + (6 * ush_ht c1 + n)))%nat
          with (6 * ush_ht c1 + (2 + (Dg + n)))%nat by lia.
        iApply (IH gt gd gs gfd hD b3 q2 szv n Ha0_b3
                  with "Hck Hjt2 Hqc2 Hsz Hrun").
  Qed.

End UkShRun.
