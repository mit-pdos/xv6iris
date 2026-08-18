(* USpecInit.v -- the VERIFIED-EXECUTION contracts of the `init' program's
   thirteen reachable functions (claude-notes/projects/user-init.md).

   THE TOP STATEMENT is [wp_init_start_body]: from init's entry state, the
   machine runs safely FOREVER, and every [exec] init performs names "sh"
   with argv ["sh"] while every [write] it performs is one byte of one of
   its own four messages, on fd 1.

   Three things make init different from sync, echo and sh:

   - IT DOES NOT TERMINATE.  main's restart loop and its wait loop both run
     forever, so main and start have no continuation and no postcondition,
     and the two loops are [iLoeb] loops closed through
     [WpUmodeBranch.wp_uv_btype_later] -- the first unbounded loops in this
     tier (every loop in echo and sh is bounded; design/kernel-proofs.md
     has the rule).

   - IT ASSUMES NOTHING ABOUT WHAT THE KERNEL RETURNS.  [xv6_init_protocol]
     (UmodeInitIo.v) returns an arbitrary value from every arm, because
     init handles every failure itself: [mknod] when the console is
     missing, and a diagnostic printf + exit(1) when fork, exec or wait
     fails.  sh needs three assumptions precisely because its theorem does
     not cover those arms.

   - IT PRINTS.  The whole printf cone (printf -> vprintf -> putc ->
     write) is verified here, for a format string containing no '%' --
     which is what all four of init's literals are.  [init_lit] is that
     class of string, and it is the reusable thing: any xv6 user program
     printing a literal gets [wp_init_vprintf_body]'s shape.

   The observers [Q] (exec) and [W] (write) are supplied PERSISTENTLY, not
   linearly as sh's [Q] is: the exec is reached once per turn of a loop
   that never ends.  UmodeInitIo.v's header explains why the content
   survives that. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import InstrBytes RegFile.
Require Import UserPtTree UserExec.
Require Import UmodeMem UmodeCap UmodeAbi UmodeArith UmodeSyscall UmodeIo
               UmodeInitIo UCodeInit.
Require User.InitSyms User.InitInstrs User.InitData.
Local Open Scope Z_scope.
Import Defs.
Import ListNotations.

(* ===================================================================== *)
(* §0 The program's address space.                                        *)
(*                                                                        *)
(* init is small: text and rodata share PAGE 0 (the dump's executable      *)
(* segment is 0x0 .. 0xe6c) and .data + .bss share page 1 (0x1000 ..       *)
(* 0x1030).  There is no heap -- init never calls malloc -- so unlike      *)
(* sh's layout there is no [sbrk] region to pin.                           *)
(* ===================================================================== *)

Definition INIT_DATA_PG : Z := 0x1000.

Record init_layout (pt : uptd) : Prop := InitLayout {
  (* page 0, fetch- and load-permitting: rodata shares it, and every
     string init hands to [write]/[open]/[exec] lives there *)
  ilay_text : init_text_layout pt;
  (* page 1, the read-WRITE data/bss page.  init only READS it (the
     [argv] array), but the segment exec() maps is RW and the layout
     record describes what exec() built, not the minimum this proof
     consumes. *)
  ilay_data : exists w : mword 64,
      ud_um pt !! svpn_of (mword_of_int INIT_DATA_PG : mword 64) = Some w /\
      uleaf_ok (Load Data) w /\ uleaf_ok (Store Data) w
}.

(* THE premise [uv_stack] does not give.  [uv_stack] only guarantees a
   budget sits at or above 4096, but init's DATA page runs to 0x1030, so a
   frame carved between 4096 and 8192 could clobber [argv] -- and then no
   [uexec_args] fact would survive to the [exec].  sh needs the same thing
   for the same reason ([sh_frame_ok]); the bound here is the next page
   above the image's last key ([UCodeInit.init_data_key_lt]). *)
Definition init_frame_ok (sp0 : mword 64) (n : Z) : Prop :=
  8192 <= uint sp0 - n.

(* ===================================================================== *)
(* §0b The literals, and what the theorem observes.                       *)
(* ===================================================================== *)

Definition init_bs (l : list Z) : list (bv 8) := (fun z => Z_to_bv 8 z) <$> l.

(* the '%' vprintf's format loop tests for *)
Definition ubyte_pct : bv 8 := Z_to_bv 8 37.

Definition INIT_CONSOLE  : Z := 0x970.   (* "console"                      *)
Definition INIT_MSG_SH   : Z := 0x978.   (* "init: starting sh\n"          *)
Definition INIT_MSG_FORK : Z := 0x990.   (* "init: fork failed\n"          *)
Definition INIT_SH       : Z := 0x9a8.   (* "sh"                           *)
Definition INIT_MSG_EXEC : Z := 0x9b0.   (* "init: exec sh failed\n"       *)
Definition INIT_MSG_WAIT : Z := 0x9c8.   (* "init: wait returned an error\n" *)
Definition INIT_ARGV     : Z := 0x1000.  (* char *argv[] = {"sh", 0}       *)

Definition init_console  : list (bv 8) := init_bs [99;111;110;115;111;108;101].
Definition init_sh_path  : list (bv 8) := init_bs [115;104].
Definition init_sh_argv  : list (list (bv 8)) := [ init_sh_path ].

Definition init_msg_sh : list (bv 8) :=
  init_bs [105;110;105;116;58;32;115;116;97;114;116;105;110;103;32;115;104;10].
Definition init_msg_fork : list (bv 8) :=
  init_bs [105;110;105;116;58;32;102;111;114;107;32;102;97;105;108;101;100;10].
Definition init_msg_exec : list (bv 8) :=
  init_bs [105;110;105;116;58;32;101;120;101;99;32;115;104;32;102;97;105;108;101;100;10].
Definition init_msg_wait : list (bv 8) :=
  init_bs [105;110;105;116;58;32;119;97;105;116;32;114;101;116;117;114;110;101;100;
           32;97;110;32;101;114;114;111;114;10].

(* every byte init can ever hand to [write] *)
Definition init_msg_bytes : list (bv 8) :=
  init_msg_sh ++ init_msg_fork ++ init_msg_exec ++ init_msg_wait.

(* A PRINTABLE LITERAL: a NUL-terminated string of non-NUL, non-'%' bytes
   living inside page 0.  This is exactly the class of format string
   [vprintf]'s state == 0 path handles, and all four of init's are one. *)
Record init_lit (M : gmap Z (bv 8)) (s : Z) (bs : list (bv 8)) : Prop := InitLit {
  (* NON-EMPTY: vprintf's [beqz s1,70a] at 0x4e4 leaves through a
     DIFFERENT epilogue for the empty string (it has not spilled s2..s8
     yet), and init has no empty literal. *)
  il_ne   : bs <> [];
  il_at   : ustr_at M s bs;
  il_nz   : forall (j : nat) (b : bv 8), bs !! j = Some b -> b <> ubyte0;
  il_nopc : forall (j : nat) (b : bv 8), bs !! j = Some b -> b <> ubyte_pct;
  il_lo   : 0 <= s;
  il_hi   : s + Z.of_nat (length bs) + 1 <= 4096
}.

(* THE two observations, as the top statement instantiates them. *)
Definition init_execs_sh `{!riscvGS Σ}
    (path : list (bv 8)) (args : list (list (bv 8))) : iProp Σ :=
  (⌜path = init_sh_path /\ args = init_sh_argv⌝)%I.

Definition init_writes_msg `{!riscvGS Σ} (fd : Z) (bs : list (bv 8)) : iProp Σ :=
  (⌜fd = 1 /\ exists b : bv 8, bs = [b] /\ b ∈ init_msg_bytes⌝)%I.

(* ===================================================================== *)
(* §0c Reading the literals off the dumped image.                         *)
(*                                                                        *)
(* A byte-window check that [vm_compute] settles, so each literal costs    *)
(* one line rather than a case split per byte.                            *)
(* ===================================================================== *)

Fixpoint ubuf_check (mp : gmap Z (bv 8)) (a : Z) (bs : list (bv 8)) : bool :=
  match bs with
  | [] => true
  | b :: bs' =>
      match mp !! a with
      | Some b' => bool_decide (b' = b) && ubuf_check mp (a + 1) bs'
      | None => false
      end
  end.

Lemma ubuf_check_sound (mp : gmap Z (bv 8)) (a : Z) (bs : list (bv 8)) :
  ubuf_check mp a bs = true -> ubuf_at mp a bs.
Proof.
  revert a. induction bs as [ | b bs' IH ]; intros a Hchk.
  - intros j c Hj. destruct j; cbn in Hj; discriminate.
  - cbn in Hchk. destruct (mp !! a) as [ b' | ] eqn:Ha; [ | discriminate ].
    apply andb_prop in Hchk as [ Heq Hrest ].
    apply bool_decide_eq_true in Heq. subst b'.
    intros j c Hj. destruct j as [ | j' ]; cbn in Hj.
    + injection Hj as ->. rewrite Z.add_0_r. exact Ha.
    + pose proof (IH (a + 1) Hrest j' c Hj) as Hc.
      replace (a + Z.of_nat (S j')) with (a + 1 + Z.of_nat j') by lia.
      exact Hc.
Qed.

(* no byte of a checked window is [c] -- the shape [init_lit]'s two
   pointwise conditions want, again as one [vm_compute] *)
Definition ubuf_avoid (bs : list (bv 8)) (c : bv 8) : bool :=
  forallb (fun b => negb (bool_decide (b = c))) bs.

Lemma ubuf_avoid_sound (bs : list (bv 8)) (c : bv 8) :
  ubuf_avoid bs c = true ->
  forall (j : nat) (b : bv 8), bs !! j = Some b -> b <> c.
Proof.
  unfold ubuf_avoid. induction bs as [ | x xs IH ]; cbn; intros HF j b Hj.
  - destruct j; cbn in Hj; discriminate.
  - apply andb_prop in HF as [ H1 H2 ].
    destruct j as [ | j' ]; cbn in Hj.
    + injection Hj as Hxb. rewrite <- Hxb.
      apply negb_true_iff in H1. apply bool_decide_eq_false in H1. exact H1.
    + exact (IH H2 j' b Hj).
Qed.

(* the four literals, and "console" and "sh", as facts about ANY image
   containing init's data *)
Lemma init_lit_from_data (M : gmap Z (bv 8)) (s : Z) (bs : list (bv 8)) :
  init_data_sub M ->
  ubuf_check InitData.init_data s bs = true ->
  InitData.init_data !! (s + Z.of_nat (length bs)) = Some ubyte0 ->
  ubuf_avoid bs ubyte0 = true ->
  ubuf_avoid bs ubyte_pct = true ->
  Nat.ltb 0 (length bs) = true ->
  Z.leb 0 s = true ->
  Z.leb (s + Z.of_nat (length bs) + 1) 4096 = true ->
  init_lit M s bs.
Proof.
  intros Hsub Hchk Hnul Hnz Hpc Hne0 Hlo0 Hhi0.
  apply Z.leb_le in Hlo0. apply Z.leb_le in Hhi0.
  apply Nat.ltb_lt in Hne0.
  constructor; try assumption.
  - intro Hnil. rewrite Hnil in Hne0. cbn in Hne0. lia.
  - split.
    + intros j b Hj. exact (Hsub _ _ (ubuf_check_sound _ _ _ Hchk j b Hj)).
    + exact (Hsub _ _ Hnul).
  - exact (ubuf_avoid_sound bs ubyte0 Hnz).
  - exact (ubuf_avoid_sound bs ubyte_pct Hpc).
Qed.

Lemma init_lit_sh (M : gmap Z (bv 8)) :
  init_data_sub M -> init_lit M INIT_MSG_SH init_msg_sh.
Proof.
  intro H. apply (init_lit_from_data M);
    [ exact H | (vm_compute; reflexivity) .. ].
Qed.

Lemma init_lit_fork (M : gmap Z (bv 8)) :
  init_data_sub M -> init_lit M INIT_MSG_FORK init_msg_fork.
Proof.
  intro H. apply (init_lit_from_data M);
    [ exact H | (vm_compute; reflexivity) .. ].
Qed.

Lemma init_lit_exec (M : gmap Z (bv 8)) :
  init_data_sub M -> init_lit M INIT_MSG_EXEC init_msg_exec.
Proof.
  intro H. apply (init_lit_from_data M);
    [ exact H | (vm_compute; reflexivity) .. ].
Qed.

Lemma init_lit_wait (M : gmap Z (bv 8)) :
  init_data_sub M -> init_lit M INIT_MSG_WAIT init_msg_wait.
Proof.
  intro H. apply (init_lit_from_data M);
    [ exact H | (vm_compute; reflexivity) .. ].
Qed.

(* the readable window a literal is, which is what [write] / [open] /
   [exec] arms ask for.  The leaf comes from the TEXT layout: rodata
   shares page 0. *)
Lemma init_lit_rd (pt : uptd) (M : gmap Z (bv 8)) (s : Z) (bs : list (bv 8)) :
  init_text_layout pt -> init_lit M s bs ->
  uv_rd pt M s (Z.of_nat (length bs) + 1).
Proof.
  intros Hlay [_ [Hb Hn] _ _ Hlo Hhi]. constructor.
  - exact Hlo.
  - lia.
  - change (2 ^ 38) with 274877906944. lia.
  - intros j Hj. exact (init_text_layout_load pt (s + j) Hlay ltac:(lia)).
  - intros j Hj.
    destruct (decide (j = Z.of_nat (length bs))) as [ -> | Hne ].
    + exists ubyte0. exact Hn.
    + assert (Hj' : (Z.to_nat j < length bs)%nat) by lia.
      destruct (lookup_lt_is_Some_2 bs (Z.to_nat j) Hj') as [ b Hbj ].
      exists b. rewrite <- (Z2Nat.id j ltac:(lia)). exact (Hb _ _ Hbj).
Qed.

Lemma init_lit_cstr (M : gmap Z (bv 8)) (s : Z) (bs : list (bv 8)) :
  init_lit M s bs -> ucstr M s (Z.of_nat (length bs)).
Proof.
  intros [_ [Hb Hn] Hnz _ _ _]. constructor.
  - lia.
  - intros j Hj.
    assert (Hj' : (Z.to_nat j < length bs)%nat) by lia.
    destruct (lookup_lt_is_Some_2 bs (Z.to_nat j) Hj') as [ b Hbj ].
    exists b. split.
    + rewrite <- (Z2Nat.id j ltac:(lia)). exact (Hb _ _ Hbj).
    + exact (Hnz _ _ Hbj).
  - exact Hn.
Qed.

(* [open]'s and [mknod]'s argument, and [exec]'s -- one line each *)
Lemma init_str_arg (pt : uptd) (M : gmap Z (bv 8)) (s : Z) (bs : list (bv 8)) :
  init_text_layout pt -> init_lit M s bs -> uio_str_arg pt M s.
Proof.
  intros Hlay Hlit. exists (Z.of_nat (length bs)).
  split; [ exact (init_lit_cstr M s bs Hlit) | exact (init_lit_rd pt M s bs Hlay Hlit) ].
Qed.

(* THE exec fact: init's `char *argv[] = {"sh", 0}' as the protocol's
   [uexec_args].  Pure -- it is a property of the dumped .data, and it
   survives every stack store because [init_frame_ok] keeps the frames
   above 8192. *)
Lemma init_exec_args (M : gmap Z (bv 8)) :
  init_data_sub M -> uexec_args M INIT_SH INIT_ARGV init_sh_path init_sh_argv.
Proof.
  intro Hsub.
  assert (Hstr : ustr_at M INIT_SH init_sh_path).
  { split.
    - intros j b Hj. apply Hsub.
      exact (ubuf_check_sound InitData.init_data INIT_SH init_sh_path
               ltac:(vm_compute; reflexivity) j b Hj).
    - apply Hsub. vm_compute. reflexivity. }
  split; [ exact Hstr | ]. split.
  - intros i bs Hi.
    destruct i as [ | i' ];
      [ | exfalso; destruct i'; cbn in Hi; discriminate ].
    cbn in Hi. injection Hi as Hbs. rewrite <- Hbs.
    exists INIT_SH. split; [ | exact Hstr ].
    intros j Hj.
    destruct j as [|[|[|[|[|[|[|[|j'']]]]]]]];
      try (exfalso; cbn in Hj; lia);
      apply Hsub; vm_compute;
      first [ reflexivity | f_equal; apply bv_eq; vm_compute; reflexivity ].
  - intros j Hj.
    destruct j as [|[|[|[|[|[|[|[|j'']]]]]]]];
      try (exfalso; cbn in Hj; lia);
      apply Hsub; vm_compute;
      first [ reflexivity | f_equal; apply bv_eq; vm_compute; reflexivity ].
Qed.

(* ===================================================================== *)
(* §1 The contracts.                                                      *)
(* ===================================================================== *)

Section USpecInit.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).
  (* the two observers, exactly as [xv6_init_protocol] takes them *)
  Context (Q : list (bv 8) -> list (list (bv 8)) -> iProp Σ).
  Context (W : Z -> list (bv 8) -> iProp Σ).

  Local Notation Pinit := (xv6_init_protocol C pt Q W).
  Local Notation UVG m M := (uv_cap_gpr C pt Pinit M m).

  (* the register file every returning stub hands back *)
  Local Notation StubFile n ret m :=
    (<[Regidx a0_idx := ret]>
       (<[Regidx a7_idx := (mword_of_int n : mword 64)]> m)).

  (* the premises every stub shares *)
  Local Notation StubPre M m :=
    (init_layout pt /\ init_text_sub M /\
     is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true).

  (* the WRITE observation a printing function must be able to make, for
     every byte it may hand over.  PERSISTENT: [vprintf]'s loop spends one
     per iteration and [main]'s restart loop runs forever. *)
  Definition init_wobs (fd : Z) (bs : list (bv 8)) : iProp Σ :=
    (□ (∀ b : bv 8, ⌜b ∈ bs⌝ -∗ W fd [b]))%I.

  (* everything init's top statement must be handed to make its two
     observations, for as many turns of the restart loop as there are *)
  Definition init_obs : iProp Σ :=
    (□ Q init_sh_path init_sh_argv ∗ init_wobs 1 init_msg_bytes)%I.

  (* ------------------------------------------------------------------- *)
  (* §1a THE SYSCALL STUBS.  Each is `li a7,N; ecall; ret' and each        *)
  (* contract is its protocol arm (UmodeInitIo.v) read at the call site.   *)
  (* ------------------------------------------------------------------- *)

  (* --- dup, fork: an arbitrary return, memory untouched --------------- *)
  Definition wp_init_pureret_body (entry n : Z)
      (M : gmap Z (bv 8)) (m : regfile) :=
    forall (Hpre : StubPre M m)
      (Hsem : forall (g : regfile) (va : mword 64) (Mx : gmap Z (bv 8)),
                Pinit n g va Mx = uinit_arm_pureret C pt g va Mx),
    UVG m M -∗
    pc_is (mword_of_int entry) -∗
    (∀ CID : CpuId, ∀ ret : mword 64,
       UVG (StubFile n ret m) M -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* --- open, mknod: read the path at a0, arbitrary return ------------- *)
  Definition wp_init_strret_body (entry n : Z)
      (M : gmap Z (bv 8)) (m : regfile) :=
    forall (Hpre : StubPre M m)
      (Hsem : forall (g : regfile) (va : mword 64) (Mx : gmap Z (bv 8)),
                Pinit n g va Mx = uinit_arm_strret C pt g va Mx)
      (Hpath : uio_str_arg pt M (uint (m !!! Regidx a0_idx))),
    UVG m M -∗
    pc_is (mword_of_int entry) -∗
    (∀ CID : CpuId, ∀ ret : mword 64,
       UVG (StubFile n ret m) M -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* --- wait(0) -------------------------------------------------------- *)
  Definition wp_init_wait_body (M : gmap Z (bv 8)) (m : regfile) :=
    forall (Hpre : StubPre M m)
      (Hnull : uint (m !!! Regidx a0_idx) = 0),
    UVG m M -∗
    pc_is (mword_of_int InitSyms.wait) -∗
    (∀ CID : CpuId, ∀ ret : mword 64,
       UVG (StubFile SYS_wait ret m) M -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* --- write(fd, buf, n): the buffer is readable AND named ------------ *)
  Definition wp_init_write_body (M : gmap Z (bv 8)) (m : regfile)
      (bs : list (bv 8)) :=
    forall (Hpre : StubPre M m)
      (Hbuf : uv_rd pt M (uint (m !!! Regidx a1_idx))
                         (uint (m !!! Regidx a2_idx)))
      (Hbs : ubuf_at M (uint (m !!! Regidx a1_idx)) bs)
      (Hlen : Z.of_nat (length bs) = uint (m !!! Regidx a2_idx)),
    UVG m M -∗
    W (uint (m !!! Regidx a0_idx)) bs -∗
    pc_is (mword_of_int InitSyms.write) -∗
    (∀ CID : CpuId, ∀ ret : mword 64,
       UVG (StubFile SYS_write ret m) M -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* --- exec(path, argv): THE observable one, and it MAY come back ------ *)
  Definition wp_init_exec_body (M : gmap Z (bv 8)) (m : regfile)
      (path : list (bv 8)) (args : list (list (bv 8))) :=
    forall (Hpre : StubPre M m)
      (Hargs : uexec_args M (uint (m !!! Regidx a0_idx))
                            (uint (m !!! Regidx a1_idx)) path args),
    UVG m M -∗
    Q path args -∗
    pc_is (mword_of_int InitSyms.exec) -∗
    (∀ CID : CpuId, ∀ ret : mword 64,
       UVG (StubFile SYS_exec ret m) M -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* --- exit: does not return ------------------------------------------ *)
  Definition wp_init_exit_body (M : gmap Z (bv 8)) (m : regfile) :=
    forall (Hlay : init_layout pt) (Htext : init_text_sub M),
    UVG m M -∗
    pc_is (mword_of_int InitSyms.exit) -∗
    WP (Loop : expr riscv_lang).

  (* ------------------------------------------------------------------- *)
  (* §2 putc(fd, c) -- a 32-byte frame, one byte spilled into it at        *)
  (* [s0-17], and [write(fd, &c, 1)].  The buffer it hands the kernel is   *)
  (* its OWN frame, which is why the byte's value is what [W] observes.    *)
  (* ------------------------------------------------------------------- *)
  Definition wp_init_putc_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (c : bv 8) :=
    forall (Hlay : init_layout pt)
      (Htext : init_text_sub M)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 32)
      (Hfr : init_frame_ok sp0 32)
      (Hc : nth_byte (m !!! Regidx a1_idx) 0 = c)
      (Hret2 : is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true),
    UVG m M -∗
    W (uint (m !!! Regidx a0_idx)) [c] -∗
    pc_is (mword_of_int InitSyms.putc) -∗
    (∀ CID : CpuId, ∀ (m' : regfile) (M' : gmap Z (bv 8)),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜uM_only M M' (uint sp0 - 32) 32⌝ -∗
       UVG m' M' -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* ------------------------------------------------------------------- *)
  (* §3 vprintf(fd, fmt, ap) ON A %-FREE FORMAT STRING, and printf.        *)
  (*                                                                      *)
  (* The format loop is BOUNDED by the string's length, so it is ordinary  *)
  (* Rocq induction on a nat measure; [ap] (a2) is copied into s7 and      *)
  (* never dereferenced, so nothing is claimed about it.  This is the      *)
  (* reusable contract: any xv6 program printing a literal wants it.       *)
  (* ------------------------------------------------------------------- *)
  Definition wp_init_vprintf_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (s : Z) (bs : list (bv 8)) :=
    forall (Hlay : init_layout pt)
      (Himg : init_img_sub M)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 128)               (* 96 own + 32 putc's *)
      (Hfr : init_frame_ok sp0 128)
      (Hfmt : m !!! Regidx a1_idx = (mword_of_int s : mword 64))
      (Hlit : init_lit M s bs)
      (Hret2 : is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true),
    UVG m M -∗
    init_wobs (uint (m !!! Regidx a0_idx)) bs -∗
    pc_is (mword_of_int InitSyms.vprintf) -∗
    (∀ CID : CpuId, ∀ (m' : regfile) (M' : gmap Z (bv 8)),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜uM_only M M' (uint sp0 - 128) 128⌝ -∗
       UVG m' M' -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* printf(fmt, ...) -- spills a0..a7 into its own varargs save area and
     calls vprintf(1, fmt, ap).  The fd is the LITERAL 1. *)
  Definition wp_init_printf_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (s : Z) (bs : list (bv 8)) :=
    forall (Hlay : init_layout pt)
      (Himg : init_img_sub M)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 224)               (* 96 own + 128 vprintf's *)
      (Hfr : init_frame_ok sp0 224)
      (Hfmt : m !!! Regidx a0_idx = (mword_of_int s : mword 64))
      (Hlit : init_lit M s bs)
      (Hret2 : is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true),
    UVG m M -∗
    init_wobs 1 bs -∗
    pc_is (mword_of_int InitSyms.printf) -∗
    (∀ CID : CpuId, ∀ (m' : regfile) (M' : gmap Z (bv 8)),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜uM_only M M' (uint sp0 - 224) 224⌝ -∗
       UVG m' M' -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* ------------------------------------------------------------------- *)
  (* §4 main and start.  NEITHER RETURNS, so neither has a continuation    *)
  (* and neither says anything about the image afterwards -- there is no   *)
  (* afterwards.  Everything the theorem asserts is in [init_obs]: it is   *)
  (* the only thing that can discharge the [exec] and [write] arms, and a  *)
  (* run that exec'd anything other than ("sh", ["sh"]), or wrote a byte   *)
  (* that is not one of init's own, could not spend it.                    *)
  (* ------------------------------------------------------------------- *)
  Definition wp_init_main_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) :=
    forall (Hlay : init_layout pt)
      (Himg : init_img_sub M)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 256)               (* 32 own + 224 printf's *)
      (Hfr : init_frame_ok sp0 256),
    UVG m M -∗
    init_obs -∗
    pc_is (mword_of_int InitSyms.main) -∗
    WP (Loop : expr riscv_lang).

  (* THE TOP STATEMENT.  The stack budget is the deepest call chain:
       start 16 + main 32 + printf 96 + vprintf 96 + putc 32 = 272. *)
  Definition wp_init_start_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) :=
    forall (Hlay : init_layout pt)
      (Himg : init_img_sub M)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 272)
      (Hfr : init_frame_ok sp0 272),
    UVG m M -∗
    init_obs -∗
    pc_is (mword_of_int InitSyms.start) -∗
    WP (Loop : expr riscv_lang).

End USpecInit.
