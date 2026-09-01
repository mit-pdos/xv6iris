(* ===================================================================== *)
(* UkSh.v -- the `sh` user program on the urun engine, SH LANE STAGES 1-2: *)
(* the ELF entry, main's prologue, main's CONSOLE PREAMBLE, and the        *)
(* COMMAND LOOP down to the blank-line test -- getcmd, memset, gets, the   *)
(* read window, and the leading-blank scan.                                *)
(*                                                                        *)
(* Ten functions' worth of pcs: start, main, getcmd, memset, gets, and the *)
(* five syscall stubs those issue (open, close, exit, write, read).  The   *)
(* catalog is UCodeShK.v -- a SECOND catalog over the same dump as         *)
(* UCodeSh.v, emitted at [--prog shk] so the first-generation sh proofs    *)
(* (UProofSh*.v, still on-build over WpUmode*/UmodeIo) keep their names.   *)
(*                                                                        *)
(* WHAT THE TWO STAGES ESTABLISH.                                          *)
(*                                                                        *)
(* (1) THE QUIET ROW, ONCE.  open (15), close (21), exit (2) and write     *)
(* (16) are all outside the eight numbers [UsysMemOk.usys_mem_ok] gives a  *)
(* window to, so the kernel writes no user byte and the heap crosses the   *)
(* trap untouched.  [wp_ksh_qstub] is that fact once, for the whole        *)
(* two-instruction-and-a-return stub shape of usys.S; open, close and      *)
(* write are instances, and stage 5's chdir and dup will be two more.      *)
(*                                                                        *)
(* (2) THE WINDOW ROW, ONCE, AND AS A HYPOTHESIS.  [read] (5) IS in the    *)
(* window table, and the consumer leaf for the general window --           *)
(* [wp_uk_ecall_window] -- does not exist on this engine yet.  Its         *)
(* statement is the file's one Hypothesis, [ush_read_leaf], spelled at the *)
(* idiom of the landed [UkRunSys.wp_uk_ecall_wait_null].  Every lemma that *)
(* depends on it SAYS SO in its own header and carries it as an explicit   *)
(* argument once the section closes: [wp_ksh_read], [wp_ksh_gets],         *)
(* [wp_ksh_getcmd], [wp_ksh_cmd_head], [wp_ksh_console], [wp_ksh_main],    *)
(* [wp_ksh_start].  Everything else here -- the byte-run algebra, the      *)
(* quiet stubs, exit, memset, and the blank scan -- is unconditional.      *)
(*                                                                        *)
(* (3) TWO UNBOUNDED LOOPS, WITH VERY DIFFERENT INVARIANTS.  The console   *)
(* preamble                                                                *)
(*                                                                        *)
(*   while ((fd = open("console", O_RDWR)) >= 0)                           *)
(*     if (fd >= 3) { close(fd); break; }                                  *)
(*                                                                        *)
(* carries NOTHING round its cycle: its branch conditions are case split   *)
(* on the abstract [uv_btaken …] boolean, so the walk never learns what fd *)
(* the kernel returned and never needs to.  90 lines.  The COMMAND loop    *)
(* carries the buffer -- [ubytes γd sh_buf 100 f] at an existential [f] -- *)
(* and five register constants, [ush_regs].  Both close through            *)
(* [UkRunLeaf.wp_uk_btype_later], which init's loops needed too and which  *)
(* upstream landed beside [wp_uk_btype]; UkRunBr.v is now down to the ONE  *)
(* leaf UkRunLeaf still has no twin for, the x0 branch [wp_uk_btype0].     *)
(*                                                                        *)
(* (4) ONE FACT ABOUT MEMORY DECIDES CONTROL FLOW, and only one.  main's   *)
(* leading-blank scan has no bound in the code; what bounds it is gets'    *)
(* postcondition -- a NUL below the buffer's size -- because 0 is neither  *)
(* a space nor a tab.  Everything else that branches is either computed    *)
(* from a register the walk set itself or case split abstractly.           *)
(*                                                                        *)
(* WHERE THE STAGE STOPS.  0x97a, the first instruction of main's body     *)
(* past the blank-line test, is [ush_rest]: an abstract continuation that  *)
(* TAKES THE LOOP HEAD as its own premise, because the rest of main's body *)
(* (the cd builtin at 0x98e, fork1/parsecmd/runcmd at 0x92c) ends by       *)
(* falling back into 0x938.  The two are mutually recursive and the honest *)
(* cut is a premise that says so; stages 4-5 discharge it.                 *)
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
Require Import UCodeShK.
Require Import TsoCtx.
Require User.ShSyms User.ShInstrs.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* THE LINE BUFFER.  [buf.0] is 100 bytes of .bss at 0x2020 -- the ONE     *)
(* object the command loop owns, and the only thing its invariant carries  *)
(* besides the free stack.  main loads its address with the [auipc s2,0x1  *)
(* ; addi s2,s2,1800] pair at 0x918, and hands it to [getcmd] with the     *)
(* size in a1.                                                            *)
(* ===================================================================== *)
Definition sh_buf : Z := 0x2020.
Definition sh_nbuf : nat := 100.

(* one index of a byte-run's contents overwritten -- what a [sb] does to
   the function a [ubytes] is indexed by *)
Definition ush_set (f : nat -> bv 8) (j : nat) (b : bv 8) : nat -> bv 8 :=
  fun i => if Nat.eqb i j then b else f i.

Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)
Require Import ProcGeom.  (* [NOFILE] -- how many slots a table has *)
Section UkSh.
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
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation s7_idx := (mword_of_int 23 : mword 5).
  Local Notation s8_idx := (mword_of_int 24 : mword 5).
  Local Notation x0_idx := (mword_of_int 0 : mword 5).

  (* ===================================================================== *)
  (* THE SYMBOL PINS, ONE NAME EACH.  [shk_syms_pins] is a conjunction that *)
  (* grows a clause per stage, so a positional destruct at every use site   *)
  (* breaks whenever the catalog does.  Destructed ONCE, here.              *)
  (* ===================================================================== *)
  Local Lemma shp_start  : ShSyms.start  = 0x9d0.
  Proof. destruct shk_syms_pins as (H&_&_&_&_&_&_&_&_&_). exact H. Qed.
  Local Lemma shp_main   : ShSyms.main   = 0x8e2.
  Proof. destruct shk_syms_pins as (_&H&_&_&_&_&_&_&_&_). exact H. Qed.
  Local Lemma shp_getcmd : ShSyms.getcmd = 0x0.
  Proof. destruct shk_syms_pins as (_&_&H&_&_&_&_&_&_&_). exact H. Qed.
  Local Lemma shp_memset : ShSyms.memset = 0xa5c.
  Proof. destruct shk_syms_pins as (_&_&_&H&_&_&_&_&_&_). exact H. Qed.
  Local Lemma shp_gets   : ShSyms.gets   = 0xaaa.
  Proof. destruct shk_syms_pins as (_&_&_&_&H&_&_&_&_&_). exact H. Qed.
  Local Lemma shp_open   : ShSyms.open   = 0xcc6.
  Proof. destruct shk_syms_pins as (_&_&_&_&_&H&_&_&_&_). exact H. Qed.
  Local Lemma shp_close  : ShSyms.close  = 0xcae.
  Proof. destruct shk_syms_pins as (_&_&_&_&_&_&H&_&_&_). exact H. Qed.
  Local Lemma shp_exit   : ShSyms.exit   = 0xc86.
  Proof. destruct shk_syms_pins as (_&_&_&_&_&_&_&H&_&_). exact H. Qed.
  Local Lemma shp_write  : ShSyms.write  = 0xca6.
  Proof. destruct shk_syms_pins as (_&_&_&_&_&_&_&_&H&_). exact H. Qed.
  Local Lemma shp_read   : ShSyms.read   = 0xc9e.
  Proof. destruct shk_syms_pins as (_&_&_&_&_&_&_&_&_&H&_). exact H. Qed.


  (* ===================================================================== *)
  (* STAGE 2, §A -- THE BYTE-RUN ALGEBRA THE LINE BUFFER NEEDS.             *)
  (*                                                                       *)
  (* Stage 1 owned nothing but the free stack: its loop invariant was empty *)
  (* and no leaf it used touched a data byte.  Stage 2's whole subject is a *)
  (* BUFFER -- [buf.0], 100 bytes of .bss at 0x2020 -- written by memset,   *)
  (* by gets, and by the KERNEL through read's window row, then read back   *)
  (* by main's blank-line scan.  So the first thing the stage needs is to   *)
  (* take ONE byte out of a run, put a DIFFERENT byte back, and still have  *)
  (* the run.  [UserHeap.ustr_byte] does the unchanged case for strings;    *)
  (* this is the changing case, for [ubytes].                               *)
  (* ===================================================================== *)

  (* one byte of a run, out and back UNCHANGED *)
  Local Lemma ush_bytes_at (dq : dfrac) (a : Z) (k j : nat) (f : nat -> bv 8) :
    (j < k)%nat ->
    ubytesq γd dq a k f -∗
      ubyteq γd dq (a + Z.of_nat j) (f j) ∗
      (ubyteq γd dq (a + Z.of_nat j) (f j) -∗ ubytesq γd dq a k f).
  Proof.
    intros Hj. rewrite /ubytesq. iIntros "H".
    iDestruct (big_sepL_lookup_acc _ _ j j with "H") as "[Hb Hcl]";
      [ apply lookup_seq; split; [ lia | exact Hj ] | ].
    iSplitL "Hb"; [ iExact "Hb" | iExact "Hcl" ].
  Qed.

  (* a run only cares about its function BELOW the length *)
  Local Lemma ush_bytes_ext (dq : dfrac) (a : Z) (k : nat) (f g : nat -> bv 8) :
    (forall i : nat, (i < k)%nat -> f i = g i) ->
    ubytesq γd dq a k f -∗ ubytesq γd dq a k g.
  Proof.
    intros Hfg. rewrite /ubytesq. iIntros "H".
    iApply (big_sepL_mono with "H").
    intros i y Hy.
    apply lookup_seq in Hy. destruct Hy as [Hy Hlt]. subst y.
    rewrite (Hfg (0 + i)%nat Hlt). reflexivity.
  Qed.

  (* a ONE-byte run is a byte *)
  Local Lemma ush_bytes_one (b : Z) (g : nat -> bv 8) (v : bv 8) :
    g 0%nat = v -> ubytes γd b 1 g ⊣⊢ ubyte γd b v.
  Proof.
    intro Hv. rewrite /ubytes /ubytesq /ubyte /= Z.add_0_r right_id Hv.
    reflexivity.
  Qed.

  (* THE ACCESSOR THE WHOLE STAGE RUNS ON: one byte out, ANY byte back. *)
  Local Lemma ush_bytes_upd (a : Z) (k j : nat) (f : nat -> bv 8) :
    (j < k)%nat ->
    ubytes γd a k f -∗
      ubyte γd (a + Z.of_nat j) (f j) ∗
      (∀ b : bv 8, ubyte γd (a + Z.of_nat j) b -∗ ubytes γd a k (ush_set f j b)).
  Proof.
    intros Hj.
    remember (k - j - 1)%nat as q eqn:Hq.
    assert (Hk : k = (j + (1 + q))%nat) by lia.
    clear Hq. subst k.
    iIntros "H".
    rewrite (ubytes_app γd a j (1 + q) f).
    iDestruct "H" as "[Hlo Hhi]".
    rewrite (ubytes_app γd (a + Z.of_nat j) 1 q (fun i => f (j + i)%nat)).
    iDestruct "Hhi" as "[Hb Hrest]".
    rewrite (ush_bytes_one (a + Z.of_nat j) (fun i => f (j + i)%nat) (f j)
               ltac:(cbn; f_equal; lia)).
    iSplitL "Hb"; [ iExact "Hb" | ].
    iIntros (b) "Hb".
    rewrite (ubytes_app γd a j (1 + q) (ush_set f j b)).
    iSplitL "Hlo".
    { iApply (ush_bytes_ext (DfracOwn 1) a j f (ush_set f j b) with "Hlo").
      intros i Hi. unfold ush_set.
      rewrite (proj2 (Nat.eqb_neq i j) ltac:(lia)). reflexivity. }
    rewrite (ubytes_app γd (a + Z.of_nat j) 1 q
               (fun i => ush_set f j b (j + i)%nat)).
    iSplitL "Hb".
    { rewrite (ush_bytes_one (a + Z.of_nat j)
                 (fun i => ush_set f j b (j + i)%nat) b
                 ltac:(cbn; unfold ush_set;
                       rewrite (proj2 (Nat.eqb_eq (j + 0)%nat j) ltac:(lia));
                       reflexivity)).
      iExact "Hb". }
    iApply (ush_bytes_ext (DfracOwn 1) (a + Z.of_nat j + Z.of_nat 1) q
              (fun i => f (j + (1 + i))%nat)
              (fun i => ush_set f j b (j + (1 + i))%nat) with "Hrest").
    intros i Hi. unfold ush_set.
    rewrite (proj2 (Nat.eqb_neq (j + (1 + i))%nat j) ltac:(lia)). reflexivity.
  Qed.

  (* ADDRESS BOUNDS OFF THE RESOURCE -- UkEcho.v's [urun_ustr_bnd] at a
     plain run.  A byte the program owns is a byte the image maps, and the
     heap invariant bounds every mapped address by MAXVA, so no caller ever
     has to say where its buffer lives. *)
  Local Lemma urun_ubyte_bnd (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (dq : dfrac) (a : Z) (b : bv 8) :
    urun γt γd γs γfd h m pc avail -∗ ubyteq γd dq a b -∗ ⌜ 0 <= a < 2 ^ 38 ⌝.
  Proof.
    iIntros "Hrun Hb".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(_ & _ & Hh & _ & _)".
    iDestruct (uheap_ubyte with "Hh Hb") as %(_ & _ & Hbnd).
    iPureIntro. exact Hbnd.
  Qed.

  Local Lemma urun_ubytes_bnd (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (dq : dfrac) (a : Z) (k : nat) (f : nat -> bv 8) :
    (0 < k)%nat ->
    urun γt γd γs γfd h m pc avail -∗ ubytesq γd dq a k f -∗
    ⌜ 0 <= a /\ a + Z.of_nat k <= 2 ^ 38 ⌝.
  Proof.
    intros Hk. iIntros "Hrun Hbs".
    iDestruct (ush_bytes_at dq a k 0%nat f ltac:(lia) with "Hbs") as "[Hb0 Hcl]".
    iDestruct (urun_ubyte_bnd with "Hrun Hb0") as %Hlo.
    iDestruct ("Hcl" with "Hb0") as "Hbs".
    iDestruct (ush_bytes_at dq a k (k - 1)%nat f ltac:(lia) with "Hbs")
      as "[Hbk _]".
    iDestruct (urun_ubyte_bnd with "Hrun Hbk") as %Hhi.
    iPureIntro. rewrite Z.add_0_r in Hlo. lia.
  Qed.

  (* [m] says nothing about x0, but the BUNDLE inside [urun] does -- and     *)
  (* gets ends on [sb zero,0(s8)], whose stored byte IS the value of x0.     *)
  (* Without this the NUL that terminates main's scan could not be named.    *)
  (* ([UkRunBr.wp_uk_btype0] exists for the same reason on the branch side;  *)
  (* this is the read of x0 as a VALUE.)                                     *)
  Local Lemma urun_x0 (h : CpuId) (m : regfile) (pc : mword 64) (avail : nat) :
    urun γt γd γs γfd h m pc avail -∗
    ⌜ m !!! Regidx x0_idx = zero_reg ⌝ ∗ urun γt γd γs γfd h m pc avail.
  Proof.
    iIntros "Hrun".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iSplitR; [ iPureIntro; exact Hx0 | ].
    iExists xi, C, pt, Rfd, Rut, sz, M, pm, fdv.
    iFrame "Hheap Hstk Hufd Hb".
    iPureIntro. split; [ exact Hlo | exact Hpm ].
  Qed.

  Local Lemma ush_nth_byte0_zero : nth_byte (zero_reg : mword 64) 0 = ubyte0.
  Proof. vm_compute. reflexivity. Qed.

  (* [x - d] tested against zero, at values that cannot wrap: every "is this
     byte a blank / a newline / a return" test in main and in gets. *)
  Local Lemma ush_eqz_sub (x d : Z) :
    0 <= x < Z64 -> 0 <= d < Z64 ->
    eq_vec (mword_of_int (x - d) : mword 64) zero_reg = Z.eqb x d.
  Proof.
    intros Hx Hd.
    assert (E : (mword_of_int (x - d) : mword 64)
                = mword_of_int ((x - d) mod Z64)).
    { apply bv_eq. rewrite !moi_unsigned Zmod_mod. reflexivity. }
    rewrite E.
    rewrite (moi_eq_zero ((x - d) mod Z64)
               ltac:(apply Z.mod_pos_bound; unfold Z64; lia)).
    destruct (Z.eqb_spec x d) as [-> | Hne].
    - replace (d - d) with 0 by lia. reflexivity.
    - apply Z.eqb_neq. intro H0.
      apply Hne. apply Z.mod_divide in H0; [ | unfold Z64; lia ].
      destruct H0 as [qq Hqq]. unfold Z64 in *. lia.
  Qed.

  Local Lemma ush_neqz_sub (x d : Z) :
    0 <= x < Z64 -> 0 <= d < Z64 ->
    neq_vec (mword_of_int (x - d) : mword 64) zero_reg = negb (Z.eqb x d).
  Proof.
    intros Hx Hd. unfold neq_vec. rewrite (ush_eqz_sub x d Hx Hd). reflexivity.
  Qed.

  (* the [addi rd,rs,-d] this file does on a loaded byte, as a NUMBER *)
  Local Lemma ush_addi_sub (x d : Z) (imm : mword 12) :
    0 <= x < Z64 -> uoff_i12 imm = - d ->
    (mword_of_int (x - d) : mword 64)
    = add_vec (mword_of_int x : mword 64) (sign_extend' 64 imm).
  Proof.
    intros Hx Hd. apply (umoi_add_i12 (mword_of_int x) imm (x - d)).
    rewrite (uint_moi x Hx) Hd. lia.
  Qed.


  (* ===================================================================== *)
  (* THE SYSCALL STUB SHAPE.  usys.S emits every stub as                    *)
  (*   c.li a7,<n> ; ecall ; c.jr ra                                        *)
  (* so ONE lemma covers every quiet-row syscall sh issues; the caller      *)
  (* supplies the three [uinstr_is] resources and the number.  The eight    *)
  (* [n <> USYS_*] premises are the program paying, one by one, for not     *)
  (* being in any of the rows that write user memory.                       *)
  (* ===================================================================== *)
  Local Lemma wp_ksh_qstub (h : CpuId) (m : regfile) (pc0 pc1 pc2 : Z)
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
    (* ---- pc0  c.li a7,n ---- *)
    iApply (wp_uk_cli γt γd γs γfd h m (mword_of_int pc0) imm a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "Ci0 Hrun").
    assert (Em : <[Regidx a7_idx := regval_into_reg (sign_extend' 64 imm : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int n : mword 64)]> m)
      by (f_equal; exact Himm).
    rewrite E01 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int n : mword 64)]> m).
    (* ---- pc1  ecall -- the QUIET row ---- *)
    iApply (wp_uk_ecall_quiet γt γd γs γfd h1 m1 (mword_of_int pc1) n avail
              Hno He Hf Hx Hs Hw Hp Hr Hst Hcl Hdp Hop
              ltac:(rewrite E12; exact Hal2)
              with "Ci1 Hrun").
    rewrite E12.
    iIntros (h2 ret) "Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- pc2  c.jr ra ---- *)
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

  (* the QUIET stub's twin at OPEN.  Same three instructions; the middle
     one is the open leaf, whose handle the shell drops -- sh does not
     track its descriptors yet. *)
  Local Lemma wp_ksh_ostub (h : CpuId) (m : regfile) (pc0 pc1 pc2 : Z)
      (imm : mword 6) (avail : nat) :
    (sign_extend' 64 imm : mword 64) = mword_of_int USYS_open ->
    usysno (<[Regidx a7_idx := (mword_of_int USYS_open : mword 64)]> m) = USYS_open ->
        (* the three exclusions are NOT here: this stub IS the open one. *)
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
            (<[Regidx a7_idx := (mword_of_int USYS_open : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Himm Hno E01 E12 Hal2.
    iIntros "#Ci0 #Ci1 #Ci2 Hrun Hcont".
    (* ---- pc0  c.li a7,USYS_open ---- *)
    iApply (wp_uk_cli γt γd γs γfd h m (mword_of_int pc0) imm a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "Ci0 Hrun").
    assert (Em : <[Regidx a7_idx := regval_into_reg (sign_extend' 64 imm : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int USYS_open : mword 64)]> m)
      by (f_equal; exact Himm).
    rewrite E01 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int USYS_open : mword 64)]> m).
    (* ---- pc1  ecall -- OPEN, which moves the descriptor table ---- *)
    iApply (wp_uk_ecall_open γt γd γs γfd h1 m1 (mword_of_int pc1) avail
              Hno ltac:(rewrite E12; exact Hal2)
              with "Ci1 Hrun").
    rewrite E12.
    (* the shell does not track its descriptors, so the handle is dropped *)
    iIntros (h2 ret) "_ Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- pc2  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int USYS_open : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr γt γd γs γfd h2 m2 (mword_of_int pc2) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "Ci2 Hrun").
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hrun").
  Qed.

  (* ---- open @0xcc6, SYS_open = 15 ------------------------------------- *)
  Lemma wp_ksh_open (h : CpuId) (m : regfile) (avail : nat) :
    shk_code γt -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.open) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun γt γd γs γfd h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun Hcont".
    rewrite shp_open.
    iApply (wp_ksh_ostub h m 0xcc6 0xcc8 0xccc
              (mword_of_int 15 : mword 6) avail
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(unfold usysno;
                    rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 15 : mword 64));
                    vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] [] [] Hrun Hcont").
    { iApply (uis_shk_cc6 with "Hcode"). }
    { iApply (uis_shk_cc8 with "Hcode"). }
    { iApply (uis_shk_ccc with "Hcode"). }
  Qed.

  (* ---- close @0xcae, SYS_close = 21 ----------------------------------- *)
  Lemma wp_ksh_close (h : CpuId) (m : regfile) (avail : nat) :
    shk_code γt -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.close) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun γt γd γs γfd h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 21 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun Hcont".
    rewrite shp_close.
    iApply (wp_ksh_qstub h m 0xcae 0xcb0 0xcb4
              (mword_of_int 21 : mword 6) 21 avail
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(unfold usysno;
                    rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 21 : mword 64));
                    vm_compute; reflexivity)
              ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] [] [] Hrun Hcont").
    { iApply (uis_shk_cae with "Hcode"). }
    { iApply (uis_shk_cb0 with "Hcode"). }
    { iApply (uis_shk_cb4 with "Hcode"). }
  Qed.

  (* ---- exit @0xc86, the arm with no continuation ---------------------- *)
  Lemma wp_ksh_exit (h : CpuId) (m : regfile) (avail : nat) :
    shk_code γt -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.exit) avail -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun".
    rewrite shp_exit.
    (* ---- 0xc86  c.li a7,2 ---- *)
    iApply (wp_uk_cli γt γd γs γfd h m (mword_of_int 0xc86)
              (mword_of_int 2 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_c86 with "Hcode"). }
    assert (Ec86 : add_vec_int (mword_of_int 0xc86 : mword 64) 2
                   = mword_of_int 0xc88)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 2 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 2 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite Ec86 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 2 : mword 64)]> m).
    (* ---- 0xc88  ecall -- SYS_exit ---- *)
    iApply (wp_uk_ecall_exit γt γd γs γfd h1 m1 (mword_of_int 0xc88) avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 2 : mword 64));
                    vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_c88 with "Hcode"). }
  Qed.


  (* ---- write @0xca6, SYS_write = 16 -- quiet, the third stub instance -- *)
  Lemma wp_ksh_write (h : CpuId) (m : regfile) (avail : nat) :
    shk_code γt -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.write) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun γt γd γs γfd h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun Hcont".
    rewrite shp_write.
    iApply (wp_ksh_qstub h m 0xca6 0xca8 0xcac
              (mword_of_int 16 : mword 6) 16 avail
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(unfold usysno;
                    rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 16 : mword 64));
                    vm_compute; reflexivity)
              ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] [] [] Hrun Hcont").
    { iApply (uis_shk_ca6 with "Hcode"). }
    { iApply (uis_shk_ca8 with "Hcode"). }
    { iApply (uis_shk_cac with "Hcode"). }
  Qed.


  (* ===================================================================== *)
  (* THE ONE HYPOTHESIS OF STAGE 2: THE GENERAL WINDOW ECALL LEAF.          *)
  (*                                                                       *)
  (* [read] is syscall 5, and 5 is one of the eight numbers                 *)
  (* [UsysMemOk.usys_mem_ok] gives a WINDOW to: the kernel may write up to  *)
  (* [max 0 arg2] bytes at [arg1] and nothing else.  UkRunSys.v has the two *)
  (* degenerate consumers of that table -- [wp_uk_ecall_quiet], where the   *)
  (* window is empty by the row, and [wp_uk_ecall_wait_null], where it is   *)
  (* empty by the argument -- but not the GENERAL one, where the caller     *)
  (* hands the buffer over and gets it back with a prefix rewritten.  A     *)
  (* sibling lane is building it as [wp_uk_ecall_window]; this is its       *)
  (* statement, spelled at the same section variables, the same binder      *)
  (* order and the same resource spellings as [wp_uk_ecall_wait_null]       *)
  (* (UkRunSys.v:175) so that the discharge is [intros] and an [exact].     *)
  (*                                                                       *)
  (* NOTE WHAT IT DOES NOT SAY.  Nothing ties the returned [r] to the       *)
  (* number of bytes [d] the kernel wrote -- the row does not, and gets     *)
  (* does not need it: gets tests [r] to decide whether to keep reading and *)
  (* stores whatever byte is in its one-byte window either way, so the walk *)
  (* is correct at any [d <= k].                                           *)
  (*                                                                       *)
  (* EVERY LEMMA BELOW THAT DEPENDS ON IT SAYS SO IN ITS HEADER:            *)
  (* [wp_ksh_read], [wp_ksh_gets], [wp_ksh_getcmd], [wp_ksh_cmd_head],      *)
  (* [wp_ksh_console], [wp_ksh_main] and [wp_ksh_start].  Everything else   *)
  (* in this file -- the byte-run algebra, the quiet stubs, exit, memset,   *)
  (* and main's blank-line scan -- is unconditional.                        *)
  (* ===================================================================== *)
  Hypothesis ush_read_leaf :
    forall (h : CpuId) (m : regfile) (pc : mword 64) (a : Z) (k : nat)
           (f : nat -> bv 8) (avail : nat),
      usysno m = USYS_read ->
      uint (m !!! Regidx a1_idx) = a ->
      uint (m !!! Regidx a2_idx) = Z.of_nat k ->
      is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
      uinstr_is γt pc false (ECALL tt) -∗
      ubytes γd a k f -∗
      urun γt γd γs γfd h m pc avail -∗
      (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8),
         ⌜ (d <= k)%nat ⌝ -∗
         ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
         ubytes γd a k g -∗
         urun γt γd γs γfd h' (<[Regidx a0_idx := r]> m)
           (add_vec_int pc 4) avail -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).

  (* ---- read @0xc9e, SYS_read = 5 -- the WINDOW row's stub -------------- *)
  (* DEPENDS ON [ush_read_leaf].                                            *)
  Lemma wp_ksh_read (h : CpuId) (m : regfile) (a : Z) (k : nat)
      (f : nat -> bv 8) (avail : nat) :
    uint (m !!! Regidx a1_idx) = a ->
    uint (m !!! Regidx a2_idx) = Z.of_nat k ->
    shk_code γt -∗
    ubytes γd a k f -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.read) avail -∗
    (∀ (h' : CpuId) (ret : mword 64) (d : nat) (g : nat -> bv 8),
       ⌜ (d <= k)%nat ⌝ -∗
       ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
       ubytes γd a k g -∗
       urun γt γd γs γfd h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha1 Ha2. iIntros "#Hcode Hbs Hrun Hcont".
    rewrite shp_read.
    (* ---- 0xc9e  c.li a7,5 ---- *)
    iApply (wp_uk_cli γt γd γs γfd h m (mword_of_int 0xc9e)
              (mword_of_int 5 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_c9e with "Hcode"). }
    assert (Ec9e : add_vec_int (mword_of_int 0xc9e : mword 64) 2
                   = mword_of_int 0xca0)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 5 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite Ec9e Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m).
    assert (Ha1_1 : uint (m1 !!! Regidx a1_idx) = a).
    { rewrite /m1 (upd_ne m (Regidx a7_idx) (Regidx a1_idx)
                     (mword_of_int 5 : mword 64)
                     ltac:(vm_compute; discriminate)). exact Ha1. }
    assert (Ha2_1 : uint (m1 !!! Regidx a2_idx) = Z.of_nat k).
    { rewrite /m1 (upd_ne m (Regidx a7_idx) (Regidx a2_idx)
                     (mword_of_int 5 : mword 64)
                     ltac:(vm_compute; discriminate)). exact Ha2. }
    (* ---- 0xca0  ecall -- the WINDOW row ---- *)
    iApply (ush_read_leaf h1 m1 (mword_of_int 0xca0) a k f avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 5 : mword 64));
                    vm_compute; reflexivity)
              Ha1_1 Ha2_1
              ltac:(vm_compute; reflexivity)
              with "[] Hbs Hrun").
    { iApply (uis_shk_ca0 with "Hcode"). }
    assert (Eca0 : add_vec_int (mword_of_int 0xca0 : mword 64) 4
                   = mword_of_int 0xca4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eca0.
    iIntros (h2 ret d g) "%Hd %Hg Hbs Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0xca4  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite /m2 /m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 5 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr γt γd γs γfd h2 m2 (mword_of_int 0xca4) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_ca4 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret d g with "[] [] Hbs Hrun");
      iPureIntro; [ exact Hd | exact Hg ].
  Qed.


  (* ===================================================================== *)
  (* memset @0xa5c -- 16 instructions, one byte loop.  UNCONDITIONAL.       *)
  (*                                                                       *)
  (* The contract deliberately FORGETS what was written: getcmd calls it as *)
  (* [memset(buf, 0, 100)] only to clear the line, and what the command     *)
  (* loop needs afterwards is that it still OWNS the buffer, not what is in *)
  (* it -- gets overwrites a prefix and plants the NUL that main's scan     *)
  (* stops on.  Dropping the contents halves the loop invariant: it carries *)
  (* the two addresses and nothing about the bytes.                         *)
  (* ===================================================================== *)

  (* a callee-saved register is none of the ones a caller may clobber *)
  Local Lemma ucs_ne (r q : mword 5) :
    ucallee_saved_idx r = true -> ucallee_saved_idx q = false ->
    Regidx r <> Regidx q.
  Proof.
    intros Hr Hq He.
    assert (Hrr : r = q) by (injection He; trivial).
    rewrite Hrr Hq in Hr. discriminate.
  Qed.

  (* the byte loop, 0xa70..0xa76:
       sb a1,0(a5) ; c.addi a5,a5,1 ; bne a5,a4,0xa70
     [k] is the number of bytes still to come AFTER this one, so the
     measure is the loop's own trip count and the [bne] decides it. *)
  (* THE LOOP CARRIES THE BYTE IT IS WRITING.  [memset] does not merely
     leave SOME contents behind, it leaves [c] at every index -- and the
     [NULL] cap at an [execcmd] node's argv is exactly that fact, so the
     postcondition names the byte rather than existentially quantifying it.
     The invariant is the prefix already written ([Hpre]); the constant is
     stable across iterations because the loop writes only a5. *)
  Local Lemma wp_ksh_memset_loop (a : Z) (N : nat) (c : bv 8) :
    forall (k j : nat) (h : CpuId) (mc : regfile) (f : nat -> bv 8) (nn : nat),
    (N = j + 1 + k)%nat ->
    0 <= a -> a + Z.of_nat N < Z64 ->
    nth_byte (mc !!! Regidx a1_idx) 0 = c ->
    (forall i : nat, (i < j)%nat -> f i = c) ->
    mc !!! Regidx a5_idx = mword_of_int (a + Z.of_nat j) ->
    mc !!! Regidx a4_idx = mword_of_int (a + Z.of_nat N) ->
    shk_code γt -∗
    ubytes γd a N f -∗
    urun γt γd γs γfd h mc (mword_of_int 0xa70) nn -∗
    (ubytes γd a N (fun _ => c) -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall r : mword 5, Regidx r <> Regidx a5_idx ->
             mc' !!! Regidx r = mc !!! Regidx r ⌝ -∗
         urun γt γd γs γfd h' mc' (mword_of_int 0xa7a) nn -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros k. induction k as [| k IH ];
      intros j h mc f nn HN Ha0 Ha64 Hc Hpre Ha5 Ha4;
      iIntros "#Hcode Hbs Hrun Hcont".
    - (* the LAST byte: after it a5 = a4 and the branch falls through *)
      iDestruct (ush_bytes_upd a N j f ltac:(lia) with "Hbs") as "[Hb Hcl]".
      iApply (wp_uk_sb γt γd γs γfd h mc (mword_of_int 0xa70)
                (mword_of_int 0 : mword 12) a5_idx a1_idx
                (a + Z.of_nat j) (f j) nn
                ltac:(rewrite Ha5 (uint_moi (a + Z.of_nat j) ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_i12; lia)
                with "[] Hb Hrun").
      { iApply (uis_shk_a70 with "Hcode"). }
      iIntros "Hb".
      iDestruct ("Hcl" $! (nth_byte (mc !!! Regidx a1_idx) 0) with "Hb") as "Hbs".
      assert (Ea70 : add_vec_int (mword_of_int 0xa70 : mword 64) 4
                     = mword_of_int 0xa74)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ea70. iIntros (h1) "Hrun".
      (* ---- 0xa74  c.addi a5,a5,1 ---- *)
      assert (E1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                   = mword_of_int 1)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_caddi γt γd γs γfd h1 mc (mword_of_int 0xa74)
                (mword_of_int 1 : mword 6) a5_idx
                (mword_of_int (a + Z.of_nat j + 1)) nn
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5 E1 moi_add; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_a74 with "Hcode"). }
      assert (Ea74 : add_vec_int (mword_of_int 0xa74 : mword 64) 2
                     = mword_of_int 0xa76)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ea74. iIntros (h2) "Hrun".
      set (m1 := <[Regidx a5_idx
                   := regval_into_reg (mword_of_int (a + Z.of_nat j + 1)
                                       : mword 64)]> mc).
      assert (Hpres : forall r : mword 5, Regidx r <> Regidx a5_idx ->
                        m1 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr; exact (upd_ne mc (Regidx a5_idx) (Regidx r) _ Hr)).
      assert (Ha5_1 : m1 !!! Regidx a5_idx
                      = mword_of_int (a + Z.of_nat j + 1))
        by exact (upd_eq mc (Regidx a5_idx)
                    (regval_into_reg (mword_of_int (a + Z.of_nat j + 1)
                                      : mword 64))).
      assert (Ha4_1 : m1 !!! Regidx a4_idx = mword_of_int (a + Z.of_nat N))
        by (rewrite (Hpres a4_idx ltac:(vm_compute; discriminate)); exact Ha4).
      (* ---- 0xa76  bne a5,a4 -- NOT taken: this was the last byte ---- *)
      assert (Htk : false = uv_btaken BNE (m1 !!! Regidx a5_idx)
                              (m1 !!! Regidx a4_idx)).
      { cbn [uv_btaken]. rewrite Ha5_1 Ha4_1.
        rewrite (moi_neq_vec (a + Z.of_nat j + 1) (a + Z.of_nat N)
                   ltac:(unfold Z64 in *; lia) ltac:(unfold Z64 in *; lia)).
        symmetry. apply negb_false_iff. apply Z.eqb_eq. lia. }
      iApply (wp_uk_btype γt γd γs γfd h2 m1 (mword_of_int 0xa76)
                (mword_of_int 8186 : mword 13) a4_idx a5_idx BNE false
                (mword_of_int 0xa70) nn
                Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shk_a76 with "Hcode"). }
      assert (Ea76 : add_vec_int (mword_of_int 0xa76 : mword 64) 4
                     = mword_of_int 0xa7a)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ea76. iIntros (h3) "Hrun".
      iApply ("Hcont" with "[Hbs] [] Hrun").
      { iApply (ush_bytes_ext (DfracOwn 1) a N
                  (ush_set f j (nth_byte (mc !!! Regidx a1_idx) 0))
                  (fun _ => c) with "Hbs").
        intros i Hi. unfold ush_set.
        destruct (Nat.eqb_spec i j) as [-> | Hne];
          [ exact Hc | apply Hpre; lia ]. }
      { iPureIntro. exact Hpres. }
    - (* a body byte: a5 moves on and the branch goes back to 0xa70 *)
      iDestruct (ush_bytes_upd a N j f ltac:(lia) with "Hbs") as "[Hb Hcl]".
      iApply (wp_uk_sb γt γd γs γfd h mc (mword_of_int 0xa70)
                (mword_of_int 0 : mword 12) a5_idx a1_idx
                (a + Z.of_nat j) (f j) nn
                ltac:(rewrite Ha5 (uint_moi (a + Z.of_nat j) ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_i12; lia)
                with "[] Hb Hrun").
      { iApply (uis_shk_a70 with "Hcode"). }
      iIntros "Hb".
      iDestruct ("Hcl" $! (nth_byte (mc !!! Regidx a1_idx) 0) with "Hb") as "Hbs".
      assert (Ea70 : add_vec_int (mword_of_int 0xa70 : mword 64) 4
                     = mword_of_int 0xa74)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ea70. iIntros (h1) "Hrun".
      assert (E1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                   = mword_of_int 1)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_caddi γt γd γs γfd h1 mc (mword_of_int 0xa74)
                (mword_of_int 1 : mword 6) a5_idx
                (mword_of_int (a + Z.of_nat j + 1)) nn
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5 E1 moi_add; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_a74 with "Hcode"). }
      assert (Ea74 : add_vec_int (mword_of_int 0xa74 : mword 64) 2
                     = mword_of_int 0xa76)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ea74. iIntros (h2) "Hrun".
      set (m1 := <[Regidx a5_idx
                   := regval_into_reg (mword_of_int (a + Z.of_nat j + 1)
                                       : mword 64)]> mc).
      assert (Hpres : forall r : mword 5, Regidx r <> Regidx a5_idx ->
                        m1 !!! Regidx r = mc !!! Regidx r)
        by (intros r Hr; exact (upd_ne mc (Regidx a5_idx) (Regidx r) _ Hr)).
      assert (Ha5_1 : m1 !!! Regidx a5_idx
                      = mword_of_int (a + Z.of_nat (j + 1))).
      { replace (a + Z.of_nat (j + 1)) with (a + Z.of_nat j + 1) by lia.
        exact (upd_eq mc (Regidx a5_idx)
                 (regval_into_reg (mword_of_int (a + Z.of_nat j + 1)
                                   : mword 64))). }
      assert (Ha4_1 : m1 !!! Regidx a4_idx = mword_of_int (a + Z.of_nat N))
        by (rewrite (Hpres a4_idx ltac:(vm_compute; discriminate)); exact Ha4).
      assert (Htk : true = uv_btaken BNE (m1 !!! Regidx a5_idx)
                             (m1 !!! Regidx a4_idx)).
      { cbn [uv_btaken]. rewrite Ha5_1 Ha4_1.
        rewrite (moi_neq_vec (a + Z.of_nat (j + 1)) (a + Z.of_nat N)
                   ltac:(unfold Z64 in *; lia) ltac:(unfold Z64 in *; lia)).
        symmetry. apply negb_true_iff. apply Z.eqb_neq. lia. }
      iApply (wp_uk_btype γt γd γs γfd h2 m1 (mword_of_int 0xa76)
                (mword_of_int 8186 : mword 13) a4_idx a5_idx BNE true
                (mword_of_int 0xa70) nn
                Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_a76 with "Hcode"). }
      iIntros (h3) "Hrun".
      iApply (IH (j + 1)%nat h3 m1
                (ush_set f j (nth_byte (mc !!! Regidx a1_idx) 0)) nn
                ltac:(lia) Ha0 Ha64
                ltac:(rewrite (Hpres a1_idx ltac:(vm_compute; discriminate));
                      exact Hc)
                ltac:(intros i Hi; unfold ush_set;
                      destruct (Nat.eqb_spec i j) as [-> | Hne];
                        [ exact Hc | apply Hpre; lia ])
                Ha5_1 Ha4_1
                with "Hcode Hbs Hrun").
      iIntros "Hbs" (h4 mc') "%Hpres' Hrun".
      iApply ("Hcont" with "Hbs [] Hrun").
      iPureIntro. intros r Hr. rewrite (Hpres' r Hr). exact (Hpres r Hr).
  Qed.


  (* two register indices are equal when their numbers are *)
  Local Lemma ush_ridx_eq (r q : mword 5) : uint r = uint q -> Regidx r = Regidx q.
  Proof.
    intro H. f_equal. apply bv_eq. rewrite <- !(uint_unsigned_n 5). exact H.
  Qed.

  Local Lemma ush_ridx_ne (r q : mword 5) : uint r <> uint q -> Regidx r <> Regidx q.
  Proof.
    intros H He. apply H.
    assert (Hrq : r = q) by (injection He; trivial). rewrite Hrq. reflexivity.
  Qed.

  (* ---- memset, the whole function ------------------------------------- *)
  Lemma wp_ksh_memset (h : CpuId) (m : regfile) (a : Z) (N : nat)
      (f : nat -> bv 8) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int a ->
    m !!! Regidx a2_idx = mword_of_int (Z.of_nat N) ->
    (0 < N)%nat -> Z.of_nat N < Z31 ->
    shk_code γt -∗
    ubytes γd a N f -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.memset) (2 + nn) -∗
    (ubytes γd a N (fun _ => nth_byte (m !!! Regidx a1_idx) 0) -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Ha2 HN0 HN31. iIntros "#Hcode Hbs Hrun Hcont".
    rewrite shp_memset.
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    iDestruct (urun_ubytes_bnd h m _ (2 + nn) (DfracOwn 1) a N f ltac:(lia)
                 with "Hrun Hbs") as %[Halo Hahi].
    change (2 ^ 38) with 274877906944 in Hahi.
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    assert (Hlo : 16 <= uint sp0) by lia.
    set (vra := m !!! Regidx ra_idx).
    set (vs0 := m !!! Regidx s0_idx).
    assert (Hbsp1 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                    = bv_unsigned sp0 - 16).
    { replace (- (8 * Z.of_nat 2)) with (-16) by lia.
      exact (uv_avi_neg sp0 16 ltac:(lia) ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp16 : uint (add_vec_int sp0 (- (8 * Z.of_nat 2))) = uint sp0 - 16)
      by (rewrite !uint_unsigned; exact Hbsp1).
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    assert (Ho0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    (* ---- 0xa5c  c.addi sp,sp,-16 -- THE PUSH ---- *)
    iApply (wp_uk_caddi_sp_dn γt γd γs γfd h m (mword_of_int 0xa5c)
              (mword_of_int 48 : mword 6) 2 nn
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_a5c with "Hcode"). }
    assert (Ea5c : add_vec_int (mword_of_int 0xa5c : mword 64) 2
                   = mword_of_int 0xa5e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp ustack_2 Ea5c.
    iIntros "(_ & [%v8 Hw8] & [%v0 Hw0])".
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 2)))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by exact (upd_eq m (Regidx csp_rs1)
                  (regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 2))))).
    assert (Hm1 : forall r : mword 5, Regidx r <> Regidx csp_rs1 ->
                    m1 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr; exact (upd_ne m (Regidx csp_rs1) (Regidx r) _ Hr)).
    (* ---- 0xa5e  c.sdsp ra,8(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd h1 m1 (mword_of_int 0xa5e)
              (mword_of_int 1 : mword 6) ra_idx (uint sp0 - 8) v8 nn
              ltac:(rewrite Hsp1 Hsp16 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw8 Hrun").
    { iApply (uis_shk_a5e with "Hcode"). }
    iIntros "Hw8".
    rewrite (Hm1 ra_idx ltac:(vm_compute; discriminate)).
    assert (Ea5e : add_vec_int (mword_of_int 0xa5e : mword 64) 2
                   = mword_of_int 0xa60)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea5e. iIntros (h2) "Hrun".
    (* ---- 0xa60  c.sdsp s0,0(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd h2 m1 (mword_of_int 0xa60)
              (mword_of_int 0 : mword 6) s0_idx (uint sp0 - 16) v0 nn
              ltac:(rewrite Hsp1 Hsp16 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw0 Hrun").
    { iApply (uis_shk_a60 with "Hcode"). }
    iIntros "Hw0".
    rewrite (Hm1 s0_idx ltac:(vm_compute; discriminate)).
    assert (Ea60 : add_vec_int (mword_of_int 0xa60 : mword 64) 2
                   = mword_of_int 0xa62)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea60. iIntros (h3) "Hrun".
    (* ---- 0xa62  c.addi4spn s0,sp,16 (s0 is dead until the epilogue) ---- *)
    iApply (wp_uk_caddi4spn γt γd γs γfd h3 m1 (mword_of_int 0xa62)
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8) s0_idx
              (add_vec (m1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8)))) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              eq_refl
              with "[] Hrun").
    { iApply (uis_shk_a62 with "Hcode"). }
    assert (Ea62 : add_vec_int (mword_of_int 0xa62 : mword 64) 2
                   = mword_of_int 0xa64)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea62. iIntros (h4) "Hrun".
    set (m2 := <[Regidx s0_idx
                 := regval_into_reg
                      (add_vec (m1 !!! Regidx csp_rs1)
                         (sign_extend' 64
                            (caddi4spn_imm (mword_of_int 4 : mword 8))))]> m1).
    assert (Hm2 : forall r : mword 5, Regidx r <> Regidx s0_idx ->
                    m2 !!! Regidx r = m1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m1 (Regidx s0_idx) (Regidx r) _ Hr)).
    assert (Hsp2 : m2 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by (rewrite (Hm2 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp1).
    assert (Ha2_2 : m2 !!! Regidx a2_idx = mword_of_int (Z.of_nat N)).
    { rewrite (Hm2 a2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm1 a2_idx ltac:(vm_compute; discriminate)). exact Ha2. }
    assert (Ha0_2 : m2 !!! Regidx a0_idx = mword_of_int a).
    { rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    (* ---- 0xa64  c.beqz a2 -- the count is nonzero, so NOT taken ---- *)
    assert (Htk64 : false = eq_vec (m2 !!! Regidx a2_idx) zero_reg).
    { rewrite Ha2_2.
      rewrite (moi_eq_zero (Z.of_nat N) ltac:(unfold Z31, Z64 in *; lia)).
      symmetry. apply Z.eqb_neq. lia. }
    iApply (wp_uk_cbeqz γt γd γs γfd h4 m2 (mword_of_int 0xa64)
              (mword_of_int 11 : mword 8) (mword_of_int 4 : mword 3) a2_idx
              false (mword_of_int 0xa7a) nn
              ltac:(vm_compute; reflexivity) Htk64
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shk_a64 with "Hcode"). }
    assert (Ea64 : add_vec_int (mword_of_int 0xa64 : mword 64) 2
                   = mword_of_int 0xa66)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea64. iIntros (h5) "Hrun".
    (* ---- 0xa66  c.mv a5,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h5 m2 (mword_of_int 0xa66) a5_idx a0_idx
              (mword_of_int a) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_2 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_a66 with "Hcode"). }
    assert (Ea66 : add_vec_int (mword_of_int 0xa66 : mword 64) 2
                   = mword_of_int 0xa68)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea66. iIntros (h6) "Hrun".
    set (m3 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int a : mword 64)]> m2).
    assert (Hm3 : forall r : mword 5, Regidx r <> Regidx a5_idx ->
                    m3 !!! Regidx r = m2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m2 (Regidx a5_idx) (Regidx r) _ Hr)).
    assert (Ha2_3 : m3 !!! Regidx a2_idx = mword_of_int (Z.of_nat N))
      by (rewrite (Hm3 a2_idx ltac:(vm_compute; discriminate)); exact Ha2_2).
    (* ---- 0xa68  c.slli a2,a2,0x20 ---- *)
    iApply (wp_uk_cslli γt γd γs γfd h6 m3 (mword_of_int 0xa68)
              (mword_of_int 32 : mword 6) a2_idx
              (mword_of_int (Z.of_nat N * 2 ^ 32)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha2_3; symmetry;
                    exact (moi_shl (Z.of_nat N) 32 ltac:(lia)))
              with "[] Hrun").
    { iApply (uis_shk_a68 with "Hcode"). }
    assert (Ea68 : add_vec_int (mword_of_int 0xa68 : mword 64) 2
                   = mword_of_int 0xa6a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea68. iIntros (h7) "Hrun".
    set (m4 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int (Z.of_nat N * 2 ^ 32)
                                     : mword 64)]> m3).
    assert (Hm4 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
                    m4 !!! Regidx r = m3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m3 (Regidx a2_idx) (Regidx r) _ Hr)).
    assert (Ha2_4 : m4 !!! Regidx a2_idx
                    = mword_of_int (Z.of_nat N * 2 ^ 32))
      by exact (upd_eq m3 (Regidx a2_idx)
                  (regval_into_reg (mword_of_int (Z.of_nat N * 2 ^ 32)
                                    : mword 64))).
    (* ---- 0xa6a  c.srli a2,a2,0x20 -- the pair is a 32-bit zero-extend -- *)
    iApply (wp_uk_csrli γt γd γs γfd h7 m4 (mword_of_int 0xa6a)
              (mword_of_int 32 : mword 6) (mword_of_int 4 : mword 3) a2_idx
              (mword_of_int (Z.of_nat N)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha2_4;
                    rewrite (moi_shr (Z.of_nat N * 2 ^ 32) 32 ltac:(lia)
                               ltac:(change (2 ^ 32) with 4294967296;
                                     unfold Z31, Z64 in *; lia));
                    rewrite Z.div_mul; [ reflexivity | vm_compute; discriminate ])
              with "[] Hrun").
    { iApply (uis_shk_a6a with "Hcode"). }
    assert (Ea6a : add_vec_int (mword_of_int 0xa6a : mword 64) 2
                   = mword_of_int 0xa6c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea6a. iIntros (h8) "Hrun".
    set (m5 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int (Z.of_nat N) : mword 64)]> m4).
    assert (Hm5 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
                    m5 !!! Regidx r = m4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m4 (Regidx a2_idx) (Regidx r) _ Hr)).
    assert (Ha2_5 : m5 !!! Regidx a2_idx = mword_of_int (Z.of_nat N))
      by exact (upd_eq m4 (Regidx a2_idx)
                  (regval_into_reg (mword_of_int (Z.of_nat N) : mword 64))).
    assert (Ha0_5 : m5 !!! Regidx a0_idx = mword_of_int a).
    { rewrite (Hm5 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm3 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_2. }
    (* ---- 0xa6c  add a4,a2,a0 -- the end address ---- *)
    iApply (wp_uk_add γt γd γs γfd h8 m5 (mword_of_int 0xa6c)
              a2_idx a0_idx a4_idx (mword_of_int (a + Z.of_nat N)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha2_5 Ha0_5 moi_add;
                    replace (a + Z.of_nat N) with (Z.of_nat N + a) by lia;
                    reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_a6c with "Hcode"). }
    assert (Ea6c : add_vec_int (mword_of_int 0xa6c : mword 64) 4
                   = mword_of_int 0xa70)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea6c. iIntros (h9) "Hrun".
    set (m6 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int (a + Z.of_nat N)
                                     : mword 64)]> m5).
    assert (Hm6 : forall r : mword 5, Regidx r <> Regidx a4_idx ->
                    m6 !!! Regidx r = m5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m5 (Regidx a4_idx) (Regidx r) _ Hr)).
    assert (Ha4_6 : m6 !!! Regidx a4_idx = mword_of_int (a + Z.of_nat N))
      by exact (upd_eq m5 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int (a + Z.of_nat N) : mword 64))).
    assert (Ha5_6 : m6 !!! Regidx a5_idx = mword_of_int (a + Z.of_nat 0)).
    { replace (a + Z.of_nat 0) with a by lia.
      rewrite (Hm6 a5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 a5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 a5_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx a5_idx)
               (regval_into_reg (mword_of_int a : mword 64))). }
    (* ---- 0xa70..0xa76  the byte loop ---- *)
    assert (Ha1_6 : m6 !!! Regidx a1_idx = m !!! Regidx a1_idx).
    { rewrite (Hm6 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm2 a1_idx ltac:(vm_compute; discriminate)).
      exact (Hm1 a1_idx ltac:(vm_compute; discriminate)). }
    iApply (wp_ksh_memset_loop a N (nth_byte (m !!! Regidx a1_idx) 0)
              (N - 1)%nat 0%nat h9 m6 f nn
              ltac:(lia) Halo ltac:(unfold Z64; lia)
              ltac:(rewrite Ha1_6; reflexivity)
              ltac:(intros i Hi; lia)
              Ha5_6 Ha4_6
              with "Hcode Hbs Hrun").
    iIntros "Hbs" (h10 mc) "%Hmc Hrun".
    assert (Hspc : mc !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 2))).
    { rewrite (Hmc csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm6 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm5 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm4 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm3 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp2. }
    (* ---- 0xa7a  c.ldsp ra,8(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h10 mc (mword_of_int 0xa7a)
              (mword_of_int 1 : mword 6) ra_idx (uint sp0 - 8) vra nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspc Hsp16 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw8 Hrun").
    { iApply (uis_shk_a7a with "Hcode"). }
    iIntros "Hw8".
    assert (Ea7a : add_vec_int (mword_of_int 0xa7a : mword 64) 2
                   = mword_of_int 0xa7c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea7a. iIntros (h11) "Hrun".
    set (e1 := <[Regidx ra_idx := regval_into_reg vra]> mc).
    assert (Hspe1 : e1 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 2))).
    { rewrite (upd_ne mc (Regidx ra_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspc. }
    (* ---- 0xa7c  c.ldsp s0,0(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h11 e1 (mword_of_int 0xa7c)
              (mword_of_int 0 : mword 6) s0_idx (uint sp0 - 16) vs0 nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspe1 Hsp16 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw0 Hrun").
    { iApply (uis_shk_a7c with "Hcode"). }
    iIntros "Hw0".
    assert (Ea7c : add_vec_int (mword_of_int 0xa7c : mword 64) 2
                   = mword_of_int 0xa7e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea7c. iIntros (h12) "Hrun".
    set (e2 := <[Regidx s0_idx := regval_into_reg vs0]> e1).
    assert (Hspe2 : e2 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 2))).
    { rewrite (upd_ne e1 (Regidx s0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspe1. }
    (* ---- 0xa7e  c.addi sp,sp,16 -- THE POP ---- *)
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
    iApply (wp_uk_caddi_sp_up γt γd γs γfd h12 e2 (mword_of_int 0xa7e)
              (mword_of_int 16 : mword 6) 2 nn
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hw8 Hw0] Hrun").
    { iApply (uis_shk_a7e with "Hcode"). }
    { rewrite Hspe2 Hup ustack_2.
      iSplit; [ iPureIntro; exact Hal8 | ].
      iSplitL "Hw8"; [ iExists vra; iFrame | iExists vs0; iFrame ]. }
    assert (Ea7e : add_vec_int (mword_of_int 0xa7e : mword 64) 2
                   = mword_of_int 0xa80)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hspe2 Hup Ea7e.
    iIntros (h13) "Hrun".
    set (e3 := <[Regidx csp_rs1 := regval_into_reg sp0]> e2).
    assert (Hra3 : e3 !!! Regidx ra_idx = vra).
    { rewrite (upd_ne e2 (Regidx csp_rs1) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne e1 (Regidx s0_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq mc (Regidx ra_idx) (regval_into_reg vra)). }
    (* ---- 0xa80  c.jr ra ---- *)
    iApply (wp_uk_cjr γt γd γs γfd h13 e3 (mword_of_int 0xa80) ra_idx
              (ret_pc vra) (2 + nn)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra3; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_a80 with "Hcode"). }
    iIntros (h14) "Hrun".
    iApply ("Hcont" with "Hbs [] Hrun").
    iPureIntro. intros r Hr.
    assert (Hcsp2 : uint csp_rs1 = 2) by (vm_compute; reflexivity).
    assert (Hs08 : uint s0_idx = 8) by (vm_compute; reflexivity).
    destruct (Z.eq_dec (uint r) 2) as [Er | Er].
    { rewrite (ush_ridx_eq r csp_rs1 ltac:(rewrite Er; vm_compute; reflexivity)).
      rewrite Hsp.
      exact (upd_eq e2 (Regidx csp_rs1) (regval_into_reg sp0)). }
    destruct (Z.eq_dec (uint r) 8) as [E8 | E8].
    { rewrite (ush_ridx_eq r s0_idx ltac:(rewrite E8; vm_compute; reflexivity)).
      rewrite (upd_ne e2 (Regidx csp_rs1) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq e1 (Regidx s0_idx) (regval_into_reg vs0)). }
    assert (Hrsp : Regidx r <> Regidx csp_rs1)
      by (apply ush_ridx_ne; rewrite Hcsp2; exact Er).
    assert (Hrs0 : Regidx r <> Regidx s0_idx)
      by (apply ush_ridx_ne; rewrite Hs08; exact E8).
    rewrite /e3 (upd_ne e2 (Regidx csp_rs1) (Regidx r) _ Hrsp).
    rewrite /e2 (upd_ne e1 (Regidx s0_idx) (Regidx r) _ Hrs0).
    rewrite /e1 (upd_ne mc (Regidx ra_idx) (Regidx r) _
                   (ucs_ne r ra_idx Hr ltac:(vm_compute; reflexivity))).
    rewrite (Hmc r (ucs_ne r a5_idx Hr ltac:(vm_compute; reflexivity))).
    rewrite (Hm6 r (ucs_ne r a4_idx Hr ltac:(vm_compute; reflexivity))).
    rewrite (Hm5 r (ucs_ne r a2_idx Hr ltac:(vm_compute; reflexivity))).
    rewrite (Hm4 r (ucs_ne r a2_idx Hr ltac:(vm_compute; reflexivity))).
    rewrite (Hm3 r (ucs_ne r a5_idx Hr ltac:(vm_compute; reflexivity))).
    rewrite (Hm2 r Hrs0). exact (Hm1 r Hrsp).
  Qed.


  (* ===================================================================== *)
  (* gets @0xaaa -- 50 instructions, a 96-byte frame, and the READ.         *)
  (* DEPENDS ON [ush_read_leaf] (through [wp_ksh_read]).                    *)
  (*                                                                       *)
  (*   for(i = 0; i+1 < max; ){                                            *)
  (*     cc = read(0, &c, 1);                                              *)
  (*     if(cc < 1) break;                                                 *)
  (*     buf[i++] = c;                                                     *)
  (*     if(c == '\n' || c == '\r') break;                                 *)
  (*   }                                                                   *)
  (*   buf[i] = '\0';                                                      *)
  (*                                                                       *)
  (* WHAT THE CONTRACT PROMISES is exactly what main's scan needs and no    *)
  (* more: the buffer comes back OWNED, with a NUL at some index below      *)
  (* [max].  It says nothing about which bytes were read -- it cannot, and  *)
  (* it does not have to.  The kernel's window row does not tie the         *)
  (* returned count to the number of bytes it wrote, and gets stores        *)
  (* whatever is in its one-byte window either way; the walk is correct at  *)
  (* every [d <= 1] the row permits.                                       *)
  (*                                                                       *)
  (* THE NUL IS WHY [urun_x0] EXISTS.  [buf[i] = '\0'] is [sb zero,0(s8)],  *)
  (* whose stored byte is the VALUE of x0 -- about which the register file  *)
  (* alone says nothing.                                                   *)
  (*                                                                       *)
  (* c LIVES IN THE FRAME, at [s0-81] = one byte inside the word at         *)
  (* [sp0-88] -- the only slot of the twelve that is a local rather than a  *)
  (* spill.  The loop therefore carries ONE byte, not the frame: the ten    *)
  (* spilled words and the other seven bytes of that word are never touched *)
  (* by it and stay in the caller's context.                                *)
  (* ===================================================================== *)

  (* the registers gets' loop body does NOT write: sp, s0, s4..s7.  Its
     [read] call clobbers ra and a0/a1/a2/a7 as well as the loop's own
     s1/s2/s3/s8/a4/a5, so the caller reads back only these six. *)
  Definition ush_gets_keep (r : mword 5) : bool :=
    let z := uint r in
    Z.eqb z 2 || Z.eqb z 3 || Z.eqb z 4 || Z.eqb z 8 ||
    ((20 <=? z) && (z <=? 23)) || ((25 <=? z) && (z <=? 27)).

  Local Lemma ush_keep_ne (r q : mword 5) :
    ush_gets_keep r = true -> ush_gets_keep q = false -> Regidx r <> Regidx q.
  Proof.
    intros Hr Hq He.
    assert (Hrr : r = q) by (injection He; trivial).
    rewrite Hrr Hq in Hr. discriminate.
  Qed.

  Local Lemma wp_ksh_gets_loop (a : Z) (N : nat) (spz : Z) :
    forall (k i : nat) (h : CpuId) (mc : regfile) (f : nat -> bv 8)
           (bc : bv 8) (nn : nat),
    (N = i + k)%nat -> (i < N)%nat ->
    0 <= a -> a + Z.of_nat N < Z64 -> Z.of_nat N < Z31 ->
    96 <= spz -> spz < Z64 ->
    mc !!! Regidx s0_idx = mword_of_int spz ->
    mc !!! Regidx s1_idx = mword_of_int (Z.of_nat i) ->
    mc !!! Regidx s2_idx = mword_of_int (a + Z.of_nat i) ->
    mc !!! Regidx s4_idx = mword_of_int (Z.of_nat N) ->
    mc !!! Regidx s5_idx = mword_of_int 1 ->
    mc !!! Regidx s6_idx = mword_of_int (spz - 81) ->
    shk_code γt -∗
    ubytes γd a N f -∗
    ubyte γd (spz - 81) bc -∗
    urun γt γd γs γfd h mc (mword_of_int 0xad0) nn -∗
    (∀ (h' : CpuId) (mc' : regfile) (i2 : nat) (g : nat -> bv 8) (bc' : bv 8),
       ⌜ (i2 < N)%nat ⌝ -∗
       ⌜ mc' !!! Regidx s8_idx = mword_of_int (Z.of_nat i2) ⌝ -∗
       ⌜ forall r : mword 5, ush_gets_keep r = true ->
           mc' !!! Regidx r = mc !!! Regidx r ⌝ -∗
       ubytes γd a N g -∗
       ubyte γd (spz - 81) bc' -∗
       urun γt γd γs γfd h' mc' (mword_of_int 0xb00) nn -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros k. induction k as [| k IH ];
      intros i h mc f bc nn HN Hi Ha0 Ha64 HN31 Hsz0 Hsz1
             Hs0 Hs1 Hs2 Hs4 Hs5 Hs6.
    { assert (HF : False) by lia. destruct HF. }
    iIntros "#Hcode Hbs Hb Hrun Hcont".
    (* ---- 0xad0  c.mv s8,s1 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h mc (mword_of_int 0xad0) s8_idx s1_idx
              (mword_of_int (Z.of_nat i)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_ad0 with "Hcode"). }
    assert (Ead0 : add_vec_int (mword_of_int 0xad0 : mword 64) 2
                   = mword_of_int 0xad2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ead0. iIntros (h1) "Hrun".
    set (m1 := <[Regidx s8_idx
                 := regval_into_reg (mword_of_int (Z.of_nat i) : mword 64)]> mc).
    assert (P1 : forall r : mword 5, ush_gets_keep r = true ->
                   m1 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr; exact (upd_ne mc (Regidx s8_idx) (Regidx r) _
                                (ush_keep_ne r s8_idx Hr
                                   ltac:(vm_compute; reflexivity)))).
    assert (Hs1_1 : m1 !!! Regidx s1_idx = mword_of_int (Z.of_nat i)).
    { rewrite (upd_ne mc (Regidx s8_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)). exact Hs1. }
    assert (Hs8_1 : m1 !!! Regidx s8_idx = mword_of_int (Z.of_nat i))
      by exact (upd_eq mc (Regidx s8_idx)
                  (regval_into_reg (mword_of_int (Z.of_nat i) : mword 64))).
    (* ---- 0xad2  addiw s3,s1,1 ---- *)
    assert (Ei1 : (sign_extend' 64 (mword_of_int 1 : mword 12) : mword 64)
                  = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_addiw γt γd γs γfd h1 m1 (mword_of_int 0xad2)
              (mword_of_int 1 : mword 12) s1_idx s3_idx
              (mword_of_int (Z.of_nat i + 1)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_1 Ei1; symmetry;
                    exact (moi_addw (Z.of_nat i) 1 ltac:(unfold Z31 in *; lia)))
              with "[] Hrun").
    { iApply (uis_shk_ad2 with "Hcode"). }
    assert (Ead2 : add_vec_int (mword_of_int 0xad2 : mword 64) 4
                   = mword_of_int 0xad6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ead2. iIntros (h2) "Hrun".
    set (m2 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int (Z.of_nat i + 1)
                                     : mword 64)]> m1).
    assert (P2 : forall r : mword 5, ush_gets_keep r = true ->
                   m2 !!! Regidx r = m1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m1 (Regidx s3_idx) (Regidx r) _
                                (ush_keep_ne r s3_idx Hr
                                   ltac:(vm_compute; reflexivity)))).
    assert (Hs3_2 : m2 !!! Regidx s3_idx = mword_of_int (Z.of_nat i + 1))
      by exact (upd_eq m1 (Regidx s3_idx)
                  (regval_into_reg (mword_of_int (Z.of_nat i + 1) : mword 64))).
    (* ---- 0xad6  c.mv s1,s3 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h2 m2 (mword_of_int 0xad6) s1_idx s3_idx
              (mword_of_int (Z.of_nat i + 1)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_2 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_ad6 with "Hcode"). }
    assert (Ead6 : add_vec_int (mword_of_int 0xad6 : mword 64) 2
                   = mword_of_int 0xad8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ead6. iIntros (h3) "Hrun".
    set (m3 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int (Z.of_nat i + 1)
                                     : mword 64)]> m2).
    assert (P3 : forall r : mword 5, ush_gets_keep r = true ->
                   m3 !!! Regidx r = m2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m2 (Regidx s1_idx) (Regidx r) _
                                (ush_keep_ne r s1_idx Hr
                                   ltac:(vm_compute; reflexivity)))).
    assert (P13 : forall r : mword 5, ush_gets_keep r = true ->
                    m3 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr; rewrite (P3 r Hr) (P2 r Hr); exact (P1 r Hr)).
    assert (Hs3_3 : m3 !!! Regidx s3_idx = mword_of_int (Z.of_nat i + 1)).
    { rewrite (upd_ne m2 (Regidx s1_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)). exact Hs3_2. }
    assert (Hs4_3 : m3 !!! Regidx s4_idx = mword_of_int (Z.of_nat N))
      by (rewrite (P13 s4_idx ltac:(vm_compute; reflexivity)); exact Hs4).
    assert (Hs8_3 : m3 !!! Regidx s8_idx = mword_of_int (Z.of_nat i)).
    { rewrite (upd_ne m2 (Regidx s1_idx) (Regidx s8_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m1 (Regidx s3_idx) (Regidx s8_idx) _
                 ltac:(vm_compute; discriminate)). exact Hs8_1. }
    (* ---- 0xad8  bge s3,s4,0xb00 -- the ONE computed branch of the loop  *)
    assert (Htk8 : Z.geb (Z.of_nat i + 1) (Z.of_nat N)
                   = uv_btaken BGE (m3 !!! Regidx s3_idx)
                       (m3 !!! Regidx s4_idx)).
    { cbn [uv_btaken]. rewrite Hs3_3 Hs4_3.
      symmetry.
      exact (moi_ge_s (Z.of_nat i + 1) (Z.of_nat N)
               ltac:(unfold Z31, Z63 in *; lia)
               ltac:(unfold Z31, Z63 in *; lia)). }
    iApply (wp_uk_btype γt γd γs γfd h3 m3 (mword_of_int 0xad8)
              (mword_of_int 40 : mword 13) s4_idx s3_idx BGE
              (Z.geb (Z.of_nat i + 1) (Z.of_nat N)) (mword_of_int 0xb00) nn
              Htk8
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_ad8 with "Hcode"). }
    destruct (Z.geb_spec (Z.of_nat i + 1) (Z.of_nat N)) as [Hge | Hlt].
    { (* the buffer is full: leave with s8 = i *)
      iIntros (h4) "Hrun".
      iApply ("Hcont" $! h4 m3 i f bc with "[] [] [] Hbs Hb Hrun");
        iPureIntro; [ lia | exact Hs8_3 | exact P13 ]. }
    assert (Ead8 : add_vec_int (mword_of_int 0xad8 : mword 64) 4
                   = mword_of_int 0xadc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ead8. iIntros (h4) "Hrun".
    (* room for one more byte *)
    assert (Hik : (i + 1 < N)%nat) by lia.
    (* ---- 0xadc  c.mv a2,s5 ---- *)
    assert (Hs5_3 : m3 !!! Regidx s5_idx = mword_of_int 1)
      by (rewrite (P13 s5_idx ltac:(vm_compute; reflexivity)); exact Hs5).
    iApply (wp_uk_cmv γt γd γs γfd h4 m3 (mword_of_int 0xadc) a2_idx s5_idx
              (mword_of_int 1) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs5_3 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_adc with "Hcode"). }
    assert (Eadc : add_vec_int (mword_of_int 0xadc : mword 64) 2
                   = mword_of_int 0xade)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eadc. iIntros (h5) "Hrun".
    set (m4 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int 1 : mword 64)]> m3).
    assert (P4 : forall r : mword 5, ush_gets_keep r = true ->
                   m4 !!! Regidx r = m3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m3 (Regidx a2_idx) (Regidx r) _
                                (ush_keep_ne r a2_idx Hr
                                   ltac:(vm_compute; reflexivity)))).
    (* ---- 0xade  c.mv a1,s6 ---- *)
    assert (Hs6_4 : m4 !!! Regidx s6_idx = mword_of_int (spz - 81)).
    { rewrite (P4 s6_idx ltac:(vm_compute; reflexivity)).
      rewrite (P13 s6_idx ltac:(vm_compute; reflexivity)). exact Hs6. }
    iApply (wp_uk_cmv γt γd γs γfd h5 m4 (mword_of_int 0xade) a1_idx s6_idx
              (mword_of_int (spz - 81)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs6_4 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_ade with "Hcode"). }
    assert (Eade : add_vec_int (mword_of_int 0xade : mword 64) 2
                   = mword_of_int 0xae0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eade. iIntros (h6) "Hrun".
    set (m5 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int (spz - 81) : mword 64)]> m4).
    assert (P5 : forall r : mword 5, ush_gets_keep r = true ->
                   m5 !!! Regidx r = m4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m4 (Regidx a1_idx) (Regidx r) _
                                (ush_keep_ne r a1_idx Hr
                                   ltac:(vm_compute; reflexivity)))).
    (* ---- 0xae0  c.li a0,0 ---- *)
    iApply (wp_uk_cli γt γd γs γfd h6 m5 (mword_of_int 0xae0)
              (mword_of_int 0 : mword 6) a0_idx nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_ae0 with "Hcode"). }
    assert (Eae0 : add_vec_int (mword_of_int 0xae0 : mword 64) 2
                   = mword_of_int 0xae2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eae0. iIntros (h7) "Hrun".
    set (m6 := <[Regidx a0_idx
                 := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 6)
                                     : mword 64)]> m5).
    assert (P6 : forall r : mword 5, ush_gets_keep r = true ->
                   m6 !!! Regidx r = m5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m5 (Regidx a0_idx) (Regidx r) _
                                (ush_keep_ne r a0_idx Hr
                                   ltac:(vm_compute; reflexivity)))).
    (* ---- 0xae2  jal ra,0xc9e <read> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h7 m6 (mword_of_int 0xae2)
              (mword_of_int 444 : mword 21) ra_idx
              (mword_of_int ShSyms.read) (mword_of_int 0xae6) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite shp_read; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite shp_read; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_ae2 with "Hcode"). }
    iIntros (h8) "Hrun".
    set (m7 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0xae6 : mword 64)]> m6).
    assert (P7 : forall r : mword 5, ush_gets_keep r = true ->
                   m7 !!! Regidx r = m6 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m6 (Regidx ra_idx) (Regidx r) _
                                (ush_keep_ne r ra_idx Hr
                                   ltac:(vm_compute; reflexivity)))).
    assert (Hra7 : m7 !!! Regidx ra_idx = mword_of_int 0xae6)
      by exact (upd_eq m6 (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0xae6 : mword 64))).
    assert (Ha1_7 : uint (m7 !!! Regidx a1_idx) = spz - 81).
    { rewrite (upd_ne m6 (Regidx ra_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m5 (Regidx a0_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m4 (Regidx a1_idx)
                 (regval_into_reg (mword_of_int (spz - 81) : mword 64))).
      apply uint_moi. unfold Z64 in *. lia. }
    assert (Ha2_7 : uint (m7 !!! Regidx a2_idx) = Z.of_nat 1).
    { rewrite (upd_ne m6 (Regidx ra_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m5 (Regidx a0_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m4 (Regidx a1_idx) (Regidx a2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m3 (Regidx a2_idx)
                 (regval_into_reg (mword_of_int 1 : mword 64))).
      vm_compute. reflexivity. }
    (* the one-byte window, as a run *)
    iDestruct (ush_bytes_one (spz - 81) (fun _ => bc) bc eq_refl) as "Hcv".
    iAssert (ubytes γd (spz - 81) 1 (fun _ => bc)) with "[Hb]" as "Hbw".
    { iApply "Hcv". iExact "Hb". }
    iApply (wp_ksh_read h8 m7 (spz - 81) 1 (fun _ => bc) nn Ha1_7 Ha2_7
              with "Hcode Hbw Hrun").
    iIntros (h9 ret d g1) "%Hd %Hg1 Hbw Hrun".
    rewrite Hra7.
    assert (Eret : ret_pc (mword_of_int 0xae6 : mword 64) = mword_of_int 0xae6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    set (m8 := <[Regidx a0_idx := ret]>
                 (<[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m7)).
    assert (P8 : forall r : mword 5, ush_gets_keep r = true ->
                   m8 !!! Regidx r = m7 !!! Regidx r).
    { intros r Hr.
      rewrite (upd_ne _ (Regidx a0_idx) (Regidx r) _
                 (ush_keep_ne r a0_idx Hr ltac:(vm_compute; reflexivity))).
      exact (upd_ne m7 (Regidx a7_idx) (Regidx r) _
               (ush_keep_ne r a7_idx Hr ltac:(vm_compute; reflexivity))). }
    assert (P18 : forall r : mword 5, ush_gets_keep r = true ->
                    m8 !!! Regidx r = mc !!! Regidx r).
    { intros r Hr.
      rewrite (P8 r Hr) (P7 r Hr) (P6 r Hr) (P5 r Hr) (P4 r Hr).
      exact (P13 r Hr). }
    assert (Hs8_8 : m8 !!! Regidx s8_idx = mword_of_int (Z.of_nat i)).
    { rewrite (upd_ne _ (Regidx a0_idx) (Regidx s8_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m7 (Regidx a7_idx) (Regidx s8_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m6 (Regidx ra_idx) (Regidx s8_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m5 (Regidx a0_idx) (Regidx s8_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m4 (Regidx a1_idx) (Regidx s8_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m3 (Regidx a2_idx) (Regidx s8_idx) _
                 ltac:(vm_compute; discriminate)). exact Hs8_3. }
    (* ---- 0xae6  blez a0,0xb00 -- an ABSTRACT split: either arm is fine *)
    remember (uv_btaken BGE (m8 !!! Regidx x0_idx) (m8 !!! Regidx a0_idx))
      as tk6 eqn:Htk6.
    iApply (wp_uk_btype γt γd γs γfd h9 m8 (mword_of_int 0xae6)
              (mword_of_int 26 : mword 13) a0_idx x0_idx BGE tk6
              (mword_of_int 0xb00) nn
              Htk6
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_ae6 with "Hcode"). }
    iDestruct (ush_bytes_one (spz - 81) g1 (g1 0%nat) eq_refl) as "Hcw".
    iAssert (ubyte γd (spz - 81) (g1 0%nat)) with "[Hbw]" as "Hb".
    { iApply "Hcw". iExact "Hbw". }
    destruct tk6.
    { (* the read gave nothing: leave with s8 = i *)
      iIntros (h10) "Hrun".
      iApply ("Hcont" $! h10 m8 i f (g1 0%nat) with "[] [] [] Hbs Hb Hrun");
        iPureIntro; [ lia | exact Hs8_8 | exact P18 ]. }
    assert (Eae6 : add_vec_int (mword_of_int 0xae6 : mword 64) 4
                   = mword_of_int 0xaea)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eae6. iIntros (h10) "Hrun".
    (* ---- 0xaea  lbu a5,-81(s0) -- read the byte back out of the frame -- *)
    set (bz := bv_unsigned (g1 0%nat)).
    assert (Hbzr : 0 <= bz < 256).
    { unfold bz. pose proof (bv_unsigned_in_range 8 (g1 0%nat)) as Hr.
      assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
      rewrite Em8 in Hr. exact Hr. }
    assert (Hs0_8 : m8 !!! Regidx s0_idx = mword_of_int spz)
      by (rewrite (P18 s0_idx ltac:(vm_compute; reflexivity)); exact Hs0).
    iApply (wp_uk_lbu γt γd γs γfd h10 m8 (mword_of_int 0xaea)
              (mword_of_int 4015 : mword 12) s0_idx a5_idx (DfracOwn 1)
              (spz - 81) (g1 0%nat) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs0_8 (uint_moi spz ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shk_aea with "Hcode"). }
    iIntros "Hb".
    assert (Eaea : add_vec_int (mword_of_int 0xaea : mword 64) 4
                   = mword_of_int 0xaee)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eaea. iIntros (h11) "Hrun".
    set (m9 := <[Regidx a5_idx
                 := regval_into_reg (zero_extend' 64 (g1 0%nat : mword 8)
                                     : mword 64)]> m8).
    assert (P9 : forall r : mword 5, ush_gets_keep r = true ->
                   m9 !!! Regidx r = m8 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m8 (Regidx a5_idx) (Regidx r) _
                                (ush_keep_ne r a5_idx Hr
                                   ltac:(vm_compute; reflexivity)))).
    assert (Ha5_9 : m9 !!! Regidx a5_idx = mword_of_int bz).
    { rewrite (upd_eq m8 (Regidx a5_idx)
                 (regval_into_reg (zero_extend' 64 (g1 0%nat : mword 8)
                                   : mword 64))).
      exact (zext8_moi (g1 0%nat)). }
    (* ---- 0xaee  sb a5,0(s2) -- buf[i] := c ---- *)
    assert (Hs2_9 : m9 !!! Regidx s2_idx = mword_of_int (a + Z.of_nat i)).
    { rewrite (upd_ne m8 (Regidx a5_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx a0_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m7 (Regidx a7_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m6 (Regidx ra_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m5 (Regidx a0_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m4 (Regidx a1_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m3 (Regidx a2_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m2 (Regidx s1_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m1 (Regidx s3_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mc (Regidx s8_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)). exact Hs2. }
    iDestruct (ush_bytes_upd a N i f ltac:(lia) with "Hbs") as "[Hbi Hcl]".
    iApply (wp_uk_sb γt γd γs γfd h11 m9 (mword_of_int 0xaee)
              (mword_of_int 0 : mword 12) s2_idx a5_idx
              (a + Z.of_nat i) (f i) nn
              ltac:(rewrite Hs2_9 (uint_moi (a + Z.of_nat i)
                                     ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              with "[] Hbi Hrun").
    { iApply (uis_shk_aee with "Hcode"). }
    iIntros "Hbi".
    iDestruct ("Hcl" $! (nth_byte (m9 !!! Regidx a5_idx) 0) with "Hbi")
      as "Hbs".
    assert (Eaee : add_vec_int (mword_of_int 0xaee : mword 64) 4
                   = mword_of_int 0xaf2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eaee. iIntros (h12) "Hrun".
    (* ---- 0xaf2  c.addi s2,s2,1 ---- *)
    assert (E1c : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                  = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi γt γd γs γfd h12 m9 (mword_of_int 0xaf2)
              (mword_of_int 1 : mword 6) s2_idx
              (mword_of_int (a + Z.of_nat (i + 1))) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2_9 E1c moi_add;
                    replace (a + Z.of_nat (i + 1)) with (a + Z.of_nat i + 1)
                      by lia; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_af2 with "Hcode"). }
    assert (Eaf2 : add_vec_int (mword_of_int 0xaf2 : mword 64) 2
                   = mword_of_int 0xaf4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eaf2. iIntros (h13) "Hrun".
    set (mA := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int (a + Z.of_nat (i + 1))
                                     : mword 64)]> m9).
    assert (PA : forall r : mword 5, ush_gets_keep r = true ->
                   mA !!! Regidx r = m9 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m9 (Regidx s2_idx) (Regidx r) _
                                (ush_keep_ne r s2_idx Hr
                                   ltac:(vm_compute; reflexivity)))).
    assert (Ha5_A : mA !!! Regidx a5_idx = mword_of_int bz).
    { rewrite (upd_ne m9 (Regidx s2_idx) (Regidx a5_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha5_9. }
    assert (Hs2_A : mA !!! Regidx s2_idx
                    = mword_of_int (a + Z.of_nat (i + 1)))
      by exact (upd_eq m9 (Regidx s2_idx)
                  (regval_into_reg (mword_of_int (a + Z.of_nat (i + 1))
                                    : mword 64))).
    (* ---- 0xaf4  addi a4,a5,-10 ---- *)
    iApply (wp_uk_addi γt γd γs γfd h13 mA (mword_of_int 0xaf4)
              (mword_of_int 4086 : mword 12) a5_idx a4_idx
              (mword_of_int (bz - 10)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_A;
                    exact (ush_addi_sub bz 10 (mword_of_int 4086 : mword 12)
                             ltac:(unfold Z64; lia)
                             ltac:(vm_compute; reflexivity)))
              with "[] Hrun").
    { iApply (uis_shk_af4 with "Hcode"). }
    assert (Eaf4 : add_vec_int (mword_of_int 0xaf4 : mword 64) 4
                   = mword_of_int 0xaf8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eaf4. iIntros (h14) "Hrun".
    set (mB := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int (bz - 10) : mword 64)]> mA).
    assert (PB : forall r : mword 5, ush_gets_keep r = true ->
                   mB !!! Regidx r = mA !!! Regidx r)
      by (intros r Hr; exact (upd_ne mA (Regidx a4_idx) (Regidx r) _
                                (ush_keep_ne r a4_idx Hr
                                   ltac:(vm_compute; reflexivity)))).
    assert (Hs3_B : mB !!! Regidx s3_idx = mword_of_int (Z.of_nat i + 1)).
    { rewrite (upd_ne mA (Regidx a4_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m9 (Regidx s2_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m8 (Regidx a5_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx a0_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m7 (Regidx a7_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m6 (Regidx ra_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m5 (Regidx a0_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m4 (Regidx a1_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m3 (Regidx a2_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)). exact Hs3_3. }
    (* ---- 0xaf8  c.beqz a4,0xafe -- ABSTRACT: '\n' ends the line ---- *)
    remember (eq_vec (mB !!! Regidx a4_idx) zero_reg) as tk8 eqn:Htk8e.
    iApply (wp_uk_cbeqz γt γd γs γfd h14 mB (mword_of_int 0xaf8)
              (mword_of_int 3 : mword 8) (mword_of_int 6 : mword 3) a4_idx
              tk8 (mword_of_int 0xafe) nn
              ltac:(vm_compute; reflexivity) Htk8e
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_af8 with "Hcode"). }
    (* the two arms differ only in whether 0xafa/0xafc run first; both end
       at 0xafe with s8 := s3 = i+1, or go round again *)
    destruct tk8.
    { (* '\n': straight to 0xafe *)
      iIntros (h15) "Hrun".
      iApply (wp_uk_cmv γt γd γs γfd h15 mB (mword_of_int 0xafe) s8_idx s3_idx
                (mword_of_int (Z.of_nat i + 1)) nn
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs3_B moi_add_zero_l; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_afe with "Hcode"). }
      assert (Eafe : add_vec_int (mword_of_int 0xafe : mword 64) 2
                     = mword_of_int 0xb00)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Eafe. iIntros (h16) "Hrun".
      iApply ("Hcont" $! h16 _ (i + 1)%nat
                (ush_set f i (nth_byte (m9 !!! Regidx a5_idx) 0))
                (g1 0%nat) with "[] [] [] Hbs Hb Hrun").
      { iPureIntro. lia. }
      { iPureIntro.
        replace (Z.of_nat (i + 1)) with (Z.of_nat i + 1) by lia.
        exact (upd_eq mB (Regidx s8_idx)
                 (regval_into_reg (mword_of_int (Z.of_nat i + 1)
                                   : mword 64))). }
      { iPureIntro. intros r Hr.
        rewrite (upd_ne mB (Regidx s8_idx) (Regidx r) _
                   (ush_keep_ne r s8_idx Hr ltac:(vm_compute; reflexivity))).
        rewrite (PB r Hr) (PA r Hr) (P9 r Hr). exact (P18 r Hr). } }
    assert (Eaf8 : add_vec_int (mword_of_int 0xaf8 : mword 64) 2
                   = mword_of_int 0xafa)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eaf8. iIntros (h15) "Hrun".
    (* ---- 0xafa  c.addi a5,a5,-13 ---- *)
    assert (E13 : (sign_extend' 64 (mword_of_int 51 : mword 6) : mword 64)
                  = mword_of_int (-13))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi γt γd γs γfd h15 mB (mword_of_int 0xafa)
              (mword_of_int 51 : mword 6) a5_idx
              (mword_of_int (bz - 13)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(assert (Ha5B : mB !!! Regidx a5_idx = mword_of_int bz)
                      by (rewrite (upd_ne mA (Regidx a4_idx) (Regidx a5_idx) _
                                     ltac:(vm_compute; discriminate));
                          exact Ha5_A);
                    rewrite Ha5B E13 moi_add;
                    replace (bz - 13) with (bz + -13) by lia; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_afa with "Hcode"). }
    assert (Eafa : add_vec_int (mword_of_int 0xafa : mword 64) 2
                   = mword_of_int 0xafc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eafa. iIntros (h16) "Hrun".
    set (mC := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int (bz - 13) : mword 64)]> mB).
    assert (PC : forall r : mword 5, ush_gets_keep r = true ->
                   mC !!! Regidx r = mB !!! Regidx r)
      by (intros r Hr; exact (upd_ne mB (Regidx a5_idx) (Regidx r) _
                                (ush_keep_ne r a5_idx Hr
                                   ltac:(vm_compute; reflexivity)))).
    assert (Hs3_C : mC !!! Regidx s3_idx = mword_of_int (Z.of_nat i + 1)).
    { rewrite (upd_ne mB (Regidx a5_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)). exact Hs3_B. }
    (* ---- 0xafc  c.bnez a5,0xad0 -- ABSTRACT: '\r' ends the line too --- *)
    remember (neq_vec (mC !!! Regidx a5_idx) zero_reg) as tkc eqn:Htkc.
    iApply (wp_uk_cbnez γt γd γs γfd h16 mC (mword_of_int 0xafc)
              (mword_of_int 234 : mword 8) (mword_of_int 7 : mword 3) a5_idx
              tkc (mword_of_int 0xad0) nn
              ltac:(vm_compute; reflexivity) Htkc
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_afc with "Hcode"). }
    assert (PCall : forall r : mword 5, ush_gets_keep r = true ->
                      mC !!! Regidx r = mc !!! Regidx r).
    { intros r Hr.
      rewrite (PC r Hr) (PB r Hr) (PA r Hr) (P9 r Hr). exact (P18 r Hr). }
    destruct tkc.
    { (* not a '\r': go round again at i+1 *)
      iIntros (h17) "Hrun".
      iApply (IH (i + 1)%nat h17 mC
                (ush_set f i (nth_byte (m9 !!! Regidx a5_idx) 0)) (g1 0%nat) nn
                ltac:(lia) ltac:(lia) Ha0 Ha64 HN31 Hsz0 Hsz1
                ltac:(rewrite (PCall s0_idx ltac:(vm_compute; reflexivity));
                      exact Hs0)
                ltac:(rewrite (upd_ne mB (Regidx a5_idx) (Regidx s1_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne mA (Regidx a4_idx) (Regidx s1_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne m9 (Regidx s2_idx) (Regidx s1_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne m8 (Regidx a5_idx) (Regidx s1_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne _ (Regidx a0_idx) (Regidx s1_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne m7 (Regidx a7_idx) (Regidx s1_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne m6 (Regidx ra_idx) (Regidx s1_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne m5 (Regidx a0_idx) (Regidx s1_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne m4 (Regidx a1_idx) (Regidx s1_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne m3 (Regidx a2_idx) (Regidx s1_idx) _
                                 ltac:(vm_compute; discriminate));
                      replace (Z.of_nat (i + 1)) with (Z.of_nat i + 1) by lia;
                      exact (upd_eq m2 (Regidx s1_idx)
                               (regval_into_reg
                                  (mword_of_int (Z.of_nat i + 1) : mword 64))))
                ltac:(rewrite (upd_ne mB (Regidx a5_idx) (Regidx s2_idx) _
                                 ltac:(vm_compute; discriminate));
                      rewrite (upd_ne mA (Regidx a4_idx) (Regidx s2_idx) _
                                 ltac:(vm_compute; discriminate));
                      exact Hs2_A)
                ltac:(rewrite (PCall s4_idx ltac:(vm_compute; reflexivity));
                      exact Hs4)
                ltac:(rewrite (PCall s5_idx ltac:(vm_compute; reflexivity));
                      exact Hs5)
                ltac:(rewrite (PCall s6_idx ltac:(vm_compute; reflexivity));
                      exact Hs6)
                with "Hcode Hbs Hb Hrun").
      iIntros (h18 mc'' i2 g2 bc2) "%Hi2 %Hs8'' %Hp'' Hbs Hb Hrun".
      iApply ("Hcont" $! h18 mc'' i2 g2 bc2 with "[] [] [] Hbs Hb Hrun");
        iPureIntro; [ exact Hi2 | exact Hs8'' | ].
      intros r Hr. rewrite (Hp'' r Hr). exact (PCall r Hr). }
    (* a '\r': fall into 0xafe *)
    assert (Eafc : add_vec_int (mword_of_int 0xafc : mword 64) 2
                   = mword_of_int 0xafe)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eafc. iIntros (h17) "Hrun".
    iApply (wp_uk_cmv γt γd γs γfd h17 mC (mword_of_int 0xafe) s8_idx s3_idx
              (mword_of_int (Z.of_nat i + 1)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_C moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_afe with "Hcode"). }
    assert (Eafe : add_vec_int (mword_of_int 0xafe : mword 64) 2
                   = mword_of_int 0xb00)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eafe. iIntros (h18) "Hrun".
    iApply ("Hcont" $! h18 _ (i + 1)%nat
              (ush_set f i (nth_byte (m9 !!! Regidx a5_idx) 0))
              (g1 0%nat) with "[] [] [] Hbs Hb Hrun").
    { iPureIntro. lia. }
    { iPureIntro.
      replace (Z.of_nat (i + 1)) with (Z.of_nat i + 1) by lia.
      exact (upd_eq mC (Regidx s8_idx)
               (regval_into_reg (mword_of_int (Z.of_nat i + 1) : mword 64))). }
    { iPureIntro. intros r Hr.
      rewrite (upd_ne mC (Regidx s8_idx) (Regidx r) _
                 (ush_keep_ne r s8_idx Hr ltac:(vm_compute; reflexivity))).
      exact (PCall r Hr). }
  Qed.


  (* the twelve-word frame, opened and closed DIRECTIONALLY.  A [⊣⊢] split
     used under [rewrite] inside a proofmode goal fires on the whole
     [envs_entails], context included; UserHeap.v's own header records what
     that cost at four words.  Here the goal is two lines long. *)
  Local Lemma ush_stack_12_open (sp : mword 64) :
    ustack γd sp 12 -∗
      ⌜ uint sp mod 8 = 0 ⌝ ∗
      (∃ w : mword 64, uword γd (uint sp - 8) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 16) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 24) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 32) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 40) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 48) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 56) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 64) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 72) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 80) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 88) w) ∗
      (∃ w : mword 64, uword γd (uint sp - 96) w).
  Proof. rewrite ustack_12. iIntros "$". Qed.

  Local Lemma ush_stack_12_close (sp : mword 64) :
    ⌜ uint sp mod 8 = 0 ⌝ -∗
    (∃ w : mword 64, uword γd (uint sp - 8) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 16) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 24) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 32) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 40) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 48) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 56) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 64) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 72) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 80) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 88) w) -∗
    (∃ w : mword 64, uword γd (uint sp - 96) w) -∗
    ustack γd sp 12.
  Proof.
    rewrite ustack_12.
    iIntros "%H H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12".
    iSplit; [ iPureIntro; exact H | ]. iFrame.
  Qed.

  (* the callee-saved set, as an arithmetic disjunction *)
  Local Lemma ucs_cases (r : mword 5) :
    ucallee_saved_idx r = true ->
    uint r = 2 \/ uint r = 3 \/ uint r = 4 \/ uint r = 8 \/ uint r = 9 \/
    (18 <= uint r <= 27).
  Proof.
    unfold ucallee_saved_idx. intro H.
    repeat (apply orb_prop in H as [H | H]).
    all: try (apply Z.eqb_eq in H; lia).
    apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
  Qed.

  Local Lemma ush_r_ne (r : mword 5) (z : Z) (q : mword 5) :
    uint q = z -> uint r <> z -> Regidx r <> Regidx q.
  Proof. intros Hq Hr. apply ush_ridx_ne. rewrite Hq. exact Hr. Qed.

  (* ---- gets, the whole function --------------------------------------- *)
  (* DEPENDS ON [ush_read_leaf].                                            *)
  Lemma wp_ksh_gets (h : CpuId) (m : regfile) (a : Z) (N : nat)
      (f : nat -> bv 8) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int a ->
    m !!! Regidx a1_idx = mword_of_int (Z.of_nat N) ->
    (0 < N)%nat -> Z.of_nat N < Z31 ->
    shk_code γt -∗
    ubytes γd a N f -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.gets) (12 + nn) -∗
    ((∃ (g : nat -> bv 8) (i2 : nat),
        ⌜ (i2 < N)%nat /\ g i2 = ubyte0 ⌝ ∗ ubytes γd a N g) -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (12 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Ha1 HN0 HN31. iIntros "#Hcode Hbs Hrun Hcont".
    rewrite shp_gets.
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    iDestruct (urun_ubytes_bnd h m _ (12 + nn) (DfracOwn 1) a N f ltac:(lia)
                 with "Hrun Hbs") as %[Halo Hahi].
    change (2 ^ 38) with 274877906944 in Hahi.
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    set (spz := uint sp0).
    assert (Hspm : (mword_of_int spz : mword 64) = sp0)
      by (unfold spz; rewrite uint_unsigned; exact (moi_of_unsigned sp0)).
    assert (Hlo : 96 <= spz) by (unfold spz; lia).
    assert (Hhi : spz < Z64).
    { unfold spz. rewrite uint_unsigned.
      pose proof (bv_unsigned_in_range 64 sp0) as Hr. rewrite Zmod64 in Hr.
      destruct Hr as [_ Hr2]. exact Hr2. }
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                   = bv_unsigned sp0 - 96).
    { replace (- (8 * Z.of_nat 12)) with (-96) by lia.
      exact (uv_avi_neg sp0 96 ltac:(lia) ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp96 : uint (add_vec_int sp0 (- (8 * Z.of_nat 12))) = spz - 96)
      by (unfold spz; rewrite !uint_unsigned; exact Hbsp).
    assert (Ho2 : uoff_sdsp (mword_of_int 2 : mword 6) = 16)
      by (vm_compute; reflexivity).
    assert (Ho3 : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
      by (vm_compute; reflexivity).
    assert (Ho4 : uoff_sdsp (mword_of_int 4 : mword 6) = 32)
      by (vm_compute; reflexivity).
    assert (Ho5 : uoff_sdsp (mword_of_int 5 : mword 6) = 40)
      by (vm_compute; reflexivity).
    assert (Ho6 : uoff_sdsp (mword_of_int 6 : mword 6) = 48)
      by (vm_compute; reflexivity).
    assert (Ho7 : uoff_sdsp (mword_of_int 7 : mword 6) = 56)
      by (vm_compute; reflexivity).
    assert (Ho8 : uoff_sdsp (mword_of_int 8 : mword 6) = 64)
      by (vm_compute; reflexivity).
    assert (Ho9 : uoff_sdsp (mword_of_int 9 : mword 6) = 72)
      by (vm_compute; reflexivity).
    assert (Ho10 : uoff_sdsp (mword_of_int 10 : mword 6) = 80)
      by (vm_compute; reflexivity).
    assert (Ho11 : uoff_sdsp (mword_of_int 11 : mword 6) = 88)
      by (vm_compute; reflexivity).
    (* ---- 0xaaa  c.addi16sp sp,sp,-96 -- THE PUSH ---- *)
    iApply (wp_uk_caddi16sp_dn γt γd γs γfd h m (mword_of_int 0xaaa)
              (mword_of_int 58 : mword 6) 12 nn
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_aaa with "Hcode"). }
    assert (Eaaa : add_vec_int (mword_of_int 0xaaa : mword 64) 2
                   = mword_of_int 0xaac)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp Eaaa.
    iIntros "Hfr" (h1) "Hrun".
    iDestruct (ush_stack_12_open with "Hfr")
      as "(_ & [%v1 Hw1] & [%v2 Hw2] & [%v3 Hw3] & [%v4 Hw4] & [%v5 Hw5]
           & [%v6 Hw6] & [%v7 Hw7] & [%v8 Hw8] & [%v9 Hw9] & [%v10 Hw10]
           & [%v11 Hw11] & [%v12 Hw12])".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 12)))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12)))
      by exact (upd_eq m (Regidx csp_rs1)
                  (regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 12))))).
    assert (Hm1 : forall r : mword 5, Regidx r <> Regidx csp_rs1 ->
                    m1 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr; exact (upd_ne m (Regidx csp_rs1) (Regidx r) _ Hr)).
    (* ---- 0xaac..0xabe  the ten spills ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd h1 m1 (mword_of_int 0xaac)
              (mword_of_int 11 : mword 6) ra_idx (spz - 8) v1 nn
              ltac:(rewrite Hsp1 Hsp96 Ho11; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw1 Hrun").
    { iApply (uis_shk_aac with "Hcode"). }
    iIntros "Hw1". rewrite (Hm1 ra_idx ltac:(vm_compute; discriminate)).
    assert (Eg1 : add_vec_int (mword_of_int 0xaac : mword 64) 2
                 = mword_of_int 0xaae) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg1. clear Eg1.
    iIntros (h2) "Hrun".
    iApply (wp_uk_csdsp γt γd γs γfd h2 m1 (mword_of_int 0xaae)
              (mword_of_int 10 : mword 6) s0_idx (spz - 16) v2 nn
              ltac:(rewrite Hsp1 Hsp96 Ho10; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw2 Hrun").
    { iApply (uis_shk_aae with "Hcode"). }
    iIntros "Hw2". rewrite (Hm1 s0_idx ltac:(vm_compute; discriminate)).
    assert (Eg2 : add_vec_int (mword_of_int 0xaae : mword 64) 2
                 = mword_of_int 0xab0) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg2. clear Eg2.
    iIntros (h3) "Hrun".
    iApply (wp_uk_csdsp γt γd γs γfd h3 m1 (mword_of_int 0xab0)
              (mword_of_int 9 : mword 6) s1_idx (spz - 24) v3 nn
              ltac:(rewrite Hsp1 Hsp96 Ho9; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw3 Hrun").
    { iApply (uis_shk_ab0 with "Hcode"). }
    iIntros "Hw3". rewrite (Hm1 s1_idx ltac:(vm_compute; discriminate)).
    assert (Eg3 : add_vec_int (mword_of_int 0xab0 : mword 64) 2
                 = mword_of_int 0xab2) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg3. clear Eg3.
    iIntros (h4) "Hrun".
    iApply (wp_uk_csdsp γt γd γs γfd h4 m1 (mword_of_int 0xab2)
              (mword_of_int 8 : mword 6) s2_idx (spz - 32) v4 nn
              ltac:(rewrite Hsp1 Hsp96 Ho8; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw4 Hrun").
    { iApply (uis_shk_ab2 with "Hcode"). }
    iIntros "Hw4". rewrite (Hm1 s2_idx ltac:(vm_compute; discriminate)).
    assert (Eg4 : add_vec_int (mword_of_int 0xab2 : mword 64) 2
                 = mword_of_int 0xab4) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg4. clear Eg4.
    iIntros (h5) "Hrun".
    iApply (wp_uk_csdsp γt γd γs γfd h5 m1 (mword_of_int 0xab4)
              (mword_of_int 7 : mword 6) s3_idx (spz - 40) v5 nn
              ltac:(rewrite Hsp1 Hsp96 Ho7; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw5 Hrun").
    { iApply (uis_shk_ab4 with "Hcode"). }
    iIntros "Hw5". rewrite (Hm1 s3_idx ltac:(vm_compute; discriminate)).
    assert (Eg5 : add_vec_int (mword_of_int 0xab4 : mword 64) 2
                 = mword_of_int 0xab6) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg5. clear Eg5.
    iIntros (h6) "Hrun".
    iApply (wp_uk_csdsp γt γd γs γfd h6 m1 (mword_of_int 0xab6)
              (mword_of_int 6 : mword 6) s4_idx (spz - 48) v6 nn
              ltac:(rewrite Hsp1 Hsp96 Ho6; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw6 Hrun").
    { iApply (uis_shk_ab6 with "Hcode"). }
    iIntros "Hw6". rewrite (Hm1 s4_idx ltac:(vm_compute; discriminate)).
    assert (Eg6 : add_vec_int (mword_of_int 0xab6 : mword 64) 2
                 = mword_of_int 0xab8) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg6. clear Eg6.
    iIntros (h7) "Hrun".
    iApply (wp_uk_csdsp γt γd γs γfd h7 m1 (mword_of_int 0xab8)
              (mword_of_int 5 : mword 6) s5_idx (spz - 56) v7 nn
              ltac:(rewrite Hsp1 Hsp96 Ho5; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw7 Hrun").
    { iApply (uis_shk_ab8 with "Hcode"). }
    iIntros "Hw7". rewrite (Hm1 s5_idx ltac:(vm_compute; discriminate)).
    assert (Eg7 : add_vec_int (mword_of_int 0xab8 : mword 64) 2
                 = mword_of_int 0xaba) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg7. clear Eg7.
    iIntros (h8) "Hrun".
    iApply (wp_uk_csdsp γt γd γs γfd h8 m1 (mword_of_int 0xaba)
              (mword_of_int 4 : mword 6) s6_idx (spz - 64) v8 nn
              ltac:(rewrite Hsp1 Hsp96 Ho4; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw8 Hrun").
    { iApply (uis_shk_aba with "Hcode"). }
    iIntros "Hw8". rewrite (Hm1 s6_idx ltac:(vm_compute; discriminate)).
    assert (Eg8 : add_vec_int (mword_of_int 0xaba : mword 64) 2
                 = mword_of_int 0xabc) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg8. clear Eg8.
    iIntros (h9) "Hrun".
    iApply (wp_uk_csdsp γt γd γs γfd h9 m1 (mword_of_int 0xabc)
              (mword_of_int 3 : mword 6) s7_idx (spz - 72) v9 nn
              ltac:(rewrite Hsp1 Hsp96 Ho3; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw9 Hrun").
    { iApply (uis_shk_abc with "Hcode"). }
    iIntros "Hw9". rewrite (Hm1 s7_idx ltac:(vm_compute; discriminate)).
    assert (Eg9 : add_vec_int (mword_of_int 0xabc : mword 64) 2
                 = mword_of_int 0xabe) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg9. clear Eg9.
    iIntros (h10) "Hrun".
    iApply (wp_uk_csdsp γt γd γs γfd h10 m1 (mword_of_int 0xabe)
              (mword_of_int 2 : mword 6) s8_idx (spz - 80) v10 nn
              ltac:(rewrite Hsp1 Hsp96 Ho2; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw10 Hrun").
    { iApply (uis_shk_abe with "Hcode"). }
    iIntros "Hw10". rewrite (Hm1 s8_idx ltac:(vm_compute; discriminate)).
    assert (Eg10 : add_vec_int (mword_of_int 0xabe : mword 64) 2
                 = mword_of_int 0xac0) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg10. clear Eg10.
    iIntros (h11) "Hrun".
    (* ---- 0xac0  c.addi4spn s0,sp,96 -- the frame pointer IS sp0 ---- *)
    assert (Hci : (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8))
                   : mword 64) = mword_of_int (8 * Z.of_nat 12))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hbu : bv_unsigned sp0 = spz)
      by (unfold spz; rewrite uint_unsigned; reflexivity).
    assert (Hlt12 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                    + 8 * Z.of_nat 12 < Z64)
      by (rewrite Hbsp Hbu; lia).
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                    (8 * Z.of_nat 12) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                 (8 * Z.of_nat 12) ltac:(lia) Hlt12).
      rewrite Hbsp. lia. }
    iApply (wp_uk_caddi4spn γt γd γs γfd h11 m1 (mword_of_int 0xac0)
              (mword_of_int 0 : mword 3) (mword_of_int 24 : mword 8) s0_idx
              sp0 nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hsp1 Hci; unfold add_vec_int in Hup; exact (eq_sym Hup))
              with "[] Hrun").
    { iApply (uis_shk_ac0 with "Hcode"). }
    assert (Eg11 : add_vec_int (mword_of_int 0xac0 : mword 64) 2
                 = mword_of_int 0xac2) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg11. clear Eg11.
    iIntros (h12) "Hrun".
    set (m2 := <[Regidx s0_idx := regval_into_reg sp0]> m1).
    assert (Ha0_2 : m2 !!! Regidx a0_idx = mword_of_int a).
    { rewrite (upd_ne m1 (Regidx s0_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    assert (Ha1_2 : m2 !!! Regidx a1_idx = mword_of_int (Z.of_nat N)).
    { rewrite (upd_ne m1 (Regidx s0_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (Hm1 a1_idx ltac:(vm_compute; discriminate)). exact Ha1. }
    (* ---- 0xac2  c.mv s7,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h12 m2 (mword_of_int 0xac2) s7_idx a0_idx
              (mword_of_int a) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_2 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_ac2 with "Hcode"). }
    assert (Eg12 : add_vec_int (mword_of_int 0xac2 : mword 64) 2
                 = mword_of_int 0xac4) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg12. clear Eg12.
    iIntros (h13) "Hrun".
    set (m3 := <[Regidx s7_idx
                 := regval_into_reg (mword_of_int a : mword 64)]> m2).
    assert (Ha1_3 : m3 !!! Regidx a1_idx = mword_of_int (Z.of_nat N)).
    { rewrite (upd_ne m2 (Regidx s7_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha1_2. }
    (* ---- 0xac4  c.mv s4,a1 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h13 m3 (mword_of_int 0xac4) s4_idx a1_idx
              (mword_of_int (Z.of_nat N)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha1_3 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_ac4 with "Hcode"). }
    assert (Eg13 : add_vec_int (mword_of_int 0xac4 : mword 64) 2
                 = mword_of_int 0xac6) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg13. clear Eg13.
    iIntros (h14) "Hrun".
    set (m4 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int (Z.of_nat N)
                                     : mword 64)]> m3).
    assert (Ha0_4 : m4 !!! Regidx a0_idx = mword_of_int a).
    { rewrite (upd_ne m3 (Regidx s4_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m2 (Regidx s7_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha0_2. }
    (* ---- 0xac6  c.mv s2,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h14 m4 (mword_of_int 0xac6) s2_idx a0_idx
              (mword_of_int a) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_4 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_ac6 with "Hcode"). }
    assert (Eg14 : add_vec_int (mword_of_int 0xac6 : mword 64) 2
                 = mword_of_int 0xac8) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg14. clear Eg14.
    iIntros (h15) "Hrun".
    set (m5 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int a : mword 64)]> m4).
    (* ---- 0xac8  c.li s1,0 ---- *)
    iApply (wp_uk_cli γt γd γs γfd h15 m5 (mword_of_int 0xac8)
              (mword_of_int 0 : mword 6) s1_idx nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_ac8 with "Hcode"). }
    assert (Eg15 : <[Regidx s1_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 6)
                                       : mword 64)]> m5
                 = <[Regidx s1_idx := regval_into_reg
                                        (mword_of_int 0 : mword 64)]> m5) by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite Eg15. clear Eg15.
    assert (Eg16 : add_vec_int (mword_of_int 0xac8 : mword 64) 2
                 = mword_of_int 0xaca) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg16. clear Eg16.
    iIntros (h16) "Hrun".
    set (m6 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int 0 : mword 64)]> m5).
    assert (Hs0_6 : m6 !!! Regidx s0_idx = mword_of_int spz).
    { rewrite Hspm.
      rewrite (upd_ne m5 (Regidx s1_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m4 (Regidx s2_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m3 (Regidx s4_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m2 (Regidx s7_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq m1 (Regidx s0_idx) (regval_into_reg sp0)). }
    (* ---- 0xaca  addi s6,s0,-81 -- &c, one byte inside the frame ---- *)
    assert (Hoff81 : uoff_i12 (mword_of_int 4015 : mword 12) = -81)
      by (vm_compute; reflexivity).
    iApply (wp_uk_addi γt γd γs γfd h16 m6 (mword_of_int 0xaca)
              (mword_of_int 4015 : mword 12) s0_idx s6_idx
              (mword_of_int (spz - 81)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs0_6;
                    exact (umoi_add_i12 (mword_of_int spz)
                             (mword_of_int 4015 : mword 12) (spz - 81)
                             ltac:(rewrite (uint_moi spz ltac:(lia)) Hoff81;
                                   lia)))
              with "[] Hrun").
    { iApply (uis_shk_aca with "Hcode"). }
    assert (Eg17 : add_vec_int (mword_of_int 0xaca : mword 64) 4
                 = mword_of_int 0xace) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg17. clear Eg17.
    iIntros (h17) "Hrun".
    set (m7 := <[Regidx s6_idx
                 := regval_into_reg (mword_of_int (spz - 81)
                                     : mword 64)]> m6).
    (* ---- 0xace  c.li s5,1 ---- *)
    iApply (wp_uk_cli γt γd γs γfd h17 m7 (mword_of_int 0xace)
              (mword_of_int 1 : mword 6) s5_idx nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_ace with "Hcode"). }
    assert (Eg18 : <[Regidx s5_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 1 : mword 6)
                                       : mword 64)]> m7
                 = <[Regidx s5_idx := regval_into_reg
                                        (mword_of_int 1 : mword 64)]> m7) by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite Eg18. clear Eg18.
    assert (Eg19 : add_vec_int (mword_of_int 0xace : mword 64) 2
                 = mword_of_int 0xad0) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg19. clear Eg19.
    iIntros (h18) "Hrun".
    set (m8 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int 1 : mword 64)]> m7).
    (* ---- the one byte of the frame the loop actually uses ---- *)
    iDestruct (ush_bytes_upd (spz - 88) 8 7 (nth_byte v11) ltac:(lia)
                 with "Hw11") as "[Hbc Hclc]".
    assert (Eg20 : spz - 88 + Z.of_nat 7 = spz - 81) by lia.
    rewrite Eg20. clear Eg20.
    (* ---- 0xad0..0xafe  the loop ---- *)
    iApply (wp_ksh_gets_loop a N spz N 0%nat h18 m8 f (nth_byte v11 7) nn
              ltac:(lia) ltac:(lia) Halo ltac:(unfold Z64; lia) HN31
              ltac:(lia) Hhi
              ltac:(rewrite (upd_ne m7 (Regidx s5_idx) (Regidx s0_idx) _
                               ltac:(vm_compute; discriminate));
                    rewrite (upd_ne m6 (Regidx s6_idx) (Regidx s0_idx) _
                               ltac:(vm_compute; discriminate));
                    exact Hs0_6)
              ltac:(replace (Z.of_nat 0) with 0 by lia;
                    rewrite (upd_ne m7 (Regidx s5_idx) (Regidx s1_idx) _
                               ltac:(vm_compute; discriminate));
                    rewrite (upd_ne m6 (Regidx s6_idx) (Regidx s1_idx) _
                               ltac:(vm_compute; discriminate));
                    exact (upd_eq m5 (Regidx s1_idx)
                             (regval_into_reg (mword_of_int 0 : mword 64))))
              ltac:(replace (a + Z.of_nat 0) with a by lia;
                    rewrite (upd_ne m7 (Regidx s5_idx) (Regidx s2_idx) _
                               ltac:(vm_compute; discriminate));
                    rewrite (upd_ne m6 (Regidx s6_idx) (Regidx s2_idx) _
                               ltac:(vm_compute; discriminate));
                    rewrite (upd_ne m5 (Regidx s1_idx) (Regidx s2_idx) _
                               ltac:(vm_compute; discriminate));
                    exact (upd_eq m4 (Regidx s2_idx)
                             (regval_into_reg (mword_of_int a : mword 64))))
              ltac:(rewrite (upd_ne m7 (Regidx s5_idx) (Regidx s4_idx) _
                               ltac:(vm_compute; discriminate));
                    rewrite (upd_ne m6 (Regidx s6_idx) (Regidx s4_idx) _
                               ltac:(vm_compute; discriminate));
                    rewrite (upd_ne m5 (Regidx s1_idx) (Regidx s4_idx) _
                               ltac:(vm_compute; discriminate));
                    rewrite (upd_ne m4 (Regidx s2_idx) (Regidx s4_idx) _
                               ltac:(vm_compute; discriminate));
                    exact (upd_eq m3 (Regidx s4_idx)
                             (regval_into_reg (mword_of_int (Z.of_nat N)
                                               : mword 64))))
              ltac:(exact (upd_eq m7 (Regidx s5_idx)
                             (regval_into_reg (mword_of_int 1 : mword 64))))
              ltac:(rewrite (upd_ne m7 (Regidx s5_idx) (Regidx s6_idx) _
                               ltac:(vm_compute; discriminate));
                    exact (upd_eq m6 (Regidx s6_idx)
                             (regval_into_reg (mword_of_int (spz - 81)
                                               : mword 64))))
              with "Hcode Hbs Hbc Hrun").
    iIntros (h19 mc i2 g bc2) "%Hi2 %Hs8c %Hpk Hbs Hbc Hrun".
    iDestruct ("Hclc" $! bc2 with "Hbc") as "Hw11".
    (* ---- 0xb00  c.add s8,s8,s7 ---- *)
    assert (Hs7c : mc !!! Regidx s7_idx = mword_of_int a).
    { rewrite (Hpk s7_idx ltac:(vm_compute; reflexivity)).
      rewrite (upd_ne m7 (Regidx s5_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m6 (Regidx s6_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m5 (Regidx s1_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m4 (Regidx s2_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m3 (Regidx s4_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s7_idx)
               (regval_into_reg (mword_of_int a : mword 64))). }
    assert (Hspc : mc !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite (Hpk csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite (upd_ne m7 (Regidx s5_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m6 (Regidx s6_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m5 (Regidx s1_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m4 (Regidx s2_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m3 (Regidx s4_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m2 (Regidx s7_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m1 (Regidx s0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hsp1. }
    iApply (wp_uk_cadd γt γd γs γfd h19 mc (mword_of_int 0xb00) s8_idx s7_idx
              (mword_of_int (a + Z.of_nat i2)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs8c Hs7c moi_add;
                    replace (a + Z.of_nat i2) with (Z.of_nat i2 + a) by lia;
                    reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_b00 with "Hcode"). }
    assert (Eg21 : add_vec_int (mword_of_int 0xb00 : mword 64) 2
                 = mword_of_int 0xb02) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg21. clear Eg21.
    iIntros (h20) "Hrun".
    set (q0 := <[Regidx s8_idx
                 := regval_into_reg (mword_of_int (a + Z.of_nat i2)
                                     : mword 64)]> mc).
    (* ---- 0xb02  sb zero,0(s8) -- THE NUL ---- *)
    iDestruct (urun_x0 with "Hrun") as "[%Hx0 Hrun]".
    assert (Hs8q : q0 !!! Regidx s8_idx = mword_of_int (a + Z.of_nat i2))
      by exact (upd_eq mc (Regidx s8_idx)
                  (regval_into_reg (mword_of_int (a + Z.of_nat i2)
                                    : mword 64))).
    iDestruct (ush_bytes_upd a N i2 g ltac:(lia) with "Hbs") as "[Hbi Hcl]".
    iApply (wp_uk_sb γt γd γs γfd h20 q0 (mword_of_int 0xb02)
              (mword_of_int 0 : mword 12) s8_idx x0_idx
              (a + Z.of_nat i2) (g i2) nn
              ltac:(rewrite Hs8q (uint_moi (a + Z.of_nat i2)
                                    ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              with "[] Hbi Hrun").
    { iApply (uis_shk_b02 with "Hcode"). }
    iIntros "Hbi".
    iDestruct ("Hcl" $! (nth_byte (q0 !!! Regidx x0_idx) 0) with "Hbi")
      as "Hbs".
    assert (Hnul : ush_set g i2 (nth_byte (q0 !!! Regidx x0_idx) 0) i2
                   = ubyte0).
    { unfold ush_set. rewrite Nat.eqb_refl.
      assert (Ex0q : q0 !!! Regidx x0_idx = zero_reg)
        by (rewrite (upd_ne mc (Regidx s8_idx) (Regidx x0_idx) _
                       ltac:(vm_compute; discriminate)); exact Hx0).
      rewrite Ex0q. exact ush_nth_byte0_zero. }
    assert (Eb02 : add_vec_int (mword_of_int 0xb02 : mword 64) 4
                   = mword_of_int 0xb06)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eb02. clear Eb02.
    iIntros (h21) "Hrun".
    (* ---- 0xb06  c.mv a0,s7 ---- *)
    assert (Hs7q : q0 !!! Regidx s7_idx = mword_of_int a).
    { rewrite (upd_ne mc (Regidx s8_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)). exact Hs7c. }
    iApply (wp_uk_cmv γt γd γs γfd h21 q0 (mword_of_int 0xb06) a0_idx s7_idx
              (mword_of_int a) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs7q moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_b06 with "Hcode"). }
    assert (Eg23 : add_vec_int (mword_of_int 0xb06 : mword 64) 2
                 = mword_of_int 0xb08) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg23. clear Eg23.
    iIntros (h22) "Hrun".
    set (q1 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int a : mword 64)]> q0).
    assert (Hspq1 : q1 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite (upd_ne q0 (Regidx a0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne mc (Regidx s8_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspc. }
    (* ---- 0xb08  c.ldsp ra ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h22 q1 (mword_of_int 0xb08)
              (mword_of_int 11 : mword 6) ra_idx (spz - 8)
              (m !!! Regidx ra_idx) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspq1 Hsp96 Ho11; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw1 Hrun").
    { iApply (uis_shk_b08 with "Hcode"). }
    iIntros "Hw1".
    assert (Eg24 : add_vec_int (mword_of_int 0xb08 : mword 64) 2
                 = mword_of_int 0xb0a) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg24. clear Eg24.
    iIntros (h23) "Hrun".
    set (r1 := <[Regidx ra_idx
                 := regval_into_reg (m !!! Regidx ra_idx)]> q1).
    assert (Hspr1 : r1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite (upd_ne q1 (Regidx ra_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspq1. }
    (* ---- 0xb0a  c.ldsp s0 ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h23 r1 (mword_of_int 0xb0a)
              (mword_of_int 10 : mword 6) s0_idx (spz - 16)
              (m !!! Regidx s0_idx) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspr1 Hsp96 Ho10; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw2 Hrun").
    { iApply (uis_shk_b0a with "Hcode"). }
    iIntros "Hw2".
    assert (Eg25 : add_vec_int (mword_of_int 0xb0a : mword 64) 2
                 = mword_of_int 0xb0c) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg25. clear Eg25.
    iIntros (h24) "Hrun".
    set (r2 := <[Regidx s0_idx
                 := regval_into_reg (m !!! Regidx s0_idx)]> r1).
    assert (Hspr2 : r2 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite (upd_ne r1 (Regidx s0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspr1. }
    (* ---- 0xb0c  c.ldsp s1 ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h24 r2 (mword_of_int 0xb0c)
              (mword_of_int 9 : mword 6) s1_idx (spz - 24)
              (m !!! Regidx s1_idx) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspr2 Hsp96 Ho9; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw3 Hrun").
    { iApply (uis_shk_b0c with "Hcode"). }
    iIntros "Hw3".
    assert (Eg26 : add_vec_int (mword_of_int 0xb0c : mword 64) 2
                 = mword_of_int 0xb0e) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg26. clear Eg26.
    iIntros (h25) "Hrun".
    set (r3 := <[Regidx s1_idx
                 := regval_into_reg (m !!! Regidx s1_idx)]> r2).
    assert (Hspr3 : r3 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite (upd_ne r2 (Regidx s1_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspr2. }
    (* ---- 0xb0e  c.ldsp s2 ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h25 r3 (mword_of_int 0xb0e)
              (mword_of_int 8 : mword 6) s2_idx (spz - 32)
              (m !!! Regidx s2_idx) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspr3 Hsp96 Ho8; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw4 Hrun").
    { iApply (uis_shk_b0e with "Hcode"). }
    iIntros "Hw4".
    assert (Eg27 : add_vec_int (mword_of_int 0xb0e : mword 64) 2
                 = mword_of_int 0xb10) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg27. clear Eg27.
    iIntros (h26) "Hrun".
    set (r4 := <[Regidx s2_idx
                 := regval_into_reg (m !!! Regidx s2_idx)]> r3).
    assert (Hspr4 : r4 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite (upd_ne r3 (Regidx s2_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspr3. }
    (* ---- 0xb10  c.ldsp s3 ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h26 r4 (mword_of_int 0xb10)
              (mword_of_int 7 : mword 6) s3_idx (spz - 40)
              (m !!! Regidx s3_idx) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspr4 Hsp96 Ho7; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw5 Hrun").
    { iApply (uis_shk_b10 with "Hcode"). }
    iIntros "Hw5".
    assert (Eg28 : add_vec_int (mword_of_int 0xb10 : mword 64) 2
                 = mword_of_int 0xb12) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg28. clear Eg28.
    iIntros (h27) "Hrun".
    set (r5 := <[Regidx s3_idx
                 := regval_into_reg (m !!! Regidx s3_idx)]> r4).
    assert (Hspr5 : r5 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite (upd_ne r4 (Regidx s3_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspr4. }
    (* ---- 0xb12  c.ldsp s4 ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h27 r5 (mword_of_int 0xb12)
              (mword_of_int 6 : mword 6) s4_idx (spz - 48)
              (m !!! Regidx s4_idx) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspr5 Hsp96 Ho6; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw6 Hrun").
    { iApply (uis_shk_b12 with "Hcode"). }
    iIntros "Hw6".
    assert (Eg29 : add_vec_int (mword_of_int 0xb12 : mword 64) 2
                 = mword_of_int 0xb14) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg29. clear Eg29.
    iIntros (h28) "Hrun".
    set (r6 := <[Regidx s4_idx
                 := regval_into_reg (m !!! Regidx s4_idx)]> r5).
    assert (Hspr6 : r6 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite (upd_ne r5 (Regidx s4_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspr5. }
    (* ---- 0xb14  c.ldsp s5 ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h28 r6 (mword_of_int 0xb14)
              (mword_of_int 5 : mword 6) s5_idx (spz - 56)
              (m !!! Regidx s5_idx) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspr6 Hsp96 Ho5; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw7 Hrun").
    { iApply (uis_shk_b14 with "Hcode"). }
    iIntros "Hw7".
    assert (Eg30 : add_vec_int (mword_of_int 0xb14 : mword 64) 2
                 = mword_of_int 0xb16) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg30. clear Eg30.
    iIntros (h29) "Hrun".
    set (r7 := <[Regidx s5_idx
                 := regval_into_reg (m !!! Regidx s5_idx)]> r6).
    assert (Hspr7 : r7 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite (upd_ne r6 (Regidx s5_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspr6. }
    (* ---- 0xb16  c.ldsp s6 ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h29 r7 (mword_of_int 0xb16)
              (mword_of_int 4 : mword 6) s6_idx (spz - 64)
              (m !!! Regidx s6_idx) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspr7 Hsp96 Ho4; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw8 Hrun").
    { iApply (uis_shk_b16 with "Hcode"). }
    iIntros "Hw8".
    assert (Eg31 : add_vec_int (mword_of_int 0xb16 : mword 64) 2
                 = mword_of_int 0xb18) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg31. clear Eg31.
    iIntros (h30) "Hrun".
    set (r8 := <[Regidx s6_idx
                 := regval_into_reg (m !!! Regidx s6_idx)]> r7).
    assert (Hspr8 : r8 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite (upd_ne r7 (Regidx s6_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspr7. }
    (* ---- 0xb18  c.ldsp s7 ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h30 r8 (mword_of_int 0xb18)
              (mword_of_int 3 : mword 6) s7_idx (spz - 72)
              (m !!! Regidx s7_idx) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspr8 Hsp96 Ho3; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw9 Hrun").
    { iApply (uis_shk_b18 with "Hcode"). }
    iIntros "Hw9".
    assert (Eg32 : add_vec_int (mword_of_int 0xb18 : mword 64) 2
                 = mword_of_int 0xb1a) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg32. clear Eg32.
    iIntros (h31) "Hrun".
    set (r9 := <[Regidx s7_idx
                 := regval_into_reg (m !!! Regidx s7_idx)]> r8).
    assert (Hspr9 : r9 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite (upd_ne r8 (Regidx s7_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspr8. }
    (* ---- 0xb1a  c.ldsp s8 ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h31 r9 (mword_of_int 0xb1a)
              (mword_of_int 2 : mword 6) s8_idx (spz - 80)
              (m !!! Regidx s8_idx) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspr9 Hsp96 Ho2; lia)
              ltac:(unfold spz; rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw10 Hrun").
    { iApply (uis_shk_b1a with "Hcode"). }
    iIntros "Hw10".
    assert (Eg33 : add_vec_int (mword_of_int 0xb1a : mword 64) 2
                 = mword_of_int 0xb1c) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg33. clear Eg33.
    iIntros (h32) "Hrun".
    set (r10 := <[Regidx s8_idx
                 := regval_into_reg (m !!! Regidx s8_idx)]> r9).
    assert (Hspr10 : r10 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite (upd_ne r9 (Regidx s8_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hspr9. }
    (* ---- 0xb1c  c.addi16sp sp,sp,96 -- THE POP ---- *)
    iApply (wp_uk_caddi16sp_up γt γd γs γfd h32 r10 (mword_of_int 0xb1c)
              (mword_of_int 6 : mword 6) 12 nn
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12]
                    Hrun").
    { iApply (uis_shk_b1c with "Hcode"). }
    { rewrite Hspr10 Hup.
      iApply (ush_stack_12_close sp0 with
                "[] [Hw1] [Hw2] [Hw3] [Hw4] [Hw5] [Hw6] [Hw7] [Hw8] [Hw9]
                 [Hw10] [Hw11] [Hw12]");
        [ iPureIntro; exact Hal8
        | iExists _; iExact "Hw1" | iExists _; iExact "Hw2"
        | iExists _; iExact "Hw3" | iExists _; iExact "Hw4"
        | iExists _; iExact "Hw5" | iExists _; iExact "Hw6"
        | iExists _; iExact "Hw7" | iExists _; iExact "Hw8"
        | iExists _; iExact "Hw9" | iExists _; iExact "Hw10"
        | iApply (uword_of_ubytes γd (spz - 88) _ with "Hw11")
        | iExists _; iExact "Hw12" ]. }
    rewrite Hspr10 Hup.
    assert (Eg34 : add_vec_int (mword_of_int 0xb1c : mword 64) 2
                 = mword_of_int 0xb1e) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eg34. clear Eg34.
    iIntros (h33) "Hrun".
    set (r11 := <[Regidx csp_rs1 := regval_into_reg sp0]> r10).
    assert (Hrar11 : r11 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite (upd_ne r10 (Regidx csp_rs1) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r9 (Regidx s8_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r8 (Regidx s7_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r7 (Regidx s6_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r6 (Regidx s5_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r5 (Regidx s4_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r4 (Regidx s3_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r3 (Regidx s2_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r2 (Regidx s1_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r1 (Regidx s0_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq q1 (Regidx ra_idx)
               (regval_into_reg (m !!! Regidx ra_idx))). }
    (* ---- 0xb1e  c.jr ra ---- *)
    iApply (wp_uk_cjr γt γd γs γfd h33 r11 (mword_of_int 0xb1e) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) (12 + nn)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hrar11; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_b1e with "Hcode"). }
    iIntros (h34) "Hrun".
    iApply ("Hcont" with "[Hbs] [] Hrun").
    { iExists (ush_set g i2 (nth_byte (q0 !!! Regidx x0_idx) 0)), i2.
      iSplit; [ iPureIntro; split; [ lia | exact Hnul ] | iExact "Hbs" ]. }
    iPureIntro. intros r Hr.
    destruct (Z.eq_dec (uint r) 2) as [Eq1 | Eq1].
    { rewrite (ush_ridx_eq r csp_rs1
                 ltac:(rewrite Eq1; vm_compute; reflexivity)).
      rewrite Hsp.
      exact (upd_eq r10 (Regidx csp_rs1) (regval_into_reg sp0)). }
    destruct (Z.eq_dec (uint r) 8) as [Eq2 | Eq2].
    { rewrite (ush_ridx_eq r s0_idx
                 ltac:(rewrite Eq2; vm_compute; reflexivity)).
      rewrite (upd_ne r10 (Regidx csp_rs1) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r9 (Regidx s8_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r8 (Regidx s7_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r7 (Regidx s6_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r6 (Regidx s5_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r5 (Regidx s4_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r4 (Regidx s3_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r3 (Regidx s2_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r2 (Regidx s1_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r1 (Regidx s0_idx) (regval_into_reg (m !!! Regidx s0_idx))). }
    destruct (Z.eq_dec (uint r) 9) as [Eq3 | Eq3].
    { rewrite (ush_ridx_eq r s1_idx
                 ltac:(rewrite Eq3; vm_compute; reflexivity)).
      rewrite (upd_ne r10 (Regidx csp_rs1) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r9 (Regidx s8_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r8 (Regidx s7_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r7 (Regidx s6_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r6 (Regidx s5_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r5 (Regidx s4_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r4 (Regidx s3_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r3 (Regidx s2_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r2 (Regidx s1_idx) (regval_into_reg (m !!! Regidx s1_idx))). }
    destruct (Z.eq_dec (uint r) 18) as [Eq4 | Eq4].
    { rewrite (ush_ridx_eq r s2_idx
                 ltac:(rewrite Eq4; vm_compute; reflexivity)).
      rewrite (upd_ne r10 (Regidx csp_rs1) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r9 (Regidx s8_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r8 (Regidx s7_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r7 (Regidx s6_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r6 (Regidx s5_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r5 (Regidx s4_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r4 (Regidx s3_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r3 (Regidx s2_idx) (regval_into_reg (m !!! Regidx s2_idx))). }
    destruct (Z.eq_dec (uint r) 19) as [Eq5 | Eq5].
    { rewrite (ush_ridx_eq r s3_idx
                 ltac:(rewrite Eq5; vm_compute; reflexivity)).
      rewrite (upd_ne r10 (Regidx csp_rs1) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r9 (Regidx s8_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r8 (Regidx s7_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r7 (Regidx s6_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r6 (Regidx s5_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r5 (Regidx s4_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r4 (Regidx s3_idx) (regval_into_reg (m !!! Regidx s3_idx))). }
    destruct (Z.eq_dec (uint r) 20) as [Eq6 | Eq6].
    { rewrite (ush_ridx_eq r s4_idx
                 ltac:(rewrite Eq6; vm_compute; reflexivity)).
      rewrite (upd_ne r10 (Regidx csp_rs1) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r9 (Regidx s8_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r8 (Regidx s7_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r7 (Regidx s6_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r6 (Regidx s5_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r5 (Regidx s4_idx) (regval_into_reg (m !!! Regidx s4_idx))). }
    destruct (Z.eq_dec (uint r) 21) as [Eq7 | Eq7].
    { rewrite (ush_ridx_eq r s5_idx
                 ltac:(rewrite Eq7; vm_compute; reflexivity)).
      rewrite (upd_ne r10 (Regidx csp_rs1) (Regidx s5_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r9 (Regidx s8_idx) (Regidx s5_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r8 (Regidx s7_idx) (Regidx s5_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r7 (Regidx s6_idx) (Regidx s5_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r6 (Regidx s5_idx) (regval_into_reg (m !!! Regidx s5_idx))). }
    destruct (Z.eq_dec (uint r) 22) as [Eq8 | Eq8].
    { rewrite (ush_ridx_eq r s6_idx
                 ltac:(rewrite Eq8; vm_compute; reflexivity)).
      rewrite (upd_ne r10 (Regidx csp_rs1) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r9 (Regidx s8_idx) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r8 (Regidx s7_idx) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r7 (Regidx s6_idx) (regval_into_reg (m !!! Regidx s6_idx))). }
    destruct (Z.eq_dec (uint r) 23) as [Eq9 | Eq9].
    { rewrite (ush_ridx_eq r s7_idx
                 ltac:(rewrite Eq9; vm_compute; reflexivity)).
      rewrite (upd_ne r10 (Regidx csp_rs1) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne r9 (Regidx s8_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r8 (Regidx s7_idx) (regval_into_reg (m !!! Regidx s7_idx))). }
    destruct (Z.eq_dec (uint r) 24) as [Eq10 | Eq10].
    { rewrite (ush_ridx_eq r s8_idx
                 ltac:(rewrite Eq10; vm_compute; reflexivity)).
      rewrite (upd_ne r10 (Regidx csp_rs1) (Regidx s8_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r9 (Regidx s8_idx) (regval_into_reg (m !!! Regidx s8_idx))). }
    assert (Hu : uint r = 3 \/ uint r = 4 \/ uint r = 25 \/
                 uint r = 26 \/ uint r = 27).
    { pose proof (ucs_cases r Hr) as Hc. lia. }
    assert (Hkeep : ush_gets_keep r = true).
    { unfold ush_gets_keep.
      destruct Hu as [E|[E|[E|[E|E]]]]; rewrite E; vm_compute; reflexivity. }
    rewrite (upd_ne r10 (Regidx csp_rs1) (Regidx r) _
               (ush_r_ne r 2 csp_rs1 ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne r9 (Regidx s8_idx) (Regidx r) _
               (ush_r_ne r 24 s8_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne r8 (Regidx s7_idx) (Regidx r) _
               (ush_r_ne r 23 s7_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne r7 (Regidx s6_idx) (Regidx r) _
               (ush_r_ne r 22 s6_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne r6 (Regidx s5_idx) (Regidx r) _
               (ush_r_ne r 21 s5_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne r5 (Regidx s4_idx) (Regidx r) _
               (ush_r_ne r 20 s4_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne r4 (Regidx s3_idx) (Regidx r) _
               (ush_r_ne r 19 s3_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne r3 (Regidx s2_idx) (Regidx r) _
               (ush_r_ne r 18 s2_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne r2 (Regidx s1_idx) (Regidx r) _
               (ush_r_ne r 9 s1_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne r1 (Regidx s0_idx) (Regidx r) _
               (ush_r_ne r 8 s0_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne q1 (Regidx ra_idx) (Regidx r) _
               (ush_r_ne r 1 ra_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne q0 (Regidx a0_idx) (Regidx r) _
               (ush_r_ne r 10 a0_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne mc (Regidx s8_idx) (Regidx r) _
               (ush_r_ne r 24 s8_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (Hpk r Hkeep).
    rewrite (upd_ne m7 (Regidx s5_idx) (Regidx r) _
               (ush_r_ne r 21 s5_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne m6 (Regidx s6_idx) (Regidx r) _
               (ush_r_ne r 22 s6_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne m5 (Regidx s1_idx) (Regidx r) _
               (ush_r_ne r 9 s1_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne m4 (Regidx s2_idx) (Regidx r) _
               (ush_r_ne r 18 s2_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne m3 (Regidx s4_idx) (Regidx r) _
               (ush_r_ne r 20 s4_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne m2 (Regidx s7_idx) (Regidx r) _
               (ush_r_ne r 23 s7_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne m1 (Regidx s0_idx) (Regidx r) _
               (ush_r_ne r 8 s0_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne m (Regidx csp_rs1) (Regidx r) _
               (ush_r_ne r 2 csp_rs1 ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    reflexivity.
  Qed.


  (* ===================================================================== *)
  (* getcmd @0x0 -- 29 instructions, a 32-byte frame, three calls.          *)
  (* DEPENDS ON [ush_read_leaf] (through [wp_ksh_gets]).                    *)
  (*                                                                       *)
  (*   write(2, "$ ", 2);  memset(buf, 0, nbuf);  gets(buf, nbuf);          *)
  (*   return buf[0] == 0 ? -1 : 0;                                         *)
  (*                                                                       *)
  (* The stack budget is the call chain spelled out: getcmd's own four      *)
  (* words on top of gets' twelve, which is the deepest callee.  memset     *)
  (* borrows two of the same twelve and write borrows none.                 *)
  (*                                                                       *)
  (* THE RETURN VALUE IS NOT COMPUTED.  [seqz]/[negw] turn [buf[0]] into    *)
  (* 0 or -1 and main branches on it at 0x940, but the walk never needs to  *)
  (* know which: both arms of that branch are proved, so the two            *)
  (* instructions go through with their values left as they are.            *)
  (* ===================================================================== *)
  Lemma wp_ksh_getcmd (h : CpuId) (m : regfile) (a : Z) (N : nat)
      (f : nat -> bv 8) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int a ->
    m !!! Regidx a1_idx = mword_of_int (Z.of_nat N) ->
    (0 < N)%nat -> Z.of_nat N < Z31 ->
    shk_code γt -∗
    ubytes γd a N f -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.getcmd) (4 + (12 + nn)) -∗
    ((∃ (g : nat -> bv 8) (i2 : nat),
        ⌜ (i2 < N)%nat /\ g i2 = ubyte0 ⌝ ∗ ubytes γd a N g) -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (4 + (12 + nn)) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Ha1 HN0 HN31. iIntros "#Hcode Hbs Hrun Hcont".
    rewrite shp_getcmd.
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    iDestruct (urun_ubytes_bnd h m _ (4 + (12 + nn)) (DfracOwn 1) a N f
                 ltac:(lia) with "Hrun Hbs") as %[Halo Hahi].
    change (2 ^ 38) with 274877906944 in Hahi.
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    assert (Hlo : 32 <= uint sp0) by lia.
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                   = bv_unsigned sp0 - 32).
    { replace (- (8 * Z.of_nat 4)) with (-32) by lia.
      exact (uv_avi_neg sp0 32 ltac:(lia) ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp32 : uint (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                    = uint sp0 - 32)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Go0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    assert (Go1 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    assert (Go2 : uoff_sdsp (mword_of_int 2 : mword 6) = 16)
      by (vm_compute; reflexivity).
    assert (Go3 : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
      by (vm_compute; reflexivity).
    (* ---- 0x0  c.addi sp,sp,-32 -- THE PUSH ---- *)
    iApply (wp_uk_caddi_sp_dn γt γd γs γfd h m (mword_of_int 0x0)
              (mword_of_int 32 : mword 6) 4 (12 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_00 with "Hcode"). }
    assert (E00 : add_vec_int (mword_of_int 0x0 : mword 64) 2
                  = mword_of_int 0x2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp ustack_4 E00.
    iIntros "(_ & [%v1 Hw1] & [%v2 Hw2] & [%v3 Hw3] & [%v4 Hw4])".
    iIntros (h1) "Hrun".
    set (n1 := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 4)))]> m).
    assert (Hsp1 : n1 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 4)))
      by exact (upd_eq m (Regidx csp_rs1)
                  (regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 4))))).
    assert (Hn1 : forall r : mword 5, Regidx r <> Regidx csp_rs1 ->
                    n1 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr; exact (upd_ne m (Regidx csp_rs1) (Regidx r) _ Hr)).
    (* ---- 0x2..0x8  the four spills ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd h1 n1 (mword_of_int 0x2)
              (mword_of_int 3 : mword 6) ra_idx (uint sp0 - 8) v1 (12 + nn)
              ltac:(rewrite Hsp1 Hsp32 Go3; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw1 Hrun").
    { iApply (uis_shk_02 with "Hcode"). }
    iIntros "Hw1". rewrite (Hn1 ra_idx ltac:(vm_compute; discriminate)).
    assert (E02 : add_vec_int (mword_of_int 0x2 : mword 64) 2
                  = mword_of_int 0x4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E02. iIntros (h2) "Hrun".
    iApply (wp_uk_csdsp γt γd γs γfd h2 n1 (mword_of_int 0x4)
              (mword_of_int 2 : mword 6) s0_idx (uint sp0 - 16) v2 (12 + nn)
              ltac:(rewrite Hsp1 Hsp32 Go2; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw2 Hrun").
    { iApply (uis_shk_04 with "Hcode"). }
    iIntros "Hw2". rewrite (Hn1 s0_idx ltac:(vm_compute; discriminate)).
    assert (E04 : add_vec_int (mword_of_int 0x4 : mword 64) 2
                  = mword_of_int 0x6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E04. iIntros (h3) "Hrun".
    iApply (wp_uk_csdsp γt γd γs γfd h3 n1 (mword_of_int 0x6)
              (mword_of_int 1 : mword 6) s1_idx (uint sp0 - 24) v3 (12 + nn)
              ltac:(rewrite Hsp1 Hsp32 Go1; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw3 Hrun").
    { iApply (uis_shk_06 with "Hcode"). }
    iIntros "Hw3". rewrite (Hn1 s1_idx ltac:(vm_compute; discriminate)).
    assert (E06 : add_vec_int (mword_of_int 0x6 : mword 64) 2
                  = mword_of_int 0x8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E06. iIntros (h4) "Hrun".
    iApply (wp_uk_csdsp γt γd γs γfd h4 n1 (mword_of_int 0x8)
              (mword_of_int 0 : mword 6) s2_idx (uint sp0 - 32) v4 (12 + nn)
              ltac:(rewrite Hsp1 Hsp32 Go0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw4 Hrun").
    { iApply (uis_shk_08 with "Hcode"). }
    iIntros "Hw4". rewrite (Hn1 s2_idx ltac:(vm_compute; discriminate)).
    assert (E08 : add_vec_int (mword_of_int 0x8 : mword 64) 2
                  = mword_of_int 0xa)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E08. iIntros (h5) "Hrun".
    (* ---- 0xa  c.addi4spn s0,sp,32 (s0 is dead until the epilogue) ---- *)
    iApply (wp_uk_caddi4spn γt γd γs γfd h5 n1 (mword_of_int 0xa)
              (mword_of_int 0 : mword 3) (mword_of_int 8 : mword 8) s0_idx
              (add_vec (n1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))
              (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              eq_refl
              with "[] Hrun").
    { iApply (uis_shk_0a with "Hcode"). }
    assert (E0a : add_vec_int (mword_of_int 0xa : mword 64) 2
                  = mword_of_int 0xc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0a. iIntros (h6) "Hrun".
    set (n2 := <[Regidx s0_idx
                 := regval_into_reg
                      (add_vec (n1 !!! Regidx csp_rs1)
                         (sign_extend' 64
                            (caddi4spn_imm (mword_of_int 8 : mword 8))))]> n1).
    assert (Hn2 : forall r : mword 5, Regidx r <> Regidx s0_idx ->
                    n2 !!! Regidx r = n1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n1 (Regidx s0_idx) (Regidx r) _ Hr)).
    assert (Ha0_2 : n2 !!! Regidx a0_idx = mword_of_int a).
    { rewrite (Hn2 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    (* ---- 0xc  c.mv s1,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h6 n2 (mword_of_int 0xc) s1_idx a0_idx
              (mword_of_int a) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_2 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_0c with "Hcode"). }
    assert (E0c : add_vec_int (mword_of_int 0xc : mword 64) 2
                  = mword_of_int 0xe)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0c. iIntros (h7) "Hrun".
    set (n3 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int a : mword 64)]> n2).
    assert (Hn3 : forall r : mword 5, Regidx r <> Regidx s1_idx ->
                    n3 !!! Regidx r = n2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n2 (Regidx s1_idx) (Regidx r) _ Hr)).
    assert (Ha1_3 : n3 !!! Regidx a1_idx = mword_of_int (Z.of_nat N)).
    { rewrite (Hn3 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn2 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn1 a1_idx ltac:(vm_compute; discriminate)). exact Ha1. }
    (* ---- 0xe  c.mv s2,a1 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h7 n3 (mword_of_int 0xe) s2_idx a1_idx
              (mword_of_int (Z.of_nat N)) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha1_3 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_0e with "Hcode"). }
    assert (E0e : add_vec_int (mword_of_int 0xe : mword 64) 2
                  = mword_of_int 0x10)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0e. iIntros (h8) "Hrun".
    set (n4 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int (Z.of_nat N)
                                     : mword 64)]> n3).
    assert (Hn4 : forall r : mword 5, Regidx r <> Regidx s2_idx ->
                    n4 !!! Regidx r = n3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n3 (Regidx s2_idx) (Regidx r) _ Hr)).
    assert (Hs1_4 : n4 !!! Regidx s1_idx = mword_of_int a).
    { rewrite (Hn4 s1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq n2 (Regidx s1_idx)
               (regval_into_reg (mword_of_int a : mword 64))). }
    assert (Hs2_4 : n4 !!! Regidx s2_idx = mword_of_int (Z.of_nat N))
      by exact (upd_eq n3 (Regidx s2_idx)
                  (regval_into_reg (mword_of_int (Z.of_nat N) : mword 64))).
    (* ---- 0x10..0x1c  the prompt: write(2, "$ ", 2) ---- *)
    iApply (wp_uk_cli γt γd γs γfd h8 n4 (mword_of_int 0x10)
              (mword_of_int 2 : mword 6) a2_idx (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_10 with "Hcode"). }
    assert (Em10 : <[Regidx a2_idx
                     := regval_into_reg (sign_extend' 64
                                           (mword_of_int 2 : mword 6)
                                         : mword 64)]> n4
                   = <[Regidx a2_idx
                       := regval_into_reg (mword_of_int 2 : mword 64)]> n4)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (E10 : add_vec_int (mword_of_int 0x10 : mword 64) 2
                  = mword_of_int 0x12)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Em10 E10. iIntros (h9) "Hrun".
    set (n5 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int 2 : mword 64)]> n4).
    assert (Hn5 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
                    n5 !!! Regidx r = n4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n4 (Regidx a2_idx) (Regidx r) _ Hr)).
    iApply (wp_uk_auipc γt γd γs γfd h9 n5 (mword_of_int 0x12)
              (mword_of_int 1 : mword 20) a1_idx
              (add_vec (mword_of_int 0x12 : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20))) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_12 with "Hcode"). }
    assert (E12 : add_vec_int (mword_of_int 0x12 : mword 64) 4
                  = mword_of_int 0x16)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E12. iIntros (h10) "Hrun".
    set (n6 := <[Regidx a1_idx
                 := regval_into_reg
                      (add_vec (mword_of_int 0x12 : mword 64)
                         (auipc_off (mword_of_int 1 : mword 20)))]> n5).
    assert (Hn6 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                    n6 !!! Regidx r = n5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n5 (Regidx a1_idx) (Regidx r) _ Hr)).
    iApply (wp_uk_addi γt γd γs γfd h10 n6 (mword_of_int 0x16)
              (mword_of_int 622 : mword 12) a1_idx a1_idx
              (add_vec (n6 !!! Regidx a1_idx)
                 (sign_extend' 64 (mword_of_int 622 : mword 12))) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_16 with "Hcode"). }
    assert (E16 : add_vec_int (mword_of_int 0x16 : mword 64) 4
                  = mword_of_int 0x1a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E16. iIntros (h11) "Hrun".
    set (n7 := <[Regidx a1_idx
                 := regval_into_reg
                      (add_vec (n6 !!! Regidx a1_idx)
                         (sign_extend' 64
                            (mword_of_int 622 : mword 12)))]> n6).
    assert (Hn7 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                    n7 !!! Regidx r = n6 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n6 (Regidx a1_idx) (Regidx r) _ Hr)).
    iApply (wp_uk_cmv γt γd γs γfd h11 n7 (mword_of_int 0x1a) a0_idx a2_idx
              (add_vec zero_reg (n7 !!! Regidx a2_idx)) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_1a with "Hcode"). }
    assert (E1a : add_vec_int (mword_of_int 0x1a : mword 64) 2
                  = mword_of_int 0x1c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1a. iIntros (h12) "Hrun".
    set (n8 := <[Regidx a0_idx
                 := regval_into_reg
                      (add_vec zero_reg (n7 !!! Regidx a2_idx))]> n7).
    assert (Hn8 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    n8 !!! Regidx r = n7 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n7 (Regidx a0_idx) (Regidx r) _ Hr)).
    (* ---- 0x1c  jal ra,0xca6 <write> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h12 n8 (mword_of_int 0x1c)
              (mword_of_int 3210 : mword 21) ra_idx
              (mword_of_int ShSyms.write) (mword_of_int 0x20) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite shp_write; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite shp_write; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_1c with "Hcode"). }
    iIntros (h13) "Hrun".
    set (n9 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x20 : mword 64)]> n8).
    assert (Hn9 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                    n9 !!! Regidx r = n8 !!! Regidx r)
      by (intros r Hr; exact (upd_ne n8 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Hra9 : n9 !!! Regidx ra_idx = mword_of_int 0x20)
      by exact (upd_eq n8 (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0x20 : mword 64))).
    iApply (wp_ksh_write h13 n9 (12 + nn) with "Hcode Hrun").
    iIntros (h14 rw) "Hrun". rewrite Hra9.
    assert (Er20 : ret_pc (mword_of_int 0x20 : mword 64) = mword_of_int 0x20)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Er20.
    set (nA := <[Regidx a0_idx := rw]>
                 (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> n9)).
    assert (HnA : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    Regidx r <> Regidx a7_idx ->
                    nA !!! Regidx r = n9 !!! Regidx r).
    { intros r Hr0 Hr7.
      rewrite (upd_ne _ (Regidx a0_idx) (Regidx r) _ Hr0).
      exact (upd_ne n9 (Regidx a7_idx) (Regidx r) _ Hr7). }
    assert (Hs1_A : nA !!! Regidx s1_idx = mword_of_int a).
    { rewrite (HnA s1_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      rewrite (Hn9 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn8 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn7 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn6 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn5 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_4. }
    assert (Hs2_A : nA !!! Regidx s2_idx = mword_of_int (Z.of_nat N)).
    { rewrite (HnA s2_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      rewrite (Hn9 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn8 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn7 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn6 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn5 s2_idx ltac:(vm_compute; discriminate)). exact Hs2_4. }
    (* ---- 0x20..0x26  memset(buf, 0, nbuf) ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h14 nA (mword_of_int 0x20) a2_idx s2_idx
              (mword_of_int (Z.of_nat N)) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2_A moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_20 with "Hcode"). }
    assert (E20 : add_vec_int (mword_of_int 0x20 : mword 64) 2
                  = mword_of_int 0x22)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E20. iIntros (h15) "Hrun".
    set (nB := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int (Z.of_nat N)
                                     : mword 64)]> nA).
    assert (HnB : forall r : mword 5, Regidx r <> Regidx a2_idx ->
                    nB !!! Regidx r = nA !!! Regidx r)
      by (intros r Hr; exact (upd_ne nA (Regidx a2_idx) (Regidx r) _ Hr)).
    iApply (wp_uk_cli γt γd γs γfd h15 nB (mword_of_int 0x22)
              (mword_of_int 0 : mword 6) a1_idx (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_22 with "Hcode"). }
    assert (E22 : add_vec_int (mword_of_int 0x22 : mword 64) 2
                  = mword_of_int 0x24)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E22. iIntros (h16) "Hrun".
    set (nC := <[Regidx a1_idx
                 := regval_into_reg (sign_extend' 64
                                       (mword_of_int 0 : mword 6)
                                     : mword 64)]> nB).
    assert (HnC : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                    nC !!! Regidx r = nB !!! Regidx r)
      by (intros r Hr; exact (upd_ne nB (Regidx a1_idx) (Regidx r) _ Hr)).
    assert (Hs1_C : nC !!! Regidx s1_idx = mword_of_int a).
    { rewrite (HnC s1_idx ltac:(vm_compute; discriminate)).
      rewrite (HnB s1_idx ltac:(vm_compute; discriminate)). exact Hs1_A. }
    iApply (wp_uk_cmv γt γd γs γfd h16 nC (mword_of_int 0x24) a0_idx s1_idx
              (mword_of_int a) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_C moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_24 with "Hcode"). }
    assert (E24 : add_vec_int (mword_of_int 0x24 : mword 64) 2
                  = mword_of_int 0x26)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E24. iIntros (h17) "Hrun".
    set (nD := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int a : mword 64)]> nC).
    assert (HnD : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    nD !!! Regidx r = nC !!! Regidx r)
      by (intros r Hr; exact (upd_ne nC (Regidx a0_idx) (Regidx r) _ Hr)).
    iApply (wp_uk_jal γt γd γs γfd h17 nD (mword_of_int 0x26)
              (mword_of_int 2614 : mword 21) ra_idx
              (mword_of_int ShSyms.memset) (mword_of_int 0x2a) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite shp_memset; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite shp_memset; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_26 with "Hcode"). }
    iIntros (h18) "Hrun".
    set (nE := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x2a : mword 64)]> nD).
    assert (HnE : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                    nE !!! Regidx r = nD !!! Regidx r)
      by (intros r Hr; exact (upd_ne nD (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (HraE : nE !!! Regidx ra_idx = mword_of_int 0x2a)
      by exact (upd_eq nD (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0x2a : mword 64))).
    assert (Ha0_E : nE !!! Regidx a0_idx = mword_of_int a).
    { rewrite (HnE a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq nC (Regidx a0_idx)
               (regval_into_reg (mword_of_int a : mword 64))). }
    assert (Ha2_E : nE !!! Regidx a2_idx = mword_of_int (Z.of_nat N)).
    { rewrite (HnE a2_idx ltac:(vm_compute; discriminate)).
      rewrite (HnD a2_idx ltac:(vm_compute; discriminate)).
      rewrite (HnC a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq nA (Regidx a2_idx)
               (regval_into_reg (mword_of_int (Z.of_nat N) : mword 64))). }
    replace (12 + nn)%nat with (2 + (10 + nn))%nat by lia.
    iApply (wp_ksh_memset h18 nE a N f (10 + nn) Ha0_E Ha2_E HN0 HN31
              with "Hcode Hbs Hrun").
    iIntros "Hbs" (h19 mM) "%HcsM Hrun". rewrite HraE.
    assert (Er2a : ret_pc (mword_of_int 0x2a : mword 64) = mword_of_int 0x2a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Er2a.
    replace (2 + (10 + nn))%nat with (12 + nn)%nat by lia.
    iAssert (∃ g : nat -> bv 8, ubytes γd a N g)%I with "[Hbs]" as "Hbs".
    { iExists _. iExact "Hbs". }
    iDestruct "Hbs" as (fm) "Hbs".
    (* ---- 0x2a..0x2e  gets(buf, nbuf) ---- *)
    assert (Hs2_M : mM !!! Regidx s2_idx = mword_of_int (Z.of_nat N)).
    { rewrite (HcsM s2_idx ltac:(vm_compute; reflexivity)).
      rewrite (HnE s2_idx ltac:(vm_compute; discriminate)).
      rewrite (HnD s2_idx ltac:(vm_compute; discriminate)).
      rewrite (HnC s2_idx ltac:(vm_compute; discriminate)).
      rewrite (HnB s2_idx ltac:(vm_compute; discriminate)). exact Hs2_A. }
    assert (Hs1_M : mM !!! Regidx s1_idx = mword_of_int a).
    { rewrite (HcsM s1_idx ltac:(vm_compute; reflexivity)).
      rewrite (HnE s1_idx ltac:(vm_compute; discriminate)).
      rewrite (HnD s1_idx ltac:(vm_compute; discriminate)). exact Hs1_C. }
    iApply (wp_uk_cmv γt γd γs γfd h19 mM (mword_of_int 0x2a) a1_idx s2_idx
              (mword_of_int (Z.of_nat N)) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2_M moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_2a with "Hcode"). }
    assert (E2a : add_vec_int (mword_of_int 0x2a : mword 64) 2
                  = mword_of_int 0x2c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E2a. iIntros (h20) "Hrun".
    set (nF := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int (Z.of_nat N)
                                     : mword 64)]> mM).
    assert (HnF : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                    nF !!! Regidx r = mM !!! Regidx r)
      by (intros r Hr; exact (upd_ne mM (Regidx a1_idx) (Regidx r) _ Hr)).
    assert (Hs1_F : nF !!! Regidx s1_idx = mword_of_int a)
      by (rewrite (HnF s1_idx ltac:(vm_compute; discriminate)); exact Hs1_M).
    iApply (wp_uk_cmv γt γd γs γfd h20 nF (mword_of_int 0x2c) a0_idx s1_idx
              (mword_of_int a) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_F moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_2c with "Hcode"). }
    assert (E2c : add_vec_int (mword_of_int 0x2c : mword 64) 2
                  = mword_of_int 0x2e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E2c. iIntros (h21) "Hrun".
    set (nG := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int a : mword 64)]> nF).
    assert (HnG : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    nG !!! Regidx r = nF !!! Regidx r)
      by (intros r Hr; exact (upd_ne nF (Regidx a0_idx) (Regidx r) _ Hr)).
    iApply (wp_uk_jal γt γd γs γfd h21 nG (mword_of_int 0x2e)
              (mword_of_int 2684 : mword 21) ra_idx
              (mword_of_int ShSyms.gets) (mword_of_int 0x32) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite shp_gets; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite shp_gets; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_2e with "Hcode"). }
    iIntros (h22) "Hrun".
    set (nH := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x32 : mword 64)]> nG).
    assert (HnH : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                    nH !!! Regidx r = nG !!! Regidx r)
      by (intros r Hr; exact (upd_ne nG (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (HraH : nH !!! Regidx ra_idx = mword_of_int 0x32)
      by exact (upd_eq nG (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0x32 : mword 64))).
    assert (Ha0_H : nH !!! Regidx a0_idx = mword_of_int a).
    { rewrite (HnH a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq nF (Regidx a0_idx)
               (regval_into_reg (mword_of_int a : mword 64))). }
    assert (Ha1_H : nH !!! Regidx a1_idx = mword_of_int (Z.of_nat N)).
    { rewrite (HnH a1_idx ltac:(vm_compute; discriminate)).
      rewrite (HnG a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq mM (Regidx a1_idx)
               (regval_into_reg (mword_of_int (Z.of_nat N) : mword 64))). }
    iApply (wp_ksh_gets h22 nH a N fm nn Ha0_H Ha1_H HN0 HN31
              with "Hcode Hbs Hrun").
    iIntros "Hbs" (h23 mG) "%HcsG Hrun". rewrite HraH.
    assert (Er32 : ret_pc (mword_of_int 0x32 : mword 64) = mword_of_int 0x32)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Er32.
    iDestruct "Hbs" as (gg i2) "[%Hgi Hbs]".
    (* ---- 0x32  lbu a0,0(s1) -- the return value's only input ---- *)
    assert (Hs1_G : mG !!! Regidx s1_idx = mword_of_int a).
    { rewrite (HcsG s1_idx ltac:(vm_compute; reflexivity)).
      rewrite (HnH s1_idx ltac:(vm_compute; discriminate)).
      rewrite (HnG s1_idx ltac:(vm_compute; discriminate)). exact Hs1_F. }
    iDestruct (ush_bytes_at (DfracOwn 1) a N 0%nat gg ltac:(lia) with "Hbs")
      as "[Hb0 Hcl0]".
    rewrite Z.add_0_r.
    iApply (wp_uk_lbu γt γd γs γfd h23 mG (mword_of_int 0x32)
              (mword_of_int 0 : mword 12) s1_idx a0_idx (DfracOwn 1)
              a (gg 0%nat) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1_G (uint_moi a ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb0 Hrun").
    { iApply (uis_shk_32 with "Hcode"). }
    iIntros "Hb0".
    iDestruct ("Hcl0" with "Hb0") as "Hbs".
    rewrite <- (Z.add_0_r a).
    assert (E32 : add_vec_int (mword_of_int 0x32 : mword 64) 4
                  = mword_of_int 0x36)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E32. iIntros (h24) "Hrun".
    set (nI := <[Regidx a0_idx
                 := regval_into_reg (zero_extend' 64 (gg 0%nat : mword 8)
                                     : mword 64)]> mG).
    assert (HnI : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    nI !!! Regidx r = mG !!! Regidx r)
      by (intros r Hr; exact (upd_ne mG (Regidx a0_idx) (Regidx r) _ Hr)).
    (* ---- 0x36  seqz a0,a0 ; 0x3a  negw a0,a0 -- values not needed ---- *)
    iApply (wp_uk_sltiu γt γd γs γfd h24 nI (mword_of_int 0x36)
              (mword_of_int 1 : mword 12) a0_idx a0_idx
              (zero_extend' 64
                 (bool_to_bit (zopz0zI_u (nI !!! Regidx a0_idx)
                                 (sign_extend' 64
                                    (mword_of_int 1 : mword 12)))))
              (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_36 with "Hcode"). }
    assert (E36 : add_vec_int (mword_of_int 0x36 : mword 64) 4
                  = mword_of_int 0x3a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E36. iIntros (h25) "Hrun".
    set (nJ := <[Regidx a0_idx
                 := regval_into_reg
                      (zero_extend' 64
                         (bool_to_bit (zopz0zI_u (nI !!! Regidx a0_idx)
                                         (sign_extend' 64
                                            (mword_of_int 1 : mword 12)))))]> nI).
    assert (HnJ : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    nJ !!! Regidx r = nI !!! Regidx r)
      by (intros r Hr; exact (upd_ne nI (Regidx a0_idx) (Regidx r) _ Hr)).
    iApply (wp_uk_subw γt γd γs γfd h25 nJ (mword_of_int 0x3a)
              x0_idx a0_idx a0_idx
              (sign_extend' 64
                 (sub_vec (subrange_vec_dec (nJ !!! Regidx x0_idx) 31 0
                           : mword 32)
                    (subrange_vec_dec (nJ !!! Regidx a0_idx) 31 0 : mword 32)))
              (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_3a with "Hcode"). }
    assert (E3a : add_vec_int (mword_of_int 0x3a : mword 64) 4
                  = mword_of_int 0x3e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E3a. iIntros (h26) "Hrun".
    set (nK := <[Regidx a0_idx
                 := regval_into_reg
                      (sign_extend' 64
                         (sub_vec (subrange_vec_dec (nJ !!! Regidx x0_idx) 31 0
                                   : mword 32)
                            (subrange_vec_dec (nJ !!! Regidx a0_idx) 31 0
                             : mword 32)))]> nJ).
    assert (HnK : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    nK !!! Regidx r = nJ !!! Regidx r)
      by (intros r Hr; exact (upd_ne nJ (Regidx a0_idx) (Regidx r) _ Hr)).
    (* the sp the epilogue reloads from: it survived all three calls *)
    assert (HspK : nK !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite (HnK csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (HnJ csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (HnI csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (HcsG csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite (HnH csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (HnG csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (HnF csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (HcsM csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite (HnE csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (HnD csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (HnC csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (HnB csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (HnA csp_rs1 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      rewrite (Hn9 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hn8 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hn7 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hn6 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hn5 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hn4 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hn3 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hn2 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp1. }
    (* ---- 0x3e..0x44  the four reloads ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h26 nK (mword_of_int 0x3e)
              (mword_of_int 3 : mword 6) ra_idx (uint sp0 - 8)
              (m !!! Regidx ra_idx) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite HspK Hsp32 Go3; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw1 Hrun").
    { iApply (uis_shk_3e with "Hcode"). }
    iIntros "Hw1".
    assert (E3e : add_vec_int (mword_of_int 0x3e : mword 64) 2
                  = mword_of_int 0x40)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E3e. iIntros (h27) "Hrun".
    set (p1 := <[Regidx ra_idx
                 := regval_into_reg (m !!! Regidx ra_idx)]> nK).
    assert (Hsp_p1 : p1 !!! Regidx csp_rs1
                     = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite (upd_ne nK (Regidx ra_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact HspK. }
    iApply (wp_uk_cldsp γt γd γs γfd h27 p1 (mword_of_int 0x40)
              (mword_of_int 2 : mword 6) s0_idx (uint sp0 - 16)
              (m !!! Regidx s0_idx) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp_p1 Hsp32 Go2; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw2 Hrun").
    { iApply (uis_shk_40 with "Hcode"). }
    iIntros "Hw2".
    assert (E40 : add_vec_int (mword_of_int 0x40 : mword 64) 2
                  = mword_of_int 0x42)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E40. iIntros (h28) "Hrun".
    set (p2 := <[Regidx s0_idx
                 := regval_into_reg (m !!! Regidx s0_idx)]> p1).
    assert (Hsp_p2 : p2 !!! Regidx csp_rs1
                     = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite (upd_ne p1 (Regidx s0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hsp_p1. }
    iApply (wp_uk_cldsp γt γd γs γfd h28 p2 (mword_of_int 0x42)
              (mword_of_int 1 : mword 6) s1_idx (uint sp0 - 24)
              (m !!! Regidx s1_idx) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp_p2 Hsp32 Go1; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw3 Hrun").
    { iApply (uis_shk_42 with "Hcode"). }
    iIntros "Hw3".
    assert (E42 : add_vec_int (mword_of_int 0x42 : mword 64) 2
                  = mword_of_int 0x44)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E42. iIntros (h29) "Hrun".
    set (p3 := <[Regidx s1_idx
                 := regval_into_reg (m !!! Regidx s1_idx)]> p2).
    assert (Hsp_p3 : p3 !!! Regidx csp_rs1
                     = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite (upd_ne p2 (Regidx s1_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hsp_p2. }
    iApply (wp_uk_cldsp γt γd γs γfd h29 p3 (mword_of_int 0x44)
              (mword_of_int 0 : mword 6) s2_idx (uint sp0 - 32)
              (m !!! Regidx s2_idx) (12 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp_p3 Hsp32 Go0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw4 Hrun").
    { iApply (uis_shk_44 with "Hcode"). }
    iIntros "Hw4".
    assert (E44 : add_vec_int (mword_of_int 0x44 : mword 64) 2
                  = mword_of_int 0x46)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E44. iIntros (h30) "Hrun".
    set (p4 := <[Regidx s2_idx
                 := regval_into_reg (m !!! Regidx s2_idx)]> p3).
    assert (Hsp_p4 : p4 !!! Regidx csp_rs1
                     = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite (upd_ne p3 (Regidx s2_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hsp_p3. }
    (* ---- 0x46  c.addi16sp sp,sp,32 -- THE POP ---- *)
    assert (HR4 : 0 <= bv_unsigned sp0 < 18446744073709551616).
    { pose proof (bv_unsigned_in_range 64 sp0) as H0.
      assert (Em : bv_modulus 64 = 18446744073709551616)
        by (vm_compute; reflexivity).
      rewrite Em in H0. exact H0. }
    assert (Hlt4 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                   + 8 * Z.of_nat 4 < Z64)
      by (rewrite Hbsp; unfold Z64; lia).
    assert (Hup4 : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                     (8 * Z.of_nat 4) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                 (8 * Z.of_nat 4) ltac:(lia) Hlt4).
      rewrite Hbsp. lia. }
    iApply (wp_uk_caddi16sp_up γt γd γs γfd h30 p4 (mword_of_int 0x46)
              (mword_of_int 2 : mword 6) 4 (12 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hw1 Hw2 Hw3 Hw4] Hrun").
    { iApply (uis_shk_46 with "Hcode"). }
    { rewrite Hsp_p4 Hup4 ustack_4.
      iSplit; [ iPureIntro; exact Hal8 | ].
      iSplitL "Hw1"; [ iExists _; iFrame | ].
      iSplitL "Hw2"; [ iExists _; iFrame | ].
      iSplitL "Hw3"; [ iExists _; iFrame | iExists _; iFrame ]. }
    assert (E46 : add_vec_int (mword_of_int 0x46 : mword 64) 2
                  = mword_of_int 0x48)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp_p4 Hup4 E46. iIntros (h31) "Hrun".
    set (p5 := <[Regidx csp_rs1 := regval_into_reg sp0]> p4).
    assert (Hra_p5 : p5 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite (upd_ne p4 (Regidx csp_rs1) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne p3 (Regidx s2_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne p2 (Regidx s1_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne p1 (Regidx s0_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq nK (Regidx ra_idx)
               (regval_into_reg (m !!! Regidx ra_idx))). }
    (* ---- 0x48  c.jr ra ---- *)
    iApply (wp_uk_cjr γt γd γs γfd h31 p5 (mword_of_int 0x48) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) (4 + (12 + nn))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra_p5; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_48 with "Hcode"). }
    iIntros (h32) "Hrun".
    iApply ("Hcont" with "[Hbs] [] Hrun").
    { iExists gg, i2. iSplit; [ iPureIntro; exact Hgi | iExact "Hbs" ]. }
    iPureIntro. intros r Hr.
    assert (Hcsp2 : uint csp_rs1 = 2) by (vm_compute; reflexivity).
    destruct (Z.eq_dec (uint r) 2) as [Eq1 | Eq1].
    { rewrite (ush_ridx_eq r csp_rs1 ltac:(rewrite Eq1; exact Hcsp2)).
      rewrite Hsp. exact (upd_eq p4 (Regidx csp_rs1) (regval_into_reg sp0)). }
    destruct (Z.eq_dec (uint r) 8) as [Eq2 | Eq2].
    { rewrite (ush_ridx_eq r s0_idx ltac:(rewrite Eq2; vm_compute; reflexivity)).
      rewrite (upd_ne p4 (Regidx csp_rs1) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne p3 (Regidx s2_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne p2 (Regidx s1_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq p1 (Regidx s0_idx)
               (regval_into_reg (m !!! Regidx s0_idx))). }
    destruct (Z.eq_dec (uint r) 9) as [Eq3 | Eq3].
    { rewrite (ush_ridx_eq r s1_idx ltac:(rewrite Eq3; vm_compute; reflexivity)).
      rewrite (upd_ne p4 (Regidx csp_rs1) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne p3 (Regidx s2_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq p2 (Regidx s1_idx)
               (regval_into_reg (m !!! Regidx s1_idx))). }
    destruct (Z.eq_dec (uint r) 18) as [Eq4 | Eq4].
    { rewrite (ush_ridx_eq r s2_idx ltac:(rewrite Eq4; vm_compute; reflexivity)).
      rewrite (upd_ne p4 (Regidx csp_rs1) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq p3 (Regidx s2_idx)
               (regval_into_reg (m !!! Regidx s2_idx))). }
    (* everything else callee-saved is untouched from end to end *)
    assert (Hu : uint r = 3 \/ uint r = 4 \/ (19 <= uint r <= 27)).
    { pose proof (ucs_cases r Hr) as Hc. lia. }
    rewrite (upd_ne p4 (Regidx csp_rs1) (Regidx r) _
               (ush_r_ne r 2 csp_rs1 ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne p3 (Regidx s2_idx) (Regidx r) _
               (ush_r_ne r 18 s2_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne p2 (Regidx s1_idx) (Regidx r) _
               (ush_r_ne r 9 s1_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne p1 (Regidx s0_idx) (Regidx r) _
               (ush_r_ne r 8 s0_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (upd_ne nK (Regidx ra_idx) (Regidx r) _
               (ush_r_ne r 1 ra_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (HnK r (ush_r_ne r 10 a0_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (HnJ r (ush_r_ne r 10 a0_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (HnI r (ush_r_ne r 10 a0_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (HcsG r Hr).
    rewrite (HnH r (ush_r_ne r 1 ra_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (HnG r (ush_r_ne r 10 a0_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (HnF r (ush_r_ne r 11 a1_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (HcsM r Hr).
    rewrite (HnE r (ush_r_ne r 1 ra_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (HnD r (ush_r_ne r 10 a0_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (HnC r (ush_r_ne r 11 a1_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (HnB r (ush_r_ne r 12 a2_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (HnA r (ush_r_ne r 10 a0_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))
               (ush_r_ne r 17 a7_idx ltac:(vm_compute; reflexivity)
                  ltac:(lia))).
    rewrite (Hn9 r (ush_r_ne r 1 ra_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (Hn8 r (ush_r_ne r 10 a0_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (Hn7 r (ush_r_ne r 11 a1_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (Hn6 r (ush_r_ne r 11 a1_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (Hn5 r (ush_r_ne r 12 a2_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (Hn4 r (ush_r_ne r 18 s2_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (Hn3 r (ush_r_ne r 9 s1_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    rewrite (Hn2 r (ush_r_ne r 8 s0_idx ltac:(vm_compute; reflexivity)
                      ltac:(lia))).
    exact (Hn1 r (ush_r_ne r 2 csp_rs1 ltac:(vm_compute; reflexivity)
                    ltac:(lia))).
  Qed.


  (* ===================================================================== *)
  (* THE COMMAND LOOP -- what stage 1 left as the Prop [ush_cmd_head].      *)
  (* DEPENDS ON [ush_read_leaf] (through getcmd).                           *)
  (*                                                                       *)
  (*   for(;;){                                                            *)
  (*     if(getcmd(buf, sizeof(buf)) < 0) break;          <- exit(0)        *)
  (*     while ( *cmd == ' ' || *cmd == '\t') cmd++;                          *)
  (*     if ( *cmd == '\n') continue;                       <- BLANK LINE     *)
  (*     ... the cd builtin, fork1/parsecmd/runcmd ...    <- [ush_rest]     *)
  (*   }                                                                   *)
  (*                                                                       *)
  (* THE INVARIANT IS NO LONGER EMPTY.  Stage 1's console loop carried      *)
  (* nothing round its cycle but the free stack; this one carries the       *)
  (* BUFFER -- [ubytes gd sh_buf 100 f] at an existentially quantified [f]  *)
  (* -- and five register values, [ush_regs], which are the constants       *)
  (* 0x914..0x926 loads once and the loop never rewrites.  That is the      *)
  (* whole invariant: the CONTENTS of the buffer are never carried round,   *)
  (* because getcmd re-establishes from scratch what the next turn needs    *)
  (* (a NUL below 100).                                                     *)
  (*                                                                       *)
  (* THE SCAN TERMINATES ON THE NUL, and that is the one place in the stage *)
  (* where a fact about MEMORY decides control flow.  [while ( *cmd==' ' ||   *)
  (* *cmd=='\t') cmd++] has no bound in the code; what bounds it is gets'   *)
  (* postcondition -- [f i2 = 0] for some [i2 < 100] -- because 0 is        *)
  (* neither a space nor a tab.  The measure is [i2 - k], so the scan is a  *)
  (* bounded Rocq induction (echo's strlen mold) inside an [iLöb].          *)
  (*                                                                       *)
  (* WHERE THE STAGE STOPS.  0x97a hands over to [ush_rest], an abstract    *)
  (* continuation THAT TAKES THE LOOP HEAD as its own premise: the rest of  *)
  (* main's body ends by falling back into 0x938 (fork1's parent arm does,  *)
  (* and so does the cd builtin), so the two are mutually recursive and the *)
  (* honest cut is a premise that says so.  Stage 4/5 discharge it; nothing *)
  (* here assumes anything about it.                                        *)
  (* ===================================================================== *)

  (* the five constants 0x914..0x926 loads and the loop preserves *)
  Definition ush_regs (m : regfile) : Prop :=
    m !!! Regidx s2_idx = mword_of_int sh_buf /\
    m !!! Regidx s3_idx = mword_of_int 100 /\
    m !!! Regidx s4_idx = mword_of_int 10 /\
    m !!! Regidx s5_idx = mword_of_int 99 /\
    m !!! Regidx s6_idx = mword_of_int 32.

  (* a register OUTSIDE s2..s6 -- which is every one the loop body writes *)
  Definition ush_reg_free (r : mword 5) : bool :=
    let z := uint r in negb ((18 <=? z) && (z <=? 22)).

  Local Lemma ush_regs_upd (m : regfile) (r : mword 5) (v : mword 64) :
    ush_regs m -> ush_reg_free r = true -> ush_regs (<[Regidx r := v]> m).
  Proof.
    intros (H2 & H3 & H4 & H5 & H6) Hf.
    unfold ush_reg_free in Hf. apply negb_true_iff in Hf.
    assert (Hne : forall (q : mword 5) (z : Z), uint q = z -> 18 <= z <= 22 ->
                    Regidx q <> Regidx r).
    { intros q z Hq Hz. apply ush_ridx_ne. rewrite Hq. intro He.
      apply andb_false_iff in Hf. destruct Hf as [Hf | Hf];
        apply Z.leb_gt in Hf; lia. }
    split_and!.
    - rewrite (upd_ne m (Regidx r) (Regidx s2_idx) v
                 (Hne s2_idx 18 ltac:(vm_compute; reflexivity) ltac:(lia))).
      exact H2.
    - rewrite (upd_ne m (Regidx r) (Regidx s3_idx) v
                 (Hne s3_idx 19 ltac:(vm_compute; reflexivity) ltac:(lia))).
      exact H3.
    - rewrite (upd_ne m (Regidx r) (Regidx s4_idx) v
                 (Hne s4_idx 20 ltac:(vm_compute; reflexivity) ltac:(lia))).
      exact H4.
    - rewrite (upd_ne m (Regidx r) (Regidx s5_idx) v
                 (Hne s5_idx 21 ltac:(vm_compute; reflexivity) ltac:(lia))).
      exact H5.
    - rewrite (upd_ne m (Regidx r) (Regidx s6_idx) v
                 (Hne s6_idx 22 ltac:(vm_compute; reflexivity) ltac:(lia))).
      exact H6.
  Qed.

  Local Lemma ush_regs_cs (m m' : regfile) :
    ush_regs m -> ucallee_saved m m' -> ush_regs m'.
  Proof.
    intros (H2 & H3 & H4 & H5 & H6) Hcs. split_and!.
    - rewrite (Hcs s2_idx ltac:(vm_compute; reflexivity)). exact H2.
    - rewrite (Hcs s3_idx ltac:(vm_compute; reflexivity)). exact H3.
    - rewrite (Hcs s4_idx ltac:(vm_compute; reflexivity)). exact H4.
    - rewrite (Hcs s5_idx ltac:(vm_compute; reflexivity)). exact H5.
    - rewrite (Hcs s6_idx ltac:(vm_compute; reflexivity)). exact H6.
  Qed.

  (* the loop head, and the abstract rest of main's body ------------------ *)
  Definition ush_loop_head : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (f : nat -> bv 8) (n : nat),
       ⌜ ush_regs m ⌝ -∗
       ubytes γd sh_buf sh_nbuf f -∗
       urun γt γd γs γfd h m (mword_of_int 0x938) (16 + n) -∗
       WP (Loop : expr riscv_lang))%I.

  Definition ush_rest : iProp Σ :=
    (□ (ush_loop_head -∗
        ∀ (h : CpuId) (m : regfile) (f : nat -> bv 8) (k i2 : nat) (n : nat),
          ⌜ ush_regs m ⌝ -∗
          ⌜ m !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k) ⌝ -∗
          ⌜ m !!! Regidx a5_idx = mword_of_int (bv_unsigned (f k)) ⌝ -∗
          ⌜ (k <= i2 < sh_nbuf)%nat /\ f i2 = ubyte0 ⌝ -∗
          ubytes γd sh_buf sh_nbuf f -∗
          urun γt γd γs γfd h m (mword_of_int 0x97a) (16 + n) -∗
          WP (Loop : expr riscv_lang)))%I.

  Global Instance ush_rest_persistent : Persistent ush_rest.
  Proof. apply _. Qed.

  (* ---- ONE TURN of the leading-blank scan, 0x964..0x974 ---------------- *)
  (*   c.addi s1,1 ; lbu a5,0(s1) ; addi a4,a5,-32 ; c.beqz a4,0x964        *)
  (*   addi a4,a5,-9 ; c.beqz a4,0x964                                      *)
  (* s1 points AT the byte just tested on entry and one past it on exit;    *)
  (* the byte decides where control goes, and the caller says which target  *)
  (* it expects.  (UkEcho.v's [wp_kecho_strlen_step] is the mold.)          *)
  Local Lemma wp_ksh_scan_step (h : CpuId) (mc : regfile) (k : nat)
      (b : mword 8) (bz : Z) (tgt : mword 64) (n : nat) :
    bv_unsigned b = bz ->
    ush_regs mc ->
    mc !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k) ->
    0 <= sh_buf + Z.of_nat (k + 1) < Z64 ->
    tgt = (if (bz =? 32) || (bz =? 9)
           then mword_of_int 0x964 else mword_of_int 0x976) ->
    shk_code γt -∗
    ubyteq γd (DfracOwn 1) (sh_buf + Z.of_nat (k + 1)) b -∗
    urun γt γd γs γfd h mc (mword_of_int 0x964) (16 + n) -∗
    (ubyteq γd (DfracOwn 1) (sh_buf + Z.of_nat (k + 1)) b -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ ush_regs mc' ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx
             = mword_of_int (sh_buf + Z.of_nat (k + 1)) ⌝ -∗
         ⌜ mc' !!! Regidx a5_idx = mword_of_int bz ⌝ -∗
         urun γt γd γs γfd h' mc' tgt (16 + n) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hbz Hregs Hs1 Hrng Htgt. iIntros "#Hcode Hb Hrun Hcont".
    assert (Hbzr : 0 <= bz < 256).
    { rewrite <- Hbz. pose proof (bv_unsigned_in_range 8 b) as Hr8.
      assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
      rewrite Em8 in Hr8. exact Hr8. }
    (* ---- 0x964  c.addi s1,s1,1 ---- *)
    assert (E1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                 = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi γt γd γs γfd h mc (mword_of_int 0x964)
              (mword_of_int 1 : mword 6) s1_idx
              (mword_of_int (sh_buf + Z.of_nat (k + 1))) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1 E1 moi_add;
                    replace (sh_buf + Z.of_nat (k + 1))
                      with (sh_buf + Z.of_nat k + 1) by lia; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_964 with "Hcode"). }
    assert (E964 : add_vec_int (mword_of_int 0x964 : mword 64) 2
                   = mword_of_int 0x966)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E964. iIntros (h1) "Hrun".
    set (m1 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int (sh_buf + Z.of_nat (k + 1))
                                     : mword 64)]> mc).
    assert (Hs1_1 : m1 !!! Regidx s1_idx
                    = mword_of_int (sh_buf + Z.of_nat (k + 1)))
      by exact (upd_eq mc (Regidx s1_idx)
                  (regval_into_reg (mword_of_int (sh_buf + Z.of_nat (k + 1))
                                    : mword 64))).
    assert (Hreg1 : ush_regs m1)
      by exact (ush_regs_upd mc s1_idx _ Hregs ltac:(vm_compute; reflexivity)).
    (* ---- 0x966  lbu a5,0(s1) ---- *)
    iApply (wp_uk_lbu γt γd γs γfd h1 m1 (mword_of_int 0x966)
              (mword_of_int 0 : mword 12) s1_idx a5_idx (DfracOwn 1)
              (sh_buf + Z.of_nat (k + 1)) b (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1_1
                      (uint_moi (sh_buf + Z.of_nat (k + 1)) Hrng);
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shk_966 with "Hcode"). }
    iIntros "Hb".
    assert (E966 : add_vec_int (mword_of_int 0x966 : mword 64) 4
                   = mword_of_int 0x96a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E966. iIntros (h2) "Hrun".
    set (m2 := <[Regidx a5_idx
                 := regval_into_reg (zero_extend' 64 b : mword 64)]> m1).
    assert (Ha5_2 : m2 !!! Regidx a5_idx = mword_of_int bz).
    { rewrite (upd_eq m1 (Regidx a5_idx)
                 (regval_into_reg (zero_extend' 64 b : mword 64))).
      rewrite <- Hbz. exact (zext8_moi b). }
    assert (Hreg2 : ush_regs m2)
      by exact (ush_regs_upd m1 a5_idx _ Hreg1 ltac:(vm_compute; reflexivity)).
    assert (Hs1_2 : m2 !!! Regidx s1_idx
                    = mword_of_int (sh_buf + Z.of_nat (k + 1))).
    { rewrite (upd_ne m1 (Regidx a5_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)). exact Hs1_1. }
    (* ---- 0x96a  addi a4,a5,-32 ---- *)
    iApply (wp_uk_addi γt γd γs γfd h2 m2 (mword_of_int 0x96a)
              (mword_of_int 4064 : mword 12) a5_idx a4_idx
              (mword_of_int (bz - 32)) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_2;
                    exact (ush_addi_sub bz 32 (mword_of_int 4064 : mword 12)
                             ltac:(unfold Z64; lia)
                             ltac:(vm_compute; reflexivity)))
              with "[] Hrun").
    { iApply (uis_shk_96a with "Hcode"). }
    assert (E96a : add_vec_int (mword_of_int 0x96a : mword 64) 4
                   = mword_of_int 0x96e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E96a. iIntros (h3) "Hrun".
    set (m3 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int (bz - 32) : mword 64)]> m2).
    assert (Ha4_3 : m3 !!! Regidx a4_idx = mword_of_int (bz - 32))
      by exact (upd_eq m2 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int (bz - 32) : mword 64))).
    assert (Hreg3 : ush_regs m3)
      by exact (ush_regs_upd m2 a4_idx _ Hreg2 ltac:(vm_compute; reflexivity)).
    assert (Hs1_3 : m3 !!! Regidx s1_idx
                    = mword_of_int (sh_buf + Z.of_nat (k + 1))).
    { rewrite (upd_ne m2 (Regidx a4_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)). exact Hs1_2. }
    assert (Ha5_3 : m3 !!! Regidx a5_idx = mword_of_int bz).
    { rewrite (upd_ne m2 (Regidx a4_idx) (Regidx a5_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha5_2. }
    (* ---- 0x96e  c.beqz a4,0x964 -- a SPACE goes round ---- *)
    assert (Htk32 : Z.eqb bz 32 = eq_vec (m3 !!! Regidx a4_idx) zero_reg).
    { rewrite Ha4_3. symmetry.
      exact (ush_eqz_sub bz 32 ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)). }
    iApply (wp_uk_cbeqz γt γd γs γfd h3 m3 (mword_of_int 0x96e)
              (mword_of_int 251 : mword 8) (mword_of_int 6 : mword 3)
              a4_idx (Z.eqb bz 32) (mword_of_int 0x964) (16 + n)
              ltac:(vm_compute; reflexivity) Htk32
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_96e with "Hcode"). }
    destruct (Z.eqb_spec bz 32) as [Hb32 | Hb32].
    { iIntros (h4) "Hrun".
      assert (Htg32 : tgt = mword_of_int 0x964).
      { rewrite Htgt; try (rewrite Hb32); try (rewrite Hb9);
          vm_compute; reflexivity. }
      iSpecialize ("Hcont" with "Hb").
      iApply ("Hcont" $! h4 m3 with "[] [] [] [Hrun]").
      - iPureIntro. exact Hreg3.
      - iPureIntro. exact Hs1_3.
      - iPureIntro. exact Ha5_3.
      - rewrite Htg32. iExact "Hrun". }
    assert (E96e : add_vec_int (mword_of_int 0x96e : mword 64) 2
                   = mword_of_int 0x970)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E96e. iIntros (h4) "Hrun".
    (* ---- 0x970  addi a4,a5,-9 ---- *)
    iApply (wp_uk_addi γt γd γs γfd h4 m3 (mword_of_int 0x970)
              (mword_of_int 4087 : mword 12) a5_idx a4_idx
              (mword_of_int (bz - 9)) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_3;
                    exact (ush_addi_sub bz 9 (mword_of_int 4087 : mword 12)
                             ltac:(unfold Z64; lia)
                             ltac:(vm_compute; reflexivity)))
              with "[] Hrun").
    { iApply (uis_shk_970 with "Hcode"). }
    assert (E970 : add_vec_int (mword_of_int 0x970 : mword 64) 4
                   = mword_of_int 0x974)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E970. iIntros (h5) "Hrun".
    set (m4 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int (bz - 9) : mword 64)]> m3).
    assert (Ha4_4 : m4 !!! Regidx a4_idx = mword_of_int (bz - 9))
      by exact (upd_eq m3 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int (bz - 9) : mword 64))).
    assert (Hreg4 : ush_regs m4)
      by exact (ush_regs_upd m3 a4_idx _ Hreg3 ltac:(vm_compute; reflexivity)).
    assert (Hs1_4 : m4 !!! Regidx s1_idx
                    = mword_of_int (sh_buf + Z.of_nat (k + 1))).
    { rewrite (upd_ne m3 (Regidx a4_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)). exact Hs1_3. }
    assert (Ha5_4 : m4 !!! Regidx a5_idx = mword_of_int bz).
    { rewrite (upd_ne m3 (Regidx a4_idx) (Regidx a5_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha5_3. }
    assert (Htk9 : Z.eqb bz 9 = eq_vec (m4 !!! Regidx a4_idx) zero_reg).
    { rewrite Ha4_4. symmetry.
      exact (ush_eqz_sub bz 9 ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)). }
    iApply (wp_uk_cbeqz γt γd γs γfd h5 m4 (mword_of_int 0x974)
              (mword_of_int 248 : mword 8) (mword_of_int 6 : mword 3)
              a4_idx (Z.eqb bz 9) (mword_of_int 0x964) (16 + n)
              ltac:(vm_compute; reflexivity) Htk9
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_974 with "Hcode"). }
    assert (E974 : add_vec_int (mword_of_int 0x974 : mword 64) 2
                   = mword_of_int 0x976)
      by (apply bv_eq; vm_compute; reflexivity).
    destruct (Z.eqb_spec bz 9) as [Hb9 | Hb9].
    { iIntros (h6) "Hrun".
      assert (Htg9 : tgt = mword_of_int 0x964).
      { rewrite Htgt; try (rewrite Hb32); try (rewrite Hb9);
          vm_compute; reflexivity. }
      iSpecialize ("Hcont" with "Hb").
      iApply ("Hcont" $! h6 m4 with "[] [] [] [Hrun]").
      - iPureIntro. exact Hreg4.
      - iPureIntro. exact Hs1_4.
      - iPureIntro. exact Ha5_4.
      - rewrite Htg9. iExact "Hrun". }
    iIntros (h6) "Hrun".
    assert (Htg0 : tgt = mword_of_int 0x976).
    { rewrite Htgt; try (rewrite Hb32); try (rewrite Hb9);
        vm_compute; reflexivity. }
    iSpecialize ("Hcont" with "Hb").
    iApply ("Hcont" $! h6 m4 with "[] [] [] [Hrun]").
    - iPureIntro. exact Hreg4.
    - iPureIntro. exact Hs1_4.
    - iPureIntro. exact Ha5_4.
    - rewrite E974 Htg0. iExact "Hrun".
  Qed.


  (* ---- the scan as a whole, 0x964..0x974 under the NUL's measure ------- *)
  Local Lemma wp_ksh_scan (f : nat -> bv 8) (i2 : nat) :
    forall (d k : nat) (h : CpuId) (mc : regfile) (n : nat),
    (i2 = k + 1 + d)%nat -> (i2 < sh_nbuf)%nat -> f i2 = ubyte0 ->
    ush_regs mc ->
    mc !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k) ->
    shk_code γt -∗
    ubytes γd sh_buf sh_nbuf f -∗
    urun γt γd γs γfd h mc (mword_of_int 0x964) (16 + n) -∗
    (∀ (h' : CpuId) (mc' : regfile) (k' : nat),
       ⌜ (k' <= i2)%nat ⌝ -∗
       ⌜ ush_regs mc' ⌝ -∗
       ⌜ mc' !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k') ⌝ -∗
       ⌜ mc' !!! Regidx a5_idx = mword_of_int (bv_unsigned (f k')) ⌝ -∗
       ubytes γd sh_buf sh_nbuf f -∗
       urun γt γd γs γfd h' mc' (mword_of_int 0x976) (16 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    assert (Hbf : sh_buf = 8224) by (vm_compute; reflexivity).
    assert (Hnb : sh_nbuf = 100%nat) by (vm_compute; reflexivity).
    intros d. induction d as [| d IH ];
      intros k h mc n Hi2 Hlt Hnul Hregs Hs1;
      iIntros "#Hcode Hbs Hrun Hcont";
      assert (Hk1lt : (k + 1 < sh_nbuf)%nat) by lia;
      assert (Hrng : 0 <= sh_buf + Z.of_nat (k + 1) < Z64)
        by (rewrite Hbf; rewrite Hnb in Hk1lt; unfold Z64; lia);
      iDestruct (ush_bytes_at (DfracOwn 1) sh_buf sh_nbuf (k + 1)%nat f Hk1lt
                   with "Hbs") as "[Hb Hcl]".
    - (* the byte AT k+1 IS the NUL: neither test fires, the scan ends *)
      assert (Hbz0 : bv_unsigned (f (k + 1)%nat) = 0)
        by (replace (k + 1)%nat with i2 by lia; rewrite Hnul;
            vm_compute; reflexivity).
      iApply (wp_ksh_scan_step h mc k (f (k + 1)%nat) 0
                (mword_of_int 0x976) n Hbz0 Hregs Hs1 Hrng
                ltac:(vm_compute; reflexivity)
                with "Hcode Hb Hrun").
      iIntros "Hb" (h1 mc') "%Hr %Hs %Ha Hrun".
      iDestruct ("Hcl" with "Hb") as "Hbs".
      iApply ("Hcont" $! h1 mc' (k + 1)%nat with "[] [] [] [] Hbs Hrun");
        iPureIntro; [ lia | exact Hr | exact Hs | rewrite Hbz0; exact Ha ].
    - remember ((bv_unsigned (f (k + 1)%nat) =? 32)
                || (bv_unsigned (f (k + 1)%nat) =? 9))%bool as blank eqn:Hbl.
      destruct blank.
      + (* a blank: round again at k+1, one closer to the NUL *)
        iApply (wp_ksh_scan_step h mc k (f (k + 1)%nat)
                  (bv_unsigned (f (k + 1)%nat)) (mword_of_int 0x964) n
                  eq_refl Hregs Hs1 Hrng
                  ltac:(rewrite <- Hbl; reflexivity)
                  with "Hcode Hb Hrun").
        iIntros "Hb" (h1 mc') "%Hr %Hs %Ha Hrun".
        iDestruct ("Hcl" with "Hb") as "Hbs".
        iApply (IH (k + 1)%nat h1 mc' n ltac:(lia) Hlt Hnul Hr Hs
                  with "Hcode Hbs Hrun").
        iIntros (h2 mc'' k') "%Hk' %Hr' %Hs' %Ha' Hbs Hrun".
        iApply ("Hcont" $! h2 mc'' k' with "[] [] [] [] Hbs Hrun");
          iPureIntro; [ exact Hk' | exact Hr' | exact Hs' | exact Ha' ].
      + (* not a blank: the scan ends here *)
        iApply (wp_ksh_scan_step h mc k (f (k + 1)%nat)
                  (bv_unsigned (f (k + 1)%nat)) (mword_of_int 0x976) n
                  eq_refl Hregs Hs1 Hrng
                  ltac:(rewrite <- Hbl; reflexivity)
                  with "Hcode Hb Hrun").
        iIntros "Hb" (h1 mc') "%Hr %Hs %Ha Hrun".
        iDestruct ("Hcl" with "Hb") as "Hbs".
        iApply ("Hcont" $! h1 mc' (k + 1)%nat with "[] [] [] [] Hbs Hrun");
          iPureIntro; [ lia | exact Hr | exact Hs | exact Ha ].
  Qed.

  (* ---- 0x9ca  the loop's only exit: exit(0) --------------------------- *)
  Local Lemma wp_ksh_die (h : CpuId) (mc : regfile) (n : nat) :
    shk_code γt -∗
    urun γt γd γs γfd h mc (mword_of_int 0x9ca) n -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun".
    iApply (wp_uk_cli γt γd γs γfd h mc (mword_of_int 0x9ca)
              (mword_of_int 0 : mword 6) a0_idx n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_9ca with "Hcode"). }
    assert (E9ca : add_vec_int (mword_of_int 0x9ca : mword 64) 2
                   = mword_of_int 0x9cc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E9ca. iIntros (h1) "Hrun".
    set (q := <[Regidx a0_idx
                := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 6)
                                    : mword 64)]> mc).
    iApply (wp_uk_jal γt γd γs γfd h1 q (mword_of_int 0x9cc)
              (mword_of_int 698 : mword 21) ra_idx
              (mword_of_int ShSyms.exit) (mword_of_int 0x9d0) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite shp_exit; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite shp_exit; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_9cc with "Hcode"). }
    iIntros (h2) "Hrun".
    iApply (wp_ksh_exit h2 _ n with "Hcode Hrun").
  Qed.


  (* ---- 0x95c/0x960  both ways into the scan land s1 on the buffer ----- *)
  Local Lemma wp_ksh_blank_entry (h : CpuId) (mc : regfile) (g : nat -> bv 8)
      (i2 n : nat) :
    ush_regs mc -> (0 < i2)%nat -> (i2 < sh_nbuf)%nat -> g i2 = ubyte0 ->
    shk_code γt -∗
    (∀ (hh : CpuId) (mm : regfile) (kk : nat),
       ⌜ ush_regs mm ⌝ -∗ ⌜ (kk <= i2)%nat ⌝ -∗
       ⌜ mm !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat kk) ⌝ -∗
       ⌜ mm !!! Regidx a5_idx = mword_of_int (bv_unsigned (g kk)) ⌝ -∗
       ubytes γd sh_buf sh_nbuf g -∗
       urun γt γd γs γfd hh mm (mword_of_int 0x976) (16 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    ubytes γd sh_buf sh_nbuf g -∗
    urun γt γd γs γfd h mc (mword_of_int 0x95c) (16 + n) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hregs Hi20 Hi2lt Hnul. iIntros "#Hcode Htail Hbs Hrun".
    iApply (wp_uk_auipc γt γd γs γfd h mc (mword_of_int 0x95c)
              (mword_of_int 1 : mword 20) s1_idx
              (add_vec (mword_of_int 0x95c : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20))) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_95c with "Hcode"). }
    assert (E95c : add_vec_int (mword_of_int 0x95c : mword 64) 4
                   = mword_of_int 0x960)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E95c. iIntros (h1) "Hrun".
    set (q1 := <[Regidx s1_idx
                 := regval_into_reg
                      (add_vec (mword_of_int 0x95c : mword 64)
                         (auipc_off (mword_of_int 1 : mword 20)))]> mc).
    assert (Hq1 : ush_regs q1)
      by exact (ush_regs_upd mc s1_idx _ Hregs ltac:(vm_compute; reflexivity)).
    iApply (wp_uk_addi γt γd γs γfd h1 q1 (mword_of_int 0x960)
              (mword_of_int 1732 : mword 12) s1_idx s1_idx
              (mword_of_int sh_buf) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq mc (Regidx s1_idx)
                               (regval_into_reg
                                  (add_vec (mword_of_int 0x95c : mword 64)
                                     (auipc_off (mword_of_int 1 : mword 20)))));
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_960 with "Hcode"). }
    assert (E960 : add_vec_int (mword_of_int 0x960 : mword 64) 4
                   = mword_of_int 0x964)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E960. iIntros (h2) "Hrun".
    set (q2 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int sh_buf : mword 64)]> q1).
    assert (Hq2 : ush_regs q2)
      by exact (ush_regs_upd q1 s1_idx _ Hq1 ltac:(vm_compute; reflexivity)).
    assert (Hs1_2 : q2 !!! Regidx s1_idx
                    = mword_of_int (sh_buf + Z.of_nat 0)).
    { replace (sh_buf + Z.of_nat 0) with sh_buf by lia.
      exact (upd_eq q1 (Regidx s1_idx)
               (regval_into_reg (mword_of_int sh_buf : mword 64))). }
    iApply (wp_ksh_scan g i2 (i2 - 1)%nat 0%nat h2 q2 n ltac:(lia) Hi2lt Hnul
              Hq2 Hs1_2 with "Hcode Hbs Hrun").
    iIntros (h3 mc' k') "%Hk' %Hr' %Hs' %Ha' Hbs Hrun".
    iApply ("Htail" $! h3 mc' k' with "[] [] [] [] Hbs Hrun");
      iPureIntro; [ exact Hr' | exact Hk' | exact Hs' | exact Ha' ].
  Qed.

  (* ---- the loop itself: 0x938..0x976, under one iLöb ------------------ *)
  (* DEPENDS ON [ush_read_leaf] (through getcmd).                          *)
  Local Lemma wp_ksh_loop : ush_rest -∗ shk_code γt -∗ ush_loop_head.
  Proof.
    assert (Hbf : sh_buf = 8224) by (vm_compute; reflexivity).
    assert (Hnb : sh_nbuf = 100%nat) by (vm_compute; reflexivity).
    assert (Hnbz : Z.of_nat sh_nbuf = 100) by (vm_compute; reflexivity).
    iIntros "#Hrest #Hcode".
    iLöb as "IH".
    iIntros (h m f n) "%Hregs Hbs Hrun".
    pose proof Hregs as (Hs2 & Hs3 & Hs4 & Hs5 & Hs6).
    (* ---- 0x938  c.mv a1,s3 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h m (mword_of_int 0x938) a1_idx s3_idx
              (mword_of_int 100) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_938 with "Hcode"). }
    assert (E938 : add_vec_int (mword_of_int 0x938 : mword 64) 2
                   = mword_of_int 0x93a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E938. iIntros (h1) "Hrun".
    set (m1 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int 100 : mword 64)]> m).
    assert (Hr1 : ush_regs m1)
      by exact (ush_regs_upd m a1_idx _ Hregs ltac:(vm_compute; reflexivity)).
    assert (Ha1_1 : m1 !!! Regidx a1_idx = mword_of_int 100)
      by exact (upd_eq m (Regidx a1_idx)
                  (regval_into_reg (mword_of_int 100 : mword 64))).
    pose proof Hr1 as (Hs2_1 & _ & _ & _ & _).
    (* ---- 0x93a  c.mv a0,s2 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h1 m1 (mword_of_int 0x93a) a0_idx s2_idx
              (mword_of_int sh_buf) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs2_1 moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_93a with "Hcode"). }
    assert (E93a : add_vec_int (mword_of_int 0x93a : mword 64) 2
                   = mword_of_int 0x93c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E93a. iIntros (h2) "Hrun".
    set (m2 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int sh_buf : mword 64)]> m1).
    assert (Hr2 : ush_regs m2)
      by exact (ush_regs_upd m1 a0_idx _ Hr1 ltac:(vm_compute; reflexivity)).
    assert (Ha0_2 : m2 !!! Regidx a0_idx = mword_of_int sh_buf)
      by exact (upd_eq m1 (Regidx a0_idx)
                  (regval_into_reg (mword_of_int sh_buf : mword 64))).
    assert (Ha1_2 : m2 !!! Regidx a1_idx = mword_of_int 100).
    { rewrite (upd_ne m1 (Regidx a0_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha1_1. }
    (* ---- 0x93c  jal ra,0x0 <getcmd> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h2 m2 (mword_of_int 0x93c)
              (mword_of_int 2094788 : mword 21) ra_idx
              (mword_of_int ShSyms.getcmd) (mword_of_int 0x940) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite shp_getcmd; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite shp_getcmd; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_93c with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x940 : mword 64)]> m2).
    assert (Hr3 : ush_regs m3)
      by exact (ush_regs_upd m2 ra_idx _ Hr2 ltac:(vm_compute; reflexivity)).
    assert (Hra3 : m3 !!! Regidx ra_idx = mword_of_int 0x940)
      by exact (upd_eq m2 (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0x940 : mword 64))).
    assert (Ha0_3 : m3 !!! Regidx a0_idx = mword_of_int sh_buf).
    { rewrite (upd_ne m2 (Regidx ra_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha0_2. }
    assert (Ha1_3 : m3 !!! Regidx a1_idx = mword_of_int (Z.of_nat sh_nbuf)).
    { rewrite Hnbz.
      rewrite (upd_ne m2 (Regidx ra_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha1_2. }
    replace (16 + n)%nat with (4 + (12 + n))%nat by lia.
    iApply (wp_ksh_getcmd h3 m3 sh_buf sh_nbuf f n Ha0_3 Ha1_3
              ltac:(rewrite Hnb; lia) ltac:(rewrite Hnbz; unfold Z31; lia)
              with "Hcode Hbs Hrun").
    iIntros "Hbs" (h4 mR) "%HcsR Hrun".
    replace (4 + (12 + n))%nat with (16 + n)%nat by lia.
    rewrite Hra3.
    assert (Er940 : ret_pc (mword_of_int 0x940 : mword 64) = mword_of_int 0x940)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Er940.
    iDestruct "Hbs" as (g i2) "[%Hgi Hbs]".
    destruct Hgi as [Hi2lt Hnul].
    assert (HrR : ush_regs mR) by exact (ush_regs_cs m3 mR Hr3 HcsR).
    pose proof HrR as (Hs2_R & Hs3_R & Hs4_R & Hs5_R & Hs6_R).
    (* ---- 0x940  bltz a0,0x9ca -- an ABSTRACT split ---- *)
    remember (uv_btaken BLT (mR !!! Regidx a0_idx) zero_reg) as tk40 eqn:Htk40.
    iApply (wp_uk_btype0 γt γd γs γfd h4 mR (mword_of_int 0x940)
              (mword_of_int 138 : mword 13) a0_idx BLT tk40
              (mword_of_int 0x9ca) (16 + n)
              Htk40
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_940 with "Hcode"). }
    destruct tk40.
    { iIntros (h5) "Hrun". iApply (wp_ksh_die h5 mR (16 + n) with "Hcode Hrun"). }
    assert (E940 : add_vec_int (mword_of_int 0x940 : mword 64) 4
                   = mword_of_int 0x944)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E940. iIntros (h5) "Hrun".
    (* ---- 0x944  lbu a5,0(s2) -- the FIRST byte of the line ---- *)
    set (bz0 := bv_unsigned (g 0%nat)).
    assert (Hbz0r : 0 <= bz0 < 256).
    { unfold bz0. pose proof (bv_unsigned_in_range 8 (g 0%nat)) as Hr8.
      assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
      rewrite Em8 in Hr8. exact Hr8. }
    iDestruct (ush_bytes_at (DfracOwn 1) sh_buf sh_nbuf 0%nat g
                 ltac:(rewrite Hnb; lia) with "Hbs") as "[Hb Hcl]".
    rewrite Z.add_0_r.
    iApply (wp_uk_lbu γt γd γs γfd h5 mR (mword_of_int 0x944)
              (mword_of_int 0 : mword 12) s2_idx a5_idx (DfracOwn 1)
              sh_buf (g 0%nat) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs2_R (uint_moi sh_buf
                                     ltac:(rewrite Hbf; unfold Z64; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shk_944 with "Hcode"). }
    iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hbs".
    assert (E944 : add_vec_int (mword_of_int 0x944 : mword 64) 4
                   = mword_of_int 0x948)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E944. iIntros (h6) "Hrun".
    set (m4 := <[Regidx a5_idx
                 := regval_into_reg (zero_extend' 64 (g 0%nat : mword 8)
                                     : mword 64)]> mR).
    assert (Hr4 : ush_regs m4)
      by exact (ush_regs_upd mR a5_idx _ HrR ltac:(vm_compute; reflexivity)).
    assert (Ha5_4 : m4 !!! Regidx a5_idx = mword_of_int bz0).
    { rewrite (upd_eq mR (Regidx a5_idx)
                 (regval_into_reg (zero_extend' 64 (g 0%nat : mword 8)
                                   : mword 64))).
      exact (zext8_moi (g 0%nat)). }
    (* ---- 0x948  addi a4,a5,-32 ---- *)
    iApply (wp_uk_addi γt γd γs γfd h6 m4 (mword_of_int 0x948)
              (mword_of_int 4064 : mword 12) a5_idx a4_idx
              (mword_of_int (bz0 - 32)) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_4;
                    exact (ush_addi_sub bz0 32 (mword_of_int 4064 : mword 12)
                             ltac:(unfold Z64; lia)
                             ltac:(vm_compute; reflexivity)))
              with "[] Hrun").
    { iApply (uis_shk_948 with "Hcode"). }
    assert (E948 : add_vec_int (mword_of_int 0x948 : mword 64) 4
                   = mword_of_int 0x94c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E948. iIntros (h7) "Hrun".
    set (m5 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int (bz0 - 32) : mword 64)]> m4).
    assert (Hr5 : ush_regs m5)
      by exact (ush_regs_upd m4 a4_idx _ Hr4 ltac:(vm_compute; reflexivity)).
    assert (Ha4_5 : m5 !!! Regidx a4_idx = mword_of_int (bz0 - 32))
      by exact (upd_eq m4 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int (bz0 - 32) : mword 64))).
    assert (Ha5_5 : m5 !!! Regidx a5_idx = mword_of_int bz0).
    { rewrite (upd_ne m4 (Regidx a4_idx) (Regidx a5_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha5_4. }
    (* ---- 0x94c  c.beqz a4,0x95c -- a leading SPACE ---- *)
    assert (Htk4c : Z.eqb bz0 32 = eq_vec (m5 !!! Regidx a4_idx) zero_reg).
    { rewrite Ha4_5. symmetry.
      exact (ush_eqz_sub bz0 32 ltac:(unfold Z64; lia)
               ltac:(unfold Z64; lia)). }
    iApply (wp_uk_cbeqz γt γd γs γfd h7 m5 (mword_of_int 0x94c)
              (mword_of_int 8 : mword 8) (mword_of_int 6 : mword 3) a4_idx
              (Z.eqb bz0 32) (mword_of_int 0x95c) (16 + n)
              ltac:(vm_compute; reflexivity) Htk4c
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_94c with "Hcode"). }
    (* the two ways into the scan and the one way past it all reconverge on
       a shared tail, so state it once *)
    iAssert (□ (∀ (hh : CpuId) (mm : regfile) (kk : nat),
                  ⌜ ush_regs mm ⌝ -∗
                  ⌜ (kk <= i2)%nat ⌝ -∗
                  ⌜ mm !!! Regidx s1_idx
                      = mword_of_int (sh_buf + Z.of_nat kk) ⌝ -∗
                  ⌜ mm !!! Regidx a5_idx
                      = mword_of_int (bv_unsigned (g kk)) ⌝ -∗
                  ubytes γd sh_buf sh_nbuf g -∗
                  urun γt γd γs γfd hh mm (mword_of_int 0x976) (16 + n) -∗
                  WP (Loop : expr riscv_lang)))%I as "#Htail".
    { iModIntro. iIntros (hh mm kk) "%Hrm %Hkk %Hsm %Ham Hbs Hrun".
      pose proof Hrm as (_ & _ & Hs4m & _ & _).
      remember (uv_btaken BEQ (mm !!! Regidx a5_idx) (mm !!! Regidx s4_idx))
        as tk76 eqn:Htk76.
      iApply (UkRunLeaf.wp_uk_btype_later γt γd γs γfd hh mm (mword_of_int 0x976)
                (mword_of_int 8130 : mword 13) s4_idx a5_idx BEQ tk76
                (mword_of_int 0x938) (16 + n)
                Htk76
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_976 with "Hcode"). }
      destruct tk76.
      { (* a blank line: round the command loop again *)
        iNext. iIntros (hh1) "Hrun".
        iApply ("IH" $! hh1 mm g n with "[] Hbs Hrun").
        iPureIntro. exact Hrm. }
      iNext.
      assert (E976 : add_vec_int (mword_of_int 0x976 : mword 64) 4
                     = mword_of_int 0x97a)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E976. iIntros (hh1) "Hrun".
      iDestruct ("Hrest" with "IH") as "Hbody".
      iApply ("Hbody" $! hh1 mm g kk i2 n with "[] [] [] [] Hbs Hrun");
        iPureIntro; [ exact Hrm | exact Hsm | exact Ham
                    | split; [ lia | exact Hnul ] ]. }
    (* the two auipc/addi pairs that both land s1 on the buffer *)
    destruct (Z.eqb_spec bz0 32) as [Hb32 | Hb32].
    { (* leading space: straight to 0x95c *)
      iIntros (h8) "Hrun".
      assert (Hi20 : (0 < i2)%nat).
      { destruct (Nat.eq_dec i2 0) as [Hz | Hne]; [ | lia ].
        exfalso. unfold bz0 in Hb32. rewrite Hz in Hnul.
        rewrite Hnul in Hb32. vm_compute in Hb32. discriminate Hb32. }
      iApply (wp_ksh_blank_entry h8 m5 g i2 n Hr5 Hi20 Hi2lt Hnul
                with "Hcode Htail Hbs Hrun"). }
    assert (E94c : add_vec_int (mword_of_int 0x94c : mword 64) 2
                   = mword_of_int 0x94e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E94c. iIntros (h8) "Hrun".
    (* ---- 0x94e  addi a4,a5,-9 ---- *)
    iApply (wp_uk_addi γt γd γs γfd h8 m5 (mword_of_int 0x94e)
              (mword_of_int 4087 : mword 12) a5_idx a4_idx
              (mword_of_int (bz0 - 9)) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_5;
                    exact (ush_addi_sub bz0 9 (mword_of_int 4087 : mword 12)
                             ltac:(unfold Z64; lia)
                             ltac:(vm_compute; reflexivity)))
              with "[] Hrun").
    { iApply (uis_shk_94e with "Hcode"). }
    assert (E94e : add_vec_int (mword_of_int 0x94e : mword 64) 4
                   = mword_of_int 0x952)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E94e. iIntros (h9) "Hrun".
    set (m6 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int (bz0 - 9) : mword 64)]> m5).
    assert (Hr6 : ush_regs m6)
      by exact (ush_regs_upd m5 a4_idx _ Hr5 ltac:(vm_compute; reflexivity)).
    assert (Ha5_6 : m6 !!! Regidx a5_idx = mword_of_int bz0).
    { rewrite (upd_ne m5 (Regidx a4_idx) (Regidx a5_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha5_5. }
    assert (Ha4_6 : m6 !!! Regidx a4_idx = mword_of_int (bz0 - 9))
      by exact (upd_eq m5 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int (bz0 - 9) : mword 64))).
    (* ---- 0x952/0x956  auipc+addi: s1 := buf ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h9 m6 (mword_of_int 0x952)
              (mword_of_int 1 : mword 20) s1_idx
              (add_vec (mword_of_int 0x952 : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20))) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_952 with "Hcode"). }
    assert (E952 : add_vec_int (mword_of_int 0x952 : mword 64) 4
                   = mword_of_int 0x956)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E952. iIntros (h10) "Hrun".
    set (m7 := <[Regidx s1_idx
                 := regval_into_reg
                      (add_vec (mword_of_int 0x952 : mword 64)
                         (auipc_off (mword_of_int 1 : mword 20)))]> m6).
    assert (Hr7 : ush_regs m7)
      by exact (ush_regs_upd m6 s1_idx _ Hr6 ltac:(vm_compute; reflexivity)).
    assert (Ha4_7 : m7 !!! Regidx a4_idx = mword_of_int (bz0 - 9)).
    { rewrite (upd_ne m6 (Regidx s1_idx) (Regidx a4_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha4_6. }
    assert (Ha5_7 : m7 !!! Regidx a5_idx = mword_of_int bz0).
    { rewrite (upd_ne m6 (Regidx s1_idx) (Regidx a5_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha5_6. }
    iApply (wp_uk_addi γt γd γs γfd h10 m7 (mword_of_int 0x956)
              (mword_of_int 1742 : mword 12) s1_idx s1_idx
              (mword_of_int sh_buf) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq m6 (Regidx s1_idx)
                               (regval_into_reg
                                  (add_vec (mword_of_int 0x952 : mword 64)
                                     (auipc_off (mword_of_int 1 : mword 20)))));
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_956 with "Hcode"). }
    assert (E956 : add_vec_int (mword_of_int 0x956 : mword 64) 4
                   = mword_of_int 0x95a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E956. iIntros (h11) "Hrun".
    set (m8 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int sh_buf : mword 64)]> m7).
    assert (Hr8 : ush_regs m8)
      by exact (ush_regs_upd m7 s1_idx _ Hr7 ltac:(vm_compute; reflexivity)).
    assert (Hs1_8 : m8 !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat 0)).
    { replace (sh_buf + Z.of_nat 0) with sh_buf by lia.
      exact (upd_eq m7 (Regidx s1_idx)
               (regval_into_reg (mword_of_int sh_buf : mword 64))). }
    assert (Ha4_8 : m8 !!! Regidx a4_idx = mword_of_int (bz0 - 9)).
    { rewrite (upd_ne m7 (Regidx s1_idx) (Regidx a4_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha4_7. }
    assert (Ha5_8 : m8 !!! Regidx a5_idx = mword_of_int bz0).
    { rewrite (upd_ne m7 (Regidx s1_idx) (Regidx a5_idx) _
                 ltac:(vm_compute; discriminate)). exact Ha5_7. }
    (* ---- 0x95a  c.bnez a4,0x976 -- not a TAB either: done scanning ---- *)
    assert (Htk5a : negb (Z.eqb bz0 9)
                    = neq_vec (m8 !!! Regidx a4_idx) zero_reg).
    { rewrite Ha4_8. symmetry.
      exact (ush_neqz_sub bz0 9 ltac:(unfold Z64; lia)
               ltac:(unfold Z64; lia)). }
    iApply (wp_uk_cbnez γt γd γs γfd h11 m8 (mword_of_int 0x95a)
              (mword_of_int 14 : mword 8) (mword_of_int 6 : mword 3) a4_idx
              (negb (Z.eqb bz0 9)) (mword_of_int 0x976) (16 + n)
              ltac:(vm_compute; reflexivity) Htk5a
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_95a with "Hcode"). }
    destruct (Z.eqb_spec bz0 9) as [Hb9 | Hb9].
    { (* a leading tab: fall into 0x95c and scan *)
      cbn [negb]. iIntros (h12) "Hrun".
      assert (E95a : add_vec_int (mword_of_int 0x95a : mword 64) 2
                     = mword_of_int 0x95c)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E95a.
      assert (Hi20 : (0 < i2)%nat).
      { destruct (Nat.eq_dec i2 0) as [Hz | Hne]; [ | lia ].
        exfalso. unfold bz0 in Hb9. rewrite Hz in Hnul.
        rewrite Hnul in Hb9. vm_compute in Hb9. discriminate Hb9. }
      iApply (wp_ksh_blank_entry h12 m8 g i2 n Hr8 Hi20 Hi2lt Hnul
                with "Hcode Htail Hbs Hrun"). }
    cbn [negb]. iIntros (h12) "Hrun".
    iApply ("Htail" $! h12 m8 0%nat with "[] [] [] [] Hbs Hrun");
      iPureIntro; [ exact Hr8 | lia | exact Hs1_8 | rewrite Ha5_8; reflexivity ].
  Qed.

  (* ===================================================================== *)
  (* 0x914..0x92a -- THE LOOP'S SETUP, and what stage 1 left open.          *)
  (*                                                                       *)
  (* Six instructions load the five constants the loop runs on: the buffer  *)
  (* address (an auipc/addi pair), its size, and the three character        *)
  (* literals for newline, 'c' and space.  main's frame is dead from here   *)
  (* on -- main does not return (0x9cc is a [jal exit]), so the eight words *)
  (* its prologue spilled are never reloaded -- which is why nothing about  *)
  (* the entry register file survives into the loop and the invariant is    *)
  (* exactly [ush_regs] plus the buffer.                                    *)
  (*                                                                       *)
  (* DEPENDS ON [ush_read_leaf] (through the loop).                         *)
  (* ===================================================================== *)
  Lemma wp_ksh_cmd_head (h : CpuId) (m : regfile) (f : nat -> bv 8) (n : nat) :
    ush_rest -∗
    shk_code γt -∗
    ubytes γd sh_buf sh_nbuf f -∗
    urun γt γd γs γfd h m (mword_of_int 0x914) (16 + n) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hrest #Hcode Hbs Hrun".
    (* ---- 0x914  li s3,100 ---- *)
    iApply (wp_uk_li γt γd γs γfd h m (mword_of_int 0x914)
              (mword_of_int 100 : mword 12) s3_idx (mword_of_int 100) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(assert (E : (sign_extend' 64 (mword_of_int 100 : mword 12)
                                 : mword 64) = mword_of_int 100)
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite E moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_914 with "Hcode"). }
    assert (E914 : add_vec_int (mword_of_int 0x914 : mword 64) 4
                   = mword_of_int 0x918)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E914. iIntros (h1) "Hrun".
    set (m1 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int 100 : mword 64)]> m).
    (* ---- 0x918/0x91c  auipc+addi: s2 := the buffer's address ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h1 m1 (mword_of_int 0x918)
              (mword_of_int 1 : mword 20) s2_idx
              (add_vec (mword_of_int 0x918 : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20))) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_918 with "Hcode"). }
    assert (E918 : add_vec_int (mword_of_int 0x918 : mword 64) 4
                   = mword_of_int 0x91c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E918. iIntros (h2) "Hrun".
    set (m2 := <[Regidx s2_idx
                 := regval_into_reg
                      (add_vec (mword_of_int 0x918 : mword 64)
                         (auipc_off (mword_of_int 1 : mword 20)))]> m1).
    iApply (wp_uk_addi γt γd γs γfd h2 m2 (mword_of_int 0x91c)
              (mword_of_int 1800 : mword 12) s2_idx s2_idx
              (mword_of_int sh_buf) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq m1 (Regidx s2_idx)
                               (regval_into_reg
                                  (add_vec (mword_of_int 0x918 : mword 64)
                                     (auipc_off (mword_of_int 1 : mword 20)))));
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_91c with "Hcode"). }
    assert (E91c : add_vec_int (mword_of_int 0x91c : mword 64) 4
                   = mword_of_int 0x920)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E91c. iIntros (h3) "Hrun".
    set (m3 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int sh_buf : mword 64)]> m2).
    (* ---- 0x920  c.li s4,10 ---- *)
    iApply (wp_uk_cli γt γd γs γfd h3 m3 (mword_of_int 0x920)
              (mword_of_int 10 : mword 6) s4_idx (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_920 with "Hcode"). }
    assert (Em920 : <[Regidx s4_idx
                      := regval_into_reg (sign_extend' 64
                                            (mword_of_int 10 : mword 6)
                                          : mword 64)]> m3
                    = <[Regidx s4_idx
                        := regval_into_reg (mword_of_int 10 : mword 64)]> m3)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (E920 : add_vec_int (mword_of_int 0x920 : mword 64) 2
                   = mword_of_int 0x922)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Em920 E920. iIntros (h4) "Hrun".
    set (m4 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int 10 : mword 64)]> m3).
    (* ---- 0x922  li s5,99 ---- *)
    iApply (wp_uk_li γt γd γs γfd h4 m4 (mword_of_int 0x922)
              (mword_of_int 99 : mword 12) s5_idx (mword_of_int 99) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(assert (E : (sign_extend' 64 (mword_of_int 99 : mword 12)
                                 : mword 64) = mword_of_int 99)
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite E moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_922 with "Hcode"). }
    assert (E922 : add_vec_int (mword_of_int 0x922 : mword 64) 4
                   = mword_of_int 0x926)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E922. iIntros (h5) "Hrun".
    set (m5 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int 99 : mword 64)]> m4).
    (* ---- 0x926  li s6,32 ---- *)
    iApply (wp_uk_li γt γd γs γfd h5 m5 (mword_of_int 0x926)
              (mword_of_int 32 : mword 12) s6_idx (mword_of_int 32) (16 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(assert (E : (sign_extend' 64 (mword_of_int 32 : mword 12)
                                 : mword 64) = mword_of_int 32)
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite E moi_add_zero_l; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_926 with "Hcode"). }
    assert (E926 : add_vec_int (mword_of_int 0x926 : mword 64) 4
                   = mword_of_int 0x92a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E926. iIntros (h6) "Hrun".
    set (m6 := <[Regidx s6_idx
                 := regval_into_reg (mword_of_int 32 : mword 64)]> m5).
    (* ---- 0x92a  c.j 0x938 ---- *)
    iApply (wp_uk_cj γt γd γs γfd h6 m6 (mword_of_int 0x92a)
              (mword_of_int 7 : mword 11) (mword_of_int 0x938) (16 + n)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_92a with "Hcode"). }
    iIntros (h7) "Hrun".
    assert (Hregs : ush_regs m6).
    { split_and!.
      - rewrite (upd_ne m5 (Regidx s6_idx) (Regidx s2_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne m4 (Regidx s5_idx) (Regidx s2_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne m3 (Regidx s4_idx) (Regidx s2_idx) _
                   ltac:(vm_compute; discriminate)).
        exact (upd_eq m2 (Regidx s2_idx)
                 (regval_into_reg (mword_of_int sh_buf : mword 64))).
      - rewrite (upd_ne m5 (Regidx s6_idx) (Regidx s3_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne m4 (Regidx s5_idx) (Regidx s3_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne m3 (Regidx s4_idx) (Regidx s3_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne m2 (Regidx s2_idx) (Regidx s3_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne m1 (Regidx s2_idx) (Regidx s3_idx) _
                   ltac:(vm_compute; discriminate)).
        exact (upd_eq m (Regidx s3_idx)
                 (regval_into_reg (mword_of_int 100 : mword 64))).
      - rewrite (upd_ne m5 (Regidx s6_idx) (Regidx s4_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (upd_ne m4 (Regidx s5_idx) (Regidx s4_idx) _
                   ltac:(vm_compute; discriminate)).
        exact (upd_eq m3 (Regidx s4_idx)
                 (regval_into_reg (mword_of_int 10 : mword 64))).
      - rewrite (upd_ne m5 (Regidx s6_idx) (Regidx s5_idx) _
                   ltac:(vm_compute; discriminate)).
        exact (upd_eq m4 (Regidx s5_idx)
                 (regval_into_reg (mword_of_int 99 : mword 64))).
      - exact (upd_eq m5 (Regidx s6_idx)
                 (regval_into_reg (mword_of_int 32 : mword 64))). }
    iDestruct (wp_ksh_loop with "Hrest Hcode") as "Hhead".
    iApply ("Hhead" $! h7 m6 f n with "[] Hbs Hrun").
    iPureIntro. exact Hregs.
  Qed.

  (* ===================================================================== *)
  (* THE CONSOLE PREAMBLE, 0x900..0x910 -- the loop, under iLöb.            *)
  (*                                                                       *)
  (*   0x900  c.mv a1,s1        ; a1 := O_RDWR                             *)
  (*   0x902  c.mv a0,s2        ; a0 := &"console"                         *)
  (*   0x904  jal ra,0xcc6      ; open                                     *)
  (*   0x908  bltz a0,0x914     ; open failed: leave the loop              *)
  (*   0x90c  bge s1,a0,0x900   ; fd <= 2: go round again  <-- BACK EDGE   *)
  (*   0x910  jal ra,0xcae      ; close(fd), then fall into 0x914          *)
  (*                                                                       *)
  (* The two branches are taken on ABSTRACT booleans -- the walk never      *)
  (* computes what the kernel returned -- and the only thing carried round  *)
  (* the cycle is [urun … 0x900 n] itself.                                  *)
  (* ===================================================================== *)
  Local Lemma wp_ksh_console (h : CpuId) (m : regfile) (f : nat -> bv 8)
      (n0 : nat) :
    ush_rest -∗
    shk_code γt -∗
    ubytes γd sh_buf sh_nbuf f -∗
    urun γt γd γs γfd h m (mword_of_int 0x900) (16 + n0) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hrest #Hcode".
    set (n := (16 + n0)%nat).
    iLöb as "IH" forall (h m).
    iIntros "Hbs Hrun".
    (* ---- 0x900  c.mv a1,s1 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h m (mword_of_int 0x900) a1_idx s1_idx
              (add_vec zero_reg (m !!! Regidx s1_idx)) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_900 with "Hcode"). }
    assert (E900 : add_vec_int (mword_of_int 0x900 : mword 64) 2
                   = mword_of_int 0x902)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E900. iIntros (h1) "Hrun".
    set (mA := <[Regidx a1_idx
                 := regval_into_reg (add_vec zero_reg (m !!! Regidx s1_idx))]> m).
    (* ---- 0x902  c.mv a0,s2 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h1 mA (mword_of_int 0x902) a0_idx s2_idx
              (add_vec zero_reg (mA !!! Regidx s2_idx)) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_902 with "Hcode"). }
    assert (E902 : add_vec_int (mword_of_int 0x902 : mword 64) 2
                   = mword_of_int 0x904)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E902. iIntros (h2) "Hrun".
    set (mB := <[Regidx a0_idx
                 := regval_into_reg (add_vec zero_reg (mA !!! Regidx s2_idx))]> mA).
    (* ---- 0x904  jal ra,0xcc6 <open> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h2 mB (mword_of_int 0x904)
              (mword_of_int 962 : mword 21) ra_idx
              (mword_of_int ShSyms.open) (mword_of_int 0x908) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite shp_open; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite shp_open; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_904 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (mC := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x908 : mword 64)]> mB).
    assert (HraC : mC !!! Regidx ra_idx = mword_of_int 0x908)
      by exact (upd_eq mB (Regidx ra_idx) (mword_of_int 0x908 : mword 64)).
    iApply (wp_ksh_open h3 mC n with "Hcode Hrun").
    iIntros (h4 ret) "Hrun".
    rewrite HraC.
    assert (Eret : ret_pc (mword_of_int 0x908 : mword 64) = mword_of_int 0x908)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    set (mD := <[Regidx a0_idx := ret]>
                 (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> mC)).
    (* ---- 0x908  bltz a0,0x914 ---- *)
    remember (uv_btaken BLT (mD !!! Regidx a0_idx) zero_reg) as t1 eqn:Ht1.
    iApply (wp_uk_btype0 γt γd γs γfd h4 mD (mword_of_int 0x908)
              (mword_of_int 12 : mword 13) a0_idx BLT t1 (mword_of_int 0x914) n
              Ht1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_908 with "Hcode"). }
    destruct t1.
    { (* open failed -- straight to the command loop's head *)
      iIntros (h5) "Hrun".
      iApply (wp_ksh_cmd_head h5 mD f n0 with "Hrest Hcode Hbs Hrun"). }
    assert (E908 : add_vec_int (mword_of_int 0x908 : mword 64) 4
                   = mword_of_int 0x90c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E908. iIntros (h5) "Hrun".
    (* ---- 0x90c  bge s1,a0,0x900 -- THE BACK EDGE ---- *)
    remember (uv_btaken BGE (mD !!! Regidx s1_idx) (mD !!! Regidx a0_idx))
      as t2 eqn:Ht2.
    iApply (UkRunLeaf.wp_uk_btype_later γt γd γs γfd h5 mD (mword_of_int 0x90c)
              (mword_of_int 8180 : mword 13) a0_idx s1_idx BGE t2
              (mword_of_int 0x900) n
              Ht2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_90c with "Hcode"). }
    destruct t2.
    { (* fd <= 2 -- round again, on the Löb hypothesis *)
      iNext. iIntros (h6) "Hrun". iApply ("IH" with "Hbs Hrun"). }
    iNext.
    assert (E90c : add_vec_int (mword_of_int 0x90c : mword 64) 4
                   = mword_of_int 0x910)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E90c. iIntros (h6) "Hrun".
    (* ---- 0x910  jal ra,0xcae <close> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h6 mD (mword_of_int 0x910)
              (mword_of_int 926 : mword 21) ra_idx
              (mword_of_int ShSyms.close) (mword_of_int 0x914) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite shp_close; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite shp_close; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_910 with "Hcode"). }
    iIntros (h7) "Hrun".
    set (mE := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x914 : mword 64)]> mD).
    assert (HraE : mE !!! Regidx ra_idx = mword_of_int 0x914)
      by exact (upd_eq mD (Regidx ra_idx) (mword_of_int 0x914 : mword 64)).
    iApply (wp_ksh_close h7 mE n with "Hcode Hrun").
    iIntros (h8 ret2) "Hrun".
    rewrite HraE.
    assert (Eret2 : ret_pc (mword_of_int 0x914 : mword 64) = mword_of_int 0x914)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eret2.
    iApply (wp_ksh_cmd_head h8 _ f n0 with "Hrest Hcode Hbs Hrun").
  Qed.


  (* ===================================================================== *)
  (* main -- the prologue and the preamble's setup.                         *)
  (*                                                                       *)
  (* Eight words of frame (ra and s0..s6), spilled and never reloaded:      *)
  (* main never returns.  0x8f6..0x8fc load O_RDWR and the address of the   *)
  (* "console" literal, and 0x900 is the loop above.                        *)
  (* ===================================================================== *)
  Lemma wp_ksh_main (h : CpuId) (m : regfile) (f : nat -> bv 8) (n0 : nat) :
    ush_rest -∗
    shk_code γt -∗
    ubytes γd sh_buf sh_nbuf f -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.main) (8 + (16 + n0)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hrest #Hcode Hbs Hrun".
    set (n := (16 + n0)%nat).
    rewrite shp_main.
    iDestruct (urun_stack with "Hrun") as %[Hal8' Hroom].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    assert (Hal8 : uint sp0 mod 8 = 0) by exact Hal8'.
    assert (Hlo : 64 <= uint sp0) by lia.
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 8)))
                   = bv_unsigned sp0 - 64).
    { replace (- (8 * Z.of_nat 8)) with (-64) by lia.
      exact (uv_avi_neg sp0 64 ltac:(lia) ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp64 : uint (add_vec_int sp0 (- (8 * Z.of_nat 8)))
                    = uint sp0 - 64)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Ho0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    assert (Ho1 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    assert (Ho2 : uoff_sdsp (mword_of_int 2 : mword 6) = 16)
      by (vm_compute; reflexivity).
    assert (Ho3 : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
      by (vm_compute; reflexivity).
    assert (Ho4 : uoff_sdsp (mword_of_int 4 : mword 6) = 32)
      by (vm_compute; reflexivity).
    assert (Ho5 : uoff_sdsp (mword_of_int 5 : mword 6) = 40)
      by (vm_compute; reflexivity).
    assert (Ho6 : uoff_sdsp (mword_of_int 6 : mword 6) = 48)
      by (vm_compute; reflexivity).
    assert (Ho7 : uoff_sdsp (mword_of_int 7 : mword 6) = 56)
      by (vm_compute; reflexivity).
    (* ---- 0x8e2  c.addi16sp sp,sp,-64 -- THE PUSH ---- *)
    iApply (wp_uk_caddi16sp_dn γt γd γs γfd h m (mword_of_int 0x8e2)
              (mword_of_int 60 : mword 6) 8 n
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_8e2 with "Hcode"). }
    assert (E8e2 : add_vec_int (mword_of_int 0x8e2 : mword 64) 2
                   = mword_of_int 0x8e4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp ustack_8 E8e2.
    iIntros "(_ & [%v1 Hw1] & [%v2 Hw2] & [%v3 Hw3] & [%v4 Hw4]
              & [%v5 Hw5] & [%v6 Hw6] & [%v7 Hw7] & [%v8 Hw8])".
    iIntros (hs0) "Hrun".
    set (mA := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 8)))]> m).
    assert (HspA : mA !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 8)))
      by exact (upd_eq m (Regidx csp_rs1)
                  (regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 8))))).
    (* ---- 0x8e4  c.sdsp ra,56(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd hs0 mA (mword_of_int 0x8e4)
              (mword_of_int 7 : mword 6) ra_idx (uint sp0 - 8) v1 n
              ltac:(rewrite HspA Hsp64 Ho7; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw1 Hrun").
    { iApply (uis_shk_8e4 with "Hcode"). }
    iIntros "Hw1".
    assert (Es0 : add_vec_int (mword_of_int 0x8e4 : mword 64) 2
                  = mword_of_int 0x8e6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Es0. iIntros (hs1) "Hrun".
    (* ---- 0x8e6  c.sdsp s0,48(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd hs1 mA (mword_of_int 0x8e6)
              (mword_of_int 6 : mword 6) s0_idx (uint sp0 - 16) v2 n
              ltac:(rewrite HspA Hsp64 Ho6; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw2 Hrun").
    { iApply (uis_shk_8e6 with "Hcode"). }
    iIntros "Hw2".
    assert (Es1 : add_vec_int (mword_of_int 0x8e6 : mword 64) 2
                  = mword_of_int 0x8e8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Es1. iIntros (hs2) "Hrun".
    (* ---- 0x8e8  c.sdsp s1,40(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd hs2 mA (mword_of_int 0x8e8)
              (mword_of_int 5 : mword 6) s1_idx (uint sp0 - 24) v3 n
              ltac:(rewrite HspA Hsp64 Ho5; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw3 Hrun").
    { iApply (uis_shk_8e8 with "Hcode"). }
    iIntros "Hw3".
    assert (Es2 : add_vec_int (mword_of_int 0x8e8 : mword 64) 2
                  = mword_of_int 0x8ea)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Es2. iIntros (hs3) "Hrun".
    (* ---- 0x8ea  c.sdsp s2,32(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd hs3 mA (mword_of_int 0x8ea)
              (mword_of_int 4 : mword 6) s2_idx (uint sp0 - 32) v4 n
              ltac:(rewrite HspA Hsp64 Ho4; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw4 Hrun").
    { iApply (uis_shk_8ea with "Hcode"). }
    iIntros "Hw4".
    assert (Es3 : add_vec_int (mword_of_int 0x8ea : mword 64) 2
                  = mword_of_int 0x8ec)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Es3. iIntros (hs4) "Hrun".
    (* ---- 0x8ec  c.sdsp s3,24(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd hs4 mA (mword_of_int 0x8ec)
              (mword_of_int 3 : mword 6) s3_idx (uint sp0 - 40) v5 n
              ltac:(rewrite HspA Hsp64 Ho3; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw5 Hrun").
    { iApply (uis_shk_8ec with "Hcode"). }
    iIntros "Hw5".
    assert (Es4 : add_vec_int (mword_of_int 0x8ec : mword 64) 2
                  = mword_of_int 0x8ee)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Es4. iIntros (hs5) "Hrun".
    (* ---- 0x8ee  c.sdsp s4,16(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd hs5 mA (mword_of_int 0x8ee)
              (mword_of_int 2 : mword 6) s4_idx (uint sp0 - 48) v6 n
              ltac:(rewrite HspA Hsp64 Ho2; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw6 Hrun").
    { iApply (uis_shk_8ee with "Hcode"). }
    iIntros "Hw6".
    assert (Es5 : add_vec_int (mword_of_int 0x8ee : mword 64) 2
                  = mword_of_int 0x8f0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Es5. iIntros (hs6) "Hrun".
    (* ---- 0x8f0  c.sdsp s5,8(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd hs6 mA (mword_of_int 0x8f0)
              (mword_of_int 1 : mword 6) s5_idx (uint sp0 - 56) v7 n
              ltac:(rewrite HspA Hsp64 Ho1; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw7 Hrun").
    { iApply (uis_shk_8f0 with "Hcode"). }
    iIntros "Hw7".
    assert (Es6 : add_vec_int (mword_of_int 0x8f0 : mword 64) 2
                  = mword_of_int 0x8f2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Es6. iIntros (hs7) "Hrun".
    (* ---- 0x8f2  c.sdsp s6,0(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd hs7 mA (mword_of_int 0x8f2)
              (mword_of_int 0 : mword 6) s6_idx (uint sp0 - 64) v8 n
              ltac:(rewrite HspA Hsp64 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw8 Hrun").
    { iApply (uis_shk_8f2 with "Hcode"). }
    iIntros "Hw8".
    assert (Es7 : add_vec_int (mword_of_int 0x8f2 : mword 64) 2
                  = mword_of_int 0x8f4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Es7. iIntros (hs8) "Hrun".
    (* ---- 0x8f4  c.addi4spn s0,sp,64 (s0 is dead: main never returns) ---- *)
    iApply (wp_uk_caddi4spn γt γd γs γfd hs8 mA (mword_of_int 0x8f4)
              (mword_of_int 0 : mword 3) (mword_of_int 16 : mword 8) s0_idx
              (add_vec (mA !!! Regidx csp_rs1)
                 (sign_extend' 64
                    (caddi4spn_imm (mword_of_int 16 : mword 8)))) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              eq_refl
              with "[] Hrun").
    { iApply (uis_shk_8f4 with "Hcode"). }
    assert (E8f4 : add_vec_int (mword_of_int 0x8f4 : mword 64) 2
                   = mword_of_int 0x8f6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E8f4. iIntros (hb) "Hrun".
    set (mB := <[Regidx s0_idx
                 := regval_into_reg
                      (add_vec (mA !!! Regidx csp_rs1)
                         (sign_extend' 64
                            (caddi4spn_imm (mword_of_int 16 : mword 8))))]> mA).
    (* ---- 0x8f6  c.li s1,2  (O_RDWR) ---- *)
    iApply (wp_uk_cli γt γd γs γfd hb mB (mword_of_int 0x8f6)
              (mword_of_int 2 : mword 6) s1_idx n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_8f6 with "Hcode"). }
    assert (E8f6 : add_vec_int (mword_of_int 0x8f6 : mword 64) 2
                   = mword_of_int 0x8f8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E8f6. iIntros (hc) "Hrun".
    set (mC := <[Regidx s1_idx
                 := regval_into_reg (sign_extend' 64 (mword_of_int 2 : mword 6)
                                     : mword 64)]> mB).
    (* ---- 0x8f8  auipc s2,0x1 ---- *)
    iApply (wp_uk_auipc γt γd γs γfd hc mC (mword_of_int 0x8f8)
              (mword_of_int 1 : mword 20) s2_idx
              (add_vec (mword_of_int 0x8f8 : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20))) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_8f8 with "Hcode"). }
    assert (E8f8 : add_vec_int (mword_of_int 0x8f8 : mword 64) 4
                   = mword_of_int 0x8fc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E8f8. iIntros (hd) "Hrun".
    set (mD := <[Regidx s2_idx
                 := regval_into_reg
                      (add_vec (mword_of_int 0x8f8 : mword 64)
                         (auipc_off (mword_of_int 1 : mword 20)))]> mC).
    (* ---- 0x8fc  addi s2,s2,-1408  (&"console") ---- *)
    iApply (wp_uk_addi γt γd γs γfd hd mD (mword_of_int 0x8fc)
              (mword_of_int 2688 : mword 12) s2_idx s2_idx
              (add_vec (mD !!! Regidx s2_idx)
                 (sign_extend' 64 (mword_of_int 2688 : mword 12))) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_shk_8fc with "Hcode"). }
    assert (E8fc : add_vec_int (mword_of_int 0x8fc : mword 64) 4
                   = mword_of_int 0x900)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E8fc. iIntros (he) "Hrun".
    (* ---- 0x900  the console loop ---- *)
    iApply (wp_ksh_console he _ f n0 with "Hrest Hcode Hbs Hrun").
  Qed.


  (* ===================================================================== *)
  (* start -- the ELF entry.  usys.S's crt: a two-word frame, then          *)
  (* main(), then exit() if it ever came back.  It does not: main's own     *)
  (* contract has no continuation, so 0x9dc is unreachable and never        *)
  (* appears here.  The [avail] arithmetic is the call chain spelled out:   *)
  (* start's two words and main's eight.                                    *)
  (* ===================================================================== *)
  Lemma wp_ksh_start (h : CpuId) (m : regfile) (f : nat -> bv 8) (n0 : nat) :
    ush_rest -∗
    shk_code γt -∗
    ubytes γd sh_buf sh_nbuf f -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.start) (2 + (8 + (16 + n0))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hrest #Hcode Hbs Hrun".
    set (n := (16 + n0)%nat).
    rewrite shp_start.
    iDestruct (urun_stack with "Hrun") as %[Hal8' Hroom].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    assert (Hal8 : uint sp0 mod 8 = 0) by exact Hal8'.
    assert (Hlo : 16 <= uint sp0) by lia.
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                   = bv_unsigned sp0 - 16).
    { replace (- (8 * Z.of_nat 2)) with (-16) by lia.
      exact (uv_avi_neg sp0 16 ltac:(lia) ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp16 : uint (add_vec_int sp0 (- (8 * Z.of_nat 2)))
                    = uint sp0 - 16)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    assert (Ho0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    (* ---- 0x9d0  c.addi sp,sp,-16 ---- *)
    iApply (wp_uk_caddi_sp_dn γt γd γs γfd h m (mword_of_int 0x9d0)
              (mword_of_int 48 : mword 6) 2 (8 + n)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_9d0 with "Hcode"). }
    assert (E9d0 : add_vec_int (mword_of_int 0x9d0 : mword 64) 2
                   = mword_of_int 0x9d2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp ustack_2 E9d0.
    iIntros "(_ & [%v8 Hw8] & [%v0 Hw0])".
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 2)))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by exact (upd_eq m (Regidx csp_rs1)
                  (regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 2))))).
    (* ---- 0x9d2  c.sdsp ra,8(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd h1 m1 (mword_of_int 0x9d2)
              (mword_of_int 1 : mword 6) ra_idx (uint sp0 - 8) v8 (8 + n)
              ltac:(rewrite Hsp1 Hsp16 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw8 Hrun").
    { iApply (uis_shk_9d2 with "Hcode"). }
    iIntros "Hw8".
    assert (E9d2 : add_vec_int (mword_of_int 0x9d2 : mword 64) 2
                   = mword_of_int 0x9d4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E9d2. iIntros (h2) "Hrun".
    (* ---- 0x9d4  c.sdsp s0,0(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd h2 m1 (mword_of_int 0x9d4)
              (mword_of_int 0 : mword 6) s0_idx (uint sp0 - 16) v0 (8 + n)
              ltac:(rewrite Hsp1 Hsp16 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw0 Hrun").
    { iApply (uis_shk_9d4 with "Hcode"). }
    iIntros "Hw0".
    assert (E9d4 : add_vec_int (mword_of_int 0x9d4 : mword 64) 2
                   = mword_of_int 0x9d6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E9d4. iIntros (h3) "Hrun".
    (* ---- 0x9d6  c.addi4spn s0,sp,16 ---- *)
    iApply (wp_uk_caddi4spn γt γd γs γfd h3 m1 (mword_of_int 0x9d6)
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8) s0_idx
              (add_vec (m1 !!! Regidx csp_rs1)
                 (sign_extend' 64
                    (caddi4spn_imm (mword_of_int 4 : mword 8)))) (8 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              eq_refl
              with "[] Hrun").
    { iApply (uis_shk_9d6 with "Hcode"). }
    assert (E9d6 : add_vec_int (mword_of_int 0x9d6 : mword 64) 2
                   = mword_of_int 0x9d8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E9d6. iIntros (h4) "Hrun".
    set (m2 := <[Regidx s0_idx
                 := regval_into_reg
                      (add_vec (m1 !!! Regidx csp_rs1)
                         (sign_extend' 64
                            (caddi4spn_imm (mword_of_int 4 : mword 8))))]> m1).
    (* ---- 0x9d8  jal ra,0x8e2 <main> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h4 m2 (mword_of_int 0x9d8)
              (mword_of_int 2096906 : mword 21) ra_idx
              (mword_of_int ShSyms.main) (mword_of_int 0x9dc) (8 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite shp_main; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite shp_main; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_9d8 with "Hcode"). }
    iIntros (h5) "Hrun".
    (* ---- main(), which never returns ---- *)
    (* [ShSyms.main] is what the jal's target already is, so this only ever
       had work to do while the wide catalog destruct was dumping unused
       [uinstr_is] hypotheses holding the literal into the context. *)
    rewrite <- ?shp_main.
    iApply (wp_ksh_main h5 _ f n0 with "Hrest Hcode Hbs Hrun").
  Qed.

End UkSh.

(* ===================================================================== *)
(* THE READ LEAF, DISCHARGED.  [ush_read_leaf] was a Hypothesis while     *)
(* the general window leaf did not exist; [UkRunSys.wp_uk_ecall_read_win] is  *)
(* that leaf's read instance, and the two spellings differ only in how    *)
(* the count is read: the hypothesis takes a2 as the unsigned word equal  *)
(* to the buffer's size, the leaf takes it as the C [int] the kernel      *)
(* narrows it to.  The bridge is ONE bound -- [Z.to_nat] of the narrowed  *)
(* count never exceeds the unsigned word -- and it needs NO side          *)
(* condition on [k]: a negative narrow floors at zero under [Z.to_nat],   *)
(* and a non-negative one IS the unsigned low half, which [mod] bounds    *)
(* by the whole word.  So every lemma above that carries the hypothesis   *)
(* as an argument is made unconditional by applying it to                 *)
(* [ush_read_leaf_holds].                                                 *)
(* ===================================================================== *)

Lemma ush_narrow_count_le (w : mword 64) (k : nat) :
  uint w = Z.of_nat k ->
  (Z.to_nat (bv_signed (subrange_vec_dec w 31 0 : mword 32)) <= k)%nat.
Proof.
  intros Hu. rewrite uint_unsigned in Hu.
  pose proof (subrange_31_0_unsigned w) as Hlo.
  (* the signed reading, as the unsigned one shifted into the signed
     window -- convertibility does the modulus arithmetic *)
  assert (Hs : bv_signed (subrange_vec_dec w 31 0 : mword 32)
               = (bv_unsigned (subrange_vec_dec w 31 0 : mword 32)
                  + 2147483648) mod 4294967296 - 2147483648)
    by reflexivity.
  rewrite Hs Hlo.
  set (u := bv_unsigned w mod 4294967296).
  assert (Hub : 0 <= u < 4294967296)
    by (apply Z.mod_pos_bound; lia).
  assert (Hule : u <= bv_unsigned w)
    by (apply Z.mod_le; [ lia | lia ]).
  pose proof (Z.div_mod (u + 2147483648) 4294967296 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (u + 2147483648) 4294967296 ltac:(lia)) as Hmb.
  lia.
Qed.

Section UkShLeaf.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context (γt γd γs γfd : gname).

  Lemma ush_read_leaf_holds :
    forall (h : CpuId) (m : regfile) (pc : mword 64) (a : Z) (k : nat)
           (f : nat -> bv 8) (avail : nat),
      usysno m = USYS_read ->
      uint (m !!! Regidx (mword_of_int 11 : mword 5)) = a ->
      uint (m !!! Regidx (mword_of_int 12 : mword 5)) = Z.of_nat k ->
      is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
      uinstr_is γt pc false (ECALL tt) -∗
      ubytes γd a k f -∗
      urun γt γd γs γfd h m pc avail -∗
      (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8),
         ⌜ (d <= k)%nat ⌝ -∗
         ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
         ubytes γd a k g -∗
         urun γt γd γs γfd h' (<[Regidx (mword_of_int 10 : mword 5) := r]> m)
           (add_vec_int pc 4) avail -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    intros h m pc a k f avail Hn Ha1 Ha2 Hal.
    pose proof (ush_narrow_count_le (m !!! Regidx (mword_of_int 12 : mword 5))
                  k Ha2) as Hbound.
    subst a.
    iIntros "#Hi Hbuf Hrun Hcont".
    iApply (wp_uk_ecall_read_win γt γd γs γfd h m pc
              (bv_signed (subrange_vec_dec
                            (m !!! Regidx (mword_of_int 12 : mword 5)) 31 0
                          : mword 32))
              k f avail Hn eq_refl Hbound Hal with "Hi Hrun Hbuf").
    iIntros (h' r d g) "%Hd %Hgf Hrun Hbuf".
    iApply ("Hcont" $! h' r d g with "[%] [%] Hbuf Hrun");
      [ lia | exact Hgf ].
  Qed.

End UkShLeaf.
