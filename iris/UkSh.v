(* ===================================================================== *)
(* UkSh.v -- the `sh` user program on the urun engine, SH LANE STAGE 1:    *)
(* the ELF entry, main's prologue, and main's CONSOLE PREAMBLE -- the      *)
(* loop that opens "console" until the process owns fd 3 --, ending at     *)
(* the command loop's head (0x914), which stage 2 walks.                   *)
(*                                                                        *)
(* Six functions' worth of pcs: start (6 instructions), main's first 15,   *)
(* and the three syscall stubs the preamble issues (open, close, exit).    *)
(* The catalog is UCodeShK.v -- a SECOND catalog over the same dump as     *)
(* UCodeSh.v, emitted at [--prog shk] so the first-generation sh proofs    *)
(* (UProofSh*.v, still on-build over WpUmode*/UmodeIo) keep their names.   *)
(*                                                                        *)
(* WHAT THIS STAGE ESTABLISHES, and why it stops here.                     *)
(*                                                                        *)
(* (1) EVERY SYSCALL ON THIS PATH TAKES THE QUIET ROW.  open (15), close   *)
(* (21) and exit (2) are all outside the eight numbers                     *)
(* [UsysMemOk.usys_mem_ok] gives a window to, so the kernel writes no user *)
(* byte and the heap crosses the trap untouched.  [wp_ksh_qstub] is that   *)
(* fact once, for the whole two-instruction-and-a-return stub shape of     *)
(* usys.S; open and close are instances, and stage 2's chdir, dup and      *)
(* write will be three more.  The stage stops at 0x914 because the command *)
(* loop's [gets] calls READ, whose WINDOW row has no consumer leaf: the    *)
(* only two ecall leaves on this engine are [wp_uk_ecall_quiet] and        *)
(* [wp_uk_ecall_exit], and UkRunSys.v's own header says the window and     *)
(* sbrk rows are "not yet built".                                          *)
(*                                                                        *)
(* (2) THE UNBOUNDED LOOP, CLOSED.  The preamble is                        *)
(*                                                                        *)
(*   while ((fd = open("console", O_RDWR)) >= 0)                           *)
(*     if (fd >= 3) { close(fd); break; }                                  *)
(*                                                                        *)
(* and it is the FIRST unbounded loop proven on urun: the quiet row hands  *)
(* back an ARBITRARY return value, so no Rocq measure decreases and echo's *)
(* two bounded scans are no precedent.  It is an [iLöb], and the [▷] it    *)
(* strips comes from the back edge's own branch -- [bge s1,a0,0x900] at    *)
(* 0x90c -- through [UkRunLeaf.wp_uk_btype_later], which init's own loops  *)
(* needed too and which upstream landed beside [wp_uk_btype].  UkRunBr.v   *)
(* is now down to the ONE leaf UkRunLeaf still has no twin for, the x0     *)
(* branch [wp_uk_btype0]; see its header for the rest of the ask.          *)
(*                                                                        *)
(* THE LOOP INVARIANT IS EMPTY, and that is the finding worth recording.   *)
(* Nothing about a register is carried around the cycle: the branch        *)
(* conditions are CASE SPLIT on the abstract boolean [uv_btaken …] rather  *)
(* than computed, so the walk never learns what fd the kernel returned and *)
(* never needs to.  What the loop preserves is exactly [urun … 0x900 n] -- *)
(* the free stack, at the depth main's prologue left it.  That is why the  *)
(* whole preamble is 90 lines rather than 900, and it is the shape stage 2 *)
(* should try FIRST on the command loop, whose real invariant is the       *)
(* buffer's, not a register's.                                             *)
(*                                                                        *)
(* (3) THE STAGE BOUNDARY IS ONE Prop.  [ush_cmd_head] says the command    *)
(* loop's head is safe at ANY register file -- main's frame is dead from   *)
(* 0x914 on (main never returns, so the eight spilled words are dropped    *)
(* here and the epilogue at no pc is ever reached), and 0x914..0x926       *)
(* reloads every register it uses.  Stage 2 discharges it; everything      *)
(* below it in this file is unconditional.                                 *)
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

Section UkSh.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context (γt γd γs : gname).

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
  Proof. destruct shk_syms_pins as (_&_&_&_&_&_&_&_&_&H). exact H. Qed.


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
    urun γt γd γs h m pc avail -∗ ubyteq γd dq a b -∗ ⌜ 0 <= a < 2 ^ 38 ⌝.
  Proof.
    iIntros "Hrun Hb".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(_ & _ & Hh & _ & _)".
    iDestruct (uheap_ubyte with "Hh Hb") as %(_ & _ & Hbnd).
    iPureIntro. exact Hbnd.
  Qed.

  Local Lemma urun_ubytes_bnd (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (dq : dfrac) (a : Z) (k : nat) (f : nat -> bv 8) :
    (0 < k)%nat ->
    urun γt γd γs h m pc avail -∗ ubytesq γd dq a k f -∗
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
    urun γt γd γs h m pc avail -∗
    ⌜ m !!! Regidx x0_idx = zero_reg ⌝ ∗ urun γt γd γs h m pc avail.
  Proof.
    iIntros "Hrun".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iSplitR; [ iPureIntro; exact Hx0 | ].
    iExists C, pt, Rut, sz, M, pm. iFrame "Hheap Hstk Hb".
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
    add_vec_int (mword_of_int pc0 : mword 64) 2 = mword_of_int pc1 ->
    add_vec_int (mword_of_int pc1 : mword 64) 4 = mword_of_int pc2 ->
    is_aligned_vaddr (Virtaddr (mword_of_int pc2 : mword 64)) 2 = true ->
    uinstr_is γt (mword_of_int pc0) true (C_LI (imm, Regidx a7_idx)) -∗
    uinstr_is γt (mword_of_int pc1) false (ECALL tt) -∗
    uinstr_is γt (mword_of_int pc2) true (C_JR (Regidx ra_idx)) -∗
    urun γt γd γs h m (mword_of_int pc0) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun γt γd γs h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int n : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Himm Hno He Hf Hx Hs Hw Hp Hr Hst E01 E12 Hal2.
    iIntros "#Ci0 #Ci1 #Ci2 Hrun Hcont".
    (* ---- pc0  c.li a7,n ---- *)
    iApply (wp_uk_cli γt γd γs h m (mword_of_int pc0) imm a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "Ci0 Hrun").
    assert (Em : <[Regidx a7_idx := regval_into_reg (sign_extend' 64 imm : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int n : mword 64)]> m)
      by (f_equal; exact Himm).
    rewrite E01 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int n : mword 64)]> m).
    (* ---- pc1  ecall -- the QUIET row ---- *)
    iApply (wp_uk_ecall_quiet γt γd γs h1 m1 (mword_of_int pc1) n avail
              Hno He Hf Hx Hs Hw Hp Hr Hst
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
    iApply (wp_uk_cjr γt γd γs h2 m2 (mword_of_int pc2) ra_idx
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
    urun γt γd γs h m (mword_of_int ShSyms.open) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun γt γd γs h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun Hcont".
    rewrite shp_open.
    iApply (wp_ksh_qstub h m 0xcc6 0xcc8 0xccc
              (mword_of_int 15 : mword 6) 15 avail
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(unfold usysno;
                    rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 15 : mword 64));
                    vm_compute; reflexivity)
              ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate)
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
    urun γt γd γs h m (mword_of_int ShSyms.close) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun γt γd γs h'
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
    urun γt γd γs h m (mword_of_int ShSyms.exit) avail -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun".
    rewrite shp_exit.
    (* ---- 0xc86  c.li a7,2 ---- *)
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0xc86)
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
    iApply (wp_uk_ecall_exit γt γd γs h1 m1 (mword_of_int 0xc88) avail
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 2 : mword 64));
                    vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_c88 with "Hcode"). }
  Qed.


  (* ---- write @0xca6, SYS_write = 16 -- quiet, the third stub instance -- *)
  Lemma wp_ksh_write (h : CpuId) (m : regfile) (avail : nat) :
    shk_code γt -∗
    urun γt γd γs h m (mword_of_int ShSyms.write) avail -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun γt γd γs h'
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
      urun γt γd γs h m pc avail -∗
      (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8),
         ⌜ (d <= k)%nat ⌝ -∗
         ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
         ubytes γd a k g -∗
         urun γt γd γs h' (<[Regidx a0_idx := r]> m)
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
    urun γt γd γs h m (mword_of_int ShSyms.read) avail -∗
    (∀ (h' : CpuId) (ret : mword 64) (d : nat) (g : nat -> bv 8),
       ⌜ (d <= k)%nat ⌝ -∗
       ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
       ubytes γd a k g -∗
       urun γt γd γs h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha1 Ha2. iIntros "#Hcode Hbs Hrun Hcont".
    rewrite shp_read.
    (* ---- 0xc9e  c.li a7,5 ---- *)
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0xc9e)
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
    iApply (wp_uk_cjr γt γd γs h2 m2 (mword_of_int 0xca4) ra_idx
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
  Local Lemma wp_ksh_memset_loop (a : Z) (N : nat) :
    forall (k j : nat) (h : CpuId) (mc : regfile) (f : nat -> bv 8) (nn : nat),
    (N = j + 1 + k)%nat ->
    0 <= a -> a + Z.of_nat N < Z64 ->
    mc !!! Regidx a5_idx = mword_of_int (a + Z.of_nat j) ->
    mc !!! Regidx a4_idx = mword_of_int (a + Z.of_nat N) ->
    shk_code γt -∗
    ubytes γd a N f -∗
    urun γt γd γs h mc (mword_of_int 0xa70) nn -∗
    ((∃ g : nat -> bv 8, ubytes γd a N g) -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall r : mword 5, Regidx r <> Regidx a5_idx ->
             mc' !!! Regidx r = mc !!! Regidx r ⌝ -∗
         urun γt γd γs h' mc' (mword_of_int 0xa7a) nn -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros k. induction k as [| k IH ];
      intros j h mc f nn HN Ha0 Ha64 Ha5 Ha4;
      iIntros "#Hcode Hbs Hrun Hcont".
    - (* the LAST byte: after it a5 = a4 and the branch falls through *)
      iDestruct (ush_bytes_upd a N j f ltac:(lia) with "Hbs") as "[Hb Hcl]".
      iApply (wp_uk_sb γt γd γs h mc (mword_of_int 0xa70)
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
      iApply (wp_uk_caddi γt γd γs h1 mc (mword_of_int 0xa74)
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
      iApply (wp_uk_btype γt γd γs h2 m1 (mword_of_int 0xa76)
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
      { iExists (ush_set f j (nth_byte (mc !!! Regidx a1_idx) 0)). iExact "Hbs". }
      { iPureIntro. exact Hpres. }
    - (* a body byte: a5 moves on and the branch goes back to 0xa70 *)
      iDestruct (ush_bytes_upd a N j f ltac:(lia) with "Hbs") as "[Hb Hcl]".
      iApply (wp_uk_sb γt γd γs h mc (mword_of_int 0xa70)
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
      iApply (wp_uk_caddi γt γd γs h1 mc (mword_of_int 0xa74)
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
      iApply (wp_uk_btype γt γd γs h2 m1 (mword_of_int 0xa76)
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
                ltac:(lia) Ha0 Ha64 Ha5_1 Ha4_1
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
    urun γt γd γs h m (mword_of_int ShSyms.memset) (2 + nn) -∗
    ((∃ g : nat -> bv 8, ubytes γd a N g) -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         urun γt γd γs h' m' (ret_pc (m !!! Regidx ra_idx)) (2 + nn) -∗
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
    iApply (wp_uk_caddi_sp_dn γt γd γs h m (mword_of_int 0xa5c)
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
    iApply (wp_uk_csdsp γt γd γs h1 m1 (mword_of_int 0xa5e)
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
    iApply (wp_uk_csdsp γt γd γs h2 m1 (mword_of_int 0xa60)
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
    iApply (wp_uk_caddi4spn γt γd γs h3 m1 (mword_of_int 0xa62)
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
    iApply (wp_uk_cbeqz γt γd γs h4 m2 (mword_of_int 0xa64)
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
    iApply (wp_uk_cmv γt γd γs h5 m2 (mword_of_int 0xa66) a5_idx a0_idx
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
    iApply (wp_uk_cslli γt γd γs h6 m3 (mword_of_int 0xa68)
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
    iApply (wp_uk_csrli γt γd γs h7 m4 (mword_of_int 0xa6a)
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
    iApply (wp_uk_add γt γd γs h8 m5 (mword_of_int 0xa6c)
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
    iApply (wp_ksh_memset_loop a N (N - 1)%nat 0%nat h9 m6 f nn
              ltac:(lia) Halo ltac:(unfold Z64; lia) Ha5_6 Ha4_6
              with "Hcode Hbs Hrun").
    iIntros "Hbs" (h10 mc) "%Hmc Hrun".
    assert (Hspc : mc !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 2))).
    { rewrite (Hmc csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm6 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm5 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm4 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm3 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp2. }
    (* ---- 0xa7a  c.ldsp ra,8(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h10 mc (mword_of_int 0xa7a)
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
    iApply (wp_uk_cldsp γt γd γs h11 e1 (mword_of_int 0xa7c)
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
    iApply (wp_uk_caddi_sp_up γt γd γs h12 e2 (mword_of_int 0xa7e)
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
    iApply (wp_uk_cjr γt γd γs h13 e3 (mword_of_int 0xa80) ra_idx
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
  (* THE STAGE BOUNDARY.  0x914 is where the console preamble hands over    *)
  (* to the command loop.  Quantified over EVERY register file, because     *)
  (* main's frame is dead from here on: main does not return (0x9cc is a    *)
  (* [jal exit]), so the eight words its prologue spilled are never         *)
  (* reloaded, and 0x914..0x926 writes every register the loop reads.       *)
  (* ===================================================================== *)
  Hypothesis ush_cmd_head :
    forall (h : CpuId) (m : regfile) (n : nat),
      shk_code γt -∗
      urun γt γd γs h m (mword_of_int 0x914) n -∗
      WP (Loop : expr riscv_lang).

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
  Local Lemma wp_ksh_console (h : CpuId) (m : regfile) (n : nat) :
    shk_code γt -∗
    urun γt γd γs h m (mword_of_int 0x900) n -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode".
    iLöb as "IH" forall (h m).
    iIntros "Hrun".
    (* ---- 0x900  c.mv a1,s1 ---- *)
    iApply (wp_uk_cmv γt γd γs h m (mword_of_int 0x900) a1_idx s1_idx
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
    iApply (wp_uk_cmv γt γd γs h1 mA (mword_of_int 0x902) a0_idx s2_idx
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
    iApply (wp_uk_jal γt γd γs h2 mB (mword_of_int 0x904)
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
    iApply (wp_uk_btype0 γt γd γs h4 mD (mword_of_int 0x908)
              (mword_of_int 12 : mword 13) a0_idx BLT t1 (mword_of_int 0x914) n
              Ht1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_908 with "Hcode"). }
    destruct t1.
    { (* open failed -- straight to the command loop's head *)
      iIntros (h5) "Hrun". iApply (ush_cmd_head h5 mD n with "Hcode Hrun"). }
    assert (E908 : add_vec_int (mword_of_int 0x908 : mword 64) 4
                   = mword_of_int 0x90c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E908. iIntros (h5) "Hrun".
    (* ---- 0x90c  bge s1,a0,0x900 -- THE BACK EDGE ---- *)
    remember (uv_btaken BGE (mD !!! Regidx s1_idx) (mD !!! Regidx a0_idx))
      as t2 eqn:Ht2.
    iApply (UkRunLeaf.wp_uk_btype_later γt γd γs h5 mD (mword_of_int 0x90c)
              (mword_of_int 8180 : mword 13) a0_idx s1_idx BGE t2
              (mword_of_int 0x900) n
              Ht2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_90c with "Hcode"). }
    destruct t2.
    { (* fd <= 2 -- round again, on the Löb hypothesis *)
      iNext. iIntros (h6) "Hrun". iApply ("IH" with "Hrun"). }
    iNext.
    assert (E90c : add_vec_int (mword_of_int 0x90c : mword 64) 4
                   = mword_of_int 0x910)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E90c. iIntros (h6) "Hrun".
    (* ---- 0x910  jal ra,0xcae <close> ---- *)
    iApply (wp_uk_jal γt γd γs h6 mD (mword_of_int 0x910)
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
    iApply (ush_cmd_head h8 _ n with "Hcode Hrun").
  Qed.


  (* ===================================================================== *)
  (* main -- the prologue and the preamble's setup.                         *)
  (*                                                                       *)
  (* Eight words of frame (ra and s0..s6), spilled and never reloaded:      *)
  (* main never returns.  0x8f6..0x8fc load O_RDWR and the address of the   *)
  (* "console" literal, and 0x900 is the loop above.                        *)
  (* ===================================================================== *)
  Lemma wp_ksh_main (h : CpuId) (m : regfile) (n : nat) :
    shk_code γt -∗
    urun γt γd γs h m (mword_of_int ShSyms.main) (8 + n) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun".
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
    iApply (wp_uk_caddi16sp_dn γt γd γs h m (mword_of_int 0x8e2)
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
    iApply (wp_uk_csdsp γt γd γs hs0 mA (mword_of_int 0x8e4)
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
    iApply (wp_uk_csdsp γt γd γs hs1 mA (mword_of_int 0x8e6)
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
    iApply (wp_uk_csdsp γt γd γs hs2 mA (mword_of_int 0x8e8)
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
    iApply (wp_uk_csdsp γt γd γs hs3 mA (mword_of_int 0x8ea)
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
    iApply (wp_uk_csdsp γt γd γs hs4 mA (mword_of_int 0x8ec)
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
    iApply (wp_uk_csdsp γt γd γs hs5 mA (mword_of_int 0x8ee)
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
    iApply (wp_uk_csdsp γt γd γs hs6 mA (mword_of_int 0x8f0)
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
    iApply (wp_uk_csdsp γt γd γs hs7 mA (mword_of_int 0x8f2)
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
    iApply (wp_uk_caddi4spn γt γd γs hs8 mA (mword_of_int 0x8f4)
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
    iApply (wp_uk_cli γt γd γs hb mB (mword_of_int 0x8f6)
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
    iApply (wp_uk_auipc γt γd γs hc mC (mword_of_int 0x8f8)
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
    iApply (wp_uk_addi γt γd γs hd mD (mword_of_int 0x8fc)
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
    iApply (wp_ksh_console he _ n with "Hcode Hrun").
  Qed.


  (* ===================================================================== *)
  (* start -- the ELF entry.  usys.S's crt: a two-word frame, then          *)
  (* main(), then exit() if it ever came back.  It does not: main's own     *)
  (* contract has no continuation, so 0x9dc is unreachable and never        *)
  (* appears here.  The [avail] arithmetic is the call chain spelled out:   *)
  (* start's two words and main's eight.                                    *)
  (* ===================================================================== *)
  Lemma wp_ksh_start (h : CpuId) (m : regfile) (n : nat) :
    shk_code γt -∗
    urun γt γd γs h m (mword_of_int ShSyms.start) (2 + (8 + n)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun".
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
    iApply (wp_uk_caddi_sp_dn γt γd γs h m (mword_of_int 0x9d0)
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
    iApply (wp_uk_csdsp γt γd γs h1 m1 (mword_of_int 0x9d2)
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
    iApply (wp_uk_csdsp γt γd γs h2 m1 (mword_of_int 0x9d4)
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
    iApply (wp_uk_caddi4spn γt γd γs h3 m1 (mword_of_int 0x9d6)
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
    iApply (wp_uk_jal γt γd γs h4 m2 (mword_of_int 0x9d8)
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
    iApply (wp_ksh_main h5 _ n with "Hcode Hrun").
  Qed.

End UkSh.
