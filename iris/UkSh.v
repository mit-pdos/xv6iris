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
(* 0x90c -- through [UkRunBr.wp_uk_btype_later].  Every leaf in            *)
(* UkRunLeaf.v is later-FREE, so UkRunBr.v had to exist first; see its     *)
(* header for the relocation ask.                                          *)
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
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile WpGpr.
Require Import AlignBits WpMmodeLeafBase.
Require Import UserBits UserPtTree UserExec ProcPtOwn.
Require Import WpUmodeBranch.
Require Import UmodeMem UmodeFetch UmodeArith UmodeAbi.
Require Import UserPerm UsysMemOk UexecWp UexecSlot UexecRet.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys UkRunBr.
Require Import UCodeShK.
Require Import TsoCtx.
Require User.ShSyms User.ShInstrs.
Local Open Scope Z_scope.
Import Defs.

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

  Local Notation CODE := "(C9d0 & C9d2 & C9d4 & C9d6 & C9d8 & C9dc & C8e2 & C8e4 & C8e6 & C8e8 & C8ea & C8ec & C8ee & C8f0 & C8f2 & C8f4 & C8f6 & C8f8 & C8fc & C900 & C902 & C904 & C908 & C90c & C910 & C914 & C918 & C91c & C920 & C922 & C926 & C92a & C92c & C930 & C932 & C934 & C938 & C93a & C93c & C940 & C944 & C948 & C94c & C94e & C952 & C956 & C95a & C95c & C960 & C964 & C966 & C96a & C96e & C970 & C974 & C976 & C97a & C97e & C982 & C986 & C98a & C98e & C990 & C994 & C998 & C99a & C99c & C99e & C9a2 & C9a4 & C9a6 & C9aa & C9ae & C9b0 & C9b4 & C9b8 & C9ba & C9be & C9c0 & C9c2 & C9c6 & C9ca & C9cc & Ccc6 & Ccc8 & Cccc & Ccae & Ccb0 & Ccb4 & Cc86 & Cc88)".

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
    iPoseProof "Hcode" as "#Hc". iDestruct "Hc" as CODE.
    destruct shk_syms_pins as (_ & _ & Hopen & _ & _). rewrite Hopen.
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
              with "Ccc6 Ccc8 Cccc Hrun Hcont").
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
    iPoseProof "Hcode" as "#Hc". iDestruct "Hc" as CODE.
    destruct shk_syms_pins as (_ & _ & _ & Hclose & _). rewrite Hclose.
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
              with "Ccae Ccb0 Ccb4 Hrun Hcont").
  Qed.

  (* ---- exit @0xc86, the arm with no continuation ---------------------- *)
  Lemma wp_ksh_exit (h : CpuId) (m : regfile) (avail : nat) :
    shk_code γt -∗
    urun γt γd γs h m (mword_of_int ShSyms.exit) avail -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun". iDestruct "Hcode" as CODE.
    destruct shk_syms_pins as (_ & _ & _ & _ & Hexit). rewrite Hexit.
    (* ---- 0xc86  c.li a7,2 ---- *)
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0xc86)
              (mword_of_int 2 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "Cc86 Hrun").
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
              with "Cc88 Hrun").
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
    iPoseProof "Hcode" as "#Hc". iDestruct "Hc" as CODE.
    (* ---- 0x900  c.mv a1,s1 ---- *)
    iApply (wp_uk_cmv γt γd γs h m (mword_of_int 0x900) a1_idx s1_idx
              (add_vec zero_reg (m !!! Regidx s1_idx)) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "C900 Hrun").
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
              with "C902 Hrun").
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
              ltac:(destruct shk_syms_pins as (_ & _ & Hop & _ & _);
                    rewrite Hop; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(destruct shk_syms_pins as (_ & _ & Hop & _ & _);
                    rewrite Hop; vm_compute; reflexivity)
              with "C904 Hrun").
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
              with "C908 Hrun").
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
    iApply (wp_uk_btype_later γt γd γs h5 mD (mword_of_int 0x90c)
              (mword_of_int 8180 : mword 13) a0_idx s1_idx BGE t2
              (mword_of_int 0x900) n
              Ht2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "C90c Hrun").
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
              ltac:(destruct shk_syms_pins as (_ & _ & _ & Hcl & _);
                    rewrite Hcl; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(destruct shk_syms_pins as (_ & _ & _ & Hcl & _);
                    rewrite Hcl; vm_compute; reflexivity)
              with "C910 Hrun").
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
    iPoseProof "Hcode" as "#Hc". iDestruct "Hc" as CODE.
    destruct shk_syms_pins as (_ & Hmain & _ & _ & _). rewrite Hmain.
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
              with "C8e2 Hrun").
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
              with "C8e4 Hw1 Hrun").
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
              with "C8e6 Hw2 Hrun").
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
              with "C8e8 Hw3 Hrun").
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
              with "C8ea Hw4 Hrun").
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
              with "C8ec Hw5 Hrun").
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
              with "C8ee Hw6 Hrun").
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
              with "C8f0 Hw7 Hrun").
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
              with "C8f2 Hw8 Hrun").
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
              with "C8f4 Hrun").
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
              ltac:(vm_compute; discriminate) with "C8f6 Hrun").
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
              with "C8f8 Hrun").
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
              with "C8fc Hrun").
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
    iPoseProof "Hcode" as "#Hc". iDestruct "Hc" as CODE.
    destruct shk_syms_pins as (Hstart & Hmain & _ & _ & _). rewrite Hstart.
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
              with "C9d0 Hrun").
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
              with "C9d2 Hw8 Hrun").
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
              with "C9d4 Hw0 Hrun").
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
              with "C9d6 Hrun").
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
              ltac:(rewrite Hmain; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hmain; vm_compute; reflexivity)
              with "C9d8 Hrun").
    iIntros (h5) "Hrun".
    (* ---- main(), which never returns ---- *)
    rewrite <- Hmain.
    iApply (wp_ksh_main h5 _ n with "Hcode Hrun").
  Qed.

End UkSh.
