(* ===================================================================== *)
(* UkSeccMain.v -- seccomp's [main] and [start], walked sh-style.         *)
(*                                                                        *)
(* Design: claude-notes/design/seccomp.md SS7 and the S3 rulings.  The     *)
(* program forks and waits, so it is not a program tree; its walk is      *)
(* stated at the run, init's shape ([UkInitMain]):                         *)
(*                                                                        *)
(*   argc < 2   the usage line on fd 2, exit(1)       [wp_ksecc_usage]     *)
(*   fork < 0   the fork diagnostic on fd 2, exit(1)   [wp_ksecc_forkfail]  *)
(*   parent     wait(0), exit(0)                       [wp_ksecc_parent]    *)
(*   child      the mask literal, seccomp(mask)        [wp_ksecc_child]     *)
(*                                                                        *)
(* THE CHILD LEAVES THE VERIFIED TIER AT ROW 23 (ruling G1).  [urun] is    *)
(* keyed at the full mask, so after [seccomp(mask)] there is no run to    *)
(* walk exec, its diagnostic or exit(1) on: [UkRunSecc.wp_uk_ecall_seccomp] *)
(* hands the RESUMED KEY to a slot family instead, and the walk takes that *)
(* family as a premise ([secc_univ]) -- the universe of the seccomp       *)
(* design, answered at the entry by [UexecSecc.useccomp_mint].  The key's  *)
(* mask is [and_vec secc_all] of the lui/addi literal, which is where      *)
(* [UkSeccLit.secc_mask_masked] enters, and its table is read off the      *)
(* child's LEDGER VIEW ([UserFd.utab], ruling G2): fork hands the child    *)
(* the parent's view, and the entry hands the parent the key's table.      *)
(*                                                                        *)
(* Every console write is on fd 2 and is paid by an abstract deposit       *)
(* ([secc_wdep]): the entry pays it out of the era licence.  Every         *)
(* immediate and address below is the catalog's ([UCodeSeccomp]).          *)
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
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys UkRunBr.
Require Import UCodeSeccomp.
Require Import CtxIdDefs.
Require User.SeccompSyms User.SeccompInstrs.
Require Import ChildTok.
Require Import UsysMemOk UexecSlot UexecRet.
Require Import UkProgAbi.
Require Import UkFork.
Require Import UkRunSecc.
Require Import UkSeccPutc UkSeccFprintf UkSeccLit.
Require Import FdSlots.
Require Import ProcGeom.     (* [PIDMAX] *)
Require Import ProcDefs.     (* [secc_all] *)
Require Import UserFd UserCwd UserChildren.
Require Import UexecSG.
Require Import UexecSecc.    (* [secc_masked] -- pure *)
Local Open Scope Z_scope.
Import Defs.

(* a reaped pid is a small positive ([UkInitMain]'s three, over plain Z) *)
Lemma secc_pid_lt_Z31 (z : Z) : 1 <= z <= PIDMAX -> z < Z31.
Proof. unfold PIDMAX, Z31. lia. Qed.
Lemma secc_pid_Z63 (z : Z) : 1 <= z <= PIDMAX -> 0 <= z < Z63.
Proof. unfold PIDMAX, Z63. lia. Qed.
Lemma secc_pid_ltb0 (z : Z) : 1 <= z <= PIDMAX -> Z.ltb z 0 = false.
Proof. unfold PIDMAX. intros H. apply Z.ltb_ge. lia. Qed.

Section UkSeccMain.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* the register reads a walk takes, through any number of updates *)
  Local Ltac name_m h x :=
    match goal with |- context [ urun _ h ?mm _ _ ] => set (x := mm) end.

  Local Ltac rg :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [ | vm_compute; discriminate ] ].

  (* ===================================================================== *)
  (* §0  WHAT THE WALK IS HANDED                                           *)
  (* ===================================================================== *)

  (* THE WRITE DEPOSIT, at every key whose ledger is [l] and every call on
     fd 2 -- what a console fd 2 buys (the entry pays it out of the era
     licence, [UexecSecc.secc_cons_pay]). *)
  Definition secc_wdep (N : uk_names Σ) (l : list fdstate) : iProp Σ :=
    (□ ∀ (m : regfile) (pc : mword 64),
        ⌜bv_signed (trunc32 (m !!! Regidx a0_idx)) = 2⌝ -∗
        ∃ fdep : sfam, udepwf_K N m pc 16 fdep (fun fdv => take NSTD fdv = l))%I.

  Global Instance secc_wdep_persistent N l : Persistent (secc_wdep N l).
  Proof using . rewrite /secc_wdep. apply _. Qed.

  (* THE UNIVERSE AT A TABLE VIEW: a slot at every masked key whose table
     is bounded by the view, at the trivial payload *)
  Definition secc_univ (v : list fdstate) : iProp Σ :=
    (□ ∀ W : uvis, ⌜secc_masked (uvis_secc W)⌝ -∗ ⌜tab_le (uvis_fd W) v⌝ -∗
        my_pay (uvis_gen W) (fun _ => True%I) -∗ uslot W)%I.

  Global Instance secc_univ_persistent v : Persistent (secc_univ v).
  Proof using . rewrite /secc_univ. apply _. Qed.

  (* ===================================================================== *)
  (* §1  THE STUBS                                                         *)
  (* ===================================================================== *)

  (* write(fd, buf, 1) @0x36c, one byte on fd 2, the ledger at its view
     riding through *)
  Lemma ksecc_wb_cons (N : uk_names Σ) (l v : list fdstate) (fdw : mword 64)
      (b : bv 8) :
    bv_signed (trunc32 fdw) = 2 ->
    secc_wdep N l -∗
    ksecc_wb N fdw b (ustd_at (ukn_fd N) l v) (ustd_at (ukn_fd N) l v).
  Proof using .
    intros Hfd. iIntros "#Hwd" (ua h m avail) "%Ha0 %Ha1 %Ha2 #Hcode [Hstd Hb] Hrun Hcont".
    destruct seccomp_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwrite).
    rewrite Hwrite.
    iApply (wp_uk_cli N h m (mword_of_int 0x36c)
              (mword_of_int 16 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_seccomp_36c with "Hcode"). }
    assert (E0 : add_vec_int (mword_of_int 0x36c : mword 64) 2
                 = mword_of_int 0x36e)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 16 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    assert (Ha0' : <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m !!! Regidx a0_idx
                   = fdw) by (rewrite upd_ne; [ exact Ha0 | vm_compute; discriminate ]).
    assert (Ha1' : <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m !!! Regidx a1_idx
                   = ua) by (rewrite upd_ne; [ exact Ha1 | vm_compute; discriminate ]).
    iDestruct ("Hwd" $! (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                 (mword_of_int 0x36e) with "[%]") as (fdep) "Hdep";
      [ rewrite Ha0'; exact Hfd | ].
    set (m1 := <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m).
    assert (Hn16 : usysno m1 = 16).
    { unfold m1, usysno. rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 16 : mword 64)).
      vm_compute. reflexivity. }
    assert (Hal4 : is_aligned_vaddr (Virtaddr (add_vec_int (mword_of_int 0x36e : mword 64) 4)) 2
                   = true) by (vm_compute; reflexivity).
    pose proof (fun fdv => ustd_at_agree (ukn_fd N) fdv l v) as Hag.
    pose proof (fun M pmv sz =>
                  usrc_ok_ubytesq (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz (DfracOwn 1)
                    (m1 !!! Regidx (mword_of_int 11)) 1 (fun _ => b)) as Hsrc.
    iApply (wp_uk_ecall_write_at N h1 m1 (mword_of_int 0x36e) avail fdep
              (ustd_at (ukn_fd N) l v)
              (UserHeap.ubytesq (ukn_d N) (DfracOwn 1)
                 (uint (m1 !!! Regidx (mword_of_int 11))) 1 (fun _ => b))
              (fun fdv => take NSTD fdv = l) 1 (fun _ => b)
              Hn16 Hal4 Hag Hsrc
              with "[] Hrun Hdep Hstd [Hb]").
    { iApply (uis_seccomp_36e with "Hcode"). }
    { rewrite Ha1' /UserHeap.ubytesq /=. rewrite Z.add_0_r. by iFrame "Hb". }
    iIntros (h' r W cw' cs') "_ _ _ _ _ _ Hstd Hb _ Hrun".
    assert (E1 : add_vec_int (mword_of_int 0x36e : mword 64) 4
                 = mword_of_int 0x372)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    name_m h' mr1.
    iApply (wp_uk_cjr N h' mr1 (mword_of_int 0x372) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(unfold mr1; rg; reflexivity)
              with "[] Hrun").
    { iApply (uis_seccomp_372 with "Hcode"). }
    iIntros (h'') "Hrun".
    iApply ("Hcont" $! h'' r with "[Hstd Hb] Hrun").
    iFrame "Hstd". rewrite Ha1' /UserHeap.ubytesq /=. rewrite Z.add_0_r.
    iDestruct "Hb" as "[$ _]".
  Qed.

  (* ...and a whole diagnostic's worth of them, the ledger constant *)
  Lemma ksecc_pay_seq_cons (N : uk_names Σ) (l v : list fdstate) (fdw : mword 64)
      (fb : nat -> bv 8) (k : nat) :
    bv_signed (trunc32 fdw) = 2 ->
    forall i : nat,
      secc_wdep N l -∗
      ksecc_pay_seq N fdw fb i k (ustd_at (ukn_fd N) l v) (ustd_at (ukn_fd N) l v).
  Proof using .
    intros Hfd. induction k as [| k IH]; intros i; iIntros "#Hwd".
    - cbn [ksecc_pay_seq]. iIntros "$".
    - cbn [ksecc_pay_seq]. iExists (ustd_at (ukn_fd N) l v).
      iSplitR; [ iApply (ksecc_wb_cons N l v fdw (fb i) Hfd with "Hwd") | ].
      iApply (IH (S i) with "Hwd").
  Qed.

  (* exit(status) @0x34c: the payload is the program's own, and free *)
  Lemma wp_ksecc_exit (N : uk_names Σ) (h : CpuId) (m : regfile) (avail : nat) :
    (forall s : Z, ⊢ ukn_pay N s) ->
    seccomp_code (ukn_t N) -∗
    urun N h m (mword_of_int SeccompSyms.exit) avail -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hq. iIntros "#Hcode Hrun".
    destruct seccomp_syms_pins
      as (_ & _ & _ & _ & _ & _ & Hexit & _ & _ & _ & _).
    rewrite Hexit.
    iApply (wp_uk_cli N h m (mword_of_int 0x34c)
              (mword_of_int 2 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_seccomp_34c with "Hcode"). }
    assert (E0 : add_vec_int (mword_of_int 0x34c : mword 64) 2
                 = mword_of_int 0x34e)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 2 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 2 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    name_m h1 mr2.
    iApply (wp_uk_ecall_exit N h1 mr2 (mword_of_int 0x34e) avail
              ltac:(unfold usysno, mr2; rg; vm_compute; reflexivity)
              with "[] [] Hrun").
    { iApply (uis_seccomp_34e with "Hcode"). }
    { iApply Hq. }
  Qed.

  (* wait(0) @0x354, at the null status pointer *)
  Lemma wp_ksecc_wait (N : uk_names Σ) (h : CpuId) (m : regfile) (avail : nat)
      (cs : gset gname) :
    uint (m !!! Regidx a0_idx) = 0 ->
    seccomp_code (ukn_t N) -∗
    urun N h m (mword_of_int SeccompSyms.wait) avail -∗
    uch (ukn_ch N) cs -∗
    (∀ (h' : CpuId) (ret : mword 64) (cs' : gset gname),
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 3 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       uch (ukn_ch N) cs' -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpsok_free.
    intros Hz.
    iIntros "#Hcode Hrun Hch Hcont".
    destruct seccomp_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & Hwait & _ & _ & _).
    rewrite Hwait.
    iApply (wp_uk_cli N h m (mword_of_int 0x354)
              (mword_of_int 3 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_seccomp_354 with "Hcode"). }
    assert (E0 : add_vec_int (mword_of_int 0x354 : mword 64) 2
                 = mword_of_int 0x356)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 3 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 3 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    name_m h1 mr3.
    iApply (wp_uk_ecall_wait_null_live N h1 mr3 (mword_of_int 0x356) avail cs
              ltac:(unfold usysno, mr3; rg; vm_compute; reflexivity)
              ltac:(unfold mr3; rg; exact Hz) ltac:(vm_compute; reflexivity)
              with "[] Hrun [] Hch").
    { iApply (uis_seccomp_356 with "Hcode"). }
    { iApply udepw_of_psok; [ apply Hpsok_free; free_lit | ];
      (discriminate || assumption || (vm_compute; discriminate)). }
    assert (E1 : add_vec_int (mword_of_int 0x356 : mword 64) 4
                 = mword_of_int 0x35a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2 ret cs') "_ _ Hrun Hch".
    name_m h2 mr4.
    iApply (wp_uk_cjr N h2 mr4 (mword_of_int 0x35a) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(unfold mr4; rg; reflexivity)
              with "[] Hrun").
    { iApply (uis_seccomp_35a with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret cs' with "Hrun Hch").
  Qed.

  (* seccomp(mask) @0x3f4: the stub's ecall is row 23, and the process
     leaves the verified tier into the slot family it is handed *)
  Lemma wp_ksecc_seccomp_stub (N : uk_names Σ) (h : CpuId) (m : regfile)
      (avail : nat) (v : list fdstate) :
    seccomp_code (ukn_t N) -∗
    urun N h m (mword_of_int SeccompSyms.seccomp) avail -∗
    utab (ukn_fd N) v -∗
    (∀ W : uvis,
       ⌜uvis_secc W = and_vec secc_all (m !!! Regidx a0_idx)⌝ -∗
       ⌜tab_le (uvis_fd W) v⌝ -∗
       my_pay (uvis_gen W) (ukn_pay N) -∗
       uslot W) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpsok_free.
    iIntros "#Hcode Hrun Htab Hcont".
    destruct seccomp_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsecc & _).
    rewrite Hsecc.
    iApply (wp_uk_cli N h m (mword_of_int 0x3f4)
              (mword_of_int 23 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_seccomp_3f4 with "Hcode"). }
    assert (E0 : add_vec_int (mword_of_int 0x3f4 : mword 64) 2
                 = mword_of_int 0x3f6)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 23 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 23 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    name_m h1 mr5.
    iApply (wp_uk_ecall_seccomp N h1 mr5 (mword_of_int 0x3f6) avail v
              ltac:(unfold usysno, mr5; rg; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun [] Htab").
    { iApply (uis_seccomp_3f6 with "Hcode"). }
    { iApply udepw_of_psok; [ apply Hpsok_free; free_lit | ];
      (discriminate || assumption || (vm_compute; discriminate)). }
    iIntros (W) "%Hsc %Hle Hmy".
    iApply ("Hcont" with "[%] [%] Hmy"); [ | exact Hle ].
    rewrite Hsc. rg. reflexivity.
  Qed.

  (* ===================================================================== *)
  (* §2  THE TWO FD-2 DIAGNOSTICS, and exit(1)                             *)
  (*                                                                       *)
  (*   auipc/addi a1,<lit> ; li a0,2 ; jal fprintf ; li a0,1 ; jal exit    *)
  (* ===================================================================== *)

  (* the usage line @0x4e (after main's [sd s1]) *)
  Lemma wp_ksecc_usage (N : uk_names Σ) (h : CpuId) (m : regfile) (n : nat)
      (l v : list fdstate) :
    (forall s : Z, ⊢ ukn_pay N s) ->
    seccomp_code (ukn_t N) -∗
    seccomp_rodata (ukn_t N) -∗
    secc_wdep N l -∗
    ustd_at (ukn_fd N) l v -∗
    urun N h m (mword_of_int 0x4e) (10 + (12 + (4 + n))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hq. iIntros "#Hcode #Hro #Hwd Hstd Hrun".
    destruct seccomp_syms_pins
      as (_ & _ & Hfprintf & _ & _ & _ & Hexit & _ & _ & _ & _).
    (* ---- 0x4e  auipc a1,0x1 ---- *)
    iApply (wp_uk_auipc N h m (mword_of_int 0x4e)
              (mword_of_int 1 : mword 20) a1_idx (mword_of_int 0x104e)
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_seccomp_4e with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x4e : mword 64) 4
                 = mword_of_int 0x52);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h1) "Hrun".
    (* ---- 0x52  addi a1,a1,-1790 -- the literal at 0x950 ---- *)
    name_m h1 mr6.
    iApply (wp_uk_addi N h1 mr6 (mword_of_int 0x52)
              (mword_of_int 2306 : mword 12) a1_idx a1_idx
              (mword_of_int 0x950) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(unfold mr6; rg; apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_seccomp_52 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x52 : mword 64) 4
                 = mword_of_int 0x56);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h2) "Hrun".
    (* ---- 0x56  c.li a0,2 ---- *)
    iApply (wp_uk_cli N h2 _ (mword_of_int 0x56)
              (mword_of_int 2 : mword 6) a0_idx (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_seccomp_56 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x56 : mword 64) 2
                 = mword_of_int 0x58);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h3) "Hrun".
    (* ---- 0x58  jal ra,0x778 <fprintf> ---- *)
    iApply (wp_uk_jal N h3 _ (mword_of_int 0x58)
              (mword_of_int 1824 : mword 21) ra_idx
              (mword_of_int SeccompSyms.fprintf) (mword_of_int 0x5c)
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hfprintf; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hfprintf; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_seccomp_58 with "Hcode"). }
    iIntros (h4) "Hrun".
    match goal with
    | |- context [ urun N h4 ?mm _ _ ] => set (m4 := mm)
    end.
    assert (Hra4 : m4 !!! Regidx ra_idx = (mword_of_int 0x5c : mword 64))
      by (unfold m4; rg; reflexivity).
    assert (Ha1_4 : m4 !!! Regidx a1_idx = mword_of_int 0x950)
      by (unfold m4; rg; reflexivity).
    assert (Hfd4 : bv_signed (trunc32 (m4 !!! Regidx a0_idx)) = 2)
      by (unfold m4; rg; vm_compute; reflexivity).
    assert (Hlen : 0x950 + Z.of_nat 30 + 2 < 2 ^ 31) by lia.
    assert (Hl30 : Z.of_nat 30 < 2 ^ 31) by lia.
    iPoseProof (ksecc_pay_seq_cons N l v (m4 !!! Regidx a0_idx) (secc_lit 0x950)
                  30 Hfd4 0 with "Hwd") as "Hseq".
    iApply (wp_ksecc_fprintf N 0x950 30 (secc_lit 0x950) h4 m4 n
              (ustd_at (ukn_fd N) l v) (ustd_at (ukn_fd N) l v)
              ltac:(lia) Hlen ltac:(lia)
              (fun j Hj => secc_lit_nopct 0x950 30 j secc_lit_usage_ok Hj)
              Ha1_4
              with "Hseq Hcode [] Hstd Hrun").
    { iApply (secc_lit_str (ukn_t N) 0x950 30 secc_lit_usage_ok Hl30 with "Hro"). }
    iIntros (h5 m5) "_ Hstd Hrun".
    rewrite (_ : ret_pc (m4 !!! Regidx ra_idx)
                 = (mword_of_int 0x5c : mword 64));
      [ | rewrite Hra4; apply bv_eq; vm_compute; reflexivity ].
    (* ---- 0x5c  c.li a0,1 ; 0x5e  jal exit ---- *)
    iApply (wp_uk_cli N h5 m5 (mword_of_int 0x5c)
              (mword_of_int 1 : mword 6) a0_idx (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_seccomp_5c with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x5c : mword 64) 2
                 = mword_of_int 0x5e);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h6) "Hrun".
    iApply (wp_uk_jal N h6 _ (mword_of_int 0x5e)
              (mword_of_int 750 : mword 21) ra_idx
              (mword_of_int SeccompSyms.exit) (mword_of_int 0x62)
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hexit; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hexit; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_seccomp_5e with "Hcode"). }
    iIntros (h7) "Hrun".
    iApply (wp_ksecc_exit N h7 _ _ Hq with "Hcode Hrun").
  Qed.

  (* the fork diagnostic @0x62 *)
  Lemma wp_ksecc_forkfail (N : uk_names Σ) (h : CpuId) (m : regfile) (n : nat)
      (l v : list fdstate) :
    (forall s : Z, ⊢ ukn_pay N s) ->
    seccomp_code (ukn_t N) -∗
    seccomp_rodata (ukn_t N) -∗
    secc_wdep N l -∗
    ustd_at (ukn_fd N) l v -∗
    urun N h m (mword_of_int 0x62) (10 + (12 + (4 + n))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hq. iIntros "#Hcode #Hro #Hwd Hstd Hrun".
    destruct seccomp_syms_pins
      as (_ & _ & Hfprintf & _ & _ & _ & Hexit & _ & _ & _ & _).
    (* ---- 0x62  auipc a1,0x1 ---- *)
    iApply (wp_uk_auipc N h m (mword_of_int 0x62)
              (mword_of_int 1 : mword 20) a1_idx (mword_of_int 0x1062)
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_seccomp_62 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x62 : mword 64) 4
                 = mword_of_int 0x66);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h1) "Hrun".
    (* ---- 0x66  addi a1,a1,-1770 -- the literal at 0x978 ---- *)
    name_m h1 mr7.
    iApply (wp_uk_addi N h1 mr7 (mword_of_int 0x66)
              (mword_of_int 2326 : mword 12) a1_idx a1_idx
              (mword_of_int 0x978) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(unfold mr7; rg; apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_seccomp_66 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x66 : mword 64) 4
                 = mword_of_int 0x6a);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h2) "Hrun".
    (* ---- 0x6a  c.li a0,2 ---- *)
    iApply (wp_uk_cli N h2 _ (mword_of_int 0x6a)
              (mword_of_int 2 : mword 6) a0_idx (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_seccomp_6a with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x6a : mword 64) 2
                 = mword_of_int 0x6c);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h3) "Hrun".
    (* ---- 0x6c  jal ra,0x778 <fprintf> ---- *)
    iApply (wp_uk_jal N h3 _ (mword_of_int 0x6c)
              (mword_of_int 1804 : mword 21) ra_idx
              (mword_of_int SeccompSyms.fprintf) (mword_of_int 0x70)
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hfprintf; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hfprintf; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_seccomp_6c with "Hcode"). }
    iIntros (h4) "Hrun".
    match goal with
    | |- context [ urun N h4 ?mm _ _ ] => set (m4 := mm)
    end.
    assert (Hra4 : m4 !!! Regidx ra_idx = (mword_of_int 0x70 : mword 64))
      by (unfold m4; rg; reflexivity).
    assert (Ha1_4 : m4 !!! Regidx a1_idx = mword_of_int 0x978)
      by (unfold m4; rg; reflexivity).
    assert (Hfd4 : bv_signed (trunc32 (m4 !!! Regidx a0_idx)) = 2)
      by (unfold m4; rg; vm_compute; reflexivity).
    assert (Hlen : 0x978 + Z.of_nat 21 + 2 < 2 ^ 31) by lia.
    assert (Hl21 : Z.of_nat 21 < 2 ^ 31) by lia.
    iPoseProof (ksecc_pay_seq_cons N l v (m4 !!! Regidx a0_idx) (secc_lit 0x978)
                  21 Hfd4 0 with "Hwd") as "Hseq".
    iApply (wp_ksecc_fprintf N 0x978 21 (secc_lit 0x978) h4 m4 n
              (ustd_at (ukn_fd N) l v) (ustd_at (ukn_fd N) l v)
              ltac:(lia) Hlen ltac:(lia)
              (fun j Hj => secc_lit_nopct 0x978 21 j secc_lit_fork_ok Hj)
              Ha1_4
              with "Hseq Hcode [] Hstd Hrun").
    { iApply (secc_lit_str (ukn_t N) 0x978 21 secc_lit_fork_ok Hl21 with "Hro"). }
    iIntros (h5 m5) "_ Hstd Hrun".
    rewrite (_ : ret_pc (m4 !!! Regidx ra_idx)
                 = (mword_of_int 0x70 : mword 64));
      [ | rewrite Hra4; apply bv_eq; vm_compute; reflexivity ].
    (* ---- 0x70  c.li a0,1 ; 0x72  jal exit ---- *)
    iApply (wp_uk_cli N h5 m5 (mword_of_int 0x70)
              (mword_of_int 1 : mword 6) a0_idx (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_seccomp_70 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x70 : mword 64) 2
                 = mword_of_int 0x72);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h6) "Hrun".
    iApply (wp_uk_jal N h6 _ (mword_of_int 0x72)
              (mword_of_int 730 : mword 21) ra_idx
              (mword_of_int SeccompSyms.exit) (mword_of_int 0x76)
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hexit; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hexit; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_seccomp_72 with "Hcode"). }
    iIntros (h7) "Hrun".
    iApply (wp_ksecc_exit N h7 _ _ Hq with "Hcode Hrun").
  Qed.

  (* ===================================================================== *)
  (* §3  AFTER THE FORK: the three arms at 0x16                             *)
  (* ===================================================================== *)

  (* THE PARENT, fork having returned the child's pid: bltz not taken,
     c.bnez taken to 0x8a; wait(0); exit(0) *)
  Lemma wp_ksecc_parent (N : uk_names Σ) (h : CpuId) (m : regfile) (avail : nat)
      (pidv : mword 32) (cs : gset gname) :
    (forall s : Z, ⊢ ukn_pay N s) ->
    (1 <= bv_unsigned pidv <= PIDMAX)%Z ->
    m !!! Regidx a0_idx = (sign_extend' 64 pidv : mword 64) ->
    seccomp_code (ukn_t N) -∗
    uch (ukn_ch N) cs -∗
    urun N h m (mword_of_int 0x16) avail -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpsok_free.
    intros Hq Hrng Ha0. iIntros "#Hcode Hch Hrun".
    destruct seccomp_syms_pins
      as (_ & _ & _ & _ & _ & _ & Hexit & Hwait & _ & _ & _).
    assert (Hpv : (sign_extend' 64 pidv : mword 64) = mword_of_int (bv_unsigned pidv))
      by exact (sext32_small pidv (secc_pid_lt_Z31 _ Hrng)).
    (* ---- 0x16  blt a0,x0,0x62 -- NOT taken ---- *)
    assert (Hblt : false = uv_btaken BLT (m !!! Regidx a0_idx) zero_reg).
    { rewrite Ha0 Hpv. cbn [uv_btaken]. rewrite zero_reg_moi.
      rewrite (moi_lt_s (bv_unsigned pidv) 0 (secc_pid_Z63 _ Hrng)
                 ltac:(unfold Z63; lia)).
      rewrite (secc_pid_ltb0 _ Hrng). reflexivity. }
    iApply (wp_uk_btype0 N h m (mword_of_int 0x16)
              (mword_of_int 76 : mword 13) a0_idx BLT false
              (add_vec (mword_of_int 0x16 : mword 64)
                 (sign_extend' 64 (mword_of_int 76 : mword 13)))
              avail Hblt eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_seccomp_16 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x16 : mword 64) 4
                 = mword_of_int 0x1a);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h1) "Hrun".
    (* ---- 0x1a  c.bnez a0,0x8a -- TAKEN ---- *)
    assert (Hbnz : true = neq_vec (m !!! Regidx a0_idx) zero_reg).
    { rewrite Ha0 Hpv.
      rewrite (moi_neq_zero (bv_unsigned pidv)
                 ltac:(pose proof (secc_pid_Z63 _ Hrng); unfold Z63, Z64 in *; lia)).
      destruct (Z.eqb_spec (bv_unsigned pidv) 0) as [He | _];
        [ exfalso; lia | reflexivity ]. }
    assert (Etgt : (mword_of_int 0x8a : mword 64)
                   = add_vec (mword_of_int 0x1a : mword 64)
                       (sign_extend' 64
                          (sign_extend' 13
                             (concat_vec (mword_of_int 56 : mword 8) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cbnez N h1 m (mword_of_int 0x1a)
              (mword_of_int 56 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              true (mword_of_int 0x8a) avail
              ltac:(vm_compute; reflexivity) Hbnz Etgt
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_seccomp_1a with "Hcode"). }
    iIntros (h2) "Hrun".
    (* ---- 0x8a  c.li a0,0 ; 0x8c  jal wait ---- *)
    iApply (wp_uk_cli N h2 m (mword_of_int 0x8a)
              (mword_of_int 0 : mword 6) a0_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_seccomp_8a with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x8a : mword 64) 2
                 = mword_of_int 0x8c);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h3) "Hrun".
    iApply (wp_uk_jal N h3 _ (mword_of_int 0x8c)
              (mword_of_int 712 : mword 21) ra_idx
              (mword_of_int SeccompSyms.wait) (mword_of_int 0x90) avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hwait; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hwait; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_seccomp_8c with "Hcode"). }
    iIntros (h4) "Hrun".
    name_m h4 mr8.
    iApply (wp_ksecc_wait N h4 mr8 avail cs
              ltac:(unfold mr8; rg; vm_compute; reflexivity)
              with "Hcode Hrun Hch").
    iIntros (h5 ret cs') "Hrun _".
    rewrite (_ : ret_pc (<[Regidx ra_idx := regval_into_reg (mword_of_int 0x90 : mword 64)]>
                           (<[Regidx a0_idx := regval_into_reg
                               (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64)]> m)
                          !!! Regidx ra_idx)
                 = (mword_of_int 0x90 : mword 64));
      [ | rg; apply bv_eq; vm_compute; reflexivity ].
    (* ---- 0x90  c.li a0,0 ; 0x92  jal exit ---- *)
    iApply (wp_uk_cli N h5 _ (mword_of_int 0x90)
              (mword_of_int 0 : mword 6) a0_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_seccomp_90 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x90 : mword 64) 2
                 = mword_of_int 0x92);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h6) "Hrun".
    iApply (wp_uk_jal N h6 _ (mword_of_int 0x92)
              (mword_of_int 698 : mword 21) ra_idx
              (mword_of_int SeccompSyms.exit) (mword_of_int 0x96) avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hexit; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hexit; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_seccomp_92 with "Hcode"). }
    iIntros (h7) "Hrun".
    iApply (wp_ksecc_exit N h7 _ _ Hq with "Hcode Hrun").
  Qed.

  (* THE FAILED FORK: bltz taken to the diagnostic *)
  Lemma wp_ksecc_forkneg (N : uk_names Σ) (h : CpuId) (m : regfile) (n : nat)
      (l v : list fdstate) :
    (forall s : Z, ⊢ ukn_pay N s) ->
    m !!! Regidx a0_idx = (mword_of_int (-1) : mword 64) ->
    seccomp_code (ukn_t N) -∗
    seccomp_rodata (ukn_t N) -∗
    secc_wdep N l -∗
    ustd_at (ukn_fd N) l v -∗
    urun N h m (mword_of_int 0x16) (10 + (12 + (4 + n))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hq Ha0. iIntros "#Hcode #Hro #Hwd Hstd Hrun".
    assert (Hblt : true = uv_btaken BLT (m !!! Regidx a0_idx) zero_reg)
      by (rewrite Ha0 zero_reg_moi; vm_compute; reflexivity).
    assert (Etgt : (mword_of_int 0x62 : mword 64)
                   = add_vec (mword_of_int 0x16 : mword 64)
                       (sign_extend' 64 (mword_of_int 76 : mword 13)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_btype0 N h m (mword_of_int 0x16)
              (mword_of_int 76 : mword 13) a0_idx BLT true
              (mword_of_int 0x62) _ Hblt Etgt
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_seccomp_16 with "Hcode"). }
    iIntros (h1) "Hrun".
    iApply (wp_ksecc_forkfail N h1 m n l v Hq with "Hcode Hro Hwd Hstd Hrun").
  Qed.

  (* THE CHILD: a0 = 0, so both branches fall through to the mask literal
     and seccomp(mask) -- and there the child is the universe *)
  Lemma wp_ksecc_child (N : uk_names Σ) (h : CpuId) (m : regfile) (avail : nat)
      (v : list fdstate) :
    ukn_pay N = (fun _ => True%I) ->
    m !!! Regidx a0_idx = (mword_of_int 0 : mword 64) ->
    seccomp_code (ukn_t N) -∗
    secc_univ v -∗
    utab (ukn_fd N) v -∗
    urun N h m (mword_of_int 0x16) avail -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpsok_free.
    intros Hpay Ha0. iIntros "#Hcode #Huniv Htab Hrun".
    destruct seccomp_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsecc & _).
    (* ---- 0x16  blt a0,x0 -- NOT taken ---- *)
    assert (Hblt : false = uv_btaken BLT (m !!! Regidx a0_idx) zero_reg).
    { rewrite Ha0. cbn [uv_btaken]. rewrite zero_reg_moi.
      assert (Hz0 : 0 <= 0 < Z63) by (unfold Z63; lia).
      rewrite (moi_lt_s 0 0 Hz0 Hz0). reflexivity. }
    iApply (wp_uk_btype0 N h m (mword_of_int 0x16)
              (mword_of_int 76 : mword 13) a0_idx BLT false
              (add_vec (mword_of_int 0x16 : mword 64)
                 (sign_extend' 64 (mword_of_int 76 : mword 13)))
              avail Hblt eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_seccomp_16 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x16 : mword 64) 4
                 = mword_of_int 0x1a);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h1) "Hrun".
    (* ---- 0x1a  c.bnez a0 -- NOT taken ---- *)
    assert (Hbnz : false = neq_vec (m !!! Regidx a0_idx) zero_reg)
      by (rewrite Ha0 zero_reg_moi; vm_compute; reflexivity).
    iApply (wp_uk_cbnez N h1 m (mword_of_int 0x1a)
              (mword_of_int 56 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              false
              (add_vec (mword_of_int 0x1a : mword 64)
                 (sign_extend' 64 (sign_extend' 13
                    (concat_vec (mword_of_int 56 : mword 8) ('b"0")))))
              avail
              ltac:(vm_compute; reflexivity) Hbnz eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_seccomp_1a with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x1a : mword 64) 2
                 = mword_of_int 0x1c);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h2) "Hrun".
    (* ---- 0x1c  lui a0,0xffe18 ; 0x20  addi a0,a0,-65 -- THE MASK ---- *)
    iApply (wp_uk_lui N h2 m (mword_of_int 0x1c)
              (mword_of_int 1048088 : mword 20) a0_idx
              (luival (mword_of_int 1048088 : mword 20)) avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_seccomp_1c with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x1c : mword 64) 4
                 = mword_of_int 0x20);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h3) "Hrun".
    name_m h3 mr9.
    iApply (wp_uk_addi N h3 mr9 (mword_of_int 0x20)
              (mword_of_int 4031 : mword 12) a0_idx a0_idx secc_mask_lit avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(unfold mr9; rg; reflexivity)
              with "[] Hrun").
    { iApply (uis_seccomp_20 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x20 : mword 64) 4
                 = mword_of_int 0x24);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h4) "Hrun".
    (* ---- 0x24  jal ra,0x3f4 <seccomp> ---- *)
    iApply (wp_uk_jal N h4 _ (mword_of_int 0x24)
              (mword_of_int 976 : mword 21) ra_idx
              (mword_of_int SeccompSyms.seccomp) (mword_of_int 0x28) avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hsecc; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hsecc; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_seccomp_24 with "Hcode"). }
    iIntros (h5) "Hrun".
    iApply (wp_ksecc_seccomp_stub N h5 _ avail v with "Hcode Hrun Htab").
    (* ---- ROW 23: THE ONE PLACE THE LITERAL ENTERS ---- *)
    iIntros (W) "%Hsc %Hle Hmy".
    rewrite Hpay.
    iApply ("Huniv" $! W with "[%] [%] Hmy"); [ | exact Hle ].
    rewrite Hsc. rg. exact secc_mask_masked.
  Qed.

  (* ===================================================================== *)
  (* §4  main @0x0 and start @0x96                                          *)
  (* ===================================================================== *)

  (* WHAT CROSSES THE FORK: the text, at the child's own name *)
  Local Instance forkable_secc_code :
    Forkable (fun gt _ _ => seccomp_code gt).
  Proof using .
    eapply Forkable_ext;
      [ | apply (forkable_utext_map SeccompInstrs.seccomp_bytes) ].
    intros gt gd gs. rewrite /seccomp_code /utext_img. reflexivity.
  Qed.

  (* main(argc, argv): the frame, argc's test, the fork and its three arms *)
  Lemma wp_ksecc_main (N : uk_names Σ) (h : CpuId) (m : regfile) (na n : nat)
      (l v : list fdstate) (szv c : Z) (cs : gset gname) :
    (forall s : Z, ⊢ ukn_pay N s) ->
    m !!! Regidx a0_idx = mword_of_int (Z.of_nat na) ->
    (Z.of_nat na < 2 ^ 31)%Z ->
    seccomp_code (ukn_t N) -∗
    seccomp_rodata (ukn_t N) -∗
    secc_wdep N l -∗
    secc_univ v -∗
    ustd_at (ukn_fd N) l v -∗
    usz (ukn_s N) szv -∗
    ucwd (ukn_cwd N) c -∗
    uch (ukn_ch N) cs -∗
    urun N h m (mword_of_int SeccompSyms.main) (4 + (10 + (12 + (4 + n)))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpsok_free.
    intros Hq Ha0 Hna.
    iIntros "#Hcode #Hro #Hwd #Huniv Hstd Hsz Hcwd Hch Hrun".
    destruct seccomp_syms_pins
      as (_ & Hmain & _ & _ & _ & Hfork & _ & _ & _ & _ & _).
    rewrite Hmain.
    set (k := (10 + (12 + (4 + n)))%nat).
    iDestruct (urun_stack with "Hrun") as %[Hal8' Hroom'].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0e.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0e).
    clear Hsp0e.
    assert (Hal8 : uint sp0 mod 8 = 0) by exact Hal8'.
    assert (Hlo : 32 <= uint sp0) by (clear -Hroom'; lia).
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                   = bv_unsigned sp0 - 32).
    { replace (- (8 * Z.of_nat 4)) with (-32) by lia.
      exact (uv_avi_neg sp0 32 ltac:(apply Z.leb_le; reflexivity)
               ltac:(rewrite <- uint_unsigned; exact Hlo)). }
    assert (Hsp32 : uint (add_vec_int sp0 (- (8 * Z.of_nat 4))) = uint sp0 - 32)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Ho24 : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
      by (vm_compute; reflexivity).
    assert (Ho16 : uoff_sdsp (mword_of_int 2 : mword 6) = 16)
      by (vm_compute; reflexivity).
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    (* ---- 0x0  c.addi sp,sp,-32 ---- *)
    iApply (wp_uk_caddi_sp_dn N h m (mword_of_int 0x0)
              (mword_of_int 32 : mword 6) 4 k
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_seccomp_00 with "Hcode"). }
    iIntros "Hframe".
    rewrite Hsp.
    rewrite (_ : add_vec_int (mword_of_int 0x0 : mword 64) 2
                 = mword_of_int 0x2);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h0) "Hrun".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 4)))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 4)))
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg _)).
    iDestruct (ustack_4_open with "Hframe")
      as "(_ & [%w1 Hw1] & [%w2 Hw2] & [%w3 Hw3] & _)".
    (* ---- 0x2  c.sdsp ra,24(sp) ; 0x4  c.sdsp s0,16(sp) ---- *)
    iApply (wp_uk_csdsp N h0 m1 (mword_of_int 0x2)
              (mword_of_int 3 : mword 6) ra_idx (uint sp0 - 8) w1 k
              ltac:(rewrite Hsp1 Hsp32 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw1 Hrun").
    { iApply (uis_seccomp_02 with "Hcode"). }
    iIntros "_".
    rewrite (_ : add_vec_int (mword_of_int 0x2 : mword 64) 2
                 = mword_of_int 0x4);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h1) "Hrun".
    iApply (wp_uk_csdsp N h1 m1 (mword_of_int 0x4)
              (mword_of_int 2 : mword 6) s0_idx (uint sp0 - 16) w2 k
              ltac:(rewrite Hsp1 Hsp32 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw2 Hrun").
    { iApply (uis_seccomp_04 with "Hcode"). }
    iIntros "_".
    rewrite (_ : add_vec_int (mword_of_int 0x4 : mword 64) 2
                 = mword_of_int 0x6);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h2) "Hrun".
    (* ---- 0x6  c.addi4spn s0,sp,32 ---- *)
    iApply (wp_uk_caddi4spn N h2 m1 (mword_of_int 0x6)
              (mword_of_int 0 : mword 3) (mword_of_int 8 : mword 8) s0_idx
              (add_vec (m1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))
              k
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_seccomp_06 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x6 : mword 64) 2
                 = mword_of_int 0x8);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h3) "Hrun".
    set (m2 := <[Regidx s0_idx
                 := regval_into_reg
                      (add_vec (m1 !!! Regidx csp_rs1)
                         (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> m1).
    assert (Hsp2 : m2 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 4)))
      by (unfold m2; rg; exact Hsp1).
    (* ---- 0x8  c.li a5,1 ---- *)
    iApply (wp_uk_cli N h3 m2 (mword_of_int 0x8)
              (mword_of_int 1 : mword 6) a5_idx k
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_seccomp_08 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x8 : mword 64) 2
                 = mword_of_int 0xa);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h4) "Hrun".
    set (m3 := <[Regidx a5_idx
                 := regval_into_reg (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)]> m2).
    assert (Ha5_3 : m3 !!! Regidx a5_idx = mword_of_int 1)
      by (unfold m3; rg; apply bv_eq; vm_compute; reflexivity).
    assert (Ha0_3 : m3 !!! Regidx a0_idx = mword_of_int (Z.of_nat na))
      by (unfold m3, m2, m1; rg; exact Ha0).
    assert (Hsp3 : m3 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 4)))
      by (unfold m3; rg; exact Hsp2).
    (* ---- 0xa  bge a5,a0,0x4c -- argc < 2? ---- *)
    assert (Hge : uv_btaken BGE (m3 !!! Regidx a5_idx) (m3 !!! Regidx a0_idx)
                  = Z.geb 1 (Z.of_nat na)).
    { rewrite Ha5_3 Ha0_3. cbn [uv_btaken].
      apply (moi_ge_s 1 (Z.of_nat na)); unfold Z63; lia. }
    destruct (Nat.le_gt_cases na 1) as [Hle | Hgt].
    { (* THE USAGE LINE *)
      assert (Ht : true = uv_btaken BGE (m3 !!! Regidx a5_idx) (m3 !!! Regidx a0_idx))
        by (rewrite Hge; symmetry; apply Z.geb_le; lia).
      assert (Etgt : add_vec (mword_of_int 0xa : mword 64)
                       (sign_extend' 64 (mword_of_int 66 : mword 13))
                     = mword_of_int 0x4c)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_btype N h4 m3 (mword_of_int 0xa)
                (mword_of_int 66 : mword 13) a0_idx a5_idx BGE true
                (mword_of_int 0x4c) k Ht
                (eq_sym Etgt) ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_seccomp_0a with "Hcode"). }
      iIntros (h5) "Hrun".
      (* ---- 0x4c  c.sdsp s1,8(sp) ---- *)
      iApply (wp_uk_csdsp N h5 m3 (mword_of_int 0x4c)
                (mword_of_int 1 : mword 6) s1_idx (uint sp0 - 24) w3 k
                ltac:(rewrite Hsp3 Hsp32 Ho8; lia)
                ltac:(rewrite Zminus_mod Hal8; reflexivity)
                with "[] Hw3 Hrun").
      { iApply (uis_seccomp_4c with "Hcode"). }
      iIntros "_".
      rewrite (_ : add_vec_int (mword_of_int 0x4c : mword 64) 2
                   = mword_of_int 0x4e);
        [ | apply bv_eq; vm_compute; reflexivity ].
      iIntros (h6) "Hrun".
      iApply (wp_ksecc_usage N h6 m3 n l v Hq with "Hcode Hro Hwd Hstd Hrun"). }
    (* ARGUMENTS: fall through to the fork *)
    assert (Hf : false = uv_btaken BGE (m3 !!! Regidx a5_idx) (m3 !!! Regidx a0_idx))
      by (rewrite Hge; symmetry; destruct (Z.geb_spec 1 (Z.of_nat na)); [ lia | reflexivity ]).
    iApply (wp_uk_btype N h4 m3 (mword_of_int 0xa)
              (mword_of_int 66 : mword 13) a0_idx a5_idx BGE false
              (add_vec (mword_of_int 0xa : mword 64)
                 (sign_extend' 64 (mword_of_int 66 : mword 13)))
              k Hf eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_seccomp_0a with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0xa : mword 64) 4
                 = mword_of_int 0xe);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h5) "Hrun".
    (* ---- 0xe  c.sdsp s1,8(sp) ; 0x10  c.mv s1,a1 ---- *)
    iApply (wp_uk_csdsp N h5 m3 (mword_of_int 0xe)
              (mword_of_int 1 : mword 6) s1_idx (uint sp0 - 24) w3 k
              ltac:(rewrite Hsp3 Hsp32 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw3 Hrun").
    { iApply (uis_seccomp_0e with "Hcode"). }
    iIntros "_".
    rewrite (_ : add_vec_int (mword_of_int 0xe : mword 64) 2
                 = mword_of_int 0x10);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h6) "Hrun".
    iApply (wp_uk_cmv N h6 m3 (mword_of_int 0x10) s1_idx a1_idx
              (add_vec zero_reg (m3 !!! Regidx a1_idx)) k
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_seccomp_10 with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x10 : mword 64) 2
                 = mword_of_int 0x12);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h7) "Hrun".
    (* ---- 0x12  jal ra,0x344 <fork> ---- *)
    iApply (wp_uk_jal N h7 _ (mword_of_int 0x12)
              (mword_of_int 818 : mword 21) ra_idx
              (mword_of_int SeccompSyms.fork) (mword_of_int 0x16) k
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hfork; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hfork; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_seccomp_12 with "Hcode"). }
    iIntros (h8) "Hrun".
    rewrite Hfork.
    match goal with
    | |- context [ urun N h8 ?mm _ _ ] => set (mf := mm)
    end.
    assert (Hraf : mf !!! Regidx ra_idx = (mword_of_int 0x16 : mword 64))
      by (unfold mf; rg; reflexivity).
    (* ---- 0x344  c.li a7,1 ---- *)
    iApply (wp_uk_cli N h8 mf (mword_of_int 0x344)
              (mword_of_int 1 : mword 6) a7_idx k
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_seccomp_344 with "Hcode"). }
    assert (E0 : add_vec_int (mword_of_int 0x344 : mword 64) 2
                 = mword_of_int 0x346)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 1 : mword 6)
                                       : mword 64)]> mf
                 = <[Regidx a7_idx := (mword_of_int 1 : mword 64)]> mf)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h9) "Hrun".
    (* ---- 0x346  ecall -- fork, at the ledger's view ---- *)
    name_m h9 mr10.
    iApply (wp_uk_ecall_fork_at N h9 mr10 (mword_of_int 0x346) k szv l ∅ c v cs
              (fun _ => True%I) emp%I (fun gt _ _ => seccomp_code gt)
              ltac:(unfold usysno, mr10; rg; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] [] Hcode Hsz Hstd [] Hcwd Hch [] Hrun []").
    { iApply (uis_seccomp_346 with "Hcode"). }
    { done. }
    { by rewrite big_sepM_empty. }
    { iModIntro. by iIntros "_". }
    rewrite (_ : add_vec_int (mword_of_int 0x346 : mword 64) 4
                 = mword_of_int 0x34a);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iSplitL.
    - (* ---- THE PARENT ---- *)
      iIntros (h' r) "%Hr Harm _ _ Hstd _ _ Hrun".
      name_m h' mr11.
      iApply (wp_uk_cjr N h' mr11 (mword_of_int 0x34a) ra_idx
                (mword_of_int 0x16) k
                ltac:(vm_compute; discriminate)
                ltac:(unfold mr11, mf; rg; apply bv_eq; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_seccomp_34a with "Hcode"). }
      iIntros (h'') "Hrun".
      iDestruct "Harm" as "[(%Hm1 & _ & _) | (%γ & %pidv & %Hrpid & %Hrng & _ & _ & Hch)]".
      + name_m h'' mr12.
        iApply (wp_ksecc_forkneg N h'' mr12 n l v Hq
                  ltac:(unfold mr12; rg; exact Hm1)
                  with "Hcode Hro Hwd Hstd Hrun").
      + name_m h'' mr13.
        iApply (wp_ksecc_parent N h'' mr13 k pidv (cs ∪ {[γ]}) Hq Hrng
                  ltac:(unfold mr13; rg; exact Hrpid)
                  with "Hcode Hch Hrun").
    - (* ---- THE CHILD ---- *)
      iIntros (N' h' γ') "%Hpq _ _ #Hcode' _ Hstd' _ _ _ _ Hrun".
      name_m h' mr14.
      iApply (wp_uk_cjr N' h' mr14 (mword_of_int 0x34a) ra_idx
                (mword_of_int 0x16) k
                ltac:(vm_compute; discriminate)
                ltac:(unfold mr14, mf; rg; apply bv_eq; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_seccomp_34a with "Hcode'"). }
      iIntros (h'') "Hrun".
      iDestruct "Hstd'" as "[_ Htab]".
      name_m h'' mr15.
      iApply (wp_ksecc_child N' h'' mr15 k v Hpq
                ltac:(unfold mr15; rg; reflexivity)
                with "Hcode' Huniv Htab Hrun").
  Qed.

  (* start(argc, argv) @0x96: main never returns *)
  Lemma wp_ksecc_start (N : uk_names Σ) (h : CpuId) (m : regfile) (na n : nat)
      (l v : list fdstate) (szv c : Z) (cs : gset gname) :
    (forall s : Z, ⊢ ukn_pay N s) ->
    m !!! Regidx a0_idx = mword_of_int (Z.of_nat na) ->
    (Z.of_nat na < 2 ^ 31)%Z ->
    (32 <= n)%nat ->
    seccomp_code (ukn_t N) -∗
    seccomp_rodata (ukn_t N) -∗
    secc_wdep N l -∗
    secc_univ v -∗
    ustd_at (ukn_fd N) l v -∗
    usz (ukn_s N) szv -∗
    ucwd (ukn_cwd N) c -∗
    uch (ukn_ch N) cs -∗
    urun N h m (mword_of_int SeccompSyms.start) n -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpsok_free.
    intros Hq Ha0 Hna Hn.
    replace n with (2 + (4 + (10 + (12 + (4 + (n - 32))))))%nat by lia.
    set (n' := (4 + (10 + (12 + (4 + (n - 32)))))%nat).
    iIntros "#Hcode #Hro #Hwd #Huniv Hstd Hsz Hcwd Hch Hrun".
    destruct seccomp_syms_pins
      as (Hstart & Hmain & _ & _ & _ & _ & _ & _ & _ & _ & _).
    rewrite Hstart.
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
    assert (Hsp16 : uint (add_vec_int sp0 (- (8 * Z.of_nat 2))) = uint sp0 - 16)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    assert (Ho0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    (* ---- 0x96  c.addi sp,sp,-16 ---- *)
    iApply (wp_uk_caddi_sp_dn N h m (mword_of_int 0x96)
              (mword_of_int 48 : mword 6) 2 n'
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_seccomp_96 with "Hcode"). }
    iIntros "Hframe".
    rewrite Hsp.
    rewrite (_ : add_vec_int (mword_of_int 0x96 : mword 64) 2
                 = mword_of_int 0x98);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h0) "Hrun".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 2)))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 2)))
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg _)).
    iDestruct (ustack_2_open with "Hframe") as "(_ & [%w1 Hw1] & [%w2 Hw2])".
    (* ---- 0x98  c.sdsp ra,8(sp) ; 0x9a  c.sdsp s0,0(sp) ---- *)
    iApply (wp_uk_csdsp N h0 m1 (mword_of_int 0x98)
              (mword_of_int 1 : mword 6) ra_idx (uint sp0 - 8) w1 n'
              ltac:(rewrite Hsp1 Hsp16 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw1 Hrun").
    { iApply (uis_seccomp_98 with "Hcode"). }
    iIntros "_".
    rewrite (_ : add_vec_int (mword_of_int 0x98 : mword 64) 2
                 = mword_of_int 0x9a);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h1) "Hrun".
    iApply (wp_uk_csdsp N h1 m1 (mword_of_int 0x9a)
              (mword_of_int 0 : mword 6) s0_idx (uint sp0 - 16) w2 n'
              ltac:(rewrite Hsp1 Hsp16 Ho0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw2 Hrun").
    { iApply (uis_seccomp_9a with "Hcode"). }
    iIntros "_".
    rewrite (_ : add_vec_int (mword_of_int 0x9a : mword 64) 2
                 = mword_of_int 0x9c);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h2) "Hrun".
    (* ---- 0x9c  c.addi4spn s0,sp,16 ---- *)
    iApply (wp_uk_caddi4spn N h2 m1 (mword_of_int 0x9c)
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8) s0_idx
              (add_vec (m1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))
              n'
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_seccomp_9c with "Hcode"). }
    rewrite (_ : add_vec_int (mword_of_int 0x9c : mword 64) 2
                 = mword_of_int 0x9e);
      [ | apply bv_eq; vm_compute; reflexivity ].
    iIntros (h3) "Hrun".
    (* ---- 0x9e  jal ra,0x0 <main> ---- *)
    iApply (wp_uk_jal N h3 _ (mword_of_int 0x9e)
              (mword_of_int 2096994 : mword 21) ra_idx
              (mword_of_int SeccompSyms.main) (mword_of_int 0xa2) n'
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hmain; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hmain; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_seccomp_9e with "Hcode"). }
    iIntros (h4) "Hrun".
    name_m h4 mr16.
    iApply (wp_ksecc_main N h4 mr16 na (n - 32) l v szv c cs Hq
              ltac:(unfold mr16, m1; rg; exact Ha0) Hna
              with "Hcode Hro Hwd Huniv Hstd Hsz Hcwd Hch Hrun").
  Qed.

End UkSeccMain.
