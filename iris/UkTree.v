(* ===================================================================== *)
(* UkTree.v -- THE TREE PAYMENT: what a user program owes per event of    *)
(* its interaction tree, stated ONCE over a program instance.             *)
(*                                                                        *)
(* Design: claude-notes/design/program-specs.md (SS3.2).  [ProgTree.v] is  *)
(* the pure half: a program's spec is a tree [proc] over the events [ev]   *)
(* (open, close, read, write, exit).  This file is the logic's half:       *)
(*                                                                        *)
(*   [ev_obl e K]   the OBLIGATION one event costs, at the program's own   *)
(*                  syscall stub -- the machine-shaped hole every landed   *)
(*                  per-program obligation ([UkEcho.kecho_w],              *)
(*                  [UkCat.kcat_r] ...) is an instance of, with the BYTES  *)
(*                  in its statement and the answer handed to [K];         *)
(*   [tree_pay t]   the payment of a whole tree: the greatest fixpoint of  *)
(*                  each node's hole with the payment of the answer's      *)
(*                  subtree in its continuation.  Greatest, so an          *)
(*                  unbounded loop ([iter]) is payable, and a payer proves  *)
(*                  it by COINDUCTION ([tree_pay_coind]): exhibit an        *)
(*                  invariant that funds one node and comes back.          *)
(*                                                                        *)
(* WHAT A HOLE SAYS.  The program is at the stub's entry with the call's   *)
(* arguments in a0..a2, holding its code and the run; the payer answers   *)
(* with the run at the stub's return (a0 = the answer, a7 = the number)   *)
(* and [K] at the answer.  The argument readings are the WEAKEST any       *)
(* program states -- a descriptor and a count as the C [int] the kernel    *)
(* reads ([trunc32]), a pointer as the word -- except a write's count,     *)
(* which every program has exactly.  A write hands the payer the SOURCE   *)
(* RUN ([usrc_at]: the bytes at the address, in the data half at a         *)
(* fraction or in the text half, the program choosing the reading) and    *)
(* gets that resource back; a read hands the buffer and gets it back at   *)
(* the answer's contents; an open hands the path string.  The kernel's UNIVERSAL facts about an answer -- open     *)
(* returns -1 or a descriptor below NOFILE, read returns -1 or at most     *)
(* the count -- are in the continuation, because the program's own tree   *)
(* is stated at them (cat writes what it read out of a 512-byte buffer).  *)
(* The read bound is NOT exported by the generic tier's free leaf          *)
(* ([UkRunSys.wp_uk_ecall_read] says nothing of the answer), so a free    *)
(* handler for reads is deferred; the real destinations have it from the  *)
(* kernel's read post.                                                    *)
(*                                                                        *)
(* THE INSTANCE.  [uprog] is the program's code resource and its five     *)
(* stub entries (user/usys.S: the same three instructions in every        *)
(* binary, at that binary's addresses).  A program with no stub for an    *)
(* event names any address there; its tree has no such node.              *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.bi.lib Require Import fixpoint_mono.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import UserHeap UkRun.
Require Import ProcGeom.               (* [NOFILE] *)
Require Import UserFd.         (* [ufdG] *)
Require Import CtxIdDefs.
Require Import ChildTok.
Require Import UexecSG.
Require Import ProgTree.
Local Open Scope Z_scope.
Import Defs.

(* the program instance: its code, and where its five stubs are *)
Record uprog (Σ : gFunctors) := MkUprog {
  up_code : iProp Σ;
  up_write : Z;
  up_read : Z;
  up_open : Z;
  up_close : Z;
  up_exit : Z;
}.
Arguments up_code {Σ} _.
Arguments up_write {Σ} _.
Arguments up_read {Σ} _.
Arguments up_open {Σ} _.
Arguments up_close {Σ} _.
Arguments up_exit {Σ} _.

(* a read's answer, off the returned word and the buffer it left *)
Definition rd_ans_of (ret : mword 64) (g : nat -> bv 8) : rd_ans :=
  if decide (bv_signed ret < 0) then RdErr
  else RdBytes (map g (seq 0 (Z.to_nat (bv_signed ret)))).

(* the kernel's universal facts about an answer *)
Definition open_ans_ok (ret : mword 64) : Prop :=
  bv_signed ret = -1
  \/ (0 <= bv_signed ret < Z.of_nat NOFILE
      /\ ret = mword_of_int (bv_signed ret)).
Definition read_ans_ok (n : nat) (ret : mword 64) : Prop :=
  bv_signed ret = -1 \/ 0 <= bv_signed ret <= Z.of_nat n.

(* an argument's bytes, as a tree names them *)
Definition uarg_bytes (g : uarg) : list (bv 8) :=
  map (ua_bytes g) (seq 0 (ua_len g)).

Lemma uarg_bytes_length (g : uarg) : length (uarg_bytes g) = ua_len g.
Proof. unfold uarg_bytes. rewrite length_map length_seq. reflexivity. Qed.

Lemma map_seq_lookup {A : Type} (f : nat -> A) (n j : nat) :
  (j < n)%nat -> map f (seq 0 n) !! j = Some (f j).
Proof.
  intros Hj.
  change (map f (seq 0 n)) with (f <$> seq 0 n).
  rewrite list_lookup_fmap lookup_seq_lt; [| exact Hj].
  reflexivity.
Qed.

Lemma map_drop {A B : Type} (f : A -> B) (n : nat) (l : list A) :
  map f (drop n l) = drop n (map f l).
Proof. revert l. induction n as [| n IH]; intros [| x l]; simpl; auto. Qed.

Section UkTree.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  Context (N : uk_names Σ).
  Context (P : uprog Σ).

  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* the C [int] reading of an argument register *)
  Local Notation cint v := (bv_signed (trunc32 v)).

  (* the run at a stub's return: a0 the answer, a7 the number, pc where
     [c.jr ra] lands *)
  Definition stub_ret (m : regfile) (num : Z) (ret : mword 64) : regfile :=
    <[Regidx a0_idx := ret]> (<[Regidx a7_idx := (mword_of_int num : mword 64)]> m).

  (* ------------------------------------------------------------------- *)
  (*  1.  THE SOURCES a call hands the payer                              *)
  (* ------------------------------------------------------------------- *)

  (* [f] spells [bs] on its domain *)
  Definition bytes_of (bs : list (bv 8)) (f : nat -> bv 8) : Prop :=
    forall j : nat, (j < length bs)%nat -> bs !! j = Some (f j).

  (* [n] bytes at [ua] read as [f]: in the text half ([tx]), or in the data
     half at the fraction [dq].  The program CHOOSES the reading when it
     hands the run over, and gets that very resource back -- an existential
     here would cost cat the ownership of its buffer. *)
  Definition usrc_at (tx : bool) (dq : dfrac) (ua : Z) (n : nat)
      (f : nat -> bv 8) : iProp Σ :=
    if tx then ([∗ list] j ∈ seq 0 n, utext γt (ua + Z.of_nat j) (f j))%I
    else ubytesq γd dq ua n f.

  (* a NUL-terminated string of [n] bytes at [pv], in either half -- the
     data half at the DISCARDED fraction only: the kernel resolves a path
     off the process image, which the open leaves read through a boxed
     view, so a path the program still owns whole is not one they take
     (every landed path is a literal, an argv string or a line the shell
     has discarded) *)
  Definition upath_at (tx : bool) (pv : Z) (n : nat) (f : nat -> bv 8) : iProp Σ :=
    if tx then utext_str γt pv n f else ustr γd DfracDiscarded pv n f.

  (* ------------------------------------------------------------------- *)
  (*  2.  THE HOLES, one per event                                        *)
  (* ------------------------------------------------------------------- *)

  Definition wr_obl (fd : Z) (bs : list (bv 8)) (K : Z -> iProp Σ) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (avail : nat) (ua : Z) (tx : bool)
       (dq : dfrac) (f : nat -> bv 8),
       ⌜bytes_of bs f⌝ -∗
       ⌜cint (m !!! Regidx a0_idx) = fd⌝ -∗
       ⌜m !!! Regidx a1_idx = (mword_of_int ua : mword 64)⌝ -∗
       ⌜m !!! Regidx a2_idx = (mword_of_int (Z.of_nat (length bs)) : mword 64)⌝ -∗
       up_code P -∗
       usrc_at tx dq ua (length bs) f -∗
       urun N h m (mword_of_int (up_write P)) avail -∗
       (∀ (h' : CpuId) (ret : mword 64),
          K (bv_signed ret) -∗
          usrc_at tx dq ua (length bs) f -∗
          urun N h' (stub_ret m 16 ret) (ret_pc (m !!! Regidx ra_idx)) avail -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  Definition rd_obl (fd : Z) (n : nat) (K : rd_ans -> iProp Σ) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (avail : nat) (a : Z) (f : nat -> bv 8),
       ⌜cint (m !!! Regidx a0_idx) = fd⌝ -∗
       ⌜m !!! Regidx a1_idx = (mword_of_int a : mword 64)⌝ -∗
       ⌜cint (m !!! Regidx a2_idx) = Z.of_nat n⌝ -∗
       up_code P -∗
       ubytes γd a n f -∗
       urun N h m (mword_of_int (up_read P)) avail -∗
       (∀ (h' : CpuId) (ret : mword 64) (g : nat -> bv 8),
          ⌜read_ans_ok n ret⌝ -∗
          K (rd_ans_of ret g) -∗
          ubytes γd a n g -∗
          urun N h' (stub_ret m 5 ret) (ret_pc (m !!! Regidx ra_idx)) avail -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  Definition op_obl (path : list (bv 8)) (mode : Z) (K : Z -> iProp Σ) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (avail : nat) (pv : Z) (tx : bool)
       (f : nat -> bv 8),
       ⌜bytes_of path f⌝ -∗
       ⌜m !!! Regidx a0_idx = (mword_of_int pv : mword 64)⌝ -∗
       ⌜m !!! Regidx a1_idx = (mword_of_int mode : mword 64)⌝ -∗
       up_code P -∗
       upath_at tx pv (length path) f -∗
       urun N h m (mword_of_int (up_open P)) avail -∗
       (∀ (h' : CpuId) (ret : mword 64),
          ⌜open_ans_ok ret⌝ -∗
          K (bv_signed ret) -∗
          upath_at tx pv (length path) f -∗
          urun N h' (stub_ret m 15 ret) (ret_pc (m !!! Regidx ra_idx)) avail -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  Definition cl_obl (fd : Z) (K : Z -> iProp Σ) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (avail : nat),
       ⌜cint (m !!! Regidx a0_idx) = fd⌝ -∗
       up_code P -∗
       urun N h m (mword_of_int (up_close P)) avail -∗
       (∀ (h' : CpuId) (ret : mword 64),
          K (bv_signed ret) -∗
          urun N h' (stub_ret m 21 ret) (ret_pc (m !!! Regidx ra_idx)) avail -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* exit never returns: the hole is the whole of the rest of the process *)
  Definition ex_obl (status : Z) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (avail : nat),
       ⌜cint (m !!! Regidx a0_idx) = status⌝ -∗
       up_code P -∗
       urun N h m (mword_of_int (up_exit P)) avail -∗
       mWP (Loop : expr riscv_lang))%I.

  Definition ev_obl (e : ev) : (ans e -> iProp Σ) -> iProp Σ :=
    match e as e return (ans e -> iProp Σ) -> iProp Σ with
    | EOpen path mode => op_obl path mode
    | EClose fd => cl_obl fd
    | ERead fd n => rd_obl fd n
    | EWrite fd bs => wr_obl fd bs
    | EExit s => fun _ => ex_obl s
    end.

  (* every hole is monotone in its continuation *)
  Lemma ev_obl_mono (e : ev) (K K' : ans e -> iProp Σ) :
    □ (∀ x, K x -∗ K' x) -∗ ev_obl e K -∗ ev_obl e K'.
  Proof using .
    iIntros "#HK Ho". destruct e; simpl.
    - iIntros (h m avail pv tx f) "%Hf %H0 %H1 Hc Hp Hrun Hcont".
      iApply ("Ho" $! h m avail pv tx f with "[%] [%] [%] Hc Hp Hrun"); [done | done | done |].
      iIntros (h' ret) "%Hok HKx Hp Hrun".
      iApply ("Hcont" $! h' ret with "[%] [HKx] Hp Hrun"); [done |].
      by iApply "HK".
    - iIntros (h m avail) "%H0 Hc Hrun Hcont".
      iApply ("Ho" $! h m avail with "[%] Hc Hrun"); [done |].
      iIntros (h' ret) "HKx Hrun".
      iApply ("Hcont" $! h' ret with "[HKx] Hrun"). by iApply "HK".
    - iIntros (h m avail a f) "%H0 %H1 %H2 Hc Hb Hrun Hcont".
      iApply ("Ho" $! h m avail a f with "[%] [%] [%] Hc Hb Hrun"); [done | done | done |].
      iIntros (h' ret g) "%Hok HKx Hb Hrun".
      iApply ("Hcont" $! h' ret g with "[%] [HKx] Hb Hrun"); [done |].
      by iApply "HK".
    - iIntros (h m avail ua tx dq f) "%Hf %H0 %H1 %H2 Hc Hs Hrun Hcont".
      iApply ("Ho" $! h m avail ua tx dq f with "[%] [%] [%] [%] Hc Hs Hrun"); [done | done | done | done |].
      iIntros (h' ret) "HKx Hs Hrun".
      iApply ("Hcont" $! h' ret with "[HKx] Hs Hrun"). by iApply "HK".
    - iExact "Ho".
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  3.  THE TREE'S PAYMENT                                              *)
  (* ------------------------------------------------------------------- *)

  Definition tree_F (Q : proc -> iProp Σ) (t : proc) : iProp Σ :=
    match t with
    | Ret v => match v with end
    | Tau t' => Q t'
    | Vis e k => ev_obl e (fun x => Q (k x))
    end.

  (* the step functional is monotone *)
  Lemma tree_F_mono_law (Q Q' : proc -> iProp Σ) :
    □ (∀ t, Q t -∗ Q' t) -∗ ∀ t, tree_F Q t -∗ tree_F Q' t.
  Proof using .
    iIntros "#HQ" (t) "Ht". destruct t as [v | t' | e k].
    - destruct v.
    - simpl. by iApply "HQ".
    - simpl. iApply (ev_obl_mono with "[] Ht").
      iIntros "!>" (x) "Hx". by iApply "HQ".
  Qed.

  Local Instance tree_F_mono : BiMonoPred (A := leibnizO proc) tree_F.
  Proof using .
    split.
    - iIntros (Q Q' _ _) "#HQ". iApply (tree_F_mono_law with "HQ").
    - intros Q _ n t t' Ht.
      assert (t = t') as ->
        by (apply leibniz_equiv; exact (proj2 (discrete_iff n t t') Ht)).
      reflexivity.
  Qed.

  Definition tree_pay : proc -> iProp Σ :=
    bi_greatest_fixpoint (A := leibnizO proc) tree_F.

  Lemma tree_pay_unfold (t : proc) : tree_pay t ⊣⊢ tree_F tree_pay t.
  Proof using . apply (greatest_fixpoint_unfold (A := leibnizO proc) tree_F t). Qed.

  Lemma tree_pay_tau (t : proc) : tree_pay (Tau t) ⊣⊢ tree_pay t.
  Proof using . apply tree_pay_unfold. Qed.

  Lemma tree_pay_vis (e : ev) (k : ans e -> proc) :
    tree_pay (Vis e k) ⊣⊢ ev_obl e (fun x => tree_pay (k x)).
  Proof using . apply tree_pay_unfold. Qed.

  (* a payer's principle: an invariant that funds one node and comes back
     funds the whole tree *)
  Lemma tree_pay_coind (I : proc -> iProp Σ) :
    □ (∀ t, I t -∗ tree_F I t) -∗ ∀ t, I t -∗ tree_pay t.
  Proof using .
    iIntros "#HI".
    iApply (greatest_fixpoint_coind (A := leibnizO proc) tree_F I).
    iIntros "!>" (t) "Ht". iDestruct ("HI" with "Ht") as "Ht".
    iApply (bi_mono_pred (A := leibnizO proc) (F := tree_F) I (fun t => I t ∨ tree_pay t)%I with "[] Ht").
    iIntros "!>" (t') "Ht'". by iLeft.
  Qed.

End UkTree.
