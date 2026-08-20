(* ProofConsoleread.v -- the whole-function WP for xv6's consoleread().

     int consoleread(int user_dst, uint64 dst, int n)
     {
       uint target = n;  int c;  char cbuf;
       acquire(&cons.lock);
       while (n > 0) {
         while (cons.r == cons.w) {
           if (killed(myproc())) { release(&cons.lock); return -1; }
           sleep_prepare(&cons.r);  release(&cons.lock);  sleep();
           acquire(&cons.lock);
         }
         c = cons.buf[cons.r++ % INPUT_BUF_SIZE];
         if (c == C('D')) { if (n < target) cons.r--; break; }
         cbuf = c;
         if (either_copyout(user_dst, dst, &cbuf, 1) == -1) break;
         dst++;  --n;
         if (c == '\n') break;
       }
       release(&cons.lock);
       return target - n;
     }

   Ninety-four instructions; the contract is SpecConsoleread.v, the decode
   layer CodeConsoleread.v, the console's own state ConsoleInv.v.  THE SHAPE
   IS PIPEREAD'S -- read ProofPiperead.v alongside this; the two are the same
   animal, a blocking read into user memory under a spinlock that a
   wakeup-issuing interrupt handler also takes.

   THE FRAME IS TWELVE SLOTS ([c.addi16sp sp,-96]).  ra/s0/s1/s2/s3/s4/s6/s7
   are saved unconditionally into slots 1..6, 8, 9; s5 -- the byte just read --
   is SHRINK-WRAPPED into slot 7 by the [c.sdsp s5,40(sp)] at +0x74, on the
   paths that get as far as having one.  Slots 10..12 are the locals, and
   [cbuf] is the single byte at [s0-81], i.e. the TOP byte of slot 11.

   The three exits all reach the epilogue at +0xce with a0 already holding the
   answer: the killed arm sets [-1] at +0xcc and falls in, and both normal
   exits compute [target - n] with the [subw a0,s7,s3] at +0x108 and jump
   back.  So [cr_epi] is one lemma and there is no restore run to share --
   unlike consolewrite, whose nine shrink-wrapped registers had to be
   reloaded twice.

   THE FIVE EXITS ARE THREADED AS ONE [∧]-BUNDLE, [cr_exits], not rebuilt per
   block: it carries the eight saved slots and the caller's [wp_next], and
   every block below takes it as a PREMISE and hands it on.  Because the
   blocks take it rather than hold it, each of them is provable from the
   PERSISTENT context alone -- so [cr_have_prop] can be built fresh (under a
   [□]) inside the wait loop's Löb instead of being threaded round the back
   edge, which is what ProofPiperead.v has to do with its [EX ∧ CP].

   THREE LOOPS' WORTH OF STRUCTURE, in the order the file builds them:
   [cr_mk_retx] (+0xfc, the shared release/subw tail), [cr_mk_have] (+0x76,
   the byte read and the copyout), [cr_mk_wait] (+0x48, the unbounded park --
   an iLöb, since nothing bounds how long a line takes to arrive), and
   [cr_mk_head] (+0x38, the outer [while (n > 0)] -- a FUEL induction, since
   the answer is a count).  The fuel premise is [Z.to_nat nc < fl] at the head
   and [Z.to_nat nc <= fl] below it, which is what makes the base case
   vacuous rather than a duplicated exit. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import StackOwn StackBytes.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import W32Arith.
Require Import IntrDefs WpSmodeIntr.
Require Import HartTp WpNext.
Require Import WpLock ProcGeom CpuOwn.
Require Import UserPtTree KvmSpec ProcPtOwn.
Require Import FdSlots ProcInv FileInvDefs.
Require Import ConsoleInv.
Require Import SchedCtx.
Require Import SpecMyproc SpecAcquire SpecKilled SpecSleepPrepare SpecSleep.
Require Import SpecEitherCopyout SpecRelease.
Require Import CodeConsoleread.
Require Import SpecConsoleread.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)

Import Defs.
Local Open Scope Z_scope.

(* MANDATORY IN ANY FILE THAT PROVES OVER [proc_priv] (durable-notes.md), and
   its twin rule -- never a bare [iFrame] here -- is in optimization.md. *)
Set Printing Depth 40.

Notation CR := KernelSyms.consoleread (only parsing).

(* THE FRAME IS TWELVE SLOTS.  A [c.sdsp]/[c.ldsp] displacement off the pushed
   sp names slot [12 - imm6] counted down from the ENTRY sp. *)
Lemma cr_slot_bridge (X : mword 64) (o : mword 64) (k : nat) :
  add_vec (mword_of_int (- (8 * Z.of_nat 12%nat))) o = mword_of_int (- (8 * Z.of_nat k)) ->
  add_vec (pa_stk X 12%nat) o = pa_stk X k.
Proof.
  intro H. unfold pa_stk, add_vec_int. rewrite add_vec_assoc H. reflexivity.
Qed.


Local Ltac reg_neq :=
  lazymatch goal with |- ?a <> ?b =>
    tryif unify a b then fail else (vm_compute; discriminate) end.
Local Ltac nz := vm_compute; discriminate.
Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.

(* ===================================================================== *)
(*  Pure bitvector facts.  The counting laws proper live in W32Arith.v;   *)
(*  what is left here is what only this function computes -- the ring     *)
(*  index, the byte it reads, and the [addiw]/[sw] round trip that        *)
(*  commits [cons.r + 1].                                                 *)
(* ===================================================================== *)

(* [cons.r++]: the [addiw a3,a5,1] / [sw a3,152(a4)] round trip commits
   [r + 1] at width 32.  [ProofPiperead.pr_sw_nread]'s twin, at the
   FOUR-byte immediate spelling. *)
Lemma cr_sw_r (r : mword 32) :
  trunc32 (sign_extend' 64 (subrange_vec_dec
     (add_vec (sign_extend' 64 r) (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0))
  = add_vec r (mword_of_int 1 : mword 32).
Proof.
  rewrite <- trunc32_subrange.
  rewrite trunc32_sext.
  rewrite trunc32_add trunc32_sext.
  assert (HK : trunc32 (sign_extend' 64 (mword_of_int 1 : mword 12)) = (mword_of_int 1 : mword 32))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite HK. reflexivity.
Qed.

(* [V] is its own re-description at the descriptor it already carries --
   what the entry into the loop needs, since every block below speaks
   [upd_upt V P'] and the caller hands in a bare [V]. *)
Lemma cr_upd_id (V : pprivate) : upd_upt V (pv_upt V) = V.
Proof. destruct V; reflexivity. Qed.

(* the two level bounds every callee wants *)
Lemma cr_lvl0 : (Z.of_nat 0%nat + 1 < 2 ^ 31)%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma cr_lvl1 : (Z.of_nat 1%nat + 1 < 2 ^ 31)%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma cr_len1_31 : (Z.of_nat 1%nat < 2 ^ 64)%Z.
Proof. vm_compute. reflexivity. Qed.

(* THE CALLEE-SAVED ROLES gcc gives this function: s1 = &cons, s2 = &cons.r
   (the sleep channel), s3 = the remaining count [n], s4 = the user cursor,
   s5 = the byte just read, s6 = [user_dst], s7 = [target].  The
   prologue/epilogue name the REGISTER, the body names the ROLE.  File-level
   so both the pure section and the proof functor below see them. *)
Notation Rra  := (mword_of_int 1  : mword 5).
Notation Rs0  := (mword_of_int 8  : mword 5).
Notation Rs1  := (mword_of_int 9  : mword 5).
Notation Ra0  := (mword_of_int 10 : mword 5).
Notation Ra1  := (mword_of_int 11 : mword 5).
Notation Ra2  := (mword_of_int 12 : mword 5).
Notation Ra3  := (mword_of_int 13 : mword 5).
Notation Ra4  := (mword_of_int 14 : mword 5).
Notation Ra5  := (mword_of_int 15 : mword 5).
Notation Rs2  := (mword_of_int 18 : mword 5).
Notation Rs3  := (mword_of_int 19 : mword 5).
Notation Rs4  := (mword_of_int 20 : mword 5).
Notation Rs5  := (mword_of_int 21 : mword 5).
Notation Rs6  := (mword_of_int 22 : mword 5).
Notation Rs7  := (mword_of_int 23 : mword 5).
Notation Rs8  := (mword_of_int 24 : mword 5).
Notation Rs9  := (mword_of_int 25 : mword 5).
Notation Rs10 := (mword_of_int 26 : mword 5).
Notation Rs11 := (mword_of_int 27 : mword 5).

Section CrBodies.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ}.
  Context `{GEN : RiscvLang.GenId}.

  Local Ltac rgne :=
    rewrite rget_ne;
    [ | let H1 := fresh in let H2 := fresh in
        intro H1; injection H1 as H2; vm_compute in H2; congruence ].

  (* ---- the frame, in two pieces ------------------------------------ *)

  (* the eight the prologue saves unconditionally *)
  Definition cr_saved (sp0 : mword 64) (m0 : regfile) : iProp Σ :=
    (pa_stk sp0 1 ↦₈[KT1] (m0 !!! Regidx Rra) ∗
     pa_stk sp0 2 ↦₈[KT1] (m0 !!! Regidx Rs0) ∗
     pa_stk sp0 3 ↦₈[KT1] (m0 !!! Regidx Rs1) ∗
     pa_stk sp0 4 ↦₈[KT1] (m0 !!! Regidx Rs2) ∗
     pa_stk sp0 5 ↦₈[KT1] (m0 !!! Regidx Rs3) ∗
     pa_stk sp0 6 ↦₈[KT1] (m0 !!! Regidx Rs4) ∗
     pa_stk sp0 8 ↦₈[KT1] (m0 !!! Regidx Rs6) ∗
     pa_stk sp0 9 ↦₈[KT1] (m0 !!! Regidx Rs7))%I.

  (* slot 7 (s5's shrink-wrap) and the three local slots, contents free.
     [cbuf] lives in slot 11 and is written by the [sb] at +0x9a, so the
     locals are carried as WORDS everywhere except across that store. *)
  Definition cr_rest (sp0 : mword 64) : iProp Σ :=
    ((∃ w : mword 64, pa_stk sp0 7  ↦₈[KT1] w) ∗
     (∃ w : mword 64, pa_stk sp0 10 ↦₈[KT1] w) ∗
     (∃ w : mword 64, pa_stk sp0 11 ↦₈[KT1] w) ∗
     (∃ w : mword 64, pa_stk sp0 12 ↦₈[KT1] w))%I.

  Lemma cr_frame_back (sp0 : mword 64) (m0 : regfile) :
    cr_saved sp0 m0 -∗ cr_rest sp0 -∗ stack_own (KTR := KT1) sp0 12.
  Proof.
    iIntros "(H1 & H2 & H3 & H4 & H5 & H6 & H8 & H9) (H7 & H10 & H11 & H12)".
    rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
    iSplitL "H1"; [by iExists _|]. iSplitL "H2"; [by iExists _|].
    iSplitL "H3"; [by iExists _|]. iSplitL "H4"; [by iExists _|].
    iSplitL "H5"; [by iExists _|]. iSplitL "H6"; [by iExists _|].
    iSplitL "H7"; [iExact "H7"|]. iSplitL "H8"; [by iExists _|].
    iSplitL "H9"; [by iExists _|]. iSplitL "H10"; [iExact "H10"|].
    iSplitL "H11"; [iExact "H11"|]. iSplitL "H12"; [iExact "H12"|]. done.
  Qed.

  (* the callee-saved registers the epilogue does NOT reload: s5 (restored on
     every path that spilled it) and s8..s11 (never touched at all). *)
  Definition cr_cs_hi (M m0 : regfile) : Prop :=
    M !!! Regidx Rs5  = m0 !!! Regidx Rs5
    /\ M !!! Regidx Rs8  = m0 !!! Regidx Rs8
    /\ M !!! Regidx Rs9  = m0 !!! Regidx Rs9
    /\ M !!! Regidx Rs10 = m0 !!! Regidx Rs10
    /\ M !!! Regidx Rs11 = m0 !!! Regidx Rs11.

  (* the function's own exit, as a [wp_next] at the entry hart *)
  Definition cr_ret `{CID0 : CpuId} (jp : nat) (m0 : regfile) (av : nat)
      (eb : bool) (pid : mword 32) (V : pprivate) (n : Z) (lks : gset string) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr jp) (fun (CID : CpuId) =>
       ∀ (mf : regfile) (r : Z) (P' : uptd),
         ⌜callee_saved m0 mf⌝ -∗
         ⌜uptd_ext (pv_upt V) P'⌝ -∗
         ⌜(-1 <= r <= Z.max 0 n)%Z⌝ -∗
         ⌜mf !!! Regidx Ra0 = (mword_of_int r : mword 64)⌝ -∗
         sie_cap_gpr KT1 mf av true (proc_addr jp) -∗
         cpu_own 0%nat eb (proc_addr jp) true lks -∗
         pc_is (ret_pc (m0 !!! Regidx Rra)) -∗
         proc_priv_core (proc_addr jp) pid (upd_upt V P') -∗
         WP (Loop : expr riscv_lang)))%I.

  (* =================================================================== *)
  (*  +0xce .. +0xe0 -- THE EPILOGUE.  All three exits reach it with the  *)
  (*  answer already in a0.                                               *)
  (* =================================================================== *)
  Lemma cr_epi `{CID : CpuId} (CID0 : CPU)
      (jp : nat) (m0 M : regfile) (av : nat) (eb : bool)
      (sp0 : mword 64) (pid : mword 32) (V : pprivate) (n r : Z) (lks : gset string) :
    let pj := proc_addr jp in
    m0 !!! Regidx csp_rs1 = sp0 ->
    M !!! Regidx csp_rs1 = pa_stk sp0 12%nat ->
    M !!! Regidx Ra0 = (mword_of_int r : mword 64) ->
    cr_cs_hi M m0 ->
    (-1 <= r <= Z.max 0 n)%Z ->
    (consoleread_stack <= av)%nat ->
    eb = true ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    kernel_text -∗
    sie_cap_gpr KT1 M (av - 12)%nat true pj -∗
    cpu_own 0%nat eb pj true lks -∗
    pc_is (mword_of_int (CR + 0xce)) -∗
    proc_priv_core pj pid V -∗
    cr_saved sp0 m0 -∗ cr_rest sp0 -∗
    cr_ret (CID0 := CID0) jp m0 av eb pid V n lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj Hm0sp HMsp HMa0 HMcs Hr Hav Heb Hcr.
    iIntros "#Ht Hcg Hcnt Hpc Hpriv (K1 & K2 & K3 & K4 & K5 & K6 & K8 & K9) Hrest Hcont".
    iPoseProof (cnri_0ce with "Ht") as "Hice".
    iPoseProof (cnri_0d0 with "Ht") as "Hid0".
    iPoseProof (cnri_0d2 with "Ht") as "Hid2".
    iPoseProof (cnri_0d4 with "Ht") as "Hid4".
    iPoseProof (cnri_0d6 with "Ht") as "Hid6".
    iPoseProof (cnri_0d8 with "Ht") as "Hid8".
    iPoseProof (cnri_0da with "Ht") as "Hida".
    iPoseProof (cnri_0dc with "Ht") as "Hidc".
    iPoseProof (cnri_0de with "Ht") as "Hi0de". iPoseProof (cnri_0e0 with "Ht") as "Hi0e0".
    assert (Hb1 : add_vec (pa_stk sp0 12%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (apply cr_slot_bridge; pcw).
    assert (Hb2 : add_vec (pa_stk sp0 12%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (apply cr_slot_bridge; pcw).
    assert (Hb3 : add_vec (pa_stk sp0 12%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (apply cr_slot_bridge; pcw).
    assert (Hb4 : add_vec (pa_stk sp0 12%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (apply cr_slot_bridge; pcw).
    assert (Hb5 : add_vec (pa_stk sp0 12%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (apply cr_slot_bridge; pcw).
    assert (Hb6 : add_vec (pa_stk sp0 12%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk sp0 6) by (apply cr_slot_bridge; pcw).
    assert (Hb8 : add_vec (pa_stk sp0 12%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 8) by (apply cr_slot_bridge; pcw).
    assert (Hb9 : add_vec (pa_stk sp0 12%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 9) by (apply cr_slot_bridge; pcw).
    (* +0xce  c.ldsp rra,88(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CR + 0xce)) (mword_of_int 11 : mword 6) Rra
              M (av - 12)%nat (m0 !!! Regidx Rra) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hice [K1]").
    { iEval (rewrite HMsp Hb1). iExact "K1". }
    iIntros (CIDe0 Hse0) "Hcg Hpc K1". iEval (rewrite HMsp Hb1) in "K1".
    set (E1 := <[Regidx Rra := regval_into_reg (m0 !!! Regidx Rra)]> M).
    change (<[Regidx Rra := regval_into_reg (m0 !!! Regidx Rra)]> M) with E1.
    assert (HE1sp : E1 !!! Regidx csp_rs1 = pa_stk sp0 12%nat)
      by (rewrite /E1 upd_ne; [exact HMsp | reg_neq]).
    assert (Ped0 : add_vec_int (mword_of_int (CR + 0xce) : mword 64) 2
                  = mword_of_int (CR + 0xd0)) by pcw.
    iEval (rewrite Ped0) in "Hpc".
    (* +0xd0  c.ldsp rs0,80(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CR + 0xd0)) (mword_of_int 10 : mword 6) Rs0
              E1 (av - 12)%nat (m0 !!! Regidx Rs0) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hid0 [K2]").
    { iEval (rewrite HE1sp Hb2). iExact "K2". }
    iIntros (CIDe1 Hse1) "Hcg Hpc K2". iEval (rewrite HE1sp Hb2) in "K2".
    set (E2 := <[Regidx Rs0 := regval_into_reg (m0 !!! Regidx Rs0)]> E1).
    change (<[Regidx Rs0 := regval_into_reg (m0 !!! Regidx Rs0)]> E1) with E2.
    assert (HE2sp : E2 !!! Regidx csp_rs1 = pa_stk sp0 12%nat)
      by (rewrite /E2 upd_ne; [exact HE1sp | reg_neq]).
    assert (Ped2 : add_vec_int (mword_of_int (CR + 0xd0) : mword 64) 2
                  = mword_of_int (CR + 0xd2)) by pcw.
    iEval (rewrite Ped2) in "Hpc".
    (* +0xd2  c.ldsp rs1,72(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CR + 0xd2)) (mword_of_int 9 : mword 6) Rs1
              E2 (av - 12)%nat (m0 !!! Regidx Rs1) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hid2 [K3]").
    { iEval (rewrite HE2sp Hb3). iExact "K3". }
    iIntros (CIDe2 Hse2) "Hcg Hpc K3". iEval (rewrite HE2sp Hb3) in "K3".
    set (E3 := <[Regidx Rs1 := regval_into_reg (m0 !!! Regidx Rs1)]> E2).
    change (<[Regidx Rs1 := regval_into_reg (m0 !!! Regidx Rs1)]> E2) with E3.
    assert (HE3sp : E3 !!! Regidx csp_rs1 = pa_stk sp0 12%nat)
      by (rewrite /E3 upd_ne; [exact HE2sp | reg_neq]).
    assert (Ped4 : add_vec_int (mword_of_int (CR + 0xd2) : mword 64) 2
                  = mword_of_int (CR + 0xd4)) by pcw.
    iEval (rewrite Ped4) in "Hpc".
    (* +0xd4  c.ldsp rs2,64(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CR + 0xd4)) (mword_of_int 8 : mword 6) Rs2
              E3 (av - 12)%nat (m0 !!! Regidx Rs2) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hid4 [K4]").
    { iEval (rewrite HE3sp Hb4). iExact "K4". }
    iIntros (CIDe3 Hse3) "Hcg Hpc K4". iEval (rewrite HE3sp Hb4) in "K4".
    set (E4 := <[Regidx Rs2 := regval_into_reg (m0 !!! Regidx Rs2)]> E3).
    change (<[Regidx Rs2 := regval_into_reg (m0 !!! Regidx Rs2)]> E3) with E4.
    assert (HE4sp : E4 !!! Regidx csp_rs1 = pa_stk sp0 12%nat)
      by (rewrite /E4 upd_ne; [exact HE3sp | reg_neq]).
    assert (Ped6 : add_vec_int (mword_of_int (CR + 0xd4) : mword 64) 2
                  = mword_of_int (CR + 0xd6)) by pcw.
    iEval (rewrite Ped6) in "Hpc".
    (* +0xd6  c.ldsp rs3,56(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CR + 0xd6)) (mword_of_int 7 : mword 6) Rs3
              E4 (av - 12)%nat (m0 !!! Regidx Rs3) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hid6 [K5]").
    { iEval (rewrite HE4sp Hb5). iExact "K5". }
    iIntros (CIDe4 Hse4) "Hcg Hpc K5". iEval (rewrite HE4sp Hb5) in "K5".
    set (E5 := <[Regidx Rs3 := regval_into_reg (m0 !!! Regidx Rs3)]> E4).
    change (<[Regidx Rs3 := regval_into_reg (m0 !!! Regidx Rs3)]> E4) with E5.
    assert (HE5sp : E5 !!! Regidx csp_rs1 = pa_stk sp0 12%nat)
      by (rewrite /E5 upd_ne; [exact HE4sp | reg_neq]).
    assert (Ped8 : add_vec_int (mword_of_int (CR + 0xd6) : mword 64) 2
                  = mword_of_int (CR + 0xd8)) by pcw.
    iEval (rewrite Ped8) in "Hpc".
    (* +0xd8  c.ldsp rs4,48(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CR + 0xd8)) (mword_of_int 6 : mword 6) Rs4
              E5 (av - 12)%nat (m0 !!! Regidx Rs4) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hid8 [K6]").
    { iEval (rewrite HE5sp Hb6). iExact "K6". }
    iIntros (CIDe5 Hse5) "Hcg Hpc K6". iEval (rewrite HE5sp Hb6) in "K6".
    set (E6 := <[Regidx Rs4 := regval_into_reg (m0 !!! Regidx Rs4)]> E5).
    change (<[Regidx Rs4 := regval_into_reg (m0 !!! Regidx Rs4)]> E5) with E6.
    assert (HE6sp : E6 !!! Regidx csp_rs1 = pa_stk sp0 12%nat)
      by (rewrite /E6 upd_ne; [exact HE5sp | reg_neq]).
    assert (Peda : add_vec_int (mword_of_int (CR + 0xd8) : mword 64) 2
                  = mword_of_int (CR + 0xda)) by pcw.
    iEval (rewrite Peda) in "Hpc".
    (* +0xda  c.ldsp rs6,32(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CR + 0xda)) (mword_of_int 4 : mword 6) Rs6
              E6 (av - 12)%nat (m0 !!! Regidx Rs6) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hida [K8]").
    { iEval (rewrite HE6sp Hb8). iExact "K8". }
    iIntros (CIDe6 Hse6) "Hcg Hpc K8". iEval (rewrite HE6sp Hb8) in "K8".
    set (E7 := <[Regidx Rs6 := regval_into_reg (m0 !!! Regidx Rs6)]> E6).
    change (<[Regidx Rs6 := regval_into_reg (m0 !!! Regidx Rs6)]> E6) with E7.
    assert (HE7sp : E7 !!! Regidx csp_rs1 = pa_stk sp0 12%nat)
      by (rewrite /E7 upd_ne; [exact HE6sp | reg_neq]).
    assert (Pedc : add_vec_int (mword_of_int (CR + 0xda) : mword 64) 2
                  = mword_of_int (CR + 0xdc)) by pcw.
    iEval (rewrite Pedc) in "Hpc".
    (* +0xdc  c.ldsp rs7,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CR + 0xdc)) (mword_of_int 3 : mword 6) Rs7
              E7 (av - 12)%nat (m0 !!! Regidx Rs7) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hidc [K9]").
    { iEval (rewrite HE7sp Hb9). iExact "K9". }
    iIntros (CIDe7 Hse7) "Hcg Hpc K9". iEval (rewrite HE7sp Hb9) in "K9".
    set (E8 := <[Regidx Rs7 := regval_into_reg (m0 !!! Regidx Rs7)]> E7).
    change (<[Regidx Rs7 := regval_into_reg (m0 !!! Regidx Rs7)]> E7) with E8.
    assert (HE8sp : E8 !!! Regidx csp_rs1 = pa_stk sp0 12%nat)
      by (rewrite /E8 upd_ne; [exact HE7sp | reg_neq]).
    assert (Pede : add_vec_int (mword_of_int (CR + 0xdc) : mword 64) 2
                  = mword_of_int (CR + 0xde)) by pcw.
    iEval (rewrite Pede) in "Hpc".
    (* +0xde  c.addi16sp sp,+96 : the pop *)
    assert (Hspv : add_vec (E8 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))) = sp0).
    { rewrite HE8sp. unfold pa_stk, add_vec_int. rewrite add_vec_assoc.
      rewrite (_ : add_vec (mword_of_int (- (8 * Z.of_nat 12%nat)) : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6)))
                   = (mword_of_int 0 : mword 64)); [| pcw].
      apply bv_add_0_r. vm_compute. reflexivity. }
    assert (Hpop : E8 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E8 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6)))) 12%nat)
      by (rewrite Hspv HE8sp; reflexivity).
    iDestruct (cr_frame_back sp0 m0 with "[K1 K2 K3 K4 K5 K6 K8 K9] Hrest") as "Hframe".
    { rewrite /cr_saved. iFrame "K1 K2 K3 K4 K5 K6 K8 K9". }
    iEval (rewrite -Hspv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (CR + 0xde)) (mword_of_int 6 : mword 6)
              E8 (av - 12)%nat 12%nat true Hpop with "Hcg Hpc Hi0de Hframe").
    iIntros (CIDp Hsp') "Hcg Hpc".
    assert (Havx : (av - 12 + 12)%nat = av) by (lia).
    iEval (rewrite Havx) in "Hcg".
    set (E9 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E8 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))))]> E8).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E8 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))))]> E8) with E9.
    assert (Pe0 : add_vec_int (mword_of_int (CR + 0xde) : mword 64) 2
                  = mword_of_int (CR + 0xe0)) by pcw.
    iEval (rewrite Pe0) in "Hpc".
    (* +0xe0  c.ret *)
    assert (HE9ra : E9 !!! Regidx Rra = m0 !!! Regidx Rra).
    { rewrite /E9 upd_ne; [| reg_neq]. rewrite /E8 upd_ne; [| reg_neq].
      rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_ne; [| reg_neq].
      rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq].
      rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq].
      rewrite /E1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (CR + 0xe0)) Rra E9 av true
              ltac:(nz) with "Hcg Hpc Hi0e0").
    iIntros (CIDr Hsr) "Hcg Hpc". iEval (rgne) in "Hpc".
    iEval (rewrite HE9ra) in "Hpc".
    assert (HE9a0 : E9 !!! Regidx Ra0 = (mword_of_int r : mword 64)).
    { rewrite /E9 upd_ne; [| reg_neq]. rewrite /E8 upd_ne; [| reg_neq].
      rewrite /E7 upd_ne; [| reg_neq]. rewrite /E6 upd_ne; [| reg_neq].
      rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq].
      rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq].
      rewrite /E1 upd_ne; [exact HMa0 | reg_neq]. }
    assert (Hcs : callee_saved m0 E9).
    {
      destruct HMcs as (Q5 & Q8 & Q9 & Q10 & Q11).
      unfold callee_saved. split_and!.
      - rewrite /E9 upd_eq. unfold regval_into_reg.
        rewrite Hspv. symmetry. exact Hm0sp.
      -
        rewrite /E9 upd_ne; [| reg_neq].
        rewrite /E8 upd_ne; [| reg_neq].
        rewrite /E7 upd_ne; [| reg_neq].
        rewrite /E6 upd_ne; [| reg_neq].
        rewrite /E5 upd_ne; [| reg_neq].
        rewrite /E4 upd_ne; [| reg_neq].
        rewrite /E3 upd_ne; [| reg_neq].
        rewrite /E2 upd_eq. reflexivity.
      -
        rewrite /E9 upd_ne; [| reg_neq].
        rewrite /E8 upd_ne; [| reg_neq].
        rewrite /E7 upd_ne; [| reg_neq].
        rewrite /E6 upd_ne; [| reg_neq].
        rewrite /E5 upd_ne; [| reg_neq].
        rewrite /E4 upd_ne; [| reg_neq].
        rewrite /E3 upd_eq. reflexivity.
      -
        rewrite /E9 upd_ne; [| reg_neq].
        rewrite /E8 upd_ne; [| reg_neq].
        rewrite /E7 upd_ne; [| reg_neq].
        rewrite /E6 upd_ne; [| reg_neq].
        rewrite /E5 upd_ne; [| reg_neq].
        rewrite /E4 upd_eq. reflexivity.
      -
        rewrite /E9 upd_ne; [| reg_neq].
        rewrite /E8 upd_ne; [| reg_neq].
        rewrite /E7 upd_ne; [| reg_neq].
        rewrite /E6 upd_ne; [| reg_neq].
        rewrite /E5 upd_eq. reflexivity.
      -
        rewrite /E9 upd_ne; [| reg_neq].
        rewrite /E8 upd_ne; [| reg_neq].
        rewrite /E7 upd_ne; [| reg_neq].
        rewrite /E6 upd_eq. reflexivity.
      -
        rewrite /E9 upd_ne; [| reg_neq].
        rewrite /E8 upd_ne; [| reg_neq].
        rewrite /E7 upd_ne; [| reg_neq].
        rewrite /E6 upd_ne; [| reg_neq].
        rewrite /E5 upd_ne; [| reg_neq].
        rewrite /E4 upd_ne; [| reg_neq].
        rewrite /E3 upd_ne; [| reg_neq].
        rewrite /E2 upd_ne; [| reg_neq].
        rewrite /E1 upd_ne; [| reg_neq].
        exact Q5.
      -
        rewrite /E9 upd_ne; [| reg_neq].
        rewrite /E8 upd_ne; [| reg_neq].
        rewrite /E7 upd_eq. reflexivity.
      -
        rewrite /E9 upd_ne; [| reg_neq].
        rewrite /E8 upd_eq. reflexivity.
      -
        rewrite /E9 upd_ne; [| reg_neq].
        rewrite /E8 upd_ne; [| reg_neq].
        rewrite /E7 upd_ne; [| reg_neq].
        rewrite /E6 upd_ne; [| reg_neq].
        rewrite /E5 upd_ne; [| reg_neq].
        rewrite /E4 upd_ne; [| reg_neq].
        rewrite /E3 upd_ne; [| reg_neq].
        rewrite /E2 upd_ne; [| reg_neq].
        rewrite /E1 upd_ne; [| reg_neq].
        exact Q8.
      -
        rewrite /E9 upd_ne; [| reg_neq].
        rewrite /E8 upd_ne; [| reg_neq].
        rewrite /E7 upd_ne; [| reg_neq].
        rewrite /E6 upd_ne; [| reg_neq].
        rewrite /E5 upd_ne; [| reg_neq].
        rewrite /E4 upd_ne; [| reg_neq].
        rewrite /E3 upd_ne; [| reg_neq].
        rewrite /E2 upd_ne; [| reg_neq].
        rewrite /E1 upd_ne; [| reg_neq].
        exact Q9.
      -
        rewrite /E9 upd_ne; [| reg_neq].
        rewrite /E8 upd_ne; [| reg_neq].
        rewrite /E7 upd_ne; [| reg_neq].
        rewrite /E6 upd_ne; [| reg_neq].
        rewrite /E5 upd_ne; [| reg_neq].
        rewrite /E4 upd_ne; [| reg_neq].
        rewrite /E3 upd_ne; [| reg_neq].
        rewrite /E2 upd_ne; [| reg_neq].
        rewrite /E1 upd_ne; [| reg_neq].
        exact Q10.
      -
        rewrite /E9 upd_ne; [| reg_neq].
        rewrite /E8 upd_ne; [| reg_neq].
        rewrite /E7 upd_ne; [| reg_neq].
        rewrite /E6 upd_ne; [| reg_neq].
        rewrite /E5 upd_ne; [| reg_neq].
        rewrite /E4 upd_ne; [| reg_neq].
        rewrite /E3 upd_ne; [| reg_neq].
        rewrite /E2 upd_ne; [| reg_neq].
        rewrite /E1 upd_ne; [| reg_neq].
        exact Q11.
    }
    iDestruct (cpu_own_transport CID CIDr 0%nat eb pj true ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    rewrite /cr_ret.
    iSpecialize ("Hcont" $! CIDr with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E9 r (pv_upt V) with "[%] [%] [%] [%] Hcg Hcnt Hpc [Hpriv]").
    - exact Hcs.
    - apply uptd_ext_refl.
    - exact Hr.
    - exact HE9a0.
    - destruct V as [vsz vupt vtf vofl vcwd vnm]. iExact "Hpriv".
  Qed.

  (* =================================================================== *)
  (*  [EPI]: the epilogue packaged as a CONTINUATION.                     *)
  (*                                                                      *)
  (*  The eight unconditionally-saved slots ride INSIDE it -- every exit   *)
  (*  reaches +0xce and none of them is in a position to hand those slots  *)
  (*  over one at a time -- so what a caller supplies is only the four     *)
  (*  free ones, the answer in a0, and the process block.                  *)
  (* =================================================================== *)
  Definition cr_epi_prop `{CID0 : CpuId}
      (jp : nat) (sp0 : mword 64) (m0 : regfile) (av : nat)
      (pid : mword 32) (V : pprivate) (n : Z) (lks : gset string) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr jp) (fun (CIDe : CpuId) =>
       ∀ (M : regfile) (P' : uptd) (r : Z),
         ⌜ M !!! Regidx csp_rs1 = pa_stk sp0 12%nat ⌝ -∗
         ⌜ M !!! Regidx Ra0 = (mword_of_int r : mword 64) ⌝ -∗
         ⌜ cr_cs_hi M m0 ⌝ -∗
         ⌜ uptd_ext (pv_upt V) P' ⌝ -∗
         ⌜ (-1 <= r <= Z.max 0 n)%Z ⌝ -∗
         sie_cap_gpr KT1 M (av - 12)%nat true (proc_addr jp) -∗
         pc_is (mword_of_int (CR + 0xce)) -∗
         cpu_own 0%nat true (proc_addr jp) true lks -∗
         proc_priv_core (proc_addr jp) pid (upd_upt V P') -∗
         cr_rest sp0 -∗
         WP (Loop : expr riscv_lang)))%I.

  (* The caller's exit, RE-BASED on a page table this call has already
     extended.  Every block below hands the process block back at some
     [upd_upt V P'], so the exit it carries has to speak that descriptor;
     without this the [uptd_ext] chain would have to be re-threaded at each
     of the five exits instead of once, here. *)
  Lemma cr_ret_shift `{CID0 : CpuId} (jp : nat) (m0 : regfile) (av : nat)
      (pid : mword 32) (V : pprivate) (P' : uptd) (n : Z) (lks : gset string) :
    uptd_ext (pv_upt V) P' ->
    cr_ret (CID0 := CID0) jp m0 av true pid V n lks -∗
    cr_ret (CID0 := CID0) jp m0 av true pid (upd_upt V P') n lks.
  Proof.
    intro Hx. iIntros "H" (CIDx Hsx mf r P'') "%Hcs %Hex %Hr %Ha0 Hcg Hcnt Hpc Hpriv".
    iSpecialize ("H" $! CIDx with "[%]"); [exact Hsx|].
    iApply ("H" $! mf r P'' with "[%] [%] [%] [%] Hcg Hcnt Hpc [Hpriv]").
    - exact Hcs.
    - exact (uptd_ext_trans _ P' _ Hx Hex).
    - exact Hr.
    - exact Ha0.
    - iExact "Hpriv".
  Qed.

  Lemma cr_mk_epi `{CID : CpuId} (jp : nat) (sp0 : mword 64) (m0 : regfile)
      (av : nat) (pid : mword 32) (V : pprivate) (n : Z) (lks : gset string) :
    m0 !!! Regidx csp_rs1 = sp0 ->
    (consoleread_stack <= av)%nat ->
    kernel_text -∗ cr_saved sp0 m0 -∗
    cr_ret (CID0 := CID) jp m0 av true pid V n lks -∗
    cr_epi_prop (CID0 := CID) jp sp0 m0 av pid V n lks.
  Proof.
    intros Hm0sp Hav.
    iIntros "#Ht Hsaved Hcont".
    rewrite /cr_epi_prop.
    iIntros (CIDe Hse M P' r) "%Hsp %Ha0 %Hcs %Hext %Hr Hcg Hpc Hcnt Hpriv Hrest".
    iApply (cr_epi (CID := CIDe) CIDe jp m0 M av true sp0 pid (upd_upt V P') n r lks
              Hm0sp Hsp Ha0 Hcs Hr Hav eq_refl ltac:(intros _; reflexivity)
              with "Ht Hcg Hcnt Hpc Hpriv Hsaved Hrest").
    iApply (cr_ret_shift (CID0 := CIDe) jp m0 av pid V P' n lks Hext).
    iApply (wp_next_retarget CID CIDe true (proc_addr jp) _ ltac:(wp_next_chain)
              with "Hcont").
  Qed.

End CrBodies.

(* ===================================================================== *)
Module ConsolereadProof (Myproc : MYPROC) (Acquire : ACQUIRE) (Killed : KILLED)
                        (SleepPrepare : SLEEP_PREPARE) (Sleep : SLEEP)
                        (EitherCopyout : EITHER_COPYOUT) (Release : RELEASE)
                        : CONSOLEREAD.

Section ProofConsoleread.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* Normalise every [rget m k] the leaves produce back to [m !!! Regidx k]
     across the WHOLE proofmode goal: away from tp the two are the same
     lookup, and every index this function names is a literal. *)
  Local Ltac rgall := repeat (rewrite rget_ne; [| vm_compute; discriminate]).

  (* [eb] is the literal [true] here (the parking premise), so [iNext] would
     otherwise descend THROUGH [cpu_own] and strip the later off
     [intr_handler_spec].  The one real [iNext] in this file is the wait
     loop's Loeb back edge. *)
  Local Typeclasses Opaque cpu_own.

  (* =================================================================== *)
  (*  [RETX] (+0xfc): release, [target - n], and jump to the epilogue.    *)
  (*                                                                      *)
  (*  FIVE ENTRIES reach it -- the [n <= 0] test at +0x38, and the four    *)
  (*  two-instruction [ld s5,40(sp)] stubs at +0xee / +0xf6 / +0xfa /      *)
  (*  +0x10e -- so it is a continuation rather than straight-line code.    *)
  (*  Every entry has s5 back at its entry value, which is why [cr_cs_hi]  *)
  (*  is already true here and the epilogue has no restore run to share.   *)
  (* =================================================================== *)
  (* [lks] is the OUTER set (matching [cr_epi_prop]/[cr_ret], which this
     hands off to unmodified via [cr_mk_retx]): the PRECONDITION below still
     holds "cons", so it reads [{["cons"]} ∪ lks], not bare
     [lks] -- see durable-notes.md's OUTER/INNER convention. *)
  Definition cr_retx_prop `{CID0 : CpuId}
      (γc : gname) (jp : nat) (sp0 : mword 64) (m0 : regfile) (av : nat)
      (pid : mword 32) (V : pprivate) (n : Z) (lks : gset string) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr jp) (fun (CIDx : CpuId) =>
       ∀ (M : regfile) (P' : uptd) (nc : Z),
         ⌜ M !!! Regidx csp_rs1 = pa_stk sp0 12%nat ⌝ -∗
         ⌜ M !!! Regidx Rs3 = (mword_of_int nc : mword 64) ⌝ -∗
         ⌜ M !!! Regidx Rs7 = (mword_of_int n : mword 64) ⌝ -∗
         ⌜ cr_cs_hi M m0 ⌝ -∗
         ⌜ (0 <= n - nc <= Z.max 0 n)%Z ⌝ -∗
         ⌜ uptd_ext (pv_upt V) P' ⌝ -∗
         sie_cap_gpr KT1 M (trap_res true + (av - 12))%nat false (proc_addr jp) -∗
         pc_is (mword_of_int (CR + 0xfc)) -∗
         cpu_own 1%nat true (proc_addr jp) false ({["cons"]} ∪ lks) -∗
         arm_pay KT1 0%nat true (proc_addr jp) -∗
         locked γc cpu_id -∗
         cons_res -∗
         proc_priv_core (proc_addr jp) pid (upd_upt V P') -∗
         cr_rest sp0 -∗
         WP (Loop : expr riscv_lang)))%I.

  Lemma cr_mk_retx (γc : gname) (jp : nat) (sp0 : mword 64) (m0 : regfile)
      (av : nat) (pid : mword 32) (V : pprivate) (n : Z) (lks : gset string) :
    (- 2 ^ 31 <= n < 2 ^ 31)%Z ->
    (consoleread_stack <= av)%nat ->
    locks_below lks "cons" ->
    kernel_text -∗ is_conslock γc -∗
    cr_epi_prop (CID0 := CID) jp sp0 m0 av pid V n lks -∗
    cr_retx_prop (CID0 := CID) γc jp sp0 m0 av pid V n lks.
  Proof.
    intros Hn31 Hav Hbelow.
    pose proof (locks_below_not_elem _ _ Hbelow) as Hfresh.
    iIntros "#Ht #Hlk EPI".
    rewrite /cr_retx_prop.
    iIntros (CIDx Hsx M P' nc)
      "%Hsp %Hs3 %Hs7 %Hcs %Hrng %Hext Hcg Hpc Hcnt Hpay Hlocked Hres Hpriv Hrest".
    iPoseProof (cnri_0fc with "Ht") as "Hi0fc".
    iPoseProof (cnri_100 with "Ht") as "Hi100".
    iPoseProof (cnri_104 with "Ht") as "Hi104".
    iPoseProof (cnri_108 with "Ht") as "Hi108".
    iPoseProof (cnri_10c with "Ht") as "Hi10c".
    (* ---- +0xfc auipc a0,0x12 ; +0x100 addi a0,a0,60 : a0 := &cons ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (CR + 0xfc)) Ra0 (mword_of_int 18 : mword 20)
              M (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi0fc").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (X1 := <[Regidx Ra0 := regval_into_reg
        (add_vec (mword_of_int (CR + 0xfc) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> M).
    assert (Hp100 : add_vec_int (mword_of_int (CR + 0xfc) : mword 64) 4
                    = mword_of_int (CR + 0x100)) by pcw.
    iEval (rewrite Hp100) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (CR + 0x100)) Ra0 Ra0 (mword_of_int 92 : mword 12)
              X1 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi100").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (X2 := <[Regidx Ra0 := regval_into_reg
        (add_vec (X1 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 92 : mword 12)))]> X1).
    assert (HX2a0 : X2 !!! Regidx Ra0 = a_cons).
    { rewrite /X2 upd_eq /X1 upd_eq /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp104 : add_vec_int (mword_of_int (CR + 0x100) : mword 64) 4
                    = mword_of_int (CR + 0x104)) by pcw.
    iEval (rewrite Hp104) in "Hpc".
    (* ---- +0x104 jal ra,release ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (CR + 0x104)) Rra (mword_of_int 2502 : mword 21)
              X2 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi104").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (X3 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CR + 0x104) : mword 64) 4)]> X2).
    assert (Hjrl : add_vec (mword_of_int (CR + 0x104) : mword 64)
                     (sign_extend' 64 (mword_of_int 2502 : mword 21))
                   = mword_of_int KernelSyms.release) by pcw.
    iEval (rewrite Hjrl) in "Hpc".
    assert (HX3a0 : X3 !!! Regidx Ra0 = a_cons)
      by (rewrite /X3 upd_ne; [exact HX2a0 | reg_neq]).
    assert (HX3ra : X3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CR + 0x104) : mword 64) 4)
      by (rewrite /X3; apply upd_eq).
    assert (HX3lka : add_vec (X3 !!! Regidx Ra0)
                       (sign_extend' 64 (mword_of_int 0 : mword 12)) = a_cons).
    { rewrite HX3a0.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by pcw.
      apply kv_addv_zero. }
    assert (HthrX : forall r : mword 5, is_cs_idx r = true -> X3 !!! Regidx r = M !!! Regidx r).
    { intros r Hr.
      assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> Ra0) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /X3 upd_ne; [| congruence]. rewrite /X2 upd_ne; [| congruence].
      rewrite /X1 upd_ne; [| congruence]. reflexivity. }
    iApply (Release.wp_release_sconf KT1 γc a_cons "cons"%string cons_res X3
              0%nat true (proc_addr jp) (av - 12)%nat ({["cons"]} ∪ lks) HX3lka
              ltac:(lia)
              with "Hcg Ht Hpc Hlk Hlocked Hres Hcnt Hpay").
    iIntros (CIDr Hsr mr) "Hcg Hpc %Hcsr Hcnt". rgall.
    assert (Hsetback : ({["cons"]} ∪ lks) ∖ {["cons"]} = lks)
      by (apply locks_add_del_below; lkbelow).
    iEval (rewrite Hsetback) in "Hcnt".
    iEval (rewrite HX3ra) in "Hpc".
    assert (Hp108 : ret_pc (add_vec_int (mword_of_int (CR + 0x104) : mword 64) 4)
                    = (mword_of_int (CR + 0x108) : mword 64)) by pcw.
    iEval (rewrite Hp108) in "Hpc".
    assert (Hthr : forall r : mword 5, is_cs_idx r = true -> mr !!! Regidx r = M !!! Regidx r).
    { intros r Hr. rewrite (callee_saved_lookup Hcsr r Hr). apply HthrX; exact Hr. }
    assert (Hmrs3 : mr !!! Regidx Rs3 = (mword_of_int nc : mword 64))
      by (rewrite (Hthr Rs3 ltac:(vm_compute; reflexivity)); exact Hs3).
    assert (Hmrs7 : mr !!! Regidx Rs7 = (mword_of_int n : mword 64))
      by (rewrite (Hthr Rs7 ltac:(vm_compute; reflexivity)); exact Hs7).
    (* ---- +0x108 subw a0,s7,s3 : the answer ---- *)
    assert (Hdiff : (0 <= n - nc < 2 ^ 31)%Z).
    { destruct (Z.max_spec 0 n) as [[_ Hm] | [_ Hm]]; rewrite Hm in Hrng; lia. }
    assert (Hsubw : sign_extend' 64
                      (sub_vec (subrange_vec_dec (mword_of_int n : mword 64) 31 0 : mword 32)
                               (subrange_vec_dec (mword_of_int nc : mword 64) 31 0 : mword 32))
                    = (mword_of_int (n - nc) : mword 64))
      by (apply w32_subw_moi; exact Hdiff).
    iApply (wp_subw_s_sconf (mword_of_int (CR + 0x108)) Ra0 Rs7 Rs3
              mr (av - 12)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi108").
    iIntros (CIDs Hss) "Hcg Hpc". rgall.
    iEval (rewrite Hmrs3 Hmrs7 Hsubw) in "Hcg".
    set (X4 := <[Regidx Ra0 := regval_into_reg (mword_of_int (n - nc) : mword 64)]> mr).
    assert (Hp10c : add_vec_int (mword_of_int (CR + 0x108) : mword 64) 4
                    = mword_of_int (CR + 0x10c)) by pcw.
    iEval (rewrite Hp10c) in "Hpc".
    (* ---- +0x10c c.j -> the epilogue at +0xce ---- *)
    iApply (wp_cj_s_sconf (mword_of_int (CR + 0x10c))
              (sign_extend' 21 (concat_vec (mword_of_int 2017 : mword 11) ('b"0")))
              X4 (av - 12)%nat true ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi10c").
    iIntros (CIDj Hsj). iApply bi.later_intro. iIntros "Hcg Hpc". rgall.
    assert (Hjce : add_vec (mword_of_int (CR + 0x10c) : mword 64)
                     (sign_extend' 64 (sign_extend' 21
                        (concat_vec (mword_of_int 2017 : mword 11) ('b"0"))))
                   = mword_of_int (CR + 0xce)) by pcw.
    iEval (rewrite Hjce) in "Hpc".
    iSpecialize ("EPI" $! CIDj with "[%]"); [wp_next_chain|].
    iApply ("EPI" $! X4 P' (n - nc) with "[%] [%] [%] [%] [%] Hcg Hpc Hcnt Hpriv Hrest").
    - rewrite /X4 upd_ne; [| reg_neq].
      rewrite (Hthr csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp.
    - rewrite /X4 upd_eq. reflexivity.
    - destruct Hcs as (Q5 & Q8 & Q9 & Q10 & Q11). unfold cr_cs_hi. split_and!.
      + rewrite /X4 upd_ne; [| reg_neq].
        rewrite (Hthr Rs5 ltac:(vm_compute; reflexivity)). exact Q5.
      + rewrite /X4 upd_ne; [| reg_neq].
        rewrite (Hthr Rs8 ltac:(vm_compute; reflexivity)). exact Q8.
      + rewrite /X4 upd_ne; [| reg_neq].
        rewrite (Hthr Rs9 ltac:(vm_compute; reflexivity)). exact Q9.
      + rewrite /X4 upd_ne; [| reg_neq].
        rewrite (Hthr Rs10 ltac:(vm_compute; reflexivity)). exact Q10.
      + rewrite /X4 upd_ne; [| reg_neq].
        rewrite (Hthr Rs11 ltac:(vm_compute; reflexivity)). exact Q11.
    - exact Hext.
    - lia.
  Qed.

  (* THE FIVE EXITS, AS ONE NON-SEPARATING CONJUNCTION.  Exactly one is
     taken, and both alternatives need the whole frame, so [∧] -- not [∗] --
     is what lets each branch of an [iSplit] see the same slots.  This
     bundle is threaded LINEARLY through the head loop, the wait loop and
     the copy block: every one of them takes it as a premise and hands it
     to whichever successor it jumps to. *)
  Definition cr_exits `{CID0 : CpuId}
      (γc : gname) (jp : nat) (sp0 : mword 64) (m0 : regfile) (av : nat)
      (pid : mword 32) (V : pprivate) (n : Z) (lks : gset string) : iProp Σ :=
    (cr_retx_prop (CID0 := CID0) γc jp sp0 m0 av pid V n lks
     ∧ cr_epi_prop (CID0 := CID0) jp sp0 m0 av pid V n lks)%I.

  (* the pins every block in the body shares: the six live callee-saved
     roles plus the three registers nothing here ever writes *)
  Definition cr_regs (M : regfile) (m0 : regfile) (sp0 : mword 64)
      (nc : Z) (cur : mword 64) (n : Z) : Prop :=
    M !!! Regidx csp_rs1 = pa_stk sp0 12%nat
    /\ M !!! Regidx Rs0 = sp0
    /\ M !!! Regidx Rs1 = a_cons
    /\ M !!! Regidx Rs2 = a_cons_r
    /\ M !!! Regidx Rs3 = (mword_of_int nc : mword 64)
    /\ M !!! Regidx Rs4 = cur
    /\ M !!! Regidx Rs6 = (mword_of_int 1 : mword 64)
    /\ M !!! Regidx Rs7 = (mword_of_int n : mword 64)
    /\ M !!! Regidx Rs8 = m0 !!! Regidx Rs8
    /\ M !!! Regidx Rs9 = m0 !!! Regidx Rs9
    /\ M !!! Regidx Rs10 = m0 !!! Regidx Rs10
    /\ M !!! Regidx Rs11 = m0 !!! Regidx Rs11.

  (* =================================================================== *)
  (*  [HEAD] (+0x38): the outer [while (n > 0)] head.                     *)
  (* =================================================================== *)
  Definition cr_head_prop `{CID0 : CpuId}
      (γa γc γf : gname) (jp : nat) (sp0 : mword 64) (m0 : regfile) (av : nat)
      (pid : mword 32) (V : pprivate) (n : Z) (fl : nat) (lks : gset string) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr jp) (fun (CIDh : CpuId) =>
       ∀ (M : regfile) (nc : Z) (cur : mword 64) (P' : uptd),
         ⌜ cr_regs M m0 sp0 nc cur n ⌝ -∗
         ⌜ M !!! Regidx Rs5 = m0 !!! Regidx Rs5 ⌝ -∗
         ⌜ (0 <= n - nc <= Z.max 0 n)%Z ⌝ -∗
         ⌜ (Z.to_nat nc < fl)%nat ⌝ -∗
         ⌜ uptd_ext (pv_upt V) P' ⌝ -∗
         cr_exits (CID0 := CID0) γc jp sp0 m0 av pid V n lks -∗
         sie_cap_gpr KT1 M (trap_res true + (av - 12))%nat false (proc_addr jp) -∗
         pc_is (mword_of_int (CR + 0x38)) -∗
         (* OUTER [lks], still holding "cons" (see [cr_retx_prop]'s note). *)
         cpu_own 1%nat true (proc_addr jp) false ({["cons"]} ∪ lks) -∗
         arm_pay KT1 0%nat true (proc_addr jp) -∗
         locked γc cpu_id -∗
         cons_res -∗
         proc_priv_core (proc_addr jp) pid (upd_upt V P') -∗
         cr_rest sp0 -∗
         WP (Loop : expr riscv_lang)))%I.

  (* =================================================================== *)
  (*  [HAVE] (+0x76): a byte is available.  Entered from BOTH the         *)
  (*  fall-through of the wait loop (+0x74) and the entry test's          *)
  (*  "already non-empty" arm (+0xf2), each of which is the single        *)
  (*  [c.sdsp s5,40(sp)] that shrink-wraps s5 -- so this block owns slot  *)
  (*  7 AT ITS SAVED VALUE and every exit reloads s5 out of it.           *)
  (*                                                                      *)
  (*  The console's resource arrives DESTRUCTED, because a5 already holds  *)
  (*  the [cons.r] this block is about to bump: reassembling it at the     *)
  (*  seam would lose exactly the equation the [sw] at +0x82 needs.        *)
  (* =================================================================== *)
  Definition cr_have_prop `{CID0 : CpuId}
      (γa γc γf : gname) (jp : nat) (sp0 : mword 64) (m0 : regfile) (av : nat)
      (pid : mword 32) (V : pprivate) (n : Z) (fl : nat) (lks : gset string) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr jp) (fun (CIDv : CpuId) =>
       ∀ (M : regfile) (nc : Z) (cur : mword 64) (P' : uptd)
         (rr ww ee : mword 32) (bs : list (bv 8)),
         ⌜ cr_regs M m0 sp0 nc cur n ⌝ -∗
         ⌜ M !!! Regidx Ra5 = sign_extend' 64 rr ⌝ -∗
         ⌜ (0 < nc)%Z /\ (0 <= n - nc <= Z.max 0 n)%Z /\ (Z.to_nat nc <= fl)%nat ⌝ -∗
         ⌜ length bs = INPUT_BUF_SIZE ⌝ -∗
         ⌜ uptd_ext (pv_upt V) P' ⌝ -∗
         cr_exits (CID0 := CID0) γc jp sp0 m0 av pid V n lks -∗
         sie_cap_gpr KT1 M (trap_res true + (av - 12))%nat false (proc_addr jp) -∗
         pc_is (mword_of_int (CR + 0x76)) -∗
         (* OUTER [lks], still holding "cons" (see [cr_retx_prop]'s note). *)
         cpu_own 1%nat true (proc_addr jp) false ({["cons"]} ∪ lks) -∗
         arm_pay KT1 0%nat true (proc_addr jp) -∗
         locked γc cpu_id -∗
         a_cons_r ↦₄ rr -∗ a_cons_w ↦₄ ww -∗ a_cons_e ↦₄ ee -∗ cons_data bs -∗
         proc_priv_core (proc_addr jp) pid (upd_upt V P') -∗
         pa_stk sp0 7%nat ↦₈[KT1] (m0 !!! Regidx Rs5) -∗
         (∃ w : mword 64, pa_stk sp0 10%nat ↦₈[KT1] w) -∗
         (∃ w : mword 64, pa_stk sp0 11%nat ↦₈[KT1] w) -∗
         (∃ w : mword 64, pa_stk sp0 12%nat ↦₈[KT1] w) -∗
         WP (Loop : expr riscv_lang)))%I.

  (* ---- the address arithmetic the two stack objects need -------------- *)

  (* slot 7 is what [c.sdsp s5,40(sp)] / [c.ldsp s5,40(sp)] name *)
  Lemma cr_b7 (sp0 : mword 64) :
    add_vec (pa_stk sp0 12%nat)
      (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
    = pa_stk sp0 7%nat.
  Proof. apply cr_slot_bridge; pcw. Qed.

  (* [cbuf] is the single byte at [s0-81], i.e. byte 7 of slot 11 *)
  Lemma cr_cbufa (sp0 : mword 64) :
    add_vec sp0 (sign_extend' 64 (mword_of_int 4015 : mword 12))
    = pa_add (pa_stk sp0 11%nat) 7%nat.
  Proof.
    unfold pa_add, pa_stk, add_vec_int. rewrite add_vec_assoc.
    apply f_equal. apply bv_eq; vm_compute; reflexivity.
  Qed.

  (* [ConsoleInv.cons_byte_addr] at the immediate the [lbu] actually
     carries ([mword_of_int 24], not [mword_of_int (Z.of_nat cons_buf_off)]) *)
  Lemma cr_byaddr (i : nat) :
    (i < INPUT_BUF_SIZE)%nat ->
    add_vec (add_vec a_cons (mword_of_int (Z.of_nat i) : mword 64))
            (sign_extend' 64 (mword_of_int 24 : mword 12))
    = pa_add a_cons (cons_buf_off + i).
  Proof. intro Hi. rewrite <- (cons_byte_addr i Hi). reflexivity. Qed.

  Lemma cr_mk_have (γa γc γf : gname) (jp : nat) (sp0 : mword 64) (m0 : regfile)
      (av : nat) (pid : mword 32) (V : pprivate) (n : Z) (fl : nat) (lks : gset string) :
    (- 2 ^ 31 <= n < 2 ^ 31)%Z ->
    (consoleread_stack <= av)%nat ->
    (* the +0x76 arm still holds cons.lock across either_copyout, whose cone
       reaches "kmem"; the bound is stated where the siblings state it. *)
    locks_below lks "cons" ->
    kernel_text -∗ is_conslock γc -∗ kalloc_env γa None -∗
    cr_head_prop (CID0 := CID) γa γc γf jp sp0 m0 av pid V n fl lks -∗
    cr_have_prop (CID0 := CID) γa γc γf jp sp0 m0 av pid V n fl lks.
  Proof.
    intros Hn31 Hav Hbelow. iIntros "#Ht #Hlk #Henv HEAD".
    rewrite /cr_have_prop.
    iIntros (CIDv Hsv M nc cur P' rr ww ee bs)
      "%Hregs %Ha5 %Hnb %Hlen %Hext EX Hcg Hpc Hcnt Hpay Hlocked Hrc Hwc Hec Hdat Hpriv Hsl7 Hq10 Hq11 Hq12".
    destruct Hregs as (Hsp & Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs6 & Hs7 & Hcs8 & Hcs9 & Hcs10 & Hcs11).
    destruct Hnb as (Hncpos & Hrng & Hfl).
    assert (Hmax : Z.max 0 n = n) by lia.
    (* ---- +0x76 auipc a4,0x12 ; +0x7a addi a4,a4,194 : a4 := &cons ---- *)
    iPoseProof (cnri_076 with "Ht") as "Hi76".
    iApply (wp_auipc_s_sconf (mword_of_int (CR + 0x76)) Ra4 (mword_of_int 18 : mword 20)
              M (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi76").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (H1 := <[Regidx Ra4 := regval_into_reg
        (add_vec (mword_of_int (CR + 0x76) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> M).
    assert (Hp7a : add_vec_int (mword_of_int (CR + 0x76) : mword 64) 4
                   = mword_of_int (CR + 0x7a)) by pcw.
    iEval (rewrite Hp7a) in "Hpc".
    iPoseProof (cnri_07a with "Ht") as "Hi7a".
    iApply (wp_addi4_s_sconf (mword_of_int (CR + 0x7a)) Ra4 Ra4 (mword_of_int 226 : mword 12)
              H1 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi7a").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (H2 := <[Regidx Ra4 := regval_into_reg
        (add_vec (H1 !!! Regidx Ra4) (sign_extend' 64 (mword_of_int 226 : mword 12)))]> H1).
    assert (HH2a4 : H2 !!! Regidx Ra4 = a_cons).
    { rewrite /H2 upd_eq /H1 upd_eq /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (HH2a5 : H2 !!! Regidx Ra5 = sign_extend' 64 rr).
    { rewrite /H2 upd_ne; [| reg_neq]. rewrite /H1 upd_ne; [| reg_neq]. exact Ha5. }
    assert (Hp7e : add_vec_int (mword_of_int (CR + 0x7a) : mword 64) 4
                   = mword_of_int (CR + 0x7e)) by pcw.
    iEval (rewrite Hp7e) in "Hpc".
    (* ---- +0x7e addiw a3,a5,1 ---- *)
    iPoseProof (cnri_07e with "Ht") as "Hi7e".
    iApply (wp_addiw_s_sconf (mword_of_int (CR + 0x7e)) Ra3 Ra5 (mword_of_int 1 : mword 12)
              H2 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi7e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite HH2a5) in "Hcg".
    set (H3 := <[Regidx Ra3 := regval_into_reg (sign_extend' 64 (subrange_vec_dec
        (add_vec (sign_extend' 64 rr) (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0))]> H2).
    assert (Hp82 : add_vec_int (mword_of_int (CR + 0x7e) : mword 64) 4
                   = mword_of_int (CR + 0x82)) by pcw.
    iEval (rewrite Hp82) in "Hpc".
    (* ---- +0x82 sw a3,152(a4) : cons.r := r + 1 ---- *)
    assert (HH3a4 : H3 !!! Regidx Ra4 = a_cons)
      by (rewrite /H3 upd_ne; [exact HH2a4 | reg_neq]).
    assert (HH3a3 : H3 !!! Regidx Ra3 = sign_extend' 64 (subrange_vec_dec
        (add_vec (sign_extend' 64 rr) (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0))
      by (rewrite /H3; apply upd_eq).
    assert (Hra : add_vec (H3 !!! Regidx Ra4)
                    (sign_extend' 64 (mword_of_int 152 : mword 12)) = a_cons_r)
      by (rewrite HH3a4; reflexivity).
    iPoseProof (cnri_082 with "Ht") as "Hi82".
    iApply (wp_sw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CR + 0x82)) Ra3 Ra4 (mword_of_int 152 : mword 12)
              H3 (trap_res true + (av - 12))%nat rr false with "Hcg Hpc Hi82 [Hrc]").
    { rgall. iEval (rewrite Hra). iExact "Hrc". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hrc". rgall.
    iEval (rewrite Hra HH3a3 cr_sw_r) in "Hrc".
    assert (Hp86 : add_vec_int (mword_of_int (CR + 0x82) : mword 64) 4
                   = mword_of_int (CR + 0x86)) by pcw.
    iEval (rewrite Hp86) in "Hpc".
    (* ---- +0x86 andi a3,a5,127 : the ring index ---- *)
    set (idxw := and_vec (sign_extend' 64 rr : mword 64)
                   (sign_extend' 64 (mword_of_int 127 : mword 12))).
    set (idx := Z.to_nat (bv_unsigned idxw)).
    assert (Hidxb : (0 <= bv_unsigned idxw < 128)%Z) by (rewrite /idxw;
          apply (w32_and_mask_bound _ (mword_of_int 127) 7 ltac:(lia)
                   ltac:(vm_compute; reflexivity))).
    assert (Hidxlt : (idx < INPUT_BUF_SIZE)%nat) by (rewrite /idx /INPUT_BUF_SIZE; lia).
    assert (Hidxw : idxw = (mword_of_int (Z.of_nat idx) : mword 64)).
    { rewrite /idx Z2Nat.id; [| lia]. symmetry. apply w32_moi_unsigned. }
    assert (Hwv : and_vec (H3 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 127 : mword 12))
                  = (mword_of_int (Z.of_nat idx) : mword 64)).
    { rewrite /H3 upd_ne; [| reg_neq]. rewrite HH2a5. exact Hidxw. }
    iPoseProof (cnri_086 with "Ht") as "Hi86".
    iApply (wp_andi_s_sconf (mword_of_int (CR + 0x86)) Ra3 Ra5 (mword_of_int 127 : mword 12)
              (mword_of_int (Z.of_nat idx) : mword 64) H3 (trap_res true + (av - 12))%nat false
              ltac:(nz) ltac:(rdok) Hwv with "Hcg Hpc Hi86").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (H4 := <[Regidx Ra3 := regval_into_reg (mword_of_int (Z.of_nat idx) : mword 64)]> H3).
    assert (Hp8a : add_vec_int (mword_of_int (CR + 0x86) : mword 64) 4
                   = mword_of_int (CR + 0x8a)) by pcw.
    iEval (rewrite Hp8a) in "Hpc".
    (* ---- +0x8a c.add a4,a4,a3 ---- *)
    assert (HH4a4 : H4 !!! Regidx Ra4 = a_cons)
      by (rewrite /H4 upd_ne; [exact HH3a4 | reg_neq]).
    assert (HH4a3 : H4 !!! Regidx Ra3 = (mword_of_int (Z.of_nat idx) : mword 64))
      by (rewrite /H4; apply upd_eq).
    iPoseProof (cnri_08a with "Ht") as "Hi8a".
    iApply (wp_cadd_s_sconf (mword_of_int (CR + 0x8a)) Ra4 Ra3 H4
              (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi8a").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite HH4a4 HH4a3) in "Hcg".
    set (H5 := <[Regidx Ra4 := regval_into_reg
        (add_vec a_cons (mword_of_int (Z.of_nat idx) : mword 64))]> H4).
    assert (Hp8c : add_vec_int (mword_of_int (CR + 0x8a) : mword 64) 2
                   = mword_of_int (CR + 0x8c)) by pcw.
    iEval (rewrite Hp8c) in "Hpc".
    (* ---- +0x8c lbu a4,24(a4) : the byte ---- *)
    destruct (cons_data_lookup_lt bs idx Hlen Hidxlt) as [db Hlk].
    iDestruct (cons_data_acc bs idx db Hlk with "Hdat") as "[Hbyte Hdback]".
    assert (HH5a4 : H5 !!! Regidx Ra4 = add_vec a_cons (mword_of_int (Z.of_nat idx) : mword 64))
      by (rewrite /H5; apply upd_eq).
    iPoseProof (cnri_08c with "Ht") as "Hi8c".
    iApply (wp_lbu_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CR + 0x8c)) Ra4 Ra4 (mword_of_int 24 : mword 12)
              H5 (trap_res true + (av - 12))%nat (db : mword 8) false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi8c [Hbyte]").
    { rgall. iEval (rewrite HH5a4 (cr_byaddr idx Hidxlt)). iExact "Hbyte". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hbyte". rgall.
    iEval (rewrite HH5a4 (cr_byaddr idx Hidxlt)) in "Hbyte".
    iDestruct ("Hdback" with "Hbyte") as "Hdat".
    set (H6 := <[Regidx Ra4 := regval_into_reg (zero_extend' 64 (db : mword 8))]> H5).
    assert (Hp90 : add_vec_int (mword_of_int (CR + 0x8c) : mword 64) 4
                   = mword_of_int (CR + 0x90)) by pcw.
    iEval (rewrite Hp90) in "Hpc".
    (* ---- +0x90 sext.w s5,a4 : [c] ---- *)
    set (cbv := bv_unsigned (db : mword 8)).
    assert (Hcbr : (0 <= cbv < 256)%Z) by (rewrite /cbv; apply w32_byte_range).
    assert (HH6a4 : H6 !!! Regidx Ra4 = zero_extend' 64 (db : mword 8))
      by (rewrite /H6; apply upd_eq).
    assert (Hsextc : sign_extend' 64 (subrange_vec_dec
        (add_vec (zero_extend' 64 (db : mword 8))
                 (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0)
        = (mword_of_int cbv : mword 64)).
    { rewrite w32_zext8_moi. apply w32_sextw_moi. rewrite /cbv. lia. }
    iPoseProof (cnri_090 with "Ht") as "Hi90".
    iApply (wp_addiw_s_sconf (mword_of_int (CR + 0x90)) Rs5 Ra4 (mword_of_int 0 : mword 12)
              H6 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi90").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite HH6a4 Hsextc) in "Hcg".
    set (H7 := <[Regidx Rs5 := regval_into_reg (mword_of_int cbv : mword 64)]> H6).
    assert (Hp94 : add_vec_int (mword_of_int (CR + 0x90) : mword 64) 4
                   = mword_of_int (CR + 0x94)) by pcw.
    iEval (rewrite Hp94) in "Hpc".
    (* ---- +0x94 c.li a3,4 ---- *)
    iPoseProof (cnri_094 with "Ht") as "Hi94".
    iApply (wp_cli_s_sconf (mword_of_int (CR + 0x94)) Ra3 (mword_of_int 4 : mword 6)
              (mword_of_int 4 : mword 64) H7 (trap_res true + (av - 12))%nat false
              ltac:(nz) ltac:(rdok) ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi94").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (H8 := <[Regidx Ra3 := regval_into_reg (mword_of_int 4 : mword 64)]> H7).
    assert (Hp96 : add_vec_int (mword_of_int (CR + 0x94) : mword 64) 2
                   = mword_of_int (CR + 0x96)) by pcw.
    iEval (rewrite Hp96) in "Hpc".
    (* the register pins at [H8]: only a3/a4/s5 have moved *)
    assert (HthrH : forall r : mword 5, is_cs_idx r = true -> r <> Rs5 ->
              H8 !!! Regidx r = M !!! Regidx r).
    { intros r Hr N21.
      assert (N13 : r <> Ra3) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N14 : r <> Ra4) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /H8 upd_ne; [| congruence]. rewrite /H7 upd_ne; [| congruence].
      rewrite /H6 upd_ne; [| congruence]. rewrite /H5 upd_ne; [| congruence].
      rewrite /H4 upd_ne; [| congruence]. rewrite /H3 upd_ne; [| congruence].
      rewrite /H2 upd_ne; [| congruence]. rewrite /H1 upd_ne; [| congruence]. reflexivity. }
    assert (HH8s5 : H8 !!! Regidx Rs5 = (mword_of_int cbv : mword 64)).
    { rewrite /H8 upd_ne; [| reg_neq]. rewrite /H7; apply upd_eq. }
    assert (HH8a3 : H8 !!! Regidx Ra3 = (mword_of_int 4 : mword 64))
      by (rewrite /H8; apply upd_eq).
    assert (HH8sp : H8 !!! Regidx csp_rs1 = pa_stk sp0 12%nat)
      by (rewrite (HthrH csp_rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Hsp).
    assert (HH8s3 : H8 !!! Regidx Rs3 = (mword_of_int nc : mword 64))
      by (rewrite (HthrH Rs3 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Hs3).
    assert (HH8s7 : H8 !!! Regidx Rs7 = (mword_of_int n : mword 64))
      by (rewrite (HthrH Rs7 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Hs7).
    (* a5 is NOT callee-saved, so it does not travel through [HthrH]; nothing
       between +0x76 and +0x96 writes it, which is why the [^D] arm can still
       store the OLD [cons.r] out of it at +0xea. *)
    assert (HH8a5 : H8 !!! Regidx Ra5 = sign_extend' 64 rr).
    { rewrite /H8 upd_ne; [| reg_neq]. rewrite /H7 upd_ne; [| reg_neq].
      rewrite /H6 upd_ne; [| reg_neq]. rewrite /H5 upd_ne; [| reg_neq].
      rewrite /H4 upd_ne; [| reg_neq]. rewrite /H3 upd_ne; [| reg_neq].
      exact HH2a5. }
    iPoseProof (cnri_096 with "Ht") as "Hi96".
    destruct (Z.eqb cbv 4) eqn:HD.
    { (* ============ c == C('D'): the end-of-file break at +0xe2 ======== *)
      iApply (wp_beq_taken_s_sconf (mword_of_int (CR + 0x96)) (mword_of_int 76 : mword 13)
                Ra3 Rs5 H8 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(nz)
                ltac:(rgall; rewrite HH8s5 HH8a3 (w32_eq_moi cbv 4 ltac:(lia) ltac:(lia)); exact HD)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi96").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hje2 : add_vec (mword_of_int (CR + 0x96) : mword 64)
                       (sign_extend' 64 (mword_of_int 76 : mword 13))
                     = mword_of_int (CR + 0xe2)) by pcw.
      iEval (rewrite Hje2) in "Hpc".
      (* ---- +0xe2 bgeu s3,s7 : was anything copied yet? ---- *)
      iPoseProof (cnri_0e2 with "Ht") as "Hie2".
      destruct (Z.geb nc n) eqn:HG.
      { (* nc >= n: nothing copied, so no push-back.  -> +0xf6 ---- *)
        iApply (wp_bgeu_taken_s_sconf (mword_of_int (CR + 0xe2)) (mword_of_int 20 : mword 13)
                  Rs7 Rs3 H8 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(nz)
                  ltac:(rgall; rewrite HH8s3 HH8s7 (w32_bgeu_moi nc n ltac:(lia) ltac:(lia)); exact HG)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hie2").
        iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        assert (Hjf6 : add_vec (mword_of_int (CR + 0xe2) : mword 64)
                         (sign_extend' 64 (mword_of_int 20 : mword 13))
                       = mword_of_int (CR + 0xf6)) by pcw.
        iEval (rewrite Hjf6) in "Hpc".
        (* ---- +0xf6 c.ldsp s5,40(sp) ; +0xf8 c.j -> +0xfc ---- *)
        iPoseProof (cnri_0f6 with "Ht") as "Hif6".
        iApply (wp_cldsp_s_sconf (mword_of_int (CR + 0xf6)) (mword_of_int 5 : mword 6) Rs5
                  H8 (trap_res true + (av - 12))%nat (m0 !!! Regidx Rs5) false
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hif6 [Hsl7]").
        { iEval (rewrite HH8sp cr_b7). iExact "Hsl7". }
        iApply wp_next_off_intro. iIntros "Hcg Hpc Hsl7". rgall.
        iEval (rewrite HH8sp cr_b7) in "Hsl7".
        set (H9 := <[Regidx Rs5 := regval_into_reg (m0 !!! Regidx Rs5)]> H8).
        assert (Hpf8 : add_vec_int (mword_of_int (CR + 0xf6) : mword 64) 2
                       = mword_of_int (CR + 0xf8)) by pcw.
        iEval (rewrite Hpf8) in "Hpc".
        iPoseProof (cnri_0f8 with "Ht") as "Hif8".
        iApply (wp_cj_s_sconf (mword_of_int (CR + 0xf8))
                  (sign_extend' 21 (concat_vec (mword_of_int 2 : mword 11) ('b"0")))
                  H9 (trap_res true + (av - 12))%nat false
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hif8").
        iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc". rgall.
        assert (Hjfc : add_vec (mword_of_int (CR + 0xf8) : mword 64)
                         (sign_extend' 64 (sign_extend' 21
                            (concat_vec (mword_of_int 2 : mword 11) ('b"0"))))
                       = mword_of_int (CR + 0xfc)) by pcw.
        iEval (rewrite Hjfc) in "Hpc".
        iDestruct "EX" as "[HRETX _]".
        iSpecialize ("HRETX" $! CIDv with "[%]"); [wp_next_chain|].
        iApply ("HRETX" $! H9 P' nc with "[%] [%] [%] [%] [%] [%]
                  Hcg Hpc Hcnt Hpay Hlocked [Hrc Hwc Hec Hdat] Hpriv [Hsl7 Hq10 Hq11 Hq12]").
        - rewrite /H9 upd_ne; [| reg_neq]. exact HH8sp.
        - rewrite /H9 upd_ne; [| reg_neq]. exact HH8s3.
        - rewrite /H9 upd_ne; [| reg_neq]. exact HH8s7.
        - unfold cr_cs_hi. split_and!.
          + rewrite /H9 upd_eq. reflexivity.
          + rewrite /H9 upd_ne; [| reg_neq].
            rewrite (HthrH Rs8 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hcs8.
          + rewrite /H9 upd_ne; [| reg_neq].
            rewrite (HthrH Rs9 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hcs9.
          + rewrite /H9 upd_ne; [| reg_neq].
            rewrite (HthrH Rs10 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hcs10.
          + rewrite /H9 upd_ne; [| reg_neq].
            rewrite (HthrH Rs11 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hcs11.
        - lia.
        - exact Hext.
        - iExists (add_vec rr (mword_of_int 1 : mword 32)), ww, ee, bs.
          iFrame "Hrc Hwc Hec Hdat". iPureIntro. exact Hlen.
        - rewrite /cr_rest. iSplitL "Hsl7"; [by iExists _|]. iFrame "Hq10 Hq11 Hq12". }
      (* ---- nc < n: push cons.r back at +0xe6 ---- *)
      iApply (wp_bgeu_fall_s_sconf (mword_of_int (CR + 0xe2)) (mword_of_int 20 : mword 13)
                Rs7 Rs3 H8 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(nz)
                ltac:(rgall; rewrite HH8s3 HH8s7 (w32_bgeu_moi nc n ltac:(lia) ltac:(lia)); exact HG)
                with "Hcg Hpc Hie2").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hpe6 : add_vec_int (mword_of_int (CR + 0xe2) : mword 64) 4
                     = mword_of_int (CR + 0xe6)) by pcw.
      iEval (rewrite Hpe6) in "Hpc".
      (* +0xe6 auipc a4,0x12 ; +0xea sw a5,234(a4) : cons.r := the OLD r *)
      iPoseProof (cnri_0e6 with "Ht") as "Hie6".
      iApply (wp_auipc_s_sconf (mword_of_int (CR + 0xe6)) Ra4 (mword_of_int 18 : mword 20)
                H8 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hie6").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      set (E1 := <[Regidx Ra4 := regval_into_reg
          (add_vec (mword_of_int (CR + 0xe6) : mword 64)
             (auipc_off (mword_of_int 18 : mword 20)))]> H8).
      assert (Hpea : add_vec_int (mword_of_int (CR + 0xe6) : mword 64) 4
                     = mword_of_int (CR + 0xea)) by pcw.
      iEval (rewrite Hpea) in "Hpc".
      assert (HE1ra : add_vec (E1 !!! Regidx Ra4)
                        (sign_extend' 64 (mword_of_int 266 : mword 12)) = a_cons_r).
      { rewrite /E1 upd_eq /a_cons_r /coff_of /a_cons. apply bv_eq; vm_compute; reflexivity. }
      assert (HE1a5 : E1 !!! Regidx Ra5 = sign_extend' 64 rr)
        by (rewrite /E1 upd_ne; [exact HH8a5 | reg_neq]).
      iPoseProof (cnri_0ea with "Ht") as "Hiea".
      iApply (wp_sw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CR + 0xea)) Ra5 Ra4 (mword_of_int 266 : mword 12)
                E1 (trap_res true + (av - 12))%nat (add_vec rr (mword_of_int 1 : mword 32)) false
                with "Hcg Hpc Hiea [Hrc]").
      { rgall. iEval (rewrite HE1ra). iExact "Hrc". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hrc". rgall.
      iEval (rewrite HE1ra HE1a5 trunc32_sext) in "Hrc".
      assert (Hpee : add_vec_int (mword_of_int (CR + 0xea) : mword 64) 4
                     = mword_of_int (CR + 0xee)) by pcw.
      iEval (rewrite Hpee) in "Hpc".
      assert (HE1sp : E1 !!! Regidx csp_rs1 = pa_stk sp0 12%nat)
        by (rewrite /E1 upd_ne; [exact HH8sp | reg_neq]).
      (* ---- +0xee c.ldsp s5,40(sp) ; +0xf0 c.j -> +0xfc ---- *)
      iPoseProof (cnri_0ee with "Ht") as "Hiee".
      iApply (wp_cldsp_s_sconf (mword_of_int (CR + 0xee)) (mword_of_int 5 : mword 6) Rs5
                E1 (trap_res true + (av - 12))%nat (m0 !!! Regidx Rs5) false
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hiee [Hsl7]").
      { iEval (rewrite HE1sp cr_b7). iExact "Hsl7". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hsl7". rgall.
      iEval (rewrite HE1sp cr_b7) in "Hsl7".
      set (E2 := <[Regidx Rs5 := regval_into_reg (m0 !!! Regidx Rs5)]> E1).
      assert (Hpf0 : add_vec_int (mword_of_int (CR + 0xee) : mword 64) 2
                     = mword_of_int (CR + 0xf0)) by pcw.
      iEval (rewrite Hpf0) in "Hpc".
      iPoseProof (cnri_0f0 with "Ht") as "Hif0".
      iApply (wp_cj_s_sconf (mword_of_int (CR + 0xf0))
                (sign_extend' 21 (concat_vec (mword_of_int 6 : mword 11) ('b"0")))
                E2 (trap_res true + (av - 12))%nat false
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hif0").
      iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc". rgall.
      assert (Hjfc2 : add_vec (mword_of_int (CR + 0xf0) : mword 64)
                        (sign_extend' 64 (sign_extend' 21
                           (concat_vec (mword_of_int 6 : mword 11) ('b"0"))))
                      = mword_of_int (CR + 0xfc)) by pcw.
      iEval (rewrite Hjfc2) in "Hpc".
      assert (HthrE : forall r : mword 5, is_cs_idx r = true -> r <> Rs5 ->
                E2 !!! Regidx r = M !!! Regidx r).
      { intros r Hr N21.
        assert (N14 : r <> Ra4) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /E2 upd_ne; [| congruence]. rewrite /E1 upd_ne; [| congruence].
        apply HthrH; assumption. }
      iDestruct "EX" as "[HRETX _]".
      iSpecialize ("HRETX" $! CIDv with "[%]"); [wp_next_chain|].
      iApply ("HRETX" $! E2 P' nc with "[%] [%] [%] [%] [%] [%]
                Hcg Hpc Hcnt Hpay Hlocked [Hrc Hwc Hec Hdat] Hpriv [Hsl7 Hq10 Hq11 Hq12]").
      - rewrite (HthrE csp_rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hsp.
      - rewrite (HthrE Rs3 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hs3.
      - rewrite (HthrE Rs7 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hs7.
      - unfold cr_cs_hi. split_and!.
        + rewrite /E2 upd_eq. reflexivity.
        + rewrite (HthrE Rs8 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hcs8.
        + rewrite (HthrE Rs9 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hcs9.
        + rewrite (HthrE Rs10 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hcs10.
        + rewrite (HthrE Rs11 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hcs11.
      - lia.
      - exact Hext.
      - iExists rr, ww, ee, bs. iFrame "Hrc Hwc Hec Hdat". iPureIntro. exact Hlen.
      - rewrite /cr_rest. iSplitL "Hsl7"; [by iExists _|]. iFrame "Hq10 Hq11 Hq12". }
    (* ================== c <> C('D'): copy the byte out ================= *)
    iApply (wp_beq_fall_s_sconf (mword_of_int (CR + 0x96)) (mword_of_int 76 : mword 13)
              Ra3 Rs5 H8 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HH8s5 HH8a3 (w32_eq_moi cbv 4 ltac:(lia) ltac:(lia)); exact HD)
              with "Hcg Hpc Hi96").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp9a : add_vec_int (mword_of_int (CR + 0x96) : mword 64) 4
                   = mword_of_int (CR + 0x9a)) by pcw.
    iEval (rewrite Hp9a) in "Hpc".
    (* carve [cbuf] out of slot 11 for the length of the copy *)
    iDestruct "Hq11" as (w11) "Hc11".
    iDestruct (slot_bytes_own (KTR := KT1) with "Hc11") as "[%Hal11 Hby11]".
    iDestruct (bytes_own_acc (KTR := KT1) (DfracOwn 1) (pa_stk sp0 11%nat) 8 7 ltac:(lia) with "Hby11")
      as "[Hchb Hchback]".
    iDestruct "Hchb" as (chb0) "Hch".
    iEval (rewrite -(cr_cbufa sp0)) in "Hch".
    assert (HH8s0 : H8 !!! Regidx Rs0 = sp0)
      by (rewrite (HthrH Rs0 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact Hs0).
    assert (HH8a4 : H8 !!! Regidx Ra4 = zero_extend' 64 (db : mword 8)).
    { rewrite /H8 upd_ne; [| reg_neq]. rewrite /H7 upd_ne; [| reg_neq]. exact HH6a4. }
    (* ---- +0x9a sb a4,-81(s0) : cbuf := c ---- *)
    iPoseProof (cnri_09a with "Ht") as "Hi9a".
    iApply (wp_sb_s_sconf (mword_of_int (CR + 0x9a)) Ra4 Rs0 (mword_of_int 4015 : mword 12)
              H8 (trap_res true + (av - 12))%nat chb0 false with "Hcg Hpc Hi9a [Hch]").
    { rgall. iEval (rewrite HH8s0). iExact "Hch". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hch". rgall.
    iEval (rewrite HH8s0) in "Hch".
    assert (Hp9e : add_vec_int (mword_of_int (CR + 0x9a) : mword 64) 4
                   = mword_of_int (CR + 0x9e)) by pcw.
    iEval (rewrite Hp9e) in "Hpc".
    (* ---- +0x9e c.li a3,1 ---- *)
    iPoseProof (cnri_09e with "Ht") as "Hi9e".
    iApply (wp_cli_s_sconf (mword_of_int (CR + 0x9e)) Ra3 (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 64) H8 (trap_res true + (av - 12))%nat false
              ltac:(nz) ltac:(rdok) ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi9e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (G1 := <[Regidx Ra3 := regval_into_reg (mword_of_int 1 : mword 64)]> H8).
    assert (Hpa0 : add_vec_int (mword_of_int (CR + 0x9e) : mword 64) 2
                   = mword_of_int (CR + 0xa0)) by pcw.
    iEval (rewrite Hpa0) in "Hpc".
    (* ---- +0xa0 addi a2,s0,-81 : a2 := &cbuf ---- *)
    assert (HG1s0 : G1 !!! Regidx Rs0 = sp0)
      by (rewrite /G1 upd_ne; [exact HH8s0 | reg_neq]).
    iPoseProof (cnri_0a0 with "Ht") as "Hia0".
    iApply (wp_addi4_s_sconf (mword_of_int (CR + 0xa0)) Ra2 Rs0 (mword_of_int 4015 : mword 12)
              G1 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hia0").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite HG1s0) in "Hcg".
    set (G2 := <[Regidx Ra2 := regval_into_reg
        (add_vec sp0 (sign_extend' 64 (mword_of_int 4015 : mword 12)))]> G1).
    assert (Hpa4 : add_vec_int (mword_of_int (CR + 0xa0) : mword 64) 4
                   = mword_of_int (CR + 0xa4)) by pcw.
    iEval (rewrite Hpa4) in "Hpc".
    (* ---- +0xa4 c.mv a1,s4 ; +0xa6 c.mv a0,s6 ---- *)
    assert (HG2s4 : G2 !!! Regidx Rs4 = cur).
    { rewrite /G2 upd_ne; [| reg_neq]. rewrite /G1 upd_ne; [| reg_neq].
      rewrite (HthrH Rs4 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hs4. }
    iPoseProof (cnri_0a4 with "Ht") as "Hia4".
    iApply (wp_cmv_s_sconf (mword_of_int (CR + 0xa4)) Ra1 Rs4 G2
              (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hia4").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite HG2s4 w32_zero_add) in "Hcg".
    set (G3 := <[Regidx Ra1 := regval_into_reg cur]> G2).
    assert (Hpa6 : add_vec_int (mword_of_int (CR + 0xa4) : mword 64) 2
                   = mword_of_int (CR + 0xa6)) by pcw.
    iEval (rewrite Hpa6) in "Hpc".
    assert (HG3s6 : G3 !!! Regidx Rs6 = (mword_of_int 1 : mword 64)).
    { rewrite /G3 upd_ne; [| reg_neq]. rewrite /G2 upd_ne; [| reg_neq].
      rewrite /G1 upd_ne; [| reg_neq].
      rewrite (HthrH Rs6 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hs6. }
    iPoseProof (cnri_0a6 with "Ht") as "Hia6".
    iApply (wp_cmv_s_sconf (mword_of_int (CR + 0xa6)) Ra0 Rs6 G3
              (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hia6").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite HG3s6 w32_zero_add) in "Hcg".
    set (G4 := <[Regidx Ra0 := regval_into_reg (mword_of_int 1 : mword 64)]> G3).
    assert (Hpa8 : add_vec_int (mword_of_int (CR + 0xa6) : mword 64) 2
                   = mword_of_int (CR + 0xa8)) by pcw.
    iEval (rewrite Hpa8) in "Hpc".
    (* ---- +0xa8 jal either_copyout ---- *)
    iPoseProof (cnri_0a8 with "Ht") as "Hia8".
    iApply (wp_jal_s_sconf (mword_of_int (CR + 0xa8)) Rra (mword_of_int 8272 : mword 21)
              G4 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hia8").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (G5 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CR + 0xa8) : mword 64) 4)]> G4).
    assert (Hjeco : add_vec (mword_of_int (CR + 0xa8) : mword 64)
                      (sign_extend' 64 (mword_of_int 8272 : mword 21))
                    = mword_of_int KernelSyms.either_copyout) by pcw.
    iEval (rewrite Hjeco) in "Hpc".
    assert (HG5a0 : G5 !!! Regidx Ra0 = (mword_of_int 1 : mword 64)).
    { rewrite /G5 upd_ne; [| reg_neq]. rewrite /G4; apply upd_eq. }
    assert (HG5a1 : G5 !!! Regidx Ra1 = cur).
    { rewrite /G5 upd_ne; [| reg_neq]. rewrite /G4 upd_ne; [| reg_neq].
      rewrite /G3; apply upd_eq. }
    assert (HG5a2 : G5 !!! Regidx Ra2
                    = add_vec sp0 (sign_extend' 64 (mword_of_int 4015 : mword 12))).
    { rewrite /G5 upd_ne; [| reg_neq]. rewrite /G4 upd_ne; [| reg_neq].
      rewrite /G3 upd_ne; [| reg_neq]. rewrite /G2; apply upd_eq. }
    assert (HG5a3 : G5 !!! Regidx Ra3 = (mword_of_int (Z.of_nat 1%nat) : mword 64)).
    { rewrite /G5 upd_ne; [| reg_neq]. rewrite /G4 upd_ne; [| reg_neq].
      rewrite /G3 upd_ne; [| reg_neq]. rewrite /G2 upd_ne; [| reg_neq].
      rewrite /G1 upd_eq. reflexivity. }
    assert (HG5ra : G5 !!! Regidx Rra = add_vec_int (mword_of_int (CR + 0xa8) : mword 64) 4)
      by (rewrite /G5; apply upd_eq).
    assert (Hstk : (either_copyout_stack <= trap_res true + (av - 12))%nat).
    { assert (trap_res true = 90%nat) as -> by reflexivity.
      lia. }
    iApply (EitherCopyout.wp_either_copyout_sconf KT1 KT1 γa γf G5
              (trap_res true + (av - 12))%nat 1%nat true (proc_addr jp) pid
              (upd_upt V P') true 1%nat (fun _ => trunc8 (H8 !!! Regidx Ra4))
              (fun _ => chb0) false ({["cons"]} ∪ lks)
              Hstk ltac:(rewrite HG5a0; vm_compute; reflexivity) HG5a3
              ltac:(vm_compute; reflexivity) cr_lvl1
              with "Hcg Hcnt Ht Hpc Henv [Hch] [Hpriv]").
    all: try lkbelow.
    { iEval (rewrite HG5a2). cbn [seq]. rewrite big_sepL_singleton pa_add_0.
      iExact "Hch". }
    { iExact "Hpriv". }
    iApply wp_next_off_intro. iIntros (mrc) "%Hcsrc Hcg Hcnt Hpc Hbuf Hpost". rgall.
    iEval (rewrite HG5ra) in "Hpc".
    assert (Hpac : ret_pc (add_vec_int (mword_of_int (CR + 0xa8) : mword 64) 4)
                   = (mword_of_int (CR + 0xac) : mword 64)) by pcw.
    iEval (rewrite Hpac) in "Hpc".
    iEval (rewrite HG5a2; cbn [seq]; rewrite big_sepL_singleton pa_add_0) in "Hbuf".
    rewrite /either_copyout_post.
    iDestruct "Hpost" as "[%Hret Hpp]".
    iDestruct "Hpp" as (P'') "[%Hext2 Hpriv]".
    assert (Hextc : uptd_ext (pv_upt V) P'') by exact (uptd_ext_trans _ P' _ Hext Hext2).
    assert (HthrG : forall r : mword 5, is_cs_idx r = true -> r <> Rs5 ->
              mrc !!! Regidx r = M !!! Regidx r).
    { intros r Hr N21.
      assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> Ra0) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N11 : r <> Ra1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N12 : r <> Ra2) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N13 : r <> Ra3) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite (callee_saved_lookup Hcsrc r Hr).
      rewrite /G5 upd_ne; [| congruence]. rewrite /G4 upd_ne; [| congruence].
      rewrite /G3 upd_ne; [| congruence]. rewrite /G2 upd_ne; [| congruence].
      rewrite /G1 upd_ne; [| congruence]. apply HthrH; assumption. }
    assert (Hmrcs5 : mrc !!! Regidx Rs5 = (mword_of_int cbv : mword 64))
      by (rewrite (callee_saved_lookup Hcsrc Rs5 ltac:(vm_compute; reflexivity));
          rewrite /G5 upd_ne; [| reg_neq]; rewrite /G4 upd_ne; [| reg_neq];
          rewrite /G3 upd_ne; [| reg_neq]; rewrite /G2 upd_ne; [| reg_neq];
          rewrite /G1 upd_ne; [| reg_neq]; exact HH8s5).
    (* ---- +0xac c.li a5,-1 ; +0xae beq a0,a5 ---- *)
    iPoseProof (cnri_0ac with "Ht") as "Hiac".
    iApply (wp_cli_s_sconf (mword_of_int (CR + 0xac)) Ra5 (mword_of_int 63 : mword 6)
              (mword_of_int (-1) : mword 64) mrc (trap_res true + (av - 12))%nat false
              ltac:(nz) ltac:(rdok) ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hiac").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (G6 := <[Regidx Ra5 := regval_into_reg (mword_of_int (-1) : mword 64)]> mrc).
    assert (Hpae : add_vec_int (mword_of_int (CR + 0xac) : mword 64) 2
                   = mword_of_int (CR + 0xae)) by pcw.
    iEval (rewrite Hpae) in "Hpc".
    assert (HG6a5 : G6 !!! Regidx Ra5 = (mword_of_int (-1) : mword 64))
      by (rewrite /G6; apply upd_eq).
    assert (HG6a0 : G6 !!! Regidx Ra0 = mrc !!! Regidx Ra0)
      by (rewrite /G6 upd_ne; [reflexivity | reg_neq]).
    assert (HG6sp : G6 !!! Regidx csp_rs1 = pa_stk sp0 12%nat).
    { rewrite /G6 upd_ne; [| reg_neq].
      rewrite (HthrG csp_rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hsp. }
    assert (HG6s5 : G6 !!! Regidx Rs5 = (mword_of_int cbv : mword 64))
      by (rewrite /G6 upd_ne; [exact Hmrcs5 | reg_neq]).
    (* give the [cbuf] byte back to slot 11 -- every exit below needs the
       slot whole again *)
    iAssert (∃ w : mword 64, pa_stk sp0 11%nat ↦₈[KT1] w)%I with "[Hbuf Hchback]" as "Hq11".
    { iDestruct ("Hchback" $! (trunc8 (H8 !!! Regidx Ra4)) with "[Hbuf]") as "Hby11".
      { iEval (rewrite (cr_cbufa sp0)) in "Hbuf". iExact "Hbuf". }
      iApply (bytes_own_slot (KTR := KT1) (pa_stk sp0 11%nat) Hal11 with "Hby11"). }
    iPoseProof (cnri_0ae with "Ht") as "Hiae".
    destruct Hret as [Hr0 | Hrm1].
    { (* ---- either_copyout SUCCEEDED: bump the cursor and the count ---- *)
      iApply (wp_beq_fall_s_sconf (mword_of_int (CR + 0xae)) (mword_of_int 76 : mword 13)
                Ra5 Ra0 G6 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(nz)
                ltac:(rgall; rewrite HG6a5 HG6a0 Hr0; vm_compute; reflexivity)
                with "Hcg Hpc Hiae").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hpb2 : add_vec_int (mword_of_int (CR + 0xae) : mword 64) 4
                     = mword_of_int (CR + 0xb2)) by pcw.
      iEval (rewrite Hpb2) in "Hpc".
      (* +0xb2 c.addi s4,s4,1 : the user cursor *)
      assert (HG6s4 : G6 !!! Regidx Rs4 = cur).
      { rewrite /G6 upd_ne; [| reg_neq].
        rewrite (HthrG Rs4 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hs4. }
      iPoseProof (cnri_0b2 with "Ht") as "Hib2".
      iApply (wp_caddi_s_sconf (mword_of_int (CR + 0xb2)) Rs4 (mword_of_int 1 : mword 6)
                G6 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hib2").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      iEval (rewrite HG6s4) in "Hcg".
      set (G7 := <[Regidx Rs4 := regval_into_reg
          (add_vec cur (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> G6).
      assert (Hpb4 : add_vec_int (mword_of_int (CR + 0xb2) : mword 64) 2
                     = mword_of_int (CR + 0xb4)) by pcw.
      iEval (rewrite Hpb4) in "Hpc".
      (* +0xb4 c.addiw s3,s3,-1 : --n *)
      assert (HG7s3 : G7 !!! Regidx Rs3 = (mword_of_int nc : mword 64)).
      { rewrite /G7 upd_ne; [| reg_neq]. rewrite /G6 upd_ne; [| reg_neq].
        rewrite (HthrG Rs3 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hs3. }
      assert (Hdec : sign_extend' 64 (subrange_vec_dec
                 (add_vec (mword_of_int nc : mword 64)
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0)
               = (mword_of_int (nc - 1) : mword 64)).
      { replace (nc - 1)%Z with (nc + (-1))%Z by lia.
        apply (w32_caddiw_moi nc (-1) (mword_of_int 63 : mword 6)); [pcw | lia]. }
      iPoseProof (cnri_0b4 with "Ht") as "Hib4".
      iApply (wp_caddiw_s_sconf (mword_of_int (CR + 0xb4)) Rs3 (mword_of_int 63 : mword 6)
                G7 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hib4").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      iEval (rewrite HG7s3 Hdec) in "Hcg".
      set (G8 := <[Regidx Rs3 := regval_into_reg (mword_of_int (nc - 1) : mword 64)]> G7).
      assert (Hpb6 : add_vec_int (mword_of_int (CR + 0xb4) : mword 64) 2
                     = mword_of_int (CR + 0xb6)) by pcw.
      iEval (rewrite Hpb6) in "Hpc".
      (* +0xb6 c.li a5,10 ; +0xb8 beq s5,a5 *)
      iPoseProof (cnri_0b6 with "Ht") as "Hib6".
      iApply (wp_cli_s_sconf (mword_of_int (CR + 0xb6)) Ra5 (mword_of_int 10 : mword 6)
                (mword_of_int 10 : mword 64) G8 (trap_res true + (av - 12))%nat false
                ltac:(nz) ltac:(rdok) ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hib6").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      set (G9 := <[Regidx Ra5 := regval_into_reg (mword_of_int 10 : mword 64)]> G8).
      assert (Hpb8 : add_vec_int (mword_of_int (CR + 0xb6) : mword 64) 2
                     = mword_of_int (CR + 0xb8)) by pcw.
      iEval (rewrite Hpb8) in "Hpc".
      assert (HthrG9 : forall r : mword 5, is_cs_idx r = true -> r <> Rs5 -> r <> Rs3 -> r <> Rs4 ->
                G9 !!! Regidx r = M !!! Regidx r).
      { intros r Hr N21 N19 N20.
        assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /G9 upd_ne; [| congruence]. rewrite /G8 upd_ne; [| congruence].
        rewrite /G7 upd_ne; [| congruence]. rewrite /G6 upd_ne; [| congruence].
        apply HthrG; assumption. }
      assert (HG9s5 : G9 !!! Regidx Rs5 = (mword_of_int cbv : mword 64)).
      { rewrite /G9 upd_ne; [| reg_neq]. rewrite /G8 upd_ne; [| reg_neq].
        rewrite /G7 upd_ne; [| reg_neq]. exact HG6s5. }
      assert (HG9a5 : G9 !!! Regidx Ra5 = (mword_of_int 10 : mword 64))
        by (rewrite /G9; apply upd_eq).
      assert (HG9sp : G9 !!! Regidx csp_rs1 = pa_stk sp0 12%nat)
        by (rewrite (HthrG9 csp_rs1 ltac:(vm_compute; reflexivity)
                       ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Hsp).
      assert (HG9s3 : G9 !!! Regidx Rs3 = (mword_of_int (nc - 1) : mword 64)).
      { rewrite /G9 upd_ne; [| reg_neq]. rewrite /G8; apply upd_eq. }
      assert (HG9s4 : G9 !!! Regidx Rs4
                      = add_vec cur (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))).
      { rewrite /G9 upd_ne; [| reg_neq]. rewrite /G8 upd_ne; [| reg_neq].
        rewrite /G7; apply upd_eq. }
      assert (HG9s7 : G9 !!! Regidx Rs7 = (mword_of_int n : mword 64))
        by (rewrite (HthrG9 Rs7 ltac:(vm_compute; reflexivity)
                       ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact Hs7).
      iAssert (cons_res) with "[Hrc Hwc Hec Hdat]" as "Hres".
      { iExists (add_vec rr (mword_of_int 1 : mword 32)), ww, ee, bs.
        iFrame "Hrc Hwc Hec Hdat". iPureIntro. exact Hlen. }
      iPoseProof (cnri_0b8 with "Ht") as "Hib8".
      destruct (Z.eqb cbv 10) eqn:HNL.
      { (* ---- c == '\n': break out at +0x10e ---- *)
        iApply (wp_beq_taken_s_sconf (mword_of_int (CR + 0xb8)) (mword_of_int 86 : mword 13)
                  Ra5 Rs5 G9 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(nz)
                  ltac:(rgall; rewrite HG9s5 HG9a5 (w32_eq_moi cbv 10 ltac:(lia) ltac:(lia)); exact HNL)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hib8").
        iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
        assert (Hj10e : add_vec (mword_of_int (CR + 0xb8) : mword 64)
                          (sign_extend' 64 (mword_of_int 86 : mword 13))
                        = mword_of_int (CR + 0x10e)) by pcw.
        iEval (rewrite Hj10e) in "Hpc".
        (* +0x10e c.ldsp s5,40(sp) ; +0x110 c.j -> +0xfc *)
        iPoseProof (cnri_10e with "Ht") as "Hi10e".
        iApply (wp_cldsp_s_sconf (mword_of_int (CR + 0x10e)) (mword_of_int 5 : mword 6) Rs5
                  G9 (trap_res true + (av - 12))%nat (m0 !!! Regidx Rs5) false
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi10e [Hsl7]").
        { iEval (rewrite HG9sp cr_b7). iExact "Hsl7". }
        iApply wp_next_off_intro. iIntros "Hcg Hpc Hsl7". rgall.
        iEval (rewrite HG9sp cr_b7) in "Hsl7".
        set (G10 := <[Regidx Rs5 := regval_into_reg (m0 !!! Regidx Rs5)]> G9).
        assert (Hp110 : add_vec_int (mword_of_int (CR + 0x10e) : mword 64) 2
                        = mword_of_int (CR + 0x110)) by pcw.
        iEval (rewrite Hp110) in "Hpc".
        iPoseProof (cnri_110 with "Ht") as "Hi110".
        iApply (wp_cj_s_sconf (mword_of_int (CR + 0x110))
                  (sign_extend' 21 (concat_vec (mword_of_int 2038 : mword 11) ('b"0")))
                  G10 (trap_res true + (av - 12))%nat false
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi110").
        iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc". rgall.
        assert (Hjfc3 : add_vec (mword_of_int (CR + 0x110) : mword 64)
                          (sign_extend' 64 (sign_extend' 21
                             (concat_vec (mword_of_int 2038 : mword 11) ('b"0"))))
                        = mword_of_int (CR + 0xfc)) by pcw.
        iEval (rewrite Hjfc3) in "Hpc".
        iDestruct "EX" as "[HRETX _]".
        iSpecialize ("HRETX" $! CIDv with "[%]"); [wp_next_chain|].
        iApply ("HRETX" $! G10 P'' (nc - 1) with "[%] [%] [%] [%] [%] [%]
                  Hcg Hpc Hcnt Hpay Hlocked Hres Hpriv [Hsl7 Hq10 Hq11 Hq12]").
        - rewrite /G10 upd_ne; [| reg_neq]. exact HG9sp.
        - rewrite /G10 upd_ne; [| reg_neq]. exact HG9s3.
        - rewrite /G10 upd_ne; [| reg_neq]. exact HG9s7.
        - unfold cr_cs_hi. split_and!.
          + rewrite /G10 upd_eq. reflexivity.
          + rewrite /G10 upd_ne; [| reg_neq].
            rewrite (HthrG9 Rs8 ltac:(vm_compute; reflexivity)
                       ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Hcs8.
          + rewrite /G10 upd_ne; [| reg_neq].
            rewrite (HthrG9 Rs9 ltac:(vm_compute; reflexivity)
                       ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Hcs9.
          + rewrite /G10 upd_ne; [| reg_neq].
            rewrite (HthrG9 Rs10 ltac:(vm_compute; reflexivity)
                       ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Hcs10.
          + rewrite /G10 upd_ne; [| reg_neq].
            rewrite (HthrG9 Rs11 ltac:(vm_compute; reflexivity)
                       ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Hcs11.
        - lia.
        - exact Hextc.
        - rewrite /cr_rest. iSplitL "Hsl7"; [by iExists _|]. iFrame "Hq10 Hq11 Hq12". }
      (* ---- c is an ordinary byte: the BACK EDGE at +0xbe ---- *)
      iApply (wp_beq_fall_s_sconf (mword_of_int (CR + 0xb8)) (mword_of_int 86 : mword 13)
                Ra5 Rs5 G9 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(nz)
                ltac:(rgall; rewrite HG9s5 HG9a5 (w32_eq_moi cbv 10 ltac:(lia) ltac:(lia)); exact HNL)
                with "Hcg Hpc Hib8").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hpbc : add_vec_int (mword_of_int (CR + 0xb8) : mword 64) 4
                     = mword_of_int (CR + 0xbc)) by pcw.
      iEval (rewrite Hpbc) in "Hpc".
      iPoseProof (cnri_0bc with "Ht") as "Hibc".
      iApply (wp_cldsp_s_sconf (mword_of_int (CR + 0xbc)) (mword_of_int 5 : mword 6) Rs5
                G9 (trap_res true + (av - 12))%nat (m0 !!! Regidx Rs5) false
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hibc [Hsl7]").
      { iEval (rewrite HG9sp cr_b7). iExact "Hsl7". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hsl7". rgall.
      iEval (rewrite HG9sp cr_b7) in "Hsl7".
      set (G10 := <[Regidx Rs5 := regval_into_reg (m0 !!! Regidx Rs5)]> G9).
      assert (Hpbe : add_vec_int (mword_of_int (CR + 0xbc) : mword 64) 2
                     = mword_of_int (CR + 0xbe)) by pcw.
      iEval (rewrite Hpbe) in "Hpc".
      iPoseProof (cnri_0be with "Ht") as "Hibe".
      iApply (wp_cj_s_sconf (mword_of_int (CR + 0xbe))
                (sign_extend' 21 (concat_vec (mword_of_int 1981 : mword 11) ('b"0")))
                G10 (trap_res true + (av - 12))%nat false
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hibe").
      iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj38 : add_vec (mword_of_int (CR + 0xbe) : mword 64)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 1981 : mword 11) ('b"0"))))
                     = mword_of_int (CR + 0x38)) by pcw.
      iEval (rewrite Hj38) in "Hpc".
      iSpecialize ("HEAD" $! CIDv with "[%]"); [wp_next_chain|].
      iApply ("HEAD" $! G10 (nc - 1)
                (add_vec cur (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) P''
                with "[%] [%] [%] [%] [%] EX Hcg Hpc Hcnt Hpay Hlocked Hres Hpriv
                     [Hsl7 Hq10 Hq11 Hq12]").
      - unfold cr_regs. split_and!.
        + rewrite /G10 upd_ne; [| reg_neq]. exact HG9sp.
        + rewrite /G10 upd_ne; [| reg_neq].
          rewrite (HthrG9 Rs0 ltac:(vm_compute; reflexivity)
                     ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Hs0.
        + rewrite /G10 upd_ne; [| reg_neq].
          rewrite (HthrG9 Rs1 ltac:(vm_compute; reflexivity)
                     ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Hs1.
        + rewrite /G10 upd_ne; [| reg_neq].
          rewrite (HthrG9 Rs2 ltac:(vm_compute; reflexivity)
                     ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Hs2.
        + rewrite /G10 upd_ne; [| reg_neq]. exact HG9s3.
        + rewrite /G10 upd_ne; [| reg_neq]. exact HG9s4.
        + rewrite /G10 upd_ne; [| reg_neq].
          rewrite (HthrG9 Rs6 ltac:(vm_compute; reflexivity)
                     ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Hs6.
        + rewrite /G10 upd_ne; [| reg_neq]. exact HG9s7.
        + rewrite /G10 upd_ne; [| reg_neq].
          rewrite (HthrG9 Rs8 ltac:(vm_compute; reflexivity)
                     ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Hcs8.
        + rewrite /G10 upd_ne; [| reg_neq].
          rewrite (HthrG9 Rs9 ltac:(vm_compute; reflexivity)
                     ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Hcs9.
        + rewrite /G10 upd_ne; [| reg_neq].
          rewrite (HthrG9 Rs10 ltac:(vm_compute; reflexivity)
                     ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Hcs10.
        + rewrite /G10 upd_ne; [| reg_neq].
          rewrite (HthrG9 Rs11 ltac:(vm_compute; reflexivity)
                     ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact Hcs11.
      - rewrite /G10 upd_eq. reflexivity.
      - lia.
      - lia.
      - exact Hextc.
      - rewrite /cr_rest. iSplitL "Hsl7"; [by iExists _|]. iFrame "Hq10 Hq11 Hq12". }
    (* ---- either_copyout FAILED: break at +0xfa ---- *)
    iApply (wp_beq_taken_s_sconf (mword_of_int (CR + 0xae)) (mword_of_int 76 : mword 13)
              Ra5 Ra0 G6 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HG6a5 HG6a0 Hrm1; apply eq_vec_true_iff; reflexivity)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hiae").
    iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hjfa : add_vec (mword_of_int (CR + 0xae) : mword 64)
                     (sign_extend' 64 (mword_of_int 76 : mword 13))
                   = mword_of_int (CR + 0xfa)) by pcw.
    iEval (rewrite Hjfa) in "Hpc".
    iPoseProof (cnri_0fa with "Ht") as "Hifa".
    iApply (wp_cldsp_s_sconf (mword_of_int (CR + 0xfa)) (mword_of_int 5 : mword 6) Rs5
              G6 (trap_res true + (av - 12))%nat (m0 !!! Regidx Rs5) false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hifa [Hsl7]").
    { iEval (rewrite HG6sp cr_b7). iExact "Hsl7". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hsl7". rgall.
    iEval (rewrite HG6sp cr_b7) in "Hsl7".
    set (G7 := <[Regidx Rs5 := regval_into_reg (m0 !!! Regidx Rs5)]> G6).
    assert (Hpfc : add_vec_int (mword_of_int (CR + 0xfa) : mword 64) 2
                   = mword_of_int (CR + 0xfc)) by pcw.
    iEval (rewrite Hpfc) in "Hpc".
    iDestruct "EX" as "[HRETX _]".
    iSpecialize ("HRETX" $! CIDv with "[%]"); [wp_next_chain|].
    iApply ("HRETX" $! G7 P'' nc with "[%] [%] [%] [%] [%] [%]
              Hcg Hpc Hcnt Hpay Hlocked [Hrc Hwc Hec Hdat] Hpriv [Hsl7 Hq10 Hq11 Hq12]").
    - rewrite /G7 upd_ne; [| reg_neq]. exact HG6sp.
    - rewrite /G7 upd_ne; [| reg_neq]. rewrite /G6 upd_ne; [| reg_neq].
      rewrite (HthrG Rs3 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hs3.
    - rewrite /G7 upd_ne; [| reg_neq]. rewrite /G6 upd_ne; [| reg_neq].
      rewrite (HthrG Rs7 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hs7.
    - unfold cr_cs_hi. split_and!.
      + rewrite /G7 upd_eq. reflexivity.
      + rewrite /G7 upd_ne; [| reg_neq]. rewrite /G6 upd_ne; [| reg_neq].
        rewrite (HthrG Rs8 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hcs8.
      + rewrite /G7 upd_ne; [| reg_neq]. rewrite /G6 upd_ne; [| reg_neq].
        rewrite (HthrG Rs9 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hcs9.
      + rewrite /G7 upd_ne; [| reg_neq]. rewrite /G6 upd_ne; [| reg_neq].
        rewrite (HthrG Rs10 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hcs10.
      + rewrite /G7 upd_ne; [| reg_neq]. rewrite /G6 upd_ne; [| reg_neq].
        rewrite (HthrG Rs11 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact Hcs11.
    - lia.
    - exact Hextc.
    - iExists (add_vec rr (mword_of_int 1 : mword 32)), ww, ee, bs.
      iFrame "Hrc Hwc Hec Hdat". iPureIntro. exact Hlen.
    - rewrite /cr_rest. iSplitL "Hsl7"; [by iExists _|]. iFrame "Hq10 Hq11 Hq12".
  Qed.

  (* =================================================================== *)
  (*  [WAIT] (+0x48): the inner [while (cons.r == cons.w)] park.          *)
  (*                                                                      *)
  (*  UNBOUNDED -- nothing says how long a line takes to arrive -- so it   *)
  (*  is an iLoeb, not a fuel induction.  Its state is just the lock       *)
  (*  token, [cons_res] and the register pins: nothing accumulates across  *)
  (*  a park, which is why the IH needs no extra quantifier.               *)
  (* =================================================================== *)
  Definition cr_wait_prop `{CID0 : CpuId}
      (γc : gname) (jp : nat) (sp0 : mword 64) (m0 : regfile) (av : nat)
      (pid : mword 32) (V : pprivate) (n : Z) (fl : nat) (lks : gset string) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr jp) (fun (CIDw : CpuId) =>
       ∀ (M : regfile) (nc : Z) (cur : mword 64) (P' : uptd),
         ⌜ cr_regs M m0 sp0 nc cur n ⌝ -∗
         ⌜ M !!! Regidx Rs5 = m0 !!! Regidx Rs5 ⌝ -∗
         ⌜ (0 < nc)%Z /\ (0 <= n - nc <= Z.max 0 n)%Z /\ (Z.to_nat nc <= fl)%nat ⌝ -∗
         ⌜ uptd_ext (pv_upt V) P' ⌝ -∗
         cr_exits (CID0 := CID0) γc jp sp0 m0 av pid V n lks -∗
         sie_cap_gpr KT1 M (trap_res true + (av - 12))%nat false (proc_addr jp) -∗
         pc_is (mword_of_int (CR + 0x48)) -∗
         (* OUTER [lks], still holding "cons" (see [cr_retx_prop]'s note):
            the interior sleep_prepare/release/sleep/acquire round trip below
            drops to bare [lks] and climbs back to this before the IH or
            [HAVE] is re-entered. *)
         cpu_own 1%nat true (proc_addr jp) false ({["cons"]} ∪ lks) -∗
         arm_pay KT1 0%nat true (proc_addr jp) -∗
         locked γc cpu_id -∗
         cons_res -∗
         proc_priv_core (proc_addr jp) pid (upd_upt V P') -∗
         cr_rest sp0 -∗
         WP (Loop : expr riscv_lang)))%I.

  Lemma cr_mk_wait (γa γc γf : gname) (γs : list gname) (jp : nat) (γlp : gname)
      (sp0 : mword 64) (m0 : regfile)
      (av : nat) (pid : mword 32) (V : pprivate) (n : Z) (fl : nat) (lks : gset string) :
    (jp < NPROC)%nat ->
    γs !! jp = Some γlp ->
    (- 2 ^ 31 <= n < 2 ^ 31)%Z ->
    (consoleread_stack <= av)%nat ->
    locks_below lks "cons" ->
    kernel_text -∗ is_conslock γc -∗ kalloc_env γa None -∗
    procs_inv γs -∗
    □ cr_have_prop (CID0 := CID) γa γc γf jp sp0 m0 av pid V n fl lks -∗
    cr_wait_prop (CID0 := CID) γc jp sp0 m0 av pid V n fl lks.
  Proof.
    intros Hjp Hjl Hn31 Hav Hbelow.
    pose proof (locks_below_not_elem _ _ Hbelow) as Hfresh.
    iIntros "#Ht #Hlk #Henv #Hpinv #HAVE".
    rewrite /cr_wait_prop.
    iLöb as "IH".
    iIntros (CIDw Hsw M nc cur P') "%Hregs %Hs5 %Hnb %Hext EX Hcg Hpc Hcnt Hpay Hlocked Hres Hpriv Hrest".
    pose proof Hregs as Hregs'.
    destruct Hregs' as (Hsp & Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs6 & Hs7 & Hcs8 & Hcs9 & Hcs10 & Hcs11).
    destruct Hnb as (Hncpos & Hrng & Hfl).
    (* ---- +0x48 jal ra,myproc ---- *)
    iPoseProof (cnri_048 with "Ht") as "Hi48".
    iApply (wp_jal_s_sconf (mword_of_int (CR + 0x48)) Rra (mword_of_int 5914 : mword 21)
              M (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi48").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (W1 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CR + 0x48) : mword 64) 4)]> M).
    assert (Hjmp : add_vec (mword_of_int (CR + 0x48) : mword 64)
                     (sign_extend' 64 (mword_of_int 5914 : mword 21))
                   = mword_of_int KernelSyms.myproc) by pcw.
    iEval (rewrite Hjmp) in "Hpc".
    assert (HW1ra : W1 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CR + 0x48) : mword 64) 4)
      by (rewrite /W1; apply upd_eq).
    assert (HcsMW1 : callee_saved M W1)
      by (rewrite /W1; apply callee_saved_insert_r;
          [vm_compute; reflexivity | apply callee_saved_refl]).
    iApply (Myproc.wp_myproc_sconf W1 (trap_res true + (av - 12))%nat 1%nat true
              (proc_addr jp) false _ cr_lvl1
              ltac:(assert (trap_res true = 90%nat) as -> by reflexivity;
                    lia)
              with "Hcg Hcnt Ht Hpc").
    iApply wp_next_off_intro. iIntros (ms1 mmp) "%Hms1 Hcg Hcnt Hpc %Hmpf". rgall.
    destruct Hmpf as [Hcsmp Hmpa0].
    iEval (rewrite HW1ra) in "Hpc".
    assert (Hp4c : ret_pc (add_vec_int (mword_of_int (CR + 0x48) : mword 64) 4)
                   = (mword_of_int (CR + 0x4c) : mword 64)) by pcw.
    iEval (rewrite Hp4c) in "Hpc".
    (* ---- +0x4c jal ra,killed ---- *)
    iPoseProof (cnri_04c with "Ht") as "Hi4c".
    iApply (wp_jal_s_sconf (mword_of_int (CR + 0x4c)) Rra (mword_of_int 8056 : mword 21)
              mmp (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi4c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (W2 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CR + 0x4c) : mword 64) 4)]> mmp).
    assert (Hjkl : add_vec (mword_of_int (CR + 0x4c) : mword 64)
                     (sign_extend' 64 (mword_of_int 8056 : mword 21))
                   = mword_of_int KernelSyms.killed) by pcw.
    iEval (rewrite Hjkl) in "Hpc".
    assert (HW2a0 : W2 !!! Regidx Ra0 = proc_addr jp)
      by (rewrite /W2 upd_ne; [exact Hmpa0 | reg_neq]).
    assert (HW2ra : W2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CR + 0x4c) : mword 64) 4)
      by (rewrite /W2; apply upd_eq).
    assert (HcsMW2 : callee_saved M W2).
    { apply (callee_saved_trans M mmp W2 (callee_saved_trans M W1 mmp HcsMW1 Hcsmp)).
      rewrite /W2. apply callee_saved_insert_r;
        [vm_compute; reflexivity | apply callee_saved_refl]. }
    iApply (Killed.wp_killed_sconf γs jp γlp W2 (trap_res true + (av - 12))%nat 1%nat true
              (proc_addr jp) false ({["cons"]} ∪ lks) HW2a0 Hjp Hjl cr_lvl1
              ltac:(assert (trap_res true = 90%nat) as -> by reflexivity;
                    lia)
              ltac:(lkbelow)
              with "Hcg Hcnt Ht Hpc Hpinv").
    all: try lkbelow.
    iApply wp_next_off_intro. iIntros (mkl kl) "[%Hcskl %Hkla0] Hcg Hcnt Hpc". rgall.
    iEval (rewrite HW2ra) in "Hpc".
    assert (Hp50 : ret_pc (add_vec_int (mword_of_int (CR + 0x4c) : mword 64) 4)
                   = (mword_of_int (CR + 0x50) : mword 64)) by pcw.
    iEval (rewrite Hp50) in "Hpc".
    assert (HcsMk : callee_saved M mkl) by (apply (callee_saved_trans M W2 mkl HcsMW2 Hcskl)).
    assert (Hmksp : mkl !!! Regidx csp_rs1 = pa_stk sp0 12%nat)
      by (rewrite (callee_saved_lookup HcsMk csp_rs1 ltac:(vm_compute; reflexivity)); exact Hsp).
    assert (Hmks1 : mkl !!! Regidx Rs1 = a_cons)
      by (rewrite (callee_saved_lookup HcsMk Rs1 ltac:(vm_compute; reflexivity)); exact Hs1).
    assert (Hmks2 : mkl !!! Regidx Rs2 = a_cons_r)
      by (rewrite (callee_saved_lookup HcsMk Rs2 ltac:(vm_compute; reflexivity)); exact Hs2).
    (* ---- +0x50 c.bnez a0 : killed? ---- *)
    iPoseProof (cnri_050 with "Ht") as "Hi50".
    destruct (neq_vec (sign_extend' 64 kl : mword 64) (zero_reg : mword 64)) eqn:Hkz.
    { (* ======= KILLED: release and return -1 at +0xc0 ======= *)
      iApply (wp_cbnez_taken_s_sconf (mword_of_int (CR + 0x50)) (mword_of_int 56 : mword 8)
                (Cregidx (mword_of_int 2)) Ra0 mkl (trap_res true + (av - 12))%nat false
                ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgall; rewrite Hkla0; exact Hkz) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi50").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hjc0 : add_vec (mword_of_int (CR + 0x50) : mword 64)
                       (sign_extend' 64 (sign_extend' 13
                          (concat_vec (mword_of_int 56 : mword 8) ('b"0"))))
                     = mword_of_int (CR + 0xc0)) by pcw.
      iEval (rewrite Hjc0) in "Hpc".
      (* +0xc0 auipc a0,0x12 ; +0xc4 addi a0,a0,120 : a0 := &cons *)
      iPoseProof (cnri_0c0 with "Ht") as "Hic0".
      iApply (wp_auipc_s_sconf (mword_of_int (CR + 0xc0)) Ra0 (mword_of_int 18 : mword 20)
                mkl (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hic0").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      set (K1 := <[Regidx Ra0 := regval_into_reg
          (add_vec (mword_of_int (CR + 0xc0) : mword 64)
             (auipc_off (mword_of_int 18 : mword 20)))]> mkl).
      assert (Hpc4 : add_vec_int (mword_of_int (CR + 0xc0) : mword 64) 4
                     = mword_of_int (CR + 0xc4)) by pcw.
      iEval (rewrite Hpc4) in "Hpc".
      iPoseProof (cnri_0c4 with "Ht") as "Hic4".
      iApply (wp_addi4_s_sconf (mword_of_int (CR + 0xc4)) Ra0 Ra0 (mword_of_int 152 : mword 12)
                K1 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hic4").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      set (K2 := <[Regidx Ra0 := regval_into_reg
          (add_vec (K1 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 152 : mword 12)))]> K1).
      assert (HK2a0 : K2 !!! Regidx Ra0 = a_cons).
      { rewrite /K2 upd_eq /K1 upd_eq /a_cons. apply bv_eq; vm_compute; reflexivity. }
      assert (Hpc8 : add_vec_int (mword_of_int (CR + 0xc4) : mword 64) 4
                     = mword_of_int (CR + 0xc8)) by pcw.
      iEval (rewrite Hpc8) in "Hpc".
      (* +0xc8 jal ra,release *)
      iPoseProof (cnri_0c8 with "Ht") as "Hic8".
      iApply (wp_jal_s_sconf (mword_of_int (CR + 0xc8)) Rra (mword_of_int 2562 : mword 21)
                K2 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hic8").
      iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      set (K3 := <[Regidx Rra := regval_into_reg
          (add_vec_int (mword_of_int (CR + 0xc8) : mword 64) 4)]> K2).
      assert (Hjrl : add_vec (mword_of_int (CR + 0xc8) : mword 64)
                       (sign_extend' 64 (mword_of_int 2562 : mword 21))
                     = mword_of_int KernelSyms.release) by pcw.
      iEval (rewrite Hjrl) in "Hpc".
      assert (HK3a0 : K3 !!! Regidx Ra0 = a_cons)
        by (rewrite /K3 upd_ne; [exact HK2a0 | reg_neq]).
      assert (HK3ra : K3 !!! Regidx Rra
                      = add_vec_int (mword_of_int (CR + 0xc8) : mword 64) 4)
        by (rewrite /K3; apply upd_eq).
      assert (HK3lka : add_vec (K3 !!! Regidx Ra0)
                         (sign_extend' 64 (mword_of_int 0 : mword 12)) = a_cons).
      { rewrite HK3a0.
        replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
          by pcw.
        apply kv_addv_zero. }
      assert (HcsK3 : callee_saved mkl K3).
      { rewrite /K3 /K2 /K1.
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity | apply callee_saved_refl]. }
      iApply (Release.wp_release_sconf KT1 γc a_cons "cons"%string cons_res K3
                0%nat true (proc_addr jp) (av - 12)%nat ({["cons"]} ∪ lks) HK3lka
                ltac:(lia)
                with "Hcg Ht Hpc Hlk Hlocked Hres Hcnt Hpay").
      iIntros (CIDr Hsr mrl) "Hcg Hpc %Hcsrl Hcnt". rgall.
      assert (Hsetback : ({["cons"]} ∪ lks) ∖ {["cons"]} = lks)
      by (apply locks_add_del_below; lkbelow).
      iEval (rewrite Hsetback) in "Hcnt".
      iEval (rewrite HK3ra) in "Hpc".
      assert (Hpcc : ret_pc (add_vec_int (mword_of_int (CR + 0xc8) : mword 64) 4)
                     = (mword_of_int (CR + 0xcc) : mword 64)) by pcw.
      iEval (rewrite Hpcc) in "Hpc".
      assert (HcsMr : callee_saved M mrl).
      { apply (callee_saved_trans M mkl mrl HcsMk).
        apply (callee_saved_trans mkl K3 mrl HcsK3 Hcsrl). }
      (* +0xcc c.li a0,-1, then FALL into the epilogue at +0xce *)
      iPoseProof (cnri_0cc with "Ht") as "Hicc".
      iApply (wp_cli_s_sconf (mword_of_int (CR + 0xcc)) Ra0 (mword_of_int 63 : mword 6)
                (mword_of_int (-1) : mword 64) mrl (av - 12)%nat true
                ltac:(nz) ltac:(rdok) ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hicc").
      iIntros (CIDz Hsz) "Hcg Hpc". rgall.
      set (K4 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> mrl).
      assert (Hpce : add_vec_int (mword_of_int (CR + 0xcc) : mword 64) 2
                     = mword_of_int (CR + 0xce)) by pcw.
      iEval (rewrite Hpce) in "Hpc".
      iDestruct "EX" as "[_ HEPI]".
      iSpecialize ("HEPI" $! CIDz with "[%]"); [wp_next_chain|].
      iApply ("HEPI" $! K4 P' (-1)%Z with "[%] [%] [%] [%] [%] Hcg Hpc Hcnt Hpriv Hrest").
      - rewrite /K4 upd_ne; [| reg_neq].
        rewrite (callee_saved_lookup HcsMr csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp.
      - rewrite /K4 upd_eq. reflexivity.
      - unfold cr_cs_hi. split_and!;
          (rewrite /K4 upd_ne; [| reg_neq]);
          [ rewrite (callee_saved_lookup HcsMr Rs5 ltac:(vm_compute; reflexivity)); exact Hs5
          | rewrite (callee_saved_lookup HcsMr Rs8 ltac:(vm_compute; reflexivity)); exact Hcs8
          | rewrite (callee_saved_lookup HcsMr Rs9 ltac:(vm_compute; reflexivity)); exact Hcs9
          | rewrite (callee_saved_lookup HcsMr Rs10 ltac:(vm_compute; reflexivity)); exact Hcs10
          | rewrite (callee_saved_lookup HcsMr Rs11 ltac:(vm_compute; reflexivity)); exact Hcs11 ].
      - exact Hext.
      - split; [lia | pose proof (Z.le_max_l 0 n); lia]. }
    (* ======= NOT killed: sleep on &cons.r ======= *)
    iApply (wp_cbnez_fall_s_sconf (mword_of_int (CR + 0x50)) (mword_of_int 56 : mword 8)
              (Cregidx (mword_of_int 2)) Ra0 mkl (trap_res true + (av - 12))%nat false
              ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgall; rewrite Hkla0; exact Hkz) with "Hcg Hpc Hi50").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp52 : add_vec_int (mword_of_int (CR + 0x50) : mword 64) 2
                   = mword_of_int (CR + 0x52)) by pcw.
    iEval (rewrite Hp52) in "Hpc".
    (* ---- +0x52 c.mv a0,s2 ; +0x54 jal sleep_prepare ---- *)
    iPoseProof (cnri_052 with "Ht") as "Hi52".
    iApply (wp_cmv_s_sconf (mword_of_int (CR + 0x52)) Ra0 Rs2 mkl
              (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi52").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite Hmks2 w32_zero_add) in "Hcg".
    set (S1 := <[Regidx Ra0 := regval_into_reg a_cons_r]> mkl).
    assert (Hp54 : add_vec_int (mword_of_int (CR + 0x52) : mword 64) 2
                   = mword_of_int (CR + 0x54)) by pcw.
    iEval (rewrite Hp54) in "Hpc".
    iPoseProof (cnri_054 with "Ht") as "Hi54".
    iApply (wp_jal_s_sconf (mword_of_int (CR + 0x54)) Rra (mword_of_int 7448 : mword 21)
              S1 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi54").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (S2 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CR + 0x54) : mword 64) 4)]> S1).
    assert (Hjsp : add_vec (mword_of_int (CR + 0x54) : mword 64)
                     (sign_extend' 64 (mword_of_int 7448 : mword 21))
                   = mword_of_int KernelSyms.sleep_prepare) by pcw.
    iEval (rewrite Hjsp) in "Hpc".
    assert (HS2a0 : S2 !!! Regidx Ra0 = a_cons_r).
    { rewrite /S2 upd_ne; [| reg_neq]. rewrite /S1; apply upd_eq. }
    assert (HS2ra : S2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CR + 0x54) : mword 64) 4)
      by (rewrite /S2; apply upd_eq).
    assert (HcsS2 : callee_saved mkl S2).
    { rewrite /S2 /S1. apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity | apply callee_saved_refl]. }
    iApply (SleepPrepare.wp_sleep_prepare_sconf γs jp γlp S2
              (trap_res true + (av - 12))%nat 1%nat true false ({["cons"]} ∪ lks) Hjp Hjl
              ltac:(rewrite HS2a0; exact a_cons_r_nz) cr_lvl1
              ltac:(assert (trap_res true = 90%nat) as -> by reflexivity;
                    lia)
              ltac:(lkbelow)
              with "Hcg Hcnt Ht Hpc Hpinv").
    all: try lkbelow.
    iApply wp_next_off_intro. iIntros (msp) "%Hcssp Hcg Hcnt Hpc". rgall.
    iEval (rewrite HS2ra) in "Hpc".
    assert (Hp58 : ret_pc (add_vec_int (mword_of_int (CR + 0x54) : mword 64) 4)
                   = (mword_of_int (CR + 0x58) : mword 64)) by pcw.
    iEval (rewrite Hp58) in "Hpc".
    assert (HcsMsp : callee_saved M msp).
    { apply (callee_saved_trans M mkl msp HcsMk).
      apply (callee_saved_trans mkl S2 msp HcsS2 Hcssp). }
    assert (Hmsps1 : msp !!! Regidx Rs1 = a_cons)
      by (rewrite (callee_saved_lookup HcsMsp Rs1 ltac:(vm_compute; reflexivity)); exact Hs1).
    (* ---- +0x58 c.mv a0,s1 ; +0x5a jal release ---- *)
    iPoseProof (cnri_058 with "Ht") as "Hi58".
    iApply (wp_cmv_s_sconf (mword_of_int (CR + 0x58)) Ra0 Rs1 msp
              (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi58").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    iEval (rewrite Hmsps1 w32_zero_add) in "Hcg".
    set (S3 := <[Regidx Ra0 := regval_into_reg a_cons]> msp).
    assert (Hp5a : add_vec_int (mword_of_int (CR + 0x58) : mword 64) 2
                   = mword_of_int (CR + 0x5a)) by pcw.
    iEval (rewrite Hp5a) in "Hpc".
    iPoseProof (cnri_05a with "Ht") as "Hi5a".
    iApply (wp_jal_s_sconf (mword_of_int (CR + 0x5a)) Rra (mword_of_int 2672 : mword 21)
              S3 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi5a").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (S4 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CR + 0x5a) : mword 64) 4)]> S3).
    assert (Hjrl0 : add_vec (mword_of_int (CR + 0x5a) : mword 64)
                      (sign_extend' 64 (mword_of_int 2672 : mword 21))
                    = mword_of_int KernelSyms.release) by pcw.
    iEval (rewrite Hjrl0) in "Hpc".
    assert (HS4a0 : S4 !!! Regidx Ra0 = a_cons).
    { rewrite /S4 upd_ne; [| reg_neq]. rewrite /S3; apply upd_eq. }
    assert (HS4ra : S4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CR + 0x5a) : mword 64) 4)
      by (rewrite /S4; apply upd_eq).
    assert (HS4lka : add_vec (S4 !!! Regidx Ra0)
                       (sign_extend' 64 (mword_of_int 0 : mword 12)) = a_cons).
    { rewrite HS4a0.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by pcw.
      apply kv_addv_zero. }
    assert (HcsS4 : callee_saved msp S4).
    { rewrite /S4 /S3. apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity | apply callee_saved_refl]. }
    iApply (Release.wp_release_sconf KT1 γc a_cons "cons"%string cons_res S4
              0%nat true (proc_addr jp) (av - 12)%nat ({["cons"]} ∪ lks) HS4lka
              ltac:(lia)
              with "Hcg Ht Hpc Hlk Hlocked Hres Hcnt Hpay").
    iIntros (CIDr0 Hsr0 mrl0) "Hcg Hpc %Hcsrl0 Hcnt". rgall.
    assert (Hsetback2 : ({["cons"]} ∪ lks) ∖ {["cons"]} = lks)
      by (apply locks_add_del_below; lkbelow).
    iEval (rewrite Hsetback2) in "Hcnt".
    iEval (rewrite HS4ra) in "Hpc".
    assert (Hp5e : ret_pc (add_vec_int (mword_of_int (CR + 0x5a) : mword 64) 4)
                   = (mword_of_int (CR + 0x5e) : mword 64)) by pcw.
    iEval (rewrite Hp5e) in "Hpc".
    assert (HcsMr0 : callee_saved M mrl0).
    { apply (callee_saved_trans M msp mrl0 HcsMsp).
      apply (callee_saved_trans msp S4 mrl0 HcsS4 Hcsrl0). }
    (* ---- +0x5e jal sleep : the park.  Interrupts are back ON here. ---- *)
    iPoseProof (cnri_05e with "Ht") as "Hi5e".
    iApply (wp_jal_s_sconf (mword_of_int (CR + 0x5e)) Rra (mword_of_int 7498 : mword 21)
              mrl0 (av - 12)%nat true ltac:(nz) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi5e").
    iIntros (CIDs0 Hss0) "Hcg Hpc". rgall.
    set (S5 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CR + 0x5e) : mword 64) 4)]> mrl0).
    assert (Hjsl : add_vec (mword_of_int (CR + 0x5e) : mword 64)
                     (sign_extend' 64 (mword_of_int 7498 : mword 21))
                   = mword_of_int KernelSyms.sleep) by pcw.
    iEval (rewrite Hjsl) in "Hpc".
    assert (HS5ra : S5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CR + 0x5e) : mword 64) 4)
      by (rewrite /S5; apply upd_eq).
    assert (HcsS5 : callee_saved mrl0 S5)
      by (rewrite /S5; apply callee_saved_insert_r;
          [vm_compute; reflexivity | apply callee_saved_refl]).
    iDestruct (cpu_own_transport CIDr0 CIDs0 0%nat true (proc_addr jp) true
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Sleep.wp_sleep_sconf γs jp γlp S5 (av - 12)%nat true lks Hjp Hjl
              ltac:(lia)
              ltac:(lkbelow)
              with "Hcg Hcnt Ht Hpc Hpinv [] []").
    all: try lkbelow.
    { rewrite /trap_csrs_ext. done. }
    { rewrite /cpu_claim_ext. done. }
    iIntros (CIDs1 Hss1 msl) "%Hcssl Hcg Hcnt Hpc _ _". rgall.
    iEval (rewrite HS5ra) in "Hpc".
    assert (Hp62 : ret_pc (add_vec_int (mword_of_int (CR + 0x5e) : mword 64) 4)
                   = (mword_of_int (CR + 0x62) : mword 64)) by pcw.
    iEval (rewrite Hp62) in "Hpc".
    assert (HcsMsl : callee_saved M msl).
    { apply (callee_saved_trans M mrl0 msl HcsMr0).
      apply (callee_saved_trans mrl0 S5 msl HcsS5 Hcssl). }
    assert (Hmsls1 : msl !!! Regidx Rs1 = a_cons)
      by (rewrite (callee_saved_lookup HcsMsl Rs1 ltac:(vm_compute; reflexivity)); exact Hs1).
    (* ---- +0x62 c.mv a0,s1 ; +0x64 jal acquire ---- *)
    iPoseProof (cnri_062 with "Ht") as "Hi62".
    iApply (wp_cmv_s_sconf (mword_of_int (CR + 0x62)) Ra0 Rs1 msl (av - 12)%nat true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi62").
    iIntros (CIDq0 Hsq0) "Hcg Hpc". rgall.
    iEval (rewrite Hmsls1 w32_zero_add) in "Hcg".
    set (S6 := <[Regidx Ra0 := regval_into_reg a_cons]> msl).
    assert (Hp64 : add_vec_int (mword_of_int (CR + 0x62) : mword 64) 2
                   = mword_of_int (CR + 0x64)) by pcw.
    iEval (rewrite Hp64) in "Hpc".
    iPoseProof (cnri_064 with "Ht") as "Hi64".
    iApply (wp_jal_s_sconf (mword_of_int (CR + 0x64)) Rra (mword_of_int 2526 : mword 21)
              S6 (av - 12)%nat true ltac:(nz) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi64").
    iIntros (CIDq1 Hsq1) "Hcg Hpc". rgall.
    set (S7 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CR + 0x64) : mword 64) 4)]> S6).
    assert (Hjaq : add_vec (mword_of_int (CR + 0x64) : mword 64)
                     (sign_extend' 64 (mword_of_int 2526 : mword 21))
                   = mword_of_int KernelSyms.acquire) by pcw.
    iEval (rewrite Hjaq) in "Hpc".
    assert (HS7a0 : S7 !!! Regidx Ra0 = a_cons).
    { rewrite /S7 upd_ne; [| reg_neq]. rewrite /S6; apply upd_eq. }
    assert (HS7ra : S7 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CR + 0x64) : mword 64) 4)
      by (rewrite /S7; apply upd_eq).
    assert (HcsS7 : callee_saved msl S7).
    { rewrite /S7 /S6. apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity | apply callee_saved_refl]. }
    iDestruct (cpu_own_transport CIDs1 CIDq1 0%nat true (proc_addr jp) true
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Acquire.wp_acquire_sconf KT1 γc "cons"%string cons_res S7 0%nat true
              (proc_addr jp) (av - 12)%nat true lks cr_lvl0
              ltac:(lia)
              Hbelow
              with "Hcg Hcnt Ht Hpc []").
    all: try lkbelow.
    { iEval (rewrite HS7a0). iExact "Hlk". }
    iIntros (CIDq2 Hsq2 ms2 maq) "%Hms2 Hcg Hpc %Hcsaq Hlocked Hres Hcnt Hpay". rgall.
    iEval (rewrite HS7ra) in "Hpc".
    assert (Hp68 : ret_pc (add_vec_int (mword_of_int (CR + 0x64) : mword 64) 4)
                   = (mword_of_int (CR + 0x68) : mword 64)) by pcw.
    iEval (rewrite Hp68) in "Hpc".
    assert (HcsMaq : callee_saved M maq).
    { apply (callee_saved_trans M msl maq HcsMsl).
      apply (callee_saved_trans msl S7 maq HcsS7 Hcsaq). }
    (* ---- +0x68 lw a5,152(s1) ; +0x6c lw a4,156(s1) ---- *)
    iDestruct "Hres" as (rr2 ww2 ee2 bs2) "(Hrc & Hwc & Hec & %Hlen2 & Hdat)".
    assert (Hmaqs1 : maq !!! Regidx Rs1 = a_cons)
      by (rewrite (callee_saved_lookup HcsMaq Rs1 ltac:(vm_compute; reflexivity)); exact Hs1).
    assert (Hra2 : add_vec (maq !!! Regidx Rs1)
                     (sign_extend' 64 (mword_of_int 152 : mword 12)) = a_cons_r)
      by (rewrite Hmaqs1; reflexivity).
    iPoseProof (cnri_068 with "Ht") as "Hi68".
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CR + 0x68)) Ra5 Rs1 (mword_of_int 152 : mword 12)
              maq (trap_res true + (av - 12))%nat rr2 false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi68 [Hrc]").
    { rgall. iEval (rewrite Hra2). iExact "Hrc". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hrc". rgall. iEval (rewrite Hra2) in "Hrc".
    set (S8 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 rr2)]> maq).
    assert (Hp6c : add_vec_int (mword_of_int (CR + 0x68) : mword 64) 4
                   = mword_of_int (CR + 0x6c)) by pcw.
    iEval (rewrite Hp6c) in "Hpc".
    assert (HS8s1 : S8 !!! Regidx Rs1 = a_cons)
      by (rewrite /S8 upd_ne; [exact Hmaqs1 | reg_neq]).
    assert (Hwa2 : add_vec (S8 !!! Regidx Rs1)
                     (sign_extend' 64 (mword_of_int 156 : mword 12)) = a_cons_w)
      by (rewrite HS8s1; reflexivity).
    iPoseProof (cnri_06c with "Ht") as "Hi6c".
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CR + 0x6c)) Ra4 Rs1 (mword_of_int 156 : mword 12)
              S8 (trap_res true + (av - 12))%nat ww2 false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi6c [Hwc]").
    { rgall. iEval (rewrite Hwa2). iExact "Hwc". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hwc". rgall. iEval (rewrite Hwa2) in "Hwc".
    set (S9 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 ww2)]> S8).
    assert (Hp70 : add_vec_int (mword_of_int (CR + 0x6c) : mword 64) 4
                   = mword_of_int (CR + 0x70)) by pcw.
    iEval (rewrite Hp70) in "Hpc".
    assert (HS9a4 : S9 !!! Regidx Ra4 = sign_extend' 64 ww2)
      by (rewrite /S9; apply upd_eq).
    assert (HS9a5 : S9 !!! Regidx Ra5 = sign_extend' 64 rr2).
    { rewrite /S9 upd_ne; [| reg_neq]. rewrite /S8; apply upd_eq. }
    assert (HcsMS9 : callee_saved M S9).
    { apply (callee_saved_trans M maq S9 HcsMaq).
      rewrite /S9 /S8. apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity | apply callee_saved_refl]. }
    assert (HregS9 : cr_regs S9 m0 sp0 nc cur n).
    { unfold cr_regs. split_and!;
        first [ rewrite (callee_saved_lookup HcsMS9 csp_rs1 ltac:(vm_compute; reflexivity)); exact Hsp
              | rewrite (callee_saved_lookup HcsMS9 Rs0 ltac:(vm_compute; reflexivity)); exact Hs0
              | rewrite (callee_saved_lookup HcsMS9 Rs1 ltac:(vm_compute; reflexivity)); exact Hs1
              | rewrite (callee_saved_lookup HcsMS9 Rs2 ltac:(vm_compute; reflexivity)); exact Hs2
              | rewrite (callee_saved_lookup HcsMS9 Rs3 ltac:(vm_compute; reflexivity)); exact Hs3
              | rewrite (callee_saved_lookup HcsMS9 Rs4 ltac:(vm_compute; reflexivity)); exact Hs4
              | rewrite (callee_saved_lookup HcsMS9 Rs6 ltac:(vm_compute; reflexivity)); exact Hs6
              | rewrite (callee_saved_lookup HcsMS9 Rs7 ltac:(vm_compute; reflexivity)); exact Hs7
              | rewrite (callee_saved_lookup HcsMS9 Rs8 ltac:(vm_compute; reflexivity)); exact Hcs8
              | rewrite (callee_saved_lookup HcsMS9 Rs9 ltac:(vm_compute; reflexivity)); exact Hcs9
              | rewrite (callee_saved_lookup HcsMS9 Rs10 ltac:(vm_compute; reflexivity)); exact Hcs10
              | rewrite (callee_saved_lookup HcsMS9 Rs11 ltac:(vm_compute; reflexivity)); exact Hcs11 ]. }
    assert (HS9s5 : S9 !!! Regidx Rs5 = m0 !!! Regidx Rs5)
      by (rewrite (callee_saved_lookup HcsMS9 Rs5 ltac:(vm_compute; reflexivity)); exact Hs5).
    iPoseProof (cnri_070 with "Ht") as "Hi70".
    destruct (eq_vec (sign_extend' 64 ww2 : mword 64) (sign_extend' 64 rr2)) eqn:Hstill.
    { (* still empty: THE BACK EDGE to +0x48 *)
      iApply (wp_beq_taken_s_sconf (mword_of_int (CR + 0x70)) (mword_of_int 8152 : mword 13)
                Ra5 Ra4 S9 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(nz)
                ltac:(rgall; rewrite HS9a4 HS9a5; exact Hstill)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi70").
      (* the Loeb back edge: the [▷] has to come off "IH", not just the goal *)
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hbk48 : add_vec (mword_of_int (CR + 0x70) : mword 64)
                        (sign_extend' 64 (mword_of_int 8152 : mword 13))
                      = mword_of_int (CR + 0x48)) by pcw.
      iEval (rewrite Hbk48) in "Hpc".
      iSpecialize ("IH" $! CIDq2 with "[%]"); [wp_next_chain|].
      iApply ("IH" $! S9 nc cur P' with "[%] [%] [%] [%] EX Hcg Hpc Hcnt Hpay Hlocked
                [Hrc Hwc Hec Hdat] Hpriv Hrest").
      - exact HregS9.
      - exact HS9s5.
      - split; [exact Hncpos | split; [exact Hrng | exact Hfl]].
      - exact Hext.
      - iExists rr2, ww2, ee2, bs2. iFrame "Hrc Hwc Hec Hdat". iPureIntro. exact Hlen2. }
    (* data arrived: fall to +0x74, spill s5 and enter the copy block *)
    iApply (wp_beq_fall_s_sconf (mword_of_int (CR + 0x70)) (mword_of_int 8152 : mword 13)
              Ra5 Ra4 S9 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HS9a4 HS9a5; exact Hstill) with "Hcg Hpc Hi70").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp74 : add_vec_int (mword_of_int (CR + 0x70) : mword 64) 4
                   = mword_of_int (CR + 0x74)) by pcw.
    iEval (rewrite Hp74) in "Hpc".
    assert (HS9sp : S9 !!! Regidx csp_rs1 = pa_stk sp0 12%nat)
      by (destruct HregS9 as (Q & _); exact Q).
    iDestruct "Hrest" as "(Hq7 & Hq10 & Hq11 & Hq12)".
    iDestruct "Hq7" as (y7) "Hsl7".
    iPoseProof (cnri_074 with "Ht") as "Hi74".
    iApply (wp_csdsp_s_sconf (mword_of_int (CR + 0x74)) (mword_of_int 5 : mword 6) Rs5
              S9 (trap_res true + (av - 12))%nat y7 false with "Hcg Hpc Hi74 [Hsl7]").
    { iEval (rewrite HS9sp cr_b7). iExact "Hsl7". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hsl7". rgall.
    iEval (rewrite HS9sp cr_b7) in "Hsl7". iEval (rewrite HS9s5) in "Hsl7".
    assert (Hp76 : add_vec_int (mword_of_int (CR + 0x74) : mword 64) 2
                   = mword_of_int (CR + 0x76)) by pcw.
    iEval (rewrite Hp76) in "Hpc".
    iSpecialize ("HAVE" $! CIDq2 with "[%]"); [wp_next_chain|].
    iApply ("HAVE" $! S9 nc cur P' rr2 ww2 ee2 bs2
              with "[%] [%] [%] [%] [%] EX Hcg Hpc Hcnt Hpay Hlocked
                   Hrc Hwc Hec Hdat Hpriv Hsl7 Hq10 Hq11 Hq12").
    - exact HregS9.
    - exact HS9a5.
    - split; [exact Hncpos | split; [exact Hrng | exact Hfl]].
    - exact Hlen2.
    - exact Hext.
  Qed.

  (* =================================================================== *)
  (*  [HEAD] (+0x38): the outer loop, by FUEL induction on the remaining  *)
  (*  count.  Bounded by [n], so no Loeb -- the packaged leaves strip the *)
  (*  step's later and a guarded IH could never be applied.  The base     *)
  (*  case is VACUOUS: the head is only entered with fuel above the       *)
  (*  count still to copy.                                                *)
  (* =================================================================== *)
  Lemma cr_mk_head (γa γc γf : gname) (γs : list gname) (jp : nat) (γlp : gname)
      (sp0 : mword 64) (m0 : regfile)
      (av : nat) (pid : mword 32) (V : pprivate) (n : Z) (fl : nat) (lks : gset string) :
    (jp < NPROC)%nat ->
    γs !! jp = Some γlp ->
    (- 2 ^ 31 <= n < 2 ^ 31)%Z ->
    (consoleread_stack <= av)%nat ->
    locks_below lks "cons" ->
    kernel_text -∗ is_conslock γc -∗ kalloc_env γa None -∗
    procs_inv γs -∗
    cr_head_prop (CID0 := CID) γa γc γf jp sp0 m0 av pid V n fl lks.
  Proof.
    intros Hjp Hjl Hn31 Hav Hbelow.
    induction fl as [| fl IHfl].
    { iIntros "#Ht #Hlk #Henv #Hpinv". rewrite /cr_head_prop.
      iIntros (CIDh Hsh M nc cur P')
        "%Hregs %Hs5 %Hrng %Hfl %Hext EX Hcg Hpc Hcnt Hpay Hlocked Hres Hpriv Hrest".
      exfalso. lia. }
    iIntros "#Ht #Hlk #Henv #Hpinv".
    (* the copy block, then the park, both built from the fuel-[fl] head *)
    iAssert (□ cr_have_prop (CID0 := CID) γa γc γf jp sp0 m0 av pid V n fl lks)%I
      with "[]" as "#HAVE".
    { iModIntro.
      iApply (cr_mk_have γa γc γf jp sp0 m0 av pid V n fl lks Hn31 Hav Hbelow with "Ht Hlk Henv").
      iApply (IHfl with "Ht Hlk Henv Hpinv"). }
    iPoseProof (cr_mk_wait γa γc γf γs jp γlp sp0 m0 av pid V n fl lks Hjp Hjl Hn31 Hav Hbelow
                  with "Ht Hlk Henv Hpinv HAVE") as "WAIT".
    rewrite /cr_head_prop.
    iIntros (CIDh Hsh M nc cur P')
      "%Hregs %Hs5 %Hrng %Hfl %Hext EX Hcg Hpc Hcnt Hpay Hlocked Hres Hpriv Hrest".
    pose proof Hregs as Hregs'.
    destruct Hregs' as (Hsp & Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs6 & Hs7 & Hcs8 & Hcs9 & Hcs10 & Hcs11).
    assert (Hncb : (- 2 ^ 31 <= nc < 2 ^ 31)%Z).
    { destruct (Z.max_spec 0 n) as [[Hn0 Hm] | [Hn0 Hm]]; rewrite Hm in Hrng; lia. }
    (* ---- +0x38 blez s3 : while (n > 0) ---- *)
    assert (Hblez : zopz0zKzJ_s (zero_reg : mword 64) (M !!! Regidx Rs3) = Z.geb 0 nc).
    { rewrite Hs3. apply w32_bge0_moi. lia. }
    iPoseProof (cnri_038 with "Ht") as "Hi38".
    destruct (Z.geb 0 nc) eqn:HZ.
    { (* n <= 0: the loop is over, release and return [target - n] *)
      iApply (wp_bge_x0_taken_s_sconf (mword_of_int (CR + 0x38)) (mword_of_int 196 : mword 13)
                Rs3 M (trap_res true + (av - 12))%nat false ltac:(nz)
                ltac:(rgall; exact Hblez) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi38").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hjfc : add_vec (mword_of_int (CR + 0x38) : mword 64)
                       (sign_extend' 64 (mword_of_int 196 : mword 13))
                     = mword_of_int (CR + 0xfc)) by pcw.
      iEval (rewrite Hjfc) in "Hpc".
      iDestruct "EX" as "[HRETX _]".
      iSpecialize ("HRETX" $! CIDh with "[%]"); [wp_next_chain|].
      iApply ("HRETX" $! M P' nc with "[%] [%] [%] [%] [%] [%]
                Hcg Hpc Hcnt Hpay Hlocked Hres Hpriv Hrest").
      - exact Hsp.
      - exact Hs3.
      - exact Hs7.
      - unfold cr_cs_hi. split_and!;
          [exact Hs5 | exact Hcs8 | exact Hcs9 | exact Hcs10 | exact Hcs11].
      - exact Hrng.
      - exact Hext. }
    assert (Hncpos : (0 < nc)%Z).
    { rewrite Z.geb_leb in HZ. apply Z.leb_gt in HZ. lia. }
    iApply (wp_bge_x0_fall_s_sconf (mword_of_int (CR + 0x38)) (mword_of_int 196 : mword 13)
              Rs3 M (trap_res true + (av - 12))%nat false ltac:(nz)
              ltac:(rgall; exact Hblez) with "Hcg Hpc Hi38").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp3c : add_vec_int (mword_of_int (CR + 0x38) : mword 64) 4
                   = mword_of_int (CR + 0x3c)) by pcw.
    iEval (rewrite Hp3c) in "Hpc".
    (* ---- +0x3c lw a5,152(s1) ; +0x40 lw a4,156(s1) ---- *)
    iDestruct "Hres" as (rr ww ee bs) "(Hrc & Hwc & Hec & %Hlenb & Hdat)".
    assert (Hra : add_vec (M !!! Regidx Rs1)
                    (sign_extend' 64 (mword_of_int 152 : mword 12)) = a_cons_r)
      by (rewrite Hs1; reflexivity).
    iPoseProof (cnri_03c with "Ht") as "Hi3c".
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CR + 0x3c)) Ra5 Rs1 (mword_of_int 152 : mword 12)
              M (trap_res true + (av - 12))%nat rr false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi3c [Hrc]").
    { rgall. iEval (rewrite Hra). iExact "Hrc". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hrc". rgall. iEval (rewrite Hra) in "Hrc".
    set (D1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 rr)]> M).
    assert (Hp40 : add_vec_int (mword_of_int (CR + 0x3c) : mword 64) 4
                   = mword_of_int (CR + 0x40)) by pcw.
    iEval (rewrite Hp40) in "Hpc".
    assert (HD1s1 : D1 !!! Regidx Rs1 = a_cons)
      by (rewrite /D1 upd_ne; [exact Hs1 | reg_neq]).
    assert (Hwa : add_vec (D1 !!! Regidx Rs1)
                    (sign_extend' 64 (mword_of_int 156 : mword 12)) = a_cons_w)
      by (rewrite HD1s1; reflexivity).
    iPoseProof (cnri_040 with "Ht") as "Hi40".
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (CR + 0x40)) Ra4 Rs1 (mword_of_int 156 : mword 12)
              D1 (trap_res true + (av - 12))%nat ww false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi40 [Hwc]").
    { rgall. iEval (rewrite Hwa). iExact "Hwc". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hwc". rgall. iEval (rewrite Hwa) in "Hwc".
    set (D2 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 ww)]> D1).
    assert (Hp44 : add_vec_int (mword_of_int (CR + 0x40) : mword 64) 4
                   = mword_of_int (CR + 0x44)) by pcw.
    iEval (rewrite Hp44) in "Hpc".
    assert (HD2a4 : D2 !!! Regidx Ra4 = sign_extend' 64 ww)
      by (rewrite /D2; apply upd_eq).
    assert (HD2a5 : D2 !!! Regidx Ra5 = sign_extend' 64 rr).
    { rewrite /D2 upd_ne; [| reg_neq]. rewrite /D1; apply upd_eq. }
    assert (HthrD : forall r : mword 5, is_cs_idx r = true -> D2 !!! Regidx r = M !!! Regidx r).
    { intros r Hr.
      assert (N14 : r <> Ra4) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> Ra5) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /D2 upd_ne; [| congruence]. rewrite /D1 upd_ne; [| congruence]. reflexivity. }
    assert (HregD2 : cr_regs D2 m0 sp0 nc cur n).
    { unfold cr_regs. split_and!;
        first [ rewrite (HthrD csp_rs1 ltac:(vm_compute; reflexivity)); exact Hsp
              | rewrite (HthrD Rs0 ltac:(vm_compute; reflexivity)); exact Hs0
              | rewrite (HthrD Rs1 ltac:(vm_compute; reflexivity)); exact Hs1
              | rewrite (HthrD Rs2 ltac:(vm_compute; reflexivity)); exact Hs2
              | rewrite (HthrD Rs3 ltac:(vm_compute; reflexivity)); exact Hs3
              | rewrite (HthrD Rs4 ltac:(vm_compute; reflexivity)); exact Hs4
              | rewrite (HthrD Rs6 ltac:(vm_compute; reflexivity)); exact Hs6
              | rewrite (HthrD Rs7 ltac:(vm_compute; reflexivity)); exact Hs7
              | rewrite (HthrD Rs8 ltac:(vm_compute; reflexivity)); exact Hcs8
              | rewrite (HthrD Rs9 ltac:(vm_compute; reflexivity)); exact Hcs9
              | rewrite (HthrD Rs10 ltac:(vm_compute; reflexivity)); exact Hcs10
              | rewrite (HthrD Rs11 ltac:(vm_compute; reflexivity)); exact Hcs11 ]. }
    assert (HD2s5 : D2 !!! Regidx Rs5 = m0 !!! Regidx Rs5)
      by (rewrite (HthrD Rs5 ltac:(vm_compute; reflexivity)); exact Hs5).
    assert (HD2sp : D2 !!! Regidx csp_rs1 = pa_stk sp0 12%nat)
      by (destruct HregD2 as (Q & _); exact Q).
    (* ---- +0x44 bne a4,a5 : is the ring non-empty? ---- *)
    iPoseProof (cnri_044 with "Ht") as "Hi44".
    destruct (neq_vec (sign_extend' 64 ww : mword 64) (sign_extend' 64 rr)) eqn:Hne.
    { (* a byte is already there: +0xf2 spills s5 and jumps to the copy block *)
      iApply (wp_bne_taken_s_sconf (mword_of_int (CR + 0x44)) (mword_of_int 174 : mword 13)
                Ra5 Ra4 D2 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(nz)
                ltac:(rgall; rewrite HD2a4 HD2a5; exact Hne)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi44").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
      assert (Hjf2 : add_vec (mword_of_int (CR + 0x44) : mword 64)
                       (sign_extend' 64 (mword_of_int 174 : mword 13))
                     = mword_of_int (CR + 0xf2)) by pcw.
      iEval (rewrite Hjf2) in "Hpc".
      iDestruct "Hrest" as "(Hq7 & Hq10 & Hq11 & Hq12)".
      iDestruct "Hq7" as (y7) "Hsl7".
      iPoseProof (cnri_0f2 with "Ht") as "Hif2".
      iApply (wp_csdsp_s_sconf (mword_of_int (CR + 0xf2)) (mword_of_int 5 : mword 6) Rs5
                D2 (trap_res true + (av - 12))%nat y7 false with "Hcg Hpc Hif2 [Hsl7]").
      { iEval (rewrite HD2sp cr_b7). iExact "Hsl7". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hsl7". rgall.
      iEval (rewrite HD2sp cr_b7) in "Hsl7". iEval (rewrite HD2s5) in "Hsl7".
      assert (Hpf4 : add_vec_int (mword_of_int (CR + 0xf2) : mword 64) 2
                     = mword_of_int (CR + 0xf4)) by pcw.
      iEval (rewrite Hpf4) in "Hpc".
      iPoseProof (cnri_0f4 with "Ht") as "Hif4".
      iApply (wp_cj_s_sconf (mword_of_int (CR + 0xf4))
                (sign_extend' 21 (concat_vec (mword_of_int 1985 : mword 11) ('b"0")))
                D2 (trap_res true + (av - 12))%nat false
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hif4").
      iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc". rgall.
      assert (Hj76 : add_vec (mword_of_int (CR + 0xf4) : mword 64)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 1985 : mword 11) ('b"0"))))
                     = mword_of_int (CR + 0x76)) by pcw.
      iEval (rewrite Hj76) in "Hpc".
      iSpecialize ("HAVE" $! CIDh with "[%]"); [wp_next_chain|].
      iApply ("HAVE" $! D2 nc cur P' rr ww ee bs
                with "[%] [%] [%] [%] [%] EX Hcg Hpc Hcnt Hpay Hlocked
                     Hrc Hwc Hec Hdat Hpriv Hsl7 Hq10 Hq11 Hq12").
      - exact HregD2.
      - exact HD2a5.
      - split; [exact Hncpos | split; [exact Hrng | lia]].
      - exact Hlenb.
      - exact Hext. }
    (* the ring is empty: fall into the park at +0x48 *)
    iApply (wp_bne_fall_s_sconf (mword_of_int (CR + 0x44)) (mword_of_int 174 : mword 13)
              Ra5 Ra4 D2 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(nz)
              ltac:(rgall; rewrite HD2a4 HD2a5; exact Hne) with "Hcg Hpc Hi44").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    assert (Hp48 : add_vec_int (mword_of_int (CR + 0x44) : mword 64) 4
                   = mword_of_int (CR + 0x48)) by pcw.
    iEval (rewrite Hp48) in "Hpc".
    iSpecialize ("WAIT" $! CIDh with "[%]"); [wp_next_chain|].
    iApply ("WAIT" $! D2 nc cur P' with "[%] [%] [%] [%] EX Hcg Hpc Hcnt Hpay Hlocked
              [Hrc Hwc Hec Hdat] Hpriv Hrest").
    - exact HregD2.
    - exact HD2s5.
    - split; [exact Hncpos | split; [exact Hrng | lia]].
    - exact Hext.
    - iExists rr, ww, ee, bs. iFrame "Hrc Hwc Hec Hdat". iPureIntro. exact Hlenb.
  Qed.

  (* =================================================================== *)
  (*  THE WHOLE FUNCTION.  The prologue is straight-line down to the      *)
  (*  entry [acquire]; the exits are built out of the frame the moment    *)
  (*  the eight saves have landed, and the loop is entered with fuel one  *)
  (*  above the request.                                                  *)
  (* =================================================================== *)
  Lemma wp_consoleread_sconf (γa : gname) (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname) (γc : gname)
      (m : regfile) (av : nat) (eb : bool)
      (pid : mword 32) (V : pprivate) (n : Z) (b : bool) (lks : gset string)
    : wp_consoleread_sconf_body γa γf γs j γlp γc m av eb pid V n b lks.
  Proof.
    cbv beta delta [wp_consoleread_sconf_body].
    intros pcE pj ret_tgt Hj Hjl Hlen Ha0v Ha2v Hnrng Hav Heb Hbelow. subst eb.
    iIntros "Hcg Hcnt #Ht Hpc #Hlk Hpriv #Henv #Hpinv Hcont".
    (* LEVEL 0 WITH AN ENABLED BASE FORCES THE ENABLED INDEX, so the whole
       entry stretch speaks one index (piperead's note). *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    assert (Hbt : b = true) by (symmetry; exact Hbm).
    clear Hbm. subst b.
    assert (Hn31 : (- 2 ^ 31 <= n < 2 ^ 31)%Z) by lia.
    set (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    (* ================== PROLOGUE: the twelve-slot frame ================ *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 12%nat).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (cnri_000 with "Ht") as "Hi00".
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 58 : mword 6) m av 12%nat true
              ltac:(lia) Hpush with "Hcg Hpc Hi00").
    iIntros (CIDp1 Hsp1) "Hcg Hframe Hpc". rgall.
    iEval (rewrite Hspm) in "Hframe".
    set (P0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6))))]> m).
    assert (HP0sp : P0 !!! Regidx csp_rs1 = pa_stk sp0 12%nat)
      by (rewrite /P0 upd_eq; rewrite Hpush Hspm; reflexivity).
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (CR + 0x02)) by pcw.
    iEval (rewrite Hpc02) in "Hpc".
    (* the eight slot bridges the prologue stores name *)
    assert (Hb1 : add_vec (pa_stk sp0 12%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
                  = pa_stk sp0 1%nat) by (apply cr_slot_bridge; pcw).
    assert (Hb2 : add_vec (pa_stk sp0 12%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))
                  = pa_stk sp0 2%nat) by (apply cr_slot_bridge; pcw).
    assert (Hb3 : add_vec (pa_stk sp0 12%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk sp0 3%nat) by (apply cr_slot_bridge; pcw).
    assert (Hb4 : add_vec (pa_stk sp0 12%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk sp0 4%nat) by (apply cr_slot_bridge; pcw).
    assert (Hb5 : add_vec (pa_stk sp0 12%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk sp0 5%nat) by (apply cr_slot_bridge; pcw).
    assert (Hb6 : add_vec (pa_stk sp0 12%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk sp0 6%nat) by (apply cr_slot_bridge; pcw).
    assert (Hb8 : add_vec (pa_stk sp0 12%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 8%nat) by (apply cr_slot_bridge; pcw).
    assert (Hb9 : add_vec (pa_stk sp0 12%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 9%nat) by (apply cr_slot_bridge; pcw).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & _)".
    iDestruct "Q1" as (u1) "Hf1". iDestruct "Q2" as (u2) "Hf2".
    iDestruct "Q3" as (u3) "Hf3". iDestruct "Q4" as (u4) "Hf4".
    iDestruct "Q5" as (u5) "Hf5". iDestruct "Q6" as (u6) "Hf6".
    iDestruct "Q8" as (u8) "Hf8". iDestruct "Q9" as (u9) "Hf9".
    (* ---- +0x02 .. +0x10: save ra, s0, s1, s2, s3, s4, s6, s7 ---- *)
    iPoseProof (cnri_002 with "Ht") as "Hi02".
    iApply (wp_csdsp_s_sconf (mword_of_int (CR + 0x02)) (mword_of_int 11 : mword 6) Rra
              P0 (av - 12)%nat u1 true with "Hcg Hpc Hi02 [Hf1]").
    { iEval (rewrite HP0sp Hb1). iExact "Hf1". }
    iIntros (CIDp2 Hsp2) "Hcg Hpc Hf1". rgall. iEval (rewrite HP0sp Hb1) in "Hf1".
    assert (HP0ra : P0 !!! Regidx Rra = m !!! Regidx Rra)
      by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HP0ra) in "Hf1".
    assert (Hpc04 : add_vec_int (mword_of_int (CR + 0x02) : mword 64) 2
                    = mword_of_int (CR + 0x04)) by pcw.
    iEval (rewrite Hpc04) in "Hpc".
    iPoseProof (cnri_004 with "Ht") as "Hi04".
    iApply (wp_csdsp_s_sconf (mword_of_int (CR + 0x04)) (mword_of_int 10 : mword 6) Rs0
              P0 (av - 12)%nat u2 true with "Hcg Hpc Hi04 [Hf2]").
    { iEval (rewrite HP0sp Hb2). iExact "Hf2". }
    iIntros (CIDp3 Hsp3) "Hcg Hpc Hf2". rgall. iEval (rewrite HP0sp Hb2) in "Hf2".
    assert (HP0s0 : P0 !!! Regidx Rs0 = m !!! Regidx Rs0)
      by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HP0s0) in "Hf2".
    assert (Hpc06 : add_vec_int (mword_of_int (CR + 0x04) : mword 64) 2
                    = mword_of_int (CR + 0x06)) by pcw.
    iEval (rewrite Hpc06) in "Hpc".
    iPoseProof (cnri_006 with "Ht") as "Hi06".
    iApply (wp_csdsp_s_sconf (mword_of_int (CR + 0x06)) (mword_of_int 9 : mword 6) Rs1
              P0 (av - 12)%nat u3 true with "Hcg Hpc Hi06 [Hf3]").
    { iEval (rewrite HP0sp Hb3). iExact "Hf3". }
    iIntros (CIDp4 Hsp4) "Hcg Hpc Hf3". rgall. iEval (rewrite HP0sp Hb3) in "Hf3".
    assert (HP0s1 : P0 !!! Regidx Rs1 = m !!! Regidx Rs1)
      by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HP0s1) in "Hf3".
    assert (Hpc08 : add_vec_int (mword_of_int (CR + 0x06) : mword 64) 2
                    = mword_of_int (CR + 0x08)) by pcw.
    iEval (rewrite Hpc08) in "Hpc".
    iPoseProof (cnri_008 with "Ht") as "Hi08".
    iApply (wp_csdsp_s_sconf (mword_of_int (CR + 0x08)) (mword_of_int 8 : mword 6) Rs2
              P0 (av - 12)%nat u4 true with "Hcg Hpc Hi08 [Hf4]").
    { iEval (rewrite HP0sp Hb4). iExact "Hf4". }
    iIntros (CIDp5 Hsp5) "Hcg Hpc Hf4". rgall. iEval (rewrite HP0sp Hb4) in "Hf4".
    assert (HP0s2 : P0 !!! Regidx Rs2 = m !!! Regidx Rs2)
      by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HP0s2) in "Hf4".
    assert (Hpc0a : add_vec_int (mword_of_int (CR + 0x08) : mword 64) 2
                    = mword_of_int (CR + 0x0a)) by pcw.
    iEval (rewrite Hpc0a) in "Hpc".
    iPoseProof (cnri_00a with "Ht") as "Hi0a".
    iApply (wp_csdsp_s_sconf (mword_of_int (CR + 0x0a)) (mword_of_int 7 : mword 6) Rs3
              P0 (av - 12)%nat u5 true with "Hcg Hpc Hi0a [Hf5]").
    { iEval (rewrite HP0sp Hb5). iExact "Hf5". }
    iIntros (CIDp6 Hsp6) "Hcg Hpc Hf5". rgall. iEval (rewrite HP0sp Hb5) in "Hf5".
    assert (HP0s3 : P0 !!! Regidx Rs3 = m !!! Regidx Rs3)
      by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HP0s3) in "Hf5".
    assert (Hpc0c : add_vec_int (mword_of_int (CR + 0x0a) : mword 64) 2
                    = mword_of_int (CR + 0x0c)) by pcw.
    iEval (rewrite Hpc0c) in "Hpc".
    iPoseProof (cnri_00c with "Ht") as "Hi0c".
    iApply (wp_csdsp_s_sconf (mword_of_int (CR + 0x0c)) (mword_of_int 6 : mword 6) Rs4
              P0 (av - 12)%nat u6 true with "Hcg Hpc Hi0c [Hf6]").
    { iEval (rewrite HP0sp Hb6). iExact "Hf6". }
    iIntros (CIDp7 Hsp7) "Hcg Hpc Hf6". rgall. iEval (rewrite HP0sp Hb6) in "Hf6".
    assert (HP0s4 : P0 !!! Regidx Rs4 = m !!! Regidx Rs4)
      by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HP0s4) in "Hf6".
    assert (Hpc0e : add_vec_int (mword_of_int (CR + 0x0c) : mword 64) 2
                    = mword_of_int (CR + 0x0e)) by pcw.
    iEval (rewrite Hpc0e) in "Hpc".
    iPoseProof (cnri_00e with "Ht") as "Hi0e".
    iApply (wp_csdsp_s_sconf (mword_of_int (CR + 0x0e)) (mword_of_int 4 : mword 6) Rs6
              P0 (av - 12)%nat u8 true with "Hcg Hpc Hi0e [Hf8]").
    { iEval (rewrite HP0sp Hb8). iExact "Hf8". }
    iIntros (CIDp8 Hsp8) "Hcg Hpc Hf8". rgall. iEval (rewrite HP0sp Hb8) in "Hf8".
    assert (HP0s6 : P0 !!! Regidx Rs6 = m !!! Regidx Rs6)
      by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HP0s6) in "Hf8".
    assert (Hpc10 : add_vec_int (mword_of_int (CR + 0x0e) : mword 64) 2
                    = mword_of_int (CR + 0x10)) by pcw.
    iEval (rewrite Hpc10) in "Hpc".
    iPoseProof (cnri_010 with "Ht") as "Hi10".
    iApply (wp_csdsp_s_sconf (mword_of_int (CR + 0x10)) (mword_of_int 3 : mword 6) Rs7
              P0 (av - 12)%nat u9 true with "Hcg Hpc Hi10 [Hf9]").
    { iEval (rewrite HP0sp Hb9). iExact "Hf9". }
    iIntros (CIDp9 Hsp9) "Hcg Hpc Hf9". rgall. iEval (rewrite HP0sp Hb9) in "Hf9".
    assert (HP0s7 : P0 !!! Regidx Rs7 = m !!! Regidx Rs7)
      by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HP0s7) in "Hf9".
    assert (Hpc12 : add_vec_int (mword_of_int (CR + 0x10) : mword 64) 2
                    = mword_of_int (CR + 0x12)) by pcw.
    iEval (rewrite Hpc12) in "Hpc".
    (* ---- the exits, built the moment the frame is saved ---- *)
    iAssert (cr_ret (CID0 := CID) j m av true pid V n lks) with "[Hcont]" as "Hcont".
    { rewrite /cr_ret. iExact "Hcont". }
    iAssert (cr_saved sp0 m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf8 Hf9]" as "Hsaved".
    { rewrite /cr_saved. iFrame "Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf8 Hf9". }
    iAssert (cr_exits (CID0 := CID) γc j sp0 m av pid V n lks)
      with "[Hsaved Hcont]" as "EX".
    { rewrite /cr_exits. iSplit.
      - iApply (cr_mk_retx γc j sp0 m av pid V n lks Hn31 Hav Hbelow with "Ht Hlk").
        iApply (cr_mk_epi j sp0 m av pid V n lks eq_refl Hav with "Ht Hsaved Hcont").
      - iApply (cr_mk_epi j sp0 m av pid V n lks eq_refl Hav with "Ht Hsaved Hcont"). }
    (* ---- +0x12 c.addi4spn s0,sp,96 ---- *)
    assert (Hs0v : add_vec (pa_stk sp0 12%nat)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8))) = sp0).
    { unfold pa_stk, add_vec_int. rewrite add_vec_assoc.
      rewrite (_ : add_vec (mword_of_int (- (8 * Z.of_nat 12%nat)) : mword 64)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8)))
                   = (mword_of_int 0 : mword 64)); [| pcw].
      apply bv_add_0_r. vm_compute. reflexivity. }
    iPoseProof (cnri_012 with "Ht") as "Hi12".
    iApply (wp_caddi4spn_s_sconf (mword_of_int (CR + 0x12)) (Cregidx (mword_of_int 0))
              (mword_of_int 24 : mword 8) Rs0 P0 (av - 12)%nat true
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi12").
    iIntros (CIDp10 Hsp10) "Hcg Hpc". rgall.
    iEval (rewrite HP0sp Hs0v) in "Hcg".
    set (P1 := <[Regidx Rs0 := regval_into_reg sp0]> P0).
    assert (Hpc14 : add_vec_int (mword_of_int (CR + 0x12) : mword 64) 2
                    = mword_of_int (CR + 0x14)) by pcw.
    iEval (rewrite Hpc14) in "Hpc".
    (* ---- +0x14/+0x16/+0x18/+0x1a: s6 := a0, s4 := a1, s3 := a2, s7 := a2 ---- *)
    assert (HP1a0 : P1 !!! Regidx Ra0 = (mword_of_int 1 : mword 64)).
    { rewrite /P1 upd_ne; [| reg_neq]. rewrite /P0 upd_ne; [| reg_neq]. exact Ha0v. }
    iPoseProof (cnri_014 with "Ht") as "Hi14".
    iApply (wp_cmv_s_sconf (mword_of_int (CR + 0x14)) Rs6 Ra0 P1 (av - 12)%nat true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi14").
    iIntros (CIDp11 Hsp11) "Hcg Hpc". rgall.
    iEval (rewrite HP1a0 w32_zero_add) in "Hcg".
    set (P2 := <[Regidx Rs6 := regval_into_reg (mword_of_int 1 : mword 64)]> P1).
    assert (Hpc16 : add_vec_int (mword_of_int (CR + 0x14) : mword 64) 2
                    = mword_of_int (CR + 0x16)) by pcw.
    iEval (rewrite Hpc16) in "Hpc".
    assert (HP2a1 : P2 !!! Regidx Ra1 = m !!! Regidx Ra1).
    { rewrite /P2 upd_ne; [| reg_neq]. rewrite /P1 upd_ne; [| reg_neq].
      rewrite /P0 upd_ne; [reflexivity | reg_neq]. }
    iPoseProof (cnri_016 with "Ht") as "Hi16".
    iApply (wp_cmv_s_sconf (mword_of_int (CR + 0x16)) Rs4 Ra1 P2 (av - 12)%nat true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi16").
    iIntros (CIDp12 Hsp12) "Hcg Hpc". rgall.
    iEval (rewrite HP2a1 w32_zero_add) in "Hcg".
    set (P3 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Ra1)]> P2).
    assert (Hpc18 : add_vec_int (mword_of_int (CR + 0x16) : mword 64) 2
                    = mword_of_int (CR + 0x18)) by pcw.
    iEval (rewrite Hpc18) in "Hpc".
    assert (HP3a2 : P3 !!! Regidx Ra2 = (mword_of_int n : mword 64)).
    { rewrite /P3 upd_ne; [| reg_neq]. rewrite /P2 upd_ne; [| reg_neq].
      rewrite /P1 upd_ne; [| reg_neq]. rewrite /P0 upd_ne; [| reg_neq]. exact Ha2v. }
    iPoseProof (cnri_018 with "Ht") as "Hi18".
    iApply (wp_cmv_s_sconf (mword_of_int (CR + 0x18)) Rs3 Ra2 P3 (av - 12)%nat true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi18").
    iIntros (CIDp13 Hsp13) "Hcg Hpc". rgall.
    iEval (rewrite HP3a2 w32_zero_add) in "Hcg".
    set (P4 := <[Regidx Rs3 := regval_into_reg (mword_of_int n : mword 64)]> P3).
    assert (Hpc1a : add_vec_int (mword_of_int (CR + 0x18) : mword 64) 2
                    = mword_of_int (CR + 0x1a)) by pcw.
    iEval (rewrite Hpc1a) in "Hpc".
    assert (HP4a2 : P4 !!! Regidx Ra2 = (mword_of_int n : mword 64))
      by (rewrite /P4 upd_ne; [exact HP3a2 | reg_neq]).
    iPoseProof (cnri_01a with "Ht") as "Hi1a".
    iApply (wp_cmv_s_sconf (mword_of_int (CR + 0x1a)) Rs7 Ra2 P4 (av - 12)%nat true
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1a").
    iIntros (CIDp14 Hsp14) "Hcg Hpc". rgall.
    iEval (rewrite HP4a2 w32_zero_add) in "Hcg".
    set (P5 := <[Regidx Rs7 := regval_into_reg (mword_of_int n : mword 64)]> P4).
    assert (Hpc1c : add_vec_int (mword_of_int (CR + 0x1a) : mword 64) 2
                    = mword_of_int (CR + 0x1c)) by pcw.
    iEval (rewrite Hpc1c) in "Hpc".
    (* the register pins at [P5] *)
    assert (HP5sp : P5 !!! Regidx csp_rs1 = pa_stk sp0 12%nat).
    { rewrite /P5 upd_ne; [| reg_neq]. rewrite /P4 upd_ne; [| reg_neq].
      rewrite /P3 upd_ne; [| reg_neq]. rewrite /P2 upd_ne; [| reg_neq].
      rewrite /P1 upd_ne; [| reg_neq]. exact HP0sp. }
    assert (HP5s0 : P5 !!! Regidx Rs0 = sp0).
    { rewrite /P5 upd_ne; [| reg_neq]. rewrite /P4 upd_ne; [| reg_neq].
      rewrite /P3 upd_ne; [| reg_neq]. rewrite /P2 upd_ne; [| reg_neq].
      rewrite /P1; apply upd_eq. }
    assert (HP5s3 : P5 !!! Regidx Rs3 = (mword_of_int n : mword 64)).
    { rewrite /P5 upd_ne; [| reg_neq]. rewrite /P4; apply upd_eq. }
    assert (HP5s4 : P5 !!! Regidx Rs4 = m !!! Regidx Ra1).
    { rewrite /P5 upd_ne; [| reg_neq]. rewrite /P4 upd_ne; [| reg_neq].
      rewrite /P3; apply upd_eq. }
    assert (HP5s6 : P5 !!! Regidx Rs6 = (mword_of_int 1 : mword 64)).
    { rewrite /P5 upd_ne; [| reg_neq]. rewrite /P4 upd_ne; [| reg_neq].
      rewrite /P3 upd_ne; [| reg_neq]. rewrite /P2; apply upd_eq. }
    assert (HP5s7 : P5 !!! Regidx Rs7 = (mword_of_int n : mword 64))
      by (rewrite /P5; apply upd_eq).
    assert (HthrP : forall r : mword 5,
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs3 -> r <> Rs4 -> r <> Rs6 -> r <> Rs7 ->
              P5 !!! Regidx r = m !!! Regidx r).
    { intros r N2 N8 N19 N20 N22 N23.
      rewrite /P5 upd_ne; [| congruence]. rewrite /P4 upd_ne; [| congruence].
      rewrite /P3 upd_ne; [| congruence]. rewrite /P2 upd_ne; [| congruence].
      rewrite /P1 upd_ne; [| congruence]. rewrite /P0 upd_ne; [| congruence]. reflexivity. }
    (* ---- +0x1c auipc a0,0x12 ; +0x20 addi a0,a0,284 : a0 := &cons ---- *)
    iPoseProof (cnri_01c with "Ht") as "Hi1c".
    iApply (wp_auipc_s_sconf (mword_of_int (CR + 0x1c)) Ra0 (mword_of_int 18 : mword 20)
              P5 (av - 12)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1c").
    iIntros (CIDp15 Hsp15) "Hcg Hpc". rgall.
    set (P6 := <[Regidx Ra0 := regval_into_reg
        (add_vec (mword_of_int (CR + 0x1c) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> P5).
    assert (Hpc20 : add_vec_int (mword_of_int (CR + 0x1c) : mword 64) 4
                    = mword_of_int (CR + 0x20)) by pcw.
    iEval (rewrite Hpc20) in "Hpc".
    iPoseProof (cnri_020 with "Ht") as "Hi20".
    iApply (wp_addi4_s_sconf (mword_of_int (CR + 0x20)) Ra0 Ra0 (mword_of_int 316 : mword 12)
              P6 (av - 12)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi20").
    iIntros (CIDp16 Hsp16) "Hcg Hpc". rgall.
    set (P7 := <[Regidx Ra0 := regval_into_reg
        (add_vec (P6 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 316 : mword 12)))]> P6).
    assert (HP7a0 : P7 !!! Regidx Ra0 = a_cons).
    { rewrite /P7 upd_eq /P6 upd_eq /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpc24 : add_vec_int (mword_of_int (CR + 0x20) : mword 64) 4
                    = mword_of_int (CR + 0x24)) by pcw.
    iEval (rewrite Hpc24) in "Hpc".
    (* ---- +0x24 jal ra,acquire ---- *)
    iPoseProof (cnri_024 with "Ht") as "Hi24".
    iApply (wp_jal_s_sconf (mword_of_int (CR + 0x24)) Rra (mword_of_int 2590 : mword 21)
              P7 (av - 12)%nat true ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi24").
    iIntros (CIDp17 Hsp17) "Hcg Hpc". rgall.
    set (P8 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (CR + 0x24) : mword 64) 4)]> P7).
    assert (Hjaq : add_vec (mword_of_int (CR + 0x24) : mword 64)
                     (sign_extend' 64 (mword_of_int 2590 : mword 21))
                   = mword_of_int KernelSyms.acquire) by pcw.
    iEval (rewrite Hjaq) in "Hpc".
    assert (HP8a0 : P8 !!! Regidx Ra0 = a_cons)
      by (rewrite /P8 upd_ne; [exact HP7a0 | reg_neq]).
    assert (HP8ra : P8 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CR + 0x24) : mword 64) 4)
      by (rewrite /P8; apply upd_eq).
    assert (HthrP8 : forall r : mword 5, is_cs_idx r = true -> P8 !!! Regidx r = P5 !!! Regidx r).
    { intros r Hr.
      assert (N1 : r <> Rra) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> Ra0) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /P8 upd_ne; [| congruence]. rewrite /P7 upd_ne; [| congruence].
      rewrite /P6 upd_ne; [| congruence]. reflexivity. }
    iDestruct (cpu_own_transport CID CIDp17 0%nat true pj true ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Acquire.wp_acquire_sconf KT1 γc "cons"%string cons_res P8 0%nat true pj
              (av - 12)%nat true lks cr_lvl0 ltac:(lia)
              Hbelow
              with "Hcg Hcnt Ht Hpc []").
    all: try lkbelow.
    { iEval (rewrite HP8a0). iExact "Hlk". }
    iIntros (CIDaq Hsaq ms0 maq) "%Hms0 Hcg Hpc %Hcsaq Hlocked Hres Hcnt Hpay". rgall.
    iEval (rewrite HP8ra) in "Hpc".
    assert (Hpc28 : ret_pc (add_vec_int (mword_of_int (CR + 0x24) : mword 64) 4)
                    = (mword_of_int (CR + 0x28) : mword 64)) by pcw.
    iEval (rewrite Hpc28) in "Hpc".
    (* ---- +0x28/+0x2c: s1 := &cons ; +0x30/+0x34: s2 := &cons.r ---- *)
    iPoseProof (cnri_028 with "Ht") as "Hi28".
    iApply (wp_auipc_s_sconf (mword_of_int (CR + 0x28)) Rs1 (mword_of_int 18 : mword 20)
              maq (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi28").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (A1 := <[Regidx Rs1 := regval_into_reg
        (add_vec (mword_of_int (CR + 0x28) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> maq).
    assert (Hpc2c : add_vec_int (mword_of_int (CR + 0x28) : mword 64) 4
                    = mword_of_int (CR + 0x2c)) by pcw.
    iEval (rewrite Hpc2c) in "Hpc".
    iPoseProof (cnri_02c with "Ht") as "Hi2c".
    iApply (wp_addi4_s_sconf (mword_of_int (CR + 0x2c)) Rs1 Rs1 (mword_of_int 304 : mword 12)
              A1 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi2c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (A2 := <[Regidx Rs1 := regval_into_reg
        (add_vec (A1 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 304 : mword 12)))]> A1).
    assert (HA2s1 : A2 !!! Regidx Rs1 = a_cons).
    { rewrite /A2 upd_eq /A1 upd_eq /a_cons. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpc30 : add_vec_int (mword_of_int (CR + 0x2c) : mword 64) 4
                    = mword_of_int (CR + 0x30)) by pcw.
    iEval (rewrite Hpc30) in "Hpc".
    iPoseProof (cnri_030 with "Ht") as "Hi30".
    iApply (wp_auipc_s_sconf (mword_of_int (CR + 0x30)) Rs2 (mword_of_int 18 : mword 20)
              A2 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi30").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (A3 := <[Regidx Rs2 := regval_into_reg
        (add_vec (mword_of_int (CR + 0x30) : mword 64)
           (auipc_off (mword_of_int 18 : mword 20)))]> A2).
    assert (Hpc34 : add_vec_int (mword_of_int (CR + 0x30) : mword 64) 4
                    = mword_of_int (CR + 0x34)) by pcw.
    iEval (rewrite Hpc34) in "Hpc".
    iPoseProof (cnri_034 with "Ht") as "Hi34".
    iApply (wp_addi4_s_sconf (mword_of_int (CR + 0x34)) Rs2 Rs2 (mword_of_int 448 : mword 12)
              A3 (trap_res true + (av - 12))%nat false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi34").
    iApply wp_next_off_intro. iIntros "Hcg Hpc". rgall.
    set (A4 := <[Regidx Rs2 := regval_into_reg
        (add_vec (A3 !!! Regidx Rs2) (sign_extend' 64 (mword_of_int 448 : mword 12)))]> A3).
    assert (HA4s2 : A4 !!! Regidx Rs2 = a_cons_r).
    { rewrite /A4 upd_eq /A3 upd_eq /a_cons_r /coff_of /a_cons.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HA4s1 : A4 !!! Regidx Rs1 = a_cons)
      by (rewrite /A4 upd_ne; [exact HA2s1 | reg_neq]).
    assert (Hpc38 : add_vec_int (mword_of_int (CR + 0x34) : mword 64) 4
                    = mword_of_int (CR + 0x38)) by pcw.
    iEval (rewrite Hpc38) in "Hpc".
    assert (HthrA : forall r : mword 5, r <> Rs1 -> r <> Rs2 ->
              A4 !!! Regidx r = maq !!! Regidx r).
    { intros r N9 N18.
      rewrite /A4 upd_ne; [| congruence]. rewrite /A3 upd_ne; [| congruence].
      rewrite /A2 upd_ne; [| congruence]. rewrite /A1 upd_ne; [| congruence]. reflexivity. }
    assert (Hchain : forall r : mword 5, is_cs_idx r = true -> r <> Rs1 -> r <> Rs2 ->
              A4 !!! Regidx r = P5 !!! Regidx r).
    { intros r Hr N9 N18.
      rewrite (HthrA r N9 N18). rewrite (callee_saved_lookup Hcsaq r Hr).
      apply HthrP8; exact Hr. }
    (* ================== enter the loop at [nc = n] ==================== *)
    assert (HregA4 : cr_regs A4 m sp0 n (m !!! Regidx Ra1) n).
    { unfold cr_regs. split_and!.
      - rewrite (Hchain csp_rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)).
        exact HP5sp.
      - rewrite (Hchain Rs0 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)).
        exact HP5s0.
      - exact HA4s1.
      - exact HA4s2.
      - rewrite (Hchain Rs3 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)).
        exact HP5s3.
      - rewrite (Hchain Rs4 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)).
        exact HP5s4.
      - rewrite (Hchain Rs6 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)).
        exact HP5s6.
      - rewrite (Hchain Rs7 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)).
        exact HP5s7.
      - rewrite (Hchain Rs8 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)).
        apply HthrP; reg_neq.
      - rewrite (Hchain Rs9 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)).
        apply HthrP; reg_neq.
      - rewrite (Hchain Rs10 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)).
        apply HthrP; reg_neq.
      - rewrite (Hchain Rs11 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)).
        apply HthrP; reg_neq. }
    assert (HA4s5 : A4 !!! Regidx Rs5 = m !!! Regidx Rs5).
    { rewrite (Hchain Rs5 ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq)).
      apply HthrP; reg_neq. }
    iPoseProof (cr_mk_head γa γc γf γs j γlp sp0 m av pid V n (S (Z.to_nat n)) lks
                  Hj Hjl Hn31 Hav Hbelow with "Ht Hlk Henv Hpinv") as "HEAD".
    iSpecialize ("HEAD" $! CIDaq with "[%]"); [wp_next_chain|].
    iApply ("HEAD" $! A4 n (m !!! Regidx Ra1) (pv_upt V)
              with "[%] [%] [%] [%] [%] EX Hcg Hpc Hcnt Hpay Hlocked Hres [Hpriv]
                   [Q7 Q10 Q11 Q12]").
    - exact HregA4.
    - exact HA4s5.
    - replace (n - n)%Z with 0%Z by lia. split; [lia | apply Z.le_max_l].
    - lia.
    - apply uptd_ext_refl.
    - rewrite cr_upd_id. iExact "Hpriv".
    - rewrite /cr_rest. iFrame "Q7 Q10 Q11 Q12".
  Qed.

End ProofConsoleread.

End ConsolereadProof.
