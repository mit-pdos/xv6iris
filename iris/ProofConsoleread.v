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

   WHAT IS STILL OWED here is the body: the wait loop at +0x38 (an iLöb --
   nothing bounds how long a line takes to arrive), the outer copy loop, and
   the [^D] / ['\n'] early breaks.  claude-notes/projects/console.md has the
   plan and what differs from piperead. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvExec.
Require Import RegFile.
Require Import InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import StackOwn StackBytes.
Require Import RiscvTryStep.
Require Import ExecCommon WpGpr.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import W32Arith.
Require Import IntrDefs WpSmodeIntr.
Require Import HartTp WpNext.
Require Import WpLock ProcGeom CpuOwn KernelRvcDecode.
Require Import KallocInv.
Require Import UserPtTree KvmSpec ProcPtOwn.
Require Import FdSlots ProcInv FileInvDefs.
Require Import ConsoleInv.
Require Import SpecPanic SchedCtx.
Require Import CodeConsoleread.
Require Import SpecConsoleread.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

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
  intro H. unfold pa_stk, add_vec_int. rewrite po_addv_assoc H. reflexivity.
Qed.


Local Ltac reg_neq :=
  lazymatch goal with |- ?a <> ?b =>
    tryif unify a b then fail else (vm_compute; discriminate) end.
Local Ltac nz := vm_compute; discriminate.
Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.

Section CrBodies.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ, !kallocG Σ}.
  Context `{GEN : RiscvLang.GenId}.

  Notation Rra  := (mword_of_int 1  : mword 5).
  Notation Rs0  := (mword_of_int 8  : mword 5).
  Notation Rs1  := (mword_of_int 9  : mword 5).
  Notation Ra0  := (mword_of_int 10 : mword 5).
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

  Local Ltac rgne :=
    rewrite rget_ne;
    [ | let H1 := fresh in let H2 := fresh in
        intro H1; injection H1 as H2; vm_compute in H2; congruence ].

  (* ---- the frame, in two pieces ------------------------------------ *)

  (* the eight the prologue saves unconditionally *)
  Definition cr_saved (sp0 : mword 64) (m0 : regfile) : iProp Σ :=
    (pa_stk sp0 1 ↦₈ (m0 !!! Regidx Rra) ∗
     pa_stk sp0 2 ↦₈ (m0 !!! Regidx Rs0) ∗
     pa_stk sp0 3 ↦₈ (m0 !!! Regidx Rs1) ∗
     pa_stk sp0 4 ↦₈ (m0 !!! Regidx Rs2) ∗
     pa_stk sp0 5 ↦₈ (m0 !!! Regidx Rs3) ∗
     pa_stk sp0 6 ↦₈ (m0 !!! Regidx Rs4) ∗
     pa_stk sp0 8 ↦₈ (m0 !!! Regidx Rs6) ∗
     pa_stk sp0 9 ↦₈ (m0 !!! Regidx Rs7))%I.

  (* slot 7 (s5's shrink-wrap) and the three local slots, contents free.
     [cbuf] lives in slot 11 and is written by the [sb] at +0x9a, so the
     locals are carried as WORDS everywhere except across that store. *)
  Definition cr_rest (sp0 : mword 64) : iProp Σ :=
    ((∃ w : mword 64, pa_stk sp0 7  ↦₈ w) ∗
     (∃ w : mword 64, pa_stk sp0 10 ↦₈ w) ∗
     (∃ w : mword 64, pa_stk sp0 11 ↦₈ w) ∗
     (∃ w : mword 64, pa_stk sp0 12 ↦₈ w))%I.

  Lemma cr_frame_back (sp0 : mword 64) (m0 : regfile) :
    cr_saved sp0 m0 -∗ cr_rest sp0 -∗ stack_own sp0 12.
  Proof.
    iIntros "(H1 & H2 & H3 & H4 & H5 & H6 & H8 & H9) (H7 & H10 & H11 & H12)".
    rewrite stack_own_slots. cbn [seq].
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
      (eb : bool) (C : iProp Σ) (pid : mword 32) (V : pprivate) (n : Z) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr jp) (fun (CID : CpuId) =>
       ∀ (mf : regfile) (r : Z) (P' : uptd),
         ⌜callee_saved m0 mf⌝ -∗
         ⌜uptd_ext (pv_upt V) P'⌝ -∗
         ⌜(-1 <= r <= Z.max 0 n)%Z⌝ -∗
         ⌜mf !!! Regidx Ra0 = (mword_of_int r : mword 64)⌝ -∗
         sie_cap_gpr mf av true (proc_addr jp) -∗
         cpu_own 0%nat eb (proc_addr jp) C true -∗
         pc_is (ret_pc (m0 !!! Regidx Rra)) -∗
         proc_priv_core (proc_addr jp) pid (upd_upt V P') -∗
         WP (Loop : expr riscv_lang)))%I.

  (* =================================================================== *)
  (*  +0xce .. +0xe0 -- THE EPILOGUE.  All three exits reach it with the  *)
  (*  answer already in a0.                                               *)
  (* =================================================================== *)
  Lemma cr_epi `{CID : CpuId} (CID0 : CPU)
      (jp : nat) (m0 M : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (sp0 : mword 64) (pid : mword 32) (V : pprivate) (n r : Z) :
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
    sie_cap_gpr M (av - 12)%nat true pj -∗
    cpu_own 0%nat eb pj C true -∗
    pc_is (mword_of_int (CR + 0xce)) -∗
    proc_priv_core pj pid V -∗
    cr_saved sp0 m0 -∗ cr_rest sp0 -∗
    cr_ret (CID0 := CID0) jp m0 av eb C pid V n -∗
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
    { rewrite HE8sp. unfold pa_stk, add_vec_int. rewrite po_addv_assoc.
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
    assert (Havx : (av - 12 + 12)%nat = av) by (unfold consoleread_stack in Hav; lia).
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
    iDestruct (cpu_own_transport CID CIDr 0%nat eb pj C true ltac:(wp_next_chain)
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

End CrBodies.
