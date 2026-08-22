(* ProofConsolewrite.v -- the whole-function WP for xv6's consolewrite().

     int consolewrite(int user_src, uint64 src, int n)
     {
       char buf[32];
       int i = 0;
       while (i < n) {
         int nn = sizeof(buf);
         if (nn > n - i) nn = n - i;
         if (either_copyin(buf, user_src, src + i, nn) == -1) break;
         uartwrite(buf, nn);
         i += nn;
       }
       return i;
     }

   Seventy-one instructions; the contract is SpecConsolewrite.v, the decode
   layer CodeConsolewrite.v.  A CHUNKED COPY LOOP -- filewrite's shape one
   tier down -- and the three things worth knowing before reading it:

   - THE BOUNCE BUFFER IS THE FRAME'S FOUR LOWEST SLOTS.  [buf] is [s0-128],
     which is the pushed sp itself, so it is slots 16..13 of a sixteen-slot
     frame.  [StackBytes.slotsn_bytes_own (KTR := KT1)] carves them into 32 bytes at the
     prologue and [bytes_own_slotsn (KTR := KT1)] puts them back before the pop; in
     between the loop owns [bytes_own], contents unspecified, and each
     iteration NAMES the first [nn] of them ([StackBytes.bytes_own_name (KTR := KT1)])
     because both callees are parametric in the contents.  The naming has to
     happen per iteration rather than once, since [nn] varies.
   - THE LOOP IS ROTATED.  The head is the TEST at +0x5e ([n - i], then the
     [min] with 32); the body starts at +0x38 and is reached from BOTH arms
     of the [min] ([bge s9,a5] taken at +0x64, and the [c.j] at +0x6a), so
     +0x38 is a join and is offered as an iAssert'ed continuation.  The back
     edge is +0x5a's fall-through.  Termination is [n - i], which each turn
     decreases by [nn >= 1]: ordinary induction on a fuel [mrem] bounding it.
   - NOTHING LINEAR CROSSES THE BACK EDGE except the frame and the process
     block.  uartwrite parks, so every leaf yields a fresh hart and
     [cpu_own_transport] moves the nesting level before each callee; both
     credentials ([dev_inv], [is_txlock]) and [kalloc_env] are persistent.

   THE EPILOGUE IS SHARED BY THREE PATHS -- the [n <= 0] exit at +0x80 (which
   sets [i] to 0), the loop exit at +0x6c and the copy-failed exit at +0x84 --
   so [cw_epi] is a lemma at +0x96, and the two nine-load restore runs are
   one lemma ([cw_restore]) applied at two addresses. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import InstrBytes WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import KernelText.
Require Import StackOwn StackBytes CalleeSaved.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import W32Arith.
Require Import IntrDefs WpSmodeIntr.
Require Import HartTp WpNext.
Require Import WpLock ProcGeom CpuOwn.
Require Import UserPtTree KvmSpec ProcPtOwn.
Require Import FdSlots ProcInv.
Require Import FileInvDefs.
Require Import DiskPtsto WpUart UartTxInv.
Require Import SchedCtx.
Require Import SpecEitherCopyin SpecUartwrite.
Require Import CodeConsolewrite.
Require Import SpecConsolewrite.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)

Import Defs.
Local Open Scope Z_scope.

(* MANDATORY IN ANY FILE THAT PROVES OVER [proc_priv] (durable-notes.md): a
   goal at this altitude carries [ProcInv.tf_page]'s 4096-conjunct big-op, and
   Rocq prints the WHOLE goal with any tactic error -- tens of minutes of
   formatting for a one-line mistake, which reads as an infinite loop. *)
Set Printing Depth 40.

Notation CW := KernelSyms.consolewrite (only parsing).

(* ===================================================================== *)
(*  Pure facts.  The 32-bit ALU laws live in W32Arith.v.                  *)
(* ===================================================================== *)

(* THE FRAME IS SIXTEEN SLOTS ([c.addi16sp sp,-128] at +0x00).  A
   [c.sdsp]/[c.ldsp] displacement off the pushed sp names slot [16 - imm6]
   counted down from the ENTRY sp; slots 16..13 are [buf]. *)
Lemma cw_slot_bridge (X : mword 64) (o : mword 64) (k : nat) :
  add_vec (mword_of_int (- (8 * Z.of_nat 16%nat))) o = mword_of_int (- (8 * Z.of_nat k)) ->
  add_vec (pa_stk X 16%nat) o = pa_stk X k.
Proof.
  intro H. unfold pa_stk, add_vec_int. rewrite add_vec_assoc H. reflexivity.
Qed.

(* the [beq a0,s8] at +0x4a, against the [-1] gcc parked in s8 *)
Lemma cw_eqv_m1_0 :
  eq_vec (mword_of_int 0 : mword 64) (mword_of_int (-1) : mword 64) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma cw_eqv_m1_m1 :
  eq_vec (mword_of_int (-1) : mword 64) (mword_of_int (-1) : mword 64) = true.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)

Module ConsolewriteProof (EitherCopyin : EITHER_COPYIN)
                         (Uartwrite : UARTWRITE) : CONSOLEWRITE.

Local Ltac reg_neq :=
  lazymatch goal with |- ?a <> ?b =>
    tryif unify a b then fail else (vm_compute; discriminate) end.
Local Ltac nz := vm_compute; discriminate.
Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.

Section CwBodies.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ}.
  Context `{GEN : RiscvLang.GenId}.

  Notation Rra  := (mword_of_int 1  : mword 5).
  Notation Rs0  := (mword_of_int 8  : mword 5).
  Notation Rs1  := (mword_of_int 9  : mword 5).
  Notation Ra0  := (mword_of_int 10 : mword 5).
  Notation Ra1  := (mword_of_int 11 : mword 5).
  Notation Ra2  := (mword_of_int 12 : mword 5).
  Notation Ra3  := (mword_of_int 13 : mword 5).
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

  (* [rget m k] at a NON-tp index is the plain map lookup ([rget_ne]). *)
  Local Ltac rgne :=
    rewrite rget_ne;
    [ | let H1 := fresh in let H2 := fresh in
        intro H1; injection H1 as H2; vm_compute in H2; congruence ].

  (* ---- the frame, in three pieces ---------------------------------- *)

  (* ra / s0 / s1, saved unconditionally by the prologue *)
  Definition cw_saved (sp0 : mword 64) (m0 : regfile) : iProp Σ :=
    (pa_stk sp0 1 ↦₈[KT1] (m0 !!! Regidx Rra) ∗
     pa_stk sp0 2 ↦₈[KT1] (m0 !!! Regidx Rs0) ∗
     pa_stk sp0 3 ↦₈[KT1] (m0 !!! Regidx Rs1))%I.

  (* s2..s10, saved only on the [n > 0] path (slots 4..12) *)
  Definition cw_spill (sp0 : mword 64) (m0 : regfile) : iProp Σ :=
    (pa_stk sp0 4  ↦₈[KT1] (m0 !!! Regidx Rs2) ∗
     pa_stk sp0 5  ↦₈[KT1] (m0 !!! Regidx Rs3) ∗
     pa_stk sp0 6  ↦₈[KT1] (m0 !!! Regidx Rs4) ∗
     pa_stk sp0 7  ↦₈[KT1] (m0 !!! Regidx Rs5) ∗
     pa_stk sp0 8  ↦₈[KT1] (m0 !!! Regidx Rs6) ∗
     pa_stk sp0 9  ↦₈[KT1] (m0 !!! Regidx Rs7) ∗
     pa_stk sp0 10 ↦₈[KT1] (m0 !!! Regidx Rs8) ∗
     pa_stk sp0 11 ↦₈[KT1] (m0 !!! Regidx Rs9) ∗
     pa_stk sp0 12 ↦₈[KT1] (m0 !!! Regidx Rs10))%I.

  (* everything below the three unconditional saves, as WORDS -- what the
     pop needs.  Slots 4..16. *)
  Definition cw_rest (sp0 : mword 64) : iProp Σ :=
    ([∗ list] k ∈ seq 4 13, ∃ w : mword 64, pa_stk sp0 k ↦₈[KT1] w)%I.

  (* ...and the same region with its four lowest slots carved into bytes *)
  Definition cw_buf (sp0 : mword 64) : iProp Σ :=
    bytes_own (KTR := KT1) (DfracOwn 1) (pa_stk sp0 16) 32.

  Lemma cw_frame_back (sp0 : mword 64) (m0 : regfile) :
    cw_saved sp0 m0 -∗ cw_rest sp0 -∗ stack_own (KTR := KT1) sp0 16.
  Proof.
    iIntros "(H1 & H2 & H3) Hr".
    rewrite (stack_own_slots (KTR := KT1)) /cw_rest.
    change (seq 1 16) with ((seq 1 3 ++ seq 4 13)%list).
    rewrite big_sepL_app. iSplitR "Hr"; [| iExact "Hr"].
    cbn [seq]. iSplitL "H1"; [by iExists _|].
    iSplitL "H2"; [by iExists _|]. iSplitL "H3"; [by iExists _|]. done.
  Qed.

  (* the four buffer slots, as words again -- run BEFORE the epilogue.  The
     alignment facts are the ones the prologue's carve handed out. *)
  Lemma cw_buf_slots (sp0 : mword 64) :
    (forall i, (i < 4)%nat -> is_aligned_paddr (Physaddr (pa_stk sp0 (16 - i))) 8 = true) ->
    cw_buf sp0 ⊢ [∗ list] i ∈ seq 0 4, ∃ w : mword 64, pa_stk sp0 (16 - i) ↦₈[KT1] w.
  Proof.
    intro Hal. rewrite /cw_buf.
    change 32%nat with (8 * 4)%nat.
    iApply (bytes_own_slotsn (KTR := KT1) sp0 16 4 ltac:(lia) Hal).
  Qed.

  (* ---- the register shape the loop maintains ----------------------- *)

  Definition cw_regs (M : regfile) (spd sp0 src : mword 64) (n i : Z) : Prop :=
    M !!! Regidx csp_rs1 = spd
    /\ M !!! Regidx Rs0   = sp0
    /\ M !!! Regidx Rs1   = (mword_of_int i : mword 64)
    /\ M !!! Regidx Rs4   = (mword_of_int n : mword 64)
    /\ M !!! Regidx Rs5   = spd
    /\ M !!! Regidx Rs6   = (mword_of_int 1 : mword 64)
    /\ M !!! Regidx Rs7   = src
    /\ M !!! Regidx Rs8   = (mword_of_int (-1) : mword 64)
    /\ M !!! Regidx Rs9   = (mword_of_int 32 : mword 64)
    /\ M !!! Regidx Rs10  = (mword_of_int 32 : mword 64).

  Lemma cw_regs_cs (M M' : regfile) spd sp0 src n i :
    callee_saved M M' -> cw_regs M spd sp0 src n i -> cw_regs M' spd sp0 src n i.
  Proof.
    intros Hcs (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    unfold cw_regs.
    rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)).
    rewrite (callee_saved_lookup Hcs Rs0 ltac:(vm_compute; reflexivity)).
    rewrite (callee_saved_lookup Hcs Rs1 ltac:(vm_compute; reflexivity)).
    rewrite (callee_saved_lookup Hcs Rs4 ltac:(vm_compute; reflexivity)).
    rewrite (callee_saved_lookup Hcs Rs5 ltac:(vm_compute; reflexivity)).
    rewrite (callee_saved_lookup Hcs Rs6 ltac:(vm_compute; reflexivity)).
    rewrite (callee_saved_lookup Hcs Rs7 ltac:(vm_compute; reflexivity)).
    rewrite (callee_saved_lookup Hcs Rs8 ltac:(vm_compute; reflexivity)).
    rewrite (callee_saved_lookup Hcs Rs9 ltac:(vm_compute; reflexivity)).
    rewrite (callee_saved_lookup Hcs Rs10 ltac:(vm_compute; reflexivity)).
    split_and!; assumption.
  Qed.

  (* the nine restored registers plus the one the function never touches.
     TEN EQUATIONS RATHER THAN A [forall c, is_cs_idx c = true -> ...]: the
     restores SET s2..s10, so a quantified statement would have to case-split
     on the thirteen callee-saved indices, while the epilogue only ever needs
     to transport each one through an insert tower whose keys are literals --
     which [upd_ne] does in one step per level. *)
  Definition cw_cs_hi (M m0 : regfile) : Prop :=
    M !!! Regidx Rs2  = m0 !!! Regidx Rs2
    /\ M !!! Regidx Rs3  = m0 !!! Regidx Rs3
    /\ M !!! Regidx Rs4  = m0 !!! Regidx Rs4
    /\ M !!! Regidx Rs5  = m0 !!! Regidx Rs5
    /\ M !!! Regidx Rs6  = m0 !!! Regidx Rs6
    /\ M !!! Regidx Rs7  = m0 !!! Regidx Rs7
    /\ M !!! Regidx Rs8  = m0 !!! Regidx Rs8
    /\ M !!! Regidx Rs9  = m0 !!! Regidx Rs9
    /\ M !!! Regidx Rs10 = m0 !!! Regidx Rs10
    /\ M !!! Regidx Rs11 = m0 !!! Regidx Rs11.

  (* uartwrite wants the pid CELL and gives it back; [proc_priv_core] is
     where a caller at this altitude has one. *)
  (* NO BARE [iFrame] AND NO DESTRUCTURING OF THE TAIL.  The tail conjunct
     is [ProcInv.tf_page], a 4096-conjunct big-op, and an unnamed [iFrame]
     against it does not terminate in any useful time (measured: > 2 min on
     this one line, with nothing else in the context).  Keeping the tail as
     ONE hypothesis makes the rebuild an [iExact] -- a syntactic check. *)
  Lemma cw_priv_pid (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv_core pa pid V ⊢
    p_pid pa ↦₄{DfracOwn (1/2)} pid ∗
    (p_pid pa ↦₄{DfracOwn (1/2)} pid -∗ proc_priv_core pa pid V).
  Proof.
    rewrite /proc_priv_core.
    iIntros "(%H1 & %H2 & Hpid & Hrest)".
    iSplitL "Hpid"; [iExact "Hpid"|].
    iIntros "Hpid".
    iSplitR; [done|]. iSplitR; [done|].
    iSplitL "Hpid"; [iExact "Hpid"|]. iExact "Hrest".
  Qed.

  (* ---- the function's own exit, as a [wp_next] at the entry hart ---- *)

  Definition cw_ret `{CID0 : CpuId} (jp : nat) (m0 : regfile) (av : nat)
      (eb : bool) (pid : mword 32) (V : pprivate) (n : Z) (lks : gset string) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr jp) (fun (CID : CpuId) =>
       ∀ (mf : regfile) (r : Z) (P' : uptd),
         ⌜callee_saved m0 mf⌝ -∗
         ⌜uptd_ext (pv_upt V) P'⌝ -∗
         ⌜(0 <= r <= Z.max 0 n)%Z⌝ -∗
         ⌜mf !!! Regidx Ra0 = (mword_of_int r : mword 64)⌝ -∗
         sie_cap_gpr KT1 mf av true (proc_addr jp) -∗
         cpu_own 0%nat eb (proc_addr jp) true lks -∗
         pc_is (ret_pc (m0 !!! Regidx Rra)) -∗
         proc_priv_core (proc_addr jp) pid (upd_upt V P') -∗
         WP (Loop : expr riscv_lang)))%I.

  (* the loop re-enters its own continuation at a MOVED descriptor; both the
     extension and the record compose, so the exit weakens along the loop. *)
  Lemma cw_ret_weaken `{CID0 : CpuId} (jp : nat) (m0 : regfile) (av : nat)
      (eb : bool) (pid : mword 32) (V : pprivate) (P1 : uptd) (n : Z) (lks : gset string) :
    uptd_ext (pv_upt V) P1 ->
    cw_ret (CID0 := CID0) jp m0 av eb pid V n lks -∗
    cw_ret (CID0 := CID0) jp m0 av eb pid (upd_upt V P1) n lks.
  Proof.
    intro Hext. rewrite /cw_ret /wp_next.
    iIntros "H" (CID) "%Hg".
    iSpecialize ("H" $! CID with "[%]"); [exact Hg|].
    iIntros (mf r P') "%Hcs %Hx %Hr %Ha0".
    iApply ("H" $! mf r P' with "[%] [%] [%] [%]").
    - exact Hcs.
    - exact (uptd_ext_trans _ _ _ Hext Hx).
    - exact Hr.
    - exact Ha0.
  Qed.

  (* =================================================================== *)
  (*  +0x96 .. +0xa0 -- THE EPILOGUE.  All three exits reach it.          *)
  (* =================================================================== *)
  Lemma cw_epi `{CID : CpuId} (CID0 : CPU)
      (jp : nat) (m0 M : regfile) (av : nat) (eb : bool)
      (sp0 : mword 64) (pid : mword 32) (V : pprivate) (n r : Z) (lks : gset string) :
    let pj := proc_addr jp in
    m0 !!! Regidx csp_rs1 = sp0 ->
    M !!! Regidx csp_rs1 = pa_stk sp0 16%nat ->
    M !!! Regidx Rs1 = (mword_of_int r : mword 64) ->
    cw_cs_hi M m0 ->
    (0 <= r <= Z.max 0 n)%Z ->
    (consolewrite_stack <= av)%nat ->
    eb = true ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    kernel_text -∗
    sie_cap_gpr KT1 M (av - 16)%nat true pj -∗
    cpu_own 0%nat eb pj true lks -∗
    pc_is (mword_of_int (CW + 0x96)) -∗
    proc_priv_core pj pid V -∗
    cw_saved sp0 m0 -∗ cw_rest sp0 -∗
    cw_ret (CID0 := CID0) jp m0 av eb pid V n lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj Hm0sp HMsp HMs1 HMcs Hr Hav Heb Hcr.
    iIntros "#Ht Hcg Hcnt Hpc Hpriv (Hk1 & Hk2 & Hk3) Hrest Hcont".
    assert (Hb1 : add_vec (pa_stk sp0 16%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (apply cw_slot_bridge; pcw).
    assert (Hb2 : add_vec (pa_stk sp0 16%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (apply cw_slot_bridge; pcw).
    assert (Hb3 : add_vec (pa_stk sp0 16%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (apply cw_slot_bridge; pcw).
    (* ---- +0x96  c.mv a0,s1 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (CW + 0x96)) Ra0 Rs1
              M (av - 16)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnwi_96 with "Ht"). }
    iIntros (CID1 Hs1) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (E1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M !!! Regidx Rs1))]> M).
    change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M !!! Regidx Rs1))]> M) with E1.
    assert (HE1a0 : E1 !!! Regidx Ra0 = (mword_of_int r : mword 64))
      by (rewrite /E1 upd_eq w32_zero_add; exact HMs1).
    assert (HE1sp : E1 !!! Regidx csp_rs1 = pa_stk sp0 16%nat)
      by (rewrite /E1 upd_ne; [exact HMsp | reg_neq]).
    assert (P98 : add_vec_int (mword_of_int (CW + 0x96) : mword 64) 2
                  = mword_of_int (CW + 0x98)) by pcw.
    iEval (rewrite P98) in "Hpc".
    (* ---- +0x98  c.ldsp ra,120(sp) ---- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CW + 0x98)) (mword_of_int 15 : mword 6) Rra
              E1 (av - 16)%nat (m0 !!! Regidx Rra) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hk1]").
    { iApply (cnwi_98 with "Ht"). }
    { iEval (rewrite HE1sp Hb1). iExact "Hk1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hk1". iEval (rewrite HE1sp Hb1) in "Hk1".
    set (E2 := <[Regidx Rra := regval_into_reg (m0 !!! Regidx Rra)]> E1).
    change (<[Regidx Rra := regval_into_reg (m0 !!! Regidx Rra)]> E1) with E2.
    assert (HE2sp : E2 !!! Regidx csp_rs1 = pa_stk sp0 16%nat)
      by (rewrite /E2 upd_ne; [exact HE1sp | reg_neq]).
    assert (P9a : add_vec_int (mword_of_int (CW + 0x98) : mword 64) 2
                  = mword_of_int (CW + 0x9a)) by pcw.
    iEval (rewrite P9a) in "Hpc".
    (* ---- +0x9a  c.ldsp s0,112(sp) ---- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CW + 0x9a)) (mword_of_int 14 : mword 6) Rs0
              E2 (av - 16)%nat (m0 !!! Regidx Rs0) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hk2]").
    { iApply (cnwi_9a with "Ht"). }
    { iEval (rewrite HE2sp Hb2). iExact "Hk2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hk2". iEval (rewrite HE2sp Hb2) in "Hk2".
    set (E3 := <[Regidx Rs0 := regval_into_reg (m0 !!! Regidx Rs0)]> E2).
    change (<[Regidx Rs0 := regval_into_reg (m0 !!! Regidx Rs0)]> E2) with E3.
    assert (HE3sp : E3 !!! Regidx csp_rs1 = pa_stk sp0 16%nat)
      by (rewrite /E3 upd_ne; [exact HE2sp | reg_neq]).
    assert (P9c : add_vec_int (mword_of_int (CW + 0x9a) : mword 64) 2
                  = mword_of_int (CW + 0x9c)) by pcw.
    iEval (rewrite P9c) in "Hpc".
    (* ---- +0x9c  c.ldsp s1,104(sp) ---- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CW + 0x9c)) (mword_of_int 13 : mword 6) Rs1
              E3 (av - 16)%nat (m0 !!! Regidx Rs1) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hk3]").
    { iApply (cnwi_9c with "Ht"). }
    { iEval (rewrite HE3sp Hb3). iExact "Hk3". }
    iIntros (CID4 Hs4) "Hcg Hpc Hk3". iEval (rewrite HE3sp Hb3) in "Hk3".
    set (E4 := <[Regidx Rs1 := regval_into_reg (m0 !!! Regidx Rs1)]> E3).
    change (<[Regidx Rs1 := regval_into_reg (m0 !!! Regidx Rs1)]> E3) with E4.
    assert (HE4sp : E4 !!! Regidx csp_rs1 = pa_stk sp0 16%nat)
      by (rewrite /E4 upd_ne; [exact HE3sp | reg_neq]).
    assert (P9e : add_vec_int (mword_of_int (CW + 0x9c) : mword 64) 2
                  = mword_of_int (CW + 0x9e)) by pcw.
    iEval (rewrite P9e) in "Hpc".
    (* ---- +0x9e  c.addi16sp sp,+128 : the pop ---- *)
    assert (Hspv : add_vec (E4 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 8 : mword 6))) = sp0).
    { rewrite HE4sp. unfold pa_stk, add_vec_int. rewrite add_vec_assoc.
      rewrite (_ : add_vec (mword_of_int (- (8 * Z.of_nat 16%nat)) : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 8 : mword 6)))
                   = (mword_of_int 0 : mword 64)); [| pcw].
      apply bv_add_0_r. vm_compute. reflexivity. }
    assert (Hpop : E4 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E4 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 8 : mword 6)))) 16%nat)
      by (rewrite Hspv HE4sp; reflexivity).
    iDestruct (cw_frame_back sp0 m0 with "[Hk1 Hk2 Hk3] Hrest") as "Hframe".
    { rewrite /cw_saved. iFrame "Hk1 Hk2 Hk3". }
    iEval (rewrite -Hspv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (CW + 0x9e)) (mword_of_int 8 : mword 6)
              E4 (av - 16)%nat 16%nat true Hpop with "Hcg Hpc [] Hframe").
    { iApply (cnwi_9e with "Ht"). }
    iIntros (CID5 Hs5) "Hcg Hpc".
    assert (Havx : (av - 16 + 16)%nat = av) by (lia).
    iEval (rewrite Havx) in "Hcg".
    set (E5 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E4 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 8 : mword 6))))]> E4).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E4 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 8 : mword 6))))]> E4) with E5.
    assert (Pa0 : add_vec_int (mword_of_int (CW + 0x9e) : mword 64) 2
                  = mword_of_int (CW + 0xa0)) by pcw.
    iEval (rewrite Pa0) in "Hpc".
    (* ---- +0xa0  c.ret ---- *)
    iApply (wp_cret_s_sconf (mword_of_int (CW + 0xa0)) Rra E5 av true
              ltac:(nz) with "Hcg Hpc []").
    { iApply (cnwi_a0 with "Ht"). }
    iIntros (CID6 Hs6) "Hcg Hpc". iEval (rgne) in "Hpc".
    assert (HE5ra : E5 !!! Regidx Rra = m0 !!! Regidx Rra).
    { rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq].
      rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_eq. reflexivity. }
    iEval (rewrite HE5ra) in "Hpc".
    assert (HE5a0 : E5 !!! Regidx Ra0 = (mword_of_int r : mword 64)).
    { rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq].
      rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq].
      exact HE1a0. }
    assert (Hcs : callee_saved m0 E5).
    { unfold callee_saved.
      assert (Hsp : E5 !!! Regidx csp_rs1 = m0 !!! Regidx csp_rs1)
        by (rewrite /E5 upd_eq; unfold regval_into_reg;
            rewrite Hspv; symmetry; exact Hm0sp).
      assert (Hs0v : E5 !!! Regidx Rs0 = m0 !!! Regidx Rs0).
      { rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq].
        rewrite /E3 upd_eq. reflexivity. }
      assert (Hs1v : E5 !!! Regidx Rs1 = m0 !!! Regidx Rs1).
      { rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_eq. reflexivity. }
      assert (Hoth : forall c : mword 5, c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
                       c <> Ra0 -> c <> Rra -> E5 !!! Regidx c = M !!! Regidx c).
      { intros c N1 N2 N3 N4 N5.
        rewrite /E5 upd_ne; [| reg_ne_side].
        rewrite /E4 upd_ne; [| reg_ne_side].
        rewrite /E3 upd_ne; [| reg_ne_side].
        rewrite /E2 upd_ne; [| reg_ne_side]. rewrite /E1 upd_ne; [| reg_ne_side].
        reflexivity. }
      destruct HMcs as (K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11).
      split_and!;
        first [ exact Hsp | exact Hs0v | exact Hs1v
              | rewrite Hoth; [ first [exact K2|exact K3|exact K4|exact K5|exact K6
                                      |exact K7|exact K8|exact K9|exact K10|exact K11]
                              | reg_neq | reg_neq | reg_neq | reg_neq | reg_neq ] ]. }
    iDestruct (cpu_own_transport CID CID6 0%nat eb pj true ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    rewrite /cw_ret.
    iSpecialize ("Hcont" $! CID6 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E5 r (pv_upt V) with "[%] [%] [%] [%] Hcg Hcnt Hpc [Hpriv]").
    - exact Hcs.
    - apply uptd_ext_refl.
    - exact Hr.
    - exact HE5a0.
    - (* [upd_upt V (pv_upt V)] is [V] only once the record is a constructor
         application, so destructure it: eta for records is not definitional
         here. *)
      destruct V as [vsz vupt vtf vofl vcwd vnm]. iExact "Hpriv".
  Qed.

  (* the whole of what the pop needs: the nine spill slots plus the four the
     buffer was carved out of, in slot order. *)
  Lemma cw_rest_of (sp0 : mword 64) (m0 : regfile) :
    (forall i, (i < 4)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (16 - i))) 8 = true) ->
    cw_spill sp0 m0 -∗ cw_buf sp0 -∗ cw_rest sp0.
  Proof.
    intro Hal. iIntros "Hsp Hbuf".
    iDestruct (cw_buf_slots sp0 Hal with "Hbuf") as "Hb".
    rewrite /cw_rest /cw_spill.
    iDestruct "Hsp" as "(H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12)".
    cbn [seq]. iDestruct "Hb" as "(B16 & B15 & B14 & B13 & _)".
    iSplitL "H4";  [by iExists _|]. iSplitL "H5";  [by iExists _|].
    iSplitL "H6";  [by iExists _|]. iSplitL "H7";  [by iExists _|].
    iSplitL "H8";  [by iExists _|]. iSplitL "H9";  [by iExists _|].
    iSplitL "H10"; [by iExists _|]. iSplitL "H11"; [by iExists _|].
    iSplitL "H12"; [by iExists _|].
    iSplitL "B13"; [iExact "B13"|]. iSplitL "B14"; [iExact "B14"|].
    iSplitL "B15"; [iExact "B15"|]. iSplitL "B16"; [iExact "B16"|]. done.
  Qed.

  (* =================================================================== *)
  (*  +0x6c .. +0x7e -- THE LOOP EXIT: i = n, restore s2..s10 and jump    *)
  (* =================================================================== *)
  Lemma cw_exit_done `{CID : CpuId} (CID0 : CPU)
      (jp : nat) (m0 M : regfile) (av : nat) (eb : bool)
      (sp0 : mword 64) (pid : mword 32) (V : pprivate) (n r : Z) (lks : gset string) :
    let pj := proc_addr jp in
    m0 !!! Regidx csp_rs1 = sp0 ->
    M !!! Regidx csp_rs1 = pa_stk sp0 16%nat ->
    M !!! Regidx Rs1 = (mword_of_int r : mword 64) ->
    M !!! Regidx Rs11 = m0 !!! Regidx Rs11 ->
    (0 <= r <= Z.max 0 n)%Z ->
    (consolewrite_stack <= av)%nat ->
    eb = true ->
    (forall i, (i < 4)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (16 - i))) 8 = true) ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    kernel_text -∗
    sie_cap_gpr KT1 M (av - 16)%nat true pj -∗
    cpu_own 0%nat eb pj true lks -∗
    pc_is (mword_of_int (CW + 0x6c)) -∗
    proc_priv_core pj pid V -∗
    cw_saved sp0 m0 -∗ cw_spill sp0 m0 -∗ cw_buf sp0 -∗
    cw_ret (CID0 := CID0) jp m0 av eb pid V n lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj Hm0sp HMsp HMs1 HMs11 Hr Hav Heb Hal Hcr.
    iIntros "#Ht Hcg Hcnt Hpc Hpriv Hsaved Hspill Hbuf Hcont".
    rewrite /cw_spill.
    iDestruct "Hspill" as "(S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12)".
    assert (Hb4 : add_vec (pa_stk sp0 16%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (apply cw_slot_bridge; pcw).
    assert (Hb5 : add_vec (pa_stk sp0 16%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (apply cw_slot_bridge; pcw).
    assert (Hb6 : add_vec (pa_stk sp0 16%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))
                  = pa_stk sp0 6) by (apply cw_slot_bridge; pcw).
    assert (Hb7 : add_vec (pa_stk sp0 16%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk sp0 7) by (apply cw_slot_bridge; pcw).
    assert (Hb8 : add_vec (pa_stk sp0 16%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk sp0 8) by (apply cw_slot_bridge; pcw).
    assert (Hb9 : add_vec (pa_stk sp0 16%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk sp0 9) by (apply cw_slot_bridge; pcw).
    assert (Hb10 : add_vec (pa_stk sp0 16%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk sp0 10) by (apply cw_slot_bridge; pcw).
    assert (Hb11 : add_vec (pa_stk sp0 16%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 11) by (apply cw_slot_bridge; pcw).
    assert (Hb12 : add_vec (pa_stk sp0 16%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 12) by (apply cw_slot_bridge; pcw).

    (* +0x6c  c.ldsp rs2,96(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CW + 0x6c)) (mword_of_int 12 : mword 6) Rs2
              M (av - 16)%nat (m0 !!! Regidx Rs2) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [S4]").
    { iApply (cnwi_6c with "Ht"). }
    { iEval (rewrite HMsp Hb4). iExact "S4". }
    iIntros (CIDl0 Hsl0) "Hcg Hpc S4".
    iEval (rewrite HMsp Hb4) in "S4".
    set (R0 := <[Regidx Rs2 := regval_into_reg (m0 !!! Regidx Rs2)]> M).
    change (<[Regidx Rs2 := regval_into_reg (m0 !!! Regidx Rs2)]> M) with R0.
    assert (HR0sp : R0 !!! Regidx csp_rs1 = pa_stk sp0 16%nat)
      by (rewrite /R0 upd_ne; [exact HMsp | reg_neq]).
    assert (Pq6e : add_vec_int (mword_of_int (CW + 0x6c) : mword 64) 2
                  = mword_of_int (CW + 0x6e)) by pcw.
    iEval (rewrite Pq6e) in "Hpc".
    (* +0x6e  c.ldsp rs3,88(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CW + 0x6e)) (mword_of_int 11 : mword 6) Rs3
              R0 (av - 16)%nat (m0 !!! Regidx Rs3) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [S5]").
    { iApply (cnwi_6e with "Ht"). }
    { iEval (rewrite HR0sp Hb5). iExact "S5". }
    iIntros (CIDl1 Hsl1) "Hcg Hpc S5".
    iEval (rewrite HR0sp Hb5) in "S5".
    set (R1 := <[Regidx Rs3 := regval_into_reg (m0 !!! Regidx Rs3)]> R0).
    change (<[Regidx Rs3 := regval_into_reg (m0 !!! Regidx Rs3)]> R0) with R1.
    assert (HR1sp : R1 !!! Regidx csp_rs1 = pa_stk sp0 16%nat)
      by (rewrite /R1 upd_ne; [exact HR0sp | reg_neq]).
    assert (Pq70 : add_vec_int (mword_of_int (CW + 0x6e) : mword 64) 2
                  = mword_of_int (CW + 0x70)) by pcw.
    iEval (rewrite Pq70) in "Hpc".
    (* +0x70  c.ldsp rs4,80(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CW + 0x70)) (mword_of_int 10 : mword 6) Rs4
              R1 (av - 16)%nat (m0 !!! Regidx Rs4) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [S6]").
    { iApply (cnwi_70 with "Ht"). }
    { iEval (rewrite HR1sp Hb6). iExact "S6". }
    iIntros (CIDl2 Hsl2) "Hcg Hpc S6".
    iEval (rewrite HR1sp Hb6) in "S6".
    set (R2 := <[Regidx Rs4 := regval_into_reg (m0 !!! Regidx Rs4)]> R1).
    change (<[Regidx Rs4 := regval_into_reg (m0 !!! Regidx Rs4)]> R1) with R2.
    assert (HR2sp : R2 !!! Regidx csp_rs1 = pa_stk sp0 16%nat)
      by (rewrite /R2 upd_ne; [exact HR1sp | reg_neq]).
    assert (Pq72 : add_vec_int (mword_of_int (CW + 0x70) : mword 64) 2
                  = mword_of_int (CW + 0x72)) by pcw.
    iEval (rewrite Pq72) in "Hpc".
    (* +0x72  c.ldsp rs5,72(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CW + 0x72)) (mword_of_int 9 : mword 6) Rs5
              R2 (av - 16)%nat (m0 !!! Regidx Rs5) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [S7]").
    { iApply (cnwi_72 with "Ht"). }
    { iEval (rewrite HR2sp Hb7). iExact "S7". }
    iIntros (CIDl3 Hsl3) "Hcg Hpc S7".
    iEval (rewrite HR2sp Hb7) in "S7".
    set (R3 := <[Regidx Rs5 := regval_into_reg (m0 !!! Regidx Rs5)]> R2).
    change (<[Regidx Rs5 := regval_into_reg (m0 !!! Regidx Rs5)]> R2) with R3.
    assert (HR3sp : R3 !!! Regidx csp_rs1 = pa_stk sp0 16%nat)
      by (rewrite /R3 upd_ne; [exact HR2sp | reg_neq]).
    assert (Pq74 : add_vec_int (mword_of_int (CW + 0x72) : mword 64) 2
                  = mword_of_int (CW + 0x74)) by pcw.
    iEval (rewrite Pq74) in "Hpc".
    (* +0x74  c.ldsp rs6,64(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CW + 0x74)) (mword_of_int 8 : mword 6) Rs6
              R3 (av - 16)%nat (m0 !!! Regidx Rs6) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [S8]").
    { iApply (cnwi_74 with "Ht"). }
    { iEval (rewrite HR3sp Hb8). iExact "S8". }
    iIntros (CIDl4 Hsl4) "Hcg Hpc S8".
    iEval (rewrite HR3sp Hb8) in "S8".
    set (R4 := <[Regidx Rs6 := regval_into_reg (m0 !!! Regidx Rs6)]> R3).
    change (<[Regidx Rs6 := regval_into_reg (m0 !!! Regidx Rs6)]> R3) with R4.
    assert (HR4sp : R4 !!! Regidx csp_rs1 = pa_stk sp0 16%nat)
      by (rewrite /R4 upd_ne; [exact HR3sp | reg_neq]).
    assert (Pq76 : add_vec_int (mword_of_int (CW + 0x74) : mword 64) 2
                  = mword_of_int (CW + 0x76)) by pcw.
    iEval (rewrite Pq76) in "Hpc".
    (* +0x76  c.ldsp rs7,56(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CW + 0x76)) (mword_of_int 7 : mword 6) Rs7
              R4 (av - 16)%nat (m0 !!! Regidx Rs7) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [S9]").
    { iApply (cnwi_76 with "Ht"). }
    { iEval (rewrite HR4sp Hb9). iExact "S9". }
    iIntros (CIDl5 Hsl5) "Hcg Hpc S9".
    iEval (rewrite HR4sp Hb9) in "S9".
    set (R5 := <[Regidx Rs7 := regval_into_reg (m0 !!! Regidx Rs7)]> R4).
    change (<[Regidx Rs7 := regval_into_reg (m0 !!! Regidx Rs7)]> R4) with R5.
    assert (HR5sp : R5 !!! Regidx csp_rs1 = pa_stk sp0 16%nat)
      by (rewrite /R5 upd_ne; [exact HR4sp | reg_neq]).
    assert (Pq78 : add_vec_int (mword_of_int (CW + 0x76) : mword 64) 2
                  = mword_of_int (CW + 0x78)) by pcw.
    iEval (rewrite Pq78) in "Hpc".
    (* +0x78  c.ldsp rs8,48(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CW + 0x78)) (mword_of_int 6 : mword 6) Rs8
              R5 (av - 16)%nat (m0 !!! Regidx Rs8) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [S10]").
    { iApply (cnwi_78 with "Ht"). }
    { iEval (rewrite HR5sp Hb10). iExact "S10". }
    iIntros (CIDl6 Hsl6) "Hcg Hpc S10".
    iEval (rewrite HR5sp Hb10) in "S10".
    set (R6 := <[Regidx Rs8 := regval_into_reg (m0 !!! Regidx Rs8)]> R5).
    change (<[Regidx Rs8 := regval_into_reg (m0 !!! Regidx Rs8)]> R5) with R6.
    assert (HR6sp : R6 !!! Regidx csp_rs1 = pa_stk sp0 16%nat)
      by (rewrite /R6 upd_ne; [exact HR5sp | reg_neq]).
    assert (Pq7a : add_vec_int (mword_of_int (CW + 0x78) : mword 64) 2
                  = mword_of_int (CW + 0x7a)) by pcw.
    iEval (rewrite Pq7a) in "Hpc".
    (* +0x7a  c.ldsp rs9,40(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CW + 0x7a)) (mword_of_int 5 : mword 6) Rs9
              R6 (av - 16)%nat (m0 !!! Regidx Rs9) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [S11]").
    { iApply (cnwi_7a with "Ht"). }
    { iEval (rewrite HR6sp Hb11). iExact "S11". }
    iIntros (CIDl7 Hsl7) "Hcg Hpc S11".
    iEval (rewrite HR6sp Hb11) in "S11".
    set (R7 := <[Regidx Rs9 := regval_into_reg (m0 !!! Regidx Rs9)]> R6).
    change (<[Regidx Rs9 := regval_into_reg (m0 !!! Regidx Rs9)]> R6) with R7.
    assert (HR7sp : R7 !!! Regidx csp_rs1 = pa_stk sp0 16%nat)
      by (rewrite /R7 upd_ne; [exact HR6sp | reg_neq]).
    assert (Pq7c : add_vec_int (mword_of_int (CW + 0x7a) : mword 64) 2
                  = mword_of_int (CW + 0x7c)) by pcw.
    iEval (rewrite Pq7c) in "Hpc".
    (* +0x7c  c.ldsp rs10,32(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CW + 0x7c)) (mword_of_int 4 : mword 6) Rs10
              R7 (av - 16)%nat (m0 !!! Regidx Rs10) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [S12]").
    { iApply (cnwi_7c with "Ht"). }
    { iEval (rewrite HR7sp Hb12). iExact "S12". }
    iIntros (CIDl8 Hsl8) "Hcg Hpc S12".
    iEval (rewrite HR7sp Hb12) in "S12".
    set (R8 := <[Regidx Rs10 := regval_into_reg (m0 !!! Regidx Rs10)]> R7).
    change (<[Regidx Rs10 := regval_into_reg (m0 !!! Regidx Rs10)]> R7) with R8.
    assert (HR8sp : R8 !!! Regidx csp_rs1 = pa_stk sp0 16%nat)
      by (rewrite /R8 upd_ne; [exact HR7sp | reg_neq]).
    assert (Pq7e : add_vec_int (mword_of_int (CW + 0x7c) : mword 64) 2
                  = mword_of_int (CW + 0x7e)) by pcw.
    iEval (rewrite Pq7e) in "Hpc".
    (* the nine values are back; s11 was never touched *)
    assert (Hhi : cw_cs_hi R8 m0).
    { unfold cw_cs_hi. split_and!;
        first [ rewrite /R8 /R7 /R6 /R5 /R4 /R3 /R2 /R1 /R0;
                repeat (rewrite upd_ne; [| reg_neq]); rewrite upd_eq; reflexivity
              | rewrite /R8 /R7 /R6 /R5 /R4 /R3 /R2 /R1 /R0;
                repeat (rewrite upd_ne; [| reg_neq]); exact HMs11 ]. }
    assert (Hs1v : R8 !!! Regidx Rs1 = (mword_of_int r : mword 64)).
    { rewrite /R8 /R7 /R6 /R5 /R4 /R3 /R2 /R1 /R0.
      repeat (rewrite upd_ne; [| reg_neq]). exact HMs1. }
    (* the four buffer slots become words again, for the pop *)
    iDestruct (cw_rest_of sp0 m0 Hal with "[S4 S5 S6 S7 S8 S9 S10 S11 S12] Hbuf")
      as "Hrest".
    { rewrite /cw_spill. iFrame "S4 S5 S6 S7 S8 S9 S10 S11 S12". }
    (* +0x7e  c.j -> +0x96 *)
    assert (Hjt : add_vec (mword_of_int (CW + 0x7e) : mword 64)
                    (sign_extend' 64 (sign_extend' 21
                       (concat_vec (mword_of_int 12 : mword 11) ('b"0"))))
                  = mword_of_int (CW + 0x96)) by pcw.
    iApply (wp_cj_s_sconf (mword_of_int (CW + 0x7e))
              (sign_extend' 21 (concat_vec (mword_of_int 12 : mword 11) ('b"0")))
              R8 (av - 16)%nat true ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (cnwi_7e with "Ht"). }
    iIntros (CIDj Hsj). iApply bi.later_intro. iIntros "Hcg Hpc".
    iEval (rewrite Hjt) in "Hpc".
    iApply (cw_epi (CID := CIDj) CID0 jp m0 R8 av eb sp0 pid V n r lks
              Hm0sp HR8sp Hs1v Hhi Hr Hav Heb ltac:(wp_next_chain)
              with "Ht Hcg Hcnt Hpc Hpriv Hsaved Hrest Hcont").
  Qed.
  (* =================================================================== *)
  (*  +0x84 .. +0x94 -- THE COPY-FAILED EXIT: restore s2..s10, fall through *)
  (* =================================================================== *)
  Lemma cw_exit_break `{CID : CpuId} (CID0 : CPU)
      (jp : nat) (m0 M : regfile) (av : nat) (eb : bool)
      (sp0 : mword 64) (pid : mword 32) (V : pprivate) (n r : Z) (lks : gset string) :
    let pj := proc_addr jp in
    m0 !!! Regidx csp_rs1 = sp0 ->
    M !!! Regidx csp_rs1 = pa_stk sp0 16%nat ->
    M !!! Regidx Rs1 = (mword_of_int r : mword 64) ->
    M !!! Regidx Rs11 = m0 !!! Regidx Rs11 ->
    (0 <= r <= Z.max 0 n)%Z ->
    (consolewrite_stack <= av)%nat ->
    eb = true ->
    (forall i, (i < 4)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (16 - i))) 8 = true) ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    kernel_text -∗
    sie_cap_gpr KT1 M (av - 16)%nat true pj -∗
    cpu_own 0%nat eb pj true lks -∗
    pc_is (mword_of_int (CW + 0x84)) -∗
    proc_priv_core pj pid V -∗
    cw_saved sp0 m0 -∗ cw_spill sp0 m0 -∗ cw_buf sp0 -∗
    cw_ret (CID0 := CID0) jp m0 av eb pid V n lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj Hm0sp HMsp HMs1 HMs11 Hr Hav Heb Hal Hcr.
    iIntros "#Ht Hcg Hcnt Hpc Hpriv Hsaved Hspill Hbuf Hcont".
    rewrite /cw_spill.
    iDestruct "Hspill" as "(S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12)".
    assert (Hb4 : add_vec (pa_stk sp0 16%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (apply cw_slot_bridge; pcw).
    assert (Hb5 : add_vec (pa_stk sp0 16%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (apply cw_slot_bridge; pcw).
    assert (Hb6 : add_vec (pa_stk sp0 16%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))
                  = pa_stk sp0 6) by (apply cw_slot_bridge; pcw).
    assert (Hb7 : add_vec (pa_stk sp0 16%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk sp0 7) by (apply cw_slot_bridge; pcw).
    assert (Hb8 : add_vec (pa_stk sp0 16%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk sp0 8) by (apply cw_slot_bridge; pcw).
    assert (Hb9 : add_vec (pa_stk sp0 16%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk sp0 9) by (apply cw_slot_bridge; pcw).
    assert (Hb10 : add_vec (pa_stk sp0 16%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk sp0 10) by (apply cw_slot_bridge; pcw).
    assert (Hb11 : add_vec (pa_stk sp0 16%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 11) by (apply cw_slot_bridge; pcw).
    assert (Hb12 : add_vec (pa_stk sp0 16%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 12) by (apply cw_slot_bridge; pcw).

    (* +0x84  c.ldsp rs2,96(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CW + 0x84)) (mword_of_int 12 : mword 6) Rs2
              M (av - 16)%nat (m0 !!! Regidx Rs2) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [S4]").
    { iApply (cnwi_84 with "Ht"). }
    { iEval (rewrite HMsp Hb4). iExact "S4". }
    iIntros (CIDl0 Hsl0) "Hcg Hpc S4".
    iEval (rewrite HMsp Hb4) in "S4".
    set (R0 := <[Regidx Rs2 := regval_into_reg (m0 !!! Regidx Rs2)]> M).
    change (<[Regidx Rs2 := regval_into_reg (m0 !!! Regidx Rs2)]> M) with R0.
    assert (HR0sp : R0 !!! Regidx csp_rs1 = pa_stk sp0 16%nat)
      by (rewrite /R0 upd_ne; [exact HMsp | reg_neq]).
    assert (Pq86 : add_vec_int (mword_of_int (CW + 0x84) : mword 64) 2
                  = mword_of_int (CW + 0x86)) by pcw.
    iEval (rewrite Pq86) in "Hpc".
    (* +0x86  c.ldsp rs3,88(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CW + 0x86)) (mword_of_int 11 : mword 6) Rs3
              R0 (av - 16)%nat (m0 !!! Regidx Rs3) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [S5]").
    { iApply (cnwi_86 with "Ht"). }
    { iEval (rewrite HR0sp Hb5). iExact "S5". }
    iIntros (CIDl1 Hsl1) "Hcg Hpc S5".
    iEval (rewrite HR0sp Hb5) in "S5".
    set (R1 := <[Regidx Rs3 := regval_into_reg (m0 !!! Regidx Rs3)]> R0).
    change (<[Regidx Rs3 := regval_into_reg (m0 !!! Regidx Rs3)]> R0) with R1.
    assert (HR1sp : R1 !!! Regidx csp_rs1 = pa_stk sp0 16%nat)
      by (rewrite /R1 upd_ne; [exact HR0sp | reg_neq]).
    assert (Pq88 : add_vec_int (mword_of_int (CW + 0x86) : mword 64) 2
                  = mword_of_int (CW + 0x88)) by pcw.
    iEval (rewrite Pq88) in "Hpc".
    (* +0x88  c.ldsp rs4,80(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CW + 0x88)) (mword_of_int 10 : mword 6) Rs4
              R1 (av - 16)%nat (m0 !!! Regidx Rs4) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [S6]").
    { iApply (cnwi_88 with "Ht"). }
    { iEval (rewrite HR1sp Hb6). iExact "S6". }
    iIntros (CIDl2 Hsl2) "Hcg Hpc S6".
    iEval (rewrite HR1sp Hb6) in "S6".
    set (R2 := <[Regidx Rs4 := regval_into_reg (m0 !!! Regidx Rs4)]> R1).
    change (<[Regidx Rs4 := regval_into_reg (m0 !!! Regidx Rs4)]> R1) with R2.
    assert (HR2sp : R2 !!! Regidx csp_rs1 = pa_stk sp0 16%nat)
      by (rewrite /R2 upd_ne; [exact HR1sp | reg_neq]).
    assert (Pq8a : add_vec_int (mword_of_int (CW + 0x88) : mword 64) 2
                  = mword_of_int (CW + 0x8a)) by pcw.
    iEval (rewrite Pq8a) in "Hpc".
    (* +0x8a  c.ldsp rs5,72(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CW + 0x8a)) (mword_of_int 9 : mword 6) Rs5
              R2 (av - 16)%nat (m0 !!! Regidx Rs5) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [S7]").
    { iApply (cnwi_8a with "Ht"). }
    { iEval (rewrite HR2sp Hb7). iExact "S7". }
    iIntros (CIDl3 Hsl3) "Hcg Hpc S7".
    iEval (rewrite HR2sp Hb7) in "S7".
    set (R3 := <[Regidx Rs5 := regval_into_reg (m0 !!! Regidx Rs5)]> R2).
    change (<[Regidx Rs5 := regval_into_reg (m0 !!! Regidx Rs5)]> R2) with R3.
    assert (HR3sp : R3 !!! Regidx csp_rs1 = pa_stk sp0 16%nat)
      by (rewrite /R3 upd_ne; [exact HR2sp | reg_neq]).
    assert (Pq8c : add_vec_int (mword_of_int (CW + 0x8a) : mword 64) 2
                  = mword_of_int (CW + 0x8c)) by pcw.
    iEval (rewrite Pq8c) in "Hpc".
    (* +0x8c  c.ldsp rs6,64(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CW + 0x8c)) (mword_of_int 8 : mword 6) Rs6
              R3 (av - 16)%nat (m0 !!! Regidx Rs6) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [S8]").
    { iApply (cnwi_8c with "Ht"). }
    { iEval (rewrite HR3sp Hb8). iExact "S8". }
    iIntros (CIDl4 Hsl4) "Hcg Hpc S8".
    iEval (rewrite HR3sp Hb8) in "S8".
    set (R4 := <[Regidx Rs6 := regval_into_reg (m0 !!! Regidx Rs6)]> R3).
    change (<[Regidx Rs6 := regval_into_reg (m0 !!! Regidx Rs6)]> R3) with R4.
    assert (HR4sp : R4 !!! Regidx csp_rs1 = pa_stk sp0 16%nat)
      by (rewrite /R4 upd_ne; [exact HR3sp | reg_neq]).
    assert (Pq8e : add_vec_int (mword_of_int (CW + 0x8c) : mword 64) 2
                  = mword_of_int (CW + 0x8e)) by pcw.
    iEval (rewrite Pq8e) in "Hpc".
    (* +0x8e  c.ldsp rs7,56(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CW + 0x8e)) (mword_of_int 7 : mword 6) Rs7
              R4 (av - 16)%nat (m0 !!! Regidx Rs7) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [S9]").
    { iApply (cnwi_8e with "Ht"). }
    { iEval (rewrite HR4sp Hb9). iExact "S9". }
    iIntros (CIDl5 Hsl5) "Hcg Hpc S9".
    iEval (rewrite HR4sp Hb9) in "S9".
    set (R5 := <[Regidx Rs7 := regval_into_reg (m0 !!! Regidx Rs7)]> R4).
    change (<[Regidx Rs7 := regval_into_reg (m0 !!! Regidx Rs7)]> R4) with R5.
    assert (HR5sp : R5 !!! Regidx csp_rs1 = pa_stk sp0 16%nat)
      by (rewrite /R5 upd_ne; [exact HR4sp | reg_neq]).
    assert (Pq90 : add_vec_int (mword_of_int (CW + 0x8e) : mword 64) 2
                  = mword_of_int (CW + 0x90)) by pcw.
    iEval (rewrite Pq90) in "Hpc".
    (* +0x90  c.ldsp rs8,48(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CW + 0x90)) (mword_of_int 6 : mword 6) Rs8
              R5 (av - 16)%nat (m0 !!! Regidx Rs8) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [S10]").
    { iApply (cnwi_90 with "Ht"). }
    { iEval (rewrite HR5sp Hb10). iExact "S10". }
    iIntros (CIDl6 Hsl6) "Hcg Hpc S10".
    iEval (rewrite HR5sp Hb10) in "S10".
    set (R6 := <[Regidx Rs8 := regval_into_reg (m0 !!! Regidx Rs8)]> R5).
    change (<[Regidx Rs8 := regval_into_reg (m0 !!! Regidx Rs8)]> R5) with R6.
    assert (HR6sp : R6 !!! Regidx csp_rs1 = pa_stk sp0 16%nat)
      by (rewrite /R6 upd_ne; [exact HR5sp | reg_neq]).
    assert (Pq92 : add_vec_int (mword_of_int (CW + 0x90) : mword 64) 2
                  = mword_of_int (CW + 0x92)) by pcw.
    iEval (rewrite Pq92) in "Hpc".
    (* +0x92  c.ldsp rs9,40(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CW + 0x92)) (mword_of_int 5 : mword 6) Rs9
              R6 (av - 16)%nat (m0 !!! Regidx Rs9) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [S11]").
    { iApply (cnwi_92 with "Ht"). }
    { iEval (rewrite HR6sp Hb11). iExact "S11". }
    iIntros (CIDl7 Hsl7) "Hcg Hpc S11".
    iEval (rewrite HR6sp Hb11) in "S11".
    set (R7 := <[Regidx Rs9 := regval_into_reg (m0 !!! Regidx Rs9)]> R6).
    change (<[Regidx Rs9 := regval_into_reg (m0 !!! Regidx Rs9)]> R6) with R7.
    assert (HR7sp : R7 !!! Regidx csp_rs1 = pa_stk sp0 16%nat)
      by (rewrite /R7 upd_ne; [exact HR6sp | reg_neq]).
    assert (Pq94 : add_vec_int (mword_of_int (CW + 0x92) : mword 64) 2
                  = mword_of_int (CW + 0x94)) by pcw.
    iEval (rewrite Pq94) in "Hpc".
    (* +0x94  c.ldsp rs10,32(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (CW + 0x94)) (mword_of_int 4 : mword 6) Rs10
              R7 (av - 16)%nat (m0 !!! Regidx Rs10) true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [S12]").
    { iApply (cnwi_94 with "Ht"). }
    { iEval (rewrite HR7sp Hb12). iExact "S12". }
    iIntros (CIDl8 Hsl8) "Hcg Hpc S12".
    iEval (rewrite HR7sp Hb12) in "S12".
    set (R8 := <[Regidx Rs10 := regval_into_reg (m0 !!! Regidx Rs10)]> R7).
    change (<[Regidx Rs10 := regval_into_reg (m0 !!! Regidx Rs10)]> R7) with R8.
    assert (HR8sp : R8 !!! Regidx csp_rs1 = pa_stk sp0 16%nat)
      by (rewrite /R8 upd_ne; [exact HR7sp | reg_neq]).
    assert (Pq96 : add_vec_int (mword_of_int (CW + 0x94) : mword 64) 2
                  = mword_of_int (CW + 0x96)) by pcw.
    iEval (rewrite Pq96) in "Hpc".
    (* the nine values are back; s11 was never touched *)
    assert (Hhi : cw_cs_hi R8 m0).
    { unfold cw_cs_hi. split_and!;
        first [ rewrite /R8 /R7 /R6 /R5 /R4 /R3 /R2 /R1 /R0;
                repeat (rewrite upd_ne; [| reg_neq]); rewrite upd_eq; reflexivity
              | rewrite /R8 /R7 /R6 /R5 /R4 /R3 /R2 /R1 /R0;
                repeat (rewrite upd_ne; [| reg_neq]); exact HMs11 ]. }
    assert (Hs1v : R8 !!! Regidx Rs1 = (mword_of_int r : mword 64)).
    { rewrite /R8 /R7 /R6 /R5 /R4 /R3 /R2 /R1 /R0.
      repeat (rewrite upd_ne; [| reg_neq]). exact HMs1. }
    (* the four buffer slots become words again, for the pop *)
    iDestruct (cw_rest_of sp0 m0 Hal with "[S4 S5 S6 S7 S8 S9 S10 S11 S12] Hbuf")
      as "Hrest".
    { rewrite /cw_spill. iFrame "S4 S5 S6 S7 S8 S9 S10 S11 S12". }
    iApply (cw_epi (CID := CIDl8) CID0 jp m0 R8 av eb sp0 pid V n r lks
              Hm0sp HR8sp Hs1v Hhi Hr Hav Heb ltac:(wp_next_chain)
              with "Ht Hcg Hcnt Hpc Hpriv Hsaved Hrest Hcont").
  Qed.
  (* =================================================================== *)
  (*  THE LOOP.  Head +0x5e (the test), body +0x38, back edge +0x5a.      *)
  (*                                                                      *)
  (*  [mrem] is FUEL, not the iteration count: each turn moves [i] up by   *)
  (*  [nn = min 32 (n - i) >= 1], so [n - i] strictly decreases and any    *)
  (*  bound on it will do.  The base case is vacuous -- the head is only   *)
  (*  ever entered with [i < n].                                          *)
  (* =================================================================== *)
  Lemma cw_loop (mrem : nat) (CID0 : CPU)
      (γa γf : gname) (γs : list gname) (jp : nat) (γlp γl : gname)
      (γu : uart_names) (γv : disk_names)
      (m0 : regfile) (av : nat) (eb : bool)
      (pid : mword 32) (n : Z) (sp0 src : mword 64) (lks : gset string) :
    (jp < NPROC)%nat -> γs !! jp = Some γlp -> length γs = NPROC ->
    (n < 2 ^ 31)%Z ->
    (consolewrite_stack <= av)%nat ->
    eb = true ->
    m0 !!! Regidx csp_rs1 = sp0 ->
    (forall k, (k < 4)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (16 - k))) 8 = true) ->
    forall (CID : CpuId) (M : regfile) (V : pprivate) (i : Z),
      (0 <= i < n)%Z ->
      (Z.to_nat (n - i) <= mrem)%nat ->
      cw_regs M (pa_stk sp0 16%nat) sp0 src n i ->
      M !!! Regidx Rs11 = m0 !!! Regidx Rs11 ->
      (true = false \/ proc_addr jp = zero_reg -> (CID : CPU) = CID0) ->
      (* consolewrite's own cone bottoms out at "proc" (11), NOT "kmem" (13):
         Uartwrite's CURRENT contract (SpecUartwrite.v) demands
         [locks_below lks "proc"] -- its sleep_prepare/sleep calls
         reach "proc" ahead of its own "uart" acquire -- and [locks_below_mono]
         only lifts a bound UP to a larger rank, never down.  A premise at
         "kmem" (13 > 11) could not supply Uartwrite's need at all.  "proc" is
         also low enough to cover EitherCopyin's anticipated "kmem" (13) floor
         once it is swept (11 <= 13), so it is the true floor of the whole
         cone, current and anticipated. *)
      locks_below lks "proc" ->
      kernel_text -∗
      sie_cap_gpr KT1 M (av - 16)%nat true (proc_addr jp) -∗
      cpu_own 0%nat eb (proc_addr jp) true lks -∗
      pc_is (mword_of_int (CW + 0x5e)) -∗
      proc_priv_core (proc_addr jp) pid V -∗
      kalloc_env γa None -∗
      dev_inv γu γv -∗
      is_txlock γl γu -∗
      procs_inv γs -∗
      cw_saved sp0 m0 -∗ cw_spill sp0 m0 -∗ cw_buf sp0 -∗
      cw_ret (CID0 := CID0) jp m0 av eb pid V n lks -∗
      WP (Loop : expr riscv_lang).
  Proof.
    intros Hj Hjlp Hlens Hn31 Hav Heb Hm0sp Hal.
    induction mrem as [| mrem IH]; intros CID M V i Hi Hrem Hregs Hs11 Hcr Hbelow.
    { (* fuel 0 is unreachable: the head is entered only with [i < n] *)
      exfalso. lia. }
    iIntros "#Ht Hcg Hcnt Hpc Hpriv #Hkenv #Hdinv #Htxl #Hpinv
             Hsaved Hspill Hbuf Hcont".
    set (pj := proc_addr jp).
    set (buf := pa_stk sp0 16%nat).
    pose proof Hregs as Hregs'.
    destruct Hregs' as (Hsp & Hs0 & Hs1 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10).
    set (nn := Z.min 32 (n - i)).
    assert (Hnn1 : (1 <= nn <= 32)%Z) by (unfold nn; lia).
    assert (Hnnle : (nn <= n - i)%Z) by (unfold nn; lia).
    set (nnN := Z.to_nat nn).
    assert (HnnN : Z.of_nat nnN = nn) by (unfold nnN; lia).
    (* THE TAIL LENGTH IS A [set] VARIABLE, not [32 - nnN]: a [replace 32 with
       (nnN + (32 - nnN))] rewrites the 32 INSIDE its own right-hand side, and
       the buffer never reassembles. *)
    set (rest := (32 - nnN)%nat).
    assert (H32 : (32 = nnN + rest)%nat) by (unfold rest, nnN; lia).
    (* ---------------------------------------------------------------- *)
    (*  +0x38 .. +0x5a -- THE BODY, offered to both arms of the [min].    *)
    (* ---------------------------------------------------------------- *)
    iAssert (∀ (CIDb : CpuId) (Mb : regfile),
               ⌜cw_regs Mb (pa_stk sp0 16%nat) sp0 src n i⌝ -∗
               ⌜Mb !!! Regidx Rs2 = (mword_of_int nn : mword 64)⌝ -∗
               ⌜Mb !!! Regidx Rs11 = m0 !!! Regidx Rs11⌝ -∗
               ⌜(true = false \/ pj = zero_reg -> (CIDb : CPU) = CID0)⌝ -∗
               sie_cap_gpr KT1 Mb (av - 16)%nat true pj -∗
               pc_is (mword_of_int (CW + 0x38)) -∗
               WP (Loop : expr riscv_lang))%I
      with "[Hcnt Hpriv Hsaved Hspill Hbuf Hcont]" as "BODY".
    { iIntros (CIDb Mb) "%Hregb %Hs2 %Hs11b %Hcrb Hcg Hpc".
      pose proof Hregb as Hregb'.
      destruct Hregb' as (Bsp & Bs0 & Bs1 & Bs4 & Bs5 & Bs6 & Bs7 & Bs8 & Bs9 & Bs10).
      (* +0x38  sext.w s3,s2 *)
      iApply (wp_addiw_s_sconf (mword_of_int (CW + 0x38)) Rs3 Rs2
                (mword_of_int 0 : mword 12) Mb (av - 16)%nat true
                ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (cnwi_38 with "Ht"). }
      iIntros (CIDc1 Hsc1) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (B1 := <[Regidx Rs3 := regval_into_reg
          (sign_extend' 64 (subrange_vec_dec (add_vec (Mb !!! Regidx Rs2)
             (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0))]> Mb).
      change (<[Regidx Rs3 := regval_into_reg
          (sign_extend' 64 (subrange_vec_dec (add_vec (Mb !!! Regidx Rs2)
             (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0))]> Mb) with B1.
      assert (HB1s3 : B1 !!! Regidx Rs3 = (mword_of_int nn : mword 64)).
      { rewrite /B1 upd_eq Hs2. apply w32_sextw_moi. lia. }
      assert (Pb3c : add_vec_int (mword_of_int (CW + 0x38) : mword 64) 4
                     = mword_of_int (CW + 0x3c)) by pcw.
      iEval (rewrite Pb3c) in "Hpc".
      (* +0x3c  c.mv a3,s3 *)
      iApply (wp_cmv_s_sconf (mword_of_int (CW + 0x3c)) Ra3 Rs3
                B1 (av - 16)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (cnwi_3c with "Ht"). }
      iIntros (CIDc2 Hsc2) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (B2 := <[Regidx Ra3 := regval_into_reg (add_vec zero_reg (B1 !!! Regidx Rs3))]> B1).
      change (<[Regidx Ra3 := regval_into_reg (add_vec zero_reg (B1 !!! Regidx Rs3))]> B1) with B2.
      assert (HB2a3 : B2 !!! Regidx Ra3 = (mword_of_int nn : mword 64))
        by (rewrite /B2 upd_eq w32_zero_add; exact HB1s3).
      assert (Pb3e : add_vec_int (mword_of_int (CW + 0x3c) : mword 64) 2
                     = mword_of_int (CW + 0x3e)) by pcw.
      iEval (rewrite Pb3e) in "Hpc".
      (* +0x3e  add a2,s1,s7 : the user source, advanced by [i] *)
      assert (HB2s1 : B2 !!! Regidx Rs1 = (mword_of_int i : mword 64)).
      { rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [| reg_neq]. exact Bs1. }
      assert (HB2s7 : B2 !!! Regidx Rs7 = src).
      { rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [| reg_neq]. exact Bs7. }
      assert (Hadd : add_vec (rget B2 Rs1) (rget B2 Rs7)
                     = add_vec (mword_of_int i : mword 64) src).
      { rgne. rgne. rewrite HB2s1. rewrite HB2s7. reflexivity. }
      iApply (wp_add_s_sconf (mword_of_int (CW + 0x3e)) Ra2 Rs1 Rs7
                (add_vec (mword_of_int i : mword 64) src)
                B2 (av - 16)%nat true ltac:(nz) ltac:(rdok) Hadd
                with "Hcg Hpc []").
      { iApply (cnwi_3e with "Ht"). }
      iIntros (CIDc3 Hsc3) "Hcg Hpc".
      set (B3 := <[Regidx Ra2 := regval_into_reg
          (add_vec (mword_of_int i : mword 64) src)]> B2).
      change (<[Regidx Ra2 := regval_into_reg
          (add_vec (mword_of_int i : mword 64) src)]> B2) with B3.
      assert (Pb42 : add_vec_int (mword_of_int (CW + 0x3e) : mword 64) 4
                     = mword_of_int (CW + 0x42)) by pcw.
      iEval (rewrite Pb42) in "Hpc".
      (* +0x42  c.mv a1,s6 *)
      iApply (wp_cmv_s_sconf (mword_of_int (CW + 0x42)) Ra1 Rs6
                B3 (av - 16)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (cnwi_42 with "Ht"). }
      iIntros (CIDc4 Hsc4) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (B4 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (B3 !!! Regidx Rs6))]> B3).
      change (<[Regidx Ra1 := regval_into_reg (add_vec zero_reg (B3 !!! Regidx Rs6))]> B3) with B4.
      assert (HB3s6 : B3 !!! Regidx Rs6 = (mword_of_int 1 : mword 64)).
      { rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_ne; [| reg_neq].
        rewrite /B1 upd_ne; [| reg_neq]. exact Bs6. }
      assert (HB4a1 : B4 !!! Regidx Ra1 = (mword_of_int 1 : mword 64))
        by (rewrite /B4 upd_eq w32_zero_add; exact HB3s6).
      assert (Pb44 : add_vec_int (mword_of_int (CW + 0x42) : mword 64) 2
                     = mword_of_int (CW + 0x44)) by pcw.
      iEval (rewrite Pb44) in "Hpc".
      (* +0x44  c.mv a0,s5 : the bounce buffer *)
      iApply (wp_cmv_s_sconf (mword_of_int (CW + 0x44)) Ra0 Rs5
                B4 (av - 16)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (cnwi_44 with "Ht"). }
      iIntros (CIDc5 Hsc5) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (B5 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (B4 !!! Regidx Rs5))]> B4).
      change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (B4 !!! Regidx Rs5))]> B4) with B5.
      assert (HB4s5 : B4 !!! Regidx Rs5 = buf).
      { rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_ne; [| reg_neq].
        rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [| reg_neq]. exact Bs5. }
      assert (HB5a0 : B5 !!! Regidx Ra0 = buf)
        by (rewrite /B5 upd_eq w32_zero_add; exact HB4s5).
      assert (HB5a1 : B5 !!! Regidx Ra1 = (mword_of_int 1 : mword 64))
        by (rewrite /B5 upd_ne; [exact HB4a1 | reg_neq]).
      assert (HB5a3 : B5 !!! Regidx Ra3 = (mword_of_int nn : mword 64)).
      { rewrite /B5 upd_ne; [| reg_neq]. rewrite /B4 upd_ne; [| reg_neq].
        rewrite /B3 upd_ne; [| reg_neq]. exact HB2a3. }
      assert (Pb46 : add_vec_int (mword_of_int (CW + 0x44) : mword 64) 2
                     = mword_of_int (CW + 0x46)) by pcw.
      iEval (rewrite Pb46) in "Hpc".
      (* +0x46  jal either_copyin *)
      iApply (wp_jal_s_sconf (mword_of_int (CW + 0x46)) Rra
                (mword_of_int 8608 : mword 21) B5 (av - 16)%nat true
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (cnwi_46 with "Ht"). }
      iIntros (CIDc6 Hsc6) "Hcg Hpc".
      set (B6 := <[Regidx Rra := regval_into_reg
          (add_vec_int (mword_of_int (CW + 0x46) : mword 64) 4)]> B5).
      change (<[Regidx Rra := regval_into_reg
          (add_vec_int (mword_of_int (CW + 0x46) : mword 64) 4)]> B5) with B6.
      assert (Jeci : add_vec (mword_of_int (CW + 0x46) : mword 64)
                       (sign_extend' 64 (mword_of_int 8608 : mword 21))
                     = mword_of_int KernelSyms.either_copyin) by pcw.
      iEval (rewrite Jeci) in "Hpc".
      assert (HB6a0 : B6 !!! Regidx Ra0 = buf)
        by (rewrite /B6 upd_ne; [exact HB5a0 | reg_neq]).
      assert (HB6a1 : B6 !!! Regidx Ra1 = (mword_of_int 1 : mword 64))
        by (rewrite /B6 upd_ne; [exact HB5a1 | reg_neq]).
      assert (HB6a3 : B6 !!! Regidx Ra3 = (mword_of_int nn : mword 64))
        by (rewrite /B6 upd_ne; [exact HB5a3 | reg_neq]).
      assert (HB6ra : B6 !!! Regidx Rra
                      = add_vec_int (mword_of_int (CW + 0x46) : mword 64) 4)
        by (rewrite /B6 upd_eq; reflexivity).
      (* the first [nn] bytes of the frame buffer, NAMED *)
      rewrite /cw_buf H32 bytes_own_app.
      iDestruct "Hbuf" as "[Hb1 Hb2]".
      iDestruct (bytes_own_name (KTR := KT1) nnN buf with "Hb1") as (fb) "Hb1".
     iDestruct (cpu_own_transport CIDb CIDc6 0%nat eb pj true 
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iApply (EitherCopyin.wp_either_copyin_sconf KT1 KT1 γa γf B6 (av - 16)%nat 0%nat
                eb pj pid V true nnN (fun _ => bv_0 8) fb true lks
                ltac:(lia)
                ltac:(rewrite HB6a1; vm_compute; reflexivity)
                ltac:(rewrite HB6a3 HnnN; reflexivity)
                ltac:(rewrite HnnN; lia) ltac:(lia)
                with "Hcg Hcnt Ht Hpc Hkenv [Hb1] Hpriv").
      all: try lkbelow.
      { iEval (rewrite HB6a0). iExact "Hb1". }
      iIntros (CIDc7 Hsc7 mf1) "%Hcs1 Hcg Hcnt Hpc Hpost".
      iEval (rewrite HB6ra) in "Hpc".
      assert (P4a : ret_pc (add_vec_int (mword_of_int (CW + 0x46) : mword 64) 4)
                    = mword_of_int (CW + 0x4a)) by pcw.
      iEval (rewrite P4a) in "Hpc".
      rewrite /either_copyin_post.
      iDestruct "Hpost" as "(%Hrv & Hpv & Hb1)".
      iDestruct "Hpv" as (P1) "(%Hext1 & Hpriv)".
      iDestruct "Hb1" as (fb') "Hb1".
      iEval (rewrite HB6a0) in "Hb1".
      (* the register shape survives the call *)
      assert (Hregc : cw_regs mf1 (pa_stk sp0 16%nat) sp0 src n i).
      { apply (cw_regs_cs B6); [exact Hcs1|].
        apply (cw_regs_cs B5); [rewrite /B6; apply callee_saved_insert_r;
                                [vm_compute; reflexivity | apply callee_saved_refl] |].
        apply (cw_regs_cs B4); [rewrite /B5; apply callee_saved_insert_r;
                                [vm_compute; reflexivity | apply callee_saved_refl] |].
        apply (cw_regs_cs B3); [rewrite /B4; apply callee_saved_insert_r;
                                [vm_compute; reflexivity | apply callee_saved_refl] |].
        apply (cw_regs_cs B2); [rewrite /B3; apply callee_saved_insert_r;
                                [vm_compute; reflexivity | apply callee_saved_refl] |].
        apply (cw_regs_cs B1); [rewrite /B2; apply callee_saved_insert_r;
                                [vm_compute; reflexivity | apply callee_saved_refl] |].
        (* B1 writes s3, which [cw_regs] does not name *)
        pose proof Hregb as Hx.
        destruct Hx as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
        unfold cw_regs; rewrite /B1;
          repeat (rewrite upd_ne; [| reg_neq]); split_and!;
          first [ exact X1 | exact X2 | exact X3 | exact X4 | exact X5
                | exact X6 | exact X7 | exact X8 | exact X9 | exact X10
                | rewrite upd_ne; [ first [exact X1|exact X2|exact X3|exact X4|exact X5
                                          |exact X6|exact X7|exact X8|exact X9|exact X10]
                                  | reg_neq] ]. }
      pose proof Hregc as Hregc'.
      destruct Hregc' as (Csp & Cs0 & Cs1 & Cs4 & Cs5 & Cs6 & Cs7 & Cs8 & Cs9 & Cs10).
      assert (Hs11c : mf1 !!! Regidx Rs11 = m0 !!! Regidx Rs11).
      { rewrite (callee_saved_lookup Hcs1 Rs11 ltac:(vm_compute; reflexivity)).
        rewrite /B6 upd_ne; [| reg_neq]. rewrite /B5 upd_ne; [| reg_neq].
        rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_ne; [| reg_neq].
        rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [| reg_neq].
        exact Hs11b. }
      assert (Hs3c : mf1 !!! Regidx Rs3 = (mword_of_int nn : mword 64)).
      { rewrite (callee_saved_lookup Hcs1 Rs3 ltac:(vm_compute; reflexivity)).
        rewrite /B6 upd_ne; [| reg_neq]. rewrite /B5 upd_ne; [| reg_neq].
        rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_ne; [| reg_neq].
        rewrite /B2 upd_ne; [| reg_neq]. exact HB1s3. }
      assert (Hs2c : mf1 !!! Regidx Rs2 = (mword_of_int nn : mword 64)).
      { rewrite (callee_saved_lookup Hcs1 Rs2 ltac:(vm_compute; reflexivity)).
        rewrite /B6 upd_ne; [| reg_neq]. rewrite /B5 upd_ne; [| reg_neq].
        rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_ne; [| reg_neq].
        rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [| reg_neq]. exact Hs2. }
      (* +0x4a  beq a0,s8 : the copy failed exit *)
      destruct Hrv as [Hr0 | Hrm1].
      - (* it succeeded: the branch is NOT taken *)
        assert (Heqf : eq_vec (rget mf1 Ra0) (rget mf1 Rs8) = false).
        { rgne. rgne. rewrite Hr0. rewrite Cs8. exact cw_eqv_m1_0. }
        iApply (wp_beq_fall_s_sconf (mword_of_int (CW + 0x4a))
                  (mword_of_int 58 : mword 13) Rs8 Ra0 mf1 (av - 16)%nat true
                  ltac:(nz) ltac:(nz)
                  Heqf with "Hcg Hpc []").
        { iApply (cnwi_4a with "Ht"). }
        iIntros (CIDc8 Hsc8) "Hcg Hpc".
        assert (P4e : add_vec_int (mword_of_int (CW + 0x4a) : mword 64) 4
                      = mword_of_int (CW + 0x4e)) by pcw.
        iEval (rewrite P4e) in "Hpc".
        (* +0x4e  c.mv a1,s3 *)
        iApply (wp_cmv_s_sconf (mword_of_int (CW + 0x4e)) Ra1 Rs3
                  mf1 (av - 16)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (cnwi_4e with "Ht"). }
        iIntros (CIDc9 Hsc9) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (D1 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (mf1 !!! Regidx Rs3))]> mf1).
        change (<[Regidx Ra1 := regval_into_reg (add_vec zero_reg (mf1 !!! Regidx Rs3))]> mf1) with D1.
        assert (HD1a1 : D1 !!! Regidx Ra1 = (mword_of_int nn : mword 64))
          by (rewrite /D1 upd_eq w32_zero_add; exact Hs3c).
        assert (P50 : add_vec_int (mword_of_int (CW + 0x4e) : mword 64) 2
                      = mword_of_int (CW + 0x50)) by pcw.
        iEval (rewrite P50) in "Hpc".
        (* +0x50  c.mv a0,s5 *)
        iApply (wp_cmv_s_sconf (mword_of_int (CW + 0x50)) Ra0 Rs5
                  D1 (av - 16)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (cnwi_50 with "Ht"). }
        iIntros (CIDca Hsca) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (D2 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (D1 !!! Regidx Rs5))]> D1).
        change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (D1 !!! Regidx Rs5))]> D1) with D2.
        assert (HD1s5 : D1 !!! Regidx Rs5 = buf)
          by (rewrite /D1 upd_ne; [exact Cs5 | reg_neq]).
        assert (HD2a0 : D2 !!! Regidx Ra0 = buf)
          by (rewrite /D2 upd_eq w32_zero_add; exact HD1s5).
        assert (HD2a1 : D2 !!! Regidx Ra1 = (mword_of_int nn : mword 64))
          by (rewrite /D2 upd_ne; [exact HD1a1 | reg_neq]).
        assert (P52 : add_vec_int (mword_of_int (CW + 0x50) : mword 64) 2
                      = mword_of_int (CW + 0x52)) by pcw.
        iEval (rewrite P52) in "Hpc".
        (* +0x52  jal uartwrite *)
        iApply (wp_jal_s_sconf (mword_of_int (CW + 0x52)) Rra
                  (mword_of_int 1952 : mword 21) D2 (av - 16)%nat true
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
        { iApply (cnwi_52 with "Ht"). }
        iIntros (CIDcb Hscb) "Hcg Hpc".
        set (D3 := <[Regidx Rra := regval_into_reg
            (add_vec_int (mword_of_int (CW + 0x52) : mword 64) 4)]> D2).
        change (<[Regidx Rra := regval_into_reg
            (add_vec_int (mword_of_int (CW + 0x52) : mword 64) 4)]> D2) with D3.
        assert (Juw : add_vec (mword_of_int (CW + 0x52) : mword 64)
                        (sign_extend' 64 (mword_of_int 1952 : mword 21))
                      = mword_of_int KernelSyms.uartwrite) by pcw.
        iEval (rewrite Juw) in "Hpc".
        assert (HD3a0 : D3 !!! Regidx Ra0 = buf)
          by (rewrite /D3 upd_ne; [exact HD2a0 | reg_neq]).
        assert (HD3a1 : D3 !!! Regidx Ra1 = (mword_of_int nn : mword 64))
          by (rewrite /D3 upd_ne; [exact HD2a1 | reg_neq]).
        assert (HD3ra : D3 !!! Regidx Rra
                        = add_vec_int (mword_of_int (CW + 0x52) : mword 64) 4)
          by (rewrite /D3 upd_eq; reflexivity).
        iDestruct (cw_priv_pid pj pid (upd_upt V P1) with "Hpriv") as "[Hpid Hpback]".
        iDestruct (cpu_own_transport CIDc7 CIDcb 0%nat eb pj true 
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iApply (Uartwrite.wp_uartwrite_sconf γu γv γs jp γlp γl D3 (av - 16)%nat
                  eb nnN fb' (DfracOwn 1) true pid (DfracOwn (1/2)) lks
                  Hj Hjlp ltac:(rewrite HD3a1 HnnN; reflexivity)
                  ltac:(rewrite HnnN; lia)
                  ltac:(lia) Heb
                  (* Uartwrite's premise is at "proc" too -- same rank,
                     [Hbelow] passed directly. *)
                  Hbelow
                  with "Hcg Hcnt Ht Hpc Hdinv Htxl Hpid [Hb1] Hpinv").
        all: try lkbelow.
        { iEval (rewrite HD3a0). iExact "Hb1". }
        iIntros (CIDcc Hscc mf2) "%Hcs2 Hcg Hcnt Hpc Hb1 Hpid #Hsent".
        iEval (rewrite HD3ra) in "Hpc".
        assert (P56 : ret_pc (add_vec_int (mword_of_int (CW + 0x52) : mword 64) 4)
                      = mword_of_int (CW + 0x56)) by pcw.
        iEval (rewrite P56) in "Hpc".
        iEval (rewrite HD3a0) in "Hb1".
        iDestruct ("Hpback" with "Hpid") as "Hpriv".
        (* the buffer is whole again *)
        iDestruct (bytes_own_of_name (KTR := KT1) nnN buf fb' with "Hb1") as "Hb1".
        iAssert (cw_buf sp0) with "[Hb1 Hb2]" as "Hbuf".
        { rewrite /cw_buf H32 (bytes_own_app (KTR := KT1)).
          iSplitL "Hb1"; [iExact "Hb1" | iExact "Hb2"]. }
        assert (Hregd : cw_regs mf2 (pa_stk sp0 16%nat) sp0 src n i).
        { apply (cw_regs_cs D3); [exact Hcs2|].
          apply (cw_regs_cs D2); [rewrite /D3; apply callee_saved_insert_r;
                                  [vm_compute; reflexivity | apply callee_saved_refl] |].
          apply (cw_regs_cs D1); [rewrite /D2; apply callee_saved_insert_r;
                                  [vm_compute; reflexivity | apply callee_saved_refl] |].
          apply (cw_regs_cs mf1); [rewrite /D1; apply callee_saved_insert_r;
                                   [vm_compute; reflexivity | apply callee_saved_refl] |].
          exact Hregc. }
        pose proof Hregd as Hregd'.
        destruct Hregd' as (Dsp & Ds0 & Ds1 & Ds4 & Ds5 & Ds6 & Ds7 & Ds8 & Ds9 & Ds10).
        assert (Hs2d : mf2 !!! Regidx Rs2 = (mword_of_int nn : mword 64)).
        { rewrite (callee_saved_lookup Hcs2 Rs2 ltac:(vm_compute; reflexivity)).
          rewrite /D3 upd_ne; [| reg_neq]. rewrite /D2 upd_ne; [| reg_neq].
          rewrite /D1 upd_ne; [| reg_neq]. exact Hs2c. }
        assert (Hs11d : mf2 !!! Regidx Rs11 = m0 !!! Regidx Rs11).
        { rewrite (callee_saved_lookup Hcs2 Rs11 ltac:(vm_compute; reflexivity)).
          rewrite /D3 upd_ne; [| reg_neq]. rewrite /D2 upd_ne; [| reg_neq].
          rewrite /D1 upd_ne; [| reg_neq]. exact Hs11c. }
        (* +0x56  addw s1,s2,s1 : i += nn *)
        iApply (wp_addw4_s_sconf (mword_of_int (CW + 0x56)) Rs1 Rs2 Rs1
                  mf2 (av - 16)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
        { iApply (cnwi_56 with "Ht"). }
        iIntros (CIDcd Hscd) "Hcg Hpc". iEval (rgne) in "Hcg". iEval (rgne) in "Hcg".
        set (F1 := <[Regidx Rs1 := regval_into_reg
            (sign_extend' 64 (add_vec (subrange_vec_dec (mf2 !!! Regidx Rs2) 31 0 : mword 32)
                                      (subrange_vec_dec (mf2 !!! Regidx Rs1) 31 0 : mword 32)))]> mf2).
        change (<[Regidx Rs1 := regval_into_reg
            (sign_extend' 64 (add_vec (subrange_vec_dec (mf2 !!! Regidx Rs2) 31 0 : mword 32)
                                      (subrange_vec_dec (mf2 !!! Regidx Rs1) 31 0 : mword 32)))]> mf2) with F1.
        assert (HF1s1 : F1 !!! Regidx Rs1 = (mword_of_int (nn + i) : mword 64)).
        { rewrite /F1 upd_eq Hs2d Ds1. apply w32_addw_moi; lia. }
        assert (HF1regs : cw_regs F1 (pa_stk sp0 16%nat) sp0 src n (nn + i)).
        { unfold cw_regs. split_and!.
          - rewrite /F1 upd_ne; [exact Dsp  | reg_neq].
          - rewrite /F1 upd_ne; [exact Ds0  | reg_neq].
          - exact HF1s1.
          - rewrite /F1 upd_ne; [exact Ds4  | reg_neq].
          - rewrite /F1 upd_ne; [exact Ds5  | reg_neq].
          - rewrite /F1 upd_ne; [exact Ds6  | reg_neq].
          - rewrite /F1 upd_ne; [exact Ds7  | reg_neq].
          - rewrite /F1 upd_ne; [exact Ds8  | reg_neq].
          - rewrite /F1 upd_ne; [exact Ds9  | reg_neq].
          - rewrite /F1 upd_ne; [exact Ds10 | reg_neq]. }
        assert (HF1s11 : F1 !!! Regidx Rs11 = m0 !!! Regidx Rs11)
          by (rewrite /F1 upd_ne; [exact Hs11d | reg_neq]).
        assert (P5a : add_vec_int (mword_of_int (CW + 0x56) : mword 64) 4
                      = mword_of_int (CW + 0x5a)) by pcw.
        iEval (rewrite P5a) in "Hpc".
        (* +0x5a  bge s1,s4 : done? *)
        assert (HF1s4 : F1 !!! Regidx Rs4 = (mword_of_int n : mword 64))
          by (rewrite /F1 upd_ne; [exact Ds4 | reg_neq]).
        assert (Hcmp : zopz0zKzJ_s (rget F1 Rs1) (rget F1 Rs4) = Z.geb (nn + i) n).
        { rgne. rgne. rewrite HF1s1. rewrite HF1s4. apply w32_bge_moi; lia. }
        destruct (Z.geb (nn + i) n) eqn:Hdone.
        + (* the loop is done: i + nn = n *)
          assert (Hge : (n <= nn + i)%Z) by (apply Z.geb_le; exact Hdone).
          assert (Hfin : (nn + i)%Z = n) by lia.
          assert (Htgt : add_vec (mword_of_int (CW + 0x5a) : mword 64)
                           (sign_extend' 64 (mword_of_int 18 : mword 13))
                         = mword_of_int (CW + 0x6c)) by pcw.
          iApply (wp_bge_taken_s_sconf (mword_of_int (CW + 0x5a))
                    (mword_of_int 18 : mword 13) Rs4 Rs1 F1 (av - 16)%nat true
                    ltac:(nz) ltac:(nz) ltac:(rewrite Hcmp; reflexivity)
                    ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
          { iApply (cnwi_5a with "Ht"). }
          iApply bi.later_intro. iIntros (CIDce Hsce) "Hcg Hpc".
          iEval (rewrite Htgt) in "Hpc".
          iDestruct (cw_ret_weaken (CID0 := CID0) jp m0 av eb pid V P1 n lks Hext1
                       with "Hcont") as "Hcont".
          iApply (cw_exit_done (CID := CIDce) CID0 jp m0 F1 av eb sp0 pid
                    (upd_upt V P1) n (nn + i)%Z lks
                    Hm0sp ltac:(destruct HF1regs as (Y1 & _); exact Y1)
                    HF1s1 HF1s11 ltac:(lia) Hav Heb Hal ltac:(wp_next_chain)
                    with "Ht Hcg Hcnt Hpc Hpriv Hsaved Hspill Hbuf Hcont").
        + (* another turn: fall through to the head at +0x5e *)
          assert (Hlt : (nn + i < n)%Z)
            by (rewrite Z.geb_leb in Hdone; apply Z.leb_gt in Hdone; lia).
          iApply (wp_bge_fall_s_sconf (mword_of_int (CW + 0x5a))
                    (mword_of_int 18 : mword 13) Rs4 Rs1 F1 (av - 16)%nat true
                    ltac:(nz) ltac:(nz) ltac:(rewrite Hcmp; reflexivity)
                    with "Hcg Hpc []").
          { iApply (cnwi_5a with "Ht"). }
          iIntros (CIDce Hsce) "Hcg Hpc".
          assert (Pbk : add_vec_int (mword_of_int (CW + 0x5a) : mword 64) 4
                        = mword_of_int (CW + 0x5e)) by pcw.
          iEval (rewrite Pbk) in "Hpc".
          iDestruct (cw_ret_weaken (CID0 := CID0) jp m0 av eb pid V P1 n _ Hext1
                       with "Hcont") as "Hcont".
          iApply (IH CIDce F1 (upd_upt V P1) (nn + i)%Z
                    ltac:(lia) ltac:(lia) HF1regs HF1s11 ltac:(wp_next_chain) Hbelow
                    with "Ht Hcg Hcnt Hpc Hpriv Hkenv Hdinv Htxl Hpinv
                          Hsaved Hspill Hbuf Hcont").
      - (* the copy failed: the branch IS taken, and [i] is the answer *)
        assert (Heqt : eq_vec (rget mf1 Ra0) (rget mf1 Rs8) = true).
        { rgne. rgne. rewrite Hrm1. rewrite Cs8. exact cw_eqv_m1_m1. }
        assert (Htgtb : add_vec (mword_of_int (CW + 0x4a) : mword 64)
                          (sign_extend' 64 (mword_of_int 58 : mword 13))
                        = mword_of_int (CW + 0x84)) by pcw.
        iApply (wp_beq_taken_s_sconf (mword_of_int (CW + 0x4a))
                  (mword_of_int 58 : mword 13) Rs8 Ra0 mf1 (av - 16)%nat true
                  ltac:(nz) ltac:(nz)
                  Heqt ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
        { iApply (cnwi_4a with "Ht"). }
        iApply bi.later_intro. iIntros (CIDc8 Hsc8) "Hcg Hpc".
        iEval (rewrite Htgtb) in "Hpc".
        iAssert (cw_buf sp0) with "[Hb1 Hb2]" as "Hbuf".
        { rewrite /cw_buf H32 (bytes_own_app (KTR := KT1)).
          iDestruct (bytes_own_of_name (KTR := KT1) nnN buf fb' with "Hb1") as "Hb1".
          iSplitL "Hb1"; [iExact "Hb1" | iExact "Hb2"]. }
        iDestruct (cw_ret_weaken (CID0 := CID0) jp m0 av eb pid V P1 n lks Hext1
                     with "Hcont") as "Hcont".
        iApply (cw_exit_break (CID := CIDc8) CID0 jp m0 mf1 av eb sp0 pid
                  (upd_upt V P1) n i lks
                  Hm0sp Csp Cs1 Hs11c ltac:(lia) Hav Heb Hal ltac:(wp_next_chain)
                  with "Ht Hcg Hcnt Hpc Hpriv Hsaved Hspill Hbuf Hcont"). }
    (* ---------------------------------------------------------------- *)
    (*  +0x5e .. +0x6a -- THE HEAD: nn := min 32 (n - i)                  *)
    (* ---------------------------------------------------------------- *)
    assert (P5e62 : add_vec_int (mword_of_int (CW + 0x5e) : mword 64) 4
                    = mword_of_int (CW + 0x62)) by pcw.
    (* +0x5e  subw a5,s4,s1 *)
    iApply (wp_subw_s_sconf (mword_of_int (CW + 0x5e)) Ra5 Rs4 Rs1
              M (av - 16)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnwi_5e with "Ht"). }
    iIntros (CIDh1 Hsh1) "Hcg Hpc". iEval (rgne) in "Hcg". iEval (rgne) in "Hcg".
    set (A1 := <[Regidx Ra5 := regval_into_reg
        (sign_extend' 64 (sub_vec (subrange_vec_dec (M !!! Regidx Rs4) 31 0 : mword 32)
                                  (subrange_vec_dec (M !!! Regidx Rs1) 31 0 : mword 32)))]> M).
    change (<[Regidx Ra5 := regval_into_reg
        (sign_extend' 64 (sub_vec (subrange_vec_dec (M !!! Regidx Rs4) 31 0 : mword 32)
                                  (subrange_vec_dec (M !!! Regidx Rs1) 31 0 : mword 32)))]> M) with A1.
    assert (HA1a5 : A1 !!! Regidx Ra5 = (mword_of_int (n - i) : mword 64)).
    { rewrite /A1 upd_eq Hs4 Hs1. apply w32_subw_moi; lia. }
    assert (HA1regs : cw_regs A1 (pa_stk sp0 16%nat) sp0 src n i).
    { unfold cw_regs; rewrite /A1;
        repeat (rewrite upd_ne; [| reg_neq]); split_and!;
        first [ exact Hsp | exact Hs0 | exact Hs1 | exact Hs4 | exact Hs5
              | exact Hs6 | exact Hs7 | exact Hs8 | exact Hs9 | exact Hs10 ]. }
    assert (HA1s11 : A1 !!! Regidx Rs11 = m0 !!! Regidx Rs11)
      by (rewrite /A1 upd_ne; [exact Hs11 | reg_neq]).
    iEval (rewrite P5e62) in "Hpc".
    (* +0x62  c.mv s2,a5 *)
    iApply (wp_cmv_s_sconf (mword_of_int (CW + 0x62)) Rs2 Ra5
              A1 (av - 16)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnwi_62 with "Ht"). }
    iIntros (CIDh2 Hsh2) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (A2 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx Ra5))]> A1).
    change (<[Regidx Rs2 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx Ra5))]> A1) with A2.
    assert (HA2s2 : A2 !!! Regidx Rs2 = (mword_of_int (n - i) : mword 64))
      by (rewrite /A2 upd_eq w32_zero_add; exact HA1a5).
    assert (HA2a5 : A2 !!! Regidx Ra5 = (mword_of_int (n - i) : mword 64))
      by (rewrite /A2 upd_ne; [exact HA1a5 | reg_neq]).
    assert (HA2regs : cw_regs A2 (pa_stk sp0 16%nat) sp0 src n i).
    { unfold cw_regs; rewrite /A2;
        repeat (rewrite upd_ne; [| reg_neq]);
        destruct HA1regs as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10);
        split_and!; first [ exact Y1 | exact Y2 | exact Y3 | exact Y4 | exact Y5
                          | exact Y6 | exact Y7 | exact Y8 | exact Y9 | exact Y10 ]. }
    assert (HA2s11 : A2 !!! Regidx Rs11 = m0 !!! Regidx Rs11)
      by (rewrite /A2 upd_ne; [exact HA1s11 | reg_neq]).
    assert (P6264 : add_vec_int (mword_of_int (CW + 0x62) : mword 64) 2
                    = mword_of_int (CW + 0x64)) by pcw.
    iEval (rewrite P6264) in "Hpc".
    (* +0x64  bge s9,a5 : is the chunk the whole remainder? *)
    assert (HA2s9 : A2 !!! Regidx Rs9 = (mword_of_int 32 : mword 64)).
    { destruct HA2regs as (_ & _ & _ & _ & _ & _ & _ & _ & Y9 & _). exact Y9. }
    assert (Hcmph : zopz0zKzJ_s (rget A2 Rs9) (rget A2 Ra5) = Z.geb 32 (n - i)).
    { rgne. rgne. rewrite HA2s9. rewrite HA2a5. apply w32_bge_moi; lia. }
    (* [destruct ... eqn:] REWRITES THE SCRUTINEE INSIDE THE IRIS CONTEXT TOO
       (durable-notes.md), so [Hcmph] already reads [... = true] / [... = false]
       in each branch: the leaf's premise closes by [reflexivity], and the
       [eqn:] fact is only good for the arithmetic. *)
    destruct (Z.geb 32 (n - i)) eqn:Hmin.
    - (* 32 >= n - i : the chunk is the remainder, s2 already holds it *)
      assert (Hmle : (n - i <= 32)%Z) by (apply Z.geb_le; exact Hmin).
      assert (Hnneq : nn = (n - i)%Z) by (unfold nn; lia).
      assert (Htgt38 : add_vec (mword_of_int (CW + 0x64) : mword 64)
                         (sign_extend' 64 (mword_of_int 8148 : mword 13))
                       = mword_of_int (CW + 0x38)) by pcw.
      iApply (wp_bge_taken_s_sconf (mword_of_int (CW + 0x64))
                (mword_of_int 8148 : mword 13) Ra5 Rs9 A2 (av - 16)%nat true
                ltac:(nz) ltac:(nz) ltac:(rewrite Hcmph; reflexivity)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (cnwi_64 with "Ht"). }
      iApply bi.later_intro. iIntros (CIDh3 Hsh3) "Hcg Hpc".
      iEval (rewrite Htgt38) in "Hpc".
      iApply ("BODY" $! CIDh3 A2 with "[%] [%] [%] [%] Hcg Hpc").
      + exact HA2regs.
      + rewrite HA2s2 Hnneq. reflexivity.
      + exact HA2s11.
      + wp_next_chain.
    - (* 32 < n - i : the chunk is 32, and s2 has to be reloaded from s10 *)
      assert (Hmgt : (32 < n - i)%Z)
        by (rewrite Z.geb_leb in Hmin; apply Z.leb_gt in Hmin; lia).
      assert (Hnneq : nn = 32%Z) by (unfold nn; lia).
      iApply (wp_bge_fall_s_sconf (mword_of_int (CW + 0x64))
                (mword_of_int 8148 : mword 13) Ra5 Rs9 A2 (av - 16)%nat true
                ltac:(nz) ltac:(nz) ltac:(rewrite Hcmph; reflexivity)
                with "Hcg Hpc []").
      { iApply (cnwi_64 with "Ht"). }
      iIntros (CIDh3 Hsh3) "Hcg Hpc".
      assert (P6468 : add_vec_int (mword_of_int (CW + 0x64) : mword 64) 4
                      = mword_of_int (CW + 0x68)) by pcw.
      iEval (rewrite P6468) in "Hpc".
      (* +0x68  c.mv s2,s10 *)
      iApply (wp_cmv_s_sconf (mword_of_int (CW + 0x68)) Rs2 Rs10
                A2 (av - 16)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (cnwi_68 with "Ht"). }
      iIntros (CIDh4 Hsh4) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (A3 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (A2 !!! Regidx Rs10))]> A2).
      change (<[Regidx Rs2 := regval_into_reg (add_vec zero_reg (A2 !!! Regidx Rs10))]> A2) with A3.
      assert (HA3s2 : A3 !!! Regidx Rs2 = (mword_of_int 32 : mword 64)).
      { rewrite /A3 upd_eq w32_zero_add.
        destruct HA2regs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Y10). exact Y10. }
      assert (HA3regs : cw_regs A3 (pa_stk sp0 16%nat) sp0 src n i).
      { unfold cw_regs; rewrite /A3;
          repeat (rewrite upd_ne; [| reg_neq]);
          destruct HA2regs as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10);
          split_and!; first [ exact Y1 | exact Y2 | exact Y3 | exact Y4 | exact Y5
                            | exact Y6 | exact Y7 | exact Y8 | exact Y9 | exact Y10 ]. }
      assert (HA3s11 : A3 !!! Regidx Rs11 = m0 !!! Regidx Rs11)
        by (rewrite /A3 upd_ne; [exact HA2s11 | reg_neq]).
      assert (P686a : add_vec_int (mword_of_int (CW + 0x68) : mword 64) 2
                      = mword_of_int (CW + 0x6a)) by pcw.
      iEval (rewrite P686a) in "Hpc".
      (* +0x6a  c.j -> +0x38 *)
      assert (Htgt38b : add_vec (mword_of_int (CW + 0x6a) : mword 64)
                          (sign_extend' 64 (sign_extend' 21
                             (concat_vec (mword_of_int 2023 : mword 11) ('b"0"))))
                        = mword_of_int (CW + 0x38)) by pcw.
      iApply (wp_cj_s_sconf (mword_of_int (CW + 0x6a))
                (sign_extend' 21 (concat_vec (mword_of_int 2023 : mword 11) ('b"0")))
                A3 (av - 16)%nat true ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (cnwi_6a with "Ht"). }
      iIntros (CIDh5 Hsh5). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt38b) in "Hpc".
      iApply ("BODY" $! CIDh5 A3 with "[%] [%] [%] [%] Hcg Hpc").
      + exact HA3regs.
      + rewrite HA3s2 Hnneq. reflexivity.
      + exact HA3s11.
      + wp_next_chain.
  Qed.

  (* =================================================================== *)
  (*  +0x00 .. +0x36 -- the prologue, the [n <= 0] exit, and the setup.   *)
  (* =================================================================== *)
  Lemma wp_consolewrite_sconf `{CID : CpuId}
      (γa : gname) (γf : gname) (γs : list gname) (jp : nat) (γlp : gname)
      (γu : uart_names) (γv : disk_names) (γl : gname)
      (m : regfile) (av : nat) (eb : bool)
      (pid : mword 32) (V : pprivate) (n : Z) (b : bool) (lks : gset string)
    : wp_consolewrite_sconf_body γa γf γs jp γlp γu γv γl m av eb pid V n b lks.
  Proof.
    cbv beta delta [wp_consolewrite_sconf_body].
    (* [Hbelow] is SpecConsolewrite.v's own [locks_below lks (lock_rank
       "proc")] premise -- see the companion note at [cw_loop] above for why
       "proc" (11), not "kmem" (13), is the cone's true floor. *)
    intros pcE pj ret_tgt Hj Hjlp Hlens Ha0 Ha2 Hnr Hav Heb Hbelow.
    iIntros "Hcg Hcnt #Ht Hpc Hpriv #Hkenv #Hdinv #Htxl #Hpinv Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    assert (Hbt : b = true) by (rewrite -Hbm; exact Heb).
    clear Hbm. subst b.
    assert (H231 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
    assert (H263 : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity).
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    (* ---- +0x00  c.addi16sp sp,-128 : the sixteen-slot frame ---- *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 56 : mword 6)))
                    = pa_stk sp0 16%nat).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 56 : mword 6) m av 16%nat true
              ltac:(lia) Hpush with "Hcg Hpc []").
    { iApply (cnwi_00 with "Ht"). }
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 56 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 56 : mword 6))))]> m) with A0.
    assert (HA0sp : A0 !!! Regidx csp_rs1 = pa_stk sp0 16%nat)
      by (rewrite /A0 upd_eq Hpush; reflexivity).
    assert (P02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (CW + 0x2)) by pcw.
    iEval (rewrite P02) in "Hpc".
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 &
                            F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & _)".
    iDestruct "F1" as (v1) "H1". iDestruct "F2" as (v2) "H2".
    iDestruct "F3" as (v3) "H3".
    assert (Hb1 : add_vec (pa_stk sp0 16%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (apply cw_slot_bridge; pcw).
    assert (Hb2 : add_vec (pa_stk sp0 16%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (apply cw_slot_bridge; pcw).
    assert (Hb3 : add_vec (pa_stk sp0 16%nat)
                    (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (apply cw_slot_bridge; pcw).
    assert (HA0ra : A0 !!! Regidx Rra = m !!! Regidx Rra)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    assert (HA0s0 : A0 !!! Regidx Rs0 = m !!! Regidx Rs0)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    assert (HA0s1 : A0 !!! Regidx Rs1 = m !!! Regidx Rs1)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    (* ---- +0x02 / +0x04 / +0x06 : ra, s0, s1 ---- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (CW + 0x2)) (mword_of_int 15 : mword 6) Rra
              A0 (av - 16)%nat v1 true with "Hcg Hpc [] [H1]").
    { iApply (cnwi_02 with "Ht"). }
    { iEval (rewrite HA0sp Hb1). iExact "H1". }
    iIntros (CID2 Hs2) "Hcg Hpc H1". iEval (rewrite HA0sp Hb1) in "H1".
    iEval (rgne) in "H1". iEval (rewrite HA0ra) in "H1".
    assert (P04 : add_vec_int (mword_of_int (CW + 0x2) : mword 64) 2
                  = mword_of_int (CW + 0x4)) by pcw.
    iEval (rewrite P04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (CW + 0x4)) (mword_of_int 14 : mword 6) Rs0
              A0 (av - 16)%nat v2 true with "Hcg Hpc [] [H2]").
    { iApply (cnwi_04 with "Ht"). }
    { iEval (rewrite HA0sp Hb2). iExact "H2". }
    iIntros (CID3 Hs3) "Hcg Hpc H2". iEval (rewrite HA0sp Hb2) in "H2".
    iEval (rgne) in "H2". iEval (rewrite HA0s0) in "H2".
    assert (P06 : add_vec_int (mword_of_int (CW + 0x4) : mword 64) 2
                  = mword_of_int (CW + 0x6)) by pcw.
    iEval (rewrite P06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (CW + 0x6)) (mword_of_int 13 : mword 6) Rs1
              A0 (av - 16)%nat v3 true with "Hcg Hpc [] [H3]").
    { iApply (cnwi_06 with "Ht"). }
    { iEval (rewrite HA0sp Hb3). iExact "H3". }
    iIntros (CID4 Hs4) "Hcg Hpc H3". iEval (rewrite HA0sp Hb3) in "H3".
    iEval (rgne) in "H3". iEval (rewrite HA0s1) in "H3".
    iAssert (cw_saved sp0 m) with "[H1 H2 H3]" as "Hsaved".
    { rewrite /cw_saved. iFrame "H1 H2 H3". }
    assert (P08 : add_vec_int (mword_of_int (CW + 0x6) : mword 64) 2
                  = mword_of_int (CW + 0x8)) by pcw.
    iEval (rewrite P08) in "Hpc".
    (* ---- +0x08  c.addi4spn s0,sp,128 : the frame pointer ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (CW + 0x8)) (Cregidx (mword_of_int 0))
              (mword_of_int 32 : mword 8) Rs0 A0 (av - 16)%nat true
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (cnwi_08 with "Ht"). }
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (A1 := <[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi4spn_imm (mword_of_int 32 : mword 8))))]> A0).
    change (<[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi4spn_imm (mword_of_int 32 : mword 8))))]> A0) with A1.
    assert (HA1s0 : A1 !!! Regidx Rs0 = sp0).
    { rewrite /A1 upd_eq HA0sp. unfold pa_stk, add_vec_int.
      rewrite add_vec_assoc.
      rewrite (_ : add_vec (mword_of_int (- (8 * Z.of_nat 16%nat)) : mword 64)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 32 : mword 8)))
                   = (mword_of_int 0 : mword 64)); [| pcw].
      apply bv_add_0_r. vm_compute. reflexivity. }
    assert (HA1sp : A1 !!! Regidx csp_rs1 = pa_stk sp0 16%nat)
      by (rewrite /A1 upd_ne; [exact HA0sp | reg_neq]).
    assert (HA1a2 : A1 !!! Regidx Ra2 = (mword_of_int n : mword 64)).
    { rewrite /A1 upd_ne; [| reg_neq]. rewrite /A0 upd_ne; [exact Ha2 | reg_neq]. }
    assert (HA1a0 : A1 !!! Regidx Ra0 = (mword_of_int 1 : mword 64)).
    { rewrite /A1 upd_ne; [| reg_neq]. rewrite /A0 upd_ne; [exact Ha0 | reg_neq]. }
    assert (HA1cs : forall c : mword 5, c <> csp_rs1 -> c <> Rs0 ->
                      A1 !!! Regidx c = m !!! Regidx c).
    { intros c N1 N2. rewrite /A1 upd_ne; [| reg_ne_side].
      rewrite /A0 upd_ne; [reflexivity | reg_ne_side]. }
    assert (P0a : add_vec_int (mword_of_int (CW + 0x8) : mword 64) 2
                  = mword_of_int (CW + 0xa)) by pcw.
    iEval (rewrite P0a) in "Hpc".
    (* ---- +0x0a  blez a2 ---- *)
    assert (Hcmp0 : zopz0zKzJ_s (zero_reg : mword 64) (rget A1 Ra2) = Z.geb 0 n).
    { rgne. rewrite HA1a2. apply w32_bge0_moi. lia. }
    destruct (Z.geb 0 n) eqn:Hb0z.
    - (* ======== n <= 0: [i] is 0 and nothing else happens ======== *)
      assert (Hn0 : (n <= 0)%Z) by (apply Z.geb_le in Hb0z; lia).
      assert (Htgt80 : add_vec (mword_of_int (CW + 0xa) : mword 64)
                         (sign_extend' 64 (mword_of_int 118 : mword 13))
                       = mword_of_int (CW + 0x80)) by pcw.
      iApply (wp_bge_x0_taken_s_sconf (mword_of_int (CW + 0xa))
                (mword_of_int 118 : mword 13) Ra2 A1 (av - 16)%nat true
                ltac:(nz) ltac:(rewrite Hcmp0; reflexivity)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (cnwi_0a with "Ht"). }
      iApply bi.later_intro. iIntros (CID6 Hs6) "Hcg Hpc".
      iEval (rewrite Htgt80) in "Hpc".
      (* +0x80  c.li s1,0 *)
      iApply (wp_cli_s_sconf (mword_of_int (CW + 0x80)) Rs1 (mword_of_int 0 : mword 6)
                (mword_of_int 0 : mword 64) A1 (av - 16)%nat true
                ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
      { iApply (cnwi_80 with "Ht"). }
      iIntros (CID7 Hs7) "Hcg Hpc".
      set (A2 := <[Regidx Rs1 := regval_into_reg (mword_of_int 0 : mword 64)]> A1).
      change (<[Regidx Rs1 := regval_into_reg (mword_of_int 0 : mword 64)]> A1) with A2.
      assert (HA2s1 : A2 !!! Regidx Rs1 = (mword_of_int 0 : mword 64))
        by (rewrite /A2 upd_eq; reflexivity).
      assert (HA2sp : A2 !!! Regidx csp_rs1 = pa_stk sp0 16%nat)
        by (rewrite /A2 upd_ne; [exact HA1sp | reg_neq]).
      assert (HA2hi : cw_cs_hi A2 m).
      { unfold cw_cs_hi. split_and!;
          (rewrite /A2 upd_ne; [| reg_neq]); apply HA1cs; reg_neq. }
      assert (P82 : add_vec_int (mword_of_int (CW + 0x80) : mword 64) 2
                    = mword_of_int (CW + 0x82)) by pcw.
      iEval (rewrite P82) in "Hpc".
      (* +0x82  c.j -> +0x96 *)
      assert (Htgt96 : add_vec (mword_of_int (CW + 0x82) : mword 64)
                         (sign_extend' 64 (sign_extend' 21
                            (concat_vec (mword_of_int 10 : mword 11) ('b"0"))))
                       = mword_of_int (CW + 0x96)) by pcw.
      iApply (wp_cj_s_sconf (mword_of_int (CW + 0x82))
                (sign_extend' 21 (concat_vec (mword_of_int 10 : mword 11) ('b"0")))
                A2 (av - 16)%nat true ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (cnwi_82 with "Ht"). }
      iIntros (CID8 Hs8). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt96) in "Hpc".
      iAssert (cw_rest sp0) with "[F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16]"
        as "Hrest".
      { rewrite /cw_rest. cbn [seq].
        iFrame "F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16".
        all: try done. }
      iApply (cw_epi (CID := CID8) CID jp m A2 av eb sp0 pid V n 0 lks
                Hspm HA2sp HA2s1 HA2hi ltac:(lia) Hav Heb ltac:(wp_next_chain)
                with "Ht Hcg Hcnt Hpc Hpriv Hsaved Hrest [Hcont]").
      (* [n <= 0]: the loop never runs, so [cw_epi] here never touches a
         lock and does not want [Hbelow]. *)
      { rewrite /cw_ret. iExact "Hcont". }
    - (* ======== n > 0: the shrink-wrapped saves and the loop ======== *)
      assert (Hnpos : (0 < n)%Z)
        by (rewrite Z.geb_leb in Hb0z; apply Z.leb_gt in Hb0z; lia).
      iApply (wp_bge_x0_fall_s_sconf (mword_of_int (CW + 0xa))
                (mword_of_int 118 : mword 13) Ra2 A1 (av - 16)%nat true
                ltac:(nz) ltac:(rewrite Hcmp0; reflexivity) with "Hcg Hpc []").
      { iApply (cnwi_0a with "Ht"). }
      iIntros (CID6 Hs6) "Hcg Hpc".
      assert (P0e : add_vec_int (mword_of_int (CW + 0xa) : mword 64) 4
                    = mword_of_int (CW + 0xe)) by pcw.
      iEval (rewrite P0e) in "Hpc".
      assert (Hq4 : add_vec (pa_stk sp0 16%nat)
                      (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))
                    = pa_stk sp0 4) by (apply cw_slot_bridge; pcw).
      iDestruct "F4" as (w4) "H4".
      iApply (wp_csdsp_s_sconf (mword_of_int (CW + 0xe)) (mword_of_int 12 : mword 6) Rs2
                A1 (av - 16)%nat w4 true with "Hcg Hpc [] [H4]").
      { iApply (cnwi_0e with "Ht"). }
      { iEval (rewrite HA1sp Hq4). iExact "H4". }
      iIntros (CIDs4 Hss4) "Hcg Hpc H4". iEval (rewrite HA1sp Hq4) in "H4".
      iEval (rgne) in "H4".
      iEval (rewrite (HA1cs Rs2 ltac:(reg_neq) ltac:(reg_neq))) in "H4".
      assert (Pw10 : add_vec_int (mword_of_int (CW + 0xe) : mword 64) 2
                    = mword_of_int (CW + 0x10)) by pcw.
      iEval (rewrite Pw10) in "Hpc".
      assert (Hq5 : add_vec (pa_stk sp0 16%nat)
                      (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
                    = pa_stk sp0 5) by (apply cw_slot_bridge; pcw).
      iDestruct "F5" as (w5) "H5".
      iApply (wp_csdsp_s_sconf (mword_of_int (CW + 0x10)) (mword_of_int 11 : mword 6) Rs3
                A1 (av - 16)%nat w5 true with "Hcg Hpc [] [H5]").
      { iApply (cnwi_10 with "Ht"). }
      { iEval (rewrite HA1sp Hq5). iExact "H5". }
      iIntros (CIDs5 Hss5) "Hcg Hpc H5". iEval (rewrite HA1sp Hq5) in "H5".
      iEval (rgne) in "H5".
      iEval (rewrite (HA1cs Rs3 ltac:(reg_neq) ltac:(reg_neq))) in "H5".
      assert (Pw12 : add_vec_int (mword_of_int (CW + 0x10) : mword 64) 2
                    = mword_of_int (CW + 0x12)) by pcw.
      iEval (rewrite Pw12) in "Hpc".
      assert (Hq6 : add_vec (pa_stk sp0 16%nat)
                      (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))
                    = pa_stk sp0 6) by (apply cw_slot_bridge; pcw).
      iDestruct "F6" as (w6) "H6".
      iApply (wp_csdsp_s_sconf (mword_of_int (CW + 0x12)) (mword_of_int 10 : mword 6) Rs4
                A1 (av - 16)%nat w6 true with "Hcg Hpc [] [H6]").
      { iApply (cnwi_12 with "Ht"). }
      { iEval (rewrite HA1sp Hq6). iExact "H6". }
      iIntros (CIDs6 Hss6) "Hcg Hpc H6". iEval (rewrite HA1sp Hq6) in "H6".
      iEval (rgne) in "H6".
      iEval (rewrite (HA1cs Rs4 ltac:(reg_neq) ltac:(reg_neq))) in "H6".
      assert (Pw14 : add_vec_int (mword_of_int (CW + 0x12) : mword 64) 2
                    = mword_of_int (CW + 0x14)) by pcw.
      iEval (rewrite Pw14) in "Hpc".
      assert (Hq7 : add_vec (pa_stk sp0 16%nat)
                      (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                    = pa_stk sp0 7) by (apply cw_slot_bridge; pcw).
      iDestruct "F7" as (w7) "H7".
      iApply (wp_csdsp_s_sconf (mword_of_int (CW + 0x14)) (mword_of_int 9 : mword 6) Rs5
                A1 (av - 16)%nat w7 true with "Hcg Hpc [] [H7]").
      { iApply (cnwi_14 with "Ht"). }
      { iEval (rewrite HA1sp Hq7). iExact "H7". }
      iIntros (CIDs7 Hss7) "Hcg Hpc H7". iEval (rewrite HA1sp Hq7) in "H7".
      iEval (rgne) in "H7".
      iEval (rewrite (HA1cs Rs5 ltac:(reg_neq) ltac:(reg_neq))) in "H7".
      assert (Pw16 : add_vec_int (mword_of_int (CW + 0x14) : mword 64) 2
                    = mword_of_int (CW + 0x16)) by pcw.
      iEval (rewrite Pw16) in "Hpc".
      assert (Hq8 : add_vec (pa_stk sp0 16%nat)
                      (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                    = pa_stk sp0 8) by (apply cw_slot_bridge; pcw).
      iDestruct "F8" as (w8) "H8".
      iApply (wp_csdsp_s_sconf (mword_of_int (CW + 0x16)) (mword_of_int 8 : mword 6) Rs6
                A1 (av - 16)%nat w8 true with "Hcg Hpc [] [H8]").
      { iApply (cnwi_16 with "Ht"). }
      { iEval (rewrite HA1sp Hq8). iExact "H8". }
      iIntros (CIDs8 Hss8) "Hcg Hpc H8". iEval (rewrite HA1sp Hq8) in "H8".
      iEval (rgne) in "H8".
      iEval (rewrite (HA1cs Rs6 ltac:(reg_neq) ltac:(reg_neq))) in "H8".
      assert (Pw18 : add_vec_int (mword_of_int (CW + 0x16) : mword 64) 2
                    = mword_of_int (CW + 0x18)) by pcw.
      iEval (rewrite Pw18) in "Hpc".
      assert (Hq9 : add_vec (pa_stk sp0 16%nat)
                      (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                    = pa_stk sp0 9) by (apply cw_slot_bridge; pcw).
      iDestruct "F9" as (w9) "H9".
      iApply (wp_csdsp_s_sconf (mword_of_int (CW + 0x18)) (mword_of_int 7 : mword 6) Rs7
                A1 (av - 16)%nat w9 true with "Hcg Hpc [] [H9]").
      { iApply (cnwi_18 with "Ht"). }
      { iEval (rewrite HA1sp Hq9). iExact "H9". }
      iIntros (CIDs9 Hss9) "Hcg Hpc H9". iEval (rewrite HA1sp Hq9) in "H9".
      iEval (rgne) in "H9".
      iEval (rewrite (HA1cs Rs7 ltac:(reg_neq) ltac:(reg_neq))) in "H9".
      assert (Pw1a : add_vec_int (mword_of_int (CW + 0x18) : mword 64) 2
                    = mword_of_int (CW + 0x1a)) by pcw.
      iEval (rewrite Pw1a) in "Hpc".
      assert (Hq10 : add_vec (pa_stk sp0 16%nat)
                      (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                    = pa_stk sp0 10) by (apply cw_slot_bridge; pcw).
      iDestruct "F10" as (w10) "H10".
      iApply (wp_csdsp_s_sconf (mword_of_int (CW + 0x1a)) (mword_of_int 6 : mword 6) Rs8
                A1 (av - 16)%nat w10 true with "Hcg Hpc [] [H10]").
      { iApply (cnwi_1a with "Ht"). }
      { iEval (rewrite HA1sp Hq10). iExact "H10". }
      iIntros (CIDs10 Hss10) "Hcg Hpc H10". iEval (rewrite HA1sp Hq10) in "H10".
      iEval (rgne) in "H10".
      iEval (rewrite (HA1cs Rs8 ltac:(reg_neq) ltac:(reg_neq))) in "H10".
      assert (Pw1c : add_vec_int (mword_of_int (CW + 0x1a) : mword 64) 2
                    = mword_of_int (CW + 0x1c)) by pcw.
      iEval (rewrite Pw1c) in "Hpc".
      assert (Hq11 : add_vec (pa_stk sp0 16%nat)
                      (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                    = pa_stk sp0 11) by (apply cw_slot_bridge; pcw).
      iDestruct "F11" as (w11) "H11".
      iApply (wp_csdsp_s_sconf (mword_of_int (CW + 0x1c)) (mword_of_int 5 : mword 6) Rs9
                A1 (av - 16)%nat w11 true with "Hcg Hpc [] [H11]").
      { iApply (cnwi_1c with "Ht"). }
      { iEval (rewrite HA1sp Hq11). iExact "H11". }
      iIntros (CIDs11 Hss11) "Hcg Hpc H11". iEval (rewrite HA1sp Hq11) in "H11".
      iEval (rgne) in "H11".
      iEval (rewrite (HA1cs Rs9 ltac:(reg_neq) ltac:(reg_neq))) in "H11".
      assert (Pw1e : add_vec_int (mword_of_int (CW + 0x1c) : mword 64) 2
                    = mword_of_int (CW + 0x1e)) by pcw.
      iEval (rewrite Pw1e) in "Hpc".
      assert (Hq12 : add_vec (pa_stk sp0 16%nat)
                      (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                    = pa_stk sp0 12) by (apply cw_slot_bridge; pcw).
      iDestruct "F12" as (w12) "H12".
      iApply (wp_csdsp_s_sconf (mword_of_int (CW + 0x1e)) (mword_of_int 4 : mword 6) Rs10
                A1 (av - 16)%nat w12 true with "Hcg Hpc [] [H12]").
      { iApply (cnwi_1e with "Ht"). }
      { iEval (rewrite HA1sp Hq12). iExact "H12". }
      iIntros (CIDs12 Hss12) "Hcg Hpc H12". iEval (rewrite HA1sp Hq12) in "H12".
      iEval (rgne) in "H12".
      iEval (rewrite (HA1cs Rs10 ltac:(reg_neq) ltac:(reg_neq))) in "H12".
      assert (Pw20 : add_vec_int (mword_of_int (CW + 0x1e) : mword 64) 2
                    = mword_of_int (CW + 0x20)) by pcw.
      iEval (rewrite Pw20) in "Hpc".
      (* the nine spill slots now hold s2..s10 *)
      iAssert (cw_spill sp0 m) with "[H4 H5 H6 H7 H8 H9 H10 H11 H12]" as "Hspill".
      { rewrite /cw_spill. iFrame "H4 H5 H6 H7 H8 H9 H10 H11 H12". }
      (* ---- +0x20 .. +0x36 : the loop's ten register roles ---- *)
      set (src := (m !!! Regidx Ra1 : mword 64)).
      (* +0x20  c.mv s6,a0 : user_src, the literal 1 *)
      iApply (wp_cmv_s_sconf (mword_of_int (CW + 0x20)) Rs6 Ra0
                A1 (av - 16)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (cnwi_20 with "Ht"). }
      iIntros (CIDg1 Hsg1) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (G1 := <[Regidx Rs6 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx Ra0))]> A1).
      change (<[Regidx Rs6 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx Ra0))]> A1) with G1.
      assert (HG1s6 : G1 !!! Regidx Rs6 = (mword_of_int 1 : mword 64))
        by (rewrite /G1 upd_eq w32_zero_add; exact HA1a0).
      assert (P22 : add_vec_int (mword_of_int (CW + 0x20) : mword 64) 2
                    = mword_of_int (CW + 0x22)) by pcw.
      iEval (rewrite P22) in "Hpc".
      (* +0x22  c.mv s7,a1 : the user source address *)
      iApply (wp_cmv_s_sconf (mword_of_int (CW + 0x22)) Rs7 Ra1
                G1 (av - 16)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (cnwi_22 with "Ht"). }
      iIntros (CIDg2 Hsg2) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (G2 := <[Regidx Rs7 := regval_into_reg (add_vec zero_reg (G1 !!! Regidx Ra1))]> G1).
      change (<[Regidx Rs7 := regval_into_reg (add_vec zero_reg (G1 !!! Regidx Ra1))]> G1) with G2.
      assert (HG1a1 : G1 !!! Regidx Ra1 = src).
      { rewrite /G1 upd_ne; [| reg_neq]. rewrite /src. apply HA1cs; reg_neq. }
      assert (HG2s7 : G2 !!! Regidx Rs7 = src)
        by (rewrite /G2 upd_eq w32_zero_add; exact HG1a1).
      assert (P24 : add_vec_int (mword_of_int (CW + 0x22) : mword 64) 2
                    = mword_of_int (CW + 0x24)) by pcw.
      iEval (rewrite P24) in "Hpc".
      (* +0x24  c.mv s4,a2 : the count *)
      iApply (wp_cmv_s_sconf (mword_of_int (CW + 0x24)) Rs4 Ra2
                G2 (av - 16)%nat true ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (cnwi_24 with "Ht"). }
      iIntros (CIDg3 Hsg3) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (G3 := <[Regidx Rs4 := regval_into_reg (add_vec zero_reg (G2 !!! Regidx Ra2))]> G2).
      change (<[Regidx Rs4 := regval_into_reg (add_vec zero_reg (G2 !!! Regidx Ra2))]> G2) with G3.
      assert (HG2a2 : G2 !!! Regidx Ra2 = (mword_of_int n : mword 64)).
      { rewrite /G2 upd_ne; [| reg_neq]. rewrite /G1 upd_ne; [| reg_neq]. exact HA1a2. }
      assert (HG3s4 : G3 !!! Regidx Rs4 = (mword_of_int n : mword 64))
        by (rewrite /G3 upd_eq w32_zero_add; exact HG2a2).
      assert (P26 : add_vec_int (mword_of_int (CW + 0x24) : mword 64) 2
                    = mword_of_int (CW + 0x26)) by pcw.
      iEval (rewrite P26) in "Hpc".
      (* +0x26  c.li s1,0 : i := 0 *)
      iApply (wp_cli_s_sconf (mword_of_int (CW + 0x26)) Rs1 (mword_of_int 0 : mword 6)
                (mword_of_int 0 : mword 64) G3 (av - 16)%nat true
                ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
      { iApply (cnwi_26 with "Ht"). }
      iIntros (CIDg4 Hsg4) "Hcg Hpc".
      set (G4 := <[Regidx Rs1 := regval_into_reg (mword_of_int 0 : mword 64)]> G3).
      change (<[Regidx Rs1 := regval_into_reg (mword_of_int 0 : mword 64)]> G3) with G4.
      assert (P28 : add_vec_int (mword_of_int (CW + 0x26) : mword 64) 2
                    = mword_of_int (CW + 0x28)) by pcw.
      iEval (rewrite P28) in "Hpc".
      (* +0x28  li s9,32 *)
      iApply (wp_li4_s_sconf (mword_of_int (CW + 0x28)) Rs9 (mword_of_int 32 : mword 12)
                (mword_of_int 32 : mword 64) G4 (av - 16)%nat true
                ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
      { iApply (cnwi_28 with "Ht"). }
      iIntros (CIDg5 Hsg5) "Hcg Hpc".
      set (G5 := <[Regidx Rs9 := regval_into_reg (mword_of_int 32 : mword 64)]> G4).
      change (<[Regidx Rs9 := regval_into_reg (mword_of_int 32 : mword 64)]> G4) with G5.
      assert (P2c : add_vec_int (mword_of_int (CW + 0x28) : mword 64) 4
                    = mword_of_int (CW + 0x2c)) by pcw.
      iEval (rewrite P2c) in "Hpc".
      (* +0x2c  li s10,32 *)
      iApply (wp_li4_s_sconf (mword_of_int (CW + 0x2c)) Rs10 (mword_of_int 32 : mword 12)
                (mword_of_int 32 : mword 64) G5 (av - 16)%nat true
                ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
      { iApply (cnwi_2c with "Ht"). }
      iIntros (CIDg6 Hsg6) "Hcg Hpc".
      set (G6 := <[Regidx Rs10 := regval_into_reg (mword_of_int 32 : mword 64)]> G5).
      change (<[Regidx Rs10 := regval_into_reg (mword_of_int 32 : mword 64)]> G5) with G6.
      assert (P30 : add_vec_int (mword_of_int (CW + 0x2c) : mword 64) 4
                    = mword_of_int (CW + 0x30)) by pcw.
      iEval (rewrite P30) in "Hpc".
      (* +0x30  addi s5,s0,-128 : &buf, i.e. the pushed sp *)
      iApply (wp_addi4_s_sconf (mword_of_int (CW + 0x30)) Rs5 Rs0
                (mword_of_int 3968 : mword 12) G6 (av - 16)%nat true
                ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (cnwi_30 with "Ht"). }
      iIntros (CIDg7 Hsg7) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (G7 := <[Regidx Rs5 := regval_into_reg
          (add_vec (G6 !!! Regidx Rs0) (sign_extend' 64 (mword_of_int 3968 : mword 12)))]> G6).
      change (<[Regidx Rs5 := regval_into_reg
          (add_vec (G6 !!! Regidx Rs0) (sign_extend' 64 (mword_of_int 3968 : mword 12)))]> G6) with G7.
      assert (HG6s0 : G6 !!! Regidx Rs0 = sp0).
      { rewrite /G6 upd_ne; [| reg_neq]. rewrite /G5 upd_ne; [| reg_neq].
        rewrite /G4 upd_ne; [| reg_neq]. rewrite /G3 upd_ne; [| reg_neq].
        rewrite /G2 upd_ne; [| reg_neq]. rewrite /G1 upd_ne; [| reg_neq]. exact HA1s0. }
      assert (HG7s5 : G7 !!! Regidx Rs5 = pa_stk sp0 16%nat).
      { rewrite /G7 upd_eq. unfold regval_into_reg. rewrite HG6s0.
        unfold pa_stk, add_vec_int. apply f_equal.
        apply bv_eq; vm_compute; reflexivity. }
      assert (P34 : add_vec_int (mword_of_int (CW + 0x30) : mword 64) 4
                    = mword_of_int (CW + 0x34)) by pcw.
      iEval (rewrite P34) in "Hpc".
      (* +0x34  c.li s8,-1 : the sentinel either_copyin is compared against *)
      iApply (wp_cli_s_sconf (mword_of_int (CW + 0x34)) Rs8 (mword_of_int 63 : mword 6)
                (mword_of_int (-1) : mword 64) G7 (av - 16)%nat true
                ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
      { iApply (cnwi_34 with "Ht"). }
      iIntros (CIDg8 Hsg8) "Hcg Hpc".
      set (G8 := <[Regidx Rs8 := regval_into_reg (mword_of_int (-1) : mword 64)]> G7).
      change (<[Regidx Rs8 := regval_into_reg (mword_of_int (-1) : mword 64)]> G7) with G8.
      assert (P36 : add_vec_int (mword_of_int (CW + 0x34) : mword 64) 2
                    = mword_of_int (CW + 0x36)) by pcw.
      iEval (rewrite P36) in "Hpc".
      (* +0x36  c.j -> the loop head at +0x5e *)
      assert (Htgt5e : add_vec (mword_of_int (CW + 0x36) : mword 64)
                         (sign_extend' 64 (sign_extend' 21
                            (concat_vec (mword_of_int 20 : mword 11) ('b"0"))))
                       = mword_of_int (CW + 0x5e)) by pcw.
      iApply (wp_cj_s_sconf (mword_of_int (CW + 0x36))
                (sign_extend' 21 (concat_vec (mword_of_int 20 : mword 11) ('b"0")))
                G8 (av - 16)%nat true ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (cnwi_36 with "Ht"). }
      iIntros (CIDg9 Hsg9). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt5e) in "Hpc".
      (* the ten roles, as [cw_regs] states them *)
      assert (HA9regs : cw_regs G8 (pa_stk sp0 16%nat) sp0 src n 0).
      { unfold cw_regs. split_and!.
        - rewrite /G8 upd_ne; [| reg_neq]. rewrite /G7 upd_ne; [| reg_neq].
          rewrite /G6 upd_ne; [| reg_neq]. rewrite /G5 upd_ne; [| reg_neq].
          rewrite /G4 upd_ne; [| reg_neq]. rewrite /G3 upd_ne; [| reg_neq].
          rewrite /G2 upd_ne; [| reg_neq]. rewrite /G1 upd_ne; [| reg_neq]. exact HA1sp.
        - rewrite /G8 upd_ne; [| reg_neq]. rewrite /G7 upd_ne; [| reg_neq]. exact HG6s0.
        - rewrite /G8 upd_ne; [| reg_neq]. rewrite /G7 upd_ne; [| reg_neq].
          rewrite /G6 upd_ne; [| reg_neq]. rewrite /G5 upd_ne; [| reg_neq].
          rewrite /G4 upd_eq. reflexivity.
        - rewrite /G8 upd_ne; [| reg_neq]. rewrite /G7 upd_ne; [| reg_neq].
          rewrite /G6 upd_ne; [| reg_neq]. rewrite /G5 upd_ne; [| reg_neq].
          rewrite /G4 upd_ne; [| reg_neq]. exact HG3s4.
        - rewrite /G8 upd_ne; [| reg_neq]. exact HG7s5.
        - rewrite /G8 upd_ne; [| reg_neq]. rewrite /G7 upd_ne; [| reg_neq].
          rewrite /G6 upd_ne; [| reg_neq]. rewrite /G5 upd_ne; [| reg_neq].
          rewrite /G4 upd_ne; [| reg_neq]. rewrite /G3 upd_ne; [| reg_neq].
          rewrite /G2 upd_ne; [| reg_neq]. exact HG1s6.
        - rewrite /G8 upd_ne; [| reg_neq]. rewrite /G7 upd_ne; [| reg_neq].
          rewrite /G6 upd_ne; [| reg_neq]. rewrite /G5 upd_ne; [| reg_neq].
          rewrite /G4 upd_ne; [| reg_neq]. rewrite /G3 upd_ne; [| reg_neq]. exact HG2s7.
        - rewrite /G8 upd_eq. reflexivity.
        - rewrite /G8 upd_ne; [| reg_neq]. rewrite /G7 upd_ne; [| reg_neq].
          rewrite /G6 upd_ne; [| reg_neq]. rewrite /G5 upd_eq. reflexivity.
        - rewrite /G8 upd_ne; [| reg_neq]. rewrite /G7 upd_ne; [| reg_neq].
          rewrite /G6 upd_eq. reflexivity. }
      assert (HA9s11 : G8 !!! Regidx Rs11 = m !!! Regidx Rs11).
      { rewrite /G8 upd_ne; [| reg_neq]. rewrite /G7 upd_ne; [| reg_neq].
        rewrite /G6 upd_ne; [| reg_neq]. rewrite /G5 upd_ne; [| reg_neq].
        rewrite /G4 upd_ne; [| reg_neq]. rewrite /G3 upd_ne; [| reg_neq].
        rewrite /G2 upd_ne; [| reg_neq]. rewrite /G1 upd_ne; [| reg_neq].
        apply HA1cs; reg_neq. }
      (* the four lowest slots become the 32-byte bounce buffer *)
      iAssert ([∗ list] k ∈ seq 0 4, ∃ w : mword 64, pa_stk sp0 (16 - k) ↦₈[KT1] w)%I
        with "[F13 F14 F15 F16]" as "Hbs".
      { cbn [seq]. iFrame "F16 F15 F14 F13". all: try done. }
      iDestruct (slotsn_bytes_own (KTR := KT1) sp0 16 4 ltac:(lia) with "Hbs") as "[%Hal Hbuf]".
      iApply (cw_loop (Z.to_nat n) CID γa γf γs jp γlp γl γu γv m av eb pid n sp0
                (m !!! Regidx Ra1) lks
                Hj Hjlp Hlens ltac:(exact (proj2 Hnr))
                Hav Heb Hspm Hal
                CIDg9 G8 V 0 ltac:(split; [apply Z.le_refl | exact Hnpos])
                ltac:(rewrite Z.sub_0_r; reflexivity)
                HA9regs HA9s11 ltac:(wp_next_chain) Hbelow
                with "Ht Hcg Hcnt Hpc Hpriv Hkenv Hdinv Htxl Hpinv
                      Hsaved Hspill [Hbuf] [Hcont]").
      { rewrite /cw_buf. change (8 * 4)%nat with 32%nat. iExact "Hbuf". }
      { rewrite /cw_ret. iExact "Hcont". }
  Qed.

End CwBodies.
End ConsolewriteProof.
