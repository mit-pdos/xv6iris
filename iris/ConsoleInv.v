(* ConsoleInv.v -- the console module's own state (kernel/console.c): the
   geometry of the [cons] global, the resource [cons.lock] protects, and the
   persistent credential [is_conslock] that consoleread -- and, when it is
   proved, consoleintr -- needs in order to touch any of it.

     #define INPUT_BUF_SIZE 128
     static struct {
       struct spinlock lock;
       char buf[INPUT_BUF_SIZE];
       uint r;   // read index
       uint w;   // write index
       uint e;   // edit index
     } cons;

   [cons] is a STATIC GLOBAL, not a kalloc'd page, so this file is much
   thinner than its model [PipeInvDefs.v]: there is no reference algebra, no
   cancellable lock and no reclamation.  The lock is an ordinary
   [WpLock.is_lock], its name field was sealed into the persistent
   [lock_name] by consoleinit (SpecConsoleinit.v hands exactly that back), and
   the credential is the whole of what a caller passes -- ONE persistent
   proposition, taken by value.

   ---- WHY THE RESOURCE IS UNCONSTRAINED ------------------------------

   [cons_res] owns the ring's 128 bytes and the three index words and says
   NOTHING that relates them.  That is not laziness, and it is worth being
   explicit about, because the obvious analogy -- [PipeInvDefs.pipe_count_ok],
   the "there are never more than PIPESIZE live bytes" coupling that
   piperead's and pipewrite's proofs maintain -- does not transfer:

   * NOTHING NEEDS IT.  The only address the code computes from an index is
     [cons.buf[cons.r % INPUT_BUF_SIZE]], and [% 128] is compiled as
     [andi a3,a5,127], so the index is in range for EVERY value of [cons.r].
     A pipe's [nread % PIPESIZE] is the same, but a pipe's writer has to know
     the slot it is about to fill is free; the console's writer tests
     [cons.e - cons.r < INPUT_BUF_SIZE] at run time instead.
   * NOTHING CONSUMES IT.  A coupling would be a statement about the console's
     LINE DISCIPLINE ("what was typed is what is read"), and no contract in
     the tree is in a position to observe one: consoleread's bytes leave
     through either_copyout into user memory, which this layer does not model.

   IT IS NOW ESTABLISHABLE, THOUGH, AND THAT IS A CHANGE.  Until xv6 `a28e94b`
   consoleintr called procdump, which is why it was assumed and why any
   coupling stated here would have been a property of an axiom.  That call is
   gone; consoleintr's callees are now exactly acquire / consputc / release /
   wakeup, all four proven and linked, so the writer of this ring is provable
   and the "nobody could" half of the argument has expired.  What is left is
   the "nobody needs" half above, which is the honest reason to keep the
   resource flat.

   So what the console publishes is exactly what it can back: the memory is
   there, one writer at a time reaches it, and a byte read out of it is some
   byte.  That is enough for consoleread's contract, which promises a RETURN
   VALUE RANGE and nothing about the bytes -- see SpecConsoleread.v, and
   [SpecFileread.fileread_ret], which is where the range is consumed.

   WHEN A CONSUMER ARRIVES, this is the file that grows the coupling, and
   there are exactly two places that must then maintain it: consoleintr's
   [cons.e - cons.r < INPUT_BUF_SIZE] guard before it appends, and
   consoleread's [cons.r--] end-of-file push-back at +0xe6 -- a DECREMENT, so
   "r never passes w" is not locally obvious there.  It is nonetheless safe:
   the push-back only ever undoes the [cons.r++] two instructions earlier.

   ---- WHERE IT COMES FROM AT BOOT ------------------------------------

   [is_conslock] is minted in [ProofMain.mn_grp_printk], immediately after the
   consoleinit call: that contract hands back the initialized lock word, the
   sealed [lock_name] and the cpu field -- exactly [WpLock.newlock]'s raw
   material -- and [cons_res] itself is a conjunct of
   [SpecMain.main_globals_raw], carved out of .bss by
   [BootCarveMain.boot_cons_res].  [UartTxInv.is_txlock] is minted in the same
   fupd, out of the [lk_fresh] the same call threads through from uartinit;
   the pair is [SpecConsoleintr.console_caps]. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvPtsto RiscvExtras.
Require Import WpLock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.


(* ------------------------------------------------------------------ *)
(*  Geometry                                                           *)
(* ------------------------------------------------------------------ *)

Definition INPUT_BUF_SIZE : nat := 128.

(* sizeof(struct spinlock): the ring starts right after the lock, which is
   the first member -- so [&cons.lock = &cons], the a0 consoleinit passes to
   initlock (SpecConsoleinit.v). *)
Definition cons_buf_off : nat := 24.

Definition a_cons : mword 64 := mword_of_int KernelSyms.cons.

(* the field addresses, in the EXACT [add_vec base (sign_extend' 64 imm)]
   form the lw/sw instructions compute (all three offsets fit the 12-bit
   immediate), so a load/store address unifies with the cell without
   rewriting -- [PipeInvDefs.poff_of]'s discipline. *)
Definition coff_of (a : mword 64) (i : Z) : mword 64 :=
  add_vec a (sign_extend' 64 (mword_of_int i : mword 12)).

Definition a_cons_r : mword 64 := coff_of a_cons 152.
Definition a_cons_w : mword 64 := coff_of a_cons 156.
Definition a_cons_e : mword 64 := coff_of a_cons 160.

(* &cons.r is the sleep channel: consoleread parks on it and consoleintr
   wakes it.  It is a static address, so it is trivially non-null -- which is
   what refutes sleep_prepare's [panic("sleep_prepare: zero chan")] arm. *)
Lemma a_cons_r_nz : eq_vec a_cons_r (zero_reg : mword 64) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma a_cons_nz : eq_vec a_cons (zero_reg : mword 64) = false.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  devsw[] -- THE DEVICE FUNCTION TABLE                                  *)
(*                                                                        *)
(*  A [struct devsw] is the two function pointers [read] and [write], so   *)
(*  entry [mj] starts at [devsw + 16*mj] and its two fields                *)
(*  sit at +0 and +8.  [NDEV] is 10, so the majors run 0..9, and CONSOLE   *)
(*  is 1 -- which is why consoleinit's two cells are [devsw + 16] and      *)
(*  [devsw + 24] ([SpecConsoleinit.devsw_console_read] / [_write]).        *)
(*                                                                        *)
(*  These live HERE and not with fileread/filewrite because they are the   *)
(*  console module's geometry: what the table holds is decided by          *)
(*  consoleinit and by the fact that nothing else ever writes it.  file.c  *)
(*  is a reader.                                                          *)
(* ===================================================================== *)

Definition NDEV_max : Z := 9.
Definition CONSOLE : Z := 1.

Definition a_devsw_read (mj : Z) : mword 64 :=
  mword_of_int (KernelSyms.devsw + 16 * mj).

Definition a_devsw_write (mj : Z) : mword 64 :=
  mword_of_int (KernelSyms.devsw + 16 * mj + 8).

(* WHAT EACH CELL HOLDS, as a function of the major.  [consoleinit] fills
   CONSOLE and NOTHING FILLS ANY OTHER ENTRY, so every other cell is still
   the BSS zero it booted with.  Stating the whole table this way -- rather
   than "null or consoleread", which is all a per-cell disjunction can say --
   is what lets a caller that has resolved the major to CONSOLE conclude it
   is about to call consoleread, and a caller that has resolved it to
   anything else conclude the slot is null and the C returns -1. *)
Definition devsw_read_val (mj : Z) : mword 64 :=
  if decide (mj = CONSOLE)
  then (mword_of_int KernelSyms.consoleread : mword 64)
  else (zero_reg : mword 64).

Definition devsw_write_val (mj : Z) : mword 64 :=
  if decide (mj = CONSOLE)
  then (mword_of_int KernelSyms.consolewrite : mword 64)
  else (zero_reg : mword 64).

(* the per-cell disjunction file.c's contracts are stated over, read off the
   table rather than assumed of it *)
Lemma devsw_read_val_cases (mj : Z) :
  devsw_read_val mj = (zero_reg : mword 64)
  \/ devsw_read_val mj = (mword_of_int KernelSyms.consoleread : mword 64).
Proof. rewrite /devsw_read_val. case_decide; [by right | by left]. Qed.

Lemma devsw_write_val_cases (mj : Z) :
  devsw_write_val mj = (zero_reg : mword 64)
  \/ devsw_write_val mj = (mword_of_int KernelSyms.consolewrite : mword 64).
Proof. rewrite /devsw_write_val. case_decide; [by right | by left]. Qed.

Lemma devsw_read_val_console :
  devsw_read_val CONSOLE = (mword_of_int KernelSyms.consoleread : mword 64).
Proof. rewrite /devsw_read_val. by case_decide. Qed.

Lemma devsw_write_val_console :
  devsw_write_val CONSOLE = (mword_of_int KernelSyms.consolewrite : mword 64).
Proof. rewrite /devsw_write_val. by case_decide. Qed.

Lemma devsw_read_val_other (mj : Z) :
  mj <> CONSOLE -> devsw_read_val mj = (zero_reg : mword 64).
Proof. intro H. rewrite /devsw_read_val. by case_decide. Qed.

Lemma devsw_write_val_other (mj : Z) :
  mj <> CONSOLE -> devsw_write_val mj = (zero_reg : mword 64).
Proof. intro H. rewrite /devsw_write_val. by case_decide. Qed.

Section ConsoleInv.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.

  (* the ring, byte by byte -- [PipeInvDefs.pipe_data]'s shape.  The contents
     are a list rather than a function so that a single-byte update is a
     [<[i := b]>] and the length premise stays where the accessor wants it. *)
  Definition cons_data (bs : list (bv 8)) : iProp Σ :=
    ([∗ list] j ↦ b ∈ bs, pa_add a_cons (cons_buf_off + j) ↦ₘ b)%I.

  Global Instance cons_data_timeless bs : Timeless (cons_data bs).
  Proof. apply _. Qed.

  Definition cons_res : iProp Σ :=
    (∃ (r w e : mword 32) (bs : list (bv 8)),
       a_cons_r ↦₄ r ∗
       a_cons_w ↦₄ w ∗
       a_cons_e ↦₄ e ∗
       ⌜length bs = INPUT_BUF_SIZE⌝ ∗
       cons_data bs)%I.

  Global Instance cons_res_timeless : Timeless cons_res.
  Proof. apply _. Qed.

  (* THE WHOLE CREDENTIAL.  Persistent, singleton, and taken by value: a
     caller of consoleread passes this and nothing else about the console. *)
  Definition is_conslock (γ : gname) : iProp Σ :=
    is_lock γ a_cons "cons"%string cons_res.

  Global Instance is_conslock_persistent γ : Persistent (is_conslock γ).
  Proof. apply _. Qed.

  (* =================================================================== *)
  (*  THE CONSOLE INVARIANT                                               *)
  (*                                                                      *)
  (*  [is_conslock] plus the WHOLE devsw table, at DISCARDED fractions --  *)
  (*  the table is written once, by consoleinit, and never again, so the   *)
  (*  cells can be given up for good and the bundle is then persistent.    *)
  (*  That is what a syscall needs: [sys_read] may be handed any           *)
  (*  descriptor, so it must own the read column before the major is       *)
  (*  known, and it must be able to hand a copy to every arm without       *)
  (*  splitting a fraction it would have to gather back.                   *)
  (*                                                                      *)
  (*  Duplicable ownership is also the only form that can survive the      *)
  (*  DEVICE ARM'S INDIRECT CALL: [devsw[major].read] is reached through a *)
  (*  register, so the cell is read and then the callee runs with the      *)
  (*  caller's resources; a fractional cell would have to be threaded      *)
  (*  through a call whose target is only known at the load.               *)
  (* =================================================================== *)
  Definition devsw_table : iProp Σ :=
    ([∗ list] i ∈ seq 0 (Z.to_nat NDEV_max + 1),
       a_devsw_read (Z.of_nat i) ↦₈□ devsw_read_val (Z.of_nat i) ∗
       a_devsw_write (Z.of_nat i) ↦₈□ devsw_write_val (Z.of_nat i))%I.

  Global Instance devsw_table_persistent : Persistent devsw_table.
  Proof. apply _. Qed.

  Definition console_inv (γ : gname) : iProp Σ :=
    (is_conslock γ ∗ devsw_table)%I.

  Global Instance console_inv_persistent γ : Persistent (console_inv γ).
  Proof. apply _. Qed.

  (* THE GNAME-FREE FORM, which is what a bundle carries.  The cons lock has
     exactly one gname for the lifetime of a boot, and no consumer needs to
     tie it to anything it already holds -- a caller of consoleread passes
     [is_conslock] by value and nothing else about the console.  So the name
     is existential here, and an arm that needs it destructs this ONCE and
     builds its callee's names record around what it got.  That is what keeps
     the console out of [fclose_names] (a positional record threaded through
     six files) and out of [FsReady.fs_ready]. *)
  Definition console_ready : iProp Σ := (∃ γ : gname, console_inv γ)%I.

  Global Instance console_ready_persistent : Persistent console_ready.
  Proof. apply _. Qed.

  Lemma console_ready_intro (γ : gname) : console_inv γ -∗ console_ready.
  Proof. iIntros "H". by iExists γ. Qed.

  (* the devsw half alone, which is all most consumers want *)
  Lemma console_ready_devsw : console_ready -∗ devsw_table.
  Proof. iIntros "H". iDestruct "H" as (γ) "[_ $]". Qed.

  Lemma console_inv_conslock (γ : gname) : console_inv γ -∗ is_conslock γ.
  Proof. by iIntros "[$ _]". Qed.

  Lemma console_inv_devsw (γ : gname) : console_inv γ -∗ devsw_table.
  Proof. by iIntros "[_ $]". Qed.

  (* ---- ONE ENTRY, at a major the caller has already bounded ---------- *)
  Local Lemma devsw_seq_lookup (mj : Z) :
    (0 <= mj <= NDEV_max)%Z ->
    seq 0 (Z.to_nat NDEV_max + 1) !! Z.to_nat mj = Some (Z.to_nat mj).
  Proof.
    intro H. apply lookup_seq. split; [reflexivity |].
    rewrite /NDEV_max in H |- *. lia.
  Qed.

  Lemma devsw_table_at (mj : Z) :
    (0 <= mj <= NDEV_max)%Z ->
    devsw_table -∗
    a_devsw_read mj ↦₈□ devsw_read_val mj ∗
    a_devsw_write mj ↦₈□ devsw_write_val mj.
  Proof.
    intro H. rewrite /devsw_table.
    iIntros "Ht".
    iDestruct (big_sepL_lookup _ _ (Z.to_nat mj) (Z.to_nat mj)
                 (devsw_seq_lookup mj H) with "Ht") as "Ht".
    rewrite (Z2Nat.id mj (proj1 H)). iExact "Ht".
  Qed.

  (* ---- WHAT consoleinit FINDS, MINUS ITS OWN TWO CELLS ---------------
     The eighteen entries consoleinit does not touch, still as the BSS left
     them.  Splitting them off this way is what keeps consoleinit's WALK
     unchanged: it goes on taking and storing its own two cells exactly as
     before, and only the postcondition's assembly is new.
     -------------------------------------------------------------------- *)
  Definition devsw_rest : iProp Σ :=
    ([∗ list] i ∈ seq 0 (Z.to_nat NDEV_max + 1),
       if decide (Z.of_nat i = CONSOLE) then emp else
         (a_devsw_read (Z.of_nat i) ↦₈ (zero_reg : mword 64) ∗
          a_devsw_write (Z.of_nat i) ↦₈ (zero_reg : mword 64)))%I.

  (* ---- THE EIGHTEEN, AS THE CARVE HANDS THEM OVER --------------------
     The boot carve produces named cells, one per [bss_cut]; this is the one
     place that turns them into the [big_sepL].  It lives HERE and not in
     [BootShared.v] on purpose: resolving the [decide] at each index needs
     the proposition NAMED ([decide_False (P := ...)]).  Written as
     [rewrite (decide_False _ _ ltac:(...))] the tactic is elaborated against
     an EVAR for [P], and [vm_compute] on an evar goal is what made
     BootShared.v diverge.  Ten cheap rewrites in a small file instead.
     -------------------------------------------------------------------- *)
  (* The two readings of [devsw_rest]'s body at a LITERAL index.  Stated as
     lemmas with no underscores on purpose: written inline as
     [rewrite (decide_False _ _ ltac:(done))] the branches stay as evars and
     the [ltac:] is elaborated against one, which is what made BootShared.v
     diverge -- and even when it does not, [rewrite] leaves the undetermined
     branch behind as an [iProp] GOAL. *)
  Local Lemma devsw_rest_body_ne (i : nat) : Z.of_nat i <> CONSOLE ->
    (if decide (Z.of_nat i = CONSOLE) then emp else
       (a_devsw_read (Z.of_nat i) ↦₈ (zero_reg : mword 64) ∗
        a_devsw_write (Z.of_nat i) ↦₈ (zero_reg : mword 64)))%I
    = (a_devsw_read (Z.of_nat i) ↦₈ (zero_reg : mword 64) ∗
       a_devsw_write (Z.of_nat i) ↦₈ (zero_reg : mword 64))%I.
  Proof. intro H. case_decide; [contradiction | reflexivity]. Qed.

  Local Lemma devsw_rest_body_eq :
    (if decide (Z.of_nat 1 = CONSOLE) then emp else
       (a_devsw_read (Z.of_nat 1) ↦₈ (zero_reg : mword 64) ∗
        a_devsw_write (Z.of_nat 1) ↦₈ (zero_reg : mword 64)))%I = emp%I.
  Proof. case_decide; [reflexivity | done]. Qed.

  (* ---- THE EIGHTEEN, AS THE CARVE HANDS THEM OVER --------------------
     The boot carve produces named cells, one per [bss_cut]; this is the one
     place that turns them into the [big_sepL], and it lives HERE and not in
     [BootShared.v] so the reduction happens in a file that compiles in
     seconds.
     -------------------------------------------------------------------- *)
  Lemma devsw_rest_intro :
    a_devsw_read (Z.of_nat 0) ↦₈ (zero_reg : mword 64) -∗
    a_devsw_write (Z.of_nat 0) ↦₈ (zero_reg : mword 64) -∗
    a_devsw_read (Z.of_nat 2) ↦₈ (zero_reg : mword 64) -∗
    a_devsw_write (Z.of_nat 2) ↦₈ (zero_reg : mword 64) -∗
    a_devsw_read (Z.of_nat 3) ↦₈ (zero_reg : mword 64) -∗
    a_devsw_write (Z.of_nat 3) ↦₈ (zero_reg : mword 64) -∗
    a_devsw_read (Z.of_nat 4) ↦₈ (zero_reg : mword 64) -∗
    a_devsw_write (Z.of_nat 4) ↦₈ (zero_reg : mword 64) -∗
    a_devsw_read (Z.of_nat 5) ↦₈ (zero_reg : mword 64) -∗
    a_devsw_write (Z.of_nat 5) ↦₈ (zero_reg : mword 64) -∗
    a_devsw_read (Z.of_nat 6) ↦₈ (zero_reg : mword 64) -∗
    a_devsw_write (Z.of_nat 6) ↦₈ (zero_reg : mword 64) -∗
    a_devsw_read (Z.of_nat 7) ↦₈ (zero_reg : mword 64) -∗
    a_devsw_write (Z.of_nat 7) ↦₈ (zero_reg : mword 64) -∗
    a_devsw_read (Z.of_nat 8) ↦₈ (zero_reg : mword 64) -∗
    a_devsw_write (Z.of_nat 8) ↦₈ (zero_reg : mword 64) -∗
    a_devsw_read (Z.of_nat 9) ↦₈ (zero_reg : mword 64) -∗
    a_devsw_write (Z.of_nat 9) ↦₈ (zero_reg : mword 64) -∗
    devsw_rest.
  Proof.
    iIntros "H0r H0w H2r H2w H3r H3w H4r H4w H5r H5w H6r H6w H7r H7w H8r H8w H9r H9w".
    rewrite /devsw_rest.
    change (Z.to_nat NDEV_max + 1)%nat with 10%nat.
    cbn [seq].
    rewrite !big_sepL_cons big_sepL_nil.
    rewrite devsw_rest_body_eq.
    rewrite (devsw_rest_body_ne 0 ltac:(done)).
    rewrite (devsw_rest_body_ne 2 ltac:(done)).
    rewrite (devsw_rest_body_ne 3 ltac:(done)).
    rewrite (devsw_rest_body_ne 4 ltac:(done)).
    rewrite (devsw_rest_body_ne 5 ltac:(done)).
    rewrite (devsw_rest_body_ne 6 ltac:(done)).
    rewrite (devsw_rest_body_ne 7 ltac:(done)).
    rewrite (devsw_rest_body_ne 8 ltac:(done)).
    rewrite (devsw_rest_body_ne 9 ltac:(done)).
    (* NAMED, in the big-op's index order -- index 1 is [CONSOLE], hence [emp]
       and no name.  A bare [iFrame] here searched all eighteen hypotheses
       against all ten elements of [devsw_rest]'s [big_sepL] and cost 4.0 s of
       this file's 8.4 s (optimization.md: "never bare [iFrame] in a large
       context"). *)
    iFrame "H0r H0w H2r H2w H3r H3w H4r H4w H5r H5w H6r H6w H7r H7w H8r H8w
            H9r H9w".
  Qed.

  (* ...and the table, once consoleinit's two stores have landed.  An
     update, because giving a fraction up for good is one. *)
  Lemma devsw_table_of_rest :
    devsw_rest -∗
    a_devsw_read CONSOLE ↦₈ (mword_of_int KernelSyms.consoleread : mword 64) -∗
    a_devsw_write CONSOLE ↦₈ (mword_of_int KernelSyms.consolewrite : mword 64) ==∗
    devsw_table.
  Proof.
    iIntros "Hrest Hr Hw".
    iMod (word_pointsto_persist with "Hr") as "#Hr".
    iMod (word_pointsto_persist with "Hw") as "#Hw".
    rewrite /devsw_table /devsw_rest.
    iApply big_sepL_bupd.
    (* [big_sepL_impl], NOT [big_sepL_mono]: the latter takes a Coq-level
       implication of entailments, so the two persisted CONSOLE cells -- the
       only thing this proof has to say about the one interesting index --
       are not in scope inside it. *)
    iApply (big_sepL_impl with "Hrest").
    iModIntro. iIntros (k i Hk) "H".
    assert (Hi : i = k) by (apply lookup_seq in Hk; lia). subst i.
    case_decide as Hc.
    - rewrite /devsw_read_val /devsw_write_val.
      rewrite !(decide_True _ _ Hc) Hc.
      iModIntro. iFrame "Hr Hw".
    - rewrite /devsw_read_val /devsw_write_val.
      rewrite !(decide_False _ _ Hc).
      iDestruct "H" as "[Hzr Hzw]".
      iMod (word_pointsto_persist with "Hzr") as "$".
      iMod (word_pointsto_persist with "Hzw") as "$".
      by iModIntro.
  Qed.

  (* ---- THE BOOT-SIDE CONSTRUCTOR ------------------------------------
     The twenty cells at full ownership -- consoleinit's two, holding the
     two function addresses it just stored, and the eighteen the BSS carve
     hands over still zero -- are given up for good and become the table.
     An update, because discarding a fraction is one ([word_pointsto_persist]).
     -------------------------------------------------------------------- *)
  Lemma devsw_table_alloc :
    ([∗ list] i ∈ seq 0 (Z.to_nat NDEV_max + 1),
       a_devsw_read (Z.of_nat i) ↦₈ devsw_read_val (Z.of_nat i) ∗
       a_devsw_write (Z.of_nat i) ↦₈ devsw_write_val (Z.of_nat i))
    ==∗ devsw_table.
  Proof.
    rewrite /devsw_table.
    iIntros "H".
    iApply big_sepL_bupd.
    iApply (big_sepL_mono with "H").
    iIntros (i x Hx) "[Hr Hw]".
    iMod (word_pointsto_persist with "Hr") as "$".
    iMod (word_pointsto_persist with "Hw") as "$".
    by iModIntro.
  Qed.

  (* ---- reading one byte out of the ring ----------------------------

     The index is [r & 127], so it is in range unconditionally; what the
     accessor has to bridge is the ADDRESS the code computes -- a base of
     [cons + idx] with the array's own +24 as the load's displacement -- and
     the [pa_add a_cons (24 + j)] the resource speaks in.  [cons_byte_addr]
     is that bridge, and it is stated over the [add_vec] form the leaf
     produces so the rewrite happens once, at the load. *)
  Lemma cons_data_acc (bs : list (bv 8)) (i : nat) (b : bv 8) :
    bs !! i = Some b ->
    cons_data bs -∗
    pa_add a_cons (cons_buf_off + i) ↦ₘ b ∗
    (pa_add a_cons (cons_buf_off + i) ↦ₘ b -∗ cons_data bs).
  Proof.
    intros Hlk. rewrite /cons_data.
    iApply (big_sepL_lookup_acc
              (fun (j : nat) (c : bv 8) =>
                 (pa_add a_cons (cons_buf_off + j) ↦ₘ c)%I) bs i b Hlk).
  Qed.

  (* ---- writing one byte into the ring -------------------------------
     consoleintr's [cons.buf[cons.e++ % INPUT_BUF_SIZE] = c].  The list
     shape is what makes this a [<[i := b']>] rather than a re-existential:
     the length premise the accessor wants is preserved by [insert], so a
     caller reassembles [cons_res] without re-deriving it. *)
  Lemma cons_data_upd (bs : list (bv 8)) (i : nat) (b b' : bv 8) :
    bs !! i = Some b ->
    cons_data bs -∗
    pa_add a_cons (cons_buf_off + i) ↦ₘ b ∗
    (pa_add a_cons (cons_buf_off + i) ↦ₘ b' -∗ cons_data (<[i := b']> bs)).
  Proof.
    intro Hlk. rewrite /cons_data. iIntros "H".
    iDestruct (big_sepL_insert_acc
                 (fun (j : nat) (c : bv 8) =>
                    (pa_add a_cons (cons_buf_off + j) ↦ₘ c)%I) bs i b Hlk
                 with "H") as "[Hb Hcl]".
    iFrame "Hb". iIntros "Hb". iApply ("Hcl" $! b' with "Hb").
  Qed.

  (* ---- the boot carve's shape --------------------------------------
     [BootCarve.boot_ran_mem_run] hands out a run indexed by a FUNCTION over
     [seq 0 n]; [cons_data] is stated over a LIST, because a single-byte
     update has to be an [insert] with the length premise preserved.  The
     two are the same big-op at [bs := f <$> seq 0 n], since [seq 0 n]'s
     element at position [j] IS [j].  This is the last piece the boot
     assembly needs to run [WpLock.newlock] over [cons_res]. *)
  Lemma cons_data_of_run (f : nat -> bv 8) (base : mword 64) :
    (forall j : nat, pa_add base j = pa_add a_cons (cons_buf_off + j)) ->
    ([∗ list] j ∈ seq 0 INPUT_BUF_SIZE, pa_add base j ↦ₘ f j)
    -∗ ∃ bs : list (bv 8), ⌜length bs = INPUT_BUF_SIZE⌝ ∗ cons_data bs.
  Proof.
    intro Hbase. iIntros "H". iExists (f <$> seq 0 INPUT_BUF_SIZE).
    iSplit; [iPureIntro; rewrite length_fmap length_seq; reflexivity |].
    rewrite /cons_data big_sepL_fmap.
    iApply (big_sepL_mono with "H").
    intros k j Hk. apply lookup_seq in Hk as [-> _]. rewrite Hbase. done.
  Qed.

  (* a ring index is always in range, so a byte is always there to be read *)
  Lemma cons_data_lookup_lt (bs : list (bv 8)) (i : nat) :
    length bs = INPUT_BUF_SIZE -> (i < INPUT_BUF_SIZE)%nat ->
    exists b, bs !! i = Some b.
  Proof.
    intros Hlen Hlt. apply lookup_lt_is_Some_2. rewrite Hlen. exact Hlt.
  Qed.

End ConsoleInv.

(* ---- the address arithmetic the load's base computation needs -------

   The code forms [a4 := cons + (r & 127)] with a [c.add] and then loads
   [lbu a4,24(a4)], i.e. [add_vec (add_vec cons idx) 24].  Both are
   64-bit wrapping adds, so the two ways of associating agree. *)
Lemma cons_byte_addr (i : nat) :
  (i < INPUT_BUF_SIZE)%nat ->
  add_vec (add_vec a_cons (mword_of_int (Z.of_nat i) : mword 64))
          (sign_extend' 64 (mword_of_int (Z.of_nat cons_buf_off) : mword 12))
  = pa_add a_cons (cons_buf_off + i).
Proof.
  intros Hlt.
  assert (Hse : (sign_extend' 64 (mword_of_int (Z.of_nat cons_buf_off) : mword 12))
                = (mword_of_int 24 : mword 64)) by (vm_compute; reflexivity).
  rewrite Hse.
  unfold pa_add, add_vec_int.
  apply bv_eq.
  rewrite !add_vec64_unsigned.
  rewrite !moi64_unsigned.
  rewrite !bv_wrap_add_idemp_l.
  rewrite !bv_wrap_add_idemp_r.
  assert (Hi : bv_wrap 64 (Z.of_nat i) = Z.of_nat i).
  { unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z.
    apply Z.mod_small. unfold INPUT_BUF_SIZE in Hlt. lia. }
  rewrite Hi. f_equal. unfold cons_buf_off.
  assert (Hc : bv_wrap 64 KernelSyms.cons = KernelSyms.cons)
    by (vm_compute; reflexivity).
  rewrite Hc. lia.
Qed.
