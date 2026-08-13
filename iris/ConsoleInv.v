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

   ---- WHAT IS OWED AT BOOT -------------------------------------------

   Nothing mints [is_conslock] yet.  consoleinit's contract
   ([SpecConsoleinit.v]) already hands back the initialized lock word, the
   sealed [lock_name] and the cpu field -- i.e. exactly [WpLock.newlock]'s
   raw material -- but the ring's own storage (the 128 bytes and the three
   words carved here) belongs to whoever owns the .bss, and the boot assembly
   that runs [newlock] over [cons_res] does not exist.  This is the same debt
   [UartTxInv.is_txlock] carries, and it is discharged in the same place; see
   claude-notes/projects/uart-driver.md. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import WpLock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
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

Section ConsoleInv.
  Context `{!riscvGS Σ, !lockG Σ}.

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
