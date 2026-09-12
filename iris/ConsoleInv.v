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

   ---- WHAT THE RESOURCE COUPLES --------------------------------------

   [cons_res] owns the ring's 128 bytes, the three index words, and a TAG
   COLUMN [ts] of 128 slots beside the bytes, and it relates them: every
   slot the indices say is LIVE holds a byte the UART really delivered,
   together with the application's persistent claim about the history it
   arrived at ([RiscvPtsto.riscv_rx_tag], the column [WpUart.uart_col]
   keeps beside [u_rx]).  Two clauses say it.

   * [cons_ok r w e] -- the three counters, in the order the line
     discipline keeps them: [r <= w <= e <= r + INPUT_BUF_SIZE].  IT IS
     STATED ON THE 32-BIT DIFFERENCES, not on the counters' values.  The
     counters are C [uint]s that are only ever incremented, so they wrap,
     and after a wrap [uint r <= uint e] is simply false; what the code
     computes and compares is [cons.e - cons.r] as a 32-bit subtraction
     ([c.subw] at consoleintr +0x03e, then [bltu] against 127), and that
     difference is exactly what survives the wrap.  So the clause is
     [uint (e - r) <= INPUT_BUF_SIZE] with [uint (w - r) <= uint (e - r)],
     and the guard the code runs IS the clause's premise.
   * [cons_row r e bs ts] -- for every offset [k] into the live range
     [0 <= k < uint (e - r)], the slot [cons_slot r k] (the ring index of
     the byte at logical position [r + k], which is [(r + k) mod 128]
     because 128 divides 2^32) holds a tagged byte: [ts] has a [Some h]
     there, [h] ends in an [ObsUartIn Uart0 b], and [bs] has [cons_xlate b].
     [cons_xlate] is the ONE translation consoleintr applies before the
     store ([c = (c == '\r') ? '\n' : c]).  Slots outside the live range
     carry [None] or a stale [Some]; the row says nothing about them, and
     nothing has to clear them.

   WHO MAINTAINS IT.  Four places, and every one of them already runs the
   test its clause needs:

   * consoleintr's [cons.e - cons.r < INPUT_BUF_SIZE] guard at +0x044,
     before the append: it is exactly [uint (e - r) <= 127], so the
     [cons.e++] that follows lands at [uint (e - r) <= 128] and the new
     slot [cons_slot r (uint (e - r))] is one no live offset already
     names.  The byte stored there is [cons_xlate] of the byte in a0 and
     the tag filed beside it is that byte's, which is what
     [SpecConsoleintr]'s tag premise hands in;
   * consoleintr's [cons.e--] at +0x0c8 (the C('U') kill loop) and +0x120
     (the backspace arm).  Both are guarded by [cons.e != cons.w], which
     with [uint (w - r) <= uint (e - r)] gives [uint (e - r) >= 1]: the
     decrement cannot take [e] below [w].  The live range shrinks, so the
     row is inherited and the dropped slot's tag is simply left in [ts];
   * consoleintr's [cons.w = cons.e] in the wake tail, which moves [w] up
     to [e] and touches neither the row nor the ring;
   * consoleread's [cons.r++] in the copy loop -- guarded by
     [cons.r != cons.w], so [uint (w - r) >= 1] and the pop cannot pass
     [w] -- and its [cons.r--] end-of-file push-back at +0x0e6.  The
     push-back is a DECREMENT, so "r never passes w" is not locally
     obvious there; it is nonetheless safe because it only ever undoes the
     [cons.r++] two instructions earlier, and the slot's tag is still in
     [ts], so the row comes back with it.

   WHAT THE COUPLING BUYS is consoleread's post: the [d] bytes it copied
   out are [d] bytes the UART delivered, in order, with their tags
   ([SpecConsoleread.v]), and the read syscall's console receipt carries
   those tags to the process ([SpecFileread.console_receipt]).  The tags
   are PERSISTENT, so handing one to a reader costs the ring nothing and
   the pop does not have to clear the column.

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
Require Import RiscvLang ObsTrace.   (* [mobs], [obs_ends_in Uart0]: the tag column's vocabulary *)
Require Import VcGen.   (* [trunc32_unsigned]/[trunc32_sext]: the ring index's wrap *)
Require Import WpLock.
Require Export UartNames.   (* [uart_names]: the receive side's ghost names;
                               the ring's high-water mark is one of them *)
From iris.base_logic.lib Require Import ghost_var own.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import mono_nat.   (* the ring's dirty marker: [cons_dirty_lb] *)
Require Import TsoCtx CtxMorphTac.   (* the lock payload's context axis; [<{ }>] *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.


(* ------------------------------------------------------------------ *)
(*  Geometry                                                           *)
(* ------------------------------------------------------------------ *)

Definition INPUT_BUF_SIZE : nat := 128.

(* [cons_names] -- the ring's three ghost names -- is in [UartNames.v],
   with the receive side's, so that [FsCfg] can carry it. *)

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
(*  THE COUPLING, AS PURE ARITHMETIC                                      *)
(*                                                                        *)
(*  Three definitions, all outside the Iris section because every one of   *)
(*  them is a fact about words and lists: the header's two clauses and     *)
(*  the slot function they are indexed by.                                 *)
(* ===================================================================== *)

(* THE ONE TRANSLATION consoleintr applies before it stores:
   [c = (c == '\r') ? '\n' : c].  Everything the ring says about a
   buffered byte is said about the byte AFTER this. *)
Definition cons_xlate (b : bv 8) : bv 8 :=
  if decide (b = (mword_of_int 13 : mword 8))
  then (mword_of_int 10 : mword 8) else b.

(* the two readings, as lemmas rather than a [destruct (decide ...)] at
   each use: the instance term inside this definition is not the one a
   consumer's [decide] elaborates to, though the two print identically
   (durable-notes, "Terms that print identically"). *)
Lemma cons_xlate_cr :
  cons_xlate (mword_of_int 13 : mword 8) = (mword_of_int 10 : mword 8).
Proof. rewrite /cons_xlate. by case_decide. Qed.

Lemma cons_xlate_other (b : bv 8) :
  b <> (mword_of_int 13 : mword 8) -> cons_xlate b = b.
Proof. intro H. rewrite /cons_xlate. by case_decide. Qed.

(* THE THREE COUNTERS.  Stated on the 32-BIT DIFFERENCES, which is what
   survives the wrap and what the code computes -- see the header. *)
Definition cons_ok (r w e : mword 32) : Prop :=
  (bv_unsigned (sub_vec w r) <= bv_unsigned (sub_vec e r)
   <= Z.of_nat INPUT_BUF_SIZE)%Z.

(* THE SLOT the byte at logical position [r + k] lives in.  The code
   computes it as [andi ...,127] on the counter itself; 128 divides 2^32,
   so the 32-bit wrap is invisible to it and this is the same number. *)
Definition cons_slot (r : mword 32) (k : Z) : nat :=
  Z.to_nat ((bv_unsigned r + k) mod Z.of_nat INPUT_BUF_SIZE).

(* THE LIVE RANGE'S ROW.  Nothing is said of a slot outside it. *)
Definition cons_row (r e : mword 32) (bs : list (bv 8))
    (ts : list (option (list mobs))) : Prop :=
  forall k : Z, (0 <= k < bv_unsigned (sub_vec e r))%Z ->
    exists (h : list mobs) (b : bv 8),
      ts !! cons_slot r k = Some (Some h)
      /\ obs_ends_in Uart0 h b
      /\ bs !! cons_slot r k = Some (cons_xlate b).

(* WHAT A CONSUMER OF THE RING CARRIES AWAY.  A copy-out run is keyed by a
   SOURCE FUNCTION ([UserPtTree.umem_wr]'s [src]), so the ledger a reader
   hands its caller is stated over that function and not over an image:
   the [j]th byte delivered is the [j]th tag's byte, translated.  The
   image form is the receipt's ([SpecFileread.console_receipt]), which
   this becomes at the one place the run's linearity is known. *)
Definition cons_tagged (bs : nat -> bv 8) (hs : list (list mobs)) (d : nat)
  : Prop :=
  length hs = d
  /\ forall j : nat, (j < d)%nat ->
       exists (h : list mobs) (b : bv 8),
         hs !! j = Some h /\ obs_ends_in Uart0 h b /\ bs j = cons_xlate b.

Lemma cons_tagged_0 (bs : nat -> bv 8) : cons_tagged bs [] 0.
Proof. split; [reflexivity | intros j Hj; exfalso; lia]. Qed.

(* =====================================================================
   THE STORED SEQUENCE AND THE CONSUMPTION CURSOR  (app-echo.md, lane
   CONS-CURSOR, C2)

   The row above says WHICH BYTES are in the ring; it says nothing about
   the ORDER they arrived in, and a reader that copies [d] of them learns
   only that each one arrived at some history.  What a program reading the
   console needs is stronger and is stated here: the ring's bytes are a
   SEQUENCE, the reader has a CURSOR into it, and consecutive reads return
   consecutive elements.

   THE SEQUENCE IS THE COMMITTED BYTES, NOT THE RING'S LIVE RANGE.  The
   ring has two regions and they behave differently.  [r .. w) is
   COMMITTED: consoleread reads up to [w] and nothing ever takes a byte
   back out of it, because both of consoleintr's [cons.e--]s are guarded by
   [cons.e != cons.w].  [w .. e) is the LINE BEING EDITED: backspace and
   C('U') shorten it.  An append-only ghost list can model the first and
   cannot model the second, so [stored] covers [r .. w) only, and the
   editable window rides beside it as an ORDINARY existential list [pd]
   that shrinks with [cons.e].  THE ONE TRANSITION THAT EXTENDS [stored] IS
   [cons.w = cons.e] -- the wake tail, reached from the '\n', the C('D')
   and the ring-full arms -- which moves the whole of [pd] onto the end of
   [stored] at once.  Nothing else touches it: the store at [cons.e++]
   extends [pd], the two [cons.e--]s pop [pd]'s tail, and consoleread's
   [cons.r++] moves the CURSOR, not the list.

   FOUR CLAUSES.
   * [cons_stored r w n st bs ts] -- the committed region: [st] has
     [n + (w - r)] entries, the cursor [n] counts the bytes already
     consumed, and the [k]th unconsumed byte (slot [cons_slot r k]) is
     [st !! (n + k)] -- its history in [ts], its byte in [bs] translated.
   * [cons_pend r w e pd bs ts] -- the same for the editable window, keyed
     from [w].
   * [cons_chain (st ++ pd)] -- THE ORDER: along the whole stored sequence
     the histories strictly extend one another.  This is what makes the
     bytes a sequence of input events rather than a bag, and it is
     inherited from the UART column's own chain, one byte at a time.
   * [cons_below (st ++ pd) hh] -- everything stored is at or before the
     HIGH-WATER MARK [hh], whose other half rides in the PLIC payload
     beside the receive token.  That half is the only thing that can tell
     consoleintr that the byte it is about to file is NEWER than every byte
     the ring already holds: two persistent bounds on the run's history are
     comparable but do not say WHICH came first, and the ring's own picture
     can be arbitrarily stale.  The exclusive pair says it. *)

Definition cons_stored (r w : mword 32) (n : nat)
    (st : list (list mobs * bv 8)) (bs : list (bv 8))
    (ts : list (option (list mobs))) : Prop :=
  length st = (n + Z.to_nat (bv_unsigned (sub_vec w r)))%nat
  /\ forall k : Z, (0 <= k < bv_unsigned (sub_vec w r))%Z ->
       exists (h : list mobs) (b : bv 8),
         st !! (n + Z.to_nat k)%nat = Some (h, b)
         /\ ts !! cons_slot r k = Some (Some h)
         /\ obs_ends_in Uart0 h b
         /\ bs !! cons_slot r k = Some (cons_xlate b).

Definition cons_pend (r w e : mword 32)
    (pd : list (list mobs * bv 8)) (bs : list (bv 8))
    (ts : list (option (list mobs))) : Prop :=
  length pd = Z.to_nat (bv_unsigned (sub_vec e w))
  /\ forall j : nat, (j < length pd)%nat ->
       exists (h : list mobs) (b : bv 8),
         pd !! j = Some (h, b)
         /\ ts !! cons_slot r (bv_unsigned (sub_vec w r) + Z.of_nat j)
            = Some (Some h)
         /\ obs_ends_in Uart0 h b
         /\ bs !! cons_slot r (bv_unsigned (sub_vec w r) + Z.of_nat j)
            = Some (cons_xlate b).

Definition cons_chain (l : list (list mobs * bv 8)) : Prop :=
  forall (i j : nat) (hi hj : list mobs) (bi bj : bv 8),
    l !! i = Some (hi, bi) -> l !! j = Some (hj, bj) -> (i < j)%nat ->
    hist_ext hi hj.

Definition cons_below (l : list (list mobs * bv 8))
    (hh : option (list mobs)) : Prop :=
  forall (j : nat) (h : list mobs) (b : bv 8),
    l !! j = Some (h, b) -> ohist_le (Some h) hh.

(* THE WINDOW A READ HANDS BACK.  [l] is a lower bound on the stored
   sequence -- a list every later bound agrees with on every index it has,
   which is what makes two successive reads' windows CONSECUTIVE -- and the
   read of [d] bytes at cursor [n] delivered exactly [l !! n .. l !! n+d).
   [length l = n + d] pins the window to the END of the bound, so a caller
   that holds two of them can line them up by length alone. *)
Definition cons_window (l : list (list mobs * bv 8)) (n d : nat)
    (bs : nat -> bv 8) (hs : list (list mobs)) : Prop :=
  length l = (n + d)%nat
  /\ length hs = d
  /\ forall j : nat, (j < d)%nat ->
       exists (h : list mobs) (b : bv 8),
         l !! (n + j)%nat = Some (h, b)
         /\ hs !! j = Some h
         /\ obs_ends_in Uart0 h b
         /\ bs j = cons_xlate b.

Lemma cons_window_0 (l : list (list mobs * bv 8)) (n : nat)
    (bs : nat -> bv 8) :
  length l = n -> cons_window l n 0 bs [].
Proof.
  intro Hl. split_and!; [lia | reflexivity | intros j Hj; exfalso; lia].
Qed.

(* the chain survives taking a prefix, which is what lets a reader that
   holds a lower bound of the stored sequence read the order off it *)
Lemma cons_chain_prefix (l1 l2 : list (list mobs * bv 8)) :
  l1 `prefix_of` l2 -> cons_chain l2 -> cons_chain l1.
Proof.
  intros [k ->] Hch i j hi hj bi bj Hi Hj Hij.
  apply (Hch i j hi hj bi bj); [| | exact Hij];
    by apply lookup_app_l_Some.
Qed.

(* the same, for the "everything here is at or before [hh]" clause *)
Lemma cons_below_prefix (l1 l2 : list (list mobs * bv 8))
    (hh : option (list mobs)) :
  l1 `prefix_of` l2 -> cons_below l2 hh -> cons_below l1 hh.
Proof.
  intros [k ->] Hb j h b Hj.
  apply (Hb j h b). by apply lookup_app_l_Some.
Qed.

(* THE STORE'S TWO PURE OBLIGATIONS, once.  consoleintr files a byte whose
   history is strictly newer than the ring's high-water mark, and the mark
   is at or after everything the ring holds -- so the byte is strictly
   after every byte in the ring, which is exactly what extends the chain
   and moves the mark to the byte just filed. *)
Lemma cons_chain_snoc (l : list (list mobs * bv 8))
    (hh : option (list mobs)) (h : list mobs) (b : bv 8) :
  cons_chain l -> cons_below l hh -> ohist_ext hh h ->
  cons_chain (l ++ [(h, b)]).
Proof.
  intros Hch Hbl Hx i j hi hj bi bj Hi Hj Hij.
  pose proof (lookup_lt_Some _ _ _ Hj) as Hjl0.
  rewrite length_app in Hjl0. cbn [length] in Hjl0.
  assert (Hil : (i < length l)%nat) by lia.
  rewrite lookup_app_l in Hi; [| exact Hil].
  destruct (decide (j < length l)%nat) as [Hjl | Hjl].
  - rewrite lookup_app_l in Hj; [| exact Hjl].
    exact (Hch i j hi hj bi bj Hi Hj Hij).
  - assert (Hje : j = length l) by lia. subst j.
    rewrite lookup_app_r in Hj; [| lia].
    rewrite Nat.sub_diag in Hj. cbn in Hj.
    injection Hj as <- <-.
    exact (ohist_ext_le_ext (Some hi) hh h (Hbl i hi bi Hi) Hx).
Qed.

Lemma cons_below_snoc (l : list (list mobs * bv 8))
    (hh : option (list mobs)) (h : list mobs) (b : bv 8) :
  cons_below l hh -> ohist_ext hh h ->
  cons_below (l ++ [(h, b)]) (Some h).
Proof.
  intros Hbl Hx j g c Hj.
  pose proof (lookup_lt_Some _ _ _ Hj) as Hjl0.
  rewrite length_app in Hjl0. cbn [length] in Hjl0.
  destruct (decide (j < length l)%nat) as [Hjl | Hjl].
  - rewrite lookup_app_l in Hj; [| exact Hjl].
    destruct (ohist_ext_le_ext (Some g) hh h (Hbl j g c Hj) Hx) as [Hp _].
    exact Hp.
  - assert (Hje : j = length l) by lia. subst j.
    rewrite lookup_app_r in Hj; [| lia].
    rewrite Nat.sub_diag in Hj. cbn in Hj.
    injection Hj as <- <-. exact (ohist_le_Some h).
Qed.

(* =====================================================================
   THE COUPLING'S ARITHMETIC

   Every clause above is a statement about [bv_unsigned (sub_vec _ _)] at
   width 32, and every move either maintainer makes shifts ONE endpoint by
   one.  The kit is here, once, so that neither proof does modular
   arithmetic inline.  [lia] cannot evaluate [2 ^ 32], so each proof that
   needs the literal asserts it (durable-notes, "Arithmetic").
   ===================================================================== *)

Lemma cons_bufz : Z.of_nat INPUT_BUF_SIZE = 128.
Proof. vm_compute. reflexivity. Qed.

Lemma cons_bvw (z : Z) : bv_wrap 32 z = z mod 2 ^ 32.
Proof. reflexivity. Qed.

Lemma cons_urange (x : mword 32) : (0 <= bv_unsigned x < 2 ^ 32)%Z.
Proof. exact (bv_unsigned_in_range _ x). Qed.

Lemma cons_subz (x y : mword 32) :
  bv_unsigned (sub_vec x y) = ((bv_unsigned x - bv_unsigned y) mod 2 ^ 32)%Z.
Proof. rewrite sub_vec32_unsigned. apply cons_bvw. Qed.

Lemma cons_addz (x y : mword 32) :
  bv_unsigned (add_vec x y) = ((bv_unsigned x + bv_unsigned y) mod 2 ^ 32)%Z.
Proof. rewrite (add_vec_unsigned x y). apply cons_bvw. Qed.

Lemma cons_u1 : bv_unsigned (mword_of_int 1 : mword 32) = 1%Z.
Proof. rewrite moi32_unsigned. vm_compute. reflexivity. Qed.

Lemma cons_um1 : bv_unsigned (mword_of_int (-1) : mword 32) = (2 ^ 32 - 1)%Z.
Proof. rewrite moi32_unsigned. vm_compute. reflexivity. Qed.

Lemma cons_sub_range (x y : mword 32) :
  (0 <= bv_unsigned (sub_vec x y) < 2 ^ 32)%Z.
Proof. exact (cons_urange (sub_vec x y)). Qed.

Lemma cons_sub_self (x : mword 32) : bv_unsigned (sub_vec x x) = 0%Z.
Proof. rewrite cons_subz Z.sub_diag. reflexivity. Qed.

(* the counters are 32 bits wide, so equal DISTANCES from a common base are
   equal words -- which is how [cons.e != cons.w] becomes [w - r < e - r] *)
Lemma cons_sub_inj (y x1 x2 : mword 32) :
  bv_unsigned (sub_vec x1 y) = bv_unsigned (sub_vec x2 y) -> x1 = x2.
Proof.
  rewrite !cons_subz. intro H.
  pose proof (cons_urange x1) as H1. pose proof (cons_urange x2) as H2.
  assert (Hlit : (2 ^ 32)%Z = 4294967296%Z) by (vm_compute; reflexivity).
  rewrite Hlit in H, H1, H2.
  assert (Hz : (((bv_unsigned x1 - bv_unsigned y)
                 - (bv_unsigned x2 - bv_unsigned y)) mod 4294967296 = 0)%Z).
  { rewrite Zminus_mod H Z.sub_diag. reflexivity. }
  replace ((bv_unsigned x1 - bv_unsigned y)
           - (bv_unsigned x2 - bv_unsigned y))%Z
     with (bv_unsigned x1 - bv_unsigned x2)%Z in Hz by lia.
  apply Z.mod_divide in Hz; [| lia]. destruct Hz as [q Hq].
  apply bv_eq. nia.
Qed.

Lemma cons_sub_eq0 (x y : mword 32) :
  bv_unsigned (sub_vec x y) = 0%Z -> x = y.
Proof.
  intro H. apply (cons_sub_inj y x y). rewrite H cons_sub_self. reflexivity.
Qed.

Lemma cons_sub_ne (x y : mword 32) :
  x <> y -> (1 <= bv_unsigned (sub_vec x y))%Z.
Proof.
  intro Hne. pose proof (cons_sub_range x y) as Hr.
  destruct (Z.eq_dec (bv_unsigned (sub_vec x y)) 0%Z) as [E | NE];
    [exfalso; exact (Hne (cons_sub_eq0 x y E)) | lia].
Qed.

(* the three one-step moves: [cons.e++], [cons.e--], [cons.r++] *)
Lemma cons_sub_inc (x y : mword 32) :
  (bv_unsigned (sub_vec x y) + 1 < 2 ^ 32)%Z ->
  bv_unsigned (sub_vec (add_vec x (mword_of_int 1 : mword 32)) y)
  = (bv_unsigned (sub_vec x y) + 1)%Z.
Proof.
  intro Hlt. rewrite cons_subz in Hlt.
  rewrite !cons_subz cons_addz cons_u1 Zminus_mod_idemp_l.
  replace (bv_unsigned x + 1 - bv_unsigned y)%Z
     with ((bv_unsigned x - bv_unsigned y) + 1)%Z by lia.
  rewrite <- Zplus_mod_idemp_l. apply Z.mod_small.
  pose proof (Z.mod_pos_bound (bv_unsigned x - bv_unsigned y) (2 ^ 32)
                ltac:(vm_compute; reflexivity)) as Hb.
  lia.
Qed.

Lemma cons_sub_dec (x y : mword 32) :
  (1 <= bv_unsigned (sub_vec x y))%Z ->
  bv_unsigned (sub_vec (add_vec x (mword_of_int (-1) : mword 32)) y)
  = (bv_unsigned (sub_vec x y) - 1)%Z.
Proof.
  intro Hge. rewrite cons_subz in Hge.
  rewrite !cons_subz cons_addz cons_um1 Zminus_mod_idemp_l.
  replace (bv_unsigned x + (2 ^ 32 - 1) - bv_unsigned y)%Z
     with ((bv_unsigned x - bv_unsigned y) - 1 + 1 * 2 ^ 32)%Z by lia.
  rewrite Z_mod_plus_full.
  rewrite <- Zminus_mod_idemp_l. apply Z.mod_small.
  pose proof (Z.mod_pos_bound (bv_unsigned x - bv_unsigned y) (2 ^ 32)
                ltac:(vm_compute; reflexivity)) as Hb.
  lia.
Qed.

Lemma cons_sub_shiftr (x y : mword 32) :
  (1 <= bv_unsigned (sub_vec x y))%Z ->
  bv_unsigned (sub_vec x (add_vec y (mword_of_int 1 : mword 32)))
  = (bv_unsigned (sub_vec x y) - 1)%Z.
Proof.
  intro Hge. rewrite cons_subz in Hge.
  rewrite !cons_subz cons_addz cons_u1 Zminus_mod_idemp_r.
  replace (bv_unsigned x - (bv_unsigned y + 1))%Z
     with ((bv_unsigned x - bv_unsigned y) - 1)%Z by lia.
  rewrite <- Zminus_mod_idemp_l. apply Z.mod_small.
  pose proof (Z.mod_pos_bound (bv_unsigned x - bv_unsigned y) (2 ^ 32)
                ltac:(vm_compute; reflexivity)) as Hb.
  lia.
Qed.

(* ---- the slot function -------------------------------------------- *)

Local Lemma cons_128_div : (128 | 2 ^ 32)%Z.
Proof. exists 33554432%Z. vm_compute. reflexivity. Qed.

Lemma cons_slot_lt (r : mword 32) (k : Z) : (cons_slot r k < INPUT_BUF_SIZE)%nat.
Proof.
  rewrite /cons_slot /INPUT_BUF_SIZE.
  change (Z.of_nat 128) with 128%Z.
  pose proof (Z.mod_pos_bound (bv_unsigned r + k) 128
                ltac:(vm_compute; reflexivity)) as Hb.
  lia.
Qed.

Lemma cons_slot_inj (r : mword 32) (k1 k2 : Z) :
  (0 <= k1 < 128)%Z -> (0 <= k2 < 128)%Z ->
  cons_slot r k1 = cons_slot r k2 -> k1 = k2.
Proof.
  intros H1 H2 He. rewrite /cons_slot /INPUT_BUF_SIZE in He.
  change (Z.of_nat 128) with 128%Z in He.
  pose proof (Z.mod_pos_bound (bv_unsigned r + k1) 128
                ltac:(vm_compute; reflexivity)) as Hb1.
  pose proof (Z.mod_pos_bound (bv_unsigned r + k2) 128
                ltac:(vm_compute; reflexivity)) as Hb2.
  apply Z2Nat.inj in He; [| lia | lia].
  assert (Hz : (((bv_unsigned r + k1) - (bv_unsigned r + k2)) mod 128 = 0)%Z).
  { rewrite Zminus_mod He Z.sub_diag. reflexivity. }
  replace ((bv_unsigned r + k1) - (bv_unsigned r + k2))%Z
     with (k1 - k2)%Z in Hz by lia.
  apply Z.mod_divide in Hz; [| lia]. destruct Hz as [q Hq]. nia.
Qed.

Lemma cons_slot_shift (r : mword 32) (k : Z) :
  cons_slot (add_vec r (mword_of_int 1 : mword 32)) k = cons_slot r (k + 1).
Proof.
  rewrite /cons_slot /INPUT_BUF_SIZE cons_addz cons_u1.
  change (Z.of_nat 128) with 128%Z.
  f_equal.
  rewrite (Zplus_mod ((bv_unsigned r + 1) mod 2 ^ 32) k).
  rewrite (Z.mod_mod_divide (bv_unsigned r + 1) (2 ^ 32) 128 cons_128_div).
  rewrite <- Zplus_mod. f_equal; lia.
Qed.

(* THE CODE'S OWN INDEX: [andi rd,rs,127] on the sign-extended counter.
   128 divides 2^32, so the wrap the sign extension exposes is invisible. *)
Lemma cons_slot_of_and (x : mword 32) :
  Z.to_nat (bv_unsigned (and_vec (sign_extend' 64 x : mword 64)
              (sign_extend' 64 (mword_of_int 127 : mword 12) : mword 64)))
  = cons_slot x 0.
Proof.
  rewrite /cons_slot /INPUT_BUF_SIZE.
  change (Z.of_nat 128) with 128%Z.
  rewrite Z.add_0_r. f_equal.
  rewrite and_vec64_unsigned.
  assert (Hm : bv_unsigned (sign_extend' 64 (mword_of_int 127 : mword 12) : mword 64)
               = Z.ones 7) by (vm_compute; reflexivity).
  rewrite Hm Z.land_ones; [| lia].
  change (2 ^ 7)%Z with 128%Z.
  assert (Hw : bv_wrap 32 (bv_unsigned (sign_extend' 64 x : mword 64))
               = bv_unsigned x).
  { rewrite <- (trunc32_unsigned (sign_extend' 64 x)). by rewrite trunc32_sext. }
  rewrite cons_bvw in Hw. rewrite <- Hw. symmetry.
  exact (Z.mod_mod_divide _ (2 ^ 32) 128 cons_128_div).
Qed.

(* ...and the same index read off the far end of the live range: the slot
   the APPEND lands in is [cons.e]'s own. *)
Lemma cons_slot_end (r e : mword 32) :
  cons_slot r (bv_unsigned (sub_vec e r)) = cons_slot e 0.
Proof.
  rewrite /cons_slot /INPUT_BUF_SIZE.
  change (Z.of_nat 128) with 128%Z.
  rewrite Z.add_0_r. f_equal. rewrite cons_subz.
  rewrite (Zplus_mod (bv_unsigned r) ((bv_unsigned e - bv_unsigned r) mod 2 ^ 32)).
  rewrite (Z.mod_mod_divide (bv_unsigned e - bv_unsigned r) (2 ^ 32) 128
             cons_128_div).
  rewrite <- Zplus_mod. f_equal; lia.
Qed.

(* ---- the four moves, at the coupling ------------------------------- *)

(* consoleintr's append, under its own [cons.e - cons.r < INPUT_BUF_SIZE] *)
Lemma cons_ok_inc_e (r w e : mword 32) :
  cons_ok r w e ->
  (bv_unsigned (sub_vec e r) < Z.of_nat INPUT_BUF_SIZE)%Z ->
  cons_ok r w (add_vec e (mword_of_int 1 : mword 32)).
Proof.
  rewrite /cons_ok cons_bufz. intros [H1 H2] Hlt.
  assert (Hbig : (2 ^ 32)%Z = 4294967296%Z) by (vm_compute; reflexivity).
  rewrite (cons_sub_inc e r ltac:(rewrite Hbig; lia)). lia.
Qed.

(* the kill loop's and the backspace arm's [cons.e--], under [cons.e != cons.w] *)
Lemma cons_ok_dec_e (r w e : mword 32) :
  cons_ok r w e -> e <> w ->
  cons_ok r w (add_vec e (mword_of_int (-1) : mword 32)).
Proof.
  rewrite /cons_ok. intros [H1 H2] Hne.
  pose proof (cons_sub_range w r) as Hrw.
  pose proof (cons_sub_range e r) as Hre.
  assert (Hlt : (bv_unsigned (sub_vec w r) < bv_unsigned (sub_vec e r))%Z).
  { destruct (Z.eq_dec (bv_unsigned (sub_vec w r))
                       (bv_unsigned (sub_vec e r))) as [E | NE]; [| lia].
    exfalso. apply Hne. symmetry. exact (cons_sub_inj r w e E). }
  rewrite (cons_sub_dec e r ltac:(lia)). lia.
Qed.

(* the wake tail's [cons.w = cons.e] *)
Lemma cons_ok_set_w (r w e : mword 32) : cons_ok r w e -> cons_ok r e e.
Proof. rewrite /cons_ok. intros [H1 H2]. lia. Qed.

(* consoleread's pop, under [cons.r != cons.w] *)
Lemma cons_ok_inc_r (r w e : mword 32) :
  cons_ok r w e -> r <> w ->
  cons_ok (add_vec r (mword_of_int 1 : mword 32)) w e.
Proof.
  rewrite /cons_ok. intros [H1 H2] Hne.
  assert (Hwr : w <> r) by (intro Hc; apply Hne; symmetry; exact Hc).
  pose proof (cons_sub_ne w r Hwr) as Hw1.
  rewrite (cons_sub_shiftr w r Hw1) (cons_sub_shiftr e r ltac:(lia)). lia.
Qed.

(* ---- the row, at the same four moves -------------------------------- *)

(* a SHORTER live range inherits the row: the two [cons.e--]s owe nothing
   for the slot they drop, and its tag simply stays in [ts]. *)
Lemma cons_row_mono (r e e' : mword 32) (bs : list (bv 8))
    (ts : list (option (list mobs))) :
  (bv_unsigned (sub_vec e' r) <= bv_unsigned (sub_vec e r))%Z ->
  cons_row r e bs ts -> cons_row r e' bs ts.
Proof. intros Hle Hrow k Hk. apply Hrow. lia. Qed.

(* the pop: the range loses its first offset and every slot shifts down *)
Lemma cons_row_shift (r e : mword 32) (bs : list (bv 8))
    (ts : list (option (list mobs))) :
  (1 <= bv_unsigned (sub_vec e r))%Z ->
  cons_row r e bs ts ->
  cons_row (add_vec r (mword_of_int 1 : mword 32)) e bs ts.
Proof.
  intros Hge Hrow k Hk.
  rewrite (cons_sub_shiftr e r Hge) in Hk.
  rewrite cons_slot_shift. apply Hrow. lia.
Qed.

(* the append: one fresh slot at the far end, and no live slot is clobbered
   because [cons_slot r] is injective below 128 *)
Lemma cons_row_push (r e : mword 32) (i : nat) (bs : list (bv 8))
    (ts : list (option (list mobs))) (h : list mobs) (b : bv 8) :
  length bs = INPUT_BUF_SIZE -> length ts = INPUT_BUF_SIZE ->
  (bv_unsigned (sub_vec e r) < Z.of_nat INPUT_BUF_SIZE)%Z ->
  (* the slot is taken as a PARAMETER with its equation, so a caller that
     got its index out of [ct_ring_idx] never has to [subst] it through an
     Iris context *)
  i = cons_slot e 0 ->
  obs_ends_in Uart0 h b ->
  cons_row r e bs ts ->
  cons_row r (add_vec e (mword_of_int 1 : mword 32))
    (<[i := cons_xlate b]> bs) (<[i := Some h]> ts).
Proof.
  intros Hlb Hlt Hde Hi Hends Hrow. subst i. revert Hrow. intros Hrow k Hk.
  assert (Hbig : (2 ^ 32)%Z = 4294967296%Z) by (vm_compute; reflexivity).
  rewrite cons_bufz in Hde.
  pose proof (cons_sub_range e r) as Hrg.
  rewrite (cons_sub_inc e r ltac:(rewrite Hbig; lia)) in Hk.
  pose proof (cons_slot_end r e) as Hend.
  destruct (Z.eq_dec k (bv_unsigned (sub_vec e r))) as [Heq | Hne].
  - subst k. exists h, b. rewrite <- Hend.
    rewrite list_lookup_insert; [| rewrite Hlt; apply cons_slot_lt].
    rewrite list_lookup_insert; [| rewrite Hlb; apply cons_slot_lt].
    split_and!; [reflexivity | exact Hends | reflexivity].
  - destruct (Hrow k ltac:(lia)) as (h0 & b0 & Ht0 & He0 & Hb0).
    assert (Hslt : cons_slot r k <> cons_slot e 0).
    { rewrite <- Hend. intro Hc. apply Hne.
      exact (cons_slot_inj r k (bv_unsigned (sub_vec e r))
               ltac:(lia) ltac:(lia) Hc). }
    exists h0, b0.
    rewrite list_lookup_insert_ne; [| congruence].
    rewrite list_lookup_insert_ne; [| congruence].
    split_and!; [exact Ht0 | exact He0 | exact Hb0].
Qed.

(* ---- THE RING'S THREE TRANSITIONS, as pure facts -------------------- *)

(* (1) THE COMMIT, [cons.w = cons.e]: the editable window becomes part of
   the committed prefix, and the window empties.  It is the ONLY transition
   that extends [stored], and the code reaches it from '\n', from C('D')
   and from the store that fills the ring (console.c's inner [if]). *)
Lemma cons_stored_commit (r w e : mword 32) (cur : nat)
    (st pd : list (list mobs * bv 8)) (bs : list (bv 8))
    (ts : list (option (list mobs))) :
  cons_ok r w e ->
  cons_stored r w cur st bs ts -> cons_pend r w e pd bs ts ->
  cons_stored r e cur (st ++ pd) bs ts.
Proof.
  intros Hok [Hlst Hst] [Hlpd Hpd].
  pose proof (cons_sub_range w r) as Hwr.
  pose proof (cons_sub_range e r) as Her.
  pose proof (cons_sub_range e w) as Hew.
  (* THE RING'S WINDOW SPLIT.  [w - r] and [e - w] add up to [e - r] at
     width 32 because [cons_ok] pins both ends inside one 128-byte span:
     [e - w] is congruent to [(e-r) - (w-r)], which is in [0,128], so the
     wrap cannot bite. *)
  assert (Hsplit : (bv_unsigned (sub_vec w r) + bv_unsigned (sub_vec e w)
                    = bv_unsigned (sub_vec e r))%Z).
  { assert (Hbig : (2 ^ 32)%Z = 4294967296%Z) by (vm_compute; reflexivity).
    pose proof (cons_urange r) as Hr0. pose proof (cons_urange w) as Hw0.
    pose proof (cons_urange e) as He0.
    pose proof (cons_sub_range e r) as Her0.
    pose proof (cons_sub_range w r) as Hwr0.
    assert (Hok2 := Hok). rewrite /cons_ok cons_bufz in Hok2.
    rewrite (cons_subz e w).
    assert (Hcong : ((bv_unsigned e - bv_unsigned w)
                     = (bv_unsigned (sub_vec e r) - bv_unsigned (sub_vec w r))
                       + ((bv_unsigned e - bv_unsigned r) / 2 ^ 32
                          - (bv_unsigned w - bv_unsigned r) / 2 ^ 32) * 2 ^ 32)%Z).
    { rewrite !cons_subz.
      pose proof (Z.div_mod (bv_unsigned e - bv_unsigned r) (2 ^ 32)
                    ltac:(lia)) as He1.
      pose proof (Z.div_mod (bv_unsigned w - bv_unsigned r) (2 ^ 32)
                    ltac:(lia)) as Hw1.
      lia. }
    rewrite Hcong Z_mod_plus_full Z.mod_small; lia. }
  split.
  { rewrite length_app Hlst Hlpd. lia. }
  intros k Hk.
  destruct (Z_lt_ge_dec k (bv_unsigned (sub_vec w r))) as [Hlt | Hge].
  - destruct (Hst k ltac:(lia)) as (h & b & Hs & Ht & He & Hb).
    exists h, b. split_and!; [| exact Ht | exact He | exact Hb].
    rewrite lookup_app_l; [exact Hs | rewrite Hlst; lia].
  - set (j := Z.to_nat (k - bv_unsigned (sub_vec w r))).
    assert (Hjlt : (j < length pd)%nat) by (rewrite Hlpd /j; lia).
    destruct (Hpd j Hjlt) as (h & b & Hs & Ht & He & Hb).
    assert (Hkj : (bv_unsigned (sub_vec w r) + Z.of_nat j = k)%Z)
      by (rewrite /j; lia).
    rewrite Hkj in Ht. rewrite Hkj in Hb.
    exists h, b. split_and!; [| exact Ht | exact He | exact Hb].
    rewrite lookup_app_r; [| rewrite Hlst; lia].
    rewrite Hlst. replace (cur + Z.to_nat k - (cur + Z.to_nat (bv_unsigned (sub_vec w r))))%nat
      with j by (rewrite /j; lia).
    exact Hs.
Qed.

Lemma cons_pend_commit (r e : mword 32) (bs : list (bv 8))
    (ts : list (option (list mobs))) :
  cons_pend r e e [] bs ts.
Proof.
  split; [| intros j Hj; cbn [length] in Hj; lia].
  cbn [length]. rewrite cons_sub_self. reflexivity.
Qed.

(* (2) THE STORE at [cons.e]: the editable window gains the byte, the
   committed prefix is untouched because the slot written is outside it. *)
Lemma cons_stored_ins (r w : mword 32) (cur : nat)
    (st : list (list mobs * bv 8)) (bs : list (bv 8))
    (ts : list (option (list mobs))) (i : nat) (h : list mobs) (b : bv 8)
    (e : mword 32) :
  cons_ok r w e ->
  (bv_unsigned (sub_vec e r) < Z.of_nat INPUT_BUF_SIZE)%Z ->
  i = cons_slot e 0 ->
  cons_stored r w cur st bs ts ->
  cons_stored r w cur st (<[i := cons_xlate b]> bs) (<[i := Some h]> ts).
Proof.
  intros Hok Hlt Hi [Hlst Hst]. subst i.
  pose proof (cons_slot_end r e) as Hend.
  pose proof (cons_sub_range w r) as Hwr0.
  pose proof (cons_sub_range e r) as Her0.
  rewrite cons_bufz in Hlt.
  destruct Hok as [Hok1 Hok2].
  split; [exact Hlst |].
  intros k Hk.
  destruct (Hst k Hk) as (g & c & Hs & Ht & He & Hb).
  assert (Hr1 : (0 <= k < 128)%Z) by lia.
  assert (Hr2 : (0 <= bv_unsigned (sub_vec e r) < 128)%Z) by lia.
  assert (Hne : cons_slot r k <> cons_slot e 0).
  { rewrite <- Hend. intro Hc.
    pose proof (cons_slot_inj r k _ Hr1 Hr2 Hc) as Hk2. lia. }
  exists g, c. split_and!; [exact Hs | | exact He |].
  - rewrite list_lookup_insert_ne; [exact Ht | congruence].
  - rewrite list_lookup_insert_ne; [exact Hb | congruence].
Qed.

Lemma cons_pend_push (r w e : mword 32) (pd : list (list mobs * bv 8))
    (bs : list (bv 8)) (ts : list (option (list mobs))) (i : nat)
    (h : list mobs) (b : bv 8) :
  length bs = INPUT_BUF_SIZE -> length ts = INPUT_BUF_SIZE ->
  cons_ok r w e ->
  (bv_unsigned (sub_vec e r) < Z.of_nat INPUT_BUF_SIZE)%Z ->
  i = cons_slot e 0 ->
  obs_ends_in Uart0 h b ->
  cons_pend r w e pd bs ts ->
  cons_pend r w (add_vec e (mword_of_int 1 : mword 32)) (pd ++ [(h, b)])
    (<[i := cons_xlate b]> bs) (<[i := Some h]> ts).
Proof.
  intros Hlb Hlt Hok Hltr Hi Hends [Hlpd Hpd]. subst i.
  assert (Hbig : (2 ^ 32)%Z = 4294967296%Z) by (vm_compute; reflexivity).
  rewrite cons_bufz in Hltr.
  pose proof (cons_sub_range e r) as Her.
  pose proof (cons_sub_range e w) as Hew.
  pose proof (cons_sub_range w r) as Hwr.
  pose proof (cons_slot_end r e) as Hend.
  (* the same window split as [cons_stored_commit]'s *)
  assert (Hsplit : (bv_unsigned (sub_vec w r) + bv_unsigned (sub_vec e w)
                    = bv_unsigned (sub_vec e r))%Z).
  { pose proof (cons_urange r) as Hr0. pose proof (cons_urange w) as Hw0.
    pose proof (cons_urange e) as He0.
    pose proof (cons_sub_range e r) as Her0.
    pose proof (cons_sub_range w r) as Hwr0.
    assert (Hok2 := Hok). rewrite /cons_ok cons_bufz in Hok2.
    rewrite (cons_subz e w).
    assert (Hcong : ((bv_unsigned e - bv_unsigned w)
                     = (bv_unsigned (sub_vec e r) - bv_unsigned (sub_vec w r))
                       + ((bv_unsigned e - bv_unsigned r) / 2 ^ 32
                          - (bv_unsigned w - bv_unsigned r) / 2 ^ 32) * 2 ^ 32)%Z).
    { rewrite !cons_subz.
      pose proof (Z.div_mod (bv_unsigned e - bv_unsigned r) (2 ^ 32)
                    ltac:(lia)) as He1.
      pose proof (Z.div_mod (bv_unsigned w - bv_unsigned r) (2 ^ 32)
                    ltac:(lia)) as Hw1.
      lia. }
    rewrite Hcong Z_mod_plus_full Z.mod_small; lia. }
  assert (Hinc : (bv_unsigned (sub_vec (add_vec e (mword_of_int 1 : mword 32)) w)
                  = bv_unsigned (sub_vec e w) + 1)%Z).
  { apply (cons_sub_inc e w). rewrite Hbig. lia. }
  split.
  { rewrite length_app Hlpd Hinc. cbn [length]. lia. }
  intros j Hj. rewrite length_app Hlpd in Hj. cbn [length] in Hj.
  destruct (decide (j < length pd)%nat) as [Hjl | Hjl].
  - destruct (Hpd j Hjl) as (g & c & Hs & Ht & He & Hb).
    assert (Hjl2 : (Z.of_nat j < bv_unsigned (sub_vec e w))%Z)
      by (rewrite Hlpd in Hjl; lia).
    assert (Hr1 : (0 <= bv_unsigned (sub_vec w r) + Z.of_nat j < 128)%Z)
      by lia.
    assert (Hr2 : (0 <= bv_unsigned (sub_vec e r) < 128)%Z) by lia.
    assert (Hne : cons_slot r (bv_unsigned (sub_vec w r) + Z.of_nat j)
                  <> cons_slot e 0).
    { rewrite <- Hend. intro Hc.
      pose proof (cons_slot_inj r _ _ Hr1 Hr2 Hc) as Hk2. lia. }
    exists g, c. split_and!; [| | exact He |].
    + rewrite lookup_app_l; [exact Hs | exact Hjl].
    + rewrite list_lookup_insert_ne; [exact Ht | congruence].
    + rewrite list_lookup_insert_ne; [exact Hb | congruence].
  - assert (Hje : j = length pd) by lia. subst j.
    assert (Hkey : (bv_unsigned (sub_vec w r) + Z.of_nat (length pd)
                    = bv_unsigned (sub_vec e r))%Z) by (rewrite Hlpd; lia).
    rewrite Hkey. rewrite <- Hend.
    exists h, b. split_and!; [| | exact Hends |].
    + rewrite lookup_app_r; [| lia]. rewrite Nat.sub_diag. reflexivity.
    + rewrite list_lookup_insert; [reflexivity | rewrite Hlt; apply cons_slot_lt].
    + rewrite list_lookup_insert; [reflexivity | rewrite Hlb; apply cons_slot_lt].
Qed.

(* (3) THE EDIT, backspace and C('U'): [cons.e] moves back one and the
   window loses its LAST entry.  The committed prefix cannot be reached --
   the code tests [cons.e != cons.w] first -- so [stored] never shrinks. *)
Lemma cons_pend_pop (r w e : mword 32) (pd : list (list mobs * bv 8))
    (x : list mobs * bv 8) (bs : list (bv 8))
    (ts : list (option (list mobs))) :
  (1 <= bv_unsigned (sub_vec e w))%Z ->
  cons_pend r w e (pd ++ [x]) bs ts ->
  cons_pend r w (add_vec e (mword_of_int (-1) : mword 32)) pd bs ts.
Proof.
  intros Hge [Hlpd Hpd].
  assert (Hbig : (2 ^ 32)%Z = 4294967296%Z) by (vm_compute; reflexivity).
  pose proof (cons_sub_range e w) as Hew.
  assert (Hdec : (bv_unsigned (sub_vec (add_vec e (mword_of_int (-1) : mword 32)) w)
                  = bv_unsigned (sub_vec e w) - 1)%Z)
    by exact (cons_sub_dec e w Hge).
  rewrite length_app in Hlpd. cbn [length] in Hlpd.
  split; [rewrite Hdec; lia |].
  intros j Hj.
  destruct (Hpd j ltac:(rewrite length_app; cbn [length]; lia))
    as (g & c & Hs & Ht & He & Hb).
  exists g, c. split_and!; [| exact Ht | exact He | exact Hb].
  rewrite lookup_app_l in Hs; [exact Hs | exact Hj].
Qed.

(* (4) THE CONSUMPTION, [cons.r++] -- CONSOLEREAD'S ONLY MOVE.  The
   committed sequence is UNTOUCHED (a byte stays in [stored] forever); what
   moves is the CURSOR, and that is the whole content of the pop: the [k]th
   unconsumed byte after it is the [(k+1)]st before it, and both name
   [st !! (S cur + k)].  This is the only transition that advances [cur],
   which is why [cur] is what a receipt's window is keyed at. *)
Lemma cons_stored_pop (r w : mword 32) (cur : nat)
    (st : list (list mobs * bv 8)) (bs : list (bv 8))
    (ts : list (option (list mobs))) :
  (1 <= bv_unsigned (sub_vec w r))%Z ->
  cons_stored r w cur st bs ts ->
  cons_stored (add_vec r (mword_of_int 1 : mword 32)) w (S cur) st bs ts.
Proof.
  intros Hge [Hlen Hst].
  pose proof (cons_sub_shiftr w r Hge) as Hdec.
  split.
  { rewrite Hlen Hdec. lia. }
  intros k Hk. rewrite Hdec in Hk.
  destruct (Hst (k + 1)%Z ltac:(lia)) as (h & b & Hs & Ht & He & Hb).
  exists h, b. rewrite cons_slot_shift.
  split_and!; [| exact Ht | exact He | exact Hb].
  replace (S cur + Z.to_nat k)%nat with (cur + Z.to_nat (k + 1))%nat by lia.
  exact Hs.
Qed.

(* ...and the editable window rides the pop unchanged: it is keyed from
   [cons.w], and the slot the [j]th pending byte lives in is the same
   address read off the new [cons.r] ([cons_slot_shift] absorbs the
   shift). *)
Lemma cons_pend_shift (r w e : mword 32) (pd : list (list mobs * bv 8))
    (bs : list (bv 8)) (ts : list (option (list mobs))) :
  (1 <= bv_unsigned (sub_vec w r))%Z ->
  cons_pend r w e pd bs ts ->
  cons_pend (add_vec r (mword_of_int 1 : mword 32)) w e pd bs ts.
Proof.
  intros Hge [Hlen Hpd]. split; [exact Hlen |].
  intros j Hj. destruct (Hpd j Hj) as (h & b & Hs & Ht & He & Hb).
  pose proof (cons_sub_shiftr w r Hge) as Hdec.
  exists h, b. rewrite cons_slot_shift Hdec.
  replace (bv_unsigned (sub_vec w r) - 1 + Z.of_nat j + 1)%Z
     with (bv_unsigned (sub_vec w r) + Z.of_nat j)%Z by lia.
  split_and!; [exact Hs | exact Ht | exact He | exact Hb].
Qed.

(* ---- WHAT A READER'S WINDOW IS BUILT OUT OF ------------------------ *)

(* a prefix of any length the sequence has *)
Lemma cons_prefix_len (st : list (list mobs * bv 8)) (k : nat) :
  (k <= length st)%nat ->
  exists l : list (list mobs * bv 8), l `prefix_of` st /\ length l = k.
Proof.
  intro Hk. exists (take k st). split.
  - exists (drop k st). symmetry. apply take_drop.
  - rewrite length_take. lia.
Qed.

(* ...and the prefix ONE LONGER, which is what a pop earns: the byte the
   read just took is the sequence's own next element, so the bound the
   window is stated at grows by exactly it. *)
Lemma cons_prefix_snoc (l st : list (list mobs * bv 8))
    (x : list mobs * bv 8) :
  l `prefix_of` st -> st !! length l = Some x ->
  (l ++ [x])%list `prefix_of` st.
Proof.
  intros [k ->] Hx.
  rewrite lookup_app_r in Hx; [| lia]. rewrite Nat.sub_diag in Hx.
  destruct k as [| y k']; [discriminate |].
  cbn in Hx. injection Hx as <-.
  exists k'. by rewrite <- app_assoc.
Qed.

(* THE WINDOW GROWS BY THE BYTE THE POP TOOK.  The run's source function is
   the old one below [d] and the popped byte at [d] -- which is exactly what
   the copy loop's glue builds -- and the tag list gains the byte's own
   history. *)
Lemma cons_window_snoc (l : list (list mobs * bv 8)) (n d : nat)
    (bs bs' : nat -> bv 8) (hs : list (list mobs))
    (h : list mobs) (b : bv 8) :
  cons_window l n d bs hs ->
  obs_ends_in Uart0 h b ->
  (forall i : nat, (i < d)%nat -> bs' i = bs i) ->
  bs' d = cons_xlate b ->
  cons_window (l ++ [(h, b)])%list n (S d) bs' (hs ++ [h])%list.
Proof.
  intros (Hl & Hhl & Hwin) Hends Hlo Hhi.
  split_and!.
  - rewrite length_app Hl. cbn [length]. lia.
  - rewrite length_app Hhl. cbn [length]. lia.
  - intros j Hj. destruct (decide (j < d)%nat) as [Hjd | Hjd].
    + destruct (Hwin j Hjd) as (g & c & Hlj & Hhj & He & Hb).
      exists g, c. split_and!.
      * rewrite lookup_app_l; [exact Hlj | rewrite Hl; lia].
      * rewrite lookup_app_l; [exact Hhj | rewrite Hhl; lia].
      * exact He.
      * rewrite (Hlo j Hjd). exact Hb.
    + assert (Hje : j = d) by lia. subst j.
      exists h, b. split_and!.
      * rewrite lookup_app_r; [| rewrite Hl; lia].
        rewrite Hl. replace (n + d - (n + d))%nat with 0%nat by lia. reflexivity.
      * rewrite lookup_app_r; [| rewrite Hhl; lia].
        rewrite Hhl Nat.sub_diag. reflexivity.
      * exact Hends.
      * exact Hhi.
Qed.

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

(* ...and the CONVERSE: a slot that holds consoleread is the console's,
   because nothing else fills the table and the symbol is not null.  It is
   a fact about the TABLE, and only a caller that knows the [devsw] column
   it read IS this table can use it -- fileread's contract does not
   (SpecSysRead.v is where [frn_rp fn = devsw_read_val] is a premise), so
   ProofFileread's console arm splits on the major instead. *)
Lemma devsw_read_val_is_console (mj : Z) :
  devsw_read_val mj = (mword_of_int KernelSyms.consoleread : mword 64) ->
  mj = CONSOLE.
Proof.
  intro H. destruct (decide (mj = CONSOLE)) as [E | NE]; [exact E | exfalso].
  rewrite (devsw_read_val_other mj NE) in H.
  apply (f_equal (@bv_unsigned 64)) in H. vm_compute in H. discriminate.
Qed.

(* THE CONSOLE'S OWN NAMESPACE, and the ONE invariant at it: the credential
   escrow [cons_cred_inv] below.  It is disjoint from [AppInv.appN] and from
   [WpLock.lockN] by construction, so the dispatcher's read arm -- which
   runs its fancy updates at [⊤] ([ProofFileread]'s [iMod (proto_read_* ⊤
   ..)]) -- may open it beside anything else the kernel holds.  The mask the
   two accessors are stated at is therefore [⊤]; they are stated at an
   arbitrary [E] with [↑consN ⊆ E] so a smaller-masked caller is not shut
   out. *)
Definition consN : namespace := nroot .@ "cons".
Definition consE : coPset := ↑consN.

Section ConsoleInv.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.
  Context `{XI : CurCtx}.

  (* the ring, byte by byte -- [PipeInvDefs.pipe_data]'s shape.  The contents
     are a list rather than a function so that a single-byte update is a
     [<[i := b]>] and the length premise stays where the accessor wants it. *)
  Definition cons_data (bs : list (bv 8)) : iProp Σ :=
    ([∗ list] j ↦ b ∈ bs, pa_add a_cons (cons_buf_off + j) ↦ₘ b)%I.

  Global Instance cons_data_timeless bs : Timeless (cons_data bs).
  Proof. apply _. Qed.

  (* THE TAG COLUMN, one slot per ring byte.  [None] is a slot no live
     offset names -- the boot ring is all [None] -- and a [Some h] is the
     application's persistent claim about the history the byte in that
     slot arrived at.  ξ-FREE, because [riscv_rx_tag] is a field of
     [riscvFixedGS] and no context indexes it; that is what keeps the
     column out of [cons_res_at]'s transport. *)
  Definition cons_tags (ts : list (option (list mobs))) : iProp Σ :=
    ([∗ list] ot ∈ ts,
       match ot with Some h => riscv_rx_tag h | None => emp end)%I.

  Global Instance cons_tags_persistent ts : Persistent (cons_tags ts).
  Proof.
    rewrite /cons_tags. apply big_sepL_persistent. intros ? [h|]; apply _.
  Qed.
  Global Instance cons_tags_timeless ts : Timeless (cons_tags ts).
  Proof.
    rewrite /cons_tags. apply big_sepL_timeless. intros ? [h|]; apply _.
  Qed.

  (* the column at the boot ring: [n] empty slots, and nothing owed *)
  Lemma cons_tags_none (n : nat) : ⊢ cons_tags (replicate n None).
  Proof.
    rewrite /cons_tags. iInduction n as [| k IH] "IH"; [done |].
    rewrite replicate_S big_sepL_cons. iSplitR; [done |]. iApply "IH".
  Qed.

  (* ...and the one write: consoleintr files a tag beside the byte it just
     stored.  The slot's old entry is DROPPED (a tag is persistent, an empty
     slot affine), so this is a wand and not an accessor. *)
  Lemma cons_tags_upd (ts : list (option (list mobs))) (i : nat)
      (h : list mobs) :
    riscv_rx_tag h -∗ cons_tags ts -∗ cons_tags (<[i := Some h]> ts).
  Proof.
    iIntros "#Ht Hts". rewrite /cons_tags.
    destruct (decide (i < length ts)%nat) as [Hlt | Hge]; last first.
    { rewrite list_insert_ge; [iExact "Hts" | lia]. }
    destruct (lookup_lt_is_Some_2 ts i Hlt) as [ot Hot].
    iDestruct (big_sepL_insert_acc
                 (fun (_ : nat) (o : option (list mobs)) =>
                    match o with Some g => riscv_rx_tag g | None => emp end)%I
                 ts i ot Hot with "Hts") as "[_ Hcl]".
    iApply ("Hcl" $! (Some h)). iExact "Ht".
  Qed.

  (* ...and the one READ: consoleread takes a copy of the tag of the byte
     it pops.  A tag is persistent, so the column is handed back whole. *)
  Lemma cons_tags_get (ts : list (option (list mobs))) (i : nat)
      (h : list mobs) :
    ts !! i = Some (Some h) -> cons_tags ts -∗ riscv_rx_tag h.
  Proof.
    intro Hi. rewrite /cons_tags. iIntros "Hts".
    iDestruct (big_sepL_lookup
                 (fun (_ : nat) (o : option (list mobs)) =>
                    match o with Some g => riscv_rx_tag g | None => emp end)%I
                 ts i (Some h) Hi with "Hts") as "H".
    iExact "H".
  Qed.

  (* ---- THE RING'S GHOSTS ---------------------------------------------

     Three names travel together, so a caller of consoleread passes ONE
     record and the ring's resource takes no gname parameters of its own.
     [cn_uart] is there because the HIGH-WATER MARK is a receive-side ghost
     ([UartNames.un_rxhi]): its other half rides in the PLIC payload beside
     the receive token, where the popper is, and that pairing is the whole
     reason the ring can order a byte it is being handed against the bytes
     it already holds. *)
  Definition cons_stored_auth (cn : cons_names)
      (st : list (list mobs * bv 8)) : iProp Σ :=
    own cn.(cn_log) (●ML (st : list (leibnizO (list mobs * bv 8)))).
  (* WHAT A RECEIPT HANDS OUT.  Persistent, and any two of them agree on
     every index both have -- which is what makes two successive reads'
     windows parts of ONE sequence. *)
  Definition cons_stored_lb (cn : cons_names)
      (st : list (list mobs * bv 8)) : iProp Σ :=
    own cn.(cn_log) (◯ML (st : list (leibnizO (list mobs * bv 8)))).
  (* THE CURSOR, in two halves.  The ring's half is inside [cons_res]; the
     other half IS THE READER TOKEN -- the exclusive right to consume the
     console's input, which is what makes "one reader" a resource instead of
     a hope about the process tree. *)
  Definition cons_cursor (cn : cons_names) (n : nat) : iProp Σ :=
    ghost_var cn.(cn_rd) (1/2) n.
  Definition cons_reader (cn : cons_names) (n : nat) : iProp Σ :=
    ghost_var cn.(cn_rd) (1/2) n.
  (* the ring's half of the high-water mark.  THE SAME PROPOSITION as
     [WpUart.uart_rx_hi (cn_uart cn) (1/2)], spelled here because this file
     sits below [WpUart] and must not depend on it; the two unfold to one
     [ghost_var] at one name. *)
  Definition cons_hi (cn : cons_names) (hh : option (list mobs)) : iProp Σ :=
    ghost_var (un_rxhi cn.(cn_uart)) (1/2) hh.

  Global Instance cons_stored_lb_persistent cn st :
    Persistent (cons_stored_lb cn st).
  Proof. rewrite /cons_stored_lb. apply _. Qed.
  Global Instance cons_stored_lb_timeless cn st :
    Timeless (cons_stored_lb cn st).
  Proof. rewrite /cons_stored_lb. apply _. Qed.
  Global Instance cons_reader_timeless cn n : Timeless (cons_reader cn n).
  Proof. rewrite /cons_reader. apply _. Qed.

  Lemma cons_cursor_agree cn n n' :
    cons_cursor cn n -∗ cons_reader cn n' -∗ ⌜n = n'⌝.
  Proof.
    iIntros "H1 H2". by iDestruct (ghost_var_agree with "H1 H2") as %->.
  Qed.
  Lemma cons_cursor_update cn n n' :
    cons_cursor cn n -∗ cons_reader cn n ==∗
      cons_cursor cn n' ∗ cons_reader cn n'.
  Proof. iIntros "H1 H2". iApply (ghost_var_update_halves with "H1 H2"). Qed.

  Lemma cons_stored_lb_get cn st :
    cons_stored_auth cn st -∗ cons_stored_auth cn st ∗ cons_stored_lb cn st.
  Proof.
    iIntros "Ha". rewrite /cons_stored_auth /cons_stored_lb.
    iEval (rewrite {1}mono_list_auth_lb_op) in "Ha".
    iDestruct "Ha" as "[Ha Hlb]".
    iFrame "Ha Hlb".
  Qed.

  Lemma cons_stored_lb_prefix cn st l :
    cons_stored_auth cn st -∗ cons_stored_lb cn l -∗ ⌜l `prefix_of` st⌝.
  Proof.
    iIntros "Ha Hl". rewrite /cons_stored_auth /cons_stored_lb.
    by iDestruct (own_valid_2 with "Ha Hl") as %?%mono_list_both_valid_L.
  Qed.

  (* TWO WINDOWS OF ONE SEQUENCE.  A reader that holds the bound from an
     earlier read and the bound from a later one can line them up: the two
     are comparable, so the shorter is a prefix of the longer and every
     index they share carries the same byte. *)
  Lemma cons_stored_lb_agree cn l1 l2 :
    cons_stored_lb cn l1 -∗ cons_stored_lb cn l2 -∗
      ⌜l1 `prefix_of` l2 \/ l2 `prefix_of` l1⌝.
  Proof.
    iIntros "H1 H2". rewrite /cons_stored_lb.
    by iDestruct (own_valid_2 with "H1 H2")
      as %?%mono_list_lb_op_valid_L.
  Qed.

  (* a bound SHORTENS to any prefix of itself, which is how a window whose
     run is still growing is kept exactly as long as the run *)
  Lemma cons_stored_lb_weaken cn l l' :
    l' `prefix_of` l -> cons_stored_lb cn l -∗ cons_stored_lb cn l'.
  Proof.
    intro Hp. rewrite /cons_stored_lb. iIntros "H".
    iApply (own_mono with "H"). by apply mono_list_lb_mono.
  Qed.

  (* =====================================================================
     THE BYTE A READ POPPED AND DID NOT DELIVER  (app-echo.md, "SH-LINE
     PHASE 2 -- THE SWALLOWED BYTE"; lane CONS-SWALLOW, W2)

     consoleread's cursor moves by [d] or by [d + 1]: two of its exits pop a
     byte and break without copying it (the [C('D')] arm with nothing
     delivered yet, and the [either_copyout] failure past [cons.r++]).  A
     reader that is told only "[d <= dc <= d + 1]" cannot tell the two apart,
     and a program reading one byte at a time then cannot tell a delivered
     line from a line with a hole in it.  So the [d + 1] case NAMES the byte
     it swallowed: its history sits in the stored sequence immediately after
     the window ([sl ++ [(h, b)]] is a bound on the ring's committed prefix,
     so the byte really is the next one), it carries the input tag every
     stored byte carries, and the reason is one of exactly the two the code
     has -- the byte was [C('D')] and nothing had been delivered, or the
     copy-out of it faulted, which is [fault] (the caller's own
     [SpecCopyout.copyout_wrote] clause at its destination).

     [fault] IS A PARAMETER because this file names no page table; the
     kernel contract instantiates it ([SpecConsoleread]) and a program
     refutes it from what it owns of its own address space. *)
  Definition cons_swallow (cn : cons_names) (fault : Prop)
      (sl : list (list mobs * bv 8)) (d dc : nat) : iProp Σ :=
    (⌜dc = d⌝
     ∨ ⌜dc = (d + 1)%nat⌝ ∗
       ∃ (h : list mobs) (b : bv 8),
         ⌜obs_ends_in Uart0 h b⌝ ∗
         cons_stored_lb cn (sl ++ [(h, b)])%list ∗
         ⌜cons_chain (sl ++ [(h, b)])%list⌝ ∗
         riscv_rx_tag h ∗
         (⌜d = 0%nat /\ bv_unsigned (cons_xlate b) = 4⌝ ∨ ⌜fault⌝))%I.

  Global Instance cons_swallow_persistent cn fault sl d dc :
    Persistent (cons_swallow cn fault sl d dc).
  Proof. rewrite /cons_swallow. apply _. Qed.

  (* THE REASON WEAKENS.  [fault] is a statement about the reader's own
     address space, and the table it is read at only GROWS while the call
     runs ([UserPtTree.uva_wmapped_mono]), so a receipt earned at the grown
     table is handed on at the entry one -- which is where the contract
     states it. *)
  Lemma cons_swallow_mono (cn : cons_names) (f1 f2 : Prop)
      (sl : list (list mobs * bv 8)) (d dc : nat) :
    (f1 -> f2) ->
    cons_swallow cn f1 sl d dc -∗ cons_swallow cn f2 sl d dc.
  Proof.
    intros Himp. rewrite /cons_swallow.
    iIntros "[%He | [%He H]]"; [iLeft; by iPureIntro |].
    iRight. iSplitR; [by iPureIntro |].
    iDestruct "H" as (h b) "(%Hen & #Hlb & %Hch & #Htg & Hwhy)".
    iExists h, b. iFrame "Hlb Htg".
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iDestruct "Hwhy" as "[%Hd | %Hf]";
      [iLeft; by iPureIntro | iRight; iPureIntro; exact (Himp Hf)].
  Qed.

  (* the arm every OTHER exit takes: the cursor moved by exactly the run *)
  Lemma cons_swallow_eq (cn : cons_names) (fault : Prop)
      (sl : list (list mobs * bv 8)) (d : nat) :
    ⊢ cons_swallow cn fault sl d d.
  Proof. rewrite /cons_swallow. iLeft. by iPureIntro. Qed.

  (* ...and the bound it carries: [d] or one more, which is what the landed
     callers read off it *)
  Lemma cons_swallow_range (cn : cons_names) (fault : Prop)
      (sl : list (list mobs * bv 8)) (d dc : nat) :
    cons_swallow cn fault sl d dc -∗ ⌜(d <= dc <= d + 1)%nat⌝.
  Proof.
    rewrite /cons_swallow. iIntros "[%He | [%He _]]"; iPureIntro; lia.
  Qed.

  Lemma cons_stored_append cn st st' :
    cons_stored_auth cn st ==∗ cons_stored_auth cn (st ++ st').
  Proof.
    rewrite /cons_stored_auth. iIntros "Ha".
    iMod (own_update _ _
            (●ML ((st ++ st') : list (leibnizO (list mobs * bv 8))))
            with "Ha") as "$"; [| done].
    apply mono_list_update. by exists st'.
  Qed.

  (* ---- A CONSOLE READ WITHOUT THE READER TOKEN IS LEGAL, AND PRICED ----

     The kernel CANNOT make console reading exclusive.  A generic process --
     one this application says nothing about -- may call read(0, ..), and
     the generic slot's supply law ([UexecExecInst.xv6_sbundle_of_supply_ne],
     a FIELD of [UexecSG]'s class) has to answer for it at every syscall
     number OUT OF A PERSISTENT SUPPLY ([□ ssupply] in both laws).  A
     deposit that demanded an exclusive token is therefore not merely
     unprovable: taken as a premise under a [□] it is INCONSISTENT (open it
     three times and hold [ghost_var γ (1/2) _] thrice), so the arm has to
     be payable from something persistent.  What the kernel does instead is
     RECORD that such a read happened, at the price of the credential the
     generic slot already holds, and let the token holder learn it.

     So the ring carries TWO cursors.  [cur] is the ACTUAL consumed count --
     pure, the ring's own, moved by EVERY consoleread -- and it is what
     [cons_stored] keys the committed sequence at.  [nrd] is the READER'S
     position, the ghost half whose partner is [cons_reader], and only a
     token-holding read moves it (it needs both halves).  Between them sits
     the one clause that makes the whole thing honest:

         ⌜cur = nrd⌝ ∨ cons_dirty_lb cn

     -- either nobody has read behind the token holder's back, or somebody
     did.

     THE MARKER RIDES IN THE RING, THE CREDENTIAL DOES NOT, and the split is
     forced by TIMELESSNESS: [cons_res] is a LOCK PAYLOAD, which acquire
     strips a [▷] off, and the credential [Wd] is an arbitrary application
     [iProp] ([AppInv.app_sup] over an abstract [app_pred]) that is not
     timeless.  So the ring holds only [cons_dirty_lb] -- a [mono_nat] lower
     bound at 1, persistent AND timeless -- and the credential sits in the
     ESCROW INVARIANT [cons_cred_inv] carried beside the lock handle in
     [is_conslock].  The payer deposits [□ Wd] there while setting the
     marker; the token holder reads it back out of the marker.  Both opens
     are atomic; nothing is held open across a step. *)

  (* WHAT THE TOKENLESS CALLER PAYS.  Boxed, so the token holder's receipt
     can carry a copy away.  [Wd] is an opaque parameter here rather than
     [AppInv.app_sup] itself because this file sits far below the
     application's invariant; [SpecFileread]'s console arm is where it is
     named ([app_sup]), and [SpecConsoleread] relays it. *)
  Definition cons_dirty_cred (Wd : iProp Σ) : iProp Σ := (□ Wd)%I.

  Global Instance cons_dirty_cred_persistent Wd :
    Persistent (cons_dirty_cred Wd).
  Proof. rewrite /cons_dirty_cred. apply _. Qed.

  (* THE RING'S MARKER and the CLEAN TOKEN it is made from.  One [mono_nat]
     at [cn_dirty]: the authority at 0 is the exclusive clean token, minted
     in the boot fupd beside the ring; the lower bound at 1 is the marker.
     The two are incompatible ([mono_nat_lb_own_valid] gives [1 <= 0]),
     which is what lets a holder of the marker rule out the escrow's clean
     arm.  Both are timeless. *)
  Definition cons_clean_tok (cn : cons_names) : iProp Σ :=
    mono_nat_auth_own cn.(cn_dirty) 1 0%nat.
  Definition cons_dirty_lb (cn : cons_names) : iProp Σ :=
    mono_nat_lb_own cn.(cn_dirty) 1%nat.

  Global Instance cons_dirty_lb_persistent cn : Persistent (cons_dirty_lb cn).
  Proof. rewrite /cons_dirty_lb. apply _. Qed.
  Global Instance cons_dirty_lb_timeless cn : Timeless (cons_dirty_lb cn).
  Proof. rewrite /cons_dirty_lb. apply _. Qed.
  Global Instance cons_clean_tok_timeless cn : Timeless (cons_clean_tok cn).
  Proof. rewrite /cons_clean_tok. apply _. Qed.

  Lemma cons_dirty_lb_clean cn :
    cons_clean_tok cn -∗ cons_dirty_lb cn -∗ False.
  Proof.
    rewrite /cons_clean_tok /cons_dirty_lb. iIntros "Ha Hlb".
    iDestruct (mono_nat_lb_own_valid with "Ha Hlb") as %[_ Hle]. lia.
  Qed.

  (* THE ESCROW.  Its body is the one place [□ Wd] lives, and it is a
     disjunction the marker decides: clean (nobody has paid) or dirty (the
     marker is out and the credential is here).  Persistent by [inv], so it
     rides in [is_conslock] and costs a caller nothing.  Spelled at the
     [mono_nat] forms rather than at the three names above so that the two
     accessors can strip the invariant's later off the timeless half
     without unfolding anything. *)
  Definition cons_cred_body (cn : cons_names) (Wd : iProp Σ) : iProp Σ :=
    (mono_nat_auth_own cn.(cn_dirty) 1 0%nat
     ∨ (mono_nat_lb_own cn.(cn_dirty) 1%nat ∗ □ Wd))%I.

  Definition cons_cred_inv (cn : cons_names) (Wd : iProp Σ) : iProp Σ :=
    inv consN (cons_cred_body cn Wd).

  Global Instance cons_cred_inv_persistent cn Wd :
    Persistent (cons_cred_inv cn Wd).
  Proof. apply _. Qed.

  (* the boot allocation: the clean token buys the escrow *)
  Lemma cons_cred_inv_alloc (cn : cons_names) (Wd : iProp Σ) (E : coPset) :
    cons_clean_tok cn ={E}=∗ cons_cred_inv cn Wd.
  Proof.
    iIntros "Hcl". rewrite /cons_cred_inv.
    iApply (inv_alloc consN E (cons_cred_body cn Wd)).
    iNext. rewrite /cons_cred_body. iLeft. iExact "Hcl".
  Qed.

  (* THE PAYER, at a mask that admits [consN].  It hands the credential in
     and gets the marker out; a second payer finds the dirty arm and simply
     takes a copy of the marker.  ATOMIC: the invariant is closed again
     before anything else happens, so nothing is held open across a step --
     which is the whole reason the credential is here and not in the
     caller's hands across the sleeping call. *)
  Lemma cons_cred_pay (cn : cons_names) (Wd : iProp Σ) (E : coPset) :
    ↑consN ⊆ E ->
    cons_cred_inv cn Wd -∗ cons_dirty_cred Wd ={E}=∗ cons_dirty_lb cn.
  Proof.
    intro HE. rewrite /cons_dirty_cred /cons_dirty_lb /cons_cred_inv.
    iIntros "#Hinv #Hcred".
    iInv "Hinv" as "Hbody" "Hclose".
    iEval (rewrite /cons_cred_body) in "Hbody".
    iDestruct "Hbody" as "[>Htok | [>#Hlb _]]".
    - iMod (mono_nat_own_update 1%nat with "Htok") as "[_ #Hlb]"; [ lia | ].
      iMod ("Hclose" with "[]") as "_".
      { iNext. rewrite /cons_cred_body. iRight.
        iSplitR; [ iExact "Hlb" | iExact "Hcred" ]. }
      iModIntro. iExact "Hlb".
    - iMod ("Hclose" with "[]") as "_".
      { iNext. rewrite /cons_cred_body. iRight.
        iSplitR; [ iExact "Hlb" | iExact "Hcred" ]. }
      iModIntro. iExact "Hlb".
  Qed.

  (* THE READER.  The marker rules out the clean arm, so the credential is
     there; it is PERSISTENT, so a copy comes out and the invariant closes
     unchanged.  The [▷] is the invariant's own -- [Wd] is an arbitrary
     application [iProp] and nothing strips a later off one -- and the site
     that uses this ([ProofConsoleread]'s tokenless read, and the token
     holder's receipt) takes the open around a machine step, where the step
     strips it. *)
  Lemma cons_cred_read (cn : cons_names) (Wd : iProp Σ) (E : coPset) :
    ↑consN ⊆ E ->
    cons_cred_inv cn Wd -∗ cons_dirty_lb cn ={E}=∗ ▷ cons_dirty_cred Wd.
  Proof.
    intro HE. rewrite /cons_dirty_cred /cons_dirty_lb /cons_cred_inv.
    iIntros "#Hinv #Hlb".
    iInv "Hinv" as "Hbody" "Hclose".
    iEval (rewrite /cons_cred_body) in "Hbody".
    iDestruct "Hbody" as "[>Htok | [_ #Hcred]]".
    - iDestruct (mono_nat_lb_own_valid with "Htok Hlb") as %[_ Hle]. lia.
    - iMod ("Hclose" with "[]") as "_".
      { iNext. rewrite /cons_cred_body. iRight.
        iSplitR; [ iExact "Hlb" | iExact "Hcred" ]. }
      iModIntro. iExact "Hcred".
  Qed.

  Definition cons_res (cn : cons_names) : iProp Σ :=
    (∃ (r w e : mword 32) (bs : list (bv 8)) (ts : list (option (list mobs)))
       (cur nrd : nat) (st pd : list (list mobs * bv 8))
       (hh : option (list mobs)),
       a_cons_r ↦₄ r ∗
       a_cons_w ↦₄ w ∗
       a_cons_e ↦₄ e ∗
       ⌜length bs = INPUT_BUF_SIZE⌝ ∗
       ⌜length ts = INPUT_BUF_SIZE⌝ ∗
       ⌜cons_ok r w e⌝ ∗
       ⌜cons_row r e bs ts⌝ ∗
       ⌜cons_stored r w cur st bs ts⌝ ∗
       ⌜cons_pend r w e pd bs ts⌝ ∗
       ⌜cons_chain (st ++ pd)⌝ ∗
       ⌜cons_below (st ++ pd) hh⌝ ∗
       cons_data bs ∗ cons_tags ts ∗
       cons_stored_auth cn st ∗ cons_cursor cn nrd ∗ cons_hi cn hh ∗
       (⌜cur = nrd⌝ ∨ cons_dirty_lb cn))%I.

  (* WHAT A CONSOLE READ COSTS ITS CALLER, AND WHAT IT HANDS BACK.  One
     [option] and two arms -- BELOW the fileread tier only: consoleread's
     own contract keeps the two arms because the two callers reach it with
     different resources, and [cons_acc] below is where the one arm the
     SYSCALL's deposit relays is assembled out of them.  [Some nrd] is a
     caller holding the reader token at its own position; [None] is a caller
     that holds none and pays the credential instead. *)
  Definition cons_pay (cn : cons_names) (Wd : iProp Σ)
      (ord : option nat) : iProp Σ :=
    match ord with
    | Some nrd => cons_reader cn nrd
    | None => cons_dirty_cred Wd
    end%I.

  (* [cur] is where the ring's committed sequence actually stood when the
     call read it, and [dc] how far the cursor moved.  A token holder gets
     its half back at [cur + dc] together with the one fact it cares about:
     either the window it was just handed begins at ITS OWN position, or
     somebody read behind its back -- and then the CREDENTIAL, read out of
     the escrow against the ring's marker, which is what sends the holder's
     continuation generic. *)
  Definition cons_out (cn : cons_names) (Wd : iProp Σ) (ord : option nat)
      (cur dc : nat) : iProp Σ :=
    match ord with
    | Some nrd =>
        cons_reader cn (cur + dc)%nat ∗ (⌜cur = nrd⌝ ∨ cons_dirty_cred Wd)
    | None => emp
    end%I.

  (* ---- THE ONE ARM THE SYSCALL'S DEPOSIT RELAYS -----------------------

     [cons_acc cn Wd Rd] is what a caller of read(0, ..) supplies, and [Rd
     cur dc] is what that caller chooses to get back -- at the position
     [cur] the ring's committed sequence stood at and the advance [dc] the
     cursor made.  ONE ARM, TWO DISJUNCTS, and the caller picks:

       a LEASE HOLDER hands in the reader token at its own [n] and a wand
       that turns consoleread's [cons_out] into whatever it wants to know
       (for sh: that the window began at ITS position, and its token back);

       a TAINTED OR GENERIC caller hands in the credential it already holds
       -- the application's claim of every view, which for a constraining
       application is exactly what the taint provides -- and owes [Rd] at
       every position, which for a caller that tracks nothing is [True].

     THIS IS WHY THERE IS NO [option] ABOVE THE FILEREAD TIER: the two
     callers differ in WHICH DISJUNCT they supply, not in the shape of the
     deposit, so one leaf and one post serve both.  The holder's half goes
     INERT under the taint -- nothing reclaims it, and its continuation
     reads the console on the credential like anyone else. *)
  (* THE INNER WAND IS A BASIC UPDATE (app-echo.md, "SH-LINE RULING", R2).
     What a lease holder wants back is not only its token but its own
     PROGRAM-SIDE POSITION moved to the new cursor, and a position it holds
     as one half of a ghost pair moves by [ghost_var_update_halves] -- a
     basic update.  So the caller's wand concludes under [|==>] on both
     disjuncts, and the kernel, which is under a WP when it applies it,
     absorbs the update with an [iMod] for free.  A bupd suffices: nothing
     the caller does here opens an invariant. *)
  Definition cons_acc (cn : cons_names) (Wd : iProp Σ)
      (Rd : nat -> nat -> iProp Σ) : iProp Σ :=
    ((∃ n : nat, cons_reader cn n ∗
        (∀ cur dc : nat, cons_out cn Wd (Some n) cur dc ==∗ Rd cur dc))
     ∨ (cons_dirty_cred Wd ∗ ∀ cur dc : nat, |==> Rd cur dc))%I.

  (* the tainted/generic caller's constructor, which is the whole of
     [FsAbsInvFire.fsabs_fileread_in]'s console case *)
  Lemma cons_acc_cred (cn : cons_names) (Wd : iProp Σ)
      (Rd : nat -> nat -> iProp Σ) :
    cons_dirty_cred Wd -∗ (∀ cur dc : nat, |==> Rd cur dc) -∗ cons_acc cn Wd Rd.
  Proof. iIntros "#Hc HR". rewrite /cons_acc. iRight. by iFrame "Hc HR". Qed.

  (* ...and the lease holder's *)
  Lemma cons_acc_reader (cn : cons_names) (Wd : iProp Σ) (n : nat)
      (Rd : nat -> nat -> iProp Σ) :
    cons_reader cn n -∗
    (∀ cur dc : nat, cons_out cn Wd (Some n) cur dc ==∗ Rd cur dc) -∗
    cons_acc cn Wd Rd.
  Proof.
    iIntros "Hrd Hw". rewrite /cons_acc. iLeft. iExists n. iFrame "Hrd Hw".
  Qed.

  (* ...AND THE ONE OPENING, which is what makes the fileread tier's console
     call UNIFORM.  Both disjuncts hand the kernel a PAYMENT
     ([cons_pay] at [Some n] or at [None]) and a wand that turns
     consoleread's [cons_out] back into what the caller asked for, so the
     proof below the accessor never case-splits: it opens once, calls
     consoleread at the [ord] it got, and closes.  The [option] therefore
     lives entirely between here and [SpecConsoleread]. *)
  Lemma cons_acc_open (cn : cons_names) (Wd : iProp Σ)
      (Rd : nat -> nat -> iProp Σ) :
    cons_acc cn Wd Rd -∗
    ∃ ord : option nat,
      cons_pay cn Wd ord ∗
      (∀ cur dc : nat, cons_out cn Wd ord cur dc ==∗ Rd cur dc).
  Proof.
    rewrite /cons_acc. iIntros "[Hl | [#Hc Hr]]".
    - iDestruct "Hl" as (n) "[Hrd Hw]".
      iExists (Some n). rewrite /cons_pay. iFrame "Hrd Hw".
    - iExists None. rewrite /cons_pay. iFrame "Hc".
      iIntros (cur dc) "_". iApply "Hr".
  Qed.

  (* THE ARM THAT DELIVERED NOTHING.  Every -1 exit of the device arm -- a
     null [devsw] slot, a major out of range, the [n < 0] sign guard, and
     consoleread's own killed return -- has to hand the caller back what it
     asked for without having read the ring at all.  It can: a lease holder
     gets its own token back at its own position and zero advance, and a
     tainted caller owes nothing to begin with. *)
  Lemma cons_acc_ret (cn : cons_names) (Wd : iProp Σ)
      (Rd : nat -> nat -> iProp Σ) :
    cons_acc cn Wd Rd ==∗ ∃ cur dc : nat, Rd cur dc.
  Proof.
    rewrite /cons_acc. iIntros "[Hl | [_ Hr]]".
    - iDestruct "Hl" as (n) "[Hrd Hw]".
      iMod ("Hw" $! n 0%nat with "[Hrd]") as "Hrd".
      { rewrite /cons_out Nat.add_0_r. iFrame "Hrd". iLeft. by iPureIntro. }
      iModIntro. iExists n, 0%nat. iExact "Hrd".
    - iMod ("Hr" $! 0%nat 0%nat) as "Hr". iModIntro.
      iExists 0%nat, 0%nat. iExact "Hr".
  Qed.

  Global Instance cons_res_timeless cn : Timeless (cons_res cn).
  Proof.
    rewrite /cons_res /cons_stored_auth /cons_cursor /cons_hi /cons_dirty_lb.
    apply _.
  Qed.

  (* ---- THE RING'S GHOSTS AT BOOT --------------------------------------

     Everything the ring's resource and its two boot-time tokens are made
     of, in one bundle, so that the .bss carve takes ONE premise: the
     committed sequence's authority at the empty list, the ring's half of
     the cursor at 0, the ring's half of the HIGH-WATER MARK at [None], the
     READER TOKEN at 0 (the cursor's other half, which travels up the boot
     chain) and the CLEAN TOKEN (the dirty marker's authority at 0, which
     main spends on [cons_cred_inv_alloc]).

     [cn_uart] is NOT allocated here.  Its [un_rxhi] pair is minted with the
     UART's ghosts ([WpUart.uart_ghosts_alloc Uart0]), one half for the PLIC
     payload beside the receive token and one for the ring, and this
     allocation takes the ring's half as its input -- which is exactly why
     the ring's names record carries the uart's rather than a copy. *)
  Definition cons_ghosts_boot (cn : cons_names) : iProp Σ :=
    (cons_stored_auth cn [] ∗ cons_cursor cn 0%nat ∗ cons_hi cn None ∗
     cons_reader cn 0%nat ∗ cons_clean_tok cn)%I.

  (* The [un_rxhi] half is spelled as its [ghost_var] rather than as
     [WpUart.uart_rx_hi], because this file sits below [WpUart]; the two
     are one proposition ([cons_hi]'s note). *)
  Lemma cons_ghosts_alloc (γu : uart_names) :
    ghost_var (un_rxhi γu) (1/2) (None : option (list mobs)) ==∗
      ∃ cn : cons_names, ⌜cn_uart cn = γu⌝ ∗ cons_ghosts_boot cn.
  Proof.
    iIntros "Hhi".
    iMod (own_alloc (●ML ([] : list (leibnizO (list mobs * bv 8)))))
      as (γl) "Hl"; [apply mono_list_auth_valid |].
    iMod (ghost_var_alloc 0%nat) as (γr) "Hr".
    iEval (rewrite -Qp.half_half) in "Hr".
    iDestruct (ghost_var_split with "Hr") as "[Hr1 Hr2]".
    iMod (mono_nat_own_alloc 0%nat) as (γk) "[Hk _]".
    iModIntro. iExists (ConsNames γu γl γr γk).
    iSplitR; [by iPureIntro |].
    rewrite /cons_ghosts_boot /cons_stored_auth /cons_cursor /cons_reader
            /cons_hi /cons_clean_tok /=.
    iFrame "Hl Hr1 Hhi Hr2 Hk".
  Qed.

End ConsoleInv.

(* THE PAYLOAD'S CtxMorph INSTANCES (tso-port M3, §4 step 1) and the
   lock handle over the CONVERTED payload.  Outside the section above
   because each quantifies over the context that section fixes -- the
   [KallocInv.v:388] template, line for line.  [cons_res] is ▷-free,
   [inv]-free and WP-free: its three index words are [↦₄] (stage 2,
   still unflipped, hence ξ-constant) and its ring is a [↦ₘ] big-op.
   Consequence: [is_conslock] is a CLOSED term -- no [CurCtx] in its
   type -- which is what §4's ordering needs of the console. *)
Section ConsoleCtx.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.
  Context `{XI : CurCtx}.

  (* >>> A6.121 (the M3 λ-conversion): the payload over an EXPLICIT context.
     [cons_res_at ξ] is the same body with the context spelled out -- it is
     [cons_res] at [cur_ctx] by [reflexivity] -- and it is what the lock
     surface takes as its [CtxId → iProp], so the invariant's free arm holds
     the console cells at the PARKED record's context and acquire's absorb
     re-indexes them by a REAL transport ([CtxMorph], the structural
     instances) instead of the constant embedding [<{ }>].  Every consumer
     keeps reading and writing [cons_res]. <<< *)
  Definition cons_data_at (ξ : CtxId) (bs : list (bv 8)) : iProp Σ :=
    ([∗ list] j ↦ b ∈ bs,
       ctx_pointsto ξ (pa_add a_cons (cons_buf_off + j)) (DfracOwn 1) b)%I.
  Definition cons_res_at (cn : cons_names)
      (ξ : CtxId) : iProp Σ :=
    (∃ (r w e : mword 32) (bs : list (bv 8)) (ts : list (option (list mobs)))
       (cur nrd : nat) (st pd : list (list mobs * bv 8))
       (hh : option (list mobs)),
       ctx_word4_pointsto ξ a_cons_r (DfracOwn 1) r ∗
       ctx_word4_pointsto ξ a_cons_w (DfracOwn 1) w ∗
       ctx_word4_pointsto ξ a_cons_e (DfracOwn 1) e ∗
       ⌜length bs = INPUT_BUF_SIZE⌝ ∗
       ⌜length ts = INPUT_BUF_SIZE⌝ ∗
       ⌜cons_ok r w e⌝ ∗
       ⌜cons_row r e bs ts⌝ ∗
       ⌜cons_stored r w cur st bs ts⌝ ∗
       ⌜cons_pend r w e pd bs ts⌝ ∗
       ⌜cons_chain (st ++ pd)⌝ ∗
       ⌜cons_below (st ++ pd) hh⌝ ∗
       cons_data_at ξ bs ∗ cons_tags ts ∗
       cons_stored_auth cn st ∗ cons_cursor cn nrd ∗ cons_hi cn hh ∗
       (⌜cur = nrd⌝ ∨ cons_dirty_lb cn))%I.
  Lemma cons_res_at_cur (cn : cons_names) :
    cons_res_at cn cur_ctx = cons_res cn.
  Proof. reflexivity. Qed.
  Global Instance cons_res_at_morph (cn : cons_names) :
    CtxMorph (cons_res_at cn).
  Proof.
    rewrite /cons_res_at /cons_data_at /cons_dirty_lb. ctx_morph_solve.
  Qed.

  (* THE WHOLE CREDENTIAL.  Persistent, singleton, and taken by value: a
     caller of consoleread passes this and nothing else about the console.
     The payload is spelled as a λ that NAMES its context (recipe rule 1):
     the ring re-indexes to whichever context holds the lock. *)
  (* ...AND THE ESCROW RIDES WITH IT (the timelessness split above).  The
     lock's payload is the ring alone -- timeless, as acquire needs -- and
     the credential [Wd] the ring's marker stands for is reached through the
     persistent [cons_cred_inv] conjoined here, so every caller that already
     takes [is_conslock] (consoleread, consoleintr, fileread) reaches it
     without a new premise.  Both conjuncts are persistent and neither
     mentions [XI], so [is_conslock] is still a CLOSED term. *)
  Definition is_conslock (cn : cons_names) (Wd : iProp Σ)
      (γ : gname) : iProp Σ :=
    (is_lock γ a_cons "cons"%string (cons_res_at cn) ∗ cons_cred_inv cn Wd)%I.

  Lemma is_conslock_lock (cn : cons_names) (Wd : iProp Σ) (γ : gname) :
    is_conslock cn Wd γ -∗ is_lock γ a_cons "cons"%string (cons_res_at cn).
  Proof. rewrite /is_conslock. by iIntros "[$ _]". Qed.

  Lemma is_conslock_cred (cn : cons_names) (Wd : iProp Σ) (γ : gname) :
    is_conslock cn Wd γ -∗ cons_cred_inv cn Wd.
  Proof. rewrite /is_conslock. by iIntros "[_ $]". Qed.

  Lemma is_conslock_intro (cn : cons_names) (Wd : iProp Σ) (γ : gname) :
    is_lock γ a_cons "cons"%string (cons_res_at cn) -∗
    cons_cred_inv cn Wd -∗ is_conslock cn Wd γ.
  Proof. rewrite /is_conslock. iIntros "#H1 #H2". by iFrame "H1 H2". Qed.

  Global Instance is_conslock_persistent cn Wd γ :
    Persistent (is_conslock cn Wd γ).
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

  Definition console_inv (cn : cons_names) (Wd : iProp Σ)
      (γ : gname) : iProp Σ :=
    (is_conslock cn Wd γ ∗ devsw_table)%I.

  Global Instance console_inv_persistent cn Wd γ :
    Persistent (console_inv cn Wd γ).
  Proof. apply _. Qed.

  (* THE GNAME-FREE FORM IS GONE (app-echo.md, lane CONS-CURSOR, C3).  It
     hid the ring's NAMES and the credential as well as the lock's gname,
     and a read cannot use that: the window a read hands back is stated at
     the ambient [FsCfg.fsc_cons] and the tokenless arm's price is the
     application's own [AppInv.app_sup], so the form every carrier of the
     console now takes is [SpecFileread.console_ready_app] -- this bundle
     with ONLY the gname left existential.  Nothing in the tree wanted the
     anonymous one: the park, the trap-loop environment, userinit and the
     syscall environment all reach the read arm. *)
  Lemma console_inv_conslock (cn : cons_names) (Wd : iProp Σ) (γ : gname) :
    console_inv cn Wd γ -∗ is_conslock cn Wd γ.
  Proof. by iIntros "[$ _]". Qed.

  Lemma console_inv_devsw (cn : cons_names) (Wd : iProp Σ) (γ : gname) :
    console_inv cn Wd γ -∗ devsw_table.
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
    iMod (ctx_word_pointsto_persist with "Hr") as "#Hr".
    iMod (ctx_word_pointsto_persist with "Hw") as "#Hw".
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
      iMod (ctx_word_pointsto_persist with "Hzr") as "$".
      iMod (ctx_word_pointsto_persist with "Hzw") as "$".
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
    iMod (ctx_word_pointsto_persist with "Hr") as "$".
    iMod (ctx_word_pointsto_persist with "Hw") as "$".
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

End ConsoleCtx.

(* ==================================================================
   THE CONSOLE BUNDLE'S TRANSPORT (tso-port.md §0.16′)

   [devsw_table] and [console_inv] are ξ-INDEXED -- the
   devsw table is [NDEV_max + 1] pairs of [↦₈□] cells -- and the park has
   to hand them to a freshly minted child context, so each needs a
   [CtxMorph].  They are NOT convertible across two contexts (the cells are
   discarded at WP time, t > 0: §0.4 item 6), and they do not have to be:
   what a deposit wants is TRANSPORTABILITY (§0.15′'s rule).

   Below the section that binds the ambient, for the usual reason (a
   section variable cannot be instantiated inside the section that binds
   it), and the structural instances go in AS TERMS -- instance search does
   not do the higher-order big-op or ∃ unification (MEASURED: with
   [ctx_morph_big_sepL]/[ctx_morph_exist] reachable by a [Hint Extern] that
   [eapply]s them, [devsw_table] still does not resolve). *)
Section ConsoleMorph.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.

  Global Instance devsw_table_morph :
    CtxMorph (λ ξ0 : CtxId, devsw_table (XI := ξ0)).
  Proof.
    iIntros (ξ ξ') "Hd H". rewrite /devsw_table.
    iMod (ctx_morph_big_sepL (seq 0 (Z.to_nat NDEV_max + 1))
                 (λ (_ : nat) (i : nat) (ξ0 : CtxId),
                    (ctx_word_pointsto ξ0 (a_devsw_read (Z.of_nat i))
                       DfracDiscarded (devsw_read_val (Z.of_nat i)) ∗
                     ctx_word_pointsto ξ0 (a_devsw_write (Z.of_nat i))
                       DfracDiscarded (devsw_write_val (Z.of_nat i)))%I)
                 (λ i x, ctx_morph_sep _ _
                           (ctx_morph_word _ _ _ _) (ctx_morph_word _ _ _ _))
                 ξ ξ' with "Hd H") as "[Hd H]".
    iModIntro. iFrame.
  Qed.

  (* the lock handle's transport: flip proves this once in SchedCtx (build
     order puts it after the lock kit); the console sits earlier, so the
     instance is restated locally -- the body is ξ-free post-M4, only the
     floor moves ([WpLock.lk_floor_morph]). *)
  Local Instance is_lock_morph_local (γ : gname) (lk : mword 64) (s : string)
      (R : TsoCtx.CtxId → iProp Σ) :
    CtxMorph (λ ξ0 : TsoCtx.CtxId, is_lock (XI := ξ0) γ lk s R).
  Proof. rewrite /is_lock. ctx_morph_solve. Qed.

  (* [console_inv] at another context (tso-port M2: a forkret park carries
     [SpecFileread.console_ready_app] in [UsertrapRes.park_globals], whose
     own morph is this one under an ∃).  The cons lock's payload is the
     closed [cons_res_at], so the handle moves by [WpLock.is_lock_morph]
     alone (its floor's transport). *)
  Global Instance console_inv_morph (cn : cons_names) (Wd : iProp Σ)
      (γ : gname) :
    CtxMorph (λ ξ0 : CtxId, console_inv (XI := ξ0) cn Wd γ).
  Proof.
    iIntros (ξ ξ') "Hd H". rewrite /console_inv /is_conslock.
    iDestruct "H" as "[[#Hlk #Hcr] Ht]".
    iMod (devsw_table_morph ξ ξ' with "Hd Ht") as "[Hd Ht]".
    iMod (is_lock_morph_local γ a_cons "cons"%string (cons_res_at cn) ξ ξ'
            with "Hd Hlk") as "[Hd #Hlk']".
    iModIntro. iFrame "Hd Ht Hlk' Hcr".
  Qed.


End ConsoleMorph.

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
