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
     there, [h] ends in an [ObsUartIn b], and [bs] has [cons_xlate b].
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
Require Import RiscvLang ObsTrace.   (* [mobs], [obs_ends_in]: the tag column's vocabulary *)
Require Import VcGen W32Arith.   (* [trunc32_unsigned]/[trunc32_sext]: the ring index's wrap *)
Require Import WpLock.
Require Import TsoCtx CtxMorphTac.   (* the lock payload's context axis; [<{ }>] *)
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
      /\ obs_ends_in h b
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
         hs !! j = Some h /\ obs_ends_in h b /\ bs j = cons_xlate b.

Lemma cons_tagged_0 (bs : nat -> bv 8) : cons_tagged bs [] 0.
Proof. split; [reflexivity | intros j Hj; exfalso; lia]. Qed.

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
  obs_ends_in h b ->
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

  Definition cons_res : iProp Σ :=
    (∃ (r w e : mword 32) (bs : list (bv 8)) (ts : list (option (list mobs))),
       a_cons_r ↦₄ r ∗
       a_cons_w ↦₄ w ∗
       a_cons_e ↦₄ e ∗
       ⌜length bs = INPUT_BUF_SIZE⌝ ∗
       ⌜length ts = INPUT_BUF_SIZE⌝ ∗
       ⌜cons_ok r w e⌝ ∗
       ⌜cons_row r e bs ts⌝ ∗
       cons_data bs ∗ cons_tags ts)%I.

  Global Instance cons_res_timeless : Timeless cons_res.
  Proof. apply _. Qed.

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
  Definition cons_res_at (ξ : CtxId) : iProp Σ :=
    (∃ (r w e : mword 32) (bs : list (bv 8)) (ts : list (option (list mobs))),
       ctx_word4_pointsto ξ a_cons_r (DfracOwn 1) r ∗
       ctx_word4_pointsto ξ a_cons_w (DfracOwn 1) w ∗
       ctx_word4_pointsto ξ a_cons_e (DfracOwn 1) e ∗
       ⌜length bs = INPUT_BUF_SIZE⌝ ∗
       ⌜length ts = INPUT_BUF_SIZE⌝ ∗
       ⌜cons_ok r w e⌝ ∗
       ⌜cons_row r e bs ts⌝ ∗
       cons_data_at ξ bs ∗ cons_tags ts)%I.
  Lemma cons_res_at_cur : cons_res_at cur_ctx = cons_res.
  Proof. reflexivity. Qed.
  Global Instance cons_res_at_morph : CtxMorph cons_res_at.
  Proof. rewrite /cons_res_at /cons_data_at. ctx_morph_solve. Qed.

  (* THE WHOLE CREDENTIAL.  Persistent, singleton, and taken by value: a
     caller of consoleread passes this and nothing else about the console.
     The payload is spelled as a λ that NAMES its context (recipe rule 1):
     the ring re-indexes to whichever context holds the lock. *)
  Definition is_conslock (γ : gname) : iProp Σ :=
    is_lock γ a_cons "cons"%string cons_res_at.

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

   [devsw_table] / [console_inv] / [console_ready] are ξ-INDEXED -- the
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

  (* [console_inv] / [console_ready] at another context (tso-port M2: a
     forkret park carries [console_ready] in [UsertrapRes.park_globals]).
     The cons lock's payload is the closed [cons_res_at], so the handle
     moves by [WpLock.is_lock_morph] alone (its floor's transport). *)
  Global Instance console_inv_morph (γ : gname) :
    CtxMorph (λ ξ0 : CtxId, console_inv (XI := ξ0) γ).
  Proof.
    iIntros (ξ ξ') "Hd H". rewrite /console_inv /is_conslock.
    iDestruct "H" as "[#Hlk Ht]".
    iMod (devsw_table_morph ξ ξ' with "Hd Ht") as "[Hd Ht]".
    iMod (is_lock_morph_local γ a_cons "cons"%string cons_res_at ξ ξ' with "Hd Hlk")
      as "[Hd #Hlk']".
    iModIntro. iFrame "Hd Ht Hlk'".
  Qed.

  Global Instance console_ready_morph :
    CtxMorph (λ ξ0 : CtxId, console_ready (XI := ξ0)).
  Proof.
    iIntros (ξ ξ') "Hd H". rewrite /console_ready.
    iDestruct "H" as (γ) "H".
    iMod (console_inv_morph γ ξ ξ' with "Hd H") as "[Hd H]".
    iModIntro. iFrame "Hd". iExists γ. iExact "H".
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
