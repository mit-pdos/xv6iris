(* ProofIalloc.v -- ialloc over the SIE-agnostic sconf world.

     struct inode* ialloc(uint dev, short type) {
       int inum;  struct buf *bp;  struct dinode *dip;
       for(inum = 1; inum < sb.ninodes; inum++){
         bp = bread(dev, IBLOCK(inum, sb));
         dip = (struct dinode * )bp->data + inum % IPB;
         if(dip->type == 0){
           memset(dip, 0, 64);   dip->type = type;
           log_write(bp);        brelse(bp);
           return iget(dev, inum);
         }
         brelse(bp);
       }
       printf("ialloc: no inodes\n");
       return 0;
     }

   *** STATUS: PROVEN AND LINKED (fs-namei N5c2).  No [Admitted], no
   [Axiom], no [cheat_]; [LinkIalloc.v] instantiates the functor and
   [Print Assumptions Ialloc.wp_ialloc_sconf] is the five platform axioms
   plus [functional_extensionality_dep] -- modulo the THREADED printk
   obligation the contract carries as a pure hypothesis (LinkIalloc.v's
   header).  ***

   THE SHAPE OF THE PROOF.  Four block lemmas entered strictly right to
   left, plus one induction, exactly ProofBalloc's layout:

     [ia_epilogue]  +0x80 .. +0x86   pop ra/s0, pop the frame, ret, and
                                     discharge the contract.  BOTH arms land
                                     here, each carrying its half of
                                     [ia_arms] as one resource, and a0 is
                                     ALREADY set by the arm (the dry arm's
                                     [c.li a0,0] is at +0x7e, the claim's a0
                                     is iget's return value).
     [ia_out]       +0x66 .. +0x7e   pop s1..s6, printk("ialloc: no
                                     inodes"), [c.li a0,0], fall into
                                     +0x80.
     [ia_claim]     +0x88 .. +0xba   memset(dip,0,64), [sh s6,0(s3)],
                                     log_write (THE CLAIM), brelse, iget,
                                     pop s1..s6, [c.j +0x80].
     [ia_scan]      +0x30 .. +0x64   THE ONLY LOOP, by induction on the fuel
                                     [Z.to_nat (ninodes - inum)]: bread, the
                                     slot arithmetic, [lh a5,0(s3)], and the
                                     two-way branch at +0x52.
     [wp_ialloc_sconf] +0x00 .. +0x2e

   THE +0x12 ARM IS DEAD, and the contract's [1 < ninodes] is what kills it
   -- balloc's [0 < size] at the very same offset, killing the very same
   shape of arm: [bgeu a5,a4] with a5 = 1 would jump to the printk WITHOUT
   having pushed s1..s6, i.e. into a SECOND epilogue shape rather than a
   second behaviour.

   THE CLAIM IS ONE ATOMIC UPDATE AND NO RESOURCE (fs-icache.md §16.5).
   [InodeRegion.ireg_claim_au] IS [SpecLogWrite.wp_log_write_au_body]'s fupd
   premise at [Efs := ⊤ ∖ ↑iregN] and [Φfsb := True]; it takes no [dinode_at]
   from anybody, because a free inum's fragment lives in the region and the
   BUFFER is the serialiser.  So the claim block plugs it in at +0x9a the
   way [ProofIupdate] plugs in [ireg_write_au], and pays nothing out.

   THE BYTES.  The scan's per-block decode is
   [InodeRegion.ireg_read_blk] (fragment-free, mask-preserving) against the
   machinery half [ProofIupdate.iu_held_L] extracts from the handle; the
   record the claim installs is [SpecIalloc.ialloc_fresh ty] and the three
   bridges between "memset wrote 64 zero bytes" and
   "[diblk_bytes (<[islot inum := ialloc_fresh ty]> ds)]" are
   [ia_dzero_bytes], [ia_fresh_of_zero] and [ia_win_acc] below.        *)
From Stdlib Require Import Eqdep_dec ZArith Bool Lia List String Ascii.
From stdpp Require Import gmap list list_numbers functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers dfrac.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvModelBytes.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText KernelDataInv.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import VcGen.
Require Import IntrDefs WpSmodeIntr.
Require Import WpSmodeHalf.
Require Import CpuOwn.
Require Import DiskPtsto DiskInv.
Require Import BufOwn.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import ByteBuf.
Require Import PrintintArith.
Require Import PrintkFmt.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import WpUart.
Require Import BufOwn BcacheInv BioInv.
Require Import FsBlocks LogInv.
Require Import DinodeEnc.
Require Import DinodeSlot.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IgetLic.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import CodeIalloc.
Require Import SpecPrintk.
Require Import SpecPanic.
Require Import SpecBread SpecBrelse SpecLogWrite SpecMemset SpecIget.
Require Import SpecIalloc.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Local Open Scope Z_scope.

(* a whole-function WP goal is enormous; keep a failing tactic's error
   printable (claude-notes/durable-notes.md) *)
Set Printing Depth 40.

(* ===================================================================== *)
(*  The no-inodes format string, in .rodata just above etext.             *)
(*  [auipc a0,0x4 / addi a0,a0,850] at +0x72 resolves to 0x80007438.      *)
(*  Hoisted as NAMED pure lemmas -- never an inline [ltac:] argument to    *)
(*  [kernel_data_string] (claude-notes/optimization.md).                   *)
(* ===================================================================== *)
Definition ia_msg : string :=
  ("ialloc: no inodes" ++ String (Ascii.ascii_of_nat 10) EmptyString)%string.
Definition ia_msg_addr : Z := 0x80007450.

Lemma ia_msg_bytes : forall j b, cstring_bytes ia_msg !! j = Some b ->
  KernelData.kernel_data !! (ia_msg_addr + Z.of_nat j)%Z = Some b.
Proof.
  intros j b Hj.
  do 19 (destruct j as [|j];
         [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
  vm_compute in Hj; discriminate.
Qed.

Lemma ia_msg_fmt : pk_kinds ia_msg = [] /\ nonul ia_msg = true /\
                   (Z.of_nat (String.length ia_msg) < 2147483645)%Z.
Proof.
  split_and!; [vm_compute; reflexivity | vm_compute; reflexivity
              | vm_compute; reflexivity].
Qed.

(* ===================================================================== *)
(*  THE ZERO RECORD, AND THE THREE BRIDGES THE CLAIM NEEDS.               *)
(*                                                                        *)
(*  [memset(dip, 0, 64)] leaves 64 zero BYTES; [sh s6,0(s3)] then writes  *)
(*  the type halfword.  What [ireg_claim_au] wants is the block's bytes   *)
(*  at [diblk_bytes (<[islot inum := ialloc_fresh ty]> ds)].  The route   *)
(*  is: zero bytes  =  [dinode_bytes ia_dzero]  (ia_dzero_bytes), then    *)
(*  [DinodeSlot.dislot_acc_gen] turns the window into the six typed cells *)
(*  the [sh] writes one of, and [ia_win_acc] puts the slot back into the  *)
(*  block at the new record.                                             *)
(* ===================================================================== *)
Definition ia_dzero : dinode :=
  MkDinode (bv_0 16) (bv_0 16) (bv_0 16) (bv_0 16) (bv_0 32)
           (replicate 13 (bv_0 32)).

Lemma ia_dzero_wf : dinode_wf ia_dzero.
Proof. rewrite /dinode_wf /ia_dzero /=. reflexivity. Qed.

(* the 64 bytes of the all-zero record ARE 64 zero bytes *)
Lemma ia_dzero_bytes (j : nat) :
  (j < 64)%nat -> dinode_bytes ia_dzero !!! j = bv_0 8.
Proof.
  intros Hj.
  (* [vm_compute; reflexivity] does NOT close these: the two [bv 8]s differ
     in their (proof-irrelevant) well-formedness component, and the error
     reads "Unable to unify 0%bv with 0%bv".  Go through [bv_eq] -- the
     [pcw] idiom used all over this tree. *)
  do 64 (destruct j as [|j]; [apply bv_eq; vm_compute; reflexivity |]).
  exfalso; lia.
Qed.

(* the byte the [memset(dip,0,64)] at +0x90 writes: [SpecMemset]'s [cbyte]
   at [cval = 0], spelled exactly as the spec body's [let] does so that the
   post's big-op folds onto it. *)
Definition ia_cbyte : bv 8 :=
  nth_byte (autocast (T := mword)
    (subrange_vec_dec (mword_of_int 0 : mword 64) (Z.sub (Z.mul 1 8) 1) 0)
    : mword 8) 0.

Lemma ia_cbyte_zero : ia_cbyte = bv_0 8.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  THE SCAN'S ARITHMETIC.  Everything the loop body needs that           *)
(*  [DinodeSlot.v] does not already have.                                 *)
(* ===================================================================== *)

(* [srli a1,s2,4] -- ialloc divides the SIGN-EXTENDED 64-bit inum, where
   iupdate's [srliw] divides the 32-bit one, so [iu_srliw4] does not apply.
   The premise is the contract's [ninodes < 2^31] through [inum < ninodes]. *)
Lemma ia_sext_small (w : mword 32) :
  bv_unsigned w < 2147483648 -> (sign_extend' 64 w : mword 64)
                                = mword_of_int (bv_unsigned w).
Proof.
  intro Hw. pose proof (bv_unsigned_in_range _ w) as [Hw0 _].
  rewrite -(sext32_64_small (bv_unsigned w)
              ltac:(change (2^31)%Z with 2147483648%Z; lia)).
  f_equal. apply bv_eq. rewrite moi32_unsigned. symmetry.
  apply bvw32_small. change (2^32)%Z with 4294967296%Z. lia.
Qed.

Lemma ia_srli4 (w : mword 32) :
  bv_unsigned w < 2147483648 ->
  shift_bits_right (sign_extend' 64 w : mword 64)
    (subrange_vec_dec (mword_of_int 4 : mword 6) (Z.sub log2_xlen 1) 0)
  = (mword_of_int (bv_unsigned w / 16) : mword 64).
Proof.
  intros Hw.
  pose proof (bv_unsigned_in_range _ w) as [Hw0 _].
  rewrite (ia_sext_small w Hw).
  assert (Hs : shift_bits_right (mword_of_int (bv_unsigned w) : mword 64)
                 (subrange_vec_dec (mword_of_int 4 : mword 6) (Z.sub log2_xlen 1) 0)
               = shiftr (mword_of_int (bv_unsigned w) : mword 64) 4).
  { unfold shift_bits_right. f_equal; vm_compute; reflexivity. }
  rewrite Hs. apply bv_eq.
  unfold shiftr, SailStdpp.Values.with_word, get_word,
    MachineWord.MachineWord.logical_shift_right.
  rewrite bv_shiftr_unsigned.
  assert (Hm64 : bv_modulus (MachineWord.MachineWord.Z_idx 64)
                 = 18446744073709551616) by (vm_compute; reflexivity).
  assert (H4 : bv_unsigned (MachineWord.MachineWord.N_to_word
                 (MachineWord.MachineWord.Z_idx 64)
                 (MachineWord.MachineWord.Z_idx 4)) = 4).
  { unfold MachineWord.MachineWord.N_to_word, MachineWord.MachineWord.Z_idx.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite Hm64. lia. }
  rewrite H4 !moi64_unsigned.
  rewrite (bvw64_small (bv_unsigned w)
             ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
  rewrite Z.shiftr_div_pow2; [| lia]. change (2 ^ 4)%Z with 16%Z.
  symmetry. apply bvw64_small.
  assert (Hd0 : 0 <= bv_unsigned w / 16) by (apply Z.div_pos; lia).
  assert (Hd1 : bv_unsigned w / 16 <= bv_unsigned w)
    by (apply Z.div_le_upper_bound; lia).
  change (2^64)%Z with 18446744073709551616%Z. lia.
Qed.

Lemma ia_add_vec32_comm (x y : mword 32) : add_vec x y = add_vec y x.
Proof. apply bv_eq. rewrite !bv_add_unsigned. f_equal. lia. Qed.

(* [andi a5,s2,15] -- the BASE-encoding twin of [iu_andi15]'s [c.andi] *)
Lemma ia_andi15 (x : mword 64) :
  and_vec x (sign_extend' 64 (mword_of_int 15 : mword 12) : mword 64)
  = (mword_of_int (bv_unsigned x `mod` 16) : mword 64).
Proof.
  assert (Hc : (sign_extend' 64 (mword_of_int 15 : mword 12) : mword 64)
               = sign_extend' 64 (sign_extend' 12 (mword_of_int 15 : mword 6)))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hc. apply iu_andi15.
Qed.

(* the [lh]'s zero test, both ways -- ProofIlock's [il_type_zero] pair,
   inlined because a Proof file must not require another Proof file *)
Lemma ia_sext64_16_inj (a c : mword 16) :
  (sign_extend' 64 a : mword 64) = sign_extend' 64 c -> a = c.
Proof.
  intro H. rewrite -(trunc16_sext64 a) -(trunc16_sext64 c) H. reflexivity.
Qed.

Lemma ia_type_zero (w : mword 16) :
  bv_unsigned w = 0 ->
  eq_vec (sign_extend' 64 w : mword 64) (zero_reg : mword 64) = true.
Proof.
  intro Hw.
  assert (Hz : w = (mword_of_int 0 : mword 16))
    by (apply bv_eq; rewrite Hw; vm_compute; reflexivity).
  rewrite Hz. vm_compute. reflexivity.
Qed.

Lemma ia_type_nonzero (w : mword 16) :
  bv_unsigned w <> 0 ->
  eq_vec (sign_extend' 64 w : mword 64) (zero_reg : mword 64) = false.
Proof.
  intro Hw. apply eq_vec_false_iff. intro Hq. apply Hw.
  assert (Hz : (zero_reg : mword 64) = sign_extend' 64 (mword_of_int 0 : mword 16))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hz in Hq. apply ia_sext64_16_inj in Hq. rewrite Hq.
  vm_compute. reflexivity.
Qed.

(* the [bltu] at +0x62, at the two words the code compares *)
Lemma ia_uint64_moi (z : Z) : 0 <= z < 18446744073709551616 ->
  uint (mword_of_int z : mword 64) = z.
Proof. intro Hz. rewrite uint_unsigned. apply moi64_small. exact Hz. Qed.

Lemma ia_bgeu_moi (x y : Z) :
  0 <= x < 18446744073709551616 -> 0 <= y < 18446744073709551616 ->
  zopz0zKzJ_u (mword_of_int x : mword 64) (mword_of_int y : mword 64) = Z.geb x y.
Proof.
  intros Hx Hy. unfold zopz0zKzJ_u.
  rewrite (ia_uint64_moi x Hx) (ia_uint64_moi y Hy). reflexivity.
Qed.

Lemma ia_bltu_moi (x y : Z) :
  0 <= x < 18446744073709551616 -> 0 <= y < 18446744073709551616 ->
  zopz0zI_u (mword_of_int x : mword 64) (mword_of_int y : mword 64) = Z.ltb x y.
Proof.
  intros Hx Hy. unfold zopz0zI_u.
  rewrite (ia_uint64_moi x Hx) (ia_uint64_moi y Hy). reflexivity.
Qed.

(* [ialloc_fresh ty] IS [ia_dzero] with the type halfword replaced -- which
   is exactly what the [sh] does to [dislot]'s first cell. *)
Lemma ia_fresh_of_zero (ty : mword 16) :
  ialloc_fresh ty
  = MkDinode ty (di_major ia_dzero) (di_minor ia_dzero) (di_nlink ia_dzero)
             (di_size ia_dzero) (di_addrs ia_dzero).
Proof. reflexivity. Qed.

Section IallocBytes.
  Context `{!riscvGS Σ, !lockG Σ, !diskGhostG Σ, !fsLogG Σ, !bioG Σ}.

  (* THE RAW 64-BYTE WINDOW of slot [k], borrowed out of the block's byte
     image and given back AT A NEW RECORD.  [DinodeSlot.diblk_slot_acc] is
     this composed with [dislot_acc_gen]; ialloc needs the RAW form too,
     because [SpecMemset] takes and returns a byte window and not the six
     typed cells. *)
  Lemma ia_win_acc (a : mword 64) (ds : list dinode) (k : nat) :
    diblk_wf ds -> (k < 16)%nat ->
    bb_bytes a 1024 (fun j => diblk_bytes ds !!! j) -∗
      ([∗ list] j ∈ seq 0 64,
         pa_add (pa_add a (64 * k)%nat) j ↦ₘ (dinode_bytes (ds !!! k) !!! j)) ∗
      (∀ d : dinode, ⌜dinode_wf d⌝ -∗
         ([∗ list] j ∈ seq 0 64,
            pa_add (pa_add a (64 * k)%nat) j ↦ₘ (dinode_bytes d !!! j)) -∗
         bb_bytes a 1024 (fun j => diblk_bytes (<[k := d]> ds) !!! j)).
  Proof.
    intros [Hlen Hall] Hk.
    assert (Hklen : (k < length ds)%nat) by (rewrite Hlen; exact Hk).
    iIntros "H". rewrite /bb_bytes.
    rewrite (bb_split3 a (64 * k)%nat 64 (1024 - (64 * k + 64))%nat 1024
               (fun j => diblk_bytes ds !!! j) ltac:(lia)).
    iDestruct "H" as "(Hpre & Hmid & Hsuf)".
    iSplitL "Hmid".
    { iApply (big_sepL_mono with "Hmid"). intros i jj Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
      rewrite (diblk_bytes_lookup_t ds k i Hall Hklen ltac:(lia)).
      reflexivity. }
    iIntros (d) "%Hd Hmid".
    rewrite (bb_split3 a (64 * k)%nat 64 (1024 - (64 * k + 64))%nat 1024
               (fun j => diblk_bytes (<[k := d]> ds) !!! j) ltac:(lia)).
    iSplitL "Hpre".
    { iApply (big_sepL_mono with "Hpre"). intros i jj Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
      rewrite (diblk_bytes_insert_other_t ds k d i Hall Hd Hklen
                 ltac:(left; lia)).
      reflexivity. }
    iSplitL "Hmid".
    { iApply (big_sepL_mono with "Hmid"). intros i jj Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
      rewrite (diblk_bytes_insert_same_t ds k d i Hall Hd Hklen ltac:(lia)).
      reflexivity. }
    iApply (big_sepL_mono with "Hsuf"). intros i jj Hj.
    apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
    rewrite (diblk_bytes_insert_other_t ds k d (64 * k + (64 + i))%nat
               Hall Hd Hklen ltac:(right; lia)).
    reflexivity.
  Qed.

  (* THE MACHINERY HALF, out of the handle and back.  [ireg_read_blk] needs
     the block's OTHER [fs_L] half to pin the region's parked bytes to the
     ones bread returned, and the handle's payload carries exactly that -- on
     BOTH polarities.  [ProofIupdate.iu_held_L] verbatim; a Proof file may
     not require another Proof file, so it is restated here. *)
  Lemma ia_held_L (bn : bio_names) (γfs : fs_names) (γd : disk_names)
      (dev : mword 32) (cov : gset Z) (k : nat) (pidv dv bno : mword 32)
      (bs bsl bsd : list (bv 8)) (d : bool) :
    bio_held bn (fs_view γfs γd dev cov) k pidv dv bno bs bsl bsd d -∗
      (uint bno ↪[fs_L γfs]{#(1/2)} bsl) ∗
      ((uint bno ↪[fs_L γfs]{#(1/2)} bsl) -∗
       bio_held bn (fs_view γfs γd dev cov) k pidv dv bno bs bsl bsd d).
  Proof.
    rewrite /bio_held /bio_pay /fs_view /=.
    iIntros "(%A & %B & %C & H1 & H2 & H3 & H4 & H5 & H6 & Hpay)".
    destruct d.
    - rewrite /fs_mdirty. iDestruct "Hpay" as "[[HL HD] Hq]".
      iFrame "HL". iIntros "HL".
      iSplitR; [done |]. iSplitR; [done |]. iSplitR; [done |].
      iFrame "H1 H2 H3 H4 H5 H6". iFrame "HL HD Hq".
    - rewrite /fs_mclean. iDestruct "Hpay" as "[[HL HD] %He]".
      iFrame "HL". iIntros "HL".
      iSplitR; [done |]. iSplitR; [done |]. iSplitR; [done |].
      iFrame "H1 H2 H3 H4 H5 H6". iFrame "HL HD". done.
  Qed.

End IallocBytes.

Module IallocProof (BR : BREAD) (LW : LOG_WRITE) (BL : BRELSE)
                   (MS : MEMSET) (IG : IGET) : IALLOC.

Notation Rra := (mword_of_int 1 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Rs1 := (mword_of_int 9 : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Rs3 := (mword_of_int 19 : mword 5).
Notation Rs4 := (mword_of_int 20 : mword 5).
Notation Rs5 := (mword_of_int 21 : mword 5).
Notation Rs6 := (mword_of_int 22 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Ra2 := (mword_of_int 12 : mword 5).
Notation Ra4 := (mword_of_int 14 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).

Local Ltac regne := reg_ne_side.

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.
Local Ltac iaidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

(* ===================================================================== *)
(*  Vocabulary: the frame, the threading invariants, the two arms, the    *)
(*  continuation.                                                         *)
(* ===================================================================== *)
Section IallocDefs.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.

  (* ialloc's 64-byte frame: ra@56 s0@48 s1@40 s2@32 s3@24 s4@16 s5@8 s6@0.
     [pa_stk sp j] counts DOWN from the entry sp, so slot j holds the
     register saved at (newsp + 64 - 8j). *)
  Definition ia_frame (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1 ↦₈[KT1] (m !!! Regidx Rra : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 2 ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 3 ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 4 ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 5 ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 6 ↦₈[KT1] (m !!! Regidx Rs4 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 7 ↦₈[KT1] (m !!! Regidx Rs5 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 8 ↦₈[KT1] (m !!! Regidx Rs6 : mword 64))%I.

  (* THE TWO ARMS, as ONE resource: what each of ialloc's two exits carries
     into the shared epilogue at +0x80.  [av] is the value in a0 there --
     which each arm has ALREADY set (the dry arm at +0x7e, the claim arm as
     iget's return value at +0xaa).

     Note what is NOT here: no region resource of any kind.  The claimed
     fragment stayed inside [InodeRegion.ireg_inv] at its [fresh_shape] arm
     (fs-icache.md §16.5) and nothing crosses back to the caller. *)
  Definition ia_arms (γ : log_names) (dev : mword 32)
      (inodestart ninodes : Z) (nib : nat) (u : nat) (Sb : gset Z)
      (av : mword 64) : iProp Σ :=
    ((* NO INODES: a0 = 0, the iget ledger unit unspent, the reservation
        untouched *)
     (⌜av = (mword_of_int 0 : mword 64)⌝ ∗ iref_slot ∗ log_opS γ (S u) Sb)
     ∨
     (* THE CLAIM: iget's postcondition verbatim, and one unit gone *)
     (∃ (kslot : nat) (q : Qp) (inum : mword 32),
        ⌜av = ientry kslot
         /\ (kslot < NINODE)%nat
         /\ 0 < bv_unsigned inum < ninodes
         /\ bv_unsigned inum < 16 * Z.of_nat nib⌝ ∗
        inode_ref kslot q dev inum ∗
        log_opS γ u (Sb ∪ {[IBLOCK inum inodestart]})))%I.

  (* THE CONTINUATION, named so it is not re-traversed by every proofmode
     split (claude-notes/optimization.md). *)
  Definition ia_cont `{GEN : GenId} `{CID0 : CpuId}
      (γ : log_names) (bn : bio_names)
      (inodestart ninodes : Z) (nib : nat) (dev : mword 32) (ty : mword 16)
      (u : nat) (Sb : gset Z) (pidv : mword 32) (dq dqs dqn : dfrac) (j : nat)
      (m : regfile) (K : nat) (b : bool) (lks : gset string) : iProp Σ :=
    wp_next true (proc_addr j) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (alloc : bool) (kslot : nat) (q : Qp) (inum : mword 32)
        (dn' : dinode),
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr j) -∗
        cpu_own 0 true (proc_addr j) b lks -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        p_pid (proc_addr j) ↦₄{dq} pidv -∗
        bslots bn 2 -∗
        (if alloc
         then ⌜mf !!! Regidx Ra0 = ientry kslot
               /\ (kslot < NINODE)%nat
               /\ 0 < bv_unsigned inum < ninodes
               /\ bv_unsigned inum < 16 * Z.of_nat nib
               /\ dn' = ialloc_fresh ty
               /\ di_type dn' = ty
               /\ fresh_shape dn'⌝ ∗
              inode_ref kslot q dev inum ∗
              log_opS γ u (Sb ∪ {[IBLOCK inum inodestart]})
         else ⌜mf !!! Regidx Ra0 = (mword_of_int 0 : mword 64)⌝ ∗
              iref_slot ∗
              log_opS γ (S u) Sb) -∗
        WP (Loop : expr riscv_lang))%I.

End IallocDefs.

(* the two register-threading invariants.  [ia_thr2] excludes only the two
   registers still un-restored at the epilogue; [ia_thr8] also excludes
   s1..s6, which are live across the whole body. *)
Definition ia_thr2 (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Definition ia_thr8 (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
    c <> Rs4 -> c <> Rs5 -> c <> Rs6 ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Definition ia_sp (m M : regfile) : Prop :=
  M !!! Regidx csp_rs1
  = add_vec (m !!! Regidx csp_rs1 : mword 64)
      (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))).

(* ===================================================================== *)
(*  +0x80 .. +0x86 : THE JOIN.  restore ra/s0, pop the frame, return.     *)
(*  a0 already carries the arm's return value.                            *)
(* ===================================================================== *)
Section IallocEpilogue.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.

  Local Lemma ia_epilogue `{GEN : GenId} `{CID0 : CpuId}
      (j : nat) (bn : bio_names) (γ : log_names)
      (inodestart ninodes : Z) (nib : nat) (dev : mword 32) (ty : mword 16)
      (u : nat) (Sb : gset Z)
      (pidv : mword 32) (dq dqs dqn : dfrac)
      (m M : regfile) (K : nat) (b : bool) (lks : gset string) :
    (K_ialloc <= K)%nat ->
    (* NOT in the parked statement: the claim arm has to hand [ia_cont] the
       [fresh_shape dn'] conjunct, and [ialloc_fresh_shape] is exactly
       [bv_unsigned ty <> 0 -> fresh_shape (ialloc_fresh ty)].  The contract
       has the premise, so threading it down costs nothing.  (N5c2 finding 1) *)
    bv_unsigned ty <> 0 ->
    ia_sp m M ->
    ia_thr2 m M ->
    sie_cap_gpr KT1 M (K - 8)%nat b (proc_addr j) -∗
    cpu_own 0 true (proc_addr j) b lks -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.ialloc + 0x80) : mword 64) -∗
    ia_frame m -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bslots bn 2 -∗
    ia_arms γ dev inodestart ninodes nib u Sb (M !!! Regidx Ra0 : mword 64) -∗
    ia_cont (CID0 := CID0) γ bn inodestart ninodes nib dev ty u Sb
            pidv dq dqs dqn j m K b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hty Hsp Hthr.
    pose proof HK as HK'. 
    iIntros "Hcg Hcnt #Htext Hpc Hframe Hppid Hsbn Hsbi Hsl Harms Hcont".
    iPoseProof (iali_80 with "Htext") as "Hi80".
    iPoseProof (iali_82 with "Htext") as "Hi82".
    iPoseProof (iali_84 with "Htext") as "Hi84".
    iPoseProof (iali_86 with "Htext") as "Hi86".
    rewrite /ia_frame.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8)".
    assert (Hc1 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc2 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    (* ===== +0x80 c.ldsp ra,56(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ialloc + 0x80))
              (mword_of_int 7 : mword 6) Rra
              M (K - 8)%nat (m !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi80 [Hf1]").
    { iEval (rewrite Hc1). iExact "Hf1". }
    iIntros (CID1 Hq1) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> M).
    assert (HP1a0 : P1 !!! Regidx Ra0 = (M !!! Regidx Ra0 : mword 64))
      by (rewrite /P1 upd_ne; [reflexivity | nz]).
    assert (HP1sp : ia_sp m P1)
      by (rewrite /ia_sp /P1 upd_ne; [exact Hsp | nz]).
    assert (HP1thr : ia_thr2 m P1).
    { intros c Hcs N2 N8. rewrite /P1 upd_ne; [| regne]. exact (Hthr c Hcs N2 N8). }
    assert (HP1ra : P1 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (Hpp82 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x80) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x82)) by pcw.
    iEval (rewrite Hpp82) in "Hpc".
    (* ===== +0x82 c.ldsp s0,48(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ialloc + 0x82))
              (mword_of_int 6 : mword 6) Rs0
              P1 (K - 8)%nat (m !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi82 [Hf2]").
    { iEval (rewrite HP1sp -Hsp Hc2). iExact "Hf2". }
    iIntros (CID2 Hq2) "Hcg Hpc Hf2".
    iEval (rewrite HP1sp -Hsp Hc2) in "Hf2".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2a0 : P2 !!! Regidx Ra0 = (M !!! Regidx Ra0 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1a0 | nz]).
    assert (HP2sp : ia_sp m P2)
      by (rewrite /ia_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2thr : ia_thr2 m P2).
    { intros c Hcs N2 N8. rewrite /P2 upd_ne; [| regne]. exact (HP1thr c Hcs N2 N8). }
    assert (HP2ra : P2 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1ra | nz]).
    assert (Hpp84 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x82) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x84)) by pcw.
    iEval (rewrite Hpp84) in "Hpc".
    (* ===== +0x84 c.addi16sp sp,64 : pop ===== *)
    assert (Hwv : add_vec (P2 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)))
                  = (m !!! Regidx csp_rs1 : mword 64)).
    { rewrite HP2sp. apply bv_eq.
      rewrite !add_vec64_unsigned.
      rewrite bv_wrap_add_idemp_l.
      assert (Hz : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)) : mword 64)
                   = 18446744073709551552) by (vm_compute; reflexivity).
      assert (Hz2 : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)) : mword 64)
                    = 64) by (vm_compute; reflexivity).
      rewrite Hz Hz2.
      replace (bv_unsigned (m !!! Regidx csp_rs1 : mword 64) + 18446744073709551552 + 64)
        with (bv_unsigned (m !!! Regidx csp_rs1 : mword 64) + 18446744073709551616) by ring.
      rewrite -bv_wrap_add_idemp_r.
      assert (Hm0 : bv_wrap 64 18446744073709551616 = 0) by (vm_compute; reflexivity).
      rewrite Hm0 Z.add_0_r.
      apply bv_wrap_small. apply bv_unsigned_in_range. }
    assert (Hpop : (P2 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (P2 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)))) 8).
    { rewrite Hwv HP2sp. unfold pa_stk, add_vec_int. apply f_equal. pcw. }
    iAssert (stack_own (KTR := KT1) (m !!! Regidx csp_rs1 : mword 64) 8)
      with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8]" as "Hstk".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hf1"; [iExists _; iExact "Hf1"|].
      iSplitL "Hf2"; [iExists _; iExact "Hf2"|].
      iSplitL "Hf3"; [iExists _; iExact "Hf3"|].
      iSplitL "Hf4"; [iExists _; iExact "Hf4"|].
      iSplitL "Hf5"; [iExists _; iExact "Hf5"|].
      iSplitL "Hf6"; [iExists _; iExact "Hf6"|].
      iSplitL "Hf7"; [iExists _; iExact "Hf7"|].
      iSplitL "Hf8"; [iExists _; iExact "Hf8"|].
      done. }
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.ialloc + 0x84))
              (mword_of_int 4 : mword 6) P2 (K - 8)%nat 8 b Hpop
              with "Hcg Hpc Hi84 Hstk").
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (P3 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P2 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> P2).
    assert (Hnk : ((K - 8) + 8)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp86 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x84) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x86)) by pcw.
    iEval (rewrite Hpp86) in "Hpc".
    (* ===== +0x86 c.ret ===== *)
    assert (HP3ra : P3 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2ra | nz]).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.ialloc + 0x86)) Rra P3 K b
              ltac:(nz) with "Hcg Hpc Hi86").
    iIntros (CID4 Hq4) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (P3 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HP3ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE CONTRACT ===== *)
    assert (Csp : P3 !!! Regidx csp_rs1 = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P3 upd_eq; exact Hwv).
    assert (Cs0 : P3 !!! Regidx Rs0 = (m !!! Regidx Rs0 : mword 64)).
    { rewrite /P3 upd_ne; [| nz]. rewrite /P2 upd_eq. reflexivity. }
    assert (Hfin : ia_thr2 m P3).
    { intros c Hcs N2 N8. rewrite /P3 upd_ne; [| regne]. exact (HP2thr c Hcs N2 N8). }
    assert (Cs1 : P3 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (apply Hfin; iaidx).
    assert (Cs2 : P3 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64))
      by (apply Hfin; iaidx).
    assert (Cs3 : P3 !!! Regidx Rs3 = (m !!! Regidx Rs3 : mword 64))
      by (apply Hfin; iaidx).
    assert (Cs4 : P3 !!! Regidx Rs4 = (m !!! Regidx Rs4 : mword 64))
      by (apply Hfin; iaidx).
    assert (Cs5 : P3 !!! Regidx Rs5 = (m !!! Regidx Rs5 : mword 64))
      by (apply Hfin; iaidx).
    assert (Cs6 : P3 !!! Regidx Rs6 = (m !!! Regidx Rs6 : mword 64))
      by (apply Hfin; iaidx).
    assert (Cs7 : P3 !!! Regidx (mword_of_int 23 : mword 5)
                  = (m !!! Regidx (mword_of_int 23 : mword 5) : mword 64))
      by (apply Hfin; iaidx).
    assert (Cs8 : P3 !!! Regidx (mword_of_int 24 : mword 5)
                  = (m !!! Regidx (mword_of_int 24 : mword 5) : mword 64))
      by (apply Hfin; iaidx).
    assert (Cs9 : P3 !!! Regidx (mword_of_int 25 : mword 5)
                  = (m !!! Regidx (mword_of_int 25 : mword 5) : mword 64))
      by (apply Hfin; iaidx).
    assert (Cs10 : P3 !!! Regidx (mword_of_int 26 : mword 5)
                  = (m !!! Regidx (mword_of_int 26 : mword 5) : mword 64))
      by (apply Hfin; iaidx).
    assert (Cs11 : P3 !!! Regidx (mword_of_int 27 : mword 5)
                  = (m !!! Regidx (mword_of_int 27 : mword 5) : mword 64))
      by (apply Hfin; iaidx).
    assert (HP3a0 : P3 !!! Regidx Ra0 = (M !!! Regidx Ra0 : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2a0 | nz]).
    assert (Hcs : callee_saved m P3)
      by (unfold callee_saved; split_and!; assumption).
    iDestruct (cpu_own_transport CID0 CID4 0 true (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    rewrite /ia_cont.
    iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain|].
    rewrite /ia_arms.
    iDestruct "Harms" as "[(%Hz & Hiref & Hop) | Hcl]".
    - iApply ("Hcont" $! P3 false 0%nat 1%Qp (mword_of_int 0 : mword 32) ia_dzero
                with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hppid Hsl [Hiref Hop]");
        [exact Hcs |].
      iSplitR; [iPureIntro; rewrite HP3a0; exact Hz |].
      iSplitL "Hiref"; [iExact "Hiref" | iExact "Hop"].
    - iDestruct "Hcl" as (kslot q inum) "(%Hp & Href & Hop)".
      destruct Hp as (Hav & Hks & Hinum & Hnib).
      iApply ("Hcont" $! P3 true kslot q inum (ialloc_fresh ty)
                with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hppid Hsl [Href Hop]");
        [exact Hcs |].
      iSplitR.
      { iPureIntro. rewrite HP3a0.
        split; [exact Hav |]. split; [exact Hks |]. split; [exact Hinum |].
        split; [exact Hnib |]. split; [reflexivity |].
        split; [exact (ialloc_fresh_type ty) | exact (ialloc_fresh_shape ty Hty)]. }
      iSplitL "Href"; [iExact "Href" | iExact "Hop"].
  Qed.

End IallocEpilogue.

(* ===================================================================== *)
(*  +0x66 .. +0x7e : THE SCAN CAME UP EMPTY.  Restore s1..s6, printk the  *)
(*  message, [c.li a0,0], and fall into the epilogue.                     *)
(*                                                                        *)
(*  This is the GENERAL printk path, not the panic path: at ialloc time   *)
(*  [panicking] is 0.  The contract carries printk's own contract as a    *)
(*  PURE hypothesis (SpecIalloc.v's header) so that [Print Assumptions]   *)
(*  stays at the standing six.                                           *)
(* ===================================================================== *)
Section IallocOut.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.

  Local Lemma ia_out `{GEN : GenId} `{CID0 : CpuId}
      (j : nat) (bn : bio_names) (γ : log_names)
      (γpr : gname) (γu : uart_names) (γd : disk_names)
      (inodestart ninodes : Z) (nib : nat) (dev : mword 32) (ty : mword 16)
      (u : nat) (Sb : gset Z)
      (pidv : mword 32) (dq dqs dqn : dfrac)
      (m M : regfile) (K : nat) (b : bool) (lks : gset string) :
    (K_ialloc <= K)%nat ->
    bv_unsigned ty <> 0 ->          (* threaded to [ia_epilogue]; see there *)
    printk_gen_contract (kt := KT1) γpr γu γd ->
    ia_sp m M ->
    ia_thr8 m M ->
    sie_cap_gpr KT1 M (K - 8)%nat b (proc_addr j) -∗
    cpu_own 0 true (proc_addr j) b lks -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.ialloc + 0x66) : mword 64) -∗
    printk_env γpr γu γd -∗
    ia_frame m -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bslots bn 2 -∗
    iref_slot -∗
    log_opS γ (S u) Sb -∗
    ia_cont (CID0 := CID0) γ bn inodestart ninodes nib dev ty u Sb
            pidv dq dqs dqn j m K b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hty Hpk Hsp Hthr.
    pose proof HK as HK'. 
    pose proof ia_msg_fmt as (Hkmsg & Hnmsg & Hlmsg).
    iIntros "Hcg Hcnt #Htext #Hkdata Hpc #Hpenv Hframe Hppid
              Hsbn Hsbi Hsl Hiref Hop Hcont".
    iPoseProof (kernel_data_string ia_msg_addr ia_msg
                  (mword_of_int ia_msg_addr) eq_refl
                  ltac:(unfold text_end, ia_msg_addr; lia) ia_msg_bytes
                  with "Hkdata") as "#Hstr".
    iPoseProof (iali_66 with "Htext") as "Hi66".
    iPoseProof (iali_68 with "Htext") as "Hi68".
    iPoseProof (iali_6a with "Htext") as "Hi6a".
    iPoseProof (iali_6c with "Htext") as "Hi6c".
    iPoseProof (iali_6e with "Htext") as "Hi6e".
    iPoseProof (iali_70 with "Htext") as "Hi70".
    iPoseProof (iali_72 with "Htext") as "Hi72".
    iPoseProof (iali_76 with "Htext") as "Hi76".
    iPoseProof (iali_7a with "Htext") as "Hi7a".
    iPoseProof (iali_7e with "Htext") as "Hi7e".
    rewrite /ia_frame.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8)".
    (* the six callee-save slot addresses, at M's sp *)
    assert (Hc3 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc4 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc5 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 5).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc6 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc7 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 7).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc8 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 8).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    (* ===== +0x66 .. +0x70 : the six restores ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ialloc + 0x66))
              (mword_of_int 5 : mword 6) Rs1
              M (K - 8)%nat (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi66 [Hf3]").
    { iEval (rewrite Hc3). iExact "Hf3". }
    iIntros (CID1 Hq1) "Hcg Hpc Hf3".
    iEval (rewrite Hc3) in "Hf3".
    set (Q1 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> M).
    assert (HQ1sp : ia_sp m Q1)
      by (rewrite /ia_sp /Q1 upd_ne; [exact Hsp | nz]).
    assert (Hpp68 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x66) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x68)) by pcw.
    iEval (rewrite Hpp68) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ialloc + 0x68))
              (mword_of_int 4 : mword 6) Rs2
              Q1 (K - 8)%nat (m !!! Regidx Rs2 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi68 [Hf4]").
    { iEval (rewrite HQ1sp -Hsp Hc4). iExact "Hf4". }
    iIntros (CID2 Hq2) "Hcg Hpc Hf4".
    iEval (rewrite HQ1sp -Hsp Hc4) in "Hf4".
    set (Q2 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> Q1).
    assert (HQ2sp : ia_sp m Q2)
      by (rewrite /ia_sp /Q2 upd_ne; [exact HQ1sp | nz]).
    assert (Hpp6a : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x68) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x6a)) by pcw.
    iEval (rewrite Hpp6a) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ialloc + 0x6a))
              (mword_of_int 3 : mword 6) Rs3
              Q2 (K - 8)%nat (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi6a [Hf5]").
    { iEval (rewrite HQ2sp -Hsp Hc5). iExact "Hf5". }
    iIntros (CID3 Hq3) "Hcg Hpc Hf5".
    iEval (rewrite HQ2sp -Hsp Hc5) in "Hf5".
    set (Q3 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3 : mword 64)]> Q2).
    assert (HQ3sp : ia_sp m Q3)
      by (rewrite /ia_sp /Q3 upd_ne; [exact HQ2sp | nz]).
    assert (Hpp6c : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x6a) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x6c)) by pcw.
    iEval (rewrite Hpp6c) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ialloc + 0x6c))
              (mword_of_int 2 : mword 6) Rs4
              Q3 (K - 8)%nat (m !!! Regidx Rs4 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi6c [Hf6]").
    { iEval (rewrite HQ3sp -Hsp Hc6). iExact "Hf6". }
    iIntros (CID4 Hq4) "Hcg Hpc Hf6".
    iEval (rewrite HQ3sp -Hsp Hc6) in "Hf6".
    set (Q4 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4 : mword 64)]> Q3).
    assert (HQ4sp : ia_sp m Q4)
      by (rewrite /ia_sp /Q4 upd_ne; [exact HQ3sp | nz]).
    assert (Hpp6e : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x6c) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x6e)) by pcw.
    iEval (rewrite Hpp6e) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ialloc + 0x6e))
              (mword_of_int 1 : mword 6) Rs5
              Q4 (K - 8)%nat (m !!! Regidx Rs5 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi6e [Hf7]").
    { iEval (rewrite HQ4sp -Hsp Hc7). iExact "Hf7". }
    iIntros (CID5 Hq5) "Hcg Hpc Hf7".
    iEval (rewrite HQ4sp -Hsp Hc7) in "Hf7".
    set (Q5 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5 : mword 64)]> Q4).
    assert (HQ5sp : ia_sp m Q5)
      by (rewrite /ia_sp /Q5 upd_ne; [exact HQ4sp | nz]).
    assert (Hpp70 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x6e) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x70)) by pcw.
    iEval (rewrite Hpp70) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ialloc + 0x70))
              (mword_of_int 0 : mword 6) Rs6
              Q5 (K - 8)%nat (m !!! Regidx Rs6 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi70 [Hf8]").
    { iEval (rewrite HQ5sp -Hsp Hc8). iExact "Hf8". }
    iIntros (CID6 Hq6) "Hcg Hpc Hf8".
    iEval (rewrite HQ5sp -Hsp Hc8) in "Hf8".
    set (Q6 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6 : mword 64)]> Q5).
    assert (HQ6sp : ia_sp m Q6)
      by (rewrite /ia_sp /Q6 upd_ne; [exact HQ5sp | nz]).
    (* the six registers are back, so the WIDE threading invariant collapses
       to the epilogue's narrow one *)
    assert (HQ6s1 : Q6 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64)).
    { rewrite /Q6 upd_ne; [| nz]. rewrite /Q5 upd_ne; [| nz].
      rewrite /Q4 upd_ne; [| nz]. rewrite /Q3 upd_ne; [| nz].
      rewrite /Q2 upd_ne; [| nz]. rewrite /Q1 upd_eq. reflexivity. }
    assert (HQ6s2 : Q6 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /Q6 upd_ne; [| nz]. rewrite /Q5 upd_ne; [| nz].
      rewrite /Q4 upd_ne; [| nz]. rewrite /Q3 upd_ne; [| nz].
      rewrite /Q2 upd_eq. reflexivity. }
    assert (HQ6s3 : Q6 !!! Regidx Rs3 = (m !!! Regidx Rs3 : mword 64)).
    { rewrite /Q6 upd_ne; [| nz]. rewrite /Q5 upd_ne; [| nz].
      rewrite /Q4 upd_ne; [| nz]. rewrite /Q3 upd_eq. reflexivity. }
    assert (HQ6s4 : Q6 !!! Regidx Rs4 = (m !!! Regidx Rs4 : mword 64)).
    { rewrite /Q6 upd_ne; [| nz]. rewrite /Q5 upd_ne; [| nz].
      rewrite /Q4 upd_eq. reflexivity. }
    assert (HQ6s5 : Q6 !!! Regidx Rs5 = (m !!! Regidx Rs5 : mword 64)).
    { rewrite /Q6 upd_ne; [| nz]. rewrite /Q5 upd_eq. reflexivity. }
    assert (HQ6s6 : Q6 !!! Regidx Rs6 = (m !!! Regidx Rs6 : mword 64))
      by (rewrite /Q6 upd_eq; reflexivity).
    assert (HQ6thr8 : ia_thr8 m Q6).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /Q6 upd_ne; [| regne]. rewrite /Q5 upd_ne; [| regne].
      rewrite /Q4 upd_ne; [| regne]. rewrite /Q3 upd_ne; [| regne].
      rewrite /Q2 upd_ne; [| regne]. rewrite /Q1 upd_ne; [| regne].
      exact (Hthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (HQ6thr : ia_thr2 m Q6).
    { intros c Hcs N2 N8.
      destruct (decide (c = Rs1)) as [->|Nx1]; [exact HQ6s1|].
      destruct (decide (c = Rs2)) as [->|Nx2]; [exact HQ6s2|].
      destruct (decide (c = Rs3)) as [->|Nx3]; [exact HQ6s3|].
      destruct (decide (c = Rs4)) as [->|Nx4]; [exact HQ6s4|].
      destruct (decide (c = Rs5)) as [->|Nx5]; [exact HQ6s5|].
      destruct (decide (c = Rs6)) as [->|Nx6]; [exact HQ6s6|].
      exact (HQ6thr8 c Hcs N2 N8 Nx1 Nx2 Nx3 Nx4 Nx5 Nx6). }
    iAssert (ia_frame m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8]" as "Hframe".
    { rewrite /ia_frame.
      iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
      iSplitL "Hf3"; [iExact "Hf3"|]. iSplitL "Hf4"; [iExact "Hf4"|].
      iSplitL "Hf5"; [iExact "Hf5"|]. iSplitL "Hf6"; [iExact "Hf6"|].
      iSplitL "Hf7"; [iExact "Hf7"|]. iExact "Hf8". }
    assert (Hpp72 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x70) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x72)) by pcw.
    iEval (rewrite Hpp72) in "Hpc".
    (* ===== +0x72 auipc a0,0x4 ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.ialloc + 0x72)) Ra0
              (mword_of_int 4 : mword 20) Q6 (K - 8)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi72").
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (Q7 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.ialloc + 0x72) : mword 64)
                     (auipc_off (mword_of_int 4 : mword 20)))]> Q6).
    assert (HQ7sp : ia_sp m Q7)
      by (rewrite /ia_sp /Q7 upd_ne; [exact HQ6sp | nz]).
    assert (HQ7thr : ia_thr2 m Q7).
    { intros c Hcs N2 N8.
      rewrite /Q7 upd_ne; [| regne]. exact (HQ6thr c Hcs N2 N8). }
    assert (Hpp76 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x72) : mword 64) 4
                    = mword_of_int (KernelSyms.ialloc + 0x76)) by pcw.
    iEval (rewrite Hpp76) in "Hpc".
    (* ===== +0x76 addi a0,a0,850 : a0 := &"ialloc: no inodes\n" ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.ialloc + 0x76)) Ra0 Ra0
              (mword_of_int 856 : mword 12) Q7 (K - 8)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi76").
    iIntros (CID8 Hq8) "Hcg Hpc".
    set (Q8 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (rget Q7 Ra0)
                     (sign_extend' 64 (mword_of_int 856 : mword 12)))]> Q7).
    assert (HQ8a0 : Q8 !!! Regidx Ra0 = (mword_of_int ia_msg_addr : mword 64)).
    { rewrite /Q8 upd_eq. rgne. rewrite /Q7 upd_eq.
      unfold ia_msg_addr. pcw. }
    assert (HQ8sp : ia_sp m Q8)
      by (rewrite /ia_sp /Q8 upd_ne; [exact HQ7sp | nz]).
    assert (HQ8thr : ia_thr2 m Q8).
    { intros c Hcs N2 N8.
      rewrite /Q8 upd_ne; [| regne]. exact (HQ7thr c Hcs N2 N8). }
    assert (Hpp7a : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x76) : mword 64) 4
                    = mword_of_int (KernelSyms.ialloc + 0x7a)) by pcw.
    iEval (rewrite Hpp7a) in "Hpc".
    (* ===== +0x7a jal ra,printk ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.ialloc + 0x7a)) Rra
              (mword_of_int 2085890 : mword 21) Q8 (K - 8)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi7a").
    iIntros (CID9 Hq9) "Hcg Hpc".
    set (Q9 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.ialloc + 0x7a) : mword 64) 4)]> Q8).
    assert (Htgtpk : add_vec (mword_of_int (KernelSyms.ialloc + 0x7a) : mword 64)
                       (sign_extend' 64 (mword_of_int 2085890 : mword 21))
                     = mword_of_int KernelSyms.printk) by pcw.
    iEval (rewrite Htgtpk) in "Hpc".
    assert (HQ9a0 : Q9 !!! Regidx Ra0 = (mword_of_int ia_msg_addr : mword 64))
      by (rewrite /Q9 upd_ne; [exact HQ8a0 | nz]).
    assert (HQ9ra : Q9 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.ialloc + 0x7a) : mword 64) 4)
      by (rewrite /Q9; apply upd_eq).
    assert (HQ9sp : ia_sp m Q9)
      by (rewrite /ia_sp /Q9 upd_ne; [exact HQ8sp | nz]).
    assert (HQ9thr : ia_thr2 m Q9).
    { intros c Hcs N2 N8.
      rewrite /Q9 upd_ne; [| regne]. exact (HQ8thr c Hcs N2 N8). }
    iDestruct (cpu_own_transport CID0 CID9 0 true (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID9) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    (* the panic tail runs at depth 0, so the held set is forced empty and
       printk's order premise ("pr", 14) needs no hypothesis here. *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlkempty Hcnt]".
    iApply (Hpk CID9 Q9 (K - 8)%nat true (proc_addr j)
              DfracDiscarded ia_msg [] b _
              ltac:(lia) Hlmsg Hnmsg ltac:(rewrite Hkmsg; reflexivity)
              ltac:(cbn [length]; lia)
              with "Hcg Htext Hkdata Hpc Hcnt Hpenv [] [//]").
    all: try lkbelow.
    { rewrite HQ9a0. iExact "Hstr". }
    iIntros (CID10 Hq10 mP) "Hcg Hpc %Hcsp Hcnt _ _".
    destruct Hcsp as (Hcs1 & Hraeq).
    assert (Hpc7e : ret_pc (Q9 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.ialloc + 0x7e))
      by (rewrite HQ9ra; pcw).
    iEval (rewrite Hpc7e) in "Hpc".
    pose proof Hcs1 as Hcs1_cs.
    assert (HmPsp : ia_sp m mP).
    { rewrite /ia_sp
        (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HQ9sp. }
    assert (HmPthr : ia_thr2 m mP).
    { intros c Hcs N2 N8.
      rewrite (callee_saved_lookup Hcs1_cs c Hcs). exact (HQ9thr c Hcs N2 N8). }
    (* ===== +0x7e c.li a0,0, then FALL into the epilogue at +0x80 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.ialloc + 0x7e)) Ra0
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
              mP (K - 8)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi7e").
    iIntros (CID11 Hq11) "Hcg Hpc".
    set (QB := <[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> mP).
    assert (HQBa0 : QB !!! Regidx Ra0 = (mword_of_int 0 : mword 64))
      by (rewrite /QB; apply upd_eq).
    assert (HQBsp : ia_sp m QB)
      by (rewrite /ia_sp /QB upd_ne; [exact HmPsp | nz]).
    assert (HQBthr : ia_thr2 m QB).
    { intros c Hcs N2 N8.
      rewrite /QB upd_ne; [| regne]. exact (HmPthr c Hcs N2 N8). }
    assert (Hpp80 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x7e) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x80)) by pcw.
    iEval (rewrite Hpp80) in "Hpc".
    iDestruct (cpu_own_transport CID10 CID11 0 true (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (ia_epilogue (CID0 := CID11) j bn γ inodestart ninodes nib dev ty u Sb
              pidv dq dqs dqn m QB K b lks HK Hty HQBsp HQBthr
              with "Hcg Hcnt Htext Hpc Hframe Hppid Hsbn Hsbi Hsl
                    [Hiref Hop] [Hcont]").
    { rewrite /ia_arms. iLeft.
      iSplitR; [iPureIntro; exact HQBa0 |].
      iSplitL "Hiref"; [iExact "Hiref" | iExact "Hop"]. }
    { iApply (wp_next_shift (b := true) (CIDa := CID9) (CIDb := CID11) ltac:(wp_next_chain)
                with "Hcont"). }
  Qed.

End IallocOut.

(* ===================================================================== *)
(*  +0x88 .. +0xba : THE CLAIM.  memset(dip,0,64) / [sh s6,0(s3)] /       *)
(*  log_write / brelse / iget / pop s1..s6 / [c.j +0x80].                 *)
(*                                                                        *)
(*  Entered from the scan's [c.beqz a5,+54] at +0x52 with the buffer      *)
(*  still HELD, s1 = bp, s3 = &dip, s2 = inum, s5 = dev, s6 = type, and   *)
(*  the decoded [ds] whose slot [islot inum] has type 0.                  *)
(*                                                                        *)
(*  The log_write at +0x9a is the ONLY ghost step, and its fupd premise   *)
(*  is [InodeRegion.ireg_claim_au ⊤ γi γfs inodestart nib inum            *)
(*  (ialloc_fresh ty) ds] -- no resource in, [True] out.                  *)
(* ===================================================================== *)
Section IallocClaim.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.

  Local Lemma ia_claim `{GEN : GenId} `{CID0 : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart inodestart ninodes : Z) (nib : nat)
      (dev : mword 32) (ty : mword 16)
      (inum : mword 32) (ds : list dinode) (u : nat) (Sb : gset Z)
      (kk : nat) (bno : mword 32) (bsd : list (bv 8)) (d0 : bool)
      (pidv : mword 32) (dq dqs dqn : dfrac)
      (m M : regfile) (K : nat) (b : bool) (lks : gset string) :
    (K_ialloc <= K)%nat ->
    log_geom_ok cov logstart ->
    (* the scan's state at +0x88 *)
    ia_sp m M ->
    ia_thr8 m M ->
    M !!! Regidx Rs1 = bnode kk ->
    M !!! Regidx Rs3 = pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat ->
    M !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64) ->
    M !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64) ->
    M !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64) ->
    (kk < NBUF)%nat ->
    uint bno = IBLOCK inum inodestart ->
    IBLOCK inum inodestart ∈ cov ->
    ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
    (* the claim's own premises, all four of [ireg_claim_au]'s *)
    bv_unsigned inum < 16 * Z.of_nat nib ->
    diblk_wf ds ->
    bv_unsigned (di_type (ds !!! DinodeEnc.islot inum)) = 0 ->
    bv_unsigned ty <> 0 ->
    (* and iget's, plus what the arms promise *)
    0 < bv_unsigned inum < ninodes ->
    dislot_align (pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat) ->
    (* ia_claim reaches log_write ("log", 3), brelse ("bcache", 4) and its
       tail iget ("itable", 2); "itable" is the lowest of the three, so one
       premise at its rank covers the whole cone via [locks_below_mono]. *)
    locks_below lks "log" ->
    sie_cap_gpr KT1 M (K - 8)%nat b (proc_addr j) -∗
    cpu_own 0 true (proc_addr j) b lks -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.ialloc + 0x88) : mword 64) -∗
    panic_env -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    ireg_inv γi γfs inodestart nib -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    is_itable2 gtl cn γfs γi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrows cn γfs γi cov logstart -∗
    iref_slot -∗
    ia_frame m -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bslots bn 1 -∗
    log_opS γ (S u) Sb -∗
    bio_held bn (fs_view γfs γd dev cov) kk pidv dev bno
       (diblk_bytes ds) (diblk_bytes ds) bsd d0 -∗
    ia_cont (CID0 := CID0) γ bn inodestart ninodes nib dev ty u Sb
            pidv dq dqs dqn j m K b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hgeom Hsp Hthr Hs1 Hs3 Hs5 Hs6 Hs2 Hkk Hbno Hcov Hlog
           Hnib Hdswf Ht0 Hty Hinum Halign Hbelow.
    pose proof HK as HK'. 
    pose proof (DinodeEnc.islot_lt inum) as Hsl16.
    iIntros "Hcg Hcnt #Htext #Hkdata Hpc #Hpanenv #Hbio #Hlctx #Hireg #Hprocs
              #Hdevi #Hdgeom #Hdlock Hitb2 Hitbl Hesc Hiref
              Hframe Hppid Hsbn Hsbi Hsl Hop Hheld Hcont".
    iPoseProof (iali_88 with "Htext") as "Hi88".
    iPoseProof (iali_8c with "Htext") as "Hi8c".
    iPoseProof (iali_8e with "Htext") as "Hi8e".
    iPoseProof (iali_90 with "Htext") as "Hi90".
    iPoseProof (iali_94 with "Htext") as "Hi94".
    iPoseProof (iali_98 with "Htext") as "Hi98".
    iPoseProof (iali_9a with "Htext") as "Hi9a".
    iPoseProof (iali_9e with "Htext") as "Hi9e".
    iPoseProof (iali_a0 with "Htext") as "Hia0".
    iPoseProof (iali_a4 with "Htext") as "Hia4".
    iPoseProof (iali_a8 with "Htext") as "Hia8".
    iPoseProof (iali_aa with "Htext") as "Hiaa".
    iPoseProof (iali_ae with "Htext") as "Hiae".
    iPoseProof (iali_b0 with "Htext") as "Hib0".
    iPoseProof (iali_b2 with "Htext") as "Hib2".
    iPoseProof (iali_b4 with "Htext") as "Hib4".
    iPoseProof (iali_b6 with "Htext") as "Hib6".
    iPoseProof (iali_b8 with "Htext") as "Hib8".
    iPoseProof (iali_ba with "Htext") as "Hiba".
    (* ---- THE BYTES: peel the 64-byte slot window out of the handle ---- *)
    iDestruct (iu_held_swap with "Hheld") as "[Hbuf Hheldback]".
    iDestruct (iu_buf_bytes (bpa kk) bno (mword_of_int 0 : mword 32) ds Hdswf
                 with "Hbuf") as "[Hbb Hbufback]".
    iDestruct (ia_win_acc (b_data (bpa kk)) ds (DinodeEnc.islot inum)
                 Hdswf Hsl16 with "Hbb") as "[Hby Hwinback]".
    (* ===== +0x88 li a2,64 ===== *)
    iApply (wp_li4_s_sconf (mword_of_int (KernelSyms.ialloc + 0x88)) Ra2
              (mword_of_int 64 : mword 12)
              (mword_of_int (Z.of_nat 64) : mword 64)
              M (K - 8)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi88").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (W0 := <[Regidx Ra2 := regval_into_reg
                  (mword_of_int (Z.of_nat 64) : mword 64)]> M).
    assert (HW0a2 : W0 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 64) : mword 64))
      by (rewrite /W0; apply upd_eq).
    assert (HW0s1 : W0 !!! Regidx Rs1 = bnode kk)
      by (rewrite /W0 upd_ne; [exact Hs1 | nz]).
    assert (HW0s2 : W0 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite /W0 upd_ne; [exact Hs2 | nz]).
    assert (HW0s3 : W0 !!! Regidx Rs3 = (pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat))
      by (rewrite /W0 upd_ne; [exact Hs3 | nz]).
    assert (HW0s5 : W0 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /W0 upd_ne; [exact Hs5 | nz]).
    assert (HW0s6 : W0 !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64))
      by (rewrite /W0 upd_ne; [exact Hs6 | nz]).
    assert (HW0sp : ia_sp m W0)
      by (rewrite /ia_sp /W0 upd_ne; [exact Hsp | nz]).
    assert (HW0thr : ia_thr8 m W0).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /W0 upd_ne; [| regne]. exact (Hthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp8c : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x88) : mword 64) 4
                    = mword_of_int (KernelSyms.ialloc + 0x8c)) by pcw.
    iEval (rewrite Hpp8c) in "Hpc".
    (* ===== +0x8c c.li a1,0 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.ialloc + 0x8c)) Ra1
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
              W0 (K - 8)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi8c").
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (W1 := <[Regidx Ra1 := regval_into_reg (mword_of_int 0 : mword 64)]> W0).
    assert (HW1a1 : W1 !!! Regidx Ra1 = (mword_of_int 0 : mword 64))
      by (rewrite /W1; apply upd_eq).
    assert (HW1a2 : W1 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 64) : mword 64))
      by (rewrite /W1 upd_ne; [exact HW0a2 | nz]).
    assert (HW1s1 : W1 !!! Regidx Rs1 = bnode kk)
      by (rewrite /W1 upd_ne; [exact HW0s1 | nz]).
    assert (HW1s2 : W1 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite /W1 upd_ne; [exact HW0s2 | nz]).
    assert (HW1s3 : W1 !!! Regidx Rs3 = (pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat))
      by (rewrite /W1 upd_ne; [exact HW0s3 | nz]).
    assert (HW1s5 : W1 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /W1 upd_ne; [exact HW0s5 | nz]).
    assert (HW1s6 : W1 !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64))
      by (rewrite /W1 upd_ne; [exact HW0s6 | nz]).
    assert (HW1sp : ia_sp m W1)
      by (rewrite /ia_sp /W1 upd_ne; [exact HW0sp | nz]).
    assert (HW1thr : ia_thr8 m W1).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /W1 upd_ne; [| regne]. exact (HW0thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp8e : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x8c) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x8e)) by pcw.
    iEval (rewrite Hpp8e) in "Hpc".
    (* ===== +0x8e c.mv a0,s3 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ialloc + 0x8e)) Ra0 Rs3
              W1 (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi8e").
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (W2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget W1 Rs3))]> W1).
    assert (HW2a0 : W2 !!! Regidx Ra0 = (pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat)).
    { rewrite /W2 upd_eq. rgne. rewrite HW1s3. apply add_vec_zero_l. }
    assert (HW2a1 : W2 !!! Regidx Ra1 = (mword_of_int 0 : mword 64))
      by (rewrite /W2 upd_ne; [exact HW1a1 | nz]).
    assert (HW2a2 : W2 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 64) : mword 64))
      by (rewrite /W2 upd_ne; [exact HW1a2 | nz]).
    assert (HW2s1 : W2 !!! Regidx Rs1 = bnode kk)
      by (rewrite /W2 upd_ne; [exact HW1s1 | nz]).
    assert (HW2s2 : W2 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite /W2 upd_ne; [exact HW1s2 | nz]).
    assert (HW2s3 : W2 !!! Regidx Rs3 = (pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat))
      by (rewrite /W2 upd_ne; [exact HW1s3 | nz]).
    assert (HW2s5 : W2 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /W2 upd_ne; [exact HW1s5 | nz]).
    assert (HW2s6 : W2 !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64))
      by (rewrite /W2 upd_ne; [exact HW1s6 | nz]).
    assert (HW2sp : ia_sp m W2)
      by (rewrite /ia_sp /W2 upd_ne; [exact HW1sp | nz]).
    assert (HW2thr : ia_thr8 m W2).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /W2 upd_ne; [| regne]. exact (HW1thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp90 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x8e) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x90)) by pcw.
    iEval (rewrite Hpp90) in "Hpc".
    (* ===== +0x90 jal ra,memset ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.ialloc + 0x90)) Rra
              (mword_of_int 2087780 : mword 21) W2 (K - 8)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi90").
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (W3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.ialloc + 0x90) : mword 64) 4)]> W2).
    assert (Htgtms : add_vec (mword_of_int (KernelSyms.ialloc + 0x90) : mword 64)
                       (sign_extend' 64 (mword_of_int 2087780 : mword 21))
                     = mword_of_int KernelSyms.memset) by pcw.
    iEval (rewrite Htgtms) in "Hpc".
    assert (HW3a0 : W3 !!! Regidx Ra0 = (pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat))
      by (rewrite /W3 upd_ne; [exact HW2a0 | nz]).
    assert (HW3a1 : W3 !!! Regidx Ra1 = (mword_of_int 0 : mword 64))
      by (rewrite /W3 upd_ne; [exact HW2a1 | nz]).
    assert (HW3a2 : W3 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 64) : mword 64))
      by (rewrite /W3 upd_ne; [exact HW2a2 | nz]).
    assert (HW3s1 : W3 !!! Regidx Rs1 = bnode kk)
      by (rewrite /W3 upd_ne; [exact HW2s1 | nz]).
    assert (HW3s2 : W3 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite /W3 upd_ne; [exact HW2s2 | nz]).
    assert (HW3s3 : W3 !!! Regidx Rs3 = (pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat))
      by (rewrite /W3 upd_ne; [exact HW2s3 | nz]).
    assert (HW3s5 : W3 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /W3 upd_ne; [exact HW2s5 | nz]).
    assert (HW3s6 : W3 !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64))
      by (rewrite /W3 upd_ne; [exact HW2s6 | nz]).
    assert (HW3sp : ia_sp m W3)
      by (rewrite /ia_sp /W3 upd_ne; [exact HW2sp | nz]).
    assert (HW3ra : W3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.ialloc + 0x90) : mword 64) 4)
      by (rewrite /W3; apply upd_eq).
    assert (HW3thr : ia_thr8 m W3).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /W3 upd_ne; [| regne]. exact (HW2thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    iEval (rewrite -HW3a0) in "Hby".
    iApply (MS.wp_memset_sconf KT1 KT0 W3 (K - 8)%nat 64%nat
              (mword_of_int 0 : mword 64)
              (fun jj => dinode_bytes (ds !!! DinodeEnc.islot inum) !!! jj)
              b (proc_addr j)
              ltac:(lia) ltac:(vm_compute; reflexivity) HW3a1 HW3a2
              with "Hcg Htext Hpc Hby").
    iIntros (CID5 Hq5 mM) "Hcg Hpc Hby %Hcsm".
    iEval (rewrite HW3a0) in "Hby".
    assert (Hpc94 : ret_pc (W3 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.ialloc + 0x94)) by (rewrite HW3ra; pcw).
    iEval (rewrite Hpc94) in "Hpc".
    pose proof Hcsm as Hcsm_cs.
    assert (HmMs1 : mM !!! Regidx Rs1 = bnode kk)
      by (rewrite (callee_saved_lookup Hcsm_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HW3s1).
    assert (HmMs2 : mM !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite (callee_saved_lookup Hcsm_cs Rs2 ltac:(vm_compute; reflexivity));
          exact HW3s2).
    assert (HmMs3 : mM !!! Regidx Rs3 = (pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat))
      by (rewrite (callee_saved_lookup Hcsm_cs Rs3 ltac:(vm_compute; reflexivity));
          exact HW3s3).
    assert (HmMs5 : mM !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite (callee_saved_lookup Hcsm_cs Rs5 ltac:(vm_compute; reflexivity));
          exact HW3s5).
    assert (HmMs6 : mM !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64))
      by (rewrite (callee_saved_lookup Hcsm_cs Rs6 ltac:(vm_compute; reflexivity));
          exact HW3s6).
    assert (HmMsp : ia_sp m mM).
    { rewrite /ia_sp
        (callee_saved_lookup Hcsm_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HW3sp. }
    assert (HmMthr : ia_thr8 m mM).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite (callee_saved_lookup Hcsm_cs c Hcs).
      exact (HW3thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    (* ---- the 64 zero bytes ARE the all-zero dinode ---- *)
    iAssert ([∗ list] jj ∈ seq 0 64,
               pa_add (pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat) jj ↦ₘ (dinode_bytes ia_dzero !!! jj))%I
      with "[Hby]" as "Hby".
    { iApply (big_sepL_mono with "Hby"). intros i jj Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
      (* memset's post carries the [cbyte] its spec's [let] spells; fold it
         onto [ia_cbyte] before the two zero bytes can be identified *)
      rewrite -/ia_cbyte ia_cbyte_zero (ia_dzero_bytes i Hlt). done. }
    iDestruct (dislot_acc_gen (pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat)
                 (fun jj => dinode_bytes ia_dzero !!! jj) ia_dzero
                 Halign ltac:(intros jj Hjj; reflexivity)
                 with "Hby") as "[Hdis Hdisback]".
    rewrite /dislot.
    iDestruct "Hdis" as "(Hd0 & Hd2 & Hd4 & Hd6 & Hd8 & Hda)".
    (* ===== +0x94 sh s6,0(s3) ===== *)
    assert (Hs0adr : add_vec (rget mM Rs3) (sign_extend' 64 (mword_of_int 0 : mword 12))
                     = (pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat)).
    { rgne. rewrite HmMs3. apply iu_off0. }
    iEval (rewrite -Hs0adr) in "Hd0".
    iApply (wp_sh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.ialloc + 0x94)) Rs6 Rs3
              (mword_of_int 0 : mword 12) mM (K - 8)%nat
              (di_type ia_dzero : mword 16) b with "Hcg Hpc Hi94 Hd0").
    iIntros (CID6 Hq6) "Hcg Hpc Hd0".
    iEval (rewrite Hs0adr; rgne; rewrite HmMs6 trunc16_sext64) in "Hd0".
    assert (Hpp98 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x94) : mword 64) 4
                    = mword_of_int (KernelSyms.ialloc + 0x98)) by pcw.
    iEval (rewrite Hpp98) in "Hpc".
    (* ---- the slot now holds [ialloc_fresh ty]; give the block back ---- *)
    iAssert (dislot (pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat) (ialloc_fresh ty)) with "[Hd0 Hd2 Hd4 Hd6 Hd8 Hda]"
      as "Hdis".
    { rewrite /dislot (ia_fresh_of_zero ty).
      cbn [di_type di_major di_minor di_nlink di_size di_addrs].
      iFrame "Hd0 Hd2 Hd4 Hd6 Hd8 Hda". }
    iDestruct ("Hdisback" $! (ialloc_fresh ty)
                 (fun jj => dinode_bytes (ialloc_fresh ty) !!! jj)
                 with "[%] Hdis") as "Hby"; [intros jj Hjj; reflexivity |].
    iDestruct ("Hwinback" $! (ialloc_fresh ty) with "[%] Hby") as "Hbb";
      [exact (ialloc_fresh_wf ty) |].
    iDestruct ("Hbufback" $! (<[DinodeEnc.islot inum := ialloc_fresh ty]> ds)
                 with "[%] Hbb") as "Hbuf".
    { exact (diblk_wf_insert ds (DinodeEnc.islot inum) (ialloc_fresh ty)
               Hdswf (ialloc_fresh_wf ty)). }
    iDestruct ("Hheldback" $!
                 (diblk_bytes (<[DinodeEnc.islot inum := ialloc_fresh ty]> ds))
                 with "Hbuf") as "Hheld".
    (* ===== +0x98 c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ialloc + 0x98)) Ra0 Rs1
              mM (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi98").
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (W4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mM Rs1))]> mM).
    assert (HW4a0 : W4 !!! Regidx Ra0 = bnode kk).
    { rewrite /W4 upd_eq. rgne. rewrite HmMs1. apply add_vec_zero_l. }
    assert (HW4s1 : W4 !!! Regidx Rs1 = bnode kk)
      by (rewrite /W4 upd_ne; [exact HmMs1 | nz]).
    assert (HW4s2 : W4 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite /W4 upd_ne; [exact HmMs2 | nz]).
    assert (HW4s5 : W4 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /W4 upd_ne; [exact HmMs5 | nz]).
    assert (HW4sp : ia_sp m W4)
      by (rewrite /ia_sp /W4 upd_ne; [exact HmMsp | nz]).
    assert (HW4thr : ia_thr8 m W4).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /W4 upd_ne; [| regne]. exact (HmMthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp9a : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x98) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x9a)) by pcw.
    iEval (rewrite Hpp9a) in "Hpc".
    (* ===== +0x9a jal ra,log_write : THE CLAIM ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.ialloc + 0x9a)) Rra
              (mword_of_int 3310 : mword 21) W4 (K - 8)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi9a").
    iIntros (CID8 Hq8) "Hcg Hpc".
    set (W5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.ialloc + 0x9a) : mword 64) 4)]> W4).
    assert (Htgtlw : add_vec (mword_of_int (KernelSyms.ialloc + 0x9a) : mword 64)
                       (sign_extend' 64 (mword_of_int 3310 : mword 21))
                     = mword_of_int KernelSyms.log_write) by pcw.
    iEval (rewrite Htgtlw) in "Hpc".
    assert (HW5a0 : W5 !!! Regidx Ra0 = bnode kk)
      by (rewrite /W5 upd_ne; [exact HW4a0 | nz]).
    assert (HW5s1 : W5 !!! Regidx Rs1 = bnode kk)
      by (rewrite /W5 upd_ne; [exact HW4s1 | nz]).
    assert (HW5s2 : W5 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite /W5 upd_ne; [exact HW4s2 | nz]).
    assert (HW5s5 : W5 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /W5 upd_ne; [exact HW4s5 | nz]).
    assert (HW5sp : ia_sp m W5)
      by (rewrite /ia_sp /W5 upd_ne; [exact HW4sp | nz]).
    assert (HW5ra : W5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.ialloc + 0x9a) : mword 64) 4)
      by (rewrite /W5; apply upd_eq).
    assert (HW5thr : ia_thr8 m W5).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /W5 upd_ne; [| regne]. exact (HW4thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    iDestruct (cpu_own_transport CID0 CID8 0 true (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID8) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKlw : (K_log_write <= K - 8)%nat) by (lia).
    (* THE ONE GHOST STEP (fs-icache.md §16.5): no resource in, [True] out.
       The free inum's fragment is INSIDE the region and stays there, at the
       [fresh_shape] arm; the buffer is the serialiser. *)
    iRename "Hop" into "HopS".
    (* ialloc wants no receipt, so its anchor is the unit (fs-log.md §G.17)
       and its credit is [emp]: this is an ordinary uncredited spend
       ([cr := false]), so log_write's relaxed credited premise (§G.19) costs
       it exactly one [log_credit_own] at the vacuous implication. *)
    iApply fupd_wp. iMod (log_epoch_lb_0 γ) as "#Hlb0". iModIntro.
    iDestruct (log_opS_named with "HopS") as (e0) "HopS".
    iPoseProof (log_credit_own γ false Sb e0 (uint bno) ltac:(discriminate))
      as "#Hcrd".
    iApply (LW.wp_log_write_au bn γ γfs γd cov logstart dev kk pidv bno
              (diblk_bytes (<[DinodeEnc.islot inum := ialloc_fresh ty]> ds))
              (diblk_bytes ds) bsd d0 u
              false Sb e0 0%nat (⊤ ∖ ↑iregN) True%I
              W5 0%nat true (proc_addr j) (K - 8)%nat b lks
              HKlw ltac:(change (2 ^ 31)%Z with 2147483648%Z; lia) Hkk HW5a0
              ltac:(rewrite Hbno; exact Hcov)
              ltac:(rewrite Hbno; exact Hlog)
              (* log_write's bound is "log"(3); ia_claim's own is
                 "itable"(2), and [locks_below_mono] weakens it. *)
              ltac:(lkbelow)
              with "Hcg Hcnt Htext Hpc Hbio Hlctx Hsl Hlb0 Hcrd HopS [] Hheld").
    all: try lkbelow.
    { iEval (rewrite Hbno).
      (* ialloc owes no receipt, so the atomic update's own anchor is the
         unit and both of its closing inputs are dropped: one adapter line
         (fs-log.md §G.17), and [ireg_claim_au] is unchanged. *)
      iApply lw_au_lb0.
      iApply (ireg_claim_au ⊤ γi γfs inodestart nib inum (ialloc_fresh ty) ds
                ltac:(solve_ndisj) Hnib Hdswf Ht0
                (ialloc_fresh_shape ty Hty) with "Hireg"). }
    iIntros (CID9 Hq9 mL) "Hcg Hcnt Hpc %Hcsl HopS _ Hlk Hsl".
    (* the block log_write just logged IS [IBLOCK inum inodestart]: that is
       [Hbno], and it is what makes the growth DETERMINATE. *)
    iEval (rewrite Hbno) in "HopS".
    (* SpecLogWrite's post now hands back the entry with its birth epoch
       named and the epoch-stamped registry row attached (fs-log.md §G.3);
       iupdate/ialloc do not spend it yet, so it is forgotten right here and
       everything below is unchanged.  G-2 replaces this line. *)
    iDestruct (log_opSwe_opSw with "HopS") as "HopS".
    iDestruct (log_opSw_opS with "HopS") as "Hop".
    assert (Hpc9e : ret_pc (W5 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.ialloc + 0x9e)) by (rewrite HW5ra; pcw).
    iEval (rewrite Hpc9e) in "Hpc".
    pose proof Hcsl as Hcsl_cs.
    assert (HmLs1 : mL !!! Regidx Rs1 = bnode kk)
      by (rewrite (callee_saved_lookup Hcsl_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HW5s1).
    assert (HmLs2 : mL !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite (callee_saved_lookup Hcsl_cs Rs2 ltac:(vm_compute; reflexivity));
          exact HW5s2).
    assert (HmLs5 : mL !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite (callee_saved_lookup Hcsl_cs Rs5 ltac:(vm_compute; reflexivity));
          exact HW5s5).
    assert (HmLsp : ia_sp m mL).
    { rewrite /ia_sp
        (callee_saved_lookup Hcsl_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HW5sp. }
    assert (HmLthr : ia_thr8 m mL).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite (callee_saved_lookup Hcsl_cs c Hcs).
      exact (HW5thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    (* ===== +0x9e c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ialloc + 0x9e)) Ra0 Rs1
              mL (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi9e").
    iIntros (CID10 Hq10) "Hcg Hpc".
    set (W6 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mL Rs1))]> mL).
    assert (HW6a0 : W6 !!! Regidx Ra0 = bnode kk).
    { rewrite /W6 upd_eq. rgne. rewrite HmLs1. apply add_vec_zero_l. }
    assert (HW6s2 : W6 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite /W6 upd_ne; [exact HmLs2 | nz]).
    assert (HW6s5 : W6 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /W6 upd_ne; [exact HmLs5 | nz]).
    assert (HW6sp : ia_sp m W6)
      by (rewrite /ia_sp /W6 upd_ne; [exact HmLsp | nz]).
    assert (HW6thr : ia_thr8 m W6).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /W6 upd_ne; [| regne]. exact (HmLthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hppa0 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x9e) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0xa0)) by pcw.
    iEval (rewrite Hppa0) in "Hpc".
    (* ===== +0xa0 jal ra,brelse ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.ialloc + 0xa0)) Rra
              (mword_of_int 2095936 : mword 21) W6 (K - 8)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hia0").
    iIntros (CID11 Hq11) "Hcg Hpc".
    set (W7 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.ialloc + 0xa0) : mword 64) 4)]> W6).
    assert (Htgtbl : add_vec (mword_of_int (KernelSyms.ialloc + 0xa0) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095936 : mword 21))
                     = mword_of_int KernelSyms.brelse) by pcw.
    iEval (rewrite Htgtbl) in "Hpc".
    assert (HW7a0 : W7 !!! Regidx Ra0 = bnode kk)
      by (rewrite /W7 upd_ne; [exact HW6a0 | nz]).
    assert (HW7s2 : W7 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite /W7 upd_ne; [exact HW6s2 | nz]).
    assert (HW7s5 : W7 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /W7 upd_ne; [exact HW6s5 | nz]).
    assert (HW7sp : ia_sp m W7)
      by (rewrite /ia_sp /W7 upd_ne; [exact HW6sp | nz]).
    assert (HW7ra : W7 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.ialloc + 0xa0) : mword 64) 4)
      by (rewrite /W7; apply upd_eq).
    assert (HW7thr : ia_thr8 m W7).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /W7 upd_ne; [| regne]. exact (HW6thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    iDestruct (cpu_own_transport CID9 CID11 0 true (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID8) (CIDb := CID11) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKbl : (K_brelse <= K - 8)%nat) by (lia).
    iApply (BL.wp_brelse_sconf γs bn (fs_view γfs γd dev cov) kk
              pidv dev bno dq W7 (K - 8)%nat true (proc_addr j)
              (diblk_bytes (<[DinodeEnc.islot inum := ialloc_fresh ty]> ds))
              bsd true b lks HKbl Hkk HW7a0
              (* brelse's bound is "bcache"(4); ia_claim's own is
                 "itable"(2), and [locks_below_mono] weakens it. *)
              ltac:(lkbelow)
              with "Hcg Hcnt Htext Hpc Hbio Hppid Hprocs Hlk").
    all: try lkbelow.
    iIntros (CID12 Hq12 mR) "%Hcsr Hcg Hcnt Hpc Hppid Hsl1".
    assert (Hpca4 : ret_pc (W7 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.ialloc + 0xa4)) by (rewrite HW7ra; pcw).
    iEval (rewrite Hpca4) in "Hpc".
    iDestruct (iu_slots_join bn 1 1 with "Hsl Hsl1") as "Hsl".
    pose proof Hcsr as Hcsr_cs.
    assert (HmRs2 : mR !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite (callee_saved_lookup Hcsr_cs Rs2 ltac:(vm_compute; reflexivity));
          exact HW7s2).
    assert (HmRs5 : mR !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite (callee_saved_lookup Hcsr_cs Rs5 ltac:(vm_compute; reflexivity));
          exact HW7s5).
    assert (HmRsp : ia_sp m mR).
    { rewrite /ia_sp
        (callee_saved_lookup Hcsr_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HW7sp. }
    assert (HmRthr : ia_thr8 m mR).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite (callee_saved_lookup Hcsr_cs c Hcs).
      exact (HW7thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    (* ===== +0xa4 addiw a1,s2,0 ===== *)
    iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.ialloc + 0xa4)) Ra1 Rs2
              (mword_of_int 0 : mword 12) mR (K - 8)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hia4").
    iIntros (CID13 Hq13) "Hcg Hpc".
    set (W8 := <[Regidx Ra1 := regval_into_reg
                  (sign_extend' 64
                     (subrange_vec_dec
                        (add_vec (rget mR Rs2)
                           (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0))]> mR).
    assert (HW8a1 : W8 !!! Regidx Ra1 = (sign_extend' 64 inum : mword 64)).
    { rewrite /W8 upd_eq. rgne. rewrite HmRs2 iu_off0.
      rewrite (iu_sub31_sext inum). reflexivity. }
    assert (HW8s5 : W8 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /W8 upd_ne; [exact HmRs5 | nz]).
    assert (HW8sp : ia_sp m W8)
      by (rewrite /ia_sp /W8 upd_ne; [exact HmRsp | nz]).
    assert (HW8thr : ia_thr8 m W8).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /W8 upd_ne; [| regne]. exact (HmRthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hppa8 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0xa4) : mword 64) 4
                    = mword_of_int (KernelSyms.ialloc + 0xa8)) by pcw.
    iEval (rewrite Hppa8) in "Hpc".
    (* ===== +0xa8 c.mv a0,s5 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ialloc + 0xa8)) Ra0 Rs5
              W8 (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hia8").
    iIntros (CID14 Hq14) "Hcg Hpc".
    set (W9 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget W8 Rs5))]> W8).
    assert (HW9a0 : W9 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64)).
    { rewrite /W9 upd_eq. rgne. rewrite HW8s5. apply add_vec_zero_l. }
    assert (HW9a1 : W9 !!! Regidx Ra1 = (sign_extend' 64 inum : mword 64))
      by (rewrite /W9 upd_ne; [exact HW8a1 | nz]).
    assert (HW9sp : ia_sp m W9)
      by (rewrite /ia_sp /W9 upd_ne; [exact HW8sp | nz]).
    assert (HW9thr : ia_thr8 m W9).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /W9 upd_ne; [| regne]. exact (HW8thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hppaa : add_vec_int (mword_of_int (KernelSyms.ialloc + 0xa8) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0xaa)) by pcw.
    iEval (rewrite Hppaa) in "Hpc".
    (* ===== +0xaa jal ra,iget ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.ialloc + 0xaa)) Rra
              (mword_of_int 2096424 : mword 21) W9 (K - 8)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hiaa").
    iIntros (CID15 Hq15) "Hcg Hpc".
    set (WA := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.ialloc + 0xaa) : mword 64) 4)]> W9).
    assert (Htgtig : add_vec (mword_of_int (KernelSyms.ialloc + 0xaa) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096424 : mword 21))
                     = mword_of_int KernelSyms.iget) by pcw.
    iEval (rewrite Htgtig) in "Hpc".
    assert (HWAa0 : WA !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /WA upd_ne; [exact HW9a0 | nz]).
    assert (HWAa1 : WA !!! Regidx Ra1 = (sign_extend' 64 inum : mword 64))
      by (rewrite /WA upd_ne; [exact HW9a1 | nz]).
    assert (HWAsp : ia_sp m WA)
      by (rewrite /ia_sp /WA upd_ne; [exact HW9sp | nz]).
    assert (HWAra : WA !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.ialloc + 0xaa) : mword 64) 4)
      by (rewrite /WA; apply upd_eq).
    assert (HWAthr : ia_thr8 m WA).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /WA upd_ne; [| regne]. exact (HW9thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    iDestruct (cpu_own_transport CID12 CID15 0 true (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID11) (CIDb := CID15) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    (* ==================================================================== *)
    (*  R14: THE SPAN LICENCE -- THE ONE PERMITTED [SpanL] SITE IN THE TREE   *)
    (* ==================================================================== *)
    (*  ialloc has claimed the inum, written [dip->type = ty], [log_write]d
        it and BRELSE'd; at this [iget] it holds nothing revocable at all --
        no buffer half (so licence (e) is unavailable, and §7.2's CURRENCY
        GAP is why no epoch device recovers it), no reference, no fragment.
        The licence the record deserves is (d), [ClaimL], and (d) is
        foreclosed by §7.1.5's theorem until F1.5c mints an [iclaim].

        So this iget presents [SpanL], whose [iname] is [⌜True⌝]: a licence
        that licenses nothing.  The span it names is exactly the gap
        [create_fresh_ty] axiomatizes, and naming it here is what turns the
        axiom's delivery-side perimeter from a paragraph into a grep line --
        [grep -n "SpanL" iris/Proof*.v] must name THIS site and no other.
        It deletes when F1.5c lands (the site becomes [ClaimL], no signature
        moves) or when the axiom retires.  See IgetLic.v's R14 header. *)
    iAssert (iname γi γfs inum SpanL) as "Hlic";
      [rewrite /iname; iPureIntro; exact I |].
    iApply (IG.wp_iget_sconf gtl cn γfs γi cov logstart nib dev inum
              SpanL
              WA 0%nat true (proc_addr j) (K - 8)%nat b lks
              ltac:(lia) ltac:(vm_compute; reflexivity)
              Hnib HWAa0 HWAa1
              ltac:(lkbelow)
              with "Hcg Hcnt Htext Hkdata Hpc Hitb2 Hitbl Hesc Hpanenv Hiref Hlic").
    all: try lkbelow.
    iIntros (CID16 Hq16 mI kslot q) "Hcg Hcnt Hpc %Higp Href _".
    destruct Higp as (Hcsi & Hkslot & Higa0).
    assert (Hpcae : ret_pc (WA !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.ialloc + 0xae)) by (rewrite HWAra; pcw).
    iEval (rewrite Hpcae) in "Hpc".
    pose proof Hcsi as Hcsi_cs.
    assert (HmIsp : ia_sp m mI).
    { rewrite /ia_sp
        (callee_saved_lookup Hcsi_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HWAsp. }
    assert (HmIthr : ia_thr8 m mI).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite (callee_saved_lookup Hcsi_cs c Hcs).
      exact (HWAthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    (* ===== +0xae .. +0xb8 : the six restores ===== *)
    rewrite /ia_frame.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8)".
    assert (Hc3 : add_vec (mI !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HmIsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc4 : add_vec (mI !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite HmIsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc5 : add_vec (mI !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 5).
    { rewrite HmIsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc6 : add_vec (mI !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
    { rewrite HmIsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc7 : add_vec (mI !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 7).
    { rewrite HmIsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc8 : add_vec (mI !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 8).
    { rewrite HmIsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ialloc + 0xae))
              (mword_of_int 5 : mword 6) Rs1
              mI (K - 8)%nat (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hiae [Hf3]").
    { iEval (rewrite Hc3). iExact "Hf3". }
    iIntros (CID17 Hq17) "Hcg Hpc Hf3".
    iEval (rewrite Hc3) in "Hf3".
    set (V1 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> mI).
    assert (HV1a0 : V1 !!! Regidx Ra0 = ientry kslot)
      by (rewrite /V1 upd_ne; [exact Higa0 | nz]).
    assert (HV1sp : ia_sp m V1)
      by (rewrite /ia_sp /V1 upd_ne; [exact HmIsp | nz]).
    assert (Hppb0 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0xae) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0xb0)) by pcw.
    iEval (rewrite Hppb0) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ialloc + 0xb0))
              (mword_of_int 4 : mword 6) Rs2
              V1 (K - 8)%nat (m !!! Regidx Rs2 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hib0 [Hf4]").
    { iEval (rewrite HV1sp -HmIsp Hc4). iExact "Hf4". }
    iIntros (CID18 Hq18) "Hcg Hpc Hf4".
    iEval (rewrite HV1sp -HmIsp Hc4) in "Hf4".
    set (V2 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> V1).
    assert (HV2a0 : V2 !!! Regidx Ra0 = ientry kslot)
      by (rewrite /V2 upd_ne; [exact HV1a0 | nz]).
    assert (HV2sp : ia_sp m V2)
      by (rewrite /ia_sp /V2 upd_ne; [exact HV1sp | nz]).
    assert (Hppb2 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0xb0) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0xb2)) by pcw.
    iEval (rewrite Hppb2) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ialloc + 0xb2))
              (mword_of_int 3 : mword 6) Rs3
              V2 (K - 8)%nat (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hib2 [Hf5]").
    { iEval (rewrite HV2sp -HmIsp Hc5). iExact "Hf5". }
    iIntros (CID19 Hq19) "Hcg Hpc Hf5".
    iEval (rewrite HV2sp -HmIsp Hc5) in "Hf5".
    set (V3 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3 : mword 64)]> V2).
    assert (HV3a0 : V3 !!! Regidx Ra0 = ientry kslot)
      by (rewrite /V3 upd_ne; [exact HV2a0 | nz]).
    assert (HV3sp : ia_sp m V3)
      by (rewrite /ia_sp /V3 upd_ne; [exact HV2sp | nz]).
    assert (Hppb4 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0xb2) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0xb4)) by pcw.
    iEval (rewrite Hppb4) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ialloc + 0xb4))
              (mword_of_int 2 : mword 6) Rs4
              V3 (K - 8)%nat (m !!! Regidx Rs4 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hib4 [Hf6]").
    { iEval (rewrite HV3sp -HmIsp Hc6). iExact "Hf6". }
    iIntros (CID20 Hq20) "Hcg Hpc Hf6".
    iEval (rewrite HV3sp -HmIsp Hc6) in "Hf6".
    set (V4 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4 : mword 64)]> V3).
    assert (HV4a0 : V4 !!! Regidx Ra0 = ientry kslot)
      by (rewrite /V4 upd_ne; [exact HV3a0 | nz]).
    assert (HV4sp : ia_sp m V4)
      by (rewrite /ia_sp /V4 upd_ne; [exact HV3sp | nz]).
    assert (Hppb6 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0xb4) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0xb6)) by pcw.
    iEval (rewrite Hppb6) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ialloc + 0xb6))
              (mword_of_int 1 : mword 6) Rs5
              V4 (K - 8)%nat (m !!! Regidx Rs5 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hib6 [Hf7]").
    { iEval (rewrite HV4sp -HmIsp Hc7). iExact "Hf7". }
    iIntros (CID21 Hq21) "Hcg Hpc Hf7".
    iEval (rewrite HV4sp -HmIsp Hc7) in "Hf7".
    set (V5 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5 : mword 64)]> V4).
    assert (HV5a0 : V5 !!! Regidx Ra0 = ientry kslot)
      by (rewrite /V5 upd_ne; [exact HV4a0 | nz]).
    assert (HV5sp : ia_sp m V5)
      by (rewrite /ia_sp /V5 upd_ne; [exact HV4sp | nz]).
    assert (Hppb8 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0xb6) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0xb8)) by pcw.
    iEval (rewrite Hppb8) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ialloc + 0xb8))
              (mword_of_int 0 : mword 6) Rs6
              V5 (K - 8)%nat (m !!! Regidx Rs6 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hib8 [Hf8]").
    { iEval (rewrite HV5sp -HmIsp Hc8). iExact "Hf8". }
    iIntros (CID22 Hq22) "Hcg Hpc Hf8".
    iEval (rewrite HV5sp -HmIsp Hc8) in "Hf8".
    set (V6 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6 : mword 64)]> V5).
    assert (HV6a0 : V6 !!! Regidx Ra0 = ientry kslot)
      by (rewrite /V6 upd_ne; [exact HV5a0 | nz]).
    assert (HV6sp : ia_sp m V6)
      by (rewrite /ia_sp /V6 upd_ne; [exact HV5sp | nz]).
    assert (HV6s1 : V6 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64)).
    { rewrite /V6 upd_ne; [| nz]. rewrite /V5 upd_ne; [| nz].
      rewrite /V4 upd_ne; [| nz]. rewrite /V3 upd_ne; [| nz].
      rewrite /V2 upd_ne; [| nz]. rewrite /V1 upd_eq. reflexivity. }
    assert (HV6s2 : V6 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /V6 upd_ne; [| nz]. rewrite /V5 upd_ne; [| nz].
      rewrite /V4 upd_ne; [| nz]. rewrite /V3 upd_ne; [| nz].
      rewrite /V2 upd_eq. reflexivity. }
    assert (HV6s3 : V6 !!! Regidx Rs3 = (m !!! Regidx Rs3 : mword 64)).
    { rewrite /V6 upd_ne; [| nz]. rewrite /V5 upd_ne; [| nz].
      rewrite /V4 upd_ne; [| nz]. rewrite /V3 upd_eq. reflexivity. }
    assert (HV6s4 : V6 !!! Regidx Rs4 = (m !!! Regidx Rs4 : mword 64)).
    { rewrite /V6 upd_ne; [| nz]. rewrite /V5 upd_ne; [| nz].
      rewrite /V4 upd_eq. reflexivity. }
    assert (HV6s5 : V6 !!! Regidx Rs5 = (m !!! Regidx Rs5 : mword 64)).
    { rewrite /V6 upd_ne; [| nz]. rewrite /V5 upd_eq. reflexivity. }
    assert (HV6s6 : V6 !!! Regidx Rs6 = (m !!! Regidx Rs6 : mword 64))
      by (rewrite /V6 upd_eq; reflexivity).
    assert (HV6thr8 : ia_thr8 m V6).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /V6 upd_ne; [| regne]. rewrite /V5 upd_ne; [| regne].
      rewrite /V4 upd_ne; [| regne]. rewrite /V3 upd_ne; [| regne].
      rewrite /V2 upd_ne; [| regne]. rewrite /V1 upd_ne; [| regne].
      exact (HmIthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (HV6thr : ia_thr2 m V6).
    { intros c Hcs N2 N8.
      destruct (decide (c = Rs1)) as [->|Nx1]; [exact HV6s1|].
      destruct (decide (c = Rs2)) as [->|Nx2]; [exact HV6s2|].
      destruct (decide (c = Rs3)) as [->|Nx3]; [exact HV6s3|].
      destruct (decide (c = Rs4)) as [->|Nx4]; [exact HV6s4|].
      destruct (decide (c = Rs5)) as [->|Nx5]; [exact HV6s5|].
      destruct (decide (c = Rs6)) as [->|Nx6]; [exact HV6s6|].
      exact (HV6thr8 c Hcs N2 N8 Nx1 Nx2 Nx3 Nx4 Nx5 Nx6). }
    iAssert (ia_frame m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8]" as "Hframe".
    { rewrite /ia_frame.
      iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
      iSplitL "Hf3"; [iExact "Hf3"|]. iSplitL "Hf4"; [iExact "Hf4"|].
      iSplitL "Hf5"; [iExact "Hf5"|]. iSplitL "Hf6"; [iExact "Hf6"|].
      iSplitL "Hf7"; [iExact "Hf7"|]. iExact "Hf8". }
    assert (Hppba : add_vec_int (mword_of_int (KernelSyms.ialloc + 0xb8) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0xba)) by pcw.
    iEval (rewrite Hppba) in "Hpc".
    (* ===== +0xba c.j +0x80 ===== *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.ialloc + 0xba))
              (sign_extend' 21 (concat_vec (mword_of_int 2019 : mword 11) ('b"0")))
              V6 (K - 8)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hiba").
    iIntros (CID23 Hq23). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Hjt : add_vec (mword_of_int (KernelSyms.ialloc + 0xba) : mword 64)
                    (sign_extend' 64 (sign_extend' 21
                       (concat_vec (mword_of_int 2019 : mword 11) ('b"0"))))
                  = mword_of_int (KernelSyms.ialloc + 0x80)) by pcw.
    iEval (rewrite Hjt) in "Hpc".
    iDestruct (cpu_own_transport CID16 CID23 0 true (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (ia_epilogue (CID0 := CID23) j bn γ inodestart ninodes nib dev ty u Sb
              pidv dq dqs dqn m V6 K b lks HK Hty HV6sp HV6thr
              with "Hcg Hcnt Htext Hpc Hframe Hppid Hsbn Hsbi Hsl
                    [Href Hop] [Hcont]").
    { rewrite /ia_arms. iRight. iExists kslot, q, inum.
      iSplitR.
      { iPureIntro. split; [exact HV6a0 |]. split; [exact Hkslot |].
        split; [exact Hinum | exact Hnib]. }
      iSplitL "Href"; [iExact "Href" | iExact "Hop"]. }
    { iApply (wp_next_shift (b := true) (CIDa := CID15) (CIDb := CID23) ltac:(wp_next_chain)
                with "Hcont"). }
  Qed.

End IallocClaim.

(* ===================================================================== *)
(*  +0x30 .. +0x64 : THE SCAN.  bread, the slot arithmetic, [lh], and the *)
(*  two-way branch -- by induction on the fuel [Z.to_nat (ninodes - inum)].*)
(*                                                                        *)
(*  bread SLEEPS, so the invariant is under a [∀ fuel, wp_next ...] the   *)
(*  way ProofDirlookup's scan is: every turn re-enters at +0x30 with a    *)
(*  fresh [CpuId] and the whole bundle.                                   *)
(* ===================================================================== *)
Section IallocScan.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.

  Local Lemma ia_scan `{GEN : GenId} `{CIDe : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname) (γpr : gname)
      (cov : gset Z) (logstart inodestart ninodes : Z) (nib : nat)
      (dev : mword 32) (ty : mword 16) (u : nat) (Sb : gset Z)
      (pidv : mword 32) (dq dqs dqn : dfrac)
      (m : regfile) (K : nat) (b : bool) (lks : gset string) :
    (K_ialloc <= K)%nat ->
    log_geom_ok cov logstart ->
    0 <= inodestart ->
    ireg_blocks_ok inodestart nib cov logstart ->
    1 < ninodes ->
    ninodes <= 16 * Z.of_nat nib ->
    ninodes < 2 ^ 31 ->
    bv_unsigned ty <> 0 ->
    printk_gen_contract (kt := KT1) γpr γu γd ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    (* ia_scan reaches bread/brelse ("bcache", 4, every turn) and ia_claim
       ("itable", 2, the claim arm); "itable" is the lower, so one premise
       at its rank covers the whole cone via [locks_below_mono]. *)
    locks_below lks "log" ->
    kernel_text -∗ kernel_data -∗
    printk_env γpr γu γd -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    ireg_inv γi γfs inodestart nib -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    is_itable2 gtl cn γfs γi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrows cn γfs γi cov logstart -∗
    (* ONE turn of the loop, at any surviving [inum], under any fuel that
       bounds what is left to scan.  Everything else is re-supplied by the
       caller of this wand at every re-entry. *)
    (∀ fuel : nat, wp_next (CID0 := CIDe) b (proc_addr j) (fun (CIDl : CpuId) =>
       ∀ (Ml : regfile) (inum : mword 32) (CIDc : CpuId),
         ⌜(Z.to_nat (ninodes - bv_unsigned inum) <= fuel)%nat⌝ -∗
         ⌜0 < bv_unsigned inum < ninodes⌝ -∗
         ⌜ia_sp m Ml⌝ -∗
         ⌜ia_thr8 m Ml⌝ -∗
         ⌜Ml !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64)⌝ -∗
         ⌜Ml !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64)⌝ -∗
         ⌜Ml !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64)⌝ -∗
         ⌜Ml !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64)⌝ -∗
         sie_cap_gpr KT1 Ml (K - 8)%nat b (proc_addr j) -∗
         cpu_own 0 true (proc_addr j) b lks -∗
         pc_is (mword_of_int (KernelSyms.ialloc + 0x30) : mword 64) -∗
         ia_frame m -∗
         p_pid (proc_addr j) ↦₄{dq} pidv -∗
         sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
         sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
         bslots bn 2 -∗
         iref_slot -∗
         log_opS γ (S u) Sb -∗
         ia_cont (CID0 := CIDc) γ bn inodestart ninodes nib dev ty u Sb
                 pidv dq dqs dqn j m K b lks -∗
         WP (Loop : expr riscv_lang))).
  Proof.
    intros HK Hgeom Hst Hblk Hn1 Hnnib Hn31 Hty Hpk Hj Hgl Hbelow.
    pose proof HK as HK'. 
    pose proof Hgeom as [Hcovok Hlogsub].
    iIntros "#Htext #Hkdata #Hpenv #Hbio #Hlctx #Hireg #Hprocs
              #Hdevi #Hdgeom #Hdlock #Hitb2 #Hitbl #Hesc".
    iPoseProof (printk_env_panic with "Hpenv") as "#Hpanenv".
    iIntros (fuel).
    iInduction fuel as [|fuel] "IH".
    - (* ---- FUEL 0: unreachable, [inum < ninodes] leaves at least one turn ---- *)
      iIntros (CIDl Hql).
      iIntros (Ml inum CIDc) "%Hfuel %Hinum %Hsp %Hthr %Hs2 %Hs4 %Hs5 %Hs6".
      iIntros "Hcg Hcnt Hpc Hframe Hppid Hsbn Hsbi Hsl Hiref Hop Hcont".
      exfalso. lia.
    - (* ---- FUEL S: one turn of the loop ---- *)
      iIntros (CIDl Hql).
      iIntros (Ml inum CIDc) "%Hfuel %Hinum %Hsp %Hthr %Hs2 %Hs4 %Hs5 %Hs6".
      iIntros "Hcg Hcnt Hpc Hframe Hppid Hsbn Hsbi Hsl Hiref Hop Hcont".
      pose proof (bv_unsigned_in_range _ inum) as [Hinum0 Hinum32].
      assert (Hm32 : bv_modulus (MachineWord.MachineWord.Z_idx 32) = 4294967296)
        by (vm_compute; reflexivity).
      rewrite Hm32 in Hinum32.
      assert (Hinum31 : bv_unsigned inum < 2147483648)
        by (change (2^31)%Z with 2147483648%Z in Hn31; lia).
      assert (Hnib : bv_unsigned inum < 16 * Z.of_nat nib) by lia.
      destruct (Hblk inum Hnib) as [Hcov Hlog].
      destruct (Hcovok _ Hcov) as [Hibpos Hiblt].
      assert (Hib : 0 <= IBLOCK inum inodestart < 2147483648)
        by (change (2 ^ 31)%Z with 2147483648%Z in Hiblt; lia).
      set (bno := (mword_of_int (IBLOCK inum inodestart) : mword 32)).
      assert (Hbno : uint bno = IBLOCK inum inodestart).
      { rewrite /bno bb_uint32 moi32_unsigned. apply bvw32_small.
        change (2^32)%Z with 4294967296%Z. lia. }
      assert (Hbnolt : (uint bno < 2147483648)%Z) by (rewrite Hbno; lia).
      assert (Hbnocov : uint bno ∈ bv_cov (fs_view γfs γd dev cov))
        by (rewrite Hbno; exact Hcov).
      assert (Hslotz : Z.of_nat (DinodeEnc.islot inum) = bv_unsigned inum `mod` 16).
      { rewrite /DinodeEnc.islot Z2Nat.id; [reflexivity |].
        pose proof (Z.mod_pos_bound (bv_unsigned inum) 16 ltac:(lia)) as [Hz _].
        exact Hz. }
      pose proof (DinodeEnc.islot_lt inum) as Hslotlt.
      iPoseProof (iali_30 with "Htext") as "Hi30".
      iPoseProof (iali_34 with "Htext") as "Hi34".
      iPoseProof (iali_38 with "Htext") as "Hi38".
      iPoseProof (iali_3a with "Htext") as "Hi3a".
      iPoseProof (iali_3c with "Htext") as "Hi3c".
      iPoseProof (iali_40 with "Htext") as "Hi40".
      iPoseProof (iali_42 with "Htext") as "Hi42".
      iPoseProof (iali_46 with "Htext") as "Hi46".
      iPoseProof (iali_4a with "Htext") as "Hi4a".
      iPoseProof (iali_4c with "Htext") as "Hi4c".
      iPoseProof (iali_4e with "Htext") as "Hi4e".
      iPoseProof (iali_52 with "Htext") as "Hi52".
      iPoseProof (iali_54 with "Htext") as "Hi54".
      iPoseProof (iali_58 with "Htext") as "Hi58".
      iPoseProof (iali_5a with "Htext") as "Hi5a".
      iPoseProof (iali_5e with "Htext") as "Hi5e".
      iPoseProof (iali_62 with "Htext") as "Hi62".
      (* ===== +0x30 srli a1,s2,0x4 : a1 := inum / IPB ===== *)
      iApply (wp_srli4_s_sconf (mword_of_int (KernelSyms.ialloc + 0x30)) Ra1 Rs2
                (mword_of_int 4 : mword 6) Ml (K - 8)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi30").
      iIntros (CID1 Hq1) "Hcg Hpc".
      set (G0 := <[Regidx Ra1 := regval_into_reg
                    (shift_bits_right (rget Ml Rs2)
                       (subrange_vec_dec (mword_of_int 4 : mword 6)
                          (Z.sub log2_xlen 1) 0))]> Ml).
      assert (HG0a1 : G0 !!! Regidx Ra1
                      = (mword_of_int (bv_unsigned inum / 16) : mword 64)).
      { rewrite /G0 upd_eq. rgne. rewrite Hs2. apply ia_srli4. exact Hinum31. }
      assert (HG0s2 : G0 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
        by (rewrite /G0 upd_ne; [exact Hs2 | nz]).
      assert (HG0s4 : G0 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
        by (rewrite /G0 upd_ne; [exact Hs4 | nz]).
      assert (HG0s5 : G0 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
        by (rewrite /G0 upd_ne; [exact Hs5 | nz]).
      assert (HG0s6 : G0 !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64))
        by (rewrite /G0 upd_ne; [exact Hs6 | nz]).
      assert (HG0sp : ia_sp m G0)
        by (rewrite /ia_sp /G0 upd_ne; [exact Hsp | nz]).
      assert (HG0thr : ia_thr8 m G0).
      { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
        rewrite /G0 upd_ne; [| regne]. exact (Hthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
      assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x30) : mword 64) 4
                      = mword_of_int (KernelSyms.ialloc + 0x34)) by pcw.
      iEval (rewrite Hpp34) in "Hpc".
      (* ===== +0x34 lw a5,24(s4) : a5 := sb.inodestart ===== *)
      assert (Hsbiadr : add_vec (rget G0 Rs4)
                          (sign_extend' 64 (mword_of_int 24 : mword 12))
                        = sb_inodestart).
      { rgne. rewrite HG0s4. rewrite /sb_inodestart /pa_add /add_vec_int. pcw. }
      iEval (rewrite -Hsbiadr) in "Hsbi".
      iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.ialloc + 0x34)) Ra5 Rs4
                (mword_of_int 24 : mword 12) G0 (K - 8)%nat
                (mword_of_int inodestart : mword 32) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi34 Hsbi").
      iIntros (CID2 Hq2) "Hcg Hpc Hsbi".
      iEval (rewrite Hsbiadr) in "Hsbi".
      set (G1 := <[Regidx Ra5 := regval_into_reg
                    (sign_extend' 64 (mword_of_int inodestart : mword 32))]> G0).
      assert (HG1a5 : G1 !!! Regidx Ra5
                      = (sign_extend' 64 (mword_of_int inodestart : mword 32) : mword 64))
        by (rewrite /G1; apply upd_eq).
      assert (HG1a1 : G1 !!! Regidx Ra1
                      = (mword_of_int (bv_unsigned inum / 16) : mword 64))
        by (rewrite /G1 upd_ne; [exact HG0a1 | nz]).
      assert (HG1s2 : G1 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
        by (rewrite /G1 upd_ne; [exact HG0s2 | nz]).
      assert (HG1s4 : G1 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
        by (rewrite /G1 upd_ne; [exact HG0s4 | nz]).
      assert (HG1s5 : G1 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
        by (rewrite /G1 upd_ne; [exact HG0s5 | nz]).
      assert (HG1s6 : G1 !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64))
        by (rewrite /G1 upd_ne; [exact HG0s6 | nz]).
      assert (HG1sp : ia_sp m G1)
        by (rewrite /ia_sp /G1 upd_ne; [exact HG0sp | nz]).
      assert (HG1thr : ia_thr8 m G1).
      { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
        rewrite /G1 upd_ne; [| regne]. exact (HG0thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
      assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x34) : mword 64) 4
                      = mword_of_int (KernelSyms.ialloc + 0x38)) by pcw.
      iEval (rewrite Hpp38) in "Hpc".
      (* ===== +0x38 c.addw a1,a1,a5 : a1 := IBLOCK(inum, sb) ===== *)
      iApply (wp_addw_s_sconf (mword_of_int (KernelSyms.ialloc + 0x38)) Ra1 Ra5
                G1 (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi38").
      iIntros (CID3 Hq3) "Hcg Hpc".
      set (G2 := <[Regidx Ra1 := regval_into_reg
                    (sign_extend' 64
                       (add_vec (subrange_vec_dec (rget G1 Ra1) 31 0 : mword 32)
                                (subrange_vec_dec (rget G1 Ra5) 31 0 : mword 32)))]> G1).
      assert (HG2a1 : G2 !!! Regidx Ra1 = (sign_extend' 64 bno : mword 64)).
      { rewrite /G2 upd_eq. rgne. rgne. rewrite HG1a1 HG1a5.
        rewrite /bno.
        (* ialloc's [c.addw a1,a5] has the two summands the other way round
           from iupdate's [c.addw a1,a1,a5] -- hence the commutation *)
        rewrite ia_add_vec32_comm.
        apply (iu_addw_ibl inum inodestart Hst Hib). }
      assert (HG2s2 : G2 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
        by (rewrite /G2 upd_ne; [exact HG1s2 | nz]).
      assert (HG2s4 : G2 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
        by (rewrite /G2 upd_ne; [exact HG1s4 | nz]).
      assert (HG2s5 : G2 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
        by (rewrite /G2 upd_ne; [exact HG1s5 | nz]).
      assert (HG2s6 : G2 !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64))
        by (rewrite /G2 upd_ne; [exact HG1s6 | nz]).
      assert (HG2sp : ia_sp m G2)
        by (rewrite /ia_sp /G2 upd_ne; [exact HG1sp | nz]).
      assert (HG2thr : ia_thr8 m G2).
      { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
        rewrite /G2 upd_ne; [| regne]. exact (HG1thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
      assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x38) : mword 64) 2
                      = mword_of_int (KernelSyms.ialloc + 0x3a)) by pcw.
      iEval (rewrite Hpp3a) in "Hpc".
      (* ===== +0x3a c.mv a0,s5 ===== *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ialloc + 0x3a)) Ra0 Rs5
                G2 (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi3a").
      iIntros (CID4 Hq4) "Hcg Hpc".
      set (G3 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (rget G2 Rs5))]> G2).
      assert (HG3a0 : G3 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64)).
      { rewrite /G3 upd_eq. rgne. rewrite HG2s5. apply add_vec_zero_l. }
      assert (HG3a1 : G3 !!! Regidx Ra1 = (sign_extend' 64 bno : mword 64))
        by (rewrite /G3 upd_ne; [exact HG2a1 | nz]).
      assert (HG3s2 : G3 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
        by (rewrite /G3 upd_ne; [exact HG2s2 | nz]).
      assert (HG3s4 : G3 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
        by (rewrite /G3 upd_ne; [exact HG2s4 | nz]).
      assert (HG3s5 : G3 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
        by (rewrite /G3 upd_ne; [exact HG2s5 | nz]).
      assert (HG3s6 : G3 !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64))
        by (rewrite /G3 upd_ne; [exact HG2s6 | nz]).
      assert (HG3sp : ia_sp m G3)
        by (rewrite /ia_sp /G3 upd_ne; [exact HG2sp | nz]).
      assert (HG3thr : ia_thr8 m G3).
      { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
        rewrite /G3 upd_ne; [| regne]. exact (HG2thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
      assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x3a) : mword 64) 2
                      = mword_of_int (KernelSyms.ialloc + 0x3c)) by pcw.
      iEval (rewrite Hpp3c) in "Hpc".
      (* ===== +0x3c jal ra,bread ===== *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.ialloc + 0x3c)) Rra
                (mword_of_int 2095772 : mword 21) G3 (K - 8)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi3c").
      iIntros (CID5 Hq5) "Hcg Hpc".
      set (G4 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.ialloc + 0x3c) : mword 64) 4)]> G3).
      assert (Htgtbr : add_vec (mword_of_int (KernelSyms.ialloc + 0x3c) : mword 64)
                         (sign_extend' 64 (mword_of_int 2095772 : mword 21))
                       = mword_of_int KernelSyms.bread) by pcw.
      iEval (rewrite Htgtbr) in "Hpc".
      assert (HG4a0 : G4 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
        by (rewrite /G4 upd_ne; [exact HG3a0 | nz]).
      assert (HG4a1 : G4 !!! Regidx Ra1 = (sign_extend' 64 bno : mword 64))
        by (rewrite /G4 upd_ne; [exact HG3a1 | nz]).
      assert (HG4s2 : G4 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
        by (rewrite /G4 upd_ne; [exact HG3s2 | nz]).
      assert (HG4s4 : G4 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
        by (rewrite /G4 upd_ne; [exact HG3s4 | nz]).
      assert (HG4s5 : G4 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
        by (rewrite /G4 upd_ne; [exact HG3s5 | nz]).
      assert (HG4s6 : G4 !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64))
        by (rewrite /G4 upd_ne; [exact HG3s6 | nz]).
      assert (HG4sp : ia_sp m G4)
        by (rewrite /ia_sp /G4 upd_ne; [exact HG3sp | nz]).
      assert (HG4ra : G4 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KernelSyms.ialloc + 0x3c) : mword 64) 4)
        by (rewrite /G4; apply upd_eq).
      assert (HG4thr : ia_thr8 m G4).
      { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
        rewrite /G4 upd_ne; [| regne]. exact (HG3thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
      iDestruct (cpu_own_transport CIDc CID5 0 true (proc_addr j) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (wp_next_shift (b := true) (CIDa := CIDc) (CIDb := CID5) ltac:(wp_next_chain)
                   with "Hcont") as "Hcont".
      assert (HKbr : (K_bread <= K - 8)%nat) by (lia).
      iDestruct (iu_slots_split bn 1 1 with "Hsl") as "[Hsl Hsl1]".
      iApply (BR.wp_bread_sconf γs j γl γu γd γk pd pav pu bn
                (fs_view γfs γd dev cov) pidv dev bno dq
                G4 (K - 8)%nat true b lks
                HKbr Hbnolt eq_refl Hbnocov eq_refl Hj Hgl HG4a0 HG4a1
                (* bread's bound is "bcache"(4); ia_scan's own is
                   "itable"(2), and [locks_below_mono] weakens it. *)
                ltac:(lkbelow)
                with "Hcg Hcnt [] [] Htext Hkdata Hpc Hpanenv Hbio Hppid Hprocs
                      Hdevi Hdgeom Hdlock Hsl1").
      all: try lkbelow.
      { rewrite /trap_csrs_ext. done. }
      { rewrite /cpu_claim_ext. done. }
      iIntros (CID6 Hq6 mB kk bs0 bsd0 d0) "%Hfacts Hcg Hcnt _ _ Hpc Hppid Hheld".
      destruct Hfacts as [Hcsb HmBa0].
      assert (Hpc40 : ret_pc (G4 !!! Regidx Rra : mword 64)
                      = mword_of_int (KernelSyms.ialloc + 0x40)) by (rewrite HG4ra; pcw).
      iEval (rewrite Hpc40) in "Hpc".
      pose proof Hcsb as Hcsb_cs.
      assert (HmBs2 : mB !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
        by (rewrite (callee_saved_lookup Hcsb_cs Rs2 ltac:(vm_compute; reflexivity));
            exact HG4s2).
      assert (HmBs4 : mB !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
        by (rewrite (callee_saved_lookup Hcsb_cs Rs4 ltac:(vm_compute; reflexivity));
            exact HG4s4).
      assert (HmBs5 : mB !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
        by (rewrite (callee_saved_lookup Hcsb_cs Rs5 ltac:(vm_compute; reflexivity));
            exact HG4s5).
      assert (HmBs6 : mB !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64))
        by (rewrite (callee_saved_lookup Hcsb_cs Rs6 ltac:(vm_compute; reflexivity));
            exact HG4s6).
      assert (HmBsp : ia_sp m mB).
      { rewrite /ia_sp
          (callee_saved_lookup Hcsb_cs csp_rs1 ltac:(vm_compute; reflexivity)).
        exact HG4sp. }
      assert (HmBthr : ia_thr8 m mB).
      { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
        rewrite (callee_saved_lookup Hcsb_cs c Hcs).
        exact (HG4thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
      (* THE DECODE: the bytes bread returned ARE sixteen dinodes.  No
         fragment is involved -- the machinery half riding in the handle's
         payload pins the region's parked bytes ([ireg_read_blk], §16). *)
      iEval (rewrite /bio_locked) in "Hheld".
      iDestruct (iu_held_k with "Hheld") as %Hkk.
      iDestruct (ia_held_L with "Hheld") as "[HpL Hheldback0]".
      iApply fupd_wp.
      iEval (rewrite Hbno (ireg_bi_iblock inum inodestart)) in "HpL".
      iMod (ireg_read_blk ⊤ γi γfs inodestart nib (ireg_bi inum) bs0
              ltac:(solve_ndisj) (ireg_bi_lt inum nib Hnib)
              with "Hireg HpL") as "(%Hex & HpL)".
      iModIntro.
      iEval (rewrite -(ireg_bi_iblock inum inodestart) -Hbno) in "HpL".
      iDestruct ("Hheldback0" with "HpL") as "Hheld".
      destruct Hex as (ds & Hdswf & Hbs0).
      subst bs0.
      assert (Hslotal : dislot_align
                (pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat)).
      { rewrite /dislot_align.
        assert (E0 : (64 * DinodeEnc.islot inum)%nat
                     = (64 * DinodeEnc.islot inum + 0)%nat) by lia.
        split_and!.
        - rewrite E0. apply iu_align; [exact Hkk | exact Hslotlt | lia
                                      | left; reflexivity | reflexivity].
        - rewrite pa_add_add. apply iu_align;
            [exact Hkk | exact Hslotlt | lia | left; reflexivity | reflexivity].
        - rewrite pa_add_add. apply iu_align;
            [exact Hkk | exact Hslotlt | lia | left; reflexivity | reflexivity].
        - rewrite pa_add_add. apply iu_align;
            [exact Hkk | exact Hslotlt | lia | left; reflexivity | reflexivity].
        - rewrite pa_add_add. apply iu_align;
            [exact Hkk | exact Hslotlt | lia | right; reflexivity | reflexivity]. }
      (* ===== +0x40 c.mv s1,a0 ===== *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ialloc + 0x40)) Rs1 Ra0
                mB (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi40").
      iIntros (CID7 Hq7) "Hcg Hpc".
      set (G5 := <[Regidx Rs1 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (rget mB Ra0))]> mB).
      assert (HG5s1 : G5 !!! Regidx Rs1 = bnode kk).
      { rewrite /G5 upd_eq. rgne. rewrite HmBa0. apply add_vec_zero_l. }
      assert (HG5a0 : G5 !!! Regidx Ra0 = bnode kk)
        by (rewrite /G5 upd_ne; [exact HmBa0 | nz]).
      assert (HG5s2 : G5 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
        by (rewrite /G5 upd_ne; [exact HmBs2 | nz]).
      assert (HG5s4 : G5 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
        by (rewrite /G5 upd_ne; [exact HmBs4 | nz]).
      assert (HG5s5 : G5 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
        by (rewrite /G5 upd_ne; [exact HmBs5 | nz]).
      assert (HG5s6 : G5 !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64))
        by (rewrite /G5 upd_ne; [exact HmBs6 | nz]).
      assert (HG5sp : ia_sp m G5)
        by (rewrite /ia_sp /G5 upd_ne; [exact HmBsp | nz]).
      assert (HG5thr : ia_thr8 m G5).
      { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
        rewrite /G5 upd_ne; [| regne]. exact (HmBthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
      assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x40) : mword 64) 2
                      = mword_of_int (KernelSyms.ialloc + 0x42)) by pcw.
      iEval (rewrite Hpp42) in "Hpc".
      (* ===== +0x42 addi s3,a0,88 : s3 := bp->data ===== *)
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.ialloc + 0x42)) Rs3 Ra0
                (mword_of_int 88 : mword 12) G5 (K - 8)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi42").
      iIntros (CID8 Hq8) "Hcg Hpc".
      set (G6 := <[Regidx Rs3 := regval_into_reg
                    (add_vec (rget G5 Ra0)
                       (sign_extend' 64 (mword_of_int 88 : mword 12)))]> G5).
      assert (HG6s3 : G6 !!! Regidx Rs3 = b_data (bpa kk)).
      { rewrite /G6 upd_eq. rgne. rewrite HG5a0. apply iu_data_addr. }
      assert (HG6a0 : G6 !!! Regidx Ra0 = bnode kk)
        by (rewrite /G6 upd_ne; [exact HG5a0 | nz]).
      assert (HG6s1 : G6 !!! Regidx Rs1 = bnode kk)
        by (rewrite /G6 upd_ne; [exact HG5s1 | nz]).
      assert (HG6s2 : G6 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
        by (rewrite /G6 upd_ne; [exact HG5s2 | nz]).
      assert (HG6s4 : G6 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
        by (rewrite /G6 upd_ne; [exact HG5s4 | nz]).
      assert (HG6s5 : G6 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
        by (rewrite /G6 upd_ne; [exact HG5s5 | nz]).
      assert (HG6s6 : G6 !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64))
        by (rewrite /G6 upd_ne; [exact HG5s6 | nz]).
      assert (HG6sp : ia_sp m G6)
        by (rewrite /ia_sp /G6 upd_ne; [exact HG5sp | nz]).
      assert (HG6thr : ia_thr8 m G6).
      { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
        rewrite /G6 upd_ne; [| regne]. exact (HG5thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
      assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x42) : mword 64) 4
                      = mword_of_int (KernelSyms.ialloc + 0x46)) by pcw.
      iEval (rewrite Hpp46) in "Hpc".
      (* ===== +0x46 andi a5,s2,15 : a5 := inum % IPB ===== *)
      iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.ialloc + 0x46)) Ra5 Rs2
                (mword_of_int 15 : mword 12)
                (mword_of_int (Z.of_nat (DinodeEnc.islot inum)) : mword 64)
                G6 (K - 8)%nat b ltac:(nz) ltac:(rdok)
                ltac:(rgne; rewrite HG6s2 ia_andi15 iu_sext_mod16 Hslotz; reflexivity)
                with "Hcg Hpc Hi46").
      iIntros (CID9 Hq9) "Hcg Hpc".
      set (G7 := <[Regidx Ra5 := regval_into_reg
                    (mword_of_int (Z.of_nat (DinodeEnc.islot inum)) : mword 64)]> G6).
      assert (HG7a5 : G7 !!! Regidx Ra5
                      = (mword_of_int (Z.of_nat (DinodeEnc.islot inum)) : mword 64))
        by (rewrite /G7; apply upd_eq).
      assert (HG7s3 : G7 !!! Regidx Rs3 = b_data (bpa kk))
        by (rewrite /G7 upd_ne; [exact HG6s3 | nz]).
      assert (HG7a0 : G7 !!! Regidx Ra0 = bnode kk)
        by (rewrite /G7 upd_ne; [exact HG6a0 | nz]).
      assert (HG7s1 : G7 !!! Regidx Rs1 = bnode kk)
        by (rewrite /G7 upd_ne; [exact HG6s1 | nz]).
      assert (HG7s2 : G7 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
        by (rewrite /G7 upd_ne; [exact HG6s2 | nz]).
      assert (HG7s4 : G7 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
        by (rewrite /G7 upd_ne; [exact HG6s4 | nz]).
      assert (HG7s5 : G7 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
        by (rewrite /G7 upd_ne; [exact HG6s5 | nz]).
      assert (HG7s6 : G7 !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64))
        by (rewrite /G7 upd_ne; [exact HG6s6 | nz]).
      assert (HG7sp : ia_sp m G7)
        by (rewrite /ia_sp /G7 upd_ne; [exact HG6sp | nz]).
      assert (HG7thr : ia_thr8 m G7).
      { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
        rewrite /G7 upd_ne; [| regne]. exact (HG6thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
      assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x46) : mword 64) 4
                      = mword_of_int (KernelSyms.ialloc + 0x4a)) by pcw.
      iEval (rewrite Hpp4a) in "Hpc".
      (* ===== +0x4a c.slli a5,0x6 ===== *)
      iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.ialloc + 0x4a)) (Regidx Ra5) Ra5
                (mword_of_int 6 : mword 6) G7 (K - 8)%nat b
                ltac:(reflexivity) ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi4a").
      iIntros (CID10 Hq10) "Hcg Hpc".
      set (G8 := <[Regidx Ra5 := regval_into_reg
                    (shift_bits_left (rget G7 Ra5)
                       (subrange_vec_dec (mword_of_int 6 : mword 6)
                          (Z.sub log2_xlen 1) 0))]> G7).
      assert (HG8a5 : G8 !!! Regidx Ra5
                      = (mword_of_int (64 * Z.of_nat (DinodeEnc.islot inum)) : mword 64)).
      { rewrite /G8 upd_eq. rgne. rewrite HG7a5. apply iu_slli6; lia. }
      assert (HG8s3 : G8 !!! Regidx Rs3 = b_data (bpa kk))
        by (rewrite /G8 upd_ne; [exact HG7s3 | nz]).
      assert (HG8a0 : G8 !!! Regidx Ra0 = bnode kk)
        by (rewrite /G8 upd_ne; [exact HG7a0 | nz]).
      assert (HG8s1 : G8 !!! Regidx Rs1 = bnode kk)
        by (rewrite /G8 upd_ne; [exact HG7s1 | nz]).
      assert (HG8s2 : G8 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
        by (rewrite /G8 upd_ne; [exact HG7s2 | nz]).
      assert (HG8s4 : G8 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
        by (rewrite /G8 upd_ne; [exact HG7s4 | nz]).
      assert (HG8s5 : G8 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
        by (rewrite /G8 upd_ne; [exact HG7s5 | nz]).
      assert (HG8s6 : G8 !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64))
        by (rewrite /G8 upd_ne; [exact HG7s6 | nz]).
      assert (HG8sp : ia_sp m G8)
        by (rewrite /ia_sp /G8 upd_ne; [exact HG7sp | nz]).
      assert (HG8thr : ia_thr8 m G8).
      { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
        rewrite /G8 upd_ne; [| regne]. exact (HG7thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
      assert (Hpp4c : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x4a) : mword 64) 2
                      = mword_of_int (KernelSyms.ialloc + 0x4c)) by pcw.
      iEval (rewrite Hpp4c) in "Hpc".
      (* ===== +0x4c c.add s3,s3,a5 : s3 := dip ===== *)
      iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.ialloc + 0x4c)) Rs3 Ra5
                G8 (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi4c").
      iIntros (CID11 Hq11) "Hcg Hpc".
      set (G9 := <[Regidx Rs3 := regval_into_reg
                    (add_vec (rget G8 Rs3) (rget G8 Ra5))]> G8).
      assert (HG9s3 : G9 !!! Regidx Rs3
                      = pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat).
      { rewrite /G9 upd_eq. rgne. rgne. rewrite HG8s3 HG8a5. apply iu_slot_addr. }
      assert (HG9a0 : G9 !!! Regidx Ra0 = bnode kk)
        by (rewrite /G9 upd_ne; [exact HG8a0 | nz]).
      assert (HG9s1 : G9 !!! Regidx Rs1 = bnode kk)
        by (rewrite /G9 upd_ne; [exact HG8s1 | nz]).
      assert (HG9s2 : G9 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
        by (rewrite /G9 upd_ne; [exact HG8s2 | nz]).
      assert (HG9s4 : G9 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
        by (rewrite /G9 upd_ne; [exact HG8s4 | nz]).
      assert (HG9s5 : G9 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
        by (rewrite /G9 upd_ne; [exact HG8s5 | nz]).
      assert (HG9s6 : G9 !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64))
        by (rewrite /G9 upd_ne; [exact HG8s6 | nz]).
      assert (HG9sp : ia_sp m G9)
        by (rewrite /ia_sp /G9 upd_ne; [exact HG8sp | nz]).
      assert (HG9thr : ia_thr8 m G9).
      { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
        rewrite /G9 upd_ne; [| regne]. exact (HG8thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
      assert (Hpp4e : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x4c) : mword 64) 2
                      = mword_of_int (KernelSyms.ialloc + 0x4e)) by pcw.
      iEval (rewrite Hpp4e) in "Hpc".
      (* ===== +0x4e lh a5,0(s3) : a5 := dip->type ===== *)
      iDestruct (iu_held_swap with "Hheld") as "[Hbuf Hheldback]".
      iDestruct (iu_buf_bytes (bpa kk) bno (mword_of_int 0 : mword 32) ds Hdswf
                   with "Hbuf") as "[Hbb Hbbback]".
      iDestruct (diblk_slot_acc (b_data (bpa kk)) ds (DinodeEnc.islot inum)
                   Hdswf Hslotlt Hslotal with "Hbb") as "[Hdis Hdisback]".
      rewrite /dislot.
      iDestruct "Hdis" as "(Hd0 & Hd2 & Hd4 & Hd6 & Hd8 & Hda)".
      assert (Hlhadr : add_vec (rget G9 Rs3)
                         (sign_extend' 64 (mword_of_int 0 : mword 12))
                       = pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat).
      { rgne. rewrite HG9s3. apply iu_off0. }
      iEval (rewrite -Hlhadr) in "Hd0".
      iApply (wp_lh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.ialloc + 0x4e)) Ra5 Rs3
                (mword_of_int 0 : mword 12) G9 (K - 8)%nat
                (di_type (ds !!! DinodeEnc.islot inum) : mword 16) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi4e Hd0").
      iIntros (CID12 Hq12) "Hcg Hpc Hd0".
      iEval (rewrite Hlhadr) in "Hd0".
      set (GA := <[Regidx Ra5 := regval_into_reg
                    (sign_extend' 64
                       (di_type (ds !!! DinodeEnc.islot inum) : mword 16))]> G9).
      assert (HGAa5 : GA !!! Regidx Ra5
                      = (sign_extend' 64
                           (di_type (ds !!! DinodeEnc.islot inum) : mword 16)
                         : mword 64))
        by (rewrite /GA; apply upd_eq).
      assert (HGAs3 : GA !!! Regidx Rs3
                      = pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat)
        by (rewrite /GA upd_ne; [exact HG9s3 | nz]).
      assert (HGAa0 : GA !!! Regidx Ra0 = bnode kk)
        by (rewrite /GA upd_ne; [exact HG9a0 | nz]).
      assert (HGAs1 : GA !!! Regidx Rs1 = bnode kk)
        by (rewrite /GA upd_ne; [exact HG9s1 | nz]).
      assert (HGAs2 : GA !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
        by (rewrite /GA upd_ne; [exact HG9s2 | nz]).
      assert (HGAs4 : GA !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
        by (rewrite /GA upd_ne; [exact HG9s4 | nz]).
      assert (HGAs5 : GA !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
        by (rewrite /GA upd_ne; [exact HG9s5 | nz]).
      assert (HGAs6 : GA !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64))
        by (rewrite /GA upd_ne; [exact HG9s6 | nz]).
      assert (HGAsp : ia_sp m GA)
        by (rewrite /ia_sp /GA upd_ne; [exact HG9sp | nz]).
      assert (HGAthr : ia_thr8 m GA).
      { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
        rewrite /GA upd_ne; [| regne]. exact (HG9thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
      (* the slot goes back UNCHANGED and the handle is whole again *)
      iAssert (dislot (pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat)
                 (ds !!! DinodeEnc.islot inum))
        with "[Hd0 Hd2 Hd4 Hd6 Hd8 Hda]" as "Hdis".
      { rewrite /dislot. iFrame "Hd0 Hd2 Hd4 Hd6 Hd8 Hda". }
      assert (Hins : <[DinodeEnc.islot inum := ds !!! DinodeEnc.islot inum]> ds = ds).
      { apply list_insert_id. apply list_lookup_lookup_total_lt.
        destruct Hdswf as [Hlen _]. rewrite Hlen. exact Hslotlt. }
      iDestruct ("Hdisback" $! (ds !!! DinodeEnc.islot inum) with "[%] Hdis") as "Hbb".
      { exact (ireg_blk_slot ds (DinodeEnc.islot inum) Hdswf Hslotlt). }
      iEval (rewrite Hins) in "Hbb".
      iDestruct ("Hbbback" $! ds with "[%] Hbb") as "Hbuf"; [exact Hdswf |].
      iDestruct ("Hheldback" $! (diblk_bytes ds) with "Hbuf") as "Hheld".
      assert (Hpp52 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x4e) : mword 64) 4
                      = mword_of_int (KernelSyms.ialloc + 0x52)) by pcw.
      iEval (rewrite Hpp52) in "Hpc".
      (* ===== +0x52 c.beqz a5,+54 : a free inode? ===== *)
      destruct (decide (bv_unsigned (di_type (ds !!! DinodeEnc.islot inum)) = 0))
        as [Ht0|Ht0].
      + (* ---- TAKEN: THE CLAIM at +0x88 ---- *)
        assert (Hcmp : eq_vec (rget GA Ra5) (zero_reg : mword 64) = true).
        { rgne. rewrite HGAa5. apply ia_type_zero. exact Ht0. }
        iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.ialloc + 0x52))
                  (mword_of_int 27 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                  GA (K - 8)%nat b ltac:(vm_compute; reflexivity) ltac:(nz) Hcmp
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi52").
        iApply bi.later_intro. iIntros (CID13 Hq13) "Hcg Hpc".
        assert (Hjt : add_vec (mword_of_int (KernelSyms.ialloc + 0x52) : mword 64)
                        (sign_extend' 64 (sign_extend' 13
                           (concat_vec (mword_of_int 27 : mword 8) ('b"0"))))
                      = mword_of_int (KernelSyms.ialloc + 0x88)) by pcw.
        iEval (rewrite Hjt) in "Hpc".
        iDestruct (cpu_own_transport CID6 CID13 0 true (proc_addr j) b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iApply (ia_claim (CID0 := CID13) γs j γl γu γd γk pd pav pu bn γ γfs γi
                  cn gtl cov logstart inodestart ninodes nib dev ty inum ds u Sb
                  kk bno bsd0 d0 pidv dq dqs dqn m GA K b lks
                  HK Hgeom HGAsp HGAthr HGAs1 HGAs3 HGAs5 HGAs6 HGAs2 Hkk
                  Hbno Hcov Hlog Hnib Hdswf Ht0 Hty Hinum Hslotal
                  Hbelow
                  with "Hcg Hcnt Htext Hkdata Hpc Hpanenv Hbio Hlctx Hireg Hprocs
                        Hdevi Hdgeom Hdlock Hitb2 Hitbl Hesc Hiref Hframe
                        Hppid Hsbn Hsbi Hsl Hop Hheld [Hcont]").
        { iApply (wp_next_shift (b := true) (CIDa := CID5) (CIDb := CID13)
                    ltac:(wp_next_chain) with "Hcont"). }
      + (* ---- FALL: brelse, inum++, and the loop test ---- *)
        assert (Hcmp : eq_vec (rget GA Ra5) (zero_reg : mword 64) = false).
        { rgne. rewrite HGAa5. apply ia_type_nonzero. exact Ht0. }
        iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.ialloc + 0x52))
                  (mword_of_int 27 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                  GA (K - 8)%nat b ltac:(vm_compute; reflexivity) ltac:(nz) Hcmp
                  with "Hcg Hpc Hi52").
        iIntros (CID13 Hq13) "Hcg Hpc".
        assert (Hpp54 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x52) : mword 64) 2
                        = mword_of_int (KernelSyms.ialloc + 0x54)) by pcw.
        iEval (rewrite Hpp54) in "Hpc".
        (* ===== +0x54 jal ra,brelse ===== *)
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.ialloc + 0x54)) Rra
                  (mword_of_int 2096012 : mword 21) GA (K - 8)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi54").
        iIntros (CID14 Hq14) "Hcg Hpc".
        set (GB := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (KernelSyms.ialloc + 0x54) : mword 64) 4)]> GA).
        assert (Htgtbl : add_vec (mword_of_int (KernelSyms.ialloc + 0x54) : mword 64)
                           (sign_extend' 64 (mword_of_int 2096012 : mword 21))
                         = mword_of_int KernelSyms.brelse) by pcw.
        iEval (rewrite Htgtbl) in "Hpc".
        assert (HGBa0 : GB !!! Regidx Ra0 = bnode kk)
          by (rewrite /GB upd_ne; [exact HGAa0 | nz]).
        assert (HGBs2 : GB !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
          by (rewrite /GB upd_ne; [exact HGAs2 | nz]).
        assert (HGBs4 : GB !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
          by (rewrite /GB upd_ne; [exact HGAs4 | nz]).
        assert (HGBs5 : GB !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
          by (rewrite /GB upd_ne; [exact HGAs5 | nz]).
        assert (HGBs6 : GB !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64))
          by (rewrite /GB upd_ne; [exact HGAs6 | nz]).
        assert (HGBsp : ia_sp m GB)
          by (rewrite /ia_sp /GB upd_ne; [exact HGAsp | nz]).
        assert (HGBra : GB !!! Regidx Rra
                        = add_vec_int (mword_of_int (KernelSyms.ialloc + 0x54) : mword 64) 4)
          by (rewrite /GB; apply upd_eq).
        assert (HGBthr : ia_thr8 m GB).
        { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
          rewrite /GB upd_ne; [| regne]. exact (HGAthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
        iDestruct (cpu_own_transport CID6 CID14 0 true (proc_addr j) b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (wp_next_shift (b := true) (CIDa := CID5) (CIDb := CID14) ltac:(wp_next_chain)
                     with "Hcont") as "Hcont".
        assert (HKbl : (K_brelse <= K - 8)%nat) by (lia).
        iAssert (bio_locked bn (fs_view γfs γd dev cov) kk pidv dev bno
                   (diblk_bytes ds) bsd0 d0) with "[Hheld]" as "Hlk";
          [rewrite /bio_locked; iExact "Hheld" |].
        iApply (BL.wp_brelse_sconf γs bn (fs_view γfs γd dev cov) kk
                  pidv dev bno dq GB (K - 8)%nat true (proc_addr j)
                  (diblk_bytes ds) bsd0 d0 b lks HKbl Hkk HGBa0
                  (* brelse's bound is "bcache"(4); ia_scan's own is
                     "itable"(2), and [locks_below_mono] weakens it. *)
                  ltac:(lkbelow)
                  with "Hcg Hcnt Htext Hpc Hbio Hppid Hprocs Hlk").
        all: try lkbelow.
        iIntros (CID15 Hq15 mR) "%Hcsr Hcg Hcnt Hpc Hppid Hsl1".
        assert (Hpc58 : ret_pc (GB !!! Regidx Rra : mword 64)
                        = mword_of_int (KernelSyms.ialloc + 0x58)) by (rewrite HGBra; pcw).
        iEval (rewrite Hpc58) in "Hpc".
        iDestruct (iu_slots_join bn 1 1 with "Hsl Hsl1") as "Hsl".
        pose proof Hcsr as Hcsr_cs.
        assert (HmRs2 : mR !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
          by (rewrite (callee_saved_lookup Hcsr_cs Rs2 ltac:(vm_compute; reflexivity));
              exact HGBs2).
        assert (HmRs4 : mR !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
          by (rewrite (callee_saved_lookup Hcsr_cs Rs4 ltac:(vm_compute; reflexivity));
              exact HGBs4).
        assert (HmRs5 : mR !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
          by (rewrite (callee_saved_lookup Hcsr_cs Rs5 ltac:(vm_compute; reflexivity));
              exact HGBs5).
        assert (HmRs6 : mR !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64))
          by (rewrite (callee_saved_lookup Hcsr_cs Rs6 ltac:(vm_compute; reflexivity));
              exact HGBs6).
        assert (HmRsp : ia_sp m mR).
        { rewrite /ia_sp
            (callee_saved_lookup Hcsr_cs csp_rs1 ltac:(vm_compute; reflexivity)).
          exact HGBsp. }
        assert (HmRthr : ia_thr8 m mR).
        { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
          rewrite (callee_saved_lookup Hcsr_cs c Hcs).
          exact (HGBthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
        (* the NEXT inum, as the 32-bit word the code carries *)
        set (inum1 := (mword_of_int (bv_unsigned inum + 1) : mword 32)).
        assert (Hinum1u : bv_unsigned inum1 = bv_unsigned inum + 1).
        { rewrite /inum1 moi32_unsigned. apply bvw32_small.
          change (2^32)%Z with 4294967296%Z. lia. }
        assert (Hsext1 : (sign_extend' 64 inum1 : mword 64)
                         = mword_of_int (bv_unsigned inum + 1)).
        { rewrite (ia_sext_small inum1 ltac:(rewrite Hinum1u; lia)) Hinum1u.
          reflexivity. }
        (* ===== +0x58 c.addi s2,1 ===== *)
        iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.ialloc + 0x58)) Rs2
                  (mword_of_int 1 : mword 6) mR (K - 8)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi58").
        iIntros (CID16 Hq16) "Hcg Hpc".
        set (GC := <[Regidx Rs2 := regval_into_reg
                      (add_vec (rget mR Rs2)
                         (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> mR).
        assert (Hone : (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))
                        : mword 64) = mword_of_int 1)
          by (apply bv_eq; vm_compute; reflexivity).
        assert (HGCs2 : GC !!! Regidx Rs2 = (sign_extend' 64 inum1 : mword 64)).
        { rewrite /GC upd_eq. rgne.
          rewrite HmRs2 Hsext1 (ia_sext_small inum Hinum31) Hone.
          apply bv_eq. rewrite !add_vec64_unsigned !moi64_unsigned.
          rewrite (bvw64_small (bv_unsigned inum)
                     ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
          rewrite (bvw64_small 1
                     ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
          reflexivity. }
        assert (HGCs4 : GC !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
          by (rewrite /GC upd_ne; [exact HmRs4 | nz]).
        assert (HGCs5 : GC !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
          by (rewrite /GC upd_ne; [exact HmRs5 | nz]).
        assert (HGCs6 : GC !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64))
          by (rewrite /GC upd_ne; [exact HmRs6 | nz]).
        assert (HGCsp : ia_sp m GC)
          by (rewrite /ia_sp /GC upd_ne; [exact HmRsp | nz]).
        assert (HGCthr : ia_thr8 m GC).
        { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
          rewrite /GC upd_ne; [| regne]. exact (HmRthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
        assert (Hpp5a : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x58) : mword 64) 2
                        = mword_of_int (KernelSyms.ialloc + 0x5a)) by pcw.
        iEval (rewrite Hpp5a) in "Hpc".
        (* ===== +0x5a lw a4,12(s4) : a4 := sb.ninodes ===== *)
        assert (Hsbnadr : add_vec (rget GC Rs4)
                            (sign_extend' 64 (mword_of_int 12 : mword 12))
                          = sb_ninodes).
        { rgne. rewrite HGCs4. rewrite /sb_ninodes /pa_add /add_vec_int. pcw. }
        iEval (rewrite -Hsbnadr) in "Hsbn".
        iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.ialloc + 0x5a)) Ra4 Rs4
                  (mword_of_int 12 : mword 12) GC (K - 8)%nat
                  (mword_of_int ninodes : mword 32) b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi5a Hsbn").
        iIntros (CID17 Hq17) "Hcg Hpc Hsbn".
        iEval (rewrite Hsbnadr) in "Hsbn".
        set (GD := <[Regidx Ra4 := regval_into_reg
                      (sign_extend' 64 (mword_of_int ninodes : mword 32))]> GC).
        assert (HGDa4 : GD !!! Regidx Ra4 = (mword_of_int ninodes : mword 64)).
        { rewrite /GD upd_eq. apply sext32_64_small.
          change (2^31)%Z with 2147483648%Z. lia. }
        assert (HGDs2 : GD !!! Regidx Rs2 = (sign_extend' 64 inum1 : mword 64))
          by (rewrite /GD upd_ne; [exact HGCs2 | nz]).
        assert (HGDs4 : GD !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
          by (rewrite /GD upd_ne; [exact HGCs4 | nz]).
        assert (HGDs5 : GD !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
          by (rewrite /GD upd_ne; [exact HGCs5 | nz]).
        assert (HGDs6 : GD !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64))
          by (rewrite /GD upd_ne; [exact HGCs6 | nz]).
        assert (HGDsp : ia_sp m GD)
          by (rewrite /ia_sp /GD upd_ne; [exact HGCsp | nz]).
        assert (HGDthr : ia_thr8 m GD).
        { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
          rewrite /GD upd_ne; [| regne]. exact (HGCthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
        assert (Hpp5e : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x5a) : mword 64) 4
                        = mword_of_int (KernelSyms.ialloc + 0x5e)) by pcw.
        iEval (rewrite Hpp5e) in "Hpc".
        (* ===== +0x5e addiw a5,s2,0 ===== *)
        iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.ialloc + 0x5e)) Ra5 Rs2
                  (mword_of_int 0 : mword 12) GD (K - 8)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi5e").
        iIntros (CID18 Hq18) "Hcg Hpc".
        set (GE := <[Regidx Ra5 := regval_into_reg
                      (sign_extend' 64
                         (subrange_vec_dec
                            (add_vec (rget GD Rs2)
                               (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0))]> GD).
        assert (HGEa5 : GE !!! Regidx Ra5
                        = (mword_of_int (bv_unsigned inum + 1) : mword 64)).
        { rewrite /GE upd_eq. rgne. rewrite HGDs2 iu_off0.
          rewrite (iu_sub31_sext inum1). exact Hsext1. }
        assert (HGEa4 : GE !!! Regidx Ra4 = (mword_of_int ninodes : mword 64))
          by (rewrite /GE upd_ne; [exact HGDa4 | nz]).
        assert (HGEs2 : GE !!! Regidx Rs2 = (sign_extend' 64 inum1 : mword 64))
          by (rewrite /GE upd_ne; [exact HGDs2 | nz]).
        assert (HGEs4 : GE !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
          by (rewrite /GE upd_ne; [exact HGDs4 | nz]).
        assert (HGEs5 : GE !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
          by (rewrite /GE upd_ne; [exact HGDs5 | nz]).
        assert (HGEs6 : GE !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64))
          by (rewrite /GE upd_ne; [exact HGDs6 | nz]).
        assert (HGEsp : ia_sp m GE)
          by (rewrite /ia_sp /GE upd_ne; [exact HGDsp | nz]).
        assert (HGEthr : ia_thr8 m GE).
        { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
          rewrite /GE upd_ne; [| regne]. exact (HGDthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
        (* ===== +0x62 bltu a5,a4 : another inum to try? ===== *)
        destruct (Z.ltb (bv_unsigned inum + 1) ninodes) eqn:Hlt.
        * (* still in range: back to +0x30 with the fuel one lower *)
          assert (Hcmp2 : zopz0zI_u (rget GE Ra5) (rget GE Ra4) = true).
          { rgne. rgne. rewrite HGEa5 HGEa4.
            rewrite (ia_bltu_moi (bv_unsigned inum + 1) ninodes
                       ltac:(change (2^31)%Z with 2147483648%Z in Hn31; lia)
                       ltac:(change (2^31)%Z with 2147483648%Z in Hn31; lia)).
            exact Hlt. }
          iApply (wp_bltu_taken_s_sconf (mword_of_int (KernelSyms.ialloc + 0x62))
                    (mword_of_int 8142 : mword 13) Ra4 Ra5 GE (K - 8)%nat b
                    ltac:(nz) ltac:(nz) Hcmp2 ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi62").
          iApply bi.later_intro. iIntros (CID19 Hq19) "Hcg Hpc".
          assert (Hjt : add_vec (mword_of_int (KernelSyms.ialloc + 0x62) : mword 64)
                          (sign_extend' 64 (mword_of_int 8142 : mword 13))
                        = mword_of_int (KernelSyms.ialloc + 0x30)) by pcw.
          iEval (rewrite Hjt) in "Hpc".
          iDestruct (cpu_own_transport CID15 CID19 0 true (proc_addr j) b
                       ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          iDestruct (wp_next_shift (b := true) (CIDa := CID14) (CIDb := CID19)
                       ltac:(wp_next_chain) with "Hcont") as "Hcont".
          (* THE RE-ENTRY.  The loop wand's own [CIDl] binder is unused by its
             body -- every resource inside is anchored at the [CIDc] the
             caller picks -- so the induction hypothesis is instantiated at
             [CIDl] itself, where the guard is exactly [Hql], and the turn's
             anchor is handed over as [CIDc := CID19]. *)
          iPoseProof ("IH" $! CIDl with "[%]") as "IHx"; [exact Hql |].
          iApply ("IHx" $! GE inum1 CID19
                    with "[%] [%] [%] [%] [%] [%] [%] [%] Hcg Hcnt Hpc Hframe
                          Hppid Hsbn Hsbi Hsl Hiref Hop Hcont").
          { rewrite Hinum1u. apply Z.ltb_lt in Hlt. lia. }
          { rewrite Hinum1u. apply Z.ltb_lt in Hlt. lia. }
          { exact HGEsp. }
          { exact HGEthr. }
          { exact HGEs2. }
          { exact HGEs4. }
          { exact HGEs5. }
          { exact HGEs6. }
        * (* out of range: fall through to the printk arm at +0x66 *)
          assert (Hcmp2 : zopz0zI_u (rget GE Ra5) (rget GE Ra4) = false).
          { rgne. rgne. rewrite HGEa5 HGEa4.
            rewrite (ia_bltu_moi (bv_unsigned inum + 1) ninodes
                       ltac:(change (2^31)%Z with 2147483648%Z in Hn31; lia)
                       ltac:(change (2^31)%Z with 2147483648%Z in Hn31; lia)).
            exact Hlt. }
          iApply (wp_bltu_fall_s_sconf (mword_of_int (KernelSyms.ialloc + 0x62))
                    (mword_of_int 8142 : mword 13) Ra4 Ra5 GE (K - 8)%nat b
                    ltac:(nz) ltac:(nz) Hcmp2 with "Hcg Hpc Hi62").
          iIntros (CID19 Hq19) "Hcg Hpc".
          assert (Hpp66 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x62) : mword 64) 4
                          = mword_of_int (KernelSyms.ialloc + 0x66)) by pcw.
          iEval (rewrite Hpp66) in "Hpc".
          iDestruct (cpu_own_transport CID15 CID19 0 true (proc_addr j) b
                       ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          iApply (ia_out (CID0 := CID19) j bn γ γpr γu γd inodestart ninodes nib
                    dev ty u Sb pidv dq dqs dqn m GE K b lks
                    HK Hty Hpk HGEsp HGEthr
                    with "Hcg Hcnt Htext Hkdata Hpc Hpenv Hframe Hppid
                          Hsbn Hsbi Hsl Hiref Hop [Hcont]").
          { iApply (wp_next_shift (b := true) (CIDa := CID14) (CIDb := CID19)
                      ltac:(wp_next_chain) with "Hcont"). }
  Qed.

End IallocScan.

(* ===================================================================== *)
(*  +0x00 .. +0x2e : THE PROLOGUE, and the contract.                      *)
(* ===================================================================== *)
Section IallocMain.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.

  Lemma wp_ialloc_gen `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname)
      (γpr : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (ninodes : Z) (nib : nat)
      (dev : mword 32) (ty : mword 16)
      (u : nat) (Sb : gset Z)
      (pidv : mword 32) (dq dqs dqn : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) :
      wp_ialloc_gen_body γs j γl γu γd γk pd pav pu bn γ γfs γi cn gtl γpr
                         cov logstart inodestart ninodes nib dev ty u Sb
                         pidv dq dqs dqn m K eb b lks.
  Proof.
    cbv beta delta [wp_ialloc_gen_body].
    intros pcE pj ret_tgt HK Hgeom Hst Hblk Hn1 Hnnib Hn31 Hty Hpk Hj Hgl
           Ha0 Ha1 Heb Hbelow.
    subst eb.
    pose proof HK as HK'. 
    assert (Hnsext : (sign_extend' 64 (mword_of_int ninodes : mword 32) : mword 64)
                     = mword_of_int ninodes)
      by (apply sext32_64_small; change (2^31)%Z with 2147483648%Z; lia).
    assert (Hone32 : (sign_extend' 64 (mword_of_int 1 : mword 32) : mword 64)
                     = mword_of_int 1) by pcw.
    (* THE +0x12 REFUTATION, as a pure fact, before a single instruction *)
    assert (Hgene : zopz0zKzJ_u (mword_of_int 1 : mword 64)
                      (mword_of_int ninodes : mword 64) = false).
    { rewrite (ia_bgeu_moi 1 ninodes
                 ltac:(lia)
                 ltac:(change (2^31)%Z with 2147483648%Z in Hn31; lia)).
      apply not_true_is_false. intro Hc. apply Z.geb_le in Hc. lia. }
    iIntros "Hcg Hcnt #Htext Hpc #Hkdata #Hpenv #Hbio #Hlctx
              Hsbn Hsbi #Hireg Hppid #Hprocs #Hdevi #Hdgeom #Hdlock Hsl
              #Hitb2 #Hitbl #Hesc Hiref Hop Hcont".
    iAssert (ia_cont (CID0 := CID) γ bn inodestart ninodes nib dev ty u Sb
               pidv dq dqs dqn j m K b lks)%I with "[Hcont]" as "Hcont";
      [rewrite /ia_cont; iExact "Hcont" |].
    iPoseProof (iali_00 with "Htext") as "Hi00".
    iPoseProof (iali_02 with "Htext") as "Hi02".
    iPoseProof (iali_04 with "Htext") as "Hi04".
    iPoseProof (iali_06 with "Htext") as "Hi06".
    iPoseProof (iali_08 with "Htext") as "Hi08".
    iPoseProof (iali_0c with "Htext") as "Hi0c".
    iPoseProof (iali_10 with "Htext") as "Hi10".
    iPoseProof (iali_12 with "Htext") as "Hi12".
    iPoseProof (iali_16 with "Htext") as "Hi16".
    iPoseProof (iali_18 with "Htext") as "Hi18".
    iPoseProof (iali_1a with "Htext") as "Hi1a".
    iPoseProof (iali_1c with "Htext") as "Hi1c".
    iPoseProof (iali_1e with "Htext") as "Hi1e".
    iPoseProof (iali_20 with "Htext") as "Hi20".
    iPoseProof (iali_22 with "Htext") as "Hi22".
    iPoseProof (iali_24 with "Htext") as "Hi24".
    iPoseProof (iali_26 with "Htext") as "Hi26".
    iPoseProof (iali_28 with "Htext") as "Hi28".
    iPoseProof (iali_2c with "Htext") as "Hi2c".
    (* ===== +0x00 c.addi16sp sp,-64 : the 8-slot frame ===== *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 8).
    { unfold pa_stk, add_vec_int. apply f_equal. pcw. }
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 60 : mword 6) m K 8 b
              ltac:(lia) Hpush with "Hcg Hpc Hi00").
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))]> m).
    assert (HR1sp : ia_sp m R1) by (rewrite /ia_sp /R1 upd_eq; reflexivity).
    assert (HR1thr : ia_thr8 m R1).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /R1 upd_ne; [reflexivity | regne]. }
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & _)".
    iDestruct "T1" as (v1) "Hf1".   iDestruct "T2" as (v2) "Hf2".
    iDestruct "T3" as (v3) "Hf3".   iDestruct "T4" as (v4) "Hf4".
    iDestruct "T5" as (v5) "Hf5".   iDestruct "T6" as (v6) "Hf6".
    iDestruct "T7" as (v7) "Hf7".   iDestruct "T8" as (v8) "Hf8".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hb1) in "Hf1". iEval (rewrite -Hb2) in "Hf2".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x2)) by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    (* ===== +0x02 / +0x04 : ra and s0 ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.ialloc + 0x2))
              (mword_of_int 7 : mword 6) Rra
              R1 (K - 8)%nat v1 b with "Hcg Hpc Hi02 Hf1").
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x2) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x4)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.ialloc + 0x4))
              (mword_of_int 6 : mword 6) Rs0
              R1 (K - 8)%nat v2 b with "Hcg Hpc Hi04 Hf2").
    iIntros (CID3 Hq3) "Hcg Hpc Hf2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x4) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x6)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    assert (HR1ra : (R1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s0 : (R1 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    iEval (rewrite Hb1; rgne; rewrite HR1ra) in "Hf1".
    iEval (rewrite Hb2; rgne; rewrite HR1s0) in "Hf2".
    (* ===== +0x06 c.addi4spn s0,sp,64 ===== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.ialloc + 0x6))
              (Cregidx (mword_of_int 0))
              (mword_of_int 16 : mword 8) Rs0 R1 (K - 8)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi06").
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))))]> R1).
    assert (HR2sp : ia_sp m R2)
      by (rewrite /ia_sp /R2 upd_ne; [exact HR1sp | nz]).
    assert (HR2thr : ia_thr8 m R2).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /R2 upd_ne; [| regne]. exact (HR1thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x6) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x8)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    (* ===== +0x08 auipc a4,0x1e ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.ialloc + 0x8)) Ra4
              (mword_of_int 30 : mword 20) R2 (K - 8)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi08").
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (R3 := <[Regidx Ra4 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.ialloc + 0x8) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> R2).
    assert (HR3a4 : R3 !!! Regidx Ra4
                    = add_vec (mword_of_int (KernelSyms.ialloc + 0x8) : mword 64)
                        (auipc_off (mword_of_int 30 : mword 20)))
      by (rewrite /R3; apply upd_eq).
    assert (HR3sp : ia_sp m R3)
      by (rewrite /ia_sp /R3 upd_ne; [exact HR2sp | nz]).
    assert (HR3thr : ia_thr8 m R3).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /R3 upd_ne; [| regne]. exact (HR2thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x8) : mword 64) 4
                    = mword_of_int (KernelSyms.ialloc + 0xc)) by pcw.
    iEval (rewrite Hpp0c) in "Hpc".
    (* ===== +0x0c lw a4,2108(a4) : a4 := sb.ninodes ===== *)
    assert (Hnadr : add_vec (rget R3 Ra4)
                      (sign_extend' 64 (mword_of_int 2126 : mword 12))
                    = sb_ninodes).
    { rgne. rewrite HR3a4. rewrite /sb_ninodes /pa_add /add_vec_int. pcw. }
    iEval (rewrite -Hnadr) in "Hsbn".
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.ialloc + 0xc)) Ra4 Ra4
              (mword_of_int 2126 : mword 12) R3 (K - 8)%nat
              (mword_of_int ninodes : mword 32) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0c Hsbn").
    iIntros (CID6 Hq6) "Hcg Hpc Hsbn".
    iEval (rewrite Hnadr) in "Hsbn".
    set (R4 := <[Regidx Ra4 := regval_into_reg
                  (sign_extend' 64 (mword_of_int ninodes : mword 32))]> R3).
    assert (HR4a4 : R4 !!! Regidx Ra4 = (mword_of_int ninodes : mword 64))
      by (rewrite /R4 upd_eq; exact Hnsext).
    assert (HR4a0 : R4 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64)).
    { rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz].
      rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [exact Ha0 | nz]. }
    assert (HR4a1 : R4 !!! Regidx Ra1 = (sign_extend' 64 ty : mword 64)).
    { rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz].
      rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [exact Ha1 | nz]. }
    assert (HR4sp : ia_sp m R4)
      by (rewrite /ia_sp /R4 upd_ne; [exact HR3sp | nz]).
    assert (HR4thr : ia_thr8 m R4).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /R4 upd_ne; [| regne]. exact (HR3thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0xc) : mword 64) 4
                    = mword_of_int (KernelSyms.ialloc + 0x10)) by pcw.
    iEval (rewrite Hpp10) in "Hpc".
    (* ===== +0x10 c.li a5,1 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.ialloc + 0x10)) Ra5
              (mword_of_int 1 : mword 6)
              (sign_extend' 64 (mword_of_int 1 : mword 32) : mword 64)
              R4 (K - 8)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi10").
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (R5 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (mword_of_int 1 : mword 32) : mword 64)]> R4).
    assert (HR5a5 : R5 !!! Regidx Ra5
                    = (sign_extend' 64 (mword_of_int 1 : mword 32) : mword 64))
      by (rewrite /R5; apply upd_eq).
    assert (HR5a4 : R5 !!! Regidx Ra4 = (mword_of_int ninodes : mword 64))
      by (rewrite /R5 upd_ne; [exact HR4a4 | nz]).
    assert (HR5a0 : R5 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R5 upd_ne; [exact HR4a0 | nz]).
    assert (HR5a1 : R5 !!! Regidx Ra1 = (sign_extend' 64 ty : mword 64))
      by (rewrite /R5 upd_ne; [exact HR4a1 | nz]).
    assert (HR5sp : ia_sp m R5)
      by (rewrite /ia_sp /R5 upd_ne; [exact HR4sp | nz]).
    assert (HR5thr : ia_thr8 m R5).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /R5 upd_ne; [| regne]. exact (HR4thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x10) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x12)) by pcw.
    iEval (rewrite Hpp12) in "Hpc".
    (* ===== +0x12 bgeu a5,a4 : THE DEAD ARM.  [1 < ninodes] refutes it --
       it would reach the printk WITHOUT having pushed s1..s6. ===== *)
    iApply (wp_bgeu_fall_s_sconf (mword_of_int (KernelSyms.ialloc + 0x12))
              (mword_of_int 96 : mword 13) Ra4 Ra5 R5 (K - 8)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HR5a5 HR5a4 Hone32; exact Hgene)
              with "Hcg Hpc Hi12").
    iIntros (CID8 Hq8) "Hcg Hpc".
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x12) : mword 64) 4
                    = mword_of_int (KernelSyms.ialloc + 0x16)) by pcw.
    iEval (rewrite Hpp16) in "Hpc".
    (* ===== +0x16 .. +0x20 : s1 .. s6 ===== *)
    assert (Hb3 : add_vec (R5 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HR5sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb4 : add_vec (R5 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite HR5sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb5 : add_vec (R5 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 5).
    { rewrite HR5sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb6 : add_vec (R5 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
    { rewrite HR5sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb7 : add_vec (R5 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 7).
    { rewrite HR5sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb8 : add_vec (R5 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 8).
    { rewrite HR5sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hb3) in "Hf3".   iEval (rewrite -Hb4) in "Hf4".
    iEval (rewrite -Hb5) in "Hf5".   iEval (rewrite -Hb6) in "Hf6".
    iEval (rewrite -Hb7) in "Hf7".   iEval (rewrite -Hb8) in "Hf8".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.ialloc + 0x16))
              (mword_of_int 5 : mword 6) Rs1
              R5 (K - 8)%nat v3 b with "Hcg Hpc Hi16 Hf3").
    iIntros (CID9 Hq9) "Hcg Hpc Hf3".
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x16) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x18)) by pcw.
    iEval (rewrite Hpp18) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.ialloc + 0x18))
              (mword_of_int 4 : mword 6) Rs2
              R5 (K - 8)%nat v4 b with "Hcg Hpc Hi18 Hf4").
    iIntros (CID10 Hq10) "Hcg Hpc Hf4".
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x18) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x1a)) by pcw.
    iEval (rewrite Hpp1a) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.ialloc + 0x1a))
              (mword_of_int 3 : mword 6) Rs3
              R5 (K - 8)%nat v5 b with "Hcg Hpc Hi1a Hf5").
    iIntros (CID11 Hq11) "Hcg Hpc Hf5".
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x1a) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x1c)) by pcw.
    iEval (rewrite Hpp1c) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.ialloc + 0x1c))
              (mword_of_int 2 : mword 6) Rs4
              R5 (K - 8)%nat v6 b with "Hcg Hpc Hi1c Hf6").
    iIntros (CID12 Hq12) "Hcg Hpc Hf6".
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x1c) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x1e)) by pcw.
    iEval (rewrite Hpp1e) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.ialloc + 0x1e))
              (mword_of_int 1 : mword 6) Rs5
              R5 (K - 8)%nat v7 b with "Hcg Hpc Hi1e Hf7").
    iIntros (CID13 Hq13) "Hcg Hpc Hf7".
    assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x1e) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x20)) by pcw.
    iEval (rewrite Hpp20) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.ialloc + 0x20))
              (mword_of_int 0 : mword 6) Rs6
              R5 (K - 8)%nat v8 b with "Hcg Hpc Hi20 Hf8").
    iIntros (CID14 Hq14) "Hcg Hpc Hf8".
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x20) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x22)) by pcw.
    iEval (rewrite Hpp22) in "Hpc".
    (* the six saved values, named -- the frame is now [ia_frame m] *)
    assert (HR5s1 : (R5 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64)).
    { rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
      rewrite /R3 upd_ne; [| nz]. rewrite /R2 upd_ne; [| nz].
      rewrite /R1 upd_ne; [reflexivity | nz]. }
    assert (HR5s2 : (R5 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
      rewrite /R3 upd_ne; [| nz]. rewrite /R2 upd_ne; [| nz].
      rewrite /R1 upd_ne; [reflexivity | nz]. }
    assert (HR5s3 : (R5 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
      rewrite /R3 upd_ne; [| nz]. rewrite /R2 upd_ne; [| nz].
      rewrite /R1 upd_ne; [reflexivity | nz]. }
    assert (HR5s4 : (R5 !!! Regidx Rs4 : mword 64) = (m !!! Regidx Rs4 : mword 64)).
    { rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
      rewrite /R3 upd_ne; [| nz]. rewrite /R2 upd_ne; [| nz].
      rewrite /R1 upd_ne; [reflexivity | nz]. }
    assert (HR5s5 : (R5 !!! Regidx Rs5 : mword 64) = (m !!! Regidx Rs5 : mword 64)).
    { rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
      rewrite /R3 upd_ne; [| nz]. rewrite /R2 upd_ne; [| nz].
      rewrite /R1 upd_ne; [reflexivity | nz]. }
    assert (HR5s6 : (R5 !!! Regidx Rs6 : mword 64) = (m !!! Regidx Rs6 : mword 64)).
    { rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
      rewrite /R3 upd_ne; [| nz]. rewrite /R2 upd_ne; [| nz].
      rewrite /R1 upd_ne; [reflexivity | nz]. }
    iEval (rewrite Hb3; rgne; rewrite HR5s1) in "Hf3".
    iEval (rewrite Hb4; rgne; rewrite HR5s2) in "Hf4".
    iEval (rewrite Hb5; rgne; rewrite HR5s3) in "Hf5".
    iEval (rewrite Hb6; rgne; rewrite HR5s4) in "Hf6".
    iEval (rewrite Hb7; rgne; rewrite HR5s5) in "Hf7".
    iEval (rewrite Hb8; rgne; rewrite HR5s6) in "Hf8".
    iAssert (ia_frame m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8]" as "Hframe".
    { rewrite /ia_frame.
      iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
      iSplitL "Hf3"; [iExact "Hf3"|]. iSplitL "Hf4"; [iExact "Hf4"|].
      iSplitL "Hf5"; [iExact "Hf5"|]. iSplitL "Hf6"; [iExact "Hf6"|].
      iSplitL "Hf7"; [iExact "Hf7"|]. iExact "Hf8". }
    (* ===== +0x22 c.mv s5,a0 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ialloc + 0x22)) Rs5 Ra0
              R5 (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi22").
    iIntros (CID15 Hq15) "Hcg Hpc".
    set (R6 := <[Regidx Rs5 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget R5 Ra0))]> R5).
    assert (HR6s5 : R6 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64)).
    { rewrite /R6 upd_eq. rgne. rewrite HR5a0. apply add_vec_zero_l. }
    assert (HR6a1 : R6 !!! Regidx Ra1 = (sign_extend' 64 ty : mword 64))
      by (rewrite /R6 upd_ne; [exact HR5a1 | nz]).
    assert (HR6a5 : R6 !!! Regidx Ra5
                    = (sign_extend' 64 (mword_of_int 1 : mword 32) : mword 64))
      by (rewrite /R6 upd_ne; [exact HR5a5 | nz]).
    assert (HR6sp : ia_sp m R6)
      by (rewrite /ia_sp /R6 upd_ne; [exact HR5sp | nz]).
    assert (HR6thr : ia_thr8 m R6).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /R6 upd_ne; [| regne]. exact (HR5thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x22) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x24)) by pcw.
    iEval (rewrite Hpp24) in "Hpc".
    (* ===== +0x24 c.mv s6,a1 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ialloc + 0x24)) Rs6 Ra1
              R6 (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi24").
    iIntros (CID16 Hq16) "Hcg Hpc".
    set (R7 := <[Regidx Rs6 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget R6 Ra1))]> R6).
    assert (HR7s6 : R7 !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64)).
    { rewrite /R7 upd_eq. rgne. rewrite HR6a1. apply add_vec_zero_l. }
    assert (HR7s5 : R7 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R7 upd_ne; [exact HR6s5 | nz]).
    assert (HR7a5 : R7 !!! Regidx Ra5
                    = (sign_extend' 64 (mword_of_int 1 : mword 32) : mword 64))
      by (rewrite /R7 upd_ne; [exact HR6a5 | nz]).
    assert (HR7sp : ia_sp m R7)
      by (rewrite /ia_sp /R7 upd_ne; [exact HR6sp | nz]).
    assert (HR7thr : ia_thr8 m R7).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /R7 upd_ne; [| regne]. exact (HR6thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x24) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x26)) by pcw.
    iEval (rewrite Hpp26) in "Hpc".
    (* ===== +0x26 c.mv s2,a5 : inum := 1 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ialloc + 0x26)) Rs2 Ra5
              R7 (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi26").
    iIntros (CID17 Hq17) "Hcg Hpc".
    set (R8 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget R7 Ra5))]> R7).
    assert (HR8s2 : R8 !!! Regidx Rs2
                    = (sign_extend' 64 (mword_of_int 1 : mword 32) : mword 64)).
    { rewrite /R8 upd_eq. rgne. rewrite HR7a5. apply add_vec_zero_l. }
    assert (HR8s5 : R8 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R8 upd_ne; [exact HR7s5 | nz]).
    assert (HR8s6 : R8 !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64))
      by (rewrite /R8 upd_ne; [exact HR7s6 | nz]).
    assert (HR8sp : ia_sp m R8)
      by (rewrite /ia_sp /R8 upd_ne; [exact HR7sp | nz]).
    assert (HR8thr : ia_thr8 m R8).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /R8 upd_ne; [| regne]. exact (HR7thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x26) : mword 64) 2
                    = mword_of_int (KernelSyms.ialloc + 0x28)) by pcw.
    iEval (rewrite Hpp28) in "Hpc".
    (* ===== +0x28 auipc s4,0x1e ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.ialloc + 0x28)) Rs4
              (mword_of_int 30 : mword 20) R8 (K - 8)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi28").
    iIntros (CID18 Hq18) "Hcg Hpc".
    set (R9 := <[Regidx Rs4 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.ialloc + 0x28) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> R8).
    assert (HR9s4 : R9 !!! Regidx Rs4
                    = add_vec (mword_of_int (KernelSyms.ialloc + 0x28) : mword 64)
                        (auipc_off (mword_of_int 30 : mword 20)))
      by (rewrite /R9; apply upd_eq).
    assert (HR9s2 : R9 !!! Regidx Rs2
                    = (sign_extend' 64 (mword_of_int 1 : mword 32) : mword 64))
      by (rewrite /R9 upd_ne; [exact HR8s2 | nz]).
    assert (HR9s5 : R9 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R9 upd_ne; [exact HR8s5 | nz]).
    assert (HR9s6 : R9 !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64))
      by (rewrite /R9 upd_ne; [exact HR8s6 | nz]).
    assert (HR9sp : ia_sp m R9)
      by (rewrite /ia_sp /R9 upd_ne; [exact HR8sp | nz]).
    assert (HR9thr : ia_thr8 m R9).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /R9 upd_ne; [| regne]. exact (HR8thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x28) : mword 64) 4
                    = mword_of_int (KernelSyms.ialloc + 0x2c)) by pcw.
    iEval (rewrite Hpp2c) in "Hpc".
    (* ===== +0x2c addi s4,s4,2064 : s4 := &sb ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.ialloc + 0x2c)) Rs4 Rs4
              (mword_of_int 2082 : mword 12) R9 (K - 8)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2c").
    iIntros (CID19 Hq19) "Hcg Hpc".
    set (RA := <[Regidx Rs4 := regval_into_reg
                  (add_vec (rget R9 Rs4)
                     (sign_extend' 64 (mword_of_int 2082 : mword 12)))]> R9).
    assert (HRAs4 : RA !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64)).
    { rewrite /RA upd_eq. rgne. rewrite HR9s4. pcw. }
    assert (HRAs2 : RA !!! Regidx Rs2
                    = (sign_extend' 64 (mword_of_int 1 : mword 32) : mword 64))
      by (rewrite /RA upd_ne; [exact HR9s2 | nz]).
    assert (HRAs5 : RA !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /RA upd_ne; [exact HR9s5 | nz]).
    assert (HRAs6 : RA !!! Regidx Rs6 = (sign_extend' 64 ty : mword 64))
      by (rewrite /RA upd_ne; [exact HR9s6 | nz]).
    assert (HRAsp : ia_sp m RA)
      by (rewrite /ia_sp /RA upd_ne; [exact HR9sp | nz]).
    assert (HRAthr : ia_thr8 m RA).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /RA upd_ne; [| regne]. exact (HR9thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.ialloc + 0x2c) : mword 64) 4
                    = mword_of_int (KernelSyms.ialloc + 0x30)) by pcw.
    iEval (rewrite Hpp30) in "Hpc".
    (* ===== +0x30 : THE SCAN, entered at inum = 1 ===== *)
    iDestruct (cpu_own_transport CID CID19 0 true (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID) (CIDb := CID19) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (Hunit1 : bv_unsigned (mword_of_int 1 : mword 32) = 1).
    { rewrite moi32_unsigned. apply bvw32_small.
      change (2^32)%Z with 4294967296%Z. lia. }
    iPoseProof (ia_scan (CIDe := CID19) γs j γl γu γd γk pd pav pu bn γ γfs γi
                  cn gtl γpr cov logstart inodestart ninodes nib dev ty u Sb
                  pidv dq dqs dqn m K b lks
                  HK Hgeom Hst Hblk Hn1 Hnnib Hn31 Hty Hpk Hj Hgl Hbelow
                  with "Htext Hkdata Hpenv Hbio Hlctx Hireg Hprocs
                        Hdevi Hdgeom Hdlock Hitb2 Hitbl Hesc") as "Hscan".
    iSpecialize ("Hscan" $! (Z.to_nat (ninodes - 1))).
    iPoseProof ("Hscan" $! CID19 with "[%]") as "Hscan1";
      [intros _; reflexivity |].
    iApply ("Hscan1" $! RA (mword_of_int 1 : mword 32) CID19
              with "[%] [%] [%] [%] [%] [%] [%] [%] Hcg Hcnt Hpc Hframe Hppid
                    Hsbn Hsbi Hsl Hiref Hop Hcont").
    { rewrite Hunit1. lia. }
    { rewrite Hunit1. lia. }
    { exact HRAsp. }
    { exact HRAthr. }
    { exact HRAs2. }
    { exact HRAs4. }
    { exact HRAs5. }
    { exact HRAs6. }
  Qed.

  (* ---- THE SET-FORGETTING INSTANCE (fs-sysfile S5i) ------------------
     [log_op] IS [∃ Sb, log_opS], so the derivation is: destruct the
     caller's reservation, run the credited proof at that [Sb], and re-pack
     each arm's payout with [LogInv.log_opS_op].  Every landed consumer of
     ialloc (there is exactly one shape, and [LinkIalloc] is unmoved) sees
     the same statement it saw before.                                     *)
  Lemma wp_ialloc_sconf `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname)
      (γpr : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (ninodes : Z) (nib : nat)
      (dev : mword 32) (ty : mword 16)
      (u : nat)
      (pidv : mword 32) (dq dqs dqn : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) :
      wp_ialloc_sconf_body γs j γl γu γd γk pd pav pu bn γ γfs γi cn gtl γpr
                           cov logstart inodestart ninodes nib dev ty u
                           pidv dq dqs dqn m K eb b lks.
  Proof.
    cbv beta delta [wp_ialloc_sconf_body].
    intros pcE pj ret_tgt HK Hgeom Hst Hblk Hn1 Hnnib Hn31 Hty Hpk Hj Hgl
           Ha0 Ha1 Heb Hbelow.
    iIntros "Hcg Hcnt #Htext Hpc #Hkdata #Hpenv #Hbio #Hlctx
              Hsbn Hsbi #Hireg Hppid #Hprocs #Hdevi #Hdgeom #Hdlock Hsl
              #Hitb2 #Hitbl #Hesc Hiref Hop Hcont".
    rewrite /log_op. iDestruct "Hop" as (Sb) "HopS".
    iApply (wp_ialloc_gen (CID := CID) γs j γl γu γd γk pd pav pu bn γ γfs γi
              cn gtl γpr cov logstart inodestart ninodes nib dev ty u Sb
              pidv dq dqs dqn m K eb b lks
              HK Hgeom Hst Hblk Hn1 Hnnib Hn31 Hty Hpk Hj Hgl Ha0 Ha1 Heb Hbelow
              with "Hcg Hcnt Htext Hpc Hkdata Hpenv Hbio Hlctx
                    Hsbn Hsbi Hireg Hppid Hprocs Hdevi Hdgeom Hdlock Hsl
                    Hitb2 Hitbl Hesc Hiref HopS [Hcont]").
    all: try lkbelow.
    iIntros (CID') "%Hq".
    iSpecialize ("Hcont" $! CID' with "[%]"); [exact Hq |].
    iIntros (mf alloc kslot q inum dn') "%Hcs Hcg Hcnt Hpc Hsbn Hsbi Hppid
              Hsl Harm".
    iApply ("Hcont" $! mf alloc kslot q inum dn'
              with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hppid Hsl [Harm]");
      [exact Hcs |].
    destruct alloc.
    - iDestruct "Harm" as "(%Hp & Href & HopS)".
      iSplitR; [iPureIntro; exact Hp |].
      iSplitL "Href"; [iExact "Href" |].
      iApply (log_opS_op with "HopS").
    - iDestruct "Harm" as "(%Hp & Hiref & HopS)".
      iSplitR; [iPureIntro; exact Hp |].
      iSplitL "Hiref"; [iExact "Hiref" |].
      iApply (log_opS_op with "HopS").
  Qed.

End IallocMain.

End IallocProof.
