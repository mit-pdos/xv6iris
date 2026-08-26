(* ProofIlock.v -- ilock over the SIE-agnostic sconf world.

     void ilock(struct inode *ip) {
       if (ip == 0 || ip->ref < 1) panic("ilock");
       acquiresleep(&ip->lock);
       if (ip->valid == 0) {
         bp = bread(ip->dev, IBLOCK(ip->inum, sb));
         dip = (struct dinode * )bp->data + ip->inum % IPB;
         ip->type = dip->type; ip->major = dip->major;
         ip->minor = dip->minor; ip->nlink = dip->nlink;
         ip->size = dip->size;
         memmove(ip->addrs, dip->addrs, sizeof(ip->addrs));
         brelse(bp); ip->valid = 1;
         if (ip->type == 0) panic("ilock: no type");
       }
     }

   174 bytes, 61 instructions.  Three lemmas, entered strictly right to left:

     [il_epilogue] +0x1e .. +0x26   pop ra/s0/s1, ret, discharge the contract
     [il_load]     +0x36 .. +0xa0   the UNCACHED arm: save s2, bread, the five
                                    field copies, the memmove, brelse,
                                    ip->valid = 1, the dead type panic,
                                    restore s2, [c.j] back to +0x1e
     [wp_ilock_sconf] +0x00 .. +0x1c prologue, the two dead panic tests,
                                    acquiresleep, and the ip->valid branch

   THE GUARD READ IS AN ATOMIC UPDATE.  [ip->ref] lives in [itable_inv],
   not in any caller's hands (design §4), so the [c.lw a5,8(a0)] at +0x0e
   goes through [WpAu4.wp_lw_au_s_sconf] (the width-4 masked wrapper)
   fed by [IcacheInv.iref_live_load_au] (v3: the caller holds a SHARE, so
   the read is against its liveness slice); what comes back out is the bounds
   [0 < v < 2^31] that [inode_ref_spos] turns into "[bge x0,a5] falls
   through".  The null half of the same panic needs no resource at all now
   that the entry is a SLOT: [il_entry_nonzero] is [ientry_unsigned].

   THE CHECKOUT is [IcacheEscrow.ic_swap_checkout], fired inside ONE
   opening of [ic_escrow] straight after acquiresleep returns.  It needs no
   atomic step of its own: the body goes in and comes back out in the same
   mask-balanced update, so [iApply fupd_wp; iInv] is the whole move.  Out
   of it come the escrow's two identity halves (at the winner's own dev and
   inum -- §13.1e, and the dev half is what makes the bread at +0x4a
   statable after the reference has been deposited), the FULL valid cell,
   and the payload keyed by that cell's bool.  WHAT MAKES THE BRANCH
   DECIDABLE is therefore the checkout itself rather than a shadow: the
   cell holds [InodeLock.valid_word v], [valid_word_eqz] reads the branch
   off it, and a [destruct v] settles at once which arm the [c.beqz] takes
   AND which side of [ic_payload]'s [if v] is in hand.

   THE UNCACHED ARM's coupling is the REGION, not a caller-held block:
   [BioFs.bio_held_fs_L] pulls the block's machinery half out of the bio
   handle and [InodeRegion.ireg_read] fires it against the payload's
   [dinode_at], which pins the buffer's bytes to [diblk_bytes ds] AND names
   this inum's slot ([ds !!! islot inum = dn]).  That single move replaces
   v1's [fs_chalf] premise, its [diblk_wf] premise and its conditional
   slot-agreement premise (§11.3).  From there [diblk_slot_acc] hands out
   slot [inum mod IPB] as six typed pieces and takes them back UNCHANGED
   (ilock only reads the buffer, which is why the block comes back at [ds]
   and no [log_write] is involved).  The five scalars land in
   [inode_meta]'s cells and the 52-byte window lands in the thirteen
   [i_addr] cells via [il_addrs_buf_upd] -- the write-direction twin of
   [InodeInv.inode_addrs_buf].

   ---- THE FIRST LIVE PANIC ARM IN THIS TREE ---------------------------

   The [ip == 0 || ip->ref < 1] panic is REFUTED, as always.  The SECOND
   one, [ip->type == 0] at +0x9c, IS NOT, and this is the first proof here
   that takes a panic branch on purpose.  The pool legitimately holds free
   inodes ([IcacheEscrow.ipool_shape]'s type-0 shape, §13.3), no caller
   premise could rule one out today (allocatedness is namei/ialloc's
   knowledge, future work), and §13.1 retired the shadow that used to carry
   v1's conditional agreement.  So [il_load] splits on the pool entry's
   shape at exactly that instruction: the allocated shape falls through on
   [inode_ok]'s type conjunct, and the free shape branches to +0xa2, runs
   the three-instruction [panic("ilock: no type")] call, and closes with
   [SpecPanic]'s own contract.  Nothing else in the proof case-splits on the
   shape -- the loads, the memmove and the brelse touch only the BUFFER's
   bytes and the entry's own cells, never the file's blocks. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvModelBytes.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import VcGen.
Require Import IntrDefs.
Require Import MinstretInv.
Require Import CpuOwn.
Require Import DiskPtsto DiskInv.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpAu4.
Require Import WpSmodeHalf WpSmodeIntr.
Require Import ByteBuf.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import ProcDefs.  (* [proc_priv_bare] *)
Require Import SleepLock.
Require Import BufOwn BcacheInv BioInv.
(* THE PAYLOAD'S OWN VOCABULARY (durable-disk 2b-inode-3): [top_frag],
   [fs_gamma_L], [bnode] / [inode_rec_local].  IMPORTED BEFORE [FsBlocks]
   on purpose -- the [FsState*] stack exports [fs_view] and [byte_range],
   both of which have live twins below, and the LAST import wins
   (durable-notes, "AND WHERE THAT IMPORT COLLIDES, PUT IT EARLY"). *)
Require Import FsState.
Require Import FsBytesGamma.
Require Import FsStateEra.
Require Import FsBlocks LogInv.
Require Import BioFs.  (* [bio_held_fs_L] *)
Require Import BlockWords.
Require Import InodeInv.
Require Import DirView.
Require Import DirLinks.
Require Import InodeLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import FsTree.
Require Import IcacheEscrow.
(* RE-IMPORT: [IcacheInv] defines its own slot-keyed [islot] over the
   reference map, which shadows [DinodeEnc.islot] (the dinode's index inside
   its block) -- and it is the latter this proof means everywhere. *)
Require Import DinodeEnc.
Require Import DinodeSlot.
Require Import CodeIlock.
Require Import KernelDataInv.
Require Import PrintkArgs.
Require Import WpUart.
Require Import SpecPanic.
Require Import SpecAcquiresleep SpecBread SpecBrelse SpecMemmove.
Require Import SpecIlock.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.

Set Printing Depth 40.

(* ===================================================================== *)
(*  The two readings ilock needs that DinodeSlot.v does not have          *)
(* ===================================================================== *)

(* [trunc16_sext64] read as injectivity, and the halfword zero test it
   gives: the [lh a5,68(s1)] at +0x98 reads back the type just stored, and
   [inode_ok]'s type conjunct is what makes the [c.beqz] fall through. *)
Lemma il_sext64_16_inj (a c : mword 16) :
  (sign_extend' 64 a : mword 64) = sign_extend' 64 c -> a = c.
Proof.
  intro H. rewrite -(trunc16_sext64 a) -(trunc16_sext64 c) H. reflexivity.
Qed.

Lemma il_type_nonzero (w : mword 16) :
  bv_unsigned w <> 0 ->
  eq_vec (sign_extend' 64 w : mword 64) (zero_reg : mword 64) = false.
Proof.
  intro Hw. apply eq_vec_false_iff. intro Hq. apply Hw.
  assert (Hz : (zero_reg : mword 64) = sign_extend' 64 (mword_of_int 0 : mword 16))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hz in Hq. apply il_sext64_16_inj in Hq. rewrite Hq.
  vm_compute. reflexivity.
Qed.

(* the entry's address is never zero, which is the whole of the first
   panic's null test: [ientry_unsigned] puts it at [itable + 24 + 136k]. *)
Lemma il_entry_nonzero (k : nat) : (k < NINODE)%nat -> uint (ientry k) <> 0.
Proof.
  intros Hk. rewrite uint_unsigned (ientry_unsigned k ltac:(lia)).
  unfold ISLOTSZ, KernelSyms.itable. lia.
Qed.

(* ...and the OTHER direction of [il_type_nonzero]: a FREE inode's type is
   zero, so the [c.beqz] at +0x9c is TAKEN and the panic is reached. *)
Lemma il_type_zero (w : mword 16) :
  bv_unsigned w = 0 ->
  eq_vec (sign_extend' 64 w : mword 64) (zero_reg : mword 64) = true.
Proof.
  intro Hw.
  assert (Hz : w = (mword_of_int 0 : mword 16))
    by (apply bv_eq; rewrite Hw; vm_compute; reflexivity).
  rewrite Hz. vm_compute. reflexivity.
Qed.

Lemma il_lock_addr (x : mword 64) :
  add_vec x (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))
  = i_lock x.
Proof.
  assert (H : (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)) : mword 64)
              = sign_extend' 64 (mword_of_int 16 : mword 12))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H. reflexivity.
Qed.

Lemma il_addi12 (x : mword 64) :
  add_vec x (sign_extend' 64 (sign_extend' 12 (mword_of_int 12 : mword 6)))
  = pa_add x 12%nat.
Proof.
  assert (H : (sign_extend' 64 (sign_extend' 12 (mword_of_int 12 : mword 6)) : mword 64)
              = mword_of_int (Z.of_nat 12%nat))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H. reflexivity.
Qed.

Section IlockParts.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.

  (* THE WRITE-DIRECTION TWIN of [InodeInv.inode_addrs_buf].  memmove's
     DESTINATION is the thirteen [i_addr] cells viewed as 52 contiguous
     bytes; unlike iupdate's read-only source they come back at NEW values,
     so the back-wand takes any list of the same length.  The per-cell
     4-alignment the byte view forgets is carried by the wand's closure,
     and it depends only on the LENGTH -- which is why one length premise
     is all the wand needs. *)
  Lemma il_addrs_buf_upd `{XI : CurCtx} (ip : mword 64) (l : list (bv 32)) :
    inode_addrs ip l -∗
      bb_bytes (i_addr ip 0) (4 * length l)%nat (fun j => ind_bytes l !!! j) ∗
      (∀ l' : list (bv 32), ⌜length l' = length l⌝ -∗
         bb_bytes (i_addr ip 0) (4 * length l')%nat
                  (fun j => ind_bytes l' !!! j) -∗
         inode_addrs ip l').
  Proof.
    iIntros "H".
    iDestruct (inode_addrs_aligned_all with "H") as %Hal.
    rewrite (inode_addrs_bytes_iff ip l Hal).
    iFrame "H". iIntros (l') "%Hlen Hb".
    rewrite (inode_addrs_bytes_iff ip l' ltac:(rewrite Hlen; exact Hal)).
    iExact "Hb".
  Qed.

  
End IlockParts.


(* ===================================================================== *)
(*  THE PANIC MESSAGE.  ilock's one LIVE arm is [panic("ilock: no type")] *)
(*  at +0xaa -- a FREE inode read off the disk; the literal sits at       *)
(*  0x80007470 in .rodata, fourteen characters and a NUL.  (The OTHER     *)
(*  panic, "ilock" at +0x22, is refuted from [ip <> 0] and needs nothing.) *)
(*  NAMED pure lemmas, not inline [ltac:] -- see optimization.md.         *)
(* ===================================================================== *)
Definition il_msg_a : Z := 0x80007470.
Definition il_msg : string := "ilock: no type".

Lemma il_panic_K (K : nat) : (K_ilock <= K)%nat -> (panic_stack <= K - 4)%nat.
Proof. lia. Qed.

Lemma il_panic_noff : (Z.of_nat 0 + 2 < 2 ^ 31)%Z.
Proof. lia. Qed.

Lemma il_panic_below (lks : gset string) :
  locks_below lks "bcache" -> locks_below lks "pr".
Proof. intros H. apply (locks_below_mono lks "bcache" "pr" H). vm_compute; lia. Qed.

Lemma il_msg_nz : eq_vec (mword_of_int il_msg_a : mword 64) zero_reg = false.
Proof. vm_compute; reflexivity. Qed.

Lemma il_msg_nonul : PrintkFmt.nonul il_msg = true.
Proof. vm_compute; reflexivity. Qed.

Lemma il_msg_bytes :
  forall j b, cstring_bytes il_msg !! j = Some b ->
    KernelData.kernel_data !! (il_msg_a + Z.of_nat j)%Z = Some b.
Proof.
  intros j b Hj.
  do 15 (destruct j as [|j]; [ vm_compute in Hj |- *; congruence | ]).
  vm_compute in Hj; discriminate.
Qed.

Section IlockMsg.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  Lemma il_msg_str :
    (kernel_data : iProp Σ) -∗ (mword_of_int il_msg_a : mword 64) ↦ₛ□ il_msg.
  Proof.
    iIntros "#Hd".
    iApply (kernel_data_string il_msg_a il_msg _ eq_refl
              ltac:(unfold text_end, il_msg_a; lia)
              ltac:(vm_compute; discriminate) il_msg_bytes with "Hd").
  Qed.
End IlockMsg.

Module IlockProof (ASL : ACQUIRESLEEP) (BR : BREAD) (MM : MEMMOVE) (BL : BRELSE)
                  (PN : PANIC)
  : ILOCK.

Notation Rra := (mword_of_int 1 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Rs1 := (mword_of_int 9 : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Ra2 := (mword_of_int 12 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).

Local Ltac regne := reg_ne_side.

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.
Local Ltac iuidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

(* the register-threading invariants.  [il_thr5] is what holds at the JOIN
   (+0x1e): s2 is restored at +0x9e on the uncached arm and never written
   on the cached one, so BOTH arrive with it at its entry value -- bmap's
   [s4] quirk, verbatim.  [il_thr6] is the weaker one the uncached arm's
   interior carries, where s2 is genuinely live. *)
Definition il_thr5 (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Definition il_thr6 (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Lemma il_thr6_of_5 (m M : regfile) : il_thr5 m M -> il_thr6 m M.
Proof. intros H c Hcs N2 N8 N9 _. exact (H c Hcs N2 N8 N9). Qed.

Definition il_sp (m M : regfile) : Prop :=
  M !!! Regidx csp_rs1
  = add_vec (m !!! Regidx csp_rs1 : mword 64)
      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))).

Section IlockDefs.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, !irefslotG Σ, !pavG Σ}.

  (* ilock's 32-byte frame: ra@24 s0@16 s1@8, and slot 4 (s2's) held
     ANONYMOUSLY -- the cached arm never writes it. *)
  Definition il_frame `{XI : CurCtx} (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1 ↦₈[KT1] (m !!! Regidx Rra : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 2 ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 3 ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) ∗
     ∃ w : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 4 ↦₈[KT1] w)%I.

  (* [cn] and [s] are here for ONE resource: the other half of the entry
     sleeplock's checkout descriptor (§14.8).  SpecIlock v3 hands it to the
     caller, so both arms of the function have to carry it to the join. *)
  Definition il_cont `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx} 
      (gfs : fs_names) (gi : gname) (gisl : gname) (bn : bio_names)
      (cn : ic_names) (s : Qp) (g : gname) (o : ilkc)
      (cov : gset Z) (logstart : Z) (inodestart : Z)
      (k : nat) (ip : mword 64) (dev inum : mword 32)
      (pidv : mword 32) (dq dqs : dfrac) (j : nat)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) (Vpr : pprivate) : iProp Σ :=
    (* THE LITERAL [true], matching SpecIlock's crossing: ilock PARKS (its
       acquiresleep sleeps), so its continuation is about an arbitrary hart
       whatever SIE was doing.  Spelled [b] this was sound only because the
       contract had no [b = false] instance. *)
    wp_next true (proc_addr j) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (dn : dinode) (bm : blkmap) (filled : bool),
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr j) -∗
        cpu_own 0 eb (proc_addr j) b lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb (proc_addr j) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        proc_priv_bare (proc_addr j) pidv Vpr -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        bslot -∗
        sleeplocked_q gisl s (i_lock ip) pidv -∗
        ic_deposit cn k (DepShr s dev inum g) -∗
        i_dev ip ↦₄{DfracOwn (1/2)} dev -∗
        i_inum ip ↦₄{DfracOwn (1/2)} inum -∗
        i_valid ip ↦₄ valid_word true -∗
        ic_loaded gfs gi cov logstart k inum dn bm -∗
        ity_shot g (di_type dn) -∗
        (* ...AND THE INUM'S FREEZE TOKEN (iclaim-ledger.md §3.9, RULING
           A-prime).  It rides the PAYLOAD ([IcacheEscrow.ic_payload]'s
           A-custody conjunct), so a checked-out holder has it on BOTH arms:
           the cached one splits it off the payload it takes out, the
           uncached one carries it past the fill.  Routing it to this post
           is what [SpecIlock] has asked for since IVb; create's fresh child
           pays [wp_iupdate_link]'s freeze pin with it. *)
        ifreeze_off (bv_unsigned inum) -∗
        (* §16.4's CLAIM BOX, exposed: [true] exactly on the fill sub-arm
           [InodeRegion.ireg_withdraw] serves, where [fresh_shape] is a
           theorem the arm already had and used to drop. *)
        ⌜filled = true -> fresh_shape dn⌝ -∗
        (* ...AND THE LICENCE's PAYOUT, per RULING C' (SpecIlock's header) *)
        ireg_wd_back o g (bv_unsigned inum) -∗
        ⌜ilk_post o filled dn⌝ -∗
        WP (Loop : expr riscv_lang))%I.

End IlockDefs.

(* ===================================================================== *)
(*  +0x1e .. +0x26 : THE JOIN -- pop ra/s0/s1, ret, and the contract.     *)
(* ===================================================================== *)
Section IlockEpilogue.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, !irefslotG Σ, !pavG Σ}.

  Local Lemma il_epilogue `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx} 
      (j : nat) (gfs : fs_names) (gi : gname) (gisl : gname) (bn : bio_names)
      (cn : ic_names) (s : Qp) (g : gname) (o : ilkc)
      (cov : gset Z) (logstart : Z) (inodestart : Z)
      (k : nat) (ip : mword 64) (dev inum : mword 32)
      (dn : dinode) (bm : blkmap) (filled : bool)
      (pidv : mword 32) (dq dqs : dfrac)
      (m M : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) (Vpr : pprivate) :
    (K_ilock <= K)%nat ->
    il_sp m M ->
    il_thr5 m M ->
    (filled = true -> fresh_shape dn) ->
    ilk_post o filled dn ->
    sie_cap_gpr KT1 M (K - 4)%nat b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.ilock + 0x1e) : mword 64) -∗
    il_frame m -∗
    proc_priv_bare (proc_addr j) pidv Vpr -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bslot -∗
    sleeplocked_q gisl s (i_lock ip) pidv -∗
    ic_deposit cn k (DepShr s dev inum g) -∗
    i_dev ip ↦₄{DfracOwn (1/2)} dev -∗
    i_inum ip ↦₄{DfracOwn (1/2)} inum -∗
    i_valid ip ↦₄ valid_word true -∗
    ic_loaded gfs gi cov logstart k inum dn bm -∗
    ity_shot g (di_type dn) -∗
    ifreeze_off (bv_unsigned inum) -∗
    ireg_wd_back o g (bv_unsigned inum) -∗
    il_cont (CID0 := CID0)  gfs gi gisl bn cn s g o cov logstart inodestart k ip
            dev inum pidv dq dqs j m K eb b lks Vpr -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp Hthr Hfr Hpost.
    pose proof HK as HK'. 
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc Hframe Hppid Hsb
              Hsl Hstok Hdep Hidev Hinumc Hvalid Hlk #Hshot Hfoff Hwb Hcont".
    (* LEVEL 0 TIES THE TWO INDICES: ilock never push_off's on its own (only
       acquiresleep/bread do, opaquely), so [cpu_own]'s [n] is [0] throughout
       and [cpu_own_eb_agree] gives [eb = b] outright (kept as a hypothesis,
       not [subst] -- [b] is still the index every leaf instruction below is
       stated at); the [_ext_transport] guards are spelled at [eb], so this
       is what lets [wp_next_chain] close them off the SAME per-step facts
       [b]'s transports use. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Heb2b. cbn in Heb2b.
    rewrite /il_frame.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4)".
    iDestruct "Hf4" as (w4) "Hf4".
    assert (Hc1 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc2 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc3 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    (* +0x1e c.ldsp ra,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ilock + 0x1e)) (mword_of_int 3 : mword 6) Rra
              M (K - 4)%nat (m !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf1]").
    { iApply (ili_1e with "Htext"). }
    { iEval (rewrite Hc1). iExact "Hf1". }
    iIntros (CID1 Hq1) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> M).
    assert (HP1sp : il_sp m P1)
      by (rewrite /il_sp /P1 upd_ne; [exact Hsp | nz]).
    assert (HP1thr : il_thr5 m P1).
    { intros c Hcs N2 N8 N9.
      rewrite /P1 upd_ne; [| regne]. exact (Hthr c Hcs N2 N8 N9). }
    assert (HP1ra : P1 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x1e) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x20)) by pcw.
    iEval (rewrite Hpp20) in "Hpc".
    (* +0x20 c.ldsp s0,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ilock + 0x20)) (mword_of_int 2 : mword 6) Rs0
              P1 (K - 4)%nat (m !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf2]").
    { iApply (ili_20 with "Htext"). }
    { iEval (rewrite HP1sp -Hsp Hc2). iExact "Hf2". }
    iIntros (CID2 Hq2) "Hcg Hpc Hf2".
    iEval (rewrite HP1sp -Hsp Hc2) in "Hf2".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2sp : il_sp m P2)
      by (rewrite /il_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2thr : il_thr5 m P2).
    { intros c Hcs N2 N8 N9.
      rewrite /P2 upd_ne; [| regne]. exact (HP1thr c Hcs N2 N8 N9). }
    assert (HP2ra : P2 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1ra | nz]).
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x20) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x22)) by pcw.
    iEval (rewrite Hpp22) in "Hpc".
    (* +0x22 c.ldsp s1,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ilock + 0x22)) (mword_of_int 1 : mword 6) Rs1
              P2 (K - 4)%nat (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf3]").
    { iApply (ili_22 with "Htext"). }
    { iEval (rewrite HP2sp -Hsp Hc3). iExact "Hf3". }
    iIntros (CID3 Hq3) "Hcg Hpc Hf3".
    iEval (rewrite HP2sp -Hsp Hc3) in "Hf3".
    set (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2).
    assert (HP3sp : il_sp m P3)
      by (rewrite /il_sp /P3 upd_ne; [exact HP2sp | nz]).
    assert (HP3thr : il_thr5 m P3).
    { intros c Hcs N2 N8 N9.
      rewrite /P3 upd_ne; [| regne]. exact (HP2thr c Hcs N2 N8 N9). }
    assert (HP3ra : P3 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2ra | nz]).
    assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x22) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x24)) by pcw.
    iEval (rewrite Hpp24) in "Hpc".
    (* ===== +0x24 c.addi16sp sp,32 : pop ===== *)
    assert (Hwv : add_vec (P3 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))
                  = (m !!! Regidx csp_rs1 : mword 64)).
    { rewrite HP3sp. apply bv_eq.
      rewrite !add_vec64_unsigned.
      rewrite bv_wrap_add_idemp_l.
      assert (Hz : bv_unsigned (sign_extend' 64
                     (sign_extend' 12 (mword_of_int 32 : mword 6)) : mword 64)
                   = 18446744073709551584) by (vm_compute; reflexivity).
      assert (Hz2 : bv_unsigned (sign_extend' 64
                      (caddi16sp_imm (mword_of_int 2 : mword 6)) : mword 64)
                    = 32) by (vm_compute; reflexivity).
      rewrite Hz Hz2.
      replace (bv_unsigned (m !!! Regidx csp_rs1 : mword 64)
                 + 18446744073709551584 + 32)
        with (bv_unsigned (m !!! Regidx csp_rs1 : mword 64)
                 + 18446744073709551616) by ring.
      rewrite -bv_wrap_add_idemp_r.
      assert (Hm0 : bv_wrap 64 18446744073709551616 = 0)
        by (vm_compute; reflexivity).
      rewrite Hm0 Z.add_0_r.
      apply bv_wrap_small. apply bv_unsigned_in_range. }
    assert (Hpop : (P3 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (P3 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HP3sp. unfold pa_stk, add_vec_int. apply f_equal. pcw. }
    assert (Hc4 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iAssert (stack_own (KTR := KT1) (m !!! Regidx csp_rs1 : mword 64) 4)
      with "[Hf1 Hf2 Hf3 Hf4]" as "Hstk".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hf1"; [iExists _; iExact "Hf1" |].
      iSplitL "Hf2"; [iExists _; iExact "Hf2" |].
      iSplitL "Hf3"; [iExists _; iExact "Hf3" |].
      iSplitL "Hf4"; [iExists _; iExact "Hf4" |].
      done. }
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.ilock + 0x24))
              (mword_of_int 2 : mword 6) P3 (K - 4)%nat 4 b Hpop
              with "Hcg Hpc [] Hstk").
    { iApply (ili_24 with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (P4 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P3 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P3).
    assert (Hnk : ((K - 4) + 4)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x24) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x26)) by pcw.
    iEval (rewrite Hpp26) in "Hpc".
    (* ===== +0x26 c.ret ===== *)
    assert (HP4ra : P4 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P4 upd_ne; [exact HP3ra | nz]).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.ilock + 0x26)) Rra P4 K b ltac:(nz)
              with "Hcg Hpc []").
    { iApply (ili_26 with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (P4 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HP4ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE CONTRACT ===== *)
    assert (Csp : P4 !!! Regidx csp_rs1 = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P4 upd_eq; exact Hwv).
    assert (Cs0 : P4 !!! Regidx Rs0 = (m !!! Regidx Rs0 : mword 64)).
    { rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_ne; [| nz].
      rewrite /P2 upd_eq. reflexivity. }
    assert (Cs1 : P4 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64)).
    { rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_eq. reflexivity. }
    assert (Hfin : il_thr5 m P4).
    { intros c Hcs N2 N8 N9.
      rewrite /P4 upd_ne; [| regne]. exact (HP3thr c Hcs N2 N8 N9). }
    assert (Cs2 : P4 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs3 : P4 !!! Regidx (mword_of_int 19 : mword 5)
                  = (m !!! Regidx (mword_of_int 19 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs4 : P4 !!! Regidx (mword_of_int 20 : mword 5)
                  = (m !!! Regidx (mword_of_int 20 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs5 : P4 !!! Regidx (mword_of_int 21 : mword 5)
                  = (m !!! Regidx (mword_of_int 21 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs6 : P4 !!! Regidx (mword_of_int 22 : mword 5)
                  = (m !!! Regidx (mword_of_int 22 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs7 : P4 !!! Regidx (mword_of_int 23 : mword 5)
                  = (m !!! Regidx (mword_of_int 23 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs8 : P4 !!! Regidx (mword_of_int 24 : mword 5)
                  = (m !!! Regidx (mword_of_int 24 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs9 : P4 !!! Regidx (mword_of_int 25 : mword 5)
                  = (m !!! Regidx (mword_of_int 25 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs10 : P4 !!! Regidx (mword_of_int 26 : mword 5)
                  = (m !!! Regidx (mword_of_int 26 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs11 : P4 !!! Regidx (mword_of_int 27 : mword 5)
                  = (m !!! Regidx (mword_of_int 27 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
   iDestruct (cpu_own_transport CID0 CID5 0 eb (proc_addr j) b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CID5 eb (proc_addr j)
                 ltac:(rewrite Heb2b; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CID5 eb (proc_addr j)
                 ltac:(rewrite Heb2b; wp_next_chain) with "Hextm") as "Hextm".
    rewrite /il_cont.
    iSpecialize ("Hcont" $! CID5 with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! P4 dn bm filled with "[%] Hcg Hcnt Hextc Hextm Hpc Hppid Hsb
                     Hsl Hstok Hdep Hidev Hinumc Hvalid Hlk Hshot Hfoff [%] Hwb [%]").
    { unfold callee_saved. split_and!; assumption. }
    { exact Hfr. }
    { exact Hpost. }
  Qed.

End IlockEpilogue.

(* ===================================================================== *)
(*  +0x36 .. +0xa0 : THE UNCACHED ARM.                                    *)
(* ===================================================================== *)
Section IlockLoad.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, !irefslotG Σ, !pavG Σ}.

  (* ------------------------------------------------------------------ *)
  (*  A CLAIMED INODE'S BUNDLE, OUT OF NOTHING (§16.4's fill sub-arm)     *)
  (* ------------------------------------------------------------------ *)

  (* ialloc's claim leaves the record at [InodeRegion.fresh_shape] and the
     fragment inside the region invariant; the FIRST fill withdraws it and
     has to build a full [IcacheEscrow.ic_loaded] payload around it.  There
     is nothing to inherit -- no pool bundle ever existed for this inum --
     so every piece comes from [bm_empty], and these three lemmas are the
     pieces.  ([InodeInv.bm_empty_wf], [bm_covers_nonpos],
     [inode_sized_zero] and [DirView.dir_ok_size_zero] do the rest, at the
     call site.) *)
  Local Lemma il_bmcells_empty : bm_cells bm_empty = replicate 13 (bv_0 32).
  Proof. rewrite /bm_cells /bm_empty /NDIRECT. cbn. reflexivity. Qed.

  Local Lemma il_ind_res_empty (gfs : fs_names) : ⊢ ind_res gfs bm_empty.
  Proof.
    rewrite /ind_res /ind_blk.
    destruct (decide (bv_unsigned (bm_ind bm_empty) = 0)) as [_|Hc];
      [done | exfalso; apply Hc; reflexivity].
  Qed.

  Local Lemma il_blocks_empty (gfs : fs_names) (data : nat -> list (bv 8)) :
    ⊢ inode_blocks gfs bm_empty data.
  Proof.
    rewrite /inode_blocks.
    iApply big_sepL_intro. iIntros "!>" (t x Hx).
    rewrite /blk_res bm_empty_get.
    destruct (decide (bv_unsigned (bv_0 32) = 0)) as [_|Hc];
      [done | exfalso; apply Hc; reflexivity].
  Qed.

  Local Lemma il_load `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (gfs : fs_names) (gi : gname) (gisl : gname)
      (cn : ic_names) (s : Qp) (g : gname) (o : ilkc)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
      (dev : mword 32)
      (k : nat) (ip : mword 64) (inum : mword 32)
      (pidv : mword 32) (dq dqs : dfrac)
      (m M : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) (Vpr : pprivate) :
    (K_ilock <= K)%nat ->
    (* [ShotK] never gets here: its one-shot refutes this whole arm at the
       caller, five hundred lines up (RULING C'). *)
    ilk_fills o ->
    il_sp m M ->
    il_thr5 m M ->
    M !!! Regidx Rs1 = ip ->
    ip = ientry k ->
    (k < NINODE)%nat ->
    log_geom_ok cov logstart ->
    0 <= inodestart ->
    IBLOCK inum inodestart ∈ cov ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    (j < NPROC)%nat ->
    gs !! j = Some gl ->
    (* il_load reaches bread/brelse, whose bound is "bcache" (4); it is the
       whole point of this helper (the fill arm), so it needs the premise
       threaded on its own binder list just like [wp_ilock_sconf] itself. *)
    locks_below lks "bcache" ->
    sie_cap_gpr KT1 M (K - 4)%nat b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.ilock + 0x36) : mword 64) -∗
    panic_env -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    ireg_inv gi gfs inodestart nib -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (λ ξ : CtxId, disk_res (XI := ξ) gd pd pav pu) -∗
    il_frame m -∗
    proc_priv_bare (proc_addr j) pidv Vpr -∗
    i_dev ip ↦₄{DfracOwn (1/2)} dev -∗
    i_inum ip ↦₄{DfracOwn (1/2)} inum -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bslot -∗
    sleeplocked_q gisl s (i_lock ip) pidv -∗
    ic_deposit cn k (DepShr s dev inum g) -∗
    i_valid ip ↦₄ (mword_of_int 0 : mword 32) -∗
    inode_raw ip -∗
    (* THE [_np] FORM, not the full [ipool_shape] (iclaim-ledger.md §3.5
       item 7).  What a checked-out UNLOADED payload actually contains is
       [IcacheEscrow.ic_unloaded], i.e. [inode_raw ∗ ipool_shape_np]: the
       ledger's [icnt] half and the freeze token left the bundle at the
       RECYCLE's peel ([ipool_shape_to_np], ProofIget +0x72) and now live on
       the slot's live [islot2] arm and the parked payload respectively.  So
       the fill has no pool shape left to convert and does no peel of its own
       -- the conversion happened once, at the recycle, for the whole
       lifetime of the cached entry. *)
    ipool_shape_np gfs gi cov logstart inum -∗
    (* THE GENERATION'S PENDING ONE-SHOT (design §17.6): the caller splits it
       out of the UNLOADED payload alongside the [inode_raw]/[ipool_shape_np]
       pair it already splits, and this arm SPENDS it against the record the
       [bread] returns.  [g] was already one of this lemma's parameters. *)
    ity_pending g -∗
    (* ...AND THE A-PRIME TOKEN, split off the same payload and carried
       straight through to the post (iclaim-ledger.md §3.9). *)
    ifreeze_off (bv_unsigned inum) -∗
    (* THE FILL's LICENCE (RULING C'): [ClaimK]'s pair, which the withdraw
       CONVERTS, or [PlainK]'s borrowed unit, which refutes the box arm and
       comes back.  See [SpecIlock]'s header. *)
    ireg_wd_lic o g (bv_unsigned inum) -∗
    il_cont (CID0 := CID0)  gfs gi gisl bn cn s g o cov logstart inodestart k ip
            dev inum pidv dq dqs j m K eb b lks Vpr -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hfills Hsp Hthr HMs1 Hip Hk Hgeom Hst Hcov Hinlt Hj Hgl Hbelow.
    pose proof HK as HK'. 
    destruct Hgeom as [Hcovok Hlogsub].
    destruct (Hcovok _ Hcov) as [Hibpos Hiblt].
    assert (Hib : 0 <= IBLOCK inum inodestart < 2147483648)
      by (change (2 ^ 31)%Z with 2147483648%Z in Hiblt; lia).
    set (bno := (mword_of_int (IBLOCK inum inodestart) : mword 32)).
    assert (Hbno : uint bno = IBLOCK inum inodestart).
    { rewrite /bno bb_uint32 moi32_unsigned. apply bvw32_small.
      change (2^32)%Z with 4294967296%Z. lia. }
    assert (Hbnolt : (uint bno < 2147483648)%Z) by (rewrite Hbno; lia).
    assert (Hbnocov : uint bno ∈ bv_cov (fs_view gfs gd dev cov))
      by (rewrite Hbno; exact Hcov).
    pose proof (bv_unsigned_in_range _ inum) as [Hinum0 Hinum1].
    assert (Hm32 : bv_modulus (MachineWord.MachineWord.Z_idx 32) = 4294967296)
      by (vm_compute; reflexivity).
    rewrite Hm32 in Hinum1.
    assert (Hslotz : Z.of_nat (islot inum) = bv_unsigned inum `mod` 16).
    { rewrite /islot Z2Nat.id; [reflexivity |].
      pose proof (Z.mod_pos_bound (bv_unsigned inum) 16 ltac:(lia)) as [Hz _].
      exact Hz. }
    pose proof (islot_lt inum) as Hslotlt.
    assert (HMs2 : M !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64))
      by (apply Hthr; iuidx).
    pose proof (il_thr6_of_5 m M Hthr) as Hthr6.
    iIntros "Hcg Hcnt Hextc Hextm #Htext #Hkd Hpc #Hpenv #Hbio #Hireg #Hprocs #Hdevi #Hdgeom
              #Hdlock Hframe Hppid Hidev Hinumc Hsb Hsl
              Hstok Hdep Hvalid Hraw Hpool Hpend Hfoff Hcl Hcont".
    (* LEVEL 0 TIES THE TWO INDICES, as in [il_epilogue]. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Heb2b. cbn in Heb2b.
    (* THE POOL ENTRY STAYS OPAQUE UNTIL THE BUFFER HAS BEEN READ (§16.4).
       Before §16.4 both of §13.3's shapes carried the region fragment, so
       the record could be named here; now the FREE shape is a bare marker
       and the record is only knowable off the block the bread returns.  The
       case analysis therefore moves down to the [ireg_read_blk] below, and
       everything between here and the type test runs on the shapes' common
       part -- the BUFFER's bytes and this entry's own cells. *)
    iDestruct "Hraw" as "[Hmeta0 Haddrs0]".
    iDestruct "Hmeta0" as (d0) "(Hmty & Hmmaj & Hmmin & Hmnl & Hmsz)".
    iDestruct "Haddrs0" as (l0) "[%Hl0len Haddrs0]".
    rewrite /il_frame.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4)".
    iDestruct "Hf4" as (w4) "Hf4".
    assert (Hc4 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    (* ===== +0x36 c.sdsp s2,0(sp) ===== *)
    iEval (rewrite -Hc4) in "Hf4".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.ilock + 0x36)) (mword_of_int 0 : mword 6) Rs2
              M (K - 4)%nat w4 b with "Hcg Hpc [] Hf4").
    { iApply (ili_36 with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hpc Hf4".
    iEval (rewrite Hc4; rgne; rewrite HMs2) in "Hf4".
    assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x36) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x38)) by pcw.
    iEval (rewrite Hpp38) in "Hpc".
    (* ===== +0x38 c.lw a5,4(s1) : a5 := ip->inum ===== *)
    assert (Hinadr : add_vec (rget M Rs1) (sign_extend' 64 (mword_of_int 4 : mword 12))
                     = i_inum ip).
    { rgne. rewrite HMs1. reflexivity. }
    iEval (rewrite -Hinadr) in "Hinumc".
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.ilock + 0x38)) Ra5 Rs1
              (mword_of_int 4 : mword 12) M (K - 4)%nat inum b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hinumc").
    { iApply (ili_38 with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc Hinumc".
    iEval (rewrite Hinadr) in "Hinumc".
    set (L1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 inum)]> M).
    assert (HL1a5 : L1 !!! Regidx Ra5 = (sign_extend' 64 inum : mword 64))
      by (rewrite /L1; apply upd_eq).
    assert (HL1s1 : L1 !!! Regidx Rs1 = ip)
      by (rewrite /L1 upd_ne; [exact HMs1 | nz]).
    assert (HL1sp : il_sp m L1)
      by (rewrite /il_sp /L1 upd_ne; [exact Hsp | nz]).
    assert (HL1thr : il_thr6 m L1).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /L1 upd_ne; [| regne]. exact (Hthr6 c Hcs N2 N8 N9 N18). }
    assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.ilock + 0x38) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x3a)) by pcw.
    iEval (rewrite Hpp3a) in "Hpc".
    (* ===== +0x3a srliw a5,a5,0x4 ===== *)
    iApply (wp_srliw_s_sconf (mword_of_int (KernelSyms.ilock + 0x3a)) Ra5 Ra5
              (mword_of_int 4 : mword 5)
              (mword_of_int (bv_unsigned inum / 16) : mword 64)
              L1 (K - 4)%nat b ltac:(nz) ltac:(rdok)
              ltac:(rgne; rewrite HL1a5; apply iu_srliw4)
              with "Hcg Hpc []").
    { iApply (ili_3a with "Htext"). }
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (L2 := <[Regidx Ra5 := regval_into_reg
                  (mword_of_int (bv_unsigned inum / 16) : mword 64)]> L1).
    assert (HL2a5 : L2 !!! Regidx Ra5
                    = (mword_of_int (bv_unsigned inum / 16) : mword 64))
      by (rewrite /L2; apply upd_eq).
    assert (HL2s1 : L2 !!! Regidx Rs1 = ip)
      by (rewrite /L2 upd_ne; [exact HL1s1 | nz]).
    assert (HL2sp : il_sp m L2)
      by (rewrite /il_sp /L2 upd_ne; [exact HL1sp | nz]).
    assert (HL2thr : il_thr6 m L2).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /L2 upd_ne; [| regne]. exact (HL1thr c Hcs N2 N8 N9 N18). }
    assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.ilock + 0x3a) : mword 64) 4
                    = mword_of_int (KernelSyms.ilock + 0x3e)) by pcw.
    iEval (rewrite Hpp3e) in "Hpc".
    (* ===== +0x3e auipc a1,0x1d ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.ilock + 0x3e)) Ra1
              (mword_of_int 29 : mword 20) L2 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (ili_3e with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (L3 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.ilock + 0x3e) : mword 64)
                     (auipc_off (mword_of_int 29 : mword 20)))]> L2).
    assert (HL3a1 : L3 !!! Regidx Ra1
                    = add_vec (mword_of_int (KernelSyms.ilock + 0x3e) : mword 64)
                        (auipc_off (mword_of_int 29 : mword 20)))
      by (rewrite /L3; apply upd_eq).
    assert (HL3a5 : L3 !!! Regidx Ra5
                    = (mword_of_int (bv_unsigned inum / 16) : mword 64))
      by (rewrite /L3 upd_ne; [exact HL2a5 | nz]).
    assert (HL3s1 : L3 !!! Regidx Rs1 = ip)
      by (rewrite /L3 upd_ne; [exact HL2s1 | nz]).
    assert (HL3sp : il_sp m L3)
      by (rewrite /il_sp /L3 upd_ne; [exact HL2sp | nz]).
    assert (HL3thr : il_thr6 m L3).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /L3 upd_ne; [| regne]. exact (HL2thr c Hcs N2 N8 N9 N18). }
    assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x3e) : mword 64) 4
                    = mword_of_int (KernelSyms.ilock + 0x42)) by pcw.
    iEval (rewrite Hpp42) in "Hpc".
    (* ===== +0x42 lw a1,1698(a1) : a1 := sb.inodestart ===== *)
    assert (Hsbadr : add_vec (rget L3 Ra1)
                       (sign_extend' 64 (mword_of_int 1684 : mword 12))
                     = sb_inodestart).
    { rgne. rewrite HL3a1. rewrite /sb_inodestart /pa_add /add_vec_int. pcw. }
    iEval (rewrite -Hsbadr) in "Hsb".
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.ilock + 0x42)) Ra1 Ra1
              (mword_of_int 1684 : mword 12) L3 (K - 4)%nat
              (mword_of_int inodestart : mword 32) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hsb").
    { iApply (ili_42 with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc Hsb".
    iEval (rewrite Hsbadr) in "Hsb".
    set (L4 := <[Regidx Ra1 := regval_into_reg
                  (sign_extend' 64 (mword_of_int inodestart : mword 32))]> L3).
    assert (HL4a1 : L4 !!! Regidx Ra1
                    = (sign_extend' 64 (mword_of_int inodestart : mword 32) : mword 64))
      by (rewrite /L4; apply upd_eq).
    assert (HL4a5 : L4 !!! Regidx Ra5
                    = (mword_of_int (bv_unsigned inum / 16) : mword 64))
      by (rewrite /L4 upd_ne; [exact HL3a5 | nz]).
    assert (HL4s1 : L4 !!! Regidx Rs1 = ip)
      by (rewrite /L4 upd_ne; [exact HL3s1 | nz]).
    assert (HL4sp : il_sp m L4)
      by (rewrite /il_sp /L4 upd_ne; [exact HL3sp | nz]).
    assert (HL4thr : il_thr6 m L4).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /L4 upd_ne; [| regne]. exact (HL3thr c Hcs N2 N8 N9 N18). }
    assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x42) : mword 64) 4
                    = mword_of_int (KernelSyms.ilock + 0x46)) by pcw.
    iEval (rewrite Hpp46) in "Hpc".
    (* ===== +0x46 c.addw a1,a1,a5 : a1 := IBLOCK(inum, sb) ===== *)
    iApply (wp_addw_s_sconf (mword_of_int (KernelSyms.ilock + 0x46)) Ra1 Ra5
              L4 (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (ili_46 with "Htext"). }
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (L5 := <[Regidx Ra1 := regval_into_reg
                  (sign_extend' 64
                     (add_vec (subrange_vec_dec (rget L4 Ra1) 31 0 : mword 32)
                              (subrange_vec_dec (rget L4 Ra5) 31 0 : mword 32)))]> L4).
    assert (HL5a1 : L5 !!! Regidx Ra1 = (sign_extend' 64 bno : mword 64)).
    { rewrite /L5 upd_eq. rgne. rgne. rewrite HL4a1 HL4a5.
      rewrite /bno. apply (iu_addw_ibl inum inodestart Hst Hib). }
    assert (HL5s1 : L5 !!! Regidx Rs1 = ip)
      by (rewrite /L5 upd_ne; [exact HL4s1 | nz]).
    assert (HL5sp : il_sp m L5)
      by (rewrite /il_sp /L5 upd_ne; [exact HL4sp | nz]).
    assert (HL5thr : il_thr6 m L5).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /L5 upd_ne; [| regne]. exact (HL4thr c Hcs N2 N8 N9 N18). }
    assert (Hpp48 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x46) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x48)) by pcw.
    iEval (rewrite Hpp48) in "Hpc".
    (* ===== +0x48 c.lw a0,0(s1) : a0 := ip->dev ===== *)
    assert (Hdadr : add_vec (rget L5 Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12))
                    = i_dev ip).
    { rgne. rewrite HL5s1. reflexivity. }
    iEval (rewrite -Hdadr) in "Hidev".
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.ilock + 0x48)) Ra0 Rs1
              (mword_of_int 0 : mword 12) L5 (K - 4)%nat dev b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hidev").
    { iApply (ili_48 with "Htext"). }
    iIntros (CID7 Hq7) "Hcg Hpc Hidev".
    iEval (rewrite Hdadr) in "Hidev".
    set (L6 := <[Regidx Ra0 := regval_into_reg (sign_extend' 64 dev)]> L5).
    assert (HL6a0 : L6 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /L6; apply upd_eq).
    assert (HL6a1 : L6 !!! Regidx Ra1 = (sign_extend' 64 bno : mword 64))
      by (rewrite /L6 upd_ne; [exact HL5a1 | nz]).
    assert (HL6s1 : L6 !!! Regidx Rs1 = ip)
      by (rewrite /L6 upd_ne; [exact HL5s1 | nz]).
    assert (HL6sp : il_sp m L6)
      by (rewrite /il_sp /L6 upd_ne; [exact HL5sp | nz]).
    assert (HL6thr : il_thr6 m L6).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /L6 upd_ne; [| regne]. exact (HL5thr c Hcs N2 N8 N9 N18). }
    assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.ilock + 0x48) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x4a)) by pcw.
    iEval (rewrite Hpp4a) in "Hpc".
    (* ===== +0x4a jal ra,bread ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.ilock + 0x4a)) Rra
              (mword_of_int 2095390 : mword 21) L6 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (ili_4a with "Htext"). }
    iIntros (CID8 Hq8) "Hcg Hpc".
    set (L7 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.ilock + 0x4a) : mword 64) 4)]> L6).
    assert (Htgtbr : add_vec (mword_of_int (KernelSyms.ilock + 0x4a) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095390 : mword 21))
                     = mword_of_int KernelSyms.bread) by pcw.
    iEval (rewrite Htgtbr) in "Hpc".
    assert (HL7a0 : L7 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /L7 upd_ne; [exact HL6a0 | nz]).
    assert (HL7a1 : L7 !!! Regidx Ra1 = (sign_extend' 64 bno : mword 64))
      by (rewrite /L7 upd_ne; [exact HL6a1 | nz]).
    assert (HL7s1 : L7 !!! Regidx Rs1 = ip)
      by (rewrite /L7 upd_ne; [exact HL6s1 | nz]).
    assert (HL7sp : il_sp m L7)
      by (rewrite /il_sp /L7 upd_ne; [exact HL6sp | nz]).
    assert (HL7ra : L7 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.ilock + 0x4a) : mword 64) 4)
      by (rewrite /L7; apply upd_eq).
    assert (HL7thr : il_thr6 m L7).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /L7 upd_ne; [| regne]. exact (HL6thr c Hcs N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID0 CID8 0 eb (proc_addr j) b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CID8 eb (proc_addr j)
                 ltac:(rewrite Heb2b; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CID8 eb (proc_addr j)
                 ltac:(rewrite Heb2b; wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID8) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKbr : (K_bread <= K - 4)%nat) by (lia).
    (* bread is index-generic now: ilock's own complement (untouched since
       entry -- nothing between il_load's own start and here touches it) is
       exactly what bread asks for, and it hands back the same shape. *)
    iApply (BR.wp_bread_sconf gs j gl gu gd gk pd pav pu bn
              (fs_view gfs gd dev cov) pidv dev bno dq
              L7 (K - 4)%nat eb b
              _ Vpr HKbr Hbnolt eq_refl Hbnocov eq_refl Hj Hgl HL7a0 HL7a1
              Hbelow
              with "Hcg Hcnt Hextc Hextm Htext Hkd Hpc Hpenv Hbio Hppid Hprocs
                    Hdevi Hdgeom Hdlock Hsl").
    all: try lkbelow.
    iIntros (CID9 Hq9 mB kk bs0 bsd0 d0b) "%Hfacts Hcg Hcnt Hextc Hextm Hpc Hppid Hheld".
    destruct Hfacts as [Hcs1 HmBa0].
    assert (Hpc4e : ret_pc (L7 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.ilock + 0x4e)) by (rewrite HL7ra; pcw).
    iEval (rewrite Hpc4e) in "Hpc".
    pose proof Hcs1 as Hcs1_cs.
    assert (HmBs1 : mB !!! Regidx Rs1 = ip)
      by (rewrite (callee_saved_lookup Hcs1_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HL7s1).
    assert (HmBsp : il_sp m mB).
    { rewrite /il_sp
        (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HL7sp. }
    assert (HmBthr : il_thr6 m mB).
    { intros c Hcs N2 N8 N9 N18.
      rewrite (callee_saved_lookup Hcs1_cs c Hcs).
      exact (HL7thr c Hcs N2 N8 N9 N18). }
    (* THE COUPLING, through the REGION rather than a caller-held block:
       the handle's machinery half against the payload's [dinode_at] pins
       the buffer's bytes to [diblk_bytes ds] AND names this inum's slot.
       That one move is v1's [fs_chalf] premise, its [diblk_wf] premise and
       its conditional slot-agreement premise, all three (§11.3). *)
    iEval (rewrite /bio_locked) in "Hheld".
    iDestruct (iu_held_k with "Hheld") as %Hkk.
    iDestruct (bio_held_fs_L with "Hheld") as "[HL Hbackl]".
    iEval (rewrite Hbno) in "HL".
    iApply fupd_wp.
    (* THE BLOCK, FRAGMENT-FREE.  §16.4's fill does not know which record is
       its own until it has decoded the buffer, because the marker shape
       carries none -- so the coupling comes through [ireg_read_blk], which
       needs only the machinery half, and the record is the slot the inum's
       arithmetic lands on. *)
    iMod (ireg_read_blk ⊤ gi gfs inodestart nib (ireg_bi inum) bs0
            ltac:(solve_ndisj) logN_top (ireg_bi_lt inum nib Hinlt) with "Hireg [HL]")
      as "(%Hdsx & HL)".
    { rewrite -(ireg_bi_iblock inum inodestart). iExact "HL". }
    iEval (rewrite -(ireg_bi_iblock inum inodestart)) in "HL".
    destruct Hdsx as (ds & Hdswf0 & Hbs0).
    subst bs0.
    destruct Hdswf0 as [Hdslen Hdsall].
    assert (Hdswf : diblk_wf ds) by (split; assumption).
    pose (dn := ds !!! islot inum).
    assert (Hagr : ds !!! islot inum = dn) by reflexivity.
    clearbody dn.
    (* NOW the pool entry's shape matters, and there are THREE cases, not
       two (§16.4): the allocated bundle (unchanged); a MARKER over a type-0
       record, which is the free inode ilock panics on; and a MARKER over a
       NONZERO type, which is ialloc's claim -- the fragment is still in the
       region and [ireg_withdraw] takes it out, [fresh_shape] in hand.  The
       marker is what makes that exhaustive: it refutes the region's OUT arm
       outright, so no itable-wide uniqueness argument is needed. *)
    iAssert (|={⊤}=>
               ((IBLOCK inum inodestart) ↪[fs_cache gfs]{#(1/2)} (diblk_bytes ds)) ∗
               ((dinode_at gi inum dn ∗
                 ireg_wd_back o g (bv_unsigned inum) ∗
                 (∃ (fl : bool) (bm : blkmap) (data : nat -> list (bv 8)),
                    ⌜fl = true -> fresh_shape dn⌝ ∗
                    ⌜ilk_post o fl dn⌝ ∗
                    ⌜inode_ok cov logstart dn bm data⌝ ∗
                    (* the three record-only facts [inode_ok] does not carry
                       (durable-disk 2b-inode-3).  The pool arm reads them
                       off its own [inode_owned_era]; the claim box gets the
                       type enumeration out of the region ((L5), which
                       [ireg_withdraw] now pays) and the other two out of
                       [fresh_shape]. *)
                    ⌜inode_rec_local dn⌝ ∗
                    ⌜dir_ok icfg_nib dn data⌝ ∗
                    ⌜dir_dots_ix (bv_unsigned inum) dn data⌝ ∗
                    ⌜dir_orphan_clean dn data⌝ ∗
                    ⌜dir_uniq dn data⌝ ∗
                    dlinks gfs (bv_unsigned inum) dn bm data ∗
                    ind_res gfs bm ∗ inode_blocks gfs bm data ∗
                    (* the CONTENTS HOLD, TIED to the record the fill just
                       decoded (namei-pinned-lookup.md §9 W3).  The pool arm
                       carries it tied already and transfers it; the CLAIM-BOX
                       arm carries it untied and [dv_set]s it to the fresh
                       record's own (empty) contents here. *)
                    dv_ride (bv_unsigned inum) (dv_of dn data) ∗
                    (* ...and the PER-FILE contents hold beside it (N-5.2A):
                       the pool arm transfers it tied, the claim-box arm
                       [fv_set_rt]s its untied one to the fresh record's own
                       (empty) bytes. *)
                    fv_ride (bv_unsigned inum) (fv_of dn data) ∗
                    (* ...and the ERA'S ABSTRACT VALUE, at the node the fill
                       is about to park (durable-disk 2b-inode-3).  The pool
                       arm carries it TIED (inside
                       [FsStateEra.inode_owned_era]) and transfers it; the
                       CLAIM-BOX arm carries it untied on the marker and
                       retags it here, with the same one-line move the two
                       contents holds make. *)
                    top_frag (fs_gamma_L gfs) (bv_unsigned inum)
                             (era_node dn bm data)))
                ∨ ⌜bv_unsigned (di_type dn) = 0⌝))%I
      with "[Hpool HL Hcl]" as ">[HL Hrest]".
    { (* NO PEEL HERE ANY MORE (iclaim-ledger.md §3.5 item 7).  OPTION A
         (b)(ii)'s redeem -- [ipool_shape_to_np] -- happened once, at the
         RECYCLE that cached this entry, and what the unloaded payload holds
         from then on IS the Timeless 2-arm [ipool_shape_np].  Keeping the
         peel here would ask the fill for the licence and the region open the
         recycle already paid, and would ask it to produce a second
         [icnt_half z 0] for an inum whose count is 1. *)
      rewrite /ipool_shape_np. iDestruct "Hpool" as "[Hal | Hmk]".
      - iDestruct "Hal" as (dn0 bm0 data0)
          "(%Hok0 & %Hdok0 & %Hddix0 & %Hdoc0 & %Hduq0 & Hdlk0 & Hera & Hdv & Hfv)".
        (* durable-disk 2b-inode-3: the pool's allocated arm owns the era
           bundle; the fill takes it apart into the three resources it used
           to hold separately plus the abstract value. *)
        iDestruct (inode_owned_era_local with "Hera") as %Hloc0.
        iDestruct (inode_owned_era_era_node_to gfs gi inum dn0 bm0 data0
                     (node_shape_ok_of_inode_ok cov logstart dn0 bm0 data0 Hok0)
                     with "Hera") as "(Hdn & Hind & Hblk & Htop)".
        pose proof (inode_rec_local_of (bv_unsigned inum)
                      (era_node dn0 bm0 data0) Hloc0) as Hrl0.
        iMod (ireg_read ⊤ gi gfs inodestart nib inum dn0
                (IBLOCK inum inodestart) (diblk_bytes ds)
                ltac:(solve_ndisj) logN_top Hinlt eq_refl with "Hireg Hdn HL")
          as "(%Hex & Hdn & HL)".
        destruct Hex as (ds1 & Hwf1 & Hbs1 & Hagr1).
        assert (Hds1 : ds1 = ds)
          by exact (diblk_bytes_inj ds1 ds Hwf1 Hdswf (eq_sym Hbs1)).
        subst ds1. rewrite Hagr in Hagr1. subst dn0.
        (* RULING C' (iclaim-ledger.md §5'''''): THIS ARM REFUTES [ClaimK].
           A pool bundle holds the inum's [dinode_at], i.e. the record is
           OUT of the region -- and while an [iclaim] is outstanding the
           record is IN it ([InodeRegion.ireg_claim_no_out]).  So a
           claimant's fill cannot land here, which is half of why its post
           can pin [filled = true].  The other two indices owe nothing: the
           plain unit is returned untouched and the one-shot never got
           here at all. *)
        iAssert (|={⊤}=> dinode_at gi inum dn
                         ∗ ireg_wd_back o g (bv_unsigned inum)
                         ∗ ⌜ilk_post o false dn⌝)%I
          with "[Hdn Hcl]" as ">(Hdn & Hwb & %Hpost0)".
        { destruct o as [tyc | | tys].
          - iDestruct "Hcl" as "[Hcl _]".
            iMod (ireg_claim_no_out ⊤ gi gfs inodestart nib inum dn tyc
                    ltac:(solve_ndisj) Hinlt with "Hireg Hdn Hcl") as %[].
          - iModIntro. iSplitL "Hdn"; [iExact "Hdn" |].
            iSplitL "Hcl"; [iExact "Hcl" |]. iPureIntro. exact I.
          - iModIntro. iSplitL "Hdn"; [iExact "Hdn" |].
            iSplitL "Hcl"; [iExact "Hcl" |]. iPureIntro. reflexivity. }
        iModIntro. iFrame "HL". iLeft. iFrame "Hdn Hwb".
        (* THE ORDINARY FILL: the pool's allocated bundle, whose record has
           real size and real blocks -- [fresh_shape] is FALSE here, which
           is why the indicator is a boolean and not a fact. *)
        iExists false, bm0, data0.
        iSplitR; [iPureIntro; discriminate |].
        iSplitR; [iPureIntro; exact Hpost0 |].
        iSplitR; [iPureIntro; exact Hok0 |].
        iSplitR; [iPureIntro; exact Hrl0 |].
        iSplitR; [iPureIntro; exact Hdok0 |].
        iSplitR; [iPureIntro; exact Hddix0 |].
        iSplitR; [iPureIntro; exact Hdoc0 |].
        iSplitR; [iPureIntro; exact Hduq0 |].
        iSplitL "Hdlk0"; [iExact "Hdlk0" |]. iFrame.
      - iDestruct "Hmk" as "[Hmk [Hdv [Hfv Htop]]]".
        destruct (decide (bv_unsigned (di_type dn) = 0)) as [Ht0 | Htnz].
        + iModIntro. iFrame "HL". iRight. iPureIntro. exact Ht0.
        + iMod (ireg_withdraw ⊤ gi gfs inodestart nib inum ds
                  (IBLOCK inum inodestart) (diblk_bytes ds) o g
                  ltac:(solve_ndisj) logN_top Hfills Hinlt eq_refl Hdswf eq_refl
                  ltac:(rewrite Hagr; exact Htnz)
                  with "Hireg Hmk Hcl HL")
            as "(%Hfresh & %Hty & %Htyok & Hwb & Hdn & HL)".
          rewrite Hagr in Hfresh. rewrite Hagr in Hty.
          rewrite Hagr in Htyok.
          iEval (rewrite Hagr) in "Hdn".
          pose proof Hfresh as Hfr0.
          destruct Hfresh as (Hfty & Hfsz & Hfad & _).
          (* §16.4's CLAIM BOX: the marker arm's hold is untied, and the
             record the withdraw just handed over has size 0, so its
             contents are [∅] -- one free own-update (§9 Revision 2). *)
          iDestruct "Hdv" as (e0) "Hdv".
          iDestruct "Hfv" as (b0) "Hfv".
          iDestruct "Htop" as (n0) "Htop".
          (* the marker arm's fragment is untied; retag it at the claim
             box's own node, exactly as the two contents holds are set *)
          iMod (ireg_top_retag ⊤ gfs (bv_unsigned inum) n0
                  (era_node dn bm_empty (fun _ => replicate BSIZE (bv_0 8)))
                  ltac:(solve_ndisj)
                  with "[Hireg] Htop") as "Htop".
          { iApply (ireg_inv_ftop with "Hireg"). }
          iMod (dvw_set_rt ⊤ gi gfs inodestart nib (bv_unsigned inum) e0
                  (dv_of dn (fun _ => replicate BSIZE (bv_0 8))) b0
                  (fv_of dn (fun _ => replicate BSIZE (bv_0 8)))
                  ltac:(solve_ndisj) with "Hireg Hdv Hfv") as "[Hdv Hfv]".
          iModIntro. iFrame "HL". iLeft. iFrame "Hdn Hwb".
          (* §16.4's CLAIM BOX: [ireg_withdraw] just PAID [fresh_shape], and
             this is where it now leaves the function instead of being spent
             on [inode_ok]/[dir_ok] and dropped. *)
          iExists true, bm_empty, (fun _ => replicate BSIZE (bv_0 8)).
          iSplitR; [iPureIntro; intros _; exact Hfr0 |].
          (* THE PAYOUT, PER INDEX: at [ClaimK] this is [create_fresh_ty]'s
             own conjunct -- the fill IS forced and the record IS the one
             the claim wrote. *)
          iSplitR; [iPureIntro; exact (ilk_post_fill o dn Hfills Hty) |].
          iSplitR.
          { iPureIntro. rewrite /inode_ok. split_and!.
            - exact (bm_empty_wf cov logstart).
            - apply bm_covers_nonpos. rewrite Hfsz. lia.
            - rewrite Hfad il_bmcells_empty. reflexivity.
            - exact Hfty.
            - rewrite Hfsz.
              pose proof (Nat2Z.is_nonneg MAXFILE).
              pose proof (Nat2Z.is_nonneg BSIZE). nia.
            - apply bm_empty_holes. intros i. reflexivity.
            - exact inode_sized_zero. }
          (* the claim box's three record-only facts: the type enumeration
             is the region's (L5), and [fresh_shape] gives the other two --
             a zero count and a size of 0, which no directory granularity
             clause can fail on. *)
          iSplitR.
          { iPureIntro. split_and!.
            - exact Htyok.
            - rewrite (fresh_shape_nlink dn Hfr0). lia.
            - intros _. rewrite Hfsz. by exists 0. }
          iSplitR; [iPureIntro; exact (dir_ok_size_zero icfg_nib dn _ Hfsz) |].
          (* a claim box is an ORPHAN by [fresh_shape]'s own last conjunct,
             which is the one discharge the ".." clause needs here *)
          iSplitR; [iPureIntro;
                    exact (dir_dots_ix_orphan (bv_unsigned inum) dn _
                             (fresh_shape_nlink dn Hfr0)) |].
          (* ...and the COMPLEMENT clause is free at the same box, from the
             other half of [fresh_shape]: a claim box has size 0, so it has
             no records at all and [dir_dots_only] is vacuous.  The two dot
             clauses partition the directory case and the claim box happens
             to land in both halves' easy corner. *)
          iSplitR; [iPureIntro;
                    exact (dir_orphan_clean_size_zero dn _ Hfsz) |].
          (* ...and the UNIQUENESS clause, at the same corner and for the
             same reason: no records at all ([dir_nrec 0 = 0]). *)
          iSplitR; [iPureIntro; exact (dir_uniq_size_zero dn _ Hfsz) |].
          (* §16.4's CLAIM BOX has [fresh_shape], i.e. size 0, so the twin
             collapses to [emp] exactly where [dir_ok_size_zero] makes the
             pure conjunct vacuous -- the resource half of §19.4's
             "[ireg_withdraw] already pays [fresh_shape]". *)
          (* ...and V2's count clause is the SAME conjunct of [fresh_shape]
             the ".." discharge above reads: a claim box is an orphan, and
             [0 <= 1]. *)
          iSplitR; [iApply (dlinks_size_zero gfs (bv_unsigned inum) dn _ _ Hfsz
                              ltac:(rewrite (fresh_shape_nlink dn Hfr0); lia)) |].
          iSplitR "Hdv Hfv Htop"; [iApply il_ind_res_empty |].
          iSplitR "Hdv Hfv Htop"; [iApply il_blocks_empty |].
          iSplitL "Hdv"; [iExact "Hdv" |].
          iSplitL "Hfv"; [iExact "Hfv" | iExact "Htop"]. }
    (* THE FILL SPENDS THE GENERATION'S ONE-SHOT (design §17.6 (3)), at the
       only instruction in this kernel that knows [di_type]: the record has
       just been decoded off the buffer, and [dn] is fixed for the rest of
       this arm.  It is spent HERE rather than on each completing branch
       because the [ip->type == 0] branch diverges through
       [SpecPanic]'s own contract and owes nothing either way -- one [iMod]
       covers both the pool bundle and §16.4's claim box. *)
    iMod (ity_shoot g (di_type dn) with "Hpend") as "#Hshot".
    iModIntro.
    iEval (rewrite -Hbno) in "HL".
    iDestruct ("Hbackl" with "HL") as "Hheld".
    assert (Hslotlen : (islot inum < length ds)%nat)
      by (rewrite Hdslen; exact Hslotlt).
    (* the addrs LENGTH -- v1 got it from [inode_ok]; the region's own
       well-formedness gives it on BOTH pool shapes *)
    assert (Hdnwf : dinode_wf dn).
    { rewrite -Hagr.
      apply (Forall_lookup_total_1 dinode_wf ds (islot inum) Hdsall Hslotlen). }
    assert (Hdalen : length (di_addrs dn) = 13%nat)
      by (unfold dinode_wf in Hdnwf; exact Hdnwf).
    assert (Hins : <[islot inum := dn]> ds = ds).
    { apply list_insert_id. rewrite -Hagr.
      apply list_lookup_lookup_total_lt. exact Hslotlen. }
    iDestruct (iu_held_swap with "Hheld") as "[Hbuf Hheldback]".
    iDestruct (iu_buf_bytes (bpa kk) bno (mword_of_int 0 : mword 32) ds Hdswf
                 with "Hbuf") as "[Hby Hbyback]".
    assert (Hslotal : dislot_align
              (pa_add (b_data (bnode kk)) (64 * islot inum)%nat)).
    { rewrite /dislot_align.
      assert (E0 : (64 * islot inum)%nat = (64 * islot inum + 0)%nat) by lia.
      split_and!.
      - rewrite E0. apply iu_align; [exact Hkk | exact Hslotlt | lia | left; reflexivity
                                   | reflexivity].
      - rewrite pa_add_add. apply iu_align;
          [exact Hkk | exact Hslotlt | lia | left; reflexivity | reflexivity].
      - rewrite pa_add_add. apply iu_align;
          [exact Hkk | exact Hslotlt | lia | left; reflexivity | reflexivity].
      - rewrite pa_add_add. apply iu_align;
          [exact Hkk | exact Hslotlt | lia | left; reflexivity | reflexivity].
      - rewrite pa_add_add. apply iu_align;
          [exact Hkk | exact Hslotlt | lia | right; reflexivity | reflexivity]. }
    iDestruct (diblk_slot_acc (b_data (bpa kk)) ds (islot inum)
                 Hdswf Hslotlt Hslotal with "Hby") as "[Hslot Hslotback]".
    iEval (rewrite Hagr) in "Hslot".
    iDestruct "Hslot" as "(Hd0 & Hd2 & Hd4 & Hd6 & Hd8 & Hda)".
    (* ===== +0x4e c.mv s2,a0 : s2 := bp ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ilock + 0x4e)) Rs2 Ra0
              mB (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (ili_4e with "Htext"). }
    iIntros (CID10 Hq10) "Hcg Hpc".
    set (B1 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mB Ra0))]> mB).
    assert (HB1s2 : B1 !!! Regidx Rs2 = bnode kk).
    { rewrite /B1 upd_eq. rgne. rewrite HmBa0. apply add_vec_zero_l. }
    assert (HB1a0 : B1 !!! Regidx Ra0 = bnode kk)
      by (rewrite /B1 upd_ne; [exact HmBa0 | nz]).
    assert (HB1s1 : B1 !!! Regidx Rs1 = ip)
      by (rewrite /B1 upd_ne; [exact HmBs1 | nz]).
    assert (HB1sp : il_sp m B1)
      by (rewrite /il_sp /B1 upd_ne; [exact HmBsp | nz]).
    assert (HB1thr : il_thr6 m B1).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /B1 upd_ne; [| regne]. exact (HmBthr c Hcs N2 N8 N9 N18). }
    assert (Hpp50 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x4e) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x50)) by pcw.
    iEval (rewrite Hpp50) in "Hpc".
    (* ===== +0x50 addi a1,a0,88 : a1 := bp->data ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.ilock + 0x50)) Ra1 Ra0
              (mword_of_int 88 : mword 12) B1 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (ili_50 with "Htext"). }
    iIntros (CID11 Hq11) "Hcg Hpc".
    set (B2 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (rget B1 Ra0)
                     (sign_extend' 64 (mword_of_int 88 : mword 12)))]> B1).
    assert (HB2a1 : B2 !!! Regidx Ra1 = b_data (bnode kk)).
    { rewrite /B2 upd_eq. rgne. rewrite HB1a0. apply iu_data_addr. }
    assert (HB2s2 : B2 !!! Regidx Rs2 = bnode kk)
      by (rewrite /B2 upd_ne; [exact HB1s2 | nz]).
    assert (HB2s1 : B2 !!! Regidx Rs1 = ip)
      by (rewrite /B2 upd_ne; [exact HB1s1 | nz]).
    assert (HB2sp : il_sp m B2)
      by (rewrite /il_sp /B2 upd_ne; [exact HB1sp | nz]).
    assert (HB2thr : il_thr6 m B2).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /B2 upd_ne; [| regne]. exact (HB1thr c Hcs N2 N8 N9 N18). }
    assert (Hpp54 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x50) : mword 64) 4
                    = mword_of_int (KernelSyms.ilock + 0x54)) by pcw.
    iEval (rewrite Hpp54) in "Hpc".
    (* ===== +0x54 c.lw a5,4(s1) : a5 := ip->inum ===== *)
    assert (Hinadr2 : add_vec (rget B2 Rs1)
                        (sign_extend' 64 (mword_of_int 4 : mword 12)) = i_inum ip).
    { rgne. rewrite HB2s1. reflexivity. }
    iEval (rewrite -Hinadr2) in "Hinumc".
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.ilock + 0x54)) Ra5 Rs1
              (mword_of_int 4 : mword 12) B2 (K - 4)%nat inum b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hinumc").
    { iApply (ili_54 with "Htext"). }
    iIntros (CID12 Hq12) "Hcg Hpc Hinumc".
    iEval (rewrite Hinadr2) in "Hinumc".
    set (B3 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 inum)]> B2).
    assert (HB3a5 : B3 !!! Regidx Ra5 = (sign_extend' 64 inum : mword 64))
      by (rewrite /B3; apply upd_eq).
    assert (HB3a1 : B3 !!! Regidx Ra1 = b_data (bnode kk))
      by (rewrite /B3 upd_ne; [exact HB2a1 | nz]).
    assert (HB3s2 : B3 !!! Regidx Rs2 = bnode kk)
      by (rewrite /B3 upd_ne; [exact HB2s2 | nz]).
    assert (HB3s1 : B3 !!! Regidx Rs1 = ip)
      by (rewrite /B3 upd_ne; [exact HB2s1 | nz]).
    assert (HB3sp : il_sp m B3)
      by (rewrite /il_sp /B3 upd_ne; [exact HB2sp | nz]).
    assert (HB3thr : il_thr6 m B3).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /B3 upd_ne; [| regne]. exact (HB2thr c Hcs N2 N8 N9 N18). }
    assert (Hpp56 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x54) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x56)) by pcw.
    iEval (rewrite Hpp56) in "Hpc".
    (* ===== +0x56 c.andi a5,15 : a5 := inum % IPB ===== *)
    iApply (wp_candi_s_sconf (mword_of_int (KernelSyms.ilock + 0x56)) Ra5
              (mword_of_int 15 : mword 6) B3 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (ili_56 with "Htext"). }
    iIntros (CID13 Hq13) "Hcg Hpc".
    set (B4 := <[Regidx Ra5 := regval_into_reg
                  (and_vec (rget B3 Ra5)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 15 : mword 6))))]> B3).
    assert (HB4a5 : B4 !!! Regidx Ra5
                    = (mword_of_int (Z.of_nat (islot inum)) : mword 64)).
    { rewrite /B4 upd_eq. rgne. rewrite HB3a5 iu_andi15 iu_sext_mod16 Hslotz.
      reflexivity. }
    assert (HB4a1 : B4 !!! Regidx Ra1 = b_data (bnode kk))
      by (rewrite /B4 upd_ne; [exact HB3a1 | nz]).
    assert (HB4s2 : B4 !!! Regidx Rs2 = bnode kk)
      by (rewrite /B4 upd_ne; [exact HB3s2 | nz]).
    assert (HB4s1 : B4 !!! Regidx Rs1 = ip)
      by (rewrite /B4 upd_ne; [exact HB3s1 | nz]).
    assert (HB4sp : il_sp m B4)
      by (rewrite /il_sp /B4 upd_ne; [exact HB3sp | nz]).
    assert (HB4thr : il_thr6 m B4).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /B4 upd_ne; [| regne]. exact (HB3thr c Hcs N2 N8 N9 N18). }
    assert (Hpp58 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x56) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x58)) by pcw.
    iEval (rewrite Hpp58) in "Hpc".
    (* ===== +0x58 c.slli a5,0x6 ===== *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.ilock + 0x58)) (Regidx Ra5) Ra5
              (mword_of_int 6 : mword 6) B4 (K - 4)%nat b
              ltac:(reflexivity) ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (ili_58 with "Htext"). }
    iIntros (CID14 Hq14) "Hcg Hpc".
    set (B5 := <[Regidx Ra5 := regval_into_reg
                  (shift_bits_left (rget B4 Ra5)
                     (subrange_vec_dec (mword_of_int 6 : mword 6)
                        (Z.sub log2_xlen 1) 0))]> B4).
    assert (HB5a5 : B5 !!! Regidx Ra5
                    = (mword_of_int (64 * Z.of_nat (islot inum)) : mword 64)).
    { rewrite /B5 upd_eq. rgne. rewrite HB4a5. apply iu_slli6; lia. }
    assert (HB5a1 : B5 !!! Regidx Ra1 = b_data (bnode kk))
      by (rewrite /B5 upd_ne; [exact HB4a1 | nz]).
    assert (HB5s2 : B5 !!! Regidx Rs2 = bnode kk)
      by (rewrite /B5 upd_ne; [exact HB4s2 | nz]).
    assert (HB5s1 : B5 !!! Regidx Rs1 = ip)
      by (rewrite /B5 upd_ne; [exact HB4s1 | nz]).
    assert (HB5sp : il_sp m B5)
      by (rewrite /il_sp /B5 upd_ne; [exact HB4sp | nz]).
    assert (HB5thr : il_thr6 m B5).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /B5 upd_ne; [| regne]. exact (HB4thr c Hcs N2 N8 N9 N18). }
    assert (Hpp5a : add_vec_int (mword_of_int (KernelSyms.ilock + 0x58) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x5a)) by pcw.
    iEval (rewrite Hpp5a) in "Hpc".
    (* ===== +0x5a c.add a1,a1,a5 : a1 := dip ===== *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.ilock + 0x5a)) Ra1 Ra5
              B5 (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (ili_5a with "Htext"). }
    iIntros (CID15 Hq15) "Hcg Hpc".
    set (B6 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (rget B5 Ra1) (rget B5 Ra5))]> B5).
    assert (HB6a1 : B6 !!! Regidx Ra1
                    = pa_add (b_data (bnode kk)) (64 * islot inum)%nat).
    { rewrite /B6 upd_eq. rgne. rgne. rewrite HB5a1 HB5a5. apply iu_slot_addr. }
    assert (HB6s2 : B6 !!! Regidx Rs2 = bnode kk)
      by (rewrite /B6 upd_ne; [exact HB5s2 | nz]).
    assert (HB6s1 : B6 !!! Regidx Rs1 = ip)
      by (rewrite /B6 upd_ne; [exact HB5s1 | nz]).
    assert (HB6sp : il_sp m B6)
      by (rewrite /il_sp /B6 upd_ne; [exact HB5sp | nz]).
    assert (HB6thr : il_thr6 m B6).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /B6 upd_ne; [| regne]. exact (HB5thr c Hcs N2 N8 N9 N18). }
    assert (Hpp5c : add_vec_int (mword_of_int (KernelSyms.ilock + 0x5a) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x5c)) by pcw.
    iEval (rewrite Hpp5c) in "Hpc".
    (* ================= the five field copies, disk -> inode ============= *)
    (* ---- type : lh a5,0(a1) ; sh a5,68(s1) ---- *)
    assert (Hs0adr : add_vec (rget B6 Ra1) (sign_extend' 64 (mword_of_int 0 : mword 12))
                     = pa_add (b_data (bpa kk)) (64 * islot inum)%nat).
    { rgne. rewrite HB6a1. apply iu_off0. }
    iEval (rewrite -Hs0adr) in "Hd0".
    iApply (wp_lh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.ilock + 0x5c)) Ra5 Ra1
              (mword_of_int 0 : mword 12) B6 (K - 4)%nat (di_type dn : mword 16) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hd0").
    { iApply (ili_5c with "Htext"). }
    iIntros (CID16 Hq16) "Hcg Hpc Hd0".
    iEval (rewrite Hs0adr) in "Hd0".
    set (F0 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (di_type dn : mword 16))]> B6).
    assert (HF0a5 : F0 !!! Regidx Ra5 = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
      by (rewrite /F0; apply upd_eq).
    assert (HF0a1 : F0 !!! Regidx Ra1
                    = pa_add (b_data (bnode kk)) (64 * islot inum)%nat)
      by (rewrite /F0 upd_ne; [exact HB6a1 | nz]).
    assert (HF0s2 : F0 !!! Regidx Rs2 = bnode kk)
      by (rewrite /F0 upd_ne; [exact HB6s2 | nz]).
    assert (HF0s1 : F0 !!! Regidx Rs1 = ip)
      by (rewrite /F0 upd_ne; [exact HB6s1 | nz]).
    assert (HF0sp : il_sp m F0)
      by (rewrite /il_sp /F0 upd_ne; [exact HB6sp | nz]).
    assert (HF0thr : il_thr6 m F0).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /F0 upd_ne; [| regne]. exact (HB6thr c Hcs N2 N8 N9 N18). }
    assert (Hpp60 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x5c) : mword 64) 4
                    = mword_of_int (KernelSyms.ilock + 0x60)) by pcw.
    iEval (rewrite Hpp60) in "Hpc".
    assert (Htyadr : add_vec (rget F0 Rs1)
                       (sign_extend' 64 (mword_of_int 68 : mword 12)) = i_type ip).
    { rgne. rewrite HF0s1. reflexivity. }
    iEval (rewrite -Htyadr) in "Hmty".
    iApply (wp_sh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.ilock + 0x60)) Ra5 Rs1
              (mword_of_int 68 : mword 12) F0 (K - 4)%nat
              (di_type d0 : mword 16) b with "Hcg Hpc [] Hmty").
    { iApply (ili_60 with "Htext"). }
    iIntros (CID17 Hq17) "Hcg Hpc Hmty".
    iEval (rewrite Htyadr; rgne; rewrite HF0a5 trunc16_sext64) in "Hmty".
    assert (Hpp64 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x60) : mword 64) 4
                    = mword_of_int (KernelSyms.ilock + 0x64)) by pcw.
    iEval (rewrite Hpp64) in "Hpc".
    (* ---- major : lh a5,2(a1) ; sh a5,70(s1) ---- *)
    assert (Hs2adr : add_vec (rget F0 Ra1) (sign_extend' 64 (mword_of_int 2 : mword 12))
                     = pa_add (pa_add (b_data (bpa kk)) (64 * islot inum)%nat) 2).
    { rgne. rewrite HF0a1. apply (iu_disp _ 2 2%nat); [lia | lia | reflexivity]. }
    iEval (rewrite -Hs2adr) in "Hd2".
    iApply (wp_lh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.ilock + 0x64)) Ra5 Ra1
              (mword_of_int 2 : mword 12) F0 (K - 4)%nat (di_major dn : mword 16) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hd2").
    { iApply (ili_64 with "Htext"). }
    iIntros (CID18 Hq18) "Hcg Hpc Hd2".
    iEval (rewrite Hs2adr) in "Hd2".
    set (F1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (di_major dn : mword 16))]> F0).
    assert (HF1a5 : F1 !!! Regidx Ra5 = (sign_extend' 64 (di_major dn : mword 16) : mword 64))
      by (rewrite /F1; apply upd_eq).
    assert (HF1a1 : F1 !!! Regidx Ra1
                    = pa_add (b_data (bnode kk)) (64 * islot inum)%nat)
      by (rewrite /F1 upd_ne; [exact HF0a1 | nz]).
    assert (HF1s2 : F1 !!! Regidx Rs2 = bnode kk)
      by (rewrite /F1 upd_ne; [exact HF0s2 | nz]).
    assert (HF1s1 : F1 !!! Regidx Rs1 = ip)
      by (rewrite /F1 upd_ne; [exact HF0s1 | nz]).
    assert (HF1sp : il_sp m F1)
      by (rewrite /il_sp /F1 upd_ne; [exact HF0sp | nz]).
    assert (HF1thr : il_thr6 m F1).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /F1 upd_ne; [| regne]. exact (HF0thr c Hcs N2 N8 N9 N18). }
    assert (Hpp68 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x64) : mword 64) 4
                    = mword_of_int (KernelSyms.ilock + 0x68)) by pcw.
    iEval (rewrite Hpp68) in "Hpc".
    assert (Hmjadr : add_vec (rget F1 Rs1)
                       (sign_extend' 64 (mword_of_int 70 : mword 12)) = i_major ip).
    { rgne. rewrite HF1s1. reflexivity. }
    iEval (rewrite -Hmjadr) in "Hmmaj".
    iApply (wp_sh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.ilock + 0x68)) Ra5 Rs1
              (mword_of_int 70 : mword 12) F1 (K - 4)%nat
              (di_major d0 : mword 16) b with "Hcg Hpc [] Hmmaj").
    { iApply (ili_68 with "Htext"). }
    iIntros (CID19 Hq19) "Hcg Hpc Hmmaj".
    iEval (rewrite Hmjadr; rgne; rewrite HF1a5 trunc16_sext64) in "Hmmaj".
    assert (Hpp6c : add_vec_int (mword_of_int (KernelSyms.ilock + 0x68) : mword 64) 4
                    = mword_of_int (KernelSyms.ilock + 0x6c)) by pcw.
    iEval (rewrite Hpp6c) in "Hpc".
    (* ---- minor : lh a5,4(a1) ; sh a5,72(s1) ---- *)
    assert (Hs4adr : add_vec (rget F1 Ra1) (sign_extend' 64 (mword_of_int 4 : mword 12))
                     = pa_add (pa_add (b_data (bpa kk)) (64 * islot inum)%nat) 4).
    { rgne. rewrite HF1a1. apply (iu_disp _ 4 4%nat); [lia | lia | reflexivity]. }
    iEval (rewrite -Hs4adr) in "Hd4".
    iApply (wp_lh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.ilock + 0x6c)) Ra5 Ra1
              (mword_of_int 4 : mword 12) F1 (K - 4)%nat (di_minor dn : mword 16) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hd4").
    { iApply (ili_6c with "Htext"). }
    iIntros (CID20 Hq20) "Hcg Hpc Hd4".
    iEval (rewrite Hs4adr) in "Hd4".
    set (F2 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (di_minor dn : mword 16))]> F1).
    assert (HF2a5 : F2 !!! Regidx Ra5 = (sign_extend' 64 (di_minor dn : mword 16) : mword 64))
      by (rewrite /F2; apply upd_eq).
    assert (HF2a1 : F2 !!! Regidx Ra1
                    = pa_add (b_data (bnode kk)) (64 * islot inum)%nat)
      by (rewrite /F2 upd_ne; [exact HF1a1 | nz]).
    assert (HF2s2 : F2 !!! Regidx Rs2 = bnode kk)
      by (rewrite /F2 upd_ne; [exact HF1s2 | nz]).
    assert (HF2s1 : F2 !!! Regidx Rs1 = ip)
      by (rewrite /F2 upd_ne; [exact HF1s1 | nz]).
    assert (HF2sp : il_sp m F2)
      by (rewrite /il_sp /F2 upd_ne; [exact HF1sp | nz]).
    assert (HF2thr : il_thr6 m F2).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /F2 upd_ne; [| regne]. exact (HF1thr c Hcs N2 N8 N9 N18). }
    assert (Hpp70 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x6c) : mword 64) 4
                    = mword_of_int (KernelSyms.ilock + 0x70)) by pcw.
    iEval (rewrite Hpp70) in "Hpc".
    assert (Hmnadr : add_vec (rget F2 Rs1)
                       (sign_extend' 64 (mword_of_int 72 : mword 12)) = i_minor ip).
    { rgne. rewrite HF2s1. reflexivity. }
    iEval (rewrite -Hmnadr) in "Hmmin".
    iApply (wp_sh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.ilock + 0x70)) Ra5 Rs1
              (mword_of_int 72 : mword 12) F2 (K - 4)%nat
              (di_minor d0 : mword 16) b with "Hcg Hpc [] Hmmin").
    { iApply (ili_70 with "Htext"). }
    iIntros (CID21 Hq21) "Hcg Hpc Hmmin".
    iEval (rewrite Hmnadr; rgne; rewrite HF2a5 trunc16_sext64) in "Hmmin".
    assert (Hpp74 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x70) : mword 64) 4
                    = mword_of_int (KernelSyms.ilock + 0x74)) by pcw.
    iEval (rewrite Hpp74) in "Hpc".
    (* ---- nlink : lh a5,6(a1) ; sh a5,74(s1) ---- *)
    assert (Hs6adr : add_vec (rget F2 Ra1) (sign_extend' 64 (mword_of_int 6 : mword 12))
                     = pa_add (pa_add (b_data (bpa kk)) (64 * islot inum)%nat) 6).
    { rgne. rewrite HF2a1. apply (iu_disp _ 6 6%nat); [lia | lia | reflexivity]. }
    iEval (rewrite -Hs6adr) in "Hd6".
    iApply (wp_lh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.ilock + 0x74)) Ra5 Ra1
              (mword_of_int 6 : mword 12) F2 (K - 4)%nat (di_nlink dn : mword 16) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hd6").
    { iApply (ili_74 with "Htext"). }
    iIntros (CID22 Hq22) "Hcg Hpc Hd6".
    iEval (rewrite Hs6adr) in "Hd6".
    set (F3 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (di_nlink dn : mword 16))]> F2).
    assert (HF3a5 : F3 !!! Regidx Ra5 = (sign_extend' 64 (di_nlink dn : mword 16) : mword 64))
      by (rewrite /F3; apply upd_eq).
    assert (HF3a1 : F3 !!! Regidx Ra1
                    = pa_add (b_data (bnode kk)) (64 * islot inum)%nat)
      by (rewrite /F3 upd_ne; [exact HF2a1 | nz]).
    assert (HF3s2 : F3 !!! Regidx Rs2 = bnode kk)
      by (rewrite /F3 upd_ne; [exact HF2s2 | nz]).
    assert (HF3s1 : F3 !!! Regidx Rs1 = ip)
      by (rewrite /F3 upd_ne; [exact HF2s1 | nz]).
    assert (HF3sp : il_sp m F3)
      by (rewrite /il_sp /F3 upd_ne; [exact HF2sp | nz]).
    assert (HF3thr : il_thr6 m F3).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /F3 upd_ne; [| regne]. exact (HF2thr c Hcs N2 N8 N9 N18). }
    assert (Hpp78 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x74) : mword 64) 4
                    = mword_of_int (KernelSyms.ilock + 0x78)) by pcw.
    iEval (rewrite Hpp78) in "Hpc".
    assert (Hnladr : add_vec (rget F3 Rs1)
                       (sign_extend' 64 (mword_of_int 74 : mword 12)) = i_nlink ip).
    { rgne. rewrite HF3s1. reflexivity. }
    iEval (rewrite -Hnladr) in "Hmnl".
    iApply (wp_sh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.ilock + 0x78)) Ra5 Rs1
              (mword_of_int 74 : mword 12) F3 (K - 4)%nat
              (di_nlink d0 : mword 16) b with "Hcg Hpc [] Hmnl").
    { iApply (ili_78 with "Htext"). }
    iIntros (CID23 Hq23) "Hcg Hpc Hmnl".
    iEval (rewrite Hnladr; rgne; rewrite HF3a5 trunc16_sext64) in "Hmnl".
    assert (Hpp7c : add_vec_int (mword_of_int (KernelSyms.ilock + 0x78) : mword 64) 4
                    = mword_of_int (KernelSyms.ilock + 0x7c)) by pcw.
    iEval (rewrite Hpp7c) in "Hpc".
    (* ---- size : c.lw a5,8(a1) ; c.sw a5,76(s1) ---- *)
    assert (Hs8adr : add_vec (rget F3 Ra1) (sign_extend' 64 (mword_of_int 8 : mword 12))
                     = pa_add (pa_add (b_data (bpa kk)) (64 * islot inum)%nat) 8).
    { rgne. rewrite HF3a1. apply (iu_disp _ 8 8%nat); [lia | lia | reflexivity]. }
    iEval (rewrite -Hs8adr) in "Hd8".
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.ilock + 0x7c)) Ra5 Ra1
              (mword_of_int 8 : mword 12) F3 (K - 4)%nat (di_size dn : mword 32) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hd8").
    { iApply (ili_7c with "Htext"). }
    iIntros (CID24 Hq24) "Hcg Hpc Hd8".
    iEval (rewrite Hs8adr) in "Hd8".
    set (F4 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (di_size dn : mword 32))]> F3).
    assert (HF4a5 : F4 !!! Regidx Ra5 = (sign_extend' 64 (di_size dn : mword 32) : mword 64))
      by (rewrite /F4; apply upd_eq).
    assert (HF4a1 : F4 !!! Regidx Ra1
                    = pa_add (b_data (bnode kk)) (64 * islot inum)%nat)
      by (rewrite /F4 upd_ne; [exact HF3a1 | nz]).
    assert (HF4s2 : F4 !!! Regidx Rs2 = bnode kk)
      by (rewrite /F4 upd_ne; [exact HF3s2 | nz]).
    assert (HF4s1 : F4 !!! Regidx Rs1 = ip)
      by (rewrite /F4 upd_ne; [exact HF3s1 | nz]).
    assert (HF4sp : il_sp m F4)
      by (rewrite /il_sp /F4 upd_ne; [exact HF3sp | nz]).
    assert (HF4thr : il_thr6 m F4).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /F4 upd_ne; [| regne]. exact (HF3thr c Hcs N2 N8 N9 N18). }
    assert (Hpp7e : add_vec_int (mword_of_int (KernelSyms.ilock + 0x7c) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x7e)) by pcw.
    iEval (rewrite Hpp7e) in "Hpc".
    assert (Hszadr : add_vec (rget F4 Rs1)
                       (sign_extend' 64 (mword_of_int 76 : mword 12)) = i_size ip).
    { rgne. rewrite HF4s1. reflexivity. }
    iEval (rewrite -Hszadr) in "Hmsz".
    iApply (wp_csw_s_sconf (mword_of_int (KernelSyms.ilock + 0x7e)) Ra5 Rs1
              (mword_of_int 76 : mword 12) F4 (K - 4)%nat
              (di_size d0 : mword 32) b with "Hcg Hpc [] Hmsz").
    { iApply (ili_7e with "Htext"). }
    iIntros (CID25 Hq25) "Hcg Hpc Hmsz".
    iEval (rewrite Hszadr; rgne; rewrite HF4a5 trunc32_sext64) in "Hmsz".
    assert (Hpp80 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x7e) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x80)) by pcw.
    iEval (rewrite Hpp80) in "Hpc".
    (* ================= the memmove ================= *)
    (* ---- +0x80 li a2,52 ---- *)
    iApply (wp_li4_s_sconf (mword_of_int (KernelSyms.ilock + 0x80)) Ra2
              (mword_of_int 52 : mword 12)
              (mword_of_int (Z.of_nat 52%nat) : mword 64) F4 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (ili_80 with "Htext"). }
    iIntros (CID26 Hq26) "Hcg Hpc".
    set (G0 := <[Regidx Ra2 := regval_into_reg
                  (mword_of_int (Z.of_nat 52%nat) : mword 64)]> F4).
    assert (HG0a2 : G0 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 52%nat) : mword 64))
      by (rewrite /G0; apply upd_eq).
    assert (HG0a1 : G0 !!! Regidx Ra1
                    = pa_add (b_data (bnode kk)) (64 * islot inum)%nat)
      by (rewrite /G0 upd_ne; [exact HF4a1 | nz]).
    assert (HG0s2 : G0 !!! Regidx Rs2 = bnode kk)
      by (rewrite /G0 upd_ne; [exact HF4s2 | nz]).
    assert (HG0s1 : G0 !!! Regidx Rs1 = ip)
      by (rewrite /G0 upd_ne; [exact HF4s1 | nz]).
    assert (HG0sp : il_sp m G0)
      by (rewrite /il_sp /G0 upd_ne; [exact HF4sp | nz]).
    assert (HG0thr : il_thr6 m G0).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /G0 upd_ne; [| regne]. exact (HF4thr c Hcs N2 N8 N9 N18). }
    assert (Hpp84 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x80) : mword 64) 4
                    = mword_of_int (KernelSyms.ilock + 0x84)) by pcw.
    iEval (rewrite Hpp84) in "Hpc".
    (* ---- +0x84 c.addi a1,a1,12 ---- *)
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.ilock + 0x84)) Ra1
              (mword_of_int 12 : mword 6) G0 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (ili_84 with "Htext"). }
    iIntros (CID27 Hq27) "Hcg Hpc".
    set (G1 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (rget G0 Ra1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 12 : mword 6))))]> G0).
    assert (HG1a1 : G1 !!! Regidx Ra1
                    = pa_add (pa_add (b_data (bpa kk)) (64 * islot inum)%nat) 12).
    { rewrite /G1 upd_eq. rgne. rewrite HG0a1. apply il_addi12. }
    assert (HG1a2 : G1 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 52%nat) : mword 64))
      by (rewrite /G1 upd_ne; [exact HG0a2 | nz]).
    assert (HG1s2 : G1 !!! Regidx Rs2 = bnode kk)
      by (rewrite /G1 upd_ne; [exact HG0s2 | nz]).
    assert (HG1s1 : G1 !!! Regidx Rs1 = ip)
      by (rewrite /G1 upd_ne; [exact HG0s1 | nz]).
    assert (HG1sp : il_sp m G1)
      by (rewrite /il_sp /G1 upd_ne; [exact HG0sp | nz]).
    assert (HG1thr : il_thr6 m G1).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /G1 upd_ne; [| regne]. exact (HG0thr c Hcs N2 N8 N9 N18). }
    assert (Hpp86 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x84) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x86)) by pcw.
    iEval (rewrite Hpp86) in "Hpc".
    (* ---- +0x86 addi a0,s1,80 ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.ilock + 0x86)) Ra0 Rs1
              (mword_of_int 80 : mword 12) G1 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (ili_86 with "Htext"). }
    iIntros (CID28 Hq28) "Hcg Hpc".
    set (G2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (rget G1 Rs1)
                     (sign_extend' 64 (mword_of_int 80 : mword 12)))]> G1).
    assert (HG2a0 : G2 !!! Regidx Ra0 = i_addr ip 0).
    { rewrite /G2 upd_eq. rgne. rewrite HG1s1. apply iu_addrs0. }
    assert (HG2a1 : G2 !!! Regidx Ra1
                    = pa_add (pa_add (b_data (bpa kk)) (64 * islot inum)%nat) 12)
      by (rewrite /G2 upd_ne; [exact HG1a1 | nz]).
    assert (HG2a2 : G2 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 52%nat) : mword 64))
      by (rewrite /G2 upd_ne; [exact HG1a2 | nz]).
    assert (HG2s2 : G2 !!! Regidx Rs2 = bnode kk)
      by (rewrite /G2 upd_ne; [exact HG1s2 | nz]).
    assert (HG2s1 : G2 !!! Regidx Rs1 = ip)
      by (rewrite /G2 upd_ne; [exact HG1s1 | nz]).
    assert (HG2sp : il_sp m G2)
      by (rewrite /il_sp /G2 upd_ne; [exact HG1sp | nz]).
    assert (HG2thr : il_thr6 m G2).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /G2 upd_ne; [| regne]. exact (HG1thr c Hcs N2 N8 N9 N18). }
    assert (Hpp8a : add_vec_int (mword_of_int (KernelSyms.ilock + 0x86) : mword 64) 4
                    = mword_of_int (KernelSyms.ilock + 0x8a)) by pcw.
    iEval (rewrite Hpp8a) in "Hpc".
    (* ---- +0x8a jal ra,memmove ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.ilock + 0x8a)) Rra
              (mword_of_int 2087498 : mword 21) G2 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (ili_8a with "Htext"). }
    iIntros (CID29 Hq29) "Hcg Hpc".
    set (G3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.ilock + 0x8a) : mword 64) 4)]> G2).
    assert (Htgtmm : add_vec (mword_of_int (KernelSyms.ilock + 0x8a) : mword 64)
                       (sign_extend' 64 (mword_of_int 2087498 : mword 21))
                     = mword_of_int KernelSyms.memmove) by pcw.
    iEval (rewrite Htgtmm) in "Hpc".
    assert (HG3a0 : G3 !!! Regidx Ra0 = i_addr ip 0)
      by (rewrite /G3 upd_ne; [exact HG2a0 | nz]).
    assert (HG3a1 : G3 !!! Regidx Ra1
                    = pa_add (pa_add (b_data (bpa kk)) (64 * islot inum)%nat) 12)
      by (rewrite /G3 upd_ne; [exact HG2a1 | nz]).
    assert (HG3a2 : G3 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 52%nat) : mword 64))
      by (rewrite /G3 upd_ne; [exact HG2a2 | nz]).
    assert (HG3s2 : G3 !!! Regidx Rs2 = bnode kk)
      by (rewrite /G3 upd_ne; [exact HG2s2 | nz]).
    assert (HG3s1 : G3 !!! Regidx Rs1 = ip)
      by (rewrite /G3 upd_ne; [exact HG2s1 | nz]).
    assert (HG3sp : il_sp m G3)
      by (rewrite /il_sp /G3 upd_ne; [exact HG2sp | nz]).
    assert (HG3ra : G3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.ilock + 0x8a) : mword 64) 4)
      by (rewrite /G3; apply upd_eq).
    assert (HG3thr : il_thr6 m G3).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /G3 upd_ne; [| regne]. exact (HG2thr c Hcs N2 N8 N9 N18). }
    (* the DESTINATION: the thirteen addrs cells as 52 contiguous bytes *)
    iDestruct (il_addrs_buf_upd ip l0 with "Haddrs0") as "[Hdst Hdstback]".
    iEval (rewrite Hl0len) in "Hdst".
    iEval (change (4 * 13)%nat with 52%nat) in "Hdst".
    assert (Hlen32 : (Z.of_nat 52%nat < 2 ^ 32)%Z) by (vm_compute; reflexivity).
    assert (HKmm : (2 <= K - 4)%nat) by lia.
    iEval (rewrite /bb_bytes -HG3a0) in "Hdst".
    iEval (rewrite /bb_bytes -HG3a1) in "Hda".
    iApply (MM.wp_memmove_sconf KT1 KT0 KT0 G3 (K - 4)%nat 52%nat
              (fun jj => ind_bytes (di_addrs dn) !!! jj)
              (fun jj => ind_bytes l0 !!! jj)
              (DfracOwn 1) b (proc_addr j) HKmm Hlen32 HG3a2
              with "Hcg Htext Hpc Hda Hdst").
    iIntros (CID30 Hq30 mM) "Hcg Hpc Hda Hdst %Hmma0 %Hcsmm".
    assert (Hpc8e : ret_pc (G3 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.ilock + 0x8e)) by (rewrite HG3ra; pcw).
    iEval (rewrite Hpc8e) in "Hpc".
    iEval (rewrite HG3a1) in "Hda".
    iEval (rewrite HG3a0) in "Hdst".
    (* the destination now holds the on-disk addrs.  Which blkmap those
       ARE is the allocated shape's business, settled at the type test. *)
    iEval (change 52%nat with (4 * 13)%nat; rewrite -Hdalen) in "Hdst".
    iDestruct ("Hdstback" $! (di_addrs dn) with "[%] Hdst") as "Haddrs".
    { rewrite Hdalen Hl0len. reflexivity. }
    pose proof Hcsmm as Hcsmm_cs.
    assert (HmMs2 : mM !!! Regidx Rs2 = bnode kk)
      by (rewrite (callee_saved_lookup Hcsmm_cs Rs2 ltac:(vm_compute; reflexivity));
          exact HG3s2).
    assert (HmMs1 : mM !!! Regidx Rs1 = ip)
      by (rewrite (callee_saved_lookup Hcsmm_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HG3s1).
    assert (HmMsp : il_sp m mM).
    { rewrite /il_sp
        (callee_saved_lookup Hcsmm_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HG3sp. }
    assert (HmMthr : il_thr6 m mM).
    { intros c Hcs N2 N8 N9 N18.
      rewrite (callee_saved_lookup Hcsmm_cs c Hcs).
      exact (HG3thr c Hcs N2 N8 N9 N18). }
    (* ---- give the slot and the block back UNCHANGED ---- *)
    iDestruct ("Hslotback" $! dn with "[%] [Hd0 Hd2 Hd4 Hd6 Hd8 Hda]") as "Hby".
    { exact Hdnwf. }
    { rewrite /dislot.
      iSplitL "Hd0"; [iExact "Hd0" |].
      iSplitL "Hd2"; [iExact "Hd2" |].
      iSplitL "Hd4"; [iExact "Hd4" |].
      iSplitL "Hd6"; [iExact "Hd6" |].
      iSplitL "Hd8"; [iExact "Hd8" |].
      rewrite /bb_bytes. iExact "Hda". }
    iDestruct ("Hbyback" $! (<[islot inum := dn]> ds) with "[%] Hby") as "Hbuf".
    { exact (diblk_wf_insert ds (islot inum) dn Hdswf Hdnwf). }
    iEval (rewrite Hins) in "Hbuf".
    iDestruct ("Hheldback" with "Hbuf") as "Hheld".
    (* ================= brelse ================= *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ilock + 0x8e)) Ra0 Rs2
              mM (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (ili_8e with "Htext"). }
    iIntros (CID31 Hq31) "Hcg Hpc".
    set (H0 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mM Rs2))]> mM).
    assert (HH0a0 : H0 !!! Regidx Ra0 = bnode kk).
    { rewrite /H0 upd_eq. rgne. rewrite HmMs2. apply add_vec_zero_l. }
    assert (HH0s1 : H0 !!! Regidx Rs1 = ip)
      by (rewrite /H0 upd_ne; [exact HmMs1 | nz]).
    assert (HH0sp : il_sp m H0)
      by (rewrite /il_sp /H0 upd_ne; [exact HmMsp | nz]).
    assert (HH0thr : il_thr6 m H0).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /H0 upd_ne; [| regne]. exact (HmMthr c Hcs N2 N8 N9 N18). }
    assert (Hpp90 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x8e) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x90)) by pcw.
    iEval (rewrite Hpp90) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.ilock + 0x90)) Rra
              (mword_of_int 2095584 : mword 21) H0 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (ili_90 with "Htext"). }
    iIntros (CID32 Hq32) "Hcg Hpc".
    set (H1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.ilock + 0x90) : mword 64) 4)]> H0).
    assert (Htgtbl : add_vec (mword_of_int (KernelSyms.ilock + 0x90) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095584 : mword 21))
                     = mword_of_int KernelSyms.brelse) by pcw.
    iEval (rewrite Htgtbl) in "Hpc".
    assert (HH1a0 : H1 !!! Regidx Ra0 = bnode kk)
      by (rewrite /H1 upd_ne; [exact HH0a0 | nz]).
    assert (HH1s1 : H1 !!! Regidx Rs1 = ip)
      by (rewrite /H1 upd_ne; [exact HH0s1 | nz]).
    assert (HH1sp : il_sp m H1)
      by (rewrite /il_sp /H1 upd_ne; [exact HH0sp | nz]).
    assert (HH1ra : H1 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.ilock + 0x90) : mword 64) 4)
      by (rewrite /H1; apply upd_eq).
    assert (HH1thr : il_thr6 m H1).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /H1 upd_ne; [| regne]. exact (HH0thr c Hcs N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID9 CID32 0 eb (proc_addr j) b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID8) (CIDb := CID32) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKbl : (K_brelse <= K - 4)%nat) by (lia).
    (* brelse is NOT generalized: its contract does not mention
       [trap_csrs_ext]/[cpu_claim_ext] at all, so [Hextc]/[Hextm] are simply
       not threaded through this call -- they stay stranded at [CID9] (where
       bread last handed them back) until the wide hop below, past brelse
       and the field copies/memmove that follow it. *)
    iApply (BL.wp_brelse_sconf gs bn (fs_view gfs gd dev cov) kk
              pidv dev bno dq H1 (K - 4)%nat eb (proc_addr j)
              (diblk_bytes ds) bsd0 d0b b
              _ Vpr HKbl Hkk HH1a0
              Hbelow
              with "Hcg Hcnt Htext Hpc Hbio Hppid Hprocs Hheld").
    all: try lkbelow.
    iIntros (CID33 Hq33 mR) "%Hcs2 Hcg Hcnt Hpc Hppid Hsl".
    assert (Hpc94 : ret_pc (H1 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.ilock + 0x94)) by (rewrite HH1ra; pcw).
    iEval (rewrite Hpc94) in "Hpc".
    pose proof Hcs2 as Hcs2_cs.
    assert (HmRs1 : mR !!! Regidx Rs1 = ip)
      by (rewrite (callee_saved_lookup Hcs2_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HH1s1).
    assert (HmRsp : il_sp m mR).
    { rewrite /il_sp
        (callee_saved_lookup Hcs2_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HH1sp. }
    assert (HmRthr : il_thr6 m mR).
    { intros c Hcs N2 N8 N9 N18.
      rewrite (callee_saved_lookup Hcs2_cs c Hcs).
      exact (HH1thr c Hcs N2 N8 N9 N18). }
    (* ================= ip->valid = 1, and the dead type panic ========== *)
    (* ---- +0x94 c.li a5,1 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.ilock + 0x94)) Ra5
              (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
              mR (K - 4)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (ili_94 with "Htext"). }
    iIntros (CID34 Hq34) "Hcg Hpc".
    set (V0 := <[Regidx Ra5 := regval_into_reg (mword_of_int 1 : mword 64)]> mR).
    assert (HV0a5 : V0 !!! Regidx Ra5 = (mword_of_int 1 : mword 64))
      by (rewrite /V0; apply upd_eq).
    assert (HV0s1 : V0 !!! Regidx Rs1 = ip)
      by (rewrite /V0 upd_ne; [exact HmRs1 | nz]).
    assert (HV0sp : il_sp m V0)
      by (rewrite /il_sp /V0 upd_ne; [exact HmRsp | nz]).
    assert (HV0thr : il_thr6 m V0).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /V0 upd_ne; [| regne]. exact (HmRthr c Hcs N2 N8 N9 N18). }
    assert (Hpp96 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x94) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x96)) by pcw.
    iEval (rewrite Hpp96) in "Hpc".
    (* ---- +0x96 c.sw a5,64(s1) : ip->valid = 1 ---- *)
    assert (Hvaladr : add_vec (rget V0 Rs1)
                        (sign_extend' 64 (mword_of_int 64 : mword 12)) = i_valid ip).
    { rgne. rewrite HV0s1. reflexivity. }
    iEval (rewrite -Hvaladr) in "Hvalid".
    iApply (wp_csw_s_sconf (mword_of_int (KernelSyms.ilock + 0x96)) Ra5 Rs1
              (mword_of_int 64 : mword 12) V0 (K - 4)%nat
              (mword_of_int 0 : mword 32) b with "Hcg Hpc [] Hvalid").
    { iApply (ili_96 with "Htext"). }
    iIntros (CID35 Hq35) "Hcg Hpc Hvalid".
    assert (Hone : trunc32 (mword_of_int 1 : mword 64) = (mword_of_int 1 : mword 32))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hvaladr; rgne; rewrite HV0a5 Hone) in "Hvalid".
    assert (Hpp98 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x96) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x98)) by pcw.
    iEval (rewrite Hpp98) in "Hpc".
    (* ---- +0x98 lh a5,68(s1) : read the type back ---- *)
    assert (Htyadr2 : add_vec (rget V0 Rs1)
                        (sign_extend' 64 (mword_of_int 68 : mword 12)) = i_type ip).
    { rgne. rewrite HV0s1. reflexivity. }
    iEval (rewrite -Htyadr2) in "Hmty".
    iApply (wp_lh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.ilock + 0x98)) Ra5 Rs1
              (mword_of_int 68 : mword 12) V0 (K - 4)%nat (di_type dn : mword 16) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hmty").
    { iApply (ili_98 with "Htext"). }
    iIntros (CID36 Hq36) "Hcg Hpc Hmty".
    iEval (rewrite Htyadr2) in "Hmty".
    set (V1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (di_type dn : mword 16))]> V0).
    assert (HV1a5 : V1 !!! Regidx Ra5 = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
      by (rewrite /V1; apply upd_eq).
    assert (HV1sp : il_sp m V1)
      by (rewrite /il_sp /V1 upd_ne; [exact HV0sp | nz]).
    assert (HV1thr : il_thr6 m V1).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /V1 upd_ne; [| regne]. exact (HV0thr c Hcs N2 N8 N9 N18). }
    assert (Hpp9c : add_vec_int (mword_of_int (KernelSyms.ilock + 0x98) : mword 64) 4
                    = mword_of_int (KernelSyms.ilock + 0x9c)) by pcw.
    iEval (rewrite Hpp9c) in "Hpc".
    (* ---- +0x9c c.beqz a5 : THE LIVE PANIC ARM.  This is the ONLY place
       the pool entry's shape matters (§13.3): the ALLOCATED shape carries
       [inode_ok], whose type conjunct makes the branch fall through, while
       a FREE inode really does reach [panic("ilock: no type")] -- the
       first genuinely-taken panic branch in this tree.  Everything before
       this instruction ran on the shapes' common part. ---- *)
    iDestruct "Hrest" as "[[Hdn [Hwb Hal]] | %Ht0]"; last first.
    { (* ===== FREE INODE: the branch is TAKEN, and ilock DIVERGES ===== *)
      assert (Htk2 : add_vec (mword_of_int (KernelSyms.ilock + 0x9c) : mword 64)
                       (sign_extend' 64 (sign_extend' 13
                          (concat_vec (mword_of_int 3 : mword 8) ('b"0"))))
                     = mword_of_int (KernelSyms.ilock + 0xa2)) by pcw.
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.ilock + 0x9c))
                (mword_of_int 3 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                V1 (K - 4)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HV1a5; exact (il_type_zero _ Ht0))
                ltac:(rewrite Htk2; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (ili_9c with "Htext"). }
      iApply bi.later_intro.
      iIntros (CIDp1 Hqp1) "Hcg Hpc".
      iEval (rewrite Htk2) in "Hpc".
      (* +0xa2 auipc a0,0x4 : the panic string's address, high part *)
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.ilock + 0xa2)) Ra0
                (mword_of_int 4 : mword 20) V1 (K - 4)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (ili_a2 with "Htext"). }
      iIntros (CIDp2 Hqp2) "Hcg Hpc".
      set (PA1 := <[Regidx Ra0 := regval_into_reg
                     (add_vec (mword_of_int (KernelSyms.ilock + 0xa2) : mword 64)
                        (auipc_off (mword_of_int 4 : mword 20)))]> V1).
      assert (Hppa6 : add_vec_int
                        (mword_of_int (KernelSyms.ilock + 0xa2) : mword 64) 4
                      = mword_of_int (KernelSyms.ilock + 0xa6)) by pcw.
      iEval (rewrite Hppa6) in "Hpc".
      (* +0xa6 addi a0,a0,438 : ...and its low part *)
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.ilock + 0xa6)) Ra0 Ra0
                (mword_of_int 456 : mword 12) PA1 (K - 4)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
      { iApply (ili_a6 with "Htext"). }
      iIntros (CIDp3 Hqp3) "Hcg Hpc".
      set (PA2 := <[Regidx Ra0 := regval_into_reg
                     (add_vec (rget PA1 Ra0)
                        (sign_extend' 64 (mword_of_int 456 : mword 12)))]> PA1).
      assert (Hppaa : add_vec_int
                        (mword_of_int (KernelSyms.ilock + 0xa6) : mword 64) 4
                      = mword_of_int (KernelSyms.ilock + 0xaa)) by pcw.
      iEval (rewrite Hppaa) in "Hpc".
      (* +0xaa jal ra,panic -- and panic() never returns *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.ilock + 0xaa)) Rra
                (mword_of_int 2086244 : mword 21) PA2 (K - 4)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (ili_aa with "Htext"). }
      iIntros (CIDp4 Hqp4) "Hcg Hpc".
      assert (Htgtpn : add_vec (mword_of_int (KernelSyms.ilock + 0xaa) : mword 64)
                         (sign_extend' 64 (mword_of_int 2086244 : mword 21))
                       = mword_of_int KernelSyms.panic) by pcw.
      iEval (rewrite Htgtpn) in "Hpc".
      (* ---- panic() AS AN ORDINARY CALL, against SpecPanic ----
         a0 holds &"ilock: no type"; [kernel_data] mints the literal.
         [cpu_own] has to arrive AT THE PANIC HART (CIDp4), and its source
         is brelse's continuation (CID33), not where brelse was called. *)
      iPoseProof (il_msg_str with "Hkd") as "#Hstr".
      iDestruct (cpu_own_transport CID33 CIDp4 0 eb (proc_addr j) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      (* THE REGFILE THE SPEC WANTS IS THE POST-JAL ONE. *)
      pose (PA3 := <[Regidx Rra := regval_into_reg
                      (add_vec_int
                         (mword_of_int (KernelSyms.ilock + 0xaa) : mword 64) 4)]> PA2).
      assert (Ha0msg : PA3 !!! Regidx Ra0 = (mword_of_int il_msg_a : mword 64))
        by pcw.
      iApply (PN.wp_panic_sconf KT1 (CID := CIDp4) PA3 (K - 4)%nat
                0%nat eb b (proc_addr j) (PkAStr DfracDiscarded il_msg) lks
                (il_panic_K K HK) eq_refl il_panic_noff
                (il_panic_below lks Hbelow)
                with "Hcg Hcnt Htext Hkd Hpc Hpenv [Hstr]").
      { rewrite /pk_desc_res Ha0msg.
        iSplit; [iPureIntro; exact il_msg_nonul|].
        iSplit; [iPureIntro; exact il_msg_nz|]. iExact "Hstr". } }
    (* ===== ALLOCATED INODE: the type is nonzero and the branch falls
       through, exactly as v1's dead arm did ===== *)
    iDestruct "Hal" as (fl bm data)
      "(%Hfr & %Hpost & %Hok & %Hrl & %Hdok & %Hddix & %Hdoc & %Hduq & Hdlk & Hindres
        & Hblocks & Hdview & Hfview & Htop)".
    (* keep the whole fact: the re-pack at the epilogue hands it to
       [IcacheEscrow.ic_mk_loaded] (durable-notes: a [Prop] you only pass
       along is destructured for READING and rebuilt from the SAVED
       original). *)
    pose proof Hok as Hokw.
    destruct Hok as (Hwf & Hcovers & Hda & Htynz & Hszcap & Hholes & Hsized).
    pose proof (blkmap_wf_dir_len _ _ _ Hwf) as Hdirlen.
    assert (Hcelllen : length (bm_cells bm) = 13%nat)
      by (rewrite /bm_cells length_app Hdirlen; reflexivity).
    iEval (rewrite Hda) in "Haddrs".
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.ilock + 0x9c))
              (mword_of_int 3 : mword 8) (Cregidx (mword_of_int 7)) Ra5
              V1 (K - 4)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgne; rewrite HV1a5; exact (il_type_nonzero _ Htynz))
              with "Hcg Hpc []").
    { iApply (ili_9c with "Htext"). }
    iIntros (CID37 Hq37) "Hcg Hpc".
    assert (Hpp9e : add_vec_int (mword_of_int (KernelSyms.ilock + 0x9c) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x9e)) by pcw.
    iEval (rewrite Hpp9e) in "Hpc".
    (* ---- +0x9e c.ldsp s2,0(sp) : restore s2, one instruction before the
       join -- bmap's [s4] quirk verbatim ---- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ilock + 0x9e)) (mword_of_int 0 : mword 6) Rs2
              V1 (K - 4)%nat (m !!! Regidx Rs2 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf4]").
    { iApply (ili_9e with "Htext"). }
    { iEval (rewrite HV1sp -Hsp Hc4). iExact "Hf4". }
    iIntros (CID38 Hq38) "Hcg Hpc Hf4".
    iEval (rewrite HV1sp -Hsp Hc4) in "Hf4".
    set (Z0 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> V1).
    assert (HZ0sp : il_sp m Z0)
      by (rewrite /il_sp /Z0 upd_ne; [exact HV1sp | nz]).
    assert (HZ0thr : il_thr5 m Z0).
    { intros c Hcs N2 N8 N9.
      destruct (decide (c = Rs2)) as [Hc | Hc].
      - subst c. rewrite /Z0 upd_eq. reflexivity.
      - rewrite /Z0 upd_ne; [| regne]. exact (HV1thr c Hcs N2 N8 N9 Hc). }
    assert (Hppa0 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x9e) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0xa0)) by pcw.
    iEval (rewrite Hppa0) in "Hpc".
    (* ---- +0xa0 c.j : back to the join at +0x1e ---- *)
    assert (Hjmp : add_vec (mword_of_int (KernelSyms.ilock + 0xa0) : mword 64)
                     (sign_extend' 64 (sign_extend' 21
                        (concat_vec (mword_of_int 1983 : mword 11) ('b"0"))))
                   = mword_of_int (KernelSyms.ilock + 0x1e)) by pcw.
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.ilock + 0xa0))
              (sign_extend' 21 (concat_vec (mword_of_int 1983 : mword 11) ('b"0")))
              Z0 (K - 4)%nat b ltac:(rewrite Hjmp; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (ili_a0 with "Htext"). }
    iIntros (CID39 Hq39).
    iApply bi.later_intro.
    iIntros "Hcg Hpc".
    iEval (rewrite Hjmp) in "Hpc".
    (* ---- into the join ---- *)
    iAssert (il_frame m) with "[Hf1 Hf2 Hf3 Hf4]" as "Hframe".
    { rewrite /il_frame.
      iSplitL "Hf1"; [iExact "Hf1" |]. iSplitL "Hf2"; [iExact "Hf2" |].
      iSplitL "Hf3"; [iExact "Hf3" |]. iExists _. iExact "Hf4". }
    iDestruct (cpu_own_transport CID33 CID39 0 eb (proc_addr j) b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    (* Hextc/Hextm were last transported to CID9 (right after bread handed
       them back); neither brelse nor the field copies/memmove between here
       and there thread the complement, so it is stranded at CID9 -- span
       the WIDE hop straight to CID39, skipping all of it in one go. *)
    iDestruct (trap_csrs_ext_transport CID9 CID39 eb (proc_addr j)
                 ltac:(rewrite Heb2b; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID9 CID39 eb (proc_addr j)
                 ltac:(rewrite Heb2b; wp_next_chain) with "Hextm") as "Hextm".
    iEval (rewrite -valid_word_true) in "Hvalid".
    iApply (il_epilogue (CID0 := CID39)  j gfs gi gisl bn cn s g o cov logstart inodestart
              k ip dev inum dn bm fl pidv dq dqs m Z0 K eb b lks Vpr
              HK HZ0sp HZ0thr Hfr Hpost
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hframe Hppid Hsb Hsl Hstok
                    Hdep Hidev Hinumc Hvalid
                    [Hmty Hmmaj Hmmin Hmnl Hmsz Haddrs Hindres Hblocks Hdn Hdlk
                     Hdview Hfview Htop]
                    Hshot Hfoff Hwb [Hcont]").
    { (* the cells are held at [ip]; [ic_loaded] names them at the SLOT.
         [Hip] is the equation, and with the payload behind [ic_mk_loaded]
         it is rewritten into the two cell premises rather than into the
         (now folded) goal. *)
      iApply (ic_mk_loaded _ _ _ _ _ _ _ _ data Hokw Hrl Hdok Hddix Hdoc Hduq
                with "Hdlk Hdn [Hmty Hmmaj Hmmin Hmnl Hmsz] [Haddrs] Hindres
                      Hblocks Hdview Hfview Htop").
      - rewrite /inode_meta -Hip.
        iSplitL "Hmty"; [iExact "Hmty" |]. iSplitL "Hmmaj"; [iExact "Hmmaj" |].
        iSplitL "Hmmin"; [iExact "Hmmin" |]. iSplitL "Hmnl"; [iExact "Hmnl" |].
        iExact "Hmsz".
      - rewrite -Hip. iExact "Haddrs". }
    { iApply (wp_next_shift (b := true) (CIDa := CID32) (CIDb := CID39) ltac:(wp_next_chain)
                with "Hcont"). }
  Qed.

End IlockLoad.

Section ProofIlockMain.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma wp_ilock_sconf 
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (gfs : fs_names) (gi : gname)
      (cn : ic_names)
      (gil gisl : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
      (k : nat) (s : Qp) (g : gname) (o : ilkc) (dev inum : mword 32)
      (pidv : mword 32) (dq dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate)
    : wp_ilock_sconf_body gs j gl gu gd gk pd pav pu bn gfs gi cn gil gisl
                          cov logstart inodestart nib k s g o dev inum
                          pidv dq dqs m K eb b lks Vpr.
  Proof.
    cbv beta delta [wp_ilock_sconf_body].
    intros pcE ip pj ret_tgt HK Hk Hgeom Hst Hcov Hinlt Hj Hgl Ha0 Hbelow.
    pose proof HK as HK'. 
    assert (Hipe : ip = ientry k) by reflexivity.
    assert (Hipnz : uint ip <> 0)
      by (rewrite Hipe; exact (il_entry_nonzero k Hk)).
    iIntros "Hcg Hcnt Hextc Hextm #Htext #Hkd Hpc #Hpenv #Hbio #Hitbl #Hesc #Hireg #Hslk
              Href Hcl Hsb Hppid #Hprocs #Hdevi #Hdgeom #Hdlock Hsl Hcont".
    (* LEVEL 0 TIES THE TWO INDICES, as in [il_epilogue]/[il_load]. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Heb2b. cbn in Heb2b.
    iAssert (il_cont (CID0 := CID)  gfs gi gisl bn cn s g o cov logstart inodestart k ip
               dev inum pidv dq dqs j m K eb b lks Vpr)%I
      with "[Hcont]" as "Hcont"; [rewrite /il_cont; iExact "Hcont" |].
    (* ===== +0x00 c.addi sp,sp,-32 ===== *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. pcw. }
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m K 4 b
              ltac:(lia) Hpush with "Hcg Hpc []").
    { iApply (ili_00 with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HR1sp : il_sp m R1) by (rewrite /il_sp /R1 upd_eq; reflexivity).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (v1) "Hf1". iDestruct "S2" as (v2) "Hf2".
    iDestruct "S3" as (v3) "Hf3".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hb1) in "Hf1". iEval (rewrite -Hb2) in "Hf2".
    iEval (rewrite -Hb3) in "Hf3".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x02)) by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    (* ===== +0x02 .. +0x06 : ra / s0 / s1 ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.ilock + 0x02)) (mword_of_int 3 : mword 6) Rra
              R1 (K - 4)%nat v1 b with "Hcg Hpc [] Hf1").
    { iApply (ili_02 with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x04)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.ilock + 0x04)) (mword_of_int 2 : mword 6) Rs0
              R1 (K - 4)%nat v2 b with "Hcg Hpc [] Hf2").
    { iApply (ili_04 with "Htext"). }
    iIntros (CID3 Hq3) "Hcg Hpc Hf2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x06)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.ilock + 0x06)) (mword_of_int 1 : mword 6) Rs1
              R1 (K - 4)%nat v3 b with "Hcg Hpc [] Hf3").
    { iApply (ili_06 with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc Hf3".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x08)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    assert (HR1ra : (R1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s0 : (R1 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s1 : (R1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    iEval (rewrite Hb1; rgne; rewrite HR1ra) in "Hf1".
    iEval (rewrite Hb2; rgne; rewrite HR1s0) in "Hf2".
    iEval (rewrite Hb3; rgne; rewrite HR1s1) in "Hf3".
    iAssert (il_frame m) with "[Hf1 Hf2 Hf3 S4]" as "Hframe".
    { rewrite /il_frame.
      iSplitL "Hf1"; [iExact "Hf1" |]. iSplitL "Hf2"; [iExact "Hf2" |].
      iSplitL "Hf3"; [iExact "Hf3" |].
      iDestruct "S4" as (w4) "Hf4". iExists w4. iExact "Hf4". }
    (* ===== +0x08 c.addi4spn s0,sp,32 ===== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.ilock + 0x08)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 R1 (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (ili_08 with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (HR2sp : il_sp m R2)
      by (rewrite /il_sp /R2 upd_ne; [exact HR1sp | nz]).
    assert (HR2a0 : R2 !!! Regidx Ra0 = ip)
      by (rewrite /R2 upd_ne; [| nz]; rewrite /R1 upd_ne; [exact Ha0 | nz]).
    assert (HR2thr : il_thr5 m R2).
    { intros c Hcs N2 N8 N9.
      rewrite /R2 upd_ne; [| regne]. rewrite /R1 upd_ne; [reflexivity | regne]. }
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.ilock + 0x08) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x0a)) by pcw.
    iEval (rewrite Hpp0a) in "Hpc".
    (* ===== +0x0a c.beqz a0 : DEAD panic arm, ip <> 0 ===== *)
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.ilock + 0x0a))
              (mword_of_int 15 : mword 8) (Cregidx (mword_of_int 2)) Ra0
              R2 (K - 4)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgne; rewrite HR2a0; exact (inode_ptr_nonzero ip Hipnz))
              with "Hcg Hpc []").
    { iApply (ili_0a with "Htext"). }
    iIntros (CID6 Hq6) "Hcg Hpc".
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.ilock + 0x0a) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x0c)) by pcw.
    iEval (rewrite Hpp0c) in "Hpc".
    (* ===== +0x0c c.mv s1,a0 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ilock + 0x0c)) Rs1 Ra0
              R2 (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (ili_0c with "Htext"). }
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (R3 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget R2 Ra0))]> R2).
    assert (HR3s1 : R3 !!! Regidx Rs1 = ip).
    { rewrite /R3 upd_eq. rgne. rewrite HR2a0. apply add_vec_zero_l. }
    assert (HR3a0 : R3 !!! Regidx Ra0 = ip)
      by (rewrite /R3 upd_ne; [exact HR2a0 | nz]).
    assert (HR3sp : il_sp m R3)
      by (rewrite /il_sp /R3 upd_ne; [exact HR2sp | nz]).
    assert (HR3thr : il_thr5 m R3).
    { intros c Hcs N2 N8 N9.
      rewrite /R3 upd_ne; [| regne]. exact (HR2thr c Hcs N2 N8 N9). }
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.ilock + 0x0c) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x0e)) by pcw.
    iEval (rewrite Hpp0e) in "Hpc".
    (* ===== +0x0e c.lw a5,8(a0) : a5 := ip->ref, HOLDING NOTHING.
       The [ref] words live in [itable_inv] (design §4), so this is an
       ATOMIC-UPDATE read: [iref_live_load_au] produces the cell inside the
       leaf's own mask and delivers, in exchange, the two bounds that kill
       the panic at +0x10.  Only the share's LIVENESS slice goes in; its
       identity fractions stay in hand. ===== *)
    assert (Hrefadr : add_vec (rget R3 Ra0) (sign_extend' 64 (mword_of_int 8 : mword 12))
                      = i_ref ip).
    { rgne. rewrite HR3a0. reflexivity. }
    (* v3: the caller holds a SHARE, which has no count fragment, so the read
       goes through its LIVENESS slice ([iref_live_load_au]) -- whose delivered
       bounds are the same ones, and whose [k < NINODE] premise this proof has
       had since its first line (§14.6/§14.8). *)
    iDestruct "Href" as "(Hrid & Hrt & Hrs)".
    (* the share's SLEEPLOCK slice is what the lock will hold while ilock has
       the entry checked out; the arm keeps the other two slices. *)
    (* the address claim, off the ref word's OWN points-to: one peek-open of
       the liveness accessor, [wordw_claim_of], and the cell straight back *)
    iApply fupd_wp.
    iMod (iref_live_gen_load_au ⊤ k s g ltac:(solve_ndisj) Hk
            with "Hitbl Hrt") as (vp) "[Hcellp Hbackp]".
    iDestruct (wordw_claim_of (KTR := KT0) 4 (i_ref (ientry k))
                 (DfracOwn 1) vp ltac:(lia) with "Hcellp") as "#Hclaim0".
    iMod ("Hbackp" with "Hcellp") as "[%Hbp Hrt]".
    iModIntro.
    iApply (wp_lw_au_s_sconf true (mword_of_int (KernelSyms.ilock + 0x0e)) Ra5 Ra0
              (mword_of_int 8 : mword 12) R3 (K - 4)%nat
              (fun v => (⌜0 < bv_unsigned v < 2 ^ 31⌝ ∗
                         live_gen k s g)%I)
              (⊤ ∖ ↑minstretN ∖ ↑icacheN) b
              ltac:(nz) ltac:(rdok) ltac:(solve_ndisj)
              with "Hcg Hpc [] [] [Hrt]").
    { iApply (ili_0e with "Htext"). }
    { rewrite Hrefadr Hipe. iExact "Hclaim0". }
    { rewrite Hrefadr Hipe.
      iMod (iref_live_gen_load_au (⊤ ∖ ↑minstretN) k s g
              ltac:(solve_ndisj) Hk with "Hitbl Hrt") as (v) "[Hcell Hback]".
      iModIntro. iExists v. iFrame "Hcell". iIntros "Hcell".
      iMod ("Hback" with "Hcell") as "[%Hb Hrt]". iModIntro. by iFrame. }
    iIntros (refv CID8 Hq8) "Hcg Hpc [%Hrefp Hrt]".
    iAssert (inode_shr_gen_bare k s dev inum g) with "[Hrt Hrid]" as "Href".
    { rewrite /inode_shr_gen_bare. iFrame. }
    set (R4 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 refv)]> R3).
    assert (HR4a5 : R4 !!! Regidx Ra5 = (sign_extend' 64 refv : mword 64))
      by (rewrite /R4; apply upd_eq).
    assert (HR4a0 : R4 !!! Regidx Ra0 = ip)
      by (rewrite /R4 upd_ne; [exact HR3a0 | nz]).
    assert (HR4s1 : R4 !!! Regidx Rs1 = ip)
      by (rewrite /R4 upd_ne; [exact HR3s1 | nz]).
    assert (HR4sp : il_sp m R4)
      by (rewrite /il_sp /R4 upd_ne; [exact HR3sp | nz]).
    assert (HR4thr : il_thr5 m R4).
    { intros c Hcs N2 N8 N9.
      rewrite /R4 upd_ne; [| regne]. exact (HR3thr c Hcs N2 N8 N9). }
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x0e) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x10)) by pcw.
    iEval (rewrite Hpp10) in "Hpc".
    (* ===== +0x10 bge x0,a5 : DEAD panic arm, ref >= 1 ===== *)
    iApply (wp_bge_x0_fall_s_sconf (mword_of_int (KernelSyms.ilock + 0x10))
              (mword_of_int 24 : mword 13) Ra5 R4 (K - 4)%nat b ltac:(nz)
              ltac:(rgne; rewrite HR4a5; exact (inode_ref_spos refv Hrefp))
              with "Hcg Hpc []").
    { iApply (ili_10 with "Htext"). }
    iIntros (CID9 Hq9) "Hcg Hpc".
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x10) : mword 64) 4
                    = mword_of_int (KernelSyms.ilock + 0x14)) by pcw.
    iEval (rewrite Hpp14) in "Hpc".
    (* ===== +0x14 c.addi a0,a0,16 : a0 := &ip->lock ===== *)
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.ilock + 0x14)) Ra0
              (mword_of_int 16 : mword 6) R4 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (ili_14 with "Htext"). }
    iIntros (CID10 Hq10) "Hcg Hpc".
    set (R5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (rget R4 Ra0)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> R4).
    assert (HR5a0 : R5 !!! Regidx Ra0 = i_lock ip).
    { rewrite /R5 upd_eq. rgne. rewrite HR4a0. apply il_lock_addr. }
    assert (HR5s1 : R5 !!! Regidx Rs1 = ip)
      by (rewrite /R5 upd_ne; [exact HR4s1 | nz]).
    assert (HR5sp : il_sp m R5)
      by (rewrite /il_sp /R5 upd_ne; [exact HR4sp | nz]).
    assert (HR5thr : il_thr5 m R5).
    { intros c Hcs N2 N8 N9.
      rewrite /R5 upd_ne; [| regne]. exact (HR4thr c Hcs N2 N8 N9). }
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.ilock + 0x14) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x16)) by pcw.
    iEval (rewrite Hpp16) in "Hpc".
    (* ===== +0x16 jal ra,acquiresleep ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.ilock + 0x16)) Rra
              (mword_of_int 3440 : mword 21) R5 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (ili_16 with "Htext"). }
    iIntros (CID11 Hq11) "Hcg Hpc".
    set (R6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.ilock + 0x16) : mword 64) 4)]> R5).
    assert (Htgtasl : add_vec (mword_of_int (KernelSyms.ilock + 0x16) : mword 64)
                        (sign_extend' 64 (mword_of_int 3440 : mword 21))
                      = mword_of_int KernelSyms.acquiresleep) by pcw.
    iEval (rewrite Htgtasl) in "Hpc".
    assert (HR6a0 : R6 !!! Regidx Ra0 = i_lock ip)
      by (rewrite /R6 upd_ne; [exact HR5a0 | nz]).
    assert (HR6s1 : R6 !!! Regidx Rs1 = ip)
      by (rewrite /R6 upd_ne; [exact HR5s1 | nz]).
    assert (HR6sp : il_sp m R6)
      by (rewrite /il_sp /R6 upd_ne; [exact HR5sp | nz]).
    assert (HR6ra : R6 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.ilock + 0x16) : mword 64) 4)
      by (rewrite /R6; apply upd_eq).
    assert (HR6thr : il_thr5 m R6).
    { intros c Hcs N2 N8 N9.
      rewrite /R6 upd_ne; [| regne]. exact (HR5thr c Hcs N2 N8 N9). }
    iDestruct (cpu_own_transport CID CID11 0 eb (proc_addr j) b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID CID11 eb (proc_addr j)
                 ltac:(rewrite Heb2b; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID CID11 eb (proc_addr j)
                 ltac:(rewrite Heb2b; wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (wp_next_shift (b := true) (CIDa := CID) (CIDb := CID11) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    (* acquiresleep is index-generic now and takes the trap-CSR complement
       as a genuine pass-through: ilock's own (untouched since entry) is
       exactly what its wait loop's interior [sleep] needs. *)
    iApply (ASL.wp_acquiresleep_gen_sconf gs j gil gisl "inode"%string (ic_tok cn k) (slh_tok (icfg_isl k)) s R6 pidv Vpr (K - 4)%nat eb b lks
              Hj ltac:(lia)
              (* acquiresleep's bound is "sleep lock"(6); ilock's own is
                 "bcache"(4), and [locks_below_mono] weakens it. *)
              ltac:(lkbelow)
              with "Hcg Hcnt Hextc Hextm Htext Hpc [] Hrs Hppid Hprocs").
    all: try lkbelow.
    { iEval (rewrite HR6a0). iExact "Hslk". }
    (* acquiresleep PARKS: it returns on hart [CIDa], handing the complement
       back too. *)
    iIntros (CIDa Hqa mf) "%Hcs1 Hcg Hcnt Hextc Hextm Hpc Hstok Htok Hppid".
    iEval (rewrite HR6a0) in "Hstok".
    assert (Hpc1a : ret_pc (R6 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.ilock + 0x1a)) by (rewrite HR6ra; pcw).
    iEval (rewrite Hpc1a) in "Hpc".
    pose proof Hcs1 as Hcs1_cs.
    assert (HmfS1 : mf !!! Regidx Rs1 = ip)
      by (rewrite (callee_saved_lookup Hcs1_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HR6s1).
    assert (Hmfsp : il_sp m mf).
    { rewrite /il_sp
        (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HR6sp. }
    assert (Hmfthr : il_thr5 m mf).
    { intros c Hcs N2 N8 N9.
      rewrite (callee_saved_lookup Hcs1_cs c Hcs).
      exact (HR6thr c Hcs N2 N8 N9). }
    (* ---- THE CHECKOUT.  One opening of [ic_escrow], mask-balanced, so no
       atomic step is needed: the winner's [ic_tok] refutes the checked-out
       arm and its reference's inum fraction refutes the recycle window,
       and what comes out is the entry's content plus BOTH identity halves
       at the winner's own dev/inum (§13.1e).  The reference itself is
       DEPOSITED (§13.1d) -- from here on ilock owns no reference, which is
       exactly why the dev half had to come out with the payload. ---- *)
    iApply fupd_wp.
    iInv "Hesc" as ">Hbody" "Hclose".
    iMod (ic_swap_checkout cn gfs gi cov logstart k (DepShr s dev inum g) g
            dev inum eq_refl with "Hbody Htok [Href]") as "[Hok | Hfrz]".
    { rewrite /ic_dep_own. iSplitR; [iPureIntro; done |]. iExact "Href". }
    2:{ (* ============ DEVIATION 1's OWED OBLIGATION, PAID BY RULING R-e
           (iclaim-ledger.md §5⁗⁗).  The checkout may find the free path's
           FROZEN PARK, and ilock holds no licence that decides it -- RULING
           C' took that content away (§5⁗″.2), and neither PlainK nor ShotK
           can get it back.

           R-e pays it from the INVARIANT.  The frozen tail carries a quarter
           of the slot's freeze SELECTOR, whose other half sits in
           [IcacheInv.live_slot]'s frozen alternative BESIDE THE SLOT'S WHOLE
           LIVENESS UNIT; and the deposit the checkout hands straight back
           carries this caller's own positive slice.  A whole unit and a
           positive slice cannot coexist, so the branch is dead -- with NO
           lock, NO licence, NO region open, and NOTHING read off the index,
           which is why the same line serves ClaimK, PlainK and ShotK. ==== *)
        iDestruct "Hfrz" as "(Htok & Hown & Hrcpt & Hsel & Hwand)".
        iDestruct (ic_dep_own_live with "Hown") as (s0 g0) "(%Hg0 & Hlv & _)".
        iMod (frz_slot_kill (⊤ ∖ ↑icEscN) k ((1/2)/2)%Qp s0
                ltac:(solve_ndisj) Hk with "Hitbl Hsel [Hlv]") as "[]".
        iExists g0. iExact "Hlv". }
    iDestruct "Hok" as "(Hbody & Hdep & Hout)".
    iMod ("Hclose" with "[Hbody]") as "_"; [iNext; iExact "Hbody" |].
    iModIntro.
    iDestruct "Hout" as (vv) "(Hidev & Hinumc & Hvalid & Hpay)".
    iEval (rewrite -Hipe) in "Hidev".
    iEval (rewrite -Hipe) in "Hinumc".
    iEval (rewrite -Hipe) in "Hvalid".
    (* ===== +0x1a c.lw a5,64(s1) : a5 := ip->valid ===== *)
    assert (Hvaladr : add_vec (rget mf Rs1) (sign_extend' 64 (mword_of_int 64 : mword 12))
                      = i_valid ip).
    { rgne. rewrite HmfS1. reflexivity. }
    iEval (rewrite -Hvaladr) in "Hvalid".
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.ilock + 0x1a)) Ra5 Rs1
              (mword_of_int 64 : mword 12) mf (K - 4)%nat (valid_word vv) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hvalid").
    { iApply (ili_1a with "Htext"). }
    iIntros (CID12 Hq12) "Hcg Hpc Hvalid".
    iEval (rewrite Hvaladr) in "Hvalid".
    set (Q1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (valid_word vv))]> mf).
    assert (HQ1a5 : Q1 !!! Regidx Ra5 = (sign_extend' 64 (valid_word vv) : mword 64))
      by (rewrite /Q1; apply upd_eq).
    assert (HQ1s1 : Q1 !!! Regidx Rs1 = ip)
      by (rewrite /Q1 upd_ne; [exact HmfS1 | nz]).
    assert (HQ1sp : il_sp m Q1)
      by (rewrite /il_sp /Q1 upd_ne; [exact Hmfsp | nz]).
    assert (HQ1thr : il_thr5 m Q1).
    { intros c Hcs N2 N8 N9.
      rewrite /Q1 upd_ne; [| regne]. exact (Hmfthr c Hcs N2 N8 N9). }
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.ilock + 0x1a) : mword 64) 2
                    = mword_of_int (KernelSyms.ilock + 0x1c)) by pcw.
    iEval (rewrite Hpp1c) in "Hpc".
    (* ===== +0x1c c.beqz a5 : the CACHED / UNCACHED split, decided by the
       shadow's [vv] rather than by any runtime case analysis ===== *)
    destruct vv.
    - (* ---- CACHED: valid = 1, fall through to the epilogue ---- *)
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.ilock + 0x1c))
                (mword_of_int 13 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                Q1 (K - 4)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HQ1a5; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (ili_1c with "Htext"). }
      iIntros (CID13 Hq13) "Hcg Hpc".
      assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.ilock + 0x1c) : mword 64) 2
                      = mword_of_int (KernelSyms.ilock + 0x1e)) by pcw.
      iEval (rewrite Hpp1e) in "Hpc".
      (* the CACHED arm's witness is the one the FILL that loaded this entry
         minted, riding on the payload's TRUE polarity (design §17.6 (1)) --
         so this arm proves the post's new conjunct with no work at all. *)
      (* A-PRIME's TOKEN comes off the payload here, exactly as it does on
         the uncached arm below (iclaim-ledger.md §3.9). *)
      iDestruct (ic_payload_split with "Hpay") as "[Hpay Hfoff]".
      iAssert (∃ (dn0 : dinode) (bm0 : blkmap),
                 ic_loaded gfs gi cov logstart k inum dn0 bm0 ∗
                 ity_shot g (di_type dn0))%I
        with "[Hpay]" as "Hpay2"; [iExact "Hpay" |].
      iDestruct "Hpay2" as (dnp bmp) "[Hlk #Hshot]".
      (* THE CACHED ARM REFUTES [ClaimK] (RULING C', iclaim-ledger.md
         §5''''').  This entry was loaded by an earlier fill, so its
         [ic_loaded] carries the inum's [dinode_at] -- the record is OUT of
         the region.  A standing [iclaim] says the opposite
         ([InodeRegion.ireg_claim_no_out]), so no claimant can reach here
         and its post's [filled = true] is a theorem.  The other two
         indices pay nothing: the plain unit goes back untouched, the
         one-shot is persistent and was never taken. *)
      iApply fupd_wp.
      iAssert (|={⊤}=> ic_loaded gfs gi cov logstart k inum dnp bmp
                       ∗ ireg_wd_back o g (bv_unsigned inum)
                       ∗ ⌜ilk_post o false dnp⌝)%I
        with "[Hlk Hcl]" as ">(Hlk & Hwb & %Hpost)".
      { destruct o as [tyc | | tys].
        - iDestruct "Hcl" as "[Hcl _]".
          iDestruct (ic_loaded_open with "Hlk") as (datx)
            "(%Hokx & %Hrlx & %Hdokx & %Hddixx & %Hdocx & %Hduqx & Hdlkx & Hdnx & Hrestx)".
          iMod (ireg_claim_no_out ⊤ gi gfs inodestart nib inum dnp tyc
                  ltac:(solve_ndisj) Hinlt with "Hireg Hdnx Hcl") as %[].
        - iModIntro. iSplitL "Hlk"; [iExact "Hlk" |].
          iSplitL "Hcl"; [iExact "Hcl" |]. iPureIntro. exact I.
        - iModIntro. iSplitL "Hlk"; [iExact "Hlk" |].
          iSplitL "Hcl"; [iExact "Hcl" |]. iPureIntro. reflexivity. }
      iModIntro.
      iDestruct (cpu_own_transport CIDa CID13 0 eb (proc_addr j) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CIDa CID13 eb (proc_addr j)
                   ltac:(rewrite Heb2b; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CIDa CID13 eb (proc_addr j)
                   ltac:(rewrite Heb2b; wp_next_chain) with "Hextm") as "Hextm".
      iDestruct (wp_next_shift (b := true) (CIDa := CID11) (CIDb := CID13) ltac:(wp_next_chain)
                   with "Hcont") as "Hcont".
      (* THE CACHED ARM REPORTS [filled = false]: the entry was loaded by
         some earlier fill and its record is whatever that fill read, so
         [fresh_shape] is not available and not claimed. *)
      iApply (il_epilogue (CID0 := CID13)  j gfs gi gisl bn cn s g o cov logstart
                inodestart k ip dev inum dnp bmp false pidv dq dqs m Q1 K eb b lks Vpr
                HK HQ1sp HQ1thr ltac:(discriminate) Hpost
                with "Hcg Hcnt Hextc Hextm Htext Hpc Hframe Hppid Hsb Hsl Hstok
                      Hdep Hidev Hinumc Hvalid Hlk Hshot Hfoff Hwb Hcont").
    - (* ---- UNCACHED: valid = 0, branch to +0x36 ---- *)
      assert (Htk : add_vec (mword_of_int (KernelSyms.ilock + 0x1c) : mword 64)
                      (sign_extend' 64 (sign_extend' 13
                         (concat_vec (mword_of_int 13 : mword 8) ('b"0"))))
                    = mword_of_int (KernelSyms.ilock + 0x36)) by pcw.
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.ilock + 0x1c))
                (mword_of_int 13 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                Q1 (K - 4)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HQ1a5; vm_compute; reflexivity)
                ltac:(rewrite Htk; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (ili_1c with "Htext"). }
      iApply bi.later_intro.
      iIntros (CID13 Hq13) "Hcg Hpc".
      iEval (rewrite Htk) in "Hpc".
      iEval (change (valid_word false) with (mword_of_int 0 : mword 32)) in "Hvalid".
      (* FOUR pieces since RULING A-prime (iclaim-ledger.md §3.10): the
         payload is [ic_payload_np ∗ ifreeze_off], and at [v = false] the
         [_np] half is [(inode_raw ∗ ipool_shape_np) ∗ ity_pending].  The
         token is the holder's from here on -- that is what [SpecIlock]'s
         post hands out and what create's fresh child and sys_link's
         [ip->nlink++] pay [wp_iupdate_link]'s pin with.  Routing it through
         [il_cont] to that post is the SAME un-landed item as the [iclaim]
         goal this file still carries (see [ireg_withdraw] in [il_load]). *)
      iAssert (inode_raw (ientry k) ∗
               ipool_shape_np gfs gi cov logstart inum ∗
               ity_pending g ∗
               ifreeze_off (bv_unsigned inum))%I
        with "[Hpay]" as "(Hraw & Hpool & Hpend & Hfoff)";
        [rewrite /ic_payload /ic_payload_np /ic_unloaded;
         iDestruct "Hpay" as "[[[$ $] $] $]" |].
      iEval (rewrite -Hipe) in "Hraw".
      (* THE UNCACHED ARM REFUTES [ShotK] (RULING C').  This arm's payload
         carries the generation's PENDING one-shot -- the fill has not run
         for [g] yet -- and the fd sites hold its SHOT twin, which is what
         they present in place of a unit.  The two cannot coexist
         ([IcacheRef.ity_pending_shot_excl]), so the three fd callers never
         reach the fill and their post's [filled = false] is a theorem.
         What comes out is [ilk_fills o], the premise [il_load] takes. *)
      iAssert (ireg_wd_lic o g (bv_unsigned inum) ∗ ity_pending g
               ∗ ⌜ilk_fills o⌝)%I
        with "[Hcl Hpend]" as "(Hcl & Hpend & %Hfills)".
      { destruct o as [tyc | | tys].
        - iSplitL "Hcl"; [iExact "Hcl" |].
          iSplitL "Hpend"; [iExact "Hpend" |]. iPureIntro. exact I.
        - iSplitL "Hcl"; [iExact "Hcl" |].
          iSplitL "Hpend"; [iExact "Hpend" |]. iPureIntro. exact I.
        - iDestruct (ity_pending_shot_excl with "Hpend Hcl") as %[]. }
      iDestruct (cpu_own_transport CIDa CID13 0 eb (proc_addr j) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CIDa CID13 eb (proc_addr j)
                   ltac:(rewrite Heb2b; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CIDa CID13 eb (proc_addr j)
                   ltac:(rewrite Heb2b; wp_next_chain) with "Hextm") as "Hextm".
      iDestruct (wp_next_shift (b := true) (CIDa := CID11) (CIDb := CID13) ltac:(wp_next_chain)
                   with "Hcont") as "Hcont".
      iApply (il_load (CID0 := CID13)  gs j gl gu gd gk pd pav pu bn gfs gi gisl
                cn s g o cov logstart inodestart nib dev k ip inum
                pidv dq dqs m Q1 K eb b lks Vpr
                HK Hfills HQ1sp HQ1thr HQ1s1 Hipe Hk Hgeom Hst Hcov Hinlt Hj Hgl
                Hbelow
                with "Hcg Hcnt Hextc Hextm Htext Hkd Hpc Hpenv Hbio Hireg Hprocs Hdevi Hdgeom
                      Hdlock Hframe Hppid Hidev Hinumc Hsb
                      Hsl Hstok Hdep Hvalid Hraw Hpool Hpend Hfoff Hcl Hcont").
  Qed.

End ProofIlockMain.

End IlockProof.
