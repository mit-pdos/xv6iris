(* ProofBread.v -- bread (with bget INLINED) over the SIE-agnostic sconf world.

     struct buf* bread(uint dev, uint blockno) {
       struct buf *b = bget(dev, blockno);     // INLINED: both scan loops
       if (!b->valid) { virtio_disk_rw(b, 0); b->valid = 1; }
       return b;
     }

   The proof is six blocks, each a [Local Lemma] over the block's ARRIVAL
   register map (design/kernel-proofs.md's re-joined-block shape), proved
   bottom-up so the two scan loops can call the already-finished code their
   exits land on rather than carrying abstract exit premises:

     bread_epi     0xb8..0xc6   the epilogue (a0 := b, pop, ret)
     bread_tail    0xb4..0xd4   the checkout swap at the [lw a5,0(s1)],
                                the valid test, and the disk-read arm
     bread_hit     0x48..0x62   refcnt++, release, acquiresleep, j tail
     bread_recyc   0x90..0xb0   the three field rewrites, refcnt:=1,
                                release, acquiresleep, fall into the tail
     bread_bloop   0x7a..0x8c   the backward (recycle) scan + the panic arm
     bread_miss    0x64..0x78   its preamble
     bread_floop   0x36..0x44   the forward (hit) scan
     wp_bread_sconf 0x00..0x34  prologue, acquire, and the forward scan's entry

   Five things carry it.

   * THE SCANS CARRY [BioInv.bcache_scan], the bcache resource with
     its existentials OPEN.  The forward scan's exit facts are statements
     about the functions [bcache_res] hides: POSITIVELY [devs k = dev /\
     bnos k = bno] at a hit (or the minted [bref] would not be at the
     requested key), and NEGATIVELY -- accumulated over the prefix it has
     walked, and at the wrap over every slot -- [¬ (devs i = dev /\ bnos i =
     bno)].  With the scan's DEV PIN (a slot claiming a covered block is on
     the view's device) that negative tie becomes the recycle's MISS FACT
     [∀ i, uint (bnos i) ≠ uint bno], which is what licenses the pool
     exchange and re-establishes the covered-blockno injectivity.

   * THE FOUR ESCROW OPENS are each around ONE instruction, with the
     mask-carrying width-4 leaves of ProofBreadParts.v: the recycle block's
     three field stores ([escrow_recyc_dev]/[_bno]/[_valid]) and the tail's
     [lw a5,0(s1)] ([BioInv.escrow_swap_checkout]).  So no bundle is carried
     across an instruction boundary, which is what makes the
     recycler-vs-hit-thread race safe for free.  The three stores are NOT
     symmetric: the dev store re-parks a normal arm (the payload is re-aimed
     at the stored dev, legal because a covered payload pins its dev to the
     view's device and the request is on it); the blockno store performs the
     eviction (the old payload's clean bundle goes back to the pool) and the
     pool withdrawal, and re-closes the escrow as the MID-RECYCLE WINDOW
     (cells only, dev cell FULL, the recycle token in the recycler's hand);
     the valid store closes the window, depositing the new block's pool
     bundle in the now-INVALID parked arm for whoever wins the sleeplock
     race to fill.

   * THE SENTINEL TESTS AT 0x2e AND 0x74 ARE DEAD.  [ord] is a permutation of
     [seq 0 NBUF] with NBUF = 30, hence nonempty, so head.next and head.prev
     are both real buffers and [bnode_eqv_bhead] refutes both branches.  The
     panic arm at 0x84 is genuinely reachable (every buffer pinned) and is
     discharged against [SpecPanic].

   * THE VALID BIT KEYS THE PAYLOAD.  [buf_parked] carries its valid cell at
     [if v then 1 else 0] for a BOOL [v] that also selects the payload's
     shape, so the tail's [c.beqz] does not merely learn a bit: the
     fall-through arm (v = true) gets the block's disk cell and the client
     payload indexing the buffer's own bytes, and assembles [bio_locked] with
     NO disk read; the taken arm (v = false) gets the block's pool bundle,
     spends it on [virtio_disk_rw] READ (which makes the bytes the disk's),
     stores valid := 1 with the cell in its own hands, and assembles the
     handle clean at the filled content.  BOTH arms are live on BOTH paths --
     a racer can fill a buffer this thread recycled.

   * THE HART, AND WHERE IT CANNOT MOVE.  Every leaf returns through
     [wp_next b p (fun CID => ...)]; the rebound [CID] carries every resource
     with it, so nothing needs a [(CID := h)] annotation and there is no ghost
     binder left to thread.  bread enters at level 0 with an ENABLED base, so
     [CpuOwn.cpu_own_eb_agree] forces the live index to be [eb] and the whole
     function is stated at that one index.  But the [acquire] at +0x1a returns
     with interrupts OFF, so the ENTIRE bget interior -- both scans, the miss
     preamble, the recycle field rewrites -- runs at the literal [false] index,
     where [wp_next_off] collapses the hart back at every single leaf.  That is
     what keeps [locked _ cpu_id] and [arm_pay] (both pinned at the hart
     that took the lock) usable across a hundred instructions, and it is why
     the two scan loops need no hart re-anchoring at all.  Only three stretches
     are hart-GENERIC: the prologue up to [acquire], the release/acquiresleep
     stretch of each exit arm, and the shared tail + epilogue.  [bd_cont] is a
     [wp_next] anchored at each block lemma's own [CID0], and [bd_cont_shift]
     moves that anchor at exactly the four points where the hart really does
     travel. *)
Set Printing Depth 40.
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants own.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvModelBytes.
Require Import RiscvExtras.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import MinstretInv.
Require Import WpLock SleepLock.
Require Import WpSmodeIntr.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import ProcGeom CpuOwn.
Require Import SchedCtx.
Require Import FdSlots.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import KernelText.
Require Import InstrBytes.
Require Import WpUart.
Require Import ArrCursor.
Require Import DiskPtsto DiskInv.
Require Import BufOwn BcacheInv BioInv.
Require Import BreadLru.
Require Import WpAu4.
Require Import ProofBreadParts.
Require Import CodeBread.
Require Import SpecAcquire SpecRelease SpecAcquiresleep.
Require Import SpecVirtioDiskRw.
Require Import KernelDataInv.
Require Import PrintkArgs.
Require Import WpUart.
Require Import SpecPanic.
Require Import SpecBread.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  Pure helpers, all over VARIABLES so no solver ever runs inside the     *)
(*  WP context (claude-notes/optimization.md).                            *)
(* ===================================================================== *)

(* the LRU order is a permutation of [seq 0 NBUF] and NBUF = 30, so it is
   nonempty: both sentinel tests are dead. *)
Lemma bd_ord_nonnil (ord : list nat) : ord ≡ₚ seq 0 NBUF -> ord <> [].
Proof.
  intros Hperm Hnil. subst ord.
  assert (Hlen : length (seq 0 NBUF) = 0%nat) by (rewrite -Hperm; reflexivity).
  rewrite length_seq in Hlen. unfold NBUF in Hlen. lia.
Qed.

(* every buffer index is somewhere in the order list: what turns the forward
   scan's accumulated exit tie (over the list it walked) into the recycle's
   per-slot miss fact. *)
Lemma bd_ord_mem (ord : list nat) :
  ord ≡ₚ seq 0 NBUF -> forall i, (i < NBUF)%nat -> i ∈ ord.
Proof. intros Hperm i Hi. rewrite Hperm. apply elem_of_seq. lia. Qed.

(* the scan's tie at the empty prefix *)
Lemma bd_done_nil (P : nat -> Prop) : forall i, i ∈ ([] : list nat) -> P i.
Proof. intros i Hi. apply elem_of_nil in Hi. destruct Hi. Qed.

(* the head of a nonempty order list, as a split *)
Lemma bd_ord_hd (ord : list nat) :
  ord <> [] -> exists (k : nat) (r : list nat), ord = (k :: r)%list.
Proof. destruct ord as [|k r]; [congruence | intros _; by exists k, r]. Qed.

(* the last element of a nonempty order list, as a split *)
Lemma bd_ord_last (ord : list nat) :
  ord <> [] -> exists (d : list nat) (k : nat), ord = (d ++ [k])%list.
Proof.
  intro Hne. destruct (rev ord) as [|k dr] eqn:Hrev.
  - exfalso. apply Hne. by apply (f_equal (@rev nat)) in Hrev; rewrite rev_involutive in Hrev.
  - exists (rev dr), k.
    apply (f_equal (@rev nat)) in Hrev. rewrite rev_involutive in Hrev.
    rewrite Hrev. cbn [rev]. reflexivity.
Qed.

(* the two immediates the field accesses use, in the leaf's spelling *)
Lemma bd_s0 : sign_extend' 64 (mword_of_int 0 : mword 12) = (mword_of_int 0 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma bd_s8 : sign_extend' 64 (mword_of_int 8 : mword 12) = (mword_of_int 8 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma bd_s12 : sign_extend' 64 (mword_of_int 12 : mword 12) = (mword_of_int 12 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma bd_s64 : sign_extend' 64 (mword_of_int 64 : mword 12) = (mword_of_int 64 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* the [wr] flag rw's spec computes from a1: [li a1,0] makes it [false]
   (ProofBwrite.bw_wr_true's inverse). *)
Lemma bd_wr_false (v : SailStdpp.Values.mword 64) (l1 l2 : list (bv 8)) :
  v = (mword_of_int 0 : mword 64) ->
  (if negb (eq_vec v (zero_reg : mword 64)) then l1 else l2) = l2.
Proof.
  intros ->.
  replace (eq_vec (mword_of_int 0 : mword 64) (zero_reg : mword 64)) with true
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

(* the valid word's two branch readings, at the {0,1} pin *)
Lemma bd_valid1_nonzero :
  eq_vec (sign_extend' 64 (mword_of_int 1 : mword 32)) (zero_reg : mword 64) = false.
Proof.
  apply eq_vec_false_iff. intro Hc. apply (f_equal bv_unsigned) in Hc.
  vm_compute in Hc. discriminate.
Qed.

Lemma bd_trunc32_zero :
  trunc32 (zero_reg : mword 64) = (mword_of_int 0 : mword 32).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* ===================================================================== *)

(* ===================================================================== *)
(*  THE PANIC MESSAGE.  bread's one live arm is bget's                    *)
(*  [panic("bget: no buffers")] at +0x8c -- the backward scan ran off the *)
(*  end with every buffer pinned; the literal sits at 0x800073c0 in       *)
(*  .rodata, sixteen characters and a NUL.  NAMED pure lemmas, not inline *)
(*  [ltac:] -- see optimization.md and the panic recipe.                  *)
(* ===================================================================== *)
Definition bd_msg_a : Z := 0x800073c0.
Definition bd_msg : string := "bget: no buffers".

Lemma bd_panic_K (K : nat) (eb : bool) :
  (K_bread <= K)%nat -> (panic_stack <= trap_res eb + (K - 6))%nat.
Proof. lia. Qed.

Lemma bd_panic_noff : (Z.of_nat 1 + 2 < 2 ^ 31)%Z.
Proof. lia. Qed.

(* THE ARM FIRES HOLDING bcache.lock (rank 2), well below "pr" (16). *)
Lemma bd_panic_below (lks : gset string) :
  locks_below lks "bcache" -> locks_below ({["bcache"]} ∪ lks) "pr".
Proof.
  intros H. apply locks_below_union_singleton; [vm_compute; lia|].
  apply (locks_below_mono lks "bcache" "pr" H). vm_compute; lia.
Qed.

Lemma bd_msg_nz : eq_vec (mword_of_int bd_msg_a : mword 64) zero_reg = false.
Proof. vm_compute; reflexivity. Qed.

Lemma bd_msg_nonul : PrintkFmt.nonul bd_msg = true.
Proof. vm_compute; reflexivity. Qed.

Lemma bd_msg_bytes :
  forall j b, cstring_bytes bd_msg !! j = Some b ->
    KernelData.kernel_data !! (bd_msg_a + Z.of_nat j)%Z = Some b.
Proof.
  intros j b Hj.
  do 17 (destruct j as [|j]; [ vm_compute in Hj |- *; congruence | ]).
  vm_compute in Hj; discriminate.
Qed.

Section BreadMsg.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  Lemma bd_msg_str :
    (kernel_data : iProp Σ) -∗ (mword_of_int bd_msg_a : mword 64) ↦ₛ□ bd_msg.
  Proof.
    iIntros "#Hd".
    iApply (kernel_data_string bd_msg_a bd_msg _ eq_refl
              ltac:(unfold text_end, bd_msg_a; lia) bd_msg_bytes with "Hd").
  Qed.
End BreadMsg.

Module BreadProof (A : ACQUIRE) (R : RELEASE) (ASL : ACQUIRESLEEP)
                  (RW : VIRTIODISKRW) (PN : PANIC) : BREAD.


  Notation Rz   := (mword_of_int 0 : mword 5).
  Notation Rra  := (mword_of_int 1 : mword 5).
  Notation Rtp  := (mword_of_int 4 : mword 5).
  Notation Rs0  := (mword_of_int 8 : mword 5).
  Notation Rs1  := (mword_of_int 9 : mword 5).
  Notation Ra0  := (mword_of_int 10 : mword 5).
  Notation Ra1  := (mword_of_int 11 : mword 5).
  Notation Ra4  := (mword_of_int 14 : mword 5).
  Notation Ra5  := (mword_of_int 15 : mword 5).
  Notation Rs2  := (mword_of_int 18 : mword 5).
  Notation Rs3  := (mword_of_int 19 : mword 5).

Local Ltac regne := reg_ne_side.

(* ===================================================================== *)
(*  THE HART-CARRYING PIECES: bread's own continuation, its frame bundle  *)
(*  and the register invariant every block carries.                       *)
(*                                                                        *)
(*  [bd_cont] is the function's own [wp_next] obligation, NAMED            *)
(*  (claude-notes/optimization.md: a whole-function proof's post must not  *)
(*  be spelled inline -- it is re-traversed by every proofmode operation,  *)
(*  and here it also appears in seven block-lemma statements).  It is      *)
(*  anchored at an explicit [CID0] rather than at any section's ambient    *)
(*  hart, and [bd_cont_shift] re-anchors it; a block lemma that does not   *)
(*  move the hart forwards it as the IDENTITY.                            *)
(* ===================================================================== *)
Section BreadDefs.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ, !uartGhostG Σ}.

  Context {kt : ktier}.
  Definition bd_cont `{GEN : GenId} `{CID0 : CpuId}
      (j : nat) (bn : bio_names) (V : bio_view Σ)
      (pidv dev bno : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (pj : mword 64) (lks : gset string)
      : iProp Σ :=
    (* THE LITERAL [true], matching SpecBread's crossing: bread PARKS (its
       acquiresleep sleeps), so its continuation is about an arbitrary hart
       whatever SIE was doing.  Spelled [eb] this was sound only because the
       contract had no [eb = false] instance. *)
    wp_next true pj (fun (CID : CpuId) =>
      ∀ (mf : regfile) (k : nat) (bs bsd : list (bv 8)) (d : bool),
        ⌜callee_saved m mf
         /\ mf !!! Regidx Ra0 = bnode k⌝ -∗
        sie_cap_gpr kt mf K eb pj -∗
        cpu_own 0 eb pj eb lks -∗
        trap_csrs_ext kt eb -∗
        cpu_claim_ext eb pj -∗
        pc_is (ret_pc (m !!! Regidx Rra)) -∗
        p_pid pj ↦₄{dq} pidv -∗
        bio_locked bn V k pidv dev bno bs bsd d -∗
        WP (Loop : expr riscv_lang))%I.

  (* Re-anchor [bd_cont] from the hart a block lemma entered at to the hart it
     hands the continuation on at.  [WpSconfVc.wp_next_shift] proves exactly
     this, but cannot see [wp_next]'s [K] through the named [Definition]
     (durable-notes), so it is re-proved here at the unfolded body. *)
  Lemma bd_cont_shift `{GEN : GenId} `{CIDa : CpuId} `{CIDb : CpuId}
      (j : nat) (bn : bio_names) (V : bio_view Σ)
      (pidv dev bno : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (pj : mword 64) (lks : gset string) :
    (* the guard is at the LITERAL [true] now, [bd_cont]'s own index *)
    (true = false \/ pj = zero_reg -> (CIDb : CPU) = (CIDa : CPU)) ->
    bd_cont (CID0 := CIDa)  j bn V pidv dev bno dq m K eb pj lks -∗
    bd_cont (CID0 := CIDb)  j bn V pidv dev bno dq m K eb pj lks.
  Proof.
    intros Hs. rewrite /bd_cont /wp_next.
    iIntros "H" (CID2 Hs2). iApply "H". iPureIntro.
    intro Hb. specialize (Hs2 Hb). specialize (Hs Hb). congruence.
  Qed.

  (* the six frame slots, as one bundle (slot 6 -- offset 0 -- is pushed but
     never written) *)
  Definition bd_frame (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1) 1 ↦₈ (m !!! Regidx Rra) ∗
     pa_stk (m !!! Regidx csp_rs1) 2 ↦₈ (m !!! Regidx Rs0) ∗
     pa_stk (m !!! Regidx csp_rs1) 3 ↦₈ (m !!! Regidx Rs1) ∗
     pa_stk (m !!! Regidx csp_rs1) 4 ↦₈ (m !!! Regidx Rs2) ∗
     pa_stk (m !!! Regidx csp_rs1) 5 ↦₈ (m !!! Regidx Rs3) ∗
     ∃ w : mword 64, pa_stk (m !!! Regidx csp_rs1) 6 ↦₈ w)%I.

  (* the register facts every block lemma carries about its arrival map:
     the frame pointer, the two saved arguments, and agreement with the entry
     map on every callee-saved register bread does not touch. *)
  Definition bd_regs (m M : regfile) : Prop :=
    M !!! Regidx csp_rs1
      = add_vec (m !!! Regidx csp_rs1)
          (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))
    /\ M !!! Regidx Rs2 = m !!! Regidx Ra0
    /\ M !!! Regidx Rs3 = m !!! Regidx Ra1
    /\ (forall c : mword 5, is_cs_idx c = true ->
          c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rtp ->
          M !!! Regidx c = m !!! Regidx c).

End BreadDefs.

(* ===================================================================== *)
(*  THE BLOCKS.  Each is a [Local Lemma] with its OWN [CID0] binder (no    *)
(*  section-ambient hart), so a block whose predecessor migrated is        *)
(*  applied at the hart it actually starts on.                            *)
(* ===================================================================== *)
Section BreadBlocks.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ, !uartGhostG Σ}.

  Context {kt : ktier}.
  (* ================================================================== *)
  (*  THE EPILOGUE (0xb8 .. 0xc6), reached from both arms of the tail.   *)
  (* ================================================================== *)

  Local Lemma bread_epi `{GEN : GenId} `{CID0 : CpuId}
      (j : nat) (bn : bio_names) (V : bio_view Σ) (k : nat)
      (pidv dev bno : mword 32) (dq : dfrac)
      (m M : regfile) (K : nat) (eb : bool)
      (bs_out bsd : list (bv 8)) (d : bool) (lks : gset string) :
    (K_bread <= K)%nat ->
    bd_regs m M ->
    M !!! Regidx Rs1 = bnode k ->
    sie_cap_gpr kt M (K - 6)%nat eb (proc_addr j) -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.bread + 0xb8) : mword 64) -∗
    bd_frame m -∗
    cpu_own 0 eb (proc_addr j) eb lks -∗
    trap_csrs_ext kt eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    bio_locked bn V k pidv dev bno bs_out bsd d -∗
    bd_cont (kt := kt) (CID0 := CID0)  j bn V pidv dev bno dq m K eb (proc_addr j) lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK (HMsp & HMs2 & HMs3 & HMthr) HMs1.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec (m !!! Regidx csp_rs1 : mword 64)
                  (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))).
    iIntros "Hcg #Htext Hpc Hframe Hcnt Hextc Hextm Hppid Hlk Hcont".
    rewrite /bd_frame.
    iDestruct "Hframe" as "(Hr40 & Hr32 & Hr24 & Hr16 & Hr8 & Hg0)".
    iDestruct "Hg0" as (vg0) "Hg0".
    iPoseProof (bdi_b8 with "Htext") as "Hib8".
    iPoseProof (bdi_ba with "Htext") as "Hiba".
    iPoseProof (bdi_bc with "Htext") as "Hibc".
    iPoseProof (bdi_be with "Htext") as "Hibe".
    iPoseProof (bdi_c0 with "Htext") as "Hic0".
    iPoseProof (bdi_c2 with "Htext") as "Hic2".
    iPoseProof (bdi_c4 with "Htext") as "Hic4".
    iPoseProof (bdi_c6 with "Htext") as "Hic6".
    (* the five saved-slot addresses, in the [c.ldsp] leaf's spelling *)
    assert (Hb1 : add_vec spr
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* +0xb8 c.mv a0,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.bread + 0xb8)) Ra0 Rs1
              M (K - 6)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hib8").
    iIntros (CIDe1 Hse1) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (E1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M !!! Regidx Rs1))]> M).
    assert (HE1a0 : E1 !!! Regidx Ra0 = bnode k).
    { rewrite /E1 upd_eq. rewrite HMs1. apply add_vec_zero_l. }
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spr)
      by (rewrite /E1 upd_ne; [exact HMsp | vm_compute; discriminate]).
    assert (Hppba : add_vec_int (mword_of_int (KernelSyms.bread + 0xb8) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0xba))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppba) in "Hpc".
    (* +0xba c.ldsp ra,40(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.bread + 0xba)) (mword_of_int 5 : mword 6) Rra
              E1 (K - 6)%nat (m !!! Regidx Rra) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hiba [Hr40]").
    { iEval (rewrite HE1sp Hb1). iExact "Hr40". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hr40".
    iEval (rewrite HE1sp Hb1) in "Hr40".
    set (E2 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra)]> E1).
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spr)
      by (rewrite /E2 upd_ne; [exact HE1sp | vm_compute; discriminate]).
    assert (Hppbc : add_vec_int (mword_of_int (KernelSyms.bread + 0xba) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0xbc))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppbc) in "Hpc".
    (* +0xbc c.ldsp s0,32(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.bread + 0xbc)) (mword_of_int 4 : mword 6) Rs0
              E2 (K - 6)%nat (m !!! Regidx Rs0) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hibc [Hr32]").
    { iEval (rewrite HE2sp Hb2). iExact "Hr32". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hr32".
    iEval (rewrite HE2sp Hb2) in "Hr32".
    set (E3 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0)]> E2).
    assert (HE3sp : E3 !!! Regidx csp_rs1 = spr)
      by (rewrite /E3 upd_ne; [exact HE2sp | vm_compute; discriminate]).
    assert (Hppbe : add_vec_int (mword_of_int (KernelSyms.bread + 0xbc) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0xbe))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppbe) in "Hpc".
    (* +0xbe c.ldsp s1,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.bread + 0xbe)) (mword_of_int 3 : mword 6) Rs1
              E3 (K - 6)%nat (m !!! Regidx Rs1) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hibe [Hr24]").
    { iEval (rewrite HE3sp Hb3). iExact "Hr24". }
    iIntros (CIDe4 Hse4) "Hcg Hpc Hr24".
    iEval (rewrite HE3sp Hb3) in "Hr24".
    set (E4 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1)]> E3).
    assert (HE4sp : E4 !!! Regidx csp_rs1 = spr)
      by (rewrite /E4 upd_ne; [exact HE3sp | vm_compute; discriminate]).
    assert (Hppc0 : add_vec_int (mword_of_int (KernelSyms.bread + 0xbe) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0xc0))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppc0) in "Hpc".
    (* +0xc0 c.ldsp s2,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.bread + 0xc0)) (mword_of_int 2 : mword 6) Rs2
              E4 (K - 6)%nat (m !!! Regidx Rs2) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hic0 [Hr16]").
    { iEval (rewrite HE4sp Hb4). iExact "Hr16". }
    iIntros (CIDe5 Hse5) "Hcg Hpc Hr16".
    iEval (rewrite HE4sp Hb4) in "Hr16".
    set (E5 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> E4).
    assert (HE5sp : E5 !!! Regidx csp_rs1 = spr)
      by (rewrite /E5 upd_ne; [exact HE4sp | vm_compute; discriminate]).
    assert (Hppc2 : add_vec_int (mword_of_int (KernelSyms.bread + 0xc0) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0xc2))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppc2) in "Hpc".
    (* +0xc2 c.ldsp s3,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.bread + 0xc2)) (mword_of_int 1 : mword 6) Rs3
              E5 (K - 6)%nat (m !!! Regidx Rs3) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hic2 [Hr8]").
    { iEval (rewrite HE5sp Hb5). iExact "Hr8". }
    iIntros (CIDe6 Hse6) "Hcg Hpc Hr8".
    iEval (rewrite HE5sp Hb5) in "Hr8".
    set (E6 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3)]> E5).
    assert (HE6sp : E6 !!! Regidx csp_rs1 = spr)
      by (rewrite /E6 upd_ne; [exact HE5sp | vm_compute; discriminate]).
    assert (Hppc4 : add_vec_int (mword_of_int (KernelSyms.bread + 0xc2) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0xc4))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppc4) in "Hpc".
    (* +0xc4 c.addi16sp sp,48 *)
    set (E7 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (E6 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E6).
    assert (Hwv : add_vec (E6 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0).
    { rewrite HE6sp. unfold spr, sp0. apply frame_cancel_48. }
    assert (Hpop : E6 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E6 !!! Regidx csp_rs1)
                               (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6).
    { rewrite Hwv HE6sp. unfold spr, sp0, pa_stk, add_vec_int.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iAssert (stack_own (KTR := kt) sp0 6) with "[Hr40 Hr32 Hr24 Hr16 Hr8 Hg0]" as "Hframe6".
    { rewrite (stack_own_slots (KTR := kt)). cbn [seq].
      iSplitL "Hr40"; [iExists _; iExact "Hr40"|].
      iSplitL "Hr32"; [iExists _; iExact "Hr32"|].
      iSplitL "Hr24"; [iExists _; iExact "Hr24"|].
      iSplitL "Hr16"; [iExists _; iExact "Hr16"|].
      iSplitL "Hr8";  [iExists _; iExact "Hr8"|].
      iSplitL "Hg0";  [iExists _; iExact "Hg0"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe6".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.bread + 0xc4)) (mword_of_int 3 : mword 6)
              E6 (K - 6)%nat 6 eb Hpop with "Hcg Hpc Hic4 Hframe6").
    iIntros (CIDe7 Hse7) "Hcg Hpc".
    assert (Hnk : ((K - 6) + 6)%nat = K) by (lia).
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg
      (add_vec (E6 !!! Regidx csp_rs1)
         (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E6) with E7.
    assert (Hppc6 : add_vec_int (mword_of_int (KernelSyms.bread + 0xc4) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0xc6))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppc6) in "Hpc".
    assert (HE7ra : E7 !!! Regidx Rra = m !!! Regidx Rra).
    { rewrite /E7 upd_ne; [| vm_compute; discriminate].
      rewrite /E6 upd_ne; [| vm_compute; discriminate].
      rewrite /E5 upd_ne; [| vm_compute; discriminate].
      rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_eq. reflexivity. }
    (* +0xc6 c.ret *)
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.bread + 0xc6)) Rra E7 K eb
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hic6").
    iIntros (CIDe8 Hse8) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    iEval (rewrite HE7ra) in "Hpc".
    assert (HE7a0 : E7 !!! Regidx Ra0 = bnode k).
    { rewrite /E7 upd_ne; [| vm_compute; discriminate].
      rewrite /E6 upd_ne; [| vm_compute; discriminate].
      rewrite /E5 upd_ne; [| vm_compute; discriminate].
      rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [exact HE1a0 | vm_compute; discriminate]. }
    (* [cpu_own] is the one resource a leaf's [wp_next] does NOT re-deliver;
       the trap-CSR complement is hart-indexed too and travels the same way. *)
    iDestruct (cpu_own_transport CID0 CIDe8 0%nat eb (proc_addr j) eb 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CIDe8 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CIDe8 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextm") as "Hextm".
    rewrite /bd_cont.
    iSpecialize ("Hcont" $! CIDe8 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E7 k bs_out bsd d with "[%] Hcg Hcnt Hextc Hextm Hpc Hppid Hlk").
    split; [| exact HE7a0].
    (* callee_saved m E7 *)
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rtp ->
              E7 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N18 N19 N4.
      rewrite /E7 upd_ne; [| regne].
      rewrite /E6 upd_ne; [| regne].
      rewrite /E5 upd_ne; [| regne].
      rewrite /E4 upd_ne; [| regne].
      rewrite /E3 upd_ne; [| regne].
      rewrite /E2 upd_ne; [| regne].
      rewrite /E1 upd_ne; [| regne].
      exact (HMthr c Hcs N2 N8 N9 N18 N19 N4). }
    unfold callee_saved.
    assert (Hc2 : E7 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1).
    { rewrite /E7 upd_eq. unfold regval_into_reg. exact Hwv. }
    assert (Hc8 : E7 !!! Regidx Rs0 = m !!! Regidx Rs0).
    { rewrite /E7 upd_ne; [| vm_compute; discriminate].
      rewrite /E6 upd_ne; [| vm_compute; discriminate].
      rewrite /E5 upd_ne; [| vm_compute; discriminate].
      rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_eq. reflexivity. }
    assert (Hc9 : E7 !!! Regidx Rs1 = m !!! Regidx Rs1).
    { rewrite /E7 upd_ne; [| vm_compute; discriminate].
      rewrite /E6 upd_ne; [| vm_compute; discriminate].
      rewrite /E5 upd_ne; [| vm_compute; discriminate].
      rewrite /E4 upd_eq. reflexivity. }
    assert (Hc18 : E7 !!! Regidx Rs2 = m !!! Regidx Rs2).
    { rewrite /E7 upd_ne; [| vm_compute; discriminate].
      rewrite /E6 upd_ne; [| vm_compute; discriminate].
      rewrite /E5 upd_eq. reflexivity. }
    assert (Hc19 : E7 !!! Regidx Rs3 = m !!! Regidx Rs3).
    { rewrite /E7 upd_ne; [| vm_compute; discriminate].
      rewrite /E6 upd_eq. reflexivity. }
    repeat split;
      first [ exact Hc2 | exact Hc8 | exact Hc9 | exact Hc18 | exact Hc19
            | apply Hthread; vm_compute; first [reflexivity | discriminate] ].
  Qed.

  (* ================================================================== *)
  (*  THE TAIL (0xb4 .. 0xd4): the (a) checkout swap at the [lw a5,0(s1)] *)
  (*  that reads b->valid, the valid test, and the disk-read arm.         *)
  (* ================================================================== *)

  Local Lemma bread_tail `{GEN : GenId} `{CID0 : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (V : bio_view Σ) (k : nat) (q : Qp)
      (pidv dev bno : mword 32) (dq : dfrac)
      (m M : regfile) (K : nat) (eb : bool) (lks : gset string) :
    (K_bread <= K)%nat ->
    (uint bno < 2147483648)%Z ->
    (k < NBUF)%nat ->
    bv_gd V = γd ->
    uint bno ∈ bv_cov V ->
    dev = bv_dev V ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    bd_regs m M ->
    M !!! Regidx Rs1 = bnode k ->
    sie_cap_gpr kt M (K - 6)%nat eb (proc_addr j) -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.bread + 0xb4) : mword 64) -∗
    inv bioN (buf_escrow_body bn V k) -∗
    bd_frame m -∗
    cpu_own 0 eb (proc_addr j) eb lks -∗
    trap_csrs_ext kt eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    procs_inv (kt := kt) γs -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    sleeplocked (snd (bn_slk bn k)) -∗
    sl_pid (buf_lock (bnode k)) ↦₄ pidv -∗
    bown bn k -∗
    bref bn k q dev bno -∗
    bd_cont (kt := kt) (CID0 := CID0)  j bn V pidv dev bno dq m K eb (proc_addr j) lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hbno Hk Hgd Hcov Hdv Hj Hgl Hregs HMs1.
    pose proof Hregs as (HMsp & HMs2 & HMs3 & HMthr).
    iIntros "Hcg #Htext Hpc #Hesc Hframe Hcnt Hextc Hextm #Hprocs Hppid".
    iIntros "#Hdev #Hgeom #Hdlock Hstok Hpid Hbown Hbref Hcont".
    (* the tail runs at depth 0 -- bread's own acquire/release around the
       buffer table is already behind it -- so the held set is forced empty
       and the rw call's order premise needs no hypothesis of its own. *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlkempty Hcnt]".
    iDestruct "Hbref" as "(Hrtok & Hrdev & Hrbno)".
    iPoseProof (bdi_b4 with "Htext") as "Hib4".
    iPoseProof (bdi_b6 with "Htext") as "Hib6".
    assert (Hva : add_vec (rget M Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12))
                  = b_valid (bpa k)).
    { rgne. rewrite HMs1 bd_s0. rewrite /b_valid /bpa. apply kv_addv_zero. }
    (* ---- +0xb4 c.lw a5,0(s1): the CHECKOUT, at this one instruction ---- *)
    iApply (wp_lw_au_s_sconf (dqm := DfracOwn 1) true
              (mword_of_int (KernelSyms.bread + 0xb4)) Ra5 Rs1 (mword_of_int 0 : mword 12)
              M (K - 6)%nat
              (fun v : mword 32 =>
                 (∃ (vb : bool) (bs : list (bv 8)),
                    ⌜v = (if vb then (mword_of_int 1 : mword 32)
                          else (mword_of_int 0 : mword 32))⌝ ∗
                    b_valid (bpa k) ↦₄ v ∗
                    b_dev (bpa k) ↦₄{DfracOwn (1/2)} dev ∗
                    buf_own (bpa k) bno (mword_of_int 0 : mword 32) bs ∗
                    buf_pay bn V k vb dev bno bs)%I)
              (⊤ ∖ ↑minstretN ∖ ↑bioN) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(solve_ndisj)
              with "Hcg Hpc Hib4 [Hbown Hrtok Hrdev Hrbno]").
    { iInv "Hesc" as ">Hbody" "Hclose".
      iDestruct (escrow_swap_checkout bn V k q dev bno
                   with "Hbody Hbown Hrtok Hrdev Hrbno") as "[Hbody Hpark2]".
      iDestruct "Hpark2" as (vb bs) "(Hvld & Hbdev & Hbuf & Hpay)".
      iModIntro.
      iExists (if vb then (mword_of_int 1 : mword 32) else (mword_of_int 0 : mword 32)).
      iEval (rewrite -Hva) in "Hvld". iFrame "Hvld".
      iIntros "Hvld". iEval (rewrite Hva) in "Hvld".
      iMod ("Hclose" with "[Hbody]") as "_". { iApply bi.later_intro. iExact "Hbody". }
      iModIntro. iExists vb, bs. iSplitR; [by iPureIntro|].
      iFrame "Hvld Hbdev Hbuf Hpay". }
    iIntros (vld CIDt1 Hst1) "Hcg Hpc H".
    iDestruct "H" as (vb bs) "(%Hpin & Hvld & Hbdev & Hbuf & Hpay)".
    iDestruct (cpu_own_transport CID0 CIDt1 0%nat eb (proc_addr j) eb 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    set (T1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (vld : mword 32))]> M).
    assert (HT1s1 : T1 !!! Regidx Rs1 = bnode k)
      by (rewrite /T1 upd_ne; [exact HMs1 | vm_compute; discriminate]).
    assert (HT1a5 : T1 !!! Regidx Ra5 = sign_extend' 64 (vld : mword 32))
      by (rewrite /T1; apply upd_eq).
    assert (HT1regs : bd_regs m T1).
    { rewrite /bd_regs. split_and!.
      - rewrite /T1 upd_ne; [exact HMsp | vm_compute; discriminate].
      - rewrite /T1 upd_ne; [exact HMs2 | vm_compute; discriminate].
      - rewrite /T1 upd_ne; [exact HMs3 | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N4.
        rewrite /T1 upd_ne; [| apply not_eq_sym; apply is_cs_idx_true_neq;
                               [vm_compute; reflexivity | assumption]].
        exact (HMthr c Hcs N2 N8 N9 N18 N19 N4). }
    assert (Hppb6 : add_vec_int (mword_of_int (KernelSyms.bread + 0xb4) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0xb6))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppb6) in "Hpc".
    destruct vb as [|]; cbv iota in Hpin.
    - (* ============ b->valid = 1: straight to the epilogue ============ *)
      (* a VALID covered buffer's parked payload says its bytes ARE the
         block's logical content, with the disk cell alongside: the handle
         assembles with no disk read at all. *)
      iEval (rewrite Hpin) in "Hvld".
      iAssert (∃ (bsd : list (bv 8)) (d : bool),
                 disk_block (bv_gd V) (uint bno) bsd ∗
                 bio_pay bn V k dev bno bs bsd d)%I with "[Hpay]" as "Hp".
      { rewrite /buf_pay. case_decide as Hc; [| exfalso; exact (Hc Hcov)].
        iDestruct "Hpay" as "[_ Hp]". iExact "Hp". }
      iDestruct "Hp" as (bsd d) "[Hdb Hpy]".
      assert (Hbeqz : eq_vec (T1 !!! Regidx Ra5) zero_reg = false).
      { rewrite HT1a5 Hpin. exact bd_valid1_nonzero. }
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.bread + 0xb6)) (mword_of_int 9 : mword 8)
                (Cregidx (mword_of_int 7)) Ra5 T1 (K - 6)%nat eb
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; exact Hbeqz)
                with "Hcg Hpc Hib6").
      iIntros (CIDv2 Hsv2) "Hcg Hpc".
      assert (Hppb8 : add_vec_int (mword_of_int (KernelSyms.bread + 0xb6) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0xb8))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppb8) in "Hpc".
      iDestruct (cpu_own_transport CIDt1 CIDv2 0%nat eb (proc_addr j) eb 
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CID0 CIDv2 eb (proc_addr j)
                   ltac:(wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID0 CIDv2 eb (proc_addr j)
                   ltac:(wp_next_chain) with "Hextm") as "Hextm".
      iDestruct (bd_cont_shift (CIDa := CID0) (CIDb := CIDv2)  j bn V pidv dev bno dq
                   m K eb (proc_addr j) lks ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (bread_epi (CID0 := CIDv2)  j bn V k pidv dev bno dq m T1 K eb
                bs bsd d lks HK HT1regs HT1s1
                with "Hcg Htext Hpc Hframe Hcnt Hextc Hextm Hppid
                      [Hstok Hpid Hvld Hbdev Hbuf Hdb Hpy] Hcont").
      rewrite /bio_locked /bio_held /bpa.
      iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      iFrame "Hstok Hpid Hvld Hbdev Hbuf Hdb Hpy".
    - (* ============ b->valid = 0: the disk read ============ *)
      (* the parked payload of an INVALID covered buffer IS the block's pool
         bundle: whoever wins the sleeplock race after a recycle finds it
         here and does the fill.  That is this thread. *)
      iAssert (pool_blk V (uint bno)) with "[Hpay]" as "Hpool".
      { rewrite /buf_pay. case_decide as Hc; [| exfalso; exact (Hc Hcov)].
        iDestruct "Hpay" as "[_ Hp]". iExact "Hp". }
      iDestruct "Hpool" as (bsl) "[Hdb Hcl]".
      iEval (rewrite Hgd) in "Hdb".
      iPoseProof (bdi_c8 with "Htext") as "Hic8".
      iPoseProof (bdi_ca with "Htext") as "Hica".
      iPoseProof (bdi_cc with "Htext") as "Hicc".
      assert (Hbeqz : eq_vec (T1 !!! Regidx Ra5) zero_reg = true).
      { rewrite HT1a5 Hpin. exact brc_word_zero_eqv. }
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.bread + 0xb6)) (mword_of_int 9 : mword 8)
                (Cregidx (mword_of_int 7)) Ra5 T1 (K - 6)%nat eb
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; exact Hbeqz) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hib6").
      iApply bi.later_intro. iIntros (CIDt2 Hst2) "Hcg Hpc".
      assert (Htgtc8 : add_vec (mword_of_int (KernelSyms.bread + 0xb6) : mword 64)
                         (sign_extend' 64 (sign_extend' 13
                            (concat_vec (mword_of_int 9 : mword 8) ('b"0"))))
                       = mword_of_int (KernelSyms.bread + 0xc8))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtc8) in "Hpc".
      (* +0xc8 c.li a1,0 : rw's write flag is FALSE *)
      assert (Hli0 : add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))
                     = (mword_of_int 0 : mword 64))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.bread + 0xc8)) Ra1 (mword_of_int 0 : mword 6)
                (mword_of_int 0 : mword 64) T1 (K - 6)%nat eb
                ltac:(vm_compute; discriminate) ltac:(rdok) Hli0
                with "Hcg Hpc Hic8").
      iIntros (CIDt3 Hst3) "Hcg Hpc".
      set (T2 := <[Regidx Ra1 := regval_into_reg (mword_of_int 0 : mword 64)]> T1).
      assert (HT2s1 : T2 !!! Regidx Rs1 = bnode k)
        by (rewrite /T2 upd_ne; [exact HT1s1 | vm_compute; discriminate]).
      assert (Hppca : add_vec_int (mword_of_int (KernelSyms.bread + 0xc8) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0xca))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppca) in "Hpc".
      (* +0xca c.mv a0,s1 *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.bread + 0xca)) Ra0 Rs1
                T2 (K - 6)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hica").
      iIntros (CIDt4 Hst4) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (T3 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (T2 !!! Regidx Rs1))]> T2).
      assert (Hppcc : add_vec_int (mword_of_int (KernelSyms.bread + 0xca) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0xcc))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppcc) in "Hpc".
      (* ===== +0xcc jal ra,virtio_disk_rw ===== *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.bread + 0xcc)) Rra (mword_of_int 11318 : mword 21)
                T3 (K - 6)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hicc").
      iIntros (CIDt5 Hst5) "Hcg Hpc".
      set (T4 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.bread + 0xcc) : mword 64) 4)]> T3).
      assert (Htgtrw : add_vec (mword_of_int (KernelSyms.bread + 0xcc) : mword 64)
                         (sign_extend' 64 (mword_of_int 11318 : mword 21))
                       = mword_of_int KernelSyms.virtio_disk_rw)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtrw) in "Hpc".
      assert (HT4a0 : T4 !!! Regidx Ra0 = bnode k).
      { rewrite /T4 upd_ne; [| vm_compute; discriminate].
        rewrite /T3 upd_eq. unfold regval_into_reg. rewrite HT2s1. apply add_vec_zero_l. }
      assert (HT4a1 : T4 !!! Regidx Ra1 = (mword_of_int 0 : mword 64)).
      { rewrite /T4 upd_ne; [| vm_compute; discriminate].
        rewrite /T3 upd_ne; [| vm_compute; discriminate].
        rewrite /T2 upd_eq. reflexivity. }
      assert (HT4s1 : T4 !!! Regidx Rs1 = bnode k).
      { rewrite /T4 upd_ne; [| vm_compute; discriminate].
        rewrite /T3 upd_ne; [| vm_compute; discriminate]. exact HT2s1. }
      assert (HT4thr : forall c : mword 5, is_cs_idx c = true ->
                         T4 !!! Regidx c = T1 !!! Regidx c).
      { intros c Hcs.
        rewrite /T4 upd_ne; [| regne].
        rewrite /T3 upd_ne; [| regne].
        rewrite /T2 upd_ne; [reflexivity | regne]. }
      assert (HT4ra : T4 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.bread + 0xcc) : mword 64) 4)
        by (rewrite /T4; apply upd_eq).
      assert (Hkdata : forall kk : nat, (kk < 1024)%nat ->
                addr_is_kdata (pa_add (b_data (T4 !!! Regidx Ra0)) kk)).
      { intros kk Hkk. rewrite HT4a0. exact (bnode_data_kdata k kk Hk Hkk). }
      assert (HKrw : (K_virtio_disk_rw <= K - 6)%nat)
        by (lia).
      iDestruct (cpu_own_transport CIDt1 CIDt5 0%nat eb (proc_addr j) eb 
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CID0 CIDt5 eb (proc_addr j)
                   ltac:(wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID0 CIDt5 eb (proc_addr j)
                   ltac:(wp_next_chain) with "Hextm") as "Hextm".
      iApply (RW.wp_virtio_disk_rw_sconf kt γs j γl γu γd γk pd pav pu T4
                (K - 6)%nat eb bno (mword_of_int 0 : mword 32) bs bsl eb
                True%I lks
                HKrw Hbno Hkdata Hj Hgl
                with "Hcg Hcnt Hextc Hextm Htext Hpc Hprocs
                      Hdev Hgeom Hdlock [Hbuf] Hdb []").
      all: try lkbelow.
      { iEval (rewrite HT4a0). rewrite /bpa. iExact "Hbuf". }
      (* bread's rw call is a READ: no disk byte moves, so the identity
         permit at the trivial receipt is the honest one.  Permits are
         uniform, which is what keeps the DMA completion from having to know
         the direction. *)
      { iApply disk_write_permit_trivial. }
      (* rw PARKS: it returns on hart [CIDrw], handing the trap-CSR
         complement back too. *)
      iIntros (CIDrw Hsrw mR) "%Hcs2 Hcg Hcnt Hextc Hextm Hpc Hbuf Hdb _".
      iPoseProof (bdi_d0 with "Htext") as "Hid0".
      iPoseProof (bdi_d2 with "Htext") as "Hid2".
      iPoseProof (bdi_d4 with "Htext") as "Hid4".
      iEval (rewrite (bd_wr_false _ bs bsl HT4a1)) in "Hbuf".
      iEval (rewrite (bd_wr_false _ bs bsl HT4a1)) in "Hdb".
      iEval (rewrite -Hgd) in "Hdb".
      iEval (rewrite HT4a0) in "Hbuf".
      assert (Hpcd0 : ret_pc (T4 !!! Regidx Rra) = mword_of_int (KernelSyms.bread + 0xd0)).
      { rewrite HT4ra. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hpcd0) in "Hpc".
      assert (HmRs1 : mR !!! Regidx Rs1 = bnode k)
        by (rewrite (callee_saved_lookup Hcs2 Rs1 ltac:(vm_compute; reflexivity)); exact HT4s1).
      (* +0xd0 c.li a5,1 *)
      assert (Hli1 : add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))
                     = (mword_of_int 1 : mword 64))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.bread + 0xd0)) Ra5 (mword_of_int 1 : mword 6)
                (mword_of_int 1 : mword 64) mR (K - 6)%nat eb
                ltac:(vm_compute; discriminate) ltac:(rdok) Hli1
                with "Hcg Hpc Hid0").
      iIntros (CIDt6 Hst6) "Hcg Hpc".
      set (T5 := <[Regidx Ra5 := regval_into_reg (mword_of_int 1 : mword 64)]> mR).
      assert (HT5s1 : T5 !!! Regidx Rs1 = bnode k)
        by (rewrite /T5 upd_ne; [exact HmRs1 | vm_compute; discriminate]).
      assert (HT5a5 : T5 !!! Regidx Ra5 = (mword_of_int 1 : mword 64))
        by (rewrite /T5; apply upd_eq).
      assert (Hppd2 : add_vec_int (mword_of_int (KernelSyms.bread + 0xd0) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0xd2))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppd2) in "Hpc".
      (* +0xd2 c.sw a5,0(s1) : b->valid = 1 (we own the cell outright) *)
      assert (Hva5 : add_vec (rget T5 Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12))
                     = b_valid (bpa k)).
      { rgne. rewrite HT5s1 bd_s0. rewrite /b_valid /bpa. apply kv_addv_zero. }
      iEval (rewrite -Hva5) in "Hvld".
      iApply (wp_csw_s_sconf (mword_of_int (KernelSyms.bread + 0xd2)) Ra5 Rs1 (mword_of_int 0 : mword 12)
                T5 (K - 6)%nat (vld : mword 32) eb
                with "Hcg Hpc Hid2 Hvld").
      iIntros (CIDt7 Hst7) "Hcg Hpc Hvld".
      iEval (rewrite Hva5) in "Hvld".
      assert (Hstv : trunc32 (rget T5 Ra5) = (mword_of_int 1 : mword 32)).
      { rgne. rewrite HT5a5. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hstv) in "Hvld".
      assert (Hppd4 : add_vec_int (mword_of_int (KernelSyms.bread + 0xd2) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0xd4))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppd4) in "Hpc".
      (* +0xd4 c.j -0x1c : back to the epilogue join *)
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.bread + 0xd4))
                (sign_extend' 21 (concat_vec (mword_of_int 2034 : mword 11) ('b"0")))
                T5 (K - 6)%nat eb ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hid4").
      iIntros (CIDt8 Hst8). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htgtb8 : add_vec (mword_of_int (KernelSyms.bread + 0xd4) : mword 64)
                         (sign_extend' 64 (sign_extend' 21
                            (concat_vec (mword_of_int 2034 : mword 11) ('b"0"))))
                       = mword_of_int (KernelSyms.bread + 0xb8))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtb8) in "Hpc".
      assert (HT5regs : bd_regs m T5).
      { rewrite /bd_regs. split_and!.
        - rewrite /T5 upd_ne; [| vm_compute; discriminate].
          rewrite (callee_saved_lookup Hcs2 csp_rs1 ltac:(vm_compute; reflexivity)).
          rewrite (HT4thr csp_rs1 ltac:(vm_compute; reflexivity)).
          rewrite /T1 upd_ne; [exact HMsp | vm_compute; discriminate].
        - rewrite /T5 upd_ne; [| vm_compute; discriminate].
          rewrite (callee_saved_lookup Hcs2 Rs2 ltac:(vm_compute; reflexivity)).
          rewrite (HT4thr Rs2 ltac:(vm_compute; reflexivity)).
          rewrite /T1 upd_ne; [exact HMs2 | vm_compute; discriminate].
        - rewrite /T5 upd_ne; [| vm_compute; discriminate].
          rewrite (callee_saved_lookup Hcs2 Rs3 ltac:(vm_compute; reflexivity)).
          rewrite (HT4thr Rs3 ltac:(vm_compute; reflexivity)).
          rewrite /T1 upd_ne; [exact HMs3 | vm_compute; discriminate].
        - intros c Hcs N2 N8 N9 N18 N19 N4.
          rewrite /T5 upd_ne; [| apply not_eq_sym; apply is_cs_idx_true_neq;
                                 [vm_compute; reflexivity | assumption]].
          rewrite (callee_saved_lookup Hcs2 c Hcs).
          rewrite (HT4thr c Hcs).
          rewrite /T1 upd_ne; [| apply not_eq_sym; apply is_cs_idx_true_neq;
                                 [vm_compute; reflexivity | assumption]].
          exact (HMthr c Hcs N2 N8 N9 N18 N19 N4). }
      iDestruct (cpu_own_transport CIDrw CIDt8 0%nat eb (proc_addr j) eb 
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CIDrw CIDt8 eb (proc_addr j)
                   ltac:(wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CIDrw CIDt8 eb (proc_addr j)
                   ltac:(wp_next_chain) with "Hextm") as "Hextm".
      iDestruct (bd_cont_shift (CIDa := CID0) (CIDb := CIDt8)  j bn V pidv dev bno dq
                   m K eb (proc_addr j) lks ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iAssert (bio_pay bn V k dev bno bsl bsl false) with "[Hcl]" as "Hpy".
      { rewrite /bio_pay. cbv iota. iFrame "Hcl". done. }
      iApply (bread_epi (CID0 := CIDt8)  j bn V k pidv dev bno dq m T5 K eb
                bsl bsl false lks HK HT5regs HT5s1
                with "Hcg Htext Hpc Hframe Hcnt Hextc Hextm Hppid
                      [Hstok Hpid Hvld Hbdev Hbuf Hdb Hpy] Hcont").
      rewrite /bio_locked /bio_held /bpa.
      iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      iFrame "Hstok Hpid Hvld Hbdev Hbuf Hdb Hpy".
  Qed.

  (* ================================================================== *)
  (*  THE HIT (0x48 .. 0x62): refcnt++, release, acquiresleep, j tail.    *)
  (*  0x48..0x56 run with the bcache lock HELD, hence at the literal      *)
  (*  [false] index, hence at this lemma's own hart.                      *)
  (* ================================================================== *)

  Local Lemma bread_hit `{GEN : GenId} `{CID0 : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (V : bio_view Σ) (k : nat)
      (Mg : gmap nat (Qp * positive)) (ord : list nat) (devs bnos : nat -> mword 32)
      (pidv dev bno : mword 32) (dq : dfrac)
      (m M : regfile) (K : nat) (eb : bool) (lks : gset string) :
    (K_bread <= K)%nat ->
    (uint bno < 2147483648)%Z ->
    (k < NBUF)%nat ->
    devs k = dev ->
    bnos k = bno ->
    bv_gd V = γd ->
    uint bno ∈ bv_cov V ->
    dev = bv_dev V ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    bd_regs m M ->
    M !!! Regidx Rs1 = bnode k ->
    (* the block owns "bcache" on entry (0x48..0x56); this Lemma's own
       release below needs [Hfresh] for its [Hsetback] simplification, and
       the ensuing acquiresleep call needs the bound lifted to "sleep lock"
       (rank 6) via [locks_below_mono]. *)
    locks_below lks "bcache" ->
    sie_cap_gpr kt M (trap_res eb + (K - 6))%nat false (proc_addr j) -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.bread + 0x48) : mword 64) -∗
    bio_ctx bn V -∗
    bd_frame m -∗
    cpu_own 1 eb (proc_addr j) false ({["bcache"]} ∪ lks) -∗
    arm_pay kt 0 eb (proc_addr j) -∗
    trap_csrs_ext kt eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    locked (bn_lk bn) cpu_id -∗
    bcache_scan bn V Mg ord devs bnos -∗
    bslot bn -∗
    procs_inv (kt := kt) γs -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    bd_cont (kt := kt) (CID0 := CID0)  j bn V pidv dev bno dq m K eb (proc_addr j) lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hbno Hk Hdevs Hbnos Hgd Hcov Hdv Hj Hgl Hregs HMs1 Hbelow.
    pose proof Hregs as (HMsp & HMs2 & HMs3 & HMthr).
    pose proof (locks_below_not_elem _ _ Hbelow) as Hfresh.
    iIntros "Hcg #Htext Hpc #Hbio Hframe Hcnt Hpay Hextc Hextm Htok Hscan Hbslot".
    iIntros "#Hprocs Hppid #Hdev #Hgeom #Hdlock Hcont".
    iDestruct (bio_ctx_lock with "Hbio") as "#Hlock".
    iDestruct (bio_ctx_buf bn V k Hk with "Hbio") as "[#Hslk #Hesc0]".
    iDestruct (buf_escrow_inv with "Hesc0") as "#Hesc".
    iPoseProof (bdi_48 with "Htext") as "Hi48".
    iPoseProof (bdi_4a with "Htext") as "Hi4a".
    iPoseProof (bdi_4c with "Htext") as "Hi4c".
    iPoseProof (bdi_4e with "Htext") as "Hi4e".
    iPoseProof (bdi_52 with "Htext") as "Hi52".
    iPoseProof (bdi_56 with "Htext") as "Hi56".
    iPoseProof (bdi_5a with "Htext") as "Hi5a".
    iPoseProof (bdi_5e with "Htext") as "Hi5e".
    iDestruct (bcache_scan_incr bn V Mg ord devs bnos k Hk with "Hscan Hbslot")
      as (cw) "[Hcell Hclose]".
    (* ---- +0x48 c.lw a5,64(s1) ---- *)
    assert (Hpa : add_vec (rget M Rs1) (sign_extend' 64 (mword_of_int 64 : mword 12))
                  = brefcnt k).
    { rgne. rewrite HMs1 bd_s64. rewrite /brefcnt /bpa /pa_add /add_vec_int. reflexivity. }
    iEval (rewrite -Hpa) in "Hcell".
    iApply (wp_clw_s_sconf (mword_of_int (KernelSyms.bread + 0x48)) Ra5 Rs1 (mword_of_int 64 : mword 12)
              M (trap_res eb + (K - 6))%nat (cw : mword 32) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi48 Hcell").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hcell".
    iEval (rewrite Hpa) in "Hcell".
    set (H1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (cw : mword 32))]> M).
    assert (HH1a5 : H1 !!! Regidx Ra5 = sign_extend' 64 (cw : mword 32))
      by (rewrite /H1; apply upd_eq).
    assert (HH1s1 : H1 !!! Regidx Rs1 = bnode k)
      by (rewrite /H1 upd_ne; [exact HMs1 | vm_compute; discriminate]).
    assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.bread + 0x48) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0x4a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4a) in "Hpc".
    (* ---- +0x4a c.addiw a5,a5,1 ---- *)
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.bread + 0x4a)) Ra5 (mword_of_int 1 : mword 6)
              H1 (trap_res eb + (K - 6))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4a").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (H2 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (subrange_vec_dec
                     (add_vec (H1 !!! Regidx Ra5)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> H1).
    assert (HH2s1 : H2 !!! Regidx Rs1 = bnode k)
      by (rewrite /H2 upd_ne; [exact HH1s1 | vm_compute; discriminate]).
    assert (Hpp4c : add_vec_int (mword_of_int (KernelSyms.bread + 0x4a) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0x4c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4c) in "Hpc".
    (* ---- +0x4c c.sw a5,64(s1) ---- *)
    assert (Hpa2 : add_vec (rget H2 Rs1) (sign_extend' 64 (mword_of_int 64 : mword 12))
                   = brefcnt k).
    { rgne. rewrite HH2s1 bd_s64. rewrite /brefcnt /bpa /pa_add /add_vec_int. reflexivity. }
    iEval (rewrite -Hpa2) in "Hcell".
    iApply (wp_csw_s_sconf (mword_of_int (KernelSyms.bread + 0x4c)) Ra5 Rs1 (mword_of_int 64 : mword 12)
              H2 (trap_res eb + (K - 6))%nat (cw : mword 32) false
              with "Hcg Hpc Hi4c Hcell").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hcell".
    iEval (rewrite Hpa2) in "Hcell".
    assert (Hstv : trunc32 (rget H2 Ra5) = incr32 (cw : mword 32)).
    { rgne. rewrite /H2 upd_eq. unfold regval_into_reg. rewrite HH1a5. reflexivity. }
    iEval (rewrite Hstv) in "Hcell".
    iMod ("Hclose" with "Hcell") as "[HRres Href]".
    iDestruct "Href" as (qref) "Href".
    iEval (rewrite Hdevs Hbnos) in "Href".
    assert (Hpp4e : add_vec_int (mword_of_int (KernelSyms.bread + 0x4c) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0x4e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4e) in "Hpc".
    (* ---- +0x4e / +0x52 : a0 := &bcache ; +0x56 jal release ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.bread + 0x4e)) Ra0 (mword_of_int 0x15 : mword 20)
              H2 (trap_res eb + (K - 6))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4e").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (H3 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.bread + 0x4e) : mword 64)
                     (auipc_off (mword_of_int 0x15 : mword 20)))]> H2).
    assert (Hpp52 : add_vec_int (mword_of_int (KernelSyms.bread + 0x4e) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0x52))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp52) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.bread + 0x52)) Ra0 Ra0 (mword_of_int 1620 : mword 12)
              H3 (trap_res eb + (K - 6))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi52").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (H4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (H3 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 1620 : mword 12)))]> H3).
    assert (HH4a0 : H4 !!! Regidx Ra0 = bcache_addr).
    { rewrite /H4 upd_eq /H3 upd_eq. rewrite /bcache_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp56 : add_vec_int (mword_of_int (KernelSyms.bread + 0x52) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0x56))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp56) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.bread + 0x56)) Rra (mword_of_int 2089102 : mword 21)
              H4 (trap_res eb + (K - 6))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi56").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (H5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.bread + 0x56) : mword 64) 4)]> H4).
    assert (Htgtrel : add_vec (mword_of_int (KernelSyms.bread + 0x56) : mword 64)
                        (sign_extend' 64 (mword_of_int 2089102 : mword 21))
                      = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtrel) in "Hpc".
    assert (HH5thr : forall c : mword 5, is_cs_idx c = true ->
                       H5 !!! Regidx c = M !!! Regidx c).
    { intros c Hcs.
      rewrite /H5 upd_ne; [| regne].
      rewrite /H4 upd_ne; [| regne].
      rewrite /H3 upd_ne; [| regne].
      rewrite /H2 upd_ne; [| regne].
      rewrite /H1 upd_ne; [reflexivity | regne]. }
    assert (HH5a0 : H5 !!! Regidx Ra0 = bcache_addr)
      by (rewrite /H5 upd_ne; [exact HH4a0 | vm_compute; discriminate]).
    assert (HH5ra : H5 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.bread + 0x56) : mword 64) 4)
      by (rewrite /H5; apply upd_eq).
    iApply (R.wp_release_sconf kt (bn_lk bn) bcache_addr "bcache"%string (bcache_res bn V) H5
              0%nat eb (proc_addr j) (K - 6)%nat ({["bcache"]} ∪ lks)
              ltac:(rewrite HH5a0; apply bv_eq; vm_compute; reflexivity)
              ltac:(lia)
              with "Hcg Htext Hpc [Hlock] Htok HRres Hcnt Hpay").
    { iExact "Hlock". }
    iIntros (CIDr Hsr mr) "Hcg Hpc %Hrelpins Hcnt".
    assert (Hsetback : ({["bcache"]} ∪ lks) ∖ {["bcache"]} = lks)
      by (apply locks_add_del_below; lkbelow).
    iEval (rewrite Hsetback) in "Hcnt".
    assert (Hpc5a : ret_pc (H5 !!! Regidx Rra) = mword_of_int (KernelSyms.bread + 0x5a)).
    { rewrite HH5ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc5a) in "Hpc".
    pose proof Hrelpins as Hrelpins_cs.
    assert (HmrX : forall c : mword 5, is_cs_idx c = true ->
                     mr !!! Regidx c = M !!! Regidx c).
    { intros c Hcs. rewrite (callee_saved_lookup Hrelpins_cs c Hcs). exact (HH5thr c Hcs). }
    assert (Hmrs1 : mr !!! Regidx Rs1 = bnode k)
      by (rewrite (HmrX Rs1 ltac:(vm_compute; reflexivity)); exact HMs1).
    (* ---- +0x5a addi a0,s1,16 : a0 := &b->lock ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.bread + 0x5a)) Ra0 Rs1 (mword_of_int 16 : mword 12)
              mr (K - 6)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5a").
    iIntros (CIDh1 Hsh1) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (H6 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mr !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 16 : mword 12)))]> mr).
    assert (HH6a0 : H6 !!! Regidx Ra0 = buf_lock (bnode k)).
    { rewrite /H6 upd_eq. rewrite Hmrs1. reflexivity. }
    assert (Hpp5e : add_vec_int (mword_of_int (KernelSyms.bread + 0x5a) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0x5e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5e) in "Hpc".
    (* ---- +0x5e jal ra,acquiresleep ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.bread + 0x5e)) Rra (mword_of_int 4984 : mword 21)
              H6 (K - 6)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi5e").
    iIntros (CIDh2 Hsh2) "Hcg Hpc".
    set (H7 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.bread + 0x5e) : mword 64) 4)]> H6).
    assert (Htgtasl : add_vec (mword_of_int (KernelSyms.bread + 0x5e) : mword 64)
                        (sign_extend' 64 (mword_of_int 4984 : mword 21))
                      = mword_of_int KernelSyms.acquiresleep)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtasl) in "Hpc".
    assert (HH7thr : forall c : mword 5, is_cs_idx c = true ->
                       H7 !!! Regidx c = M !!! Regidx c).
    { intros c Hcs.
      rewrite /H7 upd_ne; [| regne].
      rewrite /H6 upd_ne; [| regne]. exact (HmrX c Hcs). }
    assert (HH7a0 : H7 !!! Regidx Ra0 = buf_lock (bnode k))
      by (rewrite /H7 upd_ne; [exact HH6a0 | vm_compute; discriminate]).
    assert (HH7ra : H7 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.bread + 0x5e) : mword 64) 4)
      by (rewrite /H7; apply upd_eq).
    iDestruct (cpu_own_transport CIDr CIDh2 0%nat eb (proc_addr j) eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CIDh2 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CIDh2 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextm") as "Hextm".
    (* acquiresleep is index-generic now: bread's own complement (untouched
       since entry -- bread's own release above never conjured it, only the
       [arm_pay] its acquire minted) is exactly what acquiresleep asks for. *)
    iApply (ASL.wp_acquiresleep_sconf kt (dq := dq)  γs j (fst (bn_slk bn k)) (snd (bn_slk bn k))
              "buffer"%string (bown bn k) H7 pidv (K - 6)%nat eb eb lks
              Hj ltac:(lia)
              ltac:(lkbelow)
              with "Hcg Hcnt Hextc Hextm Htext Hpc [] Hppid Hprocs").
    all: try lkbelow.
    { iEval (rewrite HH7a0). iExact "Hslk". }
    (* acquiresleep PARKS: it returns on hart [CIDs], handing the complement
       back too. *)
    iIntros (CIDs Hss mf) "%Hcsasl Hcg Hcnt Hextc Hextm Hpc Hstok Hpid Hbown Hppid".
    iEval (rewrite HH7a0) in "Hpid".
    iPoseProof (bdi_62 with "Htext") as "Hi62".
    assert (Hpc62 : ret_pc (H7 !!! Regidx Rra) = mword_of_int (KernelSyms.bread + 0x62)).
    { rewrite HH7ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc62) in "Hpc".
    assert (HmfX : forall c : mword 5, is_cs_idx c = true ->
                     mf !!! Regidx c = M !!! Regidx c).
    { intros c Hcs.
      rewrite (callee_saved_lookup Hcsasl c Hcs). exact (HH7thr c Hcs). }
    assert (Hmfs1 : mf !!! Regidx Rs1 = bnode k)
      by (rewrite (HmfX Rs1 ltac:(vm_compute; reflexivity)); exact HMs1).
    assert (Hmfregs : bd_regs m mf).
    { rewrite /bd_regs. split_and!.
      - rewrite (HmfX csp_rs1 ltac:(vm_compute; reflexivity)). exact HMsp.
      - rewrite (HmfX Rs2 ltac:(vm_compute; reflexivity)). exact HMs2.
      - rewrite (HmfX Rs3 ltac:(vm_compute; reflexivity)). exact HMs3.
      - intros c Hcs N2 N8 N9 N18 N19 N4.
        rewrite (HmfX c Hcs). exact (HMthr c Hcs N2 N8 N9 N18 N19 N4). }
    (* ---- +0x62 c.j +0x52 : into the shared tail ---- *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.bread + 0x62))
              (sign_extend' 21 (concat_vec (mword_of_int 41 : mword 11) ('b"0")))
              mf (K - 6)%nat eb ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi62").
    iIntros (CIDh3 Hsh3). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Htgtb4 : add_vec (mword_of_int (KernelSyms.bread + 0x62) : mword 64)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 41 : mword 11) ('b"0"))))
                     = mword_of_int (KernelSyms.bread + 0xb4))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtb4) in "Hpc".
    iDestruct (cpu_own_transport CIDs CIDh3 0%nat eb (proc_addr j) eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CIDs CIDh3 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDs CIDh3 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (bd_cont_shift (CIDa := CID0) (CIDb := CIDh3)  j bn V pidv dev bno dq
                 m K eb (proc_addr j) lks ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (bread_tail (CID0 := CIDh3)  γs j γl γu γd γk pd pav pu bn V k qref pidv dev bno dq
              m mf K eb lks HK Hbno Hk Hgd Hcov Hdv Hj Hgl Hmfregs Hmfs1
              with "Hcg Htext Hpc Hesc Hframe Hcnt Hextc Hextm Hprocs Hppid
                    Hdev Hgeom Hdlock Hstok Hpid Hbown Href Hcont").
  Qed.

  (* ================================================================== *)
  (*  THE RECYCLE (0x90 .. 0xb0): the three field rewrites -- each with    *)
  (*  the escrow opened around ITS OWN store -- then refcnt := 1, release  *)
  (*  and acquiresleep, falling into the shared tail at 0xb4.              *)
  (*  0x90..0xa8 hold the bcache lock, hence the literal [false] index.    *)
  (* ================================================================== *)

  Local Lemma bread_recyc `{GEN : GenId} `{CID0 : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (V : bio_view Σ) (k : nat)
      (Mg : gmap nat (Qp * positive)) (ord : list nat) (devs bnos : nat -> mword 32)
      (pidv dev bno : mword 32) (dq : dfrac)
      (m M : regfile) (K : nat) (eb : bool) (lks : gset string) :
    (K_bread <= K)%nat ->
    (uint bno < 2147483648)%Z ->
    (k < NBUF)%nat ->
    Mg !! k = None ->
    bv_gd V = γd ->
    uint bno ∈ bv_cov V ->
    dev = bv_dev V ->
    (* the forward scan's exit tie, at EVERY slot: the block really is
       uncached, which is what licenses the pool exchange *)
    (forall i, (i < NBUF)%nat -> ¬ (devs i = dev /\ bnos i = bno)) ->
    m !!! Regidx Ra0 = sign_extend' 64 dev ->
    m !!! Regidx Ra1 = sign_extend' 64 bno ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    bd_regs m M ->
    M !!! Regidx Rs1 = bnode k ->
    (* the block owns "bcache" on entry (0x90..0xa8); see bread_hit's
       [Hbelow] for what this covers. *)
    locks_below lks "bcache" ->
    sie_cap_gpr kt M (trap_res eb + (K - 6))%nat false (proc_addr j) -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.bread + 0x90) : mword 64) -∗
    bio_ctx bn V -∗
    bd_frame m -∗
    cpu_own 1 eb (proc_addr j) false ({["bcache"]} ∪ lks) -∗
    arm_pay kt 0 eb (proc_addr j) -∗
    trap_csrs_ext kt eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    locked (bn_lk bn) cpu_id -∗
    bcache_scan bn V Mg ord devs bnos -∗
    bslot bn -∗
    procs_inv (kt := kt) γs -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    bd_cont (kt := kt) (CID0 := CID0)  j bn V pidv dev bno dq m K eb (proc_addr j) lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hbno Hk HMk Hgd Hcov Hdv Htie Ha0 Ha1 Hj Hgl Hregs HMs1 Hbelow.
    pose proof Hregs as (HMsp & HMs2 & HMs3 & HMthr).
    pose proof (locks_below_not_elem _ _ Hbelow) as Hfresh.
    iIntros "Hcg #Htext Hpc #Hbio Hframe Hcnt Hpay Hextc Hextm Htok Hscan Hbslot".
    iIntros "#Hprocs Hppid #Hdev #Hgeom #Hdlock Hcont".
    iDestruct (bio_ctx_lock with "Hbio") as "#Hlock".
    iDestruct (bio_ctx_buf bn V k Hk with "Hbio") as "[#Hslk #Hesc0]".
    iDestruct (buf_escrow_inv with "Hesc0") as "#Hesc".
    iPoseProof (bdi_90 with "Htext") as "Hi90".
    iPoseProof (bdi_94 with "Htext") as "Hi94".
    iPoseProof (bdi_98 with "Htext") as "Hi98".
    iPoseProof (bdi_9c with "Htext") as "Hi9c".
    iPoseProof (bdi_9e with "Htext") as "Hi9e".
    iPoseProof (bdi_a0 with "Htext") as "Hia0".
    iPoseProof (bdi_a4 with "Htext") as "Hia4".
    iPoseProof (bdi_a8 with "Htext") as "Hia8".
    iPoseProof (bdi_ac with "Htext") as "Hiac".
    iPoseProof (bdi_b0 with "Htext") as "Hib0".
    (* the three field addresses and the refcnt cell, in the leaves' spelling *)
    assert (Hadev : add_vec (rget M Rs1) (sign_extend' 64 (mword_of_int 8 : mword 12))
                    = b_dev (bpa k)).
    { rgne. rewrite HMs1 bd_s8. rewrite /b_dev /bpa /pa_add /add_vec_int. reflexivity. }
    assert (Habno : add_vec (rget M Rs1) (sign_extend' 64 (mword_of_int 12 : mword 12))
                    = b_blockno (bpa k)).
    { rgne. rewrite HMs1 bd_s12. rewrite /b_blockno /bpa /pa_add /add_vec_int. reflexivity. }
    assert (Hava : add_vec (rget M Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12))
                   = b_valid (bpa k)).
    { rgne. rewrite HMs1 bd_s0. rewrite /b_valid /bpa. apply kv_addv_zero. }
    (* the stored words: the two arguments arrive sign-extended, so the
       truncation the store performs gives the arguments back *)
    assert (Hsvdev : trunc32 (rget M Rs2) = dev)
      by (rgne; rewrite HMs2 Ha0; apply trunc32_sext).
    assert (Hsvbno : trunc32 (rget M Rs3) = bno)
      by (rgne; rewrite HMs3 Ha1; apply trunc32_sext).
    iDestruct (sie_cap_gpr_x0 M (trap_res eb + (K - 6))%nat false (proc_addr j) Rz
                 ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx0 Hcg]".
    assert (Hsvz : trunc32 (rget M Rz) = (mword_of_int 0 : mword 32))
      by (rgne; rewrite Hx0; exact bd_trunc32_zero).
    (* the recycle ghost step: the auth, the refcnt cell at 0 and the two
       bcache halves out; the closing wand mints the chain's reference. *)
    iDestruct (bcache_scan_recycle bn V Mg ord devs bnos k dev bno
                 Hk HMk Hdv Hcov Htie with "Hscan Hbslot")
      as "(%Hpure & Hauth & Hcell & Hdevs & Hbnos & Hpool & Hclose)".
    destruct Hpure as [Hmiss Huniq].
    (* ---- +0x90 sw s2,8(s1) : b->dev = dev ---- *)
    iApply (wp_sw_au_s_sconf false (mword_of_int (KernelSyms.bread + 0x90)) Rs2 Rs1
              (mword_of_int 8 : mword 12) M (trap_res eb + (K - 6))%nat
              (own (bn_auth bn) (● Mg) ∗ b_dev (bpa k) ↦₄{DfracOwn (1/2)} dev)%I
              (⊤ ∖ ↑minstretN ∖ ↑bioN) false ltac:(solve_ndisj)
              with "Hcg Hpc Hi90 [Hauth Hdevs]").
    { iInv "Hesc" as ">Hbody" "Hclose2".
      iDestruct (escrow_recyc_dev bn V k Mg (devs k) dev HMk Hdv
                   with "Hauth Hbody Hdevs") as "(Hauth & Hfull & Hback)".
      iModIntro. iExists (devs k).
      iEval (rewrite -Hadev) in "Hfull". iFrame "Hfull".
      iIntros "Hfull". iEval (rewrite Hadev Hsvdev) in "Hfull".
      iDestruct ("Hback" with "Hfull") as "[Hbody Hhalf]".
      iMod ("Hclose2" with "[Hbody]") as "_". { iApply bi.later_intro. iExact "Hbody". }
      iModIntro. iFrame "Hauth Hhalf". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc [Hauth Hdevs]".
    assert (Hpp94 : add_vec_int (mword_of_int (KernelSyms.bread + 0x90) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0x94))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp94) in "Hpc".
    (* ---- +0x94 sw s3,12(s1) : b->blockno = blockno ----
       THE CACHE MEMBERSHIP MOVES HERE, so this is where the pool exchange
       happens and where the escrow enters its mid-recycle window (cells
       only, dev cell FULL, the recycle token out in our hand). *)
    iApply (wp_sw_au_s_sconf false (mword_of_int (KernelSyms.bread + 0x94)) Rs3 Rs1
              (mword_of_int 12 : mword 12) M (trap_res eb + (K - 6))%nat
              (own (bn_auth bn) (● Mg) ∗ bmid bn k ∗ pool_blk V (uint bno) ∗
               b_blockno (bpa k) ↦₄{DfracOwn (1/2)} bno ∗
               bio_pool V (bfun_upd bnos k bno))%I
              (⊤ ∖ ↑minstretN ∖ ↑bioN) false ltac:(solve_ndisj)
              with "Hcg Hpc Hi94 [Hauth Hdevs Hbnos Hpool]").
    { iInv "Hesc" as ">Hbody" "Hclose2".
      iDestruct (escrow_recyc_bno bn V k Mg bnos dev bno
                   HMk Hk Hcov Hmiss Huniq Hdv
                   with "Hauth Hbody Hdevs Hbnos Hpool")
        as "(Hauth & Hfull & Hback)".
      iModIntro. iExists (bnos k).
      iEval (rewrite -Habno) in "Hfull". iFrame "Hfull".
      iIntros "Hfull". iEval (rewrite Habno Hsvbno) in "Hfull".
      iDestruct ("Hback" with "Hfull")
        as "(Hbody & Hbmid & HpoolB & Hbnos & Hpool)".
      iMod ("Hclose2" with "[Hbody]") as "_". { iApply bi.later_intro. iExact "Hbody". }
      iModIntro. iFrame "Hauth Hbmid HpoolB Hbnos Hpool". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc (Hauth & Hbmid & HpoolB & Hbnos & Hpool)".
    assert (Hpp98 : add_vec_int (mword_of_int (KernelSyms.bread + 0x94) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0x98))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp98) in "Hpc".
    (* ---- +0x98 sw zero,0(s1) : b->valid = 0 ----
       the recycle token refutes both normal arms, so what we reopen is the
       window we parked; the stored 0 makes the arm INVALID and deposits the
       new block's pool bundle for whoever wins the sleeplock race. *)
    iApply (wp_sw_au_s_sconf false (mword_of_int (KernelSyms.bread + 0x98)) Rz Rs1
              (mword_of_int 0 : mword 12) M (trap_res eb + (K - 6))%nat
              (own (bn_auth bn) (● Mg) ∗
               b_dev (bpa k) ↦₄{DfracOwn (1/2)} (bv_dev V) ∗
               b_blockno (bpa k) ↦₄{DfracOwn (1/2)} bno)%I
              (⊤ ∖ ↑minstretN ∖ ↑bioN) false ltac:(solve_ndisj)
              with "Hcg Hpc Hi98 [Hauth Hbmid HpoolB Hbnos]").
    { iInv "Hesc" as ">Hbody" "Hclose2".
      iDestruct (escrow_recyc_valid bn V k bno Hcov
                   with "Hbmid Hbody Hbnos HpoolB") as "(Hvld & Hbnos & Hback)".
      iDestruct "Hvld" as (vld) "Hvld".
      iModIntro. iExists vld.
      iEval (rewrite -Hava) in "Hvld". iFrame "Hvld".
      iIntros "Hvld". iEval (rewrite Hava Hsvz) in "Hvld".
      iDestruct ("Hback" with "Hvld") as "[Hbody Hdevs]".
      iMod ("Hclose2" with "[Hbody]") as "_". { iApply bi.later_intro. iExact "Hbody". }
      iModIntro. iFrame "Hauth Hdevs Hbnos". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc (Hauth & Hdevs & Hbnos)".
    iEval (rewrite -Hdv) in "Hdevs".
    assert (Hpp9c : add_vec_int (mword_of_int (KernelSyms.bread + 0x98) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0x9c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp9c) in "Hpc".
    (* ---- +0x9c c.li a5,1 ; +0x9e c.sw a5,64(s1) : b->refcnt = 1 ---- *)
    assert (Hli1 : add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))
                   = (mword_of_int 1 : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.bread + 0x9c)) Ra5 (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 64) M (trap_res eb + (K - 6))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) Hli1
              with "Hcg Hpc Hi9c").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (C1 := <[Regidx Ra5 := regval_into_reg (mword_of_int 1 : mword 64)]> M).
    assert (HC1s1 : C1 !!! Regidx Rs1 = bnode k)
      by (rewrite /C1 upd_ne; [exact HMs1 | vm_compute; discriminate]).
    assert (HC1a5 : C1 !!! Regidx Ra5 = (mword_of_int 1 : mword 64))
      by (rewrite /C1; apply upd_eq).
    assert (Hpp9e : add_vec_int (mword_of_int (KernelSyms.bread + 0x9c) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0x9e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp9e) in "Hpc".
    assert (Harc : add_vec (rget C1 Rs1) (sign_extend' 64 (mword_of_int 64 : mword 12))
                   = brefcnt k).
    { rgne. rewrite HC1s1 bd_s64. rewrite /brefcnt /bpa /pa_add /add_vec_int. reflexivity. }
    iEval (rewrite -Harc) in "Hcell".
    iApply (wp_csw_s_sconf (mword_of_int (KernelSyms.bread + 0x9e)) Ra5 Rs1 (mword_of_int 64 : mword 12)
              C1 (trap_res eb + (K - 6))%nat (mword_of_int 0 : mword 32) false
              with "Hcg Hpc Hi9e Hcell").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hcell".
    iEval (rewrite Harc) in "Hcell".
    assert (Hstv : trunc32 (rget C1 Ra5) = (mword_of_int 1 : mword 32)).
    { rgne. rewrite HC1a5. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hstv) in "Hcell".
    iMod ("Hclose" with "Hauth Hcell Hdevs Hbnos Hpool") as "[HRres Href]".
    assert (Hppa0 : add_vec_int (mword_of_int (KernelSyms.bread + 0x9e) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0xa0))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppa0) in "Hpc".
    (* ---- +0xa0 / +0xa4 : a0 := &bcache ; +0xa8 jal release ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.bread + 0xa0)) Ra0 (mword_of_int 0x15 : mword 20)
              C1 (trap_res eb + (K - 6))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hia0").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (C2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.bread + 0xa0) : mword 64)
                     (auipc_off (mword_of_int 0x15 : mword 20)))]> C1).
    assert (Hppa4 : add_vec_int (mword_of_int (KernelSyms.bread + 0xa0) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0xa4))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppa4) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.bread + 0xa4)) Ra0 Ra0 (mword_of_int 1538 : mword 12)
              C2 (trap_res eb + (K - 6))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hia4").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (C3 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (C2 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 1538 : mword 12)))]> C2).
    assert (HC3a0 : C3 !!! Regidx Ra0 = bcache_addr).
    { rewrite /C3 upd_eq /C2 upd_eq. rewrite /bcache_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hppa8 : add_vec_int (mword_of_int (KernelSyms.bread + 0xa4) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0xa8))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppa8) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.bread + 0xa8)) Rra (mword_of_int 2089020 : mword 21)
              C3 (trap_res eb + (K - 6))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hia8").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (C4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.bread + 0xa8) : mword 64) 4)]> C3).
    assert (Htgtrel : add_vec (mword_of_int (KernelSyms.bread + 0xa8) : mword 64)
                        (sign_extend' 64 (mword_of_int 2089020 : mword 21))
                      = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtrel) in "Hpc".
    assert (HC4thr : forall c : mword 5, is_cs_idx c = true ->
                       C4 !!! Regidx c = M !!! Regidx c).
    { intros c Hcs.
      rewrite /C4 upd_ne; [| regne].
      rewrite /C3 upd_ne; [| regne].
      rewrite /C2 upd_ne; [| regne].
      rewrite /C1 upd_ne; [reflexivity | regne]. }
    assert (HC4a0 : C4 !!! Regidx Ra0 = bcache_addr)
      by (rewrite /C4 upd_ne; [exact HC3a0 | vm_compute; discriminate]).
    assert (HC4ra : C4 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.bread + 0xa8) : mword 64) 4)
      by (rewrite /C4; apply upd_eq).
    iApply (R.wp_release_sconf kt (bn_lk bn) bcache_addr "bcache"%string (bcache_res bn V) C4
              0%nat eb (proc_addr j) (K - 6)%nat ({["bcache"]} ∪ lks)
              ltac:(rewrite HC4a0; apply bv_eq; vm_compute; reflexivity)
              ltac:(lia)
              with "Hcg Htext Hpc [Hlock] Htok HRres Hcnt Hpay").
    { iExact "Hlock". }
    iIntros (CIDr Hsr mr) "Hcg Hpc %Hrelpins Hcnt".
    assert (Hsetback : ({["bcache"]} ∪ lks) ∖ {["bcache"]} = lks)
      by (apply locks_add_del_below; lkbelow).
    iEval (rewrite Hsetback) in "Hcnt".
    assert (Hpcac : ret_pc (C4 !!! Regidx Rra) = mword_of_int (KernelSyms.bread + 0xac)).
    { rewrite HC4ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcac) in "Hpc".
    pose proof Hrelpins as Hrelpins_cs.
    assert (HmrX : forall c : mword 5, is_cs_idx c = true ->
                     mr !!! Regidx c = M !!! Regidx c).
    { intros c Hcs. rewrite (callee_saved_lookup Hrelpins_cs c Hcs). exact (HC4thr c Hcs). }
    assert (Hmrs1 : mr !!! Regidx Rs1 = bnode k)
      by (rewrite (HmrX Rs1 ltac:(vm_compute; reflexivity)); exact HMs1).
    (* ---- +0xac addi a0,s1,16 ; +0xb0 jal acquiresleep ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.bread + 0xac)) Ra0 Rs1 (mword_of_int 16 : mword 12)
              mr (K - 6)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hiac").
    iIntros (CIDc1 Hsc1) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (C5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mr !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 16 : mword 12)))]> mr).
    assert (HC5a0 : C5 !!! Regidx Ra0 = buf_lock (bnode k)).
    { rewrite /C5 upd_eq. rewrite Hmrs1. reflexivity. }
    assert (Hppb0 : add_vec_int (mword_of_int (KernelSyms.bread + 0xac) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0xb0))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppb0) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.bread + 0xb0)) Rra (mword_of_int 4902 : mword 21)
              C5 (K - 6)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hib0").
    iIntros (CIDc2 Hsc2) "Hcg Hpc".
    set (C6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.bread + 0xb0) : mword 64) 4)]> C5).
    assert (Htgtasl : add_vec (mword_of_int (KernelSyms.bread + 0xb0) : mword 64)
                        (sign_extend' 64 (mword_of_int 4902 : mword 21))
                      = mword_of_int KernelSyms.acquiresleep)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtasl) in "Hpc".
    assert (HC6thr : forall c : mword 5, is_cs_idx c = true ->
                       C6 !!! Regidx c = M !!! Regidx c).
    { intros c Hcs.
      rewrite /C6 upd_ne; [| regne].
      rewrite /C5 upd_ne; [| regne]. exact (HmrX c Hcs). }
    assert (HC6a0 : C6 !!! Regidx Ra0 = buf_lock (bnode k))
      by (rewrite /C6 upd_ne; [exact HC5a0 | vm_compute; discriminate]).
    assert (HC6ra : C6 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.bread + 0xb0) : mword 64) 4)
      by (rewrite /C6; apply upd_eq).
    iDestruct (cpu_own_transport CIDr CIDc2 0%nat eb (proc_addr j) eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CIDc2 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CIDc2 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextm") as "Hextm".
    (* acquiresleep is index-generic now: bread's own complement (untouched
       since entry) is exactly what acquiresleep asks for. *)
    iApply (ASL.wp_acquiresleep_sconf kt (dq := dq)  γs j (fst (bn_slk bn k)) (snd (bn_slk bn k))
              "buffer"%string (bown bn k) C6 pidv (K - 6)%nat eb eb lks
              Hj ltac:(lia)
              ltac:(lkbelow)
              with "Hcg Hcnt Hextc Hextm Htext Hpc [] Hppid Hprocs").
    all: try lkbelow.
    { iEval (rewrite HC6a0). iExact "Hslk". }
    (* acquiresleep PARKS: it returns on hart [CIDs], handing the complement
       back too. *)
    iIntros (CIDs Hss mf) "%Hcsasl Hcg Hcnt Hextc Hextm Hpc Hstok Hpid Hbown Hppid".
    iEval (rewrite HC6a0) in "Hpid".
    assert (Hpcb4 : ret_pc (C6 !!! Regidx Rra) = mword_of_int (KernelSyms.bread + 0xb4)).
    { rewrite HC6ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcb4) in "Hpc".
    assert (HmfX : forall c : mword 5, is_cs_idx c = true ->
                     mf !!! Regidx c = M !!! Regidx c).
    { intros c Hcs.
      rewrite (callee_saved_lookup Hcsasl c Hcs). exact (HC6thr c Hcs). }
    assert (Hmfs1 : mf !!! Regidx Rs1 = bnode k)
      by (rewrite (HmfX Rs1 ltac:(vm_compute; reflexivity)); exact HMs1).
    assert (Hmfregs : bd_regs m mf).
    { rewrite /bd_regs. split_and!.
      - rewrite (HmfX csp_rs1 ltac:(vm_compute; reflexivity)). exact HMsp.
      - rewrite (HmfX Rs2 ltac:(vm_compute; reflexivity)). exact HMs2.
      - rewrite (HmfX Rs3 ltac:(vm_compute; reflexivity)). exact HMs3.
      - intros c Hcs N2 N8 N9 N18 N19 N4.
        rewrite (HmfX c Hcs). exact (HMthr c Hcs N2 N8 N9 N18 N19 N4). }
    iDestruct (bd_cont_shift (CIDa := CID0) (CIDb := CIDs)  j bn V pidv dev bno dq
                 m K eb (proc_addr j) lks ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (bread_tail (CID0 := CIDs)  γs j γl γu γd γk pd pav pu bn V k (1/4)%Qp pidv dev bno dq
              m mf K eb lks HK Hbno Hk Hgd Hcov Hdv Hj Hgl Hmfregs Hmfs1
              with "Hcg Htext Hpc Hesc Hframe Hcnt Hextc Hextm Hprocs Hppid
                    Hdev Hgeom Hdlock Hstok Hpid Hbown Href Hcont").
  Qed.

  (* ================================================================== *)
  (*  THE BACKWARD (RECYCLE) SCAN.  Loop head 0x7a, advance 0x7e, back    *)
  (*  edge 0x80; exits to the recycle block at 0x90 (refcnt == 0) or to   *)
  (*  panic("bget: no buffers") at 0x84 (every buffer pinned).            *)
  (*                                                                     *)
  (*  The cursor is the LAST node of the not-yet-visited prefix [pre] of  *)
  (*  the LRU order, and [bcur_bwd_nil]/[bcur_bwd_snoc] read that off at  *)
  (*  both boundaries -- so the [bne] test needs no case split beyond     *)
  (*  "is [pre] down to one element".                                     *)
  (*                                                                     *)
  (*  THE WHOLE LOOP RUNS WITH THE BCACHE LOCK HELD, i.e. at the literal  *)
  (*  [false] index, so every leaf is a [wp_next_off] and the hart never  *)
  (*  moves: the induction hypothesis re-enters at [CID0] and nothing     *)
  (*  needs re-anchoring.                                                 *)
  (* ================================================================== *)

  Local Lemma bread_bloop `{GEN : GenId} `{CID0 : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (V : bio_view Σ)
      (Mg : gmap nat (Qp * positive)) (ord : list nat) (devs bnos : nat -> mword 32)
      (pidv dev bno : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (n : nat) (lks : gset string) :
    (K_bread <= K)%nat ->
    (uint bno < 2147483648)%Z ->
    m !!! Regidx Ra0 = sign_extend' 64 dev ->
    m !!! Regidx Ra1 = sign_extend' 64 bno ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    bv_gd V = γd ->
    uint bno ∈ bv_cov V ->
    dev = bv_dev V ->
    (forall i, (i < NBUF)%nat -> ¬ (devs i = dev /\ bnos i = bno)) ->
    (* the whole backward scan runs while [bcache] is still held too; see
       bread_floop's [Hbelow]. *)
    locks_below lks "bcache" ->
    forall (pre post : list nat) (M : regfile),
    (length pre <= n)%nat ->
    ord = (pre ++ post)%list ->
    pre <> [] ->
    bd_regs m M ->
    M !!! Regidx Rs1 = List.last (map bnode pre) bhead ->
    M !!! Regidx Ra4 = bhead ->
    sie_cap_gpr kt M (trap_res eb + (K - 6))%nat false (proc_addr j) -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.bread + 0x7a) : mword 64) -∗
    panic_env -∗
    bio_ctx bn V -∗
    bd_frame m -∗
    cpu_own 1 eb (proc_addr j) false ({["bcache"]} ∪ lks) -∗
    arm_pay kt 0 eb (proc_addr j) -∗
    trap_csrs_ext kt eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    locked (bn_lk bn) cpu_id -∗
    bcache_scan bn V Mg ord devs bnos -∗
    bslot bn -∗
    procs_inv (kt := kt) γs -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    bd_cont (kt := kt) (CID0 := CID0)  j bn V pidv dev bno dq m K eb (proc_addr j) lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hbno Ha0 Ha1 Hj Hgl Hgd Hcov Hdv Htie Hbelow.
    induction n as [|n IH];
      intros pre post M Hlen Hord Hne Hregs HMs1 HMa4.
    { exfalso. destruct pre as [|x l]; [congruence | cbn in Hlen; lia]. }
    pose proof Hregs as (HMsp & HMs2 & HMs3 & HMthr).
    destruct (bd_ord_last pre Hne) as (d & kk & Hpre).
    iIntros "Hcg #Htext #Hkd Hpc #Hpenv #Hbio Hframe Hcnt Hpay Hextc Hextm Htok Hscan Hbslot".
    iIntros "#Hprocs Hppid #Hdev #Hgeom #Hdlock Hcont".
    iPoseProof (bdi_7a with "Htext") as "Hi7a".
    iPoseProof (bdi_7c with "Htext") as "Hi7c".
    iPoseProof (bdi_7e with "Htext") as "Hi7e".
    iPoseProof (bdi_80 with "Htext") as "Hi80".
    rewrite /bcache_scan.
    iDestruct "Hscan" as
      "(Hauth & Hsauth & %Hdom & %Hordp & %Hinj & %Hdevpin & Hlru & Hpool & Hslots)".
    assert (Hord2 : ord = (d ++ kk :: post)%list)
      by (rewrite Hord Hpre -app_assoc; reflexivity).
    assert (Hkk : (kk < NBUF)%nat) by exact (bord_split_lt ord d post kk Hordp Hord2).
    assert (Hcur : M !!! Regidx Rs1 = bnode kk)
      by (rewrite HMs1 Hpre; apply bcur_bwd_snoc).
    (* ---- +0x7a c.lw a5,64(s1) : the refcnt, borrowed out of its slot ---- *)
    iDestruct (bio_slots_acc bn Mg devs bnos kk Hkk with "Hslots") as "[Hslot Hback]".
    iDestruct (bio_slot_refcnt_acc bn Mg kk (devs kk) (bnos kk) with "Hslot")
      as (cw) "(Hcell & %Hrct & Hbackslot)".
    assert (Hpa : add_vec (rget M Rs1) (sign_extend' 64 (mword_of_int 64 : mword 12))
                  = brefcnt kk).
    { rgne. rewrite Hcur bd_s64. rewrite /brefcnt /bpa /pa_add /add_vec_int. reflexivity. }
    iEval (rewrite -Hpa) in "Hcell".
    iApply (wp_clw_s_sconf (mword_of_int (KernelSyms.bread + 0x7a)) Ra5 Rs1 (mword_of_int 64 : mword 12)
              M (trap_res eb + (K - 6))%nat (cw : mword 32) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi7a Hcell").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hcell".
    iEval (rewrite Hpa) in "Hcell".
    iDestruct ("Hbackslot" with "Hcell") as "Hslot".
    iDestruct ("Hback" $! Mg devs bnos with "[%] Hslot") as "Hslots".
    { intros i Hi. split_and!; reflexivity. }
    set (B1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (cw : mword 32))]> M).
    assert (HB1a5 : B1 !!! Regidx Ra5 = sign_extend' 64 (cw : mword 32))
      by (rewrite /B1; apply upd_eq).
    assert (HB1s1 : B1 !!! Regidx Rs1 = bnode kk)
      by (rewrite /B1 upd_ne; [exact Hcur | vm_compute; discriminate]).
    assert (HB1a4 : B1 !!! Regidx Ra4 = bhead)
      by (rewrite /B1 upd_ne; [exact HMa4 | vm_compute; discriminate]).
    assert (HB1regs : bd_regs m B1).
    { rewrite /bd_regs. split_and!.
      - rewrite /B1 upd_ne; [exact HMsp | vm_compute; discriminate].
      - rewrite /B1 upd_ne; [exact HMs2 | vm_compute; discriminate].
      - rewrite /B1 upd_ne; [exact HMs3 | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N4.
        rewrite /B1 upd_ne; [| apply not_eq_sym; apply is_cs_idx_true_neq;
                               [vm_compute; reflexivity | assumption]].
        exact (HMthr c Hcs N2 N8 N9 N18 N19 N4). }
    assert (Hpp7c : add_vec_int (mword_of_int (KernelSyms.bread + 0x7a) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0x7c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7c) in "Hpc".
    destruct Hrct as [[Hwz HMkNone] | [Hwnz _]].
    - (* ======== refcnt == 0: this buffer is free, RECYCLE it ======== *)
      assert (Hbeqz : eq_vec (B1 !!! Regidx Ra5) zero_reg = true)
        by (rewrite HB1a5; exact Hwz).
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.bread + 0x7c)) (mword_of_int 10 : mword 8)
                (Cregidx (mword_of_int 7)) Ra5 B1 (trap_res eb + (K - 6))%nat false
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; exact Hbeqz) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi7c").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Htgt90 : add_vec (mword_of_int (KernelSyms.bread + 0x7c) : mword 64)
                         (sign_extend' 64 (sign_extend' 13
                            (concat_vec (mword_of_int 10 : mword 8) ('b"0"))))
                       = mword_of_int (KernelSyms.bread + 0x90))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt90) in "Hpc".
      iAssert (bcache_scan bn V Mg ord devs bnos)
        with "[Hauth Hsauth Hlru Hpool Hslots]" as "Hscan".
      { rewrite /bcache_scan. iFrame "Hauth Hsauth".
        iSplitR; [iPureIntro; exact Hdom|].
        iSplitR; [iPureIntro; exact Hordp|].
        iSplitR; [iPureIntro; exact Hinj|].
        iSplitR; [iPureIntro; exact Hdevpin|].
        iFrame "Hlru Hpool Hslots". }
      iApply (bread_recyc (CID0 := CID0)  γs j γl γu γd γk pd pav pu bn V kk Mg ord devs bnos
                pidv dev bno dq m B1 K eb lks
                HK Hbno Hkk HMkNone Hgd Hcov Hdv Htie Ha0 Ha1 Hj Hgl HB1regs HB1s1 Hbelow
                with "Hcg Htext Hpc Hbio Hframe Hcnt Hpay Hextc Hextm Htok Hscan Hbslot
                      Hprocs Hppid Hdev Hgeom Hdlock Hcont").
    - (* ======== refcnt <> 0: advance to b->prev ======== *)
      assert (Hbeqz : eq_vec (B1 !!! Regidx Ra5) zero_reg = false)
        by (rewrite HB1a5; exact Hwnz).
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.bread + 0x7c)) (mword_of_int 10 : mword 8)
                (Cregidx (mword_of_int 7)) Ra5 B1 (trap_res eb + (K - 6))%nat false
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; exact Hbeqz)
                with "Hcg Hpc Hi7c").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      assert (Hpp7e : add_vec_int (mword_of_int (KernelSyms.bread + 0x7c) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0x7e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp7e) in "Hpc".
      (* ---- +0x7e c.ld s1,72(s1) : s1 := b->prev ---- *)
      assert (HB1s1g : rget B1 Rs1 = bnode kk) by (rgne; exact HB1s1).
      iEval (rewrite Hord2 (bcur_fwd_split d kk post)) in "Hlru".
      iDestruct (bcache_lru_prev_acc bhead (bnode kk) (map bnode d) (map bnode post)
                   with "Hlru") as "[Hprev Hrelink]".
      iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.bread + 0x7e)) Rs1 Rs1 (mword_of_int 72 : mword 12)
                B1 (trap_res eb + (K - 6))%nat (List.last (map bnode d) bhead) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi7e [Hprev]").
      { iEval (rewrite HB1s1g). iExact "Hprev". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hprev".
      iEval (rewrite HB1s1g) in "Hprev".
      iDestruct ("Hrelink" with "Hprev") as "Hlru".
      iEval (rewrite -(bcur_fwd_split d kk post) -Hord2) in "Hlru".
      set (B2 := <[Regidx Rs1 := regval_into_reg (List.last (map bnode d) bhead)]> B1).
      assert (HB2s1 : B2 !!! Regidx Rs1 = List.last (map bnode d) bhead)
        by (rewrite /B2; apply upd_eq).
      assert (HB2a4 : B2 !!! Regidx Ra4 = bhead)
        by (rewrite /B2 upd_ne; [exact HB1a4 | vm_compute; discriminate]).
      assert (HB2regs : bd_regs m B2).
      { rewrite /bd_regs. split_and!.
        - rewrite /B2 upd_ne; [| vm_compute; discriminate].
          rewrite /B1 upd_ne; [exact HMsp | vm_compute; discriminate].
        - rewrite /B2 upd_ne; [| vm_compute; discriminate].
          rewrite /B1 upd_ne; [exact HMs2 | vm_compute; discriminate].
        - rewrite /B2 upd_ne; [| vm_compute; discriminate].
          rewrite /B1 upd_ne; [exact HMs3 | vm_compute; discriminate].
        - intros c Hcs N2 N8 N9 N18 N19 N4.
          rewrite /B2 upd_ne; [| lazymatch goal with
                                 | |- Regidx ?x <> Regidx ?y =>
                                     match goal with
                                     | H : x <> y |- _ => exact (fun Hq => H (regidx_inj x y Hq))
                                     end
                                 end].
          rewrite /B1 upd_ne; [| apply not_eq_sym; apply is_cs_idx_true_neq;
                                 [vm_compute; reflexivity | assumption]].
          exact (HMthr c Hcs N2 N8 N9 N18 N19 N4). }
      iAssert (bcache_scan bn V Mg ord devs bnos)
        with "[Hauth Hsauth Hlru Hpool Hslots]" as "Hscan".
      { rewrite /bcache_scan. iFrame "Hauth Hsauth".
        iSplitR; [iPureIntro; exact Hdom|].
        iSplitR; [iPureIntro; exact Hordp|].
        iSplitR; [iPureIntro; exact Hinj|].
        iSplitR; [iPureIntro; exact Hdevpin|].
        iFrame "Hlru Hpool Hslots". }
      assert (Hpp80 : add_vec_int (mword_of_int (KernelSyms.bread + 0x7e) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0x80))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp80) in "Hpc".
      destruct (decide (d = [])) as [Hde | Hdne].
      + (* ---- the prefix is exhausted: fall through to panic ---- *)
        assert (Hbne : neq_vec (B2 !!! Regidx Rs1) (B2 !!! Regidx Ra4) = false).
        { rewrite HB2s1 HB2a4 Hde bcur_bwd_nil. exact bhead_neqv_self. }
        iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.bread + 0x80)) (mword_of_int 8186 : mword 13)
                  Ra4 Rs1 B2 (trap_res eb + (K - 6))%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rgne; exact Hbne)
                  with "Hcg Hpc Hi80").
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc".
        assert (Hpp84 : add_vec_int (mword_of_int (KernelSyms.bread + 0x80) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0x84))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp84) in "Hpc".
        (* ---- the panic arm ("bget: no buffers") ---- *)
        iPoseProof (bdi_84 with "Htext") as "Hi84".
        iPoseProof (bdi_88 with "Htext") as "Hi88".
        iPoseProof (bdi_8c with "Htext") as "Hi8c".
        iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.bread + 0x84)) Ra0 (mword_of_int 4 : mword 20)
                  B2 (trap_res eb + (K - 6))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi84").
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc".
        set (Q1 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (mword_of_int (KernelSyms.bread + 0x84) : mword 64)
                         (auipc_off (mword_of_int 4 : mword 20)))]> B2).
        assert (Hpp88 : add_vec_int (mword_of_int (KernelSyms.bread + 0x84) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0x88))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp88) in "Hpc".
        iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.bread + 0x88)) Ra0 Ra0 (mword_of_int 2014 : mword 12)
                  Q1 (trap_res eb + (K - 6))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi88").
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc".
        iEval (rgne) in "Hcg".
        set (Q2 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (Q1 !!! Regidx Ra0)
                         (sign_extend' 64 (mword_of_int 2014 : mword 12)))]> Q1).
        assert (Hpp8c : add_vec_int (mword_of_int (KernelSyms.bread + 0x88) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0x8c))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp8c) in "Hpc".
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.bread + 0x8c)) Rra (mword_of_int 2087978 : mword 21)
                  Q2 (trap_res eb + (K - 6))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi8c").
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc".
        assert (Htgtpanic : add_vec (mword_of_int (KernelSyms.bread + 0x8c) : mword 64)
                              (sign_extend' 64 (mword_of_int 2087978 : mword 21))
                            = mword_of_int KernelSyms.panic)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgtpanic) in "Hpc".
        (* ---- panic() AS AN ORDINARY CALL, against SpecPanic ----
           a0 holds &"bget: no buffers"; [kernel_data] mints the literal.
           The whole scan runs with interrupts OFF (bcache.lock's push_off),
           so no hart ever moves and [cpu_own] needs no transport -- but it
           IS at noff 1 and at [{["bcache"]} ∪ lks]. *)
        iPoseProof (bd_msg_str with "Hkd") as "#Hstr".
        (* THE REGFILE THE SPEC WANTS IS THE POST-JAL ONE. *)
        pose (Q3 := <[Regidx Rra := regval_into_reg
                        (add_vec_int
                           (mword_of_int (KernelSyms.bread + 0x8c) : mword 64) 4)]> Q2).
        assert (Ha0msg : Q3 !!! Regidx Ra0 = (mword_of_int bd_msg_a : mword 64))
          by (apply bv_eq; vm_compute; reflexivity).
        iApply (PN.wp_panic_sconf kt Q3 (trap_res eb + (K - 6))%nat
                  1%nat eb false (proc_addr j) (PkAStr DfracDiscarded bd_msg)
                  ({["bcache"]} ∪ lks)
                  (bd_panic_K K eb HK) eq_refl bd_panic_noff
                  (bd_panic_below lks Hbelow)
                  with "Hcg Hcnt Htext Hkd Hpc Hpenv [Hstr]").
        { rewrite /pk_desc_res Ha0msg.
          iSplit; [iPureIntro; exact bd_msg_nonul|].
          iSplit; [iPureIntro; exact bd_msg_nz|]. iExact "Hstr". }
      + (* ---- the prefix still has a node: take the back edge ---- *)
        destruct (bd_ord_last d Hdne) as (d' & kk' & Hd').
        assert (Hord3 : ord = (d' ++ kk' :: (kk :: post))%list).
        { rewrite Hord2 Hd' -app_assoc. reflexivity. }
        assert (Hkk' : (kk' < NBUF)%nat)
          by exact (bord_split_lt ord d' (kk :: post) kk' Hordp Hord3).
        assert (Hbne : neq_vec (B2 !!! Regidx Rs1) (B2 !!! Regidx Ra4) = true).
        { rewrite HB2s1 HB2a4 Hd' bcur_bwd_snoc. exact (bnode_neqv_bhead kk' Hkk'). }
        iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.bread + 0x80)) (mword_of_int 8186 : mword 13)
                  Ra4 Rs1 B2 (trap_res eb + (K - 6))%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rgne; exact Hbne)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi80").
        iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Htgt7a : add_vec (mword_of_int (KernelSyms.bread + 0x80) : mword 64)
                           (sign_extend' 64 (mword_of_int 8186 : mword 13))
                         = mword_of_int (KernelSyms.bread + 0x7a))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt7a) in "Hpc".
        assert (Hlen' : (length d <= n)%nat).
        { rewrite Hpre length_app in Hlen. cbn in Hlen. lia. }
        iApply (IH d (kk :: post) B2 Hlen' Hord2 Hdne HB2regs HB2s1 HB2a4
                  with "Hcg Htext Hkd Hpc Hpenv Hbio Hframe Hcnt Hpay Hextc Hextm Htok Hscan Hbslot
                        Hprocs Hppid Hdev Hgeom Hdlock Hcont").
  Qed.

  (* ================================================================== *)
  (*  THE BACKWARD SCAN'S PREAMBLE (0x64 .. 0x78): s1 := bcache.head.prev, *)
  (*  a5 := a4 := &bcache.head.  The [beq] at 0x74 is DEAD: the order list *)
  (*  is a permutation of [seq 0 NBUF], hence nonempty, so head.prev is a  *)
  (*  real buffer.  Still inside the critical section: index [false].      *)
  (* ================================================================== *)

  Local Lemma bread_miss `{GEN : GenId} `{CID0 : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (V : bio_view Σ)
      (Mg : gmap nat (Qp * positive)) (ord : list nat) (devs bnos : nat -> mword 32)
      (pidv dev bno : mword 32) (dq : dfrac)
      (m M : regfile) (K : nat) (eb : bool) (lks : gset string) :
    (K_bread <= K)%nat ->
    (uint bno < 2147483648)%Z ->
    m !!! Regidx Ra0 = sign_extend' 64 dev ->
    m !!! Regidx Ra1 = sign_extend' 64 bno ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    bv_gd V = γd ->
    uint bno ∈ bv_cov V ->
    dev = bv_dev V ->
    (forall i, (i < NBUF)%nat -> ¬ (devs i = dev /\ bnos i = bno)) ->
    ord ≡ₚ seq 0 NBUF ->
    bd_regs m M ->
    (* still inside the critical section (0x64..0x78 is the backward scan's
       preamble); see bread_floop's [Hbelow] for what this is for. *)
    locks_below lks "bcache" ->
    sie_cap_gpr kt M (trap_res eb + (K - 6))%nat false (proc_addr j) -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.bread + 0x64) : mword 64) -∗
    (* (the arrival map's s1 is irrelevant: 0x64 overwrites it) *)
    panic_env -∗
    bio_ctx bn V -∗
    bd_frame m -∗
    cpu_own 1 eb (proc_addr j) false ({["bcache"]} ∪ lks) -∗
    arm_pay kt 0 eb (proc_addr j) -∗
    trap_csrs_ext kt eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    locked (bn_lk bn) cpu_id -∗
    bcache_scan bn V Mg ord devs bnos -∗
    bslot bn -∗
    procs_inv (kt := kt) γs -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    bd_cont (kt := kt) (CID0 := CID0)  j bn V pidv dev bno dq m K eb (proc_addr j) lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hbno Ha0 Ha1 Hj Hgl Hgd Hcov Hdv Htie Hordp Hregs Hbelow.
    pose proof Hregs as (HMsp & HMs2 & HMs3 & HMthr).
    destruct (bd_ord_last ord (bd_ord_nonnil ord Hordp)) as (d0 & k0 & Hordl).
    assert (Hk0 : (k0 < NBUF)%nat)
      by exact (bord_split_lt ord d0 [] k0 Hordp Hordl).
    iIntros "Hcg #Htext #Hkd Hpc #Hpenv #Hbio Hframe Hcnt Hpay Hextc Hextm Htok Hscan Hbslot".
    iIntros "#Hprocs Hppid #Hdev #Hgeom #Hdlock Hcont".
    iPoseProof (bdi_64 with "Htext") as "Hi64".
    iPoseProof (bdi_68 with "Htext") as "Hi68".
    iPoseProof (bdi_6c with "Htext") as "Hi6c".
    iPoseProof (bdi_70 with "Htext") as "Hi70".
    iPoseProof (bdi_74 with "Htext") as "Hi74".
    iPoseProof (bdi_78 with "Htext") as "Hi78".
    rewrite /bcache_scan.
    iDestruct "Hscan" as
      "(Hauth & Hsauth & %Hdom & %Hordp2 & %Hinj & %Hdevpin & Hlru & Hpool & Hslots)".
    (* ---- +0x64 auipc s1,0x1e ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.bread + 0x64)) Rs1 (mword_of_int 30 : mword 20)
              M (trap_res eb + (K - 6))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi64").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (Q1 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.bread + 0x64) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> M).
    assert (Hpp68 : add_vec_int (mword_of_int (KernelSyms.bread + 0x64) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0x68))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp68) in "Hpc".
    (* ---- +0x68 ld s1,-1882(s1) : s1 := bcache.head.prev ---- *)
    assert (Hhp : add_vec (rget Q1 Rs1) (sign_extend' 64 (mword_of_int 2286 : mword 12))
                  = bprev bhead).
    { rgne. rewrite /Q1 upd_eq. unfold regval_into_reg.
      rewrite /bprev /bhead /bnode /acur. apply bv_eq; vm_compute; reflexivity. }
    iDestruct (bcache_lru_head_prev_acc bhead (map bnode ord) with "Hlru") as "[Hhpc Hrelink]".
    iApply (wp_ld_s_sconf (mword_of_int (KernelSyms.bread + 0x68)) Rs1 Rs1 (mword_of_int 2286 : mword 12)
              Q1 (trap_res eb + (K - 6))%nat (List.last (map bnode ord) bhead) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi68 [Hhpc]").
    { iEval (rewrite Hhp). iExact "Hhpc". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hhpc".
    iEval (rewrite Hhp) in "Hhpc".
    iDestruct ("Hrelink" with "Hhpc") as "Hlru".
    set (Q2 := <[Regidx Rs1 := regval_into_reg (List.last (map bnode ord) bhead)]> Q1).
    assert (HQ2s1 : Q2 !!! Regidx Rs1 = List.last (map bnode ord) bhead)
      by (rewrite /Q2; apply upd_eq).
    assert (Hpp6c : add_vec_int (mword_of_int (KernelSyms.bread + 0x68) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0x6c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp6c) in "Hpc".
    (* ---- +0x6c / +0x70 : a5 := &bcache.head ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.bread + 0x6c)) Ra5 (mword_of_int 30 : mword 20)
              Q2 (trap_res eb + (K - 6))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6c").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (Q3 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.bread + 0x6c) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> Q2).
    assert (Hpp70 : add_vec_int (mword_of_int (KernelSyms.bread + 0x6c) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0x70))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp70) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.bread + 0x70)) Ra5 Ra5 (mword_of_int 2206 : mword 12)
              Q3 (trap_res eb + (K - 6))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi70").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (Q4 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (Q3 !!! Regidx Ra5)
                     (sign_extend' 64 (mword_of_int 2206 : mword 12)))]> Q3).
    assert (HQ4a5 : Q4 !!! Regidx Ra5 = bhead).
    { rewrite /Q4 upd_eq /Q3 upd_eq. unfold regval_into_reg.
      rewrite /bhead /bnode /acur. apply bv_eq; vm_compute; reflexivity. }
    assert (HQ4s1 : Q4 !!! Regidx Rs1 = List.last (map bnode ord) bhead).
    { rewrite /Q4 upd_ne; [| vm_compute; discriminate].
      rewrite /Q3 upd_ne; [exact HQ2s1 | vm_compute; discriminate]. }
    assert (Hpp74 : add_vec_int (mword_of_int (KernelSyms.bread + 0x70) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0x74))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp74) in "Hpc".
    (* ---- +0x74 beq s1,a5 : DEAD (the cache is never empty) ---- *)
    assert (Hbeq : eq_vec (Q4 !!! Regidx Rs1) (Q4 !!! Regidx Ra5) = false).
    { rewrite HQ4s1 HQ4a5 Hordl bcur_bwd_snoc. exact (bnode_eqv_bhead k0 Hk0). }
    iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.bread + 0x74)) (mword_of_int 16 : mword 13)
              Ra5 Rs1 Q4 (trap_res eb + (K - 6))%nat false
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rgne; rgne; exact Hbeq)
              with "Hcg Hpc Hi74").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpp78 : add_vec_int (mword_of_int (KernelSyms.bread + 0x74) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0x78))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp78) in "Hpc".
    (* ---- +0x78 c.mv a4,a5 : the loop's sentinel ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.bread + 0x78)) Ra4 Ra5
              Q4 (trap_res eb + (K - 6))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi78").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (Q5 := <[Regidx Ra4 := regval_into_reg (add_vec zero_reg (Q4 !!! Regidx Ra5))]> Q4).
    assert (HQ5a4 : Q5 !!! Regidx Ra4 = bhead).
    { rewrite /Q5 upd_eq. rewrite HQ4a5. apply add_vec_zero_l. }
    assert (HQ5s1 : Q5 !!! Regidx Rs1 = List.last (map bnode ord) bhead)
      by (rewrite /Q5 upd_ne; [exact HQ4s1 | vm_compute; discriminate]).
    assert (HQ5thr : forall c : mword 5, is_cs_idx c = true -> c <> Rs1 ->
                       Q5 !!! Regidx c = M !!! Regidx c).
    { intros c Hcs N9.
      rewrite /Q5 upd_ne; [| regne].
      rewrite /Q4 upd_ne; [| regne].
      rewrite /Q3 upd_ne; [| regne].
      rewrite /Q2 upd_ne; [| lazymatch goal with
                             | |- Regidx ?x <> Regidx ?y =>
                                 match goal with
                                 | H : x <> y |- _ => exact (fun Hq => H (regidx_inj x y Hq))
                                 end
                             end].
      rewrite /Q1 upd_ne; [reflexivity | lazymatch goal with
                                         | |- Regidx ?x <> Regidx ?y =>
                                             match goal with
                                             | H : x <> y |- _ => exact (fun Hq => H (regidx_inj x y Hq))
                                             end
                                         end]. }
    assert (HQ5regs : bd_regs m Q5).
    { rewrite /bd_regs. split_and!.
      - rewrite (HQ5thr csp_rs1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
        exact HMsp.
      - rewrite (HQ5thr Rs2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
        exact HMs2.
      - rewrite (HQ5thr Rs3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
        exact HMs3.
      - intros c Hcs N2 N8 N9 N18 N19 N4.
        rewrite (HQ5thr c Hcs N9). exact (HMthr c Hcs N2 N8 N9 N18 N19 N4). }
    iAssert (bcache_scan bn V Mg ord devs bnos)
      with "[Hauth Hsauth Hlru Hpool Hslots]" as "Hscan".
    { rewrite /bcache_scan. iFrame "Hauth Hsauth".
      iSplitR; [iPureIntro; exact Hdom|].
      iSplitR; [iPureIntro; exact Hordp2|].
      iSplitR; [iPureIntro; exact Hinj|].
        iSplitR; [iPureIntro; exact Hdevpin|].
        iFrame "Hlru Hpool Hslots". }
    assert (Hpp7a : add_vec_int (mword_of_int (KernelSyms.bread + 0x78) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0x7a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7a) in "Hpc".
    iApply (bread_bloop (CID0 := CID0)  γs j γl γu γd γk pd pav pu bn V Mg ord devs bnos
              pidv dev bno dq m K eb (length ord) lks
              HK Hbno Ha0 Ha1 Hj Hgl Hgd Hcov Hdv Htie Hbelow ord [] Q5
              ltac:(reflexivity) ltac:(rewrite app_nil_r; reflexivity)
              (bd_ord_nonnil ord Hordp) HQ5regs HQ5s1 HQ5a4
              with "Hcg Htext Hkd Hpc Hpenv Hbio Hframe Hcnt Hpay Hextc Hextm Htok Hscan Hbslot
                    Hprocs Hppid Hdev Hgeom Hdlock Hcont").
  Qed.

  (* ================================================================== *)
  (*  THE FORWARD (HIT) SCAN.  Loop head 0x3c (the dev test), advance      *)
  (*  0x36, wrap test 0x38; exits to the refcnt++ at 0x48 (dev AND blockno *)
  (*  match) or to the backward scan's preamble at 0x64 (wrapped).         *)
  (*                                                                     *)
  (*  The advance block is reached from BOTH mismatching branches, so it   *)
  (*  is asserted ONCE per iteration as the wand ["HADV"] (over an         *)
  (*  arbitrary arrival map) rather than written twice.  Like the backward *)
  (*  scan it runs entirely at the [false] index, so the wand -- and the   *)
  (*  IH -- stay at this lemma's own hart.                                 *)
  (* ================================================================== *)

  Local Lemma bread_floop `{GEN : GenId} `{CID0 : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (V : bio_view Σ)
      (Mg : gmap nat (Qp * positive)) (ord : list nat) (devs bnos : nat -> mword 32)
      (pidv dev bno : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (n : nat) (lks : gset string) :
    (K_bread <= K)%nat ->
    (uint bno < 2147483648)%Z ->
    m !!! Regidx Ra0 = sign_extend' 64 dev ->
    m !!! Regidx Ra1 = sign_extend' 64 bno ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    bv_gd V = γd ->
    uint bno ∈ bv_cov V ->
    dev = bv_dev V ->
    ord ≡ₚ seq 0 NBUF ->
    (* the whole forward scan runs while [bcache] is still held; [Hbelow] is
       what the recyc/hit exits (reached only from further down this call
       chain) need for their own [Hsetback] simplification after releasing
       it, and via [locks_below_mono] (4 <= 6) for their acquiresleep call. *)
    locks_below lks "bcache" ->
    forall (done rest : list nat) (M : regfile),
    (length rest <= n)%nat ->
    ord = (done ++ rest)%list ->
    rest <> [] ->
    (* the scan's ACCUMULATED exit tie: no slot already visited matches the
       request.  At the wrap it covers the whole order list, which is what
       upgrades (with the scan's dev pin) to the recycle's miss fact. *)
    (forall i, i ∈ done -> ¬ (devs i = dev /\ bnos i = bno)) ->
    bd_regs m M ->
    M !!! Regidx Rs1 = List.hd bhead (map bnode rest) ->
    M !!! Regidx Ra4 = bhead ->
    sie_cap_gpr kt M (trap_res eb + (K - 6))%nat false (proc_addr j) -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.bread + 0x3c) : mword 64) -∗
    panic_env -∗
    bio_ctx bn V -∗
    bd_frame m -∗
    cpu_own 1 eb (proc_addr j) false ({["bcache"]} ∪ lks) -∗
    arm_pay kt 0 eb (proc_addr j) -∗
    trap_csrs_ext kt eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    locked (bn_lk bn) cpu_id -∗
    bcache_scan bn V Mg ord devs bnos -∗
    bslot bn -∗
    procs_inv (kt := kt) γs -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    bd_cont (kt := kt) (CID0 := CID0)  j bn V pidv dev bno dq m K eb (proc_addr j) lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hbno Ha0 Ha1 Hj Hgl Hgd Hcov Hdv Hordp Hbelow.
    induction n as [|n IH];
      intros done rest M Hlen Hord Hne Hdone Hregs HMs1 HMa4.
    { exfalso. destruct rest as [|x l]; [congruence | cbn in Hlen; lia]. }
    pose proof Hregs as (HMsp & HMs2 & HMs3 & HMthr).
    destruct (bd_ord_hd rest Hne) as (kk & r & Hrest).
    assert (Hord2 : ord = (done ++ kk :: r)%list) by (rewrite Hord Hrest; reflexivity).
    assert (Hkk : (kk < NBUF)%nat) by exact (bord_split_lt ord done r kk Hordp Hord2).
    assert (Hcur : M !!! Regidx Rs1 = bnode kk)
      by (rewrite HMs1 Hrest; apply bcur_fwd_cons).
    iIntros "Hcg #Htext #Hkd Hpc #Hpenv #Hbio Hframe Hcnt Hpay Hextc Hextm Htok Hscan Hbslot".
    iIntros "#Hprocs Hppid #Hdev #Hgeom #Hdlock Hcont".
    iPoseProof (bdi_3c with "Htext") as "Hi3c".
    iPoseProof (bdi_3e with "Htext") as "Hi3e".
    iPoseProof (bdi_42 with "Htext") as "Hi42".
    iPoseProof (bdi_44 with "Htext") as "Hi44".
    (* ---- the ADVANCE block (0x36 / 0x38), asserted once ---- *)
    iAssert (∀ Mx : regfile,
               ⌜bd_regs m Mx
                /\ Mx !!! Regidx Rs1 = bnode kk /\ Mx !!! Regidx Ra4 = bhead
                /\ ¬ (devs kk = dev /\ bnos kk = bno)⌝ -∗
               sie_cap_gpr kt Mx (trap_res eb + (K - 6))%nat false (proc_addr j) -∗
               pc_is (mword_of_int (KernelSyms.bread + 0x36) : mword 64) -∗
               bd_frame m -∗
               cpu_own 1 eb (proc_addr j) false ({["bcache"]} ∪ lks) -∗
               arm_pay kt 0 eb (proc_addr j) -∗
               trap_csrs_ext kt eb -∗
               cpu_claim_ext eb (proc_addr j) -∗
               locked (bn_lk bn) cpu_id -∗
               bcache_scan bn V Mg ord devs bnos -∗
               bslot bn -∗
               p_pid (proc_addr j) ↦₄{dq} pidv -∗
               bd_cont (kt := kt) (CID0 := CID0)  j bn V pidv dev bno dq m K eb (proc_addr j) lks -∗
               WP (Loop : expr riscv_lang))%I as "HADV".
    { iIntros (Mx (Hxregs & Hxs1 & Hxa4 & Hxne)).
      iIntros "Hcg Hpc Hframe Hcnt Hpay Hextc Hextm Htok Hscan Hbslot Hppid Hcont".
      pose proof Hxregs as (Hxsp & Hxs2 & Hxs3 & Hxthr).
      assert (Hdone' : forall i, i ∈ (done ++ [kk])%list ->
                         ¬ (devs i = dev /\ bnos i = bno)).
      { intros i Hi. apply elem_of_app in Hi as [Hi | Hi].
        - exact (Hdone i Hi).
        - apply elem_of_list_singleton in Hi. subst i. exact Hxne. }
      iPoseProof (bdi_36 with "Htext") as "Hi36".
      iPoseProof (bdi_38 with "Htext") as "Hi38".
      rewrite /bcache_scan.
      iDestruct "Hscan" as
      "(Hauth & Hsauth & %Hdom & %Hordp2 & %Hinj & %Hdevpin & Hlru & Hpool & Hslots)".
      iEval (rewrite Hord2 (bcur_fwd_split done kk r)) in "Hlru".
      iDestruct (bcache_lru_next_acc bhead (bnode kk) (map bnode done) (map bnode r)
                   with "Hlru") as "[Hnextc Hrelink]".
      assert (Hxs1g : rget Mx Rs1 = bnode kk) by (rgne; exact Hxs1).
      iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.bread + 0x36)) Rs1 Rs1 (mword_of_int 80 : mword 12)
                Mx (trap_res eb + (K - 6))%nat (List.hd bhead (map bnode r)) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi36 [Hnextc]").
      { iEval (rewrite Hxs1g). iExact "Hnextc". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hnextc".
      iEval (rewrite Hxs1g) in "Hnextc".
      iDestruct ("Hrelink" with "Hnextc") as "Hlru".
      iEval (rewrite -(bcur_fwd_split done kk r) -Hord2) in "Hlru".
      set (G1 := <[Regidx Rs1 := regval_into_reg (List.hd bhead (map bnode r))]> Mx).
      assert (HG1s1 : G1 !!! Regidx Rs1 = List.hd bhead (map bnode r))
        by (rewrite /G1; apply upd_eq).
      assert (HG1a4 : G1 !!! Regidx Ra4 = bhead)
        by (rewrite /G1 upd_ne; [exact Hxa4 | vm_compute; discriminate]).
      assert (HG1regs : bd_regs m G1).
      { rewrite /bd_regs. split_and!.
        - rewrite /G1 upd_ne; [exact Hxsp | vm_compute; discriminate].
        - rewrite /G1 upd_ne; [exact Hxs2 | vm_compute; discriminate].
        - rewrite /G1 upd_ne; [exact Hxs3 | vm_compute; discriminate].
        - intros c Hcs N2 N8 N9 N18 N19 N4.
          rewrite /G1 upd_ne; [| lazymatch goal with
                                 | |- Regidx ?x <> Regidx ?y =>
                                     match goal with
                                     | H : x <> y |- _ => exact (fun Hq => H (regidx_inj x y Hq))
                                     end
                                 end].
          exact (Hxthr c Hcs N2 N8 N9 N18 N19 N4). }
      iAssert (bcache_scan bn V Mg ord devs bnos)
        with "[Hauth Hsauth Hlru Hpool Hslots]" as "Hscan".
      { rewrite /bcache_scan. iFrame "Hauth Hsauth".
        iSplitR; [iPureIntro; exact Hdom|].
        iSplitR; [iPureIntro; exact Hordp2|].
        iSplitR; [iPureIntro; exact Hinj|].
        iSplitR; [iPureIntro; exact Hdevpin|].
        iFrame "Hlru Hpool Hslots". }
      assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.bread + 0x36) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0x38))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp38) in "Hpc".
      destruct (decide (r = [])) as [Hre | Hrne].
      + (* the scan has wrapped: on to the backward scan *)
        assert (Hbeq : eq_vec (G1 !!! Regidx Rs1) (G1 !!! Regidx Ra4) = true).
        { rewrite HG1s1 HG1a4 Hre bcur_fwd_nil. exact bhead_eqv_self. }
        iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.bread + 0x38)) (mword_of_int 44 : mword 13)
                  Ra4 Rs1 G1 (trap_res eb + (K - 6))%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rgne; exact Hbeq)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi38").
        iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Htgt64 : add_vec (mword_of_int (KernelSyms.bread + 0x38) : mword 64)
                           (sign_extend' 64 (mword_of_int 44 : mword 13))
                         = mword_of_int (KernelSyms.bread + 0x64))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt64) in "Hpc".
        assert (Hordk : ord = (done ++ [kk])%list) by (rewrite Hord2 Hre; reflexivity).
        assert (Htie : forall i, (i < NBUF)%nat -> ¬ (devs i = dev /\ bnos i = bno)).
        { intros i Hi. apply Hdone'. rewrite -Hordk. exact (bd_ord_mem ord Hordp i Hi). }
        iApply (bread_miss (CID0 := CID0)  γs j γl γu γd γk pd pav pu bn V Mg ord devs bnos
                  pidv dev bno dq m G1 K eb lks
                  HK Hbno Ha0 Ha1 Hj Hgl Hgd Hcov Hdv Htie Hordp HG1regs Hbelow
                  with "Hcg Htext Hkd Hpc Hpenv Hbio Hframe Hcnt Hpay Hextc Hextm Htok Hscan Hbslot
                        Hprocs Hppid Hdev Hgeom Hdlock Hcont").
      + (* another buffer to test: back to the loop head *)
        destruct (bd_ord_hd r Hrne) as (kk2 & r2 & Hr2).
        assert (Hord3 : ord = ((done ++ [kk]) ++ kk2 :: r2)%list).
        { rewrite Hord2 Hr2 -app_assoc. reflexivity. }
        assert (Hkk2 : (kk2 < NBUF)%nat)
          by exact (bord_split_lt ord (done ++ [kk]) r2 kk2 Hordp Hord3).
        assert (Hbeq : eq_vec (G1 !!! Regidx Rs1) (G1 !!! Regidx Ra4) = false).
        { rewrite HG1s1 HG1a4 Hr2 bcur_fwd_cons. exact (bnode_eqv_bhead kk2 Hkk2). }
        iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.bread + 0x38)) (mword_of_int 44 : mword 13)
                  Ra4 Rs1 G1 (trap_res eb + (K - 6))%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rgne; exact Hbeq)
                  with "Hcg Hpc Hi38").
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc".
        assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.bread + 0x38) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0x3c))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp3c) in "Hpc".
        assert (Hlen' : (length r <= n)%nat).
        { rewrite Hrest in Hlen. cbn in Hlen. lia. }
        iApply (IH (done ++ [kk])%list r G1 Hlen'
                  ltac:(rewrite Hord2 -app_assoc; reflexivity) Hrne Hdone'
                  HG1regs HG1s1 HG1a4
                  with "Hcg Htext Hkd Hpc Hpenv Hbio Hframe Hcnt Hpay Hextc Hextm Htok Hscan Hbslot
                        Hprocs Hppid Hdev Hgeom Hdlock Hcont"). }
    (* ---- the per-iteration borrow of b->dev and b->blockno ---- *)
    rewrite /bcache_scan.
    iDestruct "Hscan" as
      "(Hauth & Hsauth & %Hdom & %Hordp2 & %Hinj & %Hdevpin & Hlru & Hpool & Hslots)".
    iDestruct (bio_slots_acc bn Mg devs bnos kk Hkk with "Hslots") as "[Hslot Hback]".
    iDestruct (bio_slot_devbno_acc bn Mg kk (devs kk) (bnos kk) with "Hslot")
      as (qc) "(Hdevc & Hbnoc & Hbackslot)".
    assert (Hadev : add_vec (rget M Rs1) (sign_extend' 64 (mword_of_int 8 : mword 12))
                    = b_dev (bpa kk)).
    { rgne. rewrite Hcur bd_s8. rewrite /b_dev /bpa /pa_add /add_vec_int. reflexivity. }
    (* ---- +0x3c c.lw a5,8(s1) : b->dev ---- *)
    iEval (rewrite -Hadev) in "Hdevc".
    iApply (wp_clw_s_sconf (dqm := DfracOwn qc) (mword_of_int (KernelSyms.bread + 0x3c)) Ra5 Rs1
              (mword_of_int 8 : mword 12) M (trap_res eb + (K - 6))%nat (devs kk) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3c Hdevc").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hdevc".
    iEval (rewrite Hadev) in "Hdevc".
    set (F1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (devs kk))]> M).
    assert (HF1a5 : F1 !!! Regidx Ra5 = sign_extend' 64 (devs kk))
      by (rewrite /F1; apply upd_eq).
    assert (HF1s1 : F1 !!! Regidx Rs1 = bnode kk)
      by (rewrite /F1 upd_ne; [exact Hcur | vm_compute; discriminate]).
    assert (HF1s2 : F1 !!! Regidx Rs2 = m !!! Regidx Ra0)
      by (rewrite /F1 upd_ne; [exact HMs2 | vm_compute; discriminate]).
    assert (HF1s3 : F1 !!! Regidx Rs3 = m !!! Regidx Ra1)
      by (rewrite /F1 upd_ne; [exact HMs3 | vm_compute; discriminate]).
    assert (HF1a4 : F1 !!! Regidx Ra4 = bhead)
      by (rewrite /F1 upd_ne; [exact HMa4 | vm_compute; discriminate]).
    assert (HF1regs : bd_regs m F1).
    { rewrite /bd_regs. split_and!;
        [ rewrite /F1 upd_ne; [exact HMsp | vm_compute; discriminate]
        | exact HF1s2 | exact HF1s3 |].
      intros c Hcs N2 N8 N9 N18 N19 N4.
      rewrite /F1 upd_ne; [| apply not_eq_sym; apply is_cs_idx_true_neq;
                             [vm_compute; reflexivity | assumption]].
      exact (HMthr c Hcs N2 N8 N9 N18 N19 N4). }
    assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.bread + 0x3c) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0x3e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3e) in "Hpc".
    destruct (decide (devs kk = dev)) as [Hdeq | Hdne].
    - (* ---- dev matches: test the block number ---- *)
      assert (Hbne : neq_vec (F1 !!! Regidx Ra5) (F1 !!! Regidx Rs2) = false).
      { rewrite HF1a5 HF1s2 Ha0 bd_sext_neqv. unfold neq_vec.
        rewrite (proj2 (eq_vec_true_iff (devs kk) dev) Hdeq). reflexivity. }
      iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.bread + 0x3e)) (mword_of_int 8184 : mword 13)
                Rs2 Ra5 F1 (trap_res eb + (K - 6))%nat false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgne; rgne; exact Hbne)
                with "Hcg Hpc Hi3e").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.bread + 0x3e) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0x42))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      (* ---- +0x42 c.lw a5,12(s1) : b->blockno ---- *)
      assert (Habno : add_vec (rget F1 Rs1) (sign_extend' 64 (mword_of_int 12 : mword 12))
                      = b_blockno (bpa kk)).
      { rgne. rewrite HF1s1 bd_s12. rewrite /b_blockno /bpa /pa_add /add_vec_int. reflexivity. }
      iEval (rewrite -Habno) in "Hbnoc".
      iApply (wp_clw_s_sconf (dqm := DfracOwn qc) (mword_of_int (KernelSyms.bread + 0x42)) Ra5 Rs1
                (mword_of_int 12 : mword 12) F1 (trap_res eb + (K - 6))%nat (bnos kk) false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi42 Hbnoc").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hbnoc".
      iEval (rewrite Habno) in "Hbnoc".
      set (F2 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (bnos kk))]> F1).
      assert (HF2a5 : F2 !!! Regidx Ra5 = sign_extend' 64 (bnos kk))
        by (rewrite /F2; apply upd_eq).
      assert (HF2s1 : F2 !!! Regidx Rs1 = bnode kk)
        by (rewrite /F2 upd_ne; [exact HF1s1 | vm_compute; discriminate]).
      assert (HF2s3 : F2 !!! Regidx Rs3 = m !!! Regidx Ra1)
        by (rewrite /F2 upd_ne; [exact HF1s3 | vm_compute; discriminate]).
      assert (HF2a4 : F2 !!! Regidx Ra4 = bhead)
        by (rewrite /F2 upd_ne; [exact HF1a4 | vm_compute; discriminate]).
      assert (HF2regs : bd_regs m F2).
      { rewrite /bd_regs. split_and!.
        - rewrite /F2 upd_ne; [| vm_compute; discriminate].
          rewrite /F1 upd_ne; [exact HMsp | vm_compute; discriminate].
        - rewrite /F2 upd_ne; [exact HF1s2 | vm_compute; discriminate].
        - exact HF2s3.
        - intros c Hcs N2 N8 N9 N18 N19 N4.
          rewrite /F2 upd_ne; [| apply not_eq_sym; apply is_cs_idx_true_neq;
                                 [vm_compute; reflexivity | assumption]].
          rewrite /F1 upd_ne; [| apply not_eq_sym; apply is_cs_idx_true_neq;
                                 [vm_compute; reflexivity | assumption]].
          exact (HMthr c Hcs N2 N8 N9 N18 N19 N4). }
      (* the cells go home either way *)
      iDestruct ("Hbackslot" with "Hdevc Hbnoc") as "Hslot".
      iDestruct ("Hback" $! Mg devs bnos with "[%] Hslot") as "Hslots".
      { intros i Hi. split_and!; reflexivity. }
      iAssert (bcache_scan bn V Mg ord devs bnos)
        with "[Hauth Hsauth Hlru Hpool Hslots]" as "Hscan".
      { rewrite /bcache_scan. iFrame "Hauth Hsauth".
        iSplitR; [iPureIntro; exact Hdom|].
        iSplitR; [iPureIntro; exact Hordp2|].
        iSplitR; [iPureIntro; exact Hinj|].
        iSplitR; [iPureIntro; exact Hdevpin|].
        iFrame "Hlru Hpool Hslots". }
      assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.bread + 0x42) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0x44))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp44) in "Hpc".
      destruct (decide (bnos kk = bno)) as [Hbeq2 | Hbne2].
      + (* ======== THE HIT ======== *)
        assert (Hbne3 : neq_vec (F2 !!! Regidx Ra5) (F2 !!! Regidx Rs3) = false).
        { rewrite HF2a5 HF2s3 Ha1 bd_sext_neqv. unfold neq_vec.
          rewrite (proj2 (eq_vec_true_iff (bnos kk) bno) Hbeq2). reflexivity. }
        iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.bread + 0x44)) (mword_of_int 8178 : mword 13)
                  Rs3 Ra5 F2 (trap_res eb + (K - 6))%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rgne; exact Hbne3)
                  with "Hcg Hpc Hi44").
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc".
        assert (Hpp48 : add_vec_int (mword_of_int (KernelSyms.bread + 0x44) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0x48))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp48) in "Hpc".
        iApply (bread_hit (CID0 := CID0)  γs j γl γu γd γk pd pav pu bn V kk Mg ord devs bnos
                  pidv dev bno dq m F2 K eb lks
                  HK Hbno Hkk Hdeq Hbeq2 Hgd Hcov Hdv Hj Hgl HF2regs HF2s1 Hbelow
                  with "Hcg Htext Hpc Hbio Hframe Hcnt Hpay Hextc Hextm Htok Hscan Hbslot
                        Hprocs Hppid Hdev Hgeom Hdlock Hcont").
      + (* blockno mismatch: advance *)
        assert (Hbne3 : neq_vec (F2 !!! Regidx Ra5) (F2 !!! Regidx Rs3) = true).
        { rewrite HF2a5 HF2s3 Ha1 bd_sext_neqv. unfold neq_vec.
          rewrite (proj2 (eq_vec_false_iff (bnos kk) bno) Hbne2). reflexivity. }
        iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.bread + 0x44)) (mword_of_int 8178 : mword 13)
                  Rs3 Ra5 F2 (trap_res eb + (K - 6))%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rgne; exact Hbne3)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi44").
        iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Htgt36 : add_vec (mword_of_int (KernelSyms.bread + 0x44) : mword 64)
                           (sign_extend' 64 (mword_of_int 8178 : mword 13))
                         = mword_of_int (KernelSyms.bread + 0x36))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt36) in "Hpc".
        iApply ("HADV" $! F2 with "[%] Hcg Hpc Hframe Hcnt Hpay Hextc Hextm Htok Hscan Hbslot Hppid Hcont").
        split_and!; [exact HF2regs | exact HF2s1 | exact HF2a4 |].
        intros [_ Hc]. exact (Hbne2 Hc).
    - (* ---- dev mismatch: advance ---- *)
      assert (Hbne : neq_vec (F1 !!! Regidx Ra5) (F1 !!! Regidx Rs2) = true).
      { rewrite HF1a5 HF1s2 Ha0 bd_sext_neqv. unfold neq_vec.
        rewrite (proj2 (eq_vec_false_iff (devs kk) dev) Hdne). reflexivity. }
      iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.bread + 0x3e)) (mword_of_int 8184 : mword 13)
                Rs2 Ra5 F1 (trap_res eb + (K - 6))%nat false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgne; rgne; exact Hbne)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi3e").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Htgt36 : add_vec (mword_of_int (KernelSyms.bread + 0x3e) : mword 64)
                         (sign_extend' 64 (mword_of_int 8184 : mword 13))
                       = mword_of_int (KernelSyms.bread + 0x36))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt36) in "Hpc".
      iDestruct ("Hbackslot" with "Hdevc Hbnoc") as "Hslot".
      iDestruct ("Hback" $! Mg devs bnos with "[%] Hslot") as "Hslots".
      { intros i Hi. split_and!; reflexivity. }
      iAssert (bcache_scan bn V Mg ord devs bnos)
        with "[Hauth Hsauth Hlru Hpool Hslots]" as "Hscan".
      { rewrite /bcache_scan. iFrame "Hauth Hsauth".
        iSplitR; [iPureIntro; exact Hdom|].
        iSplitR; [iPureIntro; exact Hordp2|].
        iSplitR; [iPureIntro; exact Hinj|].
        iSplitR; [iPureIntro; exact Hdevpin|].
        iFrame "Hlru Hpool Hslots". }
      iApply ("HADV" $! F1 with "[%] Hcg Hpc Hframe Hcnt Hpay Hextc Hextm Htok Hscan Hbslot Hppid Hcont").
      split_and!; [exact HF1regs | exact HF1s1 | exact HF1a4 |].
      intros [Hc _]. exact (Hdne Hc).
  Qed.

End BreadBlocks.

(* ===================================================================== *)

Section ProofBread.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ, !uartGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Context {kt : ktier}.
  Lemma wp_bread_sconf
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (V : bio_view Σ)
      (pidv dev bno : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
    : wp_bread_sconf_body kt γs j γl γu γd γk pd pav pu bn V
                          pidv dev bno dq m K eb b lks.
  Proof.
    cbv beta delta [wp_bread_sconf_body].
    intros pcE pj ret_tgt HK Hbno Hgd Hcov Hdv Hj Hgl Ha0 Ha1 Hbelow.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec (m !!! Regidx csp_rs1 : mword 64)
                  (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))).
    iIntros "Hcg Hcnt Hextc Hextm #Htext #Hkd Hpc #Hpenv #Hbio Hppid #Hprocs".
    iIntros "#Hdev #Hgeom #Hdlock Hbslot Hcont".
    (* bread enters at level 0, so the live index IS the saved base: one
       variable [eb] carries both, and release's exit index becomes literally
       the index the postcondition asks for (the porting guide's "derive the
       SIE index rather than stating it").  The trap-CSR complement threaded
       in above is bread's OWN premise now, index-free in shape: at
       [eb = true] it is [emp] (the acquire below mints what the two parking
       callees need); at [eb = false] it is the honest pair, carried
       untouched past the acquire (whose push_off frees nothing at
       [eb = false]) and past the whole bcache-lock interior, since the
       function's OWN release always spends the [arm_pay] it minted, never
       this complement. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbe. cbn in Hbe. subst b.
    iAssert (bd_cont (kt := kt) (CID0 := CID)  j bn V pidv dev bno dq m K eb pj lks)
      with "[Hcont]" as "Hcont".
    { rewrite /bd_cont. iExact "Hcont". }
    iDestruct (bio_ctx_lock with "Hbio") as "#Hlock".
    iPoseProof (bdi_00 with "Htext") as "Hi00".
    iPoseProof (bdi_02 with "Htext") as "Hi02".
    iPoseProof (bdi_04 with "Htext") as "Hi04".
    iPoseProof (bdi_06 with "Htext") as "Hi06".
    iPoseProof (bdi_08 with "Htext") as "Hi08".
    iPoseProof (bdi_0a with "Htext") as "Hi0a".
    iPoseProof (bdi_0c with "Htext") as "Hi0c".
    iPoseProof (bdi_0e with "Htext") as "Hi0e".
    iPoseProof (bdi_10 with "Htext") as "Hi10".
    iPoseProof (bdi_12 with "Htext") as "Hi12".
    iPoseProof (bdi_16 with "Htext") as "Hi16".
    iPoseProof (bdi_1a with "Htext") as "Hi1a".
    (* ===== PROLOGUE ===== *)
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 6).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 61 : mword 6) m K 6 eb
              ltac:(lia) Hpush with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    assert (HR1ra : R1 !!! Regidx Rra = m !!! Regidx Rra)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1s0 : R1 !!! Regidx Rs0 = m !!! Regidx Rs0)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1s1 : R1 !!! Regidx Rs1 = m !!! Regidx Rs1)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1s2 : R1 !!! Regidx Rs2 = m !!! Regidx Rs2)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1s3 : R1 !!! Regidx Rs3 = m !!! Regidx Rs3)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite (stack_own_slots (KTR := kt)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & _)".
    iDestruct "S1" as (v40) "Hr40". iDestruct "S2" as (v32) "Hr32".
    iDestruct "S3" as (v24) "Hr24". iDestruct "S4" as (v16) "Hr16".
    iDestruct "S5" as (v8)  "Hr8".  iDestruct "S6" as (v0)  "Hr0".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hr40". iEval (rewrite -Hb2) in "Hr32".
    iEval (rewrite -Hb3) in "Hr24". iEval (rewrite -Hb4) in "Hr16".
    iEval (rewrite -Hb5) in "Hr8".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.bread + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.bread + 0x02)) (mword_of_int 5 : mword 6) Rra
              R1 (K - 6)%nat v40 eb with "Hcg Hpc Hi02 Hr40").
    iIntros (CID2 Hs2) "Hcg Hpc Hr40".
    iEval (rgne) in "Hr40".
    iEval (rewrite Hb1 HR1ra) in "Hr40".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.bread + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.bread + 0x04)) (mword_of_int 4 : mword 6) Rs0
              R1 (K - 6)%nat v32 eb with "Hcg Hpc Hi04 Hr32").
    iIntros (CID3 Hs3) "Hcg Hpc Hr32".
    iEval (rgne) in "Hr32".
    iEval (rewrite Hb2 HR1s0) in "Hr32".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.bread + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.bread + 0x06)) (mword_of_int 3 : mword 6) Rs1
              R1 (K - 6)%nat v24 eb with "Hcg Hpc Hi06 Hr24").
    iIntros (CID4 Hs4) "Hcg Hpc Hr24".
    iEval (rgne) in "Hr24".
    iEval (rewrite Hb3 HR1s1) in "Hr24".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.bread + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.bread + 0x08)) (mword_of_int 2 : mword 6) Rs2
              R1 (K - 6)%nat v16 eb with "Hcg Hpc Hi08 Hr16").
    iIntros (CID5 Hs5) "Hcg Hpc Hr16".
    iEval (rgne) in "Hr16".
    iEval (rewrite Hb4 HR1s2) in "Hr16".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.bread + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.bread + 0x0a)) (mword_of_int 1 : mword 6) Rs3
              R1 (K - 6)%nat v8 eb with "Hcg Hpc Hi0a Hr8").
    iIntros (CID6 Hs6) "Hcg Hpc Hr8".
    iEval (rgne) in "Hr8".
    iEval (rewrite Hb5 HR1s3) in "Hr8".
    iAssert (bd_frame m) with "[Hr40 Hr32 Hr24 Hr16 Hr8 Hr0]" as "Hframe".
    { rewrite /bd_frame. iFrame "Hr40 Hr32 Hr24 Hr16 Hr8".
      iExists v0. iExact "Hr0". }
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.bread + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c c.addi4spn s0,sp,48 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.bread + 0x0c)) (Cregidx (mword_of_int 0))
              (mword_of_int 12 : mword 8) Rs0 R1 (K - 6)%nat eb
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok)
              with "Hcg Hpc Hi0c").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> R1).
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.bread + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0x0e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e c.mv s2,a0 : s2 := dev *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.bread + 0x0e)) Rs2 Ra0
              R2 (K - 6)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e").
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R3 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (R2 !!! Regidx Ra0))]> R2).
    assert (HR3s2 : R3 !!! Regidx Rs2 = m !!! Regidx Ra0).
    { rewrite /R3 upd_eq. unfold regval_into_reg.
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      apply add_vec_zero_l. }
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.bread + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 c.mv s3,a1 : s3 := blockno *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.bread + 0x10)) Rs3 Ra1
              R3 (K - 6)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10").
    iIntros (CID9 Hs9) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R4 := <[Regidx Rs3 := regval_into_reg (add_vec zero_reg (R3 !!! Regidx Ra1))]> R3).
    assert (HR4s3 : R4 !!! Regidx Rs3 = m !!! Regidx Ra1).
    { rewrite /R4 upd_eq. unfold regval_into_reg.
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      apply add_vec_zero_l. }
    assert (HR4s2 : R4 !!! Regidx Rs2 = m !!! Regidx Ra0)
      by (rewrite /R4 upd_ne; [exact HR3s2 | vm_compute; discriminate]).
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.bread + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0x12))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* +0x12 / +0x16 : a0 := &bcache ; +0x1a jal acquire *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.bread + 0x12)) Ra0 (mword_of_int 0x15 : mword 20)
              R4 (K - 6)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12").
    iIntros (CID10 Hs10) "Hcg Hpc".
    set (R5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.bread + 0x12) : mword 64)
                     (auipc_off (mword_of_int 0x15 : mword 20)))]> R4).
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.bread + 0x12) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0x16))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.bread + 0x16)) Ra0 Ra0 (mword_of_int 1680 : mword 12)
              R5 (K - 6)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16").
    iIntros (CID11 Hs11) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R6 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (R5 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 1680 : mword 12)))]> R5).
    assert (HR6a0 : R6 !!! Regidx Ra0 = bcache_addr).
    { rewrite /R6 upd_eq /R5 upd_eq. rewrite /bcache_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.bread + 0x16) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0x1a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.bread + 0x1a)) Rra (mword_of_int 2089026 : mword 21)
              R6 (K - 6)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi1a").
    iIntros (CID12 Hs12) "Hcg Hpc".
    set (R7 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.bread + 0x1a) : mword 64) 4)]> R6).
    assert (Htgtacq : add_vec (mword_of_int (KernelSyms.bread + 0x1a) : mword 64)
                        (sign_extend' 64 (mword_of_int 2089026 : mword 21))
                      = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtacq) in "Hpc".
    assert (HR7thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              R7 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /R7 upd_ne; [| regne].
      rewrite /R6 upd_ne; [| regne].
      rewrite /R5 upd_ne; [| regne].
      rewrite /R4 upd_ne; [| regne].
      rewrite /R3 upd_ne; [| regne].
      rewrite /R2 upd_ne; [| regne].
      rewrite /R1 upd_ne; [reflexivity | regne]. }
    assert (HR7sp : R7 !!! Regidx csp_rs1 = spr).
    { rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [exact HspR1 | vm_compute; discriminate]. }
    assert (HR7s2 : R7 !!! Regidx Rs2 = m !!! Regidx Ra0).
    { rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [exact HR4s2 | vm_compute; discriminate]. }
    assert (HR7s3 : R7 !!! Regidx Rs3 = m !!! Regidx Ra1).
    { rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [exact HR4s3 | vm_compute; discriminate]. }
    assert (HR7a0 : R7 !!! Regidx Ra0 = bcache_addr)
      by (rewrite /R7 upd_ne; [exact HR6a0 | vm_compute; discriminate]).
    assert (HR7ra : R7 !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.bread + 0x1a) : mword 64) 4)
      by (rewrite /R7; apply upd_eq).
    iDestruct (cpu_own_transport CID CID12 0%nat eb pj eb ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (A.wp_acquire_sconf kt (bn_lk bn) "bcache"%string (bcache_res bn V) R7
              0%nat eb pj (K - 6)%nat eb lks
              ltac:(vm_compute; reflexivity) ltac:(lia)
              Hbelow
              with "Hcg Hcnt Htext Hpc [Hlock]").
    all: try lkbelow.
    { iEval (rewrite HR7a0). iExact "Hlock". }
    (* acquire returns with interrupts OFF, so the whole bget interior below
       runs at the literal [false] index and the hart is pinned at [CIDq].
       [Hcont] is re-anchored here, ONCE, and travels the rest of the way as
       an ordinary frame. *)
    iIntros (CIDq Hsq ms mq) "%Hmsfacts Hcg Hpc %Hacqpins Htok HRres Hcnt Hpay".
    assert (Hpc1e : ret_pc (R7 !!! Regidx Rra) = mword_of_int (KernelSyms.bread + 0x1e)).
    { rewrite HR7ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc1e) in "Hpc".
    pose proof Hacqpins as Hacqpins_cs.
    iDestruct (bd_cont_shift (CIDa := CID) (CIDb := CIDq)  j bn V pidv dev bno dq
                 m K eb pj lks ltac:(wp_next_chain) with "Hcont") as "Hcont".
    (* the trap-CSR complement is untouched since entry -- bread's own
       release/acquire dance never conjures it, only [arm_pay] -- so its
       first transport goes straight from the entry hart to [CIDq]. *)
    iDestruct (trap_csrs_ext_transport CID CIDq eb pj ltac:(wp_next_chain)
                 with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID CIDq eb pj ltac:(wp_next_chain)
                 with "Hextm") as "Hextm".
    (* ===== the forward scan's entry ===== *)
    iDestruct (bcache_res_to_scan bn V with "HRres") as (Mg ord devs bnos) "Hscan".
    rewrite /bcache_scan.
    iDestruct "Hscan" as
      "(Hauth & Hsauth & %Hdom & %Hordp & %Hinj & %Hdevpin & Hlru & Hpool & Hslots)".
    destruct (bd_ord_hd ord (bd_ord_nonnil ord Hordp)) as (k0 & r0 & Hordh).
    assert (Hk0 : (k0 < NBUF)%nat)
      by exact (bord_split_lt ord [] r0 k0 Hordp Hordh).
    iPoseProof (bdi_1e with "Htext") as "Hi1e".
    iPoseProof (bdi_22 with "Htext") as "Hi22".
    iPoseProof (bdi_26 with "Htext") as "Hi26".
    iPoseProof (bdi_2a with "Htext") as "Hi2a".
    iPoseProof (bdi_2e with "Htext") as "Hi2e".
    iPoseProof (bdi_32 with "Htext") as "Hi32".
    iPoseProof (bdi_34 with "Htext") as "Hi34".
    (* +0x1e auipc s1,0x1e ; +0x22 ld s1,-1804(s1) : s1 := bcache.head.next *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.bread + 0x1e)) Rs1 (mword_of_int 30 : mword 20)
              mq (trap_res eb + (K - 6))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (W1 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.bread + 0x1e) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> mq).
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.bread + 0x1e) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    assert (Hhn : add_vec (rget W1 Rs1) (sign_extend' 64 (mword_of_int 2364 : mword 12))
                  = bnext bhead).
    { rgne. rewrite /W1 upd_eq. unfold regval_into_reg.
      rewrite /bnext /bhead /bnode /acur. apply bv_eq; vm_compute; reflexivity. }
    iDestruct (bcache_lru_head_next_acc bhead (map bnode ord) with "Hlru") as "[Hhnc Hrelink]".
    iApply (wp_ld_s_sconf (mword_of_int (KernelSyms.bread + 0x22)) Rs1 Rs1 (mword_of_int 2364 : mword 12)
              W1 (trap_res eb + (K - 6))%nat (List.hd bhead (map bnode ord)) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 [Hhnc]").
    { iEval (rewrite Hhn). iExact "Hhnc". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hhnc".
    iEval (rewrite Hhn) in "Hhnc".
    iDestruct ("Hrelink" with "Hhnc") as "Hlru".
    set (W2 := <[Regidx Rs1 := regval_into_reg (List.hd bhead (map bnode ord))]> W1).
    assert (HW2s1 : W2 !!! Regidx Rs1 = List.hd bhead (map bnode ord))
      by (rewrite /W2; apply upd_eq).
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.bread + 0x22) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0x26))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    (* +0x26 / +0x2a : a5 := &bcache.head *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.bread + 0x26)) Ra5 (mword_of_int 30 : mword 20)
              W2 (trap_res eb + (K - 6))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (W3 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.bread + 0x26) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> W2).
    assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.bread + 0x26) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0x2a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2a) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.bread + 0x2a)) Ra5 Ra5 (mword_of_int 2276 : mword 12)
              W3 (trap_res eb + (K - 6))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2a").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (W4 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (W3 !!! Regidx Ra5)
                     (sign_extend' 64 (mword_of_int 2276 : mword 12)))]> W3).
    assert (HW4a5 : W4 !!! Regidx Ra5 = bhead).
    { rewrite /W4 upd_eq /W3 upd_eq. unfold regval_into_reg.
      rewrite /bhead /bnode /acur. apply bv_eq; vm_compute; reflexivity. }
    assert (HW4s1 : W4 !!! Regidx Rs1 = List.hd bhead (map bnode ord))
      by (rewrite /W4 upd_ne; [| vm_compute; discriminate];
          rewrite /W3 upd_ne; [exact HW2s1 | vm_compute; discriminate]).
    assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.bread + 0x2a) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0x2e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    (* +0x2e beq s1,a5 : DEAD (the cache is never empty) *)
    assert (Hbeq : eq_vec (W4 !!! Regidx Rs1) (W4 !!! Regidx Ra5) = false).
    { rewrite HW4s1 HW4a5 Hordh bcur_fwd_cons. exact (bnode_eqv_bhead k0 Hk0). }
    iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.bread + 0x2e)) (mword_of_int 54 : mword 13)
              Ra5 Rs1 W4 (trap_res eb + (K - 6))%nat false
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rgne; rgne; exact Hbeq)
              with "Hcg Hpc Hi2e").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.bread + 0x2e) : mword 64) 4 = mword_of_int (KernelSyms.bread + 0x32))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    (* +0x32 c.mv a4,a5 : the scan's sentinel *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.bread + 0x32)) Ra4 Ra5
              W4 (trap_res eb + (K - 6))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi32").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (W5 := <[Regidx Ra4 := regval_into_reg (add_vec zero_reg (W4 !!! Regidx Ra5))]> W4).
    assert (HW5a4 : W5 !!! Regidx Ra4 = bhead).
    { rewrite /W5 upd_eq. rewrite HW4a5. apply add_vec_zero_l. }
    assert (HW5s1 : W5 !!! Regidx Rs1 = List.hd bhead (map bnode ord))
      by (rewrite /W5 upd_ne; [exact HW4s1 | vm_compute; discriminate]).
    assert (HW5thr : forall c : mword 5, is_cs_idx c = true -> c <> Rs1 ->
                       W5 !!! Regidx c = mq !!! Regidx c).
    { intros c Hcs N9.
      rewrite /W5 upd_ne; [| regne].
      rewrite /W4 upd_ne; [| regne].
      rewrite /W3 upd_ne; [| regne].
      rewrite /W2 upd_ne; [| lazymatch goal with
                             | |- Regidx ?x <> Regidx ?y =>
                                 match goal with
                                 | H : x <> y |- _ => exact (fun Hq => H (regidx_inj x y Hq))
                                 end
                             end].
      rewrite /W1 upd_ne; [reflexivity | lazymatch goal with
                                         | |- Regidx ?x <> Regidx ?y =>
                                             match goal with
                                             | H : x <> y |- _ => exact (fun Hq => H (regidx_inj x y Hq))
                                             end
                                         end]. }
    assert (HW5regs : bd_regs m W5).
    { rewrite /bd_regs. split_and!.
      - rewrite (HW5thr csp_rs1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
        rewrite (callee_saved_lookup Hacqpins_cs csp_rs1 ltac:(vm_compute; reflexivity)).
        exact HR7sp.
      - rewrite (HW5thr Rs2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
        rewrite (callee_saved_lookup Hacqpins_cs Rs2 ltac:(vm_compute; reflexivity)).
        exact HR7s2.
      - rewrite (HW5thr Rs3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)).
        rewrite (callee_saved_lookup Hacqpins_cs Rs3 ltac:(vm_compute; reflexivity)).
        exact HR7s3.
      - intros c Hcs N2 N8 N9 N18 N19 N4.
        rewrite (HW5thr c Hcs N9).
        rewrite (callee_saved_lookup Hacqpins_cs c Hcs).
        exact (HR7thr c Hcs N2 N8 N9 N18 N19). }
    iAssert (bcache_scan bn V Mg ord devs bnos)
      with "[Hauth Hsauth Hlru Hpool Hslots]" as "Hscan".
    { rewrite /bcache_scan. iFrame "Hauth Hsauth".
      iSplitR; [iPureIntro; exact Hdom|].
      iSplitR; [iPureIntro; exact Hordp|].
      iSplitR; [iPureIntro; exact Hinj|].
        iSplitR; [iPureIntro; exact Hdevpin|].
        iFrame "Hlru Hpool Hslots". }
    assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.bread + 0x32) : mword 64) 2 = mword_of_int (KernelSyms.bread + 0x34))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp34) in "Hpc".
    (* +0x34 c.j +0x8 : into the loop's test *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.bread + 0x34))
              (sign_extend' 21 (concat_vec (mword_of_int 4 : mword 11) ('b"0")))
              W5 (trap_res eb + (K - 6))%nat false ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi34").
    iApply wp_next_off_intro.
    iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Htgt3c : add_vec (mword_of_int (KernelSyms.bread + 0x34) : mword 64)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 4 : mword 11) ('b"0"))))
                     = mword_of_int (KernelSyms.bread + 0x3c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt3c) in "Hpc".
    iApply (bread_floop (CID0 := CIDq)  γs j γl γu γd γk pd pav pu bn V Mg ord devs bnos
              pidv dev bno dq m K eb (length ord) lks
              HK Hbno Ha0 Ha1 Hj Hgl Hgd Hcov Hdv Hordp Hbelow [] ord W5
              ltac:(reflexivity) ltac:(reflexivity)
              (bd_ord_nonnil ord Hordp) (bd_done_nil _) HW5regs HW5s1 HW5a4
              with "Hcg Htext Hkd Hpc Hpenv Hbio Hframe Hcnt Hpay Hextc Hextm Htok Hscan Hbslot
                    Hprocs Hppid Hdev Hgeom Hdlock Hcont").
  Qed.

End ProofBread.

End BreadProof.
