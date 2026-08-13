(* ProofDirlookup.v -- the whole-function proof of dirlookup.

     struct inode*
     dirlookup(struct inode *dp, char *name, uint *poff)

   172 bytes.  The shape of the walk, off the decode in CodeDirlookup.v:

     +0x00 .. +0x14   the 12-slot frame and the nine saves, s0 = sp+96
     +0x16 .. +0x1c   dp->type vs T_DIR; the [bne] to panic is REFUTED by
                      the contract's [di_type dn = T_DIR] premise
     +0x20 .. +0x34   s2 := dp, s5 := name, s7 := poff, a5 := dp->size,
                      s1 := 0, s4 := &de, s3 := 16, s6 := &de.name, a0 := 0
     +0x36            [c.bnez a5]: size = 0 falls to +0x38
     +0x38            [c.j +0x96] -- the EMPTY-DIRECTORY arm
     +0x3a .. +0x4e   the two panic blocks (both dead: see below)
     +0x52 .. +0x58   THE LATCH: off += 16, re-read dp->size, [bgeu] out
     +0x5c .. +0x7c   THE BODY: readi, the [lhu] free test, namecmp
     +0x7e .. +0x92   THE FOUND ARM: the optional [*poff = off], iget
     +0x94            a0 := 0 -- the loop-exhausted arm
     +0x96 .. +0xaa   THE TAIL: nine restores, the pop, [c.ret]

   Both panics are dead and neither costs a resource: panic("dirlookup not
   DIR") at +0x1c is refuted from the type premise, and panic("dirlookup
   read") at +0x46 from [ProofDirlookupParts.dlk_rd_clamp_full] -- the
   contract's GRANULARITY premise [16 | size] makes every loop readi
   full-length, so readi's kernel arm returns exactly 16 and the [bne
   a0,s3] at +0x6a always falls through.

   ---- THE THREE PIECES THE PROOF IS BUILT FROM -------------------------

   [Htail] -- the shared epilogue at +0x96, proved ONCE as a persistent
   [wp_next]-wrapped assertion in the style of ProofIget's TAILC.  It takes
   the ten frame slots, the [de] buffer as raw bytes, and a CONTINUATION
   [∀ mf, callee_saved m mf -> mf!!!a0 = Mt!!!a0 -> ...]; each of the three
   arms that reach it (empty directory, found, exhausted) supplies its own
   continuation carrying its own linear resources.  Stating it that way is
   what keeps the arm payloads out of the tail.

   [Hloop] -- the scan, a FUEL INDUCTION wrapped in [wp_next] (ProofKexit's
   shape, not ProofIget's: dirlookup's body SLEEPS inside readi, so the
   hart moves at every call and the loop statement has to quantify its own
   [CpuId]).  The invariant at +0x5c is: [i < nrec], [dir_first data i s =
   None] (no match strictly below [i]), [dlk_regs m sp0 ip nb pf (16*i) Ml],
   and the eleven linear resources.  [dir_first_step_miss] advances it past
   a free record and past a name mismatch; [dir_first_step_hit] closes the
   found arm; [dir_first_None] closes the exhausted arm at [nrec].

   The nine AMBIENT resources dirlookup threads are all PERSISTENT and are
   introduced with [#] -- [kernel_text], [panic_wp_any], [bio_ctx],
   [kalloc_env], [procs_inv], [dev_inv], [disk_geom], the disk [is_lock],
   [is_itable2], [itable_inv], [ic_escrows].  That is forced by readi's own
   contract (which hands none of them back) and it is what keeps the loop's
   universal down to the genuinely linear ones. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import VcGen.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpSmodeHalf.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import ByteBuf.
Require Import FdSlots.
Require Import ProcGeom.
Require Import ProcInv.
Require Import WpUart.
Require Import DiskPtsto.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheEscrow.
Require Import KallocInv.
Require Import UserPtTree.
Require Import PanicStub.
Require Import ProcInv.
Require Import FileInvDefs.
Require Import DirView.
Require Import PanicStub.
Require Import SpecReadi SpecNamecmp SpecIget.
Require Import CodeDirlookup.
Require Import SpecDirlookup.
Require Import ProofDirlookupParts.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Set Printing Depth 40.

(* ===================================================================== *)
(*  6.  THE PROOF                                                         *)
(* ===================================================================== *)

Module DirlookupProof (RD : READI) (NC : NAMECMP) (IG : IGET) : DIRLOOKUP.

Notation DL := KernelSyms.dirlookup (only parsing).
Notation Rra := (mword_of_int 1 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Rs1 := (mword_of_int 9 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Ra2 := (mword_of_int 12 : mword 5).
Notation Ra3 := (mword_of_int 13 : mword 5).
Notation Ra4 := (mword_of_int 14 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Rs3 := (mword_of_int 19 : mword 5).
Notation Rs4 := (mword_of_int 20 : mword 5).
Notation Rs5 := (mword_of_int 21 : mword 5).
Notation Rs6 := (mword_of_int 22 : mword 5).
Notation Rs7 := (mword_of_int 23 : mword 5).

(* ===================================================================== *)
(*  The [c.bnez a5] at +0x36 and the [bgeu s1,a5] at +0x58 both test the  *)
(*  32-bit size word widened to 64 bits.  These three put that test on    *)
(*  the [Z] side, where [dir_nrec] lives.                                 *)
(* ===================================================================== *)

Lemma dlk_sz_eqz (sz : mword 32) :
  bv_unsigned sz = 0 ->
  neq_vec (sign_extend' 64 sz : mword 64) (zero_reg : mword 64) = false.
Proof.
  intro H.
  assert (Hz : sz = (bv_0 32 : mword 32))
    by (apply bv_eq; rewrite H; vm_compute; reflexivity).
  rewrite Hz. unfold neq_vec.
  rewrite (proj2 (eq_vec_true_iff _ _));
    [reflexivity | apply bv_eq; vm_compute; reflexivity].
Qed.

Lemma dlk_sz_nez (sz : mword 32) :
  bv_unsigned sz < 2 ^ 31 -> bv_unsigned sz <> 0 ->
  neq_vec (sign_extend' 64 sz : mword 64) (zero_reg : mword 64) = true.
Proof.
  intros Hlt Hne. apply dlk_neqz_true. rewrite (dlk_sext32_moi sz Hlt).
  intro Hc. apply Hne.
  assert (Hb : 0 <= bv_unsigned sz < 2 ^ 64).
  { pose proof (bv_unsigned_in_range _ sz) as [Hl Hh]. split; [exact Hl |].
    apply (Z.lt_trans _ (bv_modulus 32) _);
      [exact Hh | vm_compute; reflexivity]. }
  pose proof (dlk_uint_moi (bv_unsigned sz) Hb) as Hu.
  rewrite Hc in Hu.
  assert (H0 : uint (mword_of_int 0 : mword 64) = 0) by (vm_compute; reflexivity).
  rewrite H0 in Hu. symmetry. exact Hu.
Qed.

Lemma dlk_first_none_zero (data : nat -> list (bv 8)) (n : nat)
    (s : list (bv 8)) :
  n = 0%nat -> dir_first data n s = None.
Proof. intro H. subst n. unfold dir_first. apply dfirst_0. Qed.

Lemma dlk_nrec_zero (sz : Z) : sz = 0 -> dir_nrec sz = 0%nat.
Proof. intro H. subst sz. unfold dir_nrec. reflexivity. Qed.

Lemma dlk_nrec_pos (sz : Z) :
  0 <= sz -> (16 | sz) -> sz <> 0 -> (0 < dir_nrec sz)%nat.
Proof.
  intros Hnn Hd Hne. apply (dir_nrec_bound sz 0 Hnn Hd). simpl. lia.
Qed.

(* the zero displacement of [sw s1,0(s7)] and [lw a0,0(s2)] *)
Lemma dlk_add_vec_0 (x : mword 64) :
  add_vec x (sign_extend' 64 (mword_of_int 0 : mword 12)) = x.
Proof.
  unfold add_vec, word_binop, with_word', with_word, MachineWord.MachineWord.add.
  apply bv_add_0_r. vm_compute. reflexivity.
Qed.

Section ProofDirlookupMain.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.

  (* readi's sixteen delivered bytes, as the [lhu]'s halfword and namecmp's
     fourteen-byte name.  Stated as ONE equivalence so the walk never has to
     rewrite a partially-applied byte function. *)
  Lemma dlk_de_view (data : nat -> list (bv 8)) (i : nat) (a : Arch.pa) :
    is_aligned_paddr (Physaddr a) 2 = true ->
    ([∗ list] jj ∈ seq 0 16, pa_add a jj ↦ₘ file_byte data (16 * i + jj)%nat)
    ⊣⊢ a ↦₂ dir_inum data i
       ∗ ([∗ list] jj ∈ seq 0 14, pa_add (pa_add a 2) jj ↦ₘ dir_name data i jj).
  Proof.
    intro Hal.
    rewrite -(dlk_half_acc data i a Hal).
    rewrite -(dlk_name_acc data i (pa_add a 2)).
    exact (dlk_de_split a (fun jj => file_byte data (16 * i + jj)%nat)).
  Qed.

  (* the [V] slot of readi's contract is dead on the kernel arm *)
  Definition dlk_dummyV : pprivate :=
    MkPPriv (mword_of_int 0)
            (UPTD (mword_of_int 0) (mword_of_int 0) ∅ ∅)
            [] [] (mword_of_int 0) [].

  (* ---- THE BLOCK STATEMENTS, NAMED (claude-notes/optimization.md, RULE
     ONE) -- [Htail]/[Hloop]/[Hlatch] are each stated below as a
     [wp_next]-wrapped [iAssert] whose continuation body is tens of lines
     of ∀/wands; spelled out in place, EVERY proofmode step of the walk
     re-embeds that whole statement in the proof term (the cost is
     |Δ| times the number of steps).  Naming the inner body turns each
     into a constant applied to its arguments in the context.

     They are TRANSPARENT ON PURPOSE and only the part AFTER
     [fun CIDx : CpuId =>] is named: the [wp_next]/[□]/[∀ fuel] at each
     use site stay syntactically visible, which is what lets
     [iSpecialize]/[iApply] unify through them without an extra
     [iEval (rewrite /...)], and what lets [iInduction fuel] leave
     [dl_loop_body]'s own induction hypothesis folded. *)

  Definition dl_tail_body
      (m : regfile) (sp0 pj ret_tgt : mword 64) (K : nat) (b : bool)
      (CIDt : CpuId) : iProp Σ :=
    (∀ (Mt : regfile) (uu10 : mword 64) (dnew : nat -> bv 8),
       ⌜dlk_tregs m sp0 Mt⌝ -∗
       sie_cap_gpr Mt (K - 12)%nat b pj -∗
       pc_is (mword_of_int (DL + 0x96)) -∗
       (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
       (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
       (pa_stk sp0 3) ↦₈ (m !!! Regidx Rs1 : mword 64) -∗
       (pa_stk sp0 4) ↦₈ (m !!! Regidx Rs2 : mword 64) -∗
       (pa_stk sp0 5) ↦₈ (m !!! Regidx Rs3 : mword 64) -∗
       (pa_stk sp0 6) ↦₈ (m !!! Regidx Rs4 : mword 64) -∗
       (pa_stk sp0 7) ↦₈ (m !!! Regidx Rs5 : mword 64) -∗
       (pa_stk sp0 8) ↦₈ (m !!! Regidx Rs6 : mword 64) -∗
       (pa_stk sp0 9) ↦₈ (m !!! Regidx Rs7 : mword 64) -∗
       (pa_stk sp0 10) ↦₈ uu10 -∗
       ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 12) jj ↦ₘ dnew jj) -∗
       wp_next (CID0 := CIDt) true pj (fun CIDf : CpuId =>
         ∀ mf : regfile,
           ⌜callee_saved m mf⌝ -∗
           ⌜mf !!! Regidx Ra0 = (Mt !!! Regidx Ra0 : mword 64)⌝ -∗
           sie_cap_gpr mf K b pj -∗
           pc_is ret_tgt -∗
           WP (Loop : expr riscv_lang)) -∗
       WP (Loop : expr riscv_lang))%I.

  (* the FOUND/EXHAUSTED continuation both [dl_loop_body] and
     [dl_latch_body] hand [wp_next] at their tail: identical in both, and
     what "Hqc" is bound to for the whole span of either body's own proof
     (readi, namecmp, iget...), so it is worth folding on its own even
     though it is not itself an [iAssert] site. *)
  Definition dl_found_cont
      (nrec : nat) (dn : dinode) (data : nat -> list (bv 8)) (s : list (bv 8))
      (m : regfile) (ip nb pf pj ret_tgt : mword 64) (K : nat)
      (b eb hasp : bool) (C : iProp Σ) (dq dqd dqn : dfrac)
      (dev pofv pidv : mword 32) (fn : nat -> bv 8) (bn : bio_names)
      (gfs : fs_names) (bm : blkmap) (CIDc : CpuId) : iProp Σ :=
    (∀ (mf : regfile) (found : bool) (kk : nat) (kslot : nat) (q : Qp),
       ⌜callee_saved m mf⌝ -∗
       sie_cap_gpr mf K b pj -∗
       cpu_own 0 eb pj C b -∗
       pc_is ret_tgt -∗
       i_dev ip ↦₄{dqd} dev -∗
       inode_meta ip dn -∗
       inode_map gfs ip bm -∗
       inode_blocks gfs bm data -∗
       ([∗ list] ii ∈ seq 0 14, pa_add nb ii ↦ₘ{dqn} fn ii) -∗
       p_pid pj ↦₄{dq} pidv -∗
       bslot bn -∗
       (if found
        then ⌜dir_first data nrec s = Some kk
              /\ (kslot < NINODE)%nat
              /\ mf !!! Regidx Ra0 = ientry kslot⌝ ∗
             inode_ref kslot q dev
               (zero_extend' 32 (dir_inum data kk : mword 16) : mword 32) ∗
             (if hasp
              then pf ↦₄ (mword_of_int (Z.of_nat (16 * kk)) : mword 32)
              else emp)
        else ⌜dir_first data nrec s = None
              /\ mf !!! Regidx Ra0 = (mword_of_int 0 : mword 64)⌝ ∗
             iref_slot ∗
             (if hasp then pf ↦₄ pofv else emp)) -∗
       WP (Loop : expr riscv_lang))%I.

  Definition dl_loop_body
      (nrec : nat) (dn : dinode) (data : nat -> list (bv 8)) (s : list (bv 8))
      (m : regfile) (sp0 ip nb pf pj ret_tgt : mword 64) (K : nat)
      (b eb hasp : bool) (C : iProp Σ) (dq dqd dqn : dfrac)
      (dev pofv pidv : mword 32) (fn : nat -> bv 8) (bn : bio_names)
      (gfs : fs_names) (bm : blkmap) (fuel : nat) (CIDl : CpuId) : iProp Σ :=
    (∀ (i : nat) (Ml : regfile) (dol : nat -> bv 8) (mt10 : mword 64),
       ⌜(S nrec - i <= fuel)%nat⌝ -∗
       ⌜Z.of_nat i * 16 < bv_unsigned (di_size dn)⌝ -∗
       ⌜dir_first data i s = None⌝ -∗
       ⌜dlk_regs m sp0 ip nb pf (16 * i) Ml⌝ -∗
       sie_cap_gpr Ml (K - 12)%nat b pj -∗
       cpu_own 0 eb pj C b -∗
       pc_is (mword_of_int (DL + 0x5c)) -∗
       (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
       (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
       (pa_stk sp0 3) ↦₈ (m !!! Regidx Rs1 : mword 64) -∗
       (pa_stk sp0 4) ↦₈ (m !!! Regidx Rs2 : mword 64) -∗
       (pa_stk sp0 5) ↦₈ (m !!! Regidx Rs3 : mword 64) -∗
       (pa_stk sp0 6) ↦₈ (m !!! Regidx Rs4 : mword 64) -∗
       (pa_stk sp0 7) ↦₈ (m !!! Regidx Rs5 : mword 64) -∗
       (pa_stk sp0 8) ↦₈ (m !!! Regidx Rs6 : mword 64) -∗
       (pa_stk sp0 9) ↦₈ (m !!! Regidx Rs7 : mword 64) -∗
       (pa_stk sp0 10) ↦₈ mt10 -∗
       ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 12) jj ↦ₘ dol jj) -∗
       i_dev ip ↦₄{dqd} dev -∗
       inode_meta ip dn -∗
       inode_map gfs ip bm -∗
       inode_blocks gfs bm data -∗
       ([∗ list] ii ∈ seq 0 14, pa_add nb ii ↦ₘ{dqn} fn ii) -∗
       (if hasp then pf ↦₄ pofv else emp) -∗
       p_pid pj ↦₄{dq} pidv -∗
       bslot bn -∗
       iref_slot -∗
       wp_next (CID0 := CID) true pj (fun (CIDc : CpuId) =>
         dl_found_cont nrec dn data s m ip nb pf pj ret_tgt K b eb hasp C
           dq dqd dqn dev pofv pidv fn bn gfs bm CIDc) -∗
       WP (Loop : expr riscv_lang))%I.

  Definition dl_latch_body
      (nrec : nat) (dn : dinode) (data : nat -> list (bv 8)) (s : list (bv 8))
      (m : regfile) (sp0 ip nb pf pj ret_tgt : mword 64) (K : nat)
      (b eb hasp : bool) (C : iProp Σ) (dq dqd dqn : dfrac)
      (dev pofv pidv : mword 32) (fn : nat -> bv 8) (bn : bio_names)
      (gfs : fs_names) (bm : blkmap) (i : nat) (CIDp : CpuId) : iProp Σ :=
    (∀ (Mp : regfile) (dol' : nat -> bv 8) (mt10' : mword 64),
       ⌜dlk_regs m sp0 ip nb pf (16 * i) Mp⌝ -∗
       ⌜dir_first data (S i) s = None⌝ -∗
       sie_cap_gpr Mp (K - 12)%nat b pj -∗
       cpu_own 0 eb pj C b -∗
       pc_is (mword_of_int (DL + 0x52)) -∗
       (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
       (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
       (pa_stk sp0 3) ↦₈ (m !!! Regidx Rs1 : mword 64) -∗
       (pa_stk sp0 4) ↦₈ (m !!! Regidx Rs2 : mword 64) -∗
       (pa_stk sp0 5) ↦₈ (m !!! Regidx Rs3 : mword 64) -∗
       (pa_stk sp0 6) ↦₈ (m !!! Regidx Rs4 : mword 64) -∗
       (pa_stk sp0 7) ↦₈ (m !!! Regidx Rs5 : mword 64) -∗
       (pa_stk sp0 8) ↦₈ (m !!! Regidx Rs6 : mword 64) -∗
       (pa_stk sp0 9) ↦₈ (m !!! Regidx Rs7 : mword 64) -∗
       (pa_stk sp0 10) ↦₈ mt10' -∗
       ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 12) jj ↦ₘ dol' jj) -∗
       i_dev ip ↦₄{dqd} dev -∗
       inode_meta ip dn -∗
       inode_map gfs ip bm -∗
       inode_blocks gfs bm data -∗
       ([∗ list] ii ∈ seq 0 14, pa_add nb ii ↦ₘ{dqn} fn ii) -∗
       (if hasp then pf ↦₄ pofv else emp) -∗
       p_pid pj ↦₄{dq} pidv -∗
       bslot bn -∗
       iref_slot -∗
       wp_next (CID0 := CID) true pj (fun (CIDc : CpuId) =>
         dl_found_cont nrec dn data s m ip nb pf pj ret_tgt K b eb hasp C
           dq dqd dqn dev pofv pidv fn bn gfs bm CIDc) -∗
       WP (Loop : expr riscv_lang))%I.

  Lemma wp_dirlookup_sconf
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (ga : gname) (gf : gname)
      (cov : gset Z) (logstart : Z) (nib : nat) (dev : mword 32)
      (ip : mword 64)
      (bm : blkmap) (data : nat -> list (bv 8))
      (dn : dinode)
      (fn : nat -> bv 8)
      (hasp : bool) (pofv : mword 32)
      (pidv : mword 32) (dq dqd dqn : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool)
    : wp_dirlookup_sconf_body gs j gl gu gd gk pd pav pu bn gfs gi cn gtl
                              ga gf cov logstart nib dev ip bm data dn
                              fn hasp pofv pidv dq dqd dqn m K eb C b.
  Proof.
    cbv beta delta [wp_dirlookup_sconf_body].
    intros pcE pj nb pf ret_tgt nrec s HK Htype Hlg Hbmwf Hbmcov Hszb
           Hinums Hj Hgs Ha0 Hposs Heb.
    pose proof HK as HK'. unfold K_dirlookup in HK'.
    (* readi's contract has its OWN [let pj := proc_addr j], so everything it
       hands back is phrased at [proc_addr j] while ours is phrased at the
       [let]-bound [pj].  The two are convertible but [iSpecialize] matches
       syntactically, so fold them back at the seam. *)
    assert (Hpjd : proc_addr j = pj) by reflexivity.
    iIntros "Hcg Hcnt #Htext Hpc #Hpanic #Hbio #Hkenv Hidev Hmeta Hmap Hblocks
              Hnm Hpoff Hppid #Hprocs #Hdev #Hgeom #Hdlk Hbslot #Hitb2 #Hitbl
              #Hesc Hislot Hcont".
    (* PIN THE INDEX.  This contract still carries [eb = true ->], and at
       level 0 [cpu_own_eb_agree] gives [eb = b], so [b] IS the literal
       [true] here.  Making that explicit is what keeps every hart-chain in
       the body at ONE index: the crossings below are the literal [true]
       (dirlookup parks, through readi down to sleep), and a [b]-indexed
       [cpu_own_transport] cannot be discharged from a [true]-indexed
       guard -- [b = false] tells you nothing about the hart.  When this
       function is itself generalized, this derivation is what goes. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    assert (Hb : b = true) by (rewrite -Hbm; exact Heb).
    clear Hbm.
    iDestruct "Hmeta" as "(Hity & Himaj & Himin & Hinl & Hisz)".
    iEval (rewrite /i_type) in "Hity".
    iEval (rewrite /i_size) in "Hisz".
    iPoseProof (dli_00 with "Htext") as "Hi00".
    iPoseProof (dli_02 with "Htext") as "Hi02".
    iPoseProof (dli_04 with "Htext") as "Hi04".
    iPoseProof (dli_06 with "Htext") as "Hi06".
    iPoseProof (dli_08 with "Htext") as "Hi08".
    iPoseProof (dli_0a with "Htext") as "Hi0a".
    iPoseProof (dli_0c with "Htext") as "Hi0c".
    iPoseProof (dli_0e with "Htext") as "Hi0e".
    iPoseProof (dli_10 with "Htext") as "Hi10".
    iPoseProof (dli_12 with "Htext") as "Hi12".
    iPoseProof (dli_14 with "Htext") as "Hi14".
    iPoseProof (dli_16 with "Htext") as "Hi16".
    iPoseProof (dli_1a with "Htext") as "Hi1a".
    iPoseProof (dli_1c with "Htext") as "Hi1c".
    (* ===== +0x00 c.addi16sp sp,-96 : the 12-slot frame ===== *)
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 12) by apply dlk_push.
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 58 : mword 6) m K 12 b
              ltac:(lia) Hpush with "Hcg Hpc Hi00").
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6))))]> m).
    assert (HR1sp : R1 !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /R1 upd_eq; exact Hpush).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as
      "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & _)".
    iDestruct "S1" as (u1) "Hb1". iDestruct "S2" as (u2) "Hb2".
    iDestruct "S3" as (u3) "Hb3". iDestruct "S4" as (u4) "Hb4".
    iDestruct "S5" as (u5) "Hb5". iDestruct "S6" as (u6) "Hb6".
    iDestruct "S7" as (u7) "Hb7". iDestruct "S8" as (u8) "Hb8".
    iDestruct "S9" as (u9) "Hb9". iDestruct "S10" as (u10) "Hb10".
    iDestruct "S11" as (u11) "Hb11". iDestruct "S12" as (u12) "Hb12".
    assert (Hf1 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HR1sp; apply dlk_frm1).
    assert (Hf2 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HR1sp; apply dlk_frm2).
    assert (Hf3 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HR1sp; apply dlk_frm3).
    assert (Hf4 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (rewrite HR1sp; apply dlk_frm4).
    assert (Hf5 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (rewrite HR1sp; apply dlk_frm5).
    assert (Hf6 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk sp0 6) by (rewrite HR1sp; apply dlk_frm6).
    assert (Hf7 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 7) by (rewrite HR1sp; apply dlk_frm7).
    assert (Hf8 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 8) by (rewrite HR1sp; apply dlk_frm8).
    assert (Hf9 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 9) by (rewrite HR1sp; apply dlk_frm9).
    iEval (rewrite -Hf1) in "Hb1". iEval (rewrite -Hf2) in "Hb2".
    iEval (rewrite -Hf3) in "Hb3". iEval (rewrite -Hf4) in "Hb4".
    iEval (rewrite -Hf5) in "Hb5". iEval (rewrite -Hf6) in "Hb6".
    iEval (rewrite -Hf7) in "Hb7". iEval (rewrite -Hf8) in "Hb8".
    iEval (rewrite -Hf9) in "Hb9".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (DL + 0x02)) by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    assert (HR1o : forall c : mword 5, c <> csp_rs1 ->
                     R1 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hc. rewrite /R1 upd_ne;
        [reflexivity
        | intro Hq; apply Hc;
          first [ exact (regidx_inj _ _ Hq) | symmetry; exact (regidx_inj _ _ Hq) ]]. }
    (* ===== +0x02 .. +0x12 : the nine saves ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (DL + 0x02)) (mword_of_int 11 : mword 6)
              Rra R1 (K - 12)%nat u1 b with "Hcg Hpc Hi02 Hb1").
    iIntros (CID2 Hq2) "Hcg Hpc Hb1".
    iEval (rgne; rewrite (HR1o Rra ltac:(nz)) Hf1) in "Hb1".
    assert (Hpp04 : add_vec_int (mword_of_int (DL + 0x02) : mword 64) 2
                    = mword_of_int (DL + 0x04)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (DL + 0x04)) (mword_of_int 10 : mword 6)
              Rs0 R1 (K - 12)%nat u2 b with "Hcg Hpc Hi04 Hb2").
    iIntros (CID3 Hq3) "Hcg Hpc Hb2".
    iEval (rgne; rewrite (HR1o Rs0 ltac:(nz)) Hf2) in "Hb2".
    assert (Hpp06 : add_vec_int (mword_of_int (DL + 0x04) : mword 64) 2
                    = mword_of_int (DL + 0x06)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (DL + 0x06)) (mword_of_int 9 : mword 6)
              Rs1 R1 (K - 12)%nat u3 b with "Hcg Hpc Hi06 Hb3").
    iIntros (CID4 Hq4) "Hcg Hpc Hb3".
    iEval (rgne; rewrite (HR1o Rs1 ltac:(nz)) Hf3) in "Hb3".
    assert (Hpp08 : add_vec_int (mword_of_int (DL + 0x06) : mword 64) 2
                    = mword_of_int (DL + 0x08)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (DL + 0x08)) (mword_of_int 8 : mword 6)
              Rs2 R1 (K - 12)%nat u4 b with "Hcg Hpc Hi08 Hb4").
    iIntros (CID5 Hq5) "Hcg Hpc Hb4".
    iEval (rgne; rewrite (HR1o Rs2 ltac:(nz)) Hf4) in "Hb4".
    assert (Hpp0a : add_vec_int (mword_of_int (DL + 0x08) : mword 64) 2
                    = mword_of_int (DL + 0x0a)) by pcw.
    iEval (rewrite Hpp0a) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (DL + 0x0a)) (mword_of_int 7 : mword 6)
              Rs3 R1 (K - 12)%nat u5 b with "Hcg Hpc Hi0a Hb5").
    iIntros (CID6 Hq6) "Hcg Hpc Hb5".
    iEval (rgne; rewrite (HR1o Rs3 ltac:(nz)) Hf5) in "Hb5".
    assert (Hpp0c : add_vec_int (mword_of_int (DL + 0x0a) : mword 64) 2
                    = mword_of_int (DL + 0x0c)) by pcw.
    iEval (rewrite Hpp0c) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (DL + 0x0c)) (mword_of_int 6 : mword 6)
              Rs4 R1 (K - 12)%nat u6 b with "Hcg Hpc Hi0c Hb6").
    iIntros (CID7 Hq7) "Hcg Hpc Hb6".
    iEval (rgne; rewrite (HR1o Rs4 ltac:(nz)) Hf6) in "Hb6".
    assert (Hpp0e : add_vec_int (mword_of_int (DL + 0x0c) : mword 64) 2
                    = mword_of_int (DL + 0x0e)) by pcw.
    iEval (rewrite Hpp0e) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (DL + 0x0e)) (mword_of_int 5 : mword 6)
              Rs5 R1 (K - 12)%nat u7 b with "Hcg Hpc Hi0e Hb7").
    iIntros (CID8 Hq8) "Hcg Hpc Hb7".
    iEval (rgne; rewrite (HR1o Rs5 ltac:(nz)) Hf7) in "Hb7".
    assert (Hpp10 : add_vec_int (mword_of_int (DL + 0x0e) : mword 64) 2
                    = mword_of_int (DL + 0x10)) by pcw.
    iEval (rewrite Hpp10) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (DL + 0x10)) (mword_of_int 4 : mword 6)
              Rs6 R1 (K - 12)%nat u8 b with "Hcg Hpc Hi10 Hb8").
    iIntros (CID9 Hq9) "Hcg Hpc Hb8".
    iEval (rgne; rewrite (HR1o Rs6 ltac:(nz)) Hf8) in "Hb8".
    assert (Hpp12 : add_vec_int (mword_of_int (DL + 0x10) : mword 64) 2
                    = mword_of_int (DL + 0x12)) by pcw.
    iEval (rewrite Hpp12) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (DL + 0x12)) (mword_of_int 3 : mword 6)
              Rs7 R1 (K - 12)%nat u9 b with "Hcg Hpc Hi12 Hb9").
    iIntros (CID10 Hq10) "Hcg Hpc Hb9".
    iEval (rgne; rewrite (HR1o Rs7 ltac:(nz)) Hf9) in "Hb9".
    assert (Hpp14 : add_vec_int (mword_of_int (DL + 0x12) : mword 64) 2
                    = mword_of_int (DL + 0x14)) by pcw.
    iEval (rewrite Hpp14) in "Hpc".
    (* ===== +0x14 c.addi4spn s0,sp,96 ===== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (DL + 0x14))
              (Cregidx (mword_of_int 0)) (mword_of_int 24 : mword 8) Rs0
              R1 (K - 12)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi14").
    iIntros (CID11 Hq11) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8))))]> R1).
    assert (HR2s0 : R2 !!! Regidx Rs0 = sp0).
    { rewrite /R2 upd_eq. rewrite HR1sp. apply dlk_fp. }
    assert (HR2a0 : R2 !!! Regidx Ra0 = ip).
    { rewrite /R2 upd_ne; [| nz]. rewrite (HR1o Ra0 ltac:(nz)). exact Ha0. }
    assert (Hpp16 : add_vec_int (mword_of_int (DL + 0x14) : mword 64) 2
                    = mword_of_int (DL + 0x16)) by pcw.
    iEval (rewrite Hpp16) in "Hpc".
    (* ===== +0x16 lh a4,68(a0) : ip->type ===== *)
    iApply (wp_lh_s_sconf (mword_of_int (DL + 0x16)) Ra4 Ra0
              (mword_of_int 68 : mword 12) R2 (K - 12)%nat (di_type dn : mword 16) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi16 [Hity]").
    { iEval (rgne; rewrite HR2a0). iExact "Hity". }
    iIntros (CID12 Hq12) "Hcg Hpc Hity".
    iEval (rgne; rewrite HR2a0) in "Hity".
    set (R3 := <[Regidx Ra4 := regval_into_reg
                  (sign_extend' 64 (di_type dn : mword 16) : mword 64)]> R2).
    assert (HR3a4 : R3 !!! Regidx Ra4
                    = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
      by (rewrite /R3; apply upd_eq).
    assert (Hpp1a : add_vec_int (mword_of_int (DL + 0x16) : mword 64) 4
                    = mword_of_int (DL + 0x1a)) by pcw.
    iEval (rewrite Hpp1a) in "Hpc".
    (* ===== +0x1a c.li a5,1 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (DL + 0x1a)) Ra5 (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 64) R3 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi1a").
    iIntros (CID13 Hq13) "Hcg Hpc".
    set (R4 := <[Regidx Ra5 := regval_into_reg (mword_of_int 1 : mword 64)]> R3).
    assert (HR4a5 : R4 !!! Regidx Ra5 = (mword_of_int 1 : mword 64))
      by (rewrite /R4; apply upd_eq).
    assert (HR4a4 : R4 !!! Regidx Ra4 = (mword_of_int 1 : mword 64)).
    { rewrite /R4 upd_ne; [| nz]. rewrite HR3a4 Htype. unfold T_DIR. pcw. }
    assert (Hpp1c : add_vec_int (mword_of_int (DL + 0x1a) : mword 64) 2
                    = mword_of_int (DL + 0x1c)) by pcw.
    iEval (rewrite Hpp1c) in "Hpc".
    (* ===== +0x1c bne a4,a5 : the panic is refuted by the premise ===== *)
    iApply (wp_bne_fall_s_sconf (mword_of_int (DL + 0x1c))
              (mword_of_int 30 : mword 13) Ra5 Ra4 R4 (K - 12)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HR4a4 HR4a5; apply dlk_neq_refl)
              with "Hcg Hpc Hi1c").
    iIntros (CID14 Hq14) "Hcg Hpc".
    assert (Hpp20 : add_vec_int (mword_of_int (DL + 0x1c) : mword 64) 4
                    = mword_of_int (DL + 0x20)) by pcw.
    iEval (rewrite Hpp20) in "Hpc".
    iPoseProof (dli_20 with "Htext") as "Hi20".
    iPoseProof (dli_22 with "Htext") as "Hi22".
    iPoseProof (dli_24 with "Htext") as "Hi24".
    iPoseProof (dli_26 with "Htext") as "Hi26".
    iPoseProof (dli_28 with "Htext") as "Hi28".
    iPoseProof (dli_2a with "Htext") as "Hi2a".
    iPoseProof (dli_2e with "Htext") as "Hi2e".
    iPoseProof (dli_30 with "Htext") as "Hi30".
    iPoseProof (dli_34 with "Htext") as "Hi34".
    iPoseProof (dli_36 with "Htext") as "Hi36".
    assert (HR4a0 : R4 !!! Regidx Ra0 = ip).
    { rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz]. exact HR2a0. }
    assert (HR4a1 : R4 !!! Regidx Ra1 = nb).
    { rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz].
      rewrite /R2 upd_ne; [| nz]. exact (HR1o Ra1 ltac:(nz)). }
    assert (HR4a2 : R4 !!! Regidx Ra2 = pf).
    { rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz].
      rewrite /R2 upd_ne; [| nz]. exact (HR1o Ra2 ltac:(nz)). }
    assert (HR4s0 : R4 !!! Regidx Rs0 = sp0).
    { rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz]. exact HR2s0. }
    assert (HR4sp : R4 !!! Regidx csp_rs1 = pa_stk sp0 12).
    { rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz].
      rewrite /R2 upd_ne; [| nz]. exact HR1sp. }
    assert (Hcsa4 : is_cs_idx Ra4 = false) by (vm_compute; reflexivity).
    assert (Hcsa5 : is_cs_idx Ra5 = false) by (vm_compute; reflexivity).
    assert (HR4o : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                     c <> Rs0 -> R4 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hc N2 N8. rewrite /R4 upd_ne; [| dlk_rne2 Hcsa5 Hc].
      rewrite /R3 upd_ne; [| dlk_rne2 Hcsa4 Hc].
      rewrite /R2 upd_ne;
        [ exact (HR1o c N2)
        | intro Hq; apply N8;
          first [ exact (regidx_inj _ _ Hq) | symmetry; exact (regidx_inj _ _ Hq) ]]. }
    (* ===== +0x20 c.mv s2,a0 : s2 := dp ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (DL + 0x20)) Rs2 Ra0 R4 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi20").
    iIntros (CID15 Hq15) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R5 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R4 !!! Regidx Ra0))]> R4).
    assert (HR5s2 : R5 !!! Regidx Rs2 = ip).
    { rewrite /R5 upd_eq. rewrite HR4a0. apply add_vec_zero_l. }
    assert (Hpp22 : add_vec_int (mword_of_int (DL + 0x20) : mword 64) 2
                    = mword_of_int (DL + 0x22)) by pcw.
    iEval (rewrite Hpp22) in "Hpc".
    (* ===== +0x22 c.mv s5,a1 : s5 := name ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (DL + 0x22)) Rs5 Ra1 R5 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi22").
    iIntros (CID16 Hq16) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R6 := <[Regidx Rs5 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R5 !!! Regidx Ra1))]> R5).
    assert (HR5a1 : R5 !!! Regidx Ra1 = nb)
      by (rewrite /R5 upd_ne; [exact HR4a1 | nz]).
    assert (HR6s5 : R6 !!! Regidx Rs5 = nb).
    { rewrite /R6 upd_eq. rewrite HR5a1. apply add_vec_zero_l. }
    assert (Hpp24 : add_vec_int (mword_of_int (DL + 0x22) : mword 64) 2
                    = mword_of_int (DL + 0x24)) by pcw.
    iEval (rewrite Hpp24) in "Hpc".
    (* ===== +0x24 c.mv s7,a2 : s7 := poff ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (DL + 0x24)) Rs7 Ra2 R6 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi24").
    iIntros (CID17 Hq17) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R7 := <[Regidx Rs7 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R6 !!! Regidx Ra2))]> R6).
    assert (HR6a2 : R6 !!! Regidx Ra2 = pf).
    { rewrite /R6 upd_ne; [| nz]. rewrite /R5 upd_ne; [exact HR4a2 | nz]. }
    assert (HR7s7 : R7 !!! Regidx Rs7 = pf).
    { rewrite /R7 upd_eq. rewrite HR6a2. apply add_vec_zero_l. }
    assert (HR7a0 : R7 !!! Regidx Ra0 = ip).
    { rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
      rewrite /R5 upd_ne; [exact HR4a0 | nz]. }
    assert (Hpp26 : add_vec_int (mword_of_int (DL + 0x24) : mword 64) 2
                    = mword_of_int (DL + 0x26)) by pcw.
    iEval (rewrite Hpp26) in "Hpc".
    (* ===== +0x26 c.lw a5,76(a0) : dp->size ===== *)
    iApply (wp_clw_s_sconf (mword_of_int (DL + 0x26)) Ra5 Ra0
              (mword_of_int 76 : mword 12) R7 (K - 12)%nat (di_size dn : mword 32) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi26 [Hisz]").
    { iEval (rgne; rewrite HR7a0). iExact "Hisz". }
    iIntros (CID18 Hq18) "Hcg Hpc Hisz".
    iEval (rgne; rewrite HR7a0) in "Hisz".
    (* the metadata bundle goes back together: readi takes it whole, and the
       loop's [lw a5,76(s2)] re-opens it once per iteration *)
    iAssert (inode_meta ip dn) with "[Hity Himaj Himin Hinl Hisz]" as "Hmeta".
    { rewrite /inode_meta /i_type /i_size. iFrame. }
    set (R8 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (di_size dn : mword 32) : mword 64)]> R7).
    assert (HR8a5 : R8 !!! Regidx Ra5
                    = (sign_extend' 64 (di_size dn : mword 32) : mword 64))
      by (rewrite /R8; apply upd_eq).
    assert (Hpp28 : add_vec_int (mword_of_int (DL + 0x26) : mword 64) 2
                    = mword_of_int (DL + 0x28)) by pcw.
    iEval (rewrite Hpp28) in "Hpc".
    (* ===== +0x28 c.li s1,0 : off := 0 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (DL + 0x28)) Rs1 (mword_of_int 0 : mword 6)
              (mword_of_int (Z.of_nat 0) : mword 64) R8 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi28").
    iIntros (CID19 Hq19) "Hcg Hpc".
    set (R9 := <[Regidx Rs1 := regval_into_reg
                  (mword_of_int (Z.of_nat 0) : mword 64)]> R8).
    assert (HR9s0 : R9 !!! Regidx Rs0 = sp0).
    { rewrite /R9 upd_ne; [| nz]. rewrite /R8 upd_ne; [| nz].
      rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
      rewrite /R5 upd_ne; [exact HR4s0 | nz]. }
    assert (Hpp2a : add_vec_int (mword_of_int (DL + 0x28) : mword 64) 2
                    = mword_of_int (DL + 0x2a)) by pcw.
    iEval (rewrite Hpp2a) in "Hpc".
    (* ===== +0x2a addi s4,s0,-96 : s4 := &de ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (DL + 0x2a)) Rs4 Rs0
              (mword_of_int 4000 : mword 12) R9 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2a").
    iIntros (CID20 Hq20) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R10 := <[Regidx Rs4 := regval_into_reg
                   (add_vec (R9 !!! Regidx Rs0)
                      (sign_extend' 64 (mword_of_int 4000 : mword 12)))]> R9).
    assert (HR10s4 : R10 !!! Regidx Rs4 = pa_stk sp0 12).
    { rewrite /R10 upd_eq. rewrite HR9s0. apply dlk_de_addr. }
    assert (Hpp2e : add_vec_int (mword_of_int (DL + 0x2a) : mword 64) 4
                    = mword_of_int (DL + 0x2e)) by pcw.
    iEval (rewrite Hpp2e) in "Hpc".
    (* ===== +0x2e c.li s3,16 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (DL + 0x2e)) Rs3 (mword_of_int 16 : mword 6)
              (mword_of_int 16 : mword 64) R10 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi2e").
    iIntros (CID21 Hq21) "Hcg Hpc".
    set (R11 := <[Regidx Rs3 := regval_into_reg (mword_of_int 16 : mword 64)]> R10).
    assert (HR11s0 : R11 !!! Regidx Rs0 = sp0).
    { rewrite /R11 upd_ne; [| nz]. rewrite /R10 upd_ne; [exact HR9s0 | nz]. }
    assert (Hpp30 : add_vec_int (mword_of_int (DL + 0x2e) : mword 64) 2
                    = mword_of_int (DL + 0x30)) by pcw.
    iEval (rewrite Hpp30) in "Hpc".
    (* ===== +0x30 addi s6,s0,-94 : s6 := &de.name ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (DL + 0x30)) Rs6 Rs0
              (mword_of_int 4002 : mword 12) R11 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi30").
    iIntros (CID22 Hq22) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R12 := <[Regidx Rs6 := regval_into_reg
                   (add_vec (R11 !!! Regidx Rs0)
                      (sign_extend' 64 (mword_of_int 4002 : mword 12)))]> R11).
    assert (HR12s6 : R12 !!! Regidx Rs6 = pa_add (pa_stk sp0 12) 2).
    { rewrite /R12 upd_eq. rewrite HR11s0. apply dlk_dename_addr. }
    assert (Hpp34 : add_vec_int (mword_of_int (DL + 0x30) : mword 64) 4
                    = mword_of_int (DL + 0x34)) by pcw.
    iEval (rewrite Hpp34) in "Hpc".
    (* ===== +0x34 c.li a0,0 : the "not found" return value ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (DL + 0x34)) Ra0 (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) R12 (K - 12)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi34").
    iIntros (CID23 Hq23) "Hcg Hpc".
    set (R13 := <[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> R12).
    assert (Hpp36 : add_vec_int (mword_of_int (DL + 0x34) : mword 64) 2
                    = mword_of_int (DL + 0x36)) by pcw.
    iEval (rewrite Hpp36) in "Hpc".
    (* ---- the register bundle the loop and the tail run on ---- *)
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (HR13 : dlk_regs m sp0 ip nb pf 0 R13).
    { unfold dlk_regs. split_and!.
      - rewrite /R13 upd_ne; [| nz]. rewrite /R12 upd_ne; [| nz].
        rewrite /R11 upd_ne; [| nz]. rewrite /R10 upd_ne; [| nz].
        rewrite /R9 upd_ne; [| nz]. rewrite /R8 upd_ne; [| nz].
        rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
        rewrite /R5 upd_ne; [exact HR4sp | nz].
      - rewrite /R13 upd_ne; [| nz]. rewrite /R12 upd_ne; [| nz].
        exact HR11s0.
      - rewrite /R13 upd_ne; [| nz]. rewrite /R12 upd_ne; [| nz].
        rewrite /R11 upd_ne; [| nz]. rewrite /R10 upd_ne; [| nz].
        rewrite /R9 upd_eq. reflexivity.
      - rewrite /R13 upd_ne; [| nz]. rewrite /R12 upd_ne; [| nz].
        rewrite /R11 upd_ne; [| nz]. rewrite /R10 upd_ne; [| nz].
        rewrite /R9 upd_ne; [| nz]. rewrite /R8 upd_ne; [| nz].
        rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
        exact HR5s2.
      - rewrite /R13 upd_ne; [| nz]. rewrite /R12 upd_ne; [| nz].
        rewrite /R11 upd_eq. reflexivity.
      - rewrite /R13 upd_ne; [| nz]. rewrite /R12 upd_ne; [| nz].
        rewrite /R11 upd_ne; [| nz]. exact HR10s4.
      - rewrite /R13 upd_ne; [| nz]. rewrite /R12 upd_ne; [| nz].
        rewrite /R11 upd_ne; [| nz]. rewrite /R10 upd_ne; [| nz].
        rewrite /R9 upd_ne; [| nz]. rewrite /R8 upd_ne; [| nz].
        rewrite /R7 upd_ne; [| nz]. exact HR6s5.
      - rewrite /R13 upd_ne; [| nz]. exact HR12s6.
      - rewrite /R13 upd_ne; [| nz]. rewrite /R12 upd_ne; [| nz].
        rewrite /R11 upd_ne; [| nz]. rewrite /R10 upd_ne; [| nz].
        rewrite /R9 upd_ne; [| nz]. rewrite /R8 upd_ne; [| nz].
        exact HR7s7.
      - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23.
        rewrite /R13 upd_ne; [| dlk_rne2 Hcsa0 Hc].
        rewrite /R12 upd_ne; [| dlk_xne N22].
        rewrite /R11 upd_ne; [| dlk_xne N19].
        rewrite /R10 upd_ne; [| dlk_xne N20].
        rewrite /R9 upd_ne; [| dlk_xne N9].
        rewrite /R8 upd_ne; [| dlk_rne2 Hcsa5 Hc].
        rewrite /R7 upd_ne; [| dlk_xne N23].
        rewrite /R6 upd_ne; [| dlk_xne N21].
        rewrite /R5 upd_ne; [| dlk_xne N18].
        exact (HR4o c Hc N2 N8). }
    (* ---- the [de] scratch record: two frame slots as sixteen bytes ---- *)
    iDestruct (dlk_slots_bytes sp0 u12 u11 with "Hb12 Hb11") as "[%Hal Hdeb]".
    destruct Hal as [Hal12 Hal11].
    iDestruct (dlk_bytes_name with "Hdeb") as (dolds0) "Hde".
    (* ================================================================= *)
    (*  THE SHARED TAIL at +0x96 -- nine restores, the pop, [c.ret].      *)
    (*                                                                    *)
    (*  Three arms reach it (empty directory, found, exhausted) and they  *)
    (*  hold different resources, so the tail takes a CONTINUATION rather *)
    (*  than the contract's own [Hcont]: it is a statement about the      *)
    (*  frame and the registers only.  [a0] rides through untouched,      *)
    (*  which is what lets each arm keep its own [a0] claim.              *)
    (* ================================================================= *)
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    iAssert (□ wp_next (CID0 := CID) true pj (fun CIDt : CpuId =>
               dl_tail_body m sp0 pj ret_tgt K b CIDt))%I with "[]" as "#Htail".
    { iModIntro.
      iIntros (CIDt Hst Mt uu10 dnew) "%HTr Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7
                                      Hb8 Hb9 Hb10 Hde Hqc".
      destruct HTr as [HTsp HTthr].
      iPoseProof (dli_96 with "Htext") as "Hi96".
      iPoseProof (dli_98 with "Htext") as "Hi98".
      iPoseProof (dli_9a with "Htext") as "Hi9a".
      iPoseProof (dli_9c with "Htext") as "Hi9c".
      iPoseProof (dli_9e with "Htext") as "Hi9e".
      iPoseProof (dli_a0 with "Htext") as "Hia0".
      iPoseProof (dli_a2 with "Htext") as "Hia2".
      iPoseProof (dli_a4 with "Htext") as "Hia4".
      iPoseProof (dli_a6 with "Htext") as "Hia6".
      iPoseProof (dli_a8 with "Htext") as "Hia8".
      iPoseProof (dli_aa with "Htext") as "Hiaa".
      (* +0x96 c.ldsp ra,88(sp) *)
      assert (HT1 : add_vec (Mt !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
                    = pa_stk sp0 1) by (rewrite HTsp; apply dlk_frm1).
      iEval (rewrite -HT1) in "Hb1".
      iApply (wp_cldsp_s_sconf (mword_of_int (DL + 0x96)) (mword_of_int 11 : mword 6)
                Rra Mt (K - 12)%nat (m !!! Regidx Rra : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi96 Hb1").
      iIntros (CIDT1 HqT1) "Hcg Hpc Hb1".
      set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> Mt).
      assert (HP1sp : P1 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /P1 upd_ne; [exact HTsp | nz]).
      assert (Hqq98 : add_vec_int (mword_of_int (DL + 0x96) : mword 64) 2
                      = mword_of_int (DL + 0x98)) by pcw.
      iEval (rewrite Hqq98) in "Hpc".
      (* +0x98 c.ldsp s0,80(sp) *)
      assert (HT2 : add_vec (P1 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))
                    = pa_stk sp0 2) by (rewrite HP1sp; apply dlk_frm2).
      iEval (rewrite -HT2) in "Hb2".
      iApply (wp_cldsp_s_sconf (mword_of_int (DL + 0x98)) (mword_of_int 10 : mword 6)
                Rs0 P1 (K - 12)%nat (m !!! Regidx Rs0 : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi98 Hb2").
      iIntros (CIDT2 HqT2) "Hcg Hpc Hb2".
      set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
      assert (HP2sp : P2 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /P2 upd_ne; [exact HP1sp | nz]).
      assert (Hqq9a : add_vec_int (mword_of_int (DL + 0x98) : mword 64) 2
                      = mword_of_int (DL + 0x9a)) by pcw.
      iEval (rewrite Hqq9a) in "Hpc".
      (* +0x9a c.ldsp s1,72(sp) *)
      assert (HT3 : add_vec (P2 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                    = pa_stk sp0 3) by (rewrite HP2sp; apply dlk_frm3).
      iEval (rewrite -HT3) in "Hb3".
      iApply (wp_cldsp_s_sconf (mword_of_int (DL + 0x9a)) (mword_of_int 9 : mword 6)
                Rs1 P2 (K - 12)%nat (m !!! Regidx Rs1 : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi9a Hb3").
      iIntros (CIDT3 HqT3) "Hcg Hpc Hb3".
      set (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2).
      assert (HP3sp : P3 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /P3 upd_ne; [exact HP2sp | nz]).
      assert (Hqq9c : add_vec_int (mword_of_int (DL + 0x9a) : mword 64) 2
                      = mword_of_int (DL + 0x9c)) by pcw.
      iEval (rewrite Hqq9c) in "Hpc".
      (* +0x9c c.ldsp s2,64(sp) *)
      assert (HT4 : add_vec (P3 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                    = pa_stk sp0 4) by (rewrite HP3sp; apply dlk_frm4).
      iEval (rewrite -HT4) in "Hb4".
      iApply (wp_cldsp_s_sconf (mword_of_int (DL + 0x9c)) (mword_of_int 8 : mword 6)
                Rs2 P3 (K - 12)%nat (m !!! Regidx Rs2 : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi9c Hb4").
      iIntros (CIDT4 HqT4) "Hcg Hpc Hb4".
      set (P4 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> P3).
      assert (HP4sp : P4 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /P4 upd_ne; [exact HP3sp | nz]).
      assert (Hqq9e : add_vec_int (mword_of_int (DL + 0x9c) : mword 64) 2
                      = mword_of_int (DL + 0x9e)) by pcw.
      iEval (rewrite Hqq9e) in "Hpc".
      (* +0x9e c.ldsp s3,56(sp) *)
      assert (HT5 : add_vec (P4 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                    = pa_stk sp0 5) by (rewrite HP4sp; apply dlk_frm5).
      iEval (rewrite -HT5) in "Hb5".
      iApply (wp_cldsp_s_sconf (mword_of_int (DL + 0x9e)) (mword_of_int 7 : mword 6)
                Rs3 P4 (K - 12)%nat (m !!! Regidx Rs3 : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi9e Hb5").
      iIntros (CIDT5 HqT5) "Hcg Hpc Hb5".
      set (P5 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3 : mword 64)]> P4).
      assert (HP5sp : P5 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /P5 upd_ne; [exact HP4sp | nz]).
      assert (Hqqa0 : add_vec_int (mword_of_int (DL + 0x9e) : mword 64) 2
                      = mword_of_int (DL + 0xa0)) by pcw.
      iEval (rewrite Hqqa0) in "Hpc".
      (* +0xa0 c.ldsp s4,48(sp) *)
      assert (HT6 : add_vec (P5 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                    = pa_stk sp0 6) by (rewrite HP5sp; apply dlk_frm6).
      iEval (rewrite -HT6) in "Hb6".
      iApply (wp_cldsp_s_sconf (mword_of_int (DL + 0xa0)) (mword_of_int 6 : mword 6)
                Rs4 P5 (K - 12)%nat (m !!! Regidx Rs4 : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hia0 Hb6").
      iIntros (CIDT6 HqT6) "Hcg Hpc Hb6".
      set (P6 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4 : mword 64)]> P5).
      assert (HP6sp : P6 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /P6 upd_ne; [exact HP5sp | nz]).
      assert (Hqqa2 : add_vec_int (mword_of_int (DL + 0xa0) : mword 64) 2
                      = mword_of_int (DL + 0xa2)) by pcw.
      iEval (rewrite Hqqa2) in "Hpc".
      (* +0xa2 c.ldsp s5,40(sp) *)
      assert (HT7 : add_vec (P6 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                    = pa_stk sp0 7) by (rewrite HP6sp; apply dlk_frm7).
      iEval (rewrite -HT7) in "Hb7".
      iApply (wp_cldsp_s_sconf (mword_of_int (DL + 0xa2)) (mword_of_int 5 : mword 6)
                Rs5 P6 (K - 12)%nat (m !!! Regidx Rs5 : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hia2 Hb7").
      iIntros (CIDT7 HqT7) "Hcg Hpc Hb7".
      set (P7 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5 : mword 64)]> P6).
      assert (HP7sp : P7 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /P7 upd_ne; [exact HP6sp | nz]).
      assert (Hqqa4 : add_vec_int (mword_of_int (DL + 0xa2) : mword 64) 2
                      = mword_of_int (DL + 0xa4)) by pcw.
      iEval (rewrite Hqqa4) in "Hpc".
      (* +0xa4 c.ldsp s6,32(sp) *)
      assert (HT8 : add_vec (P7 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                    = pa_stk sp0 8) by (rewrite HP7sp; apply dlk_frm8).
      iEval (rewrite -HT8) in "Hb8".
      iApply (wp_cldsp_s_sconf (mword_of_int (DL + 0xa4)) (mword_of_int 4 : mword 6)
                Rs6 P7 (K - 12)%nat (m !!! Regidx Rs6 : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hia4 Hb8").
      iIntros (CIDT8 HqT8) "Hcg Hpc Hb8".
      set (P8 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6 : mword 64)]> P7).
      assert (HP8sp : P8 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /P8 upd_ne; [exact HP7sp | nz]).
      assert (Hqqa6 : add_vec_int (mword_of_int (DL + 0xa4) : mword 64) 2
                      = mword_of_int (DL + 0xa6)) by pcw.
      iEval (rewrite Hqqa6) in "Hpc".
      (* +0xa6 c.ldsp s7,24(sp) *)
      assert (HT9 : add_vec (P8 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                    = pa_stk sp0 9) by (rewrite HP8sp; apply dlk_frm9).
      iEval (rewrite -HT9) in "Hb9".
      iApply (wp_cldsp_s_sconf (mword_of_int (DL + 0xa6)) (mword_of_int 3 : mword 6)
                Rs7 P8 (K - 12)%nat (m !!! Regidx Rs7 : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hia6 Hb9").
      iIntros (CIDT9 HqT9) "Hcg Hpc Hb9".
      set (P9 := <[Regidx Rs7 := regval_into_reg (m !!! Regidx Rs7 : mword 64)]> P8).
      assert (HP9sp : P9 !!! Regidx csp_rs1 = pa_stk sp0 12)
        by (rewrite /P9 upd_ne; [exact HP8sp | nz]).
      assert (Hqqa8 : add_vec_int (mword_of_int (DL + 0xa6) : mword 64) 2
                      = mword_of_int (DL + 0xa8)) by pcw.
      iEval (rewrite Hqqa8) in "Hpc".
      iEval (rewrite HT1) in "Hb1". iEval (rewrite HT2) in "Hb2".
      iEval (rewrite HT3) in "Hb3". iEval (rewrite HT4) in "Hb4".
      iEval (rewrite HT5) in "Hb5". iEval (rewrite HT6) in "Hb6".
      iEval (rewrite HT7) in "Hb7". iEval (rewrite HT8) in "Hb8".
      iEval (rewrite HT9) in "Hb9".
      (* ---- the [de] buffer goes back to being two frame slots ---- *)
      iDestruct (dlk_name_bytes with "Hde") as "Hdeb2".
      iDestruct (dlk_bytes_slots sp0 Hal12 Hal11 with "Hdeb2") as (w12 w11) "[Hc12 Hc11]".
      iAssert (stack_own sp0 12) with
        "[Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hc11 Hc12]" as "Hstk".
      { rewrite stack_own_slots. cbn [seq].
        iSplitL "Hb1"; [iExists _; iExact "Hb1" |].
        iSplitL "Hb2"; [iExists _; iExact "Hb2" |].
        iSplitL "Hb3"; [iExists _; iExact "Hb3" |].
        iSplitL "Hb4"; [iExists _; iExact "Hb4" |].
        iSplitL "Hb5"; [iExists _; iExact "Hb5" |].
        iSplitL "Hb6"; [iExists _; iExact "Hb6" |].
        iSplitL "Hb7"; [iExists _; iExact "Hb7" |].
        iSplitL "Hb8"; [iExists _; iExact "Hb8" |].
        iSplitL "Hb9"; [iExists _; iExact "Hb9" |].
        iSplitL "Hb10"; [iExists _; iExact "Hb10" |].
        iSplitL "Hc11"; [iExists _; iExact "Hc11" |].
        iSplitL "Hc12"; [iExists _; iExact "Hc12" |].
        done. }
      (* ===== +0xa8 c.addi16sp sp,96 : the pop ===== *)
      assert (Hwv : add_vec (P9 !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6)))
                    = sp0) by (rewrite HP9sp; apply dlk_pop).
      assert (Hpop : (P9 !!! Regidx csp_rs1 : mword 64)
                     = pa_stk (add_vec (P9 !!! Regidx csp_rs1 : mword 64)
                         (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6)))) 12)
        by (rewrite Hwv; exact HP9sp).
      iEval (rewrite -Hwv) in "Hstk".
      iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (DL + 0xa8))
                (mword_of_int 6 : mword 6) P9 (K - 12)%nat 12 b Hpop
                with "Hcg Hpc Hia8 Hstk").
      iIntros (CIDT10 HqT10) "Hcg Hpc".
      set (P10 := <[Regidx csp_rs1 := regval_into_reg
                     (add_vec (P9 !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))))]> P9).
      assert (Hnk : ((K - 12) + 12)%nat = K) by lia.
      iEval (rewrite Hnk) in "Hcg".
      assert (Hqqaa : add_vec_int (mword_of_int (DL + 0xa8) : mword 64) 2
                      = mword_of_int (DL + 0xaa)) by pcw.
      iEval (rewrite Hqqaa) in "Hpc".
      (* ===== +0xaa c.ret ===== *)
      assert (CPra : P10 !!! Regidx Rra = (m !!! Regidx Rra : mword 64)).
      { rewrite /P10 upd_ne; [| nz]. rewrite /P9 upd_ne; [| nz].
        rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
        rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
        rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_ne; [| nz].
        rewrite /P2 upd_ne; [| nz]. rewrite /P1 upd_eq. reflexivity. }
      iApply (wp_cret_s_sconf (mword_of_int (DL + 0xaa)) Rra P10 K b
                ltac:(nz) with "Hcg Hpc Hiaa").
      iIntros (CIDT11 HqT11) "Hcg Hpc".
      iEval (rgne) in "Hpc".
      assert (Hretf : ret_pc (P10 !!! Regidx Rra : mword 64) = ret_tgt)
        by (rewrite CPra; reflexivity).
      iEval (rewrite Hretf) in "Hpc".
      (* ===== the register facts the arms consume ===== *)
      assert (CPsp : P10 !!! Regidx csp_rs1 = (m !!! Regidx csp_rs1 : mword 64)).
      { rewrite /P10 upd_eq. rewrite Hwv. symmetry. exact Hspm. }
      assert (CPs0 : P10 !!! Regidx Rs0 = (m !!! Regidx Rs0 : mword 64)).
      { rewrite /P10 upd_ne; [| nz]. rewrite /P9 upd_ne; [| nz].
        rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
        rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
        rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_ne; [| nz].
        rewrite /P2 upd_eq. reflexivity. }
      assert (CPs1 : P10 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64)).
      { rewrite /P10 upd_ne; [| nz]. rewrite /P9 upd_ne; [| nz].
        rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
        rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
        rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_eq. reflexivity. }
      assert (CPs2 : P10 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64)).
      { rewrite /P10 upd_ne; [| nz]. rewrite /P9 upd_ne; [| nz].
        rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
        rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
        rewrite /P4 upd_eq. reflexivity. }
      assert (CPs3 : P10 !!! Regidx Rs3 = (m !!! Regidx Rs3 : mword 64)).
      { rewrite /P10 upd_ne; [| nz]. rewrite /P9 upd_ne; [| nz].
        rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
        rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_eq. reflexivity. }
      assert (CPs4 : P10 !!! Regidx Rs4 = (m !!! Regidx Rs4 : mword 64)).
      { rewrite /P10 upd_ne; [| nz]. rewrite /P9 upd_ne; [| nz].
        rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
        rewrite /P6 upd_eq. reflexivity. }
      assert (CPs5 : P10 !!! Regidx Rs5 = (m !!! Regidx Rs5 : mword 64)).
      { rewrite /P10 upd_ne; [| nz]. rewrite /P9 upd_ne; [| nz].
        rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_eq. reflexivity. }
      assert (CPs6 : P10 !!! Regidx Rs6 = (m !!! Regidx Rs6 : mword 64)).
      { rewrite /P10 upd_ne; [| nz]. rewrite /P9 upd_ne; [| nz].
        rewrite /P8 upd_eq. reflexivity. }
      assert (CPs7 : P10 !!! Regidx Rs7 = (m !!! Regidx Rs7 : mword 64)).
      { rewrite /P10 upd_ne; [| nz]. rewrite /P9 upd_eq. reflexivity. }
      assert (CPo : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 ->
                P10 !!! Regidx c = (m !!! Regidx c : mword 64)).
      { intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23.
        rewrite /P10 upd_ne; [| dlk_xne N2].
        rewrite /P9 upd_ne; [| dlk_xne N23].
        rewrite /P8 upd_ne; [| dlk_xne N22].
        rewrite /P7 upd_ne; [| dlk_xne N21].
        rewrite /P6 upd_ne; [| dlk_xne N20].
        rewrite /P5 upd_ne; [| dlk_xne N19].
        rewrite /P4 upd_ne; [| dlk_xne N18].
        rewrite /P3 upd_ne; [| dlk_xne N9].
        rewrite /P2 upd_ne; [| dlk_xne N8].
        rewrite /P1 upd_ne; [| dlk_rne2 Hcsra Hc].
        exact (HTthr c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23). }
      assert (CPa0 : P10 !!! Regidx Ra0 = (Mt !!! Regidx Ra0 : mword 64)).
      { rewrite /P10 upd_ne; [| nz]. rewrite /P9 upd_ne; [| nz].
        rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
        rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
        rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_ne; [| nz].
        rewrite /P2 upd_ne; [| nz]. rewrite /P1 upd_ne; [reflexivity | nz]. }
      iSpecialize ("Hqc" $! CIDT11 with "[%]"); [wp_next_chain |].
      iApply ("Hqc" $! P10 with "[%] [%] Hcg Hpc").
      - unfold callee_saved. split_and!;
          first [ exact CPsp | exact CPs0 | exact CPs1 | exact CPs2 | exact CPs3
                | exact CPs4 | exact CPs5 | exact CPs6 | exact CPs7
                | apply CPo; first [ vm_compute; reflexivity
                                   | vm_compute; discriminate ] ].
      - exact CPa0. }
    (* ================================================================= *)
    (*  +0x36 [c.bnez a5]: the EMPTY-DIRECTORY test.                      *)
    (* ================================================================= *)
    assert (HR13a0 : R13 !!! Regidx Ra0 = (mword_of_int 0 : mword 64))
      by (rewrite /R13; apply upd_eq).
    assert (HR13a5 : R13 !!! Regidx Ra5
                     = (sign_extend' 64 (di_size dn : mword 32) : mword 64)).
    { rewrite /R13 upd_ne; [| nz]. rewrite /R12 upd_ne; [| nz].
      rewrite /R11 upd_ne; [| nz]. rewrite /R10 upd_ne; [| nz].
      rewrite /R9 upd_ne; [| nz]. exact HR8a5. }
    pose proof (dlk_tregs_of_regs m sp0 ip nb pf 0 R13 HR13) as HR13tr.
    assert (Hszmb : Z.of_nat MAXFILE * Z.of_nat BSIZE = 274432)
      by (vm_compute; reflexivity).
    assert (Hsznn : 0 <= bv_unsigned (di_size dn))
      by exact (proj1 (bv_unsigned_in_range _ (di_size dn))).
    assert (Hsz31 : bv_unsigned (di_size dn) < 2 ^ 31).
    { apply (Z.le_lt_trans _ (Z.of_nat MAXFILE * Z.of_nat BSIZE) _);
        [exact Hszb | rewrite Hszmb; vm_compute; reflexivity]. }
    assert (Htgt5c : add_vec (mword_of_int (DL + 0x36) : mword 64)
              (sign_extend' 64 (sign_extend' 13
                 (concat_vec (mword_of_int 19 : mword 8) ('b"0"))))
              = mword_of_int (DL + 0x5c)) by pcw.
    destruct (decide (bv_unsigned (di_size dn) = 0)) as [Hsz0 | Hszn].
    - (* ---------- THE DIRECTORY IS EMPTY: fall to +0x38, jump to the
                    tail with a0 = 0 already in place ---------- *)
      iApply (wp_cbnez_fall_s_sconf (mword_of_int (DL + 0x36))
                (mword_of_int 19 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                R13 (K - 12)%nat b
                ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HR13a5; exact (dlk_sz_eqz _ Hsz0))
                with "Hcg Hpc Hi36").
      iIntros (CID24 Hq24) "Hcg Hpc".
      assert (Hpp38 : add_vec_int (mword_of_int (DL + 0x36) : mword 64) 2
                      = mword_of_int (DL + 0x38)) by pcw.
      iEval (rewrite Hpp38) in "Hpc".
      iPoseProof (dli_38 with "Htext") as "Hi38".
      assert (Htgt96 : add_vec (mword_of_int (DL + 0x38) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 47 : mword 11) ('b"0"))))
                = mword_of_int (DL + 0x96)) by pcw.
      iApply (wp_cj_s_sconf (mword_of_int (DL + 0x38))
                (sign_extend' 21 (concat_vec (mword_of_int 47 : mword 11) ('b"0")))
                R13 (K - 12)%nat b
                ltac:(rewrite Htgt96; vm_compute; reflexivity)
                with "Hcg Hpc Hi38").
      iIntros (CID25 Hq25). iNext. iIntros "Hcg Hpc".
      iEval (rewrite Htgt96) in "Hpc".
      assert (Hnone : dir_first data nrec s = None).
      { apply dlk_first_none_zero. apply dlk_nrec_zero. exact Hsz0. }
      iPoseProof ("Htail" $! CID25) as "Ht".
      iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
      iApply ("Ht" $! R13 u10 dolds0 with
                "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hde").
      { exact HR13tr. }
      iIntros (CIDf Hsf mf) "%Hcsf %Ha0f Hcg Hpc".
      iDestruct (cpu_own_transport CID CIDf 0%nat eb pj C b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
      iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf false 0%nat 0%nat 1%Qp with
                "[%] Hcg Hcnt Hpc Hidev Hmeta Hmap Hblocks Hnm Hppid Hbslot
                 [Hislot Hpoff]").
      { exact Hcsf. }
      iSplitR.
      { iPureIntro. split; [exact Hnone |]. rewrite Ha0f. exact HR13a0. }
      iFrame "Hislot Hpoff".
    - (* ---------- THE DIRECTORY IS NON-EMPTY: branch to +0x5c ---------- *)
      (* =============================================================== *)
      (*  THE SCAN.  A fuel induction wrapped in [wp_next]: readi sleeps, *)
      (*  so the hart moves inside the body and the loop statement has to *)
      (*  carry its own [CpuId].  The measure is [nrec - i].              *)
      (* =============================================================== *)
      iAssert (∀ fuel : nat,
        wp_next (CID0 := CID) true pj (fun CIDl : CpuId =>
          dl_loop_body nrec dn data s m sp0 ip nb pf pj ret_tgt K b eb hasp C
            dq dqd dqn dev pofv pidv fn bn gfs bm fuel CIDl))%I with "[]" as "Hloop".
      { iIntros (fuel). iInduction fuel as [|fuel IHf] "IHf".
        { iIntros (CIDl Hsl i Ml dol mt10)
            "%Hfuel %Hilt16 %Hnone %Hregs Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7
             Hb8 Hb9 Hb10 Hde Hidev Hmeta Hmap Hblocks Hnm Hpoff Hppid Hbslot
             Hislot Hqc".
          exfalso.
          assert (Hile : (i <= nrec)%nat)
            by exact (dlk_le_nrec (bv_unsigned (di_size dn)) i Hsznn Hilt16).
          lia. }
        iIntros (CIDl Hsl i Ml dol mt10)
          "%Hfuel %Hilt16 %Hnone %Hregs Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7
           Hb8 Hb9 Hb10 Hde Hidev Hmeta Hmap Hblocks Hnm Hpoff Hppid Hbslot
           Hislot Hqc".
        assert (Hoff31 : Z.of_nat (16 * i) + 16 < 2 ^ 31)
          by exact (dlk_off_lt31' (bv_unsigned (di_size dn)) i Hsznn Hilt16 Hszb).
        assert (Hcv : Z.of_nat (16 * S i) = Z.of_nat (S i) * 16)
          by (rewrite Nat2Z.inj_mul; lia).
        assert (Hoffs : Z.of_nat (16 * S i) = Z.of_nat (16 * i) + 16) by lia.
        (* ------------- THE LATCH at +0x52 (both misses land here) ------- *)
        iAssert (wp_next (CID0 := CIDl) true pj (fun CIDp : CpuId =>
                   dl_latch_body nrec dn data s m sp0 ip nb pf pj ret_tgt K b
                     eb hasp C dq dqd dqn dev pofv pidv fn bn gfs bm i CIDp))%I
          with "[]" as "Hlatch".
        { iIntros (CIDp Hsp Mp dol' mt10')
            "%Hpregs %Hnone2 Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9
             Hb10 Hde Hidev Hmeta Hmap Hblocks Hnm Hpoff Hppid Hbslot Hislot Hqc".
          destruct Hpregs as (Hp2 & Hp8 & Hp9 & Hp18 & Hp19 & Hp20 & Hp21 & Hp22
                              & Hp23 & Hpthr).
          pose proof (conj Hp2 (conj Hp8 (conj Hp9 (conj Hp18 (conj Hp19
            (conj Hp20 (conj Hp21 (conj Hp22 (conj Hp23 Hpthr))))))))) as HpregsW.
          iPoseProof (dli_52 with "Htext") as "Hi52".
          iPoseProof (dli_54 with "Htext") as "Hi54".
          iPoseProof (dli_58 with "Htext") as "Hi58".
          (* +0x52 c.addiw s1,s1,16 *)
          assert (Haddiw : (sign_extend' 64 (subrange_vec_dec
                     (add_vec (Mp !!! Regidx Rs1 : mword 64)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))
                     31 0) : mword 64)
                   = (mword_of_int (Z.of_nat (16 * S i)) : mword 64)).
          { assert (Hsi : Z.of_nat (16 * i + 16)%nat = Z.of_nat (16 * S i)%nat) by lia.
            rewrite Hp9 (dlk_addiw16 (16 * i) Hoff31) Hsi. reflexivity. }
          iApply (wp_caddiw_s_sconf (mword_of_int (DL + 0x52)) Rs1
                    (mword_of_int 16 : mword 6) Mp (K - 12)%nat b
                    ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi52").
          iIntros (CIDP1 HqP1) "Hcg Hpc".
          iEval (rgne; rewrite Haddiw) in "Hcg".
          set (Q1 := <[Regidx Rs1 := regval_into_reg
                        (mword_of_int (Z.of_nat (16 * S i)) : mword 64)]> Mp).
          assert (HQ1regs : dlk_regs m sp0 ip nb pf (16 * S i) Q1)
            by exact (dlk_regs_s1 m sp0 ip nb pf (16 * i) (16 * S i) Mp _
                        eq_refl HpregsW).
          assert (HQ1s1 : Q1 !!! Regidx Rs1
                          = (mword_of_int (Z.of_nat (16 * S i)) : mword 64))
            by (rewrite /Q1; apply upd_eq).
          assert (HQ1s2 : Q1 !!! Regidx Rs2 = ip)
            by (rewrite /Q1 upd_ne; [exact Hp18 | nz]).
          assert (Hqq54 : add_vec_int (mword_of_int (DL + 0x52) : mword 64) 2
                          = mword_of_int (DL + 0x54)) by pcw.
          iEval (rewrite Hqq54) in "Hpc".
          (* +0x54 lw a5,76(s2) : the size is re-read every iteration *)
          iDestruct "Hmeta" as "(Hity & Himaj & Himin & Hinl & Hisz)".
          iEval (rewrite /i_size) in "Hisz".
          iApply (wp_lw_s_sconf (mword_of_int (DL + 0x54)) Ra5 Rs2
                    (mword_of_int 76 : mword 12) Q1 (K - 12)%nat
                    (di_size dn : mword 32) b
                    ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi54 [Hisz]").
          { iEval (rgne; rewrite HQ1s2). iExact "Hisz". }
          iIntros (CIDP2 HqP2) "Hcg Hpc Hisz".
          iEval (rgne; rewrite HQ1s2) in "Hisz".
          iAssert (inode_meta ip dn) with "[Hity Himaj Himin Hinl Hisz]" as "Hmeta".
          { rewrite /inode_meta /i_size. iFrame. }
          set (Q2 := <[Regidx Ra5 := regval_into_reg
                        (sign_extend' 64 (di_size dn : mword 32) : mword 64)]> Q1).
          assert (Hcsa5' : is_cs_idx Ra5 = false) by (vm_compute; reflexivity).
          assert (HQ2regs : dlk_regs m sp0 ip nb pf (16 * S i) Q2)
            by exact (dlk_regs_caller m sp0 ip nb pf (16 * S i) Q1 Ra5 _
                        Hcsa5' HQ1regs).
          assert (HQ2s1 : Q2 !!! Regidx Rs1
                          = (mword_of_int (Z.of_nat (16 * S i)) : mword 64))
            by (rewrite /Q2 upd_ne; [exact HQ1s1 | nz]).
          assert (HQ2a5 : Q2 !!! Regidx Ra5
                          = (mword_of_int (bv_unsigned (di_size dn)) : mword 64)).
          { rewrite /Q2 upd_eq. exact (dlk_sext32_moi (di_size dn) Hsz31). }
          assert (Hqq58 : add_vec_int (mword_of_int (DL + 0x54) : mword 64) 4
                          = mword_of_int (DL + 0x58)) by pcw.
          iEval (rewrite Hqq58) in "Hpc".
          (* +0x58 bgeu s1,a5 : off >= size ends the scan *)
          assert (Hb1 : 0 <= Z.of_nat (16 * S i) < 2 ^ 64).
          { change (2 ^ 64) with 18446744073709551616.
            change (2 ^ 31) with 2147483648 in Hoff31.
            pose proof (Nat2Z.is_nonneg (16 * i)) as Hnn0. lia. }
          assert (Hb2 : 0 <= bv_unsigned (di_size dn) < 2 ^ 64).
          { split; [exact Hsznn |].
            apply (Z.lt_trans _ (2 ^ 31) _);
              [exact Hsz31 | vm_compute; reflexivity]. }
          assert (Hcmp : zopz0zKzJ_u (Q2 !!! Regidx Rs1 : mword 64)
                           (Q2 !!! Regidx Ra5 : mword 64)
                         = Z.geb (Z.of_nat (16 * S i)) (bv_unsigned (di_size dn))).
          { rewrite HQ2s1 HQ2a5. exact (dlk_bgeu _ _ Hb1 Hb2). }
          assert (Htgt94 : add_vec (mword_of_int (DL + 0x58) : mword 64)
                    (sign_extend' 64 (mword_of_int 60 : mword 13))
                    = mword_of_int (DL + 0x94)) by pcw.
          destruct (Z.geb (Z.of_nat (16 * S i)) (bv_unsigned (di_size dn)))
            eqn:Hge.
          + (* ---- the scan is over: a0 := 0 at +0x94, then the tail ---- *)
            iApply (wp_bgeu_taken_s_sconf (mword_of_int (DL + 0x58))
                      (mword_of_int 60 : mword 13) Ra5 Rs1 Q2 (K - 12)%nat b
                      ltac:(nz) ltac:(nz)
                      ltac:(rgne; rgne; rewrite Hcmp; first [ exact Hge | reflexivity ])
                      ltac:(rewrite Htgt94; vm_compute; reflexivity)
                      with "Hcg Hpc Hi58").
            iNext. iIntros (CIDP3 HqP3) "Hcg Hpc".
            iEval (rewrite Htgt94) in "Hpc".
            iPoseProof (dli_94 with "Htext") as "Hi94".
            (* +0x94 c.li a0,0 *)
            iApply (wp_cli_s_sconf (mword_of_int (DL + 0x94)) Ra0
                      (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                      Q2 (K - 12)%nat b
                      ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi94").
            iIntros (CIDP4 HqP4) "Hcg Hpc".
            set (Q3 := <[Regidx Ra0 := regval_into_reg
                          (mword_of_int 0 : mword 64)]> Q2).
            assert (Hcsa0' : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
            assert (HQ3regs : dlk_regs m sp0 ip nb pf (16 * S i) Q3)
              by exact (dlk_regs_caller m sp0 ip nb pf (16 * S i) Q2 Ra0 _
                          Hcsa0' HQ2regs).
            assert (HQ3a0 : Q3 !!! Regidx Ra0 = (mword_of_int 0 : mword 64))
              by (rewrite /Q3; apply upd_eq).
            assert (Hqq96 : add_vec_int (mword_of_int (DL + 0x94) : mword 64) 2
                            = mword_of_int (DL + 0x96)) by pcw.
            iEval (rewrite Hqq96) in "Hpc".
            (* [nrec <= S i], so the [None] we carry covers the whole file *)
            assert (Hle : bv_unsigned (di_size dn) <= Z.of_nat (16 * S i))
              by exact (proj1 (Z.geb_le _ _) Hge).
            assert (Hnle : (nrec <= S i)%nat).
            { destruct (Nat.le_gt_cases nrec (S i)) as [Hx | Hx];
                [exact Hx | exfalso].
              rewrite Hcv in Hle.
              exact (dlk_nle_of_ge (bv_unsigned (di_size dn)) (S i)
                       Hsznn Hle Hx). }
            assert (Hnn : dir_first data nrec s = None).
            { apply dir_first_None. intros jj Hjj.
              apply (proj1 (dir_first_None data (S i) s) Hnone2). lia. }
            iPoseProof ("Htail" $! CIDP4) as "Ht".
            iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
            iApply ("Ht" $! Q3 mt10' dol' with
                      "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10
                       Hde").
            { exact (dlk_tregs_of_regs m sp0 ip nb pf (16 * S i) Q3 HQ3regs). }
            iIntros (CIDf Hsf mf) "%Hcsf %Ha0f Hcg Hpc".
            iDestruct (cpu_own_transport CIDp CIDf 0%nat eb pj C b
                         ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
            iSpecialize ("Hqc" $! CIDf with "[%]"); [wp_next_chain |].
            iApply ("Hqc" $! mf false 0%nat 0%nat 1%Qp with
                      "[%] Hcg Hcnt Hpc Hidev Hmeta Hmap Hblocks Hnm Hppid
                       Hbslot [Hislot Hpoff]").
            { exact Hcsf. }
            iSplitR.
            { iPureIntro. split; [exact Hnn |]. rewrite Ha0f. exact HQ3a0. }
            iFrame "Hislot Hpoff".
          + (* ---- one more record: back to +0x5c with i+1 ---- *)
            iApply (wp_bgeu_fall_s_sconf (mword_of_int (DL + 0x58))
                      (mword_of_int 60 : mword 13) Ra5 Rs1 Q2 (K - 12)%nat b
                      ltac:(nz) ltac:(nz)
                      ltac:(rgne; rgne; rewrite Hcmp; first [ exact Hge | reflexivity ])
                      with "Hcg Hpc Hi58").
            iIntros (CIDP3 HqP3) "Hcg Hpc".
            assert (Hqq5c : add_vec_int (mword_of_int (DL + 0x58) : mword 64) 4
                            = mword_of_int (DL + 0x5c)) by pcw.
            iEval (rewrite Hqq5c) in "Hpc".
            assert (Hgt : Z.of_nat (16 * S i) < bv_unsigned (di_size dn)).
            { apply (proj1 (Z.nle_gt _ _)). intro Hc.
              rewrite (proj2 (Z.geb_le _ _) Hc) in Hge. discriminate. }
            assert (Hgtc : Z.of_nat (S i) * 16 < bv_unsigned (di_size dn))
              by (rewrite -Hcv; exact Hgt).
            assert (Hsile : (S i <= nrec)%nat)
              by exact (dlk_le_nrec (bv_unsigned (di_size dn)) (S i) Hsznn Hgtc).
            iDestruct (cpu_own_transport CIDp CIDP3 0%nat eb pj C b
                         ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
            iSpecialize ("IHf" $! CIDP3 with "[%]"); [wp_next_chain |].
            iApply ("IHf" $! (S i) Q2 dol' mt10' with
                      "[%] [%] [%] [%] Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7
                       Hb8 Hb9 Hb10 Hde Hidev Hmeta Hmap Hblocks Hnm Hpoff Hppid
                       Hbslot Hislot Hqc").
            { lia. }
            { exact Hgtc. }
            { exact Hnone2. }
            { exact HQ2regs. } }
        (* ------------------ THE BODY at +0x5c ------------------------- *)
        pose proof Hregs as HregsD.
        destruct HregsD as (Hm2 & Hm8 & Hm9 & Hm18 & Hm19 & Hm20 & Hm21 & Hm22
                            & Hm23 & Hmthr).
        assert (Hcsa0x : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
        assert (Hcsa1x : is_cs_idx Ra1 = false) by (vm_compute; reflexivity).
        assert (Hcsa2x : is_cs_idx Ra2 = false) by (vm_compute; reflexivity).
        assert (Hcsa3x : is_cs_idx Ra3 = false) by (vm_compute; reflexivity).
        assert (Hcsa4x : is_cs_idx Ra4 = false) by (vm_compute; reflexivity).
        assert (Hcsa5x : is_cs_idx Ra5 = false) by (vm_compute; reflexivity).
        assert (Hcsrax : is_cs_idx Rra = false) by (vm_compute; reflexivity).
        iPoseProof (dli_5c with "Htext") as "Hi5c".
        iPoseProof (dli_5e with "Htext") as "Hi5e".
        iPoseProof (dli_60 with "Htext") as "Hi60".
        iPoseProof (dli_62 with "Htext") as "Hi62".
        iPoseProof (dli_64 with "Htext") as "Hi64".
        iPoseProof (dli_66 with "Htext") as "Hi66".
        iPoseProof (dli_6a with "Htext") as "Hi6a".
        iPoseProof (dli_6e with "Htext") as "Hi6e".
        iPoseProof (dli_72 with "Htext") as "Hi72".
        (* +0x5c c.mv a4,s3 : n := 16 *)
        iApply (wp_cmv_s_sconf (mword_of_int (DL + 0x5c)) Ra4 Rs3 Ml
                  (K - 12)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi5c").
        iIntros (CIDB1 HqB1) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (L1 := <[Regidx Ra4 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (Ml !!! Regidx Rs3))]> Ml).
        assert (HL1regs : dlk_regs m sp0 ip nb pf (16 * i) L1).
        { rewrite /L1. apply dlk_regs_caller; [exact Hcsa4x | exact Hregs]. }
        assert (HL1a4 : L1 !!! Regidx Ra4 = (mword_of_int 16 : mword 64)).
        { rewrite /L1 upd_eq. rewrite Hm19. apply add_vec_zero_l. }
        assert (Hbb5e : add_vec_int (mword_of_int (DL + 0x5c) : mword 64) 2
                        = mword_of_int (DL + 0x5e)) by pcw.
        iEval (rewrite Hbb5e) in "Hpc".
        (* +0x5e c.mv a3,s1 : off *)
        iApply (wp_cmv_s_sconf (mword_of_int (DL + 0x5e)) Ra3 Rs1 L1
                  (K - 12)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi5e").
        iIntros (CIDB2 HqB2) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (L2 := <[Regidx Ra3 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (L1 !!! Regidx Rs1))]> L1).
        assert (HL2regs : dlk_regs m sp0 ip nb pf (16 * i) L2).
        { rewrite /L2. apply dlk_regs_caller; [exact Hcsa3x | exact HL1regs]. }
        assert (HL2a3 : L2 !!! Regidx Ra3
                        = (mword_of_int (Z.of_nat (16 * i)) : mword 64)).
        { rewrite /L2 upd_eq. destruct HL1regs as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
          rewrite D3. apply add_vec_zero_l. }
        assert (HL2a4 : L2 !!! Regidx Ra4 = (mword_of_int 16 : mword 64))
          by (rewrite /L2 upd_ne; [exact HL1a4 | nz]).
        assert (Hbb60 : add_vec_int (mword_of_int (DL + 0x5e) : mword 64) 2
                        = mword_of_int (DL + 0x60)) by pcw.
        iEval (rewrite Hbb60) in "Hpc".
        (* +0x60 c.mv a2,s4 : &de *)
        iApply (wp_cmv_s_sconf (mword_of_int (DL + 0x60)) Ra2 Rs4 L2
                  (K - 12)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi60").
        iIntros (CIDB3 HqB3) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (L3 := <[Regidx Ra2 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (L2 !!! Regidx Rs4))]> L2).
        assert (HL3regs : dlk_regs m sp0 ip nb pf (16 * i) L3).
        { rewrite /L3. apply dlk_regs_caller; [exact Hcsa2x | exact HL2regs]. }
        assert (HL3a2 : L3 !!! Regidx Ra2 = pa_stk sp0 12).
        { rewrite /L3 upd_eq. destruct HL2regs as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
          rewrite D6. apply add_vec_zero_l. }
        assert (HL3a3 : L3 !!! Regidx Ra3
                        = (mword_of_int (Z.of_nat (16 * i)) : mword 64))
          by (rewrite /L3 upd_ne; [exact HL2a3 | nz]).
        assert (HL3a4 : L3 !!! Regidx Ra4 = (mword_of_int 16 : mword 64))
          by (rewrite /L3 upd_ne; [exact HL2a4 | nz]).
        assert (Hbb62 : add_vec_int (mword_of_int (DL + 0x60) : mword 64) 2
                        = mword_of_int (DL + 0x62)) by pcw.
        iEval (rewrite Hbb62) in "Hpc".
        (* +0x62 c.li a1,0 : the KERNEL destination *)
        iApply (wp_cli_s_sconf (mword_of_int (DL + 0x62)) Ra1
                  (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64) L3
                  (K - 12)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                  with "Hcg Hpc Hi62").
        iIntros (CIDB4 HqB4) "Hcg Hpc".
        set (L4 := <[Regidx Ra1 := regval_into_reg
                      (mword_of_int 0 : mword 64)]> L3).
        assert (HL4regs : dlk_regs m sp0 ip nb pf (16 * i) L4).
        { rewrite /L4. apply dlk_regs_caller; [exact Hcsa1x | exact HL3regs]. }
        assert (HL4a1 : L4 !!! Regidx Ra1 = (mword_of_int 0 : mword 64))
          by (rewrite /L4; apply upd_eq).
        assert (HL4a2 : L4 !!! Regidx Ra2 = pa_stk sp0 12)
          by (rewrite /L4 upd_ne; [exact HL3a2 | nz]).
        assert (HL4a3 : L4 !!! Regidx Ra3
                        = (mword_of_int (Z.of_nat (16 * i)) : mword 64))
          by (rewrite /L4 upd_ne; [exact HL3a3 | nz]).
        assert (HL4a4 : L4 !!! Regidx Ra4 = (mword_of_int 16 : mword 64))
          by (rewrite /L4 upd_ne; [exact HL3a4 | nz]).
        assert (Hbb64 : add_vec_int (mword_of_int (DL + 0x62) : mword 64) 2
                        = mword_of_int (DL + 0x64)) by pcw.
        iEval (rewrite Hbb64) in "Hpc".
        (* +0x64 c.mv a0,s2 : dp *)
        iApply (wp_cmv_s_sconf (mword_of_int (DL + 0x64)) Ra0 Rs2 L4
                  (K - 12)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi64").
        iIntros (CIDB5 HqB5) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (L5 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (L4 !!! Regidx Rs2))]> L4).
        assert (HL5regs : dlk_regs m sp0 ip nb pf (16 * i) L5).
        { rewrite /L5. apply dlk_regs_caller; [exact Hcsa0x | exact HL4regs]. }
        assert (HL5a0 : L5 !!! Regidx Ra0 = ip).
        { rewrite /L5 upd_eq. destruct HL4regs as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
          rewrite D4. apply add_vec_zero_l. }
        assert (HL5a1 : L5 !!! Regidx Ra1 = (mword_of_int 0 : mword 64))
          by (rewrite /L5 upd_ne; [exact HL4a1 | nz]).
        assert (HL5a2 : L5 !!! Regidx Ra2 = pa_stk sp0 12)
          by (rewrite /L5 upd_ne; [exact HL4a2 | nz]).
        assert (HL5a3 : L5 !!! Regidx Ra3
                        = (mword_of_int (Z.of_nat (16 * i)) : mword 64))
          by (rewrite /L5 upd_ne; [exact HL4a3 | nz]).
        assert (HL5a4 : L5 !!! Regidx Ra4 = (mword_of_int 16 : mword 64))
          by (rewrite /L5 upd_ne; [exact HL4a4 | nz]).
        assert (Hbb66 : add_vec_int (mword_of_int (DL + 0x64) : mword 64) 2
                        = mword_of_int (DL + 0x66)) by pcw.
        iEval (rewrite Hbb66) in "Hpc".
        (* +0x66 jal ra,readi *)
        assert (Htgtrd : add_vec (mword_of_int (DL + 0x66) : mword 64)
                  (sign_extend' 64 (mword_of_int 2096524 : mword 21))
                  = mword_of_int KernelSyms.readi) by pcw.
        iApply (wp_jal_s_sconf (mword_of_int (DL + 0x66)) Rra
                  (mword_of_int 2096524 : mword 21) L5 (K - 12)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi66").
        iIntros (CIDB6 HqB6) "Hcg Hpc".
        iEval (rewrite Htgtrd) in "Hpc".
        set (L6 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (DL + 0x66) : mword 64) 4)]> L5).
        assert (HL6regs : dlk_regs m sp0 ip nb pf (16 * i) L6).
        { rewrite /L6. apply dlk_regs_caller; [exact Hcsrax | exact HL5regs]. }
        assert (HL6a0 : L6 !!! Regidx Ra0 = ip)
          by (rewrite /L6 upd_ne; [exact HL5a0 | nz]).
        assert (HL6a1 : L6 !!! Regidx Ra1 = (mword_of_int 0 : mword 64))
          by (rewrite /L6 upd_ne; [exact HL5a1 | nz]).
        assert (HL6a2 : L6 !!! Regidx Ra2 = pa_stk sp0 12)
          by (rewrite /L6 upd_ne; [exact HL5a2 | nz]).
        assert (HL6a3 : L6 !!! Regidx Ra3
                        = (mword_of_int (Z.of_nat (16 * i)) : mword 64))
          by (rewrite /L6 upd_ne; [exact HL5a3 | nz]).
        assert (HL6a4 : L6 !!! Regidx Ra4
                        = (mword_of_int (Z.of_nat 16) : mword 64)).
        { rewrite /L6 upd_ne; [| nz]. rewrite HL5a4. pcw. }
        assert (HL6ra : L6 !!! Regidx Rra
                        = add_vec_int (mword_of_int (DL + 0x66) : mword 64) 4)
          by (rewrite /L6; apply upd_eq).
        (* readi takes its two uints in the ABI's sign-extended form; both of
           dirlookup's are far below 2^31, where that is the identity *)
        assert (HL6a3' : L6 !!! Regidx Ra3
                         = sign_extend' 64
                             (mword_of_int (Z.of_nat (16 * i)) : mword 32))
          by (rewrite HL6a3; apply rd_arg32_small; lia).
        assert (HL6a4' : L6 !!! Regidx Ra4
                         = sign_extend' 64
                             (mword_of_int (Z.of_nat 16) : mword 32))
          by (rewrite HL6a4; apply rd_arg32_small; lia).
        (* readi's destination buffer, at the address readi names it by *)
        iAssert (([∗ list] ii ∈ seq 0 16,
                    pa_add (L6 !!! Regidx Ra2 : mword 64) ii ↦ₘ dol ii)
                 ∗ p_pid (proc_addr j) ↦₄{dq} pidv)%I with "[Hde Hppid]" as "Hdst".
        { iEval (rewrite HL6a2 Hpjd). iFrame. }
        iDestruct (cpu_own_transport CIDl CIDB6 0%nat eb pj C b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        iApply (RD.wp_readi_sconf gs j gl gu gd gk pd pav pu bn gfs ga gf
                  cov logstart dev ip bm data dn
                  false (16 * i)%nat 16%nat dol dlk_dummyV
                  pidv dq dqd L6 (K - 12)%nat eb C b
                  ltac:(unfold K_readi; lia) Hlg Hbmwf Hbmcov Hszb
                  ltac:(lia)
                  ltac:(intros _; change (Z.of_nat 16) with 16; lia)
                  Hj Hgs HL6a0
                  ltac:(rewrite HL6a1 dlk_zero_moi; exact (eq_vec_refl _))
                  HL6a3' HL6a4'
                  with "Hcg Hcnt [] [] Htext Hpc Hpanic Hbio Hkenv Hidev Hmeta Hmap
                        Hblocks Hdst Hprocs Hdev Hgeom Hdlk Hbslot").
        { rewrite Heb /trap_csrs_ext. done. }
        { rewrite Heb /cpu_claim_ext. done. }
        iIntros (CIDrd Hsrd mrd tot P')
          "%Hcsrd %Hupt %Htotcl %Hrdret Hcg Hcnt _ _ Hpc Hidev Hmeta Hmap Hblocks
           Hdst2 Hbslot".
        first [ iEval (rewrite Hpjd) in "Hcg" | idtac ].
        first [ iEval (rewrite Hpjd) in "Hcnt" | idtac ].
        iAssert (([∗ list] ii ∈ seq 0 16,
                    pa_add (L6 !!! Regidx Ra2 : mword 64) ii
                      ↦ₘ rd_delivered data dol (16 * i) tot ii)
                 ∗ p_pid (proc_addr j) ↦₄{dq} pidv)%I with "[Hdst2]" as "[Hde Hppid]".
        { iExact "Hdst2". }
        first [ iEval (rewrite Hpjd) in "Hppid" | idtac ].
        destruct Hrdret as [[_ Hbad] | [Hra0rd Hteq]]; [discriminate |].
        assert (Hrdregs : dlk_regs m sp0 ip nb pf (16 * i) mrd)
          by exact (dlk_regs_cs m sp0 ip nb pf (16 * i) L6 mrd Hcsrd HL6regs).
        assert (Hs0rd : mrd !!! Regidx Rs0 = sp0).
        { destruct Hrdregs as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10). exact D2. }
        assert (Hs3rd : mrd !!! Regidx Rs3 = (mword_of_int 16 : mword 64)).
        { destruct Hrdregs as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10). exact D5. }
        assert (Hpcrd : ret_pc (L6 !!! Regidx Rra : mword 64)
                        = mword_of_int (DL + 0x6a)) by (rewrite HL6ra; pcw).
        iEval (rewrite Hpcrd) in "Hpc".
        (* ============ §15(b): THE READ MAY BE SHORT ==================
           [rd_clamp]'s own [decide] is the split.  [16*i + 16 <= size] is
           a WHOLE record -- equivalently [i < nrec], which is what the
           rest of this proof runs on.  Otherwise the tail is a fragment a
           disk-full dirlink left behind, readi returns fewer than sixteen
           bytes, and the [bne a0,s3] at +0x6a is TAKEN into
           panic("dirlookup read") at +0x46.  That arm used to be refuted
           by the granularity premise; it is now walked. *)
        destruct (decide (Z.to_nat (bv_unsigned (di_size dn)) < 16 * i + 16)%nat)
          as [Hshort | Hfull].
        { (* ---------------- THE SHORT READ: dirlookup DIVERGES -------- *)
          assert (Htlt : (tot < 16)%nat).
          { rewrite Hteq (dlk_rd_clamp_short (di_size dn) i Hshort).
            exact (dlk_short_lt16 (bv_unsigned (di_size dn)) i Hsznn Hilt16 Hshort). }
          iPoseProof (dli_46 with "Htext") as "Hi46".
          iPoseProof (dli_4a with "Htext") as "Hi4a".
          iPoseProof (dli_4e with "Htext") as "Hi4e".
          assert (Htk46 : add_vec (mword_of_int (DL + 0x6a) : mword 64)
                    (sign_extend' 64 (mword_of_int 8156 : mword 13))
                  = mword_of_int (DL + 0x46)) by pcw.
          (* +0x6a bne a0,s3 : TAKEN *)
          iApply (wp_bne_taken_s_sconf (mword_of_int (DL + 0x6a))
                    (mword_of_int 8156 : mword 13) Rs3 Ra0 mrd (K - 12)%nat b
                    ltac:(nz) ltac:(nz)
                    ltac:(rgne; rgne; rewrite Hra0rd Hs3rd;
                          exact (dlk_neq16 tot Htlt))
                    ltac:(rewrite Htk46; vm_compute; reflexivity)
                    with "Hcg Hpc Hi6a").
          iNext. iIntros (CIDpa1 Hqpa1) "Hcg Hpc".
          iEval (rewrite Htk46) in "Hpc".
          (* +0x46 auipc a0,0x4 : the panic string, high part *)
          iApply (wp_auipc_s_sconf (mword_of_int (DL + 0x46)) Ra0
                    (mword_of_int 4 : mword 20) mrd (K - 12)%nat b
                    ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi46").
          iIntros (CIDpa2 Hqpa2) "Hcg Hpc".
          set (PA1 := <[Regidx Ra0 := regval_into_reg
                         (add_vec (mword_of_int (DL + 0x46) : mword 64)
                            (auipc_off (mword_of_int 4 : mword 20)))]> mrd).
          assert (Hpp4a : add_vec_int (mword_of_int (DL + 0x46) : mword 64) 4
                          = mword_of_int (DL + 0x4a)) by pcw.
          iEval (rewrite Hpp4a) in "Hpc".
          (* +0x4a addi a0,a0,3290 : ...and its low part *)
          iApply (wp_addi4_s_sconf (mword_of_int (DL + 0x4a)) Ra0 Ra0
                    (mword_of_int 3324 : mword 12) PA1 (K - 12)%nat b
                    ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi4a").
          iIntros (CIDpa3 Hqpa3) "Hcg Hpc".
          set (PA2 := <[Regidx Ra0 := regval_into_reg
                         (add_vec (rget PA1 Ra0)
                            (sign_extend' 64 (mword_of_int 3324 : mword 12)))]> PA1).
          assert (Hpp4e : add_vec_int (mword_of_int (DL + 0x4a) : mword 64) 4
                          = mword_of_int (DL + 0x4e)) by pcw.
          iEval (rewrite Hpp4e) in "Hpc".
          (* +0x4e jal ra,panic -- and panic() never returns *)
          iApply (wp_jal_s_sconf (mword_of_int (DL + 0x4e)) Rra
                    (mword_of_int 2084912 : mword 21) PA2 (K - 12)%nat b
                    ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi4e").
          iIntros (CIDpa4 Hqpa4) "Hcg Hpc".
          assert (Htgtpn : add_vec (mword_of_int (DL + 0x4e) : mword 64)
                             (sign_extend' 64 (mword_of_int 2084912 : mword 21))
                           = mword_of_int KernelSyms.panic) by pcw.
          iEval (rewrite Htgtpn) in "Hpc".
          iPoseProof (panic_wp_any_at CIDpa4 with "Hpanic") as "Hpan".
          iApply ("Hpan" with "Htext Hpc Hcg"). }
        (* ---------------- THE FULL READ: exactly as before ----------- *)
        assert (Hclamp : rd_clamp (di_size dn) (16 * i) 16 = 16%nat)
          by exact (dlk_rd_clamp_full' (di_size dn) i Hfull).
        assert (Htot : tot = 16%nat) by (rewrite Hteq; exact Hclamp).
        assert (Hilt : (i < nrec)%nat)
          by exact (dlk_full_lt (bv_unsigned (di_size dn)) i Hsznn Hfull).
        assert (Ha0rd : mrd !!! Regidx Ra0 = (mword_of_int 16 : mword 64))
          by (rewrite Hra0rd Htot; pcw).
        (* the delivered bytes ARE the file's bytes, split into the two views *)
        iEval (rewrite HL6a2 Htot
                 (bb_ext (pa_stk sp0 12) 16
                    (fun jj => rd_delivered data dol (16 * i) 16 jj)
                    (fun jj => file_byte data (16 * i + jj)%nat)
                    (fun jj Hjj => dlk_rd_delivered data dol i jj Hjj))
                 (dlk_de_view data i (pa_stk sp0 12) (dlk_align_8_2 _ Hal12)))
          in "Hde".
        iDestruct "Hde" as "[Hdehi Hdenm]".
        (* +0x6a bne a0,s3 : the read panic is dead *)
        iApply (wp_bne_fall_s_sconf (mword_of_int (DL + 0x6a))
                  (mword_of_int 8156 : mword 13) Rs3 Ra0 mrd (K - 12)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite Ha0rd Hs3rd; apply dlk_neq_refl)
                  with "Hcg Hpc Hi6a").
        iIntros (CIDB7 HqB7) "Hcg Hpc".
        assert (Hbb6e : add_vec_int (mword_of_int (DL + 0x6a) : mword 64) 4
                        = mword_of_int (DL + 0x6e)) by pcw.
        iEval (rewrite Hbb6e) in "Hpc".
        (* +0x6e lhu a5,-96(s0) : de.inum *)
        iApply (wp_lhu_s_sconf (mword_of_int (DL + 0x6e)) Ra5 Rs0
                  (mword_of_int 4000 : mword 12) mrd (K - 12)%nat
                  (dir_inum data i) b ltac:(nz) ltac:(rdok)
                  with "Hcg Hpc Hi6e [Hdehi]").
        { iEval (rgne; rewrite Hs0rd (dlk_de_addr sp0)). iExact "Hdehi". }
        iIntros (CIDB8 HqB8) "Hcg Hpc Hdehi".
        iEval (rgne; rewrite Hs0rd (dlk_de_addr sp0)) in "Hdehi".
        set (N1 := <[Regidx Ra5 := regval_into_reg
                      (zero_extend' 64 (dir_inum data i : mword 16) : mword 64)]> mrd).
        assert (HN1regs : dlk_regs m sp0 ip nb pf (16 * i) N1).
        { rewrite /N1. apply dlk_regs_caller; [exact Hcsa5x | exact Hrdregs]. }
        assert (HN1a5 : N1 !!! Regidx Ra5
                        = (zero_extend' 64 (dir_inum data i : mword 16) : mword 64))
          by (rewrite /N1; apply upd_eq).
        assert (Hbb72 : add_vec_int (mword_of_int (DL + 0x6e) : mword 64) 4
                        = mword_of_int (DL + 0x72)) by pcw.
        iEval (rewrite Hbb72) in "Hpc".
        assert (Htgt52 : add_vec (mword_of_int (DL + 0x72) : mword 64)
                  (sign_extend' 64 (sign_extend' 13
                     (concat_vec (mword_of_int 240 : mword 8) ('b"0"))))
                  = mword_of_int (DL + 0x52)) by pcw.
        destruct (decide (dir_inum data i = bv_0 16)) as [Hfree | Hlive].
        + (* ---- the record is FREE: [c.beqz] taken, back to the latch ---- *)
          assert (Hnm : ~ dir_match data i s).
          { intros [Hl _]. exact (Hl Hfree). }
          iApply (wp_cbeqz_taken_s_sconf (mword_of_int (DL + 0x72))
                    (mword_of_int 240 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                    N1 (K - 12)%nat b
                    ltac:(vm_compute; reflexivity) ltac:(nz)
                    ltac:(rgne; rewrite HN1a5; exact (dlk_eqz_true _ Hfree))
                    ltac:(rewrite Htgt52; vm_compute; reflexivity)
                    with "Hcg Hpc Hi72").
          iNext. iIntros (CIDB9 HqB9) "Hcg Hpc".
          iEval (rewrite Htgt52) in "Hpc".
          iAssert ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 12) jj
                     ↦ₘ file_byte data (16 * i + jj)%nat)%I
            with "[Hdehi Hdenm]" as "Hde".
          { iEval (rewrite (dlk_de_view data i (pa_stk sp0 12)
                              (dlk_align_8_2 _ Hal12))).
            iSplitL "Hdehi"; [iExact "Hdehi" | iExact "Hdenm"]. }
          iDestruct (cpu_own_transport CIDrd CIDB9 0%nat eb pj C b
                       ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
          iSpecialize ("Hlatch" $! CIDB9 with "[%]"); [wp_next_chain |].
          iApply ("Hlatch" $! N1 (fun jj => file_byte data (16 * i + jj)%nat)
                    mt10 with
                    "[%] [%] Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9
                     Hb10 Hde Hidev Hmeta Hmap Hblocks Hnm Hpoff Hppid Hbslot
                     Hislot Hqc").
          { exact HN1regs. }
          { exact (dir_first_step_miss data i s Hnone Hnm). }
        + (* ---- the record is LIVE: compare the names ---- *)
          iPoseProof (dli_74 with "Htext") as "Hi74".
          iPoseProof (dli_76 with "Htext") as "Hi76".
          iPoseProof (dli_78 with "Htext") as "Hi78".
          iPoseProof (dli_7c with "Htext") as "Hi7c".
          iApply (wp_cbeqz_fall_s_sconf (mword_of_int (DL + 0x72))
                    (mword_of_int 240 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                    N1 (K - 12)%nat b
                    ltac:(vm_compute; reflexivity) ltac:(nz)
                    ltac:(rgne; rewrite HN1a5; exact (dlk_eqz_false _ Hlive))
                    with "Hcg Hpc Hi72").
          iIntros (CIDB9 HqB9) "Hcg Hpc".
          assert (Hbb74 : add_vec_int (mword_of_int (DL + 0x72) : mword 64) 2
                          = mword_of_int (DL + 0x74)) by pcw.
          iEval (rewrite Hbb74) in "Hpc".
          (* +0x74 c.mv a1,s6 : &de.name *)
          iApply (wp_cmv_s_sconf (mword_of_int (DL + 0x74)) Ra1 Rs6 N1
                    (K - 12)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi74").
          iIntros (CIDB10 HqB10) "Hcg Hpc". iEval (rgne) in "Hcg".
          set (N2 := <[Regidx Ra1 := regval_into_reg
                        (add_vec (zero_reg : mword 64) (N1 !!! Regidx Rs6))]> N1).
          assert (HN2regs : dlk_regs m sp0 ip nb pf (16 * i) N2).
          { rewrite /N2. apply dlk_regs_caller; [exact Hcsa1x | exact HN1regs]. }
          assert (HN2a1 : N2 !!! Regidx Ra1 = pa_add (pa_stk sp0 12) 2).
          { rewrite /N2 upd_eq. destruct HN1regs as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
            rewrite D8. apply add_vec_zero_l. }
          assert (Hbb76 : add_vec_int (mword_of_int (DL + 0x74) : mword 64) 2
                          = mword_of_int (DL + 0x76)) by pcw.
          iEval (rewrite Hbb76) in "Hpc".
          (* +0x76 c.mv a0,s5 : the caller's name *)
          iApply (wp_cmv_s_sconf (mword_of_int (DL + 0x76)) Ra0 Rs5 N2
                    (K - 12)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi76").
          iIntros (CIDB11 HqB11) "Hcg Hpc". iEval (rgne) in "Hcg".
          set (N3 := <[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64) (N2 !!! Regidx Rs5))]> N2).
          assert (HN3regs : dlk_regs m sp0 ip nb pf (16 * i) N3).
          { rewrite /N3. apply dlk_regs_caller; [exact Hcsa0x | exact HN2regs]. }
          assert (HN3a0 : N3 !!! Regidx Ra0 = nb).
          { rewrite /N3 upd_eq. destruct HN2regs as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
            rewrite D7. apply add_vec_zero_l. }
          assert (HN3a1 : N3 !!! Regidx Ra1 = pa_add (pa_stk sp0 12) 2)
            by (rewrite /N3 upd_ne; [exact HN2a1 | nz]).
          assert (Hbb78 : add_vec_int (mword_of_int (DL + 0x76) : mword 64) 2
                          = mword_of_int (DL + 0x78)) by pcw.
          iEval (rewrite Hbb78) in "Hpc".
          (* +0x78 jal ra,namecmp *)
          assert (Htgtnc : add_vec (mword_of_int (DL + 0x78) : mword 64)
                    (sign_extend' 64 (mword_of_int 2097010 : mword 21))
                    = mword_of_int KernelSyms.namecmp) by pcw.
          iApply (wp_jal_s_sconf (mword_of_int (DL + 0x78)) Rra
                    (mword_of_int 2097010 : mword 21) N3 (K - 12)%nat b
                    ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi78").
          iIntros (CIDB12 HqB12) "Hcg Hpc".
          iEval (rewrite Htgtnc) in "Hpc".
          set (N4 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (DL + 0x78) : mword 64) 4)]> N3).
          assert (HN4regs : dlk_regs m sp0 ip nb pf (16 * i) N4).
          { rewrite /N4. apply dlk_regs_caller; [exact Hcsrax | exact HN3regs]. }
          assert (HN4a0 : N4 !!! Regidx Ra0 = nb)
            by (rewrite /N4 upd_ne; [exact HN3a0 | nz]).
          assert (HN4a1 : N4 !!! Regidx Ra1 = pa_add (pa_stk sp0 12) 2)
            by (rewrite /N4 upd_ne; [exact HN3a1 | nz]).
          assert (HN4ra : N4 !!! Regidx Rra
                          = add_vec_int (mword_of_int (DL + 0x78) : mword 64) 4)
            by (rewrite /N4; apply upd_eq).
          iEval (rewrite -HN4a0) in "Hnm".
          iEval (rewrite -HN4a1) in "Hdenm".
          iApply (NC.wp_namecmp_sconf N4 fn (dir_name data i) (K - 12)%nat
                    dqn (DfracOwn 1) b pj ltac:(unfold K_namecmp; lia)
                    with "Hcg Htext Hpc Hnm Hdenm").
          iIntros (CIDnc Hsnc mnc) "%Hcsnc Hcg Hpc Hnm Hdenm %Hiff".
          iEval (rewrite HN4a0) in "Hnm".
          iEval (rewrite HN4a1) in "Hdenm".
          assert (Hncregs : dlk_regs m sp0 ip nb pf (16 * i) mnc)
            by exact (dlk_regs_cs m sp0 ip nb pf (16 * i) N4 mnc Hcsnc HN4regs).
          assert (Hpcnc : ret_pc (N4 !!! Regidx Rra : mword 64)
                          = mword_of_int (DL + 0x7c)) by (rewrite HN4ra; pcw).
          iEval (rewrite Hpcnc) in "Hpc".
          assert (Htgt52b : add_vec (mword_of_int (DL + 0x7c) : mword 64)
                    (sign_extend' 64 (sign_extend' 13
                       (concat_vec (mword_of_int 235 : mword 8) ('b"0"))))
                    = mword_of_int (DL + 0x52)) by pcw.
          destruct (decide (mnc !!! Regidx Ra0 = (mword_of_int 0 : mword 64)))
            as [Hhit | Hmiss].
          * (* ======== THE NAME MATCHES: the FOUND arm ======== *)
            assert (Hmatch : dir_match data i s).
            { split; [exact Hlive |]. symmetry. exact (proj1 Hiff Hhit). }
            iApply (wp_cbnez_fall_s_sconf (mword_of_int (DL + 0x7c))
                      (mword_of_int 235 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                      mnc (K - 12)%nat b
                      ltac:(vm_compute; reflexivity) ltac:(nz)
                      ltac:(rgne; exact (dlk_neqz_false _ Hhit))
                      with "Hcg Hpc Hi7c").
            iIntros (CIDB13 HqB13) "Hcg Hpc".
            assert (Hbb7e : add_vec_int (mword_of_int (DL + 0x7c) : mword 64) 2
                            = mword_of_int (DL + 0x7e)) by pcw.
            iEval (rewrite Hbb7e) in "Hpc".
            iPoseProof (dli_7e with "Htext") as "Hi7e".
            iPoseProof (dli_86 with "Htext") as "Hi86".
            iPoseProof (dli_8a with "Htext") as "Hi8a".
            iPoseProof (dli_8e with "Htext") as "Hi8e".
            iPoseProof (dli_92 with "Htext") as "Hi92".
            assert (Hncs1 : mnc !!! Regidx Rs1
                            = (mword_of_int (Z.of_nat (16 * i)) : mword 64)).
            { destruct Hncregs as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10). exact D3. }
            assert (Hncs2 : mnc !!! Regidx Rs2 = ip).
            { destruct Hncregs as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10). exact D4. }
            assert (Hncs0 : mnc !!! Regidx Rs0 = sp0).
            { destruct Hncregs as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10). exact D2. }
            assert (Hncs7 : mnc !!! Regidx Rs7 = pf).
            { destruct Hncregs as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10). exact D9. }
            assert (Htgt86 : add_vec (mword_of_int (DL + 0x7e) : mword 64)
                      (sign_extend' 64 (mword_of_int 8 : mword 13))
                      = mword_of_int (DL + 0x86)) by pcw.
            (* +0x7e beq s7,x0 / +0x82 sw s1,0(s7) : the optional [*poff = off] *)
            iAssert (sie_cap_gpr mnc (K - 12)%nat b pj -∗
                     pc_is (mword_of_int (DL + 0x7e)) -∗
                     (if hasp then pf ↦₄ pofv else emp) -∗
                     wp_next (CID0 := CIDB13) true pj (fun CIDs : CpuId =>
                       sie_cap_gpr mnc (K - 12)%nat b pj -∗
                       pc_is (mword_of_int (DL + 0x86)) -∗
                       (if hasp
                        then pf ↦₄ (mword_of_int (Z.of_nat (16 * i)) : mword 32)
                        else emp) -∗
                       WP (Loop : expr riscv_lang)) -∗
                     WP (Loop : expr riscv_lang))%I with "[]" as "Hpoffst".
            { iIntros "Hcg Hpc Hpv Hk".
              destruct hasp.
              - iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (DL + 0x7e))
                          (mword_of_int 8 : mword 13) Rs7 mnc (K - 12)%nat b
                          ltac:(nz) ltac:(rgne; rewrite Hncs7; exact Hposs)
                          with "Hcg Hpc Hi7e").
                iIntros (CIDS1 HqS1) "Hcg Hpc".
                assert (Hbb82 : add_vec_int (mword_of_int (DL + 0x7e) : mword 64) 4
                                = mword_of_int (DL + 0x82)) by pcw.
                iEval (rewrite Hbb82) in "Hpc".
                iPoseProof (dli_82 with "Htext") as "Hi82".
                iApply (wp_sw_s_sconf (mword_of_int (DL + 0x82)) Rs1 Rs7
                          (mword_of_int 0 : mword 12) mnc (K - 12)%nat pofv b
                          with "Hcg Hpc Hi82 [Hpv]").
                { iEval (rgne; rewrite Hncs7 (dlk_add_vec_0 pf)). iExact "Hpv". }
                iIntros (CIDS2 HqS2) "Hcg Hpc Hpv".
                iEval (rgne; rgne; rewrite Hncs7 Hncs1 (dlk_add_vec_0 pf)
                         trunc32_mword_of_int) in "Hpv".
                assert (Hbb86 : add_vec_int (mword_of_int (DL + 0x82) : mword 64) 4
                                = mword_of_int (DL + 0x86)) by pcw.
                iEval (rewrite Hbb86) in "Hpc".
                iSpecialize ("Hk" $! CIDS2 with "[%]"); [wp_next_chain |].
                iApply ("Hk" with "Hcg Hpc [Hpv]"). iExact "Hpv".
              - iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (DL + 0x7e))
                          (mword_of_int 8 : mword 13) Rs7 mnc (K - 12)%nat b
                          ltac:(nz) ltac:(rgne; rewrite Hncs7; exact Hposs)
                          ltac:(rewrite Htgt86; vm_compute; reflexivity)
                          with "Hcg Hpc Hi7e").
                iNext. iIntros (CIDS1 HqS1) "Hcg Hpc".
                iEval (rewrite Htgt86) in "Hpc".
                iSpecialize ("Hk" $! CIDS1 with "[%]"); [wp_next_chain |].
                iApply ("Hk" with "Hcg Hpc Hpv"). }
            iApply ("Hpoffst" with "Hcg Hpc Hpoff").
            iIntros (CIDB14 HqB14) "Hcg Hpc Hpoff".
            (* +0x86 lhu a1,-96(s0) : the inum again *)
            iApply (wp_lhu_s_sconf (mword_of_int (DL + 0x86)) Ra1 Rs0
                      (mword_of_int 4000 : mword 12) mnc (K - 12)%nat
                      (dir_inum data i) b ltac:(nz) ltac:(rdok)
                      with "Hcg Hpc Hi86 [Hdehi]").
            { iEval (rgne; rewrite Hncs0 (dlk_de_addr sp0)). iExact "Hdehi". }
            iIntros (CIDB15 HqB15) "Hcg Hpc Hdehi".
            iEval (rgne; rewrite Hncs0 (dlk_de_addr sp0)) in "Hdehi".
            set (N5 := <[Regidx Ra1 := regval_into_reg
                          (zero_extend' 64 (dir_inum data i : mword 16) : mword 64)]> mnc).
            assert (HN5regs : dlk_regs m sp0 ip nb pf (16 * i) N5).
            { rewrite /N5. apply dlk_regs_caller; [exact Hcsa1x | exact Hncregs]. }
            assert (HN5a1 : N5 !!! Regidx Ra1
                            = (zero_extend' 64 (dir_inum data i : mword 16) : mword 64))
              by (rewrite /N5; apply upd_eq).
            assert (HN5s2 : N5 !!! Regidx Rs2 = ip)
              by (rewrite /N5 upd_ne; [exact Hncs2 | nz]).
            assert (Hbb8a : add_vec_int (mword_of_int (DL + 0x86) : mword 64) 4
                            = mword_of_int (DL + 0x8a)) by pcw.
            iEval (rewrite Hbb8a) in "Hpc".
            (* +0x8a lw a0,0(s2) : dp->dev *)
            iEval (rewrite /i_dev) in "Hidev".
            iApply (wp_lw_s_sconf (mword_of_int (DL + 0x8a)) Ra0 Rs2
                      (mword_of_int 0 : mword 12) N5 (K - 12)%nat dev b
                      ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi8a [Hidev]").
            { iEval (rgne; rewrite HN5s2). iExact "Hidev". }
            iIntros (CIDB16 HqB16) "Hcg Hpc Hidev".
            iEval (rgne; rewrite HN5s2; rewrite -/(i_dev ip)) in "Hidev".
            set (N6 := <[Regidx Ra0 := regval_into_reg
                          (sign_extend' 64 dev : mword 64)]> N5).
            assert (HN6regs : dlk_regs m sp0 ip nb pf (16 * i) N6).
            { rewrite /N6. apply dlk_regs_caller; [exact Hcsa0x | exact HN5regs]. }
            assert (HN6a0 : N6 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
              by (rewrite /N6; apply upd_eq).
            assert (HN6a1 : N6 !!! Regidx Ra1
                            = (zero_extend' 64 (dir_inum data i : mword 16) : mword 64))
              by (rewrite /N6 upd_ne; [exact HN5a1 | nz]).
            assert (Hbb8e : add_vec_int (mword_of_int (DL + 0x8a) : mword 64) 4
                            = mword_of_int (DL + 0x8e)) by pcw.
            iEval (rewrite Hbb8e) in "Hpc".
            (* +0x8e jal ra,iget *)
            assert (Htgtig : add_vec (mword_of_int (DL + 0x8e) : mword 64)
                      (sign_extend' 64 (mword_of_int 2094944 : mword 21))
                      = mword_of_int KernelSyms.iget) by pcw.
            iApply (wp_jal_s_sconf (mword_of_int (DL + 0x8e)) Rra
                      (mword_of_int 2094944 : mword 21) N6 (K - 12)%nat b
                      ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                      with "Hcg Hpc Hi8e").
            iIntros (CIDB17 HqB17) "Hcg Hpc".
            iEval (rewrite Htgtig) in "Hpc".
            set (N7 := <[Regidx Rra := regval_into_reg
                          (add_vec_int (mword_of_int (DL + 0x8e) : mword 64) 4)]> N6).
            assert (HN7regs : dlk_regs m sp0 ip nb pf (16 * i) N7).
            { rewrite /N7. apply dlk_regs_caller; [exact Hcsrax | exact HN6regs]. }
            assert (HN7a0 : N7 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
              by (rewrite /N7 upd_ne; [exact HN6a0 | nz]).
            assert (HN7a1 : N7 !!! Regidx Ra1
                            = (zero_extend' 64 (dir_inum data i : mword 16) : mword 64))
              by (rewrite /N7 upd_ne; [exact HN6a1 | nz]).
            assert (HN7ra : N7 !!! Regidx Rra
                            = add_vec_int (mword_of_int (DL + 0x8e) : mword 64) 4)
              by (rewrite /N7; apply upd_eq).
            assert (Hinumb : bv_unsigned
                      (zero_extend' 32 (dir_inum data i : mword 16) : mword 32)
                      < 16 * Z.of_nat nib).
            { rewrite (dlk_zext32_unsigned (dir_inum data i)).
              exact (Hinums i Hilt Hlive). }
            iDestruct (cpu_own_transport CIDrd CIDB17 0%nat eb pj C b
                         ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
            iApply (IG.wp_iget_sconf gtl cn gfs gi cov logstart nib dev
                      (zero_extend' 32 (dir_inum data i : mword 16) : mword 32)
                      N7 0%nat eb pj C (K - 12)%nat b
                      ltac:(unfold K_iget; lia)
                      ltac:(vm_compute; reflexivity) Hinumb HN7a0
                      ltac:(rewrite dlk_sext_zext_16_32_64; exact HN7a1)
                      with "Hcg Hcnt Htext Hpc Hitb2 Hitbl Hesc Hpanic Hislot").
            iIntros (CIDig Hsig mig kslot q) "Hcg Hcnt Hpc %Higp Href".
            destruct Higp as (Hcsig & Hkslot & Higa0).
            assert (Higregs : dlk_regs m sp0 ip nb pf (16 * i) mig)
              by exact (dlk_regs_cs m sp0 ip nb pf (16 * i) N7 mig Hcsig HN7regs).
            assert (Hpcig : ret_pc (N7 !!! Regidx Rra : mword 64)
                            = mword_of_int (DL + 0x92)) by (rewrite HN7ra; pcw).
            iEval (rewrite Hpcig) in "Hpc".
            (* +0x92 c.j +0x96 *)
            assert (Htgt96b : add_vec (mword_of_int (DL + 0x92) : mword 64)
                      (sign_extend' 64 (sign_extend' 21
                         (concat_vec (mword_of_int 2 : mword 11) ('b"0"))))
                      = mword_of_int (DL + 0x96)) by pcw.
            iApply (wp_cj_s_sconf (mword_of_int (DL + 0x92))
                      (sign_extend' 21 (concat_vec (mword_of_int 2 : mword 11) ('b"0")))
                      mig (K - 12)%nat b
                      ltac:(rewrite Htgt96b; vm_compute; reflexivity)
                      with "Hcg Hpc Hi92").
            iIntros (CIDB18 HqB18). iNext. iIntros "Hcg Hpc".
            iEval (rewrite Htgt96b) in "Hpc".
            (* the de buffer goes back to sixteen raw bytes for the tail *)
            iAssert ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 12) jj
                       ↦ₘ file_byte data (16 * i + jj)%nat)%I
              with "[Hdehi Hdenm]" as "Hde".
            { iEval (rewrite (dlk_de_view data i (pa_stk sp0 12)
                                (dlk_align_8_2 _ Hal12))).
              iSplitL "Hdehi"; [iExact "Hdehi" | iExact "Hdenm"]. }
            assert (Hsome : dir_first data nrec s = Some i).
            { apply (dir_first_mono data (S i) nrec i s ltac:(lia)).
              exact (dir_first_step_hit data i s Hnone Hmatch). }
            iPoseProof ("Htail" $! CIDB18) as "Ht".
            iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
            iApply ("Ht" $! mig mt10 (fun jj => file_byte data (16 * i + jj)%nat)
                      with "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10
                            Hde").
            { exact (dlk_tregs_of_regs m sp0 ip nb pf (16 * i) mig Higregs). }
            iIntros (CIDf Hsf mf) "%Hcsf %Ha0f Hcg Hpc".
            iDestruct (cpu_own_transport CIDig CIDf 0%nat eb pj C b
                         ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
            iSpecialize ("Hqc" $! CIDf with "[%]"); [wp_next_chain |].
            iApply ("Hqc" $! mf true i kslot q with
                      "[%] Hcg Hcnt Hpc Hidev Hmeta Hmap Hblocks Hnm Hppid
                       Hbslot [Href Hpoff]").
            { exact Hcsf. }
            iSplitR.
            { iPureIntro. split; [exact Hsome |]. split; [exact Hkslot |].
              rewrite Ha0f. exact Higa0. }
            iSplitL "Href"; [iExact "Href" | iExact "Hpoff"].
          * (* ======== THE NAME DIFFERS: [c.bnez] taken, to the latch ==== *)
            assert (Hnm : ~ dir_match data i s).
            { intros [_ Hbn]. apply Hmiss. apply Hiff. symmetry. exact Hbn. }
            iApply (wp_cbnez_taken_s_sconf (mword_of_int (DL + 0x7c))
                      (mword_of_int 235 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                      mnc (K - 12)%nat b
                      ltac:(vm_compute; reflexivity) ltac:(nz)
                      ltac:(rgne; exact (dlk_neqz_true _ Hmiss))
                      ltac:(rewrite Htgt52b; vm_compute; reflexivity)
                      with "Hcg Hpc Hi7c").
            iNext. iIntros (CIDB13 HqB13) "Hcg Hpc".
            iEval (rewrite Htgt52b) in "Hpc".
            iAssert ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 12) jj
                       ↦ₘ file_byte data (16 * i + jj)%nat)%I
              with "[Hdehi Hdenm]" as "Hde".
            { iEval (rewrite (dlk_de_view data i (pa_stk sp0 12)
                                (dlk_align_8_2 _ Hal12))).
              iSplitL "Hdehi"; [iExact "Hdehi" | iExact "Hdenm"]. }
            iDestruct (cpu_own_transport CIDrd CIDB13 0%nat eb pj C b
                         ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
            iSpecialize ("Hlatch" $! CIDB13 with "[%]"); [wp_next_chain |].
            iApply ("Hlatch" $! mnc (fun jj => file_byte data (16 * i + jj)%nat)
                      mt10 with
                      "[%] [%] Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9
                       Hb10 Hde Hidev Hmeta Hmap Hblocks Hnm Hpoff Hppid Hbslot
                       Hislot Hqc").
            { exact Hncregs. }
            { exact (dir_first_step_miss data i s Hnone Hnm). } }
      (* ---------- the loop is entered at +0x5c with off = 0 ---------- *)
      iApply (wp_cbnez_taken_s_sconf (mword_of_int (DL + 0x36))
                (mword_of_int 19 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                R13 (K - 12)%nat b
                ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HR13a5; exact (dlk_sz_nez _ Hsz31 Hszn))
                ltac:(rewrite Htgt5c; vm_compute; reflexivity)
                with "Hcg Hpc Hi36").
      iNext. iIntros (CID24 Hq24) "Hcg Hpc".
      iEval (rewrite Htgt5c) in "Hpc".
      iDestruct (cpu_own_transport CID CID24 0%nat eb pj C b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
      iSpecialize ("Hloop" $! (S nrec) CID24 with "[%]"); [wp_next_chain |].
      iApply ("Hloop" $! 0%nat R13 dolds0 u10 with
                "[%] [%] [%] [%] Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8
                 Hb9 Hb10 Hde Hidev Hmeta Hmap Hblocks Hnm Hpoff Hppid Hbslot
                 Hislot Hcont").
      { lia. }
      { exact (dlk_off0_lt (bv_unsigned (di_size dn)) Hsznn Hszn). }
      { unfold dir_first. apply dfirst_0. }
      { exact HR13. }
  Qed.

End ProofDirlookupMain.

End DirlookupProof.
