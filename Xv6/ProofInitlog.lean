/-
Proof of `initlog`'s specification (`SpecInitlog.INITLOG`), given the
interfaces of `initlock`, `bread`, `brelse`, `install_trans` and
`write_head`.

    void initlog(int dev, struct superblock *sb) {
      initlock(&log.lock, "log");
      log.start = sb->logstart;
      log.dev   = dev;
      recover_from_log();       // INLINED, and read_head with it
    }

forty-seven instructions: the six-slot frame (`ra`, `s0`, `s1`, `s2`, `s3`
and a pad -- `MachCSL.frame6s3`), the `initlock` call, the ONE superblock
read (`sb->logstart` at `+0x28`) and the TWO stores it feeds
(`log.start`, `log.dev` -- this kernel's `struct log` has no `size` field;
its fifth word is `ncommit`), then `recover_from_log` inlined:
`read_head` (`bread` at `+0x36`, `lh.n = hb->n` at `+0x3a`/`+0x3c`, the
copy loop at `+0x52`, `brelse` at `+0x5e`), `install_trans(1)` at `+0x64`,
`log.lh.n = 0` at `+0x6c` and `write_head` at `+0x70`.  Then the epilogue,
and -- as a ghost step, with no instruction of its own -- the lock's birth
(`MachCSL.kctx_newlock`) over the boot pack `Xv6/LogBoot.lean` assembles.

THE TWO STORES ARE PUBLISHED, NOT KEPT.  `log.start` and `log.dev` are
written once and then frozen at `DFrac.discard` (`Xv6.logFrozen`), because
that is what `install_trans` and `write_head` take: both run with NO lock
held -- they are the committer's helpers -- so they cannot be given
`Xv6.logCtx`, which does not exist until the last instruction has run.

**THE HEADER'S CLEAN TIE IS NOW PROVED**, not assumed.  `bread`'s post is
`Xv6.bioLocked`, whose payload half (`Xv6.bioPay`) carries the CLIENT
VIEW's content at the block -- clean arm `V.clean bno bs ∗ ⌜bsd = bs⌝`,
dirty arm `V.dirty bno bs ∗ bref` -- so with `hcl`/`hdt` (the premises
every log spec carries: `V.clean = fsMclean γfs`, `V.dirty = fsMdirty
γfs`) the bytes agree with the header block's `Xv6.fsChalf` on EITHER
polarity.  That is Rocq `ProofInitlog.v`'s `il_pay_agree`, and it is
`Xv6.il_pay_agree` below.  The other half -- that the header's content
DECODES CLEAN -- is a genuine boot premise, Rocq `SpecFsinit.v`'s (g), and
it now sits in `Xv6/SpecInitlog.lean`'s precondition as
`hhdr0 : hdrN bsHdr = 0`; at `n = 0` the write set is empty, the copy loop
at `+0x52` is dead and the `blez` at `+0x40` is proved taken.  (It is
still forced here rather than derived, because this port's
`Xv6/SpecInstallTrans.lean` recovering arm takes each entry's HOME block
CLIENT HALF -- its own deviation -- and `SpecInitlog`'s precondition hands
out client halves only for the log's own region.)

**THIS PROOF ASSUMES NOTHING BEYOND ITS CALLEES' CONTRACTS.**  The former
`LogTxAuthBridge` hypothesis (a `GhostMapG` instance collision between the
bcache's slot map and the log's transaction map) is retired: both now use
the one shared camera `Xv6G.gmUnitG`, told apart by ghost name.
-/
import Xv6.SpecInitlog
import Xv6.LogBoot
import Xv6.CodeTactics
import MachCSL.ByteWord4
import MachCSL.WpSmodeFrame6c
import Xv6.FsCallSites

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The relocations the code computes -/

/-- `auipc s2,0x1e ; addi s2,s2,1806` at `+0x12`/`+0x16`. -/
theorem il_log_addr : KA.«initlog» + 0x1e720#64 = logAddr := by
  unfold logAddr; decide
/-- `auipc a5,0x1e ; sw zero,1764(a5)` at `+0x68`/`+0x6c`. -/
theorem il_lhn_reloc : KA.«initlog» + 0x1e74c#64 = lhNAddr := by
  unfold lhNAddr logAddr; decide

theorem il_lStart : logAddr + 24#64 = lStart := rfl
theorem il_lDev : logAddr + 36#64 = lDev := rfl
theorem il_lhN : logAddr + 44#64 = lhNAddr := rfl

theorem il_br_initlock : KA.«initlog» + 0xFFFFFFFFFFFFCEF8#64 = KA.«initlock» := by decide
theorem il_br_bread : KA.«initlog» + 0xFFFFFFFFFFFFEF80#64 = KA.«bread» := by decide
theorem il_br_brelse : KA.«initlog» + 0xFFFFFFFFFFFFF088#64 = KA.«brelse» := by decide
theorem il_br_install : KA.«initlog» + 0xFFFFFFFFFFFFFF34#64 = KA.«install_trans» := by decide
theorem il_br_writehead : KA.«initlog» + 0xFFFFFFFFFFFFFED6#64 = KA.«write_head» := by decide

theorem il_ret_28 : jumpPc (KA.«initlog» + 0x28#64) = (KA.«initlog» + 0x28#64) := by decide
theorem il_ret_3a : jumpPc (KA.«initlog» + 0x3a#64) = (KA.«initlog» + 0x3a#64) := by decide
theorem il_ret_62 : jumpPc (KA.«initlog» + 0x62#64) = (KA.«initlog» + 0x62#64) := by decide
theorem il_ret_68 : jumpPc (KA.«initlog» + 0x68#64) = (KA.«initlog» + 0x68#64) := by decide
theorem il_ret_74 : jumpPc (KA.«initlog» + 0x74#64) = (KA.«initlog» + 0x74#64) := by decide

/-! ## Small arithmetic -/

theorem il_sext0 : BitVec.signExtend 64 (0#32) = 0#64 := by decide
theorem il_ext0 : BitVec.extractLsb' 0 32 (0#64) = 0#32 := by decide
theorem il_ext_sext (w : BitVec 32) : BitVec.extractLsb' 0 32 (BitVec.signExtend 64 w) = w := by
  bv_decide

/-- `blez a2` with the header's `n` word at zero: taken. -/
theorem il_blez_zero : bcond bop.BGE 0#64 0#64 = true := by decide

/-- A four-byte run that assembles to zero IS four zero bytes, hence the
zero word: what `hdr_n bs = 0` says about `hb->n`. -/
theorem il_word_zero (l : List (BitVec 8)) (h4 : l.length = 4) (h : leAssemble l = 0) :
    MachCSL.bytesToWord4 l = 0#32 := by
  obtain ⟨b0, b1, b2, b3, rfl⟩ := MachCSL.list4 l h4
  have he : b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 0))) = 0 := h
  have e0 : b0 = 0#8 := by apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
  have e1 : b1 = 0#8 := by apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
  have e2 : b2 = 0#8 := by apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
  have e3 : b3 = 0#8 := by apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
  subst e0; subst e1; subst e2; subst e3
  decide

theorem il_hdrN_word (bs : List (BitVec 8)) (hl : 4 ≤ bs.length) (h : hdrN bs = 0) :
    MachCSL.bytesToWord4 ((bs.drop (4 * 0)).take 4) = 0#32 := by
  refine il_word_zero _ ?_ h
  simp only [Nat.mul_zero, List.drop_zero, List.length_take]
  omega

/-- The buffer's first word, read and put straight back. -/
theorem il_hdr_roundtrip (bs : List (BitVec 8)) (hl : 4 ≤ bs.length) :
    bs.take (4 * 0) ++ MachCSL.wordToBytes4 (MachCSL.bytesToWord4 ((bs.drop (4 * 0)).take 4))
      ++ bs.drop (4 * 0 + 4) = bs := by
  have h4 : ((bs.drop (4 * 0)).take 4).length = 4 := by
    simp only [Nat.mul_zero, List.drop_zero, List.length_take]; omega
  rw [MachCSL.wordToBytes4_bytesToWord4 _ h4]
  simp

/-! ## The buffer's header word -/

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]

/-- `b->data` is four-byte aligned. -/
theorem il_bufdata_align (kk : Nat) (hkk : kk < NBUF) : (aBufData (bnode kk)).toNat % 4 = 0 := by
  have h := bufData_toNat kk 0 hkk (by unfold BSIZE; omega)
  have hz : aBufData (bnode kk) + BitVec.ofNat 64 0 = aBufData (bnode kk) := by simp
  rw [hz] at h
  have hbc : KernelSyms.«bcache» = 0x80018278 := rfl
  rw [hbc] at h
  omega

theorem il_hdr_addr (kk : Nat) :
    aBufData (bnode kk) + BitVec.ofNat 64 (4 * 0) = bnode kk + 88#64 := by
  unfold aBufData bOffData
  simp

/-- The header's `n` word, at the address `c.lw a2,88(a0)` computes. -/
theorem il_hdr_acc (kk : Nat) (hkk : kk < NBUF) (bs : List (BitVec 8)) (hl : 4 ≤ bs.length) :
    byteBuf (GF := GF) (aBufData (bnode kk)) (DFrac.own 1) bs ⊢
      wordPointsTo (bnode kk + 88#64) 4 (DFrac.own 1)
        (MachCSL.bytesToWord4 ((bs.drop (4 * 0)).take 4)) ∗
      (∀ w' : BitVec 32, wordPointsTo (bnode kk + 88#64) 4 (DFrac.own 1) w' -∗
        byteBuf (aBufData (bnode kk)) (DFrac.own 1)
          (bs.take (4 * 0) ++ MachCSL.wordToBytes4 w' ++ bs.drop (4 * 0 + 4))) := by
  have h := byteBuf_word4_at (GF := GF) (aBufData (bnode kk)) bs 0 (by omega)
    (il_bufdata_align kk hkk)
  rw [il_hdr_addr kk] at h
  exact h

end

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
variable [BcacheG GF] [SleepLockG GF] [DiskG GF] [FsBlocksG GF] [CurCtx]

/-- Open the held buffer at its data bytes (Rocq's `bio_locked` unfold). -/
theorem il_hold_bytes (γ : BcacheNames) (V : BioView GF) (kk : Nat) (pidv dev bno : BitVec 32)
    (bs bsd : List (BitVec 8)) :
    bufHold0 (GF := GF) γ V kk pidv dev bno bs bsd ⊢
      ⌜kk < NBUF ∧ bno.toNat ∈ V.cov ∧ dev = V.dev ∧ bs.length = BSIZE ∧ bsd.length = BSIZE⌝ ∗
      byteBuf (aBufData (bnode kk)) (DFrac.own 1) bs ∗
      (∀ bs' : List (BitVec 8), ⌜bs'.length = BSIZE⌝ -∗
        byteBuf (aBufData (bnode kk)) (DFrac.own 1) bs' -∗
        bufHold0 γ V kk pidv dev bno bs' bsd) := by
  unfold bufHold0 bufOwn
  iintro ⟨%hp, Hsl, Htok, Hrt, Hhd, Hval, Hdev, ⟨%hl, Hb, Hd, Hby⟩, Hblk⟩
  isplitl []
  · ipureintro; exact hp
  isplitl [Hby]
  · iexact Hby
  iintro %bs' %hl' Hby'
  isplitl []
  · ipureintro
    exact ⟨hp.1, hp.2.1, hp.2.2.1, hl', hp.2.2.2.2⟩
  iframe Hsl Htok Hrt Hhd Hval Hdev Hblk
  isplitl []
  · ipureintro; exact hl'
  iframe Hb Hd Hby'

/-- **THE PAYLOAD HOOK, CASHED** (Rocq `ProofInitlog.v`'s `il_pay_agree`).
The travelling payload a `bread` hands back at a covered block IS the
client view's content at that block, on EITHER polarity; with the view
instantiated at the file system's (`hcl`/`hdt`, the premises every log spec
carries), that content is the block's `Xv6.fsChalf`, so the bytes agree. -/
theorem il_pay_agree (γ : BcacheNames) (γfs : FsNames)
    (V : BioView GF) (hcl : V.clean = fsMclean γfs) (hdt : V.dirty = fsMdirty γfs)
    (kk : Nat) (dev bno : BitVec 32) (b : Nat) (hb : bno.toNat = b)
    (bs bsd bsc : List (BitVec 8)) (d : Bool) :
    bioPay (GF := GF) γ V kk dev bno bs bsd d ⊢ fsChalf γfs b bsc -∗ ⌜bs = bsc⌝ := by
  subst hb
  unfold bioPay
  cases d with
  | false =>
    simp only [Bool.false_eq_true, if_false, hcl]
    iintro ⟨Hm, %he⟩ Hc
    ihave %h := fsChalf_mclean_agree γfs bno.toNat bsc bs $$ [Hc Hm]
    case' _ => iframe Hc Hm
    ipureintro; exact h
  | true =>
    simp only [if_true, hdt]
    iintro ⟨Hm, Hr⟩ Hc
    ihave %h := fsChalf_mdirty_agree γfs bno.toNat bsc bs $$ [Hc Hm]
    case' _ => iframe Hc Hm
    ipureintro; exact h

end

/-! ## The five callees, at their call sites -/

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]

set_option maxHeartbeats 1000000 in
/-- `initlock`'s contract as a rule, with the lock pointer named (the name
pointer travels as `k'.regs 11#5`: this port's lock predicate does not read
the string, so the literal never has to be relocated). -/
theorem il_initlock_call (IL : INITLOCK) (c : CPU) (k' : KCtx)
    (vlock : BitVec 32) (vname vcpu : BitVec 64) (hK' : 2 ≤ k'.avail)
    (lk : BitVec 64) (h10 : k'.regs 10#5 = lk) :
    kctx c k' ∗ pcIs c KA.«initlock» ∗
    kmapId lk ∗ kmapId (lk + 16#64) ∗
    wordPointsTo lk 4 (DFrac.own 1) vlock ∗
    wordPointsTo (lk + 8#64) 8 (DFrac.own 1) vname ∗
    wordPointsTo (lk + 16#64) 8 (DFrac.own 1) vcpu ∗
    wpNext k'.sie k'.proc c (fun cpu' => iprop(∀ R' : RegMap,
      kctx cpu' (k'.withRegs R') -∗ pcIs cpu' (jumpPc (k'.regs 1#5)) -∗
      wordPointsTo (lk + 8#64) 8 (DFrac.own 1) (k'.regs 11#5) -∗
      lkFresh lk -∗ ⌜calleeSaved k'.regs R'⌝ -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  have h := IL.wp_initlock (hlc := hlc) (GF := GF) c k' vlock vname vcpu hK'
  unfold wp_initlock_body at h
  simp only [initlockAddr, h10] at h
  exact h

end

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
variable [BcacheG GF] [SleepLockG GF] [DiskG GF] [FsBlocksG GF] [LogG GF] [CurCtx]

set_option maxHeartbeats 2000000 in
/-- `install_trans(1)` AT THE EMPTY WRITE SET: the recovering arm with
`log.lh.n = 0`, so the loop is dead, the logged view and the pin authority
do not move, and the two slot units come straight back. -/
theorem il_install_trans (IT : INSTALL_TRANS) (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (c : CPU) (k' : KCtx) (γl : GName) (γb : BcacheNames) (V : BioView GF) (γdl : GName)
    (γfs : FsNames) (pd pav pu : BitVec 64) (j : Nat) (logstart : Nat) (dev : BitVec 32)
    (L : BlockMap) (D : RegMapF Bool) (pidv : BitVec 32) (dqp : DFrac)
    (homeL : List Nat) (Xv : Nat → List (BitVec 8)) (Xexc : List Nat)
    (pj : BitVec 64) (hpj : k'.proc = pj)
    (hj : j < NPROC) (hproc : k'.proc = procAddr j) (hK : installTransSlots ≤ k'.avail)
    (hsie : k'.sie = false) (hnoff : k'.noff = 0) (hlocks : k'.locks = [])
    (htier : k'.tier = KTier.kpt)
    (hgeom : logGeomOk V.cov logstart) (hdev : dev = V.dev)
    (hcl : V.clean = fsMclean γfs) (hdt : V.dirty = fsMdirty γfs)
    (ha0 : k'.regs 10#5 = 1#64) (hpd : descPageRw pd) :
    kctx c k' ∗ pcIs c KA.«install_trans» ∗ procsInv Γ ∗
    trapCsrs c ∗ cpuClaim c pj ∗ intrRes c ∗
    bioCtx γl γb V ∗ diskCaps V.gd γdl pd pav pu ∗ panicEnv ∗
    logFrozen logstart dev ∗
    fsBytesInv γfs.bytes γfs.cache γfs.exc homeL Xv ∗
    wordPointsTo (pPid pj) 4 dqp pidv ∗
    wordPointsTo lhNAddr 4 (DFrac.own 1) 0#32 ∗
    excOwn γfs.exc Xexc ∗
    fsCacheAuth γfs L ∗ fsDirtyAuth γfs D ∗ bslots γb 2 ∗
    wpNext true pj c (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap),
      ⌜calleeSaved k'.regs R'⌝ -∗
      kctx cpu' ((k'.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k'.regs 1#5)) -∗
      trapCsrs cpu' -∗ cpuClaim cpu' pj -∗ intrRes cpu' -∗
      wordPointsTo (pPid pj) 4 dqp pidv -∗
      wordPointsTo lhNAddr 4 (DFrac.own 1) 0#32 -∗
      excOwn γfs.exc Xexc -∗
      fsCacheAuth γfs L -∗ fsDirtyAuth γfs D -∗ bslots γb 2 -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  subst hpj
  have h := IT.wp_install_trans (hlc := hlc) (GF := GF) Γ c k' γl γb V γdl γfs pd pav pu j
    logstart dev true 0 ([] : List (BitVec 32)) (fun _ => List.replicate BSIZE 0#8) L D pidv dqp
    homeL Xv Xexc
    hj hproc hK hsie hnoff hlocks htier hgeom hdev hcl hdt
    (by simp only [if_true]; exact ha0)
    ⟨rfl, by unfold LOGBLOCKS; omega⟩
    (by intro i k'' v v' hv; simp at hv)
    (by intro w hw; exact absurd hw List.not_mem_nil)
    (by intro i; simp)
    (by intro hb; exact absurd hb (by simp))
    (by intro _ w hw; exact absurd hw List.not_mem_nil)
    (by intro _ i w hw; simp at hw)
    hpd
  unfold wp_install_trans_body at h
  simp only [installTransAddr, if_true, itRecL_nil, Nat.add_zero, List.map_nil,
    excDelMany_nil] at h
  iintro ⟨Hk, Hpc, #Hpi, Htc, Hcl, Hir, #Hbc, #Hdc, #Hpe, #Hfr, #Hbinv, Hpid, HlhN, Hexc,
    HL, HD, Hsl, Hnext⟩
  iapply h
  iframe Hk Hpc Hpi Htc Hcl Hir Hbc Hdc Hpe Hfr Hpid Hbinv
  isplitl [HlhN]
  · iexact HlhN
  isplitr [Hexc HL HD Hsl Hnext]
  · iapply BigSepL.bigSepL_nil.2; iempintro
  iframe Hexc HL HD
  isplitr [Hsl Hnext]
  · iapply BigSepL.bigSepL_nil.2; iempintro
  iframe Hsl
  iapply wpNext_intro_pin
  iintro %cpu2 %hp2 %spie %spp %R' %hcs Hk Hpc Htc Hcl Hir Hpid HlhN - Hexc HL HD - Hsl
  ihave Hn := wpNext_at true k'.proc c cpu2 _ hp2 $$ Hnext
  iapply Hn $$ %spie %spp %R' %hcs Hk Hpc Htc Hcl Hir Hpid HlhN Hexc HL HD Hsl

set_option maxHeartbeats 2000000 in
/-- `write_head()` AT THE EMPTY WRITE SET. -/
theorem il_write_head (WH : WRITE_HEAD) (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (c : CPU) (k' : KCtx) (γl : GName) (γb : BcacheNames) (V : BioView GF) (γdl : GName)
    (γfs : FsNames) (pd pav pu : BitVec 64) (j : Nat) (logstart : Nat) (dev : BitVec 32)
    (L : BlockMap) (pidv : BitVec 32) (dqp : DFrac)
    (pj : BitVec 64) (hpj : k'.proc = pj)
    (hj : j < NPROC) (hproc : k'.proc = procAddr j) (hK : writeHeadSlots ≤ k'.avail)
    (hsie : k'.sie = false) (hnoff : k'.noff = 0) (hlocks : k'.locks = [])
    (htier : k'.tier = KTier.kpt)
    (hgeom : logGeomOk V.cov logstart) (hdev : dev = V.dev)
    (hcl : V.clean = fsMclean γfs) (hdt : V.dirty = fsMdirty γfs) (hpd : descPageRw pd) :
    kctx c k' ∗ pcIs c KA.«write_head» ∗ procsInv Γ ∗
    trapCsrs c ∗ cpuClaim c pj ∗ intrRes c ∗
    bioCtx γl γb V ∗ diskCaps V.gd γdl pd pav pu ∗ panicEnv ∗
    logFrozen logstart dev ∗
    wordPointsTo (pPid pj) 4 dqp pidv ∗
    wordPointsTo lhNAddr 4 (DFrac.own 1) 0#32 ∗
    fsCacheAuth γfs L ∗ (∃ bsh : List (BitVec 8), fsChalf γfs (logHdrBno logstart) bsh) ∗
    bslot γb ∗
    wpNext true pj c (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap)
        (bs' : List (BitVec 8)),
      ⌜calleeSaved k'.regs R'⌝ -∗
      kctx cpu' ((k'.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k'.regs 1#5)) -∗
      trapCsrs cpu' -∗ cpuClaim cpu' pj -∗ intrRes cpu' -∗
      wordPointsTo (pPid pj) 4 dqp pidv -∗
      wordPointsTo lhNAddr 4 (DFrac.own 1) 0#32 -∗
      fsCacheAuth γfs (PartialMap.insert L (logHdrBno logstart) bs') -∗
      fsChalf γfs (logHdrBno logstart) bs' -∗ bslot γb -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  subst hpj
  have h := WH.wp_write_head (hlc := hlc) (GF := GF) Γ c k' γl γb V γdl γfs pd pav pu j
    logstart dev 0 ([] : List (BitVec 32)) L pidv dqp
    hj hproc hK hsie hnoff hlocks htier hgeom hdev hcl hdt
    ⟨rfl, by unfold LOGBLOCKS; omega⟩ hpd
  unfold wp_write_head_body at h
  simp only [writeHeadAddr] at h
  iintro ⟨Hk, Hpc, #Hpi, Htc, Hcl, Hir, #Hbc, #Hdc, #Hpe, #Hfr, Hpid, HlhN, HL, Hch, Hsl,
    Hnext⟩
  iapply h
  iframe Hk Hpc Hpi Htc Hcl Hir Hbc Hdc Hpe Hfr Hpid
  isplitl [HlhN]
  · iexact HlhN
  isplitr [HL Hch Hsl Hnext]
  · iapply BigSepL.bigSepL_nil.2; iempintro
  iframe HL Hch Hsl
  iapply wpNext_intro_pin
  iintro %cpu2 %hp2 %spie %spp %R' %bs' %hcs Hk Hpc Htc Hcl Hir Hpid HlhN - HL Hch %hbs Hsl
  ihave Hn := wpNext_at true k'.proc c cpu2 _ hp2 $$ Hnext
  iapply Hn $$ %spie %spp %R' %bs' %hcs Hk Hpc Htc Hcl Hir Hpid HlhN HL Hch Hsl

end

/-! ## The slot pool, split and rejoined -/

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
variable [BcacheG GF] [DiskG GF] [CurCtx]

/-- The stocked pool: the batch's thirty-two plus `initlog`'s working
pair. -/
theorem il_slots_split (γ : BcacheNames) :
    bslots (GF := GF) γ ((LOGBLOCKS + 2) + 2) ⊢
      bslot γ ∗ bslot γ ∗ bslots γ (LOGBLOCKS + 2) := by
  have h : (LOGBLOCKS + 2) + 2 = ((LOGBLOCKS + 2) + 1) + 1 := by omega
  rw [h]
  iintro H
  icases bslots_uncons γ ((LOGBLOCKS + 2) + 1) $$ H with ⟨H1, H2⟩
  icases bslots_uncons γ (LOGBLOCKS + 2) $$ H2 with ⟨H3, H4⟩
  iframe H1 H3 H4

theorem il_slots_join2 (γ : BcacheNames) : bslot (GF := GF) γ ∗ bslot γ ⊢ bslots γ 2 :=
  bslots_cons γ 1

theorem il_slots_split2 (γ : BcacheNames) : bslots (GF := GF) γ 2 ⊢ bslot γ ∗ bslot γ :=
  bslots_uncons γ 1

end

/-! ## The constructor's ghost step, the epilogue and the return -/

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
variable [BcacheG GF] [SleepLockG GF] [DiskG GF] [FsBlocksG GF] [LogG GF] [CurCtx]

set_option maxHeartbeats 8000000 in
/-- From `write_head`'s return at `+0x74`: assemble `Xv6.logResAt` out of
the raw cells and the block-view material (`Xv6/LogBoot.lean`), SEAL the
"log" spinlock over it (`MachCSL.kctx_newlock`), run the epilogue and hand
the caller back `Xv6.logCtx`. -/
theorem il_seal (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu c : CPU) (k : KCtx) (spie1 spp1 : Bool) (R : RegMap)
    (γ : LogNames) (γb : BcacheNames) (γfs : FsNames) (V : BioView GF)
    (logstart : Nat) (dev pidv vNc : BitVec 32) (sb : BitVec 64) (dqp dqs : DFrac)
    (L : BlockMap) (D : RegMapF Bool) (bsh : List (BitVec 8))
    (hK : 6 ≤ k.avail) (hsie : k.sie = false)
    (hR2 : R 2#5 = k.regs 2#5 + 0xFFFFFFFFFFFFFFD0#64)
    (p20 : R 20#5 = k.regs 20#5) (p21 : R 21#5 = k.regs 21#5) (p22 : R 22#5 = k.regs 22#5)
    (p23 : R 23#5 = k.regs 23#5) (p24 : R 24#5 = k.regs 24#5) (p25 : R 25#5 = k.regs 25#5)
    (p26 : R 26#5 = k.regs 26#5) (p27 : R 27#5 = k.regs 27#5)
    (hpin : true = false ∨ k.proc = 0#64 → c = cpu) :
    kctx c (((k.withSpie spie1 spp1).pushed 6).withRegs R) ∗
    pcIs c (KA.«initlog» + 0x74#64) ∗
    trapCsrs c ∗ cpuClaim c k.proc ∗ intrRes c ∗
    frame6s3 (k.regs 2#5) (k.regs 1#5) (k.regs 8#5) (k.regs 9#5) (k.regs 18#5) (k.regs 19#5) ∗
    wordPointsTo (pPid k.proc) 4 dqp pidv ∗
    wordPointsTo (sb + 20#64) 4 dqs (BitVec.ofNat 32 logstart) ∗
    logFrozen logstart dev ∗ fsBytesAnyAt γfs (fsHomeList V.cov logstart) ∗
    kmapId logAddr ∗ kmapId (logAddr + 16#64) ∗ lkFresh logAddr ∗
    logFreeTok γ ∗
    wordPointsTo lOut 4 (DFrac.own 1) 0#32 ∗
    wordPointsTo lCmt 4 (DFrac.own 1) 0#32 ∗
    wordPointsTo lNcommit 4 (DFrac.own 1) vNc ∗
    wordPointsTo lhNAddr 4 (DFrac.own 1) 0#32 ∗
    ([∗list] i ∈ List.range LOGBLOCKS, ∃ w : BitVec 32,
       wordPointsTo (lhBlock i) 4 (DFrac.own 1) w) ∗
    fsCacheAuth γfs L ∗ fsDirtyAuth γfs D ∗
    ([∗list] b ∈ V.cov.toList, fsDirtyHalf γfs b false) ∗
    fsChalf γfs (logHdrBno logstart) bsh ∗
    ([∗list] i ∈ List.range LOGBLOCKS, ∃ bs : List (BitVec 8),
       fsChalf γfs (logSlotBno logstart i) bs) ∗
    bslots γb (LOGBLOCKS + 2) ∗ bslots γb 2 ∗
    wpNext true k.proc cpu (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap) (γlk : GName),
      ⌜calleeSaved k.regs R'⌝ -∗
      kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
      trapCsrs cpu' -∗ cpuClaim cpu' k.proc -∗ intrRes cpu' -∗
      wordPointsTo (pPid k.proc) 4 dqp pidv -∗
      wordPointsTo (sb + 20#64) 4 dqs (BitVec.ofNat 32 logstart) -∗
      bslots γb 2 -∗
      logCtx (γ.withLk γlk) γb γfs V.cov logstart dev -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  iintro ⟨Hk, Hpc, Htc, Hcl, Hir, Hframe, Hpid, Hsb, #Hfroz, #Hrow, #Hm1, #Hm2, Hfresh, Htok,
    Hout, Hcmt, Hnc, HlhN, Hjunk, HL, HD, Hd, Hhdr, Hslots, Hpool, Hwork, Hnext⟩
  icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
  -- the boot pack
  ihave Hbatch := logStateAt_boot γb γfs V.cov logstart (opPending (∅ : RegMapF OpEntry))
      L D bsh $$ [HlhN Hjunk HL HD Hd Hhdr Hslots Hpool]
  case' _ => iframe
  ihave Hres := logResAt_boot γ γb γfs V.cov logstart vNc
      $$ [Hout Hcmt Hnc Htok Hbatch]
  case' _ => iframe
  -- the seal
  iapply wpLoop_fupd
  imod (kctx_newlock c _ logAddr "log" (logResAt γ γb γfs V.cov logstart))
    $$ [Hk Hres Hfresh Hm1 Hm2] with ⟨Hk, %γlk, #Hlk⟩
  · iframe Hm1 Hm2
    iframe
  imodintro
  ihave #Hctx := logCtx_mk γ γlk γb γfs V.cov logstart dev $$ [Hlk Hfroz Hrow]
  case' _ => iframe Hlk Hfroz Hrow
  -- the epilogue
  ihave Hframe := (show frame6s3 (GF := GF) (k.regs 2#5) (k.regs 1#5) (k.regs 8#5)
        (k.regs 9#5) (k.regs 18#5) (k.regs 19#5) ⊢
      frame6s3 ((k.withSpie spie1 spp1).regs 2#5) ((k.withSpie spie1 spp1).regs 1#5)
        ((k.withSpie spie1 spp1).regs 8#5) ((k.withSpie spie1 spp1).regs 9#5)
        ((k.withSpie spie1 spp1).regs 18#5) ((k.withSpie spie1 spp1).regs 19#5) from by
    simp only [KCtx.withSpie_regs]; iintro H; iexact H) $$ Hframe
  iapply (wp_epilogue6s3_gen c (k.withSpie spie1 spp1) (KA.«initlog» + 0x74#64)
      (by simp only [KCtx.withSpie_avail]; exact hK) R
      (by simp only [KCtx.withSpie_regs]; exact hR2)
      ((k.withSpie spie1 spp1).regs 1#5) ((k.withSpie spie1 spp1).regs 8#5)
      ((k.withSpie spie1 spp1).regs 9#5) ((k.withSpie spie1 spp1).regs 18#5)
      ((k.withSpie spie1 spp1).regs 19#5))
    $$ [- $Hk $Hpc $Hframe]
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm_g
  iframe
  inext
  iapply wpNext_intro_pin
  iintro %c2 %hp2 Hk Hpc
  have hc2 : c2 = c := hp2 (Or.inl (by k_norm_g; exact hsie))
  subst hc2
  k_norm_g
  ihave HΦ := wpNext_at true k.proc cpu c2 _ hpin $$ Hnext
  iapply HΦ $$ %spie1 %spp1 %_ %γlk [] Hk Hpc [Htc] [Hcl] [Hir] [Hpid] [Hsb] [Hwork] [Hctx]
  · ipureintro
    exact calleeSaved_epi6s3 k.regs R p20 p21 p22 p23 p24 p25 p26 p27
  · iexact Htc
  · iexact Hcl
  · iexact Hir
  · iexact Hpid
  · iexact Hsb
  · iexact Hwork
  · iexact Hctx

end

/-! ## The function -/

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

set_option maxHeartbeats 32000000 in
theorem initlog_proof
    (IL : INITLOCK) (BD : BREAD) (BE : BRELSE) (IT : INSTALL_TRANS) (WH : WRITE_HEAD) :
    INITLOG := ⟨
  fun {hlc GF} _ _ _ _ _ _ _ _ Γ _ cpu k γ γl γb V γdl γfs pd pav pu j logstart dev sb
    bsHdr L D vlock vname vcpu vStart vDev vNc vN pidv dqp dqs
    hj hproc hK hsie hnoff hlocks htier hgeom hdev hcl hdt ha0 ha1
    hhdrLen hhdrNodup hhdrHome hhdr0 hpinned hpd => by
  have hcovhdr : logstart ∈ V.cov := hgeom.2 logstart (logRegion_hdr logstart)
  have hls31 : logstart < 2 ^ 31 := (hgeom.1 logstart hcovhdr).2
  have hbnoNat : (BitVec.ofNat 32 logstart).toNat = logstart := by
    simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
  have hK6 : 6 ≤ k.avail := by
    unfold initlogSlots installTransSlots breadSlots panicSlots at hK; omega
  have hww : ∀ (K : KCtx) (a b c d : Bool), (K.withSpie a b).withSpie c d = K.withSpie c d :=
    fun _ _ _ _ _ => rfl
  have hpsw : ∀ (K : KCtx) (m : Nat) (a b : Bool),
      (K.pushed m).withSpie a b = (K.withSpie a b).pushed m := fun _ _ _ _ => rfl
  unfold wp_initlog_body
  simp only [initlogAddr]
  iintro ⟨Hk, Hpc, #Hpi, Htc, Hcl, Hir, #Hbc, #Hdc, #Hpe, Hpid, #Hat, Hexc, Htok, Hsb,
    #Hm1, #Hm2, Hlock, Hname, Hcpu, HlStart, HlDev, Hout, Hcmt, Hnc, HlhN, Hjunk, HL, HD, Hd,
    Hhdr, Hslots, Hpool0, Hnext⟩
  icases (show fsBytesAt (GF := GF) γfs (fsHomeList V.cov logstart) ⊢
      ∃ Xv : Nat → List (BitVec 8),
        fsBytesInv γfs.bytes γfs.cache γfs.exc (fsHomeList V.cov logstart) Xv from by
    unfold fsBytesAt; iintro H; iexact H) $$ Hat with ⟨%Xv, #Hbinv⟩
  -- THE EXCEPTION SET IS EMPTY at a clean header (see the `hhdr0` note in
  -- `Xv6/SpecInitlog.lean`), so the handle the recovering install hands back
  -- can be SEALED, which is what builds `Xv6.logCtx`'s byte-view row.
  ihave Hexc := (show excOwn (GF := GF) γfs.exc (hdrDec bsHdr).2 ⊢
      excOwn γfs.exc ([] : List Nat) from by
    rw [show (hdrDec bsHdr).2 = ([] : List Nat) from by rw [hdrDec_zero bsHdr hhdr0]]) $$ Hexc
  icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
  icases il_slots_split γb $$ Hpool0 with ⟨Hu1, Hu2, Hpool⟩
  -- ===== the prologue =====
  iapply (wp_prologue6s3_gen cpu k KA.«initlog» hK6)
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm_g
  iframe
  inext
  iapply wpNext_intro_pin
  iintro %c1 %hp1 Hk Hpc Hframe
  have hc1 : c1 = cpu := hp1 (Or.inl hsie)
  subst hc1
  -- +0x0e  c.mv s1,a0 ; +0x10  c.mv s3,a1
  k_step (wp_s_add c1 _ (KA.«initlog» + 0xe#64) true 9#5 0#5 10#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [ha0]
  iintro Hk Hpc
  k_step (wp_s_add c1 _ (KA.«initlog» + 0x10#64) true 19#5 0#5 11#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [ha1]
  iintro Hk Hpc
  -- +0x12/+0x16  s2 = &log
  k_step (wp_s_auipc c1 _ (KA.«initlog» + 0x12#64) false 0x1e#20 18#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step (wp_s_addi c1 _ (KA.«initlog» + 0x16#64) false 1806#12 18#5 18#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [il_log_addr]
  iintro Hk Hpc
  -- +0x1a/+0x1e  a1 = "log"
  k_step (wp_s_auipc c1 _ (KA.«initlog» + 0x1a#64) false 4#20 11#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step (wp_s_addi c1 _ (KA.«initlog» + 0x1e#64) false 2086#12 11#5 11#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  -- +0x22  c.mv a0,s2 ; +0x24  jal ra,initlock
  k_step (wp_s_add c1 _ (KA.«initlog» + 0x22#64) true 10#5 0#5 18#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step (wp_s_jal c1 _ (KA.«initlog» + 0x24#64) false 2084564#21 1#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [il_br_initlock]
  iintro Hk Hpc
  iapply (il_initlock_call IL c1 _ vlock vname vcpu ?iK logAddr ?ia0)
    $$ [- $Hk $Hpc $Hm1 $Hm2 $Hlock $Hname $Hcpu]
  rotate_right 1
  k_norm_g [il_ret_28]
  iframe #
  case iK =>
    k_norm_g
    unfold initlogSlots installTransSlots breadSlots panicSlots at hK
    omega
  case ia0 => k_norm_g
  -- ===== back from initlock =====
  iapply wpNext_intro_pin
  iintro %c2 %hp2 %R1 Hk Hpc Hname Hfresh %hcs1
  have hc2 : c2 = c1 := hp2 (Or.inl (by k_norm_g; exact hsie))
  subst hc2
  k_norm_g [il_ret_28]
  unfold calleeSaved at hcs1
  k_norm_g at hcs1
  obtain ⟨a2', a8', a9', a18', a19', a20', a21', a22', a23', a24', a25', a26', a27'⟩ := hcs1
  -- +0x28  lw a1,20(s3)
  k_step (wp_s_lw c2 _ (KA.«initlog» + 0x28#64) false 20#12 11#5 19#5 (by decide) (by decide)
      dqs (BitVec.ofNat 32 logstart))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [a19']
  iintro Hk Hpc Hsb
  -- +0x2c  sw a1,24(s2)
  k_step (wp_s_sw c2 _ (KA.«initlog» + 0x2c#64) false 24#12 18#5 11#5 (by decide) vStart)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    with [a18', il_lStart, il_ext_sext (BitVec.ofNat 32 logstart)]
  iintro Hk Hpc HlStart
  -- +0x30  sw s1,36(s2)
  k_step (wp_s_sw c2 _ (KA.«initlog» + 0x30#64) false 36#12 18#5 9#5 (by decide) vDev)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    with [a18', a9', il_lDev, il_ext_sext dev]
  iintro Hk Hpc HlDev
  -- the two cells are FROZEN here
  iapply wpLoop_bupd
  imod (logFrozen_mk logstart dev) $$ [HlDev HlStart] with #Hfroz
  · iframe HlDev HlStart
  imodintro
  -- +0x34  c.mv a0,s1 ; +0x36  jal ra,bread
  k_step (wp_s_add c2 _ (KA.«initlog» + 0x34#64) true 10#5 0#5 9#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [a9']
  iintro Hk Hpc
  k_step (wp_s_jal c2 _ (KA.«initlog» + 0x36#64) false 2092874#21 1#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [il_br_bread]
  iintro Hk Hpc
  iapply (bread_call BD Γ c2 _ γl γb V γdl pd pav pu j pidv dev (BitVec.ofNat 32 logstart) dqp
      k.proc (by k_norm_g) hj ?dproc ?dK ?dsie ?dnoff ?dlocks ?dtier ?dbno ?dcov hdev hpd
      ?da0 ?da1)
    $$ [- $Hk $Hpc $Hpi $Htc $Hcl $Hir $Hbc $Hdc $Hpe $Hpid $Hu1]
  rotate_right 1
  k_norm_g [il_ret_3a]
  iframe #
  case dproc => k_norm_g; exact hproc
  case dK =>
    k_norm_g
    unfold initlogSlots installTransSlots at hK
    omega
  case dsie => k_norm_g; exact hsie
  case dnoff => k_norm_g; exact hnoff
  case dlocks => k_norm_g; exact hlocks
  case dtier => k_norm_g; exact htier
  case dbno => rw [hbnoNat]; omega
  case dcov => rw [hbnoNat]; exact hcovhdr
  case da0 => k_norm_g
  case da1 => k_norm_g
  -- ===== back from bread: read_head =====
  iapply wpNext_intro_pin
  iintro %c3 %hp3 %spie3 %spp3 %R2 %kk %bs %bsd %dd %hcs2 Hk Hpc Htc Hcl Hir Hpid Hlocked
  k_norm_g [il_ret_3a, hww, hpsw]
  obtain ⟨hcsb, ha0kk⟩ := hcs2
  unfold calleeSaved at hcsb
  k_norm_g at hcsb
  obtain ⟨b2, b8, b9, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27⟩ := hcsb
  -- THE PAYLOAD HOOK, CASHED: the bread'd bytes ARE the header block's
  -- logged content, and `hhdr0` says that content decodes clean
  icases (bioLocked_split γb V kk pidv dev (BitVec.ofNat 32 logstart) bs bsd dd).1
    $$ Hlocked with ⟨Hhold, Hpay⟩
  ihave %hbseq := il_pay_agree γb γfs V hcl hdt kk dev (BitVec.ofNat 32 logstart)
      (logHdrBno logstart) hbnoNat bs bsd bsHdr dd $$ Hpay Hhdr
  have hbs0 : hdrN bs = 0 := by rw [hbseq]; exact hhdr0
  -- +0x3a  c.lw a2,88(a0) : lh.n := hb->n  ( = 0 )
  icases il_hold_bytes γb V kk pidv dev (BitVec.ofNat 32 logstart) bs bsd $$ Hhold
    with ⟨%hpure, Hby, Hhclose⟩
  obtain ⟨hkk, -, -, hlen, -⟩ := hpure
  have hlen4 : 4 ≤ bs.length := by rw [hlen]; unfold BSIZE; omega
  have hw0 : MachCSL.bytesToWord4 ((bs.drop (4 * 0)).take 4) = 0#32 :=
    il_hdrN_word bs hlen4 hbs0
  icases il_hdr_acc kk hkk bs hlen4 $$ Hby with ⟨Hword, Hwclose⟩
  ihave Hword := (show wordPointsTo (GF := GF) (bnode kk + 88#64) 4 (DFrac.own 1)
        (MachCSL.bytesToWord4 ((bs.drop (4 * 0)).take 4)) ⊢
      wordPointsTo (bnode kk + 88#64) 4 (DFrac.own 1) 0#32 from by rw [hw0]) $$ Hword
  k_step (wp_s_lw c3 _ (KA.«initlog» + 0x3a#64) true 88#12 12#5 10#5 (by decide) (by decide)
      (DFrac.own 1) 0#32)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [ha0kk, il_sext0]
  iintro Hk Hpc Hword
  ihave Hword := (show wordPointsTo (GF := GF) (bnode kk + 88#64) 4 (DFrac.own 1) 0#32 ⊢
      wordPointsTo (bnode kk + 88#64) 4 (DFrac.own 1)
        (MachCSL.bytesToWord4 ((bs.drop (4 * 0)).take 4)) from by rw [hw0]) $$ Hword
  ihave Hby := Hwclose $$ %(MachCSL.bytesToWord4 ((bs.drop (4 * 0)).take 4)) Hword
  ihave Hby := (show byteBuf (GF := GF) (aBufData (bnode kk)) (DFrac.own 1)
      (bs.take (4 * 0) ++
        MachCSL.wordToBytes4 (MachCSL.bytesToWord4 ((bs.drop (4 * 0)).take 4)) ++
        bs.drop (4 * 0 + 4)) ⊢
      byteBuf (aBufData (bnode kk)) (DFrac.own 1) bs from by
    rw [il_hdr_roundtrip bs hlen4]) $$ Hby
  ihave Hhold := Hhclose $$ %bs %hlen Hby
  ihave Hlocked := (bioLocked_split γb V kk pidv dev (BitVec.ofNat 32 logstart)
      bs bsd dd).2 $$ [Hhold Hpay]
  case' _ => iframe Hhold Hpay
  -- +0x3c  sw a2,44(s2)
  k_step (wp_s_sw c3 _ (KA.«initlog» + 0x3c#64) false 44#12 18#5 12#5 (by decide) vN)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [b18, a18', il_lhN, il_ext0]
  iintro Hk Hpc HlhN
  -- +0x40  blez a2 : TAKEN (the copy loop at +0x52 is dead at a clean header)
  k_step (wp_s_branch0 c3 _ (KA.«initlog» + 0x40#64) false 30#13 12#5 (by decide) bop.BGE)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [il_blez_zero]
  iintro Hk Hpc
  -- +0x5e  jal ra,brelse
  k_step (wp_s_jal c3 _ (KA.«initlog» + 0x5e#64) false 2093098#21 1#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [il_br_brelse]
  iintro Hk Hpc
  iapply (brelse_call BE Γ c3 _ γl γb V kk pidv dev (BitVec.ofNat 32 logstart) dqp bs bsd dd
      k.proc (by k_norm_g) ?rnoff ?rK ?rlk ?rsl ?rp ?rtier hkk ?ra0)
    $$ [- $Hk $Hpc $Hpi $Hbc $Hpid $Hlocked]
  rotate_right 1
  k_norm_g [il_ret_62]
  iframe #
  case rnoff => k_norm_g; simp only [hnoff]; omega
  case rK =>
    k_norm_g
    unfold initlogSlots installTransSlots breadSlots panicSlots brelseSlots releasesleepSlots
      wakeupSlots at *
    omega
  case rlk => k_norm_g; rw [hlocks]; simp
  case rsl => k_norm_g; rw [hlocks]; simp
  case rp => k_norm_g; rw [hlocks]; simp
  case rtier => k_norm_g; exact htier
  case ra0 => k_norm_g; exact ha0kk
  -- ===== back from brelse =====
  iapply wpNext_intro_pin
  iintro %c4 %hp4 %spie4 %spp4 %R3 %hsp4 Hk Hpc %hcs3 Hpid Hu1
  have hc4 : c4 = c3 := hp4 (Or.inl (by k_norm_g; exact hsie))
  subst hc4
  k_norm_g [il_ret_62, hww, hpsw]
  unfold calleeSaved at hcs3
  k_norm_g at hcs3
  obtain ⟨d2, d8, d9, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27⟩ := hcs3
  -- ===== install_trans(1) =====
  ihave Hs2 := il_slots_join2 γb $$ [Hu1 Hu2]
  case' _ => iframe
  k_step (wp_s_addi c4 _ (KA.«initlog» + 0x62#64) true 1#12 10#5 0#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step (wp_s_jal c4 _ (KA.«initlog» + 0x64#64) false 2096848#21 1#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [il_br_install]
  iintro Hk Hpc
  iapply (il_install_trans IT Γ c4 _ γl γb V γdl γfs pd pav pu j logstart dev L D pidv dqp
      (fsHomeList V.cov logstart) Xv ([] : List Nat)
      k.proc (by k_norm_g) hj ?tproc ?tK ?tsie ?tnoff ?tlocks ?ttier hgeom hdev hcl hdt
      ?ta0 hpd)
    $$ [- $Hk $Hpc $Hpi $Htc $Hcl $Hir $Hbc $Hdc $Hpe $Hfroz $Hbinv $Hpid $HlhN $Hexc $HL $HD
         $Hs2]
  rotate_right 1
  k_norm_g [il_ret_68]
  iframe #
  case tproc => k_norm_g; exact hproc
  case tK => k_norm_g; unfold initlogSlots at hK; omega
  case tsie => k_norm_g; exact hsie
  case tnoff => k_norm_g; exact hnoff
  case tlocks => k_norm_g; exact hlocks
  case ttier => k_norm_g; exact htier
  case ta0 => k_norm_g
  -- ===== back from install_trans =====
  iapply wpNext_intro_pin
  iintro %c5 %hp5 %spie5 %spp5 %R4 %hcs4 Hk Hpc Htc Hcl Hir Hpid HlhN Hexc HL HD Hs2
  k_norm_g [il_ret_68, hww, hpsw]
  unfold calleeSaved at hcs4
  k_norm_g at hcs4
  obtain ⟨f2, f8, f9, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27⟩ := hcs4
  -- +0x68 auipc a5,0x1e ; +0x6c sw zero,1764(a5) : log.lh.n = 0
  k_step (wp_s_auipc c5 _ (KA.«initlog» + 0x68#64) false 0x1e#20 15#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step (wp_s_sw c5 _ (KA.«initlog» + 0x6c#64) false 1764#12 15#5 0#5 (by decide) 0#32)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [il_lhn_reloc, il_ext0]
  iintro Hk Hpc HlhN
  -- +0x70 jal ra,write_head
  icases il_slots_split2 γb $$ Hs2 with ⟨Hu1, Hu2⟩
  ihave Hch := (show fsChalf (GF := GF) γfs (logHdrBno logstart) bsHdr ⊢
      ∃ bsh : List (BitVec 8), fsChalf γfs (logHdrBno logstart) bsh from by
    iintro H; iexists bsHdr; iexact H) $$ Hhdr
  k_step (wp_s_jal c5 _ (KA.«initlog» + 0x70#64) false 2096742#21 1#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [il_br_writehead]
  iintro Hk Hpc
  iapply (il_write_head WH Γ c5 _ γl γb V γdl γfs pd pav pu j logstart dev L pidv dqp
      k.proc (by k_norm_g) hj ?wproc ?wK ?wsie ?wnoff ?wlocks ?wtier hgeom hdev hcl hdt hpd)
    $$ [- $Hk $Hpc $Hpi $Htc $Hcl $Hir $Hbc $Hdc $Hpe $Hfroz $Hpid $HlhN $HL $Hch $Hu1]
  rotate_right 1
  k_norm_g [il_ret_74]
  iframe #
  case wproc => k_norm_g; exact hproc
  case wK =>
    k_norm_g
    unfold initlogSlots installTransSlots writeHeadSlots at *
    omega
  case wsie => k_norm_g; exact hsie
  case wnoff => k_norm_g; exact hnoff
  case wlocks => k_norm_g; exact hlocks
  case wtier => k_norm_g; exact htier
  -- ===== back from write_head: the seal =====
  iapply wpNext_intro_pin
  iintro %c6 %hp6 %spie6 %spp6 %R5 %bs' %hcs5 Hk Hpc Htc Hcl Hir Hpid HlhN HL Hch Hu1
  k_norm_g [il_ret_74, hww, hpsw]
  unfold calleeSaved at hcs5
  k_norm_g at hcs5
  obtain ⟨g2, g8, g9, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27⟩ := hcs5
  ihave Hs2 := il_slots_join2 γb $$ [Hu1 Hu2]
  case' _ => iframe
  -- **THE SEAL OF THE EXCEPTION SET** (Rocq's `exc_seal`): recovery is over,
  -- the handle is spent at `[]`, and the discarded element is the permanent
  -- certificate `Xv6.logCtx` carries.
  iapply wpLoop_bupd
  ihave Hsealed := excSeal (GF := GF) γfs.exc $$ Hexc
  imod Hsealed with #Hseal
  imodintro
  ihave #Hrow := fsBytesAnyAt_of γfs (fsHomeList V.cov logstart) $$ Hat Hseal
  iapply (il_seal Γ c2 c6 k spie6 spp6 R5 γ γb γfs V logstart dev pidv vNc sb dqp dqs
      (PartialMap.insert L (logHdrBno logstart) bs') D bs' hK6 hsie
      ((g2.trans f2).trans ((d2.trans b2).trans a2'))
      ((g20.trans f20).trans ((d20.trans b20).trans a20'))
      ((g21.trans f21).trans ((d21.trans b21).trans a21'))
      ((g22.trans f22).trans ((d22.trans b22).trans a22'))
      ((g23.trans f23).trans ((d23.trans b23).trans a23'))
      ((g24.trans f24).trans ((d24.trans b24).trans a24'))
      ((g25.trans f25).trans ((d25.trans b25).trans a25'))
      ((g26.trans f26).trans ((d26.trans b26).trans a26'))
      ((g27.trans f27).trans ((d27.trans b27).trans a27'))
      (fun hh => (hp6 hh).trans ((hp5 hh).trans (hp3 hh))))
    $$ [- $Hk $Hpc $Htc $Hcl $Hir $Hframe $Hpid $Hsb $Hfroz $Hrow $Hm1 $Hm2 $Hfresh $Htok
         $Hout $Hcmt $Hnc $HlhN $Hjunk $HL $HD $Hd $Hch $Hslots $Hpool $Hs2 $Hnext]
  k_norm_g
  try (iframe #)⟩

end

end Xv6
