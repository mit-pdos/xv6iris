/-
Proof of `end_op`'s specification (`Xv6.END_OP`), given the interfaces of
`acquire`, `release`, `wakeup`, `bread`, `bwrite`, `brelse`, `memmove`,
`write_head` and `install_trans`.  A port of Rocq `ProofEndOp.v` against
the Lean image.

    void end_op(void) {
      int do_commit = 0;
      acquire(&log.lock);
      log.outstanding -= 1;
      if (log.committing) panic("log.committing");
      if (log.outstanding == 0) { do_commit = 1; log.committing = 1; }
      else wakeup(&log);
      release(&log.lock);
      if (do_commit) {
        commit();                       // INLINED
        acquire(&log.lock);
        log.committing = 0;
        log.ncommit++;
        wakeup(&log);
        release(&log.lock);
      }
    }

Structure (98 instructions, `+0x00 .. +0x120`), block by block:

* `+0x00` the eight-slot prologue (`ra`, `s0`, `s1`, `s2` saved; `s3`,
  `s4`, `s5` SHRINK-WRAPPED onto the two arms that clobber them);
* `+0x14` `acquire`, then the ACCOUNTING critical section `+0x1a .. +0x38`:
  `out -= 1`, the `committing` test, the `out == 0` test, `committing := 1`
  (or `wakeup`) and `release`;
* `+0x3c` the `lh.n > 0` test: at `n = 0` the commit is a no-op and control
  falls into the tail;
* `+0xb4 .. +0x100` the inlined `write_log` copy loop (Löb);
* `+0x104 .. +0x120` `write_head`, `install_trans(0)`, `lh.n := 0`,
  `write_head`, and the `c.j` back into the tail;
* `+0x42 .. +0x66` the tail: re-acquire, `committing := 0`, `ncommit++`,
  `wakeup`, DEPOSIT the emptied batch, `release`;
* `+0x7a` the non-committer's arm (`wakeup`, `release`), and `+0x92` the
  shared epilogue.

THE PANIC ARM AT `+0x68` IS DEAD.  The token in hand is a live ledger
entry, so `out ≥ 1`, and `Xv6.logResAt`'s `⌜cmt = true → out = 0⌝` then
forces `cmt = false`: the `bnez a5` at `+0x24` is never taken, and
`unreachable` is never reached.

THE GHOST STORY, in one paragraph.  Under the lock the op retires
(`Xv6.logEndStep` and `Xv6.logTxRetire`, one row each).  On the LAST-OUT
path `committing` flips to `1` and `Xv6.logStateAt` comes OUT of the
payload linearly -- that is what licenses running the commit with no lock
held.  The copy loop moves each log slot's client half to the home block's
bytes (read off the CACHE AUTHORITY, which is the only handle a committer
has on a home block); `write_head` lays the header down; `install_trans(0)`
installs and unpins; `lh.n := 0` empties the batch; the second
`write_head` makes the on-disk header clean again.  At the re-acquire the
epoch BUMPS (`Xv6.logEpochBump`), which is what revokes every `loggedAt`
witness of the batch just committed, and the emptied batch is deposited.
-/
import Xv6.EndOpDefs
import Xv6.SpecWriteHead
import Xv6.SpecInstallTrans
import Xv6.SpecWakeup
import Xv6.SpecAcquire
import Xv6.SpecRelease
import Xv6.SpecBread
import Xv6.SpecBwrite
import Xv6.SpecBrelse
import Xv6.SpecMemmove

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D LeanRV64D.Functions

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The nine call sites -/

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
variable [BcacheG GF] [SleepLockG GF] [DiskG GF] [FsBlocksG GF] [LogG GF] [CurCtx]

theorem eo_ac (AC : ACQUIRE) (c : CPU) (k' : KCtx) (γ : LogNames) (γb : BcacheNames)
    (γfs : FsNames) (cov : Std.ExtTreeSet Nat compare) (ls : Nat) (dev : BitVec 32)
    (ha0 : k'.regs 10#5 = logAddr)
    (hnoff : k'.noff + 1 < 2 ^ 31) (hK : 10 ≤ k'.avail) (hs : "log" ∉ k'.locks) :
    kctx c k' ∗ pcIs c KA.«acquire» ∗ logCtx γ γb γfs cov ls dev ∗
    wpNext k'.sie k'.proc c (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap),
      ⌜k'.sie = false → spie = k'.spie ∧ spp = k'.spp⌝ -∗
      kctx cpu' (((k'.pushOffAt spie spp).withRegs R').withLocks ("log" :: k'.locks)) -∗
      pcIs cpu' (jumpPc (k'.regs 1#5)) -∗ ⌜calleeSaved k'.regs R'⌝ -∗
      locked γ.lk cpu' -∗ logResAt γ γb γfs cov ls curCtx -∗ (∃ K : Nat, viewLb cpu' K) -∗
      sieArm cpu' k'.sie k'.proc -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  have h := AC.wp_acquire (hlc := hlc) (GF := GF) c k' γ.lk "log"
    (logResAt γ γb γfs cov ls) hnoff hK hs
  unfold wp_acquire_body at h
  simp only [acquireAddr] at h
  rw [ha0] at h
  iintro ⟨Hk, Hpc, #Hctx, HΦ⟩
  ihave #Hlk := logCtx_lock γ γb γfs cov ls dev $$ Hctx
  iapply h
  iframe Hk Hpc Hlk HΦ

theorem eo_re (RE : RELEASE) (c : CPU) (k' : KCtx) (γ : LogNames) (γb : BcacheNames)
    (γfs : FsNames) (cov : Std.ExtTreeSet Nat compare) (ls : Nat) (dev : BitVec 32)
    (ha0 : k'.regs 10#5 = logAddr)
    (hsie : k'.sie = false) (hnoff : 1 ≤ k'.noff) (hK : 10 ≤ k'.avail)
    (hreen : false = (decide (k'.noff = 1) && k'.intena)) :
    kctx c k' ∗ pcIs c KA.«release» ∗ logCtx γ γb γfs cov ls dev ∗
    locked γ.lk c ∗ logResAt γ γb γfs cov ls curCtx ∗
    wpNext (k'.popExit false).sie k'.proc c (fun cpu' => iprop(∀ R' : RegMap,
      kctx cpu' (((k'.popExit false).withRegs R').withLocks
        (k'.locks.filter (fun x => x ≠ "log"))) -∗
      pcIs cpu' (jumpPc (k'.regs 1#5)) -∗ ⌜calleeSaved k'.regs R'⌝ -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  have h := RE.wp_release (hlc := hlc) (GF := GF) c k' γ.lk "log"
    (logResAt γ γb γfs cov ls) hsie hnoff hK false hreen (by simp)
  unfold wp_release_body at h
  simp only [releaseAddr] at h
  rw [ha0] at h
  iintro ⟨Hk, Hpc, #Hctx, Hlocked, Hpay, HΦ⟩
  ihave #Hlk := logCtx_lock γ γb γfs cov ls dev $$ Hctx
  iapply h
  iframe Hk Hpc Hlocked Hpay HΦ
  isplitl []
  · iexact Hlk
  · simp only [popArm_false]
    iempintro

theorem eo_wk (WK : WAKEUP) (Γ : SchedNames) (c : CPU) (k' : KCtx)
    (hnoff : k'.noff + 1 < 2 ^ 31) (hK : wakeupSlots ≤ k'.avail)
    (hlk : "proc" ∉ k'.locks) (htier : k'.tier = KTier.kpt) :
    kctx c k' ∗ pcIs c KA.«wakeup» ∗ procsInv Γ ∗
    wpNext k'.sie k'.proc c (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
      ⌜k'.sie = false → spie = k'.spie ∧ spp = k'.spp⌝ -∗
      kctx cpu' ((k'.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k'.regs 1#5)) -∗
      ⌜calleeSaved k'.regs R'⌝ -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  have h := WK.wp_wakeup (hlc := hlc) (GF := GF) Γ c k' hnoff hK hlk htier
  unfold wp_wakeup_body at h
  simp only [wakeupAddr] at h
  exact h

theorem eo_bread (BR : BREAD) (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (c : CPU) (k' : KCtx) (γl : GName) (γb : BcacheNames) (V : BioView GF) (γdl : GName)
    (pd pav pu : BitVec 64) (j : Nat) (pidv dev bno : BitVec 32) (dqp : DFrac)
    (pj : BitVec 64) (hpj : k'.proc = pj)
    (hj : j < NPROC) (hproc : k'.proc = procAddr j) (hK : breadSlots ≤ k'.avail)
    (hsie : k'.sie = false) (hnoff : k'.noff = 0) (hlocks : k'.locks = [])
    (htier : k'.tier = KTier.kpt)
    (hbno : bno.toNat < 2 ^ 31) (hcov : bno.toNat ∈ V.cov) (hdev : dev = V.dev)
    (hpd : descPageRw pd)
    (ha0 : k'.regs 10#5 = BitVec.signExtend 64 dev)
    (ha1 : k'.regs 11#5 = BitVec.signExtend 64 bno) :
    kctx c k' ∗ pcIs c KA.«bread» ∗ procsInv Γ ∗
    trapCsrs c ∗ cpuClaim c pj ∗ intrRes c ∗
    bioCtx γl γb V ∗ diskCaps V.gd γdl pd pav pu ∗ panicEnv ∗
    wordPointsTo (pPid pj) 4 dqp pidv ∗ bslot γb ∗
    wpNext true pj c (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap) (kk : Nat)
        (bs bsd : List (BitVec 8)) (d : Bool),
      ⌜calleeSaved k'.regs R' ∧ R' 10#5 = bnode kk⌝ -∗
      kctx cpu' ((k'.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k'.regs 1#5)) -∗
      trapCsrs cpu' -∗ cpuClaim cpu' pj -∗ intrRes cpu' -∗
      wordPointsTo (pPid pj) 4 dqp pidv -∗
      bioLocked γb V kk pidv dev bno bs bsd d -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  subst hpj
  have h := BR.wp_bread (hlc := hlc) (GF := GF) Γ c k' γl γb V γdl pd pav pu j pidv dev bno dqp
    hj hproc hK hsie hnoff hlocks htier hbno hcov hdev hpd ha0 ha1
  unfold wp_bread_body at h
  simp only [breadAddr] at h
  exact h

theorem eo_bwrite (BW : BWRITE) (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (c : CPU) (k' : KCtx) (γl : GName) (γb : BcacheNames) (V : BioView GF) (γdl : GName)
    (pd pav pu : BitVec 64) (j kk : Nat)
    (pidv dev bno : BitVec 32) (dqp : DFrac) (bs bsd : List (BitVec 8))
    (pj : BitVec 64) (hpj : k'.proc = pj)
    (hj : j < NPROC) (hproc : k'.proc = procAddr j) (hK : bwriteSlots ≤ k'.avail)
    (hsie : k'.sie = false) (hnoff : k'.noff = 0) (hlocks : k'.locks = [])
    (htier : k'.tier = KTier.kpt)
    (hkk : kk < NBUF) (ha0 : k'.regs 10#5 = bnode kk)
    (hbno : bno.toNat < 2 ^ 31) (hbsd : bsd.length = BSIZE) (hpd : descPageRw pd) :
    kctx c k' ∗ pcIs c KA.«bwrite» ∗ procsInv Γ ∗
    trapCsrs c ∗ cpuClaim c pj ∗ intrRes c ∗
    bioCtx γl γb V ∗ diskCaps V.gd γdl pd pav pu ∗
    wordPointsTo (pPid pj) 4 dqp pidv ∗
    bufHold0 γb V kk pidv dev bno bs bsd ∗
    wpNext true pj c (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap),
      ⌜calleeSaved k'.regs R'⌝ -∗
      kctx cpu' ((k'.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k'.regs 1#5)) -∗
      trapCsrs cpu' -∗ cpuClaim cpu' pj -∗ intrRes cpu' -∗
      wordPointsTo (pPid pj) 4 dqp pidv -∗
      bufHold0 γb V kk pidv dev bno bs bs -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  subst hpj
  have h := BW.wp_bwrite (hlc := hlc) (GF := GF) Γ c k' γl γb V γdl pd pav pu j kk
    pidv dev bno dqp bs bsd hj hproc hK hsie hnoff hlocks htier hkk ha0 hbno hbsd hpd
  unfold wp_bwrite_body at h
  simp only [bwriteAddr] at h
  exact h

theorem eo_brelse (BE : BRELSE) (Γ : SchedNames)
    (c : CPU) (k' : KCtx) (γl : GName) (γb : BcacheNames) (V : BioView GF) (kk : Nat)
    (pidv dev bno : BitVec 32) (dqp : DFrac) (bs bsd : List (BitVec 8)) (d : Bool)
    (pj : BitVec 64) (hpj : k'.proc = pj)
    (hnoff : k'.noff + 2 < 2 ^ 31) (hK : brelseSlots ≤ k'.avail)
    (hlk : "bcache" ∉ k'.locks) (hsl : "sleep lock" ∉ k'.locks) (hp : "proc" ∉ k'.locks)
    (htier : k'.tier = KTier.kpt)
    (hkk : kk < NBUF) (ha0 : k'.regs 10#5 = bnode kk) :
    kctx c k' ∗ pcIs c KA.«brelse» ∗ procsInv Γ ∗
    bioCtx γl γb V ∗ wordPointsTo (pPid pj) 4 dqp pidv ∗
    bioLocked γb V kk pidv dev bno bs bsd d ∗
    wpNext k'.sie pj c (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
      ⌜k'.sie = false → spie = k'.spie ∧ spp = k'.spp⌝ -∗
      kctx cpu' ((k'.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k'.regs 1#5)) -∗
      ⌜calleeSaved k'.regs R'⌝ -∗ wordPointsTo (pPid pj) 4 dqp pidv -∗
      bslot γb -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  subst hpj
  have h := BE.wp_brelse (hlc := hlc) (GF := GF) Γ c k' γl γb V kk pidv dev bno dqp bs bsd d
    hnoff hK hlk hsl hp htier hkk ha0
  unfold wp_brelse_body at h
  simp only [brelseAddr] at h
  exact h

theorem eo_memmove (MM : MEMMOVE) (c : CPU) (k' : KCtx)
    (bs olds : List (BitVec 8)) (m : Nat) (dqs : DFrac) (src dst : BitVec 64)
    (hsrc : k'.regs 11#5 = src) (hdst : k'.regs 10#5 = dst) (hK : 2 ≤ k'.avail)
    (hn : k'.regs 12#5 = BitVec.ofNat 64 m) (hn32 : m < 2 ^ 32)
    (hls : bs.length = m) (hld : olds.length = m) :
    kctx c k' ∗ pcIs c KA.«memmove» ∗
    byteBuf src dqs bs ∗ byteBuf dst (DFrac.own 1) olds ∗
    wpNext k'.sie k'.proc c (fun cpu' => iprop(∀ R' : RegMap,
      kctx cpu' (k'.withRegs R') -∗ pcIs cpu' (jumpPc (k'.regs 1#5)) -∗
      byteBuf src dqs bs -∗ byteBuf dst (DFrac.own 1) bs -∗
      ⌜calleeSaved k'.regs R' ∧ R' 10#5 = dst⌝ -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  subst hsrc; subst hdst
  have h := MM.wp_memmove (hlc := hlc) (GF := GF) c k' bs olds m dqs hK hn hn32 hls hld
  unfold wp_memmove_body at h
  simp only [memmoveAddr] at h
  exact h

theorem eo_wh (WH : WRITE_HEAD) (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (c : CPU) (k' : KCtx) (γl : GName) (γb : BcacheNames) (V : BioView GF) (γdl : GName)
    (γfs : FsNames) (pd pav pu : BitVec 64) (j logstart : Nat) (dev : BitVec 32)
    (n : Nat) (W : List (BitVec 32)) (L : BlockMap) (pidv : BitVec 32) (dqp : DFrac)
    (hj : j < NPROC) (hproc : k'.proc = procAddr j) (hK : writeHeadSlots ≤ k'.avail)
    (hsie : k'.sie = false) (hnoff : k'.noff = 0) (hlocks : k'.locks = [])
    (htier : k'.tier = KTier.kpt)
    (hgeom : logGeomOk V.cov logstart) (hdev : dev = V.dev)
    (hcl : V.clean = fsMclean γfs) (hdt : V.dirty = fsMdirty γfs)
    (hn : n = W.length ∧ n ≤ LOGBLOCKS) (hpd : descPageRw pd) :
    kctx c k' ∗ pcIs c KA.«write_head» ∗ procsInv Γ ∗
    trapCsrs c ∗ cpuClaim c k'.proc ∗ intrRes c ∗
    bioCtx γl γb V ∗ diskCaps V.gd γdl pd pav pu ∗ panicEnv ∗
    logFrozen logstart dev ∗
    wordPointsTo (pPid k'.proc) 4 dqp pidv ∗
    wordPointsTo lhNAddr 4 (DFrac.own 1) (BitVec.ofNat 32 n) ∗
    ([∗list] i ↦ w ∈ W, wordPointsTo (lhBlock i) 4 (DFrac.own 1) w) ∗
    fsCacheAuth γfs L ∗
    (∃ bsh : List (BitVec 8), fsChalf γfs (logHdrBno logstart) bsh) ∗
    bslot γb ∗
    wpNext true k'.proc c (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap)
        (bs' : List (BitVec 8)),
      ⌜calleeSaved k'.regs R'⌝ -∗
      kctx cpu' ((k'.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k'.regs 1#5)) -∗
      trapCsrs cpu' -∗ cpuClaim cpu' k'.proc -∗ intrRes cpu' -∗
      wordPointsTo (pPid k'.proc) 4 dqp pidv -∗
      wordPointsTo lhNAddr 4 (DFrac.own 1) (BitVec.ofNat 32 n) -∗
      ([∗list] i ↦ w ∈ W, wordPointsTo (lhBlock i) 4 (DFrac.own 1) w) -∗
      fsCacheAuth γfs (PartialMap.insert L (logHdrBno logstart) bs') -∗
      fsChalf γfs (logHdrBno logstart) bs' -∗
      ⌜bs'.length = BSIZE ∧ hdrN bs' = n ∧ hdrDec bs' = (n, W.map (fun w => w.toNat))⌝ -∗
      bslot γb -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  have h := WH.wp_write_head (hlc := hlc) (GF := GF) Γ c k' γl γb V γdl γfs pd pav pu j
    logstart dev n W L pidv dqp hj hproc hK hsie hnoff hlocks htier hgeom hdev hcl hdt hn hpd
  unfold wp_write_head_body at h
  simp only [writeHeadAddr] at h
  exact h

theorem eo_it (IT : INSTALL_TRANS) (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (c : CPU) (k' : KCtx) (γl : GName) (γb : BcacheNames) (V : BioView GF) (γdl : GName)
    (γfs : FsNames) (pd pav pu : BitVec 64) (j logstart : Nat) (dev : BitVec 32)
    (n : Nat) (W : List (BitVec 32)) (Lw : Nat → List (BitVec 8))
    (L : BlockMap) (D : RegMapF Bool) (pidv : BitVec 32) (dqp : DFrac)
    (hj : j < NPROC) (hproc : k'.proc = procAddr j) (hK : installTransSlots ≤ k'.avail)
    (hsie : k'.sie = false) (hnoff : k'.noff = 0) (hlocks : k'.locks = [])
    (htier : k'.tier = KTier.kpt)
    (hgeom : logGeomOk V.cov logstart) (hdev : dev = V.dev)
    (hcl : V.clean = fsMclean γfs) (hdt : V.dirty = fsMdirty γfs)
    (ha0 : k'.regs 10#5 = 0#64)
    (hn : n = W.length ∧ n ≤ LOGBLOCKS)
    (hnodup : ∀ (i k2 : Nat) (v v' : BitVec 32), W[i]? = some v → W[k2]? = some v' →
      v.toNat = v'.toNat → i = k2)
    (hhome : ∀ w ∈ W, fsHome V.cov logstart w.toNat)
    (hlen : ∀ i, (Lw i).length = BSIZE)
    (hcommit : ∀ (i : Nat) (w : BitVec 32), W[i]? = some w →
      PartialMap.get? L w.toNat = some (Lw i))
    (hpd : descPageRw pd) :
    kctx c k' ∗ pcIs c KA.«install_trans» ∗ procsInv Γ ∗
    trapCsrs c ∗ cpuClaim c k'.proc ∗ intrRes c ∗
    bioCtx γl γb V ∗ diskCaps V.gd γdl pd pav pu ∗ panicEnv ∗
    logFrozen logstart dev ∗
    wordPointsTo (pPid k'.proc) 4 dqp pidv ∗
    wordPointsTo lhNAddr 4 (DFrac.own 1) (BitVec.ofNat 32 n) ∗
    ([∗list] i ↦ w ∈ W, wordPointsTo (lhBlock i) 4 (DFrac.own 1) w) ∗
    fsCacheAuth γfs L ∗ fsDirtyAuth γfs D ∗
    ([∗list] i ↦ w ∈ W, fsChalf γfs (logSlotBno logstart i) (Lw i) ∗
       fsDirtyHalf γfs w.toNat true) ∗
    bslots γb 2 ∗
    wpNext true k'.proc c (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap),
      ⌜calleeSaved k'.regs R'⌝ -∗
      kctx cpu' ((k'.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k'.regs 1#5)) -∗
      trapCsrs cpu' -∗ cpuClaim cpu' k'.proc -∗ intrRes cpu' -∗
      wordPointsTo (pPid k'.proc) 4 dqp pidv -∗
      wordPointsTo lhNAddr 4 (DFrac.own 1) (BitVec.ofNat 32 n) -∗
      ([∗list] i ↦ w ∈ W, wordPointsTo (lhBlock i) 4 (DFrac.own 1) w) -∗
      fsCacheAuth γfs L -∗
      fsDirtyAuth γfs (dirtyClear D (W.map (fun w => w.toNat))) -∗
      ([∗list] i ↦ w ∈ W, fsChalf γfs (logSlotBno logstart i) (Lw i) ∗
         fsDirtyHalf γfs w.toNat false) -∗
      bslots γb (2 + W.length) -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  have h := IT.wp_install_trans (hlc := hlc) (GF := GF) Γ c k' γl γb V γdl γfs pd pav pu j
    logstart dev false n W Lw L D pidv dqp hj hproc hK hsie hnoff hlocks htier hgeom hdev
    hcl hdt (by simp only [Bool.false_eq_true, if_false]; exact ha0) hn hnodup hhome hlen
    (fun _ => hcommit) (by simp) hpd
  unfold wp_install_trans_body at h
  simp only [installTransAddr, Bool.false_eq_true, if_false] at h
  exact h

end

end Xv6
