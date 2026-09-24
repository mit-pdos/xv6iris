/-
Specification of `initlog` (kernel/log.c): the public contract.  Mirrors
Rocq `SpecInitlog.v`.

    void initlog(int dev, struct superblock *sb) {
      if (sizeof(struct logheader) >= BSIZE) panic("initlog: too big logheader");
      initlock(&log.lock, "log");
      log.start = sb->logstart;
      log.size = sb->nlog;
      log.dev = dev;
      recover_from_log();            // INLINED: read_head, install_trans(1),
                                     // log.lh.n = 0, write_head
    }

WHAT IT BUILDS.  `initlog` is the function that CREATES the log layer: it
seals the "log" spinlock over `Xv6.logResAt` and hands the caller back the
persistent `Xv6.logCtx`.  Everything it was given -- the raw `struct log`
cells, the block-view authorities, the log region's client halves and the
slot pool -- is sealed inside.

WHAT IT IS GIVEN.  The `struct superblock` field it reads (`sb->logstart`
at `sb+20`, at the caller's fraction, handed back), the raw spinlock cells
(`&log.lock = &log`), the rest of `struct log` (`outstanding` and
`committing` arrive ZERO -- `initlog` never writes them and the invariant
needs them zero, which is the `.bss` guarantee for a static object), the
four ghost names at their genesis values (`Xv6.logFreeTok`), and the
on-disk header's content `bsHdr` with its well-formedness: the decoded
write set is bounded by the region, duplicate-free, and names covered HOME
blocks.  At a clean image the decode is empty and all three are trivial;
at a real crash they are what a durable header invariant would deliver.

**Deviations, all the log port's standing ones** (see `Xv6/LogInv.lean`):
the crash seam, the era certificate, the era's born-true mirror, the byte
view's row and exception handle, block 1's park and the file system's
snapshot law are all dropped with the layers they belong to.  One further
deviation is local to this port: Rocq's contract is an `_at` form in all
five ghost names because the file system's configuration record names
them, while this port's lock library mints the lock's own name at the seal
(`MachCSL.kctx_newlock`), so the post existentially binds that one name
(`Xv6.LogNames.withLk`) and the other four are the caller's.

**Stated, not proved**, for the reason `Xv6/SpecEndOp.lean` gives: its
inlined `recover_from_log` calls `install_trans(1)` -- which IS provable
here -- and `write_head`, but sealing the lock also needs a
`MachCSL.CtxMorph` instance for `Xv6.logResAt`, which this wave does not
build.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.WpSmodeFrame
import Xv6.LogInv
import Xv6.SpecInstallTrans
import Xv6.SpecWriteHead
import Xv6.SpecInitlock
import Xv6.SpecPanic

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `initlog`. -/
def initlogAddr : BitVec 64 := KA.«initlog»

/-- `initlog`'s frame over its deepest callee (the inlined
`recover_from_log`'s `install_trans`). -/
def initlogSlots : Nat := 6 + installTransSlots

/-- **WP of `initlog(dev = a0, sb = a1)`**. -/
def wp_initlog_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
    [BcacheG GF] [SleepLockG GF] [DiskG GF] [FsBlocksG GF] [LogG GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γ : LogNames) (γl : GName) (γb : BcacheNames) (V : BioView)
    (γdl : GName) (γfs : FsNames) (pd pav pu : BitVec 64)
    (j : Nat) (logstart : Nat) (dev : BitVec 32) (sb : BitVec 64)
    (bsHdr : List (BitVec 8)) (L : BlockMap) (D : RegMapF Bool)
    (vlock : BitVec 32) (vname vcpu : BitVec 64) (vStart vDev vNc vN : BitVec 32)
    (pidv : BitVec 32) (dqp dqs : DFrac)
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : initlogSlots ≤ k.avail)
    (hsie : k.sie = false) (hnoff : k.noff = 0) (hlocks : k.locks = [])
    (htier : k.tier = KTier.kpt)
    (hgeom : logGeomOk V.cov logstart) (hdev : dev = V.dev)
    (ha0 : k.regs 10#5 = BitVec.signExtend 64 dev) (ha1 : k.regs 11#5 = sb)
    -- the on-disk header's well-formedness
    (hhdrLen : (hdrDec bsHdr).1 ≤ LOGBLOCKS)
    (hhdrNodup : (hdrDec bsHdr).2.Nodup)
    (hhdrHome : ∀ b ∈ (hdrDec bsHdr).2, fsHome V.cov logstart b)
    -- nothing is pinned in a fresh era
    (hclean : ∀ b ∈ V.cov, PartialMap.get? D b = some false)
    (hpd : descPageRw pd) : Prop :=
  kctx cpu k ∗ pcIs cpu initlogAddr ∗ procsInv Γ ∗
  trapCsrs cpu ∗ cpuClaim cpu k.proc ∗ intrRes cpu ∗
  bioCtx γl γb V ∗ diskCaps V.gd γdl pd pav pu ∗ panicEnv ∗
  wordPointsTo (pPid k.proc) 4 dqp pidv ∗
  -- the four ghost names, at their genesis values
  logFreeTok γ ∗
  -- the superblock field, read once
  wordPointsTo (sb + 20#64) 4 dqs (BitVec.ofNat 32 logstart) ∗
  -- the RAW spinlock cells of struct log (&log.lock = &log)
  kmapId logAddr ∗ kmapId (logAddr + 16#64) ∗
  wordPointsTo logAddr 4 (DFrac.own 1) vlock ∗
  wordPointsTo (logAddr + 8#64) 8 (DFrac.own 1) vname ∗
  wordPointsTo (logAddr + 16#64) 8 (DFrac.own 1) vcpu ∗
  -- the rest of struct log
  wordPointsTo lStart 4 (DFrac.own 1) vStart ∗
  wordPointsTo lDev 4 (DFrac.own 1) vDev ∗
  wordPointsTo lOut 4 (DFrac.own 1) 0#32 ∗
  wordPointsTo lCmt 4 (DFrac.own 1) 0#32 ∗
  wordPointsTo lNcommit 4 (DFrac.own 1) vNc ∗
  wordPointsTo lhNAddr 4 (DFrac.own 1) vN ∗
  ([∗list] i ∈ List.range LOGBLOCKS, ∃ w : BitVec 32,
     wordPointsTo (lhBlock i) 4 (DFrac.own 1) w) ∗
  -- the block view the batch is assembled from
  fsCacheAuth γfs L ∗ fsDirtyAuth γfs D ∗
  ([∗list] b ∈ V.cov.toList, fsDirtyHalf γfs b false) ∗
  fsChalf γfs (logHdrBno logstart) bsHdr ∗
  ([∗list] i ∈ List.range LOGBLOCKS, ∃ bs : List (BitVec 8),
     fsChalf γfs (logSlotBno logstart i) bs) ∗
  -- the slot pool, stocked: the batch's 32 plus initlog's own working pair
  bslots γb ((LOGBLOCKS + 2) + 2) ∗
  wpNext true k.proc cpu (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap) (γlk : GName),
    ⌜calleeSaved k.regs R'⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    trapCsrs cpu' -∗ cpuClaim cpu' k.proc -∗ intrRes cpu' -∗
    wordPointsTo (pPid k.proc) 4 dqp pidv -∗
    wordPointsTo (sb + 20#64) 4 dqs (BitVec.ofNat 32 logstart) -∗
    bslots γb 2 -∗
    logCtx (γ.withLk γlk) γb γfs V.cov logstart dev -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `initlog`. -/
structure INITLOG : Prop where
  wp_initlog : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
    [BcacheG GF] [SleepLockG GF] [DiskG GF] [FsBlocksG GF] [LogG GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γ : LogNames) (γl : GName) (γb : BcacheNames) (V : BioView)
    (γdl : GName) (γfs : FsNames) (pd pav pu : BitVec 64)
    (j : Nat) (logstart : Nat) (dev : BitVec 32) (sb : BitVec 64)
    (bsHdr : List (BitVec 8)) (L : BlockMap) (D : RegMapF Bool)
    (vlock : BitVec 32) (vname vcpu : BitVec 64) (vStart vDev vNc vN : BitVec 32)
    (pidv : BitVec 32) (dqp dqs : DFrac)
    hj hproc hK hsie hnoff hlocks htier hgeom hdev ha0 ha1 hhdrLen hhdrNodup hhdrHome
    hclean hpd,
    wp_initlog_body (hlc := hlc) (GF := GF) Γ cpu k γ γl γb V γdl γfs pd pav pu j
      logstart dev sb bsHdr L D vlock vname vcpu vStart vDev vNc vN pidv dqp dqs
      hj hproc hK hsie hnoff hlocks htier hgeom hdev ha0 ha1 hhdrLen hhdrNodup hhdrHome
      hclean hpd

end Xv6
