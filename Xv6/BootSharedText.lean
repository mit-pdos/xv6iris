/-
**THE SHARED BOOT ALLOCATION, THE WINDOW PERSISTED BY THE POWER THREAD**
(weak-allocproc plan §C Stage 0, item W3, option (A); PROGRESS-W3.md).

Twins of `Xv6.BootShared`'s `powerBootRows`, `powerBootRes_unpack`,
`bootShared_image`, `bootShared_carve` and `bootSharedAlloc` at
`MachCSL.powerBootResT bcRoLo bcRoHi` (`MachCSL/PowerText.lean`): the power
thread has already persisted the read-only window `[bcRoLo, bcRoHi)`
(`.text`, `.rodata`, `.eh_frame`) and recorded it in the trace slot, so the
boot gets that window PERSISTED (`winRoAt`, which is `bootRo` of the
window, `winRoAt_bootRo`) and the memory cells outside it owned
(`memCellsOut`, whose `[bcRoHi, ramEnd)` part is the carve's owned half,
`memCellsOut_ran`).  `bootCarve_imageT` is `BootCarve.bootCarve_image` less
the persist step; everything downstream is a near-copy whose only change is
the memory row.  Every existing statement is unchanged [OWN.9].
-/
import Xv6.BootShared
import MachCSL.PowerText

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std Std MachCSL

/-! ## §1 the rows, unpacked -/

section rows
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- `powerBootRows` with its memory row as `powerBootResT`'s: the window
`[bcRoLo, bcRoHi)` persisted, the cells outside it owned. -/
def powerBootRowsT (Mof : (Nat → BitVec 8) → LogMirror) (σ : MState) : IProp GF := iprop%
  (∃ r : BitVec 44, MachGS.kptRootName (hlc := hlc) (GF := GF) ↪VAR r) ∗
  genCert ∗
  ([∗list] cpu ∈ cpus, regCellsNoPins (regName (hlc := hlc) (GF := GF) cpu) (σ.regs cpu)) ∗
  ((winRoAt (MachGS.era (hlc := hlc) (GF := GF)).mem σ.mem bcRoLo bcRoHi ∗
    memCellsOut (MachGS.era (hlc := hlc) (GF := GF)) (rsvErase KernelRsv.static σ.mem) bcRoLo bcRoHi) ∗
    rsvHalvesC (MachGS.era (hlc := hlc) (GF := GF)) KernelRsv.static σ.mem ∗
    ⌜MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static ∧
      (MachFixedGS.kptOk (hlc := hlc) (GF := GF) = KernelRsv.kptOk ∧
      MachFixedGS.relPcs (hlc := hlc) (GF := GF) = KernelRsv.relPcs)⌝) ∗
  ([∗list] cpu ∈ cpus, ∃ ξ : CtxId, ctxTok (hlc := hlc) (GF := GF) cpu ξ) ∗
  ([∗list] cpu ∈ cpus, lockSet (hlc := hlc) (GF := GF) cpu []) ∗
  (MachGS.kmapName (hlc := hlc) (GF := GF) ↪●MAP KernelMap.static) ∗ kmapStatic (hlc := hlc) (GF := GF) ∗
  wireInv (hlc := hlc) (GF := GF) ∗
  ([∗list] d ∈ DevId.all, devFrag (hlc := hlc) (GF := GF) d (σ.devs.st d)) ∗
  chistAt (hlc := hlc) (GF := GF) .uart0 (genId (hlc := hlc) (GF := GF) + 1) [] uartBootHist ∗
  logMirrorHalf (hlc := hlc) (GF := GF) (Mof (diskOf σ.devs)) ∗
  swapLb (hlc := hlc) (GF := GF) (genId (hlc := hlc) (GF := GF) + 1) ∗
  crashInv (hlc := hlc) (GF := GF)


end rows

section unpack
variable {hlc : HasLC} {GF : BundledGFunctors} [MachFixedGS hlc GF]

/-- `powerBootRes_unpack` at `powerBootResT bcRoLo bcRoHi`.  Pure conversion. -/
theorem powerBootResT_unpack (Mof : (Nat → BitVec 8) → LogMirror)
    (Rb : Nat → (Nat → BitVec 8) → IProp GF) (Tn : Nat → IProp GF) (E : EraGS) (gen : Nat)
    (cP : CPU → BitVec 64 → IProp GF) (cI : ∀ cpu : CPU, ⊢ cP cpu 0#64) (σ : MState) :
    powerBootResT bcRoLo bcRoHi Mof Rb Tn E gen σ ⊢
      @powerBootRowsT hlc GF (MachGS.ofEra E gen cP cI) Mof σ ∗ Rb gen (diskOf σ.devs) ∗
        Tn (gen + 1) ∗ MachFixedGS.uClaimO (hlc := hlc) (GF := GF) ∗
        MachFixedGS.uEraTok (hlc := hlc) (GF := GF) (gen + 1) :=
  (bs_gatherRsv _ _ _ _ _ _ _).trans (bs_pull _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)


end unpack

/-! ## §2 the carve, the window already persisted -/

section carve
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]

/-- The persisted window is the carve's `bootRo`. -/
theorem winRoAt_bootRo (m : MemF Hist) :
    winRoAt (MachGS.era (hlc := hlc) (GF := GF)).mem m bcRoLo bcRoHi ⊢ bootRo (GF := GF) m bcRoLo bcRoHi := by
  unfold winRoAt bootRo winMem bcRanMem winIn bcRanIn
  exact .rfl

/-- The cells outside the window hold the carve's owned half `[bcRoHi, ramEnd)`. -/
theorem memCellsOut_ran (m : MemF Hist) :
    memCellsOut (MachGS.era (hlc := hlc) (GF := GF)) m bcRoLo bcRoHi ⊢ bootRan (GF := GF) m bcRoHi ramEnd := by
  rw [bootRan_cond]
  unfold memCellsOut
  apply BigSepM.bigSepM_mono_of_forall
  intro a H
  unfold bcRanElem
  by_cases h : bcRanIn bcRoHi ramEnd a H = true
  · have hw : winIn bcRoLo bcRoHi a H = false := by
      simp only [bcRanIn, decide_eq_true_eq] at h
      simp only [winIn, decide_eq_false_iff_not, not_and, Nat.not_lt]
      intro _; exact h.1
    simp only [h, hw, Bool.false_eq_true, ↓reduceIte]
    exact .rfl
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    exact Affine.affine

/-- **`bootCarve_image`, the window already persisted**: the persisted
window with the static claims is the kernel's read-only image, and the cells
outside the window hold the owned half `[_data, PHYSTOP)`. -/
theorem bootCarve_imageT :
    kmapStatic (GF := GF) ∗ (winRoAt (MachGS.era (hlc := hlc) (GF := GF)).mem (imgFlat bootImage) bcRoLo bcRoHi ∗
      memCellsOut (MachGS.era (hlc := hlc) (GF := GF)) (rsvErase KernelRsv.static (imgFlat bootImage)) bcRoLo bcRoHi) ⊢@{IProp GF}
      |==> ((kernelText ∗ kernelData ∗ kmapStatic) ∗
        bootRan (rsvErase KernelRsv.static (imgFlat bootImage)) bcRoHi ramEnd) := by
  iintro ⟨#Hk, #Hw, Hout⟩
  ihave #Hro := winRoAt_bootRo (hlc := hlc) (GF := GF) (imgFlat bootImage) $$ Hw
  ihave Ht := kernelText_intro (GF := GF) $$ [Hk Hro]
  · iframe Hk Hro
  ihave Hd := kernelData_intro (GF := GF) $$ Hro
  ihave Hown := memCellsOut_ran (hlc := hlc) (GF := GF) _ $$ Hout
  imodintro
  iframe Ht Hd Hk Hown

/-- `bootShared_image`, the window already persisted (`bootCarve_imageT`). -/
theorem bootShared_imageT (σ : MState) (hbf : bootFacts σ) :
    kmapStatic (GF := GF) ∗ (winRoAt (MachGS.era (hlc := hlc) (GF := GF)).mem σ.mem bcRoLo bcRoHi ∗
      memCellsOut (MachGS.era (hlc := hlc) (GF := GF)) (rsvErase KernelRsv.static σ.mem) bcRoLo bcRoHi) ⊢
      |==> (kernelText ∗ kernelData ∗ bootGotRo ∗
        bootRan (imgFlat bootImage) MachCSL.KernelSyms.«first_1» (MachCSL.KernelSyms.«first_1» + 4) ∗
        bootRan (imgFlat bootImage) MachCSL.KernelSyms.«nextpid» (MachCSL.KernelSyms.«nextpid» + 4) ∗
        bootRan (rsvErase KernelRsv.static (imgFlat bootImage)) (bcpUart .uart0) (bcpUart .uart0 + 40) ∗
        bootRan (rsvErase KernelRsv.static (imgFlat bootImage)) (bcpUart .uart1) (bcpUart .uart1 + 40) ∗
        bootRan (rsvErase KernelRsv.static (imgFlat bootImage)) MachCSL.KernelSyms.«_bss» MachCSL.KernelSyms.«end» ∗
        bootRan (imgFlat bootImage) 0x80024000 ramEnd) := by
  rw [hbf.1]
  refine (bootCarve_imageT (GF := GF)).trans ?_
  iintro H
  imod H with ⟨⟨#Ht, #Hd, -⟩, Hown⟩
  icases bootCarve_owned (GF := GF) _ $$ Hown with ⟨Hdata, Hbss, Hfree⟩
  ihave Hfree := bootRan_rsvErase_off_le (imgFlat bootImage) _ _ (by decide +kernel) $$ Hfree
  -- `.data`: the GOT and what follows hold no reserved byte; `uarts[]` does
  -- (the two transmit locks, W8-β′), so its windows stay erased
  icases (bootRan_split (GF := GF) _ _ bhGot _ (by decide) (by decide)).1 $$ Hdata with ⟨Hdata, Hgot⟩
  ihave Hgot := bootRan_rsvErase_off_le (imgFlat bootImage) _ _ (by decide +kernel) $$ Hgot
  icases (bootRan_split (GF := GF) (imgFlat bootImage) _ (bhGot + 8) _ (by decide) (by decide)).1 $$ Hgot
    with ⟨Hg, -⟩
  imod (bootRan_persist (GF := GF) (imgFlat bootImage) bhGot (bhGot + 8)) $$ Hg with #Hg
  have hw := bcpDataWindows (GF := GF) (rsvErase KernelRsv.static (imgFlat bootImage))
  rw [show (0x8000a3e8 : Nat) = bhGot from rfl] at hw
  icases hw $$ Hdata with ⟨H1, H2, H3, H4⟩
  ihave H1 := bootRan_rsvErase_off_le (imgFlat bootImage) _ _ (by decide +kernel) $$ H1
  ihave H2 := bootRan_rsvErase_off_le (imgFlat bootImage) _ _ (by decide +kernel) $$ H2
  imodintro
  unfold bootGotRo
  iframe Ht Hd Hg H1 H2 H3 H4 Hbss Hfree


end carve

section carveAll
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]

/-- `bootShared_carve`, the window already persisted (`bootShared_imageT`). -/
theorem bootShared_carveT (σ : MState) (hbf : bootFacts σ) :
    kmapStatic (GF := GF) ∗ ((winRoAt (MachGS.era (hlc := hlc) (GF := GF)).mem σ.mem bcRoLo bcRoHi ∗
      memCellsOut (MachGS.era (hlc := hlc) (GF := GF)) (rsvErase KernelRsv.static σ.mem) bcRoLo bcRoHi) ∗
      rsvHalvesC (MachGS.era (hlc := hlc) (GF := GF)) KernelRsv.static σ.mem ∗
      ⌜MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static ∧
      (MachFixedGS.kptOk (hlc := hlc) (GF := GF) = KernelRsv.kptOk ∧
      MachFixedGS.relPcs (hlc := hlc) (GF := GF) = KernelRsv.relPcs)⌝) ∗
      ([∗list] cpu ∈ cpus, ∃ ξ : CtxId, ctxTok (hlc := hlc) (GF := GF) cpu ξ) ∗
      ([∗list] cpu ∈ cpus, regCellsNoPins (regName (hlc := hlc) (GF := GF) cpu) (σ.regs cpu)) ∗
      ([∗list] cpu ∈ cpus, lockSet (hlc := hlc) (GF := GF) cpu []) ⊢
      |==> ∃ ξ0 : CtxId, bsCarveOut σ ξ0 := by
  iintro ⟨#Hk, ⟨Hmem, Hhalf, %⟨hrsv, hkptEq⟩⟩, Ht, Hr, Hl⟩
  imod bootShared_imageT σ hbf $$ [Hmem] with
    ⟨#Htx, #Hd, #Hg, Hw1, Hw2, Hu0, Hu1, Hbss, Hfree⟩
  · iframe Hk Hmem
  icases bcpBssWindowsR (GF := GF) $$ Hbss with
    ⟨Hst, Hkp, Hip, Htk, Hs0, Hc, Hring, Hpr, Hkm, Hkm2, Hpl, Hwl, Hcpus, Hproc, Htl, Hbcl, Hbc, Hbc2, Hsb, Hitl,
      Hit, Hlogl, Hlog, Hdv, Hftl, Hft, Hdk, Hdkl⟩
  ihave Hhalf := (show rsvHalvesC (MachGS.era (hlc := hlc) (GF := GF)) KernelRsv.static σ.mem ⊢
    rsvHalvesC (MachGS.era (hlc := hlc) (GF := GF)) KernelRsv.static (imgFlat bootImage) by rw [hbf.1]) $$ Hhalf
  icases bootRsvHalves _ _ $$ Hhalf with ⟨Hpre, Hhc, Hhpr, Hpost⟩
  unfold bootPreHalves bootPostHalves
  icases Hpre with ⟨Hhu0, Hhu1, Hhst, Hhcons, Hhprk, Hhkm, Hhp, Hhw⟩
  icases Hpost with ⟨Hhtl, Hhbc, Hhbufs, Hhit, Hhinodes, Hhlog, Hhft, Hhdk⟩
  imod bootShared_harts σ hbf ⟨hrsv, hkptEq⟩ $$ [] Ht Hr Hl Hs0 Hcpus Hhc with Hh
  · iframe Hk Hg
  ihave Hc := bootLockWin_intro KA.«cons» MachCSL.KernelSyms.«cons» hrsv $$ [Hc Hhcons]
  · iframe Hc Hhcons
  ihave Hpr := bootLockWin_intro KA.«pr» MachCSL.KernelSyms.«pr» hrsv $$ [Hpr Hhprk]
  · iframe Hpr Hhprk
  ihave Hkm := bootLockWin_intro KA.«kmem» MachCSL.KernelSyms.«kmem» hrsv $$ [Hkm Hhkm]
  · iframe Hkm Hhkm
  ihave Hpl := bootLockWin_intro KA.«pid_lock» MachCSL.KernelSyms.«pid_lock» hrsv $$ [Hpl Hhp]
  · iframe Hpl Hhp
  ihave Hwl := bootLockWin_intro KA.«wait_lock» MachCSL.KernelSyms.«wait_lock» hrsv $$ [Hwl Hhw]
  · iframe Hwl Hhw
  ihave Htl := bootLockWin_intro KA.«tickslock» MachCSL.KernelSyms.«tickslock» hrsv $$ [Htl Hhtl]
  · iframe Htl Hhtl
  ihave Hbcl := bootLockWin_intro KA.«bcache» MachCSL.KernelSyms.«bcache» hrsv $$ [Hbcl Hhbc]
  · iframe Hbcl Hhbc
  ihave Hitl := bootLockWin_intro KA.«itable» MachCSL.KernelSyms.«itable» hrsv $$ [Hitl Hhit]
  · iframe Hitl Hhit
  ihave Hbc := bootBufsWin_intro hrsv $$ [Hbc Hhbufs]
  · iframe Hbc Hhbufs
  ihave Hit := bootInodesWin_intro hrsv $$ [Hit Hhinodes]
  · iframe Hit Hhinodes
  ihave Hlogl := bootLockWin_intro KA.«log» MachCSL.KernelSyms.«log» hrsv $$ [Hlogl Hhlog]
  · iframe Hlogl Hhlog
  ihave Hftl := bootLockWin_intro KA.«ftable» MachCSL.KernelSyms.«ftable» hrsv $$ [Hftl Hhft]
  · iframe Hftl Hhft
  ihave Hdkl := (show bootRan (GF := GF) (rsvErase KernelRsv.static (imgFlat bootImage)) (MachCSL.KernelSyms.«disk» + 296) (MachCSL.KernelSyms.«disk» + 0x140) ⊢
      bootRan (GF := GF) (rsvErase KernelRsv.static (imgFlat bootImage)) (MachCSL.KernelSyms.«disk» + 296) (MachCSL.KernelSyms.«disk» + 296 + 24) from .rfl) $$ Hdkl
  ihave Hdkl := bootLockWin_intro rsvDiskLk (MachCSL.KernelSyms.«disk» + 296) hrsv $$ [Hdkl Hhdk]
  · iframe Hdkl Hhdk
  ihave Hhu0 := (show rsvRegionHalfC (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) (xv6LockR (rsvUartLk 0))
      (imgFlat bootImage) ⊢ rsvRegionHalfC (MachGS.era (hlc := hlc) (GF := GF)) (xv6LockR (txLockAddr .uart0))
      (imgFlat bootImage) from .rfl) $$ Hhu0
  ihave Hu0 : iprop(bootUartWin (GF := GF) .uart0) $$ [Hu0 Hhu0]
  · unfold bootUartWin
    iframe Hu0 Hhu0
    ipureintro; exact hrsv
  ihave Hhu1 := (show rsvRegionHalfC (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) (xv6LockR (rsvUartLk 1))
      (imgFlat bootImage) ⊢ rsvRegionHalfC (MachGS.era (hlc := hlc) (GF := GF)) (xv6LockR (txLockAddr .uart1))
      (imgFlat bootImage) from .rfl) $$ Hhu1
  ihave Hu1 : iprop(bootUartWin (GF := GF) .uart1) $$ [Hu1 Hhu1]
  · unfold bootUartWin
    iframe Hu1 Hhu1
    ipureintro; exact hrsv
  ihave Hproc := (show bootRan (GF := GF) (rsvErase KernelRsv.static (imgFlat bootImage)) MachCSL.KernelSyms.«proc»
      (MachCSL.KernelSyms.«proc» + 376 * NPROC) ⊢
      bootRan (rsvErase KernelRsv.static (imgFlat bootImage)) MachCSL.KernelSyms.«proc»
        (MachCSL.KernelSyms.«proc» + 376 * 64) from .rfl) $$ Hproc
  ihave Hproc := bootProcWin_intro hrsv $$ [Hproc Hhpr]
  · iframe Hproc Hhpr
  icases bootShared_peel _ $$ Hh with ⟨⟨⟨%ξ0, Ht0⟩, Hb0⟩, Hrest⟩
  have hB := (letI : CurCtx := bootSharedX ξ0; bootShared_bareRows (GF := GF))
  imod hB $$ Hk Hc Hpr Hkm Hkm2 Hdv Hkp Hu0 Hu1 Hfree with ⟨HL, HG, HU0, HU1, HP⟩
  ihave Hsc := bootShared_startedCell (GF := GF) hrsv $$ Hhst
  imodintro
  iexists ξ0
  unfold bsCarveOut bsKptWin
  iframe Htx Hd Ht0 Hb0 Hrest HL HG HU0 HU1 HP Hproc Hip Htk Hring Hw1 Hw2 Hpl Hwl Htl Hbcl Hbc Hbc2 Hsb Hitl
    Hit Hlogl Hlog Hftl Hft Hdk Hdkl Hsc


end carveAll

/-! ## §3 the shared allocation -/

section alloc
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [WchGpre GF] [CtokG GF] [DiskG GF]
  [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF] [FsTopG GF] [FsLinkG GF]
  [IcboxG GF] [SleepLockG GF] [Appcfg GF] [BcacheG GF] [OffboxG GF] [OffboxBoxG GF] [FileG GF]

set_option maxHeartbeats 400000 in
/-- **`bootSharedAlloc` at the rows of `powerBootResT`** (`powerBootRowsT`):
the carve is `bootShared_carveT`; everything else verbatim. -/
theorem bootSharedAllocT (σ : MState) (hbf : bootFacts σ) (ds0 : DevStates) (hds : σ.devs = ds0.reset)
    (ndisk : Nat) (S : FsStateRec) (sb : FsSb) (nib : Nat) (cov : ExtTreeSet Nat compare)
    (gsn gln gtn : GName) (Pb : Nat → List (BitVec 8))
    (hwf : fsBootSnapWf (diskOf σ.devs) ndisk S Pb sb nib cov) :
    powerBootRowsT (hlc := hlc) (GF := GF) (fun dk => mirrorOf (fsBlocks dk)) σ ∗
      ▷ appPred appRun (absView S.fssInodes) ∗
      -- the crash seam at the guest and the merge package, ONE row closed over
      -- the guest's durable-copy predicate (Rocq `app_dur_laws`, SY3-A3b)
      appDurLaws (hlc := hlc) cov sb.sbLogstart ∗
      eraSyncTok (hlc := hlc) (GF := GF) ∗
      fsSnap (snapGamma gsn gln gtn) gsn (fsRestrict Pb (fsHomeList cov sb.sbLogstart)) S ⊢
      |={⊤}=> ∃ (ξ0 : CtxId) (Γ : SchedNames) (W : WchG GF) (HFd : FdslotG GF) (HBs : BioslotG GF)
        (HIr : IrefslotG GF) (γc γl0 γl1 γt : GName) (γ0 γ1 : UartNames) (cn : ConsNames)
        (γd : DiskNames) (I : Icfg) (F : Fscfg) (ξd : CtxId),
        -- (NI M2-X2) the minted instance's cameras are the ambient ones
        ⌜W.toWchGpre = (inferInstance : WchGpre GF)⌝ ∗
        bootSharedOut σ ξ0 Γ γ0 γ1 γc γl0 γl1 γt cn γd ξd (diskOf σ.devs) sb nib cov Pb
          (snapSpent S nib) := by
  unfold powerBootRowsT
  rw [hds] at hwf ⊢
  iintro ⟨⟨Hkpt, #Hcert, Hregs, Hmem, Htoks, Hlocks, Hkauth, #Hkst, #Hwire, Hdevs, Hch, Hmir, #Hsw,
    #Hcinv⟩, Happ, #Hdurl, Hstok, Hsnap⟩
  -- the gname-only mints (the instances first)
  imod bootSharedDev_names (hlc := hlc) (GF := GF) with
    ⟨%Γ, %W, %HFd, %HBs, %HIr, %γc, %γl0, %γl1, %γt, %hW, Hn⟩
  -- the carve, at hart 0's context
  imod bootShared_carveT σ hbf $$ [Hmem Htoks Hregs Hlocks] with ⟨%ξ0, Hc⟩
  · iframe Hkst Hmem Htoks Hregs Hlocks
  unfold bsCarveOut bsKptWin
  icases Hc with ⟨#Htx, #Hd, Ht0, Hb0, Hrest, HL, HG, HU0, HU1, HP, ⟨W1, W2, W3, W4, W5, W6, W7, W8,
    W9, W10, W11, W12, W13, W14, W15, W16, W17, W18, W19, W20, W21⟩, Hsc⟩
  -- the devices
  imod bootSharedDev_devs (hlc := hlc) (GF := GF) (bootSharedX ξ0) ds0 (ndisk / BSIZE) $$
    [Hdevs Hch HU0 HU1] with ⟨%γ0, %γ1, %cn, %γd, Hdv⟩
  · iframe Hdevs Hch HU0 HU1
  unfold bsdDevRows
  icases Hdv with ⟨%hcn, %hcne, #Hi0, #Hi1, #Hpl, #Hdi, #Hcc, Hm0, Hm1, Hg, Hcfg, Hgh, Hroot, Hblk⟩
  unfold bsdNameRows
  icases Hn with ⟨Hh, Hs, Hav, Hsf, Hchb, Htc, Htl0, Htl1, Htt, Hlks, Hfd, Hi1, Hi2, Hi3, Hia, Hb1, Hb2⟩
  -- the kernel-tier rows
  have hK := (letI : CurCtx := (bootSharedX ξ0).toKpt; bootShared_kptRows (GF := GF) cn)
  ihave HK := hK $$ Hkst W1 W2 W3 W4 W5 W6 W7 W8 W9 W10 W11 W12 W13 W14 W15 W16 W17 W18 W19 W20 W21 Hg Hfd Hi1 Hi2 Hb1
  icases HK with ⟨HLr, HGr, HSb, HLog, HF, HNp, HDk⟩
  -- the file system
  have hF := (letI : CurCtx := bootSharedX ξ0; bootSharedFs (hlc := hlc) (GF := GF) γ0 γd cn
    (diskOf ds0.reset) ndisk S sb cov nib gsn gln gtn Pb hwf)
  imod hF $$ Hblk Happ Hdurl Hstok Hsnap Hmir Hsw Hi3 Hia Hb2 Hcert Hcinv
    with ⟨%I, %F, Hfs⟩
  unfold bsfRows
  icases Hfs with ⟨Hsup, Hmb, Hib, Hiau, Hbs, -, #Hcs, -⟩
  ihave Hsup := fsBootSupply_appInv (hlc := hlc) (GF := GF) _ _ _ _ _ _ _ _ _ _ $$ Hsup
  icases Hsup with ⟨#Hai, Hsup⟩
  -- the handover's stamped record context
  imod ctxStamped_boot (GF := GF) with ⟨%ξd, Hstmp⟩
  imodintro
  iexists ξ0, Γ, W, HFd, HBs, HIr, γc, γl0, γl1, γt, γ0, γ1, cn, γd, I, F, ξd
  isplitl []
  · ipureintro; exact hW
  unfold bootSharedOut bootSupplyCore
  isplitr
  · ipureintro; exact hcn
  isplitr
  · ipureintro; exact hcne
  iframe Htx Hd Ht0 Hb0 Hrest Hsc Hstmp Hai Hi0 Hi1 Hpl Hwire Hcert Hdi Hcinv Hcc Hroot
  iframe HL HG HLr HGr HSb HLog HF HNp Hh Hs Hav Hsf Hchb Htc Htl0 Htl1 Htt Hlks Hsup Hmb Hib Hiau
    Hbs Hcs Hm0 Hm1 Hcfg Hgh HDk Hkpt Hkauth HP


end alloc

end Xv6
