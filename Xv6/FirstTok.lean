/-
**proc.c's `static int first`, AS A RESOURCE A PROCESS CARRIES** -- a port
of Rocq `FirstTok.v` (`/shared/xv6rocq/iris/FirstTok.v`, 1081 lines): the
definitional layer of wave 7's D8 (the fork/exit generation machinery).

## Rocq's header, in short (every clause is kept)

forkret's first act after `release(&p->lock)` is

    if (__atomic_load_n(&first, __ATOMIC_ACQUIRE)) { fsinit(); ...; }

and the branch is decided by WHICH ARM OF THIS DISJUNCTION the running
process holds.  No invariant, no mask, no atomicity argument: the two arms
are mutually exclusive as resources, so "exactly one process ever takes the
boot arm" is a theorem about ownership.

* `firstAddr ↦₄ 1` is EXCLUSIVE.  Holding it is the right to run the boot
  arm: fsinit, the store of 0, kexec("/init").  The boot chain deposits it
  into the FIRST process's block (SpecUserinit) and nothing else can have it.
* `firstAddr ↦₄□ 0 ∗ fsReady` is PERSISTENT, hence free for every process
  forever.  A holder reads 0, so the `c.beqz` at forkret+0x24 is TAKEN and
  the boot arm is dead -- and it already has the file system.

`DFrac.own 1` and `DFrac.discard` at one address are incompatible
(`first_tok_boot_excl`), so the moment the boot arm persists its store no
second holder of the exclusive arm can exist: the one-shot without a
one-shot ghost.  `fsReady` rides the second arm because forkret's tail
hands the trap loop the fs environment, and in the steady arm the only
honest source is the process's own block.

## The pieces (Rocq name → Lean)

| Rocq | Lean |
|---|---|
| `first_addr` | `firstAddr` (`KA.«first_1»`) |
| `first_boot_persist` (§1) | `firstBootPersist` |
| `first_fsinit_pures` (§2) | `firstFsinitPures` |
| `first_fsinit` / `_open` (§3) | `firstFsinit` / `firstFsinit_open` |
| `first_boot`, `first_tok`, `first_done` (§4) | `firstBoot`, `firstTok`, `firstDone` |
| `first_tok_done`, `first_tok_of_done`, `first_tok_open`, `first_tok_boot`, `first_boot_intro`, `first_boot_open`, `first_tok_of_boot` | same, camelCased with `_` suffixes |
| `first_persist_pre` | `firstPersistPre` (deviation 5) |
| `first_tok_boot_excl`, `first_boot_done_excl` | `firstTok_boot_excl`, `firstBoot_done_excl` |

## DEVIATIONS from Rocq

1. **`fsabs_env` (the application's `app_inv`) is DROPPED** from
   `first_done`, `first_tok`'s steady arm and `first_fsinit_open`: Lean has
   no application layer (`AppInv`/`app_xfer`).  `first_done_fsabs` goes with
   it.  When the application layer lands, it is a third conjunct of
   `firstDone` (and of `firstTok`'s right arm), exactly Rocq's shape.
2. **The crash layer is dropped** (D11, as `Xv6/FsReady.lean` /
   `Xv6/SpecFsinit.lean` deviation 3): `fs_crash_seam`, `gen_cert` leave
   `first_boot_persist`; `log_mirror_born`, `fs_crash_seam_at`, `app_xfer`,
   the exception set's slot values and the snapshot geometry (`col_geom`,
   the `sb_bmapstart`/`sb_size` ties, `fs_parse_sb`/`fs_sb_ok`, `hdr_wf`)
   leave `first_fsinit` / its pures.  With them go the ERA DATA Rocq
   quantifies (`dk`, `sb`, `Rspent`, `Pb`) and the COVERAGE REMAINDER row
   (`[∗ set] b ∈ fsc_cov ∖ Rspent, fsblock …`, "the first process's, R3"):
   Lean's PowerOn has no `Rspent` carve (the byte view's row rides
   `bitmapReg`, SpecFsinit deviation 7), so there is nothing to state it at.
3. **`first_fsinit` IS LEAN `fsinit`'s PREMISE PILE, era data quantified**
   (Rocq's rule, on the Lean contract `wp_fsinit_eb_body`): every
   non-persistent, non-register, non-process resource fsinit takes, with the
   values fsinit is generic in (`vMagic vSize vNblocks vNlog bsSb sbOld
   bsHdr L D vlock vname vcpu vStart vDev vNc vN`) existential.  Rocq's
   pures (a)/(b)/(g)/`1 ∈ cov` are `firstFsinitPures` over Lean's
   premises `hsbImg`/`hmagic`/`hhdrLen`/`hhdrNodup`/`hhdrHome`/`hhdr0`/
   `h1cov`/`hsbOld`.  Rocq's kit rows map as: the log free token →
   `logFreeTok icfgLog`; block 1's `fs_chalf` → `fsblock fscFs.bytes 1
   bsSb` (SpecFsinit deviation 2: block 1's RUN); `ireg_boot` → `iregBoot`;
   the auths / dirty halves / header + slots → `fsCacheAuth`/`fsDirtyAuth`/
   `fsDirtyHalf`/`fsChalf` rows verbatim; `exc_own` → `excOwn`; the raw
   `&sb` bytes → `byteBuf KA.«sb»`; the struct-log cells verbatim; row (C)
   `iref_slots 2` ∗ `bslots 35` verbatim.  ADDED: initlog's
   `kmapId logAddr` / `kmapId (logAddr + 16#64)` (Lean initlog's premises,
   threaded by fsinit; Rocq's initlog does not take them).
   `ireg_reg` and `bitmap_inv`/`bitmap_reg` are PERSISTENT and so ride
   `firstBootPersist` (Rocq has `ireg_reg` in both; Lean needs it once).
   The remaining fsinit premises are projections of `FsGeomOk` (which
   rides `firstBootPersist`, as Rocq's `fs_geom_ok` does): `hgeom =
   fgoLog`, `hn1/hnnib/hn31 = fgoNinLo/Hi/31`, `hblk = fgoIreg`, `hbg =
   fgoBitmap`, `hbel = FsGeomOk.below`; `hpd` comes off the caps
   (`fsReady_descPage`); `ha0` and the pid cell are forkret's own.
   `hhdr0` (clean header) is Lean fsinit's premise (SpecFsinit deviation 4)
   and so rides the pures -- Rocq's era general-`n` form is not reachable
   until Lean's fsinit drops it.
4. **`first_boot_persist`**: `kernel_text`/`kernel_data` are inside `kctx`
   (FsReady deviation 3); `printk_env` is `panicEnv` (what Lean fsinit
   takes); `dev_inv ∗ disk_geom ∗ is_lock … disk_res_at` is `∃ pd pav pu,
   diskCaps fscDisk fscDlock pd pav pu` (FsReady deviation 4);
   `ic_escrows` is carried by `isItable2` (FsReady deviation 5); the
   "bcache" lock's name is bound, `∃ γl, bioCtx γl …` (FsReady deviation 2);
   the kmem lock and `kallocAvail` are at `fsReadyKmem` (FsReady
   deviation 6).  Rocq's sixteen rows are ten here, all persistent.
5. **`first_persist_pre` targets `fsReady` directly**, because Lean has no
   `fs_ready_pre` / `fs_ready_establish` yet (FsReady "WHAT IS LEFT").  It
   is Rocq's `first_persist_pre` composed with `fs_ready_establish`, with
   the one step Rocq does there by `ireg_boot` -- `fsReady_seal`
   (`iregBoot ==∗ iregOpen`) -- left to the caller (it is an update; this
   lemma is a pure entailment).  The same upgrades as Rocq's: `logCtx_seal`
   seals the byte view, `iregInv_of` / `bitmapInv_of` lift the PowerOn
   forms.
6. **The `CtxMorph` instances** (`first_fsinit_morph`,
   `first_boot_persist_morph`, `first_done_morph`, `first_boot_morph`,
   `first_tok_morph`) are DEFERRED, as `fs_ready_morph` is (FsReady
   deviation 8): the Lean cells here are `wordPointsTo` at the ambient
   `CurCtx`, not a λ-context form, and the consumer (the park carrying a
   block across `p->lock`, D8's ParkCap/ForkretIs retirement) does not exist
   in Lean yet.
7. **Rocq's `Typeclasses Opaque first_tok / first_boot /
   first_boot_persist` has no Lean counterpart**: Lean `iframe` matches by
   head symbol and never unfolds a `def`, so the correctness reason Rocq
   records (a broad `iFrame` eating `kernel_text` out of the boot arm) does
   not arise.  Consumers still go through the destructors
   (`firstTok_open`, `firstBoot_open`) by convention.
8. **The pure producers are DROPPED**: `fs_extent_of_image`,
   `fs_geom_ok_of_snap`, `col_geom_of_config`, `first_fsinit_pures_of_snap`
   and their helpers `nth_byte_fs_le_at`, `first_sb_image_lookup_total`,
   `first_sb_image_of_le`, `IBLOCK_in_range`: they read the era's durable
   snapshot (`FsDurSnap`, `FsState`, `FsCrash.fs_blocks`, `fs_parse_sb`,
   `col_geom`), none of which Lean has (D11); their consumer is the
   top-level boot/adequacy cone, not a kernel proof.
9. **`first_sb_base` is `KA.«sb»`** (no duplicate needed); `first_sb_image`
   is duplicated as `firstSbImage` for Rocq's reason (a token definition
   must not import `SpecFsinit`'s cone); it is DEFINITIONALLY `sbImage`
   (identical body), so the seal site bridges by `rfl`.

## What the kernel proofs will consume

* **userinit** (Rocq ProofUserinit): `firstTok_boot` (or `firstBoot_intro`
  + `firstTok_of_boot`) to deposit the exclusive arm into `<init>`'s block,
  out of the boot bundle's `firstBootPersist`, `kallocAvail fsReadyKmem
  none` (the seal allocproc's last counted draw leaves) and `firstFsinit`.
* **forkret** (the ForkretIs retirement): `firstTok_open`; boot arm →
  `firstFsinit_open` feeds `wp_fsinit_eb` (premises by `FsGeomOk`
  projections), then `fsReady_seal` + `firstPersistPre` build `fsReady`,
  the store of 0 is persisted and `firstDone` is formed; steady arm →
  `firstDone` directly.
* **kfork**: the child's block's `firstTok` is `firstTok_of_done` out of
  the parent's persistent `firstDone` (Rocq: `syscall_env` →
  `SpecSysFork` → `SpecKfork` → `kfk_b4`).  Once ProcPriv carries the token
  (D7/D8), `procPriv` gains a `firstTok` conjunct.
* **kexit**: drops the block's token (the steady arm is persistent; a
  boot-arm exit is refuted by `<init>` never exiting).

Imports only definitional files (and `SpecPanic` for `panicEnv`, as
`Xv6/FsReady.lean` imports `SpecVirtioDiskRw` for `diskCaps`).
-/
import Xv6.FsReady
import Xv6.SpecPanic
import Xv6.IrefSlots
import Xv6.FsBytesInv
import Xv6.FsImg
import Xv6.PtOwnLemmas
import MachCSL.ByteWord4
import MachCSL.CallConv

namespace Xv6

open Iris Iris.BI Iris.ProofMode Std MachCSL

set_option linter.unusedSectionVars false

/-- The static `int first`, at its identity-mapped kernel address (Rocq
`first_addr`).  `SpecForkret` names the same cell. -/
def firstAddr : BitVec 64 := KA.«first_1»

/-- `struct superblock`'s 32-byte image, DUPLICATED from `Xv6.sbImage`
(deviation 9): a token definition must not pull fsinit's Spec cone.
Definitionally equal to `sbImage` (`firstSbImage_eq`). -/
def firstSbImage (magic fssize nblocks ninodes nlog logstart inodestart bmapstart : BitVec 32) :
    List (BitVec 8) :=
  wordToBytes4 magic ++ wordToBytes4 fssize ++ wordToBytes4 nblocks ++
  wordToBytes4 ninodes ++ wordToBytes4 nlog ++ wordToBytes4 logstart ++
  wordToBytes4 inodestart ++ wordToBytes4 bmapstart

/-! ## 0.  The two cell states are incompatible -/

section Cells
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- Two 4-byte cells at one address, one of them WHOLE, cannot coexist
(the 4-byte twin of `Xv6.wordPointsTo_excl`). -/
theorem firstWord4_excl [CurCtx] (a : BitVec 64) (dq : DFrac) (w w' : BitVec 32) :
    iprop(wordPointsTo (GF := GF) a 4 (DFrac.own 1) w ∗ wordPointsTo a 4 dq w') ⊢
      (False : IProp GF) := by
  have hb : ∀ (ppn : BitVec 44) (dq' : DFrac) (u : BitVec 32),
      bytesPointsTo (GF := GF) (paOf ppn a) 4 dq' u ⊢
        ctxByte curCtx (paOf ppn a + BitVec.ofNat 64 0) dq' (nthByte (n := 4) u 0) := by
    intro ppn dq' u
    exact BigSepL.bigSepL_lookup (Φ := fun (_ : Nat) (j : Nat) =>
      iprop(ctxByte (GF := GF) curCtx (paOf ppn a + BitVec.ofNat 64 j) dq' (nthByte (n := 4) u j)))
      (l := List.range 4) (i := 0) (x := 0) (by simp)
  unfold wordPointsTo
  iintro ⟨⟨%ppn, #Hcl, %_, Hb1⟩, ⟨%ppn', #Hcl', %_, Hb2⟩⟩
  icases kmapAt_agree (vpnOf a) (kLeaf ppn .rw 0#1 0#1) (kLeaf ppn' .rw 0#1 0#1) $$ [Hcl Hcl']
    with %heq
  · isplit
    · iexact Hcl
    · iexact Hcl'
  have hp : ppn = ppn' := kLeaf_rw_ppn_inj _ _ heq
  subst hp
  ihave Hb1 := hb ppn (DFrac.own 1) w $$ Hb1
  ihave Hb2 := hb ppn dq w' $$ Hb2
  iapply ctxByte_excl
  isplitl [Hb1]
  · iexact Hb1
  · iexact Hb2

/-- **THE TWO ARMS ARE MUTUALLY EXCLUSIVE** (Rocq `first_tok_boot_excl`):
the boot arm runs at most once. -/
theorem firstTok_boot_excl [CurCtx] :
    iprop(wordPointsTo (GF := GF) firstAddr 4 (DFrac.own 1) 1#32 ∗
      wordPointsTo firstAddr 4 DFrac.discard 0#32) ⊢ (False : IProp GF) :=
  firstWord4_excl firstAddr DFrac.discard 1#32 0#32

end Cells

theorem firstSbImage_eq (a b c d e f g h : BitVec 32) :
    firstSbImage a b c d e f g h =
      wordToBytes4 a ++ wordToBytes4 b ++ wordToBytes4 c ++ wordToBytes4 d ++
      wordToBytes4 e ++ wordToBytes4 f ++ wordToBytes4 g ++ wordToBytes4 h := rfl

section FirstTok
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF]
  [BcacheG GF] [SleepLockG GF] [DiskG GF] [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF]
  [FsTopG GF] [FsLinkG GF] [IcboxG GF] [OffboxG GF] [OffboxBoxG GF] [IrefslotG GF] [CtokG GF] [WchG GF] [Appcfg GF]

/-! ## 1.  THE PERSISTENT HALF -- what main has built before userinit -/

/-- **Rocq `first_boot_persist`**: `fsReady`'s rows MINUS the three main
cannot have before fsinit (`logCtx`, which initlog builds; `kallocAvail _
none`, minted in userinit and riding `firstBoot` as its own row; the
superblock cells, which fsinit's memmove creates) and with the region and
the bitmap at their POWERON forms (`iregReg`, `bitmapReg`), plus fsinit's
`panicEnv`.  All persistent (deviation 4 for the row mapping). -/
def firstBootPersist [Fscfg] [Icfg] [CurCtx] : IProp GF := iprop(
  panicEnv ∗
  (∃ γl : GName, bioCtx γl fscBio (fsView fscFs fscDisk icfgDev fscCov)) ∗
  (∃ pd pav pu : BitVec 64, diskCaps fscDisk fscDlock pd pav pu) ∗
  isItable2 fscItlock fscIc fscFs fscIreg fscCov fscLogst icfgNib icfgDev ∗
  itableInv (hlc := hlc) ∗
  icSleeplocks fscIc ∗
  iregReg (hlc := hlc) fscIreg fscFs icfgIst icfgNib ∗
  bitmapReg fscFs fscBmapstart fscCov fscLogst fscSize ∗
  isLock fscKalloc kmemLockAddr "kmem" (kmemRes fsReadyKmem) ∗
  ⌜FsGeomOk⌝ ∗
  -- the crash seam and the era certificate (D38; LAST, as in `fsReady`)
  fsCrashSeam (hlc := hlc) (GF := GF) fscCov fscLogst ∗
  genCert (hlc := hlc) (GF := GF))

instance firstBootPersist_persistent [Fscfg] [Icfg] [CurCtx] :
    Persistent (firstBootPersist (hlc := hlc) (GF := GF)) := by
  unfold firstBootPersist; infer_instance

/-- The image's arithmetic, off the persistent half (every geometry premise
of `wp_fsinit_eb_body` is a projection of it, deviation 3). -/
theorem firstBootPersist_geom [Fscfg] [Icfg] [CurCtx] :
    firstBootPersist (hlc := hlc) (GF := GF) ⊢ ⌜FsGeomOk⌝ := by
  unfold firstBootPersist
  iintro ⟨-, -, -, -, -, -, -, -, -, %h, -⟩
  ipureintro; exact h

/-! ## 2.  THE PURE BLOCK -/

/-- **Rocq `first_fsinit_pures`**, over Lean fsinit's image premises
(deviation 3): block 1 IS a superblock at the configuration's values, the
magic (which refutes the live panic arm), the on-disk header is well formed
and clean, the superblock's block is covered, and the raw `.bss` bytes are
the record's width. -/
def firstFsinitPures [Fscfg] [Icfg]
    (vMagic vSize vNblocks vNlog : BitVec 32) (bsSb sbOld bsHdr : List (BitVec 8)) : Prop :=
  bsSb.take 32 = firstSbImage vMagic vSize vNblocks (BitVec.ofNat 32 fscNinodes) vNlog
      (BitVec.ofNat 32 fscLogst) (BitVec.ofNat 32 icfgIst) (BitVec.ofNat 32 fscBmapstart) ∧
  vMagic.toNat = FSMAGIC ∧
  (hdrDec bsHdr).1 ≤ LOGBLOCKS ∧
  (hdrDec bsHdr).2.Nodup ∧
  (∀ b ∈ (hdrDec bsHdr).2, fsHome fscCov fscLogst b ∧ b ≠ SB_BNO) ∧
  hdrN bsHdr = 0 ∧
  1 ∈ fscCov ∧
  sbOld.length = 32

/-! ## 3.  THE EXCLUSIVE HALF -- fsinit's premise pile -/

/-- **Rocq `first_fsinit`**: fsinit's exclusive premises, with every value
fsinit is generic in QUANTIFIED here, so forkret's walk names none of them
(deviation 3 for the row mapping). -/
def firstFsinit [Fscfg] [Icfg] [CurCtx] : IProp GF := iprop(
  ∃ (vMagic vSize vNblocks vNlog : BitVec 32) (bsSb sbOld bsHdr : List (BitVec 8))
    (L : BlockMap) (D : RegMapF Bool)
    (vlock : BitVec 32) (vname vcpu : BitVec 64) (vStart vDev vNc vN : BitVec 32),
    ⌜firstFsinitPures vMagic vSize vNblocks vNlog bsSb sbOld bsHdr⌝ ∗
    logFreeTok icfgLog ∗
    fsblock fscFs.bytes 1 bsSb ∗
    byteBuf KA.«sb» (DFrac.own 1) sbOld ∗
    excOwn fscFs.exc (hdrDec bsHdr).2 ∗
    iregBoot ∗
    kmapId logAddr ∗ kmapId (logAddr + 16#64) ∗
    wordPointsTo logAddr 4 (DFrac.own 1) vlock ∗
    wordPointsTo (logAddr + 8#64) 8 (DFrac.own 1) vname ∗
    wordPointsTo (logAddr + 16#64) 8 (DFrac.own 1) vcpu ∗
    wordPointsTo lStart 4 (DFrac.own 1) vStart ∗
    wordPointsTo lDev 4 (DFrac.own 1) vDev ∗
    wordPointsTo lOut 4 (DFrac.own 1) 0#32 ∗
    wordPointsTo lCmt 4 (DFrac.own 1) 0#32 ∗
    wordPointsTo lNcommit 4 (DFrac.own 1) vNc ∗
    wordPointsTo lhNAddr 4 (DFrac.own 1) vN ∗
    ([∗list] i ∈ List.range LOGBLOCKS, ∃ w : BitVec 32,
       wordPointsTo (lhBlock i) 4 (DFrac.own 1) w) ∗
    fsCacheAuth fscFs L ∗ fsDirtyAuth fscFs D ∗
    ([∗list] b ∈ fscCov.toList, fsDirtyHalf fscFs b false) ∗
    fsChalf fscFs (logHdrBno fscLogst) bsHdr ∗
    ([∗list] i ∈ List.range LOGBLOCKS, ∃ bs : List (BitVec 8),
       fsChalf fscFs (logSlotBno fscLogst i) bs) ∗
    bslots ((LOGBLOCKS + 2) + 2 + 1) ∗
    irefSlots 2)

/-- **Rocq `first_fsinit_open`**: the pile with its pure block handed out as
fsinit's own named premises, so the seal site never unfolds either layer. -/
theorem firstFsinit_open [Fscfg] [Icfg] [CurCtx] :
    firstFsinit (GF := GF) ⊢
      ∃ (vMagic vSize vNblocks vNlog : BitVec 32) (bsSb sbOld bsHdr : List (BitVec 8))
        (L : BlockMap) (D : RegMapF Bool)
        (vlock : BitVec 32) (vname vcpu : BitVec 64) (vStart vDev vNc vN : BitVec 32),
        ⌜bsSb.take 32 = firstSbImage vMagic vSize vNblocks (BitVec.ofNat 32 fscNinodes) vNlog
            (BitVec.ofNat 32 fscLogst) (BitVec.ofNat 32 icfgIst) (BitVec.ofNat 32 fscBmapstart)⌝ ∗
        ⌜vMagic.toNat = FSMAGIC⌝ ∗
        ⌜(hdrDec bsHdr).1 ≤ LOGBLOCKS⌝ ∗ ⌜(hdrDec bsHdr).2.Nodup⌝ ∗
        ⌜∀ b ∈ (hdrDec bsHdr).2, fsHome fscCov fscLogst b ∧ b ≠ SB_BNO⌝ ∗
        ⌜hdrN bsHdr = 0⌝ ∗ ⌜1 ∈ fscCov⌝ ∗ ⌜sbOld.length = 32⌝ ∗
        logFreeTok icfgLog ∗
        fsblock fscFs.bytes 1 bsSb ∗
        byteBuf KA.«sb» (DFrac.own 1) sbOld ∗
        excOwn fscFs.exc (hdrDec bsHdr).2 ∗
        iregBoot ∗
        kmapId logAddr ∗ kmapId (logAddr + 16#64) ∗
        wordPointsTo logAddr 4 (DFrac.own 1) vlock ∗
        wordPointsTo (logAddr + 8#64) 8 (DFrac.own 1) vname ∗
        wordPointsTo (logAddr + 16#64) 8 (DFrac.own 1) vcpu ∗
        wordPointsTo lStart 4 (DFrac.own 1) vStart ∗
        wordPointsTo lDev 4 (DFrac.own 1) vDev ∗
        wordPointsTo lOut 4 (DFrac.own 1) 0#32 ∗
        wordPointsTo lCmt 4 (DFrac.own 1) 0#32 ∗
        wordPointsTo lNcommit 4 (DFrac.own 1) vNc ∗
        wordPointsTo lhNAddr 4 (DFrac.own 1) vN ∗
        ([∗list] i ∈ List.range LOGBLOCKS, ∃ w : BitVec 32,
           wordPointsTo (lhBlock i) 4 (DFrac.own 1) w) ∗
        fsCacheAuth fscFs L ∗ fsDirtyAuth fscFs D ∗
        ([∗list] b ∈ fscCov.toList, fsDirtyHalf fscFs b false) ∗
        fsChalf fscFs (logHdrBno fscLogst) bsHdr ∗
        ([∗list] i ∈ List.range LOGBLOCKS, ∃ bs : List (BitVec 8),
           fsChalf fscFs (logSlotBno fscLogst i) bs) ∗
        bslots ((LOGBLOCKS + 2) + 2 + 1) ∗
        irefSlots 2 := by
  unfold firstFsinit
  iintro ⟨%vMagic, %vSize, %vNblocks, %vNlog, %bsSb, %sbOld, %bsHdr, %L, %D, %vlock, %vname,
    %vcpu, %vStart, %vDev, %vNc, %vN, %hp, H⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hp
  iexists vMagic, vSize, vNblocks, vNlog, bsSb, sbOld, bsHdr, L, D, vlock, vname, vcpu,
    vStart, vDev, vNc, vN
  isplitr; · ipureintro; exact h1
  isplitr; · ipureintro; exact h2
  isplitr; · ipureintro; exact h3
  isplitr; · ipureintro; exact h4
  isplitr; · ipureintro; exact h5
  isplitr; · ipureintro; exact h6
  isplitr; · ipureintro; exact h7
  isplitr; · ipureintro; exact h8
  iexact H

/-! ## 4.  THE TOKEN -/

/-- **Rocq `first_boot`**: the boot arm as a name of its own -- the
exclusive cell at 1, the persistent half, the SEALED allocator count (named,
at `fsReadyKmem`: what `fsReady`'s row wants), and fsinit's pile. -/
def firstBoot [Fscfg] [Icfg] [CurCtx] : IProp GF := iprop(
  wordPointsTo firstAddr 4 (DFrac.own 1) 1#32 ∗
  firstBootPersist (hlc := hlc) ∗ kallocAvail fsReadyKmem none ∗ firstFsinit)

/-- **Rocq `first_done`**: the steady arm, persistent (deviation 1:
`fsabs_env` dropped). -/
def firstDone [Fscfg] [Icfg] [CurCtx] : IProp GF := iprop(
  wordPointsTo firstAddr 4 DFrac.discard 0#32 ∗ fsReady (hlc := hlc))

instance firstDone_persistent [Fscfg] [Icfg] [CurCtx] :
    Persistent (firstDone (hlc := hlc) (GF := GF)) := by
  unfold firstDone; infer_instance

/-- **Rocq `first_tok`**: the boot arm, or the steady arm. -/
def firstTok [Fscfg] [Icfg] [CurCtx] : IProp GF := iprop(
  firstBoot (hlc := hlc) ∨ (wordPointsTo firstAddr 4 DFrac.discard 0#32 ∗ fsReady (hlc := hlc)))

/-- Rocq `first_tok_done`: the steady arm's two rows make a token. -/
theorem firstTok_done [Fscfg] [Icfg] [CurCtx] :
    wordPointsTo (GF := GF) firstAddr 4 DFrac.discard 0#32 ⊢
      fsReady (hlc := hlc) -∗ firstTok (hlc := hlc) := by
  unfold firstTok
  iintro H F
  iright
  isplitl [H]
  · iexact H
  · iexact F

/-- Rocq `first_tok_of_done`: how kfork pays the child's block. -/
theorem firstTok_of_done [Fscfg] [Icfg] [CurCtx] :
    firstDone (hlc := hlc) (GF := GF) ⊢ firstTok (hlc := hlc) := by
  unfold firstDone firstTok
  iintro H
  iright
  iexact H

/-- Rocq `first_tok_open`: the destructor, the two arms by name. -/
theorem firstTok_open [Fscfg] [Icfg] [CurCtx] :
    firstTok (hlc := hlc) (GF := GF) ⊢
      (wordPointsTo firstAddr 4 (DFrac.own 1) 1#32 ∗
        firstBootPersist (hlc := hlc) ∗ kallocAvail fsReadyKmem none ∗ firstFsinit) ∨
      firstDone (hlc := hlc) := by
  unfold firstTok firstBoot firstDone
  iintro H
  iexact H

/-- Rocq `first_tok_boot`. -/
theorem firstTok_boot [Fscfg] [Icfg] [CurCtx] :
    wordPointsTo (GF := GF) firstAddr 4 (DFrac.own 1) 1#32 ⊢
      firstBootPersist (hlc := hlc) -∗ kallocAvail fsReadyKmem none -∗ firstFsinit -∗
      firstTok (hlc := hlc) := by
  unfold firstTok firstBoot
  iintro H P K F
  ileft
  isplitl [H]
  · iexact H
  isplitl [P]
  · iexact P
  isplitl [K]
  · iexact K
  · iexact F

/-- Rocq `first_boot_intro`. -/
theorem firstBoot_intro [Fscfg] [Icfg] [CurCtx] :
    wordPointsTo (GF := GF) firstAddr 4 (DFrac.own 1) 1#32 ⊢
      firstBootPersist (hlc := hlc) -∗ kallocAvail fsReadyKmem none -∗ firstFsinit -∗
      firstBoot (hlc := hlc) := by
  unfold firstBoot
  iintro H P K F
  isplitl [H]
  · iexact H
  isplitl [P]
  · iexact P
  isplitl [K]
  · iexact K
  · iexact F

/-- Rocq `first_boot_open`. -/
theorem firstBoot_open [Fscfg] [Icfg] [CurCtx] :
    firstBoot (hlc := hlc) (GF := GF) ⊢
      wordPointsTo firstAddr 4 (DFrac.own 1) 1#32 ∗
        firstBootPersist (hlc := hlc) ∗ kallocAvail fsReadyKmem none ∗ firstFsinit := by
  unfold firstBoot
  iintro H
  iexact H

/-- Rocq `first_tok_of_boot`. -/
theorem firstTok_of_boot [Fscfg] [Icfg] [CurCtx] :
    firstBoot (hlc := hlc) (GF := GF) ⊢ firstTok (hlc := hlc) := by
  unfold firstTok
  iintro H
  ileft
  iexact H

/-- **Rocq `first_boot_done_excl`**, THE MODE SEAM'S REFUTATION: a boot
record and a steady resume are the same address at incompatible values. -/
theorem firstBoot_done_excl [Fscfg] [Icfg] [CurCtx] :
    firstBoot (hlc := hlc) (GF := GF) ⊢ firstDone (hlc := hlc) -∗ False := by
  unfold firstBoot firstDone
  iintro ⟨H1, -⟩ ⟨H0, -⟩
  iapply firstTok_boot_excl
  isplitl [H1]
  · iexact H1
  · iexact H0

/-! ## 5.  THE SEAL SITE'S fs ASSEMBLY -/

/-- **Rocq `first_persist_pre`, composed with `fs_ready_establish`**
(deviation 5): the persistent half main built, the count userinit sealed,
the log context and superblock cells fsinit returns (the cells persisted by
the caller), and the SEALED regime (`fsReady_seal` of fsinit's returned
`iregBoot`) are the whole runtime file system.  Recovery is done: initlog
sealed the byte view's exception set into `logCtx`, so the region and the
bitmap are upgraded to the sealed forms (`iregInv_of`, `bitmapInv_of`). -/
theorem firstPersistPre [Fscfg] [Icfg] [CurCtx] :
    firstBootPersist (hlc := hlc) (GF := GF) ⊢
      kallocAvail fsReadyKmem none -∗
      logCtx icfgLog fscBio fscFs fscCov fscLogst icfgDev -∗
      fsSbCells -∗ iregOpen -∗ fsReady (hlc := hlc) := by
  unfold firstBootPersist fsReady
  iintro ⟨#Hp, #Hb, #Hd, #Hi, #Ht, #Hs, #Hr, #Hm, #Hk, %Hg, #Hseam, #Hcert⟩ #HK #HL #HC #HO
  ihave #Hseal := logCtx_seal icfgLog fscBio fscFs fscCov fscLogst icfgDev $$ HL
  ihave #Hinv := iregInv_of (hlc := hlc) fscIreg fscFs icfgIst icfgNib $$ Hr Hseal
  ihave #Hbmi := bitmapInv_of fscFs fscBmapstart fscCov fscLogst fscSize $$ Hm Hseal
  isplitr; · iexact Hb
  isplitr; · iexact HL
  isplitr; · iexact Hd
  isplitr; · iexact Hi
  isplitr; · iexact Ht
  isplitr; · iexact Hs
  isplitr; · iexact Hinv
  isplitr; · iexact HO
  isplitr; · iexact Hk
  isplitr; · iexact HK
  isplitr; · ipureintro; exact Hg
  isplitr; · iexact HC
  isplitr; · iexact Hbmi
  isplitr; · iexact Hseam
  iexact Hcert

end FirstTok

end Xv6
