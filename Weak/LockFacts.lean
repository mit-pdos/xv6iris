/-
Weak: **W11-F part [OWN.98] — the per-pc lock facts, IMAGE half**: the facts about xv6's lock
code that are facts of the kernel IMAGE alone, each a `decide +kernel` over the tracked bytes
(`KernelSitesDef.kw`, the flat text walk `textPcs`), in the style of `Weak/KernelSitesDef.lean`.
Lean-only, no Rocq twin.

What the image says about the lock protocol (this kernel, `Xv6/KernelImage.lean`):

* **the acquire** — `acquire+0x1c` is `amoswap.w.aq a5,a5,(s1)` (`LockFacts.acqWord`: AMOSWAP,
  word width, `.aq` set, `.rl` clear, `rd = rs2 = a5`, `rs1 = s1`), and it is the ONLY AMO / LR / SC
  of the whole text (`LockFacts.amoCensus`).  The swapped-in value is `a4 = 1`: `c.li a4,1` at
  `acquire+0x16`, `c.mv a5,a4` at `acquire+0x1a` (the spin loop's head), and the loop's `bnez` at
  `acquire+0x22` jumps back to `+0x1a` (`LockFacts.acqLoopWords`) — so every swap writes 1;
  that the register still holds 1 at the swap is a DATAFLOW fact of the run (named, see
  `Weak/LockFacts2.lean`).
* **the release** — `release+0x16` is `fence rw,w` (`pr pw sr sw = 1 1 0 1`,
  `LockFacts.relFenceBits`) and its stream successor `release+0x1a` is `sw zero,0(s1)`
  (`LockFacts.relStoreWord`: a plain word store of `x0`, i.e. of the zero word;
  `LockFacts.relAdj`: the fence is the instruction immediately before it in the walk).  The
  release is a PLAIN store after a `fence rw,w`, NOT an AMO (the W10 notes' "`fence rw,rw; fence
  iorw,ow; amoswap.w zero`" is another compiler's `__sync_lock_release`, not this image's).
* **the fences** — the whole text has seven `FENCE`s (`LockFacts.fenceCensus`): the two release
  fences `fence rw,w` (`release+0x16`, `main+0xac`), the boot acquire fence `fence r,rw`
  (`main+0x18`), and four `fence iorw,iorw` in the virtio driver; no other fence orders a store
  before a later store.
* **`initlock`** — `initlock+0x0a` is `sw zero,0(a0)` (`LockFacts.initStoreWord`): the PLAIN
  `lk->locked = 0`; `initlock` contains no fence (`fenceCensus`).

Spec: these are facts about the bytes (opcode/funct/aq/rl/fence-bit fields per the RISC-V
unprivileged ISA's encodings, the same field definitions `KernelSitesDef` uses); what an
instruction DOES (the label it emits) is Sail's, used in `Weak/LockFacts2.lean` through a named
realization interface.  Every name is file-qualified (`LockFacts.*`).
-/
import Weak.KernelSitesDef

namespace Weak

open MachCSL

/-! ## 1. The sites -/

/-- The acquire's swap: `acquire+0x1c`. -/
def LockFacts.acqPc : Int := (KernelSyms.«acquire» : Int) + 0x1c

/-- The release store: `release+0x1a` (the lock entry of `releasePcs`). -/
def LockFacts.relPc : Int := (KernelSyms.«release» : Int) + 0x1a

/-- `initlock`'s plain `lk->locked = 0`: `initlock+0x0a`. -/
def LockFacts.initPc : Int := (KernelSyms.«initlock» : Int) + 0x0a

/-- Register fields of a base-encoded word. -/
def LockFacts.wRd (w : Nat) : Nat := wfield w 11 7
def LockFacts.wRs1 (w : Nat) : Nat := wfield w 19 15
def LockFacts.wRs2 (w : Nat) : Nat := wfield w 24 20

theorem LockFacts.relPcMem : LockFacts.relPc ∈ releasePcs := by decide +kernel

theorem LockFacts.acqPcMem : LockFacts.acqPc ∈ amoPcs := by decide +kernel

/-! ## 2. The acquire -/

/-- `acquire+0x1c` is `amoswap.w.aq a5,a5,(s1)`: an AMO (not LR/SC), funct5 = AMOSWAP (1), word
width (funct3 = 2), `.aq` set, `.rl` clear, `rd = rs2 = a5` (15), `rs1 = s1` (9). -/
theorem LockFacts.acqWord :
    wIsAmo (kw LockFacts.acqPc) = true ∧ wAmoFunct5 (kw LockFacts.acqPc) = 1 ∧
    wF3 (kw LockFacts.acqPc) = 2 ∧ wAmoAq (kw LockFacts.acqPc) = true ∧
    wAmoRl (kw LockFacts.acqPc) = false ∧ LockFacts.wRd (kw LockFacts.acqPc) = 15 ∧
    LockFacts.wRs2 (kw LockFacts.acqPc) = 15 ∧ LockFacts.wRs1 (kw LockFacts.acqPc) = 9 := by
  decide +kernel

theorem LockFacts.acqAqBit : wAmoAq (kw LockFacts.acqPc) = true := LockFacts.acqWord.2.2.2.1

/-- **THE AMO CENSUS**: the only AMO/LR/SC position of the flat text walk is `acquire+0x1c`. -/
theorem LockFacts.amoCensus : textPcs.filter (fun p => wIsAmoop (kw p)) = amoPcs := by
  decide +kernel

/-- Every AMO-opcode position of the text walk is `acquire+0x1c`. -/
theorem LockFacts.amoUnique (p : Int) : p ∈ textPcs → wIsAmoop (kw p) = true → p = LockFacts.acqPc := by
  intro hp hw
  have h : p ∈ textPcs.filter (fun p => wIsAmoop (kw p)) := List.mem_filter.2 ⟨hp, hw⟩
  rw [LockFacts.amoCensus] at h
  simpa [amoPcs, LockFacts.acqPc] using h

/-- The swapped value's dataflow, as words: `c.li a4,1` at `acquire+0x16` (0x4705), `c.mv a5,a4`
at `acquire+0x1a` (0x87ba), and the loop's `c.bnez a5,-8` at `acquire+0x22` (0xffe5) back to
`+0x1a` — so the swap at `+0x1c` always swaps in `a4 = 1` (the register fact is the run's). -/
theorem LockFacts.acqLoopWords :
    kw ((KernelSyms.«acquire» : Int) + 0x16) % 65536 = 0x4705 ∧
    kw ((KernelSyms.«acquire» : Int) + 0x1a) % 65536 = 0x87ba ∧
    kw ((KernelSyms.«acquire» : Int) + 0x22) % 65536 = 0xffe5 ∧
    (KernelSyms.«acquire» : Int) + 0x1a + 2 = LockFacts.acqPc := by
  decide +kernel

/-! ## 3. The release -/

/-- `release+0x16` is `fence rw,w`: `pr pw sr sw = true true false true`. -/
theorem LockFacts.relFenceBits :
    wIsRelFence (kw (LockFacts.relPc - 4)) = true ∧
    wFencePr (kw (LockFacts.relPc - 4)) = true ∧ wFencePw (kw (LockFacts.relPc - 4)) = true ∧
    wFenceSr (kw (LockFacts.relPc - 4)) = false ∧ wFenceSw (kw (LockFacts.relPc - 4)) = true := by
  decide +kernel

/-- `release+0x1a` is `sw zero,0(s1)`: a base-encoded plain STORE (opcode 0100011) of word width
(funct3 = 2) whose data register is `x0` — it stores the zero word. -/
theorem LockFacts.relStoreWord :
    wIsPlainStore (kw LockFacts.relPc) = true ∧ wIsRvc (kw LockFacts.relPc) = false ∧
    wOp (kw LockFacts.relPc) = 35 ∧ wF3 (kw LockFacts.relPc) = 2 ∧
    LockFacts.wRs2 (kw LockFacts.relPc) = 0 ∧ LockFacts.wRs1 (kw LockFacts.relPc) = 9 ∧
    releaseSiteb LockFacts.relPc = true := by
  decide +kernel

/-- The fence is the store's immediate predecessor in the text walk. -/
theorem LockFacts.relAdj :
    LockFacts.relPc - 4 ∈ textPcs ∧ LockFacts.relPc ∈ textPcs ∧
    LockFacts.relPc - 4 + wSize (kw (LockFacts.relPc - 4)) = LockFacts.relPc := by
  decide +kernel

/-- Every release site (`releasePcs`) has a `fence rw,w` at `pc - 4` (`KernelSitesDef.releaseSites`),
so its fence's `pw`/`sw` bits are set. -/
theorem LockFacts.relSiteBits (p : Int) :
    p ∈ releasePcs → wFencePw (kw (p - 4)) = true ∧ wFenceSw (kw (p - 4)) = true := by
  intro hp
  have h := releaseSites p hp
  unfold releaseSite releaseSiteb at h
  have hf : wIsRelFence (kw (p - 4)) = true := by
    simp only [Bool.and_eq_true] at h; exact h.1
  unfold wIsRelFence at hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨⟨-, hpred⟩, hsucc⟩ := hf
  refine ⟨?_, ?_⟩
  · unfold wFencePw; rw [hpred]; rfl
  · unfold wFenceSw; rw [hsucc]; rfl

/-! ## 4. The fences and `initlock` -/

/-- **THE FENCE CENSUS** (FENCE, funct3 = 0; `fence.i` is not one): position, pred, succ. -/
theorem LockFacts.fenceCensus :
    (textPcs.filter (fun p => wIsFence (kw p))).map
        (fun p => (p, wFencePred (kw p), wFenceSucc (kw p))) =
      [ ((KernelSyms.«release» : Int) + 0x16, 3, 1)
      , ((KernelSyms.«main» : Int) + 0x18, 2, 3)
      , ((KernelSyms.«main» : Int) + 0xac, 3, 1)
      , ((KernelSyms.«virtio_disk_rw» : Int) + 0x186, 15, 15)
      , ((KernelSyms.«virtio_disk_rw» : Int) + 0x196, 15, 15)
      , ((KernelSyms.«virtio_disk_intr» : Int) + 0x2c, 15, 15)
      , ((KernelSyms.«virtio_disk_intr» : Int) + 0x3e, 15, 15) ] := by
  decide +kernel

/-- `initlock+0x0a` is `sw zero,0(a0)`: a plain word store of `x0` (`lk->locked = 0`). -/
theorem LockFacts.initStoreWord :
    wIsPlainStore (kw LockFacts.initPc) = true ∧ wIsRvc (kw LockFacts.initPc) = false ∧
    wF3 (kw LockFacts.initPc) = 2 ∧ LockFacts.wRs2 (kw LockFacts.initPc) = 0 ∧
    LockFacts.wRs1 (kw LockFacts.initPc) = 10 ∧ releaseSiteb LockFacts.initPc = false := by
  decide +kernel

end Weak
