/-
Weak: **the static memory-ordering discipline of the kernel image**, as a decidable checker plus one
reflection fact (the definition side of the kernel site catalog).

Rocq: `iris/KernelSitesDef.v` @ xxvzwolszwmp (1cc222280).

Rocq header (verbatim, Rocq vocabulary):

    KernelSitesDef.v -- the STATIC MEMORY-ORDERING DISCIPLINE of the kernel
    image, as a decidable checker plus one reflection fact.

    HAND-WRITTEN.  tools/gen_sites.py is the AUDIT tool that produced the site
    tables quoted below (and iris/KernelSites.v, which cross-checks a handful of
    them against the Sail decoder); this file is the formal object.

    Everything here is a pure computation over the tracked image bytes
    (Kernel.KernelInstrs.kernel_bytes) and the tracked symbol table
    (Kernel.KernelSyms).  There is deliberately NO Iris, NO Sail model and NO
    decode-layer import: the whole point of the artifact is that it is a fact
    about the IMAGE, checkable by [vm_compute], with the same trust shape as the
    generated [kd_<word>] decode catalogue.  (See the bridging writeup at the
    bottom of this file for what that trust shape does and does not buy.)

In this tree the audit tool is `tools/gen_weak_sites.py` (the Lean retarget of Rocq's
`tools/gen_sites.py`), and the decoder cross-check it emits is `Weak/KernelSites.lean`.  The
import discipline is kept: this file imports only the kernel image dump (`MachCSL.KernelElf`, the
bytes) and the symbol table (`Xv6.KernelImage`, `MachCSL.KernelSyms`) -- no Iris, no Sail model.

**Deviations from Rocq.**

1. THE IMAGE.  Lean proves the kernel of `Xv6/KernelImage.lean` (xv6-riscv b72cbac1, branch
   verified), not the Rocq weak line's (9dd28f5e).  The site lists and bounds are re-derived from it
   by `tools/gen_weak_sites.py`:
   * this kernel's `forkret` reads and clears its `first.1` flag with PLAIN, UNFENCED accesses
     (`lw a5,first.1` at `forkret+0x18`, `sw zero,first.1` at `forkret+0x28`: classic xv6, not the
     weak line's `__atomic_load_n`/`__atomic_store_n` revision), so the two forkret racy-read /
     release sites and their two fences are absent: `racyLoadPcs` and
     `acqFencePcs` have one entry (`main`), `releasePcs` and `relFencePcs` two (`release`, `main`);
     every other site has the Rocq offset (`main+0x16/0x18/0xac/0xb0`, `release+0x16/0x1a`,
     `acquire+0x1c`); the four full fences sit at `virtio_disk_rw+0x186/0x196` and
     `virtio_disk_intr+0x2c/0x3e`, the fence.i at `userret+0x0`;
   * `textHi` is `0x80006126` (Rocq `0x80006124`): the dump's last text entry is the 2-byte `unimp`
     at `0x80006124`.  The flat walk visits 9095 positions, a superset of the 8814 real
     instructions of `Kernel.text` (the generator checks the containment, as Rocq's did).
2. THE BYTES.  Rocq's `kernel_bytes` is the text section only; Lean's dump `KernelElf.elfByte` is
   the whole loaded segment, so `kbyte` reads it inside `[textLo, textHi)` and is `0` outside --
   Rocq's "0 outside the text" default, unchanged.  (`Xv6.BootCarve` ties `elfByte` to
   `Kernel.text` byte for byte; nothing here depends on that.)
3. TYPES.  Addresses are `Int` (Rocq `Z`), so that pc arithmetic with negative offsets downstream
   (`KernelPinsDef`'s branch targets) stays Rocq-shaped; WORDS and fields are `Nat` (Rocq `Z`; a
   word is always in `[0, 2^32)`), and `wfield w hi lo` takes `hi lo : Nat` -- all call sites are
   literals with `lo ≤ hi`, and the `Nat` form is what the kernel evaluates natively (the
   `Weak/WeakDeps.lean` recipe).  `wSize` returns `Int` (it is added to addresses).
4. `forallb` ↦ `List.all`, `hd_error` ↦ `List.head?`, `In` ↦ `∈`, `Z.testbit` ↦ `Nat.testBit`,
   `Z.land` ↦ `&&&`, `Z.shiftr` ↦ `>>>`, `Z.ones k` ↦ `% 2 ^ k`, `walk_fuel`'s `Z.to_nat 12000`
   ↦ the literal `12000` (Lean `Nat` literals are binary).  `vm_cast_no_check (eq_refl true)` ↦
   `decide +kernel`; the six reflection facts stay separate theorems, as in Rocq.
5. The bridging writeup (section 6) is Rocq's, verbatim; its forkret discussion describes the Rocq
   image (deviation 1).

**Drift:** none (no SC dependency beyond the image dump and the symbol table).

**Name map** (Rocq → Lean): `kbyte`→`kbyte`, `kw`→`kw`, `wfield`→`wfield`, `w_is_rvc`→`wIsRvc`,
`w_size`→`wSize`, `w_op`→`wOp`, `w_f3`→`wF3`, `w_is_fence`→`wIsFence`,
`w_fence_pred/succ`→`wFencePred/Succ`, `w_fence_pr/pw/sr/sw`→`wFencePr/Pw/Sr/Sw`,
`w_is_acq_fence`→`wIsAcqFence`, `w_is_rel_fence`→`wIsRelFence`, `w_is_full_fence`→`wIsFullFence`,
`w_is_amoop`→`wIsAmoop`, `w_amo_funct5`→`wAmoFunct5`, `w_amo_aq/rl`→`wAmoAq/Rl`,
`w_is_lr/sc/amo`→`wIsLr/Sc/Amo`, `c_quad`→`cQuad`, `c_f3`→`cF3`,
`w_is_plain_load/store`→`wIsPlainLoad/Store`, `site_okb`→`siteOkb`, `text_lo/hi`→`textLo/Hi`,
`walk_fuel`→`walkFuel`, `text_addrs`→`textAddrs`, `text_pcs`→`textPcs`,
`text_stream`→`textStream`, `text_end`→`textEnd`, `chain`→`KernelSitesDef.chain` (file-qualified: a duplicate Rocq name),
`racy_load_siteb/site`→`racyLoadSiteb/Site`, `release_siteb/site`→`releaseSiteb/Site`,
`amo_siteb/site`→`amoSiteb/Site`, `acq_fence_siteb`→`acqFenceSiteb`,
`rel_fence_siteb`→`relFenceSiteb`, `racy_load_pcs`→`racyLoadPcs`, `release_pcs`→`releasePcs`,
`amo_pcs`→`amoPcs`, `acq_fence_pcs`→`acqFencePcs`, `rel_fence_pcs`→`relFencePcs`,
`image_disciplineb`→`imageDisciplineb`, `kernel_discipline`→`kernelDiscipline`,
`racy_load_pcs_ok`→`racyLoadPcsOk`, `release_pcs_ok`→`releasePcsOk`, `amo_pcs_ok`→`amoPcsOk`,
`acq_fence_pcs_ok`→`acqFencePcsOk`, `rel_fence_pcs_ok`→`relFencePcsOk`,
`kernel_sites_ok`→`kernelSitesOk`, `racy_load_sites`→`racyLoadSites`,
`release_sites`→`releaseSites`, `amo_sites`→`amoSites`.

**Not ported:** none.

**Statements checked** (by hand against Rocq): every definition and all eleven lemmas; the site
lists against `tools/gen_weak_sites.py --lists`.
-/
import MachCSL.KernelElf
import Xv6.KernelImage

namespace Weak

open MachCSL

/-! ## 1. The image, as words -/

/-- The text image's bounds (Rocq: "from the tracked dump's own header"; here the first and
one-past-last addresses of `Xv6.Kernel.text`).  `textHi` is checked, not assumed: the walk below
must land on it exactly, which is the `textEnd == textHi` conjunct of `imageDisciplineb`.  A
re-dump that grows, shrinks or re-aligns the image fails that conjunct rather than silently
checking a prefix. -/
def textLo : Int := 0x80000000
def textHi : Int := 0x80006126

/-- A byte of the tracked text image; 0 outside it (deviation 2).  The `textEnd` guard in
`imageDisciplineb` is what keeps that default from silently swallowing a re-dump that moved the
image's end. -/
def kbyte (a : Int) : Nat :=
  if textLo ≤ a ∧ a < textHi then KernelElf.elfByte (a - (KernelElf.elfBase : Int)).toNat else 0

/-- The 4-byte little-endian fetch window at `a`.  For a compressed instruction only the low half
is the instruction; every classifier below that reads a base field is guarded by
`!(wIsRvc w)`, so the high half of a compressed window is never consulted.  This mirrors the
fetch of `Xv6.KernelText` (that correspondence is not proved here). -/
def kw (a : Int) : Nat :=
  kbyte a + 256 * kbyte (a + 1) + 65536 * kbyte (a + 2) + 16777216 * kbyte (a + 3)

/-! ## 2. Word-level instruction classification -/

/-- Bits `[hi:lo]` of `w` (deviation 3). -/
def wfield (w hi lo : Nat) : Nat := (w >>> lo) % 2 ^ (hi - lo + 1)

def wIsRvc (w : Nat) : Bool := !(w &&& 3 == 3)
def wSize (w : Nat) : Int := if wIsRvc w then 2 else 4

/-- bits 6:0, base only -/
def wOp (w : Nat) : Nat := w &&& 127
/-- bits 14:12, base only -/
def wF3 (w : Nat) : Nat := wfield w 14 12

/-- FENCE (opcode 0001111, funct3 = 000). -/
def wIsFence (w : Nat) : Bool :=
  !(wIsRvc w) && (wOp w == 15) && (wF3 w == 0)
/-- PI PO PR PW -/
def wFencePred (w : Nat) : Nat := wfield w 27 24
/-- SI SO SR SW -/
def wFenceSucc (w : Nat) : Nat := wfield w 23 20

def wFencePr (w : Nat) : Bool := (wFencePred w).testBit 1
def wFencePw (w : Nat) : Bool := (wFencePred w).testBit 0
def wFenceSr (w : Nat) : Bool := (wFenceSucc w).testBit 1
def wFenceSw (w : Nat) : Bool := (wFenceSucc w).testBit 0

/-! The two DISCIPLINE fences, spelled EXACTLY -- not "has the pr/sw bits".
`fence iorw,iorw` (0x0ff0000f, gcc's `__sync_synchronize`, four sites in the virtio driver) also
has pr, pw and sw set, and it is deliberately NOT a discipline site: a full fence orders
everything around it and imposes no adjacency requirement on its neighbours.  Folding it into
the acquire / release classes would make `imageDisciplineb` false for this image and would be the
wrong claim anyway. -/

/-- `fence r,rw` = 0x0230000f -/
def wIsAcqFence (w : Nat) : Bool :=
  wIsFence w && (wFencePred w == 2) && (wFenceSucc w == 3)
/-- `fence rw,w` = 0x0310000f -/
def wIsRelFence (w : Nat) : Bool :=
  wIsFence w && (wFencePred w == 3) && (wFenceSucc w == 1)
/-- `fence iorw,iorw` -/
def wIsFullFence (w : Nat) : Bool :=
  wIsFence w && (wFencePred w == 15) && (wFenceSucc w == 15)

/-- AMO / LR / SC (opcode 0101111). -/
def wIsAmoop (w : Nat) : Bool := !(wIsRvc w) && (wOp w == 47)
def wAmoFunct5 (w : Nat) : Nat := wfield w 31 27
def wAmoAq (w : Nat) : Bool := w.testBit 26
def wAmoRl (w : Nat) : Bool := w.testBit 25
def wIsLr (w : Nat) : Bool := wIsAmoop w && (wAmoFunct5 w == 2)
def wIsSc (w : Nat) : Bool := wIsAmoop w && (wAmoFunct5 w == 3)
def wIsAmo (w : Nat) : Bool :=
  wIsAmoop w && !(wIsLr w) && !(wIsSc w)

/-! Plain (non-atomic, non-ordered) integer loads and stores.
Base: LOAD (0000011) / STORE (0100011).  Compressed: quadrant 0 and 2 of the C extension,
funct3 2/3 = word/doubleword load, 6/7 = word/doubleword store (C.LW / C.LD / C.LWSP / C.LDSP /
C.SW / C.SD / C.SWSP / C.SDSP).  Deliberately STRICT: floating-point loads/stores (0000111 /
0100111, and the C.FLD / C.FSD family) are NOT in these classes.  Strict is the safe direction --
a wider class would let the checker ACCEPT a discipline fence whose neighbour is not an integer
access.  xv6 has no kernel FP, so nothing is lost; if that ever changes the checker reports it as
a violation rather than passing silently. -/

def cQuad (w : Nat) : Nat := w &&& 3
def cF3 (w : Nat) : Nat := wfield w 15 13

def wIsPlainLoad (w : Nat) : Bool :=
  if wIsRvc w
  then ((cQuad w == 0) || (cQuad w == 2)) && ((cF3 w == 2) || (cF3 w == 3))
  else (wOp w == 3)

def wIsPlainStore (w : Nat) : Bool :=
  if wIsRvc w
  then ((cQuad w == 0) || (cQuad w == 2)) && ((cF3 w == 6) || (cF3 w == 7))
  else (wOp w == 35)

/-! ## 3. The per-position discipline check -/

/-- `siteOkb prev w next`: the discipline obligation of ONE instruction, given its PROGRAM-ORDER
neighbours' words (`none` at the ends of the text).

The neighbours are the stream predecessor/successor, NOT the words at pc-4 / pc+4.  That is a
deviation from the design sketch in design/weak-memory-phi-upgrade.md 2, and it is forced by the
image: the racy load in this kernel is COMPRESSED (c.lw, 2 bytes), so its acquire fence sits at
pc+2.  The release stores happen to be at fence_pc+4 because FENCE is always 4 bytes -- so
`releaseSite` below can and does use the pc-4 spelling, while `racyLoadSite` must use
`pc + wSize (kw pc)`.

Three clauses, one per site class:
* (acq) a `fence r,rw` is immediately PRECEDED by a plain load -- i.e. every acquire fence in the
  image is the tail of a racy-read site, so a racy read cannot be "the load with no fence after
  it";
* (rel) a `fence rw,w` is immediately FOLLOWED by a plain store -- every release fence in the
  image is the head of a release-flag site;
* (amo) every atomic memory operation carries .aq, and no LR/SC pair occurs in the image at all
  (xv6 locks with amoswap, and the page-table walker's CAS is the hardware's, not the kernel's).

What this does NOT say -- and cannot, at word level -- is that every store to a racy byte is at a
release site: which bytes a load/store touches is not a function of the encoding word.  That
direction is covered by the source-level audit in tools/gen_weak_sites.py (see the writeup at the
bottom). -/
def siteOkb (prev : Option Nat) (w : Nat) (next : Option Nat) : Bool :=
  (if wIsAcqFence w
   then match prev with | some p => wIsPlainLoad p | none => false
   else true)
  && (if wIsRelFence w
      then match next with | some n => wIsPlainStore n | none => false
      else true)
  && (if wIsAmoop w then wAmoAq w && !(wIsLr w) && !(wIsSc w)
      else true)

/-! ## 4. The whole-image fold -/

/-- Fuel: an upper bound on the number of 2-byte steps in the text.  The walk is exact for the
real instruction stream (see below); the slack covers the inter-function padding, which the walk
steps through in 2-byte increments. -/
def walkFuel : Nat := 12000

/-- The instruction addresses of the text, in stream order.  A flat walk from `textLo` stepping by
the decoded width visits a SUPERSET of the real instruction boundaries (verified by
tools/gen_weak_sites.py against `Xv6.Kernel.text`: 9095 flat positions, of which all 8814 real
instruction addresses; the extra ones are inter-function alignment padding, none of which
classify as a fence, an AMO, a load or a store).  A superset is the SOUND direction: the checker
imposes the discipline at at least every instruction the machine can fetch. -/
def textAddrs : Nat → Int → List Int
  | 0, _ => []
  | f + 1, a => if a < textHi then a :: textAddrs f (a + wSize (kw a)) else []

def textPcs : List Int := textAddrs walkFuel textLo
def textStream : List Nat := textPcs.map kw

/-- Where the walk stopped.  If the fuel ran out, or a mis-sized step desynced the walk, this is
not `textHi`. -/
def textEnd : Int :=
  match textPcs.reverse with
  | [] => textLo
  | a :: _ => a + wSize (kw a)

/-- The fold (file-qualified: Rocq `chain` is also a `WeakRvwmoKillArms` name). -/
def KernelSitesDef.chain : Option Nat → List Nat → Bool
  | _, [] => true
  | prev, w :: rest => siteOkb prev w rest.head? && KernelSitesDef.chain (some w) rest

/-! ## 5. The site predicates, the enumerated sites, the reflection facts

The predicates a weak-memory LEAF RULE takes as its pure side condition.  Boolean-valued, so a
leaf instantiated at a concrete pc discharges its premise by `decide +kernel` over four byte
lookups. -/

def racyLoadSiteb (pc : Int) : Bool :=
  wIsPlainLoad (kw pc) && wIsAcqFence (kw (pc + wSize (kw pc)))
def racyLoadSite (pc : Int) : Prop := racyLoadSiteb pc = true

def releaseSiteb (pc : Int) : Bool :=
  wIsRelFence (kw (pc - 4)) && wIsPlainStore (kw pc)
def releaseSite (pc : Int) : Prop := releaseSiteb pc = true

def amoSiteb (pc : Int) : Bool := wIsAmo (kw pc) && wAmoAq (kw pc)
def amoSite (pc : Int) : Prop := amoSiteb pc = true

def acqFenceSiteb (pc : Int) : Bool := wIsAcqFence (kw pc)
def relFenceSiteb (pc : Int) : Bool := wIsRelFence (kw pc)

/-! ### The enumerated sites (tools/gen_weak_sites.py --lists) -/

/-- Racy reads: the acquire-load of a publication flag.
`main+0x16   c.lw a5,0(a4) ; started   (main.c, the boot spin)` -/
def racyLoadPcs : List Int :=
  [ (KernelSyms.«main» : Int) + 0x16 ]

/-- Release-flag stores: the plain store immediately after a `fence rw,w`.
`release+0x1a  sw zero,0(s1) ; lk->locked = 0  (spinlock.c)`,
`main+0xb0     c.sw a4,0(a5) ; started = 1` -/
def releasePcs : List Int :=
  [ (KernelSyms.«release» : Int) + 0x1a
  , (KernelSyms.«main» : Int) + 0xb0 ]

/-- Atomics: the ONE atomic memory operation in the whole image.
`acquire+0x1c  amoswap.w.aq a5,a5,(s1)` -/
def amoPcs : List Int :=
  [ (KernelSyms.«acquire» : Int) + 0x1c ]

/-- The discipline fences themselves. -/
def acqFencePcs : List Int :=
  [ (KernelSyms.«main» : Int) + 0x18 ]
def relFencePcs : List Int :=
  [ (KernelSyms.«release» : Int) + 0x16
  , (KernelSyms.«main» : Int) + 0xac ]

/-- `imageDisciplineb` is the WHOLE-IMAGE walk; the five `List.all`s below are the per-class
enumerations.  (Rocq keeps them as separate `Qed`s because peeling a conjoined boolean apart made
its kernel re-reduce the walk lazily and overflow; they stay separate here, and `kernelSitesOk`
bundles them by assembly only.) -/
def imageDisciplineb : Bool :=
  (textEnd == textHi) && KernelSitesDef.chain none textStream

theorem kernelDiscipline : imageDisciplineb = true := by decide +kernel

/-! ### The whole-image summary lemmas, one per class -/

theorem racyLoadPcsOk : racyLoadPcs.all racyLoadSiteb = true := by decide +kernel
theorem releasePcsOk : releasePcs.all releaseSiteb = true := by decide +kernel
theorem amoPcsOk : amoPcs.all amoSiteb = true := by decide +kernel
theorem acqFencePcsOk : acqFencePcs.all acqFenceSiteb = true := by decide +kernel
theorem relFencePcsOk : relFencePcs.all relFenceSiteb = true := by decide +kernel

/-- The single fact a consumer cites.  Pure assembly of the six above. -/
theorem kernelSitesOk :
    imageDisciplineb = true
    ∧ racyLoadPcs.all racyLoadSiteb = true
    ∧ releasePcs.all releaseSiteb = true
    ∧ amoPcs.all amoSiteb = true
    ∧ acqFencePcs.all acqFenceSiteb = true
    ∧ relFencePcs.all relFenceSiteb = true :=
  ⟨kernelDiscipline, racyLoadPcsOk, releasePcsOk, amoPcsOk, acqFencePcsOk, relFencePcsOk⟩

/-! The pointwise forms a consumer actually applies.  Pure list plumbing over the reflection
facts above -- no image computation. -/

theorem racyLoadSites : ∀ pc, pc ∈ racyLoadPcs → racyLoadSite pc :=
  List.all_eq_true.1 racyLoadPcsOk

theorem releaseSites : ∀ pc, pc ∈ releasePcs → releaseSite pc :=
  List.all_eq_true.1 releasePcsOk

theorem amoSites : ∀ pc, pc ∈ amoPcs → amoSite pc :=
  List.all_eq_true.1 amoPcsOk

/-! ## 6. BRIDGING DESIGN -- how these facts discharge the Layer-1 premises

Rocq's writeup, verbatim (Rocq vocabulary; its forkret sites are the Rocq image's, deviation 1).

This is the design writeup for the premise-discharge split recorded as D-M6-8 in
completed/weak-memory-m6.md, and for the "site predicates + whole-image enumeration" item in
design/weak-memory-phi-upgrade.md 2.  It lives here rather than in claude-notes/ because it is the
contract of THIS file: what a consumer may conclude from [kernel_discipline] and the five
enumeration lemmas, and -- at least as important -- what it may not.

### 6.1  WHERE THIS SITS IN D-M6-8

D-M6-8 splits each Layer-1 premise (rf_edges_ok, ee_ok, byte_ok) into
  (a) MACHINE-side facts -- EXT/COH/view arithmetic, [covered], the waw-cover inequality:
      statements about the traced wstates, provable per-trace;
  (b) VALUE-INDEPENDENT SITE facts -- "the reading instruction's aq bit", "the fence is the
      instruction immediately after the racy load / immediately before the release store":
      functions of the PC alone, which arm (b) makes available at pcs the minimal-cycle structure
      shows to be Iris-supported;
  (c) the RESIDUE -- the same site facts at positions po-after an unsupported read, where no
      Iris-derived export can reach, and only a static, value-independent property of the image
      can help.

This file mechanizes (c) and, in doing so, supplies (b) for free.  Its value over any interp
export is that it is SUPPORT-INDEPENDENT: a value-blind forall-over-the-text statement, true at
every pc in the image whether or not that pc is pf-reachable, whether or not Iris ever visits it.
That is exactly the shape (c) needs and exactly the shape a state-interp conjunct cannot have.

### 6.2  WHICH PREMISE CONSUMES WHICH SITE CLASS

* [edges_split]'s DISCIPLINED arm (the WRITER side) consumes [release_pcs] / [rel_fence_pcs].
  M6's fenced arm (ii) needs: a certifiable promise of a release-fenced store already has all of
  that writer's pre-fence stores below it in the log.  The PC-level input to that argument is
  precisely [release_site pc] -- the [fence rw,w] is the instruction immediately before the flag
  store in program order, so every earlier write of the agent is fence-ordered before the flag
  write.  [release_pcs_ok] gives it at all three sites; [kernel_discipline]'s (rel) clause gives
  the converse closure (no [fence rw,w] anywhere in the image fails to head a store), which is
  what rules out a fourth, unenumerated release shape appearing after a re-dump.

* [ee_ok]'s FENCE-COVER arm (the READER side) consumes [racy_load_pcs] / [acq_fence_pcs] and
  [amo_pcs].  A racy read at [pc] has [fence r,rw] as its po-successor, so every later access of
  that agent is ordered after the read -- the cover [ee_ok] asks for.  An AMO read gets the same
  cover with no fence at all, from its own .aq bit: [amo_pcs_ok] is that fact, and
  [kernel_discipline]'s (amo) clause extends it to EVERY atomic in the image (there is exactly
  one, [acquire]'s amoswap.w.aq) and records that the image contains no LR/SC, so no
  reservation-based discipline is owed.

* [byte_ok] is NOT consumed here.  Per design/weak-memory-phi-upgrade.md 2 it becomes structural
  from the C/D/S points-to (S-bytes ARE the sync bytes).  What this effort contributes to it is
  the AUDIT that the S-byte set is the one the design assumes: tools/sites.md's racy-byte
  reference audit shows the only bytes a discipline site touches are [started] and [first.1],
  each referenced exactly twice in the whole image -- once by its own acquire-load site, once by
  its own release-store site.  Lock words stay CLEAN by the landed C/D/S decision (nothing
  racy-READS them; the spin is [ak_latest] through the AMO), so they are not S bytes and need no
  release-site membership beyond [release+0x1a].

### 6.3  DELIVERY: HOW A SITE FACT REACHES A LEAF PROOF

NOT by threading a standalone side condition down through the leaf interfaces.  Delivery rides
the persistent instruction facts that every kernel-code proof already holds:

  * [KernelText.kernel_text] is persistent and hart-independent (its points-to are
    [DfracDiscarded]), so any proof that has it can extract [instr pc rvc ast] at any text pc, at
    any hart, without borrowing.
  * The site classification is a fact about THE SAME BYTES.  A leaf instantiated at a concrete pc
    discharges [racy_load_siteb pc = true] by [vm_compute] over four byte lookups -- no new
    hypothesis crosses the interface, and no caller has to supply anything.
  * For a pc the Iris proof never names, the whole-image lemmas do the work instead.  That is the
    division of labour: [instr] carries the site fact where a proof is standing,
    [kernel_discipline] carries it everywhere else.

### 6.4  THE TWO DYNAMIC STATE-INTERP CONJUNCTS (post-L0, weak side)

To be added to the weak state interpretation -- NOT here; this file must stay free of Weak*
imports.  For each hart c, with [ws c] its discipline flags:

  w_relp  (ws c) = true  ->  sstatus.SIE c = 0 /\ release_siteb   (pc c) = true
  w_racyp (ws c) = true  ->  sstatus.SIE c = 0 /\ racy_load_siteb (pcprev c) = true

("armed" = the flag is set; the writer flag is armed by the release fence and consumed by the
flag store, the reader flag is armed by the racy load and consumed by the acquire fence.)
Preservation:

  ESTABLISH  the fence leaf (resp. the racy-load leaf) sets the flag and establishes both
             conjuncts: the site conjunct from [rel_fence_pcs_ok] / [acq_fence_pcs_ok] plus the
             adjacency the site predicate itself states, and SIE = 0 from the resource the
             site's region already carries (push_off's interrupt-disable, or the pre-scheduler
             boot state).
  CONSUME    the flag store (resp. the acquire fence) clears it.
  NO TRAP    trap entry cannot fire while armed: an interrupt needs sstatus.SIE = 1 and the
             conjunct says it is 0.  (A synchronous exception at the flag access is excluded
             separately, by kpt_inv's residency/permission facts for the accessed byte -- not by
             this conjunct.)
  NO DRIFT   no OTHER instruction can run while armed, by adjacency: the site predicate says the
             very next (resp. previous) instruction is the paired access, so the flag cannot
             survive an unrelated step.

The point of the SIE = 0 conjunct is that it makes preemption-between-the-fence-and-the-access
UNREPRESENTABLE rather than merely unlikely, which is what ingredient (2) of the transfer theorem
below needs.  Two facts make it discharge-able for THIS kernel:

  * every enumerated site is in an interrupts-off region.  The audit is in tools/sites.md; the
    arguments are push_off brackets (acquire, release, virtio_disk_rw, virtio_disk_intr), the
    pre-scheduler boot path (main: start() sets sie.SEIE/STIE but never sstatus.SIE, and the
    kernel's FIRST intr_on() is inside scheduler(), which main reaches only after the [started]
    publication), and -- the one delicate case -- forkret.
  * FORKRET IS THE FRAGILE ONE, AND IT IS FRAGILE IN THE SOURCE, NOT HERE.  forkret's two [first]
    sites sit AFTER [release(&p->lock)], i.e. after a pop_off.  They are nonetheless
    interrupts-off only because scheduler() does [intr_on(); intr_off();] before
    [acquire(&p->lock)], so the matching push_off recorded intena = 0 and forkret's pop_off does
    not re-enable.  An xv6 revision that drops that intr_off() (the classic scheduler has only
    intr_on()) would leave forkret's acquire-load and release-store INTERRUPTIBLE and would break
    the conjunct above -- with no change to the image discipline this file checks.  Re-audit on
    any xv6 bump.
  * the timer is sstc (S-mode stimecmp), so SIE = 0 genuinely excludes interposition: there is no
    M-mode timervec that stores to a scratch area behind the hart's back while S-mode interrupts
    are masked.

### 6.5  THE TRANSFER THEOREM (STATED, NOT PROVED)

The skeleton the above is aimed at.  Informally, over a full-machine behavior b of the weak
model:

  image_disciplineb = true ->
  forall e in events(b), pc_of e in text ->
       (plain_read e  /\ racy e      -> ee_ok's fence-cover component at e)
    /\ (plain_write e /\ published e -> edges_split's disciplined component at e)

with NO hypothesis that e is pf-supported -- that absence is the whole point.  It has exactly
three ingredients:

  (1) TEXT FETCH DETERMINISM.  The word fetched at pc is [kw pc].  On the SC side this is
      immediate: the text points-to are [DfracDiscarded], so no agent can hold the write
      permission.  On the weak side it is the statement that no write message ever targets a
      text byte, i.e. the text bytes are never in any [w] footprint -- an invariant of the same
      family as [sail_shaped], and the reason Decision 4's fetch reads fixed text rides this same
      sweep.
  (2) ARMED => SIE-OFF ADJACENCY (6.4).  Without it, "the next instruction is the fence" is a
      statement about the program text that a trap between the two could falsify at the EVENT
      level.
  (3) LABEL-FROM-WORD DECODE.  The bitmask classification in section 2 must agree with the Sail
      decoder's label for the same word.  PRIMARY ROUTE: the CATALOGUE.  KernelDecode*.v already
      holds a [kd_<word>] lemma for every word of the covered set, so a generated companion
      (iris/KernelSites.v, from tools/gen_sites.py --emit-coq) derives the per-pc decode fact by
      LOOKUP -- every proof there is [exact kd_<w>], zero new decode computation -- and the
      forall-over-text statement is the enumeration of those.  FALLBACK, recorded and
      deliberately not taken first: generic "mask implies decode" lemmas over all words.  Those
      are where the decode-bridge trap lives -- FENCE, FENCEI, CSR and SHIFTIWOP words need
      [decode_bridge_ms_bv] rather than [decode_bridge_ms], because their AST field is NARROWER
      than the encoded field it is sliced from, and the failure prints two sides that look
      identical (durable-notes, gen_code.py's bridge selection).
      (Lean: there is no catalogue; `Weak/KernelSites.lean`, generated by
      tools/gen_weak_sites.py, proves each site's decode fact through
      `MachCSL.decodesAll32_bridge`/`decodesAll16_bridge`, the kernel evaluating the decoder.)

And note what is NOT an ingredient: [pc_of e in text] is MACHINE-ENFORCED, not assumed.  A fetch
goes through address translation; [kpt_inv] (completed/kpt-share.md, KptShare.v) pins the kernel
page table's leaves, and [check_PTE_permission] rejects a fetch from a page without X
(design/tlb-translation.md).  Only the text range is executable, so an event with a pc outside
the image has no fetch to speak of.

### 6.6  WHAT ENUMERATION ALONE DOES NOT GIVE

Honestly, and in the order they would bite:

  1. THE CLASSIFIER IS NOT THE DECODER.  Section 2 is a hand-written bitmask reading of the
     RISC-V encoding.  It is validated against the Sail decoder at the 15 enumerated sites
     (iris/KernelSites.v) and nowhere else.  Image-wide, "w_is_plain_load w = true iff the model
     decodes w to a load" is an unproven correspondence.  This is ingredient (3) above and it is
     the largest single gap here.
  2. THE BYTE DIRECTION IS NOT DECIDABLE FROM THE WORD.  Nothing in this file says "every store
     to a racy byte is at a release site" -- which byte an access touches is not a function of
     its encoding.  That direction is a SOURCE-LEVEL audit (tools/sites.md), and it is clean for
     this image (each publication flag is referenced exactly twice, by its own site).  A
     register-indirect store to a racy byte would be invisible to both the checker and the audit.
  3. THE INTERRUPTS-OFF ARGUMENT IS SOURCE-LEVEL.  6.4's SIE = 0 conjunct has to be
     re-established in the weak state interp from the actual push_off/boot resources; the audit
     only says the claim is TRUE of this kernel, and flags forkret as the one that depends on a
     scheduler() detail.
  4. THE WALK IS A SUPERSET, AND THAT IS A PYTHON FACT.  [text_addrs] visits every real
     instruction boundary (checked by tools/gen_sites.py against gen_code.py's per-symbol walk:
     8457 real, 9215 visited, containment exact) -- but that containment is not itself a Coq
     theorem.  What IS a Coq theorem is that the walk ends exactly at [text_hi], which is what
     catches a desync.
  5. D-M6-8 ARM (b) STILL OWES ITS COMBINATORIAL ARGUMENT.  The minimal-cycle/segment-head
     reasoning that makes a pc Iris-supported is untouched by this file.  What this file removes
     is the NEED for it at positions po-after an unsupported read -- there, the forall-over-text
     lemma stands in for support.
  6. FENCE.I AND SFENCE.VMA CARRY NO CLAIM.  They are enumerated (one fence.i, at userret+0x0)
     and deliberately outside the discipline: they order instruction fetch and translation, not
     data.
-/

end Weak
