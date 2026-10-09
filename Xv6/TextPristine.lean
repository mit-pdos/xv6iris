/-
**THE KERNEL'S READ-ONLY WINDOW IS PRISTINE** (weak-allocproc plan §C
Stage 0, item W3, first half).

`textPristine g`: every byte of the persisted window `[bcRoLo, bcRoHi)`
(`Xv6/BootCarve.lean`: `.text`, `.rodata`, `.eh_frame`, below `_data`) has,
in the machine's memory, exactly the history a fresh era gives it -- the
boot image's byte at timestamp 0, `[⟨0, 0, img a⟩]` (`bc_imgFlat_get`).
Not "no store targets the window" (an identical-value store would be
harmless and is not excluded by the program logic's per-step facts): a
per-STATE predicate.  `textPristine_read`/`textPristine_readBytes`: such a
byte is read as the image byte by EVERY agent (in particular the
instruction-cache agent `ifetchAgent cpu`) at EVERY view.

`textRo E`: the window's histories as DISCARDED points-to in era `E`'s heap
(what `bootRan_persist` makes of the window: at `MachGS.ofEra E …` it is
`bootRo (imgFlat bootImage) bcRoLo bcRoHi`, the source of `kernelText`,
`kernelText_intro`).  `powerInterp_textPristine` (the `powerInterp_mmOk`
twin): the state interpretation, with `textRo` of the era registered at the
current generation, gives `g.pow = true → textPristine g`.

What is NOT here (PROGRESS-W3.md): delivering `textRo` of the current era to
`riscvPowerAdequacy`'s final hook, hence the sibling root.
-/
import Xv6.BootCarve
import MachCSL.Adequacy

namespace Xv6

open Iris Iris.BI Iris.ProofMode Std MachCSL

/-- The persisted window's histories at a fresh era: the boot image's byte
at timestamp 0, at every address of `[bcRoLo, bcRoHi)`. -/
def textWin : MemF Hist := bcRanMem (imgFlat bootImage) bcRoLo bcRoHi

/-- **The read-only window is pristine** at `g`: every history of the
window is the fresh era's. -/
def textPristine (g : GState) : Prop :=
  ∀ (a : PAddr) (H : Hist), get? textWin a = some H → g.m.mem[a]? = some H

/-- The window's histories, address by address. -/
theorem textWin_get (a : PAddr) (hlo : bcRoLo ≤ a.toNat) (hhi : a.toNat < bcRoHi) :
    ∃ v, bootImage[a]? = some v ∧ get? textWin a = some [⟨0, 0, v⟩] := by
  have hram : inRam a 1 := by
    unfold inRam
    unfold bcRoLo at hlo
    unfold bcRoHi at hhi
    simp only [MachCSL.KernelSyms.«_data»] at hhi
    unfold ramEnd
    omega
  obtain ⟨v, hv⟩ := bootImage_wf.ram a hram
  refine ⟨v, hv, ?_⟩
  unfold textWin bcRanMem
  rw [LawfulPartialMap.get?_filter]
  show ((imgFlat bootImage)[a]?).bind _ = _
  rw [bc_imgFlat_get bootImage a v hram hv]
  simp [bcRanIn, hlo, hhi]

/-- **A pristine window byte is the image's, to every agent at every view.** -/
theorem textPristine_read (g : GState) (hp : textPristine g) (a : PAddr)
    (hlo : bcRoLo ≤ a.toNat) (hhi : a.toNat < bcRoHi) :
    ∃ v, bootImage[a]? = some v ∧ ∀ (ag : Agent) (tvn : Nat), g.m.mem.read ag tvn a = some v := by
  obtain ⟨v, hv, hw⟩ := textWin_get a hlo hhi
  refine ⟨v, hv, fun ag tvn => ?_⟩
  unfold FlatMem.read
  rw [hp a _ hw, Option.bind_some,
    Hist.read_cons_visible _ _ _ _ (HEnt.visible_of_le _ _ _ (Nat.zero_le _))]

/-- ...and a word of the window whose bytes the image holds is read whole,
by every agent at every view (the shape of `evStep`'s fetch arm,
`MachCSL/Lang.lean`). -/
theorem textPristine_readBytes (g : GState) (hp : textPristine g) (pa : PAddr) (n : Nat)
    (w : BitVec (8 * n))
    (hin : ∀ j, j < n → bcRoLo ≤ (pa + BitVec.ofNat 64 j).toNat ∧ (pa + BitVec.ofNat 64 j).toNat < bcRoHi)
    (himg : ∀ j, j < n → bootImage[pa + BitVec.ofNat 64 j]? = some (nthByte w j)) :
    ∀ (ag : Agent) (tvn : Nat), g.m.mem.readBytes ag tvn pa n w := by
  intro ag tvn j hj
  obtain ⟨h1, h2⟩ := hin j hj
  obtain ⟨v, hv, hr⟩ := textPristine_read g hp _ h1 h2
  rw [hr ag tvn]
  rw [himg j hj] at hv
  exact congrArg some (Option.some.inj hv).symm

section ghost
variable {hlc : HasLC} {GF : BundledGFunctors} [MachFixedGS hlc GF]

/-- The window, persisted, in era `E`'s heap. -/
def textRo (E : EraGS) : IProp GF := iprop%
  [∗map] a ↦ H ∈ textWin, pointsTo (G := E.mem) a DFrac.discard H

instance textRo_persistent (E : EraGS) : Persistent (textRo (GF := GF) E) := by
  unfold textRo; infer_instance

/-- A points-to of era `E`'s heap agrees with the heap's interpretation
(`genHeap_valid`, without the update). -/
theorem textPristine_eraLookup (E : EraGS) (m : MemF Hist) (a : PAddr) (dq : DFrac) (H : Hist) :
    genHeapInterp (G := E.mem) m ∗ pointsTo (G := E.mem) a dq H ⊢@{IProp GF} ⌜get? m a = some H⌝ := by
  unfold genHeapInterp pointsTo
  iintro ⟨⟨%m', -, Hσ, -⟩, Hl⟩
  iapply ghost_map_lookup $$ Hσ Hl

/-- Era `E`'s heap, against the persisted window, is pristine there. -/
theorem textRo_heap (E : EraGS) (m : MemF Hist) :
    genHeapInterp (G := E.mem) m ∗ textRo E ⊢@{IProp GF}
      ⌜∀ (a : PAddr) (H : Hist), get? textWin a = some H → get? m a = some H⌝ := by
  refine (forall_intro fun a => ?_).trans pure_forall.2
  refine (forall_intro fun H => ?_).trans pure_forall.2
  by_cases hw : get? textWin a = some H
  · unfold textRo
    iintro ⟨Hm, #Ht⟩
    ihave Hl := BigSepM.bigSepM_lookup (Φ := fun a H => iprop(pointsTo (G := E.mem) a DFrac.discard H)) hw $$ Ht
    ihave %h := textPristine_eraLookup E m a DFrac.discard H $$ [Hm Hl]
    · iframe Hm Hl
    ipureintro
    exact fun _ => h
  · iintro _
    ipureintro
    exact fun h => absurd h hw

/-- **`powerInterp_mmOk`'s twin**: the state interpretation, with the
persisted window of the era registered at the current generation, gives the
pristine window whenever the power is on. -/
theorem powerInterp_textPristine (g : GState) (E : EraGS) :
    powerInterp g ⊢@{IProp GF} eraRegistered g.gen E -∗ textRo E -∗ ⌜g.pow = true → textPristine g⌝ := by
  unfold powerInterp eraCur
  cases hpw : g.pow
  · iintro _ _ _
    ipureintro
    intro h; cases h
  · iintro ⟨_, _, ⟨%R, HR, _, %E', %hE', Hera⟩, _⟩ #Hreg #Ht
    ihave %hRE := eraRegistered_lookup R g.gen E $$ HR Hreg
    rw [hE'] at hRE
    cases hRE
    unfold eraInterp
    icases Hera with ⟨_, Hheap, _, _⟩
    ihave %h := textRo_heap E g.m.mem $$ [Hheap Ht]
    · iframe Hheap Ht
    ipureintro
    exact fun _ a H hw => h a H hw

end ghost

end Xv6
