/-
MachCSL: the CSR family at User privilege, part 2 -- the DEFAULT class
(lane U1-X3; Rocq `UserCsr.v` §3, the "chain the false branches linearly"
half of its traversal).

The three dispatchers the check chain runs (`is_CSR_accessible`,
`stateen_allows_CSR_access`, `is_CSR_exception_virtual`) test the csr number
against literals and eleven range clauses (the PMP `0x3A?`–`0x3E?` blocks;
the six `hpmcounter`/`mhpmevent`-shaped `…[4:0] ≥ 3` blocks).  `uxrDflt c`
says `c` hits none of `is_CSR_accessible`'s.  For those, `is_CSR_accessible`
is a closed monadic term:

* `uxr_isAcc_dflt`: `is_CSR_accessible c p acc = pure false`.

Since sail-riscv 0.16 the generated `is_CSR_accessible` is a chain of `if`s on
the number (it was a `match`); the proof rewrites every literal test false
from the mask (`uxr_beq_of_mask`) and every range guard false from `uxrDflt`'s
own conjuncts, and the chain's last `else` is `pure false`.  The literal table
(`uxrLits`, `uxrLitMask`) is GENERATED from the model by
`tools/gen_uxr_csr_lits.py`, which also checks that the range guards are the
eleven `uxrDflt` names.

The other numbers are closed values (`UExecCsrTab`).
-/
import MachCSL.UExecCsrBase

noncomputable section

namespace MachCSL

open Sail Sail.ArchSem
open LeanRV64D LeanRV64D.Functions

/-! ## The default class -/

-- BEGIN GENERATED (tools/gen_uxr_csr_lits.py; do not edit)
/-- The literal tests of `is_CSR_accessible`'s chain, in the model's order (123 numbers). -/
def uxrLits : List Nat :=
  [0x301, 0x300, 0x310, 0x600, 0x747, 0x757, 0x30A, 0x31A, 0x10A, 0x60A, 0x61A, 0x342, 0x343,
   0x340, 0x106, 0x606, 0x306, 0x320, 0xF11, 0xF12, 0xF13, 0xF14, 0xF15, 0x34A, 0x34B, 0x605,
   0x615, 0x643, 0x64A, 0x200, 0x100, 0x240, 0x242, 0x243, 0x140, 0x142, 0x143, 0x607, 0xE12,
   0x304, 0x344, 0x302, 0x312, 0x303, 0x645, 0x604, 0x644, 0x602, 0x612, 0x603, 0x144, 0x104,
   0x204, 0x244, 0xB00, 0xB02, 0xB80, 0xB82, 0x205, 0x241, 0x105, 0x141, 0x305, 0x341, 0x001,
   0x002, 0x003, 0x008, 0x009, 0x00A, 0x00F, 0xC20, 0xC21, 0xC22, 0x321, 0x721, 0x322, 0x722,
   0x7A0, 0x7A1, 0x7A2, 0x7A3, 0x7A4, 0x7A5, 0x5A8, 0x7A8, 0x6A8, 0x30C, 0x30D, 0x30E, 0x30F,
   0x31C, 0x31D, 0x31E, 0x31F, 0x60C, 0x60D, 0x60E, 0x60F, 0x61C, 0x61D, 0x61E, 0x61F, 0x10C,
   0x10D, 0x10E, 0x10F, 0x680, 0x280, 0x180, 0xDA0, 0x14D, 0x15D, 0x24D, 0x25D, 0x011, 0xC00,
   0xC01, 0xC02, 0xC80, 0xC81, 0xC82, 0x181]

/-- `uxrLits` as a bitmask (bit `n` set iff `n` is listed): the kernel tests
membership with two GMP operations (a `List.contains` over `Nat` literals costs
~80µs per comparison in the kernel). -/
def uxrLitMask : Nat :=
  36648395856342730055296984112411208899296719027344655312011862051754270023038287425792415148048739504212701733562190386397034978660154103502723346394462291692247493693857505635244652150162219242386414029064433296077704318507423224687805940592139429192671066716076536263802011958733398861659931212295571487443915781108232445404593176928381304913761118582407239455217504187382552470686349445408126731862793752011991109851420456355500116247667822540929771541516098972449064620008995539595594153746062135706401462509273137178169609578718782279142176762734595973409893673569169492606505427556068228961666718584216588660557592903011624715706516587348207566363958976938356702063821205088624383661884035918388450321526873829144701515440170046648480796695058857455492119770226712024307158635755030822300451159332683387579948499095689655880211515664772808293279515856549521900570558470388960473715597143387463138989453255683697956428360508873064014546156210606802031094355958397484933632169232897093072557763444536778239437162795690020144779488143706578452757795615110946934585748296445361517387960235957306834294217002610704571062677177161770291971370043412759805694215950
-- END GENERATED

theorem uxrLitMask_eq : uxrLitMask = uxrLits.foldl (fun m c => m ||| 1 <<< c) 0 := by kernel_rfl

/-- Bit `n` of a mask. -/
def uxrBit (m n : Nat) : Bool := (m >>> n) % 2 == 1

/-- A counter-shaped range clause: `csr[11:5] = k` and `csr[4:0] ≥ 3` (the
model's guard, verbatim). -/
def uxrHpm (c : BitVec 12) (k : BitVec 7) : Bool :=
  (Sail.BitVec.extractLsb c 11 5 == k) && (BitVec.toNatInt (Sail.BitVec.extractLsb c 4 0) ≥b 3)

/-- **The default class**: no literal clause, no range clause. -/
def uxrDflt (c : BitVec 12) : Bool :=
  !(uxrBit uxrLitMask c.toNat) &&
  !(Sail.BitVec.extractLsb c 11 4 == 0x3A#8) && !(Sail.BitVec.extractLsb c 11 4 == 0x3B#8) &&
  !(Sail.BitVec.extractLsb c 11 4 == 0x3C#8) && !(Sail.BitVec.extractLsb c 11 4 == 0x3D#8) &&
  !(Sail.BitVec.extractLsb c 11 4 == 0x3E#8) &&
  !(uxrHpm c 0b0011001#7) && !(uxrHpm c 0b1011000#7) && !(uxrHpm c 0b1011100#7) &&
  !(uxrHpm c 0b1100000#7) && !(uxrHpm c 0b1100100#7) && !(uxrHpm c 0b0111001#7)

/-- A number outside the mask is none of its literals. -/
theorem uxr_beq_of_mask {c : BitVec 12} (hm : uxrBit uxrLitMask c.toNat = false) (n : BitVec 12)
    (hn : uxrBit uxrLitMask n.toNat = true) : (c == n) = false := by
  cases hc : c == n
  · rfl
  · rw [beq_iff_eq] at hc
    subst hc
    rw [hm] at hn
    exact absurd hn Bool.false_ne_true

/-! ## `is_CSR_accessible` on the default class -/

set_option maxRecDepth 100000 in
/-- `is_CSR_accessible` on the default class: `false`, reading nothing. -/
theorem uxr_isAcc_dflt (c : BitVec 12) (p : Privilege) (acc : CSRAccessType) (h : uxrDflt c = true) :
    is_CSR_accessible c p acc = pure false := by
  have h' := h
  simp only [uxrDflt, uxrHpm, Bool.and_eq_true, Bool.not_eq_true'] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hm, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h'
  unfold is_CSR_accessible
  simp (disch := decide) only [uxr_beq_of_mask hm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    Bool.false_eq_true, ↓reduceIte]

end MachCSL
