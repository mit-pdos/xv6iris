/-
**THE FILE APPLICATION'S LINKS BUNDLE** -- the reached part of Rocq
`FileLinks.v` (`iris/FileLinks.v`, pinned 1900b8a43): the
bundle `file_links` (1 of 3 declarations reached).

Rocq's note: the file application's links are what the record equation
gives -- every console link of the era is `GenLinks` at this instance once
the console record's claim is `fecl g`.  So the bundle a program holds and
spends is the EQUATION ITSELF, as a pure persistent fact, and the links are
read off it where they are spent.  This is what fills `LinkRec.lk_links` at
the file application.

## DEVIATIONS from Rocq

1. **Scope**: `fread_ret` (the read link's receipt, section `file_links`)
   and `file_links_persistent`'s section wrapper are not reached; the
   `Persistent` instance is kept.
2. `riscv_cons_res (riscv_fixedGS HRg)` is `MachFixedGS.consRes` (as
   `PipeOutNFam.consClaimV` reads it).
-/
import Xv6.FileOutClaim

namespace Xv6

open Iris Iris.BI Iris.ProofMode MachCSL

set_option linter.unusedSectionVars false

section FileLinks
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [DiskG GF]
  [EchoOutG GF] [FileAppG GF] [FileOutG GF]

/-- THE BUNDLE: the console record's claim is the file application's (Rocq
`file_links`). -/
def fileLinks (g : FileGn) : IProp GF :=
  iprop(⌜MachFixedGS.consRes (hlc := hlc) (GF := GF) = fecl (hlc := hlc) g⌝)

instance fileLinks_persistent (g : FileGn) : Persistent (fileLinks (hlc := hlc) (GF := GF) g) := by
  unfold fileLinks; infer_instance

end FileLinks

end Xv6
