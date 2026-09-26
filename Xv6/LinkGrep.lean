/-
**grep, linked**: the walks of grep's callees at one engine (Rocq's
`UkGrepLib`/`UkGrepMatch` sections close them together; DU10 split them one
function per file).  matchstar's interface is its walk given matchhere at
the same pattern; matchhere's proof closes the mutual recursion.

Not here (report of lane P-grep): grep() (`UkGrepLoop`), main
(`UkGrepMain`) and the entry (`UkGrepTree`) are stated at the program's
interaction tree (`UkTree.tree_pay` and its holes), which is H-tree's.
-/
import Xv6.ProofGrepStrchr
import Xv6.ProofGrepMemmove
import Xv6.ProofGrepMatchstar
import Xv6.ProofGrepMatchhere
import Xv6.ProofGrepMatch

namespace Xv6

/-- grep's `strchr`, `memmove`, `matchstar`, `matchhere` and `match`, at the
engine `UL`. -/
theorem grep_linked (UL : UK_LEAVES) :
    GREP_STRCHR ∧ GREP_MEMMOVE ∧ GREP_MATCHSTAR ∧ GREP_MATCHHERE ∧ GREP_MATCH :=
  have MS := grepMatchstar_holds UL
  have MH := grepMatchhere_holds UL MS
  ⟨grepStrchr_holds UL, grepMemmove_holds UL, MS, MH, grepMatch_holds UL MH⟩

end Xv6
