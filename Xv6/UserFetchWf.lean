import Xv6.UserFetchLeaf

/-!
# Leaf validity from `uptWf`

`uptWf` carries Rocq's `upt_map_wf` validity pin (every user leaf has
`uwkInv w = false`), so the fetch lane's `UftLeavesValid` premise is a
projection of it.
-/

namespace Xv6

theorem uptWf_leavesValid (P : UPtd) (h : uptWf P) : UftLeavesValid P :=
  h.2.2.2.2

end Xv6
