/-
Weak: **THEOREM 2 / P4: `AxSpinApA.tailText2` HOLDS on the capstone image** `AxSpinT2c5.σX`
(the kernel text `[_entry, etext)` + the page tables of `AxSpinT2pt.tX`, read off this tree's
kernel image `Xv6/KernelImage.lean`).

Lean-only (no Rocq source).  Recipe of `AxSpinT2c5.tailTextX` (that file's `ax_t2c5_txt` macro is
`local`, so it is restated here as `ax_spin_tail2x_txt`): each conjunct by one of
AxSpinTextCerts' constructors on the fetch page 0x80001 (`AxSpinT2c5.pageX1`: the `jal` at
0x80001c0e, 2 mod 4 ⇒ `text4U`) or 0x80000 (`AxSpinT2c5.pageX0`: kalloc's two halfwords ⇒
`textAtA` / `textAtU`), the residual byte equation by `decide +kernel` over the image.
No pins.  Names: file-qualified `AxSpinTail2X.*`.
-/
import Weak.AxSpinT2c5
import Weak.AxSpinTail2

namespace Weak

open AxSpinT2pt AxSpinT2c1

/-- One text conjunct: the fitting constructor on page 0x80000 or 0x80001. -/
local macro "ax_spin_tail2x_txt" : tactic => `(tactic|
  first
  | exact AxSpinTextCerts.textAtA AxSpinT2c5.pageX0 _ _ (by decide +kernel)
  | exact AxSpinTextCerts.textAtU AxSpinT2c5.pageX0 _ _ (by decide +kernel)
  | exact AxSpinTextCerts.text4U AxSpinT2c5.pageX0 _ _ (by decide +kernel)
  | exact AxSpinTextCerts.text4A AxSpinT2c5.pageX0 _ _ (by decide +kernel)
  | exact AxSpinTextCerts.textAtA AxSpinT2c5.pageX1 _ _ (by decide +kernel)
  | exact AxSpinTextCerts.textAtU AxSpinT2c5.pageX1 _ _ (by decide +kernel)
  | exact AxSpinTextCerts.text4U AxSpinT2c5.pageX1 _ _ (by decide +kernel)
  | exact AxSpinTextCerts.text4A AxSpinT2c5.pageX1 _ _ (by decide +kernel))

/-- THE CERTIFICATE: the three text facts of the walk past the row end hold on `σX`. -/
theorem AxSpinTail2X.tailText2X : AxSpinApA.tailText2 AxSpinT2c5.σX tX := by
  unfold AxSpinApA.tailText2
  (repeat' apply And.intro) <;> ax_spin_tail2x_txt

end Weak
