/-
**THE FILE APPLICATION'S NAMES, ITS CAMERA CLASS, THE TAINT AND THE LINE
LIST** -- §1 of Rocq `AppFile.v` (`/shared/xv6rocq/iris/AppFile.v`, pinned
1900b8a43), the Iris half (the pure types are `Xv6/AppFilePure.lean`).

* `FileFixed` (Rocq `file_fixed`): THE FIXED PART -- echo's (the taint
  counter and the era map, `EchoGn`) beside the LINE LIST's name: a
  `mono_list` of the `echo … > N` lines the console has received, in order,
  whose authority the ledger keeps and whose lower bounds ride the input
  tag.
* `FileAppNames` (Rocq `file_names`): THE INSTANCE -- echo's console pair
  beside THE DEED's, THE TICKET's and THE ESCROW LEDGER's names.
* `FileAppG` (Rocq `fileAppG`): the application's three cameras.
* `fileTaint` (Rocq `file_taint`): echo's taint at the projection.
* `flAuth`/`flLb` (Rocq `fl_auth`/`fl_lb`): the line list's authority and
  its persistent lower bounds; `flLb_lb`: two lower bounds are comparable.
* `fileCl` (Rocq `file_cl`): the birth resource -- echo's, and the line
  list empty.

## Camera classes (union_cone.md §4.1, one instance per camera)

Rocq's `fileAppG` has three components, all at types no landed class
carries, so all three are NEW (three xv6GF/unionGF slots for U4):
* `ghost_varG dst` -> `FileAppG.deedG : GhostVarG GF Dst` (the deed and
  the ticket, two names of one camera);
* `mono_list (leibnizO fwline)` -> `FileAppG.flG : MonoListG GF Fwline`;
* `mono_list (leibnizO esc_rec)` -> `FileAppG.escG : MonoListG GF EscRec`.
The section's `inG Σ (mono_listR (leibnizO Z))` binder (echo's console
flag) is `DiskG`'s `MonoListG GF Nat` (`Xv6/AppEchoCons.lean` deviation 1),
hence the `[DiskG GF]` binder; the escrow's one-shot `mono_nat` is
`MachGS`'s own (`Xv6/EscrowDefs.lean` deviation 2), as echo's taint is.

## DEVIATIONS from Rocq

1. **`file_names` IS `FileAppNames`** (the Lean name `FileNames` is the
   kernel's file-layer names, `Xv6/FilereadDev.lean`); fields `fnCons`,
   `fnDeed`, `fnTkt`, `fnEsc`.  `file_fixed` is the pair
   `EchoGn × GName` (Rocq's `echo_fixed * gname`, `.1`/`.2` kept).
2. `fileAppΣ` / `subG_fileAppΣ`: subsumed by `BundledGFunctors` (the class
   is the capacity; the slots are U4's).
3. Scope: the reached declarations plus the `Persistent`/`Timeless`
   instances of the reached predicates.  Not ported (unreached):
   `fl_auth_lb`, `fl_lb_prefix`, `fl_auth_grow`, `file_birth`.
4. Rocq's curried `A -∗ B -∗ C` lemmas are stated `⊢ A -∗ B -∗ C`
   (`Xv6/AppInv.lean` deviation 5).
-/
import Xv6.AppEcho
import Xv6.AppFilePure

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL

set_option linter.unusedSectionVars false

/-! ## The fixed part and the instance -/

/-- THE FIXED PART (Rocq `file_fixed`): echo's (the taint counter and the
era map) beside the LINE LIST's name. -/
abbrev FileFixed : Type := EchoGn × GName

/-- THE INSTANCE (Rocq `file_names`): echo's console pair beside THE
DEED's, THE TICKET's and THE ESCROW LEDGER's names. -/
structure FileAppNames where
  fnCons : EchoNames
  fnDeed : GName
  fnTkt : GName
  /-- THE ESCROW LEDGER (Rocq section 2a) -/
  fnEsc : GName

/-- THE FILE APPLICATION'S THREE NEW CAMERAS (Rocq `fileAppG`). -/
class FileAppG (GF : BundledGFunctors) where
  [deedG : GhostVarG GF Dst]
  [flG : MonoListG GF Fwline]
  [escG : MonoListG GF EscRec]

attribute [reducible, instance] FileAppG.deedG FileAppG.flG FileAppG.escG

section AppFileNames
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [DiskG GF]
  [EchoOutG GF] [FileAppG GF]

/-! ## 1a. The taint, at the projection -/

/-- Rocq `file_taint`. -/
def fileTaint (c : FileFixed) : IProp GF := echoTaint (hlc := hlc) c.1

instance fileTaint_persistent (c : FileFixed) :
    Persistent (fileTaint (hlc := hlc) (GF := GF) c) := by
  unfold fileTaint; infer_instance

instance fileTaint_timeless (c : FileFixed) :
    Timeless (fileTaint (hlc := hlc) (GF := GF) c) := by
  unfold fileTaint; infer_instance

/-! ## 1b. The line list -/

/-- The line list's authority (Rocq `fl_auth`). -/
def flAuth (c : FileFixed) (ls : List Fwline) : IProp GF :=
  MonoList.auth_own c.2 (DFrac.own 1) ls

/-- A lower bound of the line list (Rocq `fl_lb`). -/
def flLb (c : FileFixed) (ls : List Fwline) : IProp GF :=
  MonoList.lb_own c.2 ls

instance flLb_persistent (c : FileFixed) (ls : List Fwline) :
    Persistent (flLb (GF := GF) c ls) := by
  unfold flLb; infer_instance

instance flLb_timeless (c : FileFixed) (ls : List Fwline) :
    Timeless (flLb (GF := GF) c ls) := by
  unfold flLb; infer_instance

instance flAuth_timeless (c : FileFixed) (ls : List Fwline) :
    Timeless (flAuth (GF := GF) c ls) := by
  unfold flAuth; infer_instance

/-- Two lower bounds of one list are comparable (Rocq `fl_lb_lb`). -/
theorem flLb_lb (c : FileFixed) (ls ls' : List Fwline) :
    ⊢@{IProp GF} flLb c ls -∗ flLb c ls' -∗ ⌜ls <+: ls' ∨ ls' <+: ls⌝ := by
  unfold flLb
  iintro Ha Hb
  iapply MonoList.lb_own_valid c.2 ls ls' $$ Ha Hb

/-- THE BIRTH (Rocq `file_cl`): echo's counter and era map, and the line
list empty. -/
def fileCl (c : FileFixed) : IProp GF :=
  iprop(echoCl (hlc := hlc) c.1 ∗ flAuth c [])

end AppFileNames

end Xv6
