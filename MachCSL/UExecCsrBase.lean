/-
MachCSL: the CSR family at User privilege, part 1 -- the configuration it
runs under and the read-only bridge (lane U1-X3, brief
`notes/briefs/user_layer.md` G10; Rocq `UserCsr.v` §1).

**What a CSR instruction at User reads.**  `doCSR` reads `cur_privilege`,
then `check_CSR_result`.  The Lean backend evaluates every `(← …)` of a
condition up front (Rocq's `and_boolM` short-circuits; Lean's `&&` over
lifted actions does not), so at User the MODEL runs, for every csr number,
`check_CSR_priv`, `is_CSR_accessible`, `stateen_allows_CSR_access` at User,
and then `is_CSR_exception_virtual`, i.e. the same three at Supervisor.  The
CSR facts walk the SHORT-CIRCUIT chain instead (`UExecCsrSc`: Sail's own
evaluation order), related to the model's by the elimination theorem
(`SailStut`, `MachCSL/SailAndElim.lean`: the discarded operands are
read-only and total).  The registers the short-circuit chain reads
(measured: dropping any one makes some csr's walk fail) are `uxrReads`:

* `cur_privilege` (User, the user frame);
* `misa`, `senvcfg`, `scounteren`, `mstateen0`, `sstateen0` (FROZEN: the
  `hwConfig` cells, at their `hwVal` values);
* `menvcfg` (`menvcfgS`) and `mcounteren` (`2`, i.e. `TM` only), the kernel's
  user-time values;
* `mstatus` (only through the F / vector gates of `fflags`/`frm`/`fcsr` and the
  vector CSRs, where it is SYMBOLIC: the user frame's `mstatus`, with `FS = 0`).

The eager chain also read `mstateen1..3`/`sstateen1..3` (the stateen check of
`sstateen1..3`/`hstateen1..3`, whose outcome the privilege gate discards) --
cells in no owner's frame (a D52 footprint gap).  The short-circuit chain
never reads them, so they are not in the footprint.

`uxrPin f` is that table (the data cells at the file `f`'s values);
every CSR fact takes the two premises `UxrFoot D` (the footprint reads them)
and `UxrCfg s` (the walker state's file carries the closed values, `mstatus`
any value with `FS = 0`), the shape of lane U1-X2's `UxcFoot`/`UxcCfg`.

**The bridge.**  A read-only stretch is walked by `DecodeBridge.runRead` at the
table (a closed, kernel-evaluable computation even over all 4096 csr numbers);
`uxr_runRW_of_runRead` lifts it to `runRW` at any state whose file agrees with
the table, footprint reading it: the state and the oracle come back
unchanged.
-/
import MachCSL.URunRW
import MachCSL.HwConfig

namespace MachCSL

open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## The read set and its values -/

/-- The registers a CSR instruction's check chain reads at User privilege
(besides the source GPR of `CSRReg`). -/
def uxrReads : List Register :=
  [.cur_privilege, .misa, .mstatus, .menvcfg, .senvcfg, .mcounteren, .scounteren,
   .mstateen0, .sstateen0]

/-- The values the check chain runs at: User privilege, the frozen cells at
their `hwVal` values, `menvcfg`/`mcounteren` at the kernel's user-time values;
the DATA cell `mstatus` (read, never branched on except `FS`) at the file
`f`'s value. -/
def uxrPin (f : RegFile) : RegPin
  | .cur_privilege => some Privilege.User
  | .mstatus => some (f .mstatus)
  | .menvcfg => some menvcfgS
  | .mcounteren => some 2#32
  | .misa => hwVal .misa
  | .senvcfg => hwVal .senvcfg
  | .scounteren => hwVal .scounteren
  | .mstateen0 => hwVal .mstateen0
  | .sstateen0 => hwVal .sstateen0
  | _ => none

/-- The table's domain is the read set. -/
theorem uxrPin_dom (f : RegFile) (r : Register) (v : RegisterType r) (h : uxrPin f r = some v) :
    r ∈ uxrReads := by
  cases r <;> simp only [uxrPin, reduceCtorEq] at h <;> decide

/-- **The footprint premise of every CSR fact**: the footprint reads `uxrReads`. -/
def UxrFoot (D : UFoot) : Prop := ∀ r ∈ uxrReads, D.Dr r = true

/-- **The configuration premise of every CSR fact**: the file holds the
table's closed values (User, `misa`/`senvcfg`/`scounteren`/`mstateen0`/
`sstateen0` at `hwVal`, `menvcfg = menvcfgS`, `mcounteren = 2`), and `mstatus`
has `FS = 0` (Off). -/
structure UxrCfg (s : UWSt) : Prop where
  priv : s.file .cur_privilege = Privilege.User
  misa : s.file .misa = 0x800000000014112D#64
  menvcfg : s.file .menvcfg = menvcfgS
  senvcfg : s.file .senvcfg = 0#64
  mcounteren : s.file .mcounteren = 2#32
  scounteren : s.file .scounteren = 0#32
  mstateen0 : s.file .mstateen0 = 0#64
  sstateen0 : s.file .sstateen0 = 0#32
  fs : _get_Mstatus_FS (s.file .mstatus) = 0#2

/-- The file agrees with the table. -/
theorem UxrCfg.val {s : UWSt} (hc : UxrCfg s) (r : Register) (v : RegisterType r)
    (h : uxrPin s.file r = some v) : s.file r = v := by
  cases r <;> simp only [uxrPin, hwVal, reduceCtorEq, Option.some.injEq] at h <;> subst h
  all_goals simp only [hc.priv, hc.misa, hc.menvcfg, hc.senvcfg, hc.mcounteren, hc.scounteren,
    hc.mstateen0, hc.sstateen0]

/-! ## The read-only bridge -/

/-- **A read-only walk at a table lifts to `runRW`** at any state whose file
agrees with the table on its domain, the footprint reading the domain: the
state and the oracle come back unchanged (Rocq: a `goodb` walk is a `goodmb`
walk at `mm := ∅` that writes nothing). -/
theorem uxr_runRW_of_runRead {X : Type} (D : UFoot) (orc : UOrc) (s : UWSt)
    (d : (r : Register) → Option (RegisterType r))
    (hd : ∀ r v, d r = some v → D.Dr r = true ∧ s.file r = v) :
    ∀ (m : SailM X) (x : X) (b : Bool), runRead d m = some (x, b) → runRW D orc s m = some (x, s, orc) := by
  intro m
  induction m with
  | pure y =>
    intro x b h
    simp only [runRead, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | impure call k ih =>
    intro x b h
    cases call with
    | error e => simp [runRead] at h
    | ok o =>
      cases o <;> simp only [runRead, reduceCtorEq] at h
      case regRead r =>
        cases hdr : d r with
        | none => rw [hdr] at h; simp at h
        | some v =>
          rw [hdr] at h
          obtain ⟨hD, hv⟩ := hd r v hdr
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
          obtain ⟨⟨x', b'⟩, h', hx, -⟩ := h
          simp only at hx; subst hx
          rw [runRW_regRead_dr D orc s r k hD, hv]
          exact ih v x' b' h'
      all_goals
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
        obtain ⟨⟨x', b'⟩, h', hx, -⟩ := h
        simp only at hx; subst hx
        simp only [runRW]
        exact ih _ x' b' h'

/-- The bridge at the CSR table. -/
theorem uxr_runRW_of_pin {X : Type} {D : UFoot} {s : UWSt} (hD : UxrFoot D) (hc : UxrCfg s) (orc : UOrc)
    (m : SailM X) (x : X) (b : Bool) (h : runRead (uxrPin s.file) m = some (x, b)) :
    runRW D orc s m = some (x, s, orc) :=
  uxr_runRW_of_runRead D orc s _ (fun r v hv => ⟨hD r (uxrPin_dom _ r v hv), hc.val r v hv⟩) m x b h

end MachCSL
