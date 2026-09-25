/-
**The conditional entry deposit** (Rocq `UexecCond.v`): at a mint site,
decide on the KEY alone whether the process is a VERIFIED PROGRAM at its
entry, and deposit that program's slot if so, the generic one otherwise.  NO
assumption enters the composition on any branch.

Rocq's `cond_entry_slot` is a CHAIN of decidable gates (`sync_gate`,
`echo_gate`) ending in the generic WP; adding the next verified program is one
more `destruct`.

## Deviations from Rocq (FLAGGED)

1. **THE GATE CHAIN IS EMPTY until wave 9.**  The two gated branches need the
   verified programs' own slot constructors (`USyncKernel.sync_uexec_slot`,
   `UEchoKernel.echo_uexec_slot`), their dumped images (`SyncInstrs`,
   `EchoInstrs`) and the `UkRun`/`UkAbi` supplier vocabulary (`udep`,
   `udepw_law`, `uk_xpage`, `uk_args_c`) -- all of it the D24 user-mode tower.
   So `condEntrySlot` is the generic tail only, and its premises are the
   generic tail's (`□ ssupply`, `□ killCred`, `□ uexecWp`, the pay fact);
   the `PF`/`Hpsok_free`/`udepw_law`/`udep` premises return with the gates.
   The gate-independent pieces are ported: the image test
   (`textRegionEqOf`, as strong as `uimgSub` and no stronger), the
   map-stops-at-the-break gate (`ustopGate`), and `loop_ok_upt_desc`.
2. `text_region_eq_of`/`ustop_gate` are over Lean's function-typed image and
   permission view (`ElfMem`, `Nat → Option UPerm`), so they have NO
   `Decidable` instance (Rocq's come from finite gmaps); the wave-9 gates will
   decide them at the images' finite domains, or classically.
3. `uk_xpage_upt_desc` (needs `UkAbi.uk_xpage`) is deferred with the gates.
4. Rocq's `upt_desc root tfp` (allocproc's empty table) is `⟨root, tfp, ∅⟩`.
-/
import Xv6.UexecRet
import Xv6.KexecBuilt

namespace Xv6

open Iris Iris.BI Iris.ProofMode Std MachCSL

set_option linter.unusedSectionVars false

/-! ## §1 The image test -/

/-- **Rocq `text_region_eq_of`**: the text portion of `M` (its restriction to
the addresses `img` names) IS `img`. -/
def textRegionEqOf (img M : ElfMem) : Prop := ∀ a, (img a).isSome → M a = img a

/-- Rocq `text_region_eq_of_uimg_sub`. -/
theorem textRegionEqOf_uimgSub {img M : ElfMem} (h : textRegionEqOf img M) : uimgSub img M := by
  intro a b hb
  rw [h a (by rw [hb]; rfl), hb]

/-- Rocq `uimg_sub_text_region_eq_of`: the converse -- as strong as `uimgSub`
and no stronger. -/
theorem uimgSub_textRegionEqOf {img M : ElfMem} (h : uimgSub img M) : textRegionEqOf img M := by
  intro a ha
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 ha
  rw [hb, h a b hb]

/-! ## §2 The map stops at the break -/

/-- **Rocq `ustop_gate`**: the key-level reading of the kernel's `umBelow` --
every page of the permission view lies below `PGROUNDUP(sz)`. -/
def ustopGate (W : Uvis) : Prop := ∀ (p : Nat) (q : UPerm), W.perm p = some q → p * 4096 < pgRoundUpN W.sz

/-- Rocq `ustop_gate_at`. -/
theorem ustopGate_at {W : Uvis} (h : ustopGate W) (p : Nat) (q : UPerm) (hq : W.perm p = some q) :
    p * 4096 < pgRoundUpN W.sz := h p q hq

/-! ## §3 THE CONDITIONAL CONSTRUCTOR (the generic tail; deviation 1) -/

section UexecCond
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CtokG GF] [SG : UexecSG GF]
open UexecSG

/-- **Rocq `cond_entry_slot`**, at the empty gate chain: the generic slot at
the trivial payload.  THE SUPPLY and THE KILL CREDENTIAL are what the generic
tail spends (every number's deposit, every killing cause). -/
theorem condEntrySlot (W : Uvis) :
    ⊢ □ ssupply -∗ □ uKillCred -∗ □ uexecWp -∗ myPay W.gen (fun _ => iprop(True)) -∗
      uslot (GF := GF) W :=
  uexecWp_uslot_triv W

/-- **Rocq `cond_entry_slot_pay`**: THE ENTRY AT A CONSTANT PAYLOAD
(GENERIC-PAY) -- the payload as the persistent carrier `□ (killCred -∗ R)`. -/
theorem condEntrySlot_pay (R : IProp GF) (W : Uvis) :
    ⊢ □ ssupply -∗ □ uKillCred -∗ □ uexecWp -∗ myPay W.gen (fun _ => R) -∗ □ (uKillCred -∗ R) -∗
      uslot W :=
  uexecWp_uslot R W

end UexecCond

/-! ## §4 The discharge at userinit: the empty table -/

/-- **Rocq `loop_ok_upt_desc`**: the empty table is `loopOk` whenever any table
is (deviation 4). -/
theorem loopOk_uptEmpty {C : UCfg} {P : UPtd} (root tfp : BitVec 44) (h : loopOk C P)
    (hv : pageValid (pageAddr tfp)) : loopOk C ⟨root, tfp, ∅⟩ := by
  obtain ⟨h1, h2, h3, h4, _⟩ := h
  refine ⟨h1, h2, h3, h4, ⟨?_, ?_, hv⟩⟩
  · intro k w hk; rw [Iris.Std.LawfulPartialMap.get?_empty] at hk; cases hk
  · intro k1 w1 k2 w2 hk1; rw [Iris.Std.LawfulPartialMap.get?_empty] at hk1; cases hk1
