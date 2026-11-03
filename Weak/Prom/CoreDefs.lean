/-
Weak/Prom: **the ownership-free core of the Promising-RISC-V program logic, definitions** (stage S2; plan rev 7
`~/dev/weak-orch/promising/plan.md` §0 "Top-level theorem shapes" and §2 "The ownership-free core").

Everything here is a plain Lean definition over machine v2 (`Weak/Prom/Machine.lean`); the Iris layer is
`CoreWp.lean`, the adequacy theorem A0 `CoreAdeq.lean`.

* The machine trace of a run (§2 [R4.5]): `PFRun.trace h` = `traceOf h run.evs` (one entry per state step of `h`,
  its label and its fulfil timestamp), `PFRun.fulfils h`, `PFRun.traceWf M` (machine v2's `traceWf`, [R7.s4]),
  `PFRun.obsLoad h k` (§0 [R6.2]: the value of the `k`-th load-like entry), `PFRun.done`.
* The protocol family `Proto`, `Valid π img M V` (§0), the pure guard `grd π img M V φ` (§2 "⟦V⟧ φ", model
  `Valid_M(V) → φ`) with its rules, `protoOk`, `ValidInduction` (§2 A0 (iv)).
* The A/D vocabulary of §0 (`adExact`, `PO_ad`, `PO_img`).  Machine v2 has NO A/D class yet ([OWN.P3]: translation
  is deferred, Machine.lean header "Extension points"), so `PMsg.isAd` is constantly false: `adExact` holds of every
  memory and `PO_ad` of every protocol (`adExact_all`, `PO_ad_all`); the definitions are the extension point.
* `devFreeProg` (§0 [R6.1(b)]) with an explicit hart domain `ps : List P` ([R7.s3]) and `reachP`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.MachSolo

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom
open PLabel

/-! ## 1. Trace entries and the run object -/

/-- A machine-trace entry (plan §2 [R4.5]): the label of one state step and its fulfil timestamp. -/
abbrev PEv : Type := PLabel × Option Nat

/-- A machine trace. -/
abbrev Trace : Type := List PEv

/-- The message at timestamp `t` of the final memory (`M[t]` of the plan; `t = 0` is the image, no message). -/
def msgAt (M : List PMsg) : Nat → Option PMsg
  | 0 => none
  | k + 1 => M[k]?

/-- The author of the message at `t` (`M[t].tid` of the plan). -/
def tidAt (M : List PMsg) (t : Nat) : Option Nat := (msgAt M t).bind PMsg.tid

/-- A RUN of machine v2 (plan §0 `run`): its event list and final configuration. -/
structure PFRun (P D : Type) where
  evs : List PEvt
  cfg : PCfg P D

variable {P D V : Type}

/-- `run.trace h` (plan §2 [R4.5]). -/
def PFRun.trace (run : PFRun P D) (h : Nat) : Trace := traceOf h run.evs

/-- `run.fulfils h`: the fulfil timestamps of `h`, in order (plan §2). -/
def PFRun.fulfils (run : PFRun P D) (h : Nat) : List Nat := fulfilsOf h run.evs

/-- `run.traceWf M` (plan §2 (v), [R7.s4]): every hart's trace is well-formed against `M` and the run's image. -/
def PFRun.traceWf (run : PFRun P D) (M : List PMsg) : Prop := ∀ h, Weak.Prom.traceWf run.cfg.pcImg M h (run.trace h)

/-- `run.done h v` (plan §0 A0 (i)): hart `h` ends the run in a program state that is the value `v`. -/
def PFRun.done (pdone : P → Option V) (run : PFRun P D) (h : Nat) (v : V) : Prop :=
  ∃ ag, run.cfg.pcAgs[h]? = some ag ∧ pdone ag.paSt = some v

/-- The read answers of a LOAD-LIKE label (plan §0 [R6.2]: `ld`, `exld`, `rmw`; machine v2's AMO is `LRmw` or the
split pair whose read half `LAmoLd` carries the answers).  Fetches, device events are not load-like. -/
def loadLikeTvs : PLabel → Option (List (Nat × BitVec 8))
  | LLoad _ _ _ tvs _ => some tvs
  | LExLoad _ _ _ tvs _ => some tvs
  | LRmw _ _ _ tvs _ _ _ => some tvs
  | LAmoLd _ _ tvs _ => some tvs
  | _ => none

/-- `obsOf` (plan §0 [R6.2]): the little-endian assembly of the answered values, timestamps forgotten. -/
def obsOf (tvs : List (Nat × BitVec 8)) : Nat := tvs.foldr (fun tv acc => tv.2.toNat + 256 * acc) 0

/-- The load-like answers of a trace, in order. -/
def loadsOf (τ : Trace) : List (List (Nat × BitVec 8)) := τ.filterMap (fun e => loadLikeTvs e.1)

/-- `run.obsLoad h k` (plan §0 [R6.2]): the value of the `k`-th load-like entry of `run.trace h`, if any. -/
def PFRun.obsLoad (run : PFRun P D) (h k : Nat) : Option Nat := ((loadsOf (run.trace h))[k]?).map obsOf

/-- `PF.validRun img prog M run` (plan §0): `run` is a valid run of machine v2 over the program half `pstep`, from
the image `img`, the initial fabric `d0` ([R7.s2]) and the harts `ps` ([R7.s3]: hart `h` runs `ps[h]`), whose
final memory is `M`. -/
def validRun (pstep : P → D → PLabel → P → D → Prop) (img : Image) (d0 : D) (ps : List P) (M : List PMsg)
    (run : PFRun P D) : Prop :=
  Weak.Prom.validRun pstep img d0 ps run.evs run.cfg ∧ run.cfg.pcLog = M

/-- `∃! h, p h` (core Lean has no `∃!` notation without Mathlib). -/
def exU (p : Nat → Prop) : Prop := ∃ h, p h ∧ ∀ h', p h' → h' = h

/-! ## 2. Protocols, `Valid`, the guard ⟦V⟧ -/

/-- THE PROTOCOL FAMILY (plan §0 `Proto`): `okMsg m` is "protocol_{loc m} (val m)", `okImg` the same fact of the
image (t = 0). -/
structure Proto where
  okMsg : PMsg → Prop
  okImg : Image → Prop

/-- The trivial family (plan §2: the LB rows' π). -/
def Proto.triv : Proto := ⟨fun _ => True, fun _ => True⟩

/-- `Valid π img M V` (plan §0): the image and every message `M[t]`, `1 ≤ t ≤ min V |M|`, meet their protocol. -/
def Valid (π : Proto) (img : Image) (M : List PMsg) (V : Nat) : Prop :=
  π.okImg img ∧ ∀ t, 1 ≤ t → t ≤ min V M.length → ∀ m, msgAt M t = some m → π.okMsg m

/-- THE GUARD `⟦V⟧ φ` (plan §2 "Rules for ⟦·⟧"; model `Valid_M(V) → φ`). -/
def grd (π : Proto) (img : Image) (M : List PMsg) (V : Nat) (φ : Prop) : Prop := Valid π img M V → φ

/-- `protoOk t` (plan §2 FULFIL): the message at `t` meets its protocol once every earlier message does. -/
def protoOk (π : Proto) (img : Image) (M : List PMsg) (t : Nat) : Prop :=
  ∀ m, msgAt M t = some m → Valid π img M (t - 1) → π.okMsg m

section valid

variable {π : Proto} {img : Image} {M : List PMsg}

/-- `Valid` is antitone in `V` (plan §2: "`Valid_M(|M|) → Valid_M(V)` for every V"). -/
theorem Valid.mono {V V' : Nat} (h : Valid π img M V') (hV : V ≤ V') : Valid π img M V :=
  ⟨h.1, fun t h1 h2 m hm => h.2 t h1 (by omega) m hm⟩

/-- `Valid_M(|M|) → Valid_M(V)` for EVERY `V` (plan §2): `Valid` counts only `t ≤ min V |M|`. -/
theorem Valid.ofLen {V : Nat} (h : Valid π img M M.length) : Valid π img M V :=
  ⟨h.1, fun t h1 h2 m hm => h.2 t h1 (by omega) m hm⟩

/-- `⌜φ⌝ ⊢ ⟦V⟧φ` (plan §2, at any `V`; `⟦0⟧` in particular). -/
theorem grd_intro {V : Nat} {φ : Prop} (h : φ) : grd π img M V φ := fun _ => h

/-- Monotonicity in `V` (plan §2). -/
theorem grd_mono {V V' : Nat} {φ : Prop} (hV : V ≤ V') (h : grd π img M V φ) : grd π img M V' φ :=
  fun hv => h (hv.mono hV)

/-- `⟦V⟧φ ∧ ⟦V'⟧ψ ⊢ ⟦max V V'⟧(φ ∧ ψ)` (plan §2). -/
theorem grd_and {V V' : Nat} {φ ψ : Prop} (h1 : grd π img M V φ) (h2 : grd π img M V' ψ) :
    grd π img M (max V V') (φ ∧ ψ) :=
  fun hv => ⟨h1 (hv.mono (Nat.le_max_left _ _)), h2 (hv.mono (Nat.le_max_right _ _))⟩

/-- Pure entailment under the guard (plan §2). -/
theorem grd_imp {V : Nat} {φ ψ : Prop} (hφψ : φ → ψ) (h : grd π img M V φ) : grd π img M V ψ :=
  fun hv => hφψ (h hv)

/-- Removing a guard with `Valid_M(|M|)` (plan §2 A0 (i), (ii)). -/
theorem grd_elim {V : Nat} {φ : Prop} (hv : Valid π img M M.length) (h : grd π img M V φ) : φ := h hv.ofLen

/-- `⟦t⟧ proto(M[t])` holds outright: `Valid(t)` contains `M[t]`'s protocol fact (plan §2 LOAD: "each byte j comes
with … the protocol fact ⟦t_j⟧ proto(v_j)"). -/
theorem grd_self {t : Nat} {m : PMsg} (hm : msgAt M t = some m) : grd π img M t (π.okMsg m) := by
  intro hv
  cases t with
  | zero => cases hm
  | succ k =>
    have hk : k < M.length := (List.getElem?_eq_some_iff.1 hm).1
    exact hv.2 (k + 1) (by omega) (by omega) m hm

/-- A guard below a fulfil's timestamp gives `protoOk` (plan §2 FULFIL: "Soundness of `protoOk` uses the same
`pv < t`"). -/
theorem protoOk_of_grd {t pv : Nat} (hlt : pv < t) (h : ∀ m, msgAt M t = some m → grd π img M pv (π.okMsg m)) :
    protoOk π img M t :=
  fun m hm hv => h m hm (hv.mono (by omega))

end valid

/-! ## 3. The A/D vocabulary (plan §0; vacuous on machine v2, see the header) -/

/-- An A/D message (plan M20 (5) class `WCad`).  Machine v2 has no A/D class ([OWN.P3]); constantly false. -/
def _root_.Weak.Prom.PMsg.isAd (_ : PMsg) : Prop := False

/-- `memAt img M V a` (plan §0, M20 (6)): the byte-wise latest content of `a` among the image and `M[1..V]`. -/
def memAt (img : Image) (M : List PMsg) : Nat → Int → Option (BitVec 8)
  | 0, a => img a
  | V + 1, a =>
    match (msgAt M (V + 1)).bind (fun m => m.byteAt a) with
    | some b => some b
    | none => memAt img M V a

/-- The A/D update of byte `j` of a PTE (A = bit 6, D = bit 7 of the low byte, Sv39/48): the A update, or the A and
D update when `setD`. -/
def adUpdByte (setD : Bool) (j : Nat) (old : BitVec 8) : BitVec 8 :=
  if j = 0 then old ||| (if setD then 0xC0 else 0x40) else old

/-- The A/D data `data` is the update of the memory content below `t` at `pa` (`val M[t] = adUpd (memAt …)`). -/
def adData (img : Image) (M : List PMsg) (t : Nat) (pa : Int) (data : List (BitVec 8)) : Prop :=
  ∃ setD, ∀ (j : Nat) b, data[j]? = some b → ∃ old, memAt img M (t - 1) (pa + (j : Int)) = some old ∧
    b = adUpdByte setD j old

/-- `adExact img M` (plan §0): A/D messages are determined by `M`. -/
def adExact (img : Image) (M : List PMsg) : Prop :=
  ∀ t m, 1 ≤ t → t ≤ M.length → msgAt M t = some m → m.isAd → adData img M t m.pa m.data

/-- `PO_img π img` (plan §0, NA-14): the image meets every protocol. -/
def PO_img (π : Proto) (img : Image) : Prop := π.okImg img

/-- `PO_ad π img M` (plan §0, NA-14b): the protocols are closed under the A/D updates the machine can perform. -/
def PO_ad (π : Proto) (img : Image) (M : List PMsg) : Prop :=
  ∀ t m, 1 ≤ t → t ≤ M.length → msgAt M t = some m → m.isAd → Valid π img M (t - 1) →
    adData img M t m.pa m.data → π.okMsg m

/-- On machine v2 (no A/D class) every memory is `adExact` (A0 (vi)). -/
theorem adExact_all (img : Image) (M : List PMsg) : adExact img M := fun _ _ _ _ _ h => h.elim

/-- On machine v2 (no A/D class) `PO_ad` holds of every protocol (plan §0 corollary of `PF.noWCad`). -/
theorem PO_ad_all (π : Proto) (img : Image) (M : List PMsg) : PO_ad π img M := fun _ _ _ _ _ h => h.elim

/-- **`ValidInduction`** (plan §2 A0 (iv)): every non-A/D message's `protoOk`, PO-img, PO-ad and `adExact` give
`Valid π img M |M|`.  Strong induction on `t`. -/
theorem validInduction {π : Proto} {img : Image} {M : List PMsg}
    (hp : ∀ t, 1 ≤ t → t ≤ M.length → (∀ m, msgAt M t = some m → ¬ m.isAd) → protoOk π img M t)
    (himg : PO_img π img) (had : PO_ad π img M) (hex : adExact img M) : Valid π img M M.length := by
  have key : ∀ V, Valid π img M V := by
    intro V
    induction V with
    | zero => exact ⟨himg, fun t h1 h2 => by omega⟩
    | succ V ih =>
      refine ⟨himg, fun t h1 h2 m hm => ?_⟩
      by_cases ht : t ≤ V
      · exact ih.2 t h1 (by omega) m hm
      · have htV : t = V + 1 := by omega
        subst htV
        have hlen : V + 1 ≤ M.length := by omega
        have hv : Valid π img M (V + 1 - 1) := by simpa using ih
        by_cases hd : m.isAd
        · exact had (V + 1) m h1 hlen hm hd hv (hex (V + 1) m h1 hlen hm hd)
        · exact hp (V + 1) h1 hlen (fun m' hm' => by rw [hm] at hm'; cases hm'; exact hd) m hm hv
  exact key M.length

/-! ## 4. Device independence (plan §0 [R6.1(b)], [R7.s2], [R7.s3]) -/

/-- `reachP pstep p0 p`: `p` is reachable from `p0` in the program LTS, over any labels and any fabric values. -/
inductive reachP (pstep : P → D → PLabel → P → D → Prop) : P → P → Prop
  | refl (p : P) : reachP pstep p p
  | step (p : P) (d : D) (l : PLabel) (p' : P) (d' : D) (q : P) :
      pstep p d l p' d' → reachP pstep p' q → reachP pstep p q

/-- `devFreeProg pstep ps` (plan §0): no step of any hart's program reads or writes the device fabric, on the states
reachable from its initial state.  The hart domain is explicit ([R7.s3]): hart `h` runs `ps[h]`. -/
def devFreeProg (pstep : P → D → PLabel → P → D → Prop) (ps : List P) : Prop :=
  ∀ (h : Nat) p0, ps[h]? = some p0 → ∀ p, reachP pstep p0 p → ∀ d l p' d', pstep p d l p' d' → d' = d ∧ ∀ d0, pstep p d0 l p' d0

end Weak.Prom.PF
