/-
Weak: **NON-VACUITY of `AxCert.Cert`'s BARRIER and RMW arms** on the REAL Sail model, at
`AxSmodeProbe`'s concrete SUPERVISOR state (Sv39, real 3-level table, cold TLB, A/D preset; PMP
TOR over RAM).

Rocq: `iris/AxCert3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 `certb`: a boolean checker for `AxCert.Cert` at budget `BInf` (the `evbd` twin, `AxSymMem4`):
demonic data / exclusive reads answered by a PARAMETER `vs0` (used at most once per path,
`certbIndep`), a validated data / exclusive write, the barrier arm moving the flag by `relpUpd`;
`certbSound`: the checker for EVERY `vs0` of the data width is a `Cert` (both pin answers are
explored at every pin read).
§2/§3 THE RELEASE PAIR (xv6 `release`): `fence rw,w` (0x0310000f) at VA = PA 0x80000000 —
`ctfCert`: the real `riscvStep` (both ticks) is a Cert ending with NO data event, the
release-pending flag ARMED, PC + 4; then `sw zero, 0(a0)` (0x00052023) at 0x80000004 FROM an armed
flag — `ctsCert`: the data write of `[0,0,0,0]` to 0x80001008 is certified with class `WCrel`
(the flag cleared afterwards); `ctsUnarmed`: from an UNARMED flag the checker rejects (the fence
is load-bearing).
§4 THE ACQUIRE RMW: `amoswap.w.aq a1, ra, (a0)` (0x0c1525af) — `ctaCert`: the exclusive read of
4 bytes at 0x80001008 is DEMONIC (every answer), the exclusive write stores ra's low word, the
certificate ends in `CRmw true false _ (wbytes 4 ra) WCexcl`, PC + 4.
The image excludes the data doubleword (data are not text).

## Deviations from Rocq

1. O2 STAGE C (as `AxSymMem4` deviation 1, `AxCert` deviation 1): the image arm of `certb`'s
   read drops Rocq's `ak_coh` test and is checked as `Cert.cIf` (a fetch, `akIfetch = true`) or
   `Cert.cMrd` (a graph image read) by the access kind; the data-read arm additionally requires
   `akIfetch = false` (as `Cert.cDrd`).
2. THE PINS (`AxCert` deviation 2, `AxSymMem4` deviation 2): a pin read (`sig_seip` or
   `sig_meip`, `AxRunClose.pinReg`) is answered with both pins `0#1`, then both `1#1`; a pin
   write is `false`.  Q19: an `instrAnnounce` is accepted whatever its word — an SFENCE.VMA
   announce (`sfAnnB n w`) is certified by `Cert.cSf` (at `BInf` the budget is unchanged), any
   other by `Cert.cIa` (Q7 had the checker reject the sfence announce).
3. LEAN-SAIL (`AxCert` deviation 5): data / exclusive writes need `req.value = some v` (else
   `false`), record `WeakInterpProj.wbytes n v` and are answered `.Ok (some true)`; reads are
   answered `.Ok (wordOfBytes n vs, none)`; a failure node is `false` (QE is `False`).
4. TYPES (as `AxSymMem4` deviation 4): `mstate` ↦ `ExecSt`, the byte override `<[w64 a := b]>` ↦
   `AxSymMem4.bmSet` (reused), `Z_to_bv 8 (default 0 (bs !! j))` ↦
   `BitVec.ofNat 8 (bs.getD j 0)` (words as `List Nat`), `dev0_state` ↦ `testDevs`,
   `register_lookup PC rs` ↦ `rs .PC` (compared with `==`), byte-list equalities by `decide`;
   `ctRegs`/`ctState`/`ctrT` take `pc : Nat`.
5. `vm_compute; reflexivity` ↦ `decide +kernel`; `ctaAll` (four FREE bytes) ↦ the kernel
   `Eq.refl` tactic `ax_epi_ledger_krfl`.

**Rocq → Lean name map.**  `cpend` `cpend`, `dk_eqb` `dkEqb`, `dk_eqb_spec` `dkEqbSpec`, `certb`
`certb`, `certb_indep` `certbIndep`, `certb_sound` `certbSound`, `ct_da` `ctDa`, `ct_dokb`
`ctDokb`, `ct_regs` `ctRegs`, `ct_state` `ctState`, `ct_img` `ctImg`, `w_fence` `wFence`, `w_sw`
`wSw`, `w_amo` `wAmo`, `ctr_t` `ctrT`, `ctf_post` `ctfPost`, `ctf_false` `ctfFalse`, `ctf_true`
`ctfTrue`, `ctf_cert` `ctfCert`, `cts_post` `ctsPost`, `cts_false` `ctsFalse`, `cts_true`
`ctsTrue`, `cts_cert` `ctsCert`, `cts_unarmed` `ctsUnarmed`, `cta_t` `ctaT`, `cta_post`
`ctaPost`, `cta_all` `ctaAll`, `cta_cert` `ctaCert`.  None is in the duplicated-name table.

**Dropped:** nothing (Rocq 28 definitions/lemmas; Lean 28).
**Not ported:** the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxCert
import Weak.AxSymMem4

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 1. The checker -/

def cpend (d : Cdata) : Bool :=
  match d with
  | .CPend => true
  | _ => false

def dkEqb (a b : Dkind) : Bool :=
  match a, b with
  | .DKLd, .DKLd | .DKSt, .DKSt | .DKRmw, .DKRmw => true
  | _, _ => false

theorem dkEqbSpec (a b : Dkind) : dkEqb a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [dkEqb]

/-- The boolean `Cert` checker at `BInf`: data / exclusive reads are answered by `vs0`. -/
def certb {X : Type} (img : Image) (dokb : Int → Nat → Bool) (kind : Dkind)
    (vs0 : List (BitVec 8)) (Qb : Cst → X → ExecSt → Bool) :
    SailM X → Cdata → Bool → ExecSt → Bool
  | .pure x, d, r, t => Qb ⟨d, .BInf, r⟩ x t
  | .impure (.error _) _, _, _, _ => false
  | .impure (.ok o) k, d, r, t =>
    match o, k with
    | .regRead rg, k =>
      if rg = .sig_seip ∨ rg = .sig_meip then
        certb img dokb kind vs0 Qb (k (((t.regs.set .sig_seip 0#1).set .sig_meip 0#1) rg)) d r t &&
        certb img dokb kind vs0 Qb (k (((t.regs.set .sig_seip 1#1).set .sig_meip 1#1) rg)) d r t
      else certb img dokb kind vs0 Qb (k (t.regs rg)) d r t
    | .regWrite rg v, k =>
      if rg = .sig_seip ∨ rg = .sig_meip then false
      else certb img dokb kind vs0 Qb (k PUnit.unit) d r (t.setReg rg v)
    | .memRead n _ req, k =>
      if devAddr req.pa then false
      else if (classify req.access_kind).akLatest then
        (if dkEqb kind .DKRmw && cpend d && dokb (paZ req.pa) n && (vs0.length == n) then
          certb img dokb kind vs0 Qb (k (.Ok (wordOfBytes n vs0, none)))
            (.CRmwR (classify req.access_kind).akSync vs0) r t
        else false)
      else if dokb (paZ req.pa) n then
        (if dkEqb kind .DKLd && cpend d && !(classify req.access_kind).akIfetch &&
            (vs0.length == n) then
          certb img dokb kind vs0 Qb (k (.Ok (wordOfBytes n vs0, none))) (.CLd vs0) r t
        else false)
      else match imgBytes img (paZ req.pa) n with
        | some vs => certb img dokb kind vs0 Qb (k (.Ok (wordOfBytes n vs, none))) d r t
        | none => false
    | .memWrite n _ req, k =>
      if devAddr req.pa then false
      else if !(dokb (paZ req.pa) n) then false
      else if (classify req.access_kind).akLatest then
        (match d, req.value with
          | .CRmwR aq rvs, some v =>
            if dkEqb kind .DKRmw then
              certb img dokb kind vs0 Qb (k (.Ok (some true)))
                (.CRmw aq (classify req.access_kind).akSync rvs (WeakInterpProj.wbytes n v)
                  (wcls req.access_kind r)) false t
            else false
          | _, _ => false)
      else if dkEqb kind .DKSt && cpend d then
        (match req.value with
          | some v => certb img dokb kind vs0 Qb (k (.Ok (some true)))
              (.CSt (WeakInterpProj.wbytes n v) (wcls req.access_kind r)) false t
          | none => false)
      else false
    | .barrier bk, k =>
      match ebarPark bk with
      | none => certb img dokb kind vs0 Qb (k ()) d (relpUpd (ebarLabel bk) r) t
      | some _ => false
    | .instrAnnounce _ _, k => certb img dokb kind vs0 Qb (k ()) d r t
    | .branchAnnounce _ _, k => certb img dokb kind vs0 Qb (k ()) d r t
    | .cacheOp _, k => certb img dokb kind vs0 Qb (k ()) d r t
    | .tlbi _, k => certb img dokb kind vs0 Qb (k ()) d r t
    | .takeException _, k => certb img dokb kind vs0 Qb (k ()) d r t
    | .returnException _, k => certb img dokb kind vs0 Qb (k ()) d r t
    | .translationStart _, k => certb img dokb kind vs0 Qb (k ()) d r t
    | .translationEnd _, k => certb img dokb kind vs0 Qb (k ()) d r t
    | .cycleCount, k => certb img dokb kind vs0 Qb (k ()) d r t
    | .message _, k => certb img dokb kind vs0 Qb (k ()) d r t
    | .getCycleCount, k => certb img dokb kind vs0 Qb (k (0 : Nat)) d r t
    | _, _ => false

/-- After the data event the checker ignores `vs0`. -/
theorem certbIndep {X : Type} (img : Image) (dokb : Int → Nat → Bool) (kind : Dkind)
    (Qb : Cst → X → ExecSt → Bool) (m : SailM X) :
    ∀ vs vs' d r t, cpend d = false →
      certb img dokb kind vs Qb m d r t = certb img dokb kind vs' Qb m d r t := by
  induction m with
  | pure y => intro vs vs' d r t _; rfl
  | impure call k ih =>
    intro vs vs' d r t hd
    cases call with
    | error e => rfl
    | ok o =>
      cases o
      case regRead rg =>
        simp only [certb]
        split
        · rw [ih _ vs vs' d r t hd, ih _ vs vs' d r t hd]
        · exact ih _ vs vs' d r t hd
      case regWrite rg v =>
        simp only [certb]
        split
        · rfl
        · exact ih _ vs vs' d r _ hd
      case memRead n va req =>
        simp only [certb, hd, Bool.and_false]
        split
        · rfl
        · split
          · rfl
          · split
            · rfl
            · split
              · exact ih _ vs vs' d r t hd
              · rfl
      case memWrite n va req =>
        simp only [certb, hd, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        split
        · rfl
        · split
          · rfl
          · split
            · split
              · split
                · exact ih _ vs vs' _ false t rfl
                · rfl
              · rfl
            · rfl
      case barrier bk =>
        simp only [certb]
        split
        · exact ih _ vs vs' d _ t hd
        · rfl
      case instrAnnounce n w' => exact ih _ vs vs' d r t hd
      case branchAnnounce n a => exact ih _ vs vs' d r t hd
      case cacheOp c => exact ih _ vs vs' d r t hd
      case tlbi c => exact ih _ vs vs' d r t hd
      case takeException c => exact ih _ vs vs' d r t hd
      case returnException c => exact ih _ vs vs' d r t hd
      case translationStart c => exact ih _ vs vs' d r t hd
      case translationEnd c => exact ih _ vs vs' d r t hd
      case cycleCount => exact ih _ vs vs' d r t hd
      case message c => exact ih _ vs vs' d r t hd
      case getCycleCount => exact ih _ vs vs' d r t hd
      all_goals rfl

theorem certbSound {X : Type} (img : Image) (dokb : Int → Nat → Bool) (kind : Dkind)
    (Qb : Cst → X → ExecSt → Bool) (L : Nat) (m : SailM X) :
    ∀ d r t, (∀ vs0 : List (BitVec 8), vs0.length = L → certb img dokb kind vs0 Qb m d r t = true) →
      AxCert.Cert img (fun a n => dokb a n = true) kind (fun _ _ _ => False)
        (fun s x t' => Qb s x t' = true) ⟨d, .BInf, r⟩ m t := by
  induction m with
  | pure y =>
    intro d r t hb
    exact .cRet _ y t (hb (List.replicate L 0#8) List.length_replicate)
  | impure call k ih =>
    intro d r t hb
    have h0 := hb (List.replicate L 0#8) List.length_replicate
    cases call with
    | error e => simp [certb] at h0
    | ok o =>
      cases o
      case regRead rg =>
        refine .cRd _ rg k t ?_ ?_
        · intro hp v
          have hp' : rg = .sig_seip ∨ rg = .sig_meip := hp
          apply ih
          intro vs0 hl
          have hb' := hb vs0 hl
          simp only [certb] at hb'
          rw [if_pos hp', Bool.and_eq_true] at hb'
          rcases hp' with rfl | rfl <;> rcases bv1_cases v with rfl | rfl
          · simpa [RegFile.set_same, RegFile.set_other] using hb'.1
          · simpa [RegFile.set_same, RegFile.set_other] using hb'.2
          · simpa [RegFile.set_same] using hb'.1
          · simpa [RegFile.set_same] using hb'.2
        · intro hp
          have hp' : ¬ (rg = .sig_seip ∨ rg = .sig_meip) := hp
          apply ih
          intro vs0 hl
          have hb' := hb vs0 hl
          simp only [certb] at hb'
          rw [if_neg hp'] at hb'
          exact hb'
      case regWrite rg v =>
        by_cases hp : rg = .sig_seip ∨ rg = .sig_meip
        · simp only [certb] at h0
          rw [if_pos hp] at h0
          cases h0
        · refine .cWr _ rg v k t hp (ih _ _ _ _ ?_)
          intro vs0 hl
          have hb' := hb vs0 hl
          simp only [certb] at hb'
          rw [if_neg hp] at hb'
          exact hb'
      case memRead n va req =>
        simp only [certb] at h0
        cases hd : devAddr req.pa
        · cases hla : (classify req.access_kind).akLatest
          · cases hdk : dokb (paZ req.pa) n
            · cases hv : imgBytes img (paZ req.pa) n with
              | none => simp [hd, hla, hdk, hv] at h0
              | some vs =>
                have hk' : AxCert.Cert img (fun a n => dokb a n = true) kind (fun _ _ _ => False)
                    (fun s x t' => Qb s x t' = true) ⟨d, .BInf, r⟩
                    (k (.Ok (wordOfBytes n vs, none))) t := by
                  apply ih
                  intro vs0 hl
                  have hb' := hb vs0 hl
                  simp only [certb, hd, hla, hdk, hv, Bool.false_eq_true, ↓reduceIte] at hb'
                  exact hb'
                cases hf : (classify req.access_kind).akIfetch
                · exact .cMrd d .BInf r n va req k t vs hd hla hf hv hk'
                · exact .cIf _ n va req k t vs hd hla hf hv hk'
            · cases hk : kind <;> cases d <;> cases hf : (classify req.access_kind).akIfetch <;>
                simp [hd, hla, hdk, hk, hf, cpend, dkEqb] at h0
              obtain ⟨hLn, -⟩ := h0
              subst hLn hk
              refine .cDrd .BInf r L va req k t rfl hd hla hf hdk ?_
              intro vs hlv
              apply ih
              intro vs0 _
              rw [certbIndep img dokb .DKLd Qb _ vs0 vs _ r t rfl]
              have hb' := hb vs hlv
              simp only [certb, hd, hla, hdk, hf, cpend, dkEqb, hlv, beq_self_eq_true,
                Bool.not_false, Bool.and_self, Bool.false_eq_true, ↓reduceIte] at hb'
              exact hb'
          · cases hk : kind <;> cases d <;> cases hdk : dokb (paZ req.pa) n <;>
              simp [hd, hla, hdk, hk, cpend, dkEqb] at h0
            obtain ⟨hLn, -⟩ := h0
            subst hLn hk
            refine .cXrd .BInf r L va req k t rfl hd hla hdk ?_
            intro vs hlv
            apply ih
            intro vs0 _
            rw [certbIndep img dokb .DKRmw Qb _ vs0 vs _ r t rfl]
            have hb' := hb vs hlv
            simp only [certb, hd, hla, hdk, cpend, dkEqb, hlv, beq_self_eq_true,
              Bool.and_self, Bool.false_eq_true, ↓reduceIte] at hb'
            exact hb'
        · simp [hd] at h0
      case memWrite n va req =>
        simp only [certb] at h0
        cases hd : devAddr req.pa
        · cases hdk : dokb (paZ req.pa) n
          · simp [hd, hdk] at h0
          · cases hla : (classify req.access_kind).akLatest
            · cases hk : kind <;> cases d <;> simp [hd, hla, hk, hdk, cpend, dkEqb] at h0
              cases hval : req.value with
              | none => simp [hval] at h0
              | some v =>
                subst hk
                refine .cDwr .BInf r n va req k t v rfl hd hla hval hdk (ih _ _ _ _ ?_)
                intro vs0 hl
                have hb' := hb vs0 hl
                simp only [certb, hd, hla, hdk, hval, cpend, dkEqb, Bool.not_true, Bool.and_self,
                  Bool.false_eq_true, ↓reduceIte] at hb'
                exact hb'
            · cases d with
              | CRmwR aq rvs =>
                cases hval : req.value with
                | none => simp [hd, hla, hdk, hval] at h0
                | some v =>
                  cases hk : kind <;> simp [hd, hla, hdk, hval, hk, dkEqb] at h0
                  subst hk
                  refine .cXwr aq rvs .BInf r n va req k t v rfl hd hla hval hdk (ih _ _ _ _ ?_)
                  intro vs0 hl
                  have hb' := hb vs0 hl
                  simp only [certb, hd, hla, hdk, hval, dkEqb, Bool.not_true,
                    Bool.false_eq_true, ↓reduceIte] at hb'
                  exact hb'
              | _ => simp [hd, hla, hdk] at h0
        · simp [hd] at h0
      case barrier bk =>
        cases hp : ebarPark bk with
        | some _ => simp [certb, hp] at h0
        | none =>
          refine .cFence d .BInf r bk k t hp (ih _ _ _ _ ?_)
          intro vs0 hl
          have hb' := hb vs0 hl
          simp only [certb, hp] at hb'
          exact hb'
      case instrAnnounce n w =>
        cases hs : sfAnnB n w
        · exact .cIa _ n w k t hs (ih _ _ _ _ fun vs0 hl => hb vs0 hl)
        · exact .cSf d .BInf r n w k t hs (ih _ _ _ _ fun vs0 hl => hb vs0 hl)
      case branchAnnounce n a => exact .cBa _ n a k t (ih _ _ _ _ fun vs0 hl => hb vs0 hl)
      case cacheOp c => exact .cCo _ c k t (ih _ _ _ _ fun vs0 hl => hb vs0 hl)
      case tlbi c => exact .cTl _ c k t (ih _ _ _ _ fun vs0 hl => hb vs0 hl)
      case takeException c => exact .cTe _ c k t (ih _ _ _ _ fun vs0 hl => hb vs0 hl)
      case returnException c => exact .cRx _ c k t (ih _ _ _ _ fun vs0 hl => hb vs0 hl)
      case translationStart c => exact .cTs _ c k t (ih _ _ _ _ fun vs0 hl => hb vs0 hl)
      case translationEnd c => exact .cTx _ c k t (ih _ _ _ _ fun vs0 hl => hb vs0 hl)
      case cycleCount => exact .cCc _ k t (ih _ _ _ _ fun vs0 hl => hb vs0 hl)
      case message c => exact .cMsg _ c k t (ih _ _ _ _ fun vs0 hl => hb vs0 hl)
      case getCycleCount => exact .cGcc _ k t (ih _ _ _ _ fun vs0 hl => hb vs0 hl)
      all_goals simp [certb] at h0

/-! # 2. Concrete states -/

/-- 0x80001008: the data / lock word. -/
def ctDa : Int := (AxSmodeProbe.sSp : Int) + 8

def ctDokb (a : Int) (n : Nat) : Bool := (a == ctDa) && (n == 4)

/-- ra = 0x1122334455667788, a0 = the data address, PC = `pc`. -/
def ctRegs (pc : Nat) : RegFile :=
  ((sRegs pc).set .x1 (AxEpiProbe.w64 0x1122334455667788)).set .x10
    (AxEpiProbe.w64 (AxSmodeProbe.sSp + 8))

/-- Text: the 8 bytes `w0 ++ w1` at sPc .. sPc + 7. -/
def ctState (pc : Nat) (w0 w1 : List Nat) : ExecSt :=
  let bs := w0 ++ w1
  let b (j : Nat) : BitVec 8 := BitVec.ofNat 8 (bs.getD j 0)
  ⟨ctRegs pc,
    AxSymMem4.bmSet (AxSymMem4.bmSet (AxSymMem4.bmSet (AxSymMem4.bmSet
    (AxSymMem4.bmSet (AxSymMem4.bmSet (AxSymMem4.bmSet (AxSymMem4.bmSet (sAt sPc).mem
      (AxEpiProbe.w64 (sPc + 7)) (b 7)) (AxEpiProbe.w64 (sPc + 6)) (b 6))
      (AxEpiProbe.w64 (sPc + 5)) (b 5)) (AxEpiProbe.w64 (sPc + 4)) (b 4))
      (AxEpiProbe.w64 (sPc + 3)) (b 3)) (AxEpiProbe.w64 (sPc + 2)) (b 2))
      (AxEpiProbe.w64 (sPc + 1)) (b 1)) (AxEpiProbe.w64 sPc) (b 0),
    testDevs⟩

/-- The image: memory minus the data doubleword. -/
def ctImg (t : ExecSt) (a : Int) : Option (BitVec 8) :=
  if ctDa ≤ a ∧ a < ctDa + 8 then none else imgOf t a

/-- fence rw,w = 0x0310000f. -/
def wFence : List Nat := [0x0f, 0x00, 0x10, 0x03]
/-- sw zero,0(a0) = 0x00052023. -/
def wSw : List Nat := [0x23, 0x20, 0x05, 0x00]
/-- amoswap.w.aq a1,ra,(a0) = 0x0c1525af. -/
def wAmo : List Nat := [0xaf, 0x25, 0x15, 0x0c]

/-! # 3. The release pair -/

def ctrT (pc : Nat) : ExecSt := ctState pc wFence wSw

/-- `fence rw,w`: no data event, flag ARMED, PC + 4. -/
def ctfPost (s : Cst) (_ : Unit) (t' : ExecSt) : Bool :=
  match s with
  | ⟨.CPend, .BInf, true⟩ => t'.regs .PC == AxEpiProbe.w64 (sPc + 4)
  | _ => false

theorem ctfFalse :
    certb (ctImg (ctrT sPc)) ctDokb .DKSt [] ctfPost (riscvStep false) .CPend false (ctrT sPc) = true := by
  decide +kernel

theorem ctfTrue :
    certb (ctImg (ctrT sPc)) ctDokb .DKSt [] ctfPost (riscvStep true) .CPend false (ctrT sPc) = true := by
  decide +kernel

theorem ctfCert (tick : Bool) :
    AxCert.Cert (ctImg (ctrT sPc)) (fun a n => ctDokb a n = true) .DKSt (fun _ _ _ => False)
      (fun s x t' => ctfPost s x t' = true) ⟨.CPend, .BInf, false⟩ (riscvStep tick) (ctrT sPc) := by
  apply certbSound _ _ _ _ 0
  intro vs0 hl
  cases vs0 with
  | cons _ _ => cases hl
  | nil =>
    cases tick
    · exact ctfFalse
    · exact ctfTrue

/-- `sw zero, 0(a0)` FROM AN ARMED FLAG: the store is `WCrel`, flag cleared. -/
def ctsPost (s : Cst) (_ : Unit) (t' : ExecSt) : Bool :=
  match s with
  | ⟨.CSt vs .WCrel, .BInf, false⟩ =>
    (t'.regs .PC == AxEpiProbe.w64 (sPc + 8)) && decide (vs = [0#8, 0#8, 0#8, 0#8])
  | _ => false

theorem ctsFalse :
    certb (ctImg (ctrT (sPc + 4))) ctDokb .DKSt [] ctsPost (riscvStep false) .CPend true
      (ctrT (sPc + 4)) = true := by
  decide +kernel

theorem ctsTrue :
    certb (ctImg (ctrT (sPc + 4))) ctDokb .DKSt [] ctsPost (riscvStep true) .CPend true
      (ctrT (sPc + 4)) = true := by
  decide +kernel

theorem ctsCert (tick : Bool) :
    AxCert.Cert (ctImg (ctrT (sPc + 4))) (fun a n => ctDokb a n = true) .DKSt (fun _ _ _ => False)
      (fun s x t' => ctsPost s x t' = true) ⟨.CPend, .BInf, true⟩ (riscvStep tick)
      (ctrT (sPc + 4)) := by
  apply certbSound _ _ _ _ 0
  intro vs0 hl
  cases vs0 with
  | cons _ _ => cases hl
  | nil =>
    cases tick
    · exact ctsFalse
    · exact ctsTrue

/-- NEGATIVE TWIN: the same store from an UNARMED flag is NOT `WCrel` — the fence is what makes
the release (the flag is load-bearing). -/
theorem ctsUnarmed :
    certb (ctImg (ctrT (sPc + 4))) ctDokb .DKSt [] ctsPost (riscvStep false) .CPend false
      (ctrT (sPc + 4)) = false := by
  decide +kernel

/-! # 4. The acquire RMW -/

def ctaT : ExecSt := ctState sPc wAmo wSw

def ctaPost (s : Cst) (_ : Unit) (t' : ExecSt) : Bool :=
  match s with
  | ⟨.CRmw true false rvs wvs .WCexcl, .BInf, false⟩ =>
    (t'.regs .PC == AxEpiProbe.w64 (sPc + 4)) &&
      decide (wvs = [0x88#8, 0x77#8, 0x66#8, 0x55#8]) && (rvs.length == 4)
  | _ => false

theorem ctaAll (tick : Bool) (vs : List (BitVec 8)) : vs.length = 4 →
    certb (ctImg ctaT) ctDokb .DKRmw vs ctaPost (riscvStep tick) .CPend false ctaT = true := by
  intro hl
  match vs, hl with
  | [b0, b1, b2, b3], _ =>
    cases tick
    · show certb (ctImg ctaT) ctDokb .DKRmw [b0, b1, b2, b3] ctaPost (riscvStep false) .CPend
        false ctaT = true
      ax_epi_ledger_krfl
    · show certb (ctImg ctaT) ctDokb .DKRmw [b0, b1, b2, b3] ctaPost (riscvStep true) .CPend
        false ctaT = true
      ax_epi_ledger_krfl

theorem ctaCert (tick : Bool) :
    AxCert.Cert (ctImg ctaT) (fun a n => ctDokb a n = true) .DKRmw (fun _ _ _ => False)
      (fun s x t' => ctaPost s x t' = true) ⟨.CPend, .BInf, false⟩ (riscvStep tick) ctaT :=
  certbSound _ _ _ _ 4 _ _ _ _ fun vs0 hl => ctaAll tick vs0 hl

end Weak
