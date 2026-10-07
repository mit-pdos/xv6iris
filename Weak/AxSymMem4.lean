/-
Weak: **NON-VACUITY of the data certificate `EvD`** (`AxSymMem`) at `AxSmodeProbe`'s concrete
SUPERVISOR state (Sv39, real 3-level table, COLD TLB, A/D preset in the leaf PTEs:
`AxSmodeProbe.pteLeaf` = 0xCF).

Rocq: `iris/AxSymMem4.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 `evbd`: a boolean checker for `EvD`, the `AxSymEngine2.evb` twin with a demonic data-read arm
answered by a PARAMETER `vs0` and a validated data-write arm; `evbdSound`: the checker for EVERY
`vs0` of the data width is an `EvD` certificate (the data event happens at most once per path —
`evbdIndep`: after it the checker ignores `vs0` — so the ∀-read of `evdDrd` is covered
pointwise).
§2 `nvsdCert`: c.sdsp ra, 8(sp) (0xe406) at VA = PA 0x80000000: fetch through the cold-TLB walk,
the data translation (walk for sp+8's page), the 8-byte data WRITE to 0x80001008 — the
certificate premise of `wpdInstrOfEvD` for the REAL `riscvStep`, both ticks, all pin answers,
post PC + 2 and the written bytes = ra's bytes.
§3 `nvldCert`: c.ldsp ra, 8(sp) (0x60a2): the data READ is demonic (every 8-byte answer), post
PC + 2.  The image EXCLUDES the data doubleword (`imgNd`): data are not text, so the data read
cannot be an image read.

## Deviations from Rocq

1. O2 STAGE C (as `AxSymEngine2` deviation 1, `AxSymMem` deviation 1): the image arm of
   `evbd`'s read drops Rocq's `ak_coh` test (`EvD.evdMrd` covers fetches); the data-read arm
   additionally requires `(classify req.access_kind).akIfetch = false` (as `EvD.evdDrd`).
2. THE PINS (`AxSymEngine2` deviation 2): a pin read (`sig_seip` or `sig_meip`) is answered
   with both pins `0#1`, then both `1#1`; a pin write is `false`.  Q7: an `instrAnnounce` with
   `sfAnnB n w` is `false`.
3. LEAN-SAIL (`AxSymMem` deviation 2): a data write needs `req.value = some v` (else `false`) and
   moves to `DDone (WeakInterpProj.wbytes n v)`, answered `.Ok (some true)`; reads are answered
   `.Ok (wordOfBytes n vs, none)`; a failure node is `false` (QE is `False`).
4. TYPES (as `AxSmodeProbe` deviation 6): `mstate` ↦ `ExecSt`, the memory override
   `<[w64 a := b]>` ↦ the Lean-only `AxSymMem4.bmSet`, `img_of` ↦ `imgOf` (`AxSpineOk`),
   `register_lookup PC rs` ↦ `rs .PC` (compared with `==`), the post's byte-list equality by
   `decide`.
5. `vm_compute; reflexivity` ↦ `decide +kernel`; `nvldAll` (eight FREE bytes) ↦ the kernel
   `Eq.refl` tactic `ax_epi_ledger_krfl` (the evaluation never branches on the loaded bytes).

**Rocq → Lean name map.**  `dpend` `dpend`, `evbd` `evbd`, `evbd_indep` `evbdIndep`,
`evbd_sound` `evbdSound`, `nv_da` `nvDa`, `nv_dokb` `nvDokb`, `nv_regs` `nvRegs`, `nv_state`
`nvState`, `img_nd` `imgNd`, `nvsd_t` `nvsdT`, `nvsd_post` `nvsdPost`, `nvsd_false`
`nvsdFalse`, `nvsd_true` `nvsdTrue`, `nvsd_cert` `nvsdCert`, `nvld_t` `nvldT`, `nvld_post`
`nvldPost`, `nvld_all` `nvldAll`, `nvld_cert` `nvldCert`.  None is in the duplicated-name
table.  Lean-only (file-qualified): `AxSymMem4.bmSet`.

**Dropped:** nothing (Rocq 18 definitions/lemmas; Lean 18 + 1 Lean-only).
**Not ported:** the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxSymMem
import Weak.AxSymEngine2
import Weak.AxSmodeProbe
import Weak.AxSpineOk

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 1. The checker -/

def dpend (d : AxSymMem.Dstate) : Bool :=
  match d with
  | .DPend => true
  | _ => false

/-- The boolean `EvD` checker: the data read is answered by the parameter `vs0`. -/
def evbd {X : Type} (img : Image) (dokb : Int → Nat → Bool) (kind : Bool) (vs0 : List (BitVec 8))
    (Qb : AxSymMem.Dstate → X → ExecSt → Bool) :
    SailM X → AxSymMem.Dstate → ExecSt → Bool
  | .pure x, d, t => Qb d x t
  | .impure (.error _) _, _, _ => false
  | .impure (.ok o) k, d, t =>
    match o, k with
    | .regRead r, k =>
      if r = .sig_seip ∨ r = .sig_meip then
        evbd img dokb kind vs0 Qb (k (((t.regs.set .sig_seip 0#1).set .sig_meip 0#1) r)) d t &&
        evbd img dokb kind vs0 Qb (k (((t.regs.set .sig_seip 1#1).set .sig_meip 1#1) r)) d t
      else evbd img dokb kind vs0 Qb (k (t.regs r)) d t
    | .regWrite r v, k =>
      if r = .sig_seip ∨ r = .sig_meip then false
      else evbd img dokb kind vs0 Qb (k PUnit.unit) d (t.setReg r v)
    | .memRead n _ req, k =>
      if devAddr req.pa then false
      else if (classify req.access_kind).akLatest then false
      else if dokb (paZ req.pa) n then
        (if kind && dpend d && !(classify req.access_kind).akIfetch && (vs0.length == n) then
          evbd img dokb kind vs0 Qb (k (.Ok (wordOfBytes n vs0, none))) (.DDone vs0) t
        else false)
      else match imgBytes img (paZ req.pa) n with
        | some vs => evbd img dokb kind vs0 Qb (k (.Ok (wordOfBytes n vs, none))) d t
        | none => false
    | .memWrite n _ req, k =>
      if devAddr req.pa then false
      else if (classify req.access_kind).akLatest then false
      else if !kind && dpend d && dokb (paZ req.pa) n then
        (match req.value with
          | some v => evbd img dokb kind vs0 Qb (k (.Ok (some true)))
              (.DDone (WeakInterpProj.wbytes n v)) t
          | none => false)
      else false
    | .instrAnnounce n w, k => if sfAnnB n w then false else evbd img dokb kind vs0 Qb (k ()) d t
    | .branchAnnounce _ _, k => evbd img dokb kind vs0 Qb (k ()) d t
    | .cacheOp _, k => evbd img dokb kind vs0 Qb (k ()) d t
    | .tlbi _, k => evbd img dokb kind vs0 Qb (k ()) d t
    | .takeException _, k => evbd img dokb kind vs0 Qb (k ()) d t
    | .returnException _, k => evbd img dokb kind vs0 Qb (k ()) d t
    | .translationStart _, k => evbd img dokb kind vs0 Qb (k ()) d t
    | .translationEnd _, k => evbd img dokb kind vs0 Qb (k ()) d t
    | .cycleCount, k => evbd img dokb kind vs0 Qb (k ()) d t
    | .message _, k => evbd img dokb kind vs0 Qb (k ()) d t
    | .getCycleCount, k => evbd img dokb kind vs0 Qb (k (0 : Nat)) d t
    | _, _ => false

theorem evbdIndep {X : Type} (img : Image) (dokb : Int → Nat → Bool) (kind : Bool)
    (Qb : AxSymMem.Dstate → X → ExecSt → Bool) (m : SailM X) :
    ∀ vs vs' w t, evbd img dokb kind vs Qb m (.DDone w) t = evbd img dokb kind vs' Qb m (.DDone w) t := by
  induction m with
  | pure y => intro vs vs' w t; rfl
  | impure call k ih =>
    intro vs vs' w t
    cases call with
    | error e => rfl
    | ok o =>
      cases o
      case regRead r =>
        simp only [evbd]
        split
        · rw [ih _ vs vs', ih _ vs vs']
        · exact ih _ vs vs' w t
      case regWrite r v =>
        simp only [evbd]
        split
        · rfl
        · exact ih _ vs vs' w _
      case memRead n va req =>
        simp only [evbd, dpend, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        split
        · rfl
        · split
          · rfl
          · split
            · rfl
            · split
              · exact ih _ vs vs' w t
              · rfl
      case memWrite n va req =>
        simp only [evbd, dpend, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      case instrAnnounce n w' =>
        simp only [evbd]
        split
        · rfl
        · exact ih _ vs vs' w t
      case branchAnnounce n a => exact ih _ vs vs' w t
      case cacheOp c => exact ih _ vs vs' w t
      case tlbi c => exact ih _ vs vs' w t
      case takeException c => exact ih _ vs vs' w t
      case returnException c => exact ih _ vs vs' w t
      case translationStart c => exact ih _ vs vs' w t
      case translationEnd c => exact ih _ vs vs' w t
      case cycleCount => exact ih _ vs vs' w t
      case message c => exact ih _ vs vs' w t
      case getCycleCount => exact ih _ vs vs' w t
      all_goals rfl

theorem evbdSound {X : Type} (img : Image) (dokb : Int → Nat → Bool) (kind : Bool)
    (Qb : AxSymMem.Dstate → X → ExecSt → Bool) (L : Nat) (m : SailM X) :
    ∀ d t, (∀ vs0 : List (BitVec 8), vs0.length = L → evbd img dokb kind vs0 Qb m d t = true) →
      EvD img (fun a n => dokb a n = true) kind (fun _ _ _ => False)
        (fun d' x t' => Qb d' x t' = true) d m t := by
  induction m with
  | pure y =>
    intro d t hb
    exact .evdRet d y t (hb (List.replicate L 0#8) List.length_replicate)
  | impure call k ih =>
    intro d t hb
    have h0 := hb (List.replicate L 0#8) List.length_replicate
    cases call with
    | error e => simp [evbd] at h0
    | ok o =>
      cases o
      case regRead r =>
        refine .evdRd d r k t ?_ ?_
        · intro hp v
          have hp' : r = .sig_seip ∨ r = .sig_meip := hp
          apply ih
          intro vs0 hl
          have hb' := hb vs0 hl
          simp only [evbd] at hb'
          rw [if_pos hp', Bool.and_eq_true] at hb'
          rcases hp with rfl | rfl <;> rcases bv1_cases v with rfl | rfl
          · simpa [RegFile.set_same, RegFile.set_other] using hb'.1
          · simpa [RegFile.set_same, RegFile.set_other] using hb'.2
          · simpa [RegFile.set_same] using hb'.1
          · simpa [RegFile.set_same] using hb'.2
        · intro hp
          have hp' : ¬ (r = .sig_seip ∨ r = .sig_meip) := hp
          apply ih
          intro vs0 hl
          have hb' := hb vs0 hl
          simp only [evbd] at hb'
          rw [if_neg hp'] at hb'
          exact hb'
      case regWrite r v =>
        by_cases hp : r = .sig_seip ∨ r = .sig_meip
        · simp only [evbd] at h0
          rw [if_pos hp] at h0
          cases h0
        · refine .evdWr d r v k t hp (ih _ _ _ ?_)
          intro vs0 hl
          have hb' := hb vs0 hl
          simp only [evbd] at hb'
          rw [if_neg hp] at hb'
          exact hb'
      case memRead n va req =>
        simp only [evbd] at h0
        cases hd : devAddr req.pa
        · cases hla : (classify req.access_kind).akLatest
          · cases hdk : dokb (paZ req.pa) n
            · cases hv : imgBytes img (paZ req.pa) n with
              | none => simp [hd, hla, hdk, hv] at h0
              | some vs =>
                refine .evdMrd d n va req k t vs hd hla hv (ih _ _ _ ?_)
                intro vs0 hl
                have hb' := hb vs0 hl
                simp only [evbd, hd, hla, hdk, hv, Bool.false_eq_true, ↓reduceIte] at hb'
                exact hb'
            · cases hk : kind <;> cases d <;> cases hf : (classify req.access_kind).akIfetch <;>
                simp [hd, hla, hdk, hk, hf, dpend] at h0
              obtain ⟨hLn, -⟩ := h0
              subst hLn hk
              refine .evdDrd L va req k t rfl hd hla hf hdk ?_
              intro vs hlv
              apply ih
              intro vs0 _
              rw [evbdIndep img dokb true Qb _ vs0 vs]
              have hb' := hb vs hlv
              simp only [evbd, hd, hla, hdk, hf, dpend, hlv, beq_self_eq_true, Bool.not_false,
                Bool.and_self, Bool.false_eq_true, ↓reduceIte] at hb'
              exact hb'
          · simp [hd, hla] at h0
        · simp [hd] at h0
      case memWrite n va req =>
        simp only [evbd] at h0
        cases hd : devAddr req.pa
        · cases hla : (classify req.access_kind).akLatest
          · cases hk : kind <;> cases d <;> cases hdk : dokb (paZ req.pa) n <;>
              simp [hd, hla, hk, hdk, dpend] at h0
            cases hval : req.value with
            | none => simp [hval] at h0
            | some v =>
              subst hk
              refine .evdDwr n va req k t v rfl hd hla hval hdk (ih _ _ _ ?_)
              intro vs0 hl
              have hb' := hb vs0 hl
              simp only [evbd, hd, hla, hdk, hval, dpend, Bool.not_false, Bool.and_self,
                Bool.false_eq_true, ↓reduceIte] at hb'
              exact hb'
          · simp [hd, hla] at h0
        · simp [hd] at h0
      case instrAnnounce n w =>
        cases hs : sfAnnB n w
        · refine .evdIa d n w k t hs (ih _ _ _ ?_)
          intro vs0 hl
          have hb' := hb vs0 hl
          simp only [evbd, hs, Bool.false_eq_true, ↓reduceIte] at hb'
          exact hb'
        · simp [evbd, hs] at h0
      case branchAnnounce n a => exact .evdBa d n a k t (ih _ _ _ fun vs0 hl => hb vs0 hl)
      case cacheOp c => exact .evdCo d c k t (ih _ _ _ fun vs0 hl => hb vs0 hl)
      case tlbi c => exact .evdTl d c k t (ih _ _ _ fun vs0 hl => hb vs0 hl)
      case takeException c => exact .evdTe d c k t (ih _ _ _ fun vs0 hl => hb vs0 hl)
      case returnException c => exact .evdRx d c k t (ih _ _ _ fun vs0 hl => hb vs0 hl)
      case translationStart c => exact .evdTs d c k t (ih _ _ _ fun vs0 hl => hb vs0 hl)
      case translationEnd c => exact .evdTx d c k t (ih _ _ _ fun vs0 hl => hb vs0 hl)
      case cycleCount => exact .evdCc d k t (ih _ _ _ fun vs0 hl => hb vs0 hl)
      case message c => exact .evdMsg d c k t (ih _ _ _ fun vs0 hl => hb vs0 hl)
      case getCycleCount => exact .evdGcc d k t (ih _ _ _ fun vs0 hl => hb vs0 hl)
      all_goals simp [evbd] at h0

/-! # 2. The concrete store -/

def nvDa : Int := (AxSmodeProbe.sSp : Int) + 8

def nvDokb (a : Int) (n : Nat) : Bool := (a == nvDa) && (n == 8)

def nvRegs : RegFile := (sRegs sPc).set .x1 (AxEpiProbe.w64 0x1122334455667788)

/-- (Lean-only) Override one byte of a byte map. -/
def AxSymMem4.bmSet (m : BMap) (a : PAddr) (b : BitVec 8) : BMap := fun a' =>
  if a' == a then some b else m a'

/-- The probe memory with the text word replaced (c.xxx ; c.nop). -/
def nvState (lo hi : Nat) : ExecSt :=
  ⟨nvRegs,
    AxSymMem4.bmSet (AxSymMem4.bmSet (AxSymMem4.bmSet (AxSymMem4.bmSet (sAt sPc).mem
      (AxEpiProbe.w64 (sPc + 3)) 0x00#8) (AxEpiProbe.w64 (sPc + 2)) 0x01#8)
      (AxEpiProbe.w64 (sPc + 1)) (BitVec.ofNat 8 hi)) (AxEpiProbe.w64 sPc) (BitVec.ofNat 8 lo),
    testDevs⟩

/-- The image: memory minus the data doubleword. -/
def imgNd (t : ExecSt) (a : Int) : Option (BitVec 8) :=
  if nvDa ≤ a ∧ a < nvDa + 8 then none else imgOf t a

/-- c.sdsp ra, 8(sp). -/
def nvsdT : ExecSt := nvState 0x06 0xe4

def nvsdPost (d : AxSymMem.Dstate) (_ : Unit) (t' : ExecSt) : Bool :=
  match d with
  | .DDone vs => (t'.regs .PC == AxEpiProbe.w64 (sPc + 2)) &&
      decide (vs = WeakInterpProj.wbytes 8 (nvRegs .x1))
  | .DPend => false

theorem nvsdFalse : evbd (imgNd nvsdT) nvDokb false [] nvsdPost (riscvStep false) .DPend nvsdT = true := by
  decide +kernel

theorem nvsdTrue : evbd (imgNd nvsdT) nvDokb false [] nvsdPost (riscvStep true) .DPend nvsdT = true := by
  decide +kernel

theorem nvsdCert (tick : Bool) :
    EvD (imgNd nvsdT) (fun a n => nvDokb a n = true) false (fun _ _ _ => False)
      (fun d x t' => nvsdPost d x t' = true) .DPend (riscvStep tick) nvsdT := by
  apply evbdSound _ _ _ _ 0
  intro vs0 hl
  cases vs0 with
  | cons _ _ => cases hl
  | nil =>
    cases tick
    · exact nvsdFalse
    · exact nvsdTrue

/-! # 3. The concrete load: the data read is DEMONIC -/

/-- c.ldsp ra, 8(sp). -/
def nvldT : ExecSt := nvState 0xa2 0x60

def nvldPost (d : AxSymMem.Dstate) (_ : Unit) (t' : ExecSt) : Bool :=
  match d with
  | .DDone _ => t'.regs .PC == AxEpiProbe.w64 (sPc + 2)
  | .DPend => false

theorem nvldAll (tick : Bool) (vs : List (BitVec 8)) : vs.length = 8 →
    evbd (imgNd nvldT) nvDokb true vs nvldPost (riscvStep tick) .DPend nvldT = true := by
  intro hl
  match vs, hl with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    cases tick
    · show evbd (imgNd nvldT) nvDokb true [b0, b1, b2, b3, b4, b5, b6, b7] nvldPost
        (riscvStep false) .DPend nvldT = true
      ax_epi_ledger_krfl
    · show evbd (imgNd nvldT) nvDokb true [b0, b1, b2, b3, b4, b5, b6, b7] nvldPost
        (riscvStep true) .DPend nvldT = true
      ax_epi_ledger_krfl

theorem nvldCert (tick : Bool) :
    EvD (imgNd nvldT) (fun a n => nvDokb a n = true) true (fun _ _ _ => False)
      (fun d x t' => nvldPost d x t' = true) .DPend (riscvStep tick) nvldT :=
  evbdSound _ _ _ _ 8 _ _ _ fun vs0 hl => nvldAll tick vs0 hl

end Weak
