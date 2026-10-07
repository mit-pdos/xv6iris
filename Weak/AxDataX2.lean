/-
Weak: **the two INSTANCES of `AxDataX`'s certificate kit** — `AxSymMem.EvD` (§1) and
`AxCert.Cert` at budget `BInf` (§2, state `Cdata × Bool` = data event and release-pending flag)
— and the data chain's top lemmas at each instance (§3).

Rocq: `iris/AxDataX2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 the `EvD` kit rules `kD_*` (mono, ret, bind, try-catch, failure node, register read / write
off the pins, the `EvA` embedding) and its data nodes `kD_drd` / `kD_dwr`.  §2 `CI` = `Cert` at
`BInf` over the state `(d, r)`, its kit rules `kC_*` and data nodes `kC_drd` / `kC_dwr` (the
store records the class `wcls ak r`, then clears the flag).  §3 the premises `rd_pre` / `wr_pre`,
the values `ld_res` / `st_bytes` / `gpr_val`, and the top lemmas `EvD_execute_LOAD` /
`EvD_execute_STORE` / `Cert_execute_LOAD` / `Cert_execute_STORE` (applications of
`AxDataX.X_execute_LOAD` / `X_execute_STORE` at the two kits).

## Deviations from Rocq

1. THE KIT IS A STRUCTURE (`AxDataX` deviation 1).  Rocq's `kit_solve` Ltac (which feeds the
   rules one by one into `X_execute_*`) is replaced by the Lean-only bundled kits
   `AxDataX2.evdKit img dok kind : XKit img AxSymMem.Dstate (EvD img dok kind)` and
   `AxDataX2.certKit img dok kind : XKit img (Cdata × Bool) (CI img dok kind)`.  The rules
   `kD*` / `kC*` take their arguments in the order of the `XKit` fields; Rocq's outcome-type
   parameter `E` / `T` is gone (lean-sail failure nodes, `AxDataX` deviation 2).
2. PINS: `seip_reg` ↦ `AxRunClose.pinReg`.  Lean-sail register events carry no access kind.
3. DATA NODES follow the Lean certificates (`AxSymMem` deviations 1–2, `AxCert` deviations 1, 5):
   `kDDrd` / `kCDrd` take `(classify req.access_kind).akIfetch = false` (a data read is never a
   fetch); `kDDwr` / `kCDwr` take the written word `v` with `req.value = some v`, record
   `WeakInterpProj.wbytes n v` and continue at the answer `.Ok (some true)` (Rocq `inl None`).
   `N.to_nat n` ↦ `n`, `pa_z` ↦ `paZ`, `dev_addr` ↦ `devAddr`.
4. `gpr_val rs r` is over the Lean `RegFile` (`uxaXget rs r`; `= t.gpr r` by `rfl`).
   `ld_res` / `st_bytes` are over `Nat` widths: `extend_value u (rrv w vs)` /
   `AxDataX.wrb w (AxDataX.stData w v2)` (`AxDataX` deviations 4–5).  `rd_pre` / `wr_pre` take
   the section variables `dok σ` explicitly first.  The Cert top lemmas take the flag `r`
   before `t s1` (Rocq order) and state the store class as `wcls AxDataX.akPlain r`.
5. AXDATAX INTERFACE FIX (2026-10-07, owner-approved).  The top lemmas instantiate
   `XExecuteLOAD` / `XExecuteSTORE` with `CDrd := kDDrd …` / `kCDrd …` and
   `CDwr := kDDwr …` / `kCDwr …`; this needed `AxDataX`'s data-node section variables to match
   the Lean certificates: `CDrd` now takes `akIfetch = false` and `CDwr` continues at
   `.Ok (some true)` (see `AxDataX` deviation 7).

**Rocq → Lean name map.**  `kD_mono` `kDMono`, `kD_ret` `kDRet`, `kD_bind` `kDBind`,
`kD_try_catch` `kDTryCatch`, `kD_ext` `kDExt`, `kD_rd` `kDRd`, `kD_wr` `kDWr`, `kD_EvA` `kDEvA`,
`kD_drd` `kDDrd`, `kD_dwr` `kDDwr`, `CI` `CI`, `kC_mono` `kCMono`, `kC_ret` `kCRet`, `kC_bind`
`kCBind`, `kC_try_catch` `kCTryCatch`, `kC_ext` `kCExt`, `kC_rd` `kCRd`, `kC_wr` `kCWr`,
`kC_EvA` `kCEvA`, `kC_drd` `kCDrd`, `kC_dwr` `kCDwr`, `rd_pre` `rdPre`, `wr_pre` `wrPre`,
`ld_res` `ldRes`, `st_bytes` `stBytes`, `gpr_val` `gprVal`, `EvD_execute_LOAD` `EvDExecuteLOAD`, `EvD_execute_STORE`
`EvDExecuteSTORE`, `Cert_execute_LOAD` `CertExecuteLOAD`, `Cert_execute_STORE` `CertExecuteSTORE`; Ltac `kit_solve` ↦
`AxDataX2.evdKit` / `AxDataX2.certKit` (Lean-only); Lean-only `AxDataX2.gprValEq`.  None is in the duplicated-name table.

**Dropped:** the Ltac `kit_solve` (deviation 1).
Rocq 6 definitions + 24 lemmas (+1 Ltac); Lean 6 definitions + 24 lemmas + 2 Lean-only kits + 1 Lean-only lemma.
-/
import Weak.AxDataX
import Weak.AxCert

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 1. `EvD` -/

section evd
variable (img : Image) (dok : Int → Nat → Prop) (kind : Bool)

theorem kDMono {X : Type} (QE QE' : AxSymMem.Dstate → Sail.Error exception → ExecSt → Prop)
    (Q Q' : AxSymMem.Dstate → X → ExecSt → Prop) (s : AxSymMem.Dstate) (m : SailM X) (t : ExecSt) :
    (∀ s' e t', QE s' e t' → QE' s' e t') → (∀ s' x t', Q s' x t' → Q' s' x t') →
    EvD img dok kind QE Q s m t → EvD img dok kind QE' Q' s m t :=
  EvDMono img dok kind QE QE' Q Q' s m t

theorem kDRet {X : Type} (QE : AxSymMem.Dstate → Sail.Error exception → ExecSt → Prop)
    (Q : AxSymMem.Dstate → X → ExecSt → Prop) (s : AxSymMem.Dstate) (x : X) (t : ExecSt) :
    Q s x t → EvD img dok kind QE Q s (pure x) t :=
  fun h => .evdRet s x t h

theorem kDBind {X Y : Type} (QE : AxSymMem.Dstate → Sail.Error exception → ExecSt → Prop)
    (Q : AxSymMem.Dstate → Y → ExecSt → Prop) (m : SailM X) (f : X → SailM Y)
    (s : AxSymMem.Dstate) (t : ExecSt) :
    EvD img dok kind QE (fun s' x t' => EvD img dok kind QE Q s' (f x) t') s m t →
    EvD img dok kind QE Q s (m >>= f) t :=
  EvDBind img dok kind QE Q m f s t

theorem kDTryCatch {X : Type} (QE1 QE2 : AxSymMem.Dstate → Sail.Error exception → ExecSt → Prop)
    (Q : AxSymMem.Dstate → X → ExecSt → Prop) (m : SailM X) (h : Sail.Error exception → SailM X)
    (s : AxSymMem.Dstate) (t : ExecSt) :
    (∀ s' e t', QE1 s' e t' → EvD img dok kind QE2 Q s' (h e) t') →
    EvD img dok kind QE1 Q s m t → EvD img dok kind QE2 Q s (PreSail.tryCatchAll m h) t :=
  EvDTryCatch img dok kind QE1 QE2 Q m h s t

theorem kDExt {X : Type} (QE : AxSymMem.Dstate → Sail.Error exception → ExecSt → Prop)
    (Q : AxSymMem.Dstate → X → ExecSt → Prop) (s : AxSymMem.Dstate) (e : Sail.Error exception)
    (k : Empty → SailM X) (t : ExecSt) :
    QE s e t → EvD img dok kind QE Q s (.impure (.error e) k) t :=
  fun h => .evdExt s e k t h

theorem kDRd {X : Type} (QE : AxSymMem.Dstate → Sail.Error exception → ExecSt → Prop)
    (Q : AxSymMem.Dstate → X → ExecSt → Prop) (s : AxSymMem.Dstate) (r : Register)
    (k : RegisterType r → SailM X) (t : ExecSt) :
    ¬ AxRunClose.pinReg r → EvD img dok kind QE Q s (k (t.regs r)) t →
    EvD img dok kind QE Q s (.impure (.ok (.regRead r)) k) t :=
  fun hr h => .evdRd s r k t (fun hp => absurd hp hr) (fun _ => h)

theorem kDWr {X : Type} (QE : AxSymMem.Dstate → Sail.Error exception → ExecSt → Prop)
    (Q : AxSymMem.Dstate → X → ExecSt → Prop) (s : AxSymMem.Dstate) (r : Register)
    (v : RegisterType r) (k : PUnit → SailM X) (t : ExecSt) :
    ¬ AxRunClose.pinReg r → EvD img dok kind QE Q s (k PUnit.unit) (t.setReg r v) →
    EvD img dok kind QE Q s (.impure (.ok (.regWrite r v)) k) t :=
  fun hr h => .evdWr s r v k t hr h

theorem kDEvA {X : Type} (QE0 : Sail.Error exception → ExecSt → Prop) (Q0 : X → ExecSt → Prop)
    (QE : AxSymMem.Dstate → Sail.Error exception → ExecSt → Prop)
    (Q : AxSymMem.Dstate → X → ExecSt → Prop) (s : AxSymMem.Dstate) (m : SailM X) (t : ExecSt) :
    (∀ e t', QE0 e t' → QE s e t') → (∀ x t', Q0 x t' → Q s x t') →
    EvA img QE0 Q0 m t → EvD img dok kind QE Q s m t :=
  EvDOfEvA' img dok kind QE Q QE0 Q0 s m t

theorem kDDrd {X : Type} (QE : AxSymMem.Dstate → Sail.Error exception → ExecSt → Prop)
    (Q : AxSymMem.Dstate → X → ExecSt → Prop) (s : AxSymMem.Dstate) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt) :
    kind = true → s = .DPend → devAddr req.pa = false →
    (classify req.access_kind).akLatest = false → (classify req.access_kind).akIfetch = false →
    dok (paZ req.pa) n →
    (∀ vs : List (BitVec 8), vs.length = n →
      EvD img dok kind QE Q (.DDone vs) (k (.Ok (wordOfBytes n vs, none))) t) →
    EvD img dok kind QE Q s (.impure (.ok (.memRead n va req)) k) t := by
  intro hk hs h1 h2 h3 h4 H
  subst hs
  exact .evdDrd n va req k t hk h1 h2 h3 h4 H

theorem kDDwr {X : Type} (QE : AxSymMem.Dstate → Sail.Error exception → ExecSt → Prop)
    (Q : AxSymMem.Dstate → X → ExecSt → Prop) (s : AxSymMem.Dstate) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k : Result (Option Bool) Arch.abort → SailM X) (t : ExecSt) (v : BitVec (8 * n)) :
    kind = false → s = .DPend → devAddr req.pa = false →
    (classify req.access_kind).akLatest = false → req.value = some v →
    dok (paZ req.pa) n →
    EvD img dok kind QE Q (.DDone (WeakInterpProj.wbytes n v)) (k (.Ok (some true))) t →
    EvD img dok kind QE Q s (.impure (.ok (.memWrite n va req)) k) t := by
  intro hk hs h1 h2 h3 h4 H
  subst hs
  exact .evdDwr n va req k t v hk h1 h2 h3 h4 H

/-- (Lean-only; Rocq `kit_solve`) The `EvD` kit. -/
theorem AxDataX2.evdKit : XKit img AxSymMem.Dstate (EvD img dok kind) where
  cMono := kDMono img dok kind
  cRet := kDRet img dok kind
  cBind := kDBind img dok kind
  cTryCatch := kDTryCatch img dok kind
  cExt := kDExt img dok kind
  cRd := kDRd img dok kind
  cWr := kDWr img dok kind
  cEvA := kDEvA img dok kind

end evd

/-! # 2. `Cert` at `BInf`, state = (data event, release-pending flag) -/

def CI (img : Image) (dok : Int → Nat → Prop) (kind : Dkind) {X : Type}
    (QE : Cdata × Bool → Sail.Error exception → ExecSt → Prop) (Q : Cdata × Bool → X → ExecSt → Prop)
    (s : Cdata × Bool) (m : SailM X) (t : ExecSt) : Prop :=
  AxCert.Cert img dok kind (fun s' e t' => s'.csB = .BInf ∧ QE (s'.csD, s'.csR) e t')
    (fun s' x t' => s'.csB = .BInf ∧ Q (s'.csD, s'.csR) x t') ⟨s.1, .BInf, s.2⟩ m t

section certi
variable (img : Image) (dok : Int → Nat → Prop) (kind : Dkind)

theorem kCMono {X : Type} (QE QE' : Cdata × Bool → Sail.Error exception → ExecSt → Prop)
    (Q Q' : Cdata × Bool → X → ExecSt → Prop) (s : Cdata × Bool) (m : SailM X) (t : ExecSt) :
    (∀ s' e t', QE s' e t' → QE' s' e t') → (∀ s' x t', Q s' x t' → Q' s' x t') →
    CI img dok kind QE Q s m t → CI img dok kind QE' Q' s m t := by
  intro HE HQ H
  refine CertMono img dok kind _ _ _ _ _ m t ?_ ?_ H
  · exact fun _ _ _ ⟨hb, h⟩ => ⟨hb, HE _ _ _ h⟩
  · exact fun _ _ _ ⟨hb, h⟩ => ⟨hb, HQ _ _ _ h⟩

theorem kCRet {X : Type} (QE : Cdata × Bool → Sail.Error exception → ExecSt → Prop)
    (Q : Cdata × Bool → X → ExecSt → Prop) (s : Cdata × Bool) (x : X) (t : ExecSt) :
    Q s x t → CI img dok kind QE Q s (pure x) t := by
  obtain ⟨d, r⟩ := s
  intro H
  exact .cRet _ x t ⟨rfl, H⟩

theorem kCBind {X Y : Type} (QE : Cdata × Bool → Sail.Error exception → ExecSt → Prop)
    (Q : Cdata × Bool → Y → ExecSt → Prop) (m : SailM X) (f : X → SailM Y) (s : Cdata × Bool)
    (t : ExecSt) :
    CI img dok kind QE (fun s' x t' => CI img dok kind QE Q s' (f x) t') s m t →
    CI img dok kind QE Q s (m >>= f) t := by
  intro H
  apply CertBind
  refine CertMono img dok kind _ _ _ _ _ m t (fun _ _ _ h => h) ?_ H
  rintro ⟨d, b, r⟩ x t' ⟨hb, HC⟩
  dsimp only at hb HC
  subst hb
  exact HC

theorem kCTryCatch {X : Type} (QE1 QE2 : Cdata × Bool → Sail.Error exception → ExecSt → Prop)
    (Q : Cdata × Bool → X → ExecSt → Prop) (m : SailM X) (h : Sail.Error exception → SailM X)
    (s : Cdata × Bool) (t : ExecSt) :
    (∀ s' e t', QE1 s' e t' → CI img dok kind QE2 Q s' (h e) t') →
    CI img dok kind QE1 Q s m t → CI img dok kind QE2 Q s (PreSail.tryCatchAll m h) t := by
  intro Hh H
  refine CertTryCatch img dok kind _ _ _ m h _ t ?_ H
  rintro ⟨d, b, r⟩ e t' ⟨hb, HE⟩
  dsimp only at hb HE
  subst hb
  exact Hh (d, r) e t' HE

theorem kCExt {X : Type} (QE : Cdata × Bool → Sail.Error exception → ExecSt → Prop)
    (Q : Cdata × Bool → X → ExecSt → Prop) (s : Cdata × Bool) (e : Sail.Error exception)
    (k : Empty → SailM X) (t : ExecSt) :
    QE s e t → CI img dok kind QE Q s (.impure (.error e) k) t := by
  obtain ⟨d, r⟩ := s
  intro H
  exact .cExt _ e k t ⟨rfl, H⟩

theorem kCRd {X : Type} (QE : Cdata × Bool → Sail.Error exception → ExecSt → Prop)
    (Q : Cdata × Bool → X → ExecSt → Prop) (s : Cdata × Bool) (r : Register)
    (k : RegisterType r → SailM X) (t : ExecSt) :
    ¬ AxRunClose.pinReg r → CI img dok kind QE Q s (k (t.regs r)) t →
    CI img dok kind QE Q s (.impure (.ok (.regRead r)) k) t :=
  fun hr H => .cRd _ r k t (fun hp => absurd hp hr) (fun _ => H)

theorem kCWr {X : Type} (QE : Cdata × Bool → Sail.Error exception → ExecSt → Prop)
    (Q : Cdata × Bool → X → ExecSt → Prop) (s : Cdata × Bool) (r : Register) (v : RegisterType r)
    (k : PUnit → SailM X) (t : ExecSt) :
    ¬ AxRunClose.pinReg r → CI img dok kind QE Q s (k PUnit.unit) (t.setReg r v) →
    CI img dok kind QE Q s (.impure (.ok (.regWrite r v)) k) t :=
  fun hr H => .cWr _ r v k t hr H

theorem kCEvA {X : Type} (QE0 : Sail.Error exception → ExecSt → Prop) (Q0 : X → ExecSt → Prop)
    (QE : Cdata × Bool → Sail.Error exception → ExecSt → Prop)
    (Q : Cdata × Bool → X → ExecSt → Prop) (s : Cdata × Bool) (m : SailM X) (t : ExecSt) :
    (∀ e t', QE0 e t' → QE s e t') → (∀ x t', Q0 x t' → Q s x t') →
    EvA img QE0 Q0 m t → CI img dok kind QE Q s m t := by
  obtain ⟨d, r⟩ := s
  intro HE HQ H
  refine CertMono img dok kind _ _ _ _ _ m t ?_ ?_ (CertOfEvA img dok kind QE0 Q0 d r m t H)
  · rintro _ e t' ⟨rfl, h⟩
    exact ⟨rfl, HE e t' h⟩
  · rintro _ x t' ⟨rfl, h⟩
    exact ⟨rfl, HQ x t' h⟩

theorem kCDrd {X : Type} (QE : Cdata × Bool → Sail.Error exception → ExecSt → Prop)
    (Q : Cdata × Bool → X → ExecSt → Prop) (s : Cdata × Bool) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt) :
    kind = .DKLd → s.1 = .CPend → devAddr req.pa = false →
    (classify req.access_kind).akLatest = false → (classify req.access_kind).akIfetch = false →
    dok (paZ req.pa) n →
    (∀ vs : List (BitVec 8), vs.length = n →
      CI img dok kind QE Q (.CLd vs, s.2) (k (.Ok (wordOfBytes n vs, none))) t) →
    CI img dok kind QE Q s (.impure (.ok (.memRead n va req)) k) t := by
  obtain ⟨d, r⟩ := s
  intro hk hd h1 h2 h3 h4 H
  dsimp only at hd
  subst hd
  exact .cDrd .BInf r n va req k t hk h1 h2 h3 h4 H

theorem kCDwr {X : Type} (QE : Cdata × Bool → Sail.Error exception → ExecSt → Prop)
    (Q : Cdata × Bool → X → ExecSt → Prop) (s : Cdata × Bool) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k : Result (Option Bool) Arch.abort → SailM X) (t : ExecSt) (v : BitVec (8 * n)) :
    kind = .DKSt → s.1 = .CPend → devAddr req.pa = false →
    (classify req.access_kind).akLatest = false → req.value = some v →
    dok (paZ req.pa) n →
    CI img dok kind QE Q (.CSt (WeakInterpProj.wbytes n v) (wcls req.access_kind s.2), false)
      (k (.Ok (some true))) t →
    CI img dok kind QE Q s (.impure (.ok (.memWrite n va req)) k) t := by
  obtain ⟨d, r⟩ := s
  intro hk hd h1 h2 h3 h4 H
  dsimp only at hd
  subst hd
  exact .cDwr .BInf r n va req k t v hk h1 h2 h3 h4 H

/-- (Lean-only; Rocq `kit_solve`) The `Cert`-at-`BInf` kit. -/
theorem AxDataX2.certKit : XKit img (Cdata × Bool) (CI img dok kind) where
  cMono := kCMono img dok kind
  cRet := kCRet img dok kind
  cBind := kCBind img dok kind
  cTryCatch := kCTryCatch img dok kind
  cExt := kCExt img dok kind
  cRd := kCRd img dok kind
  cWr := kCWr img dok kind
  cEvA := kCEvA img dok kind

end certi

/-! # 3. The top lemmas' vocabulary -/

/-- The premises of a `Load Data` data read (Rocq section variables `dok σ` explicit). -/
def rdPre (dok : Int → Nat → Prop) (σ : ExecSt) (imm : BitVec 12) (rs1 : BitVec 5) (w : Nat)
    (va pa : BitVec 64) (md : SATPMode) (t s1 : ExecSt) : Prop :=
  w ≤ 8 ∧
  execA (get_transformed_data_addr (.Regidx rs1) (sign_extend (m := 64) imm) (.Load .Data) w)
    (tσ σ t) = some (.Ext_DataAddr_OK (.Virtaddr va), tσ σ t) ∧
  vmemWidth w ∧ is_aligned_vaddr (.Virtaddr va) w = true ∧
  execA (effectivePrivilege (.Load .Data) (t.regs .mstatus) (t.regs .cur_privilege)) (tσ σ t)
    = some (.Supervisor, tσ σ t) ∧
  execA (translationMode .Supervisor) (tσ σ t) = some (md, tσ σ t) ∧
  execA (translateAddr (.Virtaddr va) (.Load .Data)) (tσ σ t)
    = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1) ∧
  rdFacts σ (.Load .Data) .PBMT_PMA w pa ⟨s1.regs, t.mem, t.dev⟩ ∧
  devAddr pa = false ∧ dok (paZ pa) w

/-- The premises of a `Store Data` data write. -/
def wrPre (dok : Int → Nat → Prop) (σ : ExecSt) (imm : BitVec 12) (rs1 : BitVec 5) (w : Nat)
    (va pa : BitVec 64) (md : SATPMode) (t s1 : ExecSt) : Prop :=
  w ≤ 8 ∧
  execA (get_transformed_data_addr (.Regidx rs1) (sign_extend (m := 64) imm) (.Store .Data) w)
    (tσ σ t) = some (.Ext_DataAddr_OK (.Virtaddr va), tσ σ t) ∧
  vmemWidth w ∧ is_aligned_vaddr (.Virtaddr va) w = true ∧
  execA (effectivePrivilege (.Store .Data) (t.regs .mstatus) (t.regs .cur_privilege)) (tσ σ t)
    = some (.Supervisor, tσ σ t) ∧
  execA (translationMode .Supervisor) (tσ σ t) = some (md, tσ σ t) ∧
  execA (translateAddr (.Virtaddr va) (.Store .Data)) (tσ σ t)
    = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1) ∧
  wrFacts σ (.Store .Data) .PBMT_PMA w pa ⟨s1.regs, t.mem, t.dev⟩ ∧
  devAddr pa = false ∧ dok (paZ pa) w

/-- The GPR value a load writes. -/
def ldRes (u : Bool) (w : Nat) (vs : List (BitVec 8)) : BitVec 64 := extend_value u (rrv w vs)

/-- The bytes a `w`-byte store of the source value `v2` writes. -/
def stBytes (w : Nat) (v2 : BitVec 64) : List (BitVec 8) := AxDataX.wrb w (AxDataX.stData w v2)

/-- The source value of a GPR (`x0` reads zero). -/
def gprVal (rs : RegFile) (r : BitVec 5) : BitVec 64 := uxaXget rs r

theorem AxDataX2.gprValEq (t : ExecSt) (r : BitVec 5) : gprVal t.regs r = t.gpr r := rfl

section top
variable (img : Image) (dok : Int → Nat → Prop) (σ : ExecSt) (himg : img = imgOf σ)
include himg

theorem EvDExecuteLOAD (imm : BitVec 12) (rs1 rd : BitVec 5) (u : Bool) (w : Nat)
    (va pa : BitVec 64) (md : SATPMode) (Q : AxSymMem.Dstate → ExecutionResult → ExecSt → Prop)
    (t s1 : ExecSt) :
    rd.toNat ≠ 0 → rdPre dok σ imm rs1 w va pa md t s1 →
    (∀ vs : List (BitVec 8), vs.length = w →
      Q (.DDone vs) RETIRE_SUCCESS ((⟨s1.regs, t.mem, t.dev⟩ : ExecSt).setGpr rd (ldRes u w vs))) →
    EvD img dok true (fun _ _ _ => False) Q .DPend
      (execute (.LOAD (imm, .Regidx rs1, .Regidx rd, u, w))) t := by
  rintro hrd ⟨hw8, hgta, hw, hal, heff, htm, htr, hrf, hdev, hdok⟩ hq
  exact XExecuteLOAD (AxDataX2.evdKit img dok true) (fun d => d = .DPend) (fun _ vs => .DDone vs)
    (@fun _ QE Q0 s n va req k t hp h1 h2 h3 h4 H =>
      kDDrd img dok true QE Q0 s n va req k t rfl hp h1 h2 h3 h4 H)
    σ himg imm rs1 rd u w va pa md Q .DPend t s1 hw8 hrd hgta hw hal heff htm htr hrf rfl hdev hdok hq

theorem EvDExecuteSTORE (imm : BitVec 12) (rs2 rs1 : BitVec 5) (w : Nat) (va pa : BitVec 64)
    (md : SATPMode) (Q : AxSymMem.Dstate → ExecutionResult → ExecSt → Prop) (t s1 : ExecSt) :
    wrPre dok σ imm rs1 w va pa md t s1 →
    Q (.DDone (stBytes w (gprVal t.regs rs2))) RETIRE_SUCCESS ⟨s1.regs, t.mem, t.dev⟩ →
    EvD img dok false (fun _ _ _ => False) Q .DPend
      (execute (.STORE (imm, .Regidx rs2, .Regidx rs1, w))) t := by
  rintro ⟨hw8, hgta, hw, hal, heff, htm, htr, hwf, hdev, hdok⟩ hq
  exact XExecuteSTORE (AxDataX2.evdKit img dok false) (fun d => d = .DPend)
    (fun _ vs _ => .DDone vs)
    (@fun _ QE Q0 s n va req k t v hp h1 h2 h3 h4 H =>
      kDDwr img dok false QE Q0 s n va req k t v rfl hp h1 h2 h4 h3 H)
    σ himg imm rs2 rs1 w va pa md Q .DPend t s1 hw8 hgta hw hal heff htm htr hwf rfl hdev hdok hq

theorem CertExecuteLOAD (imm : BitVec 12) (rs1 rd : BitVec 5) (u : Bool) (w : Nat)
    (va pa : BitVec 64) (md : SATPMode) (Q : Cst → ExecutionResult → ExecSt → Prop) (r : Bool)
    (t s1 : ExecSt) :
    rd.toNat ≠ 0 → rdPre dok σ imm rs1 w va pa md t s1 →
    (∀ vs : List (BitVec 8), vs.length = w →
      Q ⟨.CLd vs, .BInf, r⟩ RETIRE_SUCCESS
        ((⟨s1.regs, t.mem, t.dev⟩ : ExecSt).setGpr rd (ldRes u w vs))) →
    AxCert.Cert img dok .DKLd (fun _ _ _ => False) Q ⟨.CPend, .BInf, r⟩
      (execute (.LOAD (imm, .Regidx rs1, .Regidx rd, u, w))) t := by
  rintro hrd ⟨hw8, hgta, hw, hal, heff, htm, htr, hrf, hdev, hdok⟩ hq
  have H := XExecuteLOAD (AxDataX2.certKit img dok .DKLd) (fun s => s.1 = .CPend)
    (fun s vs => (.CLd vs, s.2))
    (@fun _ QE Q0 s n va req k t hp h1 h2 h3 h4 H =>
      kCDrd img dok .DKLd QE Q0 s n va req k t rfl hp h1 h2 h3 h4 H)
    σ himg imm rs1 rd u w va pa md (fun s x t' => Q ⟨s.1, .BInf, s.2⟩ x t') (.CPend, r) t s1
    hw8 hrd hgta hw hal heff htm htr hrf rfl hdev hdok hq
  refine CertMono img dok .DKLd _ _ _ _ _ _ t (fun _ _ _ h => h.2.elim) ?_ H
  rintro ⟨d, b, r'⟩ x t' ⟨hb, HQ⟩
  dsimp only at hb HQ
  subst hb
  exact HQ

theorem CertExecuteSTORE (imm : BitVec 12) (rs2 rs1 : BitVec 5) (w : Nat) (va pa : BitVec 64)
    (md : SATPMode) (Q : Cst → ExecutionResult → ExecSt → Prop) (r : Bool) (t s1 : ExecSt) :
    wrPre dok σ imm rs1 w va pa md t s1 →
    Q ⟨.CSt (stBytes w (gprVal t.regs rs2)) (wcls AxDataX.akPlain r), .BInf, false⟩ RETIRE_SUCCESS
      ⟨s1.regs, t.mem, t.dev⟩ →
    AxCert.Cert img dok .DKSt (fun _ _ _ => False) Q ⟨.CPend, .BInf, r⟩
      (execute (.STORE (imm, .Regidx rs2, .Regidx rs1, w))) t := by
  rintro ⟨hw8, hgta, hw, hal, heff, htm, htr, hwf, hdev, hdok⟩ hq
  have H := XExecuteSTORE (AxDataX2.certKit img dok .DKSt) (fun s => s.1 = .CPend)
    (fun s vs ak => (.CSt vs (wcls ak s.2), false))
    (@fun _ QE Q0 s n va req k t v hp h1 h2 h3 h4 H =>
      kCDwr img dok .DKSt QE Q0 s n va req k t v rfl hp h1 h2 h4 h3 H)
    σ himg imm rs2 rs1 w va pa md (fun s x t' => Q ⟨s.1, .BInf, s.2⟩ x t') (.CPend, r) t s1
    hw8 hgta hw hal heff htm htr hwf rfl hdev hdok hq
  refine CertMono img dok .DKSt _ _ _ _ _ _ t (fun _ _ _ h => h.2.elim) ?_ H
  rintro ⟨d, b, r'⟩ x t' ⟨hb, HQ⟩
  dsimp only at hb HQ
  subst hb
  exact HQ

end top

end Weak
