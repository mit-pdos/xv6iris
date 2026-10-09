/-
Weak: **W5c — M1's premise set is SATISFIABLE** (plan `notes/weak-allocproc-plan.md` §C Stage 0,
"W5c"; D22).

Lean-only (no Rocq source).

## What this file proves

`srvwmoXv6M1Satisfiable`: there is a booted weak state `σ0` (`wbootFacts`, generation 0, the
disk `fsImgDisk` under a device reset), a candidate `c`, program states `pst` and a fabric `dv`
satisfying EVERY premise of M1 (`srvwmoXv6M1Premises`): `srvwmoConsistent c`, the boot image,
`pst 0 = epsInit σ0`, `dv 0 = efInit σ0.wgdev`, the SHAPED conformance `execProgOk'S` at the
boot-image-pinned LTS `pstepPin (imgZ σ0.wgimg) pstepEv` with M1's fetch clause
`candKfetch bcRoLo bcRoHi`, and `candSca c` — with a NONEMPTY trace.  The witness is hypothesis
free.

THE BLOCK.  `_entry`'s FIRST memory instruction, `ld sp,1000(sp)` at `0x80000004`
(`Xv6/KernelImage.lean`, `textChunk0`), on hart 0 alone, from the boot landing file
(`bootLand ⟨0, _⟩ WeakEvStarted.regs0`, PC `0x80000000`).  The trace is ONE axiomatic label: the
plain 8-byte load of the GOT word at `0x8000a3e8`, every byte read from the image (timestamp 0),
value `0x8000a420`.  The administrative run in front of it is BUILT BY KERNEL EVALUATION, not
written down: `LInstr`, a silent stretch (106 nodes), the fetch of `auipc sp,0xa` (4 bytes at
`0x80000000`), a silent stretch (16 nodes) to the instruction's `Ret`, `LInstr`, a silent stretch
(106 nodes), the fetch of `ld sp,1000(sp)` (4 bytes at `0x80000004`), a silent stretch (96
nodes) to the data load node.  Both fetches answer the boot image at timestamp 0 (the pin) and
lie in W3's pristine window `[bcRoLo, bcRoHi)` (the fetch clause).

THE MISSING MECHANISM, SUPPLIED (`Weak/WeakRvwmoConfWit2.lean` §6's verdict): the `esil → admRun`
BRIDGE `esilAdmRun` — a computed silent stretch `esil n D x` (`WeakEvLift`) is a label-carrying
administrative run `admRunG (pstepPin img pstepEv) true` of the hart, fetch-free, provided the
stretch crosses no SFENCE.VMA announce (`SrvwmoXv6Witness.esilNoSf`, a computable check: such an
announce is the marker `LFence false false false false`, not administrative).

THE S-VARIANT OF `execProgOk'Snoc` (`Weak/WeakRvwmoCert.lean`): `execProgOk'SSnoc` extends
`execProgOk'S` (W5b, `Weak/PfRunShape.lean`) by one realized, fused (`lbFused`) block whose
leading star satisfies the fetch clause and whose plain load is single-copy atomic.

CONSISTENCY via `snocReadConsistent` (`snocRdAdm`, `Cert.lean`): the image bytes at
timestamp 0 over the empty log.  `candSca c` is `execProgOk'SSca` of the shaped premise.

SCOPE.  Certifies satisfiability ONLY.  QUIESCENT: the fabric never moves (`dv` is constant,
`efInit σ0.wgdev`; no `LDev` label); the run does not reach `allocproc` (D44), and says nothing
about W13's bundle.  `srvwmoXv6M1PfRun` checks the premise set FEEDS W5b's replay
(`execWfPfRunPinShaped`): every M1 premise set yields the shaped pf run.

## Measurements (kernel, `decide +kernel`)

Footprint `SrvwmoXv6Witness.dEntry`: 22 registers (the deduplicated collector readback of the
four stretches).  Node counts 106 / 16 / 106 / 96.  Image words: `0x0000a117` (`auipc`),
`0x3e813103` (`ld`); GOT bytes `20 a4 00 80 00 00 00 00`.

**Name map.**  None (Lean-only).  Main declarations: `esilAdmRun`, `execProgOk'SSnoc`,
`execProgOk'SNil`, `srvwmoXv6M1Premises`, `srvwmoXv6M1Satisfiable`, `srvwmoXv6M1PfRun`;
helpers file-qualified `SrvwmoXv6Witness.*`.
-/
import Weak.PfRunShape
import Weak.WeakRvwmoConfWit2
import Weak.WeakRvwmoCert
import Weak.WeakEvCapstone
import Xv6.BootCarve
import Xv6.FsImgDisk
import MachCSL.DiskOf

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D

/-! ## 1. THE `esil → admRun` BRIDGE -/

/-- A node that is not an SFENCE.VMA announce (whose label is the marker fence, not admin). -/
def SrvwmoXv6Witness.enodeNoSf (m : SailM Unit) : Bool :=
  match m with
  | .impure (.ok (.instrAnnounce n w)) _ => !sfAnnB n w
  | _ => true

/-- The stretch `esil n D` crosses no SFENCE.VMA announce (computable, mirrors `erunSilent`). -/
def SrvwmoXv6Witness.esilNoSf : Nat → List Register → RegFile → SailM Unit → Bool
  | 0, _, _, _ => true
  | n + 1, D, rs, m =>
    match esilNode D rs m with
    | some (rs', m') => SrvwmoXv6Witness.enodeNoSf m && SrvwmoXv6Witness.esilNoSf n D rs' m'
    | none => true

/-- A hart node step with no parked fence and an untouched fabric. -/
theorem SrvwmoXv6Witness.pstepEvNode (c : CPU) (m m' : SailM Unit) (rs rs' : RegFile)
    (ib ib' : Ibch) (d : Efab) (l : Wlabel) (ors : Option RegFile) (oib : Option Ibch) :
    pnodeStep m rs ib d.efDev l m' ors none d.efDev oib none →
    rs' = ors.getD rs → ib' = oib.getD ib →
    pstepEv (.PHart c m rs none ib) d l (.PHart c m' rs' none ib') d := by
  intro h hrs hib
  exact ⟨rfl, ors, oib, none, hrs, hib, Or.inl ⟨h, rfl⟩⟩

theorem SrvwmoXv6Witness.erwLabelAdm (k : ErwKind) :
    lbAdmin true (erwLabel k) ∧ ∀ base tvs, erwLabel k ≠ .LIFetch base tvs := by
  cases k <;> simp [erwLabel, lbAdmin]

/-- ONE SILENT NODE IS ONE ADMINISTRATIVE, FETCH-FREE HART STEP. -/
theorem SrvwmoXv6Witness.esilNodePstep (c : CPU) (D : List Register) (rs rs' : RegFile)
    (m m' : SailM Unit) (ib : Ibch) (d : Efab) :
    esilNode D rs m = some (rs', m') → SrvwmoXv6Witness.enodeNoSf m = true →
    ∃ (l : Wlabel) (ib' : Ibch), lbAdmin true l ∧ (∀ base tvs, l ≠ .LIFetch base tvs) ∧
      pstepEv (.PHart c m rs none ib) d l (.PHart c m' rs' none ib') d := by
  intro h hsf
  match m, h, hsf with
  | .pure _, h, _ => simp [esilNode] at h
  | .impure (.error _) _, h, _ => simp [esilNode] at h
  | .impure (.ok o) k, h, hsf =>
    cases o
    case regRead r =>
      simp only [esilNode] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨.LSilent, ibRd ib r, trivial, (fun _ _ h => nomatch h),
          SrvwmoXv6Witness.pstepEvNode c _ _ rs rs ib _ d _ none (some (ibRd ib r))
            (by simp [pnodeStep]) rfl rfl⟩
      · simp at h
    case regWrite r v =>
      simp only [esilNode] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ha, hf⟩ := SrvwmoXv6Witness.erwLabelAdm (erwOf (depsOfIb ib.ibBits) ib.ibRds r)
        exact ⟨_, ib, ha, hf,
          SrvwmoXv6Witness.pstepEvNode c _ _ rs _ ib ib d _ (some (rs.set r v)) none
            (by simp [pnodeStep]) rfl rfl⟩
      · simp at h
    case instrAnnounce n w =>
      simp only [esilNode, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hs : sfAnnB n w = false := by
        simpa [SrvwmoXv6Witness.enodeNoSf] using hsf
      refine ⟨annLabel n w, ibAnn (ibOfBvn w), (by rw [annLabelNot hs]; trivial),
        (by rw [annLabelNot hs]; exact (fun _ _ h => nomatch h)),
        SrvwmoXv6Witness.pstepEvNode c _ _ rs rs ib _ d _ none (some (ibAnn (ibOfBvn w)))
          (by simp [pnodeStep]) rfl rfl⟩
    all_goals first
      | (simp only [esilNode, Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl⟩ := h
         exact ⟨.LSilent, ib, trivial, (fun _ _ h => nomatch h),
           SrvwmoXv6Witness.pstepEvNode c _ _ rs rs ib ib d _ none none
             (by simp [pnodeStep]) rfl rfl⟩)
      | (simp [esilNode] at h)

/-- A non-fetch label is pinned to every image. -/
theorem SrvwmoXv6Witness.fetchPinNf (img : Image) (l : Wlabel) :
    (∀ base tvs, l ≠ .LIFetch base tvs) → WeakAxRealize.fetchPin img l := by
  intro h
  cases l <;> first | trivial | exact absurd rfl (h _ _)

/-- **THE BRIDGE**: a computed silent stretch `esil n D` of a hart is a label-carrying,
fetch-free administrative run of the PINNED program LTS (any image), provided it crosses no
SFENCE.VMA announce. -/
theorem esilAdmRun (img : Image) (c : CPU) (D : List Register) :
    ∀ (n : Nat) (rs : RegFile) (m : SailM Unit) (ib : Ibch) (d : Efab),
      SrvwmoXv6Witness.esilNoSf n D rs m = true →
      ∃ (ls : List Wlabel) (ib' : Ibch),
        admRunG (pstepPin img pstepEv) true (.PHart c m rs none ib) d ls
          (.PHart c (esil n D (rs, m)).2 (esil n D (rs, m)).1 none ib') d ∧
        ∀ l, l ∈ ls → ∀ base tvs, l ≠ .LIFetch base tvs := by
  intro n
  induction n with
  | zero =>
    intro rs m ib d _
    exact ⟨[], ib, .nil _ _, by simp⟩
  | succ n ih =>
    intro rs m ib d hsf
    cases hn : esilNode D rs m with
    | none =>
      have he : esil (n + 1) D (rs, m) = (rs, m) := by
        simp only [esil, erunSilent, hn]
      rw [he]
      exact ⟨[], ib, .nil _ _, by simp⟩
    | some p =>
      obtain ⟨rs1, m1⟩ := p
      have he : esil (n + 1) D (rs, m) = esil n D (rs1, m1) := by
        simp only [esil, erunSilent, hn]
      have hsf' : SrvwmoXv6Witness.enodeNoSf m = true ∧
          SrvwmoXv6Witness.esilNoSf n D rs1 m1 = true := by
        simp only [SrvwmoXv6Witness.esilNoSf, hn, Bool.and_eq_true] at hsf
        exact hsf
      obtain ⟨l, ib1, ha, hnf, hs⟩ :=
        SrvwmoXv6Witness.esilNodePstep c D rs rs1 m m1 ib d hn hsf'.1
      obtain ⟨ls, ib', hrun, hnfs⟩ := ih rs1 m1 ib1 d hsf'.2
      rw [he]
      refine ⟨l :: ls, ib', .cons _ _ _ _ _ _ _ _ ha
        ⟨hs, SrvwmoXv6Witness.fetchPinNf img l hnf⟩ hrun, ?_⟩
      intro l' hl'
      rcases List.mem_cons.1 hl' with rfl | hl'
      · exact hnf
      · exact hnfs l' hl'

/-- Concatenation of label-carrying administrative runs. -/
theorem SrvwmoXv6Witness.admRunGApp {P D : Type} {pstep : P → D → Wlabel → P → D → Prop}
    {instr : Bool} {p : P} {d : D} {ls1 : List Wlabel} {p1 : P} {d1 : D} {ls2 : List Wlabel}
    {p2 : P} {d2 : D} :
    admRunG pstep instr p d ls1 p1 d1 → admRunG pstep instr p1 d1 ls2 p2 d2 →
    admRunG pstep instr p d (ls1 ++ ls2) p2 d2 := by
  intro h1
  induction h1 with
  | nil => exact id
  | cons p d l p1' d1' ls p' d' ha hs _ ih =>
    intro h2
    exact .cons _ _ _ _ _ _ _ _ ha hs (ih h2)

/-- The instruction boundary: `LInstr`, into `riscvStep false`, the bits cleared. -/
theorem SrvwmoXv6Witness.boundaryPstep (c : CPU) (u : Unit) (rs : RegFile) (ib : Ibch)
    (d : Efab) :
    pstepEv (.PHart c (FreeM.pure u) rs none ib) d .LInstr
      (.PHart c (riscvStep false) rs none ibNone) d :=
  SrvwmoXv6Witness.pstepEvNode c _ _ rs rs ib _ d _ none (some ibNone)
    ⟨false, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl

/-- The fetch node: an `LIFetch` of the request's footprint, any answered word. -/
theorem SrvwmoXv6Witness.fetchPstep (c : CPU) (n : Nat) (m : SailM Unit)
    (req : Mem_read_request n 64 Arch.pa Arch.translation Arch.arch_ak) (rs : RegFile)
    (ib : Ibch) (d : Efab) (w : BitVec (8 * n)) (tvs : List (Nat × BitVec 8)) :
    ereadReqAt n 64 m = some req → devAddr req.pa = false →
    (classify req.access_kind).akIfetch = true →
    tvs.length = n → (∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w j)) →
    pstepEv (.PHart c m rs none ib) d (.LIFetch (paZ req.pa) tvs)
      (.PHart c (ereadResume w.toNat m) rs none ib) d := by
  intro hreq hdev hif hlen hby
  obtain ⟨K, Hm, Hres⟩ := ereadReqAtInv n 64 m req hreq
  rw [Hres w]
  subst Hm
  refine SrvwmoXv6Witness.pstepEvNode c _ _ rs rs ib ib d _ none none ?_ rfl rfl
  simp only [pnodeStep, hdev, Bool.false_eq_true, if_false]
  refine Or.inl ⟨hif, w, tvs, hlen, hby, ?_⟩
  simp

/-- The plain data-load node: an `LLoad` (no aq, no lat, no address sources). -/
theorem SrvwmoXv6Witness.loadPstep (c : CPU) (n : Nat) (m : SailM Unit)
    (req : Mem_read_request n 64 Arch.pa Arch.translation Arch.arch_ak) (rs : RegFile)
    (ib : Ibch) (d : Efab) (w : BitVec (8 * n)) (tvs : List (Nat × BitVec 8)) :
    ereadReqAt n 64 m = some req → devAddr req.pa = false →
    classify req.access_kind = ⟨false, false, false⟩ →
    tvs.length = n → (∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w j)) →
    pstepEv (.PHart c m rs none ib) d (.LLoad false false (paZ req.pa) tvs [])
      (.PHart c (ereadResume w.toNat m) rs none ib) d := by
  intro hreq hdev hk hlen hby
  obtain ⟨K, Hm, Hres⟩ := ereadReqAtInv n 64 m req hreq
  rw [Hres w]
  subst Hm
  refine SrvwmoXv6Witness.pstepEvNode c _ _ rs rs ib ib d _ none none ?_ rfl rfl
  simp only [pnodeStep, hdev, Bool.false_eq_true, if_false]
  refine Or.inr ⟨by rw [hk], Or.inl ⟨by rw [hk], w, tvs, hlen, hby, ?_⟩⟩
  simp [hk]

/-! ## 2. THE S-VARIANT OF `execProgOk'Snoc` -/

section snocS

variable (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)

/-- The empty candidate is shaped-conformant, vacuously. -/
theorem execProgOk'SNil (img : Image) (pst : Nat → List Pexv6) (dv : Nat → Efab) :
    execProgOk'S (pstepPin img pstepEv) pclsEv fok pst dv (candExec ⟨img, []⟩) := by
  intro k s hs
  simp [candExec] at hs

/-- **THE S-VARIANT OF `execProgOk'Snoc`** (the `HEone` block shape): one more realized, FUSED
step, its leading star label-carrying and satisfying the fetch clause, its plain load
single-copy atomic at the candidate's last state. -/
theorem execProgOk'SSnoc (c : Cand) (i : Nat) (p pa : Pexv6) (da : Efab) (ls : List Wlabel)
    (l : Wlabel) (lb : Lbl) (p' : Pexv6) (d' : Efab) (pst : Nat → List Pexv6)
    (dv : Nat → Efab) :
    execProgOk'S (pstepPin c.cdImg pstepEv) pclsEv fok pst dv (candExec c) →
    (pst (cdEnd c))[i]? = some p →
    admRunG (pstepPin c.cdImg pstepEv) true p (dv (cdEnd c)) ls pa da →
    fetchesOk fok (candLastSt c) i ls →
    (∀ (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)),
       lb = .LLoad aq base ts vs →
       scaOk (candLastSt c).msImg (candLastSt c).msLog i base ts) →
    lbFused l →
    hlblRealizes pa ((candLastSt c).msWs i) lb l →
    pstepEv pa da l p' d' →
    execProgOk'S (pstepPin c.cdImg pstepEv) pclsEv fok (pstSnoc c pst i p') (dvSnoc c dv d')
      (candExec (candSnoc c ⟨i, lb⟩)) := by
  intro hpo hp hrun hfetch hsca hfu hre hst k s hs
  change (c.cdTr ++ [⟨i, lb⟩])[k]? = some s at hs
  have hlt := lookup_lt_Some hs
  simp only [List.length_append, List.length_singleton] at hlt
  by_cases hk : k < cdEnd c
  · have hs' : c.cdTr[k]? = some s := by
      rw [← candSnocTrLt c ⟨i, lb⟩ k hk]; exact hs
    obtain ⟨hsc, q, qa, qd, q', qls, h1, h2, h3, h4, h5⟩ := hpo k s hs'
    rw [candSnocStt c _ k (by omega)]
    refine ⟨hsc, q, qa, qd, q', qls, ?_⟩
    rw [pstSnocLe c pst i p' k (by omega), pstSnocLe c pst i p' (k + 1) (by omega),
      dvSnocLe c dv d' k (by omega), dvSnocLe c dv d' (k + 1) (by omega)]
    exact ⟨h1, h2, h3, h4, h5⟩
  · have : k = cdEnd c := by unfold cdEnd at hk ⊢; omega
    subst this
    have hs2 := candSnocTrEnd c ⟨i, lb⟩
    change (c.cdTr ++ [⟨i, lb⟩])[cdEnd c]? = some ⟨i, lb⟩ at hs2
    rw [hs2, Option.some.injEq] at hs
    subst hs
    rw [candSnocLastSt]
    refine ⟨hsca, p, pa, da, p', ls, ?_⟩
    rw [pstSnocLe c pst i p' (cdEnd c) (Nat.le_refl _),
      pstSnocGt c pst i p' (cdEnd c + 1) (by omega),
      dvSnocLe c dv d' (cdEnd c) (Nat.le_refl _), dvSnocGt c dv d' (cdEnd c + 1) (by omega)]
    exact ⟨hp, rfl, hrun, hfetch,
      Or.inl ⟨l, hfu, (hlblRealizesAx _ _ _ _ _).2 hre,
        hst, WeakRvwmoCert.hlblRealizesPin _ _ _ _ _ hre⟩⟩

end snocS

/-! ## 3. THE CONCRETE BLOCK: `_entry`, by kernel evaluation -/

/-- Hart 0's boot landing file (PC `0x80000000`, `_entry`). -/
def SrvwmoXv6Witness.rs0 : RegFile := bootLand ⟨0, by decide⟩ WeakEvStarted.regs0

theorem SrvwmoXv6Witness.rs0Pc : (SrvwmoXv6Witness.rs0 .PC).toNat = 0x80000000 := by
  decide +kernel

/-- THE FOOTPRINT of the four stretches (the collector readback, deduplicated). -/
def SrvwmoXv6Witness.dEntry : List Register :=
  [.cur_privilege, .mcountinhibit, .minstretcfg, .minstret_increment, .hart_state, .misa,
   .mideleg, .mip, .sig_meip, .sig_seip, .mie, .mstatus, .PC, .pma_regions, .pmpcfg_n,
   .pmpaddr_n, .htif_tohost_base, .mseccfg, .elp, .nextPC, .x2, .minstret]

/-- The two fetched windows: `auipc sp,0xa` and `ld sp,1000(sp)`. -/
def SrvwmoXv6Witness.wf1 : BitVec 32 := BitVec.ofNat 32 0x0000a117
def SrvwmoXv6Witness.wf2 : BitVec 32 := BitVec.ofNat 32 0x3e813103
/-- The GOT word the load reads (`stack0`). -/
def SrvwmoXv6Witness.wl : BitVec 64 := BitVec.ofNat 64 0x8000a420

/-- THE CURSORS, unevaluated compositions. -/
noncomputable def SrvwmoXv6Witness.x0 : ecur := (SrvwmoXv6Witness.rs0, riscvStep false)
noncomputable def SrvwmoXv6Witness.x1 : ecur :=
  esil 600 SrvwmoXv6Witness.dEntry SrvwmoXv6Witness.x0
noncomputable def SrvwmoXv6Witness.x2 : ecur :=
  esil 600 SrvwmoXv6Witness.dEntry (ecurRead SrvwmoXv6Witness.wf1.toNat SrvwmoXv6Witness.x1)
noncomputable def SrvwmoXv6Witness.x3 : ecur :=
  esil 600 SrvwmoXv6Witness.dEntry (ecurLoop false SrvwmoXv6Witness.x2)
noncomputable def SrvwmoXv6Witness.x4 : ecur :=
  esil 600 SrvwmoXv6Witness.dEntry (ecurRead SrvwmoXv6Witness.wf2.toNat SrvwmoXv6Witness.x3)

theorem SrvwmoXv6Witness.len1 : ecount 600 SrvwmoXv6Witness.dEntry SrvwmoXv6Witness.x0 = 106 := by
  decide +kernel
theorem SrvwmoXv6Witness.len2 :
    ecount 600 SrvwmoXv6Witness.dEntry
      (ecurRead SrvwmoXv6Witness.wf1.toNat SrvwmoXv6Witness.x1) = 16 := by
  decide +kernel
theorem SrvwmoXv6Witness.len3 :
    ecount 600 SrvwmoXv6Witness.dEntry (ecurLoop false SrvwmoXv6Witness.x2) = 106 := by
  decide +kernel
theorem SrvwmoXv6Witness.len4 :
    ecount 600 SrvwmoXv6Witness.dEntry
      (ecurRead SrvwmoXv6Witness.wf2.toNat SrvwmoXv6Witness.x3) = 96 := by
  decide +kernel

theorem SrvwmoXv6Witness.noSf1 :
    SrvwmoXv6Witness.esilNoSf 600 SrvwmoXv6Witness.dEntry SrvwmoXv6Witness.x0.1
      SrvwmoXv6Witness.x0.2 = true := by
  decide +kernel
theorem SrvwmoXv6Witness.noSf2 :
    SrvwmoXv6Witness.esilNoSf 600 SrvwmoXv6Witness.dEntry
      (ecurRead SrvwmoXv6Witness.wf1.toNat SrvwmoXv6Witness.x1).1
      (ecurRead SrvwmoXv6Witness.wf1.toNat SrvwmoXv6Witness.x1).2 = true := by
  decide +kernel
theorem SrvwmoXv6Witness.noSf3 :
    SrvwmoXv6Witness.esilNoSf 600 SrvwmoXv6Witness.dEntry
      (ecurLoop false SrvwmoXv6Witness.x2).1 (ecurLoop false SrvwmoXv6Witness.x2).2 = true := by
  decide +kernel
theorem SrvwmoXv6Witness.noSf4 :
    SrvwmoXv6Witness.esilNoSf 600 SrvwmoXv6Witness.dEntry
      (ecurRead SrvwmoXv6Witness.wf2.toNat SrvwmoXv6Witness.x3).1
      (ecurRead SrvwmoXv6Witness.wf2.toNat SrvwmoXv6Witness.x3).2 = true := by
  decide +kernel

/-- `auipc` retires: the second stretch ends at `Ret`. -/
theorem SrvwmoXv6Witness.x2Ret : enodeTag SrvwmoXv6Witness.x2.2 = 0 := by decide +kernel

theorem SrvwmoXv6Witness.x1IsRead : (ereadReqAt 4 64 SrvwmoXv6Witness.x1.2).isSome = true := by
  decide +kernel
theorem SrvwmoXv6Witness.x3IsRead : (ereadReqAt 4 64 SrvwmoXv6Witness.x3.2).isSome = true := by
  decide +kernel
theorem SrvwmoXv6Witness.x4IsRead : (ereadReqAt 8 64 SrvwmoXv6Witness.x4.2).isSome = true := by
  decide +kernel

noncomputable def SrvwmoXv6Witness.reqF1 : Mem_read_request 4 64 Arch.pa Arch.translation Arch.arch_ak :=
  (ereadReqAt 4 64 SrvwmoXv6Witness.x1.2).get SrvwmoXv6Witness.x1IsRead
noncomputable def SrvwmoXv6Witness.reqF2 : Mem_read_request 4 64 Arch.pa Arch.translation Arch.arch_ak :=
  (ereadReqAt 4 64 SrvwmoXv6Witness.x3.2).get SrvwmoXv6Witness.x3IsRead
noncomputable def SrvwmoXv6Witness.reqL : Mem_read_request 8 64 Arch.pa Arch.translation Arch.arch_ak :=
  (ereadReqAt 8 64 SrvwmoXv6Witness.x4.2).get SrvwmoXv6Witness.x4IsRead

theorem SrvwmoXv6Witness.f1Req : ereadReqAt 4 64 SrvwmoXv6Witness.x1.2 = some SrvwmoXv6Witness.reqF1 :=
  (Option.some_get _).symm
theorem SrvwmoXv6Witness.f2Req : ereadReqAt 4 64 SrvwmoXv6Witness.x3.2 = some SrvwmoXv6Witness.reqF2 :=
  (Option.some_get _).symm
theorem SrvwmoXv6Witness.lReq : ereadReqAt 8 64 SrvwmoXv6Witness.x4.2 = some SrvwmoXv6Witness.reqL :=
  (Option.some_get _).symm

theorem SrvwmoXv6Witness.f1Pa : paZ SrvwmoXv6Witness.reqF1.pa = 0x80000000 := by decide +kernel
theorem SrvwmoXv6Witness.f2Pa : paZ SrvwmoXv6Witness.reqF2.pa = 0x80000004 := by decide +kernel
theorem SrvwmoXv6Witness.lPa : paZ SrvwmoXv6Witness.reqL.pa = 0x8000a3e8 := by decide +kernel
theorem SrvwmoXv6Witness.f1Ifetch :
    classify SrvwmoXv6Witness.reqF1.access_kind = ⟨true, false, false⟩ := by decide +kernel
theorem SrvwmoXv6Witness.f2Ifetch :
    classify SrvwmoXv6Witness.reqF2.access_kind = ⟨true, false, false⟩ := by decide +kernel
theorem SrvwmoXv6Witness.lPlain :
    classify SrvwmoXv6Witness.reqL.access_kind = ⟨false, false, false⟩ := by decide +kernel
theorem SrvwmoXv6Witness.f1Ram : devAddr SrvwmoXv6Witness.reqF1.pa = false := by decide +kernel
theorem SrvwmoXv6Witness.f2Ram : devAddr SrvwmoXv6Witness.reqF2.pa = false := by decide +kernel
theorem SrvwmoXv6Witness.lRam : devAddr SrvwmoXv6Witness.reqL.pa = false := by decide +kernel

/-! ### 3b. The byte tables -/

def SrvwmoXv6Witness.tvs4 (w : BitVec 32) : List (Nat × BitVec 8) :=
  [(0, nthByte (n := 4) w 0), (0, nthByte (n := 4) w 1), (0, nthByte (n := 4) w 2),
   (0, nthByte (n := 4) w 3)]

def SrvwmoXv6Witness.tvs8 (w : BitVec 64) : List (Nat × BitVec 8) :=
  [(0, nthByte (n := 8) w 0), (0, nthByte (n := 8) w 1), (0, nthByte (n := 8) w 2),
   (0, nthByte (n := 8) w 3), (0, nthByte (n := 8) w 4), (0, nthByte (n := 8) w 5),
   (0, nthByte (n := 8) w 6), (0, nthByte (n := 8) w 7)]

def SrvwmoXv6Witness.ts8 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0]

def SrvwmoXv6Witness.vs8 (w : BitVec 64) : List (BitVec 8) :=
  [nthByte (n := 8) w 0, nthByte (n := 8) w 1, nthByte (n := 8) w 2, nthByte (n := 8) w 3,
   nthByte (n := 8) w 4, nthByte (n := 8) w 5, nthByte (n := 8) w 6, nthByte (n := 8) w 7]

theorem SrvwmoXv6Witness.tvs4Snd (w : BitVec 32) :
    ∀ j : Nat, j < 4 →
      ((SrvwmoXv6Witness.tvs4 w).map Prod.snd)[j]? = some (nthByte (n := 4) w j) := by
  intro j hj
  rcases j with _ | _ | _ | _ | j
  all_goals first | rfl | omega

theorem SrvwmoXv6Witness.tvs8Snd (w : BitVec 64) :
    ∀ j : Nat, j < 8 →
      ((SrvwmoXv6Witness.tvs8 w).map Prod.snd)[j]? = some (nthByte (n := 8) w j) := by
  intro j hj
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
  all_goals first | rfl | omega

theorem SrvwmoXv6Witness.ts8Lookup (j t : Nat) :
    SrvwmoXv6Witness.ts8[j]? = some t → j < 8 ∧ t = 0 := by
  intro h
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> simp [SrvwmoXv6Witness.ts8] at h ⊢ <;> omega

theorem SrvwmoXv6Witness.vs8Lookup (w : BitVec 64) (j : Nat) (v : BitVec 8) :
    (SrvwmoXv6Witness.vs8 w)[j]? = some v → j < 8 ∧ v = nthByte (n := 8) w j := by
  intro h
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;>
    simp [SrvwmoXv6Witness.vs8] at h ⊢ <;> first | exact h.symm | omega

/-- THE IMAGE: the two fetched windows and the GOT word ARE the boot image's bytes. -/
theorem SrvwmoXv6Witness.imgF1 :
    ∀ j : Nat, j < 4 →
      imgZ bootImage (0x80000000 + (j : Int)) = some (nthByte (n := 4) SrvwmoXv6Witness.wf1 j) := by
  intro j hj
  rcases j with _ | _ | _ | _ | j
  all_goals first | omega | (rw [imgZ, bootImage_get?]; decide +kernel)

theorem SrvwmoXv6Witness.imgF2 :
    ∀ j : Nat, j < 4 →
      imgZ bootImage (0x80000004 + (j : Int)) = some (nthByte (n := 4) SrvwmoXv6Witness.wf2 j) := by
  intro j hj
  rcases j with _ | _ | _ | _ | j
  all_goals first | omega | (rw [imgZ, bootImage_get?]; decide +kernel)

theorem SrvwmoXv6Witness.imgL :
    ∀ j : Nat, j < 8 →
      imgZ bootImage (accAddr (paZ SrvwmoXv6Witness.reqL.pa) j) =
        some (nthByte (n := 8) SrvwmoXv6Witness.wl j) := by
  intro j hj
  rw [SrvwmoXv6Witness.lPa]
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
  all_goals first | omega | (rw [accAddr, imgZ, bootImage_get?]; decide +kernel)

/-- A 4-byte image-answered fetch is pinned. -/
theorem SrvwmoXv6Witness.pin4 (base : Int) (w : BitVec 32) :
    (∀ j : Nat, j < 4 → imgZ bootImage (base + (j : Int)) = some (nthByte (n := 4) w j)) →
    WeakAxRealize.fetchPin (imgZ bootImage) (.LIFetch base (SrvwmoXv6Witness.tvs4 w)) := by
  intro h
  simp only [WeakAxRealize.fetchPin]
  refine ⟨by simp [SrvwmoXv6Witness.tvs4], fun j hj => ?_⟩
  have hj4 : j < 4 := by simpa [SrvwmoXv6Witness.tvs4] using hj
  rw [h j hj4, SrvwmoXv6Witness.tvs4Snd w j hj4]

theorem SrvwmoXv6Witness.roLo : ((Xv6.bcRoLo : Nat) : Int) = 0x80000000 := by decide +kernel
theorem SrvwmoXv6Witness.roHi : ((Xv6.bcRoHi : Nat) : Int) = 0x8000a380 := by decide +kernel

/-- … and lies in W3's pristine window when its footprint does. -/
theorem SrvwmoXv6Witness.kfetch4 (img : Image) (log : List Wmsg) (i : Nat) (base : Int)
    (w : BitVec 32) :
    0x80000000 ≤ base → base + 4 ≤ 0x8000a380 →
    candKfetch (Xv6.bcRoLo : Int) (Xv6.bcRoHi : Int) img log i base (SrvwmoXv6Witness.tvs4 w) := by
  intro h1 h2 j hj
  have hj4 : j < 4 := by simpa [SrvwmoXv6Witness.tvs4] using hj
  rw [SrvwmoXv6Witness.roLo, SrvwmoXv6Witness.roHi]
  omega

/-! ### 3c. THE ADMINISTRATIVE RUN, assembled from the bridge -/

/-- Hart 0 from its boundary at `_entry` to the data-load node of `ld sp,1000(sp)`: a pinned,
label-carrying administrative run whose only fetches are the two image windows. -/
theorem SrvwmoXv6Witness.entryRun (d : Efab) :
    ∃ (ls : List Wlabel) (ib4 : Ibch),
      admRunG (pstepPin (imgZ bootImage) pstepEv) true
        (.PHart ⟨0, by decide⟩ (FreeM.pure ()) SrvwmoXv6Witness.rs0 none ibNone) d ls
        (.PHart ⟨0, by decide⟩ SrvwmoXv6Witness.x4.2 SrvwmoXv6Witness.x4.1 none ib4) d ∧
      ∀ (base : Int) (tvs : List (Nat × BitVec 8)), Wlabel.LIFetch base tvs ∈ ls →
        (base = 0x80000000 ∧ tvs = SrvwmoXv6Witness.tvs4 SrvwmoXv6Witness.wf1) ∨
        (base = 0x80000004 ∧ tvs = SrvwmoXv6Witness.tvs4 SrvwmoXv6Witness.wf2) := by
  let c : CPU := ⟨0, by decide⟩
  have s0 := SrvwmoXv6Witness.boundaryPstep c () SrvwmoXv6Witness.rs0 ibNone d
  obtain ⟨ls1, ib1, h1, n1⟩ := esilAdmRun (imgZ bootImage) c SrvwmoXv6Witness.dEntry 600
    SrvwmoXv6Witness.x0.1 SrvwmoXv6Witness.x0.2 ibNone d SrvwmoXv6Witness.noSf1
  have s1 := SrvwmoXv6Witness.fetchPstep c 4 SrvwmoXv6Witness.x1.2 SrvwmoXv6Witness.reqF1
    SrvwmoXv6Witness.x1.1 ib1 d SrvwmoXv6Witness.wf1 (SrvwmoXv6Witness.tvs4 SrvwmoXv6Witness.wf1)
    SrvwmoXv6Witness.f1Req SrvwmoXv6Witness.f1Ram (by rw [SrvwmoXv6Witness.f1Ifetch]) rfl
    (SrvwmoXv6Witness.tvs4Snd _)
  obtain ⟨ls2, ib2, h2, n2⟩ := esilAdmRun (imgZ bootImage) c SrvwmoXv6Witness.dEntry 600
    (ecurRead SrvwmoXv6Witness.wf1.toNat SrvwmoXv6Witness.x1).1
    (ecurRead SrvwmoXv6Witness.wf1.toNat SrvwmoXv6Witness.x1).2 ib1 d SrvwmoXv6Witness.noSf2
  obtain ⟨u, hu⟩ := enodeTagRet _ SrvwmoXv6Witness.x2Ret
  have s2 : pstepEv (.PHart c SrvwmoXv6Witness.x2.2 SrvwmoXv6Witness.x2.1 none ib2) d .LInstr
      (.PHart c (riscvStep false) SrvwmoXv6Witness.x2.1 none ibNone) d := by
    rw [hu]; exact SrvwmoXv6Witness.boundaryPstep c u _ _ d
  obtain ⟨ls3, ib3, h3, n3⟩ := esilAdmRun (imgZ bootImage) c SrvwmoXv6Witness.dEntry 600
    (ecurLoop false SrvwmoXv6Witness.x2).1 (ecurLoop false SrvwmoXv6Witness.x2).2 ibNone d
    SrvwmoXv6Witness.noSf3
  have s3 := SrvwmoXv6Witness.fetchPstep c 4 SrvwmoXv6Witness.x3.2 SrvwmoXv6Witness.reqF2
    SrvwmoXv6Witness.x3.1 ib3 d SrvwmoXv6Witness.wf2 (SrvwmoXv6Witness.tvs4 SrvwmoXv6Witness.wf2)
    SrvwmoXv6Witness.f2Req SrvwmoXv6Witness.f2Ram (by rw [SrvwmoXv6Witness.f2Ifetch]) rfl
    (SrvwmoXv6Witness.tvs4Snd _)
  obtain ⟨ls4, ib4, h4, n4⟩ := esilAdmRun (imgZ bootImage) c SrvwmoXv6Witness.dEntry 600
    (ecurRead SrvwmoXv6Witness.wf2.toNat SrvwmoXv6Witness.x3).1
    (ecurRead SrvwmoXv6Witness.wf2.toNat SrvwmoXv6Witness.x3).2 ib3 d SrvwmoXv6Witness.noSf4
  have p1 := SrvwmoXv6Witness.pin4 (paZ SrvwmoXv6Witness.reqF1.pa) SrvwmoXv6Witness.wf1
    (by rw [SrvwmoXv6Witness.f1Pa]; exact SrvwmoXv6Witness.imgF1)
  have p2 := SrvwmoXv6Witness.pin4 (paZ SrvwmoXv6Witness.reqF2.pa) SrvwmoXv6Witness.wf2
    (by rw [SrvwmoXv6Witness.f2Pa]; exact SrvwmoXv6Witness.imgF2)
  have a0 : admRunG (pstepPin (imgZ bootImage) pstepEv) true
      (.PHart c (FreeM.pure ()) SrvwmoXv6Witness.rs0 none ibNone) d [.LInstr]
      (.PHart c (riscvStep false) SrvwmoXv6Witness.rs0 none ibNone) d :=
    .cons _ _ _ _ _ _ _ _ rfl ⟨s0, trivial⟩ (.nil _ _)
  have a1 := admRunG.cons (pstep := pstepPin (imgZ bootImage) pstepEv) (instr := true)
    _ _ (.LIFetch (paZ SrvwmoXv6Witness.reqF1.pa) (SrvwmoXv6Witness.tvs4 SrvwmoXv6Witness.wf1))
    _ _ _ _ _ (by simp [lbAdmin]) ⟨s1, p1⟩ (.nil _ _)
  have a2 := admRunG.cons (pstep := pstepPin (imgZ bootImage) pstepEv) (instr := true)
    _ _ .LInstr _ _ _ _ _ (by simp [lbAdmin]) ⟨s2, trivial⟩ (.nil _ _)
  have a3 := admRunG.cons (pstep := pstepPin (imgZ bootImage) pstepEv) (instr := true)
    _ _ (.LIFetch (paZ SrvwmoXv6Witness.reqF2.pa) (SrvwmoXv6Witness.tvs4 SrvwmoXv6Witness.wf2))
    _ _ _ _ _ (by simp [lbAdmin]) ⟨s3, p2⟩ (.nil _ _)
  refine ⟨[.LInstr] ++ ls1 ++ [.LIFetch (paZ SrvwmoXv6Witness.reqF1.pa)
      (SrvwmoXv6Witness.tvs4 SrvwmoXv6Witness.wf1)] ++ ls2 ++ [.LInstr] ++ ls3 ++
      [.LIFetch (paZ SrvwmoXv6Witness.reqF2.pa) (SrvwmoXv6Witness.tvs4 SrvwmoXv6Witness.wf2)] ++
      ls4, ib4, ?_, ?_⟩
  · exact SrvwmoXv6Witness.admRunGApp (SrvwmoXv6Witness.admRunGApp
      (SrvwmoXv6Witness.admRunGApp (SrvwmoXv6Witness.admRunGApp
      (SrvwmoXv6Witness.admRunGApp (SrvwmoXv6Witness.admRunGApp
      (SrvwmoXv6Witness.admRunGApp a0 h1) a1) h2) a2) h3) a3) h4
  · intro base tvs hm
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with ((((((h | h) | h) | h) | h) | h) | h) | h
    · cases h
    · exact absurd rfl (n1 _ h base tvs)
    · cases h; exact Or.inl ⟨SrvwmoXv6Witness.f1Pa, rfl⟩
    · exact absurd rfl (n2 _ h base tvs)
    · cases h
    · exact absurd rfl (n3 _ h base tvs)
    · cases h; exact Or.inr ⟨SrvwmoXv6Witness.f2Pa, rfl⟩
    · exact absurd rfl (n4 _ h base tvs)

/-! ## 4. M1's PREMISE SET -/

/-- **M1's premise set** (plan §A, "M1/M2 (internal)"; §C W5): the boot facts transposed through
`PowerOn` (`wbootFacts`, generation 0, `fs.img` on the disk of a reset fabric), the sRVWMO
candidate, its boot image, the initial program states and fabric, the SHAPED conformance
`execProgOk'S` at the boot-image-pinned LTS with M1's fetch clause `candKfetch bcRoLo bcRoHi`,
and `candSca`. -/
def srvwmoXv6M1Premises (σ0 : WGState) (c : Cand) (pst : Nat → List Pexv6)
    (dv : Nat → Efab) : Prop :=
  wbootFacts σ0 ∧ σ0.wggen = 0 ∧
  (∃ ds : DevStates, σ0.wgdev = ds.reset ∧ diskOf ds = Xv6.fsImgDisk) ∧
  srvwmoConsistent c ∧ c.cdImg = imgZ σ0.wgimg ∧
  pst 0 = epsInit σ0 ∧ dv 0 = efInit σ0.wgdev ∧
  execProgOk'S (pstepPin (imgZ σ0.wgimg) pstepEv) pclsEv
    (candKfetch (Xv6.bcRoLo : Int) (Xv6.bcRoHi : Int)) pst dv (candExec c) ∧
  candSca c

/-- Every M1 premise set FEEDS W5b's replay: the shaped promise-free run from the booted
initial configuration, `pairAdjacent`, ending at the supplied program states and fabric, matched
to the candidate's last state. -/
theorem srvwmoXv6M1PfRun (σ0 : WGState) (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab) :
    srvwmoXv6M1Premises σ0 c pst dv →
    ∃ (cf : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)),
      pfRunS pstepEv pclsEv (candKfetch (Xv6.bcRoLo : Int) (Xv6.bcRoHi : Int))
        (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) st cf ∧
      pairAdjacent st ∧
      cf.pcAgs.map Wpagent.paSt = pst c.cdTr.length ∧ cf.pcDev = dv c.cdTr.length ∧
      cfgMatchd cf (stt (candExec c) c.cdTr.length) := by
  rintro ⟨-, -, -, hcons, himg, hpst, hdv, hprog, -⟩
  obtain ⟨hwf, -, heximg⟩ := srvwmoRealizable c hcons
  obtain ⟨cf, st, hrun, hadj, h1, h2, h3⟩ :=
    execWfPfRunPinShaped pstepEv pclsEv _ (imgZ σ0.wgimg) pst dv (candExec c) pclsEvEqr
      (by rw [heximg, himg]) hwf hprog
  rw [heximg, himg, hpst, hdv] at hrun
  exact ⟨cf, st, hrun, hadj, h1, h2, h3⟩

/-! ## 5. THE WITNESS -/

/-- A device vector with `fs.img` on the disk. -/
def SrvwmoXv6Witness.ds : DevStates :=
  (⟨fun _ => default⟩ : DevStates).set .virtio (Virtio.initial Xv6.fsImgDisk)

theorem SrvwmoXv6Witness.dsDisk : diskOf SrvwmoXv6Witness.ds = Xv6.fsImgDisk := by
  unfold diskOf SrvwmoXv6Witness.ds
  rw [DevStates.set_same]
  rfl

/-- THE BOOTED STATE: every hart at its boot landing file, the boot image, a fresh era. -/
def SrvwmoXv6Witness.sigma0 : WGState where
  wgregs c := bootLand c WeakEvStarted.regs0
  wgimg := bootImage
  wglog := []
  wgws _ := wsInit
  wgdev := SrvwmoXv6Witness.ds.reset
  wggen := 0
  wgpow := true
  wgib _ := ibNone
  wgitv _ := 0
  wgrt _ := DevRt.init

theorem SrvwmoXv6Witness.sigma0Boot : wbootFacts SrvwmoXv6Witness.sigma0 :=
  ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => rfl,
    fun c => ⟨WeakEvStarted.regs0, bootRun_bootLand c _⟩, ⟨_, rfl⟩, fun _ => rfl⟩

/-- THE ONE AXIOMATIC LABEL: the plain 8-byte load of the GOT word, from the image. -/
noncomputable def SrvwmoXv6Witness.lbl : Lbl :=
  .LLoad false (paZ SrvwmoXv6Witness.reqL.pa) SrvwmoXv6Witness.ts8
    (SrvwmoXv6Witness.vs8 SrvwmoXv6Witness.wl)

/-- … and the wlabel realizing it. -/
noncomputable def SrvwmoXv6Witness.wlbl : Wlabel :=
  .LLoad false false (paZ SrvwmoXv6Witness.reqL.pa) (SrvwmoXv6Witness.tvs8 SrvwmoXv6Witness.wl) []

def SrvwmoXv6Witness.c0 : Cand := ⟨imgZ bootImage, []⟩

noncomputable def SrvwmoXv6Witness.cand : Cand :=
  candSnoc SrvwmoXv6Witness.c0 ⟨0, SrvwmoXv6Witness.lbl⟩

theorem SrvwmoXv6Witness.c0Log : cdLogEnd SrvwmoXv6Witness.c0 = [] := rfl

/-- THE CANDIDATE IS sRVWMO-CONSISTENT: the image bytes at timestamp 0 over the empty log. -/
theorem SrvwmoXv6Witness.candConsistent : srvwmoConsistent SrvwmoXv6Witness.cand := by
  have hc0 : srvwmoConsistent SrvwmoXv6Witness.c0 :=
    srvwmoOfWf _ (candReachable _ (fun k s hs => by simp [SrvwmoXv6Witness.c0] at hs)).1
  refine snocReadConsistent _ 0 false _ _ _ hc0 ⟨rfl, ?_, ?_⟩
  · intro j t v ht hv
    obtain ⟨hj8, rfl⟩ := SrvwmoXv6Witness.ts8Lookup j t ht
    obtain ⟨-, rfl⟩ := SrvwmoXv6Witness.vs8Lookup _ j v hv
    exact SrvwmoXv6Witness.imgL j hj8
  · rintro j t - ⟨t', -, -, m, hm, -⟩
    rw [SrvwmoXv6Witness.c0Log] at hm
    simp at hm

/-- **M1's PREMISE SET IS SATISFIABLE** (W5c, D22), hypothesis free: a booted σ0, a NONEMPTY
sRVWMO-consistent candidate — `_entry`'s `ld sp,1000(sp)` on hart 0, reading the GOT word from
the image — and program states / a (constant) fabric satisfying every premise of M1. -/
theorem srvwmoXv6M1Satisfiable :
    ∃ (σ0 : WGState) (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab),
      srvwmoXv6M1Premises σ0 c pst dv ∧
      c.cdTr = [⟨0, .LLoad false 0x8000a3e8 SrvwmoXv6Witness.ts8
        (SrvwmoXv6Witness.vs8 SrvwmoXv6Witness.wl)⟩] ∧
      ∀ k, dv k = efInit σ0.wgdev := by
  let σ0 := SrvwmoXv6Witness.sigma0
  let d0 : Efab := efInit σ0.wgdev
  obtain ⟨ls, ib4, hrun, hf⟩ := SrvwmoXv6Witness.entryRun d0
  let p' : Pexv6 := .PHart ⟨0, by decide⟩
    (ereadResume SrvwmoXv6Witness.wl.toNat SrvwmoXv6Witness.x4.2) SrvwmoXv6Witness.x4.1 none ib4
  have hld : pstepEv (.PHart ⟨0, by decide⟩ SrvwmoXv6Witness.x4.2 SrvwmoXv6Witness.x4.1 none ib4)
      d0 SrvwmoXv6Witness.wlbl p' d0 :=
    SrvwmoXv6Witness.loadPstep _ 8 _ SrvwmoXv6Witness.reqL _ ib4 d0 SrvwmoXv6Witness.wl _
      SrvwmoXv6Witness.lReq SrvwmoXv6Witness.lRam SrvwmoXv6Witness.lPlain rfl
      (SrvwmoXv6Witness.tvs8Snd _)
  have hp : ((fun _ => epsInit σ0) (cdEnd SrvwmoXv6Witness.c0) : List Pexv6)[0]? =
      some (.PHart ⟨0, by decide⟩ (FreeM.pure ()) SrvwmoXv6Witness.rs0 none ibNone) := rfl
  have hfetch : fetchesOk (candKfetch (Xv6.bcRoLo : Int) (Xv6.bcRoHi : Int))
      (candLastSt SrvwmoXv6Witness.c0) 0 ls := by
    intro base tvs hm
    rcases hf base tvs hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact SrvwmoXv6Witness.kfetch4 _ _ _ _ _ (by omega) (by omega)
    · exact SrvwmoXv6Witness.kfetch4 _ _ _ _ _ (by omega) (by omega)
  have hsca : ∀ (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)),
      SrvwmoXv6Witness.lbl = .LLoad aq base ts vs →
      scaOk (candLastSt SrvwmoXv6Witness.c0).msImg (candLastSt SrvwmoXv6Witness.c0).msLog 0
        base ts := by
    intro aq base ts vs h
    simp only [SrvwmoXv6Witness.lbl, Lbl.LLoad.injEq] at h
    obtain ⟨-, rfl, rfl, -⟩ := h
    show scaOk (imgZ bootImage) [] 0 _ _
    refine ⟨0, Nat.le_refl _, fun j t hj => ?_⟩
    obtain ⟨hj8, rfl⟩ := SrvwmoXv6Witness.ts8Lookup j t hj
    refine ⟨?_, Or.inl (Nat.le_refl 0), fun t' ht' hs => ?_⟩
    · rw [logByte0, SrvwmoXv6Witness.imgL j hj8]; rfl
    · cases t' with
      | zero => omega
      | succ i => simp [logByte] at hs
  have hre : hlblRealizes (.PHart ⟨0, by decide⟩ SrvwmoXv6Witness.x4.2 SrvwmoXv6Witness.x4.1 none ib4)
      ((candLastSt SrvwmoXv6Witness.c0).msWs 0) SrvwmoXv6Witness.lbl SrvwmoXv6Witness.wlbl :=
    ⟨trivial, rfl, rfl, rfl⟩
  have hprog := execProgOk'SSnoc (candKfetch (Xv6.bcRoLo : Int) (Xv6.bcRoHi : Int))
    SrvwmoXv6Witness.c0 0 _ _ _ ls SrvwmoXv6Witness.wlbl SrvwmoXv6Witness.lbl p' d0
    (fun _ => epsInit σ0) (fun _ => d0)
    (execProgOk'SNil _ _ _ _) hp hrun hfetch hsca trivial hre hld
  refine ⟨σ0, SrvwmoXv6Witness.cand, pstSnoc SrvwmoXv6Witness.c0 (fun _ => epsInit σ0) 0 p',
    dvSnoc SrvwmoXv6Witness.c0 (fun _ => d0) d0,
    ⟨SrvwmoXv6Witness.sigma0Boot, rfl, ⟨SrvwmoXv6Witness.ds, rfl, SrvwmoXv6Witness.dsDisk⟩,
      SrvwmoXv6Witness.candConsistent, rfl,
      pstSnocLe _ _ _ _ 0 (Nat.le_refl _), dvSnocLe _ _ _ 0 (Nat.le_refl _), hprog,
      execProgOk'SSca _ _ _ _ _ _ hprog⟩, ?_, ?_⟩
  · show [(⟨0, SrvwmoXv6Witness.lbl⟩ : Estep)] = _
    simp only [SrvwmoXv6Witness.lbl, SrvwmoXv6Witness.lPa]
  · intro k
    unfold dvSnoc
    split <;> rfl

end Weak
