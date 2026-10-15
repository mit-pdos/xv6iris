/-
Weak: **W10 F1 [OWN.94] (N2′), decision (i) — the transport at SUCCESSFUL-PROTOCOL lock co**
(`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

`CertZ14.lockCoNP` asks the member to agree with `GF` on the co order of EVERY non-plain lock-byte write,
FAILED acquires included (a spinning hart's `amoswap.w.aq` reading and writing the held value).  The
transport never needs a failed acquire's place: this file restates it at the co of the SUCCESSFUL
protocol writes only (`CertZ18.sp`: non-plain and not a failed acquire), replacing the co-based quiet
window by two value facts:

  §1  **`CertZ18.lockCoSP`**, `agreeW3`/`agreeRP3` (+ RMW read-value agreement, from the rows), the
      member fact **`CertZ18.rmwLatest`** (a member RMW reads the latest bytes of the log prefix before
      its own message — the candidate's RMW atomicity), and the named export fact
      **`CertZ18.regZeroAt`** — "a lock byte is FREE at its registration point";
  §2  the fold from values: **`CertZ18.foldFreeOfLatest`** (latest value free ⇒ fold free) and
      **`CertZ18.valFreeOfFold`** (fold free ⇒ latest value free, using `regZeroAt`);
  §3  **`CatLin.csChainedT3`** — `csChainedT2` at `agreeW3`, the reader's quiet window from the
      member's RMW value (no co agreement used), the writer's acquire shown SUCCESSFUL from the fold.

`regZeroAt` (xv6 justification): the ghost registers a lock word from a `WClean` byte at `n0 = |log|`
(`wlpAltRegister` sets the fold FREE without looking at the value — hence this separate fact); xv6
registers each lock right after `initlock`'s plain `lk->locked = 0` (a `WCplain` store, so by `wlpAt` it
lies before `n0`), and no other write of the byte lies between them (static locks: the boot hart,
before other harts start; a pipe lock: the page was handed out by `kalloc` under `kmem.lock`, `kfree`'s
junk memset precedes the free-list release).  It is a fact about the registration ghost, discharged
with the export (W11) — to be re-checked against the registration site when discharged.

Spec: FAITHFUL (proof organisation; `regZeroAt` and `rmwLatest` are true of xv6 runs and RVWMO members).
-/
import Weak.CertZ17

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. Successful-protocol co, the agreement, the two value facts -/

/-- A FAILED ACQUIRE of `b`: writes a nonzero byte at `b` and reads a nonzero byte there (an
`amoswap.w.aq` on a held lock). -/
def CertZ18.failAcq (G : Gexec) (b : Int) (e : Geid) : Prop :=
  (∃ v, gwritesByte G e b v ∧ v ≠ lockFree) ∧ (∃ t v, greadsByte G e b t v ∧ v ≠ lockFree)

/-- A SUCCESSFUL protocol write of `b`: non-plain and not a failed acquire. -/
def CertZ18.sp (G : Gexec) (b : Int) (e : Geid) : Prop :=
  CertZ14.np G e ∧ ¬ CertZ18.failAcq G b e

/-- **SUCCESSFUL-PROTOCOL LOCK CO**: on the lock bytes, the successful protocol writes are co-ordered
in `GR` as in `G`. -/
def CertZ18.lockCoSP (G GR : Gexec) (L : Int → Prop) : Prop :=
  ∀ (b : Int) (x y : Geid) (vx vy : BitVec 8), L b →
    gwritesByte G x b vx → gwritesByte G y b vy → CertZ18.sp G b x → CertZ18.sp G b y →
    (gwix G x < gwix G y ↔ gwix GR x < gwix GR y)

/-- RMW read values agree (timestamps may differ). -/
def CertZ18.rmwRdAgree (G GR : Gexec) : Prop :=
  (∀ e a t v, glblIs G e lbIsW → greadsByte G e a t v → ∃ t', greadsByte GR e a t' v) ∧
  (∀ e a t v, glblIs G e lbIsW → greadsByte GR e a t v → ∃ t', greadsByte G e a t' v)

def CertZ18.agreeW3 (G GR : Gexec) (L : Int → Prop) : Prop :=
  GR.gxImg = G.gxImg ∧
  (∀ e a v, gwritesByte GR e a v ↔ gwritesByte G e a v) ∧
  (∀ e k, gcls G e k → glblIs G e lbIsW → gcls GR e k) ∧
  CertZ18.rmwRdAgree G GR ∧
  CertZ18.lockCoSP G GR L

def CertZ18.agreeRP3 (G GR : Gexec) (pi : Nat → Nat) (L : Int → Prop) : Prop :=
  GR.gxImg = G.gxImg ∧
  List.Forall₂ (fun (r r' : List Lbl) => List.Forall₂ (fun l l' => lblReidxW (lblRen pi l) l') r r')
    G.gxProg GR.gxProg ∧
  CertZ18.lockCoSP G GR L

/-- **THE MEMBER'S RMW ATOMICITY**: an RMW of `GR` reads, at every byte, the latest message of the log
prefix before its own message (`gwix GR e - 1` messages). -/
def CertZ18.rmwLatest (GR : Gexec) (log : List Wmsg) : Prop :=
  ∀ e a t v, glblIs GR e lbIsW → greadsByte GR e a t v →
    latest GR.gxImg (log.take (gwix GR e - 1)) a t ∧
    logByte GR.gxImg (log.take (gwix GR e - 1)) t a = some v

/-- **THE NAMED EXPORT FACT — A LOCK BYTE IS FREE AT ITS REGISTRATION POINT**: the latest value of `b`
in the first `n0` messages (the image's byte when none writes it) is `lockFree`. -/
def CertZ18.regZeroAt (img : Image) (log : List Wmsg) (b : Int) (n0 : Nat) : Prop :=
  ∀ t, latest img (log.take n0) b t → logByte img (log.take n0) t b = some lockFree

/-- `protReg` with the registration point's lock byte FREE. -/
def CertZ18.protRegZ (P : Int → Int → Prop) (img : Image) (log : List Wmsg) : Prop :=
  ∀ a base, P a base →
    ∃ (n0 r0 : Nat) (h : Option Nat),
      wprotAt log a base n0 r0 ∧ wlpAt log base base n0 ∧ wlpAlt log base n0 h ∧
      CertZ18.regZeroAt img log base n0

theorem CertZ18.protRegOfZ (P : Int → Int → Prop) (img : Image) (log : List Wmsg) :
    CertZ18.protRegZ P img log → protReg P log := by
  intro h a base hP
  obtain ⟨n0, r0, hh, h1, h2, h3, -⟩ := h a base hP
  exact ⟨n0, r0, hh, h1, h2, h3⟩

theorem CertZ18.reidxRd (lb lb' : Lbl) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    lblReidxW lb lb' → lbIsW lb = true → lbRd lb = some (base, ts, vs) →
    ∃ ts', lbRd lb' = some (base, ts', vs) ∧ ts'.length = ts.length := by
  rintro (h | h | h) hw hrd
  · cases lb <;> cases lb' <;> simp_all [lblReidx, lbIsW, lbRd]
  · cases lb <;> cases lb' <;> simp_all [lblReidxSub, lbIsW]
  · cases lb <;> cases lb' <;> simp_all [lblPoisoned, lbIsW]

theorem CertZ18.reidxRdInv (lb lb' : Lbl) (base : Int) (ts' : List Nat) (vs : List (BitVec 8)) :
    lblReidxW lb lb' → lbIsW lb = true → lbRd lb' = some (base, ts', vs) →
    ∃ ts, lbRd lb = some (base, ts, vs) ∧ ts'.length = ts.length := by
  rintro (h | h | h) hw hrd
  · cases lb <;> cases lb' <;> simp_all [lblReidx, lbIsW, lbRd]
  · cases lb <;> cases lb' <;> simp_all [lblReidxSub, lbIsW]
  · cases lb <;> cases lb' <;> simp_all [lblPoisoned, lbIsW]

theorem CertZ18.renRdInv (pi : Nat → Nat) (l : Lbl) (base : Int) (ts1 : List Nat)
    (vs : List (BitVec 8)) :
    lbRd (lblRen pi l) = some (base, ts1, vs) →
    ∃ ts, lbRd l = some (base, ts, vs) ∧ ts1.length = ts.length := by
  intro h
  cases l <;> simp only [lblRen, lbRd, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl, rfl⟩ := h <;> exact ⟨_, rfl, by simp⟩

theorem CertZ18.rdAgreeOfRP (G GR : Gexec) (pi : Nat → Nat) :
    GraphFetchN2.agreeRP G GR pi (fun _ => False) → CertZ18.rmwRdAgree G GR := by
  intro hag
  constructor
  · rintro e a t v ⟨l1, hl1, hW⟩ ⟨l0, base, ts, vs, j, hl0, hrd, ht, hv, ha⟩
    rw [hl1, Option.some.injEq] at hl0
    subst hl0
    rcases GraphFetchN2.agreeRPLbl G GR pi _ e hag with ⟨h1, -⟩ | ⟨l, l', h1, h2, hl⟩
    · rw [h1] at hl1; cases hl1
    · rw [h1, Option.some.injEq] at hl1
      subst hl1
      obtain ⟨ts', hrd', hlen⟩ := CertZ18.reidxRd _ _ base (ts.map pi) vs hl
        (by rw [lblRenIsW]; exact hW) (lblRenRd pi _ base ts vs hrd)
      have hj : j < ts'.length := by
        rw [hlen, List.length_map]; exact lookup_lt_Some ht
      exact ⟨ts'[j], l', base, ts', vs, j, h2, hrd', List.getElem?_eq_getElem hj, hv, ha⟩
  · rintro e a t v ⟨l1, hl1, hW⟩ ⟨l0, base, ts', vs, j, hl0, hrd, ht, hv, ha⟩
    rcases GraphFetchN2.agreeRPLbl G GR pi _ e hag with ⟨h1, -⟩ | ⟨l, l', h1, h2, hl⟩
    · rw [h1] at hl1; cases hl1
    · rw [h1, Option.some.injEq] at hl1
      subst hl1
      rw [h2, Option.some.injEq] at hl0
      subst hl0
      obtain ⟨ts1, hrd1, hlen1⟩ := CertZ18.reidxRdInv _ _ base ts' vs hl
        (by rw [lblRenIsW]; exact hW) hrd
      obtain ⟨ts, hrd0, hlen0⟩ := CertZ18.renRdInv pi l base ts1 vs hrd1
      have hj : j < ts.length := by
        rw [← hlen0, ← hlen1]; exact lookup_lt_Some ht
      exact ⟨ts[j], l, base, ts, vs, j, h1, hrd0, List.getElem?_eq_getElem hj, hv, ha⟩

theorem CertZ18.agreeW3OfRP3 (G GR : Gexec) (pi : Nat → Nat) (L : Int → Prop) :
    CertZ18.agreeRP3 G GR pi L → CertZ18.agreeW3 G GR L := by
  rintro ⟨himg, hrows, hco⟩
  have hRP : GraphFetchN2.agreeRP G GR pi (fun _ => False) :=
    ⟨himg, hrows, fun _ _ _ _ _ hb => hb.elim⟩
  obtain ⟨h1, h2, h3, -⟩ := GraphFetchN2.agreeWOfRP G GR pi (fun _ => False) hRP
  exact ⟨h1, h2, h3, CertZ18.rdAgreeOfRP G GR pi hRP, hco⟩

/-- The write/class part, as `CertZ14`'s agreement at the empty lock set. -/
theorem CertZ18.agreeW2Of (G GR : Gexec) (L : Int → Prop) :
    CertZ18.agreeW3 G GR L → CertZ14.agreeW2 G GR (fun _ => False) :=
  fun ⟨h1, h2, h3, _, _⟩ =>
    ⟨h1, h2, h3, fun _ _ _ _ _ hb => hb.elim, fun _ _ _ _ _ hb => hb.elim⟩

/-- Protocol co gives successful-protocol co. -/
theorem CertZ18.lockCoSPOfNP (G GR : Gexec) (L : Int → Prop) :
    CertZ14.lockCoNP G GR L → CertZ18.lockCoSP G GR L :=
  fun h b x y vx vy hb hx hy hsx hsy => h.1 b x y vx vy hb hx hy hsx.1 hsy.1

/-- A non-plain release is successful. -/
theorem CertZ18.spRel (G : Gexec) (b : Int) (R : Geid) :
    CertZ14.np G R → lockRel G b R → CertZ18.sp G b R :=
  fun hnp hR => ⟨hnp, fun ⟨⟨v, hv, hne⟩, _⟩ => hne (gwritesByteDet G R b v lockFree hv hR)⟩

/-- A non-plain acquire reading the free value is successful. -/
theorem CertZ18.spRow (G : Gexec) (b : Int) (A : Geid) :
    CertZ14.np G A → acqRow G b A → CertZ18.sp G b A :=
  fun hnp ⟨t, hrd⟩ => ⟨hnp, fun ⟨_, ⟨t', v, hrd', hne⟩⟩ =>
    hne (greadsByteDet G A b t' v t lockFree hrd' hrd).2⟩

theorem CertZ18.coLeR3 (G GR : Gexec) (L : Int → Prop) (b : Int) (x y : Geid) (vx vy : BitVec 8) :
    gwf G → CertZ18.lockCoSP G GR L → L b →
    gwritesByte G x b vx → gwritesByte G y b vy → CertZ18.sp G b x → CertZ18.sp G b y →
    gwix G x ≤ gwix G y → gwix GR x ≤ gwix GR y := by
  intro hwf hco hL hx hy hsx hsy hle
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · exact Nat.le_of_lt ((hco b x y vx vy hL hx hy hsx hsy).1 hlt)
  · have := gwixInj G x y hwf.1 (gwritesByteGwrites G x b vx hwf hx)
      (gwritesByteGwrites G y b vy hwf hy) heq
    subst this
    exact Nat.le_refl _

/-! # 2. The fold from values -/

theorem CertZ18.logByteTake (img : Image) (log : List Wmsg) (p t : Nat) (a : Int) :
    t ≤ p → logByte img (log.take p) t a = logByte img log t a := by
  intro h
  cases t with
  | zero => rfl
  | succ i => rw [logByteS, logByteS, lookup_take (by omega)]

/-- The latest timestamp of a prefix bounds every later message of the prefix away from the byte. -/
theorem CertZ18.quietOfLatest (img : Image) (log : List Wmsg) (b : Int) (p t : Nat) :
    p ≤ log.length → latest img (log.take p) b t →
    ∀ r mr, t ≤ r → r < p → log[r]? = some mr → msgByte mr b = none := by
  rintro hp ⟨-, hnw⟩ r mr htr hrp hmr
  cases hb : msgByte mr b with
  | none => rfl
  | some v =>
    exfalso
    apply hnw
    refine ⟨r + 1, by omega, by rw [List.length_take, Nat.min_eq_left hp]; omega, mr, ?_,
      by rw [hb]; rfl⟩
    rw [Nat.add_sub_cancel, lookup_take hrp]
    exact hmr

theorem CertZ18.latestLe (img : Image) (log : List Wmsg) (b : Int) (p t : Nat) :
    p ≤ log.length → latest img (log.take p) b t → t ≤ p := by
  intro hp hlat
  have := logByteBounded img _ t b hlat.1
  rw [List.length_take, Nat.min_eq_left hp] at this
  exact this

/-- A zero message at a window position leaves the fold free. -/
theorem CertZ18.foldAtZero (log : List Wmsg) (b : Int) (n0 : Nat) (h : Option Nat) (i : Nat)
    (m : Wmsg) :
    lockWordByte log b → wlpAlt log b n0 h → n0 ≤ i → log[i]? = some m →
    msgByte m b = some lockFree → wlpHolderAt log b n0 (i + 1) = some none := by
  intro hlwb halt hn0 hm hbz
  have hil := lookup_lt_Some hm
  have hzero := hlwb i m lockFree hm hbz rfl
  obtain ⟨-, hf⟩ := halt
  obtain ⟨h2, ht2⟩ := wlpHolderIsSome log b n0 (i + 1) log.length h (by omega) hf
  obtain ⟨h1, ht1⟩ := wlpHolderIsSome log b n0 i log.length h (by omega) hf
  rw [ht2]
  have hstep := wlpHolderStep log b n0 i m hn0 hm
  rw [ht1, ht2] at hstep
  dsimp only at hstep
  rw [(mwritesTrue b m).2 (by rw [hbz]; rfl)] at hstep
  simp only [↓reduceIte] at hstep
  rw [(altStepZero h1 m h2 hzero hstep.symm).1]

/-- **LATEST FREE ⇒ FOLD FREE**: if the latest value of `b` in the first `p` messages is free, the
fold is free after them. -/
theorem CertZ18.foldFreeOfLatest (img : Image) (log : List Wmsg) (b : Int) (n0 : Nat)
    (h : Option Nat) (p t : Nat) :
    lockWordByte log b → wlpAlt log b n0 h → p ≤ log.length →
    latest img (log.take p) b t → logByte img (log.take p) t b = some lockFree →
    wlpHolderAt log b n0 p = some none := by
  intro hlwb halt hp hlat hv
  have hq := CertZ18.quietOfLatest img log b p t hp hlat
  have htp := CertZ18.latestLe img log b p t hp hlat
  by_cases htn : t ≤ n0
  · by_cases hpn : p ≤ n0
    · exact wlpHolderSmall log b n0 p hpn
    · rw [wlpHolderQuiet log b n0 n0 p (by omega) (fun r mr hr hmr => hq r mr (by omega) hr.2 hmr)]
      exact wlpHolderSmall log b n0 n0 (Nat.le_refl _)
  · rw [wlpHolderQuiet log b n0 t p htp (fun r mr hr hmr => hq r mr hr.1 hr.2 hmr)]
    obtain ⟨i, rfl⟩ : ∃ i, t = i + 1 := ⟨t - 1, by omega⟩
    rw [CertZ18.logByteTake img log p (i + 1) b htp, logByteS] at hv
    cases hm : log[i]? with
    | none => rw [hm] at hv; cases hv
    | some m =>
      rw [hm] at hv
      exact CertZ18.foldAtZero log b n0 h i m hlwb halt (by omega) hm (by simpa using hv)

/-- **FOLD FREE ⇒ LATEST FREE** (with the registration point's byte free): after a window prefix whose
fold is free, the latest value of `b` is free — a nonzero exclusive message never leaves the fold
free, and before the registration point `regZeroAt` gives it. -/
theorem CertZ18.valFreeOfFold (img : Image) (log : List Wmsg) (b : Int) (n0 : Nat)
    (h : Option Nat) (p t : Nat) (v : BitVec 8) :
    CertZ18.regZeroAt img log b n0 → n0 ≤ p → p ≤ log.length →
    wlpHolderAt log b n0 p = some none →
    latest img (log.take p) b t → logByte img (log.take p) t b = some v → v = lockFree := by
  intro hz hn0 hp hfree hlat hv
  have hq := CertZ18.quietOfLatest img log b p t hp hlat
  have htp := CertZ18.latestLe img log b p t hp hlat
  by_cases htn : t ≤ n0
  · rw [CertZ18.logByteTake img log p t b htp] at hv
    have hlat0 : latest img (log.take n0) b t := by
      refine ⟨by rw [CertZ18.logByteTake img log n0 t b htn, hv]; rfl, ?_⟩
      rintro ⟨s, hs1, hs2, m, hm, hs⟩
      rw [List.length_take, Nat.min_eq_left (by omega : n0 ≤ log.length)] at hs2
      rw [lookup_take (by omega)] at hm
      rw [hq (s - 1) m (by omega) (by omega) hm] at hs
      cases hs
    have hz0 := hz t hlat0
    rw [CertZ18.logByteTake img log n0 t b htn, hv] at hz0
    exact Option.some.inj hz0
  · rw [wlpHolderQuiet log b n0 t p htp (fun r mr hr hmr => hq r mr hr.1 hr.2 hmr)] at hfree
    obtain ⟨i, rfl⟩ : ∃ i, t = i + 1 := ⟨t - 1, by omega⟩
    rw [CertZ18.logByteTake img log p (i + 1) b htp, logByteS] at hv
    cases hm : log[i]? with
    | none => rw [hm] at hv; cases hv
    | some m =>
      rw [hm] at hv
      have hbv : msgByte m b = some v := by simpa using hv
      obtain ⟨h1, ht1⟩ := wlpHolderIsSome log b n0 i (i + 1) none (by omega) hfree
      have hstep := wlpHolderStep log b n0 i m (by omega) hm
      rw [ht1, hfree] at hstep
      dsimp only at hstep
      rw [(mwritesTrue b m).2 (by rw [hbv]; rfl)] at hstep
      simp only [↓reduceIte] at hstep
      by_cases hd : m.wmData = wlockZero4
      · exact zero4Byte m b v hd hbv
      · exact absurd rfl (altStepNonzero h1 m none hd hstep.symm).2.1

/-! # 3. The transport at successful-protocol co -/

namespace CatLin

/-- **`csChainedT3` — THE TRANSPORT AT SUCCESSFUL-PROTOCOL LOCK CO** (decision (i)): `csChainedT2` with
the lock co among SUCCESSFUL protocol writes only.  The reader's acquire's quiet window comes from the
member's RMW value (`rmwLatest`: it reads the latest bytes, which are free); the writer's acquire is
successful because the fold is free before it (`valFreeOfFold`, with `regZeroAt`); releases are
successful as they write the free byte. -/
theorem csChainedT3 (GD : Gdexec) (ad : List (Geid × Geid)) (GR : Gexec) (L : Int → Prop)
    (log : List Wmsg) (b a : Int) (n0 r0 : Nat) (h : Option Nat)
    (w entry exit ACQ REL : Geid) :
    rvwmoCatAD GD ad → gwf GR → CertZ18.agreeW3 GD.gdG GR L → gwrowGmo GR → L b →
    CertZ18.rmwLatest GR log → CertZ18.regZeroAt GR.gxImg log b n0 →
    acqAqB GD.gdG GR log b n0 → relCoversB GD.gdG GR log b n0 →
    logOf GR log → lockWordByte log b → wlpAlt log b n0 h → wlpAt log b b n0 →
    acqRow GD.gdG b ACQ →
    wprotAt log a b n0 r0 →
    (∃ v, gwritesByte GD.gdG w a v) → gcls GD.gdG w .WCplain →
    r0 < gwix GR w → gwix GR w ≤ log.length →
    (∀ v, ¬ gwritesByte GD.gdG w b v) →
    lockAcq GD.gdG b ACQ → glblIs GD.gdG ACQ lbAq →
    n0 < gwix GR ACQ → gwix GR ACQ ≤ log.length →
    lockCs GD.gdG b ACQ REL → CertZ14.np GD.gdG REL → WeakRvwmoGraph.gpo GD.gdG ACQ entry →
    gfenceCovers GD.gdG entry REL →
    gmoLt GD.gdG w entry → WeakRvwmoGraph.gpo GD.gdG ACQ exit → gmem GD.gdG exit →
    ACQ.1 ≠ w.1 →
    gmoLt GD.gdG w exit := by
  intro hcons hwfR hag hrowR hL hlat hz hAQ hRC hlog hlwb halt hwin hrow hpr hwa hcl hr0 hlew hnob
    hacq haq hn0A hleA hcs hnpREL _hpoe hfen hcross hpox hmx hhart
  have hag2 := CertZ18.agreeW2Of _ _ L hag
  have hag0 := CertZ14.agreeW0 _ _ _ hag2
  obtain ⟨-, hagW, -, hagRd, hagCo⟩ := hag
  -- the reader's acquire is in the window
  obtain ⟨va, hva, hvane⟩ := id hacq
  have hvaR : gwritesByte GR ACQ b va := (hagW ACQ b va).2 hva
  have hAwR := lockAcqGwrites GR b ACQ hwfR ⟨va, hvaR, hvane⟩
  obtain ⟨mA, hmA, hgA⟩ := logOfWrite GR log ACQ hwfR hlog hAwR hleA
  have hbA := (WeakRvwmoKillArms.gmsgByte GR ACQ mA b va hgA).2 hvaR
  have hnpA : CertZ14.np GD.gdG ACQ :=
    CertZ14.npAt _ GR _ log b n0 _ mA ACQ hwfR hag2 hlog hwin hmA (by omega) (by rw [hbA]; rfl)
      (by rw [show gwix GR ACQ - 1 + 1 = gwix GR ACQ by omega]; exact gwriteAtGwix GR ACQ hAwR)
  -- the fold is free before the reader's acquire: its member read is the latest, and free
  have hfreeA : wlpHolderAt log b n0 (gwix GR ACQ - 1) = some none := by
    obtain ⟨tA, hrdA⟩ := id hrow
    obtain ⟨tA', hrdA'⟩ :=
      hagRd.1 ACQ b tA lockFree (gwritesByteGlblW _ ACQ b va hva) hrdA
    obtain ⟨hlA, hvA⟩ := hlat ACQ b tA' lockFree (gwritesByteGlblW GR ACQ b va hvaR) hrdA'
    exact CertZ18.foldFreeOfLatest GR.gxImg log b n0 h _ tA' hlwb halt (by omega) hlA hvA
  have hspA : CertZ18.sp GD.gdG b ACQ := CertZ18.spRow _ b ACQ hnpA hrow
  obtain ⟨hwf, h6, hlv, -, -, -, -, -⟩ := hcons
  generalize GD.gdG = G at *
  have hndR := hwfR.1
  obtain ⟨vw, hvw⟩ := hwa
  have hwR : w ∈ gwrites GR := GraphFetchN2.wrR G GR _ w a vw hwfR hag0 hvw
  have hclR : gcls GR w .WCplain := hag2.2.2.1 w _ hcl (gwritesByteGlblW G w a vw hvw)
  have hnobR : ∀ v, ¬ gwritesByte GR w b v := fun v hv => hnob v ((hagW w b v).1 hv)
  obtain ⟨q, mq, hq, hlk, hs, hnz, ht, hfree, hno, ACQw, hatw, hacqwR, hixw, hhw⟩ :=
    holderAcqGraph GR log b a n0 r0 w hwfR hlog hlwb hpr hwR hr0 hlew ⟨vw, (hagW w a vw).2 hvw⟩
      hclR
  have hrA := acqRowIsR G b ACQ hrow
  have hmoAx : gmoLt G ACQ exit := acqGmoAfterC G ACQ exit h6 hpox hrA haq hmx
  obtain ⟨vq, hvq, hvqne⟩ := id hacqwR
  have hvqG : gwritesByte G ACQw b vq := (hagW ACQw b vq).1 hvq
  have hacqw : lockAcq G b ACQw := ⟨vq, hvqG, hvqne⟩
  have hnpw : CertZ14.np G ACQw :=
    CertZ14.npAt _ GR _ log b n0 q mq ACQw hwfR hag2 hlog hwin hlk hq.1 hs hatw
  have hAwwR : ACQw ∈ gwrites GR := lockAcqGwrites GR b ACQw hwfR hacqwR
  have hwne : ACQw ≠ w := fun he => hnob vq (he ▸ hvqG)
  have hpoAw : WeakRvwmoGraph.gpo G ACQw w :=
    GraphFetchN2.poOfRowR G GR _ ACQw w b a vq vw hag0 hrowR hvqG hvw hhw hwne (by omega)
  have hposA := WeakRvwmoGraph.gwixPos GR ACQ hAwR
  have hwinA : GraphFetchN2.inWin GR log n0 ACQw := ⟨by omega, by omega⟩
  by_cases heq : q = gwix GR ACQ - 1
  · exfalso
    have hA : ACQw = ACQ := gwixInj GR ACQw ACQ hndR hAwwR hAwR (by omega)
    apply hhart
    rw [← hA]
    exact hhw
  by_cases hlt : q < gwix GR ACQ - 1
  · -- WRITER-FIRST
    obtain ⟨r, R, mr, hr, hlkr, hsr, hzr, hatR, hRrel, hRix, -, hRh⟩ :=
      releaseBetweenGraph GR log b n0 q (gwix GR ACQ - 1) mq w.1 hwfR hlog hq.1 hlt hlk hs hnz ht
        hfree hfreeA
    obtain ⟨mw, hmw, hgw⟩ := logOfWrite GR log w hwfR hlog hwR hlew
    have hrp : gwix GR w - 1 ≤ r := by
      by_cases hc : r < gwix GR w - 1
      · exact absurd hzr (hno r mr ⟨hr.1, hc⟩ hlkr hsr)
      · omega
    have hrne : r ≠ gwix GR w - 1 := by
      intro hre
      rw [hre, hmw, Option.some.injEq] at hlkr
      subst hlkr
      rw [gmsgByteNone GR w mw b hgw hnobR] at hsr
      simp at hsr
    have hposw := WeakRvwmoGraph.gwixPos GR w hwR
    have hRG : lockRel G b R := (hagW R b lockFree).1 hRrel
    have hnpR : CertZ14.np G R :=
      CertZ14.npAt _ GR _ log b n0 r mr R hwfR hag2 hlog hwin hlkr (by omega) hsr hatR
    have hwRne : w ≠ R := fun he => hnob lockFree (he ▸ hRG)
    have hpowR : WeakRvwmoGraph.gpo G w R :=
      GraphFetchN2.poOfRowR G GR _ w R a b vw lockFree hag0 hrowR hvw hRG hRh.symm hwRne
        (by omega)
    have hfc : gfenceCovers G w R :=
      hRC ACQw R w hacqw hRG hwinA ⟨by omega, by omega⟩ hpoAw hpowR (gwritesByteGlblW G w a vw hvw)
    have h1 : gmoLt G w R := fenceGmoAfterC G w R h6 hfc
    have h2 : gmoLt G R ACQ :=
      gwixLtGmo G R ACQ hwf (lockRelGwrites G b R hwf hRG) (lockAcqGwrites G b ACQ hwf hacq)
        ((hagCo b R ACQ lockFree va hL hRG hva (CertZ18.spRel G b R hnpR hRG) hspA).2 (by omega))
    exact gmoLtTrans G w ACQ exit (gmoLtTrans G w R ACQ h1 h2) hmoAx
  · -- READER-FIRST
    have hltA : gwix GR ACQ - 1 < q := by omega
    have hnzA : mA.wmData ≠ wlockZero4 := fun hz => hvane (zero4Byte mA b va hz hbA)
    have htA := gmsgTid GR ACQ mA hgA
    obtain ⟨r', R', mr', hr', hlkr', hsr', -, hatR', hrelr', hixr', -, hhr'⟩ :=
      releaseBetweenGraph GR log b n0 (gwix GR ACQ - 1) q mA ACQ.1 hwfR hlog (by omega) hltA hmA
        (by rw [hbA]; rfl) hnzA htA hfreeA hfree
    obtain ⟨-, hRel, -, -, hnoin⟩ := hcs
    have hR'G : lockRel G b R' := (hagW R' b lockFree).1 hrelr'
    have hnpR' : CertZ14.np G R' :=
      CertZ14.npAt _ GR _ log b n0 r' mr' R' hwfR hag2 hlog hwin hlkr' (by omega) hsr' hatR'
    have hspR' := CertZ18.spRel G b R' hnpR' hR'G
    have hspREL := CertZ18.spRel G b REL hnpREL hRel
    have hAR'G : gwix G ACQ < gwix G R' :=
      (hagCo b ACQ R' va lockFree hL hva hR'G hspA hspR').2 (by omega)
    have hRleG : gwix G REL ≤ gwix G R' := by
      by_cases hc : gwix G R' < gwix G REL
      · exact absurd ⟨hAR'G, hc⟩ (hnoin R' lockFree hR'G hhr')
      · omega
    have hRleR : gwix GR REL ≤ gwix GR R' :=
      CertZ18.coLeR3 G GR L b REL R' lockFree lockFree hwf hagCo hL hRel hR'G hspREL hspR' hRleG
    -- the writer's acquire is SUCCESSFUL: the fold is free before it
    have hspw : CertZ18.sp G b ACQw := by
      refine ⟨hnpw, fun ⟨_, ⟨t, v, hrd, hne⟩⟩ => hne ?_⟩
      obtain ⟨t', hrd'⟩ := hagRd.1 ACQw b t v (gwritesByteGlblW G ACQw b vq hvqG) hrd
      obtain ⟨hl, hv⟩ := hlat ACQw b t' v (gwritesByteGlblW GR ACQw b vq hvq) hrd'
      rw [hixw, Nat.add_sub_cancel] at hl hv
      exact CertZ18.valFreeOfFold GR.gxImg log b n0 h q t' v hz hq.1 (by omega) hfree hl hv
    have hmoRA : gmoLt G REL ACQw :=
      gwixLtGmo G REL ACQw hwf (lockRelGwrites G b REL hwf hRel) (lockAcqGwrites G b ACQw hwf hacqw)
        ((hagCo b REL ACQw lockFree vq hL hRel hvqG hspREL hspw).2 (by omega))
    obtain ⟨hrw, haqw⟩ := hAQ ACQw hacqw hwinA
    have hmoAw : gmoLt G ACQw w :=
      acqGmoAfterC G ACQw w h6 hpoAw hrw haqw
        (WeakRvwmoGraph.glblIsWGmem G w (gwritesByteGlblW G w a vw hvw))
    have hmoeR := fenceGmoAfterC G entry REL h6 hfen
    exact absurd (gmoLtTrans G w entry w hcross
      (gmoLtTrans G entry REL w hmoeR (gmoLtTrans G REL ACQw w hmoRA hmoAw))) (gmoLtIrrefl G w)

end CatLin

end Weak
