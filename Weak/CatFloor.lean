/-
Weak: **W12b — the walk's floor kit over riscv.cat: a per-byte coherence invariant** (plan
`notes/weak-allocproc-plan.md` §C W12b; D34 (a) [OWN.13]; gate 3 of `notes/W12-spike.md`).

Lean-only, no Rocq twin.  `WeakRvwmoFloor` §4–§6 and `WeakRvwmoCert3` §2–§3 re-done so that the
floor discharge needs only the riscv.cat six arms (`gppoCat6Gmo`), not RVWMO⁻'s `gppoGmo`.

**Why the old invariant fails under cat.**  `finv`'s coh clause is `gvisUb G r (coh ws a)`:
"every write of index ≤ `coh ws a` is gmo-before `r`".  After an OWN store `w` to `a`, `coh ws a ≥
gwix w`; under cat `w` may be forwarded to the po-later read `r` and be gmo-AFTER it (no ppo
rule orders W→R; `CatLinWit.sbrfi`), so the clause is false (`CatFloorWit.sbrfiOldUbFails`).
`greadSrcUb`'s po case (a forwarded source) fails the same way.

**The new invariant `finvC G r a t`** (`r` reads byte `a` at timestamp `t`):
  * coh — PER BYTE: `cohUbA G a t (coh ws a)`: "every write TO `a` of index ≤ `coh ws a` has
    index ≤ `t`" (exactly what the floor obligation `¬ writesIn log a t _` needs).  Kept by:
    an own store to `a` (po-visible to `r`, so ≤ `t` by co-maximality — `cohOwnWrite`); an own
    read of `a` at `t'` (`cohOwnRead`: its source is po-visible, or gmo-before a po-later own
    write to `a` (RULE 1), or the two reads are ordered by RULE 2 — or the sources coincide);
    the pre-view (`cohUbAOfVis`: `gvisUb` implies it).
  * the forward bank — `fwdOk`: the bank at `b` holds `(gwix w, 0)` for the LATEST own store `w`
    to `b`.  So a FORWARDED plain read's view contribution `fwdView` is `0` (`fwdHit`: a
    po-earlier own source is the latest own store to that byte, by rule 1 + co-maximality).
  * `wVrNew`, `wVRel`, `wVrOld`, `wVwOld` — `gvisUb` as before, their hooks being RULES 5, 7, 4:
    rule 5 (`gacqPo`) and rule 4 (`gfenceCovers`) are cat arms; a read's source is gmo-before it
    unless forwarded (then `fwdView = 0`), and an RMW's source always is (RULE 1).

**Two premises the tree's cat transcription does not imply (spec notes, vacuous for kernel rows).**
  * D35 — the `wVRel` hook consumes RULE 7 for `[W.rl];po;[R.aq]`: `grelAcqGmoC G`.  riscv.cat's
    rule 7 is `[RCsc];po;[RCsc]` with RCsc = every aq/rl-annotated AMO/LR/SC, and the graph
    carries aq/rl only on atomics (LR/SC are `LLoad aq`/`LStore rl`, `projLbl`), so riscv.cat
    implies it — FAITHFUL; but `AxGraphCat.lbRcsc` demands BOTH bits, so `rvwmoCatAD` does not
    (D35 (a), RULED, is the `lbRcsc` correction — outside this item's files).  Vacuous for kernel
    rows (no rl-annotated write: release is `fence rw,w; sw`).
  * D36 (a) RULED — no plain `LLoad aq` in the reader's row before it (`noPlainAqC`): WeakMem's
    forwarded ACQUIRE load raises `wVrNew` to the forwarded store's index (`fwdViewAq`), stricter
    than cat.  True for the kernel (acquire is `amoswap.w.aq`, an RMW).

  §1  `cohUbA` and its three sources.  §2  `fwdOk`, its preservation, `fwdHit`.
  §3  `finvC`, `finvCStep`, `finvCReplay`, `floorOfGraphC`, `gtraceSnocReadConsistentC`
      (the `WeakRvwmoFloor` twins).
  §4  `cinvCStepWit`, `cinvCReplay`, `floorOfCgraphC`, `certFloorOkC`, `certReadInLog'C`,
      `cpolReadC` (the `WeakRvwmoCert3` twins).
Deviation from the plan text ("`Floor`/`Cert3` restatements"): NEW twins, the RVWMO⁻ originals
untouched (their consumers `Walk*` keep compiling; `Floor` stays single-writer for W5d-G G5).
-/
import Weak.CatLin
import Weak.WeakRvwmoCert3

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

namespace CatLin

/-! # 0. The two extra premises -/

/-- D35: rule 7 at `[W.rl];po;[R.aq]` (riscv.cat's RCsc rule on annotated atomics). -/
def grelAcqGmoC (G : Gexec) : Prop := ∀ e1 e2, grelAcq G e1 e2 → gmoLt G e1 e2

/-- D36 (a): no plain acquire load in hart `x` below position `n`. -/
def noPlainAqC (G : Gexec) (x n : Nat) : Prop :=
  ∀ k, k < n → ∀ base ts vs, gxLbl G (x, k) ≠ some (.LLoad true base ts vs)

/-- The cat hypothesis supplies the three graph facts the floor kit reads. -/
theorem catADFloor (GD : Gdexec) (ad : List (Geid × Geid)) :
    rvwmoCatAD GD ad → gwf GD.gdG ∧ gppoCat6Gmo GD.gdG ∧ gloadValue GD.gdG :=
  fun h => ⟨h.1, h.2.1, h.2.2.1⟩

/-! # 1. The per-byte coherence bound -/

theorem rdSome (G : Gexec) (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    greadsByte G e a t v → (gxLbl G e).isSome := by
  rintro ⟨l, _, _, _, _, hl, _⟩
  rw [hl]; rfl

theorem wrSome (G : Gexec) (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte G e a v → (gxLbl G e).isSome := by
  rintro ⟨l, _, _, _, hl, _⟩
  rw [hl]; rfl

/-- "Every write TO `a` of index ≤ `n` has index ≤ `t`." -/
def cohUbA (G : Gexec) (a : Int) (t n : Nat) : Prop :=
  ∀ (s : Nat) (w : Geid) (v : BitVec 8), gwriteAt G s = some w → s ≤ n → gwritesByte G w a v →
    s ≤ t

theorem cohUbAMaxcl (G : Gexec) (a : Int) (t : Nat) : maxcl (cohUbA G a t) := by
  refine ⟨?_, ?_⟩
  · intro s w v hs hle _
    have : s = 0 := by omega
    subst this
    simp [gwriteAt] at hs
  · intro n1 n2 h1 h2 s w v hs hle hw
    rcases Nat.le_total n1 n2 with h | h
    · rw [Nat.max_eq_right h] at hle; exact h2 s w v hs hle hw
    · rw [Nat.max_eq_left h] at hle; exact h1 s w v hs hle hw

/-- A gmo bound implies the per-byte bound (co-maximality). -/
theorem cohUbAOfVis (G : Gexec) (hwf : gwf G) (hlv : gloadValue G) (r : Geid) (a : Int)
    (t : Nat) (v : BitVec 8) (n : Nat) :
    greadsByte G r a t v → gvisUb G r n → cohUbA G a t n := by
  intro hr hub s w v' hs hle hw
  have hle' := (hlv r a t v hr).2 w v' hw (.inl (hub s w hs hle))
  rw [(gwriteAtInv G s w hwf.1 hs).2] at hle'
  exact hle'

/-- An own po-earlier store to `a` is VISIBLE to `r`: its index is ≤ `t`. -/
theorem cohOwnWrite (G : Gexec) (hwf : gwf G) (hlv : gloadValue G) (r : Geid) (a : Int)
    (t : Nat) (v : BitVec 8) (w : Geid) (v' : BitVec 8) :
    greadsByte G r a t v → WeakRvwmoGraph.gpo G w r → gwritesByte G w a v' →
    cohUbA G a t (gwix G w) := by
  intro hr hpo hw s w2 v2 _ hle _
  have := (hlv r a t v hr).2 w v' hw (.inr hpo)
  omega

/-- THE PER-BYTE STEP for an own po-earlier read of `a` at `t'`: `t' ≤ t` (rules 1 and 2). -/
theorem cohOwnRead (G : Gexec) (hwf : gwf G) (h6 : gppoCat6Gmo G) (hlv : gloadValue G)
    (r e : Geid) (a : Int) (t t' : Nat) (v v' : BitVec 8) :
    greadsByte G r a t v → greadsByte G e a t' v' → WeakRvwmoGraph.gpo G e r →
    cohUbA G a t t' := by
  intro hr hre hper
  suffices ht : t' ≤ t by
    intro s w v2 _ hle _
    omega
  by_cases heq : t' = t
  · omega
  rcases Nat.eq_zero_or_pos t' with h0 | hpos
  · omega
  obtain ⟨w', hwat, hwb', hvis⟩ := gloadSrcElim G t' a v' e hpos (hlv e a t' v' hre).1
  obtain ⟨hw'g, hix⟩ := gwriteAtInv G t' w' hwf.1 hwat
  have hcomax : ∀ w2 v2, gwritesByte G w2 a v2 → gvisible G w2 r → gwix G w2 ≤ t :=
    fun w2 v2 hw hv => (hlv r a t v hr).2 w2 v2 hw hv
  rcases hvis with hmo | hpo
  · by_cases hint : ∃ (j : Nat) (v'' : BitVec 8), e.2 < j ∧ j < r.2 ∧
        gwritesByte G (r.1, j) a v''
    · -- a same-hart write to `a` between: rule 1 puts it gmo-after `e`, so after `w'`
      obtain ⟨j, v'', hj1, hj2, hwj⟩ := hint
      have hpoej : WeakRvwmoGraph.gpo G e (r.1, j) :=
        ⟨hper.1, hj1, rdSome G e a t' v' hre, wrSome G _ a v'' hwj⟩
      have hmo1 : gmoLt G e (r.1, j) := h6 _ _ (.inl ⟨hpoej, a, .inr ⟨t', v', hre⟩, v'', hwj⟩)
      have hjw : (r.1, j) ∈ gwrites G := gwritesByteGwrites G _ a v'' hwf hwj
      have hlt := gmoGwixLt G w' (r.1, j) hwf hw'g hjw (gmoLtTrans G _ _ _ hmo hmo1)
      have hpojr : WeakRvwmoGraph.gpo G (r.1, j) r :=
        ⟨rfl, hj2, wrSome G _ a v'' hwj, rdSome G r a t v hr⟩
      have := hcomax (r.1, j) v'' hwj (.inr hpojr)
      omega
    · -- no write between and different sources: rule 2 orders the reads
      have hmo2 : gmoLt G e r := by
        refine h6 _ _ (.inr (.inl ⟨hper, a, t', v', t, v, hre, hr, heq, ?_⟩))
        intro w2 v2 hw2 hp1 hp2
        apply hint
        refine ⟨w2.2, v2, hp1.2.1, hp2.2.1, ?_⟩
        have hw2e : (r.1, w2.2) = w2 := Prod.ext hp2.1.symm rfl
        rw [hw2e]; exact hw2
      have := hcomax w' v' hwb' (.inl (gmoLtTrans G _ _ _ hmo hmo2))
      omega
  · have := hcomax w' v' hwb' (.inr (gpoTrans G _ _ _ hpo hper))
    omega

/-- The floor obligation from the per-byte bound. -/
theorem noWritesInOfCohUb (G : Gexec) (a : Int) (t : Nat) (log : List Wmsg) (n : Nat) :
    (∀ (s : Nat) m, 0 < s → log[s - 1]? = some m →
       ∀ b', (msgByte m b').isSome →
         ∃ w v', gwriteAt G s = some w ∧ gwritesByte G w b' v') →
    cohUbA G a t n → ¬ writesIn log a t n := by
  rintro hlog hub ⟨s, hlo, hhi, m, hm, hby⟩
  obtain ⟨w, v', hw, hwb⟩ := hlog s m (by omega) hm a hby
  have := hub s w v' hw hhi hwb
  omega

/-! # 2. The forward bank: it holds the LATEST own store per byte -/

def fwdOk (G : Gexec) (x k : Nat) (ws : Wstate) : Prop :=
  fwd0 ws ∧
  ∀ (w : Geid) (b : Int) (v : BitVec 8), w.1 = x → w.2 < k → gwritesByte G w b v →
    (∀ (j : Nat) (v' : BitVec 8), w.2 < j → j < k → ¬ gwritesByte G (x, j) b v') →
    get? ws.wFwd b = some (gwix G w, 0)

theorem fwdOkInit (G : Gexec) (x : Nat) : fwdOk G x 0 wsInit :=
  ⟨fwd0Init, fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩

/-- A step that writes nothing and keeps the bank. -/
theorem fwdOkKeep (G : Gexec) (x k : Nat) (ws ws' : Wstate) :
    fwdOk G x k ws → ws'.wFwd = ws.wFwd → (∀ b v, ¬ gwritesByte G (x, k) b v) →
    fwdOk G x (k + 1) ws' := by
  rintro ⟨h0, hb⟩ heq hnw
  refine ⟨fwd0Ext _ _ heq h0, fun w b v hx hk hw hlat => ?_⟩
  rw [heq]
  rcases Nat.lt_or_ge w.2 k with hlt | hge
  · exact hb w b v hx hlt hw (fun j v' h1 h2 => hlat j v' h1 (by omega))
  · exfalso
    have hwe : w = (x, k) := Prod.ext hx (by omega)
    subst hwe
    exact hnw b v hw

theorem storeBytesFwd (rl : Bool) (t : Nat) (as_ : List Int) (ws : Wstate) (b : Int) :
    get? (as_.foldl (fun w a => storePost w rl a t) ws).wFwd b =
      if b ∈ as_ then some (t, 0) else get? ws.wFwd b := by
  induction as_ generalizing ws with
  | nil => simp
  | cons c l ih =>
    rw [List.foldl_cons, ih]
    by_cases hb : b ∈ l
    · simp [hb]
    · by_cases hbc : b = c
      · subst hbc
        have : get? (storePost ws rl b t).wFwd b = some (t, 0) := lookupInsert
        simp [hb, this]
      · have : get? (storePost ws rl c t).wFwd b = get? ws.wFwd b := lookupInsertNe (Ne.symm hbc)
        simp [hb, hbc, this]

theorem storePostRunFwdAt (ws : Wstate) (rl : Bool) (base : Int) (n t : Nat) (b : Int) :
    get? (storePostRun ws rl base n t).wFwd b =
      if b ∈ (List.range' 0 n).map (fun j : Nat => base + (j : Int)) then some (t, 0)
      else get? ws.wFwd b := by
  rw [storePostRun, ctrlPostFwd]
  exact storeBytesFwd rl t _ ws b

/-- A store step (or an RMW's store half, after its read half `ws0`) re-banks its bytes. -/
theorem fwdOkStore (G : Gexec) (x k : Nat) (ws ws0 : Wstate) (l : Lbl) (base : Int)
    (vs : List (BitVec 8)) (rl : Bool) (tw : Nat) :
    fwdOk G x k ws → ws0.wFwd = ws.wFwd →
    gxLbl G (x, k) = some l → lbWr l = some (base, vs) → gwix G (x, k) = tw →
    fwdOk G x (k + 1) (storePostRun ws0 rl base vs.length tw) := by
  rintro ⟨h0, hb⟩ heq hl hwr htw
  refine ⟨fwd0StorePostRun _ _ _ _ _ (fwd0Ext _ _ heq h0), fun w b v hx hk hw hlat => ?_⟩
  rw [storePostRunFwdAt]
  by_cases hk' : w.2 = k
  · have hwe : w = (x, k) := Prod.ext hx hk'
    subst hwe
    obtain ⟨l', base', vs', j, hl', hwr', hv', ha'⟩ := hw
    rw [hl, Option.some.injEq] at hl'
    subst hl'
    rw [hwr, Option.some.injEq, Prod.mk.injEq] at hwr'
    obtain ⟨rfl, rfl⟩ := hwr'
    have hmem : b ∈ (List.range' 0 vs.length).map (fun j : Nat => base + (j : Int)) :=
      List.mem_map.2 ⟨j, List.mem_range'.2 ⟨j, lookup_lt_Some hv', by omega⟩, ha'⟩
    rw [if_pos hmem, htw]
  · have hlt : w.2 < k := by omega
    have hnot : b ∉ (List.range' 0 vs.length).map (fun j : Nat => base + (j : Int)) := by
      intro hmem
      obtain ⟨j, hj, hbj⟩ := elemOfMapSeq base vs.length b hmem
      obtain ⟨v', hv'⟩ := someOfIsSome (lookup_lt_is_Some_2 hj)
      exact hlat k v' (by omega) (by omega) ⟨l, base, vs, j, hl, hwr, hv', hbj.symm⟩
    rw [if_neg hnot, heq]
    exact hb w b v hx hlt hw (fun j v' h1 h2 => hlat j v' h1 (by omega))

/-- THE FORWARDING HIT: a po-earlier own source of a read at `(x,k)` is the latest own store to
that byte (rule 1 + the read's co-maximality), so the bank names it. -/
theorem fwdHit (G : Gexec) (hwf : gwf G) (h6 : gppoCat6Gmo G) (hlv : gloadValue G)
    (x k : Nat) (ws : Wstate) (b : Int) (t' : Nat) (v' : BitVec 8) (w' : Geid) :
    fwdOk G x k ws → greadsByte G (x, k) b t' v' →
    gwriteAt G t' = some w' → gwritesByte G w' b v' → WeakRvwmoGraph.gpo G w' (x, k) →
    get? ws.wFwd b = some (t', 0) := by
  rintro ⟨_, hb⟩ hre hwat hwb hpo
  obtain ⟨hw'g, hix⟩ := gwriteAtInv G t' w' hwf.1 hwat
  rw [← hix]
  apply hb w' b v' hpo.1 hpo.2.1 hwb
  intro j v'' h1 h2 hwj
  have hpo1 : WeakRvwmoGraph.gpo G w' (x, j) := ⟨hpo.1, h1, hpo.2.2.1, wrSome G _ b v'' hwj⟩
  have hmo : gmoLt G w' (x, j) := h6 _ _ (.inl ⟨hpo1, b, .inl ⟨v', hwb⟩, v'', hwj⟩)
  have hjw : (x, j) ∈ gwrites G := gwritesByteGwrites G _ b v'' hwf hwj
  have hlt := gmoGwixLt G w' (x, j) hwf hw'g hjw hmo
  have hpo2 : WeakRvwmoGraph.gpo G (x, j) (x, k) :=
    ⟨rfl, h2, wrSome G _ b v'' hwj, rdSome G _ b t' v' hre⟩
  have := (hlv (x, k) b t' v' hre).2 (x, j) v'' hwj (.inr hpo2)
  omega

theorem fwdViewCongr (ws ws0 : Wstate) (aq : Bool) (a : Int) (t : Nat) :
    ws.wFwd = ws0.wFwd → fwdView ws aq a t = fwdView ws0 aq a t := by
  intro h; unfold fwdView; rw [h]

/-- `loadRunVrOld` with the per-entry hypothesis on the FORWARDED view. -/
theorem loadFoldVrOldF (P : Nat → Prop) (aq : Bool) (vpre : Nat) (ats : List (Int × Nat))
    (ws ws0 : Wstate) :
    maxcl P → ws.wFwd = ws0.wFwd → P ws.wVrOld → P vpre →
    (∀ p ∈ ats, P (fwdView ws0 aq p.1 p.2)) →
    P (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws).wVrOld := by
  intro hcl
  induction ats generalizing ws with
  | nil => intro _ hc _ _; exact hc
  | cons p l ih =>
    intro heq hc hv hts
    apply ih (loadPostAt ws aq vpre p.1 p.2) (by rw [loadPostAtFwd]; exact heq) _ hv
      (fun q hq => hts q (List.mem_cons_of_mem _ hq))
    show P (max ws.wVrOld (max vpre (fwdView ws aq p.1 p.2)))
    rw [fwdViewCongr ws ws0 aq p.1 p.2 heq]
    exact maxclMax P _ _ hcl hc (maxclMax P _ _ hcl hv (hts p List.mem_cons_self))

theorem loadRunVrOldF (P : Nat → Prop) (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) :
    maxcl P → P ws.wVrOld → P (loadVpre ws aq) →
    (∀ (j : Nat) t, ts[j]? = some t → P (fwdView ws aq (accAddr base j) t)) →
    P (loadPostRun ws aq base ts).wVrOld := by
  intro hcl hc hv hts
  rw [loadPostRun, ctrlPostVrOld]
  apply loadFoldVrOldF P aq _ _ ws ws hcl rfl hc hv
  intro p hp
  obtain ⟨j, _, ht, he⟩ := elemOfRunAts base ts p hp
  rw [he]
  exact hts j p.2 ht

/-! # 3. The invariant and the floor over a G-trace prefix -/

def finvC (G : Gexec) (r : Geid) (a : Int) (t : Nat) (k : Nat) (ws : Wstate) : Prop :=
  fwdOk G r.1 k ws ∧
  cohUbA G a t (coh ws a) ∧
  gvisUb G r ws.wVrNew ∧
  (ahook G r k → gvisUb G r ws.wVRel) ∧
  (fhook G r k true → gvisUb G r ws.wVrOld) ∧
  (fhook G r k false → gvisUb G r ws.wVwOld)

theorem finvCInit (G : Gexec) (r : Geid) (a : Int) (t : Nat) : finvC G r a t 0 wsInit := by
  refine ⟨fwdOkInit G r.1, ?_, gvisUb0 G r, fun _ => gvisUb0 G r, fun _ => gvisUb0 G r,
    fun _ => gvisUb0 G r⟩
  rw [cohInit]; exact (cohUbAMaxcl G a t).1

/-- A label that does not write writes no byte. -/
theorem notWriteNoByte (G : Gexec) (e : Geid) (l : Lbl) :
    gxLbl G e = some l → lbIsW l = false → ∀ b v, ¬ gwritesByte G e b v := by
  rintro hl hw b v ⟨l', base, vs, j, hl', hwr, _⟩
  rw [hl, Option.some.injEq] at hl'
  subst hl'
  rw [lbWrIsW _ _ hwr] at hw
  cases hw

/-! ## 3.1 THE STEP -/

theorem finvCStep (G : Gexec) (hwf : gwf G) (h6 : gppoCat6Gmo G) (hlv : gloadValue G)
    (h7 : grelAcqGmoC G) (r : Geid) (a : Int) (t : Nat) (v : BitVec 8)
    (hrb : greadsByte G r a t v) (k : Nat) (l : Lbl) (ws : Wstate) (tw : Nat) :
    k < r.2 →
    gxLbl G (r.1, k) = some l →
    (lbIsW l = true → gwix G (r.1, k) = tw) →
    (∀ base ts vs, l ≠ .LLoad true base ts vs) →
    finvC G r a t k ws → finvC G r a t (k + 1) (WeakRvwmoFloor.lstep tw ws l) := by
  rintro hk hl htw hnoaq ⟨hfo, hcoh, hrn, hrel, hro, hwo⟩
  have hfw : fwd0 ws := hfo.1
  have hrr : glblIs G r lbIsR := by
    obtain ⟨l0, base, ts, vs, j, hl0, hrd, _⟩ := hrb
    exact ⟨l0, hl0, lbRdIsR l0 _ hrd⟩
  have hcl : maxcl (gvisUb G r) := gvisUbMaxcl G r
  have hclA : maxcl (cohUbA G a t) := cohUbAMaxcl G a t
  have hesome : (gxLbl G (r.1, k)).isSome := by rw [hl]; rfl
  have hpo : WeakRvwmoGraph.gpo G (r.1, k) r :=
    ⟨rfl, hk, hesome, WeakRvwmoFloor.hrsome G r hrr⟩
  -- the ordering arms (rules 5, 4, 7), as they apply to THIS event
  have hoaq : glblIs G (r.1, k) lbIsR → glblIs G (r.1, k) lbAq → gmoLt G (r.1, k) r :=
    fun h1 h2 => h6 _ _ (.inr (.inr (.inr (.inr (.inl
      ⟨hpo, h1, h2, WeakRvwmoFloor.hrmem G r hrr⟩)))))
  have hof : ∀ pb, fhook G r (k + 1) pb →
      (if pb then glblIs G (r.1, k) lbIsR else glblIs G (r.1, k) lbIsW) →
      gmoLt G (r.1, k) r := by
    rintro pb ⟨kf, pr, pw, sr, sw, hk1, hk2, hf, hpb, hsr⟩ hcls
    refine h6 _ _ (.inr (.inr (.inr (.inl
      ⟨pr, pw, sr, sw, ⟨rfl, hk, kf, show k < kf by omega, hk2, hf⟩, ?_, .inl ⟨hrr, hsr⟩⟩))))
    cases pb with
    | true => exact .inl ⟨hcls, hpb⟩
    | false => exact .inr ⟨hcls, hpb⟩
  have horl : ahook G r (k + 1) → glblIs G (r.1, k) lbIsW →
      glblIs G (r.1, k) lbRl → gmoLt G (r.1, k) r := by
    rintro ⟨kf, hk1, hr1, hr2, hle⟩ hw hrl
    have hpo2 : WeakRvwmoGraph.gpo G (r.1, k) (r.1, kf) := by
      obtain ⟨l', hl', _⟩ := hr1
      exact ⟨rfl, show k < kf by omega, hesome, by rw [hl']; rfl⟩
    have hlt := h7 _ _ ⟨hpo2, hw, hrl, hr1, hr2⟩
    rcases hle with heq | hlt2
    · rw [heq] at hlt; exact hlt
    · exact gmoLtTrans G _ _ _ hlt hlt2
  have hwix : lbIsW l = true → gmoLt G (r.1, k) r → gvisUb G r tw := by
    intro hw hord
    have hg : (r.1, k) ∈ gwrites G :=
      gisWGwrites G _ hwf hesome (by simp only [gisW, hl]; exact hw)
    apply gvisUbOfWrite G r tw (r.1, k) hwf _ hord
    rw [← htw hw]; exact gwriteAtGwix G _ hg
  -- the per-byte coh sources
  have hvisA : ∀ n, gvisUb G r n → cohUbA G a t n := fun n => cohUbAOfVis G hwf hlv r a t v n hrb
  have hcohW : ∀ base vs, lbWr l = some (base, vs) →
      (∃ j : Nat, j < vs.length ∧ accAddr base j = a) → cohUbA G a t tw := by
    rintro base vs hwr ⟨j, hj, hja⟩
    obtain ⟨v', hv'⟩ := someOfIsSome (lookup_lt_is_Some_2 hj)
    have hwb : gwritesByte G (r.1, k) a v' := ⟨l, base, vs, j, hl, hwr, hv', hja⟩
    have := cohOwnWrite G hwf hlv r a t v (r.1, k) v' hrb hpo hwb
    rwa [htw (lbWrIsW l _ hwr)] at this
  have hcohR : ∀ base ts vs, lbRd l = some (base, ts, vs) → vs.length = ts.length →
      ∀ (j : Nat) t', ts[j]? = some t' → accAddr base j = a → cohUbA G a t t' := by
    intro base ts vs hrd hlen j t' hj hja
    obtain ⟨v', hv'⟩ := someOfIsSome (lookup_lt_is_Some_2
      (show j < vs.length by rw [hlen]; exact lookup_lt_Some hj))
    exact cohOwnRead G hwf h6 hlv r (r.1, k) a t t' v v' hrb ⟨l, base, ts, vs, j, hl, hrd, hj, hv', hja⟩
      hpo
  cases l with
  | LIo kd base vs =>
    simp only [finvC, WeakRvwmoFloor.lstep]
    exact ⟨fwdOkKeep G r.1 k ws ws hfo rfl (notWriteNoByte G _ _ hl rfl), hcoh, hrn,
      fun hah => hrel (ahookS G r k hah), fun hfh => hro (fhookS G r k true hfh),
      fun hfh => hwo (fhookS G r k false hfh)⟩
  | LLoad aq base ts vs =>
    cases aq with
    | true => exact absurd rfl (hnoaq base ts vs)
    | false =>
    have hlen : vs.length = ts.length := WeakRvwmoFloor.gshape G hwf _ _ hl
    have hisr : glblIs G (r.1, k) lbIsR := ⟨_, hl, rfl⟩
    have hvpre : gvisUb G r (loadVpre ws false) := by
      unfold loadVpre
      exact maxclMax _ _ _ hcl hrn (gvisUb0 G r)
    simp only [finvC, WeakRvwmoFloor.lstep]
    refine ⟨fwdOkKeep G r.1 k ws _ hfo (loadPostRunFwd _ _ _ _) (notWriteNoByte G _ _ hl rfl),
      ?_, ?_, ?_, ?_, ?_⟩
    · exact loadRunCoh _ ws false base ts a hclA hfw hcoh (hvisA _ hvpre)
        (fun j t' hj hja => hcohR base ts vs rfl hlen j t' hj hja)
    · rw [loadRunVrNewPlain]; exact hrn
    · rw [loadRunVRel]; intro hah; exact hrel (ahookS G r k hah)
    · intro hfh
      have hord := hof true hfh hisr
      apply loadRunVrOldF _ ws false base ts hcl (hro (fhookS G r k true hfh)) hvpre
      intro j t' hj
      obtain ⟨v', hv'⟩ := someOfIsSome (lookup_lt_is_Some_2
        (show j < vs.length by rw [hlen]; exact lookup_lt_Some hj))
      have hre : greadsByte G (r.1, k) (accAddr base j) t' v' :=
        ⟨_, base, ts, vs, j, hl, rfl, hj, hv', rfl⟩
      cases t' with
      | zero => exact fwdViewP _ ws false _ 0 hcl hfw (gvisUb0 G r)
      | succ n =>
        obtain ⟨w', hwat, hwb, hvis⟩ := (hlv _ _ _ _ hre).1
        rcases hvis with hmo | hpow
        · exact fwdViewP _ ws false _ _ hcl hfw
            (gvisUbOfWrite G r (n + 1) w' hwf hwat (gmoLtTrans G _ _ _ hmo hord))
        · rw [fwdViewHit ws _ (n + 1) (n + 1) 0
            (fwdHit G hwf h6 hlv r.1 k ws _ (n + 1) v' w' hfo hre hwat hwb hpow) rfl]
          exact gvisUb0 G r
    · rw [loadRunVwOld]; intro hfh; exact hwo (fhookS G r k false hfh)
  | LStore rl base vs kc =>
    have hisw : glblIs G (r.1, k) lbIsW := ⟨_, hl, rfl⟩
    simp only [finvC, WeakRvwmoFloor.lstep]
    refine ⟨fwdOkStore G r.1 k ws ws _ base vs rl tw hfo rfl hl rfl (htw rfl), ?_, ?_, ?_, ?_, ?_⟩
    · exact storeRunCoh _ ws rl base vs.length tw a hclA hcoh (hcohW base vs rfl)
    · rw [storeRunVrNew]; exact hrn
    · intro hah
      cases rl with
      | true =>
        exact storeRunVRel _ ws true base _ tw hcl (hrel (ahookS G r k hah))
          (hwix rfl (horl hah hisw ⟨_, hl, rfl⟩))
      | false => rw [storeRunVRelNorl]; exact hrel (ahookS G r k hah)
    · rw [storeRunVrOld]; intro hfh; exact hro (fhookS G r k true hfh)
    · intro hfh
      exact storeRunVwOld _ ws rl base _ tw hcl (hwo (fhookS G r k false hfh))
        (hwix rfl (hof false hfh hisw))
  | LFence pr pw sr sw =>
    simp only [finvC, WeakRvwmoFloor.lstep]
    refine ⟨fwdOkKeep G r.1 k ws _ hfo (fencePostFwd _ _ _ _ _) (notWriteNoByte G _ _ hl rfl),
      hcoh, ?_, ?_, ?_, ?_⟩
    · apply fencePostVrNewPred _ ws pr pw sr sw hcl hrn
      · intro hpr hsr; exact hro ⟨k, pr, pw, sr, sw, Nat.le_refl _, hk, hl, hpr, hsr⟩
      · intro hpw hsr; exact hwo ⟨k, pr, pw, sr, sw, Nat.le_refl _, hk, hl, hpw, hsr⟩
    · intro hah; exact hrel (ahookS G r k hah)
    · intro hfh; exact hro (fhookS G r k true hfh)
    · intro hfh; exact hwo (fhookS G r k false hfh)
  | LRmw aq rl base ts rvs wvs kc =>
    obtain ⟨hne, hlenw, hlenr⟩ := WeakRvwmoFloor.gshape G hwf _ _ hl
    have hisr : glblIs G (r.1, k) lbIsR := ⟨_, hl, rfl⟩
    have hisw : glblIs G (r.1, k) lbIsW := ⟨_, hl, rfl⟩
    -- an RMW's source is gmo-before it: rule 1 closes the forwarded case
    have hsrcR : ∀ (j : Nat) t', ts[j]? = some t' → gmoLt G (r.1, k) r → gvisUb G r t' := by
      intro j t' hj hord
      have hjr : j < rvs.length := by rw [hlenr]; exact lookup_lt_Some hj
      have hjw : j < wvs.length := by rw [hlenw]; exact lookup_lt_Some hj
      obtain ⟨rv, hrv⟩ := someOfIsSome (lookup_lt_is_Some_2 hjr)
      obtain ⟨wv, hwv⟩ := someOfIsSome (lookup_lt_is_Some_2 hjw)
      have hre : greadsByte G (r.1, k) (accAddr base j) t' rv :=
        ⟨_, base, ts, rvs, j, hl, rfl, hj, hrv, rfl⟩
      have hwe : gwritesByte G (r.1, k) (accAddr base j) wv := ⟨_, base, wvs, j, hl, rfl, hwv, rfl⟩
      cases t' with
      | zero => exact gvisUb0 G r
      | succ n =>
        obtain ⟨w', hwat, hwb, hvis⟩ := (hlv _ _ _ _ hre).1
        have hmo : gmoLt G w' (r.1, k) := by
          rcases hvis with hmo | hpow
          · exact hmo
          · exact h6 _ _ (.inl ⟨hpow, accAddr base j, .inl ⟨rv, hwb⟩, wv, hwe⟩)
        exact gvisUbOfWrite G r (n + 1) w' hwf hwat (gmoLtTrans G _ _ _ hmo hord)
    have hvpre : gvisUb G r (loadVpre ws aq) := by
      unfold loadVpre
      apply maxclMax _ _ _ hcl hrn
      cases aq with
      | false => exact gvisUb0 G r
      | true => exact hrel ⟨k, Nat.le_refl _, hisr, ⟨_, hl, rfl⟩, .inr (hoaq hisr ⟨_, hl, rfl⟩)⟩
    simp only [finvC, WeakRvwmoFloor.lstep]
    refine ⟨fwdOkStore G r.1 k ws _ _ base wvs rl tw hfo (loadPostRunFwd _ _ _ _) hl rfl
      (htw rfl), ?_, ?_, ?_, ?_, ?_⟩
    · apply storeRunCoh _ _ rl base wvs.length tw a hclA
      · exact loadRunCoh _ ws aq base ts a hclA hfw hcoh (hvisA _ hvpre)
          (fun j t' hj hja => hcohR base ts rvs rfl hlenr j t' hj hja)
      · exact hcohW base wvs rfl
    · rw [storeRunVrNew]
      cases aq with
      | true =>
        exact loadRunVrNew _ ws true base ts hcl hfw hrn hvpre
          (fun j t' hj => hsrcR j t' hj (hoaq hisr ⟨_, hl, rfl⟩))
      | false => rw [loadRunVrNewPlain]; exact hrn
    · intro hah
      cases rl with
      | true =>
        apply storeRunVRel _ _ true base _ tw hcl
        · rw [loadRunVRel]; exact hrel (ahookS G r k hah)
        · exact hwix rfl (horl hah hisw ⟨_, hl, rfl⟩)
      | false => rw [storeRunVRelNorl, loadRunVRel]; exact hrel (ahookS G r k hah)
    · rw [storeRunVrOld]
      intro hfh
      exact loadRunVrOld _ ws aq base ts hcl hfw (hro (fhookS G r k true hfh)) hvpre
        (fun j t' hj => hsrcR j t' hj (hof true hfh hisr))
    · intro hfh
      apply storeRunVwOld _ _ rl base _ tw hcl
      · rw [loadRunVwOld]; exact hwo (fhookS G r k false hfh)
      · exact hwix rfl (hof false hfh hisw)

/-! ## 3.2 THE INDUCTION over the candidate's trace -/

theorem finvCReplay (G : Gexec) (hwf : gwf G) (h6 : gppoCat6Gmo G) (hlv : gloadValue G)
    (h7 : grelAcqGmoC G) (r : Geid) (a : Int) (t : Nat) (v : BitVec 8)
    (hrb : greadsByte G r a t v) (hnoaq : noPlainAqC G r.1 r.2)
    (c : Cand) (ev : Nat → Geid) (p : Nat) :
    GtracePrefix G c ev →
    gcnt r.1 c.cdTr ≤ r.2 →
    p ≤ c.cdTr.length →
    finvC G r a t (gcnt r.1 (c.cdTr.take p)) ((stt (candExec c) p).msWs r.1) := by
  intro hgt hcnt
  induction p with
  | zero =>
    intro _
    rw [candSttInit, List.take_zero]
    exact finvCInit G r a t
  | succ p ih =>
    intro hp
    obtain ⟨s, hs⟩ := someOfIsSome (lookup_lt_is_Some_2 (show p < c.cdTr.length by omega))
    have hlog : (stt (candExec c) p).msLog = cdLog c p := candElog c p (by omega)
    rw [candNext c p s hs]
    by_cases hag : s.esAg = r.1
    · rw [gcntStepEq r.1 c.cdTr p s hs hag, hag, mnextWsEq]
      have hev : ev p = (r.1, gcnt r.1 (c.cdTr.take p)) := by
        rw [gtpEvEq G c ev p s hgt hs, hag]
      have hklt : gcnt r.1 (c.cdTr.take p) < r.2 := by
        have hle := gcntTakeLe r.1 c.cdTr (p + 1)
        rw [gcntStepEq r.1 c.cdTr p s hs hag] at hle
        omega
      have hlbl : gxLbl G (r.1, gcnt r.1 (c.cdTr.take p)) = some s.esLb := by
        rw [← hev]; exact hgt.gtpLbl p s hs
      apply finvCStep G hwf h6 hlv h7 r a t v hrb (gcnt r.1 (c.cdTr.take p)) s.esLb _ _ hklt hlbl
      · intro hw; rw [← hev, hlog]; exact hgt.gtpWix p s hs hw
      · intro base ts vs heq
        exact hnoaq _ hklt base ts vs (by rw [hlbl, heq])
      · exact ih (by omega)
    · rw [gcntStepNe r.1 c.cdTr p s hs hag,
        mnextWsNe _ s.esAg s.esLb r.1 (fun h => hag h.symm)]
      exact ih (by omega)

/-! ## 3.3 THE FLOOR DISCHARGE over cat -/

theorem floorOfGraphC (G : Gexec) (c : Cand) (ev : Nat → Geid) (i : Nat) (r : Geid) (a : Int)
    (t : Nat) (v : BitVec 8) (aq : Bool) :
    gwf G → gppoCat6Gmo G → gloadValue G → grelAcqGmoC G →
    noPlainAqC G i (gcnt i c.cdTr) →
    GtracePrefix G c ev →
    r = (i, gcnt i c.cdTr) →
    greadsByte G r a t v →
    (aq = true → glblIs G r lbAq) →
    ¬ writesIn (cdLog c c.cdTr.length) a t
      (max (loadVpre ((stt (candExec c) c.cdTr.length).msWs i) aq)
           (coh ((stt (candExec c) c.cdTr.length).msWs i) a)) := by
  intro hwf h6 hlv h7 hnoaq hgt hr hrb haq
  have hrr : glblIs G r lbIsR := by
    obtain ⟨l, base, ts, vs, j, hl, hrd, _⟩ := hrb
    exact ⟨l, hl, lbRdIsR l _ hrd⟩
  subst hr
  have hcl : maxcl (gvisUb G (i, gcnt i c.cdTr)) := gvisUbMaxcl G _
  have hclA : maxcl (cohUbA G a t) := cohUbAMaxcl G a t
  have hinv := finvCReplay G hwf h6 hlv h7 _ a t v hrb hnoaq c ev c.cdTr.length hgt
    (Nat.le_refl _) (Nat.le_refl _)
  rw [take_ge (l := c.cdTr) (Nat.le_refl _)] at hinv
  obtain ⟨_, hcoh, hrn, hrel, _, _⟩ := hinv
  apply noWritesInOfCohUb G a t _ _ (gtpLogWrites G c ev hgt)
  apply maxclMax _ _ _ hclA _ hcoh
  apply cohUbAOfVis G hwf hlv _ a t v _ hrb
  unfold loadVpre
  apply maxclMax _ _ _ hcl hrn
  cases aq with
  | false => exact gvisUb0 G _
  | true => exact hrel ⟨_, Nat.le_refl _, hrr, haq rfl, .inl rfl⟩

/-- `gtraceSnocReadConsistent` over cat. -/
theorem gtraceSnocReadConsistentC (G : Gexec) (c : Cand) (ev : Nat → Geid) (i : Nat)
    (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    gwf G → gppoCat6Gmo G → gloadValue G → grelAcqGmoC G →
    noPlainAqC G i (gcnt i c.cdTr) →
    srvwmoConsistent c →
    GtracePrefix G c ev →
    gxLbl G (i, gcnt i c.cdTr) = some (.LLoad aq base ts vs) →
    (∀ (j : Nat) t, ts[j]? = some t → t ≤ (cdLogEnd c).length) →
    srvwmoConsistent (candSnoc c ⟨i, .LLoad aq base ts vs⟩) ∧
    GtracePrefix G (candSnoc c ⟨i, .LLoad aq base ts vs⟩) (evSnoc c ev (i, gcnt i c.cdTr)) := by
  intro hwf h6 hlv h7 hnoaq hc hgt hl hsrc
  have hlen : vs.length = ts.length := WeakRvwmoFloor.gshape G hwf _ _ hl
  have hrb : ∀ (j : Nat) t v, ts[j]? = some t → vs[j]? = some v →
      greadsByte G (i, gcnt i c.cdTr) (accAddr base j) t v :=
    fun j t v hj hv => ⟨_, base, ts, vs, j, hl, rfl, hj, hv, rfl⟩
  refine ⟨?_, gtracePrefixSnoc G c ev i _ hwf hgt hl (fun h => by simp [lbIsW] at h)⟩
  apply snocReadConsistent c i aq base ts vs hc
  refine ⟨hlen, ?_, ?_⟩
  · intro j t v hj hv
    have hval := (hlv _ _ _ _ (hrb j t v hj hv)).1
    cases t with
    | zero => rw [logByte0, hgt.gtpImg]; exact hval
    | succ n =>
      obtain ⟨w, hw, hwb, _⟩ := hval
      exact gtpLogByte G c ev hgt (n + 1) w (accAddr base j) v (by omega) (hsrc j (n + 1) hj)
        hw hwb
  · intro j t hj
    have hjlt : j < vs.length := by rw [hlen]; exact lookup_lt_Some hj
    obtain ⟨v, hv⟩ := someOfIsSome (lookup_lt_is_Some_2 hjlt)
    exact floorOfGraphC G c ev i (i, gcnt i c.cdTr) (accAddr base j) t v aq hwf h6 hlv h7 hnoaq
      hgt rfl (hrb j t v hj hv) (fun h => by subst h; exact ⟨_, hl, rfl⟩)

/-! # 4. The certified prefix (`WeakRvwmoCert3` §2–§3 over cat) -/

/-- THE WITNESS STEP over cat: as `cinvStepWit`, plus "`G`'s own event there writes nothing"
(a witness or poisoned position replaces a READ). -/
theorem cinvCStepWit (G : Gexec) (hwf : gwf G) (hlv : gloadValue G)
    (r : Geid) (a : Int) (t : Nat) (v : BitVec 8) (hrb : greadsByte G r a t v)
    (k : Nat) (ws : Wstate) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) (tw : Nat) :
    (∀ (j : Nat) t', ts[j]? = some t' → accAddr base j ≠ a) →
    (fhook G r (k + 1) true → ∀ (j : Nat) t', ts[j]? = some t' → gvisUb G r t') →
    (∀ b v', ¬ gwritesByte G (r.1, k) b v') →
    finvC G r a t k ws →
    finvC G r a t (k + 1) (WeakRvwmoFloor.lstep tw ws (.LLoad false base ts vs)) := by
  rintro hdisj hub hnw ⟨hfo, hcoh, hrn, hrel, hro, hwo⟩
  have hfw : fwd0 ws := hfo.1
  have hcl : maxcl (gvisUb G r) := gvisUbMaxcl G r
  have hclA : maxcl (cohUbA G a t) := cohUbAMaxcl G a t
  have hvpre : gvisUb G r (loadVpre ws false) := by
    unfold loadVpre
    exact maxclMax _ _ _ hcl hrn (gvisUb0 G r)
  simp only [finvC, WeakRvwmoFloor.lstep]
  refine ⟨fwdOkKeep G r.1 k ws _ hfo (loadPostRunFwd _ _ _ _) hnw, ?_, ?_, ?_, ?_, ?_⟩
  · exact loadRunCoh _ ws false base ts a hclA hfw hcoh
      (cohUbAOfVis G hwf hlv r a t v _ hrb hvpre) (fun j t' hj hja => absurd hja (hdisj j t' hj))
  · rw [loadRunVrNewPlain]; exact hrn
  · rw [loadRunVRel]; intro hah; exact hrel (ahookS G r k hah)
  · intro hfh
    exact loadRunVrOld _ ws false base ts hcl hfw (hro (fhookS G r k true hfh)) hvpre (hub hfh)
  · rw [loadRunVwOld]; intro hfh; exact hwo (fhookS G r k false hfh)

theorem cinvCReplay (G : Gexec) (hwf : gwf G) (h6 : gppoCat6Gmo G) (hlv : gloadValue G)
    (h7 : grelAcqGmoC G) (r : Geid) (a : Int) (t : Nat) (v : BitVec 8)
    (hrb : greadsByte G r a t v) (hnoaq : noPlainAqC G r.1 r.2)
    (c : Cand) (ev : Nat → Geid) (W : Geid → Prop) (p : Nat) :
    CtracePrefix G c ev W →
    WPolocClosed G W →
    witFenceUb G c ev W r →
    poisOkAt G c ev r →
    ¬ W r →
    gcnt r.1 c.cdTr ≤ r.2 →
    p ≤ c.cdTr.length →
    finvC G r a t (gcnt r.1 (c.cdTr.take p)) ((stt (candExec c) p).msWs r.1) := by
  intro hgt hpc hwub hpd hnW hcnt
  have hrr : glblIs G r lbIsR := by
    obtain ⟨l, base, ts, vs, j, hl, hrd, _⟩ := hrb
    exact ⟨l, hl, lbRdIsR l _ hrd⟩
  have hra : gaccesses G r a := .inr ⟨t, v, hrb⟩
  induction p with
  | zero =>
    intro _
    rw [candSttInit, List.take_zero]
    exact finvCInit G r a t
  | succ p ih =>
    intro hp
    obtain ⟨s, hs⟩ := someOfIsSome (lookup_lt_is_Some_2 (show p < c.cdTr.length by omega))
    have hlog : (stt (candExec c) p).msLog = cdLog c p := candElog c p (by omega)
    rw [candNext c p s hs]
    by_cases hag : s.esAg = r.1
    case neg =>
      rw [gcntStepNe r.1 c.cdTr p s hs hag,
        mnextWsNe _ s.esAg s.esLb r.1 (fun h => hag h.symm)]
      exact ih (by omega)
    rw [gcntStepEq r.1 c.cdTr p s hs hag, hag, mnextWsEq]
    have hev : ev p = (r.1, gcnt r.1 (c.cdTr.take p)) := by
      rw [ctpEvEq G c ev W p s hgt hs, hag]
    have hklt : gcnt r.1 (c.cdTr.take p) < r.2 := by
      have hle := gcntTakeLe r.1 c.cdTr (p + 1)
      rw [gcntStepEq r.1 c.cdTr p s hs hag] at hle
      omega
    have hIH := ih (by omega)
    rcases hgt.ctpStep p s hs with ⟨_, hlblp⟩ | ⟨hW, hwitp⟩ | hpois
    · -- A TRUE STEP
      have hlbl : gxLbl G (r.1, gcnt r.1 (c.cdTr.take p)) = some s.esLb := by
        rw [← hev]; exact hlblp
      apply finvCStep G hwf h6 hlv h7 r a t v hrb _ s.esLb _ _ hklt hlbl
      · intro hw; rw [← hev, hlog]; exact hgt.ctpWix p s hs hw
      · intro base ts vs heq
        exact hnoaq _ hklt base ts vs (by rw [hlbl, heq])
      · exact hIH
    · -- A WITNESS (G's event there is a plain load: it writes nothing)
      obtain ⟨base, n, ts0, vs0, hlg, hn, hlb⟩ := hwitp
      rw [hlb, latestReadLbl]
      apply cinvCStepWit G hwf hlv r a t v hrb _ _ base _ _ _ ?_ ?_ ?_ hIH
      · intro j t' hj heq
        obtain ⟨hjn, _⟩ := lrdTsLookup (cdPre c p) base n j t' hj
        have hlen0 : vs0.length = ts0.length := WeakRvwmoFloor.gshape G hwf _ _ hlg
        obtain ⟨t0, ht0⟩ := someOfIsSome (lookup_lt_is_Some_2 (show j < ts0.length by omega))
        obtain ⟨v0, hv0⟩ := someOfIsSome (lookup_lt_is_Some_2 (show j < vs0.length by omega))
        have hacc : gaccesses G (ev p) a :=
          .inr ⟨t0, v0, .LLoad false base ts0 vs0, base, ts0, vs0, j, hlg, rfl, ht0, hv0, heq⟩
        have hpo : WeakRvwmoGraph.gpo G (ev p) r := by
          refine ⟨by rw [hev], by rw [hev]; exact hklt, by rw [hlg]; rfl,
            WeakRvwmoFloor.hrsome G r hrr⟩
        exact hnW (hpc (ev p) r a hW hpo hacc hra hrr)
      · intro hfh j t' hj
        obtain ⟨_, rfl⟩ := lrdTsLookup (cdPre c p) base n j t' hj
        rw [cdPreLog]
        apply gvisUbDown G r _ (cdLog c p).length (latestTsLe _ _)
        exact hwub p s hs hW (by rw [hev]) (by rw [hev]; exact hfh)
      · rw [← hev]; exact notWriteNoByte G _ _ hlg rfl
    · -- A POISONED STEP (G's event there is not a write)
      obtain ⟨hdisj, hub⟩ := hpd p s hs hpois (by rw [hev])
      obtain ⟨⟨lb0, hlb0, hw0⟩, ⟨base, n, hlb⟩, _, _⟩ := hpois
      rw [hlb, latestReadLbl]
      apply cinvCStepWit G hwf hlv r a t v hrb _ _ base _ _ _ ?_ ?_ ?_ hIH
      · intro j t' hj heq
        apply hdisj a hra
        exact ⟨base, lrdTs (cdPre c p) base n, lrdVs (cdPre c p) base n, by rw [hlb]; rfl,
          j, t', hj, heq⟩
      · intro hfh j t' hj
        obtain ⟨_, rfl⟩ := lrdTsLookup (cdPre c p) base n j t' hj
        rw [cdPreLog]
        apply gvisUbDown G r _ (cdLog c p).length (latestTsLe _ _)
        exact hub (by rw [hev]; exact hfh)
      · rw [← hev]; exact notWriteNoByte G _ _ hlb0 hw0

theorem floorOfCgraphC (G : Gexec) (c : Cand) (ev : Nat → Geid) (W : Geid → Prop) (i : Nat)
    (r : Geid) (a : Int) (t : Nat) (v : BitVec 8) (aq : Bool) :
    gwf G → gppoCat6Gmo G → gloadValue G → grelAcqGmoC G →
    noPlainAqC G i (gcnt i c.cdTr) →
    CtracePrefix G c ev W →
    WPolocClosed G W →
    witFenceUb G c ev W r →
    poisOkAt G c ev r →
    ¬ W r →
    r = (i, gcnt i c.cdTr) →
    greadsByte G r a t v →
    (aq = true → glblIs G r lbAq) →
    ¬ writesIn (cdLog c c.cdTr.length) a t
      (max (loadVpre ((stt (candExec c) c.cdTr.length).msWs i) aq)
           (coh ((stt (candExec c) c.cdTr.length).msWs i) a)) := by
  intro hwf h6 hlv h7 hnoaq hgt hpc hwub hpd hnW hr hrb haq
  have hrr : glblIs G r lbIsR := by
    obtain ⟨l, base, ts, vs, j, hl, hrd, _⟩ := hrb
    exact ⟨l, hl, lbRdIsR l _ hrd⟩
  subst hr
  have hcl : maxcl (gvisUb G (i, gcnt i c.cdTr)) := gvisUbMaxcl G _
  have hclA : maxcl (cohUbA G a t) := cohUbAMaxcl G a t
  have hinv := cinvCReplay G hwf h6 hlv h7 _ a t v hrb hnoaq c ev W c.cdTr.length hgt hpc hwub
    hpd hnW (Nat.le_refl _) (Nat.le_refl _)
  rw [take_ge (l := c.cdTr) (Nat.le_refl _)] at hinv
  obtain ⟨_, hcoh, hrn, hrel, _, _⟩ := hinv
  apply noWritesInOfCohUb G a t _ _ (ctpLogWrites G c ev W hgt)
  apply maxclMax _ _ _ hclA _ hcoh
  apply cohUbAOfVis G hwf hlv _ a t v _ hrb
  unfold loadVpre
  apply maxclMax _ _ _ hcl hrn
  cases aq with
  | false => exact gvisUb0 G _
  | true => exact hrel ⟨_, Nat.le_refl _, hrr, haq rfl, .inl rfl⟩

theorem certFloorOkC (G : Gexec) (c : Cand) (ev : Nat → Geid) (W : Geid → Prop) (i : Nat)
    (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    gwf G → gppoCat6Gmo G → gloadValue G → grelAcqGmoC G →
    noPlainAqC G i (gcnt i c.cdTr) →
    CtracePrefix G c ev W →
    WPolocClosed G W →
    witFenceUb G c ev W (i, gcnt i c.cdTr) →
    poisOkAt G c ev (i, gcnt i c.cdTr) →
    ¬ W (i, gcnt i c.cdTr) →
    gxLbl G (i, gcnt i c.cdTr) = some (.LLoad aq base ts vs) →
    floorOk c i aq base ts := by
  intro hwf h6 hlv h7 hnoaq hgt hpc hwub hpd hnW hl j t hj
  have hlen : vs.length = ts.length := WeakRvwmoFloor.gshape G hwf _ _ hl
  obtain ⟨v, hv⟩ := someOfIsSome (lookup_lt_is_Some_2
    (show j < vs.length by rw [hlen]; exact lookup_lt_Some hj))
  exact floorOfCgraphC G c ev W i _ (accAddr base j) t v aq hwf h6 hlv h7 hnoaq hgt hpc hwub hpd
    hnW rfl ⟨.LLoad aq base ts vs, base, ts, vs, j, hl, rfl, hj, hv, rfl⟩
    (fun h => by subst h; exact ⟨.LLoad true base ts vs, hl, rfl⟩)

theorem certReadInLog'C (G : Gexec) (c : Cand) (ev : Nat → Geid) (W : Geid → Prop) (i : Nat)
    (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    gwf G → gppoCat6Gmo G → gloadValue G → grelAcqGmoC G →
    noPlainAqC G i (gcnt i c.cdTr) →
    CtracePrefix G c ev W →
    WPolocClosed G W →
    witFenceUb G c ev W (i, gcnt i c.cdTr) →
    poisOkAt G c ev (i, gcnt i c.cdTr) →
    ¬ W (i, gcnt i c.cdTr) →
    gxLbl G (i, gcnt i c.cdTr) = some (.LLoad aq base ts vs) →
    srcInLog c base ts vs →
    mstepOk (candLastSt c) i (.LLoad aq base ts vs) :=
  fun hwf h6 hlv h7 hnoaq hgt hpc hwub hpd hnW hl hsrc =>
    certReadInLog c i aq base ts vs hsrc
      (certFloorOkC G c ev W i aq base ts vs hwf h6 hlv h7 hnoaq hgt hpc hwub hpd hnW hl)

/-- `cpolRead` over cat, at the certification context `cpolCtx`. -/
theorem cpolReadC (G : Gexec) (W : Geid → Prop) (x : Nat) (c : Cand) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) :
    gwf G → gppoCat6Gmo G → gloadValue G → grelAcqGmoC G →
    noPlainAqC G x (gcnt x c.cdTr) →
    WPolocClosed G W → cpolCtx G W x c →
    ¬ W (x, gcnt x c.cdTr) →
    gxLbl G (x, gcnt x c.cdTr) = some (.LLoad aq base ts vs) →
    srcInLog c base ts vs →
    mstepOk (candLastSt c) x (.LLoad aq base ts vs) := by
  rintro hwf h6 hlv h7 hnoaq hpc ⟨ev, hgt, hwub, hpd⟩ hnW hl hsrc
  exact certReadInLog'C G c ev W x aq base ts vs hwf h6 hlv h7 hnoaq hgt hpc hwub
    (poisOkAtOfHart G c ev x hpd) hnW hl hsrc

/-- … and from the chain's hypothesis. -/
theorem cpolReadCatAD (GD : Gdexec) (ad : List (Geid × Geid)) (W : Geid → Prop) (x : Nat)
    (c : Cand) (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    rvwmoCatAD GD ad → grelAcqGmoC GD.gdG → noPlainAqC GD.gdG x (gcnt x c.cdTr) →
    WPolocClosed GD.gdG W → cpolCtx GD.gdG W x c →
    ¬ W (x, gcnt x c.cdTr) →
    gxLbl GD.gdG (x, gcnt x c.cdTr) = some (.LLoad aq base ts vs) →
    srcInLog c base ts vs →
    mstepOk (candLastSt c) x (.LLoad aq base ts vs) :=
  fun hc h7 hnoaq =>
    cpolReadC GD.gdG W x c aq base ts vs hc.1 hc.2.1 hc.2.2.1 h7 hnoaq

end CatLin

end Weak
