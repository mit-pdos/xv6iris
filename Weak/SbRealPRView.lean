/-
Weak: **allocproc route P, row P-W6 on the S-R walk — `R-view` and THE CUT OF A STALE LOAD** (the consumer
half of `SimRelP`'s view conjunct; `Weak/SbRealPView.lean` §3 (a)–(c); `PROGRESS-PW6.md` design check "LOADS
ARE STALE").  Lean-only, no Rocq twin.  A PRIMED TWIN: nothing registered imports this file.

**Spec first.**  RVWMO's load value axiom (`gloadValue`): each byte of a load reads the gmo-latest store among
those gmo-before it and the hart's po-earlier ones.  So (a) a foreign source is gmo-before the load, every
store to the byte co-after the source is gmo-AFTER the load (from-reads, `frLtW`); (c) no own po-earlier store
to the byte is co-after the source.  The S-R walk realizes the load at GF's timestamps (`SbOrdR.srGate`,
sources landed) with the twin's views DOMINATED (`SbDom.DomInv` → `SpikeSR.DomAt`: the twin's floor and the
byte's coherence floor below every store to the byte co-after the source).

**`RView G w σ cpu`** (MachCSL's floors DOMINATED as the twin's are, in `SbDom`'s GF vocabulary; `SimRelP`'s view
conjunct):
* `tvD`/`rvD`/`pubD`/`cohD` — MachCSL's floor `tv`, read watermark `rv`, the hart's last landed store position
  and each coherence floor are below the from-read successors of the future loads they constrain (`dR`,
  `dF true`, `dF false`, `dC`: the components `SbDom.DomInv` proves for the twin's `wVrNew`, `wVrOld`,
  `wVwOld`, `coh`);
* `cohSrc` — a non-zero MachCSL coherence floor is the position of a FOREIGN landed store to that byte (a
  load's foreign source, `LoadSrcs.stampAt`);
* `cohFwd` — a byte an own PENDING store covers has floor `0` (its issue reset it, `HRead.resetCoh`; loads of
  it read own entries, stamp `0`);
* `cohOwn` — a non-zero floor is above every own realized store to the byte (CoWR at the load that set it).

**`cutBytesOfRView`**: at a non-exempt plain-load head of an S-R walk state (`PInvR`, the gate `srGate`), with
`rmemP` and `RView`, there is a GF cut `T ≤ ltop` with `SbRealPView.CutBytes` — so the realizing read
`SbRealPView.loadLblPR` applies.  `T` is the largest FOREIGN non-forwarded source; the cross-byte coherence
floors are below it by `cohSrc` + `cohD` (a floor is a store position to its byte below the head's from-read
successors there, hence at most the source) and `cohOwn` (an own source forces floor `0`).

The preservation of `RView` along the realization's rows is the next item (`PROGRESS-PW6.md`).

Spec: FAITHFUL (theorems about the existing models; riscv.cat's load value, rules 1 and 2 through `CatH`; no
xv6 fact, no new named input).  Lean-only helpers `SbRealPRView.*`.
-/
import Weak.SbRealPView
import Weak.SbOrdR
import Weak.SbHeadHop

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl PfStepTsoMem SbRealP SbRealPView

namespace SbRealPRView

open SbWalk SbAgree SbReplay SbOrd SpikeSP SbDom SpikeSR

/-! # 1. `R-view` -/

/-- **`R-view` at hart `cpu`** (GF-level, `SbDom`'s vocabulary at the row's realized length `len`): MachCSL's
floor `tv` below the from-read successors of every future load (`dR`), its read watermark `rv` and its last
landed store's position below those of every future load behind a delivering fence (`dF true` / `dF false`),
each coherence floor below those of every future load of its byte (`dC`); and the provenance of the coherence
floors (`cohSrc`, `cohFwd`, `cohOwn`). -/
structure RView (G : Gexec) (w : WS) (σ : MState) (cpu : CPU) : Prop where
  tvD : dR G (hartAgent cpu) (w.rows (hartAgent cpu)).length (σ.tv cpu)
  rvD : dF G (hartAgent cpu) (w.rows (hartAgent cpu)).length true (σ.hr cpu).rv
  pubD : dF G (hartAgent cpu) (w.rows (hartAgent cpu)).length false (ownPubL (hartAgent cpu) σ.log σ.llog)
  cohD : ∀ a : PAddr, dC G (hartAgent cpu) (w.rows (hartAgent cpu)).length (paZ a) ((σ.hr cpu).coh a)
  cohSrc : ∀ a : PAddr, (σ.hr cpu).coh a ≠ 0 → ∃ m, w.σ.ms.msLog[(σ.hr cpu).coh a - 1]? = some m ∧
    (msgByte m (paZ a)).isSome ∧ m.wmTid ≠ some (hartAgent cpu)
  cohFwd : ∀ a : PAddr, (∃ e ∈ w.σ.sb (hartAgent cpu), (msgByte e.msg (paZ a)).isSome) → (σ.hr cpu).coh a = 0
  cohOwn : ∀ a : PAddr, (σ.hr cpu).coh a ≠ 0 → ∀ (W : Geid) (u : BitVec 8), W.1 = hartAgent cpu →
    W.2 < (w.rows W.1).length → gwritesByte G W (paZ a) u → gwix G W < (σ.hr cpu).coh a

/-! # 2. Helpers -/

/-- A finite maximum over the indices satisfying a predicate. -/
theorem finMax (P : Nat → Prop) (f : Nat → Nat) : ∀ n : Nat,
    ∃ T, (∀ j, j < n → P j → f j ≤ T) ∧ (T = 0 ∨ ∃ k, k < n ∧ P k ∧ T = f k)
  | 0 => ⟨0, fun j hj => absurd hj (Nat.not_lt_zero _), .inl rfl⟩
  | n + 1 => by
    obtain ⟨T, hT1, hT2⟩ := finMax P f n
    by_cases hP : P n
    · by_cases hle : f n ≤ T
      · refine ⟨T, fun j hj hPj => ?_, ?_⟩
        · rcases Nat.lt_or_ge j n with h | h
          · exact hT1 j h hPj
          · have : j = n := by omega
            subst this; exact hle
        · rcases hT2 with h | ⟨k, hk, hPk, hTk⟩
          · exact .inl h
          · exact .inr ⟨k, by omega, hPk, hTk⟩
      · refine ⟨f n, fun j hj hPj => ?_, .inr ⟨n, by omega, hP, rfl⟩⟩
        rcases Nat.lt_or_ge j n with h | h
        · have := hT1 j h hPj; omega
        · have : j = n := by omega
          subst this; exact Nat.le_refl _
    · refine ⟨T, fun j hj hPj => ?_, ?_⟩
      · rcases Nat.lt_or_ge j n with h | h
        · exact hT1 j h hPj
        · have : j = n := by omega
          subst this; exact absurd hPj hP
      · rcases hT2 with h | ⟨k, hk, hPk, hTk⟩
        · exact .inl h
        · exact .inr ⟨k, by omega, hPk, hTk⟩

/-- A member write message's author is its row. -/
theorem wmsgTid (rows : Nat → List Lbl) (e : Geid) (m : Wmsg) (h : wmsgOf rows e = some m) :
    m.wmTid = some e.1 := by
  unfold wmsgOf at h
  cases hr : (rows e.1)[e.2]? with
  | none => rw [hr] at h; cases h
  | some l =>
    rw [hr] at h
    dsimp only at h
    cases hw : lbWr l with
    | none => rw [hw] at h; cases h
    | some q => rw [hw] at h; cases h; rfl

/-- **A LOG POSITION IS A LANDED GF WRITE** (S-P): position `t'` of the twin's log is GF's `t'`-th write,
landed, authored by its row, with GF's bytes. -/
theorem logPos {img : Image} {G : Gexec} {X : Geid → Prop} {w : WS} (hI : Inv img w) (hpf : pfx G X w)
    (hW : wrW w <+: gwrites G) (hnd : G.gxGmo.Nodup) (t' : Nat) (m : Wmsg) (ht : 0 < t')
    (hm : w.σ.ms.msLog[t' - 1]? = some m) :
    ∃ n, n ∈ wrW w ∧ (gwrites G)[t' - 1]? = some n ∧ gwix G n = t' ∧ m.wmTid = some n.1 ∧
      ∀ a u, msgByte m a = some u ↔ gwritesByte G n a u := by
  obtain ⟨hlen, hat⟩ := logAt img G w hI hW
  have hlt : t' - 1 < (wrW w).length := by rw [← hlen]; exact lookup_lt_Some hm
  obtain ⟨e, m0, he, hm0, hl⟩ := hat (t' - 1) hlt
  rw [hm, Option.some.injEq] at hl
  subst hl
  have hew : e ∈ wrW w := by
    obtain ⟨T, hT⟩ := hW
    have : (wrW w)[t' - 1]? = some e := by
      rw [← hT, List.getElem?_append_left hlt] at he; exact he
    exact List.mem_of_getElem? this
  refine ⟨e, hew, he, ?_, wmsgTid w.rows e m hm0, msgOfRow G X w hpf e m hm0⟩
  have := gwixOfLookup G (t' - 1) e hnd he
  omega

/-- A forwarded byte has a covering pending entry. -/
theorem fwdCover (sb : List SbEnt) (a : Int) (v : BitVec 8) (h : SbCand.fwdByte sb a = some v) :
    ∃ e ∈ sb, (msgByte e.msg a).isSome := by
  refine Classical.byContradiction fun hn => ?_
  have hnone : ∀ e ∈ sb, msgByte e.msg a = none := by
    intro e he
    cases hs : msgByte e.msg a with
    | none => rfl
    | some _ => exact absurd ⟨e, he, by rw [hs]; rfl⟩ hn
  rw [fwdByteNone sb a hnone] at h
  cases h

/-! # 3. The cut of a stale load -/

/-- Log position `t` is an own store of agent `x`. -/
def ownAt (log : List Wmsg) (x t : Nat) : Prop := 0 < t ∧ ∃ m, log[t - 1]? = some m ∧ m.wmTid = some x

theorem getDOf (ts : List Nat) (k tk : Nat) (h : ts[k]? = some tk) : ts.getD k 0 = tk := by
  rw [List.getD_eq_getElem?_getD, h]; rfl

/-- **THE CUT OF A STALE LOAD**: at a non-exempt plain-load head of an S-R walk state, with `rmemP` and `R-view`,
there is a GF cut `T ≤ ltop` for which the S-R walk's per-byte cut holds. -/
theorem cutBytesOfRView {N : Nat} {img : Image} {X : Geid → Prop} {dev : List Geid} (G : Gexec) (w : WS)
    (σ : MState) (cpu : CPU) (hP : SbOrdR.PInvR N img G X dev w) (hc : CatH G) (himg : G.gxImg = img)
    (hnd : G.gxGmo.Nodup) (hR : rmemP img w.σ σ) (hV : RView G w σ cpu)
    (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G (hd w (hartAgent cpu)) = some (LLoad aq base ts vs))
    (hg : SbOrdR.srGate G w (hartAgent cpu) aq base ts vs)
    (pa : PAddr) (n : Nat) (hbase : base = paZ pa) (hnw : pa.toNat + n ≤ 2 ^ 64) (hlen : ts.length = n) :
    ∃ T, T ≤ σ.ltop ∧ CutBytes w.σ σ cpu pa n base ts vs T ∧
      (∀ i, i < n → (σ.hr cpu).coh (pa + BitVec.ofNat 64 i) ≤ T) ∧
      (T = 0 ∨ ∃ s, s ∈ gwrites G ∧ gwix G s = T ∧ gmoLt G s (hd w (hartAgent cpu))) := by
  have hI := hP.inv
  have hpf := hP.pf
  have hW := hP.spw
  have hfut : fut G (hartAgent cpu) (w.rows (hartAgent cpu)).length (hd w (hartAgent cpu)) :=
    ⟨rfl, Nat.le_refl _, aq, base, ts, vs, hl⟩
  have hvl : vs.length = ts.length := lblShape G hc.wf _ _ hl
  obtain ⟨hlogLen, -⟩ := logAt img G w hI hW
  have hltop : σ.ltop = (wrW w).length := by
    have h1 := congrArg List.length hR.2.1
    simp only [List.length_map, landAuthors] at h1
    show σ.llog.length = _
    rw [← h1, hlogLen]
  obtain ⟨T, hT1, hT2⟩ := finMax (fun j => SbCand.fwdByte (w.σ.sb (hartAgent cpu)) (accAddr base j) = none ∧
    ¬ ownAt w.σ.ms.msLog (hartAgent cpu) (ts.getD j 0)) (fun j => ts.getD j 0) n
  -- a source read by the head
  have hsrc : ∀ (j t : Nat) (v : BitVec 8), ts[j]? = some t → vs[j]? = some v →
      greadsByte G (hd w (hartAgent cpu)) (accAddr base j) t v :=
    fun j t v htj hvj => ⟨_, base, ts, vs, j, hl, rfl, htj, hvj, rfl⟩
  -- its log byte (S-P: the landed source's message)
  have hlogB : ∀ (j t : Nat) (v : BitVec 8), ts[j]? = some t → vs[j]? = some v → t ≤ (wrW w).length →
      logByte w.σ.ms.msImg w.σ.ms.msLog t (accAddr base j) = some v := by
    intro j t v htj hvj htw
    rw [hI.img]
    exact (staleStep img G X w hI hpf hW hnd hc.lv himg _ _ t v (hsrc j t v htj hvj) htw 0
      (fun n0 u hn _ => by have := gwixPos G n0 (gwritesOf G n0 _ u hc.wf hn); omega)).1
  -- a non-own landed source is gmo-before the head
  have hgmoSrc : ∀ (j t : Nat) (v : BitVec 8), ts[j]? = some t → vs[j]? = some v → 0 < t → t ≤ (wrW w).length →
      ¬ ownAt w.σ.ms.msLog (hartAgent cpu) t →
      ∃ s, (gwrites G)[t - 1]? = some s ∧ gwix G s = t ∧ gmoLt G s (hd w (hartAgent cpu)) := by
    intro j t v htj hvj ht0 htw hno
    obtain ⟨m, hm⟩ : ∃ m, w.σ.ms.msLog[t - 1]? = some m := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨s, -, hs, hgw, htid, -⟩ := logPos hI hpf hW hnd t m ht0 hm
    refine ⟨s, hs, hgw, ?_⟩
    have hwa : gwriteAt G t = some s := by
      cases t with
      | zero => omega
      | succ i => exact hs
    rcases srcCases hc _ _ t v s (hsrc j t v htj hvj) hwa with h | h
    · exact h
    · exfalso
      apply hno
      refine ⟨ht0, m, hm, ?_⟩
      rw [htid, h.1]; rfl
  -- every later landed write to the byte is gmo-after the head
  have hlater : ∀ (j t : Nat) (v : BitVec 8) (t' : Nat), ts[j]? = some t → vs[j]? = some v → t < t' →
      (logByte w.σ.ms.msImg w.σ.ms.msLog t' (accAddr base j)).isSome →
      ∃ n' m' u, w.σ.ms.msLog[t' - 1]? = some m' ∧ n' ∈ wrW w ∧ gwix G n' = t' ∧
        m'.wmTid = some n'.1 ∧ gwritesByte G n' (accAddr base j) u ∧ gmoLt G (hd w (hartAgent cpu)) n' := by
    intro j t v t' htj hvj htt hs'
    cases t' with
    | zero => omega
    | succ i =>
      simp only [logByte] at hs'
      cases hm' : w.σ.ms.msLog[i]? with
      | none => rw [hm'] at hs'; cases hs'
      | some m' =>
        rw [hm'] at hs'
        obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hs'
        obtain ⟨n', hn'W, -, hgw, htid, hby⟩ := logPos hI hpf hW hnd (i + 1) m' (by omega) hm'
        have hwb := (hby _ u).1 hu
        refine ⟨n', m', u, hm', hn'W, hgw, htid, hwb, ?_⟩
        exact frLtW hc _ n' _ t v u (hsrc j t v htj hvj) hwb (by omega)
          (plainNe _ aq base ts vs hl n' _ u hwb)
  -- an own landed write is po-before the head, hence visible: never co-after the source
  have hnoOwn : ∀ (j t : Nat) (v : BitVec 8) (n' : Geid) (u : BitVec 8), ts[j]? = some t → vs[j]? = some v → n' ∈ wrW w →
      n'.1 = hartAgent cpu → gwritesByte G n' (accAddr base j) u → gwix G n' ≤ t := by
    intro j t v n' u htj hvj hn' hx hwb
    have hreal := wrWReal hI n' hn'
    obtain ⟨l', -, -, -, hl', -, -, -⟩ := id hwb
    have hpo : WeakRvwmoGraph.gpo G n' (hd w (hartAgent cpu)) :=
      SbHeadHop.gpoOfLbl G n' _ l' _ hl' hl hx (by rw [hx] at hreal; exact hreal)
    exact (hc.lv _ _ t v (hsrc j t v htj hvj)).2 n' u hwb (.inr hpo)
  -- the cut's candidate bytes
  have hcand : ∀ k : Nat, k < n → (SbCand.fwdByte (w.σ.sb (hartAgent cpu)) (accAddr base k) = none ∧
      ¬ ownAt w.σ.ms.msLog (hartAgent cpu) (ts.getD k 0)) →
      ∃ tk vk, ts[k]? = some tk ∧ vs[k]? = some vk ∧ ts.getD k 0 = tk ∧ tk ≤ (wrW w).length ∧
        ¬ ownAt w.σ.ms.msLog (hartAgent cpu) tk := by
    intro k hk ⟨hnfk, hnok⟩
    obtain ⟨tk, htk⟩ : ∃ tk, ts[k]? = some tk := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨vk, hvk⟩ : ∃ vk, vs[k]? = some vk := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rcases hg k tk vk htk hvk with hf | ⟨-, hland, -⟩
    · rw [hf] at hnfk; cases hnfk
    · exact ⟨tk, vk, htk, hvk, getDOf ts k tk htk, hland, by rw [← getDOf ts k tk htk]; exact hnok⟩
  -- the cut is below every later write
  have hTlt : ∀ (j t : Nat) (v : BitVec 8) (t' : Nat), ts[j]? = some t → vs[j]? = some v → t < t' →
      (logByte w.σ.ms.msImg w.σ.ms.msLog t' (accAddr base j)).isSome → T < t' := by
    intro j t v t' htj hvj htt hs'
    obtain ⟨n', m', u, -, hn'W, hgw, -, hwb, hgt⟩ := hlater j t v t' htj hvj htt hs'
    rcases hT2 with h0 | ⟨k, hk, hPk, hTk⟩
    · omega
    · obtain ⟨tk, vk, htk, hvk, hgd, hland, hnok⟩ := hcand k hk hPk
      rw [hTk, hgd]
      cases tk with
      | zero => omega
      | succ ik =>
        obtain ⟨s, hs, hgs, hlt⟩ := hgmoSrc k _ vk htk hvk (by omega) hland hnok
        have := wixLt hc s n' (List.mem_of_getElem? hs) (gwritesOf G n' _ u hc.wf hwb)
          (SbDom.gmoTrans s _ n' hlt hgt)
        omega
  -- every coherence floor of the footprint is below the cut
  have hcohT : ∀ i, i < n → (σ.hr cpu).coh (pa + BitVec.ofNat 64 i) ≤ T := by
    intro i hi
    obtain ⟨ti, hti⟩ : ∃ ti, ts[i]? = some ti := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨vi, hvi⟩ : ∃ vi, vs[i]? = some vi := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hpai : paZ (pa + BitVec.ofNat 64 i) = accAddr base i := by
      rw [hbase]; exact paZAddJ pa n i hnw hi
    by_cases hz : (σ.hr cpu).coh (pa + BitVec.ofNat 64 i) = 0
    · rw [hz]; exact Nat.zero_le _
    · rcases hg i ti vi hti hvi with hfi | ⟨hnfi, hlandi, -⟩
      · exact absurd (hV.cohFwd _ (by rw [hpai]; exact fwdCover _ _ _ hfi)) hz
      · obtain ⟨m2, hm2, hb2, -⟩ := hV.cohSrc _ hz
        obtain ⟨n2, -, -, hgw2, -, hby2⟩ := logPos hI hpf hW hnd _ m2 (by omega) hm2
        obtain ⟨u2, hu2⟩ := Option.isSome_iff_exists.1 hb2
        have hwb2 := (hby2 _ u2).1 hu2
        rw [hpai] at hwb2
        have hcti : (σ.hr cpu).coh (pa + BitVec.ofNat 64 i) ≤ ti := by
          refine Classical.byContradiction fun hlt => ?_
          have hdi := hV.cohD (pa + BitVec.ofNat 64 i) _ hfut ti vi n2 u2
            (by rw [hpai]; exact hsrc i ti vi hti hvi) (by rw [hpai]; exact hwb2) (by omega)
          omega
        by_cases hoi : ownAt w.σ.ms.msLog (hartAgent cpu) ti
        · exfalso
          obtain ⟨hti0, m3, hm3, htid3⟩ := hoi
          obtain ⟨n3, hn3W, -, hgw3, htid3', hby3⟩ := logPos hI hpf hW hnd ti m3 hti0 hm3
          have hlb := hlogB i ti vi hti hvi hlandi
          have hmb : msgByte m3 (accAddr base i) = some vi := by
            cases ti with
            | zero => omega
            | succ q =>
              simp only [logByte] at hlb
              have hm3' : w.σ.ms.msLog[q]? = some m3 := hm3
              rw [hm3'] at hlb; exact hlb
          have hwb3 := (hby3 _ vi).1 hmb
          have hx3 : n3.1 = hartAgent cpu := by rw [htid3'] at htid3; exact Option.some.inj htid3
          have := hV.cohOwn _ hz n3 vi hx3 (wrWReal hI n3 hn3W) (by rw [hpai]; exact hwb3)
          omega
        · have := hT1 i hi ⟨hnfi, by rw [getDOf ts i ti hti]; exact hoi⟩
          rw [getDOf ts i ti hti] at this
          omega
  -- the cut's GF witness
  have hTw : T = 0 ∨ ∃ s, s ∈ gwrites G ∧ gwix G s = T ∧ gmoLt G s (hd w (hartAgent cpu)) := by
    rcases hT2 with h0 | ⟨k, hk, hPk, hTk⟩
    · exact .inl h0
    · obtain ⟨tk, vk, htk, hvk, hgd, hland, hnok⟩ := hcand k hk hPk
      cases tk with
      | zero => exact .inl (by rw [hTk, hgd])
      | succ ik =>
        obtain ⟨s, hs, hgs, hlt⟩ := hgmoSrc k _ vk htk hvk (by omega) hland hnok
        exact .inr ⟨s, List.mem_of_getElem? hs, by rw [hgs, hTk, hgd], hlt⟩
  refine ⟨T, ?_, fun j t v hj htj hvj => ?_, hcohT, hTw⟩
  · rcases hT2 with h0 | ⟨k, hk, hPk, hTk⟩
    · omega
    · obtain ⟨tk, vk, htk, hvk, hgd, hland, -⟩ := hcand k hk hPk
      rw [hltop, hTk, hgd]; exact hland
  · rcases hg j t v htj hvj with hf | ⟨hnf, hland, -⟩
    · exact .inl hf
    · refine .inr ⟨hnf, hlogB j t v htj hvj hland, ?_, fun t' htt hs' => ?_⟩
      · by_cases ho : ownAt w.σ.ms.msLog (hartAgent cpu) t
        · exact .inr ho
        · have := hT1 j hj ⟨hnf, by rw [getDOf ts j t htj]; exact ho⟩
          rw [getDOf ts j t htj] at this
          exact .inl this
      · obtain ⟨n', m', u, hm', hn'W, hgw, htid, hwb, hgt⟩ := hlater j t v t' htj hvj htt hs'
        have htv := hV.tvD _ (accAddr base j) hfut t v n' u (hsrc j t v htj hvj) hwb (by omega)
        rw [hgw] at htv
        have hTt := hTlt j t v t' htj hvj htt hs'
        refine ⟨hTt, htv, fun i hi => ?_, ?_⟩
        · have := hcohT i hi; omega
        · rintro ⟨-, m'', hm'', htid''⟩
          rw [hm', Option.some.injEq] at hm''
          subst hm''
          rw [htid] at htid''
          have hx := Option.some.inj htid''
          have := hnoOwn j t v n' u htj hvj hn'W hx hwb
          omega

#print axioms Weak.SbRealPRView.cutBytesOfRView

end SbRealPRView

end Weak
