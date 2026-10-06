/-
Weak: **T2-1c′, the trace-flexible linearization**.

Rocq: `iris/WeakRvwmoLin2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`WeakRvwmoLin.rule14_linearization` linearizes a rule-14 graph along ONE trace (the rank trace).
A device bundle's fabric order is an additional constraint on the trace, so the linearization
must accept ANY trace respecting `ptraceRel` = po ∪ rf ∪ gmo|W.  A trace is a list of ALL
program events (fences included): the carrier is `gevs'` (definitionally `gevs`).  The log index
of a write IS its `gwix` for every `ptraceExt` trace (`twCount`), so labels go across unchanged.

§1 list plumbing; §2 `ptraceRel`/`ptraceExt`/`candOf`; §3 the snoc step over all four labels
(the RMW's atomicity clause is `gatomicity` read through the log dictionary); §4 the counting
core (`tpoCount`, `twCount`) and the induction (`tprefix`); §5 `gtraceLinearization` (rule 14
not needed); §6 the rank trace is a `ptraceExt` (`glinPtraceExt`), non-vacuity at `mpg'`;
§7 the dev-order version (`gfexecConsistent'`, `ptraceExistsF`, `trDevOrderedOfPtrace`,
`fconfSupply'`, `fconfTraceRealize`).  A leaf.

## Deviations from Rocq

1. NAMES: camelCase (map below); `l !! n` ↦ `l[n]?`; `is_Some o` ↦ `o.isSome = true`;
   `≡ₚ` ↦ `List.Perm`; `omap` ↦ `filterMap`; `seq 0 n` ↦ `List.range' 0 n`; Prop-predicate
   `filter P` (with `Decision`) ↦ `filter p` over `p : A → Bool` (`decide` where needed);
   `grf` ↦ `WeakRvwmoAcyc.grf`, `gpo` ↦ `WeakRvwmoGraph.gpo`, `gmsg` ↦ `WeakRvwmoLin.gmsg`,
   `grow` ↦ `WeakRvwmoLin.grow`, `grank` ↦ `WeakRvwmoLin.grank`, `tc` ↦ `MachCSL.tc`.
   Duplicated names file-qualified: `WeakRvwmoLin2.filterAll`, `WeakRvwmoLin2.tev`.
2. The Rocq `Section Trace` / `Section Rank` hypotheses become explicit parameters of each
   declaration, exactly those Rocq's section closing keeps.
3. O2 / D1 — fetch-inertness (`WeakRvwmoFab` deviation 2): `fconfSupply` takes
   `candFetchInertF boot N c`.  So `fconfSupply'` gains that premise at `candOf G L`, and in
   `fconfTraceRealize` (where `L` is existential) Rocq's `∃ L pst, … ∧ pst 0 = … ∧ fab … = d0 ∧
   execProgOk' …` becomes `∃ L, … ∧ (candFetchInertF boot N c → ∃ pst, pst 0 = … ∧ fab … = d0 ∧
   execProgOk' …)`; the other conjuncts are Rocq's.
4. Lean-only helpers: `WeakRvwmoLin2.gevs'Eq` (`gevs' G = gevs G`, Rocq: definitional) and
   `WeakRvwmoLin2.devLbl` (the "every dev event is labelled" fact Rocq inlines twice), and the
   local `where`-auxiliary `ptraceRelMem.gwriteAtInv'`.
5. §8's `Print Assumptions` audit is dropped (the lint's axiom/sorry ban is the audit).

**Rocq → Lean name map.**  `before_index` `beforeIndex`, `elem_of_take_lookup`
`elemOfTakeLookup`, `filter_all` `WeakRvwmoLin2.filterAll`, `filter_take_S` `filterTakeS`,
`filter_take_mono'` `filterTakeMono'`, `filter_lookup_count` `filterLookupCount`, `ptrace_rel`
`ptraceRel`, `ptrace_ext` `ptraceExt`, `cand_of` `candOf`, `gmo_lt_dec2` `gmoLtDec2`,
`cand_of_tr` `candOfTr`, `gcnt_fmap` `gcntFmap`, `tcnt_gcnt` `tcntGcnt`, `glb_rd_len`
`glbRdLen`, `gtrace_prefix_ev` `gtracePrefixEv`, `gtrace_snoc_rd_adm` `gtraceSnocRdAdm`,
`gtrace_rmw_latest` `gtraceRmwLatest`, `gtrace_snoc_step` `gtraceSnocStep`, `twf` `twf`, `tnd`
`tnd`, `tmem` `tmem`, `tlbl` `tlbl`, `tord` `tord`, `tnodup_take` `tnodupTake`, `tpo_perm`
`tpoPerm`, `tpo_count` `tpoCount`, `twrites_mem` `twritesMem`, `tw_perm` `twPerm`, `tw_below`
`twBelow`, `tw_count` `twCount`, `tw_list` `twList`, `tlog_end` `tlogEnd`, `tlog_len` `tlogLen`,
`tsrc_bound` `tsrcBound`, `tev` `WeakRvwmoLin2.tev`, `tisw` `tisw`, `tcand_len` `tcandLen`,
`tprefix` `tprefix`, `thart_len` `thartLen`, `trow_eq` `trowEq`, `tlog_full` `tlogFull`, `tfull`
`tfull`, `gtrace_linearization_min` `gtraceLinearizationMin`, `gtrace_linearization`
`gtraceLinearization`, `rwf` `rwf`, `rgmem` `rgmem`, `rk_before` `rkBefore`, `rk_gmo_w`
`rkGmoW`, `rk_po` `rkPo`, `rk_rf` `rkRf`, `rk_ww` `rkWw`, `glin_ptrace_ext` `glinPtraceExt`,
`rule14_linearization'` `rule14Linearization'`, `cand_of_lin_cand` `candOfLinCand`,
`gtrace_linearization_nonvacuous` `gtraceLinearizationNonvacuous`, `ptrace_relF` `ptraceRelF`,
`gfexec_consistent'` `gfexecConsistent'`, `ptrace_rel_dec` `ptraceRelDec`, `ptrace_relF_dec`
`ptraceRelFDec`, `ptrace_ext_acyclic` `ptraceExtAcyclic`, `gfexec_consistent'_nodev`
`gfexecConsistent'Nodev`, `gfexec_consistent_nodev` `gfexecConsistentNodev`, `ptrace_rel_mem`
`ptraceRelMem`, `ptrace_exists_F` `ptraceExistsF`, `filter_ordered_count` `filterOrderedCount`,
`dcnt_filter` `dcntFilter`, `tr_dev_ordered_of_ptrace` `trDevOrderedOfPtrace`, `fconf_supply'`
`fconfSupply'`, `fconf_trace_realize` `fconfTraceRealize`.

**Dropped:** nothing (Rocq 69 declarations; Lean 69 + 3 helpers).
-/
import Weak.WeakRvwmoFloor
import Weak.WeakRvwmoFabInd
import Weak.WeakRvwmoProbeK1
import Weak.WeakRvwmoDec

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

/-! # 1. Plumbing -/

theorem beforeIndex {A : Type _} (L : List A) (x y : A) (m n : Nat) :
    L.Nodup → L[m]? = some x → L[n]? = some y → before L x y → m < n := by
  rintro hnd hm hn ⟨i, j, hi, hj, hij⟩
  rw [NoDup_lookup hnd hi hm, NoDup_lookup hnd hj hn] at hij
  exact hij

theorem elemOfTakeLookup {A : Type _} (l : List A) (k : Nat) (x : A) :
    x ∈ l.take k ↔ ∃ p, p < k ∧ l[p]? = some x := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := elem_of_list_lookup_1 h
    obtain ⟨hp, hlt⟩ := lookup_take_Some.1 hp
    exact ⟨p, hlt, hp⟩
  · rintro ⟨p, hlt, hp⟩
    exact elem_of_list_lookup_2 (lookup_take_Some.2 ⟨hp, hlt⟩)

theorem WeakRvwmoLin2.filterAll {A : Type _} (p : A → Bool) (l : List A) :
    (∀ x, x ∈ l → p x = true) → l.filter p = l :=
  fun h => List.filter_eq_self.2 (fun x hx => h x hx)

theorem filterTakeS {A : Type _} (p : A → Bool) (l : List A) (k : Nat) (x : A) :
    l[k]? = some x → p x = true →
    ((l.take (k + 1)).filter p).length = ((l.take k).filter p).length + 1 := by
  intro hk hx
  rw [take_S_r hk, List.filter_append]
  simp [hx]

theorem filterTakeMono' {A : Type _} (p : A → Bool) (l : List A) (k k' : Nat) :
    k ≤ k' → ((l.take k).filter p).length ≤ ((l.take k').filter p).length := by
  intro hle
  have h : l.take k = (l.take k').take k := by rw [List.take_take, Nat.min_eq_left hle]
  rw [h]
  exact ((List.take_sublist _ _).filter p).length_le

theorem filterLookupCount {A : Type _} (p : A → Bool) (l : List A) (k : Nat) (x : A) :
    l[k]? = some x → p x = true → (l.filter p)[((l.take k).filter p).length]? = some x := by
  intro hk hx
  have hs : l.filter p = (l.take k).filter p ++ (l.drop k).filter p := by
    rw [← List.filter_append, List.take_append_drop]
  rw [hs, drop_S hk, List.filter_cons_of_pos hx]
  exact list_lookup_middle rfl

/-! # 2. The order a trace must respect -/

/-- po ∪ rf ∪ gmo|W. -/
def ptraceRel (G : Gexec) (x y : Geid) : Prop :=
  WeakRvwmoGraph.gpo G x y ∨ WeakRvwmoAcyc.grf G x y ∨
  (gisW G x = true ∧ gisW G y = true ∧ gmoLt G x y)

/-- A trace: every program event once, in an order extending `ptraceRel`. -/
def ptraceExt (G : Gexec) (L : List Geid) : Prop :=
  L.Perm (gevs' G) ∧ ∀ x y, ptraceRel G x y → before L x y

/-- The candidate a trace names. -/
def candOf (G : Gexec) (L : List Geid) : Cand := ⟨G.gxImg, L.map (glinStep G)⟩

instance gmoLtDec2 (G : Gexec) (e1 e2 : Geid) : Decidable (gmoLt G e1 e2) := by
  unfold gmoLt; infer_instance

theorem candOfTr (G : Gexec) (L : List Geid) : (candOf G L).cdTr = L.map (glinStep G) := rfl

theorem WeakRvwmoLin2.gevs'Eq (G : Gexec) : gevs' G = gevs G := rfl

theorem gcntFmap (G : Gexec) (i : Nat) (l : List Geid) :
    gcnt i (l.map (glinStep G)) = (l.filter (fun x : Geid => decide (x.1 = i))).length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    unfold gcnt at ih ⊢
    by_cases h : x.1 = i
    · simp [List.filter_cons, glinStep, h, ih]
    · simp [List.filter_cons, glinStep, h, ih]

/-! # 3. The step -/

theorem tcntGcnt (i : Nat) (tr : List Estep) : tcnt i tr = gcnt i tr := rfl

theorem glbRdLen (G : Gexec) (e : Geid) (l : Lbl) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) :
    gwf G → gxLbl G e = some l → lbRd l = some (base, ts, vs) → vs.length = ts.length := by
  intro hwf hl hrd
  have hs := WeakRvwmoFloor.gshape G hwf e l hl
  cases l with
  | LLoad aq b ts' vs' =>
    simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨-, rfl, rfl⟩ := hrd
    exact hs
  | LStore => simp [lbRd] at hrd
  | LFence => simp [lbRd] at hrd
  | LRmw aq rl b ts' rvs wvs k =>
    simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨-, rfl, rfl⟩ := hrd
    exact hs.2.2

theorem gtracePrefixEv (G : Gexec) (c : Cand) (ev ev' : Nat → Geid) :
    (∀ p s, c.cdTr[p]? = some s → ev p = ev' p) →
    GtracePrefix G c ev → GtracePrefix G c ev' := by
  rintro heq ⟨himg, hag, hpos, hlbl, hwix, hlog⟩
  refine ⟨himg, ?_, ?_, ?_, ?_, hlog⟩
  · intro p s hs; rw [← heq p s hs]; exact hag p s hs
  · intro p s hs; rw [← heq p s hs]; exact hpos p s hs
  · intro p s hs; rw [← heq p s hs]; exact hlbl p s hs
  · intro p s hs hw; rw [← heq p s hs]; exact hwix p s hs hw

theorem gtraceSnocRdAdm (G : Gexec) (c : Cand) (ev : Nat → Geid) (i : Nat) (l : Lbl)
    (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    rvwmoMinusConsistent G → GtracePrefix G c ev →
    gxLbl G (i, gcnt i c.cdTr) = some l → lbRd l = some (base, ts, vs) →
    vs.length = ts.length →
    (∀ (j : Nat) t, ts[j]? = some t → t ≤ (cdLogEnd c).length) →
    snocRdAdm c i (lbAq l) base ts vs := by
  intro hcons hgt hl hrd hlen hsrc
  obtain ⟨hwf, hppo, hlv, hat⟩ := hcons
  have hrb : ∀ (j : Nat) t v, ts[j]? = some t → vs[j]? = some v →
      greadsByte G (i, gcnt i c.cdTr) (accAddr base j) t v :=
    fun j t v hj hv => ⟨l, base, ts, vs, j, hl, hrd, hj, hv, rfl⟩
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
    exact floorOfGraph G c ev i (i, gcnt i c.cdTr) (accAddr base j) t v (lbAq l)
      ⟨hwf, hppo, hlv, hat⟩ hgt rfl (hrb j t v hj hv) (fun h => ⟨l, hl, h⟩)

/-- (O6) The atomicity clause. -/
theorem gtraceRmwLatest (G : Gexec) (c : Cand) (ev : Nat → Geid) (i : Nat) (l : Lbl)
    (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    rvwmoMinusConsistent G → GtracePrefix G c ev →
    gxLbl G (i, gcnt i c.cdTr) = some l → lbRd l = some (base, ts, vs) → lbIsW l = true →
    vs.length = ts.length →
    gwix G (i, gcnt i c.cdTr) = (cdLogEnd c).length + 1 →
    (∀ (j : Nat) t, ts[j]? = some t → t ≤ (cdLogEnd c).length) →
    ∀ (j : Nat) t, ts[j]? = some t → latest c.cdImg (cdLogEnd c) (accAddr base j) t := by
  intro hcons hgt hl hrd hw hlen hix hsrc j t hj
  have hjlt : j < vs.length := by rw [hlen]; exact lookup_lt_Some hj
  obtain ⟨v, hv⟩ := someOfIsSome (lookup_lt_is_Some_2 hjlt)
  have hrb : greadsByte G (i, gcnt i c.cdTr) (accAddr base j) t v :=
    ⟨l, base, ts, vs, j, hl, hrd, hj, hv, rfl⟩
  refine ⟨?_, ?_⟩
  · have hval := (gtraceSnocRdAdm G c ev i l base ts vs hcons hgt hl hrd hlen hsrc).2.1
    rw [hval j t v hj hv]; rfl
  · rintro ⟨s, hlo, hhi, m, hm, hby⟩
    obtain ⟨w', v', hw', hwb'⟩ := gtpLogWrites G c ev hgt s m (by omega) hm (accAddr base j) hby
    have hix' : gwix G w' = s := (gwriteAtInv G s w' hcons.1.1 hw').2
    apply hcons.2.2.2 (i, gcnt i c.cdTr) (accAddr base j) t v hrb ⟨l, hl, hw⟩ w' v' hwb'
    rw [hix', hix]
    exact ⟨hlo, by omega⟩

/-- THE SNOC STEP, at any label. -/
theorem gtraceSnocStep (G : Gexec) (c : Cand) (ev : Nat → Geid) (i : Nat) (l : Lbl) :
    rvwmoMinusConsistent G → srvwmoConsistent c → GtracePrefix G c ev →
    gxLbl G (i, gcnt i c.cdTr) = some l →
    (lbIsW l = true → gwix G (i, gcnt i c.cdTr) = (cdLogEnd c).length + 1) →
    (∀ base ts vs, lbRd l = some (base, ts, vs) →
       ∀ (j : Nat) t, ts[j]? = some t → t ≤ (cdLogEnd c).length) →
    srvwmoConsistent (candSnoc c ⟨i, l⟩) ∧
    GtracePrefix G (candSnoc c ⟨i, l⟩) (evSnoc c ev (i, gcnt i c.cdTr)) := by
  intro hcons hc hgt hl hix hsrc
  cases l with
  | LLoad aq base ts vs =>
    exact gtraceSnocReadConsistent G c ev i aq base ts vs hcons hc hgt hl (hsrc base ts vs rfl)
  | LStore rl base vs kc =>
    exact gtraceSnocWriteConsistent G c ev i rl base vs kc hcons.1 hc hgt hl (hix rfl)
  | LFence pr pw sr sw =>
    exact ⟨snocFenceConsistent c i pr pw sr sw hc,
      gtracePrefixSnoc G c ev i _ hcons.1 hgt hl (fun h => by simp [lbIsW] at h)⟩
  | LRmw aq rl base ts rvs wvs kc =>
    refine ⟨?_, gtracePrefixSnoc G c ev i _ hcons.1 hgt hl (fun _ => hix rfl)⟩
    obtain ⟨hne, hlenw, hlenr⟩ := WeakRvwmoFloor.gshape G hcons.1 _ _ hl
    exact snocRmwConsistent c i aq rl base ts rvs wvs kc hc hne hlenw
      (gtraceSnocRdAdm G c ev i (.LRmw aq rl base ts rvs wvs kc) base ts rvs hcons hgt hl rfl
        hlenr (hsrc base ts rvs rfl))
      (gtraceRmwLatest G c ev i (.LRmw aq rl base ts rvs wvs kc) base ts rvs hcons hgt hl rfl
        rfl hlenr (hix rfl) (hsrc base ts rvs rfl))

/-! # 4. The counting core and the induction -/

theorem twf (G : Gexec) (hcons : rvwmoMinusConsistent G) : gwf G := hcons.1

theorem tnd (G : Gexec) (L : List Geid) (hext : ptraceExt G L) : L.Nodup :=
  hext.1.nodup_iff.2 (gevsNodup G)

theorem tmem (G : Gexec) (L : List Geid) (hext : ptraceExt G L) (e : Geid) :
    e ∈ L ↔ (gxLbl G e).isSome = true := by
  rw [hext.1.mem_iff, WeakRvwmoLin2.gevs'Eq]; exact elemOfGevs G e

theorem tlbl (G : Gexec) (L : List Geid) (hext : ptraceExt G L) (k : Nat) (e : Geid) :
    L[k]? = some e → (gxLbl G e).isSome = true :=
  fun hk => (tmem G L hext e).1 (elem_of_list_lookup_2 hk)

theorem tord (G : Gexec) (L : List Geid) (hext : ptraceExt G L) (m n : Nat) (x y : Geid) :
    L[m]? = some x → L[n]? = some y → ptraceRel G x y → m < n :=
  fun hm hn hr => beforeIndex L x y m n (tnd G L hext) hm hn (hext.2 x y hr)

theorem tnodupTake (G : Gexec) (L : List Geid) (hext : ptraceExt G L) (k : Nat) :
    (L.take k).Nodup :=
  (tnd G L hext).sublist (List.take_sublist k L)

theorem tpoPerm (G : Gexec) (L : List Geid) (hext : ptraceExt G L) (k : Nat) (e : Geid) :
    L[k]? = some e →
    ((L.take k).filter (fun x : Geid => decide (x.1 = e.1))).Perm
      ((List.range' 0 e.2).map (fun j => (e.1, j))) := by
  intro hk
  have hel := tlbl G L hext k e hk
  have hb := (gxLblBounds G e).1 hel
  apply NoDup_Permutation (NoDup_filter (tnodupTake G L hext k))
    (NoDup_fmap_2 (fun a b h => (Prod.mk.inj h).2) NoDup_seq)
  intro x
  rw [elem_of_list_filter, elemOfTakeLookup, elem_of_list_fmap]
  constructor
  · rintro ⟨hx1, p, hlt, hp⟩
    have hx1 : x.1 = e.1 := of_decide_eq_true hx1
    have hxl := tlbl G L hext p x hp
    refine ⟨x.2, Prod.ext hx1 rfl, elem_of_seq.2 ⟨Nat.zero_le _, ?_⟩⟩
    apply Classical.byContradiction
    intro hge
    by_cases heq : x.2 = e.2
    · have hxe : x = e := Prod.ext hx1 heq
      rw [hxe] at hp
      have := NoDup_lookup (tnd G L hext) hp hk
      omega
    · have hpo : WeakRvwmoGraph.gpo G e x := ⟨hx1.symm, by omega, hel, hxl⟩
      have := tord G L hext k p e x hk hp (Or.inl hpo)
      omega
  · rintro ⟨j, rfl, hj⟩
    obtain ⟨-, hj⟩ := elem_of_seq.1 hj
    refine ⟨by simp, ?_⟩
    have hb2 := hb.2
    have hjl : (gxLbl G (e.1, j)).isSome = true :=
      (gxLblBounds G _).2 ⟨hb.1, by show j < (WeakRvwmoLin.grow G e.1).length; omega⟩
    obtain ⟨p, hp⟩ := elem_of_list_lookup_1 ((tmem G L hext _).2 hjl)
    exact ⟨p, tord G L hext p k _ e hp hk
      (Or.inl ⟨rfl, by show j < e.2; omega, hjl, hel⟩), hp⟩

theorem tpoCount (G : Gexec) (L : List Geid) (hext : ptraceExt G L) (k : Nat) (e : Geid) :
    L[k]? = some e → gcnt e.1 (candOf G (L.take k)).cdTr = e.2 := by
  intro hk
  show gcnt e.1 ((L.take k).map (glinStep G)) = e.2
  rw [gcntFmap, (tpoPerm G L hext k e hk).length_eq, List.length_map, List.length_range']

theorem twritesMem (G : Gexec) (L : List Geid) (hcons : rvwmoMinusConsistent G)
    (hext : ptraceExt G L) (x : Geid) :
    x ∈ gwrites G ↔ x ∈ L ∧ gisW G x = true :=
  ⟨fun hx => ⟨(tmem G L hext x).2 (gwritesLbl G hcons.1 x hx), gwritesIsw G x hx⟩,
   fun ⟨hx, hw⟩ => gisWGwrites G x hcons.1 ((tmem G L hext x).1 hx) hw⟩

theorem twPerm (G : Gexec) (L : List Geid) (hcons : rvwmoMinusConsistent G)
    (hext : ptraceExt G L) (k : Nat) (e : Geid) :
    L[k]? = some e → gisW G e = true →
    ((L.take k).filter (gisW G)).Perm ((gwrites G).filter (fun w => decide (gmoLt G w e))) := by
  intro hk hw
  have hnd : G.gxGmo.Nodup := hcons.1.1
  have he : e ∈ gwrites G := (twritesMem G L hcons hext e).2 ⟨elem_of_list_lookup_2 hk, hw⟩
  apply NoDup_Permutation (NoDup_filter (tnodupTake G L hext k))
    (NoDup_filter (gwritesNodup G hnd))
  intro x
  rw [elem_of_list_filter, elem_of_list_filter, elemOfTakeLookup]
  constructor
  · rintro ⟨hxw, p, hlt, hp⟩
    have hx : x ∈ gwrites G := (twritesMem G L hcons hext x).2 ⟨elem_of_list_lookup_2 hp, hxw⟩
    refine ⟨?_, hx⟩
    have hne : x ≠ e := by
      intro hxe
      rw [hxe] at hp
      have := NoDup_lookup (tnd G L hext) hp hk
      omega
    rcases gmoLtTotal G x e hnd ((gwritesElemOf G x).1 hx).1 ((gwritesElemOf G e).1 he).1 hne
      with hmo | hmo
    · exact decide_eq_true hmo
    · exfalso
      have := tord G L hext k p e x hk hp (Or.inr (Or.inr ⟨hw, hxw, hmo⟩))
      omega
  · rintro ⟨hmo, hx⟩
    have hmo := of_decide_eq_true hmo
    have hxw := gwritesIsw G x hx
    refine ⟨hxw, ?_⟩
    obtain ⟨p, hp⟩ := elem_of_list_lookup_1 ((twritesMem G L hcons hext x).1 hx).1
    exact ⟨p, tord G L hext p k x e hp hk (Or.inr (Or.inr ⟨hxw, hw, hmo⟩)), hp⟩

theorem twBelow (G : Gexec) (hcons : rvwmoMinusConsistent G) (n : Nat) (e : Geid) :
    (gwrites G)[n]? = some e →
    (gwrites G).filter (fun w => decide (gmoLt G w e)) = (gwrites G).take n := by
  intro hn
  have hnd : G.gxGmo.Nodup := hcons.1.1
  have hss := gwritesSorted G hnd
  have he : e ∈ gwrites G := elem_of_list_lookup_2 hn
  have hsplit : (gwrites G).filter (fun w => decide (gmoLt G w e)) =
      ((gwrites G).take n).filter (fun w => decide (gmoLt G w e)) ++
      (e :: (gwrites G).drop (n + 1)).filter (fun w => decide (gmoLt G w e)) := by
    rw [← List.filter_append, take_drop_middle hn]
  have h1 : ((gwrites G).take n).filter (fun w => decide (gmoLt G w e)) = (gwrites G).take n := by
    apply WeakRvwmoLin2.filterAll
    intro x hx
    obtain ⟨p, hp⟩ := elem_of_list_lookup_1 hx
    obtain ⟨hp, hlt⟩ := lookup_take_Some.1 hp
    have hx' : x ∈ gwrites G := elem_of_list_lookup_2 hp
    have hlt' : gpos G x < gpos G e :=
      stronglySortedLookupElim (fun x y => gpos G x < gpos G y) _ p n x e hss hp hn hlt
    exact decide_eq_true ⟨((gwritesElemOf G x).1 hx').1, ((gwritesElemOf G e).1 he).1, hlt'⟩
  have h2 : (e :: (gwrites G).drop (n + 1)).filter (fun w => decide (gmoLt G w e)) = [] := by
    apply List.filter_eq_nil_iff.2
    intro x hx hmo
    have hmo := of_decide_eq_true hmo
    rcases List.mem_cons.1 hx with hxe | hx
    · rw [hxe] at hmo; exact Nat.lt_irrefl _ hmo.2.2
    · obtain ⟨p, hp⟩ := elem_of_list_lookup_1 hx
      rw [lookup_drop] at hp
      have h3 : gpos G e < gpos G x :=
        stronglySortedLookupElim (fun x y => gpos G x < gpos G y) _ n (n + 1 + p) e x hss hn hp
          (by omega)
      exact Nat.lt_asymm h3 hmo.2.2
  rw [hsplit, h1, h2, List.append_nil]

theorem twCount (G : Gexec) (L : List Geid) (hcons : rvwmoMinusConsistent G)
    (hext : ptraceExt G L) (k : Nat) (e : Geid) :
    L[k]? = some e → gisW G e = true →
    gwix G e = ((L.take k).filter (gisW G)).length + 1 := by
  intro hk hw
  have he : e ∈ gwrites G := (twritesMem G L hcons hext e).2 ⟨elem_of_list_lookup_2 hk, hw⟩
  obtain ⟨n, hn, hix⟩ := gwixLookup G e he
  rw [hix, (twPerm G L hcons hext k e hk hw).length_eq, twBelow G hcons n e hn, List.length_take]
  have := lookup_lt_Some hn
  omega

/-- THE WRITE LIST: a trace's writes, in trace order, ARE `gwrites`. -/
theorem twList (G : Gexec) (L : List Geid) (hcons : rvwmoMinusConsistent G)
    (hext : ptraceExt G L) : L.filter (gisW G) = gwrites G := by
  have hnd := hcons.1.1
  have hperm : (L.filter (gisW G)).Perm (gwrites G) := by
    apply NoDup_Permutation (NoDup_filter (tnd G L hext)) (gwritesNodup G hnd)
    intro x
    rw [elem_of_list_filter, twritesMem G L hcons hext]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩
  apply list_eq
  intro n
  cases hw : (gwrites G)[n]? with
  | none =>
    apply lookup_ge_None_2
    rw [hperm.length_eq]; exact lookup_ge_None_1 hw
  | some w =>
    have hwm : w ∈ gwrites G := elem_of_list_lookup_2 hw
    have hwb := gwritesIsw G w hwm
    obtain ⟨p, hp⟩ := elem_of_list_lookup_1 ((twritesMem G L hcons hext w).1 hwm).1
    have hc := twCount G L hcons hext p w hp hwb
    rw [gwixOfLookup G n w hnd hw] at hc
    have hn : n = ((L.take p).filter (gisW G)).length := by omega
    rw [hn]; exact filterLookupCount _ L p w hp hwb

theorem tlogEnd (G : Gexec) (L : List Geid) (k : Nat) :
    cdLogEnd (candOf G (L.take k)) = (L.take k).filterMap (WeakRvwmoLin.gmsg G) := by
  rw [cdLogEndFull, trMsgsOmap]; exact omapGlin G (L.take k)

theorem tlogLen (G : Gexec) (L : List Geid) (k : Nat) :
    (cdLogEnd (candOf G (L.take k))).length = ((L.take k).filter (gisW G)).length := by
  rw [tlogEnd, omapGmsgLen]

/-- (O2) A read's source is already in the log — the rf arm. -/
theorem tsrcBound (G : Gexec) (L : List Geid) (hcons : rvwmoMinusConsistent G)
    (hext : ptraceExt G L) (k : Nat) (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    L[k]? = some e → greadsByte G e a t v →
    t ≤ (cdLogEnd (candOf G (L.take k))).length := by
  intro hk hrd
  rw [tlogLen]
  cases t with
  | zero => omega
  | succ n =>
    obtain ⟨w, hw, -, -⟩ := (hcons.2.2.1 e a (n + 1) v hrd).1
    have hrf : WeakRvwmoAcyc.grf G w e := ⟨a, n + 1, v, hrd, hw⟩
    obtain ⟨hwm, hix⟩ := gwriteAtInv G (n + 1) w hcons.1.1 hw
    have hwb := gwritesIsw G w hwm
    obtain ⟨p, hp⟩ := elem_of_list_lookup_1 ((twritesMem G L hcons hext w).1 hwm).1
    have hlt : p < k := tord G L hext p k w e hp hk (Or.inr (Or.inl hrf))
    rw [← hix, twCount G L hcons hext p w hp hwb, ← filterTakeS (gisW G) L p w hp hwb]
    exact filterTakeMono' _ L (p + 1) k (by omega)

def WeakRvwmoLin2.tev (L : List Geid) : Nat → Geid := fun p => (L[p]?).getD (0, 0)

theorem tisw (G : Gexec) (e : Geid) : (gxLbl G e).isSome = true → lbIsW (glbl G e) = gisW G e := by
  intro h
  obtain ⟨l, hl⟩ := someOfIsSome h
  simp [glbl, gisW, hl]

theorem tcandLen (G : Gexec) (L : List Geid) (k : Nat) :
    k ≤ L.length → (candOf G (L.take k)).cdTr.length = k := by
  intro hk
  show ((L.take k).map (glinStep G)).length = k
  rw [List.length_map, List.length_take]
  omega

/-- (O1) Every prefix is a G-trace prefix. -/
theorem tprefix (G : Gexec) (L : List Geid) (hcons : rvwmoMinusConsistent G)
    (hext : ptraceExt G L) (k : Nat) :
    srvwmoConsistent (candOf G (L.take k)) ∧
    GtracePrefix G (candOf G (L.take k)) (WeakRvwmoLin2.tev L) := by
  induction k with
  | zero =>
    have ht0 : (candOf G (L.take 0)).cdTr = [] := by simp [candOf]
    refine ⟨srvwmoOfWf _ (candReachable _ (fun kk s hs => by rw [ht0] at hs; simp at hs)).1, ?_⟩
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro p s hs; rw [ht0] at hs; simp at hs
    · intro p s hs; rw [ht0] at hs; simp at hs
    · intro p s hs; rw [ht0] at hs; simp at hs
    · intro p s hs; rw [ht0] at hs; simp at hs
    · intro s hs hle
      have h0 : cdLog (candOf G (L.take 0)) (candOf G (L.take 0)).cdTr.length = [] := by
        simp only [cdLog, ht0, List.take_nil]; rfl
      rw [h0] at hle
      simp at hle
      omega
  | succ k ih =>
    cases hk : L[k]? with
    | none =>
      have hge : L.take (k + 1) = L.take k := by
        have := lookup_ge_None_1 hk
        rw [take_ge (show L.length ≤ k + 1 by omega), take_ge (show L.length ≤ k by omega)]
      rw [hge]; exact ih
    | some e =>
      have hlt : k < L.length := lookup_lt_Some hk
      have hcl : (candOf G (L.take k)).cdTr.length = k := tcandLen G L k (by omega)
      have hel := tlbl G L hext k e hk
      have hcnt : gcnt e.1 (candOf G (L.take k)).cdTr = e.2 := tpoCount G L hext k e hk
      have hev : (e.1, gcnt e.1 (candOf G (L.take k)).cdTr) = e := by rw [hcnt]
      have hl : gxLbl G (e.1, gcnt e.1 (candOf G (L.take k)).cdTr) = some (glbl G e) := by
        rw [hev]; obtain ⟨l, hl⟩ := someOfIsSome hel; simp [glbl, hl]
      have hsnoc : candSnoc (candOf G (L.take k)) ⟨e.1, glbl G e⟩ = candOf G (L.take (k + 1)) := by
        simp only [candSnoc, candOf, take_S_r hk, List.map_append, List.map_cons, List.map_nil,
          glinStep]
      have hix : lbIsW (glbl G e) = true →
          gwix G (e.1, gcnt e.1 (candOf G (L.take k)).cdTr) =
            (cdLogEnd (candOf G (L.take k))).length + 1 := by
        intro hw
        rw [hev, tlogLen, twCount G L hcons hext k e hk (by rw [← tisw G e hel]; exact hw)]
      have hsrcb : ∀ base ts vs, lbRd (glbl G e) = some (base, ts, vs) →
          ∀ (j : Nat) t, ts[j]? = some t → t ≤ (cdLogEnd (candOf G (L.take k))).length := by
        intro base ts vs hrd j t hj
        obtain ⟨l, hl'⟩ := someOfIsSome hel
        have hgl : glbl G e = l := by simp [glbl, hl']
        rw [hgl] at hrd
        have hlen := glbRdLen G e l base ts vs hcons.1 hl' hrd
        have hjlt : j < vs.length := by rw [hlen]; exact lookup_lt_Some hj
        obtain ⟨v, hv⟩ := someOfIsSome (lookup_lt_is_Some_2 hjlt)
        exact tsrcBound G L hcons hext k e (accAddr base j) t v hk
          ⟨l, base, ts, vs, j, hl', hrd, hj, hv, rfl⟩
      obtain ⟨hc', hp'⟩ := gtraceSnocStep G _ (WeakRvwmoLin2.tev L) e.1 (glbl G e) hcons ih.1
        ih.2 hl hix hsrcb
      rw [hsnoc] at hc' hp'
      refine ⟨hc', gtracePrefixEv G _ _ _ ?_ hp'⟩
      intro p s hs
      have hplt : p < k + 1 := by
        have hb := lookup_lt_Some hs
        rw [tcandLen G L (k + 1) (by omega)] at hb
        exact hb
      by_cases hp : p < k
      · exact evSnocLt _ _ _ p (by omega)
      · have hpk : p = k := by omega
        rw [hpk]
        unfold evSnoc
        rw [if_neg (by rw [hcl]; exact Nat.lt_irrefl k)]
        show _ = (L[k]?).getD (0, 0)
        rw [hk]
        exact hev

theorem thartLen (G : Gexec) (L : List Geid) (hext : ptraceExt G L) (i : Nat) :
    (L.filter (fun x : Geid => decide (x.1 = i))).length = (WeakRvwmoLin.grow G i).length := by
  have hperm : (L.filter (fun x : Geid => decide (x.1 = i))).Perm (gevsHart G i) := by
    apply NoDup_Permutation (NoDup_filter (tnd G L hext)) (gevsHartNodup G i)
    intro x
    rw [elem_of_list_filter, elemOfGevsHart, tmem G L hext]
    constructor
    · rintro ⟨h1, h2⟩
      have h1 := of_decide_eq_true h1
      refine ⟨h1, ?_⟩
      rw [← h1]; exact ((gxLblBounds G x).1 h2).2
    · rintro ⟨h1, h2⟩
      refine ⟨decide_eq_true h1, (gxLblBounds G x).2 ⟨?_, by rw [h1]; exact h2⟩⟩
      cases hp : G.gxProg[i]? with
      | some row => rw [h1]; exact lookup_lt_Some hp
      | none => exfalso; simp [WeakRvwmoLin.grow, hp] at h2
  rw [hperm.length_eq]
  simp [gevsHart]

theorem trowEq (G : Gexec) (L : List Geid) (hext : ptraceExt G L) (i : Nat) :
    trow i (candOf G L).cdTr = WeakRvwmoLin.grow G i := by
  have hg : gcnt i (candOf G L).cdTr = (WeakRvwmoLin.grow G i).length := by
    show gcnt i (L.map (glinStep G)) = _
    rw [gcntFmap, thartLen G L hext]
  have hlen : (trow i (candOf G L).cdTr).length = (WeakRvwmoLin.grow G i).length := by
    unfold trow; rw [List.length_map]; exact hg
  apply list_eq
  intro n
  by_cases hn : n < (WeakRvwmoLin.grow G i).length
  · have hi : i < G.gxProg.length := by
      cases hp : G.gxProg[i]? with
      | some row => exact lookup_lt_Some hp
      | none => exfalso; simp [WeakRvwmoLin.grow, hp] at hn
    have hlbl : (gxLbl G (i, n)).isSome = true := (gxLblBounds G _).2 ⟨hi, hn⟩
    obtain ⟨p, hp⟩ := elem_of_list_lookup_1 ((tmem G L hext _).2 hlbl)
    have hs : (candOf G L).cdTr[p]? = some (glinStep G (i, n)) := by
      show (L.map (glinStep G))[p]? = _
      rw [List.getElem?_map, hp]; rfl
    have hrow := trowAt i (candOf G L).cdTr p (glinStep G (i, n)) hs rfl
    have htk : (candOf G L).cdTr.take p = (candOf G (L.take p)).cdTr := by
      show (L.map (glinStep G)).take p = (L.take p).map (glinStep G)
      rw [List.map_take]
    have hc := tpoCount G L hext p (i, n) hp
    simp only at hc
    rw [htk, tcntGcnt, hc] at hrow
    rw [hrow]
    obtain ⟨l, hl⟩ := someOfIsSome hlbl
    have hgl : (WeakRvwmoLin.grow G i)[n]? = some l := by
      simp only [gxLbl] at hl
      unfold WeakRvwmoLin.grow
      cases hpi : G.gxProg[i]? with
      | some row => rw [hpi] at hl; simpa using hl
      | none => rw [hpi] at hl; simp at hl
    rw [hgl]
    simp [glinStep, glbl, hl]
  · have h1 : (trow i (candOf G L).cdTr)[n]? = none := lookup_ge_None_2 (by omega)
    have h2 : (WeakRvwmoLin.grow G i)[n]? = none := lookup_ge_None_2 (by omega)
    rw [h1, h2]

theorem tlogFull (G : Gexec) (L : List Geid) (hcons : rvwmoMinusConsistent G)
    (hext : ptraceExt G L) :
    cdLog (candOf G L) (candOf G L).cdTr.length = (gwrites G).filterMap (WeakRvwmoLin.gmsg G) := by
  unfold cdLog
  rw [take_ge (Nat.le_refl _), trMsgsOmap]
  show List.filterMap esWmsg (L.map (glinStep G)) = _
  rw [omapGlin, omapGmsgFilter, twList G L hcons hext]

theorem tfull (G : Gexec) (L : List Geid) (hcons : rvwmoMinusConsistent G)
    (hext : ptraceExt G L) :
    srvwmoConsistent (candOf G L) ∧ GtracePrefix G (candOf G L) (WeakRvwmoLin2.tev L) := by
  have h := tprefix G L hcons hext L.length
  rwa [List.take_of_length_le (Nat.le_refl L.length)] at h

/-! # 5. The theorem -/

theorem gtraceLinearizationMin (G : Gexec) (L : List Geid) :
    rvwmoMinusConsistent G → ptraceExt G L →
    srvwmoConsistent (candOf G L) ∧
    (candOf G L).cdImg = G.gxImg ∧
    (∀ i, List.map (fun s => s.esLb)
        (List.filter (fun s => decide (s.esAg = i)) (candOf G L).cdTr) = (G.gxProg[i]?).getD []) ∧
    cdLog (candOf G L) (candOf G L).cdTr.length = (gwrites G).filterMap (WeakRvwmoLin.gmsg G) :=
  fun hcons hext =>
    ⟨(tfull G L hcons hext).1, rfl, fun i => trowEq G L hext i, tlogFull G L hcons hext⟩

theorem gtraceLinearization (G : Gexec) (L : List Geid) :
    rvwmoMinusConsistent G → grule14 G → ptraceExt G L →
    srvwmoConsistent (candOf G L) ∧
    (candOf G L).cdImg = G.gxImg ∧
    (∀ i, List.map (fun s => s.esLb)
        (List.filter (fun s => decide (s.esAg = i)) (candOf G L).cdTr) = (G.gxProg[i]?).getD []) ∧
    cdLog (candOf G L) (candOf G L).cdTr.length = (gwrites G).filterMap (WeakRvwmoLin.gmsg G) :=
  fun hcons _ hext => gtraceLinearizationMin G L hcons hext

/-! # 6. T2-1c′ subsumes T2-1c, and non-vacuity -/

theorem rwf (G : Gexec) (hcons : rvwmoMinusConsistent G) : gwf G := hcons.1

theorem rgmem (G : Gexec) (hcons : rvwmoMinusConsistent G) (e : Geid) :
    e ∈ G.gxGmo → (gxLbl G e).isSome = true := by
  intro he
  obtain ⟨l, hl, -⟩ := gwfGmoMem G e hcons.1 he
  rw [hl]; rfl

theorem rkBefore (G : Gexec) (hcons : rvwmoMinusConsistent G) (x y : Geid) :
    (gxLbl G x).isSome = true → (gxLbl G y).isSome = true →
    WeakRvwmoLin.grank G x < WeakRvwmoLin.grank G y → before (glinEids G) x y := by
  intro hx hy hlt
  obtain ⟨kx, hkx⟩ := glinIndex G hcons.1 x hx
  obtain ⟨ky, hky⟩ := glinIndex G hcons.1 y hy
  refine ⟨kx, ky, hkx, hky, ?_⟩
  apply Classical.byContradiction
  intro hge
  by_cases heq : kx = ky
  · rw [heq, hky] at hkx
    obtain rfl := Option.some.inj hkx
    omega
  · have hle : WeakRvwmoLin.grank G y ≤ WeakRvwmoLin.grank G x :=
      stronglySortedLookupElim (fun a b => WeakRvwmoLin.grank G a ≤ WeakRvwmoLin.grank G b)
        (glinEids G) ky kx y x (rblocksRankSorted _ _ _) hky hkx (by omega)
    omega

theorem rkGmoW (G : Gexec) (hcons : rvwmoMinusConsistent G) (h14 : grule14 G) (w e : Geid) :
    w ∈ gwrites G → gmoLt G w e → WeakRvwmoLin.grank G w < WeakRvwmoLin.grank G e := by
  intro hw hmo
  have hwf := hcons.1
  have hnd := hwf.1
  obtain ⟨i, k⟩ := e
  have hel : (gxLbl G (i, k)).isSome = true := rgmem G hcons _ hmo.2.1
  obtain ⟨hbi, -⟩ := (gxLblBounds G (i, k)).1 hel
  rw [grankWrite G hwf w hw]
  unfold WeakRvwmoLin.grank
  cases hf : gnxw G (i, k) with
  | some u =>
    obtain ⟨m, rfl, hkm, hm, hwm, -⟩ := gnxwSome G i k u hf
    have hlm := glblSome G i m hbi hm
    have hum : (i, m) ∈ gwrites G := gisWGwrites G (i, m) hwf hlm hwm
    have hmo' : gmoLt G w (i, m) := by
      by_cases hkm' : k = m
      · rw [← hkm']; exact hmo
      · exact gmoLtTrans G _ _ _ hmo (h14 _ _ ⟨rfl, by show k < m; omega, hel, hlm⟩
          (gwfGmoMem G _ hwf hmo.2.1) (WeakRvwmoLin.gisWGlblIs G _ hlm hwm))
    exact (gwixGposLt G w (i, m) hnd hw hum).2 hmo'.2.2
  | none =>
    have := gwixLe G w hw
    show gwix G w < (gwrites G).length + 1 + i
    omega

theorem rkPo (G : Gexec) (hcons : rvwmoMinusConsistent G) (h14 : grule14 G) (x y : Geid) :
    WeakRvwmoGraph.gpo G x y → before (glinEids G) x y := by
  rintro ⟨hag, hlt, hx, hy⟩
  obtain ⟨kx, hkx⟩ := glinIndex G hcons.1 x hx
  obtain ⟨ky, hky⟩ := glinIndex G hcons.1 y hy
  exact ⟨kx, ky, hkx, hky, glinPoLt G hcons.1 h14 kx ky x y hkx hky hag hlt⟩

theorem rkRf (G : Gexec) (hcons : rvwmoMinusConsistent G) (h14 : grule14 G) (w r : Geid) :
    WeakRvwmoAcyc.grf G w r → before (glinEids G) w r := by
  rintro ⟨a, t, v, hrd, hw⟩
  cases t with
  | zero => simp [gwriteAt] at hw
  | succ n =>
    obtain ⟨hwm, -⟩ := gwriteAtInv G (n + 1) w hcons.1.1 hw
    have hmo : gmoLt G w r := WeakRvwmoLin.grfGmo G hcons.2.1 hcons.2.2.1 r a n v w hrd hw
    exact rkBefore G hcons w r (gwritesLbl G hcons.1 w hwm) (rgmem G hcons r hmo.2.1)
      (rkGmoW G hcons h14 w r hwm hmo)

theorem rkWw (G : Gexec) (hcons : rvwmoMinusConsistent G) (h14 : grule14 G) (x y : Geid) :
    gisW G x = true → gisW G y = true → gmoLt G x y → before (glinEids G) x y := by
  intro hx hy hmo
  have hlx := rgmem G hcons x hmo.1
  have hly := rgmem G hcons y hmo.2.1
  exact rkBefore G hcons x y hlx hly (rkGmoW G hcons h14 x y (gisWGwrites G x hcons.1 hlx hx) hmo)

theorem glinPtraceExt (G : Gexec) (hcons : rvwmoMinusConsistent G) (h14 : grule14 G) :
    ptraceExt G (glinEids G) := by
  refine ⟨?_, ?_⟩
  · rw [WeakRvwmoLin2.gevs'Eq]
    exact rblocksPerm _ _ _ (gevsNodup G)
      (fun x hx => grankLtBound G hcons.1 x ((elemOfGevs G x).1 hx))
  · rintro x y (hpo | hrf | ⟨hx, hy, hmo⟩)
    · exact rkPo G hcons h14 x y hpo
    · exact rkRf G hcons h14 x y hrf
    · exact rkWw G hcons h14 x y hx hy hmo

/-- T2-1c, re-derived. -/
theorem rule14Linearization' (G : Gexec) :
    rvwmoMinusConsistent G → grule14 G →
    srvwmoConsistent (candOf G (glinEids G)) ∧
    (candOf G (glinEids G)).cdImg = G.gxImg ∧
    (∀ i, List.map (fun s => s.esLb)
        (List.filter (fun s => decide (s.esAg = i)) (candOf G (glinEids G)).cdTr) =
          (G.gxProg[i]?).getD []) ∧
    cdLog (candOf G (glinEids G)) (candOf G (glinEids G)).cdTr.length =
      (gwrites G).filterMap (WeakRvwmoLin.gmsg G) :=
  fun hcons h14 => gtraceLinearizationMin G _ hcons (glinPtraceExt G hcons h14)

theorem candOfLinCand (G : Gexec) : candOf G (glinEids G) = linCand G := rfl

theorem gtraceLinearizationNonvacuous :
    ptraceExt mpg' (glinEids mpg') ∧
    srvwmoConsistent (candOf mpg' (glinEids mpg')) ∧
    (candOf mpg' (glinEids mpg')).cdTr.length = 3 := by
  have hext := glinPtraceExt mpg' mpg'Consistent mpg'Rule14
  refine ⟨hext, (gtraceLinearizationMin mpg' _ mpg'Consistent hext).1, ?_⟩
  show ((glinEids mpg').map (glinStep mpg')).length = 3
  rw [List.length_map, hext.1.length_eq]
  rfl

/-! # 7. The dev-order version -/

def ptraceRelF (GF : Gfexec) (x y : Geid) : Prop :=
  ptraceRel GF.gfGd.gdG x y ∨ gdevAdj GF x y

def gfexecConsistent' (GF : Gfexec) : Prop :=
  rvwmoMinusDepsConsistent GF.gfGd ∧ (∀ x, ¬ tc (ptraceRelF GF) x x)

instance ptraceRelDec (G : Gexec) (x y : Geid) : Decidable (ptraceRel G x y) := by
  unfold ptraceRel; infer_instance

instance ptraceRelFDec (GF : Gfexec) (x y : Geid) : Decidable (ptraceRelF GF x y) := by
  unfold ptraceRelF; infer_instance

/-! ## 7.1 The two axioms -/

theorem ptraceExtAcyclic (G : Gexec) (L : List Geid) :
    ptraceExt G L → ∀ x, ¬ tc (ptraceRel G) x x := by
  intro hext x htc
  have hnd : L.Nodup := tnd G L hext
  have hb : ∀ a b, tc (ptraceRel G) a b → before L a b := by
    intro a b h
    induction h with
    | single h => exact hext.2 _ _ h
    | tail _ h ih => exact beforeTrans L _ _ _ hnd ih (hext.2 _ _ h)
  obtain ⟨i, j, hi, hj, hij⟩ := hb x x htc
  have := NoDup_lookup hnd hi hj
  omega

theorem gfexecConsistent'Nodev (GF : Gfexec) :
    GF.gfDev = [] → rvwmoMinusDepsConsistent GF.gfGd → grule14 GF.gfGd.gdG →
    gfexecConsistent' GF := by
  intro hnil hc h14
  refine ⟨hc, ?_⟩
  have hsub : ∀ x y, ptraceRelF GF x y → ptraceRel GF.gfGd.gdG x y := by
    rintro x y (h | ⟨n, hn, -⟩)
    · exact h
    · rw [hnil] at hn; simp at hn
  intro x htc
  exact ptraceExtAcyclic _ _ (glinPtraceExt _ hc.1 h14) x (tcMono _ _ x x hsub htc)

theorem gfexecConsistentNodev (GF : Gfexec) :
    GF.gfDev = [] → rvwmoMinusDepsConsistent GF.gfGd → gfexecConsistent GF := by
  intro hnil hc
  refine ⟨hc, ?_⟩
  rintro a b ⟨n, hn, -⟩
  rw [hnil] at hn; simp at hn

/-! ## 7.2 Existence of a fabric-ordered trace -/

theorem ptraceRelMem (G : Gexec) (x y : Geid) :
    ptraceRel G x y → (gxLbl G x).isSome = true ∧ (gxLbl G y).isSome = true := by
  rintro (⟨-, -, hx, hy⟩ | ⟨a, t, v, hrd, hw⟩ | ⟨hx, hy, -⟩)
  · exact ⟨hx, hy⟩
  · refine ⟨?_, ?_⟩
    · obtain ⟨hwm, -⟩ := gwriteAtInv' G t x hw
      exact hwm
    · obtain ⟨l, -, -, -, -, hl, -⟩ := hrd
      rw [hl]; rfl
  · constructor
    · cases h : gxLbl G x with
      | none => simp [gisW, h] at hx
      | some _ => rfl
    · cases h : gxLbl G y with
      | none => simp [gisW, h] at hy
      | some _ => rfl
where
  gwriteAtInv' (G : Gexec) (t : Nat) (x : Geid) :
      gwriteAt G t = some x → (gxLbl G x).isSome = true ∧ True := by
    intro hw
    cases t with
    | zero => simp [gwriteAt] at hw
    | succ n =>
      have hw' : (gwrites G)[n]? = some x := hw
      have hwb := ((gwritesElemOf G x).1 (elem_of_list_lookup_2 hw')).2
      refine ⟨?_, trivial⟩
      cases h : gxLbl G x with
      | none => simp [gisW, h] at hwb
      | some _ => rfl

theorem ptraceExistsF (GF : Gfexec) :
    gfexecConsistent' GF →
    (∀ e, e ∈ GF.gfDev → (gxLbl GF.gfGd.gdG e).isSome = true) →
    ∃ L, ptraceExt GF.gfGd.gdG L ∧
      (∀ (m n : Nat) e e', m < n → GF.gfDev[m]? = some e → GF.gfDev[n]? = some e' → before L e e') := by
  rintro ⟨_, hacy⟩ hdev
  have hndg : (gevs' GF.gfGd.gdG).Nodup := gevsNodup _
  obtain ⟨L, hL, hord⟩ :=
    topoSortExists (ptraceRelF GF) (fun x y => ptraceRelFDec GF x y) hacy _ hndg
  have hmem : ∀ x y, ptraceRelF GF x y →
      x ∈ gevs' GF.gfGd.gdG ∧ y ∈ gevs' GF.gfGd.gdG := by
    rintro x y (hr | ⟨n, hn, hsn⟩)
    · obtain ⟨hx, hy⟩ := ptraceRelMem _ _ _ hr
      exact ⟨elemOfGevs' _ _ hx, elemOfGevs' _ _ hy⟩
    · exact ⟨elemOfGevs' _ _ (hdev _ (elem_of_list_lookup_2 hn)),
        elemOfGevs' _ _ (hdev _ (elem_of_list_lookup_2 hsn))⟩
  have hbef : ∀ x y, ptraceRelF GF x y → before L x y :=
    fun x y hr => hord x y (hmem x y hr).1 (hmem x y hr).2 hr
  have hnd : L.Nodup := hL.nodup_iff.2 hndg
  refine ⟨L, ⟨hL, fun x y hr => hbef x y (Or.inl hr)⟩, ?_⟩
  intro m n e e' hlt hm hn
  obtain ⟨d, hd⟩ : ∃ d, d = n - (m + 1) := ⟨_, rfl⟩
  induction d generalizing m n e e' with
  | zero =>
    have heq : n = m + 1 := by omega
    rw [heq] at hn
    exact hbef _ _ (Or.inr ⟨m, hm, hn⟩)
  | succ d ih =>
    have hlt2 : m + 1 < GF.gfDev.length := by have := lookup_lt_Some hn; omega
    obtain ⟨e2, he2⟩ := someOfIsSome (lookup_lt_is_Some_2 hlt2)
    exact beforeTrans L _ _ _ hnd (hbef _ _ (Or.inr ⟨m, hm, he2⟩))
      (ih (m + 1) n e2 e' (by omega) he2 hn (by omega))

/-! ## 7.3 The trace visits the dev blocks in `gfDev`'s order -/

theorem filterOrderedCount {A : Type _} [DecidableEq A] (L M : List A) (n p : Nat) (x : A) :
    L.Nodup → M.Nodup → (∀ y, y ∈ M → y ∈ L) →
    (∀ (m m' : Nat) y z, m < m' → M[m]? = some y → M[m']? = some z → before L y z) →
    M[n]? = some x → L[p]? = some x →
    ((L.take p).filter (fun y => decide (y ∈ M))).length = n := by
  intro hndL hndM hsub hord hn hp
  have hcount : ((L.take p).filter (fun y => decide (y ∈ M))).Perm (M.take n) := by
    apply NoDup_Permutation (NoDup_filter (hndL.sublist (List.take_sublist _ _)))
      (hndM.sublist (List.take_sublist _ _))
    intro y
    rw [elem_of_list_filter, elemOfTakeLookup, elemOfTakeLookup]
    constructor
    · rintro ⟨hy, q, hq, hqL⟩
      have hy := of_decide_eq_true hy
      obtain ⟨m, hm⟩ := elem_of_list_lookup_1 hy
      refine ⟨m, ?_, hm⟩
      apply Classical.byContradiction
      intro hge
      by_cases heq : m = n
      · rw [heq, hn] at hm
        obtain rfl := Option.some.inj hm
        have := NoDup_lookup hndL hqL hp
        omega
      · have hb := hord n m x y (by omega) hn hm
        have := beforeIndex L x y p q hndL hp hqL hb
        omega
    · rintro ⟨m, hmn, hm⟩
      have hyM : y ∈ M := elem_of_list_lookup_2 hm
      refine ⟨decide_eq_true hyM, ?_⟩
      obtain ⟨q, hq⟩ := elem_of_list_lookup_1 (hsub y hyM)
      exact ⟨q, beforeIndex L y x q p hndL hq hp (hord m n y x hmn hm hn), hq⟩
  rw [hcount.length_eq, List.length_take]
  have := lookup_lt_Some hn
  omega

theorem dcntFilter (G : Gexec) (L : List Geid) (GF : Gfexec) (k : Nat) :
    ptraceExt G L →
    dcnt GF (candOf G L).cdTr k = ((L.take k).filter (fun x => decide (x ∈ GF.gfDev))).length := by
  intro hext
  induction k with
  | zero => rw [dcnt0]; simp
  | succ k ih =>
    cases hk : L[k]? with
    | none =>
      have hnone : (candOf G L).cdTr[k]? = none := by
        show (L.map (glinStep G))[k]? = none
        rw [List.getElem?_map, hk]; rfl
      have hge : L.take (k + 1) = L.take k := by
        have := lookup_ge_None_1 hk
        rw [take_ge (show L.length ≤ k + 1 by omega), take_ge (show L.length ≤ k by omega)]
      rw [hge, ← ih, dcntStepNe GF _ k (by simp [dstepAt, hnone])]
    | some e =>
      have hs : (candOf G L).cdTr[k]? = some (glinStep G e) := by
        show (L.map (glinStep G))[k]? = _
        rw [List.getElem?_map, hk]; rfl
      have htk : (candOf G L).cdTr.take k = (candOf G (L.take k)).cdTr := by
        show (L.map (glinStep G)).take k = (L.take k).map (glinStep G)
        rw [List.map_take]
      have hev : ((glinStep G e).esAg, tcnt (glinStep G e).esAg ((candOf G L).cdTr.take k)) = e := by
        show (e.1, tcnt e.1 ((candOf G L).cdTr.take k)) = e
        rw [htk, tcntGcnt, tpoCount G L hext k e hk]
      have hdst : dstepAt GF (candOf G L).cdTr k = decide (e ∈ GF.gfDev) := by
        unfold dstepAt
        rw [hs]
        simp only
        rw [hev]
      rw [take_S_r hk, List.filter_append]
      by_cases hin : e ∈ GF.gfDev
      · rw [dcntStepDev GF _ k (by rw [hdst]; exact decide_eq_true hin), ih]
        simp [hin]
      · rw [dcntStepNe GF _ k (by rw [hdst]; exact decide_eq_false hin), ih]
        simp [hin]

theorem trDevOrderedOfPtrace (GF : Gfexec) (L : List Geid) :
    ptraceExt GF.gfGd.gdG L → GF.gfDev.Nodup →
    (∀ e, e ∈ GF.gfDev → (gxLbl GF.gfGd.gdG e).isSome = true) →
    (∀ (m n : Nat) e e', m < n → GF.gfDev[m]? = some e → GF.gfDev[n]? = some e' → before L e e') →
    trDevOrdered GF (candOf GF.gfGd.gdG L) := by
  intro hext hnd hlbl hord
  have hndL : L.Nodup := tnd _ L hext
  have hsub : ∀ y, y ∈ GF.gfDev → y ∈ L := fun x hx => (tmem _ L hext x).2 (hlbl x hx)
  intro k s hs hin
  cases hk : L[k]? with
  | none =>
    exfalso
    have h0 : (candOf GF.gfGd.gdG L).cdTr[k]? = none := by
      show (L.map (glinStep GF.gfGd.gdG))[k]? = none
      rw [List.getElem?_map, hk]; rfl
    rw [h0] at hs; cases hs
  | some e =>
    have hse : s = glinStep GF.gfGd.gdG e := by
      have h1 : (candOf GF.gfGd.gdG L).cdTr[k]? = some (glinStep GF.gfGd.gdG e) := by
        show (L.map (glinStep GF.gfGd.gdG))[k]? = _
        rw [List.getElem?_map, hk]; rfl
      rw [h1] at hs; exact (Option.some.inj hs).symm
    have htk : (candOf GF.gfGd.gdG L).cdTr.take k = (candOf GF.gfGd.gdG (L.take k)).cdTr := by
      show (L.map (glinStep GF.gfGd.gdG)).take k = (L.take k).map (glinStep GF.gfGd.gdG)
      rw [List.map_take]
    have hev : (s.esAg, tcnt s.esAg ((candOf GF.gfGd.gdG L).cdTr.take k)) = e := by
      rw [hse]
      show (e.1, tcnt e.1 _) = e
      rw [htk, tcntGcnt, tpoCount GF.gfGd.gdG L hext k e hk]
    rw [hev] at hin ⊢
    obtain ⟨n, hn⟩ := elem_of_list_lookup_1 hin
    have hc := filterOrderedCount L GF.gfDev n k e hndL hnd hsub hord hn hk
    have hc' : ((L.take k).filter (fun x => decide (x ∈ GF.gfDev))).length = n := by
      rw [← hc]; congr 1; apply List.filter_congr; intro x _; exact decide_eq_decide.2 Iff.rfl
    rw [dcntFilter GF.gfGd.gdG L GF k hext, hc']
    exact hn

/-! ## 7.4 The composition -/

/-- (Lean-only helper) every fabric event of a conformant bundle is labelled. -/
theorem WeakRvwmoLin2.devLbl (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec) :
    gfexecConf boot d0 fab GF →
    ∀ e, e ∈ GF.gfDev → (gxLbl GF.gfGd.gdG e).isSome = true := by
  intro hconf e he
  obtain ⟨n, hn⟩ := elem_of_list_lookup_1 he
  obtain ⟨i, k⟩ := e
  obtain ⟨row, hrow, hlt⟩ := hconf.2.2.1 n i k hn
  simp only [gxLbl, hrow, Option.bind_some]
  exact lookup_lt_is_Some_2 hlt

/-- (Deviation 3: the fetch-inertness premise.) -/
theorem fconfSupply' (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (N : Nat) (L : List Geid) :
    gfexecConf boot d0 fab GF →
    rvwmoMinusConsistent GF.gfGd.gdG →
    ptraceExt GF.gfGd.gdG L →
    (∀ (m n : Nat) e e', m < n → GF.gfDev[m]? = some e → GF.gfDev[n]? = some e' → before L e e') →
    GF.gfGd.gdG.gxProg.length ≤ N →
    candFetchInertF boot N (candOf GF.gfGd.gdG L) →
    ∃ pst : Nat → List Pexv6,
      pst 0 = (List.range' 0 N).map boot ∧
      fab (dcnt GF (candOf GF.gfGd.gdG L).cdTr 0) = d0 ∧
      execProgOk' pstepEv pclsEv pst (fun k => fab (dcnt GF (candOf GF.gfGd.gdG L).cdTr k))
        (candExec (candOf GF.gfGd.gdG L)) := by
  intro hconf _ hext hord hN hfi
  exact fconfSupply (candOf GF.gfGd.gdG L) boot d0 fab GF N hconf (fun i => trowEq _ L hext i) hN
    (trDevOrderedOfPtrace GF L hext hconf.2.1 (WeakRvwmoLin2.devLbl boot d0 fab GF hconf) hord)
    hfi

/-- THE DELIVERABLE (deviation 3: the supply conditional on `candFetchInertF`). -/
theorem fconfTraceRealize (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (N : Nat) :
    gfexecConsistent' GF →
    gfexecConf boot d0 fab GF →
    GF.gfGd.gdG.gxProg.length ≤ N →
    ∃ L : List Geid,
      srvwmoConsistent (candOf GF.gfGd.gdG L) ∧
      (candOf GF.gfGd.gdG L).cdImg = GF.gfGd.gdG.gxImg ∧
      (∀ i, List.map (fun s => s.esLb)
          (List.filter (fun s => decide (s.esAg = i)) (candOf GF.gfGd.gdG L).cdTr) =
            (GF.gfGd.gdG.gxProg[i]?).getD []) ∧
      cdLog (candOf GF.gfGd.gdG L) (candOf GF.gfGd.gdG L).cdTr.length =
        (gwrites GF.gfGd.gdG).filterMap (WeakRvwmoLin.gmsg GF.gfGd.gdG) ∧
      (candFetchInertF boot N (candOf GF.gfGd.gdG L) →
        ∃ pst : Nat → List Pexv6,
          pst 0 = (List.range' 0 N).map boot ∧
          fab (dcnt GF (candOf GF.gfGd.gdG L).cdTr 0) = d0 ∧
          execProgOk' pstepEv pclsEv pst (fun k => fab (dcnt GF (candOf GF.gfGd.gdG L).cdTr k))
            (candExec (candOf GF.gfGd.gdG L))) := by
  intro hc' hconf hN
  have hcons : rvwmoMinusConsistent GF.gfGd.gdG := hc'.1.1
  obtain ⟨L, hext, hord⟩ := ptraceExistsF GF hc' (WeakRvwmoLin2.devLbl boot d0 fab GF hconf)
  obtain ⟨h1, h2, h3, h4⟩ := gtraceLinearizationMin _ L hcons hext
  exact ⟨L, h1, h2, h3, h4,
    fun hfi => fconfSupply' boot d0 fab GF N L hconf hcons hext hord hN hfi⟩

end Weak
