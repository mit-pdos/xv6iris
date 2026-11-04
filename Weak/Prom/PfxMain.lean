/-
Weak/Prom: **S3d — THE PREFIX LEMMA (NA-1), S3a scope** (plan rev 7 §0 "(T-inf)", §6 S3d, §8 S3d, §9 Q1;
owner ruling [OWN.P4]).

`rvwmo_prefix`: for every (possibly infinite) execution `E` of a test in the S3a scope (`progS3aB`: no I/O; ALU,
plain loads/stores of any size, FENCE, FENCE.TSO, branches and jumps to ANY target (loops), `csrr`, `fence.i`,
`nop`) that the reference allows (`infExec`: the harts run the program, the path conditions hold, `rvwmoRefInf` —
Ref.lean's axioms over a gmo RELATION with the progress axiom), and every finite list `O` of its memory
operations, there is a FINITE PARTIAL EXECUTION (`partExec`: every hart stopped after finitely many steps, path
conditions, Ref.lean's `rvwmoRef`) in which every event of every hart up to an observed one is EXACTLY `E`'s
(skeleton, address, bytes read, bytes written).

The witness is the cut of PfxCut.lean (`trsC`, `νC`, `gC`).  Its legality: `rvwmoRef_XC` (gmoWf; evWf; ppoAx —
PfxPpo.lean; the load value axiom — PfxVal.lean; atomicity and §zalrsc vacuous in scope), `condsOk_C` (every path
condition and every address only mentions loads of `Gl`, which keep their values).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.PfxPpo

noncomputable section

namespace Weak.Prom.Pfx

open Classical
open Weak.Prom.Ref
open Weak.Prom.Cmp (progS3aB)
open Cut

section lemmas

variable {E : IExec} {O : List EvId} (H : Hyp E O)
include H

theorem XC_rdat {r : EvId} (hr : inD E O r) (hl : (E.sk r).kind.isLoad = true) :
    ((XC E O).ev r).rdat = νC E O r := by
  have hl' : (E.sev r).sk.kind.isLoad = true := hl
  rw [XC_ev H hr]; unfold concEv; simp only; rw [if_pos hl']

theorem rvwmoRef_XC : rvwmoRef (XC E O) := by
  apply (rvwmoRef_iff _).2
  refine ⟨⟨gC_nodup H, fun e he => ?_, fun e he hm => ?_⟩, fun e he => ⟨fun hl => ?_, fun hs => ?_⟩,
    ppoAx_XC H, lva_XC H, ?_, ?_⟩
  · have hD := (mem_gC H e).1 he
    have hi := ((mem_Dm H e).1 hD).1
    exact ⟨(XC_ids H e).2 hi, by rw [XC_sk H hi]; exact ((mem_Dm H e).1 hD).2⟩
  · have hi := (XC_ids H e).1 he
    rw [XC_sk H hi] at hm
    exact (mem_gC H e).2 ((mem_Dm H e).2 ⟨hi, hm⟩)
  · have hi := (XC_ids H e).1 he
    rw [XC_sk H hi] at hl ⊢
    have hrl : e ∈ Dl E O := List.mem_filter.2 ⟨(mem_Dm H e).2 ⟨hi, Kind.isMem_of_isLoad _ hl⟩, hl⟩
    rw [XC_rdat H hi hl, νC_fix H hrl]
    unfold nb; simp
  · have hi := (XC_ids H e).1 he
    rw [XC_sk H hi] at hs ⊢
    have hs' : (E.sev e).sk.kind.isStore = true := hs
    rw [XC_ev H hi]; unfold concEv; simp only; rw [if_pos hs']
    simp [byteList]; rfl
  · intro r hr w _ hp
    exfalso
    have hri := (XC_ids H r).1 hr
    unfold pairedS at hp
    rw [XC_sk H hri] at hp
    rcases kind_frag H (inD_has H hri) with hk | hk | ⟨f, hk⟩ <;> simp [hk] at hp
  · intro w hw hsc
    exfalso
    have hwi := (XC_ids H w).1 hw
    rw [XC_sk H hwi] at hsc
    rcases kind_frag H (inD_has H hwi) with hk | hk | ⟨f, hk⟩ <;> rw [hk] at hsc <;> cases hsc

/-- An expression over loads of `Gl` evaluates as in `E`. -/
theorem eval_G {μ : Val} (hμ : AgreeG E O μ) {x : Ex} (hx : ∀ v ∈ x.vars, v ∈ Gl E O) : x.eval μ = x.eval E.ν :=
  Ex.eval_congr _ _ _ (fun v hv => hμ v (hx v hv))

/-- **The path conditions and the alignment of the cut.** -/
theorem condsOk_C : condsOk (νC E O) (trsC E O) = true := by
  unfold condsOk
  apply List.all_eq_true.2
  intro s hs
  obtain ⟨h, hh, rfl⟩ : ∃ h, h < E.T.harts.length ∧ s = E.st h (kcut E O h) := by
    unfold trsC at hs
    obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hs
    exact ⟨h, List.mem_range.1 hh, rfl⟩
  have hE := H.conds h hh (kcut E O h)
  unfold condsOk at hE
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, List.all_eq_true] at hE ⊢
  obtain ⟨hc1, hc2⟩ := hE
  have hcut := kcut_spec H hh
  refine ⟨fun c hc => ?_, fun se hse => ?_⟩
  · have hv := hcut.2 c hc
    obtain ⟨cc, a, b, t⟩ := c
    have := hc1 _ hc
    simp only at this hv ⊢
    rw [eval_G H (agreeG_νC H) (fun v h' => hv v (List.mem_append_left _ h')),
      eval_G H (agreeG_νC H) (fun v h' => hv v (List.mem_append_right _ h'))]
    exact this
  · have := hc2 se hse
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hse
    have hl : i < cut E O h := by rw [← hcut.1]; exact hi
    have hsev := sev_eq H.conf H.frag hh hi
    rw [List.getElem?_eq_getElem hi, hget, Option.some.injEq] at hsev
    have hiD : inD E O (h, i) := ⟨hh, hl⟩
    have hpa := concC_pa H (agreeG_νC H) (gC E O) hiD
    rw [concC_ev H _ _ hiD] at hpa
    have hpa' : (E.sev (h, i)).addr.eval (νC E O) = (E.sev (h, i)).addr.eval E.ν := hpa
    rw [← hsev] at hpa'
    rw [hpa']; exact this

/-- **The cut is a finite partial execution.** -/
theorem partExec_C : partExec E.T (trsC E O) (νC E O) (gC E O) := by
  refine ⟨trsC_len H, fun h hh => ?_, condsOk_C H, rvwmoRef_XC H⟩
  have hh' : h < E.T.harts.length := by rw [trsC_len H] at hh; exact hh
  have : (trsC E O)[h] = E.st h (kcut E O h) := by
    have := trsC_get H hh'
    rw [List.getElem?_eq_getElem hh, Option.some.injEq] at this; exact this
  rw [this]; exact reach H.conf H.frag hh' _

/-- **Every event of po-down(O) is exactly `E`'s.** -/
theorem agree_C {o : EvId} (ho : o ∈ O) {i : Nat} (hi : i ≤ o.2) :
    (o.1, i) ∈ (XC E O).ids ∧ (XC E O).ev (o.1, i) = E.ev (o.1, i) := by
  have hoD : inD E O o := Al_inD H (List.mem_append_left _ ho)
  have hiD : inD E O (o.1, i) := inD_of_le H hoD hi
  have hP : ∀ j ≤ i, (o.1, j) ∈ Pl O := fun j hj => (mem_Pl H _).2 ⟨o, ho, rfl, by simp; omega⟩
  refine ⟨(XC_ids H _).2 hiD, ?_⟩
  rw [XC_ev H hiD]
  have hih := inD_has H hiD
  have hpa := concC_pa H (agreeG_νC H) (gC E O) hiD
  rw [concC_ev H _ _ hiD] at hpa
  unfold IExec.ev concEv at hpa ⊢
  simp only at hpa ⊢
  rw [hpa]
  congr 1
  · split
    · rename_i hl
      exact agreeG_νC H _ (Pl_Gl H (hP i (Nat.le_refl _)) ⟨hih, Kind.isMem_of_isLoad _ hl⟩)
    · rfl
  · split
    · congr 1
      apply eval_G H (agreeG_νC H)
      intro v hv
      obtain ⟨hv1, hv2⟩ := wval_vars H.conf H.frag hiD.1 hih hv
      obtain ⟨hlt, hvm⟩ := deps_mem H.conf H.frag hiD.1 hih (d := v.2) (Or.inr (Or.inl hv2))
      obtain ⟨v1, v2⟩ := v
      simp only at hv1 hlt hvm; subst v1
      exact Pl_Gl H (hP v2 (Nat.le_of_lt hlt)) hvm
    · rfl

end lemmas

/-- **THE PREFIX LEMMA (NA-1), S3a scope.**  Every finite set of memory operations of a (possibly infinite)
execution that the reference allows is reproduced — with every event of every hart up to an observed one exactly
as in `E` — by a FINITE PARTIAL EXECUTION of the same program that the (finite) reference allows. -/
theorem rvwmo_prefix {T : Test} (hT : progS3aB T = true) {E : IExec} (hE : infExec T E) (O : List EvId)
    (hO : ∀ e ∈ O, E.isMem e) :
    ∃ (trs : List SSt) (ν : Val) (g : List EvId), partExec T trs ν g ∧
      ∀ o ∈ O, ∀ i ≤ o.2, (o.1, i) ∈ (conc T trs ν g).ids ∧ (conc T trs ν g).ev (o.1, i) = E.ev (o.1, i) := by
  obtain ⟨hET, hconf, hconds, href⟩ := hE
  subst hET
  have hio : E.T.io = [] := by
    simp only [progS3aB, Bool.and_eq_true, List.isEmpty_iff] at hT; exact hT.1.1
  have H : Hyp E O := ⟨hconf, hconds, href, fragT_of hT, hio, hO⟩
  exact ⟨trsC E O, νC E O, gC E O, partExec_C H, fun o ho i hi => agree_C H ho hi⟩

end Weak.Prom.Pfx

end
