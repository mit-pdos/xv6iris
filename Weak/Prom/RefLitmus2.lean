/-
Weak/Prom: **verdict theorems `ref_<test>` of the reference** (rows 26, 28–37, 41, 52–61).

Each theorem is the reference verdict of a §5 row (plan rev 7), proved by the kernel evaluating the enumerator's
Bool (`decide +kernel`; `exists_sound` for ALLOWED, `forbid_sound` for FORBIDDEN, `Weak/Prom/RefCheck.lean`).
Every verdict equals Table S's text verdict (`~/dev/weak-orch/promising/s0t/tableS.md` §19.1, §21) and, where
§20 names a repository test, the repository's herd result.  Every FORBIDDEN row also has `ref_<test>_exec`: the
test HAS an execution (the verdict is not vacuous).
-/
import Weak.Prom.RefTests

namespace Weak.Prom.Ref.Lit

open Weak.Prom.Ref

/-- Row 26a MP+sis: FORBIDDEN. -/
theorem ref_mix26a : forbiddenRef mix26a := forbid_sound _ (by decide +kernel)

theorem ref_mix26a_exec : allowedRef (anyOutcome mix26a) := exists_sound _ (by decide +kernel)

/-- Row 26b MP+fence.rw.rw+si: FORBIDDEN. -/
theorem ref_mix26b : forbiddenRef mix26b := forbid_sound _ (by decide +kernel)

theorem ref_mix26b_exec : allowedRef (anyOutcome mix26b) := exists_sound _ (by decide +kernel)

/-- Row 26c WRR+2W+sis: FORBIDDEN. -/
theorem ref_mix26c : forbiddenRef mix26c := forbid_sound _ (by decide +kernel)

theorem ref_mix26c_exec : allowedRef (anyOutcome mix26c) := exists_sound _ (by decide +kernel)

/-- Row 26d MIX1: ALLOWED. -/
theorem ref_mix26d : allowedRef mix26d := exists_sound _ (by decide +kernel)

/-- Row 26d MIX1, the only outcome: FORBIDDEN. -/
theorem ref_mix26dNot : forbiddenRef mix26dNot := forbid_sound _ (by decide +kernel)

theorem ref_mix26dNot_exec : allowedRef (anyOutcome mix26dNot) := exists_sound _ (by decide +kernel)

/-- Row 26e rsw1 (manual): ALLOWED. -/
theorem ref_mix26e : allowedRef mix26e := exists_sound _ (by decide +kernel)

/-- Row 26f rsw2 (manual): ALLOWED. -/
theorem ref_mix26f : allowedRef mix26f := exists_sound _ (by decide +kernel)

/-- Row 26g rsw3 (manual): ALLOWED. -/
theorem ref_mix26g : allowedRef mix26g := exists_sound _ (by decide +kernel)

/-- Row 26h LR-SC-mixed1: FORBIDDEN. -/
theorem ref_mix26h : forbiddenRef mix26h := forbid_sound _ (by decide +kernel)

theorem ref_mix26h_exec : allowedRef (anyOutcome mix26h) := exists_sound _ (by decide +kernel)

/-- Row 26i LR-SC-mixed2: FORBIDDEN. -/
theorem ref_mix26i : forbiddenRef mix26i := forbid_sound _ (by decide +kernel)

theorem ref_mix26i_exec : allowedRef (anyOutcome mix26i) := exists_sound _ (by decide +kernel)

/-- Row 28 MP+amo-data+fence.r.r: FORBIDDEN. -/
theorem ref_mpAmoData : forbiddenRef mpAmoData := forbid_sound _ (by decide +kernel)

theorem ref_mpAmoData_exec : allowedRef (anyOutcome mpAmoData) := exists_sound _ (by decide +kernel)

/-- Row 28c MP+amo-ctrl+fence.r.r: FORBIDDEN. -/
theorem ref_mpAmoCtrl : forbiddenRef mpAmoCtrl := forbid_sound _ (by decide +kernel)

theorem ref_mpAmoCtrl_exec : allowedRef (anyOutcome mpAmoCtrl) := exists_sound _ (by decide +kernel)

/-- Row 29 LB+amo-po: ALLOWED. -/
theorem ref_lbAmoPo : allowedRef lbAmoPo := exists_sound _ (by decide +kernel)

/-- Row 30 LB+amo-ad: ALLOWED. -/
theorem ref_lbAmoAd : allowedRef lbAmoAd := exists_sound _ (by decide +kernel)

/-- Row 31 LR;SC: ALLOWED. -/
theorem ref_lrsc : allowedRef lrsc := exists_sound _ (by decide +kernel)

/-- Row 31b LR;ld;SC: ALLOWED. -/
theorem ref_lrldsc : allowedRef lrldsc := exists_sound _ (by decide +kernel)

/-- Row 32 (= 26j) mixed-size SCA: FORBIDDEN. -/
theorem ref_mixSca : forbiddenRef mixSca := forbid_sound _ (by decide +kernel)

theorem ref_mixSca_exec : allowedRef (anyOutcome mixSca) := exists_sound _ (by decide +kernel)

/-- Row 35a litmus_lrsdsc: ALLOWED. -/
theorem ref_lrsdsc_a : allowedRef lrsdsc_a := exists_sound _ (by decide +kernel)

/-- Row 35b: ALLOWED. -/
theorem ref_lrsdsc_b : allowedRef lrsdsc_b := exists_sound _ (by decide +kernel)

/-- Row 35c: ALLOWED. -/
theorem ref_lrsdsc_c : allowedRef lrsdsc_c := exists_sound _ (by decide +kernel)

/-- Row 35d (mismatched address): ALLOWED. -/
theorem ref_lrsdsc_d : allowedRef lrsdsc_d := exists_sound _ (by decide +kernel)

/-- Row 36 LR;AMO;SC: ALLOWED. -/
theorem ref_lrAmoSc : allowedRef lrAmoSc := exists_sound _ (by decide +kernel)

/-- Row 37 LR;SC-fail;SC: FORBIDDEN. -/
theorem ref_lrScSc : forbiddenRef lrScSc := forbid_sound _ (by decide +kernel)

theorem ref_lrScSc_exec : allowedRef (anyOutcome lrScSc) := exists_sound _ (by decide +kernel)

/-- Row 41 LB+misa: ALLOWED. -/
theorem ref_lbMisa : allowedRef lbMisa := exists_sound _ (by decide +kernel)

/-- Row 52 write subsumption: FORBIDDEN. -/
theorem ref_wsub : forbiddenRef wsub := forbid_sound _ (by decide +kernel)

theorem ref_wsub_exec : allowedRef (anyOutcome wsub) := exists_sound _ (by decide +kernel)

/-- Row 53 ARM-weak: FORBIDDEN. -/
theorem ref_armWeak : forbiddenRef armWeak := forbid_sound _ (by decide +kernel)

theorem ref_armWeak_exec : allowedRef (anyOutcome armWeak) := exists_sound _ (by decide +kernel)

/-- Row 54 LBa: FORBIDDEN. -/
theorem ref_lbAcq : forbiddenRef lbAcq := forbid_sound _ (by decide +kernel)

theorem ref_lbAcq_exec : allowedRef (anyOutcome lbAcq) := exists_sound _ (by decide +kernel)

/-- Row 55 LBr: FORBIDDEN. -/
theorem ref_lbRel : forbiddenRef lbRel := forbid_sound _ (by decide +kernel)

theorem ref_lbRel_exec : allowedRef (anyOutcome lbRel) := exists_sound _ (by decide +kernel)

/-- Row 56 Upd-Stuck: ALLOWED. -/
theorem ref_updStuck : allowedRef updStuck := exists_sound _ (by decide +kernel)

/-- Row 57 COH: FORBIDDEN. -/
theorem ref_coh : forbiddenRef coh := forbid_sound _ (by decide +kernel)

theorem ref_coh_exec : allowedRef (anyOutcome coh) := exists_sound _ (by decide +kernel)

/-- Row 58 SEQ: FORBIDDEN. -/
theorem ref_seqT : forbiddenRef seqT := forbid_sound _ (by decide +kernel)

theorem ref_seqT_exec : allowedRef (anyOutcome seqT) := exists_sound _ (by decide +kernel)

/-- Row 59 LBfd: FORBIDDEN. -/
theorem ref_lbfd : forbiddenRef lbfd := forbid_sound _ (by decide +kernel)

theorem ref_lbfd_exec : allowedRef (anyOutcome lbfd) := exists_sound _ (by decide +kernel)

/-- Row 60 RNG: FORBIDDEN. -/
theorem ref_rng : forbiddenRef rng := forbid_sound _ (by decide +kernel)

theorem ref_rng_exec : allowedRef (anyOutcome rng) := exists_sound _ (by decide +kernel)

/-- Row 61 Disjoint-Lists: FORBIDDEN. -/
theorem ref_disjLists : forbiddenRef disjLists := forbid_sound _ (by decide +kernel)

theorem ref_disjLists_exec : allowedRef (anyOutcome disjLists) := exists_sound _ (by decide +kernel)


/-! ## Table S probe IO-AQ (finding F-S3): acquire does not order a RAM AMO before an I/O store -/

/-- An I/O region (PMA: not strongly ordered, channel 0). -/
def mmio : Nat := 0x10000000

/-- IO-AQ: H0 `li t,1; amoswap.w.aq a0,t,(lock); li t2,1; sw t2,(mmio)`, `lock = x` (RAM). -/
def ioAq : Test := ⟨[[li 5 1, amoswapW true false 10 5 8, li 7 1, sw 7 9]], [[(8, X), (9, mmio)]], [],
  [⟨mmio, mmio + 0x1000, false, 0⟩], .tt⟩

/-- IO-AQ: ALLOWED — an execution whose gmo puts the MMIO store BEFORE the acquiring AMO (mm-explanatory.adoc:
1149–1153 "acquire and release ordering annotations apply only from one memory operation to another memory
operation and from one I/O operation to another I/O operation, but not from a memory operation to an I/O nor vice
versa").  The old encoding's `gacqPo` (WeakRvwmoGraph.lean:245–246) forbids it (Table S F-S3). -/
theorem ref_ioAq : ∃ ν g, progExec ioAq [[]] ν g ∧ gB g (0, 1) (0, 0) = true := by
  obtain ⟨ν, h1, _, h3⟩ := probe_sound ioAq [[]] [(0, 1), (0, 0)] (fun g => gB g (0, 1) (0, 0))
    (by decide +kernel)
  exact ⟨ν, _, h1, h3⟩

/-- The same-class contrast: with the store to RAM, acquire orders it (rule 5).  MP-shaped observation:
H0 `amoswap.w.aq a0,t,(x); sw t2,(y)` ‖ H1 `lw b0,(y); fence r,r; lw b1,(x)`; FORBIDDEN (b0=1 ∧ b1=0). -/
def ramAq : Test := mk [[li 5 1, amoswapW true false 10 5 8, li 7 1, sw 7 9], [lw 10 9, fRR, lw 11 8]]
  [[(8, X), (9, Y)], [(8, X), (9, Y)]] [] (ands [r 1 10 1, r 1 11 0])

theorem ref_ramAq : forbiddenRef ramAq := forbid_sound _ (by decide +kernel)
theorem ref_ramAq_exec : allowedRef (anyOutcome ramAq) := exists_sound _ (by decide +kernel)

end Weak.Prom.Ref.Lit
