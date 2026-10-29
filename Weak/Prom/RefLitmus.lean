/-
Weak/Prom: **verdict theorems `ref_<test>` of the reference** (rows 1–25).

Each theorem is the reference verdict of a §5 row (plan rev 7), proved by the kernel evaluating the enumerator's
Bool (`decide +kernel`; `exists_sound` for ALLOWED, `forbid_sound` for FORBIDDEN, `Weak/Prom/RefCheck.lean`).
Every verdict equals Table S's text verdict (`~/dev/weak-orch/promising/s0t/tableS.md` §19.1, §21) and, where
§20 names a repository test, the repository's herd result.  Every FORBIDDEN row also has `ref_<test>_exec`: the
test HAS an execution (the verdict is not vacuous).
-/
import Weak.Prom.RefTests

namespace Weak.Prom.Ref.Lit

open Weak.Prom.Ref

/-- Row 1 LB: ALLOWED. -/
theorem ref_lb : allowedRef lb := exists_sound _ (by decide +kernel)

/-- Row 2 LB+data+data: FORBIDDEN. -/
theorem ref_lbdd : forbiddenRef lbdd := forbid_sound _ (by decide +kernel)

theorem ref_lbdd_exec : allowedRef (anyOutcome lbdd) := exists_sound _ (by decide +kernel)

/-- Row 3 LB+fakedep (repo LB+datas): FORBIDDEN. -/
theorem ref_lbDatas : forbiddenRef lbDatas := forbid_sound _ (by decide +kernel)

theorem ref_lbDatas_exec : allowedRef (anyOutcome lbDatas) := exists_sound _ (by decide +kernel)

/-- Row 4 LB+ctrl+ctrl (repo LB+ctrls): FORBIDDEN. -/
theorem ref_lbCtrls : forbiddenRef lbCtrls := forbid_sound _ (by decide +kernel)

theorem ref_lbCtrls_exec : allowedRef (anyOutcome lbCtrls) := exists_sound _ (by decide +kernel)

/-- Row 4′ LB+ctrls, beq variant: FORBIDDEN. -/
theorem ref_lbCtrlsBeq : forbiddenRef lbCtrlsBeq := forbid_sound _ (by decide +kernel)

theorem ref_lbCtrlsBeq_exec : allowedRef (anyOutcome lbCtrlsBeq) := exists_sound _ (by decide +kernel)

/-- Row 5 LB+lrsc (manual litmus_lb_lrsc): FORBIDDEN. -/
theorem ref_lbLrsc : forbiddenRef lbLrsc := forbid_sound _ (by decide +kernel)

theorem ref_lbLrsc_exec : allowedRef (anyOutcome lbLrsc) := exists_sound _ (by decide +kernel)

/-- Row 6 OOTA-42: FORBIDDEN. -/
theorem ref_oota42 : forbiddenRef oota42 := forbid_sound _ (by decide +kernel)

theorem ref_oota42_exec : allowedRef (anyOutcome oota42) := exists_sound _ (by decide +kernel)

/-- Row 7 MP: ALLOWED. -/
theorem ref_mp : allowedRef mp := exists_sound _ (by decide +kernel)

/-- Row 8 MP+fence.w.w+fence.r.rw (repo): FORBIDDEN. -/
theorem ref_mpFF : forbiddenRef mpFF := forbid_sound _ (by decide +kernel)

theorem ref_mpFF_exec : allowedRef (anyOutcome mpFF) := exists_sound _ (by decide +kernel)

/-- Row 8′ MP+fence.w.w+fence.r.r: FORBIDDEN. -/
theorem ref_mpFFrr : forbiddenRef mpFFrr := forbid_sound _ (by decide +kernel)

theorem ref_mpFFrr_exec : allowedRef (anyOutcome mpFFrr) := exists_sound _ (by decide +kernel)

/-- Row 9 MP+fence.w.w+addr: FORBIDDEN. -/
theorem ref_mpFAddr : forbiddenRef mpFAddr := forbid_sound _ (by decide +kernel)

theorem ref_mpFAddr_exec : allowedRef (anyOutcome mpFAddr) := exists_sound _ (by decide +kernel)

/-- Row 10 MP+amo.rl+amo.aq: FORBIDDEN. -/
theorem ref_mpAmoRlAq : forbiddenRef mpAmoRlAq := forbid_sound _ (by decide +kernel)

theorem ref_mpAmoRlAq_exec : allowedRef (anyOutcome mpAmoRlAq) := exists_sound _ (by decide +kernel)

/-- Row 11 MP+fence.rw.w-amo+amo-fence.r.rw: FORBIDDEN. -/
theorem ref_mpFAmo : forbiddenRef mpFAmo := forbid_sound _ (by decide +kernel)

theorem ref_mpFAmo_exec : allowedRef (anyOutcome mpFAmo) := exists_sound _ (by decide +kernel)

/-- Row 11b AMO-store-part+fence.r.rw: FORBIDDEN. -/
theorem ref_amoStorePart : forbiddenRef amoStorePart := forbid_sound _ (by decide +kernel)

theorem ref_amoStorePart_exec : allowedRef (anyOutcome amoStorePart) := exists_sound _ (by decide +kernel)

/-- Row 12 SB: ALLOWED. -/
theorem ref_sbT : allowedRef sbT := exists_sound _ (by decide +kernel)

/-- Row 13 SB+fence.rw.rws: FORBIDDEN. -/
theorem ref_sbFF : forbiddenRef sbFF := forbid_sound _ (by decide +kernel)

theorem ref_sbFF_exec : allowedRef (anyOutcome sbFF) := exists_sound _ (by decide +kernel)

/-- Row 14 SB-fwd (repo SB+rfi-fence.r.rs): ALLOWED. -/
theorem ref_sbFwd : allowedRef sbFwd := exists_sound _ (by decide +kernel)

/-- Row 15 PPOCA (repo): ALLOWED. -/
theorem ref_ppoca : allowedRef ppoca := exists_sound _ (by decide +kernel)

/-- Row 16 datarfi (manual): FORBIDDEN. -/
theorem ref_datarfi : forbiddenRef datarfi := forbid_sound _ (by decide +kernel)

theorem ref_datarfi_exec : allowedRef (anyOutcome datarfi) := exists_sound _ (by decide +kernel)

/-- Row 17 datacoirfi (manual): ALLOWED. -/
theorem ref_datacoirfi : allowedRef datacoirfi := exists_sound _ (by decide +kernel)

/-- Row 17r datacoirfi (repo MP+fence.w.w+data-wsi-rfi-addr): ALLOWED. -/
theorem ref_datacoirfiR : allowedRef datacoirfiR := exists_sound _ (by decide +kernel)

/-- Row 18 addrpo (manual): FORBIDDEN. -/
theorem ref_addrpo : forbiddenRef addrpo := forbid_sound _ (by decide +kernel)

theorem ref_addrpo_exec : allowedRef (anyOutcome addrpo) := exists_sound _ (by decide +kernel)

/-- Row 18r addrpo (repo LB+fence.r.rw+addr-po): FORBIDDEN. -/
theorem ref_addrpoR : forbiddenRef addrpoR := forbid_sound _ (by decide +kernel)

theorem ref_addrpoR_exec : allowedRef (anyOutcome addrpoR) := exists_sound _ (by decide +kernel)

/-- Row 19 MP+fence.w.w+fri-rfi-addr (manual): ALLOWED. -/
theorem ref_frirfi : allowedRef frirfi := exists_sound _ (by decide +kernel)

/-- Row 20 RSW (repo): ALLOWED. -/
theorem ref_rsw : allowedRef rsw := exists_sound _ (by decide +kernel)

/-- Row 21 2+2W: ALLOWED. -/
theorem ref_w22 : allowedRef w22 := exists_sound _ (by decide +kernel)

/-- Row 21′ 2+2W+fence.w.ws: FORBIDDEN. -/
theorem ref_w22F : forbiddenRef w22F := forbid_sound _ (by decide +kernel)

theorem ref_w22F_exec : allowedRef (anyOutcome w22F) := exists_sound _ (by decide +kernel)

/-- Row 22 CoWW: FORBIDDEN. -/
theorem ref_coWW : forbiddenRef coWW := forbid_sound _ (by decide +kernel)

theorem ref_coWW_exec : allowedRef (anyOutcome coWW) := exists_sound _ (by decide +kernel)

/-- Row 22 CoWR0: FORBIDDEN. -/
theorem ref_coWR0 : forbiddenRef coWR0 := forbid_sound _ (by decide +kernel)

theorem ref_coWR0_exec : allowedRef (anyOutcome coWR0) := exists_sound _ (by decide +kernel)

/-- Row 22 CoWR (repo HAND): FORBIDDEN. -/
theorem ref_coWR : forbiddenRef coWR := forbid_sound _ (by decide +kernel)

theorem ref_coWR_exec : allowedRef (anyOutcome coWR) := exists_sound _ (by decide +kernel)

/-- Row 22 CoRW1: FORBIDDEN. -/
theorem ref_coRW1 : forbiddenRef coRW1 := forbid_sound _ (by decide +kernel)

theorem ref_coRW1_exec : allowedRef (anyOutcome coRW1) := exists_sound _ (by decide +kernel)

/-- Row 22 CoRW2: FORBIDDEN. -/
theorem ref_coRW2 : forbiddenRef coRW2 := forbid_sound _ (by decide +kernel)

theorem ref_coRW2_exec : allowedRef (anyOutcome coRW2) := exists_sound _ (by decide +kernel)

/-- Row 22 CoRR: FORBIDDEN. -/
theorem ref_coRR : forbiddenRef coRR := forbid_sound _ (by decide +kernel)

theorem ref_coRR_exec : allowedRef (anyOutcome coRR) := exists_sound _ (by decide +kernel)

/-- Row 22 CoRR2 (SLR, 4 harts): FORBIDDEN. -/
theorem ref_coRR2 : forbiddenRef coRR2 := forbid_sound _ (by decide +kernel)

theorem ref_coRR2_exec : allowedRef (anyOutcome coRR2) := exists_sound _ (by decide +kernel)

/-- Row 23 Par-Inc: FORBIDDEN. -/
theorem ref_parInc : forbiddenRef parInc := forbid_sound _ (by decide +kernel)

theorem ref_parInc_exec : allowedRef (anyOutcome parInc) := exists_sound _ (by decide +kernel)

/-- Row 24 ISA2+fence.rw.rws: FORBIDDEN. -/
theorem ref_isa2F : forbiddenRef isa2F := forbid_sound _ (by decide +kernel)

theorem ref_isa2F_exec : allowedRef (anyOutcome isa2F) := exists_sound _ (by decide +kernel)

/-- Row 24 ISA2 (plain): ALLOWED. -/
theorem ref_isa2 : allowedRef isa2 := exists_sound _ (by decide +kernel)

/-- Row 24 WRC+fence.rw.rws: FORBIDDEN. -/
theorem ref_wrcF : forbiddenRef wrcF := forbid_sound _ (by decide +kernel)

theorem ref_wrcF_exec : allowedRef (anyOutcome wrcF) := exists_sound _ (by decide +kernel)

/-- Row 24 WRC (plain): ALLOWED. -/
theorem ref_wrc : allowedRef wrc := exists_sound _ (by decide +kernel)

/-- Row 25 IRIW+ctrlfenceis: ALLOWED. -/
theorem ref_iriwCtrlFi : allowedRef iriwCtrlFi := exists_sound _ (by decide +kernel)

/-- Row 25 IRIW (plain): ALLOWED. -/
theorem ref_iriw : allowedRef iriw := exists_sound _ (by decide +kernel)

/-- Row 25 IRIW+fence.r.rws: FORBIDDEN. -/
theorem ref_iriwF : forbiddenRef iriwF := forbid_sound _ (by decide +kernel)

theorem ref_iriwF_exec : allowedRef (anyOutcome iriwF) := exists_sound _ (by decide +kernel)

end Weak.Prom.Ref.Lit
