/-
Weak: **W9a (B) B5 cycRun — the execute stage, part 2: the control transfers and the CSR reads**
([OWN.85] Q-B5-CYCLE = C1; report `PROGRESS-cycRun.md`).  Lean-only.

* `cyDf`: the cycle predicate together with B1's dataflow fact of the same tree (both follow the
  same dataflow bookkeeping along every path).
* `cyJumpTo`: Sail's `jump_to t` (`BaseInsts.lean:250`) on the kernel configuration — the
  extension check is the default (`none`), `Ext_Zca` is enabled (so no misaligned-target trap),
  `nextPC := t`, `RETIRE_SUCCESS`.

Every helper is `Weak.PinCycRun.*`.
-/
import Weak.PinCycRunExec

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open KernelPinsDef

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

namespace PinCycRun
open SailCycleOrderK PinDataflow
open PinCycRunFp (pfB pf pfT pfProt pfRegOk pfW isTrapR resTrap)

/-! ## 1. The cycle predicate with B1's dataflow -/

/-- **THE PRODUCT** (header): `cyB` and `dfB` of the same tree give `cyB` with both posts. -/
theorem cyDf {X : Type} (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (S : Register → Bool)
    (T : CySt → (r : Register) → RegisterType r → Prop) (Q : X → CySt → Prop)
    (Pd : X → DfSt → Prop) :
    ∀ (m : SailM X) (st : CySt), RbootAll st.rv → cyB A Aa S T Q m st → dfB Pd m st.d →
      cyB A Aa S T (fun x st' => Q x st' ∧ Pd x st'.d) m st := by
  intro m
  induction m with
  | pure x => intro st _ hq hd; exact ⟨hq, hd⟩
  | impure call k ih =>
    intro st hrb hq hd
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead r =>
        intro v hv
        exact ih v (cyRd st r) hrb (hq v hv) (hd v (PinCycRun.rdRboot st r v hrb hv))
      case regWrite r v =>
        refine ⟨hq.1, fun hs => ⟨(hq.2 hs).1, fun u => ?_⟩⟩
        exact ih u (cyWr st r v) (rbootAllSet _ r v hrb (hq.2 hs).1) ((hq.2 hs).2 u) (hd.2 u)
      case memRead n va req =>
        exact ⟨fun h1 h2 ha w hw => ih _ _ hrb (hq.1 h1 h2 ha w hw) (hd _),
          fun h w => ih _ st hrb (hq.2 h w) (hd _)⟩
      case instrAnnounce n w => exact ⟨hq.1, fun u => ih u _ hrb (hq.2 u) (hd u)⟩
      case getCycleCount => exact ih _ st hrb hq (hd _)
      all_goals exact fun v => ih v st hrb (hq v) (hd v)

/-! ## 2. `jump_to` -/

/-- The state after `nextPC := t`: the mirror's `nextPC` set, everything else kept. -/
def jumpRel (t : BitVec 64) (st st' : CySt) : Prop :=
  st'.rv = st.rv.set .nextPC t ∧ st'.fe = st.fe ∧ st'.an = st.an ∧ st'.d.ro = st.d.ro ∧
  st'.d.n = st.d.n ∧ st'.d.ok = st.d.ok

set_option maxHeartbeats 4000000 in
/-- **`jump_to t`** (header): on the kernel configuration it sets `nextPC := t` and retires. -/
theorem cyJumpTo {Y : Type} (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop)
    (T : CySt → (r : Register) → RegisterType r → Prop) (Q : Y → CySt → Prop) (t : BitVec 64)
    (f : ExecutionResult → SailM Y) (st : CySt) (hcfg : kCfg st.rv) (hrb : RbootAll st.rv)
    (hk : ∀ st', jumpRel t st st' → cyB A Aa cyS T Q (f RETIRE_SUCCESS) st') :
    cyB A Aa cyS T Q (jump_to t >>= f) st := by
  unfold jump_to
  simp only [ext_control_check_pc, SailME.run, PreSail.PreSailME.run, ExceptT.run_bind,
    run_liftM, pure_bind, bind_assoc, assert]
  refine cyAssertBind A Aa T _ _ _ _ _ (fun _ => ?_)
  -- the tail common to both arms: `nextPC := t`, retire
  have hset : ∀ st1 : CySt, st1.rv = st.rv → st1.fe = st.fe → st1.an = st.an →
      st1.d.ro = st.d.ro → st1.d.n = st.d.n → st1.d.ok = st.d.ok →
      cyB A Aa cyS T Q (ExceptT.run (liftM (set_next_pc t) >>= fun _ => pure RETIRE_SUCCESS) >>=
        fun x => (match x with
          | Except.error (Sum.inr e) => pure e
          | Except.error (Sum.inl e) => throw e
          | Except.ok e => pure e) >>= f) st1 := by
    intro st1 e1 e2 e3 e4 e5 e6
    simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, set_next_pc, branch_announce,
      PreSail.branch_announce]
    intro u
    refine cyWriteBind _ _ _ _ _ (by decide) trivial ?_
    have hW := PinCycRun.dfWrNextPC st1.d
    exact hk _ ⟨by show st1.rv.set .nextPC t = _; rw [e1], e2, e3, hW.2.2.trans e4,
      hW.1.trans e5, hW.2.1.trans e6⟩
  by_cases hb : bit_to_bool (BitVec.access t 1) = true
  · simp only [hb, if_true, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
    refine cyBBind (fun z st' => z = true ∧ st'.rv = st.rv ∧ st'.fe = st.fe ∧ st'.an = st.an ∧
      st'.d.ro = st.d.ro ∧ st'.d.n = st.d.n ∧ st'.d.ok = st.d.ok) _ _ _ _ ?_ (fun z st1 h => ?_)
    · exact cyOfRunRead A Aa cyS T drefS _ _ _ _ true true PinCycRun.zcaOn
        (SailCycleOrderFp.fpCurrentlyEnabled _) (PinCycRun.drefAgree _ hcfg) hrb
        (fun st' e1 e2 e3 e4 e5 e6 => ⟨rfl, e1, e2, e3, e4, e5, e6⟩)
    · obtain ⟨rfl, e1, e2, e3, e4, e5, e6⟩ := h
      simp only [Functions.not, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
      exact hset st1 e1 e2 e3 e4 e5 e6
  · simp only [hb, Bool.false_eq_true, ↓reduceIte, pure_bind]
    exact hset st rfl rfl rfl rfl rfl rfl

/-! ## 3. Branches and jumps -/

/-- A footprint keeps the dataflow state's role. -/
theorem PinCycRun.dfRoKeep {X : Type} (P : X → Prop) :
    ∀ (m : SailM X) (d : DfSt), pfB false P m → dfB (fun _ d' => d'.ro = d.ro) m d := by
  intro m
  induction m with
  | pure x => intro _ _; rfl
  | impure call k ih =>
    intro d hp
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead r => exact fun v hv => ih v (dfRd d r) (hp v hv)
      case regWrite r v => exact ⟨hp.1.1, fun u => ih u (dfWr d r) (hp.2 u)⟩
      case memRead => exact fun v => ih v d (hp.2 v)
      case instrAnnounce => exact hp.elim
      case barrier => exact fun v => ih v d hp.2
      all_goals exact fun v => ih v d (hp v)

/-- The `pfB` lift of a bound stretch, keeping the frame and the role. -/
theorem cyLiftK {X Y : Type} (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop)
    (T : CySt → (r : Register) → RegisterType r → Prop) (P : X → Prop) (Q : Y → CySt → Prop)
    (m : SailM X) (f : X → SailM Y) (st : CySt) (hp : pfB false P m) (hrb : RbootAll st.rv)
    (hk : ∀ x st', P x → cyFrame st st' → st'.d.ro = st.d.ro → cyB A Aa cyS T Q (f x) st') :
    cyB A Aa cyS T Q (m >>= f) st := by
  refine cyBBind (fun x st' => P x ∧ cyFrame st st' ∧ st'.d.ro = st.d.ro) Q m f st ?_
    (fun x st' h => hk x st' h.1 h.2.1 h.2.2)
  refine cyOfPfDf A Aa cyS T ?_ P _ _ m st hp (PinCycRun.dfRoKeep P m st.d hp) hrb
    (fun x st' h1 h2 h3 => ⟨h1, h2, h3⟩)
  intro r hr
  simp only [cyS, Bool.or_eq_true, decide_eq_true_eq] at hr
  rcases hr with rfl | rfl <;> rfl

/-- A control transfer's post: retired, the log, the flag, the role kept, the protected mirror
kept but `nextPC`, whose new value `ok` admits. -/
def ctlPost (ok : BitVec 64 → Prop) (st : CySt) (r : ExecutionResult) (st' : CySt) : Prop :=
  r = RETIRE_SUCCESS ∧ st'.fe = st.fe ∧ st'.an = st.an ∧ st'.d.ro = st.d.ro ∧ RbootAll st'.rv ∧
  (∀ r', pfProt r' = true → r' ≠ .nextPC → st'.rv r' = st.rv r') ∧ ok (st'.rv .nextPC)

theorem PinCycRun.jumpPost (ok : BitVec 64 → Prop) (t : BitVec 64) (st st1 st' : CySt)
    (hf : cyFrame st st1) (hro : st1.d.ro = st.d.ro) (hj : jumpRel t st1 st') (ht : ok t) :
    ctlPost ok st RETIRE_SUCCESS st' := by
  obtain ⟨e1, e2, e3, e4, -, -⟩ := hj
  refine ⟨rfl, e2.trans hf.2.2.1, e3.trans hf.2.2.2, e4.trans hro, ?_, ?_, ?_⟩
  · rw [e1]; exact rbootAllSet _ _ _ hf.2.1 trivial
  · intro r hr hne; rw [e1, RegFile.set_other _ _ _ _ hne]; exact hf.1 r hr
  · rw [e1, RegFile.set_same]; exact ht

set_option maxHeartbeats 40000000 in
/-- **A conditional branch** (header): retired, `nextPC` kept (not taken) or `PC + imm`. -/
theorem cyExecBtype (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop)
    (T : CySt → (r : Register) → RegisterType r → Prop) (imm : BitVec 13) (rs2 rs1 : regidx)
    (op : bop) (st : CySt) (hcfg : kCfg st.rv) (hrb : RbootAll st.rv) :
    cyB A Aa cyS T (ctlPost (fun v => v = st.rv .nextPC ∨
      v = st.rv .PC + sign_extend (m := 64) imm) st) (execute_BTYPE imm rs2 rs1 op) st := by
  unfold execute_BTYPE
  refine cyLiftK A Aa T (fun _ => True) _ _ _ st (by cases op <;> pf_walk) hrb
    (fun taken st1 _ hf hro => ?_)
  cases taken
  · exact ⟨rfl, hf.2.2.1, hf.2.2.2, hro, hf.2.1, fun r hr _ => hf.1 r hr,
      Or.inl (hf.1 .nextPC (by decide))⟩
  · simp only [if_true]
    refine cyReadBind _ _ _ _ (fun v hv => ?_)
    have e : v = st.rv .PC := by
      rw [PinCycRun.rdMirror _ _ _ (by decide) hv]; exact hf.1 .PC (by decide)
    subst e
    have hcfg1 : kCfg (cyRd st1 .PC).rv := PinCycRun.kCfgProt _ _ (fun r hr _ _ => hf.1 r hr) hcfg
    have := cyJumpTo A Aa T (ctlPost (fun v => v = st.rv .nextPC ∨
      v = st.rv .PC + sign_extend (m := 64) imm) st) (st.rv .PC + sign_extend (m := 64) imm) pure
      (cyRd st1 .PC) hcfg1 hf.2.1
      (fun st' hj => PinCycRun.jumpPost _ _ st (cyRd st1 .PC) st' hf hro hj (Or.inr rfl))
    simpa only [bind_pure] using this

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfWXBits (rd : regidx) (v : BitVec 64) : pfT (wX_bits rd v) := by
  pf_walk

set_option maxHeartbeats 40000000 in
/-- **A direct jump** (header): retired, `nextPC = PC + imm`. -/
theorem cyExecJal (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop)
    (T : CySt → (r : Register) → RegisterType r → Prop) (imm : BitVec 21) (rd : regidx)
    (st : CySt) (hcfg : kCfg st.rv) (hrb : RbootAll st.rv) :
    cyB A Aa cyS T (ctlPost (fun v => v = st.rv .PC + sign_extend (m := 64) imm) st)
      (execute_JAL imm rd) st := by
  unfold execute_JAL get_next_pc
  try simp only [bind_assoc]
  refine cyReadBind _ _ _ _ (fun link _ => ?_)
  refine cyReadBind _ _ _ _ (fun v hv => ?_)
  have e : v = st.rv .PC := PinCycRun.rdMirror _ _ _ (by decide) hv
  subst e
  have hcfg2 : kCfg (cyRd (cyRd st .nextPC) .PC).rv := hcfg
  refine cyJumpTo A Aa T _ _ _ _ hcfg2 hrb (fun st2 hj => ?_)
  refine cyLiftK A Aa T (fun _ => True) _ _ _ st2 (pfWXBits _ _) ?_ (fun u st3 _ hf hro => ?_)
  · obtain ⟨e1, -⟩ := hj; rw [e1]; exact rbootAllSet _ _ _ hrb trivial
  · obtain ⟨e1, e2, e3, e4, -, -⟩ := hj
    refine ⟨rfl, hf.2.2.1.trans e2, hf.2.2.2.trans e3, hro.trans e4, hf.2.1, ?_, ?_⟩
    · intro r hr hne
      rw [hf.1 r hr, e1, RegFile.set_other _ _ _ _ hne]
      rfl
    · rw [hf.1 .nextPC (by decide), e1, RegFile.set_same]

/-! ## 4. The CSR reads -/

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfReadCSR (c : BitVec 12) : pfT (read_CSR c) := by
  pf_walk

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfRXBits (r : regidx) : pfT (rX_bits r) := by
  pf_walk

set_option maxHeartbeats 40000000 in
/-- **A CSR read** `csrrs rd, c, x0` (header): given that the access check passes on the kernel
configuration, retired, `nextPC` kept. -/
theorem cyExecCsrRead (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop)
    (T : CySt → (r : Register) → RegisterType r → Prop) (c : BitVec 12) (rd : regidx)
    (hc1 : c ≠ 0x344#12) (hc2 : c ≠ 0x144#12)
    (hchk : ∀ st : CySt, kCfg st.rv → RbootAll st.rv →
      cyB A Aa cyS T (fun x st' => x = .CSR_Check_OK () ∧ cyFrame st st' ∧ st'.d.ro = st.d.ro)
        (check_CSR_result c Privilege.Supervisor .CSRRead) st)
    (st : CySt) (hcfg : kCfg st.rv) (hrb : RbootAll st.rv) :
    cyB A Aa cyS T (ctlPost (fun v => v = st.rv .nextPC) st)
      (execute_CSRReg c (regidx.Regidx 0#5) rd .CSRRS) st := by
  unfold execute_CSRReg doCSR
  have hacc : csr_access_type csrop.CSRRS (rd == zreg) (regidx.Regidx 0#5 == zreg) =
      .CSRRead := by
    cases (rd == zreg) <;> rfl
  simp only [hacc]
  refine cyLiftK A Aa T _ _ _ _ st (pfRXBits _) hrb (fun v1 st1 _ hf1 hro1 => ?_)
  refine cyReadBind _ _ _ _ (fun p hp => ?_)
  have ep : p = Privilege.Supervisor := by
    rw [PinCycRun.rdMirror _ _ _ (by decide) hp, hf1.1 .cur_privilege (by decide)]; exact hcfg.1
  subst ep
  have hcfg1 : kCfg (cyRd st1 .cur_privilege).rv :=
    PinCycRun.kCfgProt _ _ (fun r hr _ _ => hf1.1 r hr) hcfg
  refine cyBBind _ _ _ _ _ (hchk _ hcfg1 hf1.2.1) (fun x st3 h3 => ?_)
  obtain ⟨rfl, hf3, hro3⟩ := h3
  have hf13 : cyFrame st st3 := cyFrameTrans _ _ _ hf1 hf3
  refine cyReadBind _ _ _ _ (fun p2 _ => ?_)
  simp only [ext_check_CSR, Functions.not, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine cyLiftK A Aa T _ _ _ _ _ (pfReadCSR c) hf13.2.1 (fun rv st4 _ hf4 hro4 => ?_)
  have hf14 : cyFrame st st4 := cyFrameTrans _ _ _ hf13 hf4
  split
  case isFalse h => exact absurd (by decide) h
  case isTrue =>
    simp only [pure_bind]
    refine cyLiftK A Aa T (fun _ => True) _ _ _ _ (by unfold csr_id_read_callback; pf_walk)
      hf14.2.1 (fun u st5 _ hf5 hro5 => ?_)
    refine cyLiftK A Aa T _ _ _ _ _ (pfWXBits _ _) hf5.2.1 (fun u2 st6 _ hf6 hro6 => ?_)
    have hf16 : cyFrame st st6 := cyFrameTrans _ _ _ (cyFrameTrans _ _ _ hf14 hf5) hf6
    exact ⟨rfl, hf16.2.2.1, hf16.2.2.2,
      hro6.trans (hro5.trans (hro4.trans (hro3.trans hro1))), hf16.2.1,
      fun r hr _ => hf16.1 r hr, hf16.1 .nextPC (by decide)⟩

/-- A passing access check, decided. -/
def chkOkB (o : Option (CSRCheckResult × Bool)) : Bool :=
  match o with
  | some (.CSR_Check_OK (), true) => true
  | _ => false

theorem PinCycRun.chkOfB (o : Option (CSRCheckResult × Bool)) (h : chkOkB o = true) :
    o = some (.CSR_Check_OK (), true) := by
  unfold chkOkB at h
  split at h
  · rfl
  · cases h

theorem PinCycRun.sepcCheck :
    runRead drefS (check_CSR_result 0x141#12 Privilege.Supervisor .CSRRead) =
      some (.CSR_Check_OK (), true) :=
  PinCycRun.chkOfB _ (by decide +kernel)

/-- The access check of `csrr rd, sepc` on the kernel configuration. -/
theorem cyCheckSepc (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop)
    (T : CySt → (r : Register) → RegisterType r → Prop) (st : CySt) (hcfg : kCfg st.rv)
    (hrb : RbootAll st.rv) :
    cyB A Aa cyS T (fun x st' => x = .CSR_Check_OK () ∧ cyFrame st st' ∧ st'.d.ro = st.d.ro)
      (check_CSR_result 0x141#12 Privilege.Supervisor .CSRRead) st :=
  cyOfRunRead A Aa cyS T drefS _ _ _ _ _ _ PinCycRun.sepcCheck
    (SailCycleOrderFp.fpCheckCSRResult _ _ _) (PinCycRun.drefAgree _ hcfg) hrb
    (fun st' e1 e2 e3 e4 _ _ => ⟨rfl, ⟨fun r _ => by rw [e1], by rw [e1]; exact hrb, e2, e3⟩, e4⟩)

set_option maxHeartbeats 40000000 in
theorem PinCycRun.fpStateenSatp :
    SailCycleOrderFp.fpT (stateen_allows_CSR_access 0x180#12 .Supervisor .CSRRead) := by
  fp_walk

set_option maxHeartbeats 40000000 in
/-- The access check of `csrr rd, satp` on the kernel configuration (`mstatus.TVM = 0`). -/
theorem cyCheckSatp (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop)
    (T : CySt → (r : Register) → RegisterType r → Prop) (st : CySt) (hcfg : kCfg st.rv)
    (hrb : RbootAll st.rv) :
    cyB A Aa cyS T (fun x st' => x = .CSR_Check_OK () ∧ cyFrame st st' ∧ st'.d.ro = st.d.ro)
      (check_CSR_result 0x180#12 Privilege.Supervisor .CSRRead) st := by
  have hH : runRead drefS (currentlyEnabled .Ext_H) = some (false, false) := by decide +kernel
  have hS : runRead drefS (stateen_allows_CSR_access 0x180#12 .Supervisor .CSRRead) =
      some (true, false) := by decide +kernel
  have hacc : is_CSR_accessible 0x180#12 .Supervisor .CSRRead = satp_accessible .Supervisor := by
    rfl
  unfold check_CSR_result check_CSR check_CSR_priv privLevel_to_CSR_privbits
  simp only [bind_assoc, hacc]
  refine cyBBind (fun z st' => z = false ∧ st'.rv = st.rv ∧ st'.fe = st.fe ∧ st'.an = st.an ∧
    st'.d.ro = st.d.ro ∧ st'.d.n = st.d.n ∧ st'.d.ok = st.d.ok) _ _ _ _ ?_ (fun z st1 h => ?_)
  · exact cyOfRunRead A Aa cyS T drefS _ _ _ _ false false hH
      (SailCycleOrderFp.fpCurrentlyEnabled _) (PinCycRun.drefAgree _ hcfg) hrb
      (fun st' e1 e2 e3 e4 e5 e6 => ⟨rfl, e1, e2, e3, e4, e5, e6⟩)
  obtain ⟨rfl, e1, e2, e3, e4, -, -⟩ := h
  simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
  rw [if_pos (by decide : zopz0zKzJ_u 1#2 (csrPriv 384#12) = true),
    if_pos (by decide : check_CSR_access 384#12 .CSRRead = true)]
  unfold satp_accessible
  simp only [bind_assoc, pure_bind]
  refine cyReadBind _ _ _ _ (fun m hm => ?_)
  have em : m = st.rv .mstatus := by
    rw [PinCycRun.rdMirror _ _ _ (by decide) hm, e1]
  subst em
  rw [if_pos (by rw [hcfg.2.2.2.2.2.1]; rfl)]
  refine cyBBind (fun z st' => z = true ∧ st'.rv = st.rv ∧ st'.fe = st.fe ∧ st'.an = st.an ∧
    st'.d.ro = st.d.ro ∧ st'.d.n = (cyRd st1 .mstatus).d.n ∧ st'.d.ok = (cyRd st1 .mstatus).d.ok)
    _ _ _ _ ?_ (fun z st2 h => ?_)
  · refine cyOfRunRead A Aa cyS T drefS _ _ _ _ true false hS
      PinCycRun.fpStateenSatp ?_ ?_
      (fun st' f1 f2 f3 f4 f5 f6 => ⟨rfl, f1.trans e1, f2.trans e2, f3.trans e3, f4.trans e4, f5, f6⟩)
    · show ∀ r v, drefS r = some v → wireReg r = false ∧ st1.rv r = v
      rw [e1]; exact PinCycRun.drefAgree _ hcfg
    · show RbootAll st1.rv
      rw [e1]; exact hrb
  obtain ⟨rfl, f1, f2, f3, f4, -, -⟩ := h
  exact ⟨rfl, ⟨fun r _ => by rw [f1], by rw [f1]; exact hrb, f2, f3⟩, f4⟩

end PinCycRun
end Weak
