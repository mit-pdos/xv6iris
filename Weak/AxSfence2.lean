/-
Weak: **the sfence.vma execute certificate, the TLB-post spine, the row-level marker-form PTW
model, and the concrete pieces on xv6's `sfence.vma zero, zero` (0x12000073)** — the parts of
Rocq's AxSfence2 that hold in the Lean engine (the WPd LEAF itself is PENDING, see below).

Rocq: `iris/AxSfence2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Companion of AxSfence (graph level).
§1 ROW LEVEL.  `ptwModelRowF i kd ws ks GD` — the twin of AxWalk5's `ptwModelRow` over
   AxSfence's `ptwModelF`, walker attribution `gpForRow i kd ws` and sfence tags `gpSfRow i ks`.
   Rocq `sf_fetch_of_fetch_gd_ok`: a row fetch item whose bytes are `sf_bytes` IS an
   `sf_fetch` event of the graph.
§2 THE EXECUTE.  `certExecuteSfence`: in S-mode with mstatus.TVM = 0, `execute (SFENCE_VMA
   (zreg, zreg))` is a `Cert` (no row item, no data event, no fence — the execute emits only
   register events) ending in RETIRE_SUCCESS with the TLB register FLUSHED (`tlbFlushed`: every
   slot `none`) and nothing else changed (`ExecSC9.execExecuteSFENCEVMAS` through
   `CertOfRfFPost` and AxWalk5's `rfFExecuteSFENCEVMA`).  `tlbAgreesFlushed`: `tlbAgrees asid T`
   holds of a flushed TLB, for EVERY asid and tree (AxPtProt's `tlbAgreesFlush`).
§3 THE SPINE WITH A TLB POST.  `spineCertXTTlb`: AxDataX5's `spineCertXT` extended by a
   predicate `Ptlb` on the TLB register that the execute certificate establishes (`CertXTP`)
   and that the spine's tail (rd write, PC/minstret update `tfinal`, `tick_clock`'s frame
   `tickFrame`) preserves; it needs the regime's tick-frame stability `HCtick`.
   `CertXTPSfence`: the execute certificate of sfence.vma, TLB-flushed.
§4 THE X LEAF (Rocq `X_sfence`, `X_sfence_agrees`, `X_sfence_S`, `X_sfence_agrees_S`) — PENDING.
§5 CONCRETE (non-vacuity) at AxLeafS3's S-mode state `σL` with xv6's word: `decSfence`
   (decode fact at every regime state), `text4Sfence`, `ctrlOkSWFlush`, `ctrlOkSWTick`;
   Rocq's `sfence_whole` / `sfence_whole_agrees` (whole-instruction certificate) — PENDING;
   `sfWordNotFence`: AxSfence's `sfWord` is NOT trivially true (xv6's `fence rw,w` word is not
   an sfence word; the decode hypotheses hold at a concrete regime state).

## PENDING (blocked; owner/orchestrator question, nothing is stubbed)

Q7 (`notes/weak-port-q7-sfence.md`) makes the SFENCE.VMA ANNOUNCE a graph event (label
`LFence false false false false`, `WeakEvLang.annLabel`).  The Lean `AxCert.Cert` has no arm
for that node: `Cert.cIa` requires `sfAnnB n w = false` (AxCert deviation 3), so NO `Cert` of a
whole `riscvStep` that executes an sfence.vma word exists, and `CertHartActiveBaseT` /
`spineCertX(T)` all carry `sfAnnB 32 w = false`.  Rocq's leaf `X_sfence` (through
`wpd_instr_of_Cert`) and its corollaries `X_sfence_agrees`, `X_sfence_S`, `X_sfence_agrees_S`,
and the whole-instruction certificates `sfence_whole`, `sfence_whole_agrees`, therefore cannot
be stated on the existing engine (their premises `Hdec`/`text_at4` at an sfence word would
contradict `sfAnnB 32 w = false`).  Proposed fix (needs edits outside this file): a Cert arm
`cSf (d b r n w k t) : sfAnnB n w = true → Cert … ⟨d, b, r⟩ (k ()) t → Cert … ⟨d, bsucc b, r⟩
(.impure (.ok (.instrAnnounce n w)) k) t` (one row item, the marker; the release flag is
unchanged since `relpUpd` of the all-false fence is the identity), its case in
`AxCert2.wpdOfCertM` via a twin of `wpdFenceNodeM` at the announce node (`pnodeStep`'s announce
arm emits `annLabel n w`, `AStepFence` is the only step), the trivial cases in the other
`Cert` inductions (`CertMono`, `CertBind`, AxCert3 `certb`, AxDataX9 `CertWOfCert`, …), and an
sfence twin of `CertHartActiveBaseT` without `hw`.  The Lean leaf's continuation is then at row
position `k + 1` (the marker is a row item; Rocq: "no row item").

## Deviations from Rocq

1. Q7 — §1: Rocq `sf_fetch_of_fetch_gd_ok` (a fetch row item with sfence bytes is the marker)
   has no Lean counterpart — under Stage C a fetch is not a row item, and under Q7 the marker
   is the announce's own `LFence false false false false` row item.  It is replaced by
   `sfMarkOfRow`: a row item `LFence false false false false` of hart `i` at `k` IS an
   `sfMark` event of the graph.
2. Q7 — §3: `spineCertXTTlb` takes `Hsf : sfAnnB 32 w = false` right after `textAt4 pc w` (as
   AxDataX5's `spineCertXT`, deviation 1 there); so it does NOT apply to the sfence word (see
   PENDING).
3. TYPES / SPELLING as AxDataX5 / AxLeafS3: `vec (option TLB_Entry) (2^6)` ↦
   `Vector (Option TLB_Entry) (2 ^ 6)`; `vec_access_dec v j` with `0 ≤ j < 64` over `Z` ↦
   `v[j]!` with `j : Nat`, `j < 64`; `tlb_hash (__id 39) vpn` ↦ `tlb_hash 39 vpn`;
   `register_lookup r t.(sregs)` ↦ `t.regs r`; `register_set tlb v rs` ↦ `rs.set .tlb v`;
   `set_reg t tlb tv` ↦ `t.setReg .tlb tv`; `eq_vec (_get_Mstatus_TVM ms) 'b"1" = false` ↦
   `(_get_Mstatus_TVM ms == 1#1) = false`; `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg`;
   `CS d BInf r` ↦ `⟨d, .BInf, r⟩`; `cs_b` ↦ `csB`; `add_vec_int` ↦ `BitVec.addInt`;
   `img_S` ↦ `imgS`; `ctrl_ok_S(W)` ↦ `ctrlOkS(W)`; `nvS_satp` ↦ `nvSSatp`.  Section variables
   `img dok kind` are explicit arguments.
4. §5 decode: Rocq `dec_sfence` (by `rfF_dec_sfence` + KernelDecode20 `kd_12000073`) ↦ the
   read-only decode walk `AxSfence2.walkSfence` at `AxLeafS3.drefS` + `AxLeafS3.decOfWalk`
   (AxLeafS3 deviation 3); `rfF_dec_sfence` is not ported (unused).  `sf_word_not_fence`:
   Rocq's `kd_0310000f` ↦ `execOfRunRead` over the same walk (`runRead` at `drefS`, by the
   kernel).  The word: `σL W_sfence` ↦ `σL WSfence.toNat` (AxLeafS3's `σL` takes a `Nat`),
   `mword_of_int W_sfence` ↦ `BitVec.ofInt 32 WSfence` (AxSfence's spelling), `W_fence` ↦
   `AxLeafS3.wFence` (`BitVec.ofNat 32`).
5. `ctrl_ok_SW_tick`'s Lean twin `tickFrameCtrlSW` exists in AxSpinE (not imported here); this
   file states its own `ctrlOkSWTick` (Rocq name, Rocq statement).

**Rocq → Lean name map.**  `ptw_model_row_f` `ptwModelRowF`; `sf_fetch_of_fetch_gd_ok` ↦
`sfMarkOfRow` (deviation 1); `tlb_flushed` `tlbFlushed`; `tlb_flushed_hash` `tlbFlushedHash`;
`tlb_agrees_flushed` `tlbAgreesFlushed`; `tlb_exact_flushed` `tlbExactFlushed`;
`cert_execute_sfence` `certExecuteSfence`; `tfinal_tlb` `tfinalTlb`; `CertXTP` `CertXTP`;
`spine_certXT_tlb` `spineCertXTTlb`; `CertXTP_sfence` `CertXTPSfence`; `ctrl_ok_S_flush`
`ctrlOkSFlush`; `ctrl_ok_S_TVM` `ctrlOkSTVM`; `dec_sfence` `decSfence`; `text4_sfence`
`text4Sfence`; `ctrl_ok_SW_flush` `ctrlOkSWFlush`; `ctrl_ok_SW_tick` `ctrlOkSWTick`;
`sf_word_not_fence` `sfWordNotFence`.  None is in the duplicated-name table.
Lean-only (file-qualified): `AxSfence2.walkSfence`, `AxSfence2.walkFence` (the `runRead` twin
of AxLeafS3's `walkFence`, for `sfWordNotFence`).

**Dropped:** `rfF_dec_sfence` (deviation 4; unused).  **PENDING (not ported, see above):**
`X_sfence`, `X_sfence_agrees`, `X_sfence_S`, `X_sfence_agrees_S`, `sfence_whole`,
`sfence_whole_agrees` (no downstream Rocq file imports AxSfence2).  **Not ported:** the section
notations `CM` / `EvM`, the Ltac `lk` (`RegFile` rewrites instead) and the `Print Assumptions`
lines (the lint's axiom check covers them).
Rocq 25 definitions/lemmas; Lean 18 ported (one restated, deviation 1) + 2 Lean-only; 6 pending,
1 dropped.
-/
import Weak.AxLeafS3
import Weak.AxSfence
import Weak.AxWalk5
import Weak.ExecSC9

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. Row level -/

/-- Rocq `ptw_model_row_f`: the row-level marker-form PTW model. -/
def ptwModelRowF (i : Nat) (kd : Nat) (ws : List (Nat × Wev)) (ks : List Nat)
    (GD : Gdexec) : Prop :=
  ptwModelF (Gptw.mk GD (gpForRow i kd ws) (gpSfRow i ks))

/-- Rocq `sf_fetch_of_fetch_gd_ok`, Q7 form (deviation 1): a marker row item of hart `i` is an
`sfMark` event of the graph. -/
theorem sfMarkOfRow (GD : Gdexec) (i k : Nat) :
    (AxOpsem.grow GD i)[k]? = some (Lbl.LFence false false false false) →
    sfMark GD.gdG (i, k) :=
  AxWp.growLookup GD i k _

/-! # 2. The execute of `sfence.vma zero, zero` -/

/-- Rocq `tlb_flushed`. -/
def tlbFlushed (v : Vector (Option TLB_Entry) (2 ^ 6)) : Prop :=
  ∀ j : Nat, j < 64 → v[j]! = none

/-- Rocq `tlb_flushed_hash`. -/
theorem tlbFlushedHash (v : Vector (Option TLB_Entry) (2 ^ 6)) (vpn : BitVec 27) :
    tlbFlushed v → v[tlb_hash 39 vpn]! = none :=
  fun H => H _ (Nat.lt_of_lt_of_le (AxPtProt.tlbHashLt vpn) (by decide))

/-- Rocq `tlb_agrees_flushed`. -/
theorem tlbAgreesFlushed (asid : BitVec 16) (T : PTree) (v : Vector (Option TLB_Entry) (2 ^ 6)) :
    tlbFlushed v → tlbAgrees asid T v :=
  fun H => tlbAgreesFlush asid T v (fun vpn' => tlbFlushedHash v vpn' H)

/-- Rocq `tlb_exact_flushed`. -/
theorem tlbExactFlushed (T : PTree) (v : Vector (Option TLB_Entry) (2 ^ 6)) :
    tlbFlushed v → tlbExact T v := by
  intro H vpn' ent Hget
  rw [tlbFlushedHash v vpn' H] at Hget
  cases Hget

/-- Rocq `cert_execute_sfence`. -/
theorem certExecuteSfence (img : Image) (dok : Int → Nat → Prop) (kind : Dkind) (s0 : Cst)
    (t : ExecSt) :
    t.regs .cur_privilege = .Supervisor →
    (_get_Mstatus_TVM (t.regs .mstatus) == 1#1) = false →
    AxCert.Cert img dok kind (fun (_ : Cst) (_ : Sail.Error exception) (_ : ExecSt) => False)
      (fun s x t' => x = RETIRE_SUCCESS ∧ s = s0 ∧ ∃ tv, tlbFlushed tv ∧ t' = t.setReg .tlb tv)
      s0 (execute (.SFENCE_VMA (zreg, zreg))) t := by
  intro Hp Ht
  obtain ⟨tv, He, Hv⟩ := execExecuteSFENCEVMAS t Hp Ht
  exact CertOfRfFPost img dok kind _ _ _ s0 t RETIRE_SUCCESS (t.setReg .tlb tv)
    (show rfF (execute_SFENCE_VMA zreg zreg) from rfFExecuteSFENCEVMA _ _) He
    ⟨rfl, rfl, tv, Hv, rfl⟩

/-! # 3. The spine with a TLB post -/

/-- Rocq `tfinal_tlb`. -/
theorem tfinalTlb (b : Bool) (tx : ExecSt) : (tfinal b tx).regs .tlb = tx.regs .tlb := by
  unfold tfinal
  cases b <;> simp only [ExecSt.setReg_regs, Bool.false_eq_true, ↓reduceIte] <;>
    (try rw [RegFile.set_other _ _ _ _ (by decide)]) <;> rw [RegFile.set_other _ _ _ _ (by decide)]

/-- Rocq `CertXTP`: AxDataX4's `CertXT` + a TLB predicate established by the execute. -/
def CertXTP (img : Image) (dok : Int → Nat → Prop) (kind : Dkind)
    (ctrlOk : RegFile → Prop) (Ptlb : Vector (Option TLB_Entry) (2 ^ 6) → Prop)
    (rs : RegFile) (pc : BitVec 64) (ins : instruction)
    (ow : Cst → Option (BitVec 5 × BitVec 64)) (s0 : Cst) (PX : Cst → Prop) : Prop :=
  ∀ tpc : ExecSt, ctrlOk tpc.regs →
    tpc.regs .PC = pc →
    tpc.regs .nextPC = BitVec.addInt pc 4 →
    gprAgree tpc.regs rs →
    AxCert.Cert img dok kind (fun (_ : Cst) (_ : Sail.Error exception) (_ : ExecSt) => False)
      (fun s x t' => x = RETIRE_SUCCESS ∧ PX s ∧
        ∃ t0, tlbFrame tpc t0 ∧ ctrlOk t0.regs ∧ Ptlb (t0.regs .tlb) ∧ t' = wrOpt (ow s) t0)
      s0 (execute ins) tpc

/-- Rocq `spine_certXT_tlb` (deviation 2: `Hsf`). -/
theorem spineCertXTTlb (img : Image) (dok : Int → Nat → Prop) (kind : Dkind)
    (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
    (textAt4 : BitVec 64 → BitVec 32 → Prop)
    (Hsp : SpineOkT img ctrlOk textAt) (Hf4 : SpineFetch4T img ctrlOk textAt4)
    (HCtick : ∀ t t' : ExecSt, tickFrame t t' → ctrlOk t.regs → ctrlOk t'.regs)
    (Ptlb : Vector (Option TLB_Entry) (2 ^ 6) → Prop)
    (rs : RegFile) (pc : BitVec 64) (w : BitVec 32) (ins : instruction)
    (ow : Cst → Option (BitVec 5 × BitVec 64)) (d : Cdata) (r : Bool) (PX : Cst → Prop) :
    ctrlOk rs → rs .PC = pc → textAt4 pc w → sfAnnB 32 w = false →
    (∀ t : ExecSt, ctrlOk t.regs →
      EvA img (fun _ _ => False) (fun x t' => x = ins ∧ t' = t) (ext_decode w) t) →
    (∀ s, PX s → owOk (ow s)) → (∀ s, PX s → s.csB = .BInf) →
    CertXTP img dok kind ctrlOk Ptlb rs pc ins ow ⟨d, .BInf, r⟩ PX →
    ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
      AxCert.Cert img dok kind (fun _ _ _ => False)
        (fun s _ t' => PX s ∧ GoodC ctrlOk false rs pc none (ow s) t'.regs ∧ Ptlb (t'.regs .tlb))
        ⟨d, .BInf, r⟩ (riscvStep tick) t := by
  intro Hct HPC Htx Hsf Hdec How HPX Hcert tick t Hag
  have Hct_t : ctrlOk t.regs := Hsp.sptSeip _ _ Hct Hag
  have HPC_t : t.regs .PC = pc := by
    rw [Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))]; exact HPC
  obtain ⟨b, Hb⟩ := Hsp.sptInc t Hct_t
  have Hct_a : ctrlOk (t.setReg .minstret_increment b).regs :=
    Hsp.sptFrame _ _ _ (Or.inr (Or.inr (Or.inl rfl))) Hct_t
  have HPC_a : (t.setReg .minstret_increment b).regs .PC = pc := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC_t
  obtain ⟨t1, Hfr, Hct1, Hfetch⟩ := Hf4 _ pc w Hct_a HPC_a Htx
  have HPC_1 : t1.regs .PC = pc := (tlbFrameLookup _ _ _ Hfr (by decide)).trans HPC_a
  have Hgag : gprAgree (t1.setReg .nextPC (BitVec.addInt pc 4)).regs rs := by
    intro r _
    simp only [ExecSt.setReg_regs]
    rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide), AxSpineOk5.tlbFrameXget _ _ Hfr,
      ExecSt.setReg_regs, AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]
    exact AxSymEngine2.uxaXgetAgree _ _ Hag r
  have Hct_pc : ctrlOk (t1.setReg .nextPC (BitVec.addInt pc 4)).regs :=
    Hsp.sptFrame _ _ _ (Or.inr (Or.inl rfl)) Hct1
  have HPC_pc : (t1.setReg .nextPC (BitVec.addInt pc 4)).regs .PC = pc := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC_1
  have Hnpc_pc : (t1.setReg .nextPC (BitVec.addInt pc 4)).regs .nextPC =
      BitVec.addInt pc 4 := by
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  have Hexec := Hcert _ Hct_pc HPC_pc Hnpc_pc Hgag
  have Hrun := CertHartActiveBaseT img dok kind _ t1 w ins pc d r
    (fun s t' => PX s ∧ ∃ t0, tlbFrame (t1.setReg .nextPC (BitVec.addInt pc 4)) t0 ∧
      ctrlOk t0.regs ∧ Ptlb (t0.regs .tlb) ∧ t' = wrOpt (ow s) t0) Hsf
    (Hsp.sptDisp _ Hct_a) Hfetch (Hdec _ Hct1) (Hsp.sptLpad _ Hct1) HPC_1 Hexec
  have Hmi1 : t1.regs .minstret_increment = b := by
    rw [tlbFrameLookup _ _ _ Hfr (by decide)]
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  refine CertRiscvStep img dok kind tick ⟨d, .BInf, r⟩ t
    (fun s t' => PX s ∧ GoodC ctrlOk false rs pc none (ow s) t'.regs ∧ Ptlb (t'.regs .tlb)) _
    ?_ ?_
  · have HT := CertTryStepActive img dok kind t b (zero_extend (m := 32) w) d r
      (fun s t' => PX s ∧ ∃ t0, tlbFrame (t1.setReg .nextPC (BitVec.addInt pc 4)) t0 ∧
        ctrlOk t0.regs ∧ Ptlb (t0.regs .tlb) ∧ t' = wrOpt (ow s) t0)
      (fun s t' => PX s ∧ GoodC ctrlOk false rs pc none (ow s) t'.regs ∧ Ptlb (t'.regs .tlb))
      Hb (Hsp.sptHart _ Hct_a) Hrun ?_
    · exact CertMono img dok kind _ _ _ _ _ _ t (fun _ _ _ h => h) (fun _ _ _ h => h.2) HT
    · rintro s _ ⟨HP, t0, Hfr0, Hc0, Hpt, rfl⟩
      have Hct_x := wrNpcCtrl img ctrlOk textAt Hsp (ow s) none _ Hc0
      have How' := How s HP
      rw [show wrOpt (ow s) t0 = wrOpt (ow s) (npcOpt none t0) from rfl]
      refine ⟨?_, ?_, HP, ⟨?_, ?_, ?_⟩, ?_⟩
      · rw [wrNpcOther _ _ _ _ (by decide) (by decide), tlbFrameLookup _ _ _ Hfr0 (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide)]
        exact Hsp.sptHart _ Hct1
      · rw [wrNpcOther _ _ _ _ (by decide) (by decide), tlbFrameLookup _ _ _ Hfr0 (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide)]
        exact Hmi1
      · unfold tfinal
        cases b
        · exact Hsp.sptFrame _ _ _ (Or.inl rfl) Hct_x
        · exact Hsp.sptFrame _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
            (Hsp.sptFrame _ _ _ (Or.inl rfl) Hct_x)
      · rw [tfinalPC, wrNpcNextPC, tlbFrameLookup _ _ _ Hfr0 (by decide)]
        exact Hnpc_pc
      · intro r Hr
        rw [tfinalGpr, wrNpcGpr _ _ _ _ Hr How']
        refine gprPostAgree _ _ _ _ ?_ Hr
        intro r1 Hr1
        rw [AxSpineOk5.tlbFrameXget _ _ Hfr0]
        exact Hgag r1 Hr1
      · rw [tfinalTlb, wrNpcOther _ _ _ _ (by decide) (by decide)]
        exact Hpt
  · rintro s' t' ⟨HP, HG, Hpt⟩
    cases tick with
    | false => exact ⟨HP, HG, Hpt⟩
    | true =>
      obtain ⟨d', b', r'⟩ := s'
      have Hb' : b' = .BInf := HPX _ HP
      subst Hb'
      refine CertMono img dok kind _ _ _ _ _ _ t' (fun _ _ _ h => h) ?_
        (CertEvA img dok kind _ _ d' r' t' (sptTickFrame img t'))
      rintro _ _ t'' ⟨rfl, Hf⟩
      obtain ⟨Hk1, Hk2⟩ := tickFrameKeep _ _ Hf
      obtain ⟨Hc, HG2, HG3⟩ := HG
      refine ⟨HP, ⟨HCtick _ _ Hf Hc, Hk1.trans HG2, fun r Hr => (Hk2 r).trans (HG3 r Hr)⟩, ?_⟩
      rw [Hf .tlb (by decide) (by decide) (by decide)]
      exact Hpt

/-- Rocq `CertXTP_sfence`: the execute certificate of `sfence.vma zero, zero` in a regime that
is Supervisor, TVM = 0 and closed under a TLB flush. -/
theorem CertXTPSfence (img : Image) (dok : Int → Nat → Prop) (kind : Dkind)
    (ctrlOk : RegFile → Prop)
    (Hpriv : ∀ rs, ctrlOk rs → rs .cur_privilege = .Supervisor)
    (HTVM : ∀ rs, ctrlOk rs → (_get_Mstatus_TVM (rs .mstatus) == 1#1) = false)
    (Hflush : ∀ rs v, ctrlOk rs → tlbFlushed v → ctrlOk (rs.set .tlb v))
    (rs : RegFile) (pc : BitVec 64) (d : Cdata) (r : Bool) :
    CertXTP img dok kind ctrlOk tlbFlushed rs pc (.SFENCE_VMA (zreg, zreg)) (fun _ => none)
      ⟨d, .BInf, r⟩ (fun s => s = ⟨d, .BInf, r⟩) := by
  intro tpc Hc _ _ _
  refine CertMono _ _ _ _ _ _ _ _ _ _ (fun _ _ _ h => h) ?_
    (certExecuteSfence img dok kind ⟨d, .BInf, r⟩ tpc (Hpriv _ Hc) (HTVM _ Hc))
  rintro s x t' ⟨rfl, rfl, tv, Hv, rfl⟩
  refine ⟨rfl, rfl, tpc.setReg .tlb tv, Or.inr ⟨tv, rfl⟩, Hflush _ _ Hc Hv, ?_, rfl⟩
  simp only [ExecSt.setReg_regs, RegFile.set_same]
  exact Hv

/-! # 4. The S-mode kernel regime (the X leaf itself is PENDING, see the header) -/

/-- Rocq `ctrl_ok_S_flush`. -/
theorem ctrlOkSFlush (T : PTree) (satp0 : BitVec 64) (rs : RegFile)
    (v : Vector (Option TLB_Entry) (2 ^ 6)) :
    ctrlOkS T satp0 rs → tlbFlushed v → ctrlOkS T satp0 (rs.set .tlb v) := by
  intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, _, h13⟩ hv
  have e : ∀ r : Register, r ≠ .tlb → (rs.set .tlb v) r = rs r :=
    fun r hr => RegFile.set_other _ _ _ _ hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e .cur_privilege (by decide)]; exact h1
  · rw [e .hart_state (by decide)]; exact h2
  · rw [e .misa (by decide)]; exact h3
  · rw [e .menvcfg (by decide)]; exact h4
  · rw [e .htif_tohost_base (by decide)]; exact h5
  · rw [e .elp (by decide)]; exact h6
  · rw [e .pma_regions (by decide)]; exact h7
  · rw [e .mstatus (by decide)]; exact h8
  · rw [e .mstatus (by decide)]; exact h9
  · rw [e .mie (by decide), e .mideleg (by decide)]; exact h10
  · rw [e .satp (by decide)]; exact h11
  · rw [RegFile.set_same]; exact tlbExactFlushed T v hv
  · unfold AxSpineOk6.pmpOk at h13 ⊢
    rw [e .pmpcfg_n (by decide), e .pmpaddr_n (by decide)]
    exact h13

/-- Rocq `ctrl_ok_S_TVM`. -/
theorem ctrlOkSTVM (T : PTree) (satp0 : BitVec 64) (rs : RegFile) :
    ctrlOkS T satp0 rs → (_get_Mstatus_TVM (rs .mstatus) == 1#1) = false :=
  fun h => h.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2

/-! # 5. Concrete: xv6's `sfence.vma zero, zero` (0x12000073) at an S-mode state -/

/-- (Lean-only, deviation 4) the decode walk of `sfence.vma zero, zero`. -/
theorem AxSfence2.walkSfence :
    AxLeafS3.rdWalk AxLeafS3.drefS (ext_decode (BitVec.ofInt 32 WSfence)) =
      some (.SFENCE_VMA (zreg, zreg)) := by
  ax_epi_ledger_krfl

/-- Rocq `dec_sfence` (deviation 4). -/
theorem decSfence (σ t : ExecSt) : ctrlOkSW pT nvSSatp t.regs →
    EvA (imgS σ) (fun (_ : Sail.Error exception) (_ : ExecSt) => False)
      (fun x t' => x = .SFENCE_VMA (zreg, zreg) ∧ t' = t)
      (ext_decode (BitVec.ofInt 32 WSfence)) t :=
  AxLeafS3.decOfWalk _ _ AxSfence2.walkSfence σ t

/-- Rocq `text4_sfence`. -/
theorem text4Sfence :
    textAt4S (σL WSfence.toNat) pT (AxEpiProbe.w64 sPc) (BitVec.ofInt 32 WSfence) :=
  AxLeafS3.text4Of _ _ (by unfold BytesAt; decide +kernel) (by decide +kernel)

/-- Rocq `ctrl_ok_SW_flush`. -/
theorem ctrlOkSWFlush (rs : RegFile) (v : Vector (Option TLB_Entry) (2 ^ 6)) :
    ctrlOkSW pT nvSSatp rs → tlbFlushed v → ctrlOkSW pT nvSSatp (rs.set .tlb v) := by
  intro ⟨Hc, HW⟩ Hv
  refine ⟨ctrlOkSFlush _ _ _ _ Hc Hv, pmpWDep rs _ (fun r hr => ?_) HW⟩
  refine RegFile.set_other _ _ _ _ (fun h => ?_)
  subst h
  exact absurd hr (by decide)

/-- Rocq `ctrl_ok_SW_tick`. -/
theorem ctrlOkSWTick (t t' : ExecSt) : tickFrame t t' → ctrlOkSW pT nvSSatp t.regs →
    ctrlOkSW pT nvSSatp t'.regs := by
  intro Hf ⟨Hc, HW⟩
  refine ⟨tickFrameCtrlS _ _ _ _ Hf Hc, pmpWDep t.regs _ (fun r hr => ?_) HW⟩
  refine Hf r (fun h => ?_) (fun h => ?_) (fun h => ?_) <;> subst h <;> exact absurd hr (by decide)

/-- (Lean-only, deviation 4) the `runRead` decode walk of `fence rw,w` at `drefS`. -/
theorem AxSfence2.walkFence :
    runRead AxLeafS3.drefS (ext_decode (BitVec.ofNat 32 AxLeafS3.wFence)) = some (fenceRwW, true) := by
  ax_epi_ledger_krfl

/-- Rocq `sf_word_not_fence`: NON-TRIVIALITY of AxSfence's `sfWord` — the decode hypotheses
hold at a concrete regime state, so a non-sfence word is not an sfence word. -/
theorem sfWordNotFence : ¬ sfWord (BitVec.ofNat 32 AxLeafS3.wFence) := by
  intro ⟨rs1, rs2, H⟩
  obtain ⟨Hm, Hcfg⟩ := cfgOfCK (σL AxLeafS3.wFence) rsLCtrlOk
  have E := H _ Hm Hcfg
  have hc := rsLCtrlOk.1
  have F := execOfRunRead AxLeafS3.drefS _ (σL AxLeafS3.wFence) fenceRwW true
    (fun r v hv => by
      unfold AxLeafS3.drefS at hv
      split at hv <;> simp only [Option.some.injEq, reduceCtorEq] at hv <;> subst hv
      · exact hc.1
      · exact hc.2.2.1
      · exact hc.2.2.2.1) AxSfence2.walkFence
  rw [F] at E
  have E' := congrArg (fun o => o.map Prod.fst) E
  simp only [Option.map_some] at E'
  unfold fenceRwW at E'
  exact instruction.noConfusion (Option.some.inj E')

end Weak
