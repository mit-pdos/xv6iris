/-
Weak/Mini: **L4 MiniCmp — loads and stores simulated** (mini plan rev 4 §2 L4; Pulte AtoP.v `sim_step` for
reads and writes).

* LOAD `r`: the machine answers the timestamp `t` of the store `r` reads (0: the initial memory).  Admissible
  (`loadOk`): no store to the word with a timestamp in `(t, pre-view ⊔ coh]` — below the pre-view such a store would
  be gmo-before `r` (rules 4, 9 bound the pre-view by `r`'s timestamp), hence a later candidate than `r`'s store; below
  `coh` it is excluded by `coh2`.  The post-view is at most `r`'s timestamp (a forwarded answer: rule 12 through the
  forward bank; otherwise `r`'s store is gmo-before `r`, or is the forward bank's store by rule 1).
* STORE `w`: fulfils its own promise `vo w`; COH by `coh1`, EXT by rules 9, 10 and `vcap`/`vwNew`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.CmpStep

namespace Weak.Mini.Cmp

open Weak.Mini Weak.Mini.Mach

variable {P : MProg} {C : MCut}

theorem ldExt_lt {sz w : Nat} (hsz : sz ≤ 8) (hw : w < 2 ^ (8 * sz)) (sgn : Bool) : ldExt sz sgn w < two64 := by
  have h64 : two64 = 2 ^ 64 := rfl
  have hp : 2 ^ (8 * sz) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold ldExt sext
  split
  · split
    · rename_i _ h1
      have : 0 < 2 ^ (8 * sz) := Nat.two_pow_pos _
      omega
    · omega
  · omega

section steps

variable (hC : miniCut P C) {h : Nat} (hh : h < P.harts.length)
include hC hh

/-- A LOAD. -/
theorem step_load (hwf : P.wf) {s : Weak.Mini.MSt} {H : MHart} (hI : Inv P C h s H) {sgn : Bool}
    {rd rs1 off : Nat} (hi : (P.prog h)[s.pc]? = some (.load sgn rd rs1 off))
    (hX : SC P C h s (exec P.sz h C.V s (.load sgn rd rs1 off))) :
    StepOk P C h s (exec P.sz h C.V s (.load sgn rd rs1 off)) H := by
  have hmem := List.mem_of_getElem? hi
  have hreg : rd < 32 ∧ rs1 < 32 := (hwf.2.2 h _ hmem).2
  have hsz : P.sz ≤ 8 := by rcases hwf.1 with h | h | h | h <;> omega
  have hg := hgmo hC
  rcases h1 : s.rd rs1 with ⟨v1, t1⟩
  have hex : exec P.sz h C.V s (.load sgn rd rs1 off) =
      ((s.emit ⟨.ld, s.ii, MAlu.add.eval v1 (off % two64), C.V (h, s.evs.length) % 2 ^ (8 * P.sz), t1, [],
        s.ctl⟩).wr rd (ldExt P.sz sgn (C.V (h, s.evs.length) % 2 ^ (8 * P.sz)), [s.evs.length])).adv := by
    simp [exec, h1]
  rw [hex] at hX ⊢
  have hwlt : C.V (h, s.evs.length) % 2 ^ (8 * P.sz) < 2 ^ (8 * P.sz) := Nat.mod_lt _ (Nat.two_pow_pos _)
  generalize C.V (h, s.evs.length) % 2 ^ (8 * P.sz) = w at hX hwlt ⊢
  have haddr : (H.fr.rd rs1 + off) % two64 = MAlu.add.eval v1 (off % two64) := by
    rw [hI.regs, h1]; simp [MAlu.eval]
  generalize MAlu.add.eval v1 (off % two64) = a at hX haddr ⊢
  obtain ⟨hev, hnN⟩ := hX.next ⟨.ld, s.ii, a, w, t1, [], s.ctl⟩ (by simp [MSt.adv, (wr_same _ _ _).2.1, MSt.emit])
  -- the new event `r = (h, n)`
  have hkd : kd P C h s.evs.length = .ld := by unfold kd; rw [hev]
  have hrM : (C.evs P).isMem (h, s.evs.length) := isMem_hj hh hnN (.inl hkd)
  have hrL : (C.evs P).isLd (h, s.evs.length) := hkd
  have hpa : pa P C h s.evs.length = a := by unfold pa; rw [hev]
  have hal : a % P.sz = 0 := by have := hC.2.2.1 _ hrM; rw [hev] at this; exact this
  obtain ⟨o, hrf, hval⟩ := hlva hC _ hrM.1 hrL
  have hwv : ((C.evs P).ev (h, s.evs.length)).v = w := by rw [hev]
  -- the taint of the address register: loads ppo-before `r` (rule 9)
  have hdva : dom P C h (· ∈ t1) (srcsView H.ws (srcR rs1)) := by
    have := dom_srcR hI.regv hreg.2; rw [h1] at this; exact this
  have ht1 : ∀ i ∈ t1, i < s.evs.length ∧ kd P C h i = .ld ∧ i < NN P C h :=
    fun i hi => hX.taint i (hX.wf.rd rs1 i (by rw [h1]; exact hi))
  have hva : srcsView H.ws (srcR rs1) ≤ vo P C (h, s.evs.length) :=
    le_vo_of hC hdva (fun i hi => gmo_r9 hC (isMem_hj hh (ht1 i hi).2.2 (.inl (ht1 i hi).2.1)) hrM
      (po_hj (ht1 i hi).1 hnN) (by rw [hev]; exact hi))
  have hvpre : ldPre H.ws (srcsView H.ws (srcR rs1)) ≤ vo P C (h, s.evs.length) :=
    Nat.max_le.2 ⟨hva, hI.vrNew _ (Nat.le_refl _) hnN hkd⟩
  -- the answer
  have hwin : ¬ writesIn (memL (C.evs P) C.g) a (kts P C o)
      (max (ldPre H.ws (srcsView H.ws (srcR rs1))) (H.ws.coh a)) := by
    rintro ⟨t', ht1', ht2', m, hm, hma⟩
    obtain ⟨w', hw'g, hw's, hvo, rfl⟩ := memL_get C.g hC.1 hm
    have hvo' : vo P C w' = t' := by unfold vo; rw [hvo]; omega
    have hw'M := (mem_g hC w').1 hw'g
    have hpaw : ((C.evs P).ev w').pa = a := hma
    by_cases hle : t' ≤ ldPre H.ws (srcsView H.ws (srcR rs1))
    · have hne : w' ≠ (h, s.evs.length) := fun he => MEvsF.ld_st hrL (he ▸ hw's)
      have hgw := gmo_of_vo hC hw'M hw's hrM hne (by omega)
      have := kts_ge hC hrf ⟨hw'M.1, hw's, by rw [hpaw, ← hpa]; rfl, .inl hgw⟩
      omega
    · have hle' : t' ≤ H.ws.coh a := by omega
      have := hI.coh2 _ (Nat.le_refl _) hnN hkd w' hw'g hw's (by rw [hpaw, hpa]) (by rw [hpa]; omega) o hrf
      omega
  have hmemv : memv P (memL (C.evs P) C.g) (kts P C o) a = some w := by
    cases o with
    | none =>
      show some (P.img0 a % wordW P) = some w
      rw [← hwv, hval]; simp only [MEvs.valOf]; rw [hev]; rfl
    | some w0 =>
      obtain ⟨hw0h, hw0s, hw0pa, _⟩ := hrf.1
      have hw0g : w0 ∈ C.g := (mem_g hC w0).2 ⟨hw0h, .inr hw0s⟩
      obtain ⟨hpos, hget⟩ := voL_mem C.g hw0g hw0s
      show memv P _ (vo P C w0) a = some w
      unfold vo
      rw [show voL (C.evs P) C.g w0 = (voL (C.evs P) C.g w0 - 1) + 1 by omega]
      simp only [memv, hget, msgOf]
      rw [hw0pa, hev, if_pos rfl, ← hwv, hval]; rfl
  -- the post-view is at most `r`'s timestamp
  have hcand : ∀ {w0 : EvId}, o = some w0 → (C.evs P).cand (h, s.evs.length) w0 := by
    intro w0 hh0; subst hh0; exact hrf.1
  have hown : ∀ {w0 : EvId}, o = some w0 → (C.evs P).po w0 (h, s.evs.length) →
      ∃ j0, w0 = (h, j0) ∧ j0 < s.evs.length ∧ kd P C h j0 = .st ∧ pa P C h j0 = a := by
    intro w0 hh0 hpo
    obtain ⟨hw0h, hw0s, hw0pa, _⟩ := hcand hh0
    obtain ⟨h0, j0⟩ := w0
    have : h0 = h := hpo.1; subst this
    exact ⟨j0, rfl, po_idx hpo hw0h.2 hnN, hw0s, by unfold pa; rw [hw0pa, hev]⟩
  -- the answer is at most `r`'s timestamp unless it is the hart's own po-earlier store
  have hgen : ∀ (_ : ∀ w0, o = some w0 → (C.evs P).po w0 (h, s.evs.length) →
      ¬ (C.evs P).gmo w0 (h, s.evs.length) → False), kts P C o ≤ vo P C (h, s.evs.length) := by
    intro hno
    cases o with
    | none => exact Nat.zero_le _
    | some w0 =>
      rcases (hcand rfl).2.2.2 with hgm | hpo
      · exact vo_gmo_le hC hgm
      · by_cases hgm : (C.evs P).gmo w0 (h, s.evs.length)
        · exact vo_gmo_le hC hgm
        · exact absurd (hno w0 rfl hpo hgm) id
  have hfv : fwdView H.ws a (kts P C o) ≤ vo P C (h, s.evs.length) := by
    have hfw := hI.fwd a
    unfold fwdView
    cases hfa : H.ws.fwd a with
    | none =>
      rw [hfa] at hfw
      simp only
      refine hgen (fun w0 hh0 hpo _ => ?_)
      obtain ⟨j0, _, hw2, hw3, hw4⟩ := hown hh0 hpo
      exact hfw _ hw2 hw3 hw4
    | some p =>
      obtain ⟨tf, vf⟩ := p
      rw [hfa] at hfw
      simp only
      obtain ⟨jf, hjf, hsf, hpaf, hlf, htf, hvf⟩ := hfw
      have hjfM : (C.evs P).isMem (h, jf) := isMem_hj hh (by omega) (.inr hsf)
      by_cases hteq : kts P C o = tf
      · rw [if_pos hteq]
        cases o with
        | none =>
          have := vo_pos hC (mem_hj hC hh (j := jf) (by omega) (.inr hsf)) hsf
          simp only [kts] at hteq; omega
        | some w0 =>
          obtain ⟨hw0h, hw0s, _, _⟩ := hrf.1
          have := vo_inj hC ⟨hw0h, .inr hw0s⟩ hjfM hw0s hsf (by rw [← htf]; exact hteq)
          subst this
          exact hvf _ (Nat.le_refl _) hnN hkd hpa hrf
      · rw [if_neg hteq]
        refine hgen (fun w0 hh0 hpo _ => ?_)
        obtain ⟨j0, rfl, hw2, hw3, hw4⟩ := hown hh0 hpo
        rcases Nat.lt_trichotomy j0 jf with hlt | heq | hgt
        · have hj0M : (C.evs P).isMem (h, j0) := isMem_hj hh (by omega) (.inr hw3)
          have hg1 := gmo_r1 hC hj0M hjfM (po_hj hlt (show jf < NN P C h by omega)) hsf (by
            show pa P C h j0 = pa P C h jf; rw [hw4, hpaf])
          have hcf : (C.evs P).cand (h, s.evs.length) (h, jf) :=
            ⟨⟨hh, show jf < NN P C h by omega⟩, hsf, by show pa P C h jf = pa P C h _; rw [hpaf, hpa], .inr (po_hj hjf hnN)⟩
          have hr : (C.evs P).rf (h, s.evs.length) (some (h, j0)) := hh0 ▸ hrf
          rcases hr.2 _ hcf with he | he
          · have := congrArg Prod.snd he; simp only at this; omega
          · exact MEvsF.gmo_asymm hg hg1 he
        · subst heq; apply hteq; rw [hh0, htf]; rfl
        · exact hlf j0 hgt hw2 hw3 hw4
  have hvp : max (ldPre H.ws (srcsView H.ws (srcR rs1))) (fwdView H.ws a (kts P C o)) ≤
      vo P C (h, s.evs.length) := Nat.max_le.2 ⟨hvpre, hfv⟩
  -- the answer is below every later store to the word
  have htlt : ∀ j, s.evs.length < j → j < NN P C h → kd P C h j = .st → pa P C h j = a →
      kts P C o < vo P C (h, j) := by
    intro j hj1 hj2 hst hpj
    have hjM := isMem_hj hh hj2 (.inr hst)
    cases o with
    | none => exact vo_pos hC (mem_hj hC hh hj2 (.inr hst)) hst
    | some w0 =>
      obtain ⟨hw0h, hw0s, hw0pa, hord⟩ := hcand rfl
      rcases hord with hgm | hpo
      · have := vo_gmo_st hC (gmo_r1 hC hrM hjM (po_hj hj1 hj2) hst (by show pa P C h _ = pa P C h j; rw [hpa, hpj]))
          hst
        have := vo_gmo_le hC hgm
        show vo P C w0 < _; omega
      · exact vo_gmo_st hC (gmo_r1 hC ⟨hw0h, .inr hw0s⟩ hjM (po_trans hpo (po_hj hj1 hj2)) hst
          (by rw [hw0pa]; show pa P C h _ = pa P C h j; rw [hpa, hpj])) hst
  -- the machine steps
  have hn : mNext P h H.fr (.load a (kts P C o) w (srcR rs1)) =
      some ⟨H.fr.pc + 1, H.fr.wr rd (if sgn then sext P.sz w else w), regWL rd [.ldres] ++ [.instr]⟩ := by
    simp only [mNext, hI.q, hI.pc, hi, instrNext, haddr, hal]
    simp [wordW, hwlt]
  have hmM := mMem.load (P := P) (log := memL (C.evs P) C.g) (i := h) H.prom H.ws a (kts P C o) w (srcR rs1)
    ⟨hmemv, hwin⟩
  have hs := hSteps.step _ _ _ _ _ _ _ _ hn hmM (hSteps_q _ (regWL_af rd [.ldres]) _ _ H.prom rfl)
  refine ⟨_, _, hs, ?_, ?_⟩
  · rw [foldl_regWL]
    generalize hvpd : max (ldPre H.ws (srcsView H.ws (srcR rs1))) (fwdView H.ws a (kts P C o)) = vp at hvp
    have hlen : ((s.emit ⟨.ld, s.ii, a, w, t1, [], s.ctl⟩).wr rd (ldExt P.sz sgn w, [s.evs.length])).adv.evs.length =
        s.evs.length + 1 := by simp [MSt.adv, (wr_same _ _ _).2.1, MSt.emit]
    have hrd' : ∀ r, (((s.emit ⟨.ld, s.ii, a, w, t1, [], s.ctl⟩).wr rd (ldExt P.sz sgn w, [s.evs.length])).adv).rd r
        = (s.wr rd (ldExt P.sz sgn w, [s.evs.length])).rd r := fun r => by
      show ((s.emit _).wr rd _).rd r = _
      rw [Cmp.rd_wr, Cmp.rd_wr]; rfl
    have hldv : (loadPost H.ws (srcsView H.ws (srcR rs1)) (ldPre H.ws (srcsView H.ws (srcR rs1))) a
        (kts P C o)).ldv = vp := by
      show max H.ws.ldv _ = vp; rw [hI.ldv, ← hvpd]; simp
    have hcoh : (loadPost H.ws (srcsView H.ws (srcR rs1)) (ldPre H.ws (srcsView H.ws (srcR rs1))) a
        (kts P C o)).coh = fun b => if b = a then max (H.ws.coh a) (max vp (kts P C o)) else H.ws.coh b := by
      rw [← hvpd]; rfl
    have hregs' := regs_wr2 hI.len hI.regs (H.fr.pc + 1) [] rd _ (ldExt P.sz sgn w, [s.evs.length])
      (Nat.mod_eq_of_lt (ldExt_lt hsz hwlt sgn))
    refine ⟨by simp [MSt.adv, (wr_same _ _ _).1, MSt.emit, hI.pc], rfl, by rw [front_wr_len, hI.len],
      fun r => by rw [hrd']; exact hregs' r,
      fun r => by rw [hrd']; exact regLt_wr hI.regLt rd _ (ldExt_lt hsz hwlt sgn) r, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, rfl, ?_⟩
    · -- regv
      intro r h0 h32
      show dom P C h (· ∈ ((((s.emit _).wr rd _).adv).rd r).2)
        (if rd ≠ 0 ∧ r = rd then srcsView (loadPost _ _ _ _ _) [.ldres] else H.ws.regv r)
      rw [hrd', Cmp.rd_wr, srcsView_ld, hldv]
      by_cases hr : r = rd
      · subst hr
        rw [if_pos (show r ≠ 0 ∧ r = r from ⟨by omega, rfl⟩),
          if_pos (show 0 < r ∧ r < 32 ∧ r = r from ⟨h0, h32, rfl⟩)]
        exact .inr ⟨s.evs.length, List.mem_singleton_self _, hvp⟩
      · rw [if_neg (show ¬ (rd ≠ 0 ∧ r = rd) from fun h' => hr h'.2),
          if_neg (show ¬ (0 < rd ∧ rd < 32 ∧ r = rd) from fun h' => hr h'.2.2)]
        exact hI.regv r h0 h32
    · -- vrOld
      rw [hlen]
      show dom P C h _ (max H.ws.vrOld _)
      rw [hvpd]
      exact dom_max (dom_mono hI.vrOld (fun j hj => ⟨by omega, hj.2⟩)) (.inr ⟨_, ⟨by omega, hkd⟩, hvp⟩)
    · rw [hlen]; exact dom_mono hI.vwOld (fun j hj => ⟨by omega, hj.2⟩)
    · rw [hlen]; intro j hj1 hj2 hld; exact hI.vrNew j (by omega) hj2 hld
    · rw [hlen]; intro j hj1 hj2 hst; exact hI.vwNew j (by omega) hj2 hst
    · -- vcap (rule 13)
      rw [hlen]; intro j hj1 hj2 hst
      show max (srcsView H.ws (srcR rs1)) H.ws.vcap < _
      refine Nat.max_lt.2 ⟨lt_vo_of hC hh hj2 hst hdva (fun i hi => ?_), hI.vcap j (by omega) hj2 hst⟩
      obtain ⟨hi1, hi2, hi3⟩ := ht1 i hi
      exact gmo_r13 hC (isMem_hj hh hi3 (.inl hi2)) (isMem_hj hh hj2 (.inr hst)) (po_hj (by omega) hj2) hst hrM
        (po_hj hi1 hnN) (po_hj (by omega) hj2) (by rw [hev]; exact hi)
    · -- coh1
      rw [hlen]; intro j hj1 hj2 hst
      rw [hcoh]
      show (if pa P C h j = a then _ else _) < _
      split
      · rename_i hpj
        have h0 := hI.coh1 j (by omega) hj2 hst; rw [hpj] at h0
        refine Nat.max_lt.2 ⟨h0, Nat.max_lt.2 ⟨?_, htlt j (by omega) hj2 hst hpj⟩⟩
        have := vo_gmo_st hC (gmo_r1 hC hrM (isMem_hj hh hj2 (.inr hst)) (po_hj (by omega) hj2) hst
          (by show pa P C h _ = pa P C h j; rw [hpa, hpj])) hst
        omega
      · exact hI.coh1 j (by omega) hj2 hst
    · -- coh2 (CoRR)
      rw [hlen]; intro j hj1 hj2 hld w' hw'g hw's hpaw hle o' hrf'
      rw [hcoh] at hle
      simp only at hle
      split at hle
      · rename_i hpj
        have hjM := isMem_hj hh hj2 (.inl hld)
        have hcorr := kts_corr hC hrM hjM hrL hld (po_hj (by omega) hj2)
          (by show pa P C h _ = pa P C h j; rw [hpa, hpj]) hrf hrf'
        by_cases hc : vo P C w' ≤ H.ws.coh a
        · exact hI.coh2 j (by omega) hj2 hld w' hw'g hw's hpaw (by rw [hpj]; exact hc) o' hrf'
        · by_cases hc2 : vo P C w' ≤ kts P C o
          · omega
          · have hle3 : vo P C w' ≤ vo P C (h, s.evs.length) := by omega
            have hw'M := (mem_g hC w').1 hw'g
            have hne : w' ≠ (h, s.evs.length) := fun he => MEvsF.ld_st hrL (he ▸ hw's)
            have hgw := gmo_of_vo hC hw'M hw's hrM hne hle3
            have := kts_ge hC hrf ⟨hw'M.1, hw's, by rw [hpaw]; show pa P C h j = pa P C h _; rw [hpa, hpj], .inl hgw⟩
            omega
      · exact hI.coh2 j (by omega) hj2 hld w' hw'g hw's hpaw hle o' hrf'
    · rw [hlen]; intro b
      exact fwdOk_mono (hI.fwd b) (fun h' => by rw [hkd] at h'; cases h'.1)
    · rw [hlen]; exact prom_mono hI.prom (by rw [hkd]; intro h'; cases h')
  · have hlv := loadVals_af _ (regWL_af rd [.ldres])
    have e1 : loadVals ((MLab.load a (kts P C o) w (srcR rs1), none) ::
        (regWL rd [.ldres] ++ [MLab.instr]).map (fun l => (l, none))) = w :: [] := by
      rw [← hlv]; rfl
    rw [e1]
    simp [ldVals, MSt.adv, (wr_same _ _ _).2.1, MSt.emit, List.filterMap_append]

/-- A STORE. -/
theorem step_store (hwf : P.wf) {s : Weak.Mini.MSt} {H : MHart} (hI : Inv P C h s H) {rs2 rs1 off : Nat}
    (hi : (P.prog h)[s.pc]? = some (.store rs2 rs1 off))
    (hX : SC P C h s (exec P.sz h C.V s (.store rs2 rs1 off))) :
    StepOk P C h s (exec P.sz h C.V s (.store rs2 rs1 off)) H := by
  have hmem := List.mem_of_getElem? hi
  have hreg : rs1 < 32 ∧ rs2 < 32 := (hwf.2.2 h _ hmem).2
  have hg := hgmo hC
  rcases h1 : s.rd rs1 with ⟨v1, t1⟩
  rcases h2 : s.rd rs2 with ⟨v2, t2⟩
  have hex : exec P.sz h C.V s (.store rs2 rs1 off) =
      (s.emit ⟨.st, s.ii, MAlu.add.eval v1 (off % two64), v2 % 2 ^ (8 * P.sz), t1, t2, s.ctl⟩).adv := by
    simp [exec, h1, h2]
  rw [hex] at hX ⊢
  have haddr : (H.fr.rd rs1 + off) % two64 = MAlu.add.eval v1 (off % two64) := by
    rw [hI.regs, h1]; simp [MAlu.eval]
  generalize MAlu.add.eval v1 (off % two64) = a at hX haddr ⊢
  obtain ⟨hev, hnN⟩ := hX.next ⟨.st, s.ii, a, v2 % 2 ^ (8 * P.sz), t1, t2, s.ctl⟩ rfl
  have hkd : kd P C h s.evs.length = .st := by unfold kd; rw [hev]
  have hrM : (C.evs P).isMem (h, s.evs.length) := isMem_hj hh hnN (.inr hkd)
  have hrS : (C.evs P).isSt (h, s.evs.length) := hkd
  have hrg := mem_hj hC hh hnN (.inr hkd)
  have hpa : pa P C h s.evs.length = a := by unfold pa; rw [hev]
  have hal : a % P.sz = 0 := by have := hC.2.2.1 _ hrM; rw [hev] at this; exact this
  have hr2 : H.fr.rd rs2 = v2 := by rw [hI.regs, h2]
  -- the sources: loads ppo-before the store (rules 9, 10)
  have hdva : dom P C h (· ∈ t1) (srcsView H.ws (srcR rs1)) := by
    have := dom_srcR hI.regv hreg.1; rw [h1] at this; exact this
  have hdvd : dom P C h (· ∈ t2) (srcsView H.ws (srcR rs2)) := by
    have := dom_srcR hI.regv hreg.2; rw [h2] at this; exact this
  have ht : ∀ i, i ∈ t1 ∨ i ∈ t2 → i < s.evs.length ∧ kd P C h i = .ld ∧ i < NN P C h := by
    intro i hi
    rcases hi with hi | hi
    · exact hX.taint i (hX.wf.rd rs1 i (by rw [h1]; exact hi))
    · exact hX.taint i (hX.wf.rd rs2 i (by rw [h2]; exact hi))
  have hiM : ∀ i, i ∈ t1 ∨ i ∈ t2 → (C.evs P).isMem (h, i) :=
    fun i hi => isMem_hj hh (ht i hi).2.2 (.inl (ht i hi).2.1)
  have hva : srcsView H.ws (srcR rs1) < vo P C (h, s.evs.length) :=
    lt_vo_of hC hh hnN hkd hdva (fun i hi => gmo_r9 hC (hiM i (.inl hi)) hrM (po_hj (ht i (.inl hi)).1 hnN)
      (by rw [hev]; exact hi))
  have hvd : srcsView H.ws (srcR rs2) < vo P C (h, s.evs.length) :=
    lt_vo_of hC hh hnN hkd hdvd (fun i hi => gmo_r10 hC (hiM i (.inr hi)) hrM (po_hj (ht i (.inr hi)).1 hnN) hrS
      (by rw [hev]; exact hi))
  -- the machine steps
  have hn : mNext P h H.fr (.store a (v2 % 2 ^ (8 * P.sz)) (srcR rs1) (srcR rs2)) =
      some ⟨H.fr.pc + 1, H.fr.regs, [.instr]⟩ := by
    simp only [mNext, hI.q, hI.pc, hi, instrNext, haddr, hal, hr2]
    simp [wordW]
  obtain ⟨hpos, hget⟩ := voL_mem C.g hrg hkd
  have hmM := mMem.store (P := P) (log := memL (C.evs P) C.g) (i := h) H.prom H.ws a (v2 % 2 ^ (8 * P.sz))
    (srcR rs1) (srcR rs2) (vo P C (h, s.evs.length))
    ((hI.prom _).2 ⟨_, Nat.le_refl _, hnN, hkd, rfl⟩)
    (by unfold vo; rw [hget]; simp only [msgOf]; rw [hev])
    (by have := hI.coh1 _ (Nat.le_refl _) hnN hkd; rw [hpa] at this; exact this)
    (Nat.max_lt.2 ⟨hva, Nat.max_lt.2 ⟨hvd, Nat.max_lt.2 ⟨hI.vcap _ (Nat.le_refl _) hnN hkd,
      hI.vwNew _ (Nat.le_refl _) hnN hkd⟩⟩⟩)
  have haf : ∀ l ∈ [MLab.instr], AF l := by simp [AF]
  have hs := hSteps.step _ _ _ _ _ _ _ _ hn hmM (hSteps_q _ haf _ _ _ rfl)
  refine ⟨_, _, hs, ?_, ?_⟩
  · simp only [List.foldl_cons, List.foldl_nil, eff]
    have hlen : ((s.emit ⟨.st, s.ii, a, v2 % 2 ^ (8 * P.sz), t1, t2, s.ctl⟩).adv).evs.length =
        s.evs.length + 1 := by simp [MSt.adv, MSt.emit]
    refine ⟨by simp [MSt.adv, MSt.emit, hI.pc], rfl, hI.len, fun r => by rw [front_rd_same]; exact hI.regs r,
      hI.regLt, hI.regv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
    · rw [hlen]; exact dom_mono hI.vrOld (fun j hj => ⟨by omega, hj.2⟩)
    · rw [hlen]
      show dom P C h _ (max H.ws.vwOld _)
      exact dom_max (dom_mono hI.vwOld (fun j hj => ⟨by omega, hj.2⟩)) (.inr ⟨_, ⟨by omega, hkd⟩, Nat.le_refl _⟩)
    · rw [hlen]; intro j hj1 hj2 hld; exact hI.vrNew j (by omega) hj2 hld
    · rw [hlen]; intro j hj1 hj2 hst; exact hI.vwNew j (by omega) hj2 hst
    · -- vcap (rule 13)
      rw [hlen]; intro j hj1 hj2 hst
      show max (srcsView H.ws (srcR rs1)) H.ws.vcap < _
      refine Nat.max_lt.2 ⟨lt_vo_of hC hh hj2 hst hdva (fun i hi => ?_), hI.vcap j (by omega) hj2 hst⟩
      exact gmo_r13 hC (hiM i (.inl hi)) (isMem_hj hh hj2 (.inr hst)) (po_hj (by have := (ht i (.inl hi)).1; omega) hj2)
        hst hrM (po_hj (ht i (.inl hi)).1 hnN) (po_hj (by omega) hj2) (by rw [hev]; exact hi)
    · -- coh1 (rule 1)
      rw [hlen]; intro j hj1 hj2 hst
      show (if pa P C h j = a then _ else _) < _
      split
      · rename_i hpj
        have h0 := hI.coh1 j (by omega) hj2 hst; rw [hpj] at h0
        refine Nat.max_lt.2 ⟨h0, vo_gmo_st hC (gmo_r1 hC hrM (isMem_hj hh hj2 (.inr hst)) (po_hj (by omega) hj2) hst
          (by show pa P C h _ = pa P C h j; rw [hpa, hpj])) hst⟩
      · exact hI.coh1 j (by omega) hj2 hst
    · -- coh2
      rw [hlen]; intro j hj1 hj2 hld w' hw'g hw's hpaw hle o' hrf'
      simp only [storePost] at hle
      split at hle
      · rename_i hpj
        by_cases hc : vo P C w' ≤ H.ws.coh a
        · exact hI.coh2 j (by omega) hj2 hld w' hw'g hw's hpaw (by rw [hpj]; exact hc) o' hrf'
        · have hc2 : vo P C w' ≤ vo P C (h, s.evs.length) := by omega
          have := kts_ge hC hrf' ⟨hrM.1, hrS, by show pa P C h _ = pa P C h j; rw [hpa, hpj],
            .inr (po_hj (by omega) hj2)⟩
          omega
      · exact hI.coh2 j (by omega) hj2 hld w' hw'g hw's hpaw hle o' hrf'
    · -- the forward bank (rule 12)
      rw [hlen]; intro b
      show fwdOk P C h _ b (if b = a then _ else _)
      split
      · rename_i hba
        subst hba
        refine ⟨s.evs.length, by omega, hkd, hpa, fun j2 h1 h2 _ => by omega, rfl, ?_⟩
        intro j' hj1 hj2 hld hpj hrf'
        have hjM := isMem_hj hh hj2 (.inl hld)
        refine le_vo_of hC (dom_max (dom_mono hdva (fun i hi => Or.inl hi)) (dom_mono hdvd (fun i hi => Or.inr hi)))
          (fun i hi => ?_)
        have hi1 := (ht i hi).1
        exact gmo_r12 hC (hiM i hi) hjM (po_hj (by omega) hj2) hld hrM.1 (po_hj hi1 hnN) (po_hj (by omega) hj2) hrS
          (by rw [hev]; exact hi) hrf'
      · rename_i hba
        exact fwdOk_mono (hI.fwd b) (fun h' => hba (h'.2 ▸ hpa))
    · -- promises: the store's own is fulfilled
      rw [hlen]; intro t
      show t ∈ H.prom.filter _ ↔ _
      rw [List.mem_filter, hI.prom t]
      constructor
      · rintro ⟨⟨j, hj1, hj2, hj3, rfl⟩, hne⟩
        refine ⟨j, ?_, hj2, hj3, rfl⟩
        rcases Nat.lt_or_ge s.evs.length j with h5 | h5
        · exact h5
        · have : j = s.evs.length := by omega
          subst this; simp at hne
      · rintro ⟨j, hj1, hj2, hj3, rfl⟩
        refine ⟨⟨j, by omega, hj2, hj3, rfl⟩, ?_⟩
        have hne : vo P C (h, j) ≠ vo P C (h, s.evs.length) := fun he => by
          have := vo_inj hC (isMem_hj hh hj2 (.inr hj3)) hrM hj3 hkd he
          simp at this; omega
        simpa using hne
  · have e1 : loadVals ((MLab.store a (v2 % 2 ^ (8 * P.sz)) (srcR rs1) (srcR rs2), some (vo P C (h, s.evs.length)))
        :: [MLab.instr].map (fun l => (l, none))) = [] := rfl
    rw [e1]
    simp [ldVals, MSt.adv, MSt.emit, List.filterMap_append]

end steps

end Weak.Mini.Cmp
