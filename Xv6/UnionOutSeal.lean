/-
**THE UNION LEDGER'S STEPS AND ITS BIRTH** (lane U4, the U4 seal wave) --
the declarations of Rocq `UnionOut.v` (`/shared/xv6rocq/iris/UnionOut.v` @
1900b8a43) §5-§7 reached only through the instance `union_laws_at`
(`App.xv6_app_laws`), which the U0-X glob walk cannot see: `union_birth_all`,
`union_led_init`, `union_era_split`, `union_led_pow`, `union_led_tx`, `union_led_rx`.

## DEVIATIONS from Rocq

1. The counter cases classically (`UnionOutLed` deviation 1): `decide_ext`
   is `if_pos`/`if_neg` at the landed `open Classical` ite.
2. Rocq's section parameter `ug` is explicit; `S (obs_boots h)` is
   `obsBoots h + 1`.
-/
import Xv6.UnionOutLed
import Xv6.FileOutSeal
import Xv6.UnionOutPureSeal
import Xv6.EchoOutSealEra
import Xv6.PipeOutSeal

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL

set_option linter.unusedSectionVars false

section UnionBirth
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [DiskG GF]
  [EchoOutG GF] [FileAppG GF] [FileOutG GF] [PipeOutG GF]

/-- **Rocq `union_birth_all`**: the file's birth, and the byte ledger's map
beside it. -/
theorem unionBirthAll : ⊢@{IProp GF} |==> ∃ ug : UnionGn, unionClAll (hlc := hlc) ug := by
  imod (fileBirthAll (hlc := hlc) (GF := GF)) with ⟨%g, Hf⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := Nat) (V := PipeEra) (H := RegMapF)) with ⟨%gm, Hm⟩
  imodintro
  iexists ⟨g, gm⟩
  unfold unionClAll
  iframe Hf Hm

/-- **Rocq `union_led_init`**: the ledger is born empty. -/
theorem unionLed_init (ug : UnionGn) : ⊢ unionClAll (hlc := hlc) (GF := GF) ug -∗ unionLed ug [] := by
  unfold unionClAll fileClAll fileCl echoCl unionLed pinMap f0Map peraMap
  iintro ⟨⟨⟨⟨Ht, Hm⟩, Hfl⟩, Hmf⟩, Hme⟩
  have hd : lmDisc ulmG [] := lmDisc_nil ulmG
  rw [if_pos hd, show eflOf ([] : List Obs) = [] from rfl]
  dsimp only [fgnEcho, ugnPipe]
  isplitl [Ht]
  · iexact Ht
  isplitl [Hm]
  · iexists ∅; iframe Hm; ipureintro; exact pinDom_empty _
  isplitl [Hmf]
  · iexists ∅; iframe Hmf; ipureintro; exact pinDom_empty _
  isplitl [Hme]
  · iexists ∅; iframe Hme; ipureintro; exact pinDom_empty _
  isplitl [Hfl]
  · iexact Hfl
  ileft
  unfold unionPhiRes
  iexists ([] : List Fstate)
  isplitr
  · ipureintro; intro _; exact unionPhiBody_nil
  · iapply (f0Pinned_undrained (GF := GF) ug.ugnFile [] [] rfl)

/-- **Rocq `union_era_split`**: THE FOUNDING -- the era's ghosts become the
claim at the start of its era and init's credential. -/
theorem union_era_split (ug : UnionGn) (k : Nat) (v : EraPins) (vf : FileEra) (w : PipeEra) (gb : GName) :
    ⊢ eraPin (GF := GF) (fgnEcho ug.ugnFile) k v -∗ fileEraPin ug.ugnFile k vf -∗ peraPin (ugnPipe ug) k w -∗
      eraFull (hlc := hlc) v -∗ f0Auth vf [] -∗ f0fAuth vf [] -∗ blkAuth w [] -∗ rblkAuth gb [] -∗
      curHalf w 1 0 gb false -∗
      ucl (hlc := hlc) ug k [] ⟨[], [], [], none⟩ ∗ fturn (GF := GF) ug.ugnFile k := by
  unfold eraFull
  iintro #Hpin #Hfp #Hpera ⟨Ht, Hcs, Hps, HE, Hdl, Hdll, Hsc, Hrp⟩ Hf0 Hfla Hblk Hrb Hcur1
  have hsplit := (inferInstance : Fractional (PROP := IProp GF)
    (fun q : Qp => MonoNat.auth_own v.go (DFrac.own q) (.ofNat 0))).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hsplit
  ihave ⟨Ht1, Ht2⟩ := hsplit.mp $$ Ht
  have hdl := ghost_var_split (GF := GF) v.gdl (0 : Nat) (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hdl
  unfold dlCnt
  ihave ⟨Hdl1, Hdl2⟩ := hdl $$ Hdl
  ihave ⟨Hcs, #Hcslb⟩ := csLb_get (GF := GF) v [] $$ Hcs
  ihave ⟨Hps, #Hpslb⟩ := psLb_get (GF := GF) v [] $$ Hps
  ihave ⟨Hdll, #Hdllb⟩ := dlListLb_get (GF := GF) v [] $$ Hdll
  ihave #Hinp := inpLb_of_dlLb (GF := GF) v [] [] (List.nil_prefix) $$ Hdllb
  isplitl [Ht1 Hcs Hps HE Hdl1 Hdll Hfla Hblk Hrb Hcur1 Hsc]
  · unfold ucl
    have hm := pwclV_mid (ugnPipe ug) ulmG (ucparams (hlc := hlc) (GF := GF) ug) (∅ : Fstate) (uwa ug) uwild
      k [] ⟨[], [], [], none⟩ v
    rw [ucparams_gcPIN] at hm
    unfold seccFlag at hm
    iapply hm $$ Hpin Hsc
    unfold peclV
    ileft
    unfold gcl
    iright
    iexists v, gstage0 ulmG
    have hst : lmStream ulmG (∅ : Fstate) (gstage0 ulmG) = [] := rfl
    have hpc : lmPcount ulmG (gstage0 ulmG).gsPs (gstage0 ulmG).gsCs (gsState ulmG (∅ : Fstate) (gstage0 ulmG))
        (gstage0 ulmG).gsE (gstage0 ulmG).gsW = 0 := rfl
    rw [ucparams_gcPIN, hst, hpc]
    dsimp only [uwa, gstage0]
    isplitr
    · iexact Hpin
    isplitl [Hfla]
    · unfold f0wa
      dsimp only [optList, Option.getD]
      iexists vf
      iframe Hfp Hfla
      isplitl []
      · unfold f0Wit; iempintro
      · iapply (f0Typed_none (GF := GF) ug.ugnFile)
    isplitl [Hblk Hrb Hcur1]
    · unfold pext
      iexists w, 0, gb, ([] : List (BitVec 8)), false
      iframe Hpera Hblk Hcur1 Hrb
    unfold turnAuth dlCnt
    dsimp only [List.length_nil]
    iframe Ht1 Hcs Hps HE Hdl1 Hdll
    ipureintro
    refine ⟨lmOutPure_0 ulmG (∅ : Fstate) k [] fstateOk_empty, lmCsLenOk_0 ulmG, lmPsLenOk_0 ulmG (∅ : Fstate),
      ginPure_0 ulmG k, ?_, ?_, lmDlOk_0 ulmG⟩
    · simp [garmEra]
    · rfl
  · unfold fturn turn dlCnt
    iexists v, vf
    iframe Hpin Hfp Ht2 Hdl2 Hcslb Hpslb Hinp Hrp Hf0

open Classical in
/-- **Rocq `union_led_pow`**: THE POWER STEP -- the on-arm allocates the
era's three records, mints the pins, and splits the ghosts into the era's
claim and init's credential. -/
theorem unionLed_pow (ug : UnionGn) (h : List Obs) (on : Bool) :
    unionLed (hlc := hlc) (GF := GF) ug h ⊢ |==> (unionLed ug (h ++ [powerEv on]) ∗
      (if on then iprop(emp)
       else iprop(ucl (hlc := hlc) ug (obsBoots h + 1) [] ⟨[], [], [], none⟩ ∗
         fturn (GF := GF) ug.ugnFile (obsBoots h + 1)))) := by
  have hdp := lmDisc_power ulmG h on unionSt_ok
  have hite : (if lmDisc ulmG (h ++ [powerEv on]) then (0 : Nat) else 1) =
      (if lmDisc ulmG h then (0 : Nat) else 1) := by
    unfold powerEv; by_cases hd : lmDisc ulmG h
    · rw [if_pos hd, if_pos (hdp.2 hd)]
    · rw [if_neg hd, if_neg (fun h' => hd (hdp.1 h'))]
  have hefl := eflOf_power h on
  unfold unionLed
  rw [hite, hefl]
  iintro ⟨Ht, Hpm, Hfm, Hme, Hfl, Hphi⟩
  cases on with
  | true =>
    have he : obsBoots [powerEv true] = 0 := rfl
    ihave Hpm := pinMap_step (GF := GF) (fgnEcho ug.ugnFile) h (powerEv true) he $$ Hpm
    ihave Hfm := f0Map_step (GF := GF) ug.ugnFile h (powerEv true) he $$ Hfm
    ihave Hme := peraMap_step (GF := GF) (ugnPipe ug) h (powerEv true) he $$ Hme
    imodintro
    isplitl [Ht Hpm Hfm Hme Hfl Hphi]
    · iframe Ht Hpm Hfm Hme Hfl
      icases Hphi with (Hphi | #HT)
      · ileft
        unfold unionPhiRes
        icases Hphi with ⟨%s0s, %hb, -⟩
        iexists s0s
        isplitr
        · ipureintro
          intro hd
          exact unionPhiBody_off h s0s (hb ((lmDisc_power ulmG h true unionSt_ok).1 hd))
        · iapply (f0Pinned_undrained (GF := GF) ug.ugnFile _ s0s)
          rw [openSeg_power _ _ rfl]; rfl
      · iright; iexact HT
    · iempintro
  | false =>
    simp only [powerEv, Bool.false_eq_true, ↓reduceIte]
    imod (eraFull_alloc (hlc := hlc) (GF := GF)) with ⟨%v, Hfull⟩
    imod (f0Alloc (GF := GF)) with ⟨%vf, Hf0, Hfla⟩
    imod (blkAlloc (GF := GF)) with ⟨%w, %gb, Hblk, Hrb, Hcur1⟩
    imod (pinMap_on (GF := GF) (fgnEcho ug.ugnFile) h v) $$ Hpm with ⟨Hpm, #Hpin⟩
    imod (f0Map_on (GF := GF) ug.ugnFile h vf) $$ Hfm with ⟨Hfm, #Hfp⟩
    imod (peraMap_on (GF := GF) (ugnPipe ug) h w) $$ Hme with ⟨Hme, #Hpera⟩
    ihave ⟨Hcl, Hturn⟩ := (union_era_split (hlc := hlc) (GF := GF) ug (obsBoots h + 1) v vf w gb)
      $$ Hpin Hfp Hpera Hfull Hf0 Hfla Hblk Hrb Hcur1
    imodintro
    isplitl [Ht Hpm Hfm Hme Hfl Hphi]
    · iframe Ht Hpm Hfm Hme Hfl
      icases Hphi with (Hphi | #HT)
      · ileft
        unfold unionPhiRes
        icases Hphi with ⟨%s0s, %hb, -⟩
        iexists s0s ++ [∅]
        isplitr
        · ipureintro
          intro hd
          exact unionPhiBody_on h s0s (hb ((lmDisc_power ulmG h false unionSt_ok).1 hd))
        · iapply (f0Pinned_undrained (GF := GF) ug.ugnFile _ _)
          rw [openSeg_power _ _ rfl]; rfl
      · iright; iexact HT
    · iframe Hcl Hturn

open Classical in
/-- **Rocq `union_led_rx`**: THE INPUT STEP -- the counter decides, and the
byte's TAG is handed out, its line list's lower bound grown by what the
input completed. -/
theorem unionLed_rx (ug : UnionGn) (h : List Obs) (i : UartId) (b : BitVec 8) (hsh : traceShape h true) :
    unionLed (hlc := hlc) (GF := GF) ug h ⊢
      |==> (unionLed ug (h ++ [Obs.dev (.uartIn i b)]) ∗ utag (hlc := hlc) ug (h ++ [Obs.dev (.uartIn i b)])) := by
  have he : obsBoots [Obs.dev (.uartIn i b)] = 0 := rfl
  have hin : lmDisc ulmG (h ++ [Obs.dev (.uartIn i b)]) → lmDisc ulmG h := by
    cases i with
    | uart0 => exact lmDisc_in ulmG (ulm_byte_laws admUG admSOn) h b hsh
    | uart1 => exact (lmDisc_other ulmG h (Obs.dev (.uartIn .uart1 b)) rfl (by simp [notConsIn]) hsh).1
  have hsh' : traceShape (h ++ [Obs.dev (.uartIn i b)]) true := traceShape_snoc h _ true true hsh rfl
  unfold unionLed
  iintro ⟨Hcnt, Hpm, Hfm, Hme, Hfl, Hphi⟩
  ihave Hpm := pinMap_step (GF := GF) (fgnEcho ug.ugnFile) h _ he $$ Hpm
  ihave Hfm := f0Map_step (GF := GF) ug.ugnFile h _ he $$ Hfm
  ihave Hme := peraMap_step (GF := GF) (ugnPipe ug) h _ he $$ Hme
  imod (flAuth_grow_pre (GF := GF) ug.ugnFile (eflOf h) (eflOf (h ++ [Obs.dev (.uartIn i b)]))
    (eflOf_snoc h _)) $$ Hfl with ⟨Hfl, #Hfllb⟩
  ihave Hphi : iprop(unionPhiRes (GF := GF) ug (h ++ [Obs.dev (.uartIn i b)]) ∨
      fileTaint (hlc := hlc) (GF := GF) ug.ugnFile.fgnCl) $$ [Hphi]
  · icases Hphi with (Hphi | #HT)
    · ileft
      unfold unionPhiRes
      icases Hphi with ⟨%s0s, %hb, #Hp⟩
      iexists s0s
      isplitr
      · ipureintro
        intro hd
        exact unionPhiBody_step_io h _ s0s hsh rfl (by cases i <;> rfl) (hb (hin hd))
      · iapply (f0Pinned_io (GF := GF) ug.ugnFile h _ s0s rfl (by cases i <;> rfl)) $$ Hp
    · iright; iexact HT
  unfold utag
  by_cases hd' : lmDisc ulmG (h ++ [Obs.dev (.uartIn i b)])
  · rw [if_pos hd', if_pos (hin hd')]
    imodintro
    iframe Hcnt Hpm Hfm Hme Hfl Hphi Hfllb
    isplitr
    · ipureintro; exact hsh'
    · ileft; ipureintro; exact hd'
  · rw [if_neg hd']
    imod (MonoNat.own_update (fgnEcho ug.ugnFile).taint _ (.ofNat 1)
      (by split <;> simp [MaxNat.le_toNat])) $$ Hcnt with ⟨Hcnt, #Hlb⟩
    imodintro
    iframe Hcnt Hpm Hfm Hme Hfl Hphi Hfllb
    isplitr
    · ipureintro; exact hsh'
    · iright
      unfold fileTaint echoTaint fgnEcho at *
      iexact Hlb

/-- What a drain hands the ledger (Rocq `union_led_tx`'s premise). -/
noncomputable def unionTxGo (ug : UnionGn) (h : List Obs) (i : UartId) (b : BitVec 8) : IProp GF :=
  match i with
  | .uart0 => iprop(∃ (s0 : Fstate) (vf : FileEra),
      ⌜lmGoodOut ulmG s0 (openSeg h ++ [Obs.dev (.uartOut .uart0 b)])⌝ ∗ f0Typed ug.ugnFile s0
      ∗ fileEraPin ug.ugnFile (obsBoots h) vf ∗ f0Lb vf s0)
  | .uart1 => iprop(True)

open Classical in
/-- **Rocq `union_led_tx`**: THE OUTPUT STEP, AND THE ERA'S FIRST DRAIN. -/
theorem unionLed_tx (ug : UnionGn) (h : List Obs) (i : UartId) (b : BitVec 8) (hsh : traceShape h true) :
    ⊢ (fileTaint (hlc := hlc) (GF := GF) ug.ugnFile.fgnCl ∨ unionTxGo (GF := GF) ug h i b) -∗
      unionLed ug h ==∗ unionLed ug (h ++ [Obs.dev (.uartOut i b)]) := by
  have he : obsBoots [Obs.dev (.uartOut i b)] = 0 := rfl
  have hdo := lmDisc_out ulmG h i b hsh
  have hite : (if lmDisc ulmG (h ++ [Obs.dev (.uartOut i b)]) then (0 : Nat) else 1) =
      (if lmDisc ulmG h then (0 : Nat) else 1) := by
    by_cases hd : lmDisc ulmG h
    · rw [if_pos hd, if_pos (hdo.2 hd)]
    · rw [if_neg hd, if_neg (fun h' => hd (hdo.1 h'))]
  unfold unionLed
  rw [hite, eflOf_out h i b hsh]
  iintro Hgo ⟨Hcnt, Hpm, Hfm, Hme, Hfl, Hphi⟩
  ihave Hpm := pinMap_step (GF := GF) (fgnEcho ug.ugnFile) h _ he $$ Hpm
  ihave Hfm := f0Map_step (GF := GF) ug.ugnFile h _ he $$ Hfm
  ihave Hme := peraMap_step (GF := GF) (ugnPipe ug) h _ he $$ Hme
  iframe Hcnt Hpm Hfm Hme
  icases Hphi with (Hphi | #HT)
  · unfold unionPhiRes
    icases Hphi with ⟨%s0s, %hb, #Hpin0⟩
    cases i with
    | uart1 =>
      imodintro
      iframe Hfl
      ileft
      iexists s0s
      isplitr
      · ipureintro
        intro hd
        exact unionPhiBody_step_io h _ s0s hsh rfl rfl (hb ((lmDisc_out ulmG h .uart1 b hsh).1 hd))
      · iapply (f0Pinned_io (GF := GF) ug.ugnFile h _ s0s rfl rfl) $$ Hpin0
    | uart0 =>
      icases Hgo with (#HT | Hgo)
      · imodintro; iframe Hfl; iright; iexact HT
      unfold unionTxGo
      icases Hgo with ⟨%s0, %vf, %hgo, #Hty, #Hfp, #Hlb⟩
      ihave ⟨Hfl, %hadm⟩ := (f0Typed_adm (GF := GF) ug.ugnFile (eflOf h) s0) $$ [Hfl Hty]
      · iframe Hfl Hty
      ihave %hlast : iprop(⌜obsWire .uart0 (openSeg h) ≠ [] → ∃ u1, s0s = u1 ++ [s0]⌝) $$ []
      · by_cases hw : obsWire .uart0 (openSeg h) = []
        · ipureintro; intro hne; exact absurd hw hne
        · ihave %hl := (f0Pinned_drained (GF := GF) ug.ugnFile h s0s vf s0 hw) $$ [Hfp Hlb Hpin0]
          · iframe Hfp Hlb Hpin0
          ipureintro; intro _; exact hl
      imodintro
      iframe Hfl
      ileft
      iexists s0s.dropLast ++ [s0]
      isplitr
      · ipureintro
        intro hd
        have hd0 := (lmDisc_out ulmG h .uart0 b hsh).1 hd
        exact unionPhiBody_drain h b s0s s0 hsh hd0 hgo hadm hlast (hb hd0)
      · iapply (f0Pinned_drain (GF := GF) ug.ugnFile h b s0s.dropLast vf s0) $$ [Hfp Hlb]
        iframe Hfp Hlb
  · imodintro; iframe Hfl; iright; iexact HT

end UnionBirth

end Xv6
