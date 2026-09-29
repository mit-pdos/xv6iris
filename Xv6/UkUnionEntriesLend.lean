/-
**THE FILE LINES' LENDS AT THE UNION RECORD: the console device out of the
round's cursor** (Rocq `UkUnionEntries.v` §1, pinned `1900b8a43`).

echo's lend at the console is the block at its first byte, code 0
(`uecho_lend`); cat's is the round's cursor at the block's first byte, the
round's state named -- the console owing the content or the diagnostic at a
present file, the diagnostic at an absent one (`ucat_lend`).

CONE (this file): `uecho_lend`, `ucat_lend` (and `ucat_alts`, pure, in
`UkUnionEntriesPure`).  Not reached: `ucat_lend_taint`.

## Deviations from Rocq

1. **The union's claim is a parameter (Union*, U1-F/U1-P, not ported)** (`HfpPipeP.UnionP`: `ucl`,
   `union_params_at` atoms; `unionLinks`), the console device H-io's
   (`UkConsOut.consDevAtc`).  Two facts Rocq reads off `union_params_at`'s BODY are
   therefore premises here, to be discharged by U1-P's definition:
   * the era's pin `era_pin (fgn_echo (ugn_file ug)) (S gen_id) v` is the
     parameters' own `gPIN (genId + 1) v` (Rocq: definitionally);
   * a file line is not a wild line, `¬ gwild I` (Rocq: `cbn [gwild
     union_params_at]; rewrite Hfl; discriminate`).
2. `cons_short` / `cons_adm` / `cons_cur` are H-io's UkConsOut
   `consShort` / `consAdm` / `consCur`.
-/
import Xv6.UkUnionEntriesPure
import Xv6.HfpPipeClaimsP
import Xv6.UexecExecInst

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Std (ExtTreeSet)
open Ualt HfpPipeP

set_option linter.unusedSectionVars false

section UkUnionLend
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FsTopG GF] [OffboxG GF]
  [Appcfg GF] [FsBytesG GF] [CtokG GF] [Fscfg] [Icfg] [DiskG GF] [EchoOutG GF]
  [PS : UprogSG GF]
  [GhostMapG GF Nat (BitVec 8) RegMapF] [GhostVarG GF Nat] [GhostMapG GF (Option Nat) UfdCell UfdMapF]
  [GhostVarG GF (ExtTreeSet GName compare)] [GhostVarG GF Int]

variable {FG : Type} (UP : UnionP hlc GF FG) (ug : UnionGn FG)

/-- **Rocq `uecho_lend`**: echo's lend at the console, the block at its
first byte, code 0 (deviation 1). -/
theorem uecho_lend (sb : Fstate) (v : EraPins) (I : List (BitVec 8)) (ws : List (List (BitVec 8)))
    (hfl : lmLineAt ulmG I = Uline.LEcho ws) (hshort : ((wlLine (ws.drop 1)).length : Int) < 2 ^ 31)
    (hwild : ¬ (UP.unionParamsAt ug sb).gwild I) :
    ⊢ unionLinks UP ug -∗ (UP.unionParamsAt ug sb).gPIN (genId (hlc := hlc) (GF := GF) + 1) v -∗
      gwcBlk (UP.unionParamsAt ug sb) (genId (hlc := hlc) (GF := GF) + 1) v I 0 0 -∗
      consDevAtc ulmG (UP.unionParamsAt ug sb) (unionLinks UP ug) [0] v I [wlLine (ws.drop 1)] := by
  have hs : consShort [wlLine (ws.drop 1)] := by
    intro x hx; rw [List.mem_singleton.mp hx]; exact hshort
  iintro #Hlk #Hpin Hb
  unfold gwcBlk
  icases Hb with (⟨%ps, %cs, %s1, %pos, %hw, Ht, #Hps, #Hcs, #HI, #HW⟩ | #HT)
  · have hbodies : [0].map (lmBody ulmG s1 cs I) = [wlLine (ws.drop 1)] := by
      simp [ulm_echo_body s1 cs I ws hfl]
    rw [← hbodies]
    iapply consDevAtc_of_blk0 ulmG (UP.unionParamsAt ug sb) (unionLinks UP ug) [0] v I ps cs s1 pos [0]
      hwild hw (List.Subset.refl _) (by intro c hc; simp at hc; subst hc; exact ulm_echo_adm s1 cs I ws hfl)
      (by rw [hbodies]; exact hs) $$ Hlk Hpin [Ht]
    unfold consCur
    iframe Ht Hps Hcs HI HW
  · iapply consDevAtc_taint ulmG (UP.unionParamsAt ug sb) (unionLinks UP ug) [0] v I _ hs $$ Hlk HT

/-- **Rocq `ucat_lend`**: cat's lend -- the round's cursor at the block's
first byte, the round's state named (deviation 1). -/
theorem ucat_lend (sb : Fstate) (v : EraPins) (ps cs : List Nat) (I : List (BitVec 8)) (pos : Nat)
    (nm : List (BitVec 8)) (content : Option (List (BitVec 8)))
    (hw : lmWrBlkT ulmG ps cs sb I pos) (hfl : lmLineAt ulmG I = Uline.LCat nm)
    (hst : (ulmState sb cs I)[nm]? = content) (hs : consShort (ucatAlts nm content))
    (hwild : ¬ (UP.unionParamsAt ug sb).gwild I) :
    ⊢ unionLinks UP ug -∗ (UP.unionParamsAt ug sb).gPIN (genId (hlc := hlc) (GF := GF) + 1) v -∗
      consCur (UP.unionParamsAt ug sb) v ps cs sb I pos 0 0 -∗
      consDevAtc ulmG (UP.unionParamsAt ug sb) (unionLinks UP ug)
        [ualtCode (UR .RCRan), ualtCode (UR .RCNoOpen)] v I (ucatAlts nm content) := by
  have hnp : ulineNopipe (lmLineAt ulmG I) := by rw [hfl]; exact ulineNopipe_cat nm
  have hadm : ∀ a : Ralt, raltOk (.LCat nm) a → consAdm ulmG sb cs I (ualtCode (UR a)) := by
    intro a ha
    exact ulm_cons_adm_R sb cs I a hnp (by rw [hfl]; exact ha)
  cases content with
  | some bs =>
    have hbodies : [ualtCode (UR .RCRan), ualtCode (UR .RCNoOpen)].map (lmBody ulmG sb cs I) =
        [bs, catDgOpen nm] := by
      simp [ulm_cat_body_ran sb cs I nm bs hfl hst, ulm_cat_body_noopen sb cs I nm hfl]
    rw [show ucatAlts nm (some bs) = [bs, catDgOpen nm] from rfl, ← hbodies]
    iintro #Hlk #Hpin Hc
    iapply consDevAtc_of_blk0 ulmG (UP.unionParamsAt ug sb) (unionLinks UP ug)
      [ualtCode (UR .RCRan), ualtCode (UR .RCNoOpen)] v I ps cs sb pos
      [ualtCode (UR .RCRan), ualtCode (UR .RCNoOpen)] hwild hw (List.Subset.refl _)
      (by
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hadm .RCRan trivial
        · rw [List.mem_singleton.mp hc]; exact hadm .RCNoOpen trivial)
      (by rw [hbodies]; exact hs) $$ Hlk Hpin Hc
  | none =>
    have hbodies : [ualtCode (UR .RCRan)].map (lmBody ulmG sb cs I) = [catDgOpen nm] := by
      simp [ulm_cat_body_ran_none sb cs I nm hfl hst]
    rw [show ucatAlts nm none = [catDgOpen nm] from rfl, ← hbodies]
    iintro #Hlk #Hpin Hc
    iapply consDevAtc_of_blk0 ulmG (UP.unionParamsAt ug sb) (unionLinks UP ug)
      [ualtCode (UR .RCRan), ualtCode (UR .RCNoOpen)] v I ps cs sb pos
      [ualtCode (UR .RCRan)] hwild hw
      (by intro x hx; rw [List.mem_singleton.mp hx]; exact List.mem_cons_self)
      (by
        intro c hc
        rw [List.mem_singleton.mp hc]
        exact hadm .RCRan trivial)
      (by rw [hbodies]; exact hs) $$ Hlk Hpin Hc

end UkUnionLend

end Xv6
