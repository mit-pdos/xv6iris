/-
**THE WALK'S LOOKUPS IN THE FS LEDGER, WITHOUT TOUCHING THE WALK** (NI M3
private files FS-2b; design of record `claude-notes/projects/noninterference.md`,
"M3 private files design (2026-10-05)" F4, and the coordinator's ruling (a) of
2026-10-06: back-pointers, the wrapper route).

namex fires one CALLER-SUPPLIED hop per path element (`FsAbsWalk.axHop`, at the
era lend `FsAbsEra.elend`).  So the ledger's lookups can be appended by the
CALLER's family rather than by namex: a call site that holds `ftopInv` wraps
its family before handing it to the walk, and namex, nameiparent and dirlookup
stay byte-identical (FS-1's estimate of threading the actor through ~46 walk
files is avoided).

* The wrapped cursor `walkCur` is the original cursor, the walk's ledger
  chain so far (`walkChain`: a lower bound of the ledger in which the
  lookups followed from the last one's position name the elements walked
  and resolve to the cursor's directory, `NiFs.fevWalkIs`), and the
  ORIGINAL family's unfired hops.  The wrapped miss cursor is the original
  one beside the original unfired hops past it.
* The wrapped hops therefore OWN NOTHING but `ftopInv` (persistent): each
  takes the original hop out of the cursor, appends `hop act d nm prev` --
  checked against the authority, so it lands past the chain's bound and
  `prev` points strictly earlier (`FsLedger.ftopLed_obsAfter`) -- fires the
  original hop and rebuilds the cursor.
* So every exit UNWRAPS exactly (`walkCur_unwrap`, `walkMiss_unwrap`): a
  walk that dies hands the client back its own unfired hops, as the failure
  posts (`SysOpenDefs.nameiWalkDeadEra`) demand.

`walkLook_fire` is `FsAbsOpenFire.opfOpen_fire_1`'s twin: the same terminal
observation commit, plus the type test's `look act i prev` appended past the
walk's chain (exec keeps the untwinned fire).
-/
import Xv6.FsAbsOpenFire

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL

section WalkLed
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [IcacheG GF] [Xv6G GF] [FdslotG GF]
  [BioslotG GF] [IrefslotG GF] [CtokG GF] [WchG GF] [FsTopG GF] [FsBytesG GF] [OffboxG GF]

/-- **AN OBSERVATION AT A HELD ROW, APPENDED PAST A BOUND THE CALLER HOLDS**:
the fragment pins the row in the fold before the event, the authority pins
the event past `L`. -/
theorem ftopObsAfterAt [Icfg] (γfs : FsNames) (E : CoPset) (hE : (↑ftopN : CoPset) ⊆ E) (e : Fev)
    (he : fevObs e) (L : List Fev) (dq : DFrac) (i : Nat) (n : FsNode) :
    ⊢@{IProp GF} ftopInv (hlc := hlc) γfs -∗ fsLedLb γfs L -∗ topFragQ (fsGammaL γfs) dq i n ={E}=∗
      topFragQ (fsGammaL γfs) dq i n ∗
      ∃ h : List Fev, ⌜L <+: h ∧ fevRows h i = ftopRow n⌝ ∗ fsLedLb γfs (h ++ [e]) := by
  iintro #Hi #HL Hf
  unfold ftopInv
  imod (inv_acc_timeless (E := E) (N := ftopN) (P := ftopBody (GF := GF) γfs) hE) $$ Hi
    with ⟨Hb, Hclose⟩
  unfold ftopBody
  icases Hb with ⟨%I, %A, Ha, Hla, Hpark, %hcl, Hled⟩
  unfold topFragQ fsGammaL
  ihave %hlk := ghost_map_lookup $$ Ha Hf
  imod ftopLed_obsAfter γfs I e he L $$ HL Hled with ⟨Hled, ⟨%h, %hh, #Hr⟩⟩
  imod Hclose $$ [Ha Hla Hpark Hled]
  · iexists I, A
    iframe Ha Hla Hpark Hled
    ipureintro; exact hcl
  imodintro
  iframe Hf
  iexists h
  iframe Hr
  ipureintro; exact ⟨hh.2, fevTie_row i n hh.1 hlk⟩

/-- (NI M3 private files FS-2a′) **open's PARKED INSTALL, AT THE ROW, AFTER A
LOWER BOUND**: `ftopObsAfterAt`'s twin for a parked inode install, the WHOLE
fresh shadow in hand: the ledger keeps its quarter (`FsLedger.ftopLed_pkOpen`),
the kernel's half and the row's quarter come back with the registration
witness the descriptor row will carry. -/
theorem ftopPkOpenAfterAt [Icfg] (γfs : FsNames) (E : CoPset) (hE : (↑ftopN : CoPset) ⊆ E)
    (a : BitVec 64) (i : Nat) (γo : GName) (po : Option Nat) (L : List Fev) (dq : DFrac) (n : FsNode) :
    ⊢@{IProp GF} ftopInv (hlc := hlc) γfs -∗ fsLedLb γfs L -∗ topFragQ (fsGammaL γfs) dq i n -∗
      offGv γo 1 0 ={E}=∗
      topFragQ (fsGammaL γfs) dq i n ∗ offGv γo (1 : Qp).half 0 ∗ offGv γo (1 : Qp).half.half 0 ∗
      fevPkWit γo ∗
      ∃ h : List Fev, ⌜L <+: h ∧ fevRows h i = ftopRow n⌝ ∗ fsLedLb γfs (h ++ [.open a i γo false po]) := by
  iintro #Hi #HL Hf Hw
  unfold ftopInv
  imod (inv_acc_timeless (E := E) (N := ftopN) (P := ftopBody (GF := GF) γfs) hE) $$ Hi
    with ⟨Hb, Hclose⟩
  unfold ftopBody
  icases Hb with ⟨%I, %A, Ha, Hla, Hpark, %hcl, Hled⟩
  unfold topFragQ fsGammaL
  ihave %hlk := ghost_map_lookup $$ Ha Hf
  imod ftopLed_pkOpen γfs I a i γo po L $$ HL Hw Hled with ⟨Hled, Hk, Hu, #Hwit, ⟨%h, %hh, #Hr⟩⟩
  imod Hclose $$ [Ha Hla Hpark Hled]
  · iexists I, A
    iframe Ha Hla Hpark Hled
    ipureintro; exact hcl
  imodintro
  iframe Hf Hk Hu Hwit
  iexists h
  iframe Hr
  ipureintro; exact ⟨hh.2, fevTie_row i n hh.1 hlk⟩

/-- **THE WALK's LEDGER CHAIN** after `k` elements of `es`, standing at `d`:
a lower bound in which the lookups followed from the last one's position
(`po`) name `es.take k` and resolve from the start `s0` to `d`. -/
def walkChain (γfs : FsNames) (rt s0 : Nat) (es : List Fname) (k d : Nat) : IProp GF :=
  iprop(∃ (H : List Fev) (po : Option Nat), fsLedLb γfs H ∗ ⌜fevWalkIs H rt s0 po (es.take k) d⌝)

instance walkChain_persistent (γfs : FsNames) (rt s0 : Nat) (es : List Fname) (k d : Nat) :
    Persistent (walkChain (GF := GF) γfs rt s0 es k d) := by
  unfold walkChain; infer_instance

/-- **THE WRAPPED CURSOR**: the original, the chain, the original unfired hops -/
def walkCur (γfs : FsNames) (rt s0 : Nat) (es : List Fname) (P Pmiss : Nat → Nat → IProp GF)
    (k d : Nat) : IProp GF :=
  iprop(P k d ∗ walkChain γfs rt s0 es k d ∗ axHopsFrom rt (elend (fsGammaL γfs)) P Pmiss es k)

/-- **THE WRAPPED MISS CURSOR**: the original, the original unfired hops past it -/
def walkMiss (γfs : FsNames) (rt : Nat) (es : List Fname) (P Pmiss : Nat → Nat → IProp GF)
    (k d : Nat) : IProp GF :=
  iprop(Pmiss k d ∗ axHopsFrom rt (elend (fsGammaL γfs)) P Pmiss es (k + 1))

theorem elend_open (Γ : FsViewNames GF) (d : Nat) (dq : DFrac) (ents : Std.ExtTreeMap Fname Nat compare) :
    elend Γ d dq ents ⊢
      ∃ n : FsNode, topFragQ Γ dq d n ∗ ⌜fnIsDir n = true ∧ dirEntries n = ents ∧ fnNlink n ≠ 0⌝ := by
  unfold elend; exact .rfl

theorem elend_close (Γ : FsViewNames GF) (d : Nat) (dq : DFrac) (ents : Std.ExtTreeMap Fname Nat compare)
    (n : FsNode) (hn : fnIsDir n = true ∧ dirEntries n = ents ∧ fnNlink n ≠ 0) :
    topFragQ Γ dq d n ⊢ elend Γ d dq ents := by
  unfold elend
  iintro H
  iexists n
  iframe H
  ipureintro; exact hn

/-- the wrapped cursor, unwrapped -/
theorem walkCur_unwrap (γfs : FsNames) (rt s0 : Nat) (es : List Fname) (P Pmiss : Nat → Nat → IProp GF)
    (k d : Nat) :
    walkCur (GF := GF) γfs rt s0 es P Pmiss k d ⊣⊢
      P k d ∗ walkChain γfs rt s0 es k d ∗ axHopsFrom rt (elend (fsGammaL γfs)) P Pmiss es k := by
  unfold walkCur; exact .rfl

/-- the wrapped miss cursor, unwrapped -/
theorem walkMiss_unwrap (γfs : FsNames) (rt : Nat) (es : List Fname) (P Pmiss : Nat → Nat → IProp GF)
    (k d : Nat) :
    walkMiss (GF := GF) γfs rt es P Pmiss k d ⊣⊢
      Pmiss k d ∗ axHopsFrom rt (elend (fsGammaL γfs)) P Pmiss es (k + 1) := by
  unfold walkMiss; exact .rfl

theorem walkChain_open (γfs : FsNames) (rt s0 : Nat) (es : List Fname) (k d : Nat) :
    walkChain (GF := GF) γfs rt s0 es k d ⊢
      ∃ (H : List Fev) (po : Option Nat), fsLedLb γfs H ∗ ⌜fevWalkIs H rt s0 po (es.take k) d⌝ := by
  unfold walkChain; exact .rfl

theorem walkChain_intro (γfs : FsNames) (rt s0 : Nat) (es : List Fname) (k d : Nat) (H : List Fev)
    (po : Option Nat) (hw : fevWalkIs H rt s0 po (es.take k) d) :
    fsLedLb (GF := GF) γfs H ⊢ walkChain γfs rt s0 es k d := by
  unfold walkChain
  iintro #H
  iexists H, po
  iframe H
  ipureintro; exact hw

/-- a directory's typed row is its entry map -/
theorem ftopRow_dir (n : FsNode) (hd : fnIsDir n = true) :
    ftopRow n = some (.dir (dirEntries n), fnNlink n) := by
  rw [ftopRow_typed n (fnIsDir_typed n hd), absRow_dir_eq n hd]; rfl

/-- the fold's lookup at a directory row is the lent entry map's, chroot's
self rule included -/
theorem fevHop_dir {h : List Fev} {rt d : Nat} {n : FsNode} (hd : fnIsDir n = true)
    (hr : fevRows h d = ftopRow n) (s : Fname) :
    fevHop h rt d s = if s = DOTDOT ∧ d = rt then some d else (dirEntries n)[s]? := by
  unfold fevHop
  rw [hr, ftopRow_dir n hd]
  rfl

theorem take_succ_of_get {es : List Fname} {k : Nat} {s : Fname} (hg : es[k]? = some s) :
    es.take (k + 1) = es.take k ++ [s] := by
  rw [List.take_succ, hg]; rfl

theorem drop_of_get {es : List Fname} {k : Nat} {s : Fname} (hg : es[k]? = some s) :
    es.drop k = s :: es.drop (k + 1) := by
  obtain ⟨hk, he⟩ := List.getElem?_eq_some_iff.mp hg
  rw [List.drop_eq_getElem_cons hk, he]

/-- **THE WRAPPED HOP**: owns nothing but `ftopInv`; takes the original hop
out of the cursor, appends the lookup past the chain's bound with the chain's
last position as its back-pointer, fires the original, re-forms the cursor. -/
theorem walkHop [Icfg] (γfs : FsNames) (act : BitVec 64) (rt s0 : Nat) (es : List Fname)
    (P Pmiss : Nat → Nat → IProp GF) (k : Nat) (s : Fname) (hg : es[k]? = some s) :
    ftopInv (hlc := hlc) γfs ⊢
      axHop rt (elend (fsGammaL γfs)) (walkCur γfs rt s0 es P Pmiss) (walkMiss γfs rt es P Pmiss) k s := by
  have hs := drop_of_get hg
  have htake := take_succ_of_get hg
  iintro #Hi
  unfold axHop
  iintro %d %ents %dqv Hc Hel
  icases (walkCur_unwrap γfs rt s0 es P Pmiss k d).1 $$ Hc with ⟨HP, Hch, Hh⟩
  icases walkChain_open γfs rt s0 es k d $$ Hch with ⟨%H, %po, #HL, %hw⟩
  ihave ⟨Hh0, Hh1⟩ := axHopsFrom_cons rt _ P Pmiss es k s _ hs $$ Hh
  icases elend_open _ _ _ _ $$ Hel with ⟨%n, Hf, %hn⟩
  imod ftopObsAfterAt γfs ⊤ CoPset.subseteq_top (.hop act d s po) trivial H dqv d n $$ Hi HL Hf
    with ⟨Hf, ⟨%h, %hh, #Hr⟩⟩
  ihave Hel := elend_close _ _ _ _ n hn $$ Hf
  unfold axHop
  imod Hh0 $$ %d %ents %dqv HP Hel with ⟨Hel, HA⟩
  obtain ⟨hdir, hents, -⟩ := hn
  have hhop := fevHop_dir (h := h) (rt := rt) hdir hh.2 s
  rw [hents] at hhop
  imodintro
  iframe Hel
  by_cases hsr : s = DOTDOT ∧ d = rt
  · rw [axHopAns_self rt P Pmiss k d s ents hsr.1 hsr.2,
      axHopAns_self rt (walkCur γfs rt s0 es P Pmiss) (walkMiss γfs rt es P Pmiss) k d s ents hsr.1 hsr.2]
    rw [if_pos hsr] at hhop
    iapply (walkCur_unwrap γfs rt s0 es P Pmiss (k + 1) d).2
    iframe HA Hh1
    iapply walkChain_intro γfs rt s0 es (k + 1) d _ (some h.length)
      (by rw [htake]; exact fevWalkIs_hop hh.1 hw act s hhop) $$ Hr
  · rw [axHopAns_rec rt P Pmiss k d s ents hsr,
      axHopAns_rec rt (walkCur γfs rt s0 es P Pmiss) (walkMiss γfs rt es P Pmiss) k d s ents hsr]
    rw [if_neg hsr] at hhop
    cases hc : ents[s]? with
    | none =>
      simp only [axHopNext]
      iapply (walkMiss_unwrap γfs rt es P Pmiss k d).2
      iframe HA Hh1
    | some c =>
      simp only [axHopNext]
      rw [hc] at hhop
      iapply (walkCur_unwrap γfs rt s0 es P Pmiss (k + 1) c).2
      iframe HA Hh1
      iapply walkChain_intro γfs rt s0 es (k + 1) c _ (some h.length)
        (by rw [htake]; exact fevWalkIs_hop hh.1 hw act s hhop) $$ Hr

/-- **THE WRAPPED FAMILY**, from any index -/
theorem walkHops [Icfg] (γfs : FsNames) (act : BitVec 64) (rt s0 : Nat) (es : List Fname)
    (P Pmiss : Nat → Nat → IProp GF) (n : Nat) :
    ftopInv (hlc := hlc) γfs ⊢
      axHopsFrom rt (elend (fsGammaL γfs)) (walkCur γfs rt s0 es P Pmiss) (walkMiss γfs rt es P Pmiss) es n := by
  refine (show ftopInv (hlc := hlc) γfs ⊢ □ ftopInv (hlc := hlc) γfs by
    iintro #H; imodintro; iexact H).trans ?_
  unfold axHopsFrom
  refine BigSepL.bigSepL_intro (fun j s hj => ?_)
  have hg : es[n + j]? = some s := by rw [← List.getElem?_drop]; exact hj
  iintro #H
  iapply (walkHop γfs act rt s0 es P Pmiss (n + j) s hg) $$ H

/-- **THE WRAPPED START** (namei's side, at the path the call fetched) -/
theorem walkStart [Icfg] (γfs : FsNames) (act : BitVec 64) (rt cw : Nat) (P Pmiss : Nat → Nat → IProp GF)
    (pl : List (BitVec 8)) :
    ftopInv (hlc := hlc) γfs ⊢ exStart γfs rt cw P Pmiss pl -∗
      exStart γfs rt cw (walkCur γfs rt (umStartOf rt cw pl) (pathElems pl) P Pmiss)
        (walkMiss γfs rt (pathElems pl) P Pmiss) pl := by
  iintro #Hi Hs
  unfold exStart
  iintro %r %hr
  imod Hs $$ %r %hr with ⟨HP, Hh⟩
  imod (fsLedLb_nil γfs) with #HL
  ihave Hw := walkHops γfs act rt (umStartOf rt cw pl) (pathElems pl) P Pmiss 0 $$ Hi
  imodintro
  rw [exHops_is_axHops, exHops_is_axHops]
  iframe Hw
  iapply (walkCur_unwrap γfs rt (umStartOf rt cw pl) (pathElems pl) P Pmiss 0 r).2
  iframe HP Hh
  iapply walkChain_intro γfs rt _ _ 0 r [] none (by rw [List.take_zero, hr]; exact fevWalkIs_nil _ _ _) $$ HL

/-- **A DEAD WALK, UNWRAPPED**: namex's death receipt at the wrapped family
is the original's -- the cursor's own unfired hops come back, the wrapped
ones (which own nothing) are dropped. -/
theorem walkDead_unwrap (γfs : FsNames) (rt s0 : Nat) (P Pmiss : Nat → Nat → IProp GF)
    (pl : List (BitVec 8)) :
    (∃ (kd d : Nat), ⌜kd < (pathElems pl).length⌝ ∗
      ((walkCur γfs rt s0 (pathElems pl) P Pmiss kd d ∗
          exHopsFrom rt γfs (walkCur γfs rt s0 (pathElems pl) P Pmiss) (walkMiss γfs rt (pathElems pl) P Pmiss) pl kd) ∨
       (walkMiss γfs rt (pathElems pl) P Pmiss kd d ∗
          exHopsFrom rt γfs (walkCur γfs rt s0 (pathElems pl) P Pmiss) (walkMiss γfs rt (pathElems pl) P Pmiss) pl
            (kd + 1)))) ⊢@{IProp GF}
    (∃ (kd d : Nat), ⌜kd < (pathElems pl).length⌝ ∗
      ((P kd d ∗ exHopsFrom rt γfs P Pmiss pl kd) ∨ (Pmiss kd d ∗ exHopsFrom rt γfs P Pmiss pl (kd + 1)))) := by
  iintro ⟨%kd, %d, %hk, (⟨Hc, -⟩ | ⟨Hm, -⟩)⟩
  · icases (walkCur_unwrap γfs rt s0 (pathElems pl) P Pmiss kd d).1 $$ Hc with ⟨HP, -, Hh⟩
    iexists kd, d
    isplitr
    · ipureintro; exact hk
    ileft
    rw [exHops_is_axHops]
    iframe HP Hh
  · icases (walkMiss_unwrap γfs rt (pathElems pl) P Pmiss kd d).1 $$ Hm with ⟨HP, Hh⟩
    iexists kd, d
    isplitr
    · ipureintro; exact hk
    iright
    rw [exHops_is_axHops]
    iframe HP Hh

/-- **THE TYPE TEST, OBSERVED** (`FsAbsOpenFire.opfOpen_fire_1`'s twin): the
terminal observation commit fired as there, and the caller's `look act i po`
appended past the bound `L` at the record it holds. -/
theorem walkLook_fire_1 [Icfg] (γfs : FsNames) (E : CoPset)
    (Fo : Pfam GF (Aview → Nat → Anode → IProp GF)) (i : Nat) (n : FsNode)
    (hE : (↑ftopN : CoPset) ∪ ↑appN ⊆ E) (hnz : fnType n ≠ 0) (act : BitVec 64) (po : Option Nat)
    (L : List Fev) :
    ⊢@{IProp GF} ftopInv (hlc := hlc) γfs -∗ fsLedLb γfs L -∗
      pfAt (aopenCommitAt (hlc := hlc) (fsGammaL γfs) appE) Fo -∗
      topFrag (fsGammaL γfs) i n ={E}=∗
        topFrag (fsGammaL γfs) i n ∗
        (∃ h : List Fev, ⌜L <+: h ∧ fevRows h i = ftopRow n⌝ ∗ fsLedLb γfs (h ++ [.look act i po])) ∗
        ∃ av : Aview, ⌜arowAt av i (absRow n)⌝ ∗ Fo.pfRecv av i (absRow n) := by
  iintro #Hi #HL Hcm Hf
  rw [topFrag_1]
  imod ftopObsAfterAt γfs E (ftopN_sub_app E hE) (.look act i po) trivial L (DFrac.own 1) i n $$ Hi HL Hf
    with ⟨Hf, Hr⟩
  rw [← topFrag_1]
  imod opfOpen_fire_1 γfs E Fo i n hE hnz $$ Hi Hcm Hf with ⟨Hf, Hob⟩
  imodintro
  iframe Hf Hr Hob

end WalkLed

end Xv6
