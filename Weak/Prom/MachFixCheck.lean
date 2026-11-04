/-
Weak/Prom: **MachFix axiom audit** (2026-11-04): `#print axioms` of the re-proved machine lemmas, checkers, the
logic's adequacy theorems (A0, A0 under havoc, track (a)/(b) adequacy, NF_R) and a sample of the litmus / G4
theorems after FIX MachFix-R-b5 (absorbed invalidate view) and FIX MachFix-havoc (Sail `.error` = havoc).
Expected for each: `[propext, Classical.choice, Quot.sound]` (or a subset).
-/
import Weak.Prom.CoreHavoc
import Weak.Prom.EmitHavoc
import Weak.Prom.MachForbid
import Weak.Prom.MachComplete
import Weak.Prom.MachSound
import Weak.Prom.NfrRun
import Weak.Prom.OwnWp
import Weak.Prom.OwnLock
import Weak.Prom.OwnMPL
import Weak.Prom.OwnMP2
import Weak.Prom.OwnALock
import Weak.Prom.OwnALock1b
import Weak.Prom.OwnAMP
import Weak.Prom.CoreLit
import Weak.Prom.CoreLitA
import Weak.Prom.CmpMain

#print axioms Weak.Prom.memStep_bnd
#print axioms Weak.Prom.memStep_extend
#print axioms Weak.Prom.Mach.explorerStep_sound
#print axioms Weak.Prom.Mach.memStepF_sound
#print axioms Weak.Prom.Mach.memStepL_sound
#print axioms Weak.Prom.Mach.memStepL_complete
#print axioms Weak.Prom.Mach.soloDFS_complete
#print axioms Weak.Prom.Mach.forbidChainB_sound
#print axioms Weak.Prom.Nfr.memStep_restrict
#print axioms Weak.Prom.Nfr.nfR
#print axioms Weak.Prom.Own.ownAdequacy
#print axioms Weak.Prom.Own.lit_noInval
#print axioms Weak.Prom.PF.adequacy
#print axioms Weak.Prom.PF.adequacyH
#print axioms Weak.Prom.PF.noHavoc_of_adequacyH
#print axioms Weak.Prom.forbiddenH_iff
#print axioms Weak.Prom.havocRun_of_prefix
#print axioms Weak.Prom.sailErr_stable
#print axioms Weak.Prom.OA.adequacyA
#print axioms Weak.Prom.OA.x_noInvalT
#print axioms Weak.Prom.OA.own_lock1a
#print axioms Weak.Prom.OA.own_lock1b
#print axioms Weak.Prom.OA.own_mp
#print axioms Weak.Prom.Own.Lk.g4_lock
#print axioms Weak.Prom.Own.MPL.g4_mpOwnL
#print axioms Weak.Prom.Own.MP2.g4_mp2
#print axioms Weak.Prom.PF.lit_lbdd
#print axioms Weak.Prom.PF.lit_mpAmoRlAq
