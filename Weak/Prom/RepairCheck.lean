/-
Weak/Prom: **post-rebase repair axiom audit** ([rebase-repair], 2026-11-04): `#print axioms` of every G4 verdict of
track (a) (OwnA*.lean) and track (b) (Own*.lean) after the rebase onto MachFix (MachFix-R-b5 absorbed invalidate
view; MachFix-havoc).  Expected for each: `[propext, Classical.choice, Quot.sound]` (or a subset).
-/
import Weak.Prom.OwnAMP
import Weak.Prom.OwnAMP2
import Weak.Prom.OwnALock
import Weak.Prom.OwnALock1b
import Weak.Prom.OwnALock1c
import Weak.Prom.OwnAHold
import Weak.Prom.OwnAPipe
import Weak.Prom.OwnANeg
import Weak.Prom.OwnMPL
import Weak.Prom.OwnMP2
import Weak.Prom.OwnLock
import Weak.Prom.OwnLock1b
import Weak.Prom.OwnLock1c
import Weak.Prom.OwnLock4

-- track (a)
#print axioms Weak.Prom.OA.own_mp
#print axioms Weak.Prom.OA.own_mp2
#print axioms Weak.Prom.OA.own_lock1a
#print axioms Weak.Prom.OA.own_lock1b
#print axioms Weak.Prom.OA.C.own_lock1c
#print axioms Weak.Prom.OA.H.own_hold
#print axioms Weak.Prom.OA.P.own_pipe
#print axioms Weak.Prom.OA.slot_two_readers
-- track (b)
#print axioms Weak.Prom.Own.MPL.g4_mpOwnL
#print axioms Weak.Prom.Own.MP2.g4_mp2
#print axioms Weak.Prom.Own.Lk.g4_lock
#print axioms Weak.Prom.Own.Pre.Lk1b.g4_lock1b
#print axioms Weak.Prom.Own.X.L1c.g4_lock1c
#print axioms Weak.Prom.Own.L4.g4_lockBirth
#print axioms Weak.Prom.Own.MPL.g4_noDoubleClaimL
