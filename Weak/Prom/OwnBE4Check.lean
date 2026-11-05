/-
Weak/Prom: **E-b4 — the statement check** (stage E-b4): `own_be4` (track (b)) has EXACTLY the type of
`own_e4` (track (a), OwnAE4.lean, imported only for this comparison); axioms of `own_be4`.
-/
import Weak.Prom.OwnBE4
import Weak.Prom.OwnAE4

example : type_of% Weak.Prom.OB.E4.own_be4 = type_of% Weak.Prom.OA.E4.own_e4 := rfl

#print axioms Weak.Prom.OB.E4.own_be4
