/-
Weak/Mini: axiom check of the P2-C deliverables (MiniLogic `mini_adequacy`, the leaf rules, the machine-level
example lemmas).  Expected: `[propext, Classical.choice, Quot.sound]` or fewer.
-/
import Weak.Mini.LitLoop

#print axioms Weak.Mini.Logic.mini_adequacy
#print axioms Weak.Mini.Logic.wp_alui
#print axioms Weak.Mini.Logic.wp_alu
#print axioms Weak.Mini.Logic.wp_load
#print axioms Weak.Mini.Logic.wp_store
#print axioms Weak.Mini.Logic.wp_fence
#print axioms Weak.Mini.Logic.wp_br
#print axioms Weak.Mini.Logic.wp_jmp
#print axioms Weak.Mini.Logic.wp_nop
#print axioms Weak.Mini.Logic.wp_done
#print axioms Weak.Mini.Logic.mini_lit_lbdd
#print axioms Weak.Mini.Logic.mini_lit_mpFF
#print axioms Weak.Mini.Logic.mini_lit_mpLoop
