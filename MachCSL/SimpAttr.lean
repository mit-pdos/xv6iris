/-
The `sail_facts` simp set: closed facts about the generated model's
configuration (which extensions the hart supports, platform constants, ...)
used by `sail_norm` to decide the conditions the model tests.
-/
import Lean
register_simp_attr sail_facts
