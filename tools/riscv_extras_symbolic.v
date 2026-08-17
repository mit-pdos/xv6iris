
(* Appended by tools/regen_sail_model.sh: the model is generated with
   -D SYMBOLIC, whose Isla-only extern [mark_register] has no Coq builtin.
   Register marking is a no-op here (it only annotates Isla traces). *)
Definition mark_register {register : Type} {type_of_register : register -> Type} {a : Type}
  (_ : @register_ref register type_of_register a) (_ : string) : unit := tt.
