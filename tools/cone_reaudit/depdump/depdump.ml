open Names
open Declarations

(* ---- module-implementation lookup (copied from vernac/assumptions.ml):
   a constant of a module sealed by an interface (M : T) has no body in
   Global; look in the implementation instead. ---- *)
let modcache = ref (MPmap.empty : structure_body MPmap.t)

let rec search_mod_label lab = function
  | [] -> raise Not_found
  | (l, SFBmodule mb) :: _ when Label.equal l lab -> mb
  | _ :: fields -> search_mod_label lab fields

let rec search_cst_label lab = function
  | [] -> raise Not_found
  | (l, SFBconst cb) :: _ when Label.equal l lab -> cb
  | _ :: fields -> search_cst_label lab fields

let rec search_mind_label lab = function
  | [] -> raise Not_found
  | (l, SFBmind mind) :: _ when Label.equal l lab -> mind
  | _ :: fields -> search_mind_label lab fields

let rec fields_of_functor f subs mp0 args = function
  | NoFunctor a -> f subs mp0 args a
  | MoreFunctor (mbid,_,e) ->
    let open Mod_subst in
    match args with
    | [] -> assert false
    | mpa :: args ->
      let subs = join (map_mbid mbid mpa empty_delta_resolver) subs in
      fields_of_functor f subs mp0 args e

let rec lookup_module_in_impl mp =
    match mp with
    | MPfile _ -> Global.lookup_module mp
    | MPbound _ -> Global.lookup_module mp
    | MPdot (mp',lab') ->
       if ModPath.equal mp' (Global.current_modpath ()) then
         Global.lookup_module mp
       else
         let fields = memoize_fields_of_mp mp' in
         search_mod_label lab' fields

and memoize_fields_of_mp mp =
  try MPmap.find mp !modcache
  with Not_found ->
    let l = fields_of_mp mp in
    modcache := MPmap.add mp l !modcache;
    l

and fields_of_mp mp =
  let open Mod_subst in
  let mb = lookup_module_in_impl mp in
  let fields,inner_mp,subs = fields_of_mb empty_subst mb [] in
  let subs =
    if ModPath.equal inner_mp mp then subs
    else add_mp inner_mp mp mb.mod_delta subs
  in
  Modops.subst_structure subs fields

and fields_of_mb subs mb args = match Declareops.mod_expr mb with
  | Algebraic expr -> fields_of_expression subs mb.mod_mp args mb.mod_type expr
  | Struct sign ->
    let sign = Modops.annotate_struct_body sign mb.mod_type in
    fields_of_signature subs mb.mod_mp args sign
  | Abstract|FullStruct -> fields_of_signature subs mb.mod_mp args mb.mod_type

and fields_of_signature x =
  fields_of_functor
    (fun subs mp0 args struc ->
      assert (args = []);
      (struc, mp0, subs)) x

and fields_of_expr subs mp0 args = function
  | MEident mp ->
    let mb = lookup_module_in_impl (Mod_subst.subst_mp subs mp) in
    fields_of_mb subs mb args
  | MEapply (me1,mp2) -> fields_of_expr subs mp0 (mp2::args) me1
  | MEwith _ -> assert false

and fields_of_expression subs mp args mty me =
  let me = Modops.annotate_module_expression me mty in
  fields_of_functor fields_of_expr subs mp args me

let lookup_constant_in_impl cst fallback =
  try
    let mp,lab = KerName.repr (Constant.canonical cst) in
    let fields = memoize_fields_of_mp mp in
    search_cst_label lab fields
  with Not_found | Assert_failure _ ->
    match fallback with
      | Some cb -> cb
      | None -> raise Not_found

let lookup_constant cst =
  let env = Global.env() in
  if not (Environ.mem_constant cst env)
  then lookup_constant_in_impl cst None
  else
    let cb = Environ.lookup_constant cst env in
    if Declareops.constant_has_body cb then cb
    else lookup_constant_in_impl cst (Some cb)

let lookup_mind mind =
  let env = Global.env() in
  if Environ.mem_mind mind env then Environ.lookup_mind mind env
  else
    let mp,lab = KerName.repr (MutInd.canonical mind) in
    let fields = memoize_fields_of_mp mp in
    search_mind_label lab fields

(* ---- bounded top-of-term hash (as assumptions.ml) ---- *)
let rec hash_top n c =
  let open Hashset.Combine in
  let sub c = if n <= 1 then 0 else hash_top (n - 1) c in
  match Constr.kind c with
  | Constr.Const (kn, _) -> combinesmall 1 (Constant.UserOrd.hash kn)
  | Constr.Ind ((mi, i), _) -> combinesmall 2 (combine (MutInd.UserOrd.hash mi) i)
  | Constr.Construct (((mi, i), j), _) ->
    combinesmall 3 (combine3 (MutInd.UserOrd.hash mi) i j)
  | Constr.Var id -> combinesmall 4 (Id.hash id)
  | Constr.Rel i -> combinesmall 5 i
  | Constr.App (f, args) ->
    let k = Array.length args in
    combinesmall 6
      (combine3 (sub f) k (if Int.equal k 0 then 0 else sub args.(k - 1)))
  | Constr.Lambda (_, t, b) -> combinesmall 7 (combine (sub t) (sub b))
  | Constr.Prod (_, t, b) -> combinesmall 8 (combine (sub t) (sub b))
  | Constr.LetIn (_, b, t, c) -> combinesmall 9 (combine3 (sub b) (sub t) (sub c))
  | Constr.Proj (p, _, c) ->
    combinesmall 10 (combine (Projection.CanOrd.hash p) (sub c))
  | Constr.Case (ci, _, _, _, _, c, br) ->
    combinesmall 11 (combine3 (Ind.UserOrd.hash ci.Constr.ci_ind)
                       (Array.length br) (sub c))
  | Constr.Cast (c, _, _) -> combinesmall 12 (sub c)
  | Constr.Fix (_, (_, tl, _)) -> combinesmall 13 (Array.length tl)
  | Constr.CoFix (_, (_, tl, _)) -> combinesmall 14 (Array.length tl)
  | Constr.Array (_, t, _, _) -> combinesmall 15 (Array.length t)
  | Constr.Int i -> combinesmall 16 (Uint63.hash i)
  | Constr.Float _ -> 17
  | Constr.String _ -> 18
  | Constr.Sort _ -> 19
  | Constr.Meta i -> combinesmall 20 i
  | Constr.Evar _ -> 21

let cache_bits = 20
let cache_size = 1 lsl cache_bits
let cache_key = Array.make cache_size Constr.mkProp
let cache_gen = Array.make cache_size (-1)
let gen_count = ref 0

let seen gen c =
  let i = hash_top 4 c land (cache_size - 1) in
  if Int.equal (Array.unsafe_get cache_gen i) gen && Array.unsafe_get cache_key i == c
  then true
  else begin
    Array.unsafe_set cache_gen i gen;
    Array.unsafe_set cache_key i c;
    false
  end

let refs_of (acc : (string, unit) Hashtbl.t) (out : GlobRef.t list ref) (c : Constr.t) =
  incr gen_count;
  let gen = !gen_count in
  let add r =
    let k = match r with
      | GlobRef.ConstRef kn -> "C" ^ Constant.to_string kn
      | GlobRef.IndRef (mi, _) -> "I" ^ MutInd.to_string mi
      | GlobRef.ConstructRef ((mi, _), _) -> "I" ^ MutInd.to_string mi
      | GlobRef.VarRef id -> "V" ^ Id.to_string id in
    if not (Hashtbl.mem acc k) then begin Hashtbl.add acc k (); out := r :: !out end in
  let rec go c =
    match Constr.kind c with
    | Constr.Rel _ | Constr.Meta _ | Constr.Sort _ | Constr.Int _ | Constr.Float _
    | Constr.String _ -> ()
    | Constr.Var id -> add (GlobRef.VarRef id)
    | Constr.Const (kn, _) -> add (GlobRef.ConstRef kn)
    | Constr.Ind ((mi, _), _) -> add (GlobRef.IndRef (mi, 0))
    | Constr.Construct (((mi, _), _), _) -> add (GlobRef.IndRef (mi, 0))
    | _ ->
      if seen gen c then () else begin
        (match Constr.kind c with
         | Constr.Proj (p, _, _) ->
           add (GlobRef.ConstRef (Projection.constant p));
           add (GlobRef.IndRef (fst (Projection.inductive p), 0))
         | Constr.Case (ci, _, _, _, _, _, _) -> add (GlobRef.IndRef (fst ci.Constr.ci_ind, 0))
         | _ -> ());
        Constr.iter go c
      end in
  go c

let key_of r = match r with
  | GlobRef.ConstRef kn -> Constant.to_string kn
  | GlobRef.IndRef (mi, _) | GlobRef.ConstructRef ((mi, _), _) -> MutInd.to_string mi
  | GlobRef.VarRef id -> "VAR:" ^ Id.to_string id

let expandable name =
  let pre p = String.length name >= String.length p && String.sub name 0 (String.length p) = p in
  List.exists pre ["xv6iris."; "Kernel."; "User."]

let deps_of r =
  let acc = Hashtbl.create 64 and out = ref [] in
  let kind =
    match r with
    | GlobRef.ConstRef kn ->
      let cb = lookup_constant kn in
      refs_of acc out cb.const_type;
      (match cb.const_body with
       | Def c -> refs_of acc out c; "def"
       | OpaqueDef o ->
         (match Global.force_proof Library.indirect_accessor o with
          | (c, _) -> refs_of acc out c; "opaque"
          | exception _ -> "opaque-nobody")
       | Undef _ -> "axiom"
       | _ -> "prim")
    | GlobRef.IndRef (mi, _) | GlobRef.ConstructRef ((mi, _), _) ->
      let mib = lookup_mind mi in
      let ctx l = List.iter (fun d ->
          refs_of acc out (Context.Rel.Declaration.get_type d);
          Option.iter (refs_of acc out) (Context.Rel.Declaration.get_value d)) l in
      ctx mib.mind_params_ctxt;
      Array.iter (fun oib ->
          ctx oib.mind_arity_ctxt;
          Array.iter (refs_of acc out) oib.mind_user_lc) mib.mind_packets;
      "ind"
    | GlobRef.VarRef _ -> "var" in
  kind, List.rev !out

let run () =
  match Sys.getenv_opt "DEPDUMP_ROOTS", Sys.getenv_opt "DEPDUMP_OUT" with
  | Some roots, Some outf ->
    let oc = open_out outf in
    let seen = Hashtbl.create 100000 in
    let q = Queue.create () in
    List.iter (fun s ->
        let r = Nametab.global (Libnames.qualid_of_string s) in
        let k = key_of r in
        Printf.fprintf oc "R %s\n" k;
        if not (Hashtbl.mem seen k) then (Hashtbl.add seen k (); Queue.add r q))
      (String.split_on_char ',' roots);
    while not (Queue.is_empty q) do
      let r = Queue.pop q in
      let k = key_of r in
      if expandable k then begin
        let kind, ds = (try deps_of r with e -> ("err:" ^ String.escaped (Printexc.to_string e), [])) in
        Printf.fprintf oc "N %s %s\n" k kind;
        List.iter (fun d ->
            let dk = key_of d in
            Printf.fprintf oc "E %s %s\n" k dk;
            if not (Hashtbl.mem seen dk) then (Hashtbl.add seen dk (); Queue.add d q)) ds;
        flush oc
      end else Printf.fprintf oc "X %s\n" k
    done;
    close_out oc
  | _ -> prerr_endline "depdump: set DEPDUMP_ROOTS and DEPDUMP_OUT"

let _ = Mltop.add_known_module "depdump"

let () = Vernacextend.static_vernac_extend ~plugin:(Some "depdump") ~command:"DepDump"
    ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None
    [(Vernacextend.TyML
        (false,
         Vernacextend.TyTerminal ("DepDump", Vernacextend.TyNil),
         (let body () = Vernactypes.vtdefault (fun () -> run ()) in
          fun ?loc ~atts () -> body (Attributes.unsupported_attributes atts)),
         None))]
