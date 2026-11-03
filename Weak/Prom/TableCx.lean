/-
Weak/Prom: **Table C of machine v2, EXTRACTED FROM THE LEAN DECLARATIONS** (S0 exit, (E1); plan rev 7 §1A
"Instrument 1: Table C (code side), generated from the code").

A meta-program (`Lean.Meta`, run at elaboration time) that reads the actual declarations of machine v2
(`Weak/Prom/Machine.lean`), emission v2 (`Weak/Prom/Emit.lean`), the Sail interface types and the Sail model, and
produces Table C's ROW IDs, family by family:

* **C-F** — the fields of `PState`, `PResv`, `PRmw`, `PMsg`, `PAgent`, `PCfg` and the constructors of `PClass`,
  `CmoKind` (`getStructureFields`, the inductive's constructor list).  Each field row carries its WRITER and READER
  arms, computed from the C-A analysis below (the def-use pairs of G1b).
* **C-L** — the constructors of the label type `PLabel`, each with the `memStep` arm(s) whose conclusion has it.
* **C-A** — the constructors of `memStep` (and of `pmStep`); per constructor ONE ROW PER PREMISE (each hypothesis
  of the constructor's type, top-level `∧` split) with the state fields it reads, ONE ROW PER POST-STATE FIELD it
  writes, one `.u` row listing the untouched fields, the promise-set and fulfil-timestamp rows.  "Reads" and
  "writes" are computed after UNFOLDING every definition of `Weak.Prom.Machine` the term uses, down to field
  projections (the plan's "Unfolding depth" [R4.s4]); a recursive definition is summarised from its equation lemmas
  by a fixpoint (`loadBytes` writes `wCoh wVrOld wVrNew wVwNew wLdv`, …).  "Writes f" = the post-state's field `f`
  is not syntactically the pre-state's `f` after unfolding (a structure update copies a field as a projection).
* **C-A branch rows** (`C-A.br.*`) — every `if` condition and every non-iteration `match` inside the unfolded
  Machine definitions (the guards G3 must take both ways; `ProbeCov.lean` logs them).
* **C-E** — every arm of every `match` in emission v2's definitions reachable from `pstepV2` (`hnodeStep`'s `match
  h.m` and `match o, k`: one arm per `Outcome` constructor, read off the matcher's type), every `if` condition and
  every `∨` disjunct of a Prop-valued definition (`bndStep`, `ramRead`, `ramWrite`, …).
* **C-K** — the 14 values of the access-kind type (`Access_kind RISCV_strong_access` over `Explicit_access_kind`,
  `RISCV_strong_access`'s varieties), each with emission v2's classification (`akIfetch`, `akExcl`, `akAcq`,
  `akRel`, `akStrong`, `isTtw`, computed by `whnf`).
* **C-D** — the constructors of Sail's `instruction` (`Defs.lean`), each with the decoder-check classes
  (`DecoderTable.lean`/`DecoderObs.lean`, evaluated) whose Sail decode is that constructor.
* **C-R** — the constructors of Sail's `Register` that emission v2 tracks (`eregNum r ≠ none`, by `whnf`) and
  `nextPC`, each with the number of `writeReg` sites of that register in the generated model (scanned).
* **C-S** — every constructor of Sail's `Register`, classified by the table (architectural / model-internal).

`#tableCx` prints every row; `tableCx_check` (in `TableCv2.lean`) compares the row IDs with the marked table and
FAILS THE BUILD on a missing or extra row.  Nothing here is used by a theorem.
-/
import Weak.Prom.DecoderCheck
import Lean

namespace Weak.Prom.TC

open Lean Meta Elab Command

/-- An extracted row: ID and description. -/
structure XRow where
  id : String
  desc : String
  deriving Inhabited, Repr

/-! ## 1. Utilities -/

def lastS (n : Name) : String :=
  match n with
  | .str _ s => s
  | .num _ k => toString k
  | .anonymous => ""

def nm (n : Name) : String := lastS n

def ppS (e : Expr) : MetaM String := do
  let s := toString (← ppExpr e)
  let s := s.replace "\n" " "
  let s := (s.splitOn "  ").foldl (fun a b => if b.isEmpty then a else if a.isEmpty then b else a ++ " " ++ b.trimLeft) ""
  return if s.length > 160 then (s.take 157).toString ++ "..." else s

/-- Is constant `c` declared in module `m`? -/
def inModule (m c : Name) : MetaM Bool := do
  let env ← getEnv
  match env.getModuleIdx? m, env.getModuleIdxFor? c with
  | some a, some b => return a == b
  | _, _ => return false

/-- Does the definition's value use structural / well-founded recursion? -/
def isRecDef (c : Name) : MetaM Bool := do
  match (← getEnv).find? c with
  | some (.defnInfo d) =>
    return d.value.find? (fun e => match e with
      | .const n _ => lastS n == "brecOn" || n == ``WellFounded.fix || n == c ++ `_unary
      | _ => false) |>.isSome
  | _ => return false

/-- A non-recursive, non-matcher definition of module `m` (to unfold). -/
def unfoldable (m c : Name) : MetaM Bool := do
  if !(← inModule m c) then return false
  if (← getMatcherInfo? c).isSome then return false
  match (← getEnv).find? c with
  | some (.defnInfo _) => return !(← isRecDef c)
  | _ => return false

def recursive (m c : Name) : MetaM Bool := do
  if !(← inModule m c) then return false
  if (← getMatcherInfo? c).isSome then return false
  isRecDef c

/-- Unfold one application of a definition. -/
def unfold1 (e : Expr) : MetaM Expr := do
  let fn := e.getAppFn
  let .const c us := fn | return e
  let some ci := (← getEnv).find? c | return e
  let v ← instantiateValueLevelParams ci us
  return v.beta e.getAppArgs

/-! ## 2. The written-field analysis (relative to a base state) -/

/-- A structure: name, constructor, field names. -/
structure SInfo where
  sname : Name
  ctor : Name
  fields : Array Name

def sinfo (s : Name) : MetaM SInfo := do
  let env ← getEnv
  let fs := getStructureFields env s
  let some si := getStructureInfo? env s | throwError "no structure {s}"
  let _ := si
  let ind ← getConstInfoInduct s
  return ⟨s, ind.ctors.head!, fs⟩

/-- If `e` is the projection of field `j` of structure `S` applied to `x`, return `x`. -/
def projOf? (S : SInfo) (j : Nat) (e : Expr) : MetaM (Option Expr) := do
  match e with
  | .proj s k x => return if s == S.sname && k == j then some x else none
  | .mdata _ b => projOf? S j b
  | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .const c _ =>
      if c == S.sname ++ S.fields[j]! && args.size ≥ 1 then return some args.back! else return none
    | _ => return none

/-- Summaries of recursive definitions: per (definition, structure) the written fields relative to the argument at
`idx`. -/
abbrev SumMap := Std.HashMap (Name × Name) (Nat × Array Bool)

/-- The index of the first explicit argument of `c` whose type is the structure. -/
def stateArgIdx (S : SInfo) (c : Name) : MetaM (Option Nat) := do
  let ci ← getConstInfo c
  forallTelescope ci.type fun xs _ => do
    for k in [0:xs.size] do
      let t ← inferType xs[k]!
      if t.getAppFn.isConstOf S.sname then return some k
    return none

def orB (a b : Array Bool) : Array Bool := (a.zip b).map (fun (x, y) => x || y)

mutual

/-- Fields of `S` in which `e` may differ from `base` (module `m`'s definitions unfolded). -/
partial def wr (m : Name) (S : SInfo) (sums : IO.Ref SumMap) (base : Expr) (e : Expr) : MetaM (Array Bool) := do
  let top := S.fields.map (fun _ => true)
  let none' := S.fields.map (fun _ => false)
  let e := e.headBeta
  match e with
  | .mdata _ b => wr m S sums base b
  | .letE _ _ v b _ => wr m S sums base (b.instantiate1 v)
  | .fvar _ => return if e == base then none' else top
  | _ =>
  let fn := e.getAppFn
  let args := e.getAppArgs
  let .const c _ := fn | return top
  if c == S.ctor && args.size == S.fields.size + (args.size - S.fields.size) then
    let off := args.size - S.fields.size
    let mut out := none'
    for j in [0:S.fields.size] do
      match ← projOf? S j args[off + j]! with
      | some x => if (← wr m S sums base x)[j]! then out := out.set! j true
      | none => out := out.set! j true
    return out
  if c == ``ite && args.size == 5 then
    return orB (← wr m S sums base args[3]!) (← wr m S sums base args[4]!)
  if c == ``dite && args.size == 5 then
    let a ← lambdaTelescope args[3]! fun _ b => wr m S sums base b
    let b ← lambdaTelescope args[4]! fun _ b => wr m S sums base b
    return orB a b
  if let some mi ← getMatcherInfo? c then
    let nAlts := mi.altNumParams.size
    let first := mi.numParams + 1 + mi.numDiscrs
    if args.size < first + nAlts then return top
    let extra := args.extract (first + nAlts) args.size
    let mut out := none'
    for k in [0:nAlts] do
      let alt := args[first + k]!
      let w ← lambdaBoundedTelescope alt (max mi.altNumParams[k]! 1) fun _ b =>
        wr m S sums base (mkAppN b extra).headBeta
      out := orB out w
    return out
  if ← unfoldable m c then
    return ← wr m S sums base (← unfold1 e)
  if ← recursive m c then
    match ← stateArgIdx S c with
    | none => return top
    | some idx =>
      if args.size ≤ idx then return top
      let s ← summary m S sums c idx
      return orB s (← wr m S sums base args[idx]!)
  return top

/-- The fixpoint summary of a recursive definition `c` (its equation lemmas). -/
partial def summary (m : Name) (S : SInfo) (sums : IO.Ref SumMap) (c : Name) (idx : Nat) : MetaM (Array Bool) := do
  if let some (_, s) := (← sums.get)[(c, S.sname)]? then return s
  let none' := S.fields.map (fun _ => false)
  sums.modify (·.insert (c, S.sname) (idx, none'))
  let some eqns ← getEqnsFor? c | return S.fields.map (fun _ => true)
  let mut cur := none'
  for _ in [0:8] do
    let mut acc := none'
    for eq in eqns do
      let ci ← getConstInfo eq
      let w ← forallTelescope ci.type fun _ body => do
        let some (_, lhs, rhs) := body.eq? | return S.fields.map (fun _ => true)
        let la := lhs.getAppArgs
        if la.size ≤ idx then return S.fields.map (fun _ => true)
        wr m S sums la[idx]! rhs
      acc := orB acc w
    if acc == cur then break
    cur := acc
    sums.modify (·.insert (c, S.sname) (idx, cur))
  return cur

end

/-! ## 3. The read analysis (projections of the tracked structures) -/

/-- Per structure, its projection-function names. -/
def projNames (Ss : List SInfo) : List Name := Ss.flatMap (fun S => S.fields.toList.map (S.sname ++ ·))

mutual

partial def rdE (m : Name) (Ss : List SInfo) (rsum : IO.Ref (Std.HashMap Name (Array Name)))
    (acc : IO.Ref (Array Name)) (e : Expr) : MetaM Unit := do
  match e with
  | .mdata _ b => rdE m Ss rsum acc b
  | .letE _ t v b _ => rdE m Ss rsum acc t; rdE m Ss rsum acc v; rdE m Ss rsum acc b
  | .lam _ _ b _ => rdE m Ss rsum acc b
  | .forallE _ t b _ => rdE m Ss rsum acc t; rdE m Ss rsum acc b
  | .proj s j x =>
    if let some S := Ss.find? (·.sname == s) then
      acc.modify (fun a => if a.contains (s ++ S.fields[j]!) then a else a.push (s ++ S.fields[j]!))
    rdE m Ss rsum acc x
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .const c _ =>
      -- a structure update copies fields as projections: not a read
      if let some S := Ss.find? (·.ctor == c) then
        let off := args.size - S.fields.size
        for k in [0:args.size] do
          if k ≥ off then
            if (← projOf? S (k - off) args[k]!).isSome then
              match args[k]!.getAppArgs.back? with
              | some x => rdE m Ss rsum acc x
              | none => pure ()
              continue
          rdE m Ss rsum acc args[k]!
        return
      if (projNames Ss).contains c then
        acc.modify (fun a => if a.contains c then a else a.push c)
        for a in args do rdE m Ss rsum acc a
        return
      if ← unfoldable m c then
        rdE m Ss rsum acc (← unfold1 e)
        return
      if ← recursive m c then
        for n in ← rdSummary m Ss rsum c do
          acc.modify (fun a => if a.contains n then a else a.push n)
      for a in args do rdE m Ss rsum acc a
    | _ =>
      rdE m Ss rsum acc fn
      for a in args do rdE m Ss rsum acc a
  | .const c _ =>
    if (projNames Ss).contains c then acc.modify (fun a => if a.contains c then a else a.push c)
  | _ => pure ()

partial def rdSummary (m : Name) (Ss : List SInfo) (rsum : IO.Ref (Std.HashMap Name (Array Name))) (c : Name) :
    MetaM (Array Name) := do
  if let some s := (← rsum.get)[c]? then return s
  rsum.modify (·.insert c #[])
  let some eqns ← getEqnsFor? c | return #[]
  let acc ← IO.mkRef (#[] : Array Name)
  for eq in eqns do
    let ci ← getConstInfo eq
    forallTelescope ci.type fun _ body => do
      if let some (_, _, rhs) := body.eq? then rdE m Ss rsum acc rhs
  let r ← acc.get
  rsum.modify (·.insert c r)
  return r

end

def reads (m : Name) (Ss : List SInfo) (rsum : IO.Ref (Std.HashMap Name (Array Name))) (e : Expr) :
    MetaM (Array Name) := do
  let acc ← IO.mkRef #[]
  rdE m Ss rsum acc e
  return (← acc.get)

def fieldStr (ns : Array Name) : String :=
  String.intercalate " " (ns.toList.map (fun n => s!"{nm n.getPrefix}.{nm n}"))

/-! ## 4. Branch rows (if / match / or) inside a module's definitions -/

/-- The constructor-name skeleton of a pattern (parameters of the constructor skipped). -/
partial def patName (p : Expr) : MetaM String := do
  let fn := p.getAppFn
  if fn.isConstOf ``OfNat.ofNat && p.getAppArgs.size ≥ 2 then
    match p.getAppArgs[1]! with
    | .lit (.natVal n) => return toString n
    | _ => pure ()
  if fn.isConstOf ``Int.negSucc && p.getAppArgs.size ≥ 1 then
    return s!"-({← patName p.getAppArgs[0]!})+1"
  match p with
  | .lit (.natVal n) => return toString n
  | _ => pure ()
  match fn with
  | .const c _ =>
    match (← getEnv).find? c with
    | some (.ctorInfo ci) =>
      let args := p.getAppArgs.extract ci.numParams p.getAppArgs.size
      let inner ← args.toList.filterMapM (fun a => do
        match a.getAppFn with
        | .const c' _ =>
          match (← getEnv).find? c' with
          | some (.ctorInfo _) => return some (← patName a)
          | _ => return none
        | _ => return none)
      return if inner.isEmpty then nm c else s!"{nm c}({String.intercalate "," inner})"
    | _ => return "_"
  | .lit (.natVal n) => return toString n
  | _ => return "_"

/-- The alternatives' pattern names of a matcher. -/
def altNames (c : Name) (mi : MatcherInfo) : MetaM (Array String) := do
  let ci ← getConstInfo c
  forallTelescope ci.type fun xs _ => do
    let mut out := #[]
    for k in [0:mi.altNumParams.size] do
      let t ← inferType xs[mi.numParams + 1 + mi.numDiscrs + k]!
      let s ← forallTelescope t fun _ b => do
        let ps ← b.getAppArgs.toList.mapM patName
        return String.intercalate "," ps
      out := out.push s
    return out

/-- Flatten a disjunction. -/
partial def disjuncts (e : Expr) : List Expr :=
  match e.getAppFn, e.getAppArgs with
  | .const ``Or _, #[a, b] => disjuncts a ++ disjuncts b
  | _, _ => [e]

structure BrSt where
  rows : Array XRow := #[]
  seen : Array Name := #[]

/-- Scan definition `owner`'s value: `if` conditions, matcher arms, `∨` disjuncts; descend into the module's other
definitions (each scanned once, as its own owner).  `iterOk`: skip matchers whose discriminant is a `List`/`Nat`
(the recursion of a structural fold). -/
partial def scanBr (m : Name) (fam : String) (st : IO.Ref BrSt) (owner : String) (cnt : IO.Ref Nat) (e : Expr) :
    MetaM Unit := do
  let next : MetaM Nat := do cnt.modify (· + 1); cnt.get
  let push (id d : String) : MetaM Unit := st.modify (fun s => { s with rows := s.rows.push ⟨id, d⟩ })
  match e with
  | .mdata _ b => scanBr m fam st owner cnt b
  | .letE n t v b _ =>
    scanBr m fam st owner cnt v
    withLetDecl n t v fun x => scanBr m fam st owner cnt (b.instantiate1 x)
  | .lam n t b bi => withLocalDecl n bi t fun x => scanBr m fam st owner cnt (b.instantiate1 x)
  | .forallE n t b bi =>
    scanBr m fam st owner cnt t
    withLocalDecl n bi t fun x => scanBr m fam st owner cnt (b.instantiate1 x)
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .const c _ =>
      if (c == ``ite || c == ``dite) && args.size == 5 then
        let k ← next
        push s!"{fam}.{owner}.if{k}" s!"if {← ppS args[1]!}"
        scanBr m fam st owner cnt args[1]!
        scanBr m fam st owner cnt args[3]!
        scanBr m fam st owner cnt args[4]!
        return
      if c == ``Or && args.size == 2 then
        let ds := disjuncts e
        let k ← next
        for j in [0:ds.length] do
          push s!"{fam}.{owner}.or{k}.{j + 1}" (← ppS ds[j]!)
        for d in ds do scanBr m fam st owner cnt d
        return
      if let some mi ← getMatcherInfo? c then
        let first := mi.numParams + 1 + mi.numDiscrs
        let discrs := args.extract (mi.numParams + 1) first
        let mut iter := false
        for d in discrs do
          let t ← whnfR (← inferType d)
          if t.getAppFn.isConstOf ``List || t.isConstOf ``Nat then iter := true
        let _ := iter
        if (← inModule m c) then
          let k ← next
          let ns ← altNames c mi
          let dstr ← discrs.toList.mapM ppS
          for j in [0:ns.size] do
            let dup := (ns.toList.filter (· == ns[j]!)).length > 1
            let an := if dup then s!"{ns[j]!}#{j + 1}" else ns[j]!
            push s!"{fam}.{owner}.m{k}.{an}" s!"match {String.intercalate ", " dstr} | {ns[j]!}"
        for a in args do scanBr m fam st owner cnt a
        return
      if (← unfoldable m c) then
        if !(← st.get).seen.contains c then
          st.modify (fun s => { s with seen := s.seen.push c })
          let ci ← getConstInfo c
          let c2 ← IO.mkRef 0
          scanBr m fam st (nm c) c2 (ci.value!)
      if (← recursive m c) then
        if !(← st.get).seen.contains c then
          st.modify (fun s => { s with seen := s.seen.push c })
          if let some eqns ← getEqnsFor? c then
            let c2 ← IO.mkRef 0
            for eq in eqns do
              let ci ← getConstInfo eq
              forallTelescope ci.type fun _ body => do
                if let some (_, _, rhs) := body.eq? then scanBr m fam st (nm c) c2 rhs
      for a in args do scanBr m fam st owner cnt a
    | _ =>
      scanBr m fam st owner cnt fn
      for a in args do scanBr m fam st owner cnt a
  | _ => pure ()

/-! ## 5. The families -/

def machM : Name := `Weak.Prom.Machine
def emitM : Name := `Weak.Prom.Emit

/-- The machine structures whose fields are tracked. -/
def machStructs : List Name :=
  [``Weak.Prom.PState, ``Weak.Prom.PResv, ``Weak.Prom.PRmw, ``Weak.Prom.PMsg]

structure CA where
  rows : Array XRow := #[]
  /-- per tracked projection: writer arms / reader arms -/
  writers : Std.HashMap Name (Array String) := {}
  readers : Std.HashMap Name (Array String) := {}

def addTo (mp : Std.HashMap Name (Array String)) (k : Name) (v : String) : Std.HashMap Name (Array String) :=
  let a := mp.getD k #[]
  mp.insert k (if a.contains v then a else a.push v)

def pushRow (ca : IO.Ref CA) (id d : String) : MetaM Unit :=
  ca.modify (fun s => { s with rows := s.rows.push ⟨id, d⟩ })

/-- Split top-level conjunctions. -/
partial def conjuncts (e : Expr) : List Expr :=
  match e.getAppFn, e.getAppArgs with
  | .const ``And _, #[a, b] => conjuncts a ++ conjuncts b
  | _, _ => [e]

/-- C-A for `memStep`: premise rows, post-state rows, untouched-field row, promise/fulfil rows. -/
def extractMemStep (ca : IO.Ref CA) : MetaM Unit := do
  let PS ← sinfo ``Weak.Prom.PState
  let Ss ← machStructs.mapM sinfo
  let sums ← IO.mkRef ({} : SumMap)
  let rsum ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  let ind ← getConstInfoInduct ``Weak.Prom.memStep
  for c in ind.ctors do
    let ci ← getConstInfoCtor c
    let arm := nm c
    forallTelescope ci.type fun xs concl => do
      let cargs := concl.getAppArgs
      -- memStep img log i prom ws l ots ws' prom'
      let promPre := cargs[3]!
      let ws := cargs[4]!
      let lab := cargs[5]!
      let ots := cargs[6]!
      let post := cargs[7]!
      let promPost := cargs[8]!
      pushRow ca s!"C-L.{nm lab.getAppFn.constName!}" s!"arm memStep.{arm}"
      let mut k := 0
      for x in xs do
        let t ← inferType x
        if ← isProp t then
          k := k + 1
          let cs := conjuncts t
          for j in [0:cs.length] do
            let id := if cs.length = 1 then s!"C-A.{arm}.p{k}" else s!"C-A.{arm}.p{k}.{j + 1}"
            let mut rs ← reads machM Ss rsum cs[j]!
            -- a premise that compares a log entry with a constructed message reads every message field
            if (cs[j]!.find? (fun e => e.isConstOf ``Weak.Prom.PMsg.mk)).isSome then
              for f in getStructureFields (← getEnv) ``Weak.Prom.PMsg do
                if !rs.contains (``Weak.Prom.PMsg ++ f) then rs := rs.push (``Weak.Prom.PMsg ++ f)
            for r in rs do ca.modify (fun s => { s with readers := addTo s.readers r arm })
            pushRow ca id s!"{← ppS cs[j]!}   [reads {fieldStr rs}]"
      let w ← wr machM PS sums ws post
      let rsPost ← reads machM Ss rsum post
      for r in rsPost do ca.modify (fun s => { s with readers := addTo s.readers r arm })
      let mut untouched := #[]
      for j in [0:PS.fields.size] do
        let f := PS.fields[j]!
        if w[j]! then
          pushRow ca s!"C-A.{arm}.w.{f}" s!"post-state writes PState.{f}"
          ca.modify (fun s => { s with writers := addTo s.writers (PS.sname ++ f) arm })
        else untouched := untouched.push (toString f)
      pushRow ca s!"C-A.{arm}.u" s!"untouched: {String.intercalate " " untouched.toList}; post reads {fieldStr rsPost}"
      let promCh := !(promPost == promPre)
      pushRow ca s!"C-A.{arm}.prom" (if promCh then "promise set: the fulfilled timestamp removed" else "promise set unchanged")
      let fulfils := ots.getAppFn.isConstOf ``Option.some
      pushRow ca s!"C-A.{arm}.ots" (if fulfils then "fulfils a timestamp (write arm)" else "no fulfil")
      -- a post-state that constructs a reservation / AMO slot writes its fields
      for sn in [``Weak.Prom.PResv, ``Weak.Prom.PRmw] do
        let S ← sinfo sn
        if (post.find? (fun e => e.isConstOf S.ctor)).isSome then
          for f in S.fields do ca.modify (fun s => { s with writers := addTo s.writers (sn ++ f) arm })

/-- C-A for `pmStep` (promise / state). -/
def extractPmStep (ca : IO.Ref CA) : MetaM Unit := do
  let ind ← getConstInfoInduct ``Weak.Prom.pmStep
  let CS ← sinfo ``Weak.Prom.PCfg
  let AS ← sinfo ``Weak.Prom.PAgent
  let sums ← IO.mkRef ({} : SumMap)
  let rsum ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  for c in ind.ctors do
    let ci ← getConstInfoCtor c
    let arm := nm c
    forallTelescope ci.type fun xs concl => do
      let cargs := concl.getAppArgs
      let cfg := cargs[cargs.size - 3]!
      let post := cargs[cargs.size - 1]!
      let mut k := 0
      for x in xs do
        let t ← inferType x
        if ← isProp t then
          k := k + 1
          for j in [0:(conjuncts t).length] do
            let cs := conjuncts t
            let id := if cs.length = 1 then s!"C-A.pm.{arm}.p{k}" else s!"C-A.pm.{arm}.p{k}.{j + 1}"
            let rs ← reads machM [CS, AS] rsum cs[j]!
            for r in rs do ca.modify (fun s => { s with readers := addTo s.readers r s!"pm.{arm}" })
            pushRow ca id s!"{← ppS cs[j]!}   [reads {fieldStr rs}]"
      let w ← wr machM CS sums cfg post
      for j in [0:CS.fields.size] do
        let f := CS.fields[j]!
        if w[j]! then
          pushRow ca s!"C-A.pm.{arm}.w.{f}" s!"post-config writes PCfg.{f}"
          ca.modify (fun s => { s with writers := addTo s.writers (CS.sname ++ f) s!"pm.{arm}" })
          if toString f == "pcLog" then
            for g in getStructureFields (← getEnv) ``Weak.Prom.PMsg do
              ca.modify (fun s => { s with writers := addTo s.writers (``Weak.Prom.PMsg ++ g) s!"pm.{arm}" })
      -- the agent record the post-configuration installs, relative to the pre-state agent `ag`
      let ag? ← xs.findM? (fun x => do return (← x.fvarId!.getDecl).userName == `ag)
      if let some ag := ag? then
        if let some am := post.find? (fun e => e.getAppFn.isConstOf AS.ctor && e.getAppArgs.size == AS.fields.size + 1) then
          let wa ← wr machM AS sums ag am
          for j in [0:AS.fields.size] do
            if wa[j]! then
              let f := AS.fields[j]!
              pushRow ca s!"C-A.pm.{arm}.wag.{f}" s!"installed agent writes PAgent.{f}"
              ca.modify (fun s => { s with writers := addTo s.writers (AS.sname ++ f) s!"pm.{arm}" })

/-- C-F rows (fields and class constructors), with writers/readers from the C-A analysis. -/
def extractFields (ca : CA) : MetaM (Array XRow) := do
  let mut out := #[]
  for s in [``Weak.Prom.PState, ``Weak.Prom.PResv, ``Weak.Prom.PRmw, ``Weak.Prom.PMsg, ``Weak.Prom.PAgent,
            ``Weak.Prom.PCfg] do
    let fs := getStructureFields (← getEnv) s
    for f in fs do
      let p := s ++ f
      let ws := ca.writers.getD p #[]
      let rs := ca.readers.getD p #[]
      out := out.push ⟨s!"C-F.{nm s}.{f}",
        s!"writers [{String.intercalate " " ws.toList}] readers [{String.intercalate " " rs.toList}]"⟩
  for s in [``Weak.Prom.PClass, ``Weak.Prom.CmoKind] do
    let ind ← getConstInfoInduct s
    for c in ind.ctors do
      out := out.push ⟨s!"C-F.{nm s}.{nm c}", "message class / CMO kind constructor"⟩
  return out

/-- Every `PLabel` constructor must be the label of some arm (C-L), and only once. -/
def checkLabels (rows : Array XRow) : MetaM (Array XRow) := do
  let ind ← getConstInfoInduct ``Weak.Prom.PLabel
  let mut out := #[]
  for c in ind.ctors do
    let id := s!"C-L.{nm c}"
    let arms := rows.filter (·.id == id)
    if arms.isEmpty then out := out.push ⟨id, "NO memStep ARM"⟩
    else out := out.push ⟨id, String.intercalate ", " (arms.toList.map (·.desc))⟩
  return out

/-- C-A branch rows: `if`/`match` inside the Machine definitions the arms use. -/
def extractMachBranches : MetaM (Array XRow) := do
  let st ← IO.mkRef ({} : BrSt)
  let ind ← getConstInfoInduct ``Weak.Prom.memStep
  for c in ind.ctors do
    let ci ← getConstInfoCtor c
    let cnt ← IO.mkRef 0
    -- scan the constructor's type: descend into the definitions it uses (rows are per definition)
    forallTelescope ci.type fun xs concl => do
      for x in xs do scanBr machM "C-A.br" st "_" cnt (← inferType x)
      scanBr machM "C-A.br" st "_" cnt concl
  return (← st.get).rows.filter (fun r => !r.id.startsWith "C-A.br._.")

/-- C-E rows: branches of the emission's definitions reachable from `pstepV2`. -/
def extractEmit : MetaM (Array XRow) := do
  let st ← IO.mkRef ({} : BrSt)
  let ci ← getConstInfo ``Weak.Prom.pstepV2
  st.modify (fun s => { s with seen := s.seen.push ``Weak.Prom.pstepV2 })
  let cnt ← IO.mkRef 0
  scanBr emitM "C-E" st "pstepV2" cnt ci.value!
  return (← st.get).rows

/-- C-K: the 14 access-kind values and their classification. -/
def extractAK : MetaM (Array XRow) := do
  let akT := mkApp (mkConst ``Sail.ConcurrencyInterfaceV1.Access_kind) (mkConst ``LeanRV64D.RISCV_strong_access)
  let _ := akT
  let vars := [``Sail.ConcurrencyInterfaceV1.Access_variety.AV_plain,
    ``Sail.ConcurrencyInterfaceV1.Access_variety.AV_exclusive, ``Sail.ConcurrencyInterfaceV1.Access_variety.AV_atomic_rmw]
  let strs := [``Sail.ConcurrencyInterfaceV1.Access_strength.AS_normal,
    ``Sail.ConcurrencyInterfaceV1.Access_strength.AS_rel_or_acq,
    ``Sail.ConcurrencyInterfaceV1.Access_strength.AS_acq_rcpc]
  let arch := mkConst ``LeanRV64D.RISCV_strong_access
  let mut vals : Array (String × Expr) := #[]
  -- the constructor list of Access_kind, each expanded over its payload's finite type
  let ind ← getConstInfoInduct ``Sail.ConcurrencyInterfaceV1.Access_kind
  for c in ind.ctors do
    let con := mkApp (mkConst c) arch
    match nm c with
    | "AK_explicit" =>
      for v in vars do for s in strs do
        vals := vals.push (s!"AK_explicit.{nm v}.{nm s}",
          mkApp con (mkApp2 (mkConst ``Sail.ConcurrencyInterfaceV1.Explicit_access_kind.mk) (mkConst v) (mkConst s)))
    | "AK_arch" =>
      for v in vars do
        vals := vals.push (s!"AK_arch.{nm v}", mkApp con (mkApp (mkConst ``LeanRV64D.RISCV_strong_access.mk) (mkConst v)))
    | n => vals := vals.push (n, mkApp con (mkConst ``Unit.unit))
  let fns := [(``MachCSL.akIfetch, "ifetch"), (``MachCSL.akExcl, "excl"), (``MachCSL.akAcq, "acq"),
    (``MachCSL.akRel, "rel"), (``Weak.Prom.akStrong, "strong"), (``Weak.Prom.isTtw, "ttw")]
  let mut out := #[]
  for (n, v) in vals do
    let mut cls := #[]
    for (f, fnm) in fns do
      let b ← whnfD (mkApp (mkConst f) v)
      if b.isConstOf ``Bool.true then cls := cls.push fnm
      else if !b.isConstOf ``Bool.false then cls := cls.push s!"{fnm}?"
    out := out.push ⟨s!"C-K.{n}", s!"classify: [{String.intercalate " " cls.toList}]"⟩
  return out

unsafe def evalStrings (stx : Term) : TermElabM (List String) := do
  let ty := mkApp (mkConst ``List [levelZero]) (mkConst ``String)
  let e ← Term.elabTermEnsuringType stx (some ty)
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  evalExpr (List String) ty e

unsafe def evalBools (stx : Term) : TermElabM (List Bool) := do
  let ty := mkApp (mkConst ``List [levelZero]) (mkConst ``Bool)
  let e ← Term.elabTermEnsuringType stx (some ty)
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  evalExpr (List Bool) ty e

/-- C-D: the `instruction` constructors and the decoder-check classes decoding to each. -/
def extractDecoder (decoded : List (String × String × Bool)) : MetaM (Array XRow) := do
  let ind ← getConstInfoInduct ``LeanRV64D.instruction
  let mut out := #[]
  for c in ind.ctors do
    let key := s!"LeanRV64D.instruction.{nm c}"
    let cls := decoded.filter (fun (_, d, _) => d == key || d.startsWith (key ++ " "))
    let nw := (cls.filter (·.2.2)).length
    out := out.push ⟨s!"C-D.{nm c}", s!"{cls.length} classes, weaker {nw}: {String.intercalate " " ((cls.take 6).map (·.1))}{if cls.length > 6 then " …" else ""}"⟩
  return out

/-- Count `writeReg <r>` sites in the generated model, per register constructor. -/
def writeSites : MetaM (Std.HashMap Name Nat) := do
  let env ← getEnv
  let mut cnt : Std.HashMap Name Nat := {}
  for (n, ci) in env.constants.toList do
    if !(`LeanRV64D).isPrefixOf n then continue
    if n.isInternalDetail then continue
    let .defnInfo _ := ci | continue
    let some v := ci.value? | continue
    let hits := v.foldConsts (init := ([] : List Name)) (fun _ acc => acc)
    let _ := hits
    -- count applications `writeReg r`, `r` a Register constructor
    let rec go (e : Expr) (acc : Std.HashMap Name Nat) (fuel : Nat) : Std.HashMap Name Nat :=
      match fuel with
      | 0 => acc
      | fuel + 1 =>
      match e with
      | .app f a =>
        let acc := match e.getAppFn, e.getAppArgs with
          | .const w _, args =>
            if lastS w == "writeReg" then
              match args.toList.find? (fun x => match x with
                | .const r _ => (`LeanRV64D.Register).isPrefixOf r
                | _ => false) with
              | some (.const r _) => acc.insert r (acc.getD r 0 + 1)
              | _ => acc
            else acc
          | _, _ => acc
        go a (go f acc fuel) fuel
      | .lam _ t b _ => go b (go t acc fuel) fuel
      | .forallE _ t b _ => go b (go t acc fuel) fuel
      | .letE _ t v b _ => go b (go v (go t acc fuel) fuel) fuel
      | .mdata _ b => go b acc fuel
      | .proj _ _ b => go b acc fuel
      | _ => acc
    cnt := go v cnt 10000
  return cnt

/-- C-R and C-S: the `Register` constructors. -/
def extractRegs : MetaM (Array XRow × Array XRow) := do
  let ind ← getConstInfoInduct ``LeanRV64D.Register
  let sites ← writeSites
  let mut cr := #[]
  let mut cs := #[]
  for c in ind.ctors do
    let n := sites.getD c 0
    cs := cs.push ⟨s!"C-S.reg.{nm c}", s!"{n} writeReg occurrences"⟩
    let v ← whnfD (mkApp (mkConst ``Weak.eregNum) (mkConst c))
    let tracked := v.getAppFn.isConstOf ``Option.some
    if tracked || nm c == "nextPC" then
      cr := cr.push ⟨s!"C-R.{nm c}", s!"key {← ppS v}; {n} writeReg occurrences"⟩
  return (cr, cs)

/-- ALL ROWS of Table C v2, by family. -/
def extractAll (decoded : List (String × String × Bool)) : MetaM (Array (String × Array XRow)) := do
  let ca ← IO.mkRef ({} : CA)
  extractMemStep ca
  extractPmStep ca
  let cav ← ca.get
  let cf ← extractFields cav
  let cl ← checkLabels cav.rows
  let caRows := cav.rows.filter (fun r => !r.id.startsWith "C-L.")
  let br ← extractMachBranches
  let ce ← extractEmit
  let ck ← extractAK
  let cd ← extractDecoder decoded
  let (cr, cs) ← extractRegs
  return #[("C-F", cf), ("C-L", cl), ("C-A", caRows), ("C-A.br", br), ("C-E", ce), ("C-K", ck), ("C-D", cd),
    ("C-R", cr), ("C-S", cs)]

unsafe def decodedNames : TermElabM (List (String × String × Bool)) := do
  let names ← evalStrings (← `(Weak.Prom.Dec.rows.map (fun r => r.2.1.name)))
  let decs ← evalStrings (← `(Weak.Prom.Dec.rows.map (fun r => ((r.2.1.decoded.splitOn " ").headD ""))))
  let wk ← evalBools (← `(Weak.Prom.Dec.rows.map (fun r => (Weak.Prom.Dec.mmV2 r).any (fun m => m.2 == .weaker))))
  return names.zip (decs.zip wk)

@[implemented_by decodedNames] opaque decodedNamesS : TermElabM (List (String × String × Bool))

/-- `#tableCx` prints every extracted row of Table C v2, with per-family counts. -/
elab "#tableCx" : command => do
  let fams ← liftTermElabM do
    let dn ← decodedNamesS
    extractAll dn
  let mut lines := #[]
  for (f, rs) in fams do
    lines := lines.push s!"=== {f}: {rs.size} rows"
    for r in rs do lines := lines.push s!"{r.id} | {r.desc}"
  logInfo (String.intercalate "\n" lines.toList)

/-! ## 6. The check against the marked table -/

/-- A marked row: ID, mark, decider. -/
abbrev MRow := String × String × String

unsafe def evalTableU (n : Name) : TermElabM (List MRow) := do
  let e := mkConst n
  let ty ← inferType e
  evalExpr (List MRow) ty e

@[implemented_by evalTableU] opaque evalTableS (n : Name) : TermElabM (List MRow)

unsafe def probeNamesU (fam : String) : TermElabM (List String) := do
  let f := mkIdent `Weak.Prom.Probe.probeNames
  evalStrings (← `($f $(quote fam)))

@[implemented_by probeNamesU] opaque probeNamesS (fam : String) : TermElabM (List String)

def markOk (m : String) : Bool :=
  m == "FAITHFUL" || m == "WEAKER" || m == "INERT" ||
  ["STRONGER:", "PF:", "SCOPE:"].any (fun p => m.startsWith p && m.length > p.length + 2)

def knownFams : List String := ["G1", "G1w", "G1lxs", "G1b", "G2", "G3", "G5", "G5x", "TS", "ROW", "COV", "ORACLE"]

/-- `#tableCx_check tbl`: the extracted row IDs must EQUAL the table's (no missing, no extra, no duplicate row);
every mark and decider must be well-formed and resolve (theorem names exist; probe names exist in their family;
comparison families are known); a C-D row is marked WEAKER exactly when the decoder check found a WEAKER class of
that constructor.  Any failure is a build error. -/
elab "#tableCx_check " tbl:ident : command => do
  let (fams, tab, probes) ← liftTermElabM do
    let dn ← decodedNamesS
    let fams ← extractAll dn
    let tab ← evalTableS tbl.getId
    let mut probes : Std.HashMap String (List String) := {}
    for f in ["G1b", "G1lxs", "G3", "G5", "G5x", "TS", "ROW"] do
      probes := probes.insert f (← probeNamesS f)
    return (fams, tab, probes)
  let rows := fams.flatMap (·.2)
  let ids := rows.map (·.id)
  let tids := tab.map (·.1)
  let mut errs : Array String := #[]
  for r in rows do
    if !tids.contains r.id then errs := errs.push s!"MISSING (extracted, not in the table): {r.id} | {r.desc}"
  for t in tids do
    if !ids.contains t then errs := errs.push s!"EXTRA (in the table, not extracted): {t}"
  let mut seen : Std.HashSet String := {}
  for t in tids do
    if seen.contains t then errs := errs.push s!"DUPLICATE table row: {t}"
    seen := seen.insert t
  let env ← getEnv
  for (id, mk, dc) in tab do
    if !markOk mk then errs := errs.push s!"BAD MARK {id}: {mk}"
    for d in dc.splitOn " + " do
      if d.startsWith "cmp:" then
        for f in (d.drop 4).toString.splitOn "," do
          if !knownFams.contains f then errs := errs.push s!"BAD FAMILY {id}: {f}"
      else if d.startsWith "dec:" then
        for t in (d.drop 4).toString.splitOn "," do
          if !env.contains t.toName then errs := errs.push s!"UNKNOWN THEOREM {id}: {t}"
      else if d.startsWith "text:" then
        for p in (d.drop 5).toString.splitOn "," do
          match p.splitOn "/" with
          | [f, n] =>
            match probes[f]? with
            | some ns => if !ns.contains n then errs := errs.push s!"UNKNOWN PROBE {id}: {p}"
            | none => errs := errs.push s!"UNKNOWN PROBE FAMILY {id}: {p}"
          | _ => errs := errs.push s!"BAD PROBE REF {id}: {p}"
      else if d.startsWith "reason:" then
        if d.length < 20 then errs := errs.push s!"REASON TOO SHORT {id}"
      else errs := errs.push s!"BAD DECIDER {id}: {d}"
  -- C-D marks agree with the decoder check
  for r in rows do
    if r.id.startsWith "C-D." then
      let nw := ((r.desc.splitOn "weaker ").getD 1 "0").takeWhile Char.isDigit |>.toString.toNat!
      match tab.find? (·.1 == r.id) with
      | some (_, mk, _) =>
        if nw > 0 && mk != "WEAKER" then errs := errs.push s!"C-D MARK {r.id}: decoder check has {nw} WEAKER classes, table says {mk}"
        if nw == 0 && mk == "WEAKER" then errs := errs.push s!"C-D MARK {r.id}: no WEAKER class, table says WEAKER"
      | none => pure ()
  if !errs.isEmpty then
    throwError m!"Table C v2 check FAILED ({errs.size} problems):\n{String.intercalate "\n" errs.toList}"
  -- summary
  let mut lines := #[s!"Table C v2: {rows.size} rows, all marked and decided"]
  for (f, rs) in fams do
    let ms := rs.toList.filterMap (fun r => (tab.find? (·.1 == r.id)).map (·.2.1))
    let cnt (p : String → Bool) := (ms.filter p).length
    lines := lines.push s!"  {f}: {rs.size} rows — FAITHFUL {cnt (· == "FAITHFUL")}, WEAKER {cnt (· == "WEAKER")}, INERT {cnt (· == "INERT")}, PF {cnt (·.startsWith "PF:")}, SCOPE {cnt (·.startsWith "SCOPE:")}, STRONGER {cnt (·.startsWith "STRONGER:")}"
  logInfo (String.intercalate "\n" lines.toList)

end Weak.Prom.TC
