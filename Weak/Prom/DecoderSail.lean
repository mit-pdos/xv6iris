/-
Weak/Prom: **the decoder check's Sail observations** (S0-P part (3)): every class of `DecoderTable.classes` is run
for ONE instruction through the Sail model (`SailExec.riscvStepP`, M-mode power-on state of `MachSail.bootX`,
translation off), and the Sail events are classified by BOTH emissions:
* emission v2 (`Weak/Prom/Emit.lean`): `regSrcs`/`depsAddr`/`depsVsrc`/`depsCtrl` of `v2Roles`, the `LCmo` of a
  Zicbom instruction (`dsrcOfRs1`), exactly as `hnodeStep`/`bndStep` (and `MachSail.sNext`) do;
* today's emission (`Weak/WeakEvInst.lean` `pnodeStep`): `erwOf (depsOfIb bits) ibRds r` with DEC-7's dynamic read
  set (`ibRead` at every `regRead`, reset by the announce, `ibAnn`), `LLoad … []` (D-8), `LExLoad`/`LStore`/
  `LExStore` with `depsAsrc`/`depsVsrc`.
It also runs Sail's decoder (`ext_decode`/`ext_decode_compressed`, compiled by `Vtest.Model`'s `compile_cone%`)
on the class's encoding and prints the constructor, so the table's encodings are checked against the model.
Answers: fetches from the image (the class word, then `c.nop`s), data reads `0`, writes `.Ok (some true)` (an SC
in mode `scFailM`: `.Err ()`); the reservation predicate is `false` in mode `scFailP`, else `true`.

Run: `lake env lean --run Weak/Prom/DecoderSail.lean > Weak/Prom/DecoderObs.lean` (the output is a Lean file).
-/
import Weak.Prom.MachSail
import Weak.Prom.DecoderTable

namespace Weak.Prom.Dec.SailRun

open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D
open Weak (Dsrc OpRoles depsOfIb depsCtrl depsAddr depsVsrc depsAsrc depsRd depsRd2 eregNum ibOfBvn erwOf
  ErwKind paZ)
open Weak.Prom Weak.Prom.Dec

def CODE : Nat := 0x80400000

/-- One recorded Sail event. -/
inductive Ev where
  | rr (r : Register)
  | rw (r : Register)
  | mr (n : Nat) (pa : Int) (ak : AK)
  | mw (n : Nat) (pa : Int) (ak : AK) (ok : Bool)
  | bar
  | ann (w : BitVec 32)
  | exc

instance : Inhabited Ev := ⟨.bar⟩

/-- The register file of a class: every GPR `xk` holds the RAM address `0x80010000 + 0x100·k`; the two branch
operands are set so that the branch is taken (`brT`) or not (`brN`). -/
def regsFor (c : Cls) : Vtest.XRegs := Id.run do
  let mut x := (SailLit.bootX 0).insert .PC (BitVec.ofNat 64 CODE)
  for k in List.range 32 do
    x := SailLit.setGpr x k (BitVec.ofNat 64 (0x80010000 + 0x100 * k))
  let a : Nat := 0x80010600
  let pre (p : String) : Bool := c.name.startsWith p
  let t := c.mode == .brT
  let n := c.mode == .brN
  if pre "beq" && t || pre "bne" && n || pre "bge-" && t || pre "bgeu" && t then
    x := SailLit.setGpr x 7 (BitVec.ofNat 64 (if pre "beq" || pre "bne" then a else a - 0x100))
  if pre "blt-" && n || pre "bltu" && n then x := SailLit.setGpr x 7 (BitVec.ofNat 64 (a - 0x100))
  if pre "bge-" && n || pre "bgeu" && n then x := SailLit.setGpr x 7 (BitVec.ofNat 64 0x80010700)
  if pre "c.beqz" && t || pre "c.bnez" && n then x := SailLit.setGpr x 10 0
  return x

/-- The image: the class word at `CODE` (a compressed parcel padded with `c.nop`s), `c.nop`s after it. -/
def imgFor (c : Cls) (a : Int) : BitVec 8 :=
  let off := a - (CODE : Int)
  if 0 ≤ off ∧ off < 64 then
    let o := off.toNat
    let comp := c.w < 0x10000 && c.w % 4 != 3
    let word := if comp then c.w ||| (0x0001 <<< 16) else c.w
    if o < 4 then BitVec.ofNat 8 ((word >>> (8 * o)) % 256)
    else BitVec.ofNat 8 (if o % 2 == 0 then 0x01 else 0x00)
  else 0#8

/-- Step the Sail monad to its end, recording the events. -/
partial def run (c : Cls) (m : SailM Unit) (rs : Vtest.XRegs) (acc : Array Ev) (fuel : Nat) :
    Array Ev × String × Vtest.XRegs :=
  if fuel = 0 then (acc, "fuel", rs) else
  match m with
  | .pure _ => (acc, "", rs)
  | .impure (.error _) _ => (acc, "sail-error", rs)
  | .impure (.ok o) k =>
    match o, k with
    | .regRead r, k => run c (k (rs.get r)) rs (acc.push (.rr r)) (fuel - 1)
    | .regWrite r v, k => run c (k PUnit.unit) (rs.insert r v) (acc.push (.rw r)) (fuel - 1)
    | .memRead n _ req, k =>
      let ak := req.access_kind
      let pa := paZ req.pa
      let bs := (List.range n).map (fun j => if akIfetch ak then imgFor c (pa + j) else 0#8)
      run c (k (.Ok (MachCSL.bvOfBytes n bs, none))) rs (acc.push (.mr n pa ak)) (fuel - 1)
    | .memWrite n _ req, k =>
      let ak := req.access_kind
      let fail := c.mode == .scFailM && akExcl ak
      run c (k (if fail then .Err () else .Ok (some true))) rs (acc.push (.mw n (paZ req.pa) ak (!fail)))
        (fuel - 1)
    | .barrier _, k => run c (k ()) rs (acc.push .bar) (fuel - 1)
    | .instrAnnounce _ w, k => run c (k ()) rs (acc.push (.ann (ibOfBvn w))) (fuel - 1)
    | .branchAnnounce _ _, k => run c (k ()) rs acc (fuel - 1)
    | .cacheOp _, k => run c (k ()) rs acc (fuel - 1)
    | .tlbi _, k => run c (k ()) rs acc (fuel - 1)
    | .takeException _, k => run c (k ()) rs (acc.push .exc) (fuel - 1)
    | .returnException _, k => run c (k ()) rs acc (fuel - 1)
    | .translationStart _, k => run c (k ()) rs acc (fuel - 1)
    | .translationEnd _, k => run c (k ()) rs acc (fuel - 1)
    | .cycleCount, k => run c (k ()) rs acc (fuel - 1)
    | .message _, k => run c (k ()) rs acc (fuel - 1)
    | .getCycleCount, k => run c (k (0 : Nat)) rs acc (fuel - 1)
    | .choose _, _ => (acc, "choose", rs)
    | .readRam .., _ => (acc, "readRam", rs)
    | .writeRam .., _ => (acc, "writeRam", rs)

/-- Run Sail's decoder on the class word (register reads answered from `rs`). -/
partial def runDec (m : SailM instruction) (rs : Vtest.XRegs) (fuel : Nat) : String :=
  if fuel = 0 then "fuel" else
  match m with
  | .pure i => (toString (repr i)).replace "\n" " "
  | .impure (.error _) _ => "decode-error"
  | .impure (.ok o) k =>
    match o, k with
    | .regRead r, k => runDec (k (rs.get r)) rs (fuel - 1)
    | _, _ => "decode-event"

def regName (r : Register) : String :=
  let s := toString (repr r)
  (s.splitOn ".").getLast!

/-- Append-or-replace by key. -/
def upd {α : Type} (l : List (Nat × α)) (n : Nat) (v : α) : List (Nat × α) :=
  if l.any (·.1 == n) then l.map (fun p => if p.1 == n then (n, v) else p) else l ++ [(n, v)]

def addAll (l m : List R) : List R := m.foldl (fun acc r => if acc.contains r then acc else acc ++ [r]) l

/-- Emission v2's view of the events. -/
def classV2 (evs : List Ev) : Emitted := Id.run do
  let mut bits : Option (BitVec 32) := none
  let mut scOk := false
  let mut e : Emitted := {}
  let mut ds : List (Nat × Option (List R × Bool)) := []
  let mut ix : Ix := ixNone
  for ev in evs do
    match ev with
    | .ann w => bits := some w; ix := { ix with bits := some w }
    | .rr r =>
      match csrCapture ix r with
      | some n => ix := { ix with csrOld := true }; ds := upd ds csrOldKey (some (rsOf [.DReg n], false))
      | none => pure ()
    | .rw r =>
      if r == .nextPC then e := { e with ctrl := addAll e.ctrl (rsOf (depsCtrl (v2Roles bits))) }
      else match eregNum r with
        | some n => let s := regSrcs bits scOk n; ds := upd ds n (some (rsOf s, memOf s))
        | none => pure ()
    | .mr _ _ ak =>
      if akIfetch ak then pure () else e := { e with asrc := addAll e.asrc (rsOf (depsAddr (v2Roles bits))) }
    | .mw _ _ ak ok =>
      if akExcl ak && isSC bits && !ok then pure () else
      if akExcl ak && isSC bits then scOk := true
      e := { e with asrc := addAll e.asrc (rsOf (depsAddr (v2Roles bits))),
                    dsrc := addAll e.dsrc (rsOf (depsVsrc (v2Roles bits))) }
    | _ => pure ()
  match bits with
  | some w => if (cboKind bits).isSome then e := { e with asrc := addAll e.asrc (rsOf (dsrcOfRs1 w)) }
  | none => pure ()
  return v2Old bits ({ e with dests := ds.map (fun p => (rOfKey p.1, p.2)) } : Emitted)

/-- Today's emission's view of the events, with the DEC-7 read sets at each tracked write and `nextPC` write. -/
def classToday (evs : List Ev) : Emitted × List (Nat × List Nat) × List (List Nat) := Id.run do
  let mut bits : Option (BitVec 32) := none
  let mut rds : List Nat := []
  let mut e : Emitted := {}
  let mut ds : List (Nat × Option (List R × Bool)) := []
  let mut wr : List (Nat × List Nat) := []
  let mut pcs : List (List Nat) := []
  for ev in evs do
    match ev with
    | .ann w => bits := some w; rds := []
    | .rr r => match eregNum r with | some n => rds := rds ++ [n] | none => pure ()
    | .rw r =>
      if r == .nextPC then pcs := pcs ++ [rds]
      match eregNum r with
      | some n => wr := wr ++ [(n, rds)]
      | none => pure ()
      match erwOf (depsOfIb bits) rds r with
      | .ERWctrl s => e := { e with ctrl := addAll e.ctrl (rsOf s) }
      | .ERWreg rd s => ds := upd ds rd (some (rsOf s, memOf s))
      | .ERWnone =>
        match eregNum r with
        | some n => if ds.any (·.1 == n) then pure () else ds := ds ++ [(n, none)]
        | none => pure ()
    | .mr _ _ ak =>
      if akIfetch ak then pure ()
      else if akExcl ak then e := { e with asrc := addAll e.asrc (rsOf (depsAsrc (depsOfIb bits))) }
      else pure ()
    | .mw _ _ _ _ =>
      e := { e with asrc := addAll e.asrc (rsOf (depsAsrc (depsOfIb bits))),
                    dsrc := addAll e.dsrc (rsOf (depsVsrc (depsOfIb bits))) }
    | _ => pure ()
  return ({ e with dests := ds.map (fun p => (rOfKey p.1, p.2)) }, wr, pcs)

/-- The memory events (`isWrite`, `excl`, `ok`), fetches excluded. -/
def memEvs (evs : List Ev) : List (Bool × Bool × Bool) :=
  evs.filterMap (fun ev => match ev with
    | .mr _ _ ak => if akIfetch ak then none else some (false, akExcl ak, true)
    | .mw _ _ ak ok => some (true, akExcl ak, ok)
    | _ => none)

def esc (s : String) : String := (repr s).pretty

def main : IO Unit := do
  IO.println "/-\nWeak/Prom: GENERATED by `lake env lean --run Weak/Prom/DecoderSail.lean` (do not edit): the Sail\nobservations of every decoder-check class (see `DecoderSail.lean`).\n-/"
  IO.println "import Weak.Prom.DecoderTable\n\nnamespace Weak.Prom.Dec\n"
  IO.println "/-- One class's row: the observation, the today's-emission write trace (tracked key, DEC-7 read\nset), the read sets at the `nextPC` writes, and the memory events. -/"
  IO.println "abbrev ORow := Obs × List (Nat × List Nat) × List (List Nat) × List (Bool × Bool × Bool)\n"
  let mut k := 0
  for c in classes do
    let rs := regsFor c
    let P : BitVec 64 → Bool := fun _ => c.mode != .scFailP
    let (evs, stop, _) := run c (riscvStepP P false) rs #[] 200000
    let evs := evs.toList
    let comp := c.w < 0x10000 && c.w % 4 != 3
    let dec := if comp then runDec (LeanRV64D.Functions.ext_decode_compressed (BitVec.ofNat 16 c.w)) rs 10000
               else runDec (LeanRV64D.Functions.ext_decode (BitVec.ofNat 32 c.w)) rs 10000
    let dec := String.ofList (dec.toList.take 70)
    let writes := (evs.filterMap (fun e => match e with | .rw r => some (regName r) | _ => none)).eraseDups
    let keys := (evs.filterMap (fun e => match e with | .rw r => eregNum r | _ => none))
    -- a TRAP writes the cause AND the exception PC (a `csrw mcause` writes only the former)
    let wrote (r : Register) : Bool := evs.any (fun e => match e with | .rw r' => r' == r | _ => false)
    let trap := (wrote .mcause && wrote .mepc) || (wrote .scause && wrote .sepc) ||
      evs.any (fun e => match e with | .exc => true | _ => false)
    let stop := if stop == "" && trap then "trap" else stop
    let v2 := classV2 evs
    let (td, wr, pcs) := classToday evs
    let o : Obs := ⟨c.name, dec, writes, keys, stop, v2, td⟩
    let line := s!"def o{k} : ORow := ({repr o}, {repr wr}, {repr pcs}, {repr (memEvs evs)})"
    IO.println (line.replace "\n" " ")
    k := k + 1
  IO.println s!"\n/-- Per class, in `classes` order. -/\ndef obsData : List ORow := [{String.intercalate ", " ((List.range k).map (fun i => s!"o{i}"))}]"
  IO.println "\nend Weak.Prom.Dec"

end Weak.Prom.Dec.SailRun

def main : IO Unit := Weak.Prom.Dec.SailRun.main
