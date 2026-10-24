import KaterCert.ModelEval
import Lean.Data.Json

/-!
`kater-model-check [-v] FILE...`: the differential test of the model against
the oracle. Reads the graphs `kater-oracle graphs --json` writes, each with
the oracle's meaning of every builtin relation and predicate on it, and
compares those with the model's (`Model.Finite.pred`, `Model.Finite.rel`,
which `ModelEval` proves mean what `Model.lean` does), and checks that each
graph satisfies `Graph.WF` (`Model.Finite.wf`). Prints each disagreement,
the first few of each builtin and axiom in full; exits with 1 if there is
one, or a file does not read.
-/

open Lean KaterCert Model

instance : Inhabited Kind := ⟨.OTHER⟩
instance : Inhabited Order := ⟨.NA⟩

/-- What a line of the oracle's says of a graph. -/
structure Record where
  source : String
  name : String
  graph : Finite
  /-- The oracle's meaning of the predicates, and of the relations, in the
  order of the header; `none` where it has none. -/
  preds : Array (Option (Array Bool))
  rels : Array (Option (Array Bool))
  /-- The oracle's axioms the graph violates. -/
  axioms : Nat

def bits (j : Json) : Except String (Array Bool) := do
  let s ← j.getStr?
  s.toList.toArray.mapM fun
    | '0' => pure false
    | '1' => pure true
    | c => throw s!"not a bit: {c}"

def field (j : Json) (k : String) : Except String Json := j.getObjVal? k

def natArray (j : Json) : Except String (Array Nat) := do
  (← j.getArr?).mapM (·.getNat?)

def strArray (j : Json) : Except String (Array String) := do
  (← j.getArr?).mapM (·.getStr?)

def kindOf : String → Except String Kind
  | "R" => pure .R | "W" => pure .W | "F" => pure .F | "TC" => pure .TC | "TB" => pure .TB
  | "TJ" => pure .TJ | "TE" => pure .TE | "TK" => pure .TK | "ALLOC" => pure .ALLOC
  | "FREE" => pure .FREE | "HPRET" => pure .HPRET | "HPPROTECT" => pure .HPPROTECT
  | "METHOD-BEGIN" => pure .MB | "METHOD-END" => pure .ME | "OTHER" => pure .OTHER
  | k => throw s!"unknown kind {k}"

def orderOf : String → Except String Order
  | "na" => pure .NA | "rlx" => pure .RLX | "acq" => pure .ACQ | "rel" => pure .REL
  | "acq_rel" => pure .ACQ_REL | "sc" => pure .SC
  | o => throw s!"unknown ordering {o}"

def optBits (j : Json) : Except String (Option (Array Bool)) :=
  if j.isNull then pure none else some <$> bits j

def readRecord (j : Json) : Except String Record := do
  let n ← (← field j "n").getNat?
  let sized {α} (what : String) (a : Array α) (size : Nat) : Except String (Array α) :=
    if a.size = size then pure a else throw s!"{what}: {a.size} entries, not {size}"
  let thread ← sized "thread" (← natArray (← field j "thread")) n
  let kind ← sized "kind" (← (← strArray (← field j "kind")).mapM kindOf) n
  let order ← sized "order" (← (← strArray (← field j "order")).mapM orderOf) n
  let loc ← sized "loc" (← natArray (← field j "loc")) n
  let hp ← sized "hp" (← natArray (← field j "hp")) n
  let flag (k : String) : Except String (Fin n → Bool) := do
    let a ← sized k (← bits (← field j k)) n
    pure fun e => a[e]!
  let edges (k : String) : Except String (Fin n → Fin n → Bool) := do
    let a ← sized k (← bits (← field j k)) (n * n)
    pure fun x y => a[x.val * n + y.val]!
  let graph : Finite :=
    { n, thread := fun e => thread[e]!, kind := fun e => kind[e]!, order := fun e => order[e]!
      loc := fun e => loc[e]!, hp := fun e => hp[e]!
      excl := ← flag "excl", durable := ← flag "durable", recovery := ← flag "recovery"
      abstractLock := ← flag "abstractLock", dependableOther := ← flag "dependableOther"
      rf := ← edges "rf", mo := ← edges "mo", ctrl := ← edges "ctrl", addr := ← edges "addr"
      data := ← edges "data", pctrl := ← edges "pctrl", tc := ← edges "tc", tj := ← edges "tj"
      lin := ← edges "lin", added := ← edges "added", hb := ← edges "hb" }
  pure
    { source := ← (← field j "source").getStr?, name := ← (← field j "name").getStr?, graph
      preds := ← (← (← field j "pred").getArr?).mapM optBits
      rels := ← (← (← field j "rel").getArr?).mapM optBits
      axioms := ← (← field j "axioms").getNat? }

/-- Kater's name of a builtin, as Lean names its constructor. -/
def leanName (kater : String) : String := kater.map fun c => if c == '-' then '_' else c

def ctorName {α} [Repr α] (a : α) : String :=
  match ((repr a).pretty.splitOn ".").getLast? with
  | some s => s
  | none => ""

/-- The builtins of the header, as Lean's: (Kater's name, Lean's builtin). -/
def readHeader (j : Json) : Except String (Array (String × Builtin.Pred) ×
    Array (String × Builtin.Rel)) := do
  let entry (e : Json) : Except String (Int × String) := do
    let a ← e.getArr?
    pure (← a[0]!.getInt?, ← a[1]!.getStr?)
  let preds ← (← (← field j "preds").getArr?).mapM fun e => do
    let (id, name) ← entry e
    match Builtin.Pred.ofId id with
    | some p =>
      -- Kater gives LK and UL no name
      if !name.startsWith "#" && leanName name != ctorName p then
        throw s!"predicate {id} is {name} in Kater, {ctorName p} in Lean"
      pure (name, p)
    | none => throw s!"predicate {id} ({name}) is no builtin of Lean's"
  let rels ← (← (← field j "rels").getArr?).mapM fun e => do
    let (id, name) ← entry e
    match Builtin.Rel.ofId id with
    | some r =>
      if leanName name != ctorName r then
        throw s!"relation {id} is {name} in Kater, {ctorName r} in Lean"
      pure (name, r)
    | none => throw s!"relation {id} ({name}) is no builtin of Lean's"
  if preds.size != Builtin.Pred.all.length || rels.size != Builtin.Rel.all.length then
    throw "the oracle's builtins are not Lean's"
  pure (preds, rels)

/-- The graph, as a line of the oracle's says it, for a disagreement. -/
def describe (r : Record) : String :=
  let g := r.graph
  let evs := (List.finRange g.n).map fun e =>
    s!"e{e.val}: T{g.thread e} {ctorName (g.kind e)} {ctorName (g.order e)} loc {g.loc e}" ++
      (if g.excl e then " excl" else "") ++ (if g.hp e != 0 then s!" hp {g.hp e}" else "")
  let rel (name : String) (f : Fin g.n → Fin g.n → Bool) : List String :=
    let es := (List.finRange g.n).flatMap fun x => (List.finRange g.n).filterMap fun y =>
      if f x y then some s!"e{x.val}->e{y.val}" else none
    if es.isEmpty then [] else [s!"{name}: {" ".intercalate es}"]
  let added := ((List.finRange g.n).map fun e =>
      (((List.finRange g.n).filter (g.added · e)).length, e)).mergeSort
    (fun a b => a.1 ≤ b.1)
  "\n".intercalate (evs ++ rel "rf" g.rf ++ rel "mo" g.mo ++ rel "ctrl" g.ctrl ++
    rel "addr" g.addr ++ rel "data" g.data ++ rel "pctrl" g.pctrl ++ rel "tc" g.tc ++
    rel "tj" g.tj ++ rel "lin" g.lin ++ rel "hb" g.hb ++
    [s!"added: {" ".intercalate (added.map fun (_, e) => s!"e{e.val}")}"])

structure Tally where
  graphs : Std.HashMap String Nat := {}
  /-- Graphs the oracle's axioms reject, by source. -/
  rejected : Std.HashMap String Nat := {}
  /-- Disagreements, and graphs that fail an axiom of `WF`, by builtin or
  axiom. -/
  differ : Std.HashMap String Nat := {}
  pairs : Nat := 0
  shown : Nat := 3

def Tally.bump (m : Std.HashMap String Nat) (k : String) : Std.HashMap String Nat :=
  m.insert k (m.getD k 0 + 1)

def checkRecord (preds : Array (String × Builtin.Pred)) (rels : Array (String × Builtin.Rel))
    (r : Record) (t : Tally) : IO Tally := do
  let g := r.graph
  let mut t := { t with graphs := Tally.bump t.graphs r.source }
  if r.axioms > 0 then t := { t with rejected := Tally.bump t.rejected r.source }
  let report (t : Tally) (what detail : String) : IO Tally := do
    if t.differ.getD what 0 < t.shown then
      IO.println s!"{what}: {detail}, on {r.source} graph {r.name}:\n{describe r}\n"
    pure { t with differ := Tally.bump t.differ what }
  for (i, (name, p)) in preds.toList.zipIdx.map (fun (x, i) => (i, x)) do
    match r.preds[i]? with
    | some (some oracle) =>
      let lean := (List.finRange g.n).map (g.pred p ·)
      t := { t with pairs := t.pairs + g.n }
      if lean.toArray != oracle then
        let at_ := (List.finRange g.n).filter fun e => g.pred p e != oracle[e]!
        t ← report t name s!"the oracle and the model differ at {at_.map (s!"e{·.val}")}: \
          the model has it at {(List.finRange g.n).filter (g.pred p ·) |>.map (s!"e{·.val}")}"
    | _ => pure ()
  for (i, (name, rl)) in rels.toList.zipIdx.map (fun (x, i) => (i, x)) do
    match r.rels[i]? with
    | some (some oracle) =>
      -- si and loc-overlap mean nothing to the oracle
      if rl == .si || rl == .loc_overlap then continue
      t := { t with pairs := t.pairs + g.n * g.n }
      let all := (List.finRange g.n).flatMap fun x => (List.finRange g.n).map (x, ·)
      let diff := all.filter fun (x, y) => g.rel rl x y != oracle[x.val * g.n + y.val]!
      if !diff.isEmpty then
        let edges (l : List (Fin g.n × Fin g.n)) := l.map fun (x, y) => s!"e{x.val}->e{y.val}"
        t ← report t name s!"the oracle and the model differ at {edges diff}: \
          the model has {edges (all.filter fun (x, y) => g.rel rl x y)}"
    | _ => pure ()
  for (name, ok) in g.wfChecks do
    if !ok then t ← report t s!"WF.{name}" "the graph fails the axiom"
  pure t

def checkFile (path : String) (t : Tally) : IO (Tally × Bool) := do
  let h ← IO.FS.Handle.mk path .read
  let header ← match Json.parse (← h.getLine) >>= readHeader with
    | .ok hd => pure hd
    | .error e => IO.eprintln s!"{path}: {e}"; return (t, false)
  let mut t := t
  let mut ok := true
  let mut line := 1
  repeat
    let l ← h.getLine
    if l.isEmpty then break
    line := line + 1
    match Json.parse l >>= readRecord with
    | .ok r => t ← checkRecord header.1 header.2 r t
    | .error e => IO.eprintln s!"{path}:{line}: {e}"; ok := false
  pure (t, ok)

def main (args : List String) : IO UInt32 := do
  let verbose := args.contains "-v"
  let files := args.filter (· != "-v")
  if files.isEmpty then
    IO.eprintln "usage: kater-model-check [-v] FILE..."
    return 2
  let mut t : Tally := { shown := if verbose then 1000 else 3 }
  let mut ok := true
  for f in files do
    let (t', ok') ← checkFile f t
    t := t'
    ok := ok && ok'
  let total := t.graphs.fold (fun s _ v => s + v) 0
  let sources := t.graphs.toList.mergeSort (fun a b => a.1 ≤ b.1)
  IO.println s!"{total} graphs ({", ".intercalate (sources.map fun (s, c) => s!"{c} {s}")}), \
    {t.pairs} values of builtins compared"
  for (s, c) in t.rejected.toList do
    IO.println s!"  {c} {s} graphs violate the oracle's own axioms"
  if t.differ.isEmpty then
    IO.println "the model and the oracle agree on every builtin, and every graph satisfies WF"
  else
    for (what, c) in t.differ.toList.mergeSort (fun a b => a.1 ≤ b.1) do
      IO.println s!"  {what}: {c} graphs"
  return if ok && t.differ.isEmpty then 0 else 1
