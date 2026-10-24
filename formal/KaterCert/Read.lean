import Lean.Data.Json
import KaterCert.Checker
import KaterCert.Chain

/-!
# Reading certificates

Certificates as `kater-oracle certify --json` writes them
(`tests/oracle/Certificate.cpp`). A letter is
`{"relation": [id, inverse] or null, "pre": [[id, complement], ...], "post": [...]}`;
an automaton is `{"states": n, "starting": [...], "accepting": [...],
"transitions": [[source, letter, destination], ...]}`; row p of the
simulation lists, as 0s and 1s, which states simulate p. Fields the checker
does not need (the letters' text) are ignored.

A certificate's `chain`, if it has one, lists its letters once, in
`labels`, and gives a letter elsewhere by its index there. Its passes are
`{"pass": name, "evidence": ..., "result": automaton}`; evidence has the
`hypothesis` (`transitive`, `within` or `empty`), its `letter`, `automaton`
and `word`, the `roles` (`["state", n]`, `["after", n]` or
`["copy", j, g]`), the `copies` (`{"from": n, "to": n, "path": [[letter,
destination, known predicates], ...]}`) and the `inclusions`.

What is read here is trusted to be what Kater wrote: the proof is about the
`Certificate` and `Chain` this produces.

This mirrors the C++ regions `CertificateJSON` and `ChainJSON`
(`tests/oracle/Certificate.cpp`): `scripts/check-mirrors.sh` reports when
they change.
-/

namespace KaterCert.Read

open Lean (Json)

/-- A certificate file: the certificate, what it is for, and the verdict
`checkCertificate` gave it, if recorded. -/
structure Entry where
  file : String
  constraint : String
  /-- How the certificate differs from Kater's, if it does. -/
  mutation : Option String
  verdict : Option String
  cert : Certificate
  /-- How the certificate's right automaton came from the right-hand side. -/
  chain : Option Chain

def pair (j : Json) : Except String (Json × Json) := do
  let a ← j.getArr?
  if h : a.size = 2 then return (a[0], a[1])
  else throw s!"expected a pair, got {j.compress}"

def list (j : Json) (f : Json → Except String α) : Except String (List α) := do
  (← j.getArr?).toList.mapM f

def predicate (j : Json) : Except String Predicate := do
  let (id, complement) ← pair j
  return { id := ← id.getInt?, complement := ← complement.getBool? }

def label (j : Json) : Except String Label := do
  let rel ← match ← j.getObjVal? "relation" with
    | .null => pure none
    | r => do
      let (id, inverse) ← pair r
      pure (some { id := ← id.getInt?, inverse := ← inverse.getBool? })
  return {
    rel
    pre := ← list (← j.getObjVal? "pre") predicate
    post := ← list (← j.getObjVal? "post") predicate }

/-- An automaton, its letters read by `letter`. -/
def nfaWith (letter : Json → Except String Label) (j : Json) : Except String (NFA Label) := do
  let n ← (← j.getObjVal? "states").getNat?
  let mut outs : Array (Array (Label × Nat)) := Array.replicate n #[]
  for t in ← (← j.getObjVal? "transitions").getArr? do
    let a ← t.getArr?
    unless a.size = 3 do throw s!"a transition is [source, letter, destination]: {t.compress}"
    let src ← a[0]!.getNat?
    unless src < n do throw s!"a transition from no state: {t.compress}"
    outs := outs.modify src (·.push (← letter a[1]!, ← a[2]!.getNat?))
  let mut accepting := Array.replicate n false
  for q in ← list (← j.getObjVal? "accepting") Json.getNat? do
    unless q < n do throw s!"accepting state {q} is not a state"
    accepting := accepting.set! q true
  return {
    outs := outs.map Array.toList
    accepting
    start := ← list (← j.getObjVal? "starting") Json.getNat? }

def nfa (j : Json) : Except String (NFA Label) := nfaWith label j

def simulation (j : Json) : Except String (Array Bool) := do
  let mut bits := #[]
  for row in ← list j Json.getStr? do
    for b in row.toList do
      match b with
      | '0' => bits := bits.push false
      | '1' => bits := bits.push true
      | _ => throw s!"a simulation row is 0s and 1s: {row}"
  return bits

def certificate (j : Json) : Except String Certificate := do
  return {
    lhs := ← nfa (← j.getObjVal? "lhs")
    rhs := ← nfa (← j.getObjVal? "rhs")
    simulation := ← simulation (← j.getObjVal? "simulation")
    pairs := ← list (← j.getObjVal? "pairs") fun p => do
      let (left, right) ← pair p
      return (← left.getNat?, ← list right Json.getNat?)
    inclusions := ← list (← j.getObjVal? "inclusions") fun i => do
      let (a, b) ← pair i
      return (← label a, ← label b) }

/-- A letter of a chain: its index among the chain's `labels`. -/
def labelAt (labels : Array Label) (j : Json) : Except String Label := do
  let i ← j.getNat?
  match labels[i]? with
  | some l => return l
  | none => throw s!"letter {i} is not among the chain's"

def role (j : Json) : Except String Role := do
  match (← j.getArr?).toList with
  | [k, n] =>
    match ← k.getStr? with
    | "state" => return .state (← n.getNat?)
    | "after" => return .after (← n.getNat?)
    | _ => throw s!"no role is {j.compress}"
  | [k, q, g] =>
    if (← k.getStr?) == "copy" then return .copy (← q.getNat?) (← g.getNat?)
    else throw s!"no role is {j.compress}"
  | _ => throw s!"no role is {j.compress}"

def step (labels : Array Label) (j : Json) : Except String Step := do
  let a ← j.getArr?
  unless a.size = 3 do throw s!"a step of a path is [letter, destination, known]: {j.compress}"
  return {
    letter := ← labelAt labels a[0]!
    dest := ← a[1]!.getNat?
    known := ← list a[2]! predicate }

def copyOf (labels : Array Label) (j : Json) : Except String Copy := do
  return {
    src := ← (← j.getObjVal? "from").getNat?
    dst := ← (← j.getObjVal? "to").getNat?
    path := ← list (← j.getObjVal? "path") (step labels) }

def evidence (labels : Array Label) (j : Json) : Except String Evidence := do
  let hypothesis ← match ← (← j.getObjVal? "hypothesis").getStr? with
    | "transitive" => pure Hypothesis.transitive
    | "within" => pure .within
    | "empty" => pure .empty
    | h => throw s!"no hypothesis is {h}"
  return {
    hypothesis
    letter := ← labelAt labels (← j.getObjVal? "letter")
    automaton := ← nfaWith (labelAt labels) (← j.getObjVal? "automaton")
    word := ← list (← j.getObjVal? "word") (labelAt labels)
    roles := (← list (← j.getObjVal? "roles") role).toArray
    copies := (← list (← j.getObjVal? "copies") (copyOf labels)).toArray
    inclusions := ← list (← j.getObjVal? "inclusions") fun i => do
      let (a, b) ← pair i
      return (← labelAt labels a, ← labelAt labels b) }

def pass (labels : Array Label) (j : Json) : Except String Pass := do
  return {
    name := ← (← j.getObjVal? "pass").getStr?
    evidence := ← match j.getObjVal? "evidence" with
      | .ok e => some <$> evidence labels e
      | .error _ => pure none
    result := ← nfaWith (labelAt labels) (← j.getObjVal? "result") }

def chain (j : Json) : Except String Chain := do
  let labels := (← list (← j.getObjVal? "labels") label).toArray
  return {
    start := ← nfaWith (labelAt labels) (← j.getObjVal? "start")
    passes := ← list (← j.getObjVal? "passes") (pass labels) }

/-- An optional string field. -/
def optString (j : Json) (k : String) : Except String (Option String) :=
  match j.getObjVal? k with
  | .ok v => some <$> v.getStr?
  | .error _ => pure none

def entry (s : String) : Except String Entry := do
  let j ← Json.parse s
  return {
    file := (← optString j "file").getD ""
    constraint := (← optString j "constraint").getD ""
    mutation := ← optString j "mutation"
    verdict := ← optString j "verdict"
    cert := ← certificate j
    chain := ← match j.getObjVal? "chain" with
      | .ok c => some <$> chain c
      | .error _ => pure none }

end KaterCert.Read
