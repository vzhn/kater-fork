import Lean.Data.Json
import KaterCert.Checker

/-!
# Reading certificates

Certificates as `kater-oracle certify --json` writes them
(`tests/oracle/Certificate.cpp`). A letter is
`{"relation": [id, inverse] or null, "pre": [[id, complement], ...], "post": [...]}`;
an automaton is `{"states": n, "starting": [...], "accepting": [...],
"transitions": [[source, letter, destination], ...]}`; row p of the
simulation lists, as 0s and 1s, which states simulate p. Fields the checker
does not need (the letters' text) are ignored.

What is read here is trusted to be what Kater wrote: the proof is about the
`Certificate` this produces.
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

def nfa (j : Json) : Except String (NFA Label) := do
  let n ← (← j.getObjVal? "states").getNat?
  let mut outs : Array (Array (Label × Nat)) := Array.replicate n #[]
  for t in ← (← j.getObjVal? "transitions").getArr? do
    let a ← t.getArr?
    unless a.size = 3 do throw s!"a transition is [source, letter, destination]: {t.compress}"
    let src ← a[0]!.getNat?
    unless src < n do throw s!"a transition from no state: {t.compress}"
    outs := outs.modify src (·.push (← label a[1]!, ← a[2]!.getNat?))
  let mut accepting := Array.replicate n false
  for q in ← list (← j.getObjVal? "accepting") Json.getNat? do
    unless q < n do throw s!"accepting state {q} is not a state"
    accepting := accepting.set! q true
  return {
    outs := outs.map Array.toList
    accepting
    start := ← list (← j.getObjVal? "starting") Json.getNat? }

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
    cert := ← certificate j }

end KaterCert.Read
