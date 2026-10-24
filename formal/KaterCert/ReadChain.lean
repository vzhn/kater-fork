import KaterCert.Read
import KaterCert.Exp
import KaterCert.Builtin

/-!
# Reading the evidence of whole proofs

The evidence of an assertion as `kater-oracle evidence --json` writes it
(`tests/oracle/Evidence.cpp`): the assertion's constraint, the module's
`disjoint` declarations, the per-location variants of its relations, its
assumptions, and for each inclusion Kater proved, the expressions, the
automata between its passes and the final certificate.

An expression is `{"label": LETTER}`, `{"alt": [E, ...]}`, `{"seq": [E,
...]}`, `{"star": E}`, `{"plus": E}`, `{"opt": E}` or `{"rec": {"relation":
ID, "relations": [ID, ...], "defs": [E, ...]}}`; lists fold into the binary
`Exp` (an empty sequence is the identity, an empty alternative `0`). A `rec`
is a `fix` of its definitions, in which a letter of one of the relations it
defines is a reference to it (`ref`), and must have no checks and not be
inverted, as Kater's `CharRE::expandOnNFA` ignores them. `and`, `minus` and
`rot` do not read: `toNFA` rejects them.

What is read here is trusted to be what Kater wrote: the proofs are about
what this produces.

This mirrors the C++ region `EvidenceJSON` (`tests/oracle/Evidence.cpp`):
`scripts/check-mirrors.sh` reports when it changes.
-/

namespace KaterCert.ReadChain

open Lean (Json)
open KaterCert.Read

/-- An expression within `let rec`s that define the relations `recs`, the
innermost first. -/
partial def expIn (recs : List (List Int)) (j : Json) : Except String Exp := do
  if let .ok l := j.getObjVal? "label" then
    let l ← label l
    match l.rel, recs with
    | some r, inner :: outer =>
      match inner.findIdx? (· == r.id) with
      | some i =>
        if r.inverse || !l.pre.isEmpty || !l.post.isEmpty then
          throw s!"a recursive relation with checks or inverted: {j.compress.take 200}"
        return .ref i
      | none =>
        if outer.any (·.contains r.id) then
          throw s!"the relation of an enclosing let rec: {j.compress.take 200}"
        return .label l
    | _, _ => return .label l
  if let .ok a := j.getObjVal? "alt" then
    let ks ← (← a.getArr?).toList.mapM (expIn recs)
    return match ks with
      | [] => .zero
      | k :: ks => ks.foldl .alt k
  if let .ok a := j.getObjVal? "seq" then
    let ks ← (← a.getArr?).toList.mapM (expIn recs)
    return match ks with
      | [] => .label .eps
      | k :: ks => ks.foldl .seq k
  if let .ok k := j.getObjVal? "star" then return .star (← expIn recs k)
  if let .ok k := j.getObjVal? "plus" then return .plus (← expIn recs k)
  if let .ok k := j.getObjVal? "opt" then return .opt (← expIn recs k)
  if let .ok r := j.getObjVal? "rec" then
    let rel ← (← r.getObjVal? "relation").getInt?
    let rels ← (← (← r.getObjVal? "relations").getArr?).toList.mapM (·.getInt?)
    let defs ← (← (← r.getObjVal? "defs").getArr?).toList.mapM (expIn (rels :: recs))
    if defs.length != rels.length then
      throw s!"a let rec with more or fewer definitions than relations: {j.compress.take 200}"
    match rels.findIdx? (· == rel) with
    | some main => return .fix main (Defs.ofList defs)
    | none => throw s!"a let rec of a relation it does not define: {j.compress.take 200}"
  throw s!"unsupported expression: {j.compress.take 200}"

def exp (j : Json) : Except String Exp := expIn [] j

def sides (j : Json) : Except String (Exp × Exp × Bool × Bool) := do
  return (← exp (← j.getObjVal? "lhs"), ← exp (← j.getObjVal? "rhs"),
    ← (← j.getObjVal? "sameEnds").getBool?, ← (← j.getObjVal? "rotated").getBool?)

def constraint (j : Json) : Except String Constraint := do
  if let .ok s := j.getObjVal? "subset" then
    let (l, r, e, o) ← sides s
    return .subset l r e o
  if let .ok s := j.getObjVal? "equal" then
    let (l, r, e, o) ← sides s
    return .equal l r e o
  if let .ok t := j.getObjVal? "total" then return .total (← exp t)
  throw s!"unsupported constraint: {j.compress.take 200}"

/-- A step of an inclusion check: the automaton a stage of `checkInclusion`
made, with the assumption a saturation used. -/
structure Step where
  stage : String
  assumption : Option Nat
  nfa : NFA Label
  /-- For each state, the states of the step before it stands for: a hint
  for the search, which the proofs do not need. -/
  origins : Array (List Nat) := #[]

instance : Inhabited (NFA Label) := ⟨{ outs := #[], accepting := #[], start := [] }⟩
instance : Inhabited Step := ⟨{ stage := "", assumption := none, nfa := default }⟩

/-- The evidence of an inclusion `checkInclusion` proved. -/
structure Inclusion where
  lhs : Exp
  rhs : Exp
  sameEnds : Bool
  rotated : Bool
  steps : List Step
  cert : Certificate

/-- An assumption of the module, as declared. `saturated` if the theory did
not take it in; its constraint does not read if it is of a form the checkers
do not support. -/
structure Assumption where
  text : String
  builtin : Bool
  saturated : Bool
  constraint : Except String Constraint

/-- The evidence of an assertion. -/
structure Evidence where
  file : String
  assertion : String
  constraint : Constraint
  disjoint : List (List Int)
  perLoc : List (Int × Int)
  assumptions : Array Assumption
  inclusions : List Inclusion

def step (j : Json) : Except String Step := do
  return {
    stage := ← (← j.getObjVal? "stage").getStr?
    assumption := ← match ← j.getObjVal? "assumption" with
      | .null => pure none
      | n => some <$> n.getNat?
    nfa := ← nfa (← j.getObjVal? "nfa")
    origins := ← match j.getObjVal? "origins" with
      | .ok o => (·.toArray) <$> list o fun l => list l Json.getNat?
      | .error _ => pure #[] }

def inclusion (j : Json) : Except String Inclusion := do
  return {
    lhs := ← exp (← j.getObjVal? "lhs")
    rhs := ← exp (← j.getObjVal? "rhs")
    sameEnds := ← (← j.getObjVal? "sameEnds").getBool?
    rotated := ← (← j.getObjVal? "rotated").getBool?
    steps := ← list (← j.getObjVal? "steps") step
    cert := ← certificate (← j.getObjVal? "certificate") }

def assumption (j : Json) : Except String Assumption := do
  return {
    text := ← (← j.getObjVal? "text").getStr?
    builtin := ← (← j.getObjVal? "builtin").getBool?
    saturated := ← (← j.getObjVal? "saturated").getBool?
    constraint := constraint (← j.getObjVal? "constraint") }

def evidence (s : String) : Except String Evidence := do
  let j ← Json.parse s
  return {
    file := ← (← j.getObjVal? "file").getStr?
    assertion := ← (← j.getObjVal? "assertion").getStr?
    constraint := ← constraint (← j.getObjVal? "constraint")
    disjoint := ← list (← j.getObjVal? "disjoint") fun d => list d Json.getInt?
    perLoc := ← list (← j.getObjVal? "perLoc") fun p => do
      let (r, v) ← pair p
      return (← r.getInt?, ← v.getInt?)
    assumptions := (← list (← j.getObjVal? "assumptions") assumption).toArray
    inclusions := ← list (← j.getObjVal? "inclusions") inclusion }

end KaterCert.ReadChain
