import KaterCert.Read
import KaterCert.Chain
import KaterCert.Exp
import KaterCert.Builtin

/-!
# Reading the evidence of whole proofs

The evidence of an assertion as `kater-oracle evidence --json` writes it
(`tests/oracle/Evidence.cpp`): the assertion's constraint, the module's
`disjoint` declarations, the per-location variants of its relations, its
assumptions, and for each inclusion Kater proved, the expressions, the
automata between the passes of the left side, the chain of passes of the
right side, with the evidence of its saturations (as in the certificates'
JSON, `Read.chain`), and the final certificate.

An expression is `{"label": LETTER}`, `{"alt": [E, ...]}`, `{"seq": [E,
...]}`, `{"star": E}`, `{"plus": E}`, `{"opt": E}` or `{"rec": {"relation":
ID, "relations": [ID, ...], "defs": [E, ...]}}`; lists fold into the binary
`Exp` (an empty sequence is the identity, an empty alternative `0`). A `rec`
is a `fix` of its definitions, in which a letter of one of the relations it
defines is a reference to it (`ref`), and must have no checks and not be
inverted, as Kater's `CharRE::expandOnNFA` ignores them. `and`, `minus` and
`rot` do not read: `toNFA` rejects them.

The evidence of an extensibility check, as `kater-oracle evidence --export`
writes it, has the expression of the constraint, whether a cycle is one of
its words, the module's `ppo` and `pporf`, the automaton of the constraint
the check takes the exits from (`cycles`), and an inclusion for each words
automaton: as above, but with no left-hand side's expression, and the steps
of its left side the words automaton (`words`) and the automaton of the
final check (`leftFinal`).

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

/-- A step of the left side of an inclusion check: the automaton a stage of
`checkInclusion` made. -/
structure LeftStep where
  stage : String
  nfa : NFA Label
  /-- For each state, the states of the step before it stands for: a hint
  for the search, which the proofs do not need. -/
  origins : Array (List Nat) := #[]

instance : Inhabited (NFA Label) := ⟨{ outs := #[], accepting := #[], start := [] }⟩
instance : Inhabited LeftStep := ⟨{ stage := "", nfa := default }⟩

/-- The evidence of an inclusion `checkInclusion` proved: its sides, the
steps of the left side, the chain of passes of the right side with the
origins of its automata (hints, as for the steps), and the certificate. -/
structure Inclusion where
  lhs : Exp
  rhs : Exp
  sameEnds : Bool
  rotated : Bool
  steps : List LeftStep
  chain : Chain
  chainOrigins : List (Array (List Nat))
  cert : Certificate

/-- An assumption of the module, as declared. `saturated` if the theory did
not take it in; `temporary` if the exporter made it for a while (an `unless`
clause); its constraint does not read if it is of a form the checkers do not
support. -/
structure Assumption where
  text : String
  builtin : Bool
  saturated : Bool
  temporary : Bool := false
  constraint : Except String Constraint

/-- What the evidence says of a module: its `disjoint` declarations, the
per-location variants of its relations, and its assumptions. -/
structure Module where
  disjoint : List (List Int)
  perLoc : List (Int × Int)
  assumptions : Array Assumption

/-- The evidence of an assertion. -/
structure Evidence where
  file : String
  assertion : String
  constraint : Constraint
  disjoint : List (List Int)
  perLoc : List (Int × Int)
  assumptions : Array Assumption
  inclusions : List Inclusion

def Evidence.module (ev : Evidence) : Module := ⟨ev.disjoint, ev.perLoc, ev.assumptions⟩

/-- The evidence of an inclusion `decideExitWords` proved: whether its words
go back to the event, its right-hand side, the words automaton Kater built
(`toEndOfWord`), with the states of `cycles` its states copy as origins, the
automaton of the final check, with origins in the words, the chain of passes
of the right side with the origins of its automata, and the certificate. -/
structure WordsInclusion where
  backToEvent : Bool
  rhs : Exp
  words : LeftStep
  final : LeftStep
  chain : Chain
  chainOrigins : List (Array (List Nat))
  cert : Certificate

/-- The evidence of an extensibility check (`Checker::ExtensibilityEvidence`):
the claim, the expression whose cycles it is about (`single`: of one word),
the module's `ppo` and the prefix relation `pporf` made of it, the automaton
of the expression the exits are taken from, the inclusions of its words,
and the module. -/
structure Extensibility where
  file : String
  claim : String
  re : Exp
  single : Bool
  ppo : Exp
  pporf : Exp
  cycles : NFA Label
  words : List WordsInclusion
  module : Module

def origins (j : Json) : Except String (Array (List Nat)) :=
  (·.toArray) <$> list j fun l => list l Json.getNat?

def leftStep (j : Json) : Except String LeftStep := do
  return {
    stage := ← (← j.getObjVal? "stage").getStr?
    nfa := ← nfa (← j.getObjVal? "nfa")
    origins := ← origins (← j.getObjVal? "origins") }

def inclusion (j : Json) : Except String Inclusion := do
  return {
    lhs := ← exp (← j.getObjVal? "lhs")
    rhs := ← exp (← j.getObjVal? "rhs")
    sameEnds := ← (← j.getObjVal? "sameEnds").getBool?
    rotated := ← (← j.getObjVal? "rotated").getBool?
    steps := ← list (← j.getObjVal? "steps") leftStep
    chain := ← chain (← j.getObjVal? "chain")
    chainOrigins := ← list (← j.getObjVal? "chainOrigins") origins
    cert := ← certificate (← j.getObjVal? "certificate") }

def assumption (j : Json) : Except String Assumption := do
  return {
    text := ← (← j.getObjVal? "text").getStr?
    builtin := ← (← j.getObjVal? "builtin").getBool?
    saturated := ← (← j.getObjVal? "saturated").getBool?
    temporary := match j.getObjVal? "temporary" with
      | .ok t => t.getBool?.toOption.getD false
      | .error _ => false
    constraint := constraint (← j.getObjVal? "constraint") }

def module (j : Json) : Except String Module := do
  return {
    disjoint := ← list (← j.getObjVal? "disjoint") fun d => list d Json.getInt?
    perLoc := ← list (← j.getObjVal? "perLoc") fun p => do
      let (r, v) ← pair p
      return (← r.getInt?, ← v.getInt?)
    assumptions := (← list (← j.getObjVal? "assumptions") assumption).toArray }

def evidenceOf (j : Json) : Except String Evidence := do
  let m ← module j
  return {
    file := ← (← j.getObjVal? "file").getStr?
    assertion := ← (← j.getObjVal? "assertion").getStr?
    constraint := ← constraint (← j.getObjVal? "constraint")
    disjoint := m.disjoint
    perLoc := m.perLoc
    assumptions := m.assumptions
    inclusions := ← list (← j.getObjVal? "inclusions") inclusion }

def evidence (s : String) : Except String Evidence := do
  evidenceOf (← Json.parse s)

/-- An inclusion of `decideExitWords`: no left-hand side's expression, and
the steps of its left side the words and the final automaton. -/
def wordsInclusion (j : Json) : Except String WordsInclusion := do
  let i ← j.getObjVal? "inclusion"
  if let .ok l := i.getObjVal? "lhs" then
    unless l matches .null do
      throw "the inclusion of a words automaton has a left-hand side's expression"
  match ← list (← i.getObjVal? "steps") leftStep with
  | [w, f] =>
    unless w.stage == "words" && f.stage == "leftFinal" do
      throw s!"the steps of a words inclusion are {w.stage} and {f.stage}"
    return {
      backToEvent := ← (← j.getObjVal? "backToEvent").getBool?
      rhs := ← exp (← i.getObjVal? "rhs")
      words := w
      final := f
      chain := ← chain (← i.getObjVal? "chain")
      chainOrigins := ← list (← i.getObjVal? "chainOrigins") origins
      cert := ← certificate (← i.getObjVal? "certificate") }
  | _ => throw "a words inclusion's steps are not the words and the final automaton"

def extensibilityOf (j : Json) : Except String Extensibility := do
  let x ← j.getObjVal? "extensibility"
  return {
    file := ← (← j.getObjVal? "file").getStr?
    claim := ← (← j.getObjVal? "claim").getStr?
    re := ← exp (← x.getObjVal? "re")
    single := ← (← x.getObjVal? "single").getBool?
    ppo := ← exp (← x.getObjVal? "ppo")
    pporf := ← exp (← x.getObjVal? "pporf")
    cycles := ← nfa (← x.getObjVal? "cycles")
    words := ← list (← x.getObjVal? "words") wordsInclusion
    module := ← module j }

/-- A file of evidence: of an assertion (or a claim an export rests on), or
of an extensibility check. -/
inductive File where
  | assertion (ev : Evidence)
  | extensibility (x : Extensibility)

def file (s : String) : Except String File := do
  let j ← Json.parse s
  match j.getObjVal? "extensibility" with
  | .ok _ => return .extensibility (← extensibilityOf j)
  | .error _ => return .assertion (← evidenceOf j)

end KaterCert.ReadChain
