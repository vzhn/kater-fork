import KaterCert.Label
import KaterCert.NFA

/-!
# The checker

Kater's certificate of an inclusion between two automata
(`Checker::Certificate`), and `check`, the checker of
`tests/oracle/Certificate.cpp` (`checkCertificate`): the same conditions in
the same order, with the same messages.

This mirrors the C++ regions `Certificate` (`src/Checker.hpp`) and
`checkCertificate` (`tests/oracle/Certificate.cpp`): `scripts/check-mirrors.sh`
reports when they change.
-/

namespace KaterCert

/-- What the proof of `lhs ⊆ rhs` rests on: the simulation Kater used on the
left automaton, the pairs (left state, set of right states) it explored, and
the letter inclusions it took from the theory. Kater's certificate also has
the chain of passes `rhs` came by, which `Chain` (`KaterCert/Chain.lean`)
has and checks apart. -/
structure Certificate where
  lhs : NFA Label
  rhs : NFA Label
  /-- `simulation[simulated * lhs.size + simulator]` -/
  simulation : Array Bool
  pairs : List (Nat × List Nat)
  /-- `(a, b)`: letter `a` is included in letter `b`. -/
  inclusions : List (Label × Label)

namespace Certificate

variable (c : Certificate)

/-- Whether `s` simulates `p`. A number that is not a left state simulates
nothing and is simulated by nothing (Kater's states are all in range, so this
only matters for ill-formed input). -/
def simulates (s p : Nat) : Bool :=
  s < c.lhs.size && p < c.lhs.size &&
    c.simulation.getD (p * c.lhs.size + s) false

/-- The letters that the certificate's inclusions put `a` in. -/
def above (a : Label) : List Label :=
  c.inclusions.filterMap fun (x, y) => if x == a then some y else none

/-- The right states that the states `P` reach by the letters that match `a`:
`a` itself, and the letters it is included in. -/
def next (a : Label) (P : List Nat) : List Nat :=
  let above := c.above a
  P.flatMap fun q =>
    (c.rhs.trans q).filterMap fun (b, q') =>
      if a == b || above.any (· == b) then some q' else none

/-- The sets of right states paired with each left state. -/
def byState : Array (List (List Nat)) :=
  (Array.range c.lhs.size).map fun s =>
    c.pairs.filterMap fun (p, P) => if p == s then some P else none

/-- Whether a pair subsumes (p, Q): some pair (s, Q') with s simulating p and
Q' ⊆ Q. `bs` is `c.byState`, computed once. -/
def covered (bs : Array (List (List Nat))) (p : Nat) (Q : List Nat) : Bool :=
  (List.range c.lhs.size).any fun s =>
    c.simulates s p && (bs.getD s []).any fun Q' => Q'.all fun q => Q.any (· == q)

/-- Condition (1), the simulation: a simulator accepts where the simulated
state does, and follows each of its steps into a simulating state; and it is
reflexive and transitive, which the proof does not need. -/
def simulationError : Option String :=
  (List.range c.lhs.size).findSome? fun p =>
    if !c.simulates p p then some s!"the simulation is not reflexive at {p}" else
    (List.range c.lhs.size).findSome? fun s =>
      if s == p || !c.simulates s p then none
      else if c.lhs.isAccepting p && !c.lhs.isAccepting s then
        some "a non-accepting state simulates an accepting one"
      else if !(c.lhs.trans p).all fun (a, p') =>
          (c.lhs.trans s).any fun (b, s') => b == a && c.simulates s' p' then
        some s!"state {s} does not simulate {p}"
      else if (List.range c.lhs.size).any fun r => c.simulates r s && !c.simulates r p then
        some "the simulation is not transitive"
      else none

/-- Negated predicates in the right automaton would make Kater's search split
letters, which the check does not model. The proof does not need this
condition either: to it, a negated predicate is a letter like any other. -/
def negatedError : Option String :=
  if c.rhs.outs.any fun ts => ts.any fun (b, _) => b.pre.any (·.complement) then
    some "the right automaton has negated predicates"
  else none

/-- Each pair is of a left state. -/
def pairsError : Option String :=
  c.pairs.findSome? fun (p, _) =>
    if p ≥ c.lhs.size then some "a pair names no left state" else none

/-- Condition (2): a pair covers each starting state. -/
def startError (bs : Array (List (List Nat))) : Option String :=
  c.lhs.start.findSome? fun p =>
    if c.covered bs p c.rhs.start then none
    else some s!"no pair covers starting state {p}"

/-- Conditions (3) and (4): each pair whose left state accepts has an
accepting right state, and each step out of a pair lands on a pair the
simulation subsumes. -/
def pairError (bs : Array (List (List Nat))) : Option String :=
  c.pairs.findSome? fun (p, P) =>
    if c.lhs.isAccepting p && !P.any c.rhs.isAccepting then
      some s!"left state {p} accepts where no right state does"
    else if !(c.lhs.trans p).all fun (a, p') => c.covered bs p' (c.next a P) then
      some s!"a step out of a pair of left state {p} lands on no subsumed pair"
    else none

/-- Why the certificate is not a proof, if it is not. -/
def check : Option String :=
  if c.simulation.size ≠ c.lhs.size * c.lhs.size then
    some "the simulation is not over the left automaton's states"
  else
    c.simulationError <|> c.negatedError <|> c.pairsError <|>
      (let bs := c.byState
       c.startError bs <|> c.pairError bs)

end Certificate

end KaterCert
