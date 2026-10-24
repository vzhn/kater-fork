import KaterCert.Rel

/-!
# Letters

Kater's letters (`TransLabel`) and what they mean. A letter is either a
predicate `[pre]`, which relates events only to themselves, or
`[pre];r;[post]` for a relation `r`, possibly inverted, and sets of
predicates `pre` and `post`, each possibly complemented.

The base relations and predicates are uninterpreted: an `Interp` gives them
any meaning, as an execution graph does. What the builtins mean in GenMC's
graphs is not modeled here, so the letter inclusions a certificate rests on
stay hypotheses.

This mirrors the C++ regions `TransLabel`, `Relation`, `Predicate`,
`PredicateSet` (`src/`) and `LetterSemantics` (`tests/oracle/Semantics.cpp`):
`scripts/check-mirrors.sh` reports when they change.
-/

namespace KaterCert

universe u

/-- Kater's `Predicate`: an id (builtins non-negative, user predicates
negative), and whether it is complemented. -/
structure Predicate where
  id : Int
  complement : Bool
  deriving DecidableEq, Repr

/-- Kater's `Relation`: an id (builtins non-negative, user relations
negative), and whether it is inverted. -/
structure Relation where
  id : Int
  inverse : Bool
  deriving DecidableEq, Repr

/-- Kater's `TransLabel`: `[pre];rel;[post]`, or the predicate `[pre]` when it
has no relation (Kater gives predicates no `post`). The predicate lists are in
Kater's order, so equal letters are equal lists. -/
structure Label where
  rel : Option Relation
  pre : List Predicate
  post : List Predicate
  deriving DecidableEq, Repr

/-- A meaning for the base relations and predicates, by id. -/
structure Interp (E : Type u) where
  rel : Int → Rel E
  pred : Int → E → Prop

variable {E : Type u}

/-- Whether a predicate holds of an event. -/
def Predicate.Holds (M : Interp E) (p : Predicate) (e : E) : Prop :=
  if p.complement then ¬ M.pred p.id e else M.pred p.id e

/-- Whether every predicate of a set holds of an event. -/
def Checks (M : Interp E) (ps : List Predicate) (e : E) : Prop :=
  ∀ p ∈ ps, p.Holds M e

/-- The relation a base relation denotes. -/
def Relation.denote (M : Interp E) (r : Relation) : Rel E :=
  fun x y => if r.inverse then M.rel r.id y x else M.rel r.id x y

/-- The relation a letter denotes, as the oracle's `Semantics::eval` reads
it. -/
def Label.denote (M : Interp E) (l : Label) : Rel E :=
  match l.rel with
  | none => fun x y => x = y ∧ Checks M l.pre x
  | some r => fun x y => Checks M l.pre x ∧ r.denote M x y ∧ Checks M l.post y

/-- A predicate is a subset of the identity. -/
theorem Label.denote_sub_id (M : Interp E) {l : Label} (h : l.rel = none) :
    Rel.Sub (l.denote M) Rel.id := by
  intro x y hxy
  simp only [Label.denote, h] at hxy
  exact hxy.1

end KaterCert
