import KaterCert.Label

/-!
# Expressions and constraints

Kater's expressions (`RegExp`) as they reach `RegExp::toNFA`, and the
constraints of its assertions and assumptions, with what they mean.

`&`, `\` and `rot` are absent: `toNFA` rejects them, and the parser turns the
forms Kater supports into flags of a constraint (`A & id <= B`,
`A <= rot B`) or into other expressions (`A \ B <= C` into `A <= B | C`).
Alternatives and sequences are binary here; Kater's are lists, which a reader
folds (an empty sequence is the identity, an empty alternative `0`).
`let rec` (`MutRecRE`) is a `fix` of its definitions, in which the relations
it defines are references (`ref`), numbered as the definitions are. Kater
pushes inverses into letters, except that of a `let rec`, a `MutRecRE`
flagged flipped: that is an `inv` of the `fix`.

This mirrors the C++ region `ExpSemantics` (`tests/oracle/Semantics.cpp`), the
oracle's semantics of expressions: `scripts/check-mirrors.sh` reports when it
changes.
-/

namespace KaterCert

universe u

/-- The letter of the identity: the predicate that checks nothing. -/
def Label.eps : Label := { rel := none, pre := [], post := [] }

mutual

/-- An expression. -/
inductive Exp where
  /-- A letter (`CharRE`): `[pre];r;[post]`, or a predicate. -/
  | label (l : Label)
  /-- `0`, the empty alternative. -/
  | zero
  | alt (a b : Exp)
  | seq (a b : Exp)
  | star (a : Exp)
  | plus (a : Exp)
  /-- `a?` -/
  | opt (a : Exp)
  /-- A recursive relation of the innermost `fix`: its `i`-th definition. -/
  | ref (i : Nat)
  /-- `let rec` (`MutRecRE`): the `main`-th of the relations the definitions
  define together, in their least solution. -/
  | fix (main : Nat) (defs : Defs)
  /-- The inverse `a^-1`. -/
  | inv (a : Exp)

/-- The definitions of a `let rec`. -/
inductive Defs where
  | nil
  | cons (e : Exp) (rest : Defs)

end

deriving instance DecidableEq for Exp
deriving instance Repr for Exp

instance : Inhabited Exp := ⟨.zero⟩

namespace Defs

/-- The definitions as a list. -/
def toList : Defs → List Exp
  | .nil => []
  | .cons e es => e :: es.toList

/-- Definitions from a list. -/
def ofList : List Exp → Defs
  | [] => .nil
  | e :: es => .cons e (ofList es)

/-- The `i`-th definition; `0` if there is none. -/
def get : Defs → Nat → Exp
  | .nil, _ => .zero
  | .cons e _, 0 => e
  | .cons _ es, i + 1 => es.get i

end Defs

namespace Exp

variable {E : Type u}

mutual

/-- The relation an expression denotes, as the oracle's `Semantics::eval`
reads it, with `ρ` the relations of the innermost `fix`'s definitions. A
`fix` denotes the least solution of its definitions, reached by iterating
them from the empty relations (`Semantics::evalMutRec`). -/
def denoteIn (M : Interp E) (ρ : Nat → Rel E) : Exp → Rel E
  | .label l => l.denote M
  | .zero => Rel.empty
  | .alt a b => Rel.union (a.denoteIn M ρ) (b.denoteIn M ρ)
  | .seq a b => Rel.comp (a.denoteIn M ρ) (b.denoteIn M ρ)
  | .star a => Rel.Star (a.denoteIn M ρ)
  | .plus a => Rel.Plus (a.denoteIn M ρ)
  | .opt a => Rel.Opt (a.denoteIn M ρ)
  | .ref i => ρ i
  | .fix main defs => fun x y => ∃ n, Nat.repeat (Defs.denoteIn M · defs) n (fun _ => Rel.empty) main x y
  | .inv a => Rel.inv (a.denoteIn M ρ)

/-- The relations definitions denote, given those `ρ` of the relations they
define. -/
def _root_.KaterCert.Defs.denoteIn (M : Interp E) (ρ : Nat → Rel E) : Defs → Nat → Rel E
  | .nil, _ => Rel.empty
  | .cons e _, 0 => e.denoteIn M ρ
  | .cons _ es, i + 1 => Defs.denoteIn M ρ es i

end

/-- The relation an expression denotes. A reference outside any `fix`
relates nothing. -/
def denote (M : Interp E) : Exp → Rel E
  | .label l => l.denote M
  | .zero => Rel.empty
  | .alt a b => Rel.union (a.denote M) (b.denote M)
  | .seq a b => Rel.comp (a.denote M) (b.denote M)
  | .star a => Rel.Star (a.denote M)
  | .plus a => Rel.Plus (a.denote M)
  | .opt a => Rel.Opt (a.denote M)
  | .ref _ => Rel.empty
  | .fix main defs => (Exp.fix main defs).denoteIn M fun _ => Rel.empty
  | .inv a => Rel.inv (a.denote M)

end Exp

theorem Label.denote_eps {E : Type u} (M : Interp E) {x y : E} :
    Label.eps.denote M x y ↔ x = y := by
  simp [Label.denote, Label.eps, Checks]

/-- A constraint of an assertion or an assumption. `A & id <= B` is a subset
constraint with `sameEnds`, `A & id <= rot B` one with `rotated` as well. -/
inductive Constraint where
  | subset (lhs rhs : Exp) (sameEnds rotated : Bool)
  | equal (lhs rhs : Exp) (sameEnds rotated : Bool)
  /-- `total r`, of an assumption. -/
  | total (e : Exp)
  deriving DecidableEq, Repr, Inhabited

namespace Constraint

variable {E : Type u}

/-- What a subset constraint says. `A & id <= rot B` says that B has a cycle
if A has one (Kater's proof shows more: a rotation of each cycle of A is one
of B); `rot` without `& id` says the same, as the parser only accepts it of
an A within the identity, whose pairs are all cycles. -/
def SubsetHolds (M : Interp E) (lhs rhs : Exp) (sameEnds rotated : Bool) : Prop :=
  if rotated then (∃ x, lhs.denote M x x) → ∃ y, rhs.denote M y y
  else if sameEnds then ∀ x, lhs.denote M x x → rhs.denote M x x
  else Rel.Sub (lhs.denote M) (rhs.denote M)

/-- What a constraint says. `total r` makes r a strict total order on all
events, as the oracle reads it (Proposition 3.12 of the Kater paper). -/
def Holds (M : Interp E) : Constraint → Prop
  | .subset lhs rhs sameEnds rotated => SubsetHolds M lhs rhs sameEnds rotated
  | .equal lhs rhs sameEnds rotated =>
    SubsetHolds M lhs rhs sameEnds rotated ∧ SubsetHolds M rhs lhs sameEnds rotated
  | .total e =>
    Rel.Sub (Rel.comp (e.denote M) (e.denote M)) (e.denote M) ∧
      (∀ x, ¬ e.denote M x x) ∧ ∀ x y, x ≠ y → e.denote M x y ∨ e.denote M y x

end Constraint

end KaterCert
