import KaterCert.Label

/-!
# What the checkers ask of the theory

Kater's decision procedure rests on facts about the base relations and
predicates that its `Theory` states: which predicates imply which, which
predicates no event satisfies together, which relations are within which,
their domains and codomains, their per-location variants, and which relations
relate only events on the same location. A `Theory` here answers the same
questions, and `Theory.Sound` is what it takes for its answers to be true of
an interpretation.

The checkers ask only a `Theory`, and their soundness theorems assume it is
sound. The theory they are run with is Lean's own, not Kater's, and the model
proves it sound of every graph (`Model`): the facts stop being hypotheses.

Letter inclusion (`labelIncl`, `entails`) is Kater's (`Theory::isIncludedIn`
of letters, predicate sets and predicates). This mirrors the C++ region
`LetterInclusion` (`src/Theory.cpp`): `scripts/check-mirrors.sh` reports when
it changes.
-/

namespace KaterCert

universe u

structure Theory where
  /-- `p` implies `q`. -/
  predIncl : Predicate → Predicate → Bool
  /-- No event satisfies all of these predicates. -/
  unsat : List Predicate → Bool
  /-- `r` is within `s`. -/
  relIncl : Relation → Relation → Bool
  /-- Predicates that hold where an `r` step starts. -/
  dom : Relation → List Predicate
  /-- Predicates that hold where an `r` step ends. -/
  codom : Relation → List Predicate
  /-- The per-location variant of `r`, in the same direction. -/
  perLoc : Relation → Option Relation
  /-- `r` relates only events on the same location. -/
  keepsLoc : Relation → Bool
  /-- `r` relates every event to itself. -/
  reflexive : Relation → Bool

namespace Theory

variable {E : Type u}

/-- What it takes for a theory's answers to be true of `M`, with `loc` as the
relation of being on the same location: an equivalence, as every event is on
the same location as itself. -/
structure Sound (θ : Theory) (M : Interp E) (loc : Rel E) : Prop where
  predIncl : ∀ p q, θ.predIncl p q = true → ∀ e, p.Holds M e → q.Holds M e
  unsat : ∀ ps, θ.unsat ps = true → ∀ e, ¬ Checks M ps e
  relIncl : ∀ r s, θ.relIncl r s = true → Rel.Sub (r.denote M) (s.denote M)
  dom : ∀ r, ∀ p ∈ θ.dom r, ∀ x y, r.denote M x y → p.Holds M x
  codom : ∀ r, ∀ p ∈ θ.codom r, ∀ x y, r.denote M x y → p.Holds M y
  loc_refl : ∀ x, loc x x
  loc_symm : ∀ x y, loc x y → loc y x
  loc_trans : ∀ x y z, loc x y → loc y z → loc x z
  perLoc : ∀ r r', θ.perLoc r = some r' → ∀ x y, r.denote M x y → loc x y → r'.denote M x y
  keepsLoc : ∀ r, θ.keepsLoc r = true → ∀ x y, r.denote M x y → loc x y
  reflexive : ∀ r, θ.reflexive r = true → ∀ x, r.denote M x x

/-- The tests `K` entail the tests `U`: each test of `U` is one of `K` or
follows from one of them. -/
def entails (θ : Theory) (K U : List Predicate) : Bool :=
  U.all fun u => K.any fun k => k == u || θ.predIncl k u

/-- Kater's letter inclusion (`Theory::isIncludedIn` of two letters): the
checks of `a` entail those of `b`, and `a`'s relation is within `b`'s. A
predicate is within a relation that relates every event to itself. -/
def labelIncl (θ : Theory) (a b : Label) : Bool :=
  match a.rel, b.rel with
  | none, none => θ.entails a.pre b.pre
  | none, some s => θ.reflexive s && θ.entails a.pre b.pre && θ.entails a.pre b.post
  | some r, some s => θ.entails a.pre b.pre && θ.relIncl r s && θ.entails a.post b.post
  | some _, none => false

variable {θ : Theory} {M : Interp E} {loc : Rel E}

theorem Sound.entails (h : θ.Sound M loc) {K U : List Predicate} (he : θ.entails K U = true)
    {e : E} (hK : Checks M K e) : Checks M U e := by
  intro u hu
  simp only [Theory.entails, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
    beq_iff_eq] at he
  obtain ⟨k, hk, hku⟩ := he u hu
  rcases hku with rfl | hku
  · exact hK k hk
  · exact h.predIncl k u hku e (hK k hk)

theorem Sound.labelIncl (h : θ.Sound M loc) {a b : Label} (hab : θ.labelIncl a b = true) :
    Rel.Sub (a.denote M) (b.denote M) := by
  intro x y hxy
  rcases a with ⟨_ | r, apre, apost⟩ <;> rcases b with ⟨_ | s, bpre, bpost⟩
  · simp only [Theory.labelIncl] at hab
    simp only [Label.denote] at hxy ⊢
    exact ⟨hxy.1, h.entails hab hxy.2⟩
  · simp only [Theory.labelIncl, Bool.and_eq_true] at hab
    simp only [Label.denote] at hxy ⊢
    obtain ⟨rfl, hpre⟩ := hxy
    exact ⟨h.entails hab.1.2 hpre, h.reflexive _ hab.1.1 x, h.entails hab.2 hpre⟩
  · simp [Theory.labelIncl] at hab
  · simp only [Theory.labelIncl, Bool.and_eq_true] at hab
    simp only [Label.denote] at hxy ⊢
    obtain ⟨hpre, hr, hpost⟩ := hxy
    exact ⟨h.entails hab.1.1 hpre, h.relIncl _ _ hab.1.2 x y hr, h.entails hab.2 hpost⟩

end Theory

end KaterCert
