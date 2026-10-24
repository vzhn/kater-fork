import KaterCert.Rel

/-!
# Automata

Kater's automata (`NFA`): states numbered from 0, labeled transitions, and
starting and accepting states. An automaton denotes the pairs of events that
a word it accepts relates, where a word denotes the composition of its
letters, and the empty word the identity.

This mirrors the C++ region `NFASemantics` (`tests/oracle/Semantics.cpp`):
`scripts/check-mirrors.sh` reports when it changes.
-/

namespace KaterCert

universe u

/-- An automaton over letters `L`. A number that is not a state has no
transitions and does not accept. -/
structure NFA (L : Type) where
  /-- The transitions out of each state, as (letter, destination). -/
  outs : Array (List (L × Nat))
  /-- Whether each state accepts. -/
  accepting : Array Bool
  /-- The starting states. -/
  start : List Nat
  deriving DecidableEq

namespace NFA

variable {L : Type}

/-- The number of states. -/
def size (A : NFA L) : Nat := A.outs.size

/-- The transitions out of `q`. -/
def trans (A : NFA L) (q : Nat) : List (L × Nat) := A.outs.getD q []

/-- Whether `q` accepts. -/
def isAccepting (A : NFA L) (q : Nat) : Bool := A.accepting.getD q false

/-- `A.Accepts q w`: from `q`, `A` reads `w` into an accepting state. -/
inductive Accepts (A : NFA L) : Nat → List L → Prop
  | nil {q} : A.isAccepting q = true → A.Accepts q []
  | cons {q a q' w} : (a, q') ∈ A.trans q → A.Accepts q' w → A.Accepts q (a :: w)

end NFA

variable {L : Type} {E : Type u}

/-- The relation a word denotes, given the relation of each letter. -/
def wordRel (I : L → Rel E) : List L → Rel E
  | [] => Rel.id
  | a :: w => Rel.comp (I a) (wordRel I w)

/-- The relation an automaton denotes: the pairs that a word it accepts from
a starting state relates. -/
def NFA.denote (I : L → Rel E) (A : NFA L) : Rel E :=
  fun x y => ∃ q ∈ A.start, ∃ w, A.Accepts q w ∧ wordRel I w x y

/-- `Matches le w w'`: `w'` matches `w` letter by letter, each letter `a` of
`w` by a letter `b` with `le a b`. -/
inductive Matches (le : L → L → Prop) : List L → List L → Prop
  | nil : Matches le [] []
  | cons {a b w w'} : le a b → Matches le w w' → Matches le (a :: w) (b :: w')

/-- A word is within the words that match it, if each letter is within the
letters that match it. -/
theorem Matches.wordRel_sub {le : L → L → Prop} {I : L → Rel E}
    (hle : ∀ a b, le a b → Rel.Sub (I a) (I b)) :
    ∀ {w w'}, Matches le w w' → Rel.Sub (wordRel I w) (wordRel I w')
  | _, _, .nil => Rel.Sub.refl _
  | _, _, .cons hab hw => Rel.comp_mono (hle _ _ hab) (hw.wordRel_sub hle)

theorem wordRel_append (I : L → Rel E) :
    ∀ (u v : List L) {x y : E}, wordRel I (u ++ v) x y ↔ Rel.comp (wordRel I u) (wordRel I v) x y
  | [], _, _, _ => Rel.id_comp.symm
  | a :: u, v, x, y => by
    simp only [List.cons_append, wordRel]
    constructor
    · rintro ⟨z, ha, hw⟩
      obtain ⟨z', hu, hv⟩ := (wordRel_append I u v).mp hw
      exact ⟨z', ⟨z, ha, hu⟩, hv⟩
    · rintro ⟨z', ⟨z, ha, hu⟩, hv⟩
      exact ⟨z, ha, (wordRel_append I u v).mpr ⟨z', hu, hv⟩⟩

end KaterCert
