import KaterCert.NFA

/-!
# Paths

The paths of an automaton, and what the words that reach a state relate:
`past A q`, the pairs a word from a starting state of `A` to `q` relates.
An automaton denotes what its accepting states' pasts relate.
-/

namespace KaterCert

universe u

variable {L : Type} {E : Type u}

namespace NFA

/-- `A.Path q w q'`: from `q`, `A` reads `w` into `q'`. -/
inductive Path (A : NFA L) : Nat → List L → Nat → Prop
  | nil {q} : A.Path q [] q
  | snoc {q w p a p'} : A.Path q w p → (a, p') ∈ A.trans p → A.Path q (w ++ [a]) p'

/-- The pairs that a word from a starting state of `A` to `q` relates. -/
def past (I : L → Rel E) (A : NFA L) (q : Nat) : Rel E :=
  fun x y => ∃ s ∈ A.start, ∃ w, A.Path s w q ∧ wordRel I w x y

theorem Path.cons {A : NFA L} {q a q₁ w q'} (ht : (a, q₁) ∈ A.trans q) (hp : A.Path q₁ w q') :
    A.Path q (a :: w) q' := by
  induction hp with
  | nil => exact .snoc (w := []) .nil ht
  | snoc _ ht' ih => exact .snoc (w := a :: _) ih ht'

/-- A word an automaton accepts leads to an accepting state. -/
theorem Accepts.path {A : NFA L} {q w} (h : A.Accepts q w) :
    ∃ q', A.Path q w q' ∧ A.isAccepting q' = true := by
  induction h with
  | nil hacc => exact ⟨_, .nil, hacc⟩
  | cons ht _ ih =>
    obtain ⟨q', hp, hacc⟩ := ih
    exact ⟨q', .cons ht hp, hacc⟩

theorem Path.accepts {A : NFA L} {q w q'} (hp : A.Path q w q') :
    ∀ {v}, A.Accepts q' v → A.Accepts q (w ++ v) := by
  induction hp with
  | nil => exact fun h => h
  | snoc _ ht ih =>
    intro v hv
    rw [List.append_assoc]
    exact ih (.cons ht hv)

end NFA

theorem wordRel_append {I : L → Rel E} :
    ∀ {w v : List L} {x z : E},
      wordRel I (w ++ v) x z ↔ ∃ y, wordRel I w x y ∧ wordRel I v y z
  | [], _, x, z => by
    constructor
    · exact fun h => ⟨x, rfl, h⟩
    · intro ⟨y, hxy, h⟩
      cases hxy
      exact h
  | a :: w, v, x, z => by
    constructor
    · intro ⟨y, ha, h⟩
      obtain ⟨y', hw, hv⟩ := (wordRel_append (w := w) (v := v)).mp h
      exact ⟨y', ⟨y, ha, hw⟩, hv⟩
    · intro ⟨y', ⟨y, ha, hw⟩, hv⟩
      exact ⟨y, ha, (wordRel_append (w := w) (v := v)).mpr ⟨y', hw, hv⟩⟩

theorem wordRel_snoc {I : L → Rel E} {w : List L} {a : L} {x z : E} :
    wordRel I (w ++ [a]) x z ↔ Rel.comp (wordRel I w) (I a) x z := by
  rw [wordRel_append]
  constructor
  · intro ⟨y, hw, y', ha, hid⟩
    cases hid
    exact ⟨y, hw, ha⟩
  · intro ⟨y, hw, ha⟩
    exact ⟨y, hw, z, ha, rfl⟩

namespace NFA

variable {I : L → Rel E} {A : NFA L}

/-- A starting state is reached by the empty word. -/
theorem past_start {q : Nat} (hq : q ∈ A.start) : Rel.Sub Rel.id (A.past I q) := by
  intro x y hxy
  exact ⟨q, hq, [], .nil, hxy⟩

/-- A step leads from a state's past into its destination's. -/
theorem past_step {q a q'} (ht : (a, q') ∈ A.trans q) :
    Rel.Sub (Rel.comp (A.past I q) (I a)) (A.past I q') := by
  intro x z ⟨y, ⟨s, hs, w, hp, hw⟩, ha⟩
  exact ⟨s, hs, w ++ [a], .snoc hp ht, wordRel_snoc.mpr ⟨y, hw, ha⟩⟩

/-- What an accepting state's past relates, the automaton denotes. -/
theorem past_accepting {q : Nat} (hq : A.isAccepting q = true) :
    Rel.Sub (A.past I q) (A.denote I) := by
  intro x y ⟨s, hs, w, hp, hw⟩
  have h := hp.accepts (v := []) (.nil hq)
  rw [List.append_nil] at h
  exact ⟨s, hs, w, h, hw⟩

/-- An automaton denotes what its accepting states' pasts relate. -/
theorem denote_past {x y : E} (h : A.denote I x y) :
    ∃ q, A.isAccepting q = true ∧ A.past I q x y := by
  obtain ⟨s, hs, w, hacc, hw⟩ := h
  obtain ⟨q, hp, hq⟩ := hacc.path
  exact ⟨q, hq, s, hs, w, hp, hw⟩

/-- The pasts of `A` are within what `bound` gives each state, if `bound`
holds of the starting states and every step keeps it. -/
theorem past_bound (bound : Nat → Rel E)
    (hstart : ∀ q ∈ A.start, Rel.Sub Rel.id (bound q))
    (hstep : ∀ q a q', (a, q') ∈ A.trans q → Rel.Sub (Rel.comp (bound q) (I a)) (bound q')) :
    ∀ q, Rel.Sub (A.past I q) (bound q) := by
  intro q x y ⟨s, hs, w, hp, hw⟩
  induction hp generalizing y with
  | nil => exact hstart _ hs x y hw
  | snoc _ ht ih =>
    obtain ⟨z, hwz, ha⟩ := wordRel_snoc.mp hw
    exact hstep _ _ _ ht x y ⟨z, ih z hwz, ha⟩

end NFA

end KaterCert
