import KaterCert.NFA

/-!
# The conditions a certificate meets

The four conditions of a certificate (`doc/verification.md`, Certificates),
over any automata, any relation `sim` between the left automaton's states and
any matching `le` of letters, and the proof that they make every word of the
left automaton matched, letter by letter, by a word of the right one.

`pairs` are the pairs (left state, set of right states) the search explored.
A pair (p, P) claims that every word the left automaton accepts from p is
matched by a word the right one accepts from a state of P.
-/

namespace KaterCert

universe u

variable {L : Type}

/-- What a certificate must satisfy. -/
structure Conditions (lhs rhs : NFA L) (le : L → L → Prop) (sim : Nat → Nat → Prop)
    (pairs : List (Nat × List Nat)) : Prop where
  /-- (1) `sim` is a simulation: a simulator accepts where the simulated
  state does, -/
  sim_accepting : ∀ s p, sim s p → s ≠ p →
    lhs.isAccepting p = true → lhs.isAccepting s = true
  /-- and follows each of its steps into a state that simulates the
  destination. -/
  sim_step : ∀ s p, sim s p → s ≠ p → ∀ a p', (a, p') ∈ lhs.trans p →
    ∃ s', (a, s') ∈ lhs.trans s ∧ sim s' p'
  /-- (2) A pair covers each starting state: some (s, Q) has s simulating
  the start and Q within the right automaton's starting states. -/
  start : ∀ p ∈ lhs.start, ∃ s Q, sim s p ∧ (s, Q) ∈ pairs ∧ ∀ q ∈ Q, q ∈ rhs.start
  /-- (3) Each pair whose left state accepts has an accepting right state. -/
  accepting : ∀ p P, (p, P) ∈ pairs → lhs.isAccepting p = true →
    ∃ q ∈ P, rhs.isAccepting q = true
  /-- (4) Each step p --a--> p' out of a pair (p, P) lands on a pair the
  simulation subsumes: some (s, Q) with s simulating p' and Q within the
  states P reaches by the letters that match a. -/
  step : ∀ p P, (p, P) ∈ pairs → ∀ a p', (a, p') ∈ lhs.trans p →
    ∃ s Q, sim s p' ∧ (s, Q) ∈ pairs ∧
      ∀ q' ∈ Q, ∃ q ∈ P, ∃ b, (b, q') ∈ rhs.trans q ∧ le a b

namespace Conditions

variable {lhs rhs : NFA L} {le : L → L → Prop} {sim : Nat → Nat → Prop}
  {pairs : List (Nat × List Nat)}

/-- A simulator accepts every word the state it simulates does. Neither
reflexivity nor transitivity is needed: a state accepts what it accepts. -/
theorem simulates (h : Conditions lhs rhs le sim pairs) :
    ∀ w s p, sim s p → lhs.Accepts p w → lhs.Accepts s w := by
  intro w
  induction w with
  | nil =>
    intro s p hsp hp
    by_cases hs : s = p
    · exact hs ▸ hp
    · cases hp with
      | nil hacc => exact .nil (h.sim_accepting s p hsp hs hacc)
  | cons a w ih =>
    intro s p hsp hp
    by_cases hs : s = p
    · exact hs ▸ hp
    · cases hp with
      | cons ht hw =>
        obtain ⟨s', hs', hsim⟩ := h.sim_step s p hsp hs _ _ ht
        exact .cons hs' (ih s' _ hsim hw)

/-- A pair subsumes its run at every step: what the left automaton accepts
from the pair's left state is matched from one of its right states. -/
theorem pair (h : Conditions lhs rhs le sim pairs) :
    ∀ w p P, (p, P) ∈ pairs → lhs.Accepts p w →
      ∃ q ∈ P, ∃ w', Matches le w w' ∧ rhs.Accepts q w' := by
  intro w
  induction w with
  | nil =>
    intro p P hpair hp
    cases hp with
    | nil hacc =>
      obtain ⟨q, hq, hqacc⟩ := h.accepting p P hpair hacc
      exact ⟨q, hq, [], .nil, .nil hqacc⟩
  | cons a w ih =>
    intro p P hpair hp
    cases hp with
    | @cons _ _ p' _ ht hw =>
      obtain ⟨s, Q, hsim, hsQ, hQ⟩ := h.step p P hpair a p' ht
      obtain ⟨q', hq', w', hm, hacc⟩ := ih s Q hsQ (h.simulates w s p' hsim hw)
      obtain ⟨q, hq, b, hb, hab⟩ := hQ q' hq'
      exact ⟨q, hq, b :: w', .cons hab hm, .cons hb hacc⟩

/-- Every word the left automaton accepts is matched, letter by letter, by a
word the right one accepts. -/
theorem language (h : Conditions lhs rhs le sim pairs) {p : Nat} {w : List L}
    (hp : p ∈ lhs.start) (hw : lhs.Accepts p w) :
    ∃ q ∈ rhs.start, ∃ w', Matches le w w' ∧ rhs.Accepts q w' := by
  obtain ⟨s, Q, hsim, hsQ, hQ⟩ := h.start p hp
  obtain ⟨q, hq, w', hm, hacc⟩ := h.pair w s Q hsQ (h.simulates w s p hsim hw)
  exact ⟨q, hQ q hq, w', hm, hacc⟩

/-- If each letter is within the letters that match it, the left automaton's
relation is within the right one's. -/
theorem sound {E : Type u} (h : Conditions lhs rhs le sim pairs) (I : L → Rel E)
    (hle : ∀ a b, le a b → Rel.Sub (I a) (I b)) :
    Rel.Sub (lhs.denote I) (rhs.denote I) := by
  intro x y ⟨p, hp, w, hw, hxy⟩
  obtain ⟨q, hq, w', hm, hacc⟩ := h.language hp hw
  exact ⟨q, hq, w', hacc, hm.wordRel_sub hle x y hxy⟩

end Conditions

end KaterCert
