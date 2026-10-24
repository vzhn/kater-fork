import KaterCert.Checker
import KaterCert.Conditions

/-!
# Soundness of the checker

If `check` accepts a certificate, the certificate meets the four conditions;
so if each of its letter inclusions holds, the left automaton's relation is
within the right one's.
-/

namespace KaterCert

universe u

namespace Certificate

variable {c : Certificate}

theorem orElse_eq_none {α : Type} {a b : Option α} :
    (a <|> b) = none ↔ a = none ∧ b = none := by
  cases a <;> simp [HOrElse.hOrElse, OrElse.orElse, Option.orElse]

theorem simulates_lt {s p : Nat} (h : c.simulates s p = true) :
    s < c.lhs.size ∧ p < c.lhs.size := by
  simp only [simulates, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem mem_above {a b : Label} (h : b ∈ c.above a) : (a, b) ∈ c.inclusions := by
  simp only [above, List.mem_filterMap] at h
  obtain ⟨⟨x, y⟩, hmem, hf⟩ := h
  by_cases hx : x = a
  · subst hx
    simp only [beq_self_eq_true, ite_true, Option.some.injEq] at hf
    exact hf ▸ hmem
  · simp [hx] at hf

theorem mem_next {a : Label} {P : List Nat} {q' : Nat} (h : q' ∈ c.next a P) :
    ∃ q ∈ P, ∃ b, (b, q') ∈ c.rhs.trans q ∧ (a = b ∨ (a, b) ∈ c.inclusions) := by
  simp only [next, List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨q, hq, ⟨b, q''⟩, hmem, hf⟩ := h
  by_cases hm : (a == b || (c.above a).any (· == b)) = true
  · simp only [hm, ite_true, Option.some.injEq] at hf
    subst hf
    refine ⟨q, hq, b, hmem, ?_⟩
    simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hm
    rcases hm with rfl | ⟨b', hb', rfl⟩
    · exact .inl rfl
    · exact .inr (mem_above hb')
  · simp [hm] at hf

theorem mem_byState {s : Nat} {Q : List Nat} (h : Q ∈ c.byState.getD s []) :
    (s, Q) ∈ c.pairs := by
  simp only [byState, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_range] at h
  split at h
  · simp only [Option.map_some, Option.getD_some, List.mem_filterMap] at h
    obtain ⟨⟨p, P⟩, hmem, hf⟩ := h
    by_cases hps : p = s
    · subst hps
      simp only [beq_self_eq_true, ite_true, Option.some.injEq] at hf
      exact hf ▸ hmem
    · simp [hps] at hf
  · simp at h

theorem covered_spec {p : Nat} {Q : List Nat} (h : c.covered c.byState p Q = true) :
    ∃ s Q', c.simulates s p = true ∧ (s, Q') ∈ c.pairs ∧ ∀ q ∈ Q', q ∈ Q := by
  simp only [covered, List.any_eq_true, Bool.and_eq_true, List.all_eq_true,
    beq_iff_eq] at h
  obtain ⟨s, _, hsim, Q', hQ', hsub⟩ := h
  refine ⟨s, Q', hsim, mem_byState hQ', fun q hq => ?_⟩
  obtain ⟨x, hx, rfl⟩ := hsub q hq
  exact hx

/-- What the simulation check establishes. -/
theorem simulation_spec (h : c.simulationError = none) {s p : Nat}
    (hsp : c.simulates s p = true) (hne : s ≠ p) :
    (c.lhs.isAccepting p = true → c.lhs.isAccepting s = true) ∧
      ∀ a p', (a, p') ∈ c.lhs.trans p →
        ∃ s', (a, s') ∈ c.lhs.trans s ∧ c.simulates s' p' = true := by
  obtain ⟨hs, hp⟩ := simulates_lt hsp
  unfold simulationError at h
  rw [List.findSome?_eq_none_iff] at h
  have h := h p (List.mem_range.mpr hp)
  split at h
  · exact absurd h (by simp)
  rw [List.findSome?_eq_none_iff] at h
  have h := h s (List.mem_range.mpr hs)
  have hskip : (s == p || !c.simulates s p) = false := by simp [hne, hsp]
  rw [hskip] at h
  simp only [Bool.false_eq_true, ite_false] at h
  split at h
  · exact absurd h (by simp)
  rename_i hacc
  split at h
  · exact absurd h (by simp)
  rename_i hfollow
  constructor
  · intro hpacc
    simp only [hpacc, Bool.true_and, Bool.not_eq_true'] at hacc
    simpa using hacc
  · intro a p' ht
    simp only [Bool.not_eq_true, Bool.not_eq_false', List.all_eq_true] at hfollow
    have hf := hfollow (a, p') ht
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hf
    obtain ⟨⟨b, s'⟩, hmem, hb, hsim⟩ := hf
    subst hb
    exact ⟨s', hmem, hsim⟩

/-- An accepted certificate meets the four conditions, with `simulates` as
the simulation, and a letter matched by itself and by the letters the
inclusions put it in. -/
theorem conditions (h : c.check = none) :
    Conditions c.lhs c.rhs (fun a b => a = b ∨ (a, b) ∈ c.inclusions)
      (fun s p => c.simulates s p = true) c.pairs := by
  unfold check at h
  split at h
  · exact absurd h (by simp)
  simp only [orElse_eq_none] at h
  obtain ⟨hsim, -, -, hstart, hpair⟩ := h
  have hpairs : ∀ p P, (p, P) ∈ c.pairs →
      (c.lhs.isAccepting p && !P.any c.rhs.isAccepting) = false ∧
        ∀ a p', (a, p') ∈ c.lhs.trans p → c.covered c.byState p' (c.next a P) = true := by
    intro p P hmem
    unfold pairError at hpair
    rw [List.findSome?_eq_none_iff] at hpair
    have h := hpair (p, P) hmem
    simp only at h
    split at h
    · exact absurd h (by simp)
    rename_i hacc
    split at h
    · exact absurd h (by simp)
    rename_i hsteps
    refine ⟨by simpa using hacc, fun a p' ht => ?_⟩
    simp only [Bool.not_eq_true, Bool.not_eq_false', List.all_eq_true] at hsteps
    exact hsteps (a, p') ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s p hsp hne
    exact (simulation_spec hsim hsp hne).1
  · intro s p hsp hne
    exact (simulation_spec hsim hsp hne).2
  · intro p hp
    unfold startError at hstart
    rw [List.findSome?_eq_none_iff] at hstart
    have h := hstart p hp
    split at h
    · rename_i hcov
      exact covered_spec hcov
    · exact absurd h (by simp)
  · intro p P hmem hacc
    have h := (hpairs p P hmem).1
    simp only [hacc, Bool.true_and, Bool.not_eq_false', List.any_eq_true] at h
    exact h
  · intro p P hmem a p' ht
    obtain ⟨s, Q, hsim, hsQ, hQ⟩ := covered_spec ((hpairs p P hmem).2 a p' ht)
    exact ⟨s, Q, hsim, hsQ, fun q' hq' => mem_next (hQ q' hq')⟩

/-- **Soundness.** If `check` accepts a certificate, and each of the
certificate's letter inclusions holds in the interpretation `I` of letters,
then the left automaton's relation is within the right one's. -/
theorem check_sound {E : Type u} (c : Certificate) (h : c.check = none)
    (I : Label → Rel E) (hinc : ∀ a b, (a, b) ∈ c.inclusions → Rel.Sub (I a) (I b)) :
    Rel.Sub (c.lhs.denote I) (c.rhs.denote I) := by
  refine (conditions h).sound I fun a b hab => ?_
  rcases hab with rfl | hmem
  · exact Rel.Sub.refl _
  · exact hinc a b hmem

/-- The same, with letters meaning what they mean in Kater: `[pre];r;[post]`
and `[pre]`, over any meaning `M` of the base relations and predicates. -/
theorem check_sound_interp {E : Type u} (c : Certificate) (h : c.check = none)
    (M : Interp E)
    (hinc : ∀ a b, (a, b) ∈ c.inclusions → Rel.Sub (a.denote M) (b.denote M)) :
    Rel.Sub (c.lhs.denote (Label.denote M)) (c.rhs.denote (Label.denote M)) :=
  check_sound c h (Label.denote M) hinc

end Certificate

end KaterCert

/-! The proof rests on Lean's standard axioms and nothing else: `lake build`
fails if a `sorry` or a new axiom creeps in. -/

/--
info: 'KaterCert.Certificate.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms KaterCert.Certificate.check_sound

/--
info: 'KaterCert.Certificate.check_sound_interp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms KaterCert.Certificate.check_sound_interp
