import KaterCert.SaturationSound
import KaterCert.Soundness

/-!
# The chain from the right-hand side to the final check

How the right automaton of an inclusion check came from the right-hand side
(`Checker::Chain`): the automaton the right-hand side normalized to, and each
pass after it with the automaton it produced, the last of which is the right
automaton. A saturation comes with evidence; the other passes are trusted.
`Chain.check` is `checkChain` of `tests/oracle/Chain.cpp`: the same
conditions in the same order, with the same messages.

`Chain.sound` joins the chain to the certificate of the final check: if both
checkers accept, the certificate's left automaton denotes no more than the
automaton the right-hand side normalized to, given the certificate's letter
inclusions, each saturation's hypothesis and letter inclusions, and the
contracts of the passes without evidence.

This mirrors the C++ regions `Chain` (`src/Checker.hpp`) and `checkChain`
(`tests/oracle/Chain.cpp`): `scripts/check-mirrors.sh` reports when they
change.
-/

namespace KaterCert

universe u

/-- A pass of a chain: its name, its evidence if it is a saturation, and the
automaton it produced. -/
structure Pass where
  name : String
  evidence : Option Evidence
  result : NFA Label

/-- How the right automaton of an inclusion check came from the right-hand
side. -/
structure Chain where
  start : NFA Label
  passes : List Pass

namespace Chain

/-- The passes trusted to meet their contracts, without evidence. -/
def trusted : List String := ["normalize", "prune", "rotate"]

/-- From pass `i` on, given the automaton `last`: why the passes do not lead
to `rhs` through saturations whose evidence checks, if they do not. -/
def go (rhs : NFA Label) (i : Nat) (last : NFA Label) : List Pass → Option String
  | [] => if last = rhs then none else some "the chain does not end at the right automaton"
  | p :: ps =>
    match p.evidence with
    | some ev =>
      match ev.check last p.result with
      | some why => some s!"pass {i} ({p.name}): {why}"
      | none => go rhs (i + 1) p.result ps
    | none =>
      if trusted.contains p.name then go rhs (i + 1) p.result ps
      else some s!"pass {i} ({p.name}) has no evidence"

/-- Why the chain does not lead from its start to `rhs`, if it does not. -/
def check (ch : Chain) (rhs : NFA Label) : Option String := go rhs 0 ch.start ch.passes

/-- Each pass, with the automaton it was given. -/
def links (ch : Chain) : List (NFA Label × Pass) :=
  (ch.start :: ch.passes.map (·.result)).zip ch.passes

variable {E : Type u}

/-- What the saturations rest on, with letters read through `Mi`: each one's
hypothesis and letter inclusions. -/
def SaturationsHold (ch : Chain) (Mi : Interp E) : Prop :=
  ∀ p ∈ ch.passes, ∀ ev, p.evidence = some ev → ev.Holds Mi ∧ ev.InclusionsHold Mi

/-- The contracts of the passes without evidence: each one's result denotes
no more than what it was given. (`rotate` adds no cycle instead: for a `rot`
constraint, this does not hold.) -/
def TrustedHold (ch : Chain) (Mi : Interp E) : Prop :=
  ∀ before p, (before, p) ∈ ch.links → p.evidence = none →
    Rel.Sub (p.result.denote (Label.denote Mi)) (before.denote (Label.denote Mi))

theorem go_sound {Mi : Interp E} {rhs : NFA Label} :
    ∀ (ps : List Pass) (i : Nat) (last : NFA Label), go rhs i last ps = none →
      (∀ p ∈ ps, ∀ ev, p.evidence = some ev → ev.Holds Mi ∧ ev.InclusionsHold Mi) →
      (∀ before p, (before, p) ∈ (last :: ps.map (·.result)).zip ps → p.evidence = none →
        Rel.Sub (p.result.denote (Label.denote Mi)) (before.denote (Label.denote Mi))) →
      Rel.Sub (rhs.denote (Label.denote Mi)) (last.denote (Label.denote Mi))
  | [], _, last, h, _, _ => by
    simp only [go] at h
    split at h
    · rename_i heq
      subst heq
      exact Rel.Sub.refl _
    · exact absurd h (by simp)
  | p :: ps, i, last, h, hsat, htrust => by
    have hlink : (last, p) ∈ (last :: (p :: ps).map (·.result)).zip (p :: ps) := by
      simp
    have hrest : ∀ before q, (before, q) ∈ (p.result :: ps.map (·.result)).zip ps →
        q.evidence = none →
        Rel.Sub (q.result.denote (Label.denote Mi)) (before.denote (Label.denote Mi)) := by
      intro before q hmem hq
      exact htrust before q (by simp [hmem]) hq
    have hsat' : ∀ q ∈ ps, ∀ ev, q.evidence = some ev → ev.Holds Mi ∧ ev.InclusionsHold Mi :=
      fun q hq => hsat q (List.mem_cons_of_mem p hq)
    simp only [go] at h
    split at h
    · rename_i ev hev
      split at h
      · exact absurd h (by simp)
      · rename_i hcheck
        obtain ⟨hyp, hinc⟩ := hsat p List.mem_cons_self ev hev
        exact Rel.Sub.trans (go_sound ps (i + 1) p.result h hsat' hrest)
          (ev.check_sound hcheck hyp hinc)
    · rename_i hev
      split at h
      · exact Rel.Sub.trans (go_sound ps (i + 1) p.result h hsat' hrest)
          (htrust last p hlink hev)
      · exact absurd h (by simp)

/-- If `check` accepts a chain, and what it rests on holds, then `rhs`
denotes no more than the chain's start. -/
theorem check_sound (ch : Chain) (rhs : NFA Label) (h : ch.check rhs = none) (Mi : Interp E)
    (hsat : ch.SaturationsHold Mi) (htrust : ch.TrustedHold Mi) :
    Rel.Sub (rhs.denote (Label.denote Mi)) (ch.start.denote (Label.denote Mi)) :=
  go_sound ch.passes 0 ch.start h hsat htrust

/-- **The chain and the final check.** If `check` accepts a certificate and
`Chain.check` its chain, then, given the certificate's letter inclusions,
each saturation's hypothesis and letter inclusions, and the contracts of the
passes without evidence, the certificate's left automaton denotes no more
than the automaton the right-hand side normalized to. -/
theorem sound (c : Certificate) (ch : Chain) (h : (c.check <|> ch.check c.rhs) = none)
    (Mi : Interp E)
    (hinc : ∀ a b, (a, b) ∈ c.inclusions → Rel.Sub (a.denote Mi) (b.denote Mi))
    (hsat : ch.SaturationsHold Mi) (htrust : ch.TrustedHold Mi) :
    Rel.Sub (c.lhs.denote (Label.denote Mi)) (ch.start.denote (Label.denote Mi)) := by
  rw [Certificate.orElse_eq_none] at h
  exact Rel.Sub.trans (c.check_sound_interp h.1 Mi hinc) (ch.check_sound c.rhs h.2 Mi hsat htrust)

end Chain

end KaterCert

/-! The proofs rest on Lean's standard axioms and nothing else: `lake build`
fails if a `sorry` or a new axiom creeps in. -/

/--
info: 'KaterCert.Chain.sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms KaterCert.Chain.sound
