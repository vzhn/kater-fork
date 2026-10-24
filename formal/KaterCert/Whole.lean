import KaterCert.Thompson
import KaterCert.Guarded
import KaterCert.Loc
import KaterCert.Rotate
import KaterCert.Builtin
import KaterCert.Soundness
import KaterCert.ReadChain

/-!
# Whole proofs

Kater proves an assertion `A <= B` (or `A = B`, `A & id <= B`, `A & id <=
rot B`) by one or two inclusion checks (`Checker::checkInclusion`), each a
chain of automata from the expressions to the final check. Its evidence
(`ReadChain.Evidence`) records every automaton of the chain. This checks each
link:

- the left-hand side: Lean's automaton of `A` (`Thompson`), with `rf` split
  as Kater splits it (`expandRfs`), is within Kater's left automaton
  (`Guarded`); for `& id`, through the stages of `saturateInitFinalPreds`
  (cycles, `Guarded` in cycle mode) and `saturateLoc` (`Loc`);
- the right-hand side: Kater's first right automaton is within Lean's
  automaton of `B`, and each automaton after it within the one before it,
  each saturation given its assumption (`Saturations`, a parameter: the
  checker of saturations is another piece), each normalization as relations
  (`Guarded`), and the rotation for `rot` adds no cycle (`Rotate`);
- the final check: the certificate is of the last two automata, and the
  checker in Lean accepts it, with its letter inclusions true of the theory.

The theory is Lean's (`Theory.ofDecls`), built from the module's
declarations and the assumptions Kater takes into its theory, as Lean reads
them. `checkAssertion_sound` proves that an accepted chain makes the
assertion hold wherever the theory is sound, `rf` is `rfe | rfi`, and the
module's assumptions hold.

This mirrors the C++ regions `checkInclusion`, `Evidence` (`src/Checker.cpp`,
`src/Checker.hpp`), `expandRfs` (`src/Checker.cpp`) and
`incorporateAssumptions` (`src/Assumptions.cpp`): `scripts/check-mirrors.sh`
reports when they change.
-/

namespace KaterCert

universe u

open ReadChain

/-! ## `rf` split -/

namespace Exp

/-- A letter of a bare relation: no checks, not inverted. -/
def bareLabel (id : Int) : Label := { rel := some { id, inverse := false }, pre := [], post := [] }

mutual

/-- Whether an expression reads one of the relations `ids` (in any letter,
those of `let rec` definitions too). -/
def mentions (ids : List Int) : Exp → Bool
  | .label l => match l.rel with | some r => ids.contains r.id | none => false
  | .zero | .ref _ => false
  | .alt a b | .seq a b => a.mentions ids || b.mentions ids
  | .star a | .plus a | .opt a => a.mentions ids
  | .fix _ defs => Defs.mentions ids defs

def _root_.KaterCert.Defs.mentions (ids : List Int) : Defs → Bool
  | .nil => false
  | .cons e es => e.mentions ids || Defs.mentions ids es

end

mutual

/-- `rf` replaced by `rfe | rfi`, where it is a letter of its own (in `let
rec` definitions too). -/
def splitRf : Exp → Exp
  | .label l => if l == bareLabel Builtin.Rel.rf.id then
      .alt (.label (bareLabel Builtin.Rel.rfe.id)) (.label (bareLabel Builtin.Rel.rfi.id))
    else .label l
  | .zero => .zero
  | .alt a b => .alt a.splitRf b.splitRf
  | .seq a b => .seq a.splitRf b.splitRf
  | .star a => .star a.splitRf
  | .plus a => .plus a.splitRf
  | .opt a => .opt a.splitRf
  | .ref i => .ref i
  | .fix main defs => .fix main (Defs.splitRf defs)

def _root_.KaterCert.Defs.splitRf : Defs → Defs
  | .nil => .nil
  | .cons e es => .cons e.splitRf (Defs.splitRf es)

end

/-- Kater's `expandRfs`: the left-hand side with `rf` split into `rfe | rfi`
if the right-hand side reads either. -/
def expandRfs (lhs rhs : Exp) : Exp :=
  if rhs.mentions [Builtin.Rel.rfe.id, Builtin.Rel.rfi.id] then lhs.splitRf else lhs

/-- The parts of a sequence, as Kater's `SeqRE` lists them. -/
def seqList : Exp → List Exp
  | .seq a b => a.seqList ++ b.seqList
  | e => [e]

end Exp

namespace Whole

variable {E : Type}

/-- `rf` is `rfe | rfi` in `M`. -/
def RfSplit (M : Interp E) : Prop :=
  ∀ x y, M.rel Builtin.Rel.rf.id x y ↔ M.rel Builtin.Rel.rfe.id x y ∨ M.rel Builtin.Rel.rfi.id x y

mutual

theorem splitRf_denoteIn {M : Interp E} (h : RfSplit M) :
    ∀ (e : Exp) (ρ : Nat → Rel E) {x y : E}, e.splitRf.denoteIn M ρ x y ↔ e.denoteIn M ρ x y
  | .label l, _, x, y => by
    unfold Exp.splitRf
    split
    · rename_i hl
      have hl' : l = Exp.bareLabel Builtin.Rel.rf.id := by simpa using hl
      subst hl'
      simp only [Exp.denoteIn, Rel.union, Label.denote, Exp.bareLabel, Relation.denote, Checks]
      simp only [List.not_mem_nil, false_imp_iff, imp_true_iff, true_and, and_true,
        Bool.false_eq_true, ite_false]
      exact (h x y).symm
    · rfl
  | .zero, _, _, _ => Iff.rfl
  | .alt a b, ρ, x, y => by
    simp only [Exp.splitRf, Exp.denoteIn, Rel.union, splitRf_denoteIn h a ρ,
      splitRf_denoteIn h b ρ]
  | .seq a b, ρ, x, y => by
    simp only [Exp.splitRf, Exp.denoteIn, Rel.comp]
    exact ⟨fun ⟨z, h₁, h₂⟩ => ⟨z, (splitRf_denoteIn h a ρ).mp h₁, (splitRf_denoteIn h b ρ).mp h₂⟩,
      fun ⟨z, h₁, h₂⟩ => ⟨z, (splitRf_denoteIn h a ρ).mpr h₁, (splitRf_denoteIn h b ρ).mpr h₂⟩⟩
  | .star a, ρ, x, y => by
    simp only [Exp.splitRf, Exp.denoteIn]
    constructor
    · exact fun h' => Rel.Star.mono (fun _ _ => (splitRf_denoteIn h a ρ).mp) _ _ h'
    · exact fun h' => Rel.Star.mono (fun _ _ => (splitRf_denoteIn h a ρ).mpr) _ _ h'
  | .plus a, ρ, x, y => by
    simp only [Exp.splitRf, Exp.denoteIn, Rel.Plus, Rel.comp]
    constructor
    · exact fun ⟨z, h₁, h₂⟩ => ⟨z, (splitRf_denoteIn h a ρ).mp h₁,
        Rel.Star.mono (fun _ _ => (splitRf_denoteIn h a ρ).mp) _ _ h₂⟩
    · exact fun ⟨z, h₁, h₂⟩ => ⟨z, (splitRf_denoteIn h a ρ).mpr h₁,
        Rel.Star.mono (fun _ _ => (splitRf_denoteIn h a ρ).mpr) _ _ h₂⟩
  | .opt a, ρ, x, y => by
    simp only [Exp.splitRf, Exp.denoteIn, Rel.Opt, Rel.union, splitRf_denoteIn h a ρ]
  | .ref _, _, _, _ => Iff.rfl
  | .fix main defs, _, x, y => by
    simp only [Exp.splitRf, Exp.denoteIn]
    have : ∀ n, Nat.repeat (Defs.denoteIn M · (Defs.splitRf defs)) n (fun _ => Rel.empty) =
        Nat.repeat (Defs.denoteIn M · defs) n (fun _ => Rel.empty) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        simp only [Nat.repeat]
        rw [ih]
        funext i x y
        exact propext (defs_splitRf_denoteIn h defs _ i)
    simp only [this]

theorem defs_splitRf_denoteIn {M : Interp E} (h : RfSplit M) :
    ∀ (defs : Defs) (ρ : Nat → Rel E) (i : Nat) {x y : E},
      (Defs.splitRf defs).denoteIn M ρ i x y ↔ defs.denoteIn M ρ i x y
  | .nil, _, _, _, _ => Iff.rfl
  | .cons e _, ρ, 0, _, _ => splitRf_denoteIn h e ρ
  | .cons _ es, ρ, i + 1, _, _ => defs_splitRf_denoteIn h es ρ i

end

theorem splitRf_denote {M : Interp E} (h : RfSplit M) (e : Exp) {x y : E} :
    e.splitRf.denote M x y ↔ e.denote M x y := by
  rw [Exp.denote_iff_denoteIn, Exp.denote_iff_denoteIn]
  exact splitRf_denoteIn h e _

theorem expandRfs_denote {M : Interp E} (h : RfSplit M) (lhs rhs : Exp) {x y : E} :
    (Exp.expandRfs lhs rhs).denote M x y ↔ lhs.denote M x y := by
  unfold Exp.expandRfs
  split
  · exact splitRf_denote h lhs
  · rfl

/-! ## The assumptions the theory takes in -/

/-- The predicate of a letter that checks one plain predicate. -/
def onePred : Exp → Option Predicate
  | .label l => if l.rel.isNone then
      (match l.pre with | [p] => if p.complement then none else some p | _ => none) else none
  | _ => none

/-- The checks of letters that are all predicates. -/
def predChecks : List Exp → Option (List Predicate)
  | [] => some []
  | .label l :: es => if l.rel.isNone then (predChecks es).map (l.pre ++ ·) else none
  | _ :: _ => none

/-- Whether an expression is a letter of `r`. -/
def isRel (r : Relation) : Exp → Bool
  | .label m => m.rel == some r
  | _ => false

/-- The checks before and after the step of `r` in a sequence
`[A];r;[B]`. -/
def domainOfSeq (r : Relation) (parts : List Exp) : Option (List Predicate × List Predicate) :=
  match parts.findIdx? (isRel r) with
  | none => none
  | some i =>
    match parts[i]?, predChecks (parts.take i), predChecks (parts.drop (i + 1)) with
    | some (.label m), some pb, some pa =>
      if m.pre.isEmpty && m.post.isEmpty then some (pb, pa) else none
    | _, _, _ => none

/-- Checks of the source and target of a step of `r`, as of the relation's
own direction: those of an inverted `r` swapped. -/
def orient (r : Relation) (p : List Predicate × List Predicate) : List Predicate × List Predicate :=
  if r.inverse then (p.2, p.1) else p

/-- The domain and codomain `r <= [A];r;[B]` states of the relation of `r`. -/
def domainOf (r : Relation) (rhs : Exp) : Option (List Predicate × List Predicate) :=
  (match rhs with
   | .label m => if m.rel == some r then some (m.pre, m.post) else none
   | _ => domainOfSeq r rhs.seqList).map (orient r)

/-- What Kater's theory takes in from an assumption
(`Assumptions::incorporateInto`), as Lean reads it: a domain and a codomain
(`r <= [A];r;[B]`), or incompatible predicates (`[A;B;...] <= 0`). -/
def incorporate (d : Decls) : Constraint → Decls
  | .subset (.label l) rhs false false | .equal (.label l) rhs false false =>
    match l.rel with
    | some r =>
      if l.pre.isEmpty && l.post.isEmpty then
        match domainOf r rhs with
        | some (dom, codom) => { d with domains := d.domains ++ [(r.id, dom, codom)] }
        | none => d
      else d
    | none => d
  | .subset lhs .zero _ _ =>
    let parts := lhs.seqList
    if parts.length < 2 then d else
    match parts.mapM onePred with
    | some ps =>
      let ids := (ps.map (·.id)).eraseDups
      if ids.length == 2 then { d with disjoint := d.disjoint ++ [ids] }
      else { d with invalid := d.invalid ++ [ids] }
    | none => d
  | _ => d

/-- A module's declarations, and what Kater's theory took in of its
assumptions. -/
def declsOf (ev : Evidence) : Decls :=
  ev.assumptions.foldl (fun d a => match a.constraint with
    | .ok c => if a.saturated then d else incorporate d c
    | .error _ => d) { disjoint := ev.disjoint, perLoc := ev.perLoc }

/-! ## Saturations -/

/-- A checker of saturation steps: `ok θ before after hyp step` claims that,
given `hyp`, `after` is within `before`. -/
structure Saturations where
  ok : Theory → NFA Label → NFA Label → Constraint → Step → Bool
  sound : ∀ {E : Type} (M : Interp E) (loc : Rel E) (θ : Theory) (before after : NFA Label)
    (hyp : Constraint) (s : Step), ok θ before after hyp s = true → θ.Sound M loc →
    hyp.Holds M → Rel.Sub (after.denote (Label.denote M)) (before.denote (Label.denote M))

/-- Saturations that add nothing a check of relations cannot see: the
checker until the saturation certificates come. -/
def noSaturations : Saturations where
  ok θ before after _ s := Guarded.prove θ after before false (some s.origins)
  sound := fun _ _ _ _ _ _ _ h hθ _ => Guarded.prove_sound hθ h

/-! ## The chain -/

/-- The left-hand side: the automaton of the final check, if Lean's
automaton of `lhs` is within it (and, for `& id`, its cycles are). -/
def stepOf (inc : Inclusion) (stage : String) : Option Step := inc.steps.find? (·.stage == stage)

def left (θ : Theory) (inc : Inclusion) (lhs : Exp) : Except String (NFA Label) :=
  if !lhs.wellFormed then .error "a let rec of the left-hand side is not left-linear" else
  match stepOf inc "leftFinal" with
  | none => .error "no left automaton"
  | some sf =>
    if !inc.sameEnds then
      if Guarded.prove θ (Thompson.nfa lhs) sf.nfa false then .ok sf.nfa
      else .error "the left-hand side is not within Kater's left automaton"
    else
      match stepOf inc "left", stepOf inc "leftInitFinal", stepOf inc "leftLoc" with
      | some s₀, some s₁, some s₂ =>
        if !Guarded.prove θ (Thompson.nfa lhs) s₀.nfa false then
          .error "the left-hand side is not within Kater's left automaton"
        else if !Guarded.prove θ s₀.nfa s₁.nfa true (some s₁.origins) then
          .error "saturateInitFinalPreds loses a cycle"
        else if !Loc.check θ s₁.nfa s₂.nfa then
          .error "saturateLoc does not check"
        else if !Guarded.prove θ s₂.nfa sf.nfa false (some sf.origins) then
          .error "the left automaton loses a word of the one before it"
        else .ok sf.nfa
      | _, _, _ => .error "a stage of the left-hand side is missing"

/-- The right-hand side from `prev` on: each step is within the one before
it (a saturation given its assumption), and a rotation, which comes last,
adds no cycle. The automaton of the final check, and whether it is a
rotation. -/
def right (θ : Theory) (sat : Saturations) (hyps : Array Assumption) :
    NFA Label → List Step → Except String (NFA Label × Bool)
  | prev, [] => .ok (prev, false)
  | prev, s :: rest =>
    if s.stage == "saturated" then
      match s.assumption.bind (hyps[·]?) with
      | some a =>
        match a.constraint with
        | .ok c =>
          if sat.ok θ prev s.nfa c s then right θ sat hyps s.nfa rest
          else .error s!"the saturation with {a.text} does not check"
        | .error e => .error s!"a saturation with an assumption that does not read: {e}"
      | none => .error "a saturation names no assumption"
    else if s.stage == "normalized" || s.stage == "pruned" then
      if Guarded.prove θ s.nfa prev false (some s.origins) then right θ sat hyps s.nfa rest
      else .error s!"a {s.stage} automaton is not within the one before it"
    else if s.stage == "rotated" then
      if rest.isEmpty && Guarded.prove θ s.nfa (Rotate.rotations prev) false then
        .ok (s.nfa, true)
      else .error "the rotated automaton is not within the rotations of the one before it"
    else .error s!"unexpected stage {s.stage}"

/-- The final check: the certificate is of the two automata, and accepted,
with its letter inclusions true of the theory. -/
def final (θ : Theory) (c : Certificate) (L R : NFA Label) : Except String Unit :=
  if c.lhs != L then .error "the certificate is not of the left automaton"
  else if c.rhs != R then .error "the certificate is not of the right automaton"
  else match c.check with
    | some why => .error s!"the certificate is not valid: {why}"
    | none =>
      if c.inclusions.all fun (a, b) => θ.labelIncl a b then .ok ()
      else .error "the certificate rests on a letter inclusion Lean does not know"

/-- The evidence of an inclusion `checkInclusion` proved. -/
def checkInclusion (θ : Theory) (sat : Saturations) (hyps : Array Assumption) (inc : Inclusion) :
    Except String Unit :=
  match left θ inc (Exp.expandRfs inc.lhs inc.rhs) with
  | .error e => .error e
  | .ok L =>
    match inc.steps.dropWhile (·.stage != "right") with
    | [] => .error "no right automaton"
    | r₀ :: rest =>
      if !Guarded.prove θ r₀.nfa (Thompson.nfa inc.rhs) false then
        .error "Kater's right automaton is not within the right-hand side"
      else match right θ sat hyps r₀.nfa rest with
        | .error e => .error e
        | .ok (R, rot) =>
          if rot != inc.rotated then
            .error "a rotation where there is none, or none where there is one"
          else final θ inc.cert L R

/-- The evidence of an assertion. -/
def checkAssertion (sat : Saturations) (ev : Evidence) : Except String Unit :=
  if !(declsOf ev).wf then .error "the per-location variants are not well-formed" else
  match ev.constraint, ev.inclusions with
  | .subset A B e r, [i₁] =>
    if !(i₁.lhs == A && i₁.rhs == B && i₁.sameEnds == e && i₁.rotated == r) then
      .error "the inclusion is not of the assertion"
    else checkInclusion (Theory.ofDecls (declsOf ev)) sat ev.assumptions i₁
  | .equal A B e r, [i₁, i₂] =>
    if !(i₁.lhs == A && i₁.rhs == B && i₁.sameEnds == e && i₁.rotated == r) then
      .error "the first inclusion is not of the assertion"
    else if !(i₂.lhs == B && i₂.rhs == Exp.expandRfs A B && i₂.sameEnds == e &&
        i₂.rotated == r) then
      .error "the second inclusion is not of the assertion"
    else match checkInclusion (Theory.ofDecls (declsOf ev)) sat ev.assumptions i₁ with
      | .error e => .error e
      | .ok () => checkInclusion (Theory.ofDecls (declsOf ev)) sat ev.assumptions i₂
  | _, _ => .error "the inclusions are not those of the assertion"

/-! ## Soundness -/

/-- The assumptions that read hold in `M`. -/
def HypsHold (M : Interp E) (hyps : Array Assumption) : Prop :=
  ∀ (i : Nat) (a : Assumption) (c : Constraint), hyps[i]? = some a → a.constraint = .ok c →
    c.Holds M

theorem bind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

variable {θ : Theory} {M : Interp E} {loc : Rel E}

local notation "⟦" A "⟧" => NFA.denote (Label.denote M) A

theorem left_sound (hθ : θ.Sound M loc) {inc : Inclusion} {lhs : Exp} {L : NFA Label}
    (h : left θ inc lhs = .ok L) :
    (inc.sameEnds = false → Rel.Sub (lhs.denote M) ⟦L⟧) ∧
      ∀ x, lhs.denote M x x → ⟦L⟧ x x := by
  unfold left at h
  split at h
  · simp at h
  rename_i hwf
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hwf
  split at h
  · simp at h
  · rename_i sf _
    split at h
    · rename_i hse
      split at h
      · rename_i hp
        simp only [Except.ok.injEq] at h
        subst h
        have hsub : Rel.Sub (lhs.denote M) ⟦sf.nfa⟧ := fun x y hxy =>
          Guarded.prove_sound hθ hp x y (Thompson.nfa_complete M lhs hwf hxy)
        exact ⟨fun _ => hsub, fun x hx => hsub x x hx⟩
      · simp at h
    · rename_i hse
      split at h
      · rename_i s₀ s₁ s₂ _ _ _
        split at h
        · simp at h
        · rename_i h₀
          split at h
          · simp at h
          · rename_i h₁
            split at h
            · simp at h
            · rename_i h₂
              split at h
              · simp at h
              · rename_i h₃
                simp only [Except.ok.injEq] at h
                subst h
                simp only [Bool.not_eq_true', Bool.not_eq_false] at h₀ h₁ h₂ h₃
                refine ⟨fun hne => by simp [hne] at hse, fun x hx => ?_⟩
                have a₀ := Guarded.prove_sound hθ h₀ x x (Thompson.nfa_complete M lhs hwf hx)
                have a₁ := Guarded.prove_sound_cycle hθ h₁ x a₀
                have a₂ := Loc.check_sound hθ h₂ x a₁
                exact Guarded.prove_sound hθ h₃ x x a₂
      · simp at h

theorem right_sound (hθ : θ.Sound M loc) {sat : Saturations} {hyps : Array Assumption}
    (hh : HypsHold M hyps) :
    ∀ {prev : NFA Label} {steps : List Step} {R : NFA Label} {rot : Bool},
      right θ sat hyps prev steps = .ok (R, rot) →
        (rot = false → Rel.Sub ⟦R⟧ ⟦prev⟧) ∧ (rot = true → ∀ x, ⟦R⟧ x x → ∃ y, ⟦prev⟧ y y)
  | prev, [], R, rot, h => by
    simp only [right, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ => Rel.Sub.refl _, fun h => by simp at h⟩
  | prev, s :: rest, R, rot, h => by
    -- each step is within the one before it, so what holds of the rest holds of `prev`
    have step : ∀ {X : NFA Label}, Rel.Sub ⟦X⟧ ⟦prev⟧ → right θ sat hyps X rest = .ok (R, rot) →
        (rot = false → Rel.Sub ⟦R⟧ ⟦prev⟧) ∧ (rot = true → ∀ x, ⟦R⟧ x x → ∃ y, ⟦prev⟧ y y) := by
      intro X hX hr
      obtain ⟨h₁, h₂⟩ := right_sound hθ hh hr
      refine ⟨fun hr' => Rel.Sub.trans (h₁ hr') hX, fun hr' x hx => ?_⟩
      obtain ⟨y, hy⟩ := h₂ hr' x hx
      exact ⟨y, hX y y hy⟩
    unfold right at h
    split at h
    · split at h
      · rename_i a ha
        split at h
        · rename_i c hc
          split at h
          · rename_i hok
            obtain ⟨i, hi, hai⟩ : ∃ i, s.assumption = some i ∧ hyps[i]? = some a := by
              cases hs : s.assumption with
              | none => simp [hs] at ha
              | some i => exact ⟨i, rfl, by simpa [hs] using ha⟩
            exact step (sat.sound M loc θ prev s.nfa c s hok hθ (hh i a c hai hc)) h
          · simp at h
        · simp at h
      · simp at h
    · split at h
      · split at h
        · rename_i hp
          exact step (Guarded.prove_sound hθ hp) h
        · simp at h
      · split at h
        · split at h
          · rename_i hp
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [Bool.and_eq_true] at hp
            refine ⟨fun h => by simp at h, fun _ x hx => ?_⟩
            exact Rotate.rotations_cycle M (Guarded.prove_sound hθ hp.2 x x hx)
          · simp at h
        · simp at h

theorem final_sound (hθ : θ.Sound M loc) {c : Certificate} {L R : NFA Label}
    (h : final θ c L R = .ok ()) : Rel.Sub ⟦L⟧ ⟦R⟧ := by
  unfold final at h
  split at h
  · simp at h
  · rename_i hl
    split at h
    · simp at h
    · rename_i hr
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hl hr
      subst hl hr
      split at h
      · simp at h
      · rename_i hc
        split at h
        · rename_i hinc
          exact Certificate.check_sound_interp c hc M fun a b hab => by
            simp only [List.all_eq_true] at hinc
            exact hθ.labelIncl (hinc (a, b) hab)
        · simp at h

/-- **An inclusion's chain is sound**: if `checkInclusion` accepts it, the
theory is sound, `rf` is `rfe | rfi` and the assumptions hold, the
inclusion holds. -/
theorem checkInclusion_sound (hθ : θ.Sound M loc) (hrf : RfSplit M) {sat : Saturations}
    {hyps : Array Assumption} (hh : HypsHold M hyps) {inc : Inclusion}
    (h : checkInclusion θ sat hyps inc = .ok ()) :
    Constraint.SubsetHolds M inc.lhs inc.rhs inc.sameEnds inc.rotated := by
  unfold checkInclusion at h
  split at h
  · simp at h
  · rename_i L hL
    have ⟨hLsub, hLcyc⟩ := left_sound hθ hL
    have hA : ∀ {x y}, inc.lhs.denote M x y → (Exp.expandRfs inc.lhs inc.rhs).denote M x y :=
      fun hxy => (expandRfs_denote hrf _ _).mpr hxy
    split at h
    · simp at h
    · rename_i r₀ rest _
      split at h
      · simp at h
      · rename_i hr₀
        simp only [Bool.not_eq_true', Bool.not_eq_false] at hr₀
        have hR₀ : Rel.Sub ⟦r₀.nfa⟧ (inc.rhs.denote M) := fun x y hxy =>
          Thompson.nfa_sound M inc.rhs (Guarded.prove_sound hθ hr₀ x y hxy)
        split at h
        · simp at h
        · rename_i R rot hR
          obtain ⟨hRsub, hRcyc⟩ := right_sound hθ hh hR
          split at h
          · simp at h
          · rename_i hrot
            simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hrot
            have hfin := final_sound hθ h
            unfold Constraint.SubsetHolds
            split
            · rename_i hrt
              rintro ⟨x, hx⟩
              have hLx := hfin x x (hLcyc x (hA hx))
              rw [hrot, hrt] at hRcyc
              obtain ⟨y, hy⟩ := hRcyc rfl x hLx
              exact ⟨y, hR₀ y y hy⟩
            · rename_i hrt
              simp only [Bool.not_eq_true] at hrt
              rw [hrot, hrt] at hRsub
              split
              · intro x hx
                exact hR₀ x x (hRsub rfl x x (hfin x x (hLcyc x (hA hx))))
              · rename_i hse
                simp only [Bool.not_eq_true] at hse
                intro x y hxy
                exact hR₀ x y (hRsub rfl x y (hfin x y (hLsub hse x y (hA hxy))))

/-- **An assertion's chain is sound**: if `checkAssertion` accepts its
evidence, then wherever the theory of its module is sound, `rf` is
`rfe | rfi` and the module's assumptions hold, the assertion holds. -/
theorem checkAssertion_sound {sat : Saturations} {ev : Evidence}
    (h : checkAssertion sat ev = .ok ())
    (hθ : (Theory.ofDecls (declsOf ev)).Sound M loc) (hrf : RfSplit M)
    (hh : HypsHold M ev.assumptions) : ev.constraint.Holds M := by
  unfold checkAssertion at h
  split at h
  · simp at h
  · split at h
    · rename_i A B e r i₁ hc _
      split at h
      · simp at h
      · rename_i heq
        simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq] at heq
        obtain ⟨⟨⟨hl, hr⟩, he⟩, hrt⟩ := heq
        have s₁ := checkInclusion_sound hθ hrf hh h
        rw [hl, hr, he, hrt] at s₁
        rw [hc]
        exact s₁
    · rename_i A B e r i₁ i₂ hc _
      split at h
      · simp at h
      · rename_i heq₁
        split at h
        · simp at h
        · rename_i heq₂
          simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq] at heq₁ heq₂
          obtain ⟨⟨⟨hl₁, hr₁⟩, he₁⟩, hrt₁⟩ := heq₁
          obtain ⟨⟨⟨hl₂, hr₂⟩, he₂⟩, hrt₂⟩ := heq₂
          split at h
          · simp at h
          · rename_i h₁
            have s₁ := checkInclusion_sound hθ hrf hh h₁
            have s₂ := checkInclusion_sound hθ hrf hh h
            rw [hl₁, hr₁, he₁, hrt₁] at s₁
            rw [hl₂, hr₂, he₂, hrt₂] at s₂
            rw [hc]
            refine ⟨s₁, ?_⟩
            -- the second inclusion's right-hand side is the assertion's left one, rf split
            unfold Constraint.SubsetHolds at s₂ ⊢
            split
            · rename_i hrt
              simp only [hrt, ite_true] at s₂
              intro hx
              obtain ⟨y, hy⟩ := s₂ hx
              exact ⟨y, (expandRfs_denote hrf _ _).mp hy⟩
            · rename_i hrt
              simp only [hrt, Bool.false_eq_true, ite_false] at s₂
              split
              · rename_i hse
                simp only [hse, ite_true] at s₂
                intro x hx
                exact (expandRfs_denote hrf _ _).mp (s₂ x hx)
              · rename_i hse
                simp only [hse, Bool.false_eq_true, ite_false] at s₂
                intro x y hxy
                exact (expandRfs_denote hrf _ _).mp (s₂ x y hxy)
    · simp at h

end Whole

end KaterCert
