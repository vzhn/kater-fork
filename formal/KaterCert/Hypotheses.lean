import KaterCert.SaturationSound
import KaterCert.Thompson
import KaterCert.Guarded
import KaterCert.Builtin

/-!
# The hypotheses of the saturations

A saturation of the right-hand side assumes a hypothesis (`Evidence.Holds`):
that a letter is transitive, that an automaton denotes no more than a word,
or that an automaton denotes nothing. Kater takes it from an assumption of
the module (`expandSubsetAssumption`, `src/Checker.cpp`):

- `r;r <= r`, `r+ <= r` and `total r` make `r` transitive
  (`saturateTransitive`);
- `A <= B` makes the automaton of `A`, with `any` starred (`starifyAny`),
  denote no more than the word of `B` (`saturateID`, `saturateBuiltin`); for
  a compilation scheme `[P];po;[Q] <= [P];po;[F];po;[Q]`, the automaton is
  that of `[P];po+;[Q]` (`saturateSubword`);
- `A <= 0` makes the automaton of `A` denote nothing (`saturateEmpty`).

`justifies` checks that an assumption gives a hypothesis: the letter is the
assumption's, or Lean's automaton of the assumption's left-hand side, with
`po` repeated and `any` starred (`Exp.widen`), takes in the hypothesis'
automaton, and the word's (or none) takes in Lean's automaton of its
right-hand side (`Guarded`). Where the assumption holds, `po` is transitive
and `any` relates every two events (`Facts`), the hypothesis holds
(`justifies_sound`). `saturates` checks a saturation: its evidence, its
letter inclusions, and an assumption that gives its hypothesis.

This mirrors the C++ region `expandAssumption` (`src/Checker.cpp`):
`scripts/check-mirrors.sh` reports when it changes.
-/

namespace KaterCert

universe u

variable {E : Type u}

/-- What the saturations rest on beyond the theory, as in the model: `po` is
transitive, and `any` relates every two events. -/
structure Facts (M : Interp E) : Prop where
  po_trans : ∀ x y z, M.rel Builtin.Rel.po.id x y → M.rel Builtin.Rel.po.id y z →
    M.rel Builtin.Rel.po.id x z
  any_univ : ∀ x y, M.rel Builtin.Rel.any.id x y

namespace Exp

/-- The letter `[pre];r;[post]` as `[pre];f r;[post]`. -/
def around (l : Label) (r : Relation) (f : Exp → Exp) : Exp :=
  .seq (.label ⟨none, l.pre, []⟩) (.seq (f (.label ⟨some r, [], []⟩)) (.label ⟨none, l.post, []⟩))

/-- The expression with each letter of `po` repeated (`po+`) and each of
`any` starred (`any*`): no more, where `po` is transitive and `any`
relates every two events. -/
def widen : Exp → Exp
  | .label l =>
    match l.rel with
    | some r =>
      if r = ⟨Builtin.Rel.po.id, false⟩ then around l r .plus
      else if r = ⟨Builtin.Rel.any.id, false⟩ then around l r .star
      else .label l
    | none => .label l
  | .zero => .zero
  | .alt a b => .alt a.widen b.widen
  | .seq a b => .seq a.widen b.widen
  | .star a => .star a.widen
  | .plus a => .plus a.widen
  | .opt a => .opt a.widen
  | .ref i => .ref i
  | .fix main defs => .fix main defs
  | .inv a => .inv a.widen

/-- A word as an expression. -/
def ofWord : List Label → Exp
  | [] => .label .eps
  | a :: w => .seq (.label a) (ofWord w)

end Exp

/-- The inclusions a constraint states that Kater saturates with: `A <= B`,
and for `A = B` also `B <= A`. -/
def Constraint.subsets : Constraint → List (Exp × Exp)
  | .subset A B false false => [(A, B)]
  | .equal A B false false => [(A, B), (B, A)]
  | _ => []

/-- Whether a constraint makes the letter `l` transitive: `l;l <= l`,
`l+ <= l`, or `total l`. -/
def Constraint.transitive (c : Constraint) (l : Label) : Bool :=
  c == .total (.label l) || c.subsets.any fun (A, B) =>
    B == .label l && (A == .seq (.label l) (.label l) || A == .plus (.label l))

/-- Whether the assumption `c` gives the hypothesis of a saturation's
evidence (see above). -/
def justifies (θ : Theory) (c : Constraint) (ev : Evidence) : Bool :=
  match ev.hypothesis with
  | .transitive => c.transitive ev.letter
  | .within => c.subsets.any fun (A, B) =>
    B.wellFormed && Guarded.prove θ ev.automaton (Thompson.nfa A.widen) false &&
      Guarded.prove θ (Thompson.nfa B) (Thompson.nfa (Exp.ofWord ev.word)) false
  | .empty => c.subsets.any fun (A, B) =>
    B.wellFormed && Guarded.prove θ ev.automaton (Thompson.nfa A.widen) false &&
      Guarded.prove θ (Thompson.nfa B) (Thompson.nfa .zero) false

/-- Whether a saturation from `before` to `after` checks: its evidence does
(`Evidence.check`), its letter inclusions are the theory's, and one of the
assumptions `hyps` gives its hypothesis. -/
def saturates (θ : Theory) (hyps : List Constraint) (before after : NFA Label) (ev : Evidence) :
    Bool :=
  (ev.check before after).isNone && ev.inclusions.all (fun (a, b) => θ.labelIncl a b) &&
    hyps.any (justifies θ · ev)

/-! ## Soundness -/

variable {M : Interp E}

theorem plus_trans {A R : Rel E} (hA : Rel.Sub A R) (hR : ∀ x y z, R x y → R y z → R x z)
    {x y : E} (h : Rel.Plus A x y) : R x y := by
  obtain ⟨z, hxz, hzy⟩ := h
  have : ∀ {z y : E}, Rel.Star A z y → ∀ {x : E}, R x z → R x y := by
    intro z y hs
    induction hs with
    | refl => exact fun h => h
    | step ha _ ih => exact fun h => ih (hR _ _ _ h (hA _ _ ha))
  exact this hzy (hA _ _ hxz)

theorem around_sub {l : Label} {r : Relation} (hl : l.rel = some r) {f : Exp → Exp}
    (hf : ∀ x y, (f (.label ⟨some r, [], []⟩)).denote M x y → r.denote M x y) {x y : E}
    (h : (Exp.around l r f).denote M x y) : (Exp.label l).denote M x y := by
  obtain ⟨z, ⟨rfl, hpre⟩, w, hr, ⟨rfl, hpost⟩⟩ := h
  simp only [Exp.denote, Label.denote, hl]
  exact ⟨hpre, hf _ _ hr, hpost⟩

/-- Widening takes in no more, where `po` is transitive and `any` relates
every two events. -/
theorem widen_sub (hF : Facts M) : ∀ (e : Exp) {x y : E}, e.widen.denote M x y → e.denote M x y
  | .label l, x, y, h => by
    unfold Exp.widen at h
    split at h
    · rename_i r hr
      split at h
      · rename_i hpo
        subst hpo
        refine around_sub hr (fun x y h' => ?_) h
        simp only [Relation.denote, Bool.false_eq_true, ite_false]
        refine plus_trans (R := M.rel Builtin.Rel.po.id) (fun a b hab => ?_) hF.po_trans h'
        simp only [Exp.denote, Label.denote, Relation.denote, Bool.false_eq_true, ite_false] at hab
        exact hab.2.1
      · split at h
        · rename_i hany
          subst hany
          refine around_sub hr (fun x y _ => ?_) h
          simp only [Relation.denote, Bool.false_eq_true, ite_false]
          exact hF.any_univ x y
        · exact h
    · exact h
  | .zero, _, _, h => h
  | .alt a b, _, _, h => by
    rcases h with h | h
    · exact .inl (widen_sub hF a h)
    · exact .inr (widen_sub hF b h)
  | .seq a b, _, _, h => by
    obtain ⟨z, h₁, h₂⟩ := h
    exact ⟨z, widen_sub hF a h₁, widen_sub hF b h₂⟩
  | .star a, _, _, h => Rel.Star.mono (fun _ _ => widen_sub hF a) _ _ h
  | .plus a, _, _, h => by
    obtain ⟨z, h₁, h₂⟩ := h
    exact ⟨z, widen_sub hF a h₁, Rel.Star.mono (fun _ _ => widen_sub hF a) _ _ h₂⟩
  | .opt a, _, _, h => by
    rcases h with h | h
    · exact .inl h
    · exact .inr (widen_sub hF a h)
  | .ref _, _, _, h => h
  | .fix _ _, _, _, h => h
  | .inv a, _, _, h => widen_sub hF a h

theorem ofWord_denote : ∀ (w : List Label) {x y : E},
    (Exp.ofWord w).denote M x y ↔ wordRel (Label.denote M) w x y
  | [], x, y => Label.denote_eps M
  | a :: w, x, y => by
    simp only [Exp.ofWord, Exp.denote, Rel.comp, wordRel]
    constructor
    · rintro ⟨z, ha, hw⟩
      exact ⟨z, ha, (ofWord_denote w).mp hw⟩
    · rintro ⟨z, ha, hw⟩
      exact ⟨z, ha, (ofWord_denote w).mpr hw⟩

theorem Constraint.subsets_sound {c : Constraint} (h : c.Holds M) {A B : Exp}
    (hAB : (A, B) ∈ c.subsets) : Rel.Sub (A.denote M) (B.denote M) := by
  cases c with
  | subset A' B' se rot =>
    cases se <;> cases rot <;>
      simp only [Constraint.subsets, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil] at hAB
    obtain ⟨rfl, rfl⟩ := hAB
    simpa only [Constraint.Holds, Constraint.SubsetHolds, Bool.false_eq_true, ite_false] using h
  | equal A' B' se rot =>
    cases se <;> cases rot <;>
      simp only [Constraint.subsets, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
        or_false] at hAB
    simp only [Constraint.Holds, Constraint.SubsetHolds, Bool.false_eq_true, ite_false] at h
    rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h.1
    · exact h.2
  | total e => simp [Constraint.subsets] at hAB

theorem Constraint.transitive_sound {c : Constraint} (h : c.Holds M) {l : Label}
    (ht : c.transitive l = true) :
    Rel.Sub (Rel.comp (l.denote M) (l.denote M)) (l.denote M) := by
  simp only [Constraint.transitive, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
    Bool.and_eq_true] at ht
  rcases ht with rfl | ⟨⟨A, B⟩, hAB, rfl, rfl | rfl⟩
  · exact h.1
  · exact Constraint.subsets_sound h hAB
  · intro x y ⟨z, h₁, h₂⟩
    exact Constraint.subsets_sound h hAB x y ⟨z, h₁, .step h₂ (.refl _)⟩

variable {θ : Theory} {loc : Rel E}

/-- **An assumption that justifies a hypothesis gives it**, where the
theory is sound, `po` is transitive and `any` relates every two events. -/
theorem justifies_sound (hθ : θ.Sound M loc) (hF : Facts M) {c : Constraint} (hc : c.Holds M)
    {ev : Evidence} (h : justifies θ c ev = true) : ev.Holds M := by
  unfold justifies at h
  unfold Evidence.Holds
  cases hh : ev.hypothesis <;> simp only [hh] at h ⊢
  · exact Constraint.transitive_sound hc h
  · simp only [List.any_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨A, B⟩, hAB, ⟨hwf, h₁⟩, h₂⟩ := h
    intro x y hxy
    have a₁ := widen_sub hF A (Thompson.nfa_sound M A.widen (Guarded.prove_sound hθ h₁ x y hxy))
    have a₂ := Guarded.prove_sound hθ h₂ x y
      (Thompson.nfa_complete M B hwf (Constraint.subsets_sound hc hAB x y a₁))
    exact (ofWord_denote ev.word).mp (Thompson.nfa_sound M _ a₂)
  · simp only [List.any_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨A, B⟩, hAB, ⟨hwf, h₁⟩, h₂⟩ := h
    intro x y hxy
    have a₁ := widen_sub hF A (Thompson.nfa_sound M A.widen (Guarded.prove_sound hθ h₁ x y hxy))
    have a₂ := Guarded.prove_sound hθ h₂ x y
      (Thompson.nfa_complete M B hwf (Constraint.subsets_sound hc hAB x y a₁))
    exact Thompson.nfa_sound M .zero a₂

/-- **A saturation that checks adds nothing**, where the theory is sound,
the assumptions hold, `po` is transitive and `any` relates every two
events. -/
theorem saturates_sound (hθ : θ.Sound M loc) (hF : Facts M) {hyps : List Constraint}
    (hh : ∀ c ∈ hyps, c.Holds M) {before after : NFA Label} {ev : Evidence}
    (h : saturates θ hyps before after ev = true) :
    Rel.Sub (after.denote (Label.denote M)) (before.denote (Label.denote M)) := by
  simp only [saturates, Bool.and_eq_true, Option.isNone_iff_eq_none, List.all_eq_true,
    List.any_eq_true] at h
  obtain ⟨⟨hcheck, hinc⟩, c, hc, hj⟩ := h
  exact ev.check_sound hcheck (justifies_sound hθ hF (hh c hc) hj)
    (fun a b hab => hθ.labelIncl (hinc (a, b) hab))

end KaterCert
