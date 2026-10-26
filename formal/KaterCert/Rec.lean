import KaterCert.Exp

/-!
# Recursive definitions

`let rec x₁ = e₁ and ... and xₖ = eₖ` (`MutRecRE`) is left-linear: Kater's
parser accepts a recursive relation only first in a sequence, and not under
`*` or `+` (`ParsingDriver::checkMutRecDisjunctLeftRec`). So each definition
is, as a relation, `cᵢ | x_j ; a | ...`: a part `cᵢ` without references, and
parts that start with a reference and go on without one (`Exp.nf`). The
least solution is then reachability: `xᵢ` relates what a `cᵢ` does, and
what `x_j ; a` does for each part of `eᵢ` (`Reach`, `fix_iff_reach`). The
automaton of a `fix` (`Thompson`) has a state for each relation and an
automaton for each part between them.
-/

namespace KaterCert

universe u

namespace Exp

/-- No reference of the innermost `fix` is free in the expression (those of
a `fix` are its own). -/
def refFree : Exp → Bool
  | .label _ | .zero => true
  | .alt a b | .seq a b => a.refFree && b.refFree
  | .star a | .plus a | .opt a => a.refFree
  | .ref _ => false
  | .fix _ _ => true
  | .inv a => a.refFree

mutual

/-- A size: what `Thompson.build` recurses on. -/
def size : Exp → Nat
  | .label _ | .zero | .ref _ => 1
  | .alt a b | .seq a b => a.size + b.size + 1
  | .star a | .plus a | .opt a | .inv a => a.size + 1
  | .fix _ defs => defs.size + 1

def _root_.KaterCert.Defs.size : Defs → Nat
  | .nil => 0
  | .cons e es => e.size + es.size

end

theorem size_pos : ∀ e : Exp, 0 < e.size
  | .label _ | .zero | .ref _ => by simp [size]
  | .alt _ _ | .seq _ _ => by simp [size]
  | .star _ | .plus _ | .opt _ | .inv _ => by simp [size]
  | .fix _ _ => by simp [size]

/-- A definition as `c | x_j ; a | ...`: the part `c` without references and
the parts `(j, a)` that start with the reference `x_j`; `none` if the
definition is not left-linear. -/
def nf : Exp → Option (Exp × List (Nat × Exp))
  | .label l => some (.label l, [])
  | .zero => some (.zero, [])
  | .ref j => some (.zero, [(j, .label .eps)])
  | .alt a b =>
    match a.nf, b.nf with
    | some (ca, la), some (cb, lb) => some (.alt ca cb, la ++ lb)
    | _, _ => none
  | .seq a b =>
    if b.refFree then
      match a.nf with
      | some (ca, la) => some (.seq ca b, la.map fun p => (p.1, .seq p.2 b))
      | none => none
    else none
  | .star a => if a.refFree then some (.star a, []) else none
  | .plus a => if a.refFree then some (.plus a, []) else none
  | .opt a =>
    match a.nf with
    | some (ca, la) => some (.opt ca, la)
    | none => none
  | .fix m defs => some (.fix m defs, [])
  | .inv a => if a.refFree then some (.inv a, []) else none

variable {E : Type u} {M : Interp E}

/-- An expression without free references means the same whatever they do. -/
theorem refFree_denoteIn : ∀ {e : Exp}, e.refFree = true → ∀ (ρ : Nat → Rel E) {x y : E},
    e.denoteIn M ρ x y ↔ e.denote M x y
  | .label _, _, _, _, _ => Iff.rfl
  | .zero, _, _, _, _ => Iff.rfl
  | .alt a b, h, ρ, x, y => by
    simp only [refFree, Bool.and_eq_true] at h
    simp only [denote, denoteIn, Rel.union]
    rw [refFree_denoteIn h.1 ρ, refFree_denoteIn h.2 ρ]
  | .seq a b, h, ρ, x, y => by
    simp only [refFree, Bool.and_eq_true] at h
    simp only [denote, denoteIn, Rel.comp]
    constructor
    · rintro ⟨z, h₁, h₂⟩
      exact ⟨z, (refFree_denoteIn h.1 ρ).mp h₁, (refFree_denoteIn h.2 ρ).mp h₂⟩
    · rintro ⟨z, h₁, h₂⟩
      exact ⟨z, (refFree_denoteIn h.1 ρ).mpr h₁, (refFree_denoteIn h.2 ρ).mpr h₂⟩
  | .star a, h, ρ, x, y => by
    simp only [refFree] at h
    simp only [denote, denoteIn]
    constructor
    · exact fun h' => Rel.Star.mono (fun _ _ => (refFree_denoteIn h ρ).mp) _ _ h'
    · exact fun h' => Rel.Star.mono (fun _ _ => (refFree_denoteIn h ρ).mpr) _ _ h'
  | .plus a, h, ρ, x, y => by
    simp only [refFree] at h
    simp only [denote, denoteIn, Rel.Plus, Rel.comp]
    constructor
    · rintro ⟨z, h₁, h₂⟩
      exact ⟨z, (refFree_denoteIn h ρ).mp h₁,
        Rel.Star.mono (fun _ _ => (refFree_denoteIn h ρ).mp) _ _ h₂⟩
    · rintro ⟨z, h₁, h₂⟩
      exact ⟨z, (refFree_denoteIn h ρ).mpr h₁,
        Rel.Star.mono (fun _ _ => (refFree_denoteIn h ρ).mpr) _ _ h₂⟩
  | .opt a, h, ρ, x, y => by
    simp only [refFree] at h
    simp only [denote, denoteIn, Rel.Opt, Rel.union]
    rw [refFree_denoteIn h ρ]
  | .ref _, h, _, _, _ => by simp [refFree] at h
  | .fix _ _, _, _, _, _ => Iff.rfl
  | .inv a, h, ρ, x, y => by
    simp only [refFree] at h
    simp only [denote, denoteIn, Rel.inv]
    exact refFree_denoteIn h ρ

/-- `denote` is `denoteIn` with references relating nothing. -/
theorem denote_iff_denoteIn : ∀ (e : Exp) {x y : E},
    e.denote M x y ↔ e.denoteIn M (fun _ => Rel.empty) x y
  | .label _, _, _ => Iff.rfl
  | .zero, _, _ => Iff.rfl
  | .alt a b, x, y => by
    simp only [denote, denoteIn, Rel.union]
    rw [denote_iff_denoteIn a, denote_iff_denoteIn b]
  | .seq a b, x, y => by
    simp only [denote, denoteIn, Rel.comp]
    exact ⟨fun ⟨z, h₁, h₂⟩ => ⟨z, (denote_iff_denoteIn a).mp h₁, (denote_iff_denoteIn b).mp h₂⟩,
      fun ⟨z, h₁, h₂⟩ => ⟨z, (denote_iff_denoteIn a).mpr h₁, (denote_iff_denoteIn b).mpr h₂⟩⟩
  | .star a, x, y => by
    simp only [denote, denoteIn]
    exact ⟨fun h => Rel.Star.mono (fun _ _ => (denote_iff_denoteIn a).mp) _ _ h,
      fun h => Rel.Star.mono (fun _ _ => (denote_iff_denoteIn a).mpr) _ _ h⟩
  | .plus a, x, y => by
    simp only [denote, denoteIn, Rel.Plus, Rel.comp]
    exact ⟨fun ⟨z, h₁, h₂⟩ => ⟨z, (denote_iff_denoteIn a).mp h₁,
        Rel.Star.mono (fun _ _ => (denote_iff_denoteIn a).mp) _ _ h₂⟩,
      fun ⟨z, h₁, h₂⟩ => ⟨z, (denote_iff_denoteIn a).mpr h₁,
        Rel.Star.mono (fun _ _ => (denote_iff_denoteIn a).mpr) _ _ h₂⟩⟩
  | .opt a, x, y => by
    simp only [denote, denoteIn, Rel.Opt, Rel.union]
    rw [denote_iff_denoteIn a]
  | .ref _, _, _ => Iff.rfl
  | .fix _ _, _, _ => Iff.rfl
  | .inv a, x, y => by
    simp only [denote, denoteIn, Rel.inv]
    exact denote_iff_denoteIn a

/-- What the normal form of a definition gives: parts without references, no
larger than the definition, that make up what it denotes. -/
theorem nf_spec : ∀ {e : Exp} {c : Exp} {L : List (Nat × Exp)}, e.nf = some (c, L) →
    c.refFree = true ∧ (∀ p ∈ L, p.2.refFree = true) ∧ c.size ≤ e.size ∧
      (∀ p ∈ L, p.2.size ≤ e.size) ∧
      ∀ (ρ : Nat → Rel E) {x y : E}, e.denoteIn M ρ x y ↔
        c.denote M x y ∨ ∃ p ∈ L, ∃ z, ρ p.1 x z ∧ p.2.denote M z y
  | .label l, c, L, h => by
    simp only [nf, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, by simp, Nat.le_refl _, by simp, fun ρ x y => ?_⟩
    simp [denote, denoteIn]
  | .zero, c, L, h => by
    simp only [nf, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, by simp, Nat.le_refl _, by simp, fun ρ x y => ?_⟩
    simp [denote, denoteIn, Rel.empty]
  | .ref j, c, L, h => by
    simp only [nf, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, by simp [refFree], Nat.le_refl _, by simp [size], fun ρ x y => ?_⟩
    simp only [denoteIn, denote, Rel.empty, false_or, List.mem_singleton, exists_eq_left]
    constructor
    · intro h
      exact ⟨y, h, (Label.denote_eps M).mpr rfl⟩
    · rintro ⟨z, hz, hzy⟩
      exact ((Label.denote_eps M).mp hzy) ▸ hz
  | .alt a b, c, L, h => by
    simp only [nf] at h
    split at h
    · rename_i ca la cb lb ha hb
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨ra, rla, sa, sla, da⟩ := nf_spec ha
      obtain ⟨rb, rlb, sb, slb, db⟩ := nf_spec hb
      refine ⟨by simp [refFree, ra, rb], fun p hp => ?_, by simp [size]; omega, fun p hp => ?_,
        fun ρ x y => ?_⟩
      · simp only [List.mem_append] at hp
        rcases hp with hp | hp
        · exact rla p hp
        · exact rlb p hp
      · simp only [List.mem_append] at hp
        simp only [size]
        rcases hp with hp | hp
        · have := sla p hp; omega
        · have := slb p hp; omega
      · simp only [denoteIn, Rel.union, denote] at da db ⊢
        rw [da ρ, db ρ]
        simp only [List.mem_append]
        constructor
        · rintro ((h | ⟨p, hp, h⟩) | (h | ⟨p, hp, h⟩))
          · exact .inl (.inl h)
          · exact .inr ⟨p, .inl hp, h⟩
          · exact .inl (.inr h)
          · exact .inr ⟨p, .inr hp, h⟩
        · rintro ((h | h) | ⟨p, hp | hp, h⟩)
          · exact .inl (.inl h)
          · exact .inr (.inl h)
          · exact .inl (.inr ⟨p, hp, h⟩)
          · exact .inr (.inr ⟨p, hp, h⟩)
    · simp at h
  | .seq a b, c, L, h => by
    simp only [nf] at h
    split at h
    · rename_i hb
      split at h
      · rename_i ca la ha
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ra, rla, sa, sla, da⟩ := nf_spec ha
        refine ⟨by simp [refFree, ra, hb], fun p hp => ?_, by simp [size]; omega, fun p hp => ?_,
          fun ρ x y => ?_⟩
        · simp only [List.mem_map] at hp
          obtain ⟨q, hq, rfl⟩ := hp
          simp [refFree, rla q hq, hb]
        · simp only [List.mem_map] at hp
          obtain ⟨q, hq, rfl⟩ := hp
          have := sla q hq
          simp only [size]; omega
        · simp only [denoteIn, Rel.comp, denote] at da ⊢
          simp only [List.mem_map]
          constructor
          · rintro ⟨z, ha', hb'⟩
            rw [refFree_denoteIn hb ρ] at hb'
            rcases (da ρ).mp ha' with h | ⟨p, hp, w, hw, hpw⟩
            · exact .inl ⟨z, h, hb'⟩
            · exact .inr ⟨(p.1, .seq p.2 b), ⟨p, hp, rfl⟩, w, hw, z, hpw, hb'⟩
          · rintro (⟨z, hc, hb'⟩ | ⟨_, ⟨p, hp, rfl⟩, w, hw, z, hpw, hb'⟩)
            · exact ⟨z, (da ρ).mpr (.inl hc), (refFree_denoteIn hb ρ).mpr hb'⟩
            · exact ⟨z, (da ρ).mpr (.inr ⟨p, hp, w, hw, hpw⟩), (refFree_denoteIn hb ρ).mpr hb'⟩
      · simp at h
    · simp at h
  | .star a, c, L, h => by
    simp only [nf] at h
    split at h
    · rename_i ha
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp [refFree, ha], by simp, Nat.le_refl _, by simp, fun ρ x y => ?_⟩
      simp only [List.not_mem_nil, false_and, exists_false, or_false]
      exact refFree_denoteIn (e := .star a) (by simp [refFree, ha]) ρ
    · simp at h
  | .plus a, c, L, h => by
    simp only [nf] at h
    split at h
    · rename_i ha
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp [refFree, ha], by simp, Nat.le_refl _, by simp, fun ρ x y => ?_⟩
      simp only [List.not_mem_nil, false_and, exists_false, or_false]
      exact refFree_denoteIn (e := .plus a) (by simp [refFree, ha]) ρ
    · simp at h
  | .opt a, c, L, h => by
    simp only [nf] at h
    split at h
    · rename_i ca la ha
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨ra, rla, sa, sla, da⟩ := nf_spec ha
      refine ⟨by simp [refFree, ra], rla, by simp [size]; omega, fun p hp => ?_,
        fun ρ x y => ?_⟩
      · have := sla p hp; simp only [size]; omega
      · simp only [denoteIn, Rel.Opt, Rel.union, denote] at da ⊢
        rw [da ρ]
        constructor
        · rintro (h | h | h)
          · exact .inl (.inl h)
          · exact .inl (.inr h)
          · exact .inr h
        · rintro ((h | h) | h)
          · exact .inl h
          · exact .inr (.inl h)
          · exact .inr (.inr h)
    · simp at h
  | .fix m defs, c, L, h => by
    simp only [nf, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, by simp, Nat.le_refl _, by simp, fun ρ x y => ?_⟩
    simp only [List.not_mem_nil, false_and, exists_false, or_false]
    exact refFree_denoteIn (e := .fix m defs) rfl ρ
  | .inv a, c, L, h => by
    simp only [nf] at h
    split at h
    · rename_i ha
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp [refFree, ha], by simp, Nat.le_refl _, by simp, fun ρ x y => ?_⟩
      simp only [List.not_mem_nil, false_and, exists_false, or_false]
      exact refFree_denoteIn (e := .inv a) (by simp [refFree, ha]) ρ
    · simp at h

end Exp

namespace Defs

variable {E : Type u} {M : Interp E}

/-- The `i`-th definition's relation is what the `i`-th definition denotes. -/
theorem denoteIn_get (ρ : Nat → Rel E) : ∀ (defs : Defs) (i : Nat) {x y : E},
    defs.denoteIn M ρ i x y ↔ (defs.get i).denoteIn M ρ x y
  | .nil, _, _, _ => by simp [Defs.denoteIn, Defs.get, Exp.denoteIn]
  | .cons _ _, 0, _, _ => Iff.rfl
  | .cons _ es, i + 1, _, _ => denoteIn_get ρ es i

theorem get_of_lt : ∀ (defs : Defs) (i : Nat), i < defs.toList.length →
    defs.toList[i]? = some (defs.get i)
  | .nil, _, h => by simp [toList] at h
  | .cons e _, 0, _ => by simp [toList, get]
  | .cons _ es, i + 1, h => by
    simp only [toList, List.length_cons] at h
    simpa [toList, get] using get_of_lt es i (by omega)

theorem get_of_ge : ∀ (defs : Defs) (i : Nat), defs.toList.length ≤ i → defs.get i = .zero
  | .nil, _, _ => rfl
  | .cons _ _, 0, h => by simp [toList] at h
  | .cons _ es, i + 1, h => by
    simp only [toList, List.length_cons] at h
    exact get_of_ge es i (by omega)

theorem size_lt : ∀ {defs : Defs} {e : Exp}, e ∈ defs.toList → e.size < defs.size + 1
  | .nil, _, h => by simp [toList] at h
  | .cons d ds, e, h => by
    simp only [toList, List.mem_cons] at h
    simp only [Defs.size]
    rcases h with rfl | h
    · omega
    · have := size_lt h; omega

end Defs

/-! ## The least solution as reachability -/

/-- `Reach N M i x y`: the definitions, in normal form `N`, make `xᵢ` relate
`x` to `y`. -/
inductive Reach {E : Type u} (N : List (Exp × List (Nat × Exp))) (M : Interp E) :
    Nat → Rel E
  | base {i : Nat} {c : Exp} {L : List (Nat × Exp)} {x y : E} :
      N[i]? = some (c, L) → c.denote M x y → Reach N M i x y
  | step {i : Nat} {c : Exp} {L : List (Nat × Exp)} {j : Nat} {a : Exp} {x z y : E} :
      N[i]? = some (c, L) → (j, a) ∈ L → Reach N M j x z → a.denote M z y → Reach N M i x y

theorem lt_of_getElem? {α : Type _} {l : List α} {i : Nat} {x : α} (h : l[i]? = some x) :
    i < l.length := by
  rcases Nat.lt_or_ge i l.length with h' | h'
  · exact h'
  · simp [List.getElem?_eq_none h'] at h

theorem Reach.lt {E : Type u} {N : List (Exp × List (Nat × Exp))} {M : Interp E} {i : Nat}
    {x y : E} (h : Reach N M i x y) : i < N.length := by
  cases h with
  | base hi _ => exact lt_of_getElem? hi
  | step hi _ _ _ => exact lt_of_getElem? hi

/-- The normal forms of definitions, if they are all left-linear. -/
def Defs.nfs (defs : Defs) : Option (List (Exp × List (Nat × Exp))) := defs.toList.mapM Exp.nf

theorem mapM_nf_get {es : List Exp} {N : List (Exp × List (Nat × Exp))}
    (h : es.mapM Exp.nf = some N) :
    N.length = es.length ∧
      ∀ (i : Nat) (e : Exp), es[i]? = some e → ∃ p, N[i]? = some p ∧ e.nf = some p := by
  induction es generalizing N with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun i e he => by simp at he⟩
  | cons e es ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨p, hp, qs, hqs, rfl⟩ := h
    obtain ⟨hlen, hget⟩ := ih hqs
    refine ⟨by simp [hlen], fun i e' he' => ?_⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he'
      subst he'
      exact ⟨p, rfl, hp⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at he' ⊢
      exact hget i e' he'

/-- The `i`-th normal form is that of the `i`-th definition. -/
theorem Defs.nf_of_nfs {defs : Defs} {N : List (Exp × List (Nat × Exp))} (hN : defs.nfs = some N)
    {i : Nat} {c : Exp} {L : List (Nat × Exp)} (hi : N[i]? = some (c, L)) :
    defs.get i ∈ defs.toList ∧ (defs.get i).nf = some (c, L) := by
  obtain ⟨hlen, hget⟩ := mapM_nf_get hN
  have hlt : i < defs.toList.length := hlen ▸ lt_of_getElem? hi
  have hmem := Defs.get_of_lt defs i hlt
  obtain ⟨p, hp, hnf⟩ := hget i (defs.get i) hmem
  rw [hi] at hp
  cases hp
  exact ⟨List.mem_of_getElem? hmem, hnf⟩

/-- The parts of the normal forms are no larger than the definitions. -/
theorem Defs.size_of_nfs {defs : Defs} {N : List (Exp × List (Nat × Exp))} (hN : defs.nfs = some N)
    {i : Nat} {c : Exp} {L : List (Nat × Exp)} (hi : N[i]? = some (c, L)) :
    c.size ≤ defs.size ∧ ∀ p ∈ L, p.2.size ≤ defs.size := by
  obtain ⟨hmem, hnf⟩ := Defs.nf_of_nfs hN hi
  obtain ⟨-, -, hc, hL, -⟩ :=
    Exp.nf_spec (E := PUnit.{1}) (M := { rel := fun _ => Rel.empty, pred := fun _ _ => False }) hnf
  have := Defs.size_lt hmem
  exact ⟨by omega, fun p hp => by have := hL p hp; omega⟩

/-! ## Well-formed expressions -/

namespace Exp

mutual

/-- Every `fix` of the expression is left-linear, as Kater's parser makes
them: what the automaton of an expression needs to read all it denotes
(`Thompson.complete`). -/
def wellFormed : Exp → Bool
  | .label _ | .zero | .ref _ => true
  | .alt a b | .seq a b => a.wellFormed && b.wellFormed
  | .star a | .plus a | .opt a | .inv a => a.wellFormed
  | .fix _ defs => defs.nfs.isSome && defs.wellFormed

def _root_.KaterCert.Defs.wellFormed : Defs → Bool
  | .nil => true
  | .cons e es => e.wellFormed && es.wellFormed

end

/-- The parts of a well-formed definition's normal form are well-formed. -/
theorem nf_wellFormed : ∀ {e c : Exp} {L : List (Nat × Exp)}, e.nf = some (c, L) →
    e.wellFormed = true → c.wellFormed = true ∧ ∀ p ∈ L, p.2.wellFormed = true
  | .label _, c, L, h, _ => by
    simp only [nf, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simp⟩
  | .zero, c, L, h, _ => by
    simp only [nf, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simp⟩
  | .ref _, c, L, h, _ => by
    simp only [nf, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simp [wellFormed]⟩
  | .alt a b, c, L, h, hw => by
    simp only [nf] at h
    split at h
    · rename_i ca la cb lb ha hb
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [wellFormed, Bool.and_eq_true] at hw
      obtain ⟨wa, wla⟩ := nf_wellFormed ha hw.1
      obtain ⟨wb, wlb⟩ := nf_wellFormed hb hw.2
      refine ⟨by simp [wellFormed, wa, wb], fun p hp => ?_⟩
      simp only [List.mem_append] at hp
      rcases hp with hp | hp
      · exact wla p hp
      · exact wlb p hp
    · simp at h
  | .seq a b, c, L, h, hw => by
    simp only [nf] at h
    split at h
    · split at h
      · rename_i ca la ha
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [wellFormed, Bool.and_eq_true] at hw
        obtain ⟨wa, wla⟩ := nf_wellFormed ha hw.1
        refine ⟨by simp [wellFormed, wa, hw.2], fun p hp => ?_⟩
        simp only [List.mem_map] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        simp [wellFormed, wla q hq, hw.2]
      · simp at h
    · simp at h
  | .star a, c, L, h, hw => by
    simp only [nf] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hw, by simp⟩
    · simp at h
  | .plus a, c, L, h, hw => by
    simp only [nf] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hw, by simp⟩
    · simp at h
  | .opt a, c, L, h, hw => by
    simp only [nf] at h
    split at h
    · rename_i ca la ha
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [wellFormed] at hw
      obtain ⟨wa, wla⟩ := nf_wellFormed ha hw
      exact ⟨by simp [wellFormed, wa], wla⟩
    · simp at h
  | .fix _ _, c, L, h, hw => by
    simp only [nf, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hw, by simp⟩
  | .inv a, c, L, h, hw => by
    simp only [nf] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hw, by simp⟩
    · simp at h

end Exp

theorem Defs.wellFormed_of_mem : ∀ {defs : Defs} {e : Exp}, defs.wellFormed = true →
    e ∈ defs.toList → e.wellFormed = true
  | .nil, _, _, h => by simp [Defs.toList] at h
  | .cons _ _, _, hw, h => by
    simp only [Defs.wellFormed, Bool.and_eq_true] at hw
    simp only [Defs.toList, List.mem_cons] at h
    rcases h with rfl | h
    · exact hw.1
    · exact wellFormed_of_mem hw.2 h

/-- The parts of the normal forms of well-formed definitions are
well-formed. -/
theorem Defs.wellFormed_of_nfs {defs : Defs} {N : List (Exp × List (Nat × Exp))}
    (hN : defs.nfs = some N) (hw : defs.wellFormed = true) {i : Nat} {c : Exp}
    {L : List (Nat × Exp)} (hi : N[i]? = some (c, L)) :
    c.wellFormed = true ∧ ∀ p ∈ L, p.2.wellFormed = true := by
  obtain ⟨hmem, hnf⟩ := Defs.nf_of_nfs hN hi
  exact Exp.nf_wellFormed hnf (Defs.wellFormed_of_mem hw hmem)

variable {E : Type u} {M : Interp E}

/-- The iterates of definitions from the empty relations. -/
def approx (M : Interp E) (defs : Defs) (n : Nat) : Nat → Rel E :=
  Nat.repeat (Defs.denoteIn M · defs) n (fun _ => Rel.empty)

theorem approx_succ (defs : Defs) (n : Nat) :
    approx M defs (n + 1) = defs.denoteIn M (approx M defs n) := rfl

/-- **The least solution is reachability**: a `fix` whose definitions are
left-linear relates what its definitions, in normal form, reach. -/
theorem fix_iff_reach {main : Nat} {defs : Defs} {N : List (Exp × List (Nat × Exp))}
    (hN : defs.nfs = some N) (ρ : Nat → Rel E) {x y : E} :
    (Exp.fix main defs).denoteIn M ρ x y ↔ Reach N M main x y := by
  obtain ⟨hlen, -⟩ := mapM_nf_get hN
  have hdef : ∀ i c L, N[i]? = some (c, L) → (defs.get i).nf = some (c, L) :=
    fun _ _ _ hi => (Defs.nf_of_nfs hN hi).2
  have hnone : ∀ i, N[i]? = none → ∀ ρ' x y, ¬ defs.denoteIn M ρ' i x y := by
    intro i hi ρ' x y h
    rw [Defs.denoteIn_get] at h
    have hge : defs.toList.length ≤ i := by
      rcases Nat.lt_or_ge i defs.toList.length with h' | h'
      · have := (List.getElem?_eq_none_iff.mp hi); omega
      · exact h'
    rw [Defs.get_of_ge defs i hge] at h
    exact h
  constructor
  · rintro ⟨n, hn⟩
    -- every iterate is within reachability
    have : ∀ n i x y, approx M defs n i x y → Reach N M i x y := by
      intro n
      induction n with
      | zero => intro i x y h; exact absurd h id
      | succ n ih =>
        intro i x y h
        rw [approx_succ] at h
        cases hi : N[i]? with
        | none => exact absurd h (hnone i hi _ x y)
        | some p =>
          obtain ⟨c, L⟩ := p
          rw [Defs.denoteIn_get] at h
          rcases ((Exp.nf_spec (hdef i c L hi)).2.2.2.2 _).mp h with h | ⟨q, hq, z, hz, hq'⟩
          · exact .base hi h
          · exact .step hi hq (ih q.1 x z hz) hq'
    exact this n main x y hn
  · intro h
    -- reachability is reached by some iterate
    have : ∀ i x y, Reach N M i x y → ∃ n, approx M defs n i x y := by
      intro i x y h
      induction h with
      | @base i c L x y hi hc =>
        refine ⟨1, ?_⟩
        rw [approx_succ, Defs.denoteIn_get]
        exact ((Exp.nf_spec (hdef i c L hi)).2.2.2.2 _).mpr (.inl hc)
      | @step i c L j a x z y hi hja _ ha ih =>
        obtain ⟨n, hn⟩ := ih
        refine ⟨n + 1, ?_⟩
        rw [approx_succ, Defs.denoteIn_get]
        exact ((Exp.nf_spec (hdef i c L hi)).2.2.2.2 _).mpr (.inr ⟨(j, a), hja, z, hn, ha⟩)
    exact this main x y h

end KaterCert
