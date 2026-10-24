import KaterCert.Guarded

/-!
# Per-location variants on cycles (`saturateLoc`)

For `A & id`, Kater replaces a step `[pre];r;[post]` of the left automaton
by its per-location variant (`po` by `po-loc`) when every step that can come
before it, and every step that can come after it, is a predicate or keeps
the location (`Theory::isEco`). On a cycle through the step, the steps around
it then lead from where it ends back to where it starts on one location, so
the step itself is within the variant.

`check X Y` verifies that `Y` is `X` with some steps so replaced: each step
of `X` is one of `Y`, or its replacement is, and then the states that reach
its source, and those its destination reaches, are closed sets whose steps
keep the location. The search for the closed sets is not proved; the check
of them is. `check_sound`: each cycle of `X` is one of `Y`.

This mirrors the C++ region `saturateLoc` (`src/Saturation.cpp`):
`scripts/check-mirrors.sh` reports when it changes.
-/

namespace KaterCert

universe u

namespace NFA

variable {L : Type}

/-- `A.Run p w q`: `A` reads `w` from `p` to `q`. -/
inductive Run (A : NFA L) : Nat → List L → Nat → Prop
  | nil (p : Nat) : A.Run p [] p
  | cons {p : Nat} {a : L} {q : Nat} {w : List L} {r : Nat} :
      (a, q) ∈ A.trans p → A.Run q w r → A.Run p (a :: w) r

theorem Run.snoc {A : NFA L} {p q r : Nat} {w : List L} {a : L} (h : A.Run p w q)
    (ha : (a, r) ∈ A.trans q) : A.Run p (w ++ [a]) r := by
  induction h with
  | nil => exact .cons ha (.nil r)
  | cons ht _ ih => exact .cons ht (ih ha)

end NFA

namespace Loc

/-- A step keeps the location: it is a predicate, or of a relation that does. -/
def good (θ : Theory) (l : Label) : Bool :=
  match l.rel with
  | none => true
  | some r => θ.keepsLoc r

/-- `l` with its relation replaced by its per-location variant. -/
def replaced (θ : Theory) (l : Label) : Option Label :=
  match l.rel with
  | some r => (θ.perLoc r).map fun r' => { l with rel := some r' }
  | none => none

/-- `B` is closed under predecessors in `X`, and every step into it keeps
the location. -/
def closedBack (θ : Theory) (X : NFA Label) (B : List Nat) : Bool :=
  (List.range X.size).all fun p => (X.trans p).all fun (l, q) =>
    !B.contains q || (B.contains p && good θ l)

/-- `F` is closed under successors in `X`, and every step out of it keeps
the location. -/
def closedFwd (θ : Theory) (X : NFA Label) (F : List Nat) : Bool :=
  F.all fun p => (X.trans p).all fun (l, q) => F.contains q && good θ l

/-- The states that reach `s` in `X` (not proved: `closedBack` checks). -/
def reaching (X : NFA Label) (s : Nat) : List Nat := Id.run do
  let mut seen := Array.replicate X.size false
  let mut out := [s]
  if s < X.size then seen := seen.set! s true
  let mut work := [s]
  let preds : Array (List Nat) := Id.run do
    let mut ps := Array.replicate X.size []
    for p in [0:X.size] do
      for (_, q) in X.trans p do
        if q < X.size then ps := ps.modify q (p :: ·)
    return ps
  for _ in [0:X.size + 1] do
    match work with
    | [] => break
    | q :: rest =>
      work := rest
      for p in preds.getD q [] do
        if !seen.getD p true then
          seen := seen.set! p true
          out := p :: out
          work := p :: work
  return out

/-- The states `X` reaches from `d` (not proved: `closedFwd` checks). -/
def reachable (X : NFA Label) (d : Nat) : List Nat := Id.run do
  let mut seen := Array.replicate X.size false
  let mut out := [d]
  if d < X.size then seen := seen.set! d true
  let mut work := [d]
  for _ in [0:X.size + 1] do
    match work with
    | [] => break
    | p :: rest =>
      work := rest
      for (_, q) in X.trans p do
        if !seen.getD q true then
          seen := seen.set! q true
          out := q :: out
          work := q :: work
  return out

/-- Each step of `X` is a step of `Y`, or its replacement is, around which
`X` keeps the location. -/
def stepsOk (θ : Theory) (X Y : NFA Label) : Bool :=
  (List.range X.size).all fun p => (X.trans p).all fun (l, q) =>
    (Y.trans p).contains (l, q) ||
      match replaced θ l with
      | some l' =>
        (Y.trans p).contains (l', q) &&
          (let B := reaching X p
           B.contains p && closedBack θ X B) &&
          (let F := reachable X q
           F.contains q && closedFwd θ X F)
      | none => false

/-- `Y` is `X` with steps replaced by their per-location variants where
cycles keep the location. -/
def check (θ : Theory) (X Y : NFA Label) : Bool :=
  X.start.all (Y.start.contains ·) &&
    (List.range X.accepting.size).all (fun p => !X.isAccepting p || Y.isAccepting p) &&
    stepsOk θ X Y

variable {E : Type u} {θ : Theory} {M : Interp E} {loc : Rel E}

theorem lt_of_mem_trans {X : NFA Label} {p : Nat} {t : Label × Nat} (h : t ∈ X.trans p) :
    p < X.size := by
  rcases Nat.lt_or_ge p X.size with hp | hp
  · exact hp
  · simp [NFA.trans, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by exact hp)] at h

theorem lt_of_isAccepting {X : NFA Label} {p : Nat} (h : X.isAccepting p = true) :
    p < X.accepting.size := by
  rcases Nat.lt_or_ge p X.accepting.size with hp | hp
  · exact hp
  · simp [NFA.isAccepting, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by exact hp)] at h

theorem good_loc (hθ : θ.Sound M loc) {l : Label} (h : good θ l = true) {c c' : E}
    (hl : l.denote M c c') : loc c c' := by
  unfold good at h
  unfold Label.denote at hl
  split at h <;> rename_i hr <;> simp only [hr] at hl
  · obtain ⟨rfl, -⟩ := hl
    exact hθ.loc_refl c
  · exact hθ.keepsLoc _ h c c' hl.2.1

theorem closedBack_run (hθ : θ.Sound M loc) {X : NFA Label} {B : List Nat}
    (hB : closedBack θ X B = true) :
    ∀ {p u q}, X.Run p u q → q ∈ B → p ∈ B ∧ ∀ c c', wordRel (Label.denote M) u c c' → loc c c'
  | _, _, _, .nil p, hq => ⟨hq, fun c c' h => (show c = c' from h) ▸ hθ.loc_refl c⟩
  | p, _, _, .cons (a := a) (q := q₁) ht hw, hq => by
    obtain ⟨hq₁, ih⟩ := closedBack_run hθ hB hw hq
    have hp := lt_of_mem_trans ht
    simp only [closedBack, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
      List.contains_iff_mem, Bool.and_eq_true] at hB
    rcases hB p hp (a, q₁) ht with h | ⟨hpB, hgood⟩
    · simp at h; exact absurd hq₁ h
    · refine ⟨hpB, fun c c' h => ?_⟩
      obtain ⟨d, hd, hw'⟩ := h
      exact hθ.loc_trans _ _ _ (good_loc hθ hgood hd) (ih d c' hw')

theorem closedFwd_accepts (hθ : θ.Sound M loc) {X : NFA Label} {F : List Nat}
    (hF : closedFwd θ X F = true) :
    ∀ {p w}, X.Accepts p w → p ∈ F → ∀ c c', wordRel (Label.denote M) w c c' → loc c c'
  | _, _, .nil _, _, c, c', h => (show c = c' from h) ▸ hθ.loc_refl c
  | p, _, .cons (a := a) (q' := q) ht hw, hp, c, c', h => by
    simp only [closedFwd, List.all_eq_true, List.contains_iff_mem, Bool.and_eq_true] at hF
    obtain ⟨hq, hgood⟩ := hF p hp (a, q) ht
    obtain ⟨d, hd, hw'⟩ := h
    exact hθ.loc_trans _ _ _ (good_loc hθ hgood hd) (closedFwd_accepts hθ
      (by simpa [closedFwd, List.all_eq_true, List.contains_iff_mem] using hF) hw hq d c' hw')

theorem replaced_denote (hθ : θ.Sound M loc) {l l' : Label} (h : replaced θ l = some l')
    {c c' : E} (hl : l.denote M c c') (hloc : loc c c') : l'.denote M c c' := by
  unfold replaced at h
  split at h
  · rename_i r hr
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    simp only [Label.denote, hr] at hl ⊢
    exact ⟨hl.1, hθ.perLoc r r' hr' c c' hl.2.1 hloc, hl.2.2⟩
  · simp at h

theorem claim (hθ : θ.Sound M loc) {X Y : NFA Label} (h : stepsOk θ X Y = true)
    (hacc : ∀ p, X.isAccepting p = true → Y.isAccepting p = true) {a : E} :
    ∀ {p v}, X.Accepts p v → ∀ {q₀ u c}, X.Run q₀ u p → wordRel (Label.denote M) u a c →
      wordRel (Label.denote M) v c a →
      ∃ v', Y.Accepts p v' ∧ wordRel (Label.denote M) v' c a
  | _, _, .nil hp, _, _, _, _, _, hv => ⟨[], .nil (hacc _ hp), hv⟩
  | p, _, .cons (a := l) (q' := p') (w := v₁) ht hw, q₀, u, c, hu, hua, hv => by
    obtain ⟨c', hl, hv₁⟩ := hv
    have hu' : X.Run q₀ (u ++ [l]) p' := hu.snoc ht
    have hua' : wordRel (Label.denote M) (u ++ [l]) a c' := by
      rw [wordRel_append]
      exact ⟨c, hua, c', hl, rfl⟩
    have hp := lt_of_mem_trans ht
    simp only [stepsOk, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      List.contains_iff_mem] at h
    rcases h p hp (l, p') ht with hkept | hrep
    · obtain ⟨v', hv', hr'⟩ := claim hθ (by simpa [stepsOk, List.all_eq_true, List.mem_range,
        List.contains_iff_mem] using h) hacc hw hu' hua' hv₁
      exact ⟨l :: v', .cons hkept hv', c', hl, hr'⟩
    · split at hrep
      · rename_i l' hl'
        simp only [Bool.and_eq_true, List.contains_iff_mem] at hrep
        obtain ⟨⟨hmem, hBp, hB⟩, hFq, hF⟩ := hrep
        have hac : loc a c := (closedBack_run hθ hB hu hBp).2 a c hua
        have hca : loc c' a := closedFwd_accepts hθ hF hw hFq c' a hv₁
        have hcc : loc c c' :=
          hθ.loc_trans _ _ _ (hθ.loc_symm _ _ hac) (hθ.loc_symm _ _ hca)
        obtain ⟨v', hv', hr'⟩ := claim hθ (by simpa [stepsOk, List.all_eq_true, List.mem_range,
          List.contains_iff_mem] using h) hacc hw hu' hua' hv₁
        exact ⟨l' :: v', .cons hmem hv', c', replaced_denote hθ hl' hl hcc, hr'⟩
      · simp at hrep

/-- **Soundness**: if `check` accepts, and the theory is sound, each cycle of
`X` is one of `Y`. -/
theorem check_sound (hθ : θ.Sound M loc) {X Y : NFA Label} (h : check θ X Y = true) :
    ∀ a, X.denote (Label.denote M) a a → Y.denote (Label.denote M) a a := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hstart, hacc⟩, hsteps⟩ := h
  have hacc' : ∀ p, X.isAccepting p = true → Y.isAccepting p = true := by
    intro p hp
    rcases hacc p (lt_of_isAccepting hp) with h | h
    · simp [hp] at h
    · exact h
  rintro a ⟨q₀, hq₀, w, hw, hr⟩
  obtain ⟨w', hw', hr'⟩ := claim hθ hsteps hacc' hw (.nil q₀) rfl hr
  exact ⟨q₀, hstart q₀ hq₀, w', hw', hr'⟩

end Loc

end KaterCert
