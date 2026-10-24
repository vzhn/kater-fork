import KaterCert.Thompson
import KaterCert.Loc

/-!
# Rotations (`saturateRotate`)

For `A & id <= rot B`, Kater adds to the right automaton every rotation of
its words: for each state `s`, the words `v u` such that it reads `v` from
`s` to an accepting state and `u` from a starting state to `s`. A cycle of a
rotation `v u`, through an event `x`, is a cycle `u v` of the automaton
through the event between `v` and `u`: rotating adds no cycle.

`rotations R` is Lean's own automaton of `R` and its rotations: a copy of
`R`, and for each state `s` two more, the first starting at `s`, the second
accepting at `s`, joined by steps of the identity from the first's accepting
states to the second's starting ones. `rotations_cycle` proves that each
cycle it has is one of `R`. Kater's rotated automaton, normalized, is
compared with it as relations (`Guarded`).
-/

namespace KaterCert

universe u

namespace Rotate

variable (R : NFA Label)

/-- The steps of `R`, within its states, shifted by `off`. -/
def copyT (off : Nat) : List (Nat × Label × Nat) :=
  (List.range R.size).flatMap fun p =>
    (R.trans p).filterMap fun t => if t.2 < R.size then some (off + p, t.1, off + t.2) else none

/-- Where the copies of `s` begin. -/
def base (s : Nat) : Nat := R.size + 2 * R.size * s

/-- The accepting states of `R`, within its states. -/
def finals : List Nat := (List.range R.size).filter R.isAccepting

/-- The starting states of `R`, within its states. -/
def starts : List Nat := R.start.filter (· < R.size)

/-- The steps of `rotations R`. -/
def steps : List (Nat × Label × Nat) :=
  copyT R 0 ++ (List.range R.size).flatMap fun s =>
    copyT R (base R s) ++ copyT R (base R s + R.size) ++
      (finals R).flatMap fun f => (starts R).map fun q => (base R s + f, Label.eps, base R s + R.size + q)

/-- `R` and its rotations. -/
def rotations : NFA Label :=
  NFA.ofList (R.size + 2 * R.size * R.size) (steps R)
    (starts R ++ (List.range R.size).map fun s => base R s + s)
    (finals R ++ (List.range R.size).map fun s => base R s + R.size + s)

/-! ## Rotating adds no cycle -/

variable {R}

theorem le_base (s : Nat) : R.size ≤ base R s := by unfold base; omega

theorem base_mono {s s' : Nat} (h : s < s') : base R s + 2 * R.size ≤ base R s' := by
  unfold base
  have := Nat.mul_le_mul_left (2 * R.size) (show s + 1 ≤ s' from h)
  rw [Nat.mul_add, Nat.mul_one] at this
  omega

/-- The copies of different states do not overlap. -/
theorem base_inj {s s' i j : Nat} (hi : i < 2 * R.size) (hj : j < 2 * R.size)
    (h : base R s + i = base R s' + j) : s = s' ∧ i = j := by
  rcases Nat.lt_trichotomy s s' with hs | hs | hs
  · have := base_mono (R := R) hs; omega
  · subst hs; omega
  · have := base_mono (R := R) hs; omega

theorem mem_copyT {off u v : Nat} {a : Label} :
    (u, a, v) ∈ copyT R off ↔
      ∃ p q, u = off + p ∧ v = off + q ∧ p < R.size ∧ q < R.size ∧ (a, q) ∈ R.trans p := by
  simp only [copyT, List.mem_flatMap, List.mem_range, List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, ⟨b, q⟩, hmem, hf⟩
    simp only at hf
    split at hf
    · rename_i hq
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl, rfl⟩ := hf
      exact ⟨p, q, rfl, rfl, hp, hq, hmem⟩
    · simp at hf
  · rintro ⟨p, q, rfl, rfl, hp, hq, hmem⟩
    exact ⟨p, hp, (a, q), hmem, by simp [hq]⟩

theorem mem_steps {t : Nat × Label × Nat} :
    t ∈ steps R ↔ t ∈ copyT R 0 ∨ ∃ s < R.size, t ∈ copyT R (base R s) ∨
      t ∈ copyT R (base R s + R.size) ∨
        ∃ f ∈ finals R, ∃ q ∈ starts R, t = (base R s + f, Label.eps, base R s + R.size + q) := by
  simp only [steps, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro (h | ⟨s, hs, (h | h) | ⟨f, hf, q, hq, rfl⟩⟩)
    · exact .inl h
    · exact .inr ⟨s, hs, .inl h⟩
    · exact .inr ⟨s, hs, .inr (.inl h)⟩
    · exact .inr ⟨s, hs, .inr (.inr ⟨f, hf, q, hq, rfl⟩)⟩
  · rintro (h | ⟨s, hs, h | h | ⟨f, hf, q, hq, rfl⟩⟩)
    · exact .inl h
    · exact .inr ⟨s, hs, .inl (.inl h)⟩
    · exact .inr ⟨s, hs, .inl (.inr h)⟩
    · exact .inr ⟨s, hs, .inr ⟨f, hf, q, hq, rfl⟩⟩

theorem mem_finals {f : Nat} (h : f ∈ finals R) : f < R.size ∧ R.isAccepting f = true := by
  simp only [finals, List.mem_filter, List.mem_range] at h
  exact h

theorem mem_starts {q : Nat} (h : q ∈ starts R) : q < R.size ∧ q ∈ R.start := by
  simp only [starts, List.mem_filter, decide_eq_true_eq] at h
  exact ⟨h.2, h.1⟩

/-- A path within a copy is a run of `R`. -/
theorem copy_run {off : Nat} :
    ∀ {u w v}, Path (copyT R off) u w v → ∀ {p}, u = off + p → p < R.size →
      ∃ q, v = off + q ∧ q < R.size ∧ R.Run p w q
  | _, _, _, .nil _, p, rfl, hp => ⟨p, rfl, hp, .nil p⟩
  | _, _, _, .cons ht hw, p, hu, hp => by
    obtain ⟨p', q, hu', rfl, _, hq, hmem⟩ := mem_copyT.mp ht
    have : p' = p := by omega
    subst this
    obtain ⟨r, rfl, hr, hrun⟩ := copy_run hw rfl hq
    exact ⟨r, rfl, hr, .cons hmem hrun⟩

/-- The copy of `R` itself is closed: a path from it is a run of `R`. -/
theorem path_copy0 : ∀ {u w v}, Path (steps R) u w v → u < R.size → R.Run u w v ∧ v < R.size
  | _, _, _, .nil _, hu => ⟨.nil _, hu⟩
  | u, _, _, .cons ht hw, hu => by
    rcases mem_steps.mp ht with h | ⟨s, hs, h | h | ⟨f, hf, q, hq, he⟩⟩
    · obtain ⟨p, q, hp, rfl, _, hq, hmem⟩ := mem_copyT.mp h
      simp only [Nat.zero_add] at hp
      subst hp
      obtain ⟨hrun, hv⟩ := path_copy0 hw (by omega)
      exact ⟨.cons (by simpa using hmem) hrun, hv⟩
    · obtain ⟨p, q, hp, -, -, -, -⟩ := mem_copyT.mp h
      have := le_base (R := R) s; omega
    · obtain ⟨p, q, hp, -, -, -, -⟩ := mem_copyT.mp h
      have := le_base (R := R) s; omega
    · simp only [Prod.mk.injEq] at he
      have := le_base (R := R) s; omega

/-- The second copy of `s`, which accepts at `s`, is closed. -/
theorem path_second {s : Nat} : ∀ {u w v}, Path (steps R) u w v → ∀ {p}, p < R.size →
    u = base R s + R.size + p → ∃ q, v = base R s + R.size + q ∧ q < R.size ∧ R.Run p w q
  | _, _, _, .nil _, p, hp, rfl => ⟨p, rfl, hp, .nil p⟩
  | u, _, _, .cons ht hw, p, hp, hu => by
    rcases mem_steps.mp ht with h | ⟨s', hs', h | h | ⟨f, hf, q, hq, he⟩⟩
    · obtain ⟨p', q, hp', -, hp'n, -, -⟩ := mem_copyT.mp h
      have := le_base (R := R) s; omega
    · obtain ⟨p', q, hp', -, hp'n, -, -⟩ := mem_copyT.mp h
      have := base_inj (R := R) (s := s) (s' := s') (i := R.size + p) (j := p') (by omega) (by omega)
        (by omega)
      omega
    · obtain ⟨p', q, hp', rfl, hp'n, hq, hmem⟩ := mem_copyT.mp h
      obtain ⟨rfl, hpp⟩ := base_inj (R := R) (s := s) (s' := s') (i := R.size + p)
        (j := R.size + p') (by omega) (by omega) (by omega)
      have : p' = p := by omega
      subst this
      obtain ⟨r, rfl, hr, hrun⟩ := path_second hw hq rfl
      exact ⟨r, rfl, hr, .cons hmem hrun⟩
    · simp only [Prod.mk.injEq] at he
      have hf' := (mem_finals hf).1
      have := base_inj (R := R) (s := s) (s' := s') (i := R.size + p) (j := f) (by omega)
        (by omega) (by omega)
      omega

/-- A path from the first copy of `s`, which starts at `s`: it stays in the
copy, or leaves it from an accepting state into the second copy. -/
theorem path_first {s p : Nat} (hp : p < R.size) {w : List Label} {v : Nat}
    (h : Path (steps R) (base R s + p) w v) :
    (∃ q, v = base R s + q ∧ q < R.size ∧ R.Run p w q) ∨
      ∃ u f q₀ w' q, w = u ++ Label.eps :: w' ∧ R.Run p u f ∧ f ∈ finals R ∧ q₀ ∈ starts R ∧
        v = base R s + R.size + q ∧ q < R.size ∧ R.Run q₀ w' q := by
  rcases Path.exitAny (Tin := copyT R (base R s))
      (R := fun u => base R s ≤ u ∧ u < base R s + R.size)
      (Exit := fun e => ∃ f ∈ finals R, e = base R s + f)
      (fun t ht => by
        obtain ⟨_, _, -, hv, -, hq, -⟩ := mem_copyT.mp (show (t.1, t.2.1, t.2.2) ∈ _ from ht)
        omega)
      (fun t ht hR => by
        rcases mem_steps.mp ht with h | ⟨s', hs', h | h | ⟨f, hf, q, hq, he⟩⟩
        · obtain ⟨_, _, hu, -, hp0, -, -⟩ := mem_copyT.mp (show (t.1, t.2.1, t.2.2) ∈ _ from h)
          have := le_base (R := R) s; omega
        · obtain ⟨p', _, hu, -, hp'n, -, -⟩ := mem_copyT.mp (show (t.1, t.2.1, t.2.2) ∈ _ from h)
          obtain ⟨rfl, -⟩ := base_inj (R := R) (s := s) (s' := s') (i := t.1 - base R s) (j := p')
            (by omega) (by omega) (by omega)
          exact .inl h
        · obtain ⟨p', _, hu, -, hp'n, -, -⟩ := mem_copyT.mp (show (t.1, t.2.1, t.2.2) ∈ _ from h)
          have := base_inj (R := R) (s := s) (s' := s') (i := t.1 - base R s) (j := R.size + p')
            (by omega) (by omega) (by omega)
          omega
        · subst he
          have hf' := (mem_finals hf).1
          obtain ⟨rfl, -⟩ := base_inj (R := R) (s := s) (s' := s') (i := base R s' + f - base R s)
            (j := f) (by simp at hR; omega) (by omega) (by simp at hR; omega)
          exact .inr ⟨f, hf, rfl⟩)
      h ⟨by omega, by omega⟩ with hin | ⟨u, e, a, q', w', rfl, hu, ⟨f, hf, rfl⟩, ha, hna, hw'⟩
  · obtain ⟨q, rfl, hq, hrun⟩ := copy_run hin rfl hp
    exact .inl ⟨q, rfl, hq, hrun⟩
  · obtain ⟨f', rfl', hf'n, hrun⟩ := copy_run hu rfl hp
    have hfeq : f' = f := by omega
    subst hfeq
    rcases mem_steps.mp ha with h | ⟨s', hs', h | h | ⟨g, hg, q₀, hq₀, he⟩⟩
    · obtain ⟨_, _, hu', -, hp0, -, -⟩ := mem_copyT.mp h
      have := le_base (R := R) s; omega
    · obtain ⟨p', _, hu', -, hp'n, -, -⟩ := mem_copyT.mp h
      obtain ⟨rfl, -⟩ := base_inj (R := R) (s := s) (s' := s') (i := f') (j := p')
        (by omega) (by omega) (by omega)
      exact absurd h hna
    · obtain ⟨p', _, hu', -, hp'n, -, -⟩ := mem_copyT.mp h
      have := base_inj (R := R) (s := s) (s' := s') (i := f') (j := R.size + p') (by omega)
        (by omega) (by omega)
      omega
    · simp only [Prod.mk.injEq] at he
      obtain ⟨he₁, rfl, rfl⟩ := he
      have hg' := (mem_finals hg).1
      obtain ⟨rfl, -⟩ := base_inj (R := R) (s := s) (s' := s') (i := f') (j := g) (by omega)
        (by omega) he₁
      have hq₀' := (mem_starts hq₀).1
      obtain ⟨q, rfl, hq, hrun'⟩ := path_second (s := s) hw' hq₀' rfl
      exact .inr ⟨u, f', q₀, w', q, rfl, hrun, hf, hq₀, rfl, hq, hrun'⟩

theorem run_accepts {p q : Nat} {w : List Label} (h : R.Run p w q) (hq : R.isAccepting q = true) :
    R.Accepts p w := by
  induction h with
  | nil => exact .nil hq
  | cons ht _ ih => exact .cons ht (ih hq)

theorem run_append {p q r : Nat} {u v : List Label} (h₁ : R.Run p u q) (h₂ : R.Run q v r) :
    R.Run p (u ++ v) r := by
  induction h₁ with
  | nil => exact h₂
  | cons ht _ ih => exact .cons ht (ih h₂)

theorem size_rotations : (rotations R).size = R.size + 2 * R.size * R.size := by
  simp [rotations, NFA.ofList, NFA.size]

/-- **Rotating adds no cycle**: each cycle of `rotations R` is one of `R`. -/
theorem rotations_cycle {E : Type u} (M : Interp E) {x : E}
    (h : (rotations R).denote (Label.denote M) x x) : ∃ y, R.denote (Label.denote M) y y := by
  obtain ⟨q, hq, w, hw, hr⟩ := h
  let N := R.size + 2 * R.size * R.size
  have hlast : ∀ s < R.size, base R s + 2 * R.size ≤ N := by
    intro s hs
    have := base_mono (R := R) hs
    simp only [base] at this ⊢
    omega
  have hT : ∀ t ∈ steps R, t.1 < N := by
    intro t ht
    rcases mem_steps.mp ht with h | ⟨s, hs, h | h | ⟨f, hf, q, hq, rfl⟩⟩
    · obtain ⟨_, _, hu, -, hp, -, -⟩ := mem_copyT.mp (show (t.1, t.2.1, t.2.2) ∈ _ from h)
      simp only [N]; omega
    · obtain ⟨_, _, hu, -, hp, -, -⟩ := mem_copyT.mp (show (t.1, t.2.1, t.2.2) ∈ _ from h)
      have := hlast s hs; omega
    · obtain ⟨_, _, hu, -, hp, -, -⟩ := mem_copyT.mp (show (t.1, t.2.1, t.2.2) ∈ _ from h)
      have := hlast s hs; omega
    · have := hlast s hs
      have := (mem_finals hf).1
      dsimp only; omega
  have hacc : ∀ q ∈ finals R ++ (List.range R.size).map (fun s => base R s + R.size + s), q < N := by
    intro q hq
    simp only [List.mem_append, List.mem_map, List.mem_range] at hq
    rcases hq with hq | ⟨s, hs, rfl⟩
    · have := (mem_finals hq).1; simp only [N]; omega
    · have := hlast s hs; omega
  obtain ⟨e, hpath, he⟩ := (NFA.accepts_ofList hT hacc).mp hw
  simp only [rotations, NFA.ofList, List.mem_append, List.mem_map, List.mem_range] at hq
  simp only [List.mem_append, List.mem_map, List.mem_range] at he
  rcases hq with hq | ⟨s, hs, rfl⟩
  · -- from the copy of R itself: a word of R
    have hq' := mem_starts hq
    obtain ⟨hrun, hen⟩ := path_copy0 hpath hq'.1
    rcases he with he | ⟨s, hs, rfl⟩
    · exact ⟨x, q, hq'.2, w, run_accepts hrun (mem_finals he).2, hr⟩
    · have := le_base (R := R) s; omega
  · -- from the first copy of s: a rotation
    rcases path_first (s := s) hs hpath with ⟨f, rfl, hf, -⟩ | ⟨u, f, q₀, w', e', rfl, hu, hf, hq₀, rfl, he', hw'⟩
    · rcases he with he | ⟨s', hs', he⟩
      · have := (mem_finals he).1; have := le_base (R := R) s; omega
      · have := base_inj (R := R) (s := s) (s' := s') (i := f) (j := R.size + s') (by omega)
          (by omega) (by omega)
        omega
    · rcases he with he | ⟨s', hs', he⟩
      · have := (mem_finals he).1; have := le_base (R := R) s; omega
      · obtain ⟨rfl, hse⟩ := base_inj (R := R) (s := s) (s' := s') (i := R.size + e')
          (j := R.size + s') (by omega) (by omega) (by omega)
        have : e' = s := by omega
        subst this
        rw [wordRel_append] at hr
        obtain ⟨z, hu', hz⟩ := hr
        obtain ⟨z', hz', hw''⟩ := hz
        rw [Label.denote_eps] at hz'
        subst hz'
        refine ⟨z, q₀, (mem_starts hq₀).2, w' ++ u,
          run_accepts (run_append hw' hu) (mem_finals hf).2, ?_⟩
        rw [wordRel_append]
        exact ⟨x, hw'', hu'⟩

end Rotate

end KaterCert
