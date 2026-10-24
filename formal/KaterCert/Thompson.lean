import KaterCert.Exp
import KaterCert.NFA
import KaterCert.Rec

/-!
# The automaton of an expression

Lean's own automaton of an expression, Thompson's construction, and the proof
that it denotes what the expression does. Kater's automata are compared with
these (`Guarded`), so that what Kater's `RegExp::toNFA`, `normalize` and
`to_DFA` do need not be trusted.

The construction numbers states from `n`: an expression's automaton starts
at `n`, accepts at `n + 1`, and takes the states after them that its parts
need. Nothing enters its start and nothing leaves its final state, so the
automaton of a part, inside the automaton of the whole, is left only through
its final state. Steps between the parts read the identity, `Label.eps`.

The automaton of a `fix` (`let rec`) whose definitions are left-linear has a
hub for each relation it defines, and between the hubs the automata of the
parts of the definitions' normal forms (`Exp.nf`): from its start to the
hub of `xᵢ` it reads what `xᵢ` relates (`Reach`). The parts are not
subexpressions, so the construction recurses on a bound of its depth, which
`Exp.size` meets.
-/

namespace KaterCert

universe u

/-- `Path T p w q`: the transitions `T`, as (source, letter, destination),
read `w` from `p` to `q`. -/
inductive Path {L : Type} (T : List (Nat × L × Nat)) : Nat → List L → Nat → Prop
  | nil (p : Nat) : Path T p [] p
  | cons {p : Nat} {a : L} {q : Nat} {w : List L} {r : Nat} :
      (p, a, q) ∈ T → Path T q w r → Path T p (a :: w) r

namespace Path

variable {L : Type} {T T' : List (Nat × L × Nat)}

theorem mono (h : ∀ t ∈ T, t ∈ T') : ∀ {p w q}, Path T p w q → Path T' p w q
  | _, _, _, .nil p => .nil p
  | _, _, _, .cons ht hw => .cons (h _ ht) (mono h hw)

theorem append : ∀ {p u q v r}, Path T p u q → Path T q v r → Path T p (u ++ v) r
  | _, _, _, _, _, .nil _, h => h
  | _, _, _, _, _, .cons ht hw, h => .cons ht (append hw h)

theorem single {p a q} (h : (p, a, q) ∈ T) : Path T p [a] q := .cons h (.nil q)

/-- A path between two states takes a first step. -/
theorem first {p w q} (h : Path T p w q) (hpq : p ≠ q) :
    ∃ a q' w', w = a :: w' ∧ (p, a, q') ∈ T ∧ Path T q' w' q := by
  cases h with
  | nil => exact absurd rfl hpq
  | cons ht hw => exact ⟨_, _, _, rfl, ht, hw⟩

/-- A path out of a state that no transition leaves is empty. -/
theorem of_no_out {p w q} (hout : ∀ t ∈ T, t.1 ≠ p) (h : Path T p w q) : w = [] ∧ q = p := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩
  | cons ht _ => exact absurd rfl (hout _ ht)

/-- A path within transitions that stay in a set of states stays in it. -/
theorem stays {R : Nat → Prop} (hin : ∀ t ∈ T, R t.1 → R t.2.2) :
    ∀ {p w q}, Path T p w q → R p → R q
  | _, _, _, .nil _, h => h
  | _, _, _, .cons ht hw, h => stays hin hw (hin _ ht h)

/-- A path out of a part `Tin` of `T`, from a state of the part's states `R`:
either it stays in the part, or it leaves through `f`, the one state of `R`
that steps of `T` outside the part leave, and that no step of the part
leaves. -/
theorem exit {Tin : List (Nat × L × Nat)} {R : Nat → Prop} {f : Nat}
    (hin : ∀ t ∈ Tin, R t.2.2)
    (hT : ∀ t ∈ T, R t.1 → t ∈ Tin ∨ t.1 = f) :
    ∀ {p w q}, Path T p w q → R p →
      Path Tin p w q ∨ ∃ u a q' v, w = u ++ a :: v ∧ Path Tin p u f ∧ (f, a, q') ∈ T ∧
        Path T q' v q
  | _, _, _, .nil p, _ => .inl (.nil p)
  | p, _, _, .cons (a := a) (q := q₁) (w := w) ht hw, hp => by
    rcases hT _ ht hp with hin' | hf
    · rcases exit hin hT hw (hin _ hin') with h | ⟨u, b, q', v, rfl, hu, hb, hv⟩
      · exact .inl (.cons hin' h)
      · exact .inr ⟨a :: u, b, q', v, rfl, .cons hin' hu, hb, hv⟩
    · simp only at hf
      subst hf
      exact .inr ⟨[], a, q₁, w, rfl, .nil _, ht, hw⟩

/-- The same, for a part left through any of several states: either the path
stays in the part, or it leaves it, by a step not of the part, from one of
the states `Exit` names. -/
theorem exitAny {Tin : List (Nat × L × Nat)} {R Exit : Nat → Prop}
    (hin : ∀ t ∈ Tin, R t.2.2)
    (hT : ∀ t ∈ T, R t.1 → t ∈ Tin ∨ Exit t.1) :
    ∀ {p w q}, Path T p w q → R p →
      Path Tin p w q ∨ ∃ u e a q' v, w = u ++ a :: v ∧ Path Tin p u e ∧ Exit e ∧
        (e, a, q') ∈ T ∧ (e, a, q') ∉ Tin ∧ Path T q' v q
  | _, _, _, .nil p, _ => .inl (.nil p)
  | p, _, _, .cons (a := a) (q := q₁) (w := w) ht hw, hp => by
    by_cases hin' : (p, a, q₁) ∈ Tin
    · rcases exitAny hin hT hw (hin _ hin') with h | ⟨u, e, b, q', v, rfl, hu, he, hb, hnb, hv⟩
      · exact .inl (.cons hin' h)
      · exact .inr ⟨a :: u, e, b, q', v, rfl, .cons hin' hu, he, hb, hnb, hv⟩
    · rcases hT _ ht hp with h | hf
      · exact absurd h hin'
      · exact .inr ⟨[], p, a, q₁, w, rfl, .nil _, hf, ht, hin', hw⟩

end Path

variable {L : Type} {E : Type u}

namespace Thompson

/-- Pieces `(s, e, d)` laid out from `m`: the automaton `b e` of each,
entered from `s` and left to `d` by steps of the identity. -/
def lay (b : Exp → Nat → List (Nat × Label × Nat) × Nat) :
    List (Nat × Exp × Nat) → Nat → List (Nat × Label × Nat) × Nat
  | [], m => ([], m)
  | (s, e, d) :: ps, m =>
    ([(s, .eps, m), (m + 1, .eps, d)] ++ ((b e m).1 ++ (lay b ps (b e m).2).1),
      (lay b ps (b e m).2).2)

/-- The pieces of the automaton of a `fix` whose definitions have the normal
forms `N` (`Defs.nfs`), the hub of its `i`-th relation `xᵢ` at `n + 2 + i`:
each `cᵢ` from the start to the hub of `xᵢ`, and each `x_j ; a` of the
`i`-th definition from the hub of `x_j` to that of `xᵢ`. -/
def pieces (N : List (Exp × List (Nat × Exp))) (n : Nat) : List (Nat × Exp × Nat) :=
  go N 0
where
  /-- The pieces of the definitions `R`, the first of them the `i`-th. -/
  go : List (Exp × List (Nat × Exp)) → Nat → List (Nat × Exp × Nat)
    | [], _ => []
    | (c, L) :: R, i =>
      (n, c, n + 2 + i) ::
        ((L.filter (·.1 < N.length)).map fun p => (n + 2 + p.1, p.2, n + 2 + i)) ++ go R (i + 1)

/-- The automaton of `fix main defs` from `n`, `b` giving those of the
pieces: the pieces between the hubs, and a step from the hub of the main
relation to the final state. A `fix` whose definitions are not left-linear
gets no transitions. -/
def buildFix (b : Exp → Nat → List (Nat × Label × Nat) × Nat) (main : Nat) (defs : Defs)
    (n : Nat) : List (Nat × Label × Nat) × Nat :=
  match defs.nfs with
  | some N =>
    if main < N.length then
      ((n + 2 + main, .eps, n + 1) :: (lay b (pieces N n) (n + 2 + N.length)).1,
        (lay b (pieces N n) (n + 2 + N.length)).2)
    else ([], n + 2)
  | none => ([], n + 2)

/-- `build k e n`: the transitions of `e`'s automaton, which starts at `n`,
accepts at `n + 1`, and has its other states from `n + 2` up to the bound
it returns. `k` bounds the depth of the construction: what is deeper gets
no transitions, and `e.size` is deep enough (`complete`). -/
def build : Nat → Exp → Nat → List (Nat × Label × Nat) × Nat
  | 0, _, n => ([], n + 2)
  | _ + 1, .label l, n => ([(n, l, n + 1)], n + 2)
  | _ + 1, .zero, n => ([], n + 2)
  | k + 1, .alt a b, n =>
    let ra := build k a (n + 2)
    let rb := build k b ra.2
    ([(n, .eps, n + 2), (n + 3, .eps, n + 1), (n, .eps, ra.2), (ra.2 + 1, .eps, n + 1)] ++
      (ra.1 ++ rb.1), rb.2)
  | k + 1, .seq a b, n =>
    let ra := build k a (n + 2)
    let rb := build k b ra.2
    ([(n, .eps, n + 2), (n + 3, .eps, ra.2), (ra.2 + 1, .eps, n + 1)] ++ (ra.1 ++ rb.1), rb.2)
  | k + 1, .star a, n =>
    let ra := build k a (n + 2)
    ([(n, .eps, n + 1), (n, .eps, n + 2), (n + 3, .eps, n + 2), (n + 3, .eps, n + 1)] ++ ra.1,
      ra.2)
  | k + 1, .plus a, n =>
    let ra := build k a (n + 2)
    ([(n, .eps, n + 2), (n + 3, .eps, n + 2), (n + 3, .eps, n + 1)] ++ ra.1, ra.2)
  | k + 1, .opt a, n =>
    let ra := build k a (n + 2)
    ([(n, .eps, n + 1), (n, .eps, n + 2), (n + 3, .eps, n + 1)] ++ ra.1, ra.2)
  | _ + 1, .ref _, n => ([], n + 2)
  | k + 1, .fix main defs, n => buildFix (build k) main defs n

/-- What the construction keeps: its states are between `n` and the bound,
nothing enters its start, and nothing leaves its final state. -/
structure WF (T : List (Nat × Label × Nat)) (n m : Nat) : Prop where
  bound : n + 2 ≤ m
  src : ∀ t ∈ T, n ≤ t.1 ∧ t.1 < m
  dst : ∀ t ∈ T, n ≤ t.2.2 ∧ t.2.2 < m
  no_in : ∀ t ∈ T, t.2.2 ≠ n
  no_out : ∀ t ∈ T, t.1 ≠ n + 1

theorem WF.empty (n : Nat) : WF [] n (n + 2) :=
  ⟨by omega, by simp, by simp, by simp, by simp⟩

section Lay

variable {b : Exp → Nat → List (Nat × Label × Nat) × Nat}

theorem lay_bound (hb : ∀ e m, WF (b e m).1 m (b e m).2) :
    ∀ (ps : List (Nat × Exp × Nat)) (m : Nat), m ≤ (lay b ps m).2
  | [], m => Nat.le_refl m
  | (_, e, _) :: ps, m => by
    have := (hb e m).bound
    have := lay_bound hb ps (b e m).2
    simp only [lay]
    omega

/-- A transition of laid out pieces leaves a state of theirs, or a state a
piece is entered from. -/
theorem lay_src (hb : ∀ e m, WF (b e m).1 m (b e m).2) :
    ∀ (ps : List (Nat × Exp × Nat)) (m : Nat), ∀ t ∈ (lay b ps m).1,
      (m ≤ t.1 ∧ t.1 < (lay b ps m).2) ∨ ∃ p ∈ ps, t.1 = p.1
  | [], _, t, ht => by simp [lay] at ht
  | (s, e, d) :: ps, m, t, ht => by
    have hbm := hb e m
    have := hbm.bound
    have := lay_bound hb ps (b e m).2
    simp only [lay] at ht ⊢
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at ht
    rcases ht with rfl | rfl | ht | ht
    · exact .inr ⟨(s, e, d), by simp, rfl⟩
    · exact .inl (by dsimp only; omega)
    · have := hbm.src t ht
      exact .inl (by omega)
    · rcases lay_src hb ps (b e m).2 t ht with h | ⟨p, hp, h⟩
      · exact .inl (by omega)
      · exact .inr ⟨p, by simp [hp], h⟩

/-- A transition of laid out pieces enters a state of theirs, or a state a
piece leads to. -/
theorem lay_dst (hb : ∀ e m, WF (b e m).1 m (b e m).2) :
    ∀ (ps : List (Nat × Exp × Nat)) (m : Nat), ∀ t ∈ (lay b ps m).1,
      (m ≤ t.2.2 ∧ t.2.2 < (lay b ps m).2) ∨ ∃ p ∈ ps, t.2.2 = p.2.2
  | [], _, t, ht => by simp [lay] at ht
  | (s, e, d) :: ps, m, t, ht => by
    have hbm := hb e m
    have := hbm.bound
    have := lay_bound hb ps (b e m).2
    simp only [lay] at ht ⊢
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at ht
    rcases ht with rfl | rfl | ht | ht
    · exact .inl (by dsimp only; omega)
    · exact .inr ⟨(s, e, d), by simp, rfl⟩
    · have := hbm.dst t ht
      exact .inl (by omega)
    · rcases lay_dst hb ps (b e m).2 t ht with h | ⟨p, hp, h⟩
      · exact .inl (by omega)
      · exact .inr ⟨p, by simp [hp], h⟩

end Lay

section Pieces

variable {N : List (Exp × List (Nat × Exp))} {n : Nat}

theorem mem_go : ∀ {R : List (Exp × List (Nat × Exp))} {i : Nat} {p : Nat × Exp × Nat},
    p ∈ pieces.go N n R i → ∃ k c L, R[k]? = some (c, L) ∧ (p = (n, c, n + 2 + (i + k)) ∨
      ∃ j a, (j, a) ∈ L ∧ j < N.length ∧ p = (n + 2 + j, a, n + 2 + (i + k)))
  | [], _, _, h => by simp [pieces.go] at h
  | (c, L) :: R, i, p, h => by
    simp only [pieces.go, List.mem_cons, List.mem_append, List.mem_map, List.mem_filter,
      decide_eq_true_eq, or_assoc] at h
    rcases h with rfl | ⟨⟨j, a⟩, ⟨hja, hj⟩, rfl⟩ | h
    · exact ⟨0, c, L, rfl, .inl (by simp)⟩
    · exact ⟨0, c, L, rfl, .inr ⟨j, a, hja, hj, by simp⟩⟩
    · obtain ⟨k, c', L', hk, hp⟩ := mem_go h
      refine ⟨k + 1, c', L', by simpa using hk, ?_⟩
      rw [show i + (k + 1) = i + 1 + k by omega]
      exact hp

/-- A piece is a part `cᵢ`, from the start to the hub of `xᵢ`, or a part
`x_j ; a` of the `i`-th definition, from the hub of `x_j` to that of
`xᵢ`. -/
theorem mem_pieces {p : Nat × Exp × Nat} (h : p ∈ pieces N n) : ∃ i c L, N[i]? = some (c, L) ∧
    (p = (n, c, n + 2 + i) ∨ ∃ j a, (j, a) ∈ L ∧ j < N.length ∧ p = (n + 2 + j, a, n + 2 + i)) := by
  unfold pieces at h
  obtain ⟨k, c, L, hk, hp⟩ := mem_go h
  simp only [Nat.zero_add] at hp
  exact ⟨k, c, L, hk, hp⟩

theorem go_base : ∀ {R : List (Exp × List (Nat × Exp))} {i k : Nat} {c : Exp}
    {L : List (Nat × Exp)}, R[k]? = some (c, L) → (n, c, n + 2 + (i + k)) ∈ pieces.go N n R i
  | [], _, _, _, _, h => by simp at h
  | (_, _) :: _, _, 0, _, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [pieces.go]
  | (_, _) :: _, i, k + 1, _, _, h => by
    simp only [List.getElem?_cons_succ] at h
    have := go_base (i := i + 1) h
    rw [show i + (k + 1) = i + 1 + k by omega]
    simp only [pieces.go, List.mem_cons, List.mem_append, or_assoc]
    exact .inr (.inr this)

theorem go_step : ∀ {R : List (Exp × List (Nat × Exp))} {i k : Nat} {c : Exp}
    {L : List (Nat × Exp)} {j : Nat} {a : Exp}, R[k]? = some (c, L) → (j, a) ∈ L →
    j < N.length → (n + 2 + j, a, n + 2 + (i + k)) ∈ pieces.go N n R i
  | [], _, _, _, _, _, _, h, _, _ => by simp at h
  | (_, _) :: _, _, 0, _, _, j, a, h, hja, hj => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [pieces.go, List.mem_cons, List.mem_append, List.mem_map, List.mem_filter,
      decide_eq_true_eq, or_assoc]
    exact .inr (.inl ⟨(j, a), ⟨hja, hj⟩, by simp⟩)
  | (_, _) :: _, i, k + 1, _, _, _, _, h, hja, hj => by
    simp only [List.getElem?_cons_succ] at h
    have := go_step (i := i + 1) h hja hj
    rw [show i + (k + 1) = i + 1 + k by omega]
    simp only [pieces.go, List.mem_cons, List.mem_append, or_assoc]
    exact .inr (.inr this)

theorem pieces_base {i : Nat} {c : Exp} {L : List (Nat × Exp)} (h : N[i]? = some (c, L)) :
    (n, c, n + 2 + i) ∈ pieces N n := by
  have := go_base (N := N) (n := n) (i := 0) h
  simpa [pieces] using this

theorem pieces_step {i : Nat} {c : Exp} {L : List (Nat × Exp)} {j : Nat} {a : Exp}
    (h : N[i]? = some (c, L)) (hja : (j, a) ∈ L) (hj : j < N.length) :
    (n + 2 + j, a, n + 2 + i) ∈ pieces N n := by
  have := go_step (N := N) (n := n) (i := 0) h hja hj
  simpa [pieces] using this

/-- Pieces lead from the start or a hub to a hub. -/
theorem pieces_bounds {p : Nat × Exp × Nat} (h : p ∈ pieces N n) :
    (p.1 = n ∨ (n + 2 ≤ p.1 ∧ p.1 < n + 2 + N.length)) ∧ n + 2 ≤ p.2.2 ∧
      p.2.2 < n + 2 + N.length := by
  obtain ⟨i, c, L, hi, hp⟩ := mem_pieces h
  have := lt_of_getElem? hi
  rcases hp with rfl | ⟨j, a, -, hj, rfl⟩
  · exact ⟨.inl rfl, by dsimp only; omega, by dsimp only; omega⟩
  · exact ⟨.inr (by dsimp only; omega), by dsimp only; omega, by dsimp only; omega⟩

end Pieces

theorem buildFix_wf {b : Exp → Nat → List (Nat × Label × Nat) × Nat}
    (hb : ∀ e m, WF (b e m).1 m (b e m).2) (main : Nat) (defs : Defs) (n : Nat) :
    WF (buildFix b main defs n).1 n (buildFix b main defs n).2 := by
  unfold buildFix
  split
  · rename_i N _
    split
    · rename_i hmain
      have hl := lay_bound hb (pieces N n) (n + 2 + N.length)
      have hsrc := lay_src hb (pieces N n) (n + 2 + N.length)
      have hdst := lay_dst hb (pieces N n) (n + 2 + N.length)
      dsimp only
      refine ⟨by omega, ?_, ?_, ?_, ?_⟩ <;> intro t ht <;>
        simp only [List.mem_cons] at ht <;> rcases ht with rfl | ht
      all_goals first
        | (dsimp only; omega)
        | (rcases hsrc t ht with h | ⟨p, hp, h⟩ <;>
            first | omega | (have := pieces_bounds hp; omega))
        | (rcases hdst t ht with h | ⟨p, hp, h⟩ <;>
            first | omega | (have := pieces_bounds hp; omega))
    · exact WF.empty n
  · exact WF.empty n

theorem build_wf : ∀ (k : Nat) (e : Exp) (n : Nat), WF (build k e n).1 n (build k e n).2
  | 0, _, n => by simp only [build]; exact WF.empty n
  | _ + 1, .label l, n => by
    simp only [build]
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩ <;> intro t ht <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht <;> subst ht <;>
      (dsimp only; omega)
  | _ + 1, .zero, n => by simp only [build]; exact WF.empty n
  | k + 1, .alt a b, n => by
    obtain ⟨ha0, has, had, hai, hao⟩ := build_wf k a (n + 2)
    obtain ⟨hb0, hbs, hbd, hbi, hbo⟩ := build_wf k b (build k a (n + 2)).2
    simp only [build]
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩ <;> intro t ht <;>
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at ht <;>
      rcases ht with rfl | rfl | rfl | rfl | ht | ht
    all_goals first
      | (dsimp only; omega)
      | (have := has t ht; have := had t ht; have := hai t ht; have := hao t ht; omega)
      | (have := hbs t ht; have := hbd t ht; omega)
  | k + 1, .seq a b, n => by
    obtain ⟨ha0, has, had, hai, hao⟩ := build_wf k a (n + 2)
    obtain ⟨hb0, hbs, hbd, hbi, hbo⟩ := build_wf k b (build k a (n + 2)).2
    simp only [build]
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩ <;> intro t ht <;>
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at ht <;>
      rcases ht with rfl | rfl | rfl | ht | ht
    all_goals first
      | (dsimp only; omega)
      | (have := has t ht; have := had t ht; have := hai t ht; have := hao t ht; omega)
      | (have := hbs t ht; have := hbd t ht; omega)
  | k + 1, .star a, n => by
    obtain ⟨ha0, has, had, hai, hao⟩ := build_wf k a (n + 2)
    simp only [build]
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩ <;> intro t ht <;>
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at ht <;>
      rcases ht with rfl | rfl | rfl | rfl | ht
    all_goals first
      | (dsimp only; omega)
      | (have := has t ht; have := had t ht; omega)
  | k + 1, .plus a, n => by
    obtain ⟨ha0, has, had, hai, hao⟩ := build_wf k a (n + 2)
    simp only [build]
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩ <;> intro t ht <;>
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at ht <;>
      rcases ht with rfl | rfl | rfl | ht
    all_goals first
      | (dsimp only; omega)
      | (have := has t ht; have := had t ht; omega)
  | k + 1, .opt a, n => by
    obtain ⟨ha0, has, had, hai, hao⟩ := build_wf k a (n + 2)
    simp only [build]
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩ <;> intro t ht <;>
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at ht <;>
      rcases ht with rfl | rfl | rfl | ht
    all_goals first
      | (dsimp only; omega)
      | (have := has t ht; have := had t ht; omega)
  | _ + 1, .ref _, n => by simp only [build]; exact WF.empty n
  | k + 1, .fix main defs, n => by
    simp only [build]
    exact buildFix_wf (fun e m => build_wf k e m) main defs n

variable {E : Type u} (M : Interp E)

/-- The relation of a word, letters meaning what they mean in Kater. -/
abbrev rel (w : List Label) : Rel E := wordRel (Label.denote M) w

theorem rel_eps {w : List Label} {x y : E} : rel M (.eps :: w) x y ↔ rel M w x y := by
  simp only [rel, wordRel]
  constructor
  · rintro ⟨z, hz, hw⟩
    rw [Label.denote_eps] at hz
    exact hz ▸ hw
  · intro h
    exact ⟨x, (Label.denote_eps M).mpr rfl, h⟩

theorem rel_append {u v : List Label} {x y : E} :
    rel M (u ++ v) x y ↔ Rel.comp (rel M u) (rel M v) x y :=
  wordRel_append _ u v

theorem rel_nil {x y : E} : rel M [] x y ↔ x = y := Iff.rfl

/-- `ε u ε` reads what `u` does. -/
theorem rel_wrap {u : List Label} {x y : E} :
    rel M (.eps :: (u ++ [.eps])) x y ↔ rel M u x y := by
  rw [rel_eps, rel_append]
  constructor
  · rintro ⟨z, hu, hz⟩
    have := (rel_eps M).mp hz
    rw [rel_nil] at this
    exact this ▸ hu
  · intro h
    exact ⟨y, h, (rel_eps M).mpr ((rel_nil M).mpr rfl)⟩

section Parts

variable {T ta : List (Nat × Label × Nat)} {n m : Nat}

/-- A path in `T` from a part's start to the whole's final state: it reads
the part to the part's final state, and steps on. -/
theorem through {f : Nat} {R : Nat → Prop} {p q : Nat} {w : List Label}
    (hin : ∀ t ∈ ta, R t.2.2) (hT : ∀ t ∈ T, R t.1 → t ∈ ta ∨ t.1 = f) (hq : ¬ R q)
    (h : Path T p w q) (hp : R p) :
    ∃ u a q' v, w = u ++ a :: v ∧ Path ta p u f ∧ (f, a, q') ∈ T ∧ Path T q' v q := by
  rcases Path.exit hin hT h hp with h' | h'
  · exact absurd (Path.stays (fun t ht _ => hin t ht) h' hp) hq
  · exact h'

end Parts

/-- A transition from a state that neither part leaves is a connecting one. -/
theorem mem_conn {C ta tb : List (Nat × Label × Nat)} {s : Nat} {c : Label} {q : Nat}
    (hta : ∀ t ∈ ta, t.1 ≠ s) (htb : ∀ t ∈ tb, t.1 ≠ s)
    (h : (s, c, q) ∈ C ++ (ta ++ tb)) : (s, c, q) ∈ C := by
  simp only [List.mem_append] at h
  rcases h with h | h | h
  · exact h
  · exact absurd rfl (hta _ h)
  · exact absurd rfl (htb _ h)

theorem mem_conn₁ {C ta : List (Nat × Label × Nat)} {s : Nat} {c : Label} {q : Nat}
    (hta : ∀ t ∈ ta, t.1 ≠ s) (h : (s, c, q) ∈ C ++ ta) : (s, c, q) ∈ C := by
  simp only [List.mem_append] at h
  rcases h with h | h
  · exact h
  · exact absurd rfl (hta _ h)

/-- No transition of a part leaves a state outside its range. -/
theorem out_of_range {T : List (Nat × Label × Nat)} {lo hi s : Nat}
    (hsrc : ∀ t ∈ T, lo ≤ t.1 ∧ t.1 < hi) (hs : s < lo ∨ hi ≤ s) : ∀ t ∈ T, t.1 ≠ s := by
  intro t ht
  have := hsrc t ht
  omega

/-- The loop of `a*` and `a+`: a path from the part's start, through the
part and back to it, to the whole's final state reads `a+`. -/
theorem loop {ta T : List (Nat × Label × Nat)} {n m : Nat} {A : Rel E}
    (wa : WF ta (n + 2) m)
    (hT : ∀ t ∈ T, (n + 2 ≤ t.1 ∧ t.1 < m) → t ∈ ta ∨ t.1 = n + 3)
    (hf : ∀ c q, (n + 3, c, q) ∈ T → c = .eps ∧ (q = n + 2 ∨ q = n + 1))
    (hout : ∀ t ∈ T, t.1 ≠ n + 1)
    (ih : ∀ {u x y}, Path ta (n + 2) u (n + 3) → rel M u x y → A x y) :
    ∀ (k : Nat) {w : List Label} {x y : E}, w.length ≤ k →
      Path T (n + 2) w (n + 1) → rel M w x y → Rel.Plus A x y := by
  have := wa.bound
  intro k
  induction k with
  | zero =>
    intro w x y hk h _
    cases h with
    | cons => simp at hk
  | succ k ihk =>
    intro w x y hk h hw
    obtain ⟨u, c, q', v, rfl, hu, hc, hv⟩ :=
      through (R := fun s => n + 2 ≤ s ∧ s < m) (fun t ht => wa.dst t ht) hT (by omega) h
        (by omega)
    obtain ⟨rfl, hq'⟩ := hf c q' hc
    rw [rel_append] at hw
    obtain ⟨z, hzu, hzv⟩ := hw
    rw [rel_eps] at hzv
    have hza := ih hu hzu
    rcases hq' with rfl | rfl
    · obtain ⟨z', h₁, h₂⟩ := ihk (by simp at hk; omega) hv hzv
      exact ⟨z, hza, .step h₁ h₂⟩
    · obtain ⟨rfl, -⟩ := Path.of_no_out hout hv
      obtain rfl := (rel_nil M).mp hzv
      exact ⟨_, hza, .refl _⟩

theorem sound_alt {ta tb : List (Nat × Label × Nat)} {n m k : Nat} {A B : Rel E}
    (wa : WF ta (n + 2) m) (wb : WF tb m k)
    (iha : ∀ {u x y}, Path ta (n + 2) u (n + 3) → rel M u x y → A x y)
    (ihb : ∀ {u x y}, Path tb m u (m + 1) → rel M u x y → B x y) {w : List Label} {x y : E}
    (h : Path ([(n, .eps, n + 2), (n + 3, .eps, n + 1), (n, .eps, m), (m + 1, .eps, n + 1)] ++
      (ta ++ tb)) n w (n + 1))
    (hw : rel M w x y) : Rel.union A B x y := by
  have := wa.bound
  have := wb.bound
  have hout : ∀ t ∈ [(n, Label.eps, n + 2), (n + 3, Label.eps, n + 1), (n, Label.eps, m),
      (m + 1, Label.eps, n + 1)] ++ (ta ++ tb), t.1 ≠ n + 1 := by
    intro t ht
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at ht
    rcases ht with rfl | rfl | rfl | rfl | ht | ht
    all_goals first
      | (dsimp only; omega)
      | (have := wa.src t ht; omega)
      | (have := wb.src t ht; omega)
  cases h with
  | @cons _ c q w' _ ht hv =>
    have ht := mem_conn (out_of_range wa.src (s := n) (by omega))
      (out_of_range wb.src (s := n) (by omega)) ht
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ht
    rcases ht with ⟨-, rfl, rfl⟩ | ⟨h1, -⟩ | ⟨-, rfl, hq⟩ | ⟨h1, -⟩
    · obtain ⟨u, c', q', v, rfl, hu, hc, hv'⟩ :=
        through (R := fun s => n + 2 ≤ s ∧ s < m) (fun t ht => wa.dst t ht)
          (by
            intro t ht hR
            simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
              or_assoc] at ht
            rcases ht with rfl | rfl | rfl | rfl | ht | ht
            · dsimp at hR; omega
            · exact .inr rfl
            · dsimp at hR; omega
            · dsimp at hR; omega
            · exact .inl ht
            · have := wb.src t ht; omega)
          (by omega) hv (by omega)
      have hc := mem_conn (fun t ht => by have := wa.no_out t ht; omega)
        (out_of_range wb.src (s := n + 3) (by omega)) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hc
      rcases hc with ⟨h1, -⟩ | ⟨-, rfl, rfl⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
      · omega
      · obtain ⟨rfl, -⟩ := Path.of_no_out hout hv'
        exact .inl (iha hu ((rel_wrap M).mp hw))
      · omega
      · omega
    · omega
    · rw [hq] at hv
      obtain ⟨u, c', q', v, rfl, hu, hc, hv'⟩ :=
        through (R := fun s => m ≤ s ∧ s < k) (fun t ht => wb.dst t ht)
          (by
            intro t ht hR
            simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
              or_assoc] at ht
            rcases ht with rfl | rfl | rfl | rfl | ht | ht
            · dsimp at hR; omega
            · dsimp at hR; omega
            · dsimp at hR; omega
            · exact .inr rfl
            · have := wa.src t ht; omega
            · exact .inl ht)
          (by omega) hv (by omega)
      have hc := mem_conn (out_of_range wa.src (s := m + 1) (by omega))
        (fun t ht => by have := wb.no_out t ht; omega) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hc
      rcases hc with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, rfl, rfl⟩
      · omega
      · omega
      · omega
      · obtain ⟨rfl, -⟩ := Path.of_no_out hout hv'
        exact .inr (ihb hu ((rel_wrap M).mp hw))
    · omega

theorem sound_seq {ta tb : List (Nat × Label × Nat)} {n m k : Nat} {A B : Rel E}
    (wa : WF ta (n + 2) m) (wb : WF tb m k)
    (iha : ∀ {u x y}, Path ta (n + 2) u (n + 3) → rel M u x y → A x y)
    (ihb : ∀ {u x y}, Path tb m u (m + 1) → rel M u x y → B x y) {w : List Label} {x y : E}
    (h : Path ([(n, .eps, n + 2), (n + 3, .eps, m), (m + 1, .eps, n + 1)] ++ (ta ++ tb)) n w
      (n + 1))
    (hw : rel M w x y) : Rel.comp A B x y := by
  have := wa.bound
  have := wb.bound
  have hout : ∀ t ∈ [(n, Label.eps, n + 2), (n + 3, Label.eps, m), (m + 1, Label.eps, n + 1)] ++
      (ta ++ tb), t.1 ≠ n + 1 := by
    intro t ht
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at ht
    rcases ht with rfl | rfl | rfl | ht | ht
    all_goals first
      | (dsimp only; omega)
      | (have := wa.src t ht; omega)
      | (have := wb.src t ht; omega)
  cases h with
  | @cons _ c q w' _ ht hv =>
    have ht := mem_conn (out_of_range wa.src (s := n) (by omega))
      (out_of_range wb.src (s := n) (by omega)) ht
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ht
    rcases ht with ⟨-, rfl, rfl⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · obtain ⟨u, c', q', v, rfl, hu, hc, hv'⟩ :=
        through (R := fun s => n + 2 ≤ s ∧ s < m) (fun t ht => wa.dst t ht)
          (by
            intro t ht hR
            simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
              or_assoc] at ht
            rcases ht with rfl | rfl | rfl | ht | ht
            · dsimp at hR; omega
            · exact .inr rfl
            · dsimp at hR; omega
            · exact .inl ht
            · have := wb.src t ht; omega)
          (by omega) hv (by omega)
      have hc := mem_conn (fun t ht => by have := wa.no_out t ht; omega)
        (out_of_range wb.src (s := n + 3) (by omega)) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hc
      rcases hc with ⟨h1, -⟩ | ⟨-, rfl, hq⟩ | ⟨h1, -⟩
      · omega
      · rw [hq] at hv'
        obtain ⟨u', c'', q'', v', rfl, hu', hc', hv''⟩ :=
          through (R := fun s => m ≤ s ∧ s < k) (fun t ht => wb.dst t ht)
            (by
              intro t ht hR
              simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
                or_assoc] at ht
              rcases ht with rfl | rfl | rfl | ht | ht
              · dsimp at hR; omega
              · dsimp at hR; omega
              · exact .inr rfl
              · have := wa.src t ht; omega
              · exact .inl ht)
            (by omega) hv' (by omega)
        have hc' := mem_conn (out_of_range wa.src (s := m + 1) (by omega))
          (fun t ht => by have := wb.no_out t ht; omega) hc'
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hc'
        rcases hc' with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, rfl, rfl⟩
        · omega
        · omega
        · obtain ⟨rfl, -⟩ := Path.of_no_out hout hv''
          rw [rel_eps, rel_append] at hw
          obtain ⟨z, hzu, hz⟩ := hw
          rw [rel_eps] at hz
          obtain ⟨z', hzu', hz'⟩ := (rel_append M).mp hz
          rw [rel_eps, rel_nil] at hz'
          subst hz'
          exact ⟨z, iha hu hzu, ihb hu' hzu'⟩
      · omega
    · omega
    · omega

theorem sound_star {ta : List (Nat × Label × Nat)} {n m : Nat} {A : Rel E}
    (wa : WF ta (n + 2) m)
    (iha : ∀ {u x y}, Path ta (n + 2) u (n + 3) → rel M u x y → A x y) {w : List Label} {x y : E}
    (h : Path ([(n, .eps, n + 1), (n, .eps, n + 2), (n + 3, .eps, n + 2), (n + 3, .eps, n + 1)] ++
      ta) n w (n + 1))
    (hw : rel M w x y) : Rel.Star A x y := by
  have := wa.bound
  have hout : ∀ t ∈ [(n, Label.eps, n + 1), (n, Label.eps, n + 2), (n + 3, Label.eps, n + 2),
      (n + 3, Label.eps, n + 1)] ++ ta, t.1 ≠ n + 1 := by
    intro t ht
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at ht
    rcases ht with rfl | rfl | rfl | rfl | ht
    all_goals first
      | (dsimp only; omega)
      | (have := wa.src t ht; omega)
  cases h with
  | @cons _ c q w' _ ht hv =>
    have ht := mem_conn₁ (out_of_range wa.src (s := n) (by omega)) ht
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ht
    rcases ht with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · obtain ⟨rfl, -⟩ := Path.of_no_out hout hv
      rw [rel_eps, rel_nil] at hw
      subst hw
      exact .refl _
    · rw [rel_eps] at hw
      obtain ⟨z, h₁, h₂⟩ := loop M wa
        (by
          intro t ht hR
          simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
            or_assoc] at ht
          rcases ht with rfl | rfl | rfl | rfl | ht
          · dsimp at hR; omega
          · dsimp at hR; omega
          · exact .inr rfl
          · exact .inr rfl
          · exact .inl ht)
        (by
          intro c q hc
          have hc := mem_conn₁ (fun t ht => by have := wa.no_out t ht; omega) hc
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hc
          rcases hc with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
          · omega
          · omega
          · exact ⟨rfl, .inl rfl⟩
          · exact ⟨rfl, .inr rfl⟩)
        hout iha w'.length (Nat.le_refl _) hv hw
      exact .step h₁ h₂
    · omega
    · omega

theorem sound_plus {ta : List (Nat × Label × Nat)} {n m : Nat} {A : Rel E}
    (wa : WF ta (n + 2) m)
    (iha : ∀ {u x y}, Path ta (n + 2) u (n + 3) → rel M u x y → A x y) {w : List Label} {x y : E}
    (h : Path ([(n, .eps, n + 2), (n + 3, .eps, n + 2), (n + 3, .eps, n + 1)] ++ ta) n w (n + 1))
    (hw : rel M w x y) : Rel.Plus A x y := by
  have := wa.bound
  have hout : ∀ t ∈ [(n, Label.eps, n + 2), (n + 3, Label.eps, n + 2),
      (n + 3, Label.eps, n + 1)] ++ ta, t.1 ≠ n + 1 := by
    intro t ht
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at ht
    rcases ht with rfl | rfl | rfl | ht
    all_goals first
      | (dsimp only; omega)
      | (have := wa.src t ht; omega)
  cases h with
  | @cons _ c q w' _ ht hv =>
    have ht := mem_conn₁ (out_of_range wa.src (s := n) (by omega)) ht
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ht
    rcases ht with ⟨-, rfl, rfl⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [rel_eps] at hw
      exact loop M wa
        (by
          intro t ht hR
          simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
            or_assoc] at ht
          rcases ht with rfl | rfl | rfl | ht
          · dsimp at hR; omega
          · exact .inr rfl
          · exact .inr rfl
          · exact .inl ht)
        (by
          intro c q hc
          have hc := mem_conn₁ (fun t ht => by have := wa.no_out t ht; omega) hc
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hc
          rcases hc with ⟨h1, -⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
          · omega
          · exact ⟨rfl, .inl rfl⟩
          · exact ⟨rfl, .inr rfl⟩)
        hout iha w'.length (Nat.le_refl _) hv hw
    · omega
    · omega

theorem sound_opt {ta : List (Nat × Label × Nat)} {n m : Nat} {A : Rel E}
    (wa : WF ta (n + 2) m)
    (iha : ∀ {u x y}, Path ta (n + 2) u (n + 3) → rel M u x y → A x y) {w : List Label} {x y : E}
    (h : Path ([(n, .eps, n + 1), (n, .eps, n + 2), (n + 3, .eps, n + 1)] ++ ta) n w (n + 1))
    (hw : rel M w x y) : Rel.Opt A x y := by
  have := wa.bound
  have hout : ∀ t ∈ [(n, Label.eps, n + 1), (n, Label.eps, n + 2),
      (n + 3, Label.eps, n + 1)] ++ ta, t.1 ≠ n + 1 := by
    intro t ht
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at ht
    rcases ht with rfl | rfl | rfl | ht
    all_goals first
      | (dsimp only; omega)
      | (have := wa.src t ht; omega)
  cases h with
  | @cons _ c q w' _ ht hv =>
    have ht := mem_conn₁ (out_of_range wa.src (s := n) (by omega)) ht
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ht
    rcases ht with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨h1, -⟩
    · obtain ⟨rfl, -⟩ := Path.of_no_out hout hv
      rw [rel_eps, rel_nil] at hw
      exact .inl hw
    · obtain ⟨u, c', q', v, rfl, hu, hc, hv'⟩ :=
        through (R := fun s => n + 2 ≤ s ∧ s < m) (fun t ht => wa.dst t ht)
          (by
            intro t ht hR
            simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
              or_assoc] at ht
            rcases ht with rfl | rfl | rfl | ht
            · dsimp at hR; omega
            · dsimp at hR; omega
            · exact .inr rfl
            · exact .inl ht)
          (by omega) hv (by omega)
      have hc := mem_conn₁ (fun t ht => by have := wa.no_out t ht; omega) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hc
      rcases hc with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, rfl, rfl⟩
      · omega
      · omega
      · obtain ⟨rfl, -⟩ := Path.of_no_out hout hv'
        exact .inr (iha hu ((rel_wrap M).mp hw))
    · omega

section Fix

variable {b : Exp → Nat → List (Nat × Label × Nat) × Nat}

/-- A path into a piece, from outside the pieces to outside them: it reads
the piece's automaton through, and steps on from the state the piece leads
to. -/
theorem lay_through (hb : ∀ e m, WF (b e m).1 m (b e m).2) {T : List (Nat × Label × Nat)} :
    ∀ {ps : List (Nat × Exp × Nat)} {m : Nat}, (∀ p ∈ ps, p.1 < m) →
    (∀ t ∈ T, m ≤ t.1 → t.1 < (lay b ps m).2 → t ∈ (lay b ps m).1) →
    ∀ {s : Nat} {a : Label} {q : Nat} {w : List Label} {r : Nat}, s < m →
      (s, a, q) ∈ (lay b ps m).1 → Path T q w r → r < m →
      ∃ e d u v, (s, e, d) ∈ ps ∧ a = .eps ∧ (∃ m', Path (b e m').1 m' u (m' + 1)) ∧
        w = u ++ .eps :: v ∧ Path T d v r
  | [], _, _, _, _, _, _, _, _, _, ht, _, _ => by simp [lay] at ht
  | (s', e, d) :: ps, m, hps, hT, s, a, q, w, r, hs, ht, hw, hr => by
    have hbm := hb e m
    have := hbm.bound
    have hl := lay_bound hb ps (b e m).2
    have hsrc := lay_src hb ps (b e m).2
    have hs' : s' < m := hps (s', e, d) (by simp)
    have hps' : ∀ p ∈ ps, p.1 < m := fun p hp => hps p (by simp [hp])
    simp only [lay] at hT ht
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc,
      Prod.mk.injEq] at ht
    rcases ht with ⟨hss, ha, hq⟩ | ⟨h1, -, -⟩ | ht | ht
    · -- the first piece
      subst ha
      rw [hq] at hw
      obtain ⟨u, c, q', v, hwu, hu, hc, hv⟩ :=
        through (R := fun t => m ≤ t ∧ t < (b e m).2) (fun t ht => hbm.dst t ht)
          (by
            intro t ht' hR
            have := hT t ht' hR.1 (by omega)
            simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
              or_assoc] at this
            rcases this with rfl | rfl | h | h
            · dsimp only at hR; omega
            · exact .inr rfl
            · exact .inl h
            · rcases hsrc t h with h' | ⟨p, hp, h'⟩
              · omega
              · have := hps' p hp; omega)
          (by omega) hw (by omega)
      have hc := hT _ hc (by omega) (by omega)
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc,
        Prod.mk.injEq] at hc
      rcases hc with ⟨h1, -⟩ | ⟨-, hc, hd⟩ | hc | hc
      · omega
      · rw [hd] at hv
        exact ⟨e, d, u, v, by simp [hss], rfl, ⟨m, hu⟩, hc ▸ hwu, hv⟩
      · exact absurd rfl (hbm.no_out _ hc)
      · rcases hsrc _ hc with h' | ⟨p, hp, h'⟩
        · dsimp only at h'; omega
        · have := hps' p hp; dsimp only at h'; omega
    · omega
    · have := hbm.src _ ht
      dsimp only at this
      omega
    · obtain ⟨e', d', u, v, hp, ha, hu, hw', hv⟩ := lay_through hb
        (fun p hp => by have := hps' p hp; omega)
        (by
          intro t ht' h1 h2
          have := hT t ht' (by omega) h2
          simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
            or_assoc] at this
          rcases this with rfl | rfl | h | h
          · dsimp only at h1; omega
          · dsimp only at h1; omega
          · have := hbm.src t h; omega
          · exact h)
        (by omega) ht hw (by omega)
      exact ⟨e', d', u, v, by simp [hp], ha, hu, hw', hv⟩

variable {E : Type u} (M : Interp E)

/-- What the automaton of a `fix` reads from its start to its final state,
its main relation reaches. -/
theorem fix_paths (hb : ∀ e m, WF (b e m).1 m (b e m).2)
    (ihb : ∀ e m {u : List Label} {x y : E}, Path (b e m).1 m u (m + 1) → rel M u x y →
      e.denote M x y)
    {N : List (Exp × List (Nat × Exp))} {n main : Nat} (hmain : main < N.length)
    {w : List Label} {x y : E}
    (h : Path ((n + 2 + main, .eps, n + 1) :: (lay b (pieces N n) (n + 2 + N.length)).1) n w
      (n + 1))
    (hw : rel M w x y) : Reach N M main x y := by
  have hps : ∀ p ∈ pieces N n, p.1 < n + 2 + N.length := fun p hp => by
    have := pieces_bounds hp; omega
  have hsrc := lay_src hb (pieces N n) (n + 2 + N.length)
  have hT : ∀ t ∈ (n + 2 + main, Label.eps, n + 1) :: (lay b (pieces N n) (n + 2 + N.length)).1,
      n + 2 + N.length ≤ t.1 → t.1 < (lay b (pieces N n) (n + 2 + N.length)).2 →
      t ∈ (lay b (pieces N n) (n + 2 + N.length)).1 := by
    intro t ht h1 _
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · dsimp only at h1; omega
    · exact ht
  have hout : ∀ t ∈ (n + 2 + main, Label.eps, n + 1) ::
      (lay b (pieces N n) (n + 2 + N.length)).1, t.1 ≠ n + 1 := by
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · dsimp only; omega
    · rcases hsrc t ht with h | ⟨p, hp, h⟩
      · omega
      · have := pieces_bounds hp; omega
  -- from the hub of a relation the walk has reached
  have hA : ∀ (len : Nat) {i : Nat} {z y : E} {w : List Label}, w.length ≤ len →
      Reach N M i x z →
      Path ((n + 2 + main, .eps, n + 1) :: (lay b (pieces N n) (n + 2 + N.length)).1)
        (n + 2 + i) w (n + 1) →
      rel M w z y → Reach N M main x y := by
    intro len
    induction len with
    | zero =>
      intro i z y w hlen _ hp _
      obtain ⟨_, _, _, rfl, _, _⟩ := hp.first (by omega)
      simp at hlen
    | succ len ih =>
      intro i z y w hlen hr hpath hw
      have hi := hr.lt
      obtain ⟨a, q, w', rfl, ht, hv⟩ := hpath.first (by omega)
      simp only [List.mem_cons] at ht
      rcases ht with ht | ht
      · simp only [Prod.mk.injEq] at ht
        obtain ⟨h1, ha, hq⟩ := ht
        have hi' : i = main := by omega
        subst hi' ha
        rw [hq] at hv
        obtain ⟨rfl, -⟩ := Path.of_no_out hout hv
        rw [rel_eps, rel_nil] at hw
        exact hw ▸ hr
      · obtain ⟨e, d, u, v, hp, ha, ⟨m', hu⟩, rfl, hv'⟩ :=
          lay_through hb hps hT (by omega) ht hv (by omega)
        subst ha
        obtain ⟨i', c, L, hi', hpc⟩ := mem_pieces hp
        rcases hpc with hpc | ⟨j, a', hja, hj, hpc⟩
        · simp only [Prod.mk.injEq] at hpc; omega
        · simp only [Prod.mk.injEq] at hpc
          obtain ⟨hji, he, hd⟩ := hpc
          have hji : j = i := by omega
          subst hji he
          rw [hd] at hv'
          rw [rel_eps, rel_append] at hw
          obtain ⟨z', hu', hv''⟩ := hw
          rw [rel_eps] at hv''
          exact ih (by simp at hlen; omega) (.step hi' hja hr (ihb e m' hu hu')) hv' hv''
  -- from the start
  obtain ⟨a, q, w', rfl, ht, hv⟩ := h.first (by omega)
  simp only [List.mem_cons] at ht
  rcases ht with ht | ht
  · simp only [Prod.mk.injEq] at ht; omega
  · obtain ⟨e, d, u, v, hp, ha, ⟨m', hu⟩, rfl, hv'⟩ :=
      lay_through hb hps hT (by omega) ht hv (by omega)
    subst ha
    obtain ⟨i', c, L, hi', hpc⟩ := mem_pieces hp
    rcases hpc with hpc | ⟨j, a', hja, hj, hpc⟩
    · simp only [Prod.mk.injEq] at hpc
      obtain ⟨-, he, hd⟩ := hpc
      subst he
      rw [hd] at hv'
      rw [rel_eps, rel_append] at hw
      obtain ⟨z', hu', hv''⟩ := hw
      rw [rel_eps] at hv''
      exact hA _ (Nat.le_refl _) (.base hi' (ihb e m' hu hu')) hv' hv''
    · simp only [Prod.mk.injEq] at hpc; omega

theorem buildFix_sound (hb : ∀ e m, WF (b e m).1 m (b e m).2)
    (ihb : ∀ e m {u : List Label} {x y : E}, Path (b e m).1 m u (m + 1) → rel M u x y →
      e.denote M x y)
    {main : Nat} {defs : Defs} {n : Nat} {w : List Label} {x y : E}
    (h : Path (buildFix b main defs n).1 n w (n + 1)) (hw : rel M w x y) :
    (Exp.fix main defs).denote M x y := by
  unfold buildFix at h
  split at h
  · rename_i N hN
    split at h
    · rename_i hmain
      exact (fix_iff_reach hN _).mpr (fix_paths M hb ihb hmain h hw)
    · obtain ⟨_, _, _, _, ht, _⟩ := h.first (by omega)
      simp at ht
  · obtain ⟨_, _, _, _, ht, _⟩ := h.first (by omega)
    simp at ht

end Fix

/-- What the automaton of an expression reads from its start to its final
state, the expression denotes. -/
theorem sound : ∀ (k : Nat) (e : Exp) (n : Nat) {w : List Label} {x y : E},
    Path (build k e n).1 n w (n + 1) → rel M w x y → e.denote M x y
  | 0, _, n, w, x, y, h, _ => by
    obtain ⟨_, _, _, _, ht, _⟩ := h.first (by omega)
    simp [build] at ht
  | _ + 1, .label l, n, w, x, y, h, hw => by
    cases h with
    | cons ht hv =>
      simp only [build, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ht
      obtain ⟨-, rfl, rfl⟩ := ht
      obtain ⟨rfl, -⟩ := Path.of_no_out (by simp [build]) hv
      obtain ⟨z, hz, hzy⟩ := hw
      obtain rfl := (rel_nil M).mp hzy
      exact hz
  | _ + 1, .zero, n, w, x, y, h, _ => by
    cases h with
    | cons ht _ => simp [build] at ht
  | k + 1, .alt a b, n, w, x, y, h, hw =>
    sound_alt M (build_wf k a _) (build_wf k b _) (sound k a _) (sound k b _) h hw
  | k + 1, .seq a b, n, w, x, y, h, hw =>
    sound_seq M (build_wf k a _) (build_wf k b _) (sound k a _) (sound k b _) h hw
  | k + 1, .star a, n, w, x, y, h, hw => sound_star M (build_wf k a _) (sound k a _) h hw
  | k + 1, .plus a, n, w, x, y, h, hw => sound_plus M (build_wf k a _) (sound k a _) h hw
  | k + 1, .opt a, n, w, x, y, h, hw => sound_opt M (build_wf k a _) (sound k a _) h hw
  | _ + 1, .ref _, n, w, x, y, h, _ => by
    obtain ⟨_, _, _, _, ht, _⟩ := h.first (by omega)
    simp [build] at ht
  | k + 1, .fix main defs, n, w, x, y, h, hw => by
    simp only [build] at h
    exact buildFix_sound M (fun e m => build_wf k e m) (fun e m _ _ _ hu hr => sound k e m hu hr)
      h hw

/-- `ε u ε` along a path. -/
theorem wrap_path {T : List (Nat × Label × Nat)} {p q r t : Nat} {u : List Label}
    (h₁ : (p, Label.eps, q) ∈ T) (hu : Path T q u r) (h₂ : (r, Label.eps, t) ∈ T) :
    Path T p (.eps :: (u ++ [.eps])) t :=
  .cons h₁ (hu.append (.single h₂))

theorem mem_left {C ta tb : List (Nat × Label × Nat)} : ∀ t ∈ ta, t ∈ C ++ (ta ++ tb) :=
  fun _ h => List.mem_append.mpr (.inr (List.mem_append.mpr (.inl h)))

theorem mem_right {C ta tb : List (Nat × Label × Nat)} : ∀ t ∈ tb, t ∈ C ++ (ta ++ tb) :=
  fun _ h => List.mem_append.mpr (.inr (List.mem_append.mpr (.inr h)))

theorem mem_part {C ta : List (Nat × Label × Nat)} : ∀ t ∈ ta, t ∈ C ++ ta :=
  fun _ h => List.mem_append.mpr (.inr h)

/-- The iterations of `a*` and `a+` past the first, through the loop of the
part: one or more of them read from the part's start to its final state. -/
theorem iterate {ta T : List (Nat × Label × Nat)} {n : Nat} {A : Rel E}
    (hta : ∀ t ∈ ta, t ∈ T) (hback : (n + 3, Label.eps, n + 2) ∈ T)
    (iha : ∀ {x y}, A x y → ∃ u, Path ta (n + 2) u (n + 3) ∧ rel M u x y) :
    ∀ {x y z : E}, A x y → Rel.Star A y z →
      ∃ w, Path T (n + 2) w (n + 3) ∧ rel M w x z := by
  intro x y z hxy hyz
  induction hyz generalizing x with
  | refl =>
    obtain ⟨u, hu, hr⟩ := iha hxy
    exact ⟨u, hu.mono hta, hr⟩
  | step hyz' _ ih =>
    obtain ⟨u, hu, hr⟩ := iha hxy
    obtain ⟨w, hw, hwr⟩ := ih hyz'
    refine ⟨u ++ .eps :: w, (hu.mono hta).append (.cons hback hw), ?_⟩
    rw [rel_append]
    exact ⟨_, hr, (rel_eps M).mpr hwr⟩

/-- A piece's automaton, read through, from the state the piece is entered
from to the one it leads to. -/
theorem lay_complete {b : Exp → Nat → List (Nat × Label × Nat) × Nat} {P : List Label → Prop} :
    ∀ {ps : List (Nat × Exp × Nat)} {m s : Nat} {e : Exp} {d : Nat}, (s, e, d) ∈ ps →
    (∀ m', ∃ u, Path (b e m').1 m' u (m' + 1) ∧ P u) →
    ∃ u, Path (lay b ps m).1 s (.eps :: (u ++ [.eps])) d ∧ P u
  | [], _, _, _, _, h, _ => by simp at h
  | (_, _, _) :: _, m, _, _, _, h, hp => by
    simp only [List.mem_cons, Prod.mk.injEq] at h
    simp only [lay]
    rcases h with ⟨rfl, rfl, rfl⟩ | h
    · obtain ⟨u, hu, hPu⟩ := hp m
      exact ⟨u, wrap_path (by simp) (hu.mono mem_left) (by simp), hPu⟩
    · obtain ⟨u, hu, hPu⟩ := lay_complete (m := (b _ m).2) h hp
      exact ⟨u, hu.mono mem_right, hPu⟩

/-- What a `fix` whose definitions are well-formed denotes, its automaton
reads from its start to its final state. -/
theorem buildFix_complete {b : Exp → Nat → List (Nat × Label × Nat) × Nat}
    {main : Nat} {defs : Defs}
    (ihb : ∀ e, e.size ≤ defs.size → e.wellFormed = true → ∀ m {x y : E}, e.denote M x y →
      ∃ u, Path (b e m).1 m u (m + 1) ∧ rel M u x y)
    (hwf : (Exp.fix main defs).wellFormed = true) {n : Nat} {x y : E}
    (h : (Exp.fix main defs).denote M x y) :
    ∃ w, Path (buildFix b main defs n).1 n w (n + 1) ∧ rel M w x y := by
  simp only [Exp.wellFormed, Bool.and_eq_true, Option.isSome_iff_exists] at hwf
  obtain ⟨⟨N, hN⟩, hwd⟩ := hwf
  have hr := (fix_iff_reach hN _).mp h
  have hmain := hr.lt
  unfold buildFix
  rw [hN]
  simp only [hmain, ite_true]
  -- each relation, from the start to its hub
  have hC : ∀ {i : Nat} {x y : E}, Reach N M i x y →
      ∃ w, Path (lay b (pieces N n) (n + 2 + N.length)).1 n w (n + 2 + i) ∧ rel M w x y := by
    intro i x y hr
    induction hr with
    | @base i c L x y hi hc =>
      obtain ⟨hcs, -⟩ := Defs.size_of_nfs hN hi
      obtain ⟨hcw, -⟩ := Defs.wellFormed_of_nfs hN hwd hi
      obtain ⟨u, hu, hr⟩ := lay_complete (m := n + 2 + N.length) (P := fun u => rel M u x y)
        (pieces_base hi) (fun m' => ihb c hcs hcw m' hc)
      exact ⟨_, hu, (rel_wrap M).mpr hr⟩
    | @step i c L j a x z y hi hja hr' ha ih =>
      obtain ⟨-, has⟩ := Defs.size_of_nfs hN hi
      obtain ⟨-, haw⟩ := Defs.wellFormed_of_nfs hN hwd hi
      obtain ⟨w, hw, hwr⟩ := ih
      obtain ⟨u, hu, hr⟩ := lay_complete (m := n + 2 + N.length) (P := fun u => rel M u z y)
        (pieces_step hi hja hr'.lt) (fun m' => ihb a (has _ hja) (haw _ hja) m' ha)
      refine ⟨w ++ .eps :: (u ++ [.eps]), hw.append hu, ?_⟩
      rw [rel_append]
      exact ⟨z, hwr, (rel_wrap M).mpr hr⟩
  obtain ⟨w, hw, hwr⟩ := hC hr
  refine ⟨w ++ [.eps], (hw.mono fun _ h => List.mem_cons_of_mem _ h).append (.single (by simp)), ?_⟩
  rw [rel_append]
  exact ⟨y, hwr, (rel_eps M).mpr ((rel_nil M).mpr rfl)⟩

/-- What a well-formed expression denotes, the automaton reads from its
start to its final state, if its bound is the expression's size or more. -/
theorem complete : ∀ (k : Nat) (e : Exp) (n : Nat) {x y : E}, e.size ≤ k →
    e.wellFormed = true → e.denote M x y → ∃ w, Path (build k e n).1 n w (n + 1) ∧ rel M w x y
  | 0, e, _, _, _, hs, _, _ => absurd hs (by have := Exp.size_pos e; omega)
  | _ + 1, .label l, n, x, y, _, _, h => by
    refine ⟨[l], .single (by simp [build]), ?_⟩
    exact ⟨y, h, (rel_nil M).mpr rfl⟩
  | _ + 1, .zero, n, x, y, _, _, h => absurd h id
  | k + 1, .alt a b, n, x, y, hs, hwf, h => by
    simp only [Exp.size] at hs
    simp only [Exp.wellFormed, Bool.and_eq_true] at hwf
    simp only [build]
    rcases h with h | h
    · obtain ⟨u, hu, hr⟩ := complete k a (n + 2) (by omega) hwf.1 h
      exact ⟨_, wrap_path (by simp) (hu.mono mem_left) (by simp), (rel_wrap M).mpr hr⟩
    · obtain ⟨u, hu, hr⟩ := complete k b _ (by omega) hwf.2 h
      exact ⟨_, wrap_path (by simp) (hu.mono mem_right) (by simp), (rel_wrap M).mpr hr⟩
  | k + 1, .seq a b, n, x, y, hs, hwf, h => by
    simp only [Exp.size] at hs
    simp only [Exp.wellFormed, Bool.and_eq_true] at hwf
    simp only [build]
    obtain ⟨z, hxz, hzy⟩ := h
    obtain ⟨u, hu, hr⟩ := complete k a (n + 2) (by omega) hwf.1 hxz
    obtain ⟨u', hu', hr'⟩ := complete k b _ (by omega) hwf.2 hzy
    refine ⟨.eps :: (u ++ .eps :: (u' ++ [.eps])),
      .cons (by simp) ((hu.mono mem_left).append (wrap_path (by simp) (hu'.mono mem_right)
        (by simp))), ?_⟩
    rw [rel_eps, rel_append]
    exact ⟨z, hr, (rel_wrap M).mpr hr'⟩
  | k + 1, .star a, n, x, y, hs, hwf, h => by
    simp only [Exp.size] at hs
    simp only [Exp.wellFormed] at hwf
    simp only [build]
    cases h with
    | refl => exact ⟨[.eps], .single (by simp), (rel_eps M).mpr ((rel_nil M).mpr rfl)⟩
    | step hxz hzy =>
      obtain ⟨w, hw, hr⟩ := iterate M (mem_part (C := [(n, .eps, n + 1), (n, .eps, n + 2),
        (n + 3, .eps, n + 2), (n + 3, .eps, n + 1)])) (by simp)
        (fun h => complete k a (n + 2) (by omega) hwf h) hxz hzy
      exact ⟨_, wrap_path (by simp) hw (by simp), (rel_wrap M).mpr hr⟩
  | k + 1, .plus a, n, x, y, hs, hwf, h => by
    simp only [Exp.size] at hs
    simp only [Exp.wellFormed] at hwf
    simp only [build]
    obtain ⟨z, hxz, hzy⟩ := h
    obtain ⟨w, hw, hr⟩ := iterate M (mem_part (C := [(n, .eps, n + 2), (n + 3, .eps, n + 2),
      (n + 3, .eps, n + 1)])) (by simp) (fun h => complete k a (n + 2) (by omega) hwf h) hxz hzy
    exact ⟨_, wrap_path (by simp) hw (by simp), (rel_wrap M).mpr hr⟩
  | k + 1, .opt a, n, x, y, hs, hwf, h => by
    simp only [Exp.size] at hs
    simp only [Exp.wellFormed] at hwf
    simp only [build]
    rcases h with h | h
    · exact ⟨[.eps], .single (by simp), (rel_eps M).mpr ((rel_nil M).mpr h)⟩
    · obtain ⟨u, hu, hr⟩ := complete k a (n + 2) (by omega) hwf h
      exact ⟨_, wrap_path (by simp) (hu.mono mem_part) (by simp), (rel_wrap M).mpr hr⟩
  | _ + 1, .ref _, n, x, y, _, _, h => absurd h id
  | k + 1, .fix main defs, n, x, y, hs, hwf, h => by
    simp only [Exp.size] at hs
    simp only [build]
    exact buildFix_complete M (fun e he hwe m _ _ h' => complete k e m (by omega) hwe h') hwf h

end Thompson

/-- The automaton of `n` states with the transitions `T`, as (source,
letter, destination), and the given starting and accepting states. -/
def NFA.ofList {L : Type} (n : Nat) (T : List (Nat × L × Nat)) (start accepting : List Nat) :
    NFA L where
  outs := (Array.range n).map fun p => T.filterMap fun t => if t.1 = p then some t.2 else none
  accepting := (Array.range n).map fun p => accepting.contains p
  start := start

namespace NFA

variable {L : Type} {n : Nat} {T : List (Nat × L × Nat)} {st acc : List Nat}

theorem mem_trans_ofList {p : Nat} {a : L} {q : Nat} (hp : p < n) :
    (a, q) ∈ (ofList n T st acc).trans p ↔ (p, a, q) ∈ T := by
  simp only [trans, ofList, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_range, hp, ite_true, Option.map_some, Option.getD_some, List.mem_filterMap]
  constructor
  · rintro ⟨⟨s, b, d⟩, hmem, hf⟩
    by_cases hs : s = p
    · subst hs
      simp only [ite_true, Option.some.injEq] at hf
      cases hf
      exact hmem
    · simp [hs] at hf
  · intro h
    exact ⟨(p, a, q), h, by simp⟩

theorem isAccepting_ofList {p : Nat} (hp : p < n) :
    (ofList n T st acc).isAccepting p = true ↔ p ∈ acc := by
  simp [isAccepting, ofList, Array.getD_eq_getD_getElem?, hp]

theorem trans_ofList_ge {p : Nat} (hp : n ≤ p) : (ofList n T st acc).trans p = [] := by
  simp only [trans, ofList, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_range]
  split
  · omega
  · rfl

/-- What the automaton accepts: the words of the paths from a state to an
accepting one. -/
theorem accepts_ofList (hT : ∀ t ∈ T, t.1 < n) (hacc : ∀ q ∈ acc, q < n) {p : Nat}
    {w : List L} : (ofList n T st acc).Accepts p w ↔ ∃ q, Path T p w q ∧ q ∈ acc := by
  constructor
  · intro h
    induction h with
    | @nil q hq =>
      by_cases hn : q < n
      · exact ⟨q, .nil q, (isAccepting_ofList hn).mp hq⟩
      · simp [isAccepting, ofList, Array.getD_eq_getD_getElem?, hn] at hq
    | @cons q a q' w ht _ ih =>
      by_cases hn : q < n
      · obtain ⟨r, hr, hracc⟩ := ih
        exact ⟨r, .cons ((mem_trans_ofList hn).mp ht) hr, hracc⟩
      · rw [trans_ofList_ge (by omega)] at ht
        simp at ht
  · rintro ⟨q, hpath, hq⟩
    induction hpath with
    | nil r => exact .nil ((isAccepting_ofList (hacc r hq)).mpr hq)
    | cons ht _ ih =>
      exact .cons ((mem_trans_ofList (hT _ ht)).mpr ht) (ih hq)

end NFA

namespace Thompson

/-- Lean's automaton of an expression: it starts at state 0 and accepts at
state 1. -/
def nfa (e : Exp) : NFA Label :=
  NFA.ofList (build e.size e 0).2 (build e.size e 0).1 [0] [1]

variable {E : Type u} (M : Interp E)

theorem nfa_accepts {e : Exp} {w : List Label} :
    (nfa e).Accepts 0 w ↔ Path (build e.size e 0).1 0 w 1 := by
  have wf := build_wf e.size e 0
  have hT : ∀ t ∈ (build e.size e 0).1, t.1 < (build e.size e 0).2 := fun t ht => (wf.src t ht).2
  have hacc : ∀ q ∈ [1], q < (build e.size e 0).2 := by
    intro q hq
    simp at hq
    have := wf.bound
    omega
  rw [nfa, NFA.accepts_ofList hT hacc]
  simp

/-- What Lean's automaton of an expression denotes, the expression does. -/
theorem nfa_sound (e : Exp) {x y : E} (h : (nfa e).denote (Label.denote M) x y) :
    e.denote M x y := by
  obtain ⟨q, hq, w, hw, hr⟩ := h
  simp only [nfa, NFA.ofList, List.mem_cons, List.not_mem_nil, or_false] at hq
  subst hq
  exact sound M e.size e 0 (nfa_accepts.mp hw) hr

/-- What a well-formed expression denotes, Lean's automaton of it does. -/
theorem nfa_complete (e : Exp) (hwf : e.wellFormed = true) {x y : E} (h : e.denote M x y) :
    (nfa e).denote (Label.denote M) x y := by
  obtain ⟨w, hpath, hr⟩ := complete M e.size e 0 (Nat.le_refl _) hwf h
  exact ⟨0, by simp [nfa, NFA.ofList], w, nfa_accepts.mpr hpath, hr⟩

/-- **Thompson's construction is correct**: Lean's automaton of a
well-formed expression denotes what the expression does. -/
theorem nfa_denote (e : Exp) (hwf : e.wellFormed = true) {x y : E} :
    (nfa e).denote (Label.denote M) x y ↔ e.denote M x y :=
  ⟨nfa_sound M e, nfa_complete M e hwf⟩

end Thompson

end KaterCert
