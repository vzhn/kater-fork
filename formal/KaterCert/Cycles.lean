import KaterCert.Extensible

/-!
# The cycles of an extensibility check

How the words of an extensibility check come from its constraint
(`exitsToCheck`, `toEndOfWord`, `canSkip`) is a claim about the cycles of
the constraint's automaton `N`: each cycle through an event `e` that GenMC
adds either visits `e` where it can do without it, or reads, from `e`, a
word of the words automaton. This proves it of the words Lean builds
(`Extensible.words`), for any meaning of the letters:

- A cycle is a closed run of `N` over events (`Walk`): letters between
  events, and the ends of words, where the next word begins at the same
  event. A visit of `e` is entered by a relation's letter; the run reads
  predicates of `e`, and maybe ends its word, until a relation's letter
  leaves `e`: an exit, which the search of `Extensible.reach` covers
  (`cover`).
- At a visit, the exit is not by a step within `rf`, `mo` or `fr`, of which
  `e` has none, and does not check what an event GenMC adds cannot be.
  Either the check asks about it, and the rest of the cycle's word from `e`
  is a word of the words automaton; or it can be skipped after every step
  into the state, and the run with one step of `N` in place of the step
  into `e`, the predicates of `e` and the exit is a shorter closed run
  (`shorten`).
- So if the words automaton relates `e` to nothing (for coherence: the
  automaton of the exits that go on into the next word does not relate `e`
  to itself), a shortest cycle does not visit `e` (`avoid`): it is a cycle
  of the events other than `e`.

`cycles_sound` puts it together: wherever the theory is sound, `po` and
`po-loc` are transitive, and `e` has no step within `rf`, `mo` or `fr` out
of it and is `addable`, a cycle of `N` is one of `N` without `e`, unless
the words relate `e` to something. `check_sound` takes what it assumes of
the words and of `N` from Lean's checks of the evidence (`checkInclusions`,
`checkCycles`).

The argument is Kater's (`doc/verification.md`, Extensibility), about the
words Lean builds (`Extensible.lean`, which mirrors `exitsToCheck`).
-/

namespace KaterCert

universe u

/-- The meaning of letters on the events other than `e`. -/
def Interp.without {E : Type u} (M : Interp E) (e : E) : Interp {a : E // a ≠ e} where
  rel i a b := M.rel i a.1 b.1
  pred i a := M.pred i a.1

theorem Label.denote_without {E : Type u} {M : Interp E} {e : E} (l : Label)
    {a b : {a : E // a ≠ e}} : l.denote (M.without e) a b ↔ l.denote M a.1 b.1 := by
  rcases l with ⟨_ | r, pre, post⟩
  · simp only [Label.denote, Subtype.ext_iff]
    rfl
  · rfl

open ReadChain

namespace Extensible

variable {E : Type u}

/-! ## Runs over events -/

/-- A move of a run of an automaton over events: by a letter, from state
`src` at event `x` to state `dst` at event `y`; or, with no letter, from
`src`, where a word ends, to `dst`, where the next begins, at one event. -/
structure Move (E : Type u) where
  src : Nat
  lab : Option Label
  dst : Nat
  x : E
  y : E

namespace Move

/-- The move is one of `N`, with the letters meaning `M`. -/
def Valid (N : NFA Label) (M : Interp E) (m : Move E) : Prop :=
  match m.lab with
  | some l => (l, m.dst) ∈ N.trans m.src ∧ l.denote M m.x m.y
  | none => N.isAccepting m.src = true ∧ m.dst ∈ N.start ∧ m.x = m.y

/-- A move by a relation's letter. -/
def isStep (m : Move E) : Bool :=
  match m.lab with
  | some l => l.rel.isSome
  | none => false

/-- The end of a word. -/
def isWrap (m : Move E) : Bool := m.lab.isNone

variable {N : NFA Label} {M : Interp E}

/-- A move that is not a relation's stays at its event. -/
theorem stay {m : Move E} (hv : m.Valid N M) (hs : m.isStep = false) : m.x = m.y := by
  unfold Valid at hv
  unfold isStep at hs
  split at hv
  · rename_i l hl
    rw [hl] at hs
    have hr : l.rel = none := by
      cases h : l.rel with
      | none => rfl
      | some _ => simp [h] at hs
    have := hv.2
    simp only [Label.denote, hr] at this
    exact this.1
  · exact hv.2.2

/-- A move between events other than `e` is one with the letters on them. -/
theorem valid_lift {e : E} {m : Move E} (hv : m.Valid N M) {hx : m.x ≠ e} {hy : m.y ≠ e} :
    (⟨m.src, m.lab, m.dst, ⟨m.x, hx⟩, ⟨m.y, hy⟩⟩ : Move {a : E // a ≠ e}).Valid N (M.without e) := by
  rcases m with ⟨src, lab, dst, x, y⟩
  cases lab with
  | some l =>
    simp only [Valid] at hv ⊢
    exact ⟨hv.1, (Label.denote_without l).mpr hv.2⟩
  | none =>
    simp only [Valid] at hv ⊢
    exact ⟨hv.1, hv.2.1, Subtype.ext hv.2.2⟩

end Move

/-- `Walk N M q a ms q' b`: the moves `ms`, in order, take `N` from state `q`
at event `a` to state `q'` at event `b`. -/
inductive Walk (N : NFA Label) (M : Interp E) : Nat → E → List (Move E) → Nat → E → Prop
  | nil (q : Nat) (a : E) : Walk N M q a [] q a
  | cons {m : Move E} {ms : List (Move E)} {q : Nat} {b : E} :
      m.Valid N M → Walk N M m.dst m.y ms q b → Walk N M m.src m.x (m :: ms) q b

namespace Walk

variable {N : NFA Label} {M : Interp E}

theorem append {q a A q' b B q'' c} (h₁ : Walk N M q a A q' b) (h₂ : Walk N M q' b B q'' c) :
    Walk N M q a (A ++ B) q'' c := by
  induction h₁ with
  | nil => exact h₂
  | cons hv _ ih => exact .cons hv (ih h₂)

theorem split : ∀ {A B : List (Move E)} {q a q'' c}, Walk N M q a (A ++ B) q'' c →
    ∃ q' b, Walk N M q a A q' b ∧ Walk N M q' b B q'' c
  | [], _, q, a, _, _, h => ⟨q, a, .nil q a, h⟩
  | _ :: _, _, _, _, _, _, h => by
    cases h with
    | cons hv h' =>
      obtain ⟨q', b, h₁, h₂⟩ := split h'
      exact ⟨q', b, .cons hv h₁, h₂⟩

theorem cons_inv {m : Move E} {ms q a q' b} (h : Walk N M q a (m :: ms) q' b) :
    q = m.src ∧ a = m.x ∧ m.Valid N M ∧ Walk N M m.dst m.y ms q' b := by
  cases h with
  | cons hv h' => exact ⟨rfl, rfl, hv, h'⟩

/-- Moves that are not relations' stay at their event. -/
theorem stays {q a ms q' b} (h : Walk N M q a ms q' b) (hs : ∀ m ∈ ms, m.isStep = false) :
    a = b := by
  induction h with
  | nil => rfl
  | @cons m ms₀ q₀ b₀ hv h' ih =>
    rw [Move.stay hv (hs m (List.mem_cons_self ..))]
    exact ih fun m' hm' => hs m' (List.mem_cons_of_mem _ hm')

/-- The run of a word an automaton accepts. -/
theorem ofAccepts {q w} (h : N.Accepts q w) : ∀ {a b}, wordRel (Label.denote M) w a b →
    ∃ ms f, Walk N M q a ms f b ∧ N.isAccepting f = true ∧ ∀ m ∈ ms, m.isWrap = false := by
  induction h with
  | nil hq =>
    intro a b hab
    cases hab
    exact ⟨[], _, .nil _ _, hq, by simp⟩
  | @cons q l q' w ht _ ih =>
    intro a b hab
    obtain ⟨c, hl, hw⟩ := hab
    obtain ⟨ms, f, hms, hf, hnw⟩ := ih hw
    refine ⟨⟨q, some l, q', a, c⟩ :: ms, f, Walk.cons (m := ⟨q, some l, q', a, c⟩) ⟨ht, hl⟩ hms,
      hf, ?_⟩
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · rfl
    · exact hnw m hm

/-- The word of a run without the end of a word, to an accepting state. -/
theorem toAccepts {q a ms f b} (h : Walk N M q a ms f b) (hf : N.isAccepting f = true)
    (hnw : ∀ m ∈ ms, m.isWrap = false) : ∃ w, N.Accepts q w ∧ wordRel (Label.denote M) w a b := by
  induction h with
  | nil => exact ⟨[], .nil hf, rfl⟩
  | @cons m ms' q₀ b₀ hv h' ih =>
    obtain ⟨w, hw, hr⟩ := ih hf fun m' hm' => hnw m' (List.mem_cons_of_mem _ hm')
    have hm := hnw m (List.mem_cons_self ..)
    unfold Move.isWrap at hm
    unfold Move.Valid at hv
    split at hv
    · rename_i l hl
      exact ⟨l :: w, .cons hv.1 hw, ⟨_, hv.2, hr⟩⟩
    · rename_i hl
      simp [hl] at hm

/-- The first word of a run to an accepting state: up to the end of the
first word, if it ends one. -/
theorem rest {q a ms f b} (h : Walk N M q a ms f b) (hf : N.isAccepting f = true) :
    ∃ w c, N.Accepts q w ∧ wordRel (Label.denote M) w a c := by
  induction h with
  | nil => exact ⟨[], _, .nil hf, rfl⟩
  | @cons m ms' q₀ b₀ hv h' ih =>
    obtain ⟨w, c, hw, hr⟩ := ih hf
    unfold Move.Valid at hv
    split at hv
    · rename_i l _
      exact ⟨l :: w, c, .cons hv.1 hw, ⟨_, hv.2, hr⟩⟩
    · exact ⟨[], m.x, .nil hv.1, rfl⟩

/-- What a run to an accepting state relates: a word, and then whole
words. -/
theorem toStar {q a ms f b} (h : Walk N M q a ms f b) (hf : N.isAccepting f = true) :
    ∃ w c, N.Accepts q w ∧ wordRel (Label.denote M) w a c ∧
      Rel.Star (N.denote (Label.denote M)) c b := by
  induction h with
  | nil => exact ⟨[], _, .nil hf, rfl, .refl _⟩
  | @cons m ms' q₀ b₀ hv h' ih =>
    obtain ⟨w, c, hw, hr, hs⟩ := ih hf
    unfold Move.Valid at hv
    split at hv
    · rename_i l _
      exact ⟨l :: w, c, .cons hv.1 hw, ⟨_, hv.2, hr⟩, hs⟩
    · obtain ⟨hacc, hstart, hxy⟩ := hv
      refine ⟨[], m.x, .nil hacc, rfl, .step ?_ hs⟩
      rw [hxy]
      exact ⟨_, hstart, w, hw, hr⟩

/-- The run of a pair a word of an automaton relates. -/
theorem ofDenote {a b} (h : N.denote (Label.denote M) a b) :
    ∃ s ∈ N.start, ∃ ms f, Walk N M s a ms f b ∧ N.isAccepting f = true ∧
      ∀ m ∈ ms, m.isWrap = false := by
  obtain ⟨s, hs, w, hw, hr⟩ := h
  obtain ⟨ms, f, hms, hf, hnw⟩ := ofAccepts hw hr
  exact ⟨s, hs, ms, f, hms, hf, hnw⟩

/-- The run of a pair the words of an automaton relate in sequence. -/
theorem ofPlus {a b} (h : Rel.Plus (N.denote (Label.denote M)) a b) :
    ∃ s ∈ N.start, ∃ ms f, Walk N M s a ms f b ∧ N.isAccepting f = true := by
  obtain ⟨z, haz, hzb⟩ := h
  have : ∀ {z b}, Rel.Star (N.denote (Label.denote M)) z b → ∀ {a},
      N.denote (Label.denote M) a z →
        ∃ s ∈ N.start, ∃ ms f, Walk N M s a ms f b ∧ N.isAccepting f = true := by
    intro z b hzb
    induction hzb with
    | refl =>
      intro a haz
      obtain ⟨s, hs, ms, f, hms, hf, -⟩ := ofDenote haz
      exact ⟨s, hs, ms, f, hms, hf⟩
    | @step z' y' b' hzy hyb ih =>
      intro a haz
      obtain ⟨s', hs', ms', f', hms', hf'⟩ := ih hzy
      obtain ⟨s, hs, ms, f, hms, hf, -⟩ := ofDenote haz
      refine ⟨s, hs, ms ++ ⟨f, none, s', z', z'⟩ :: ms', f', ?_, hf'⟩
      exact hms.append (Walk.cons (m := ⟨f, none, s', z', z'⟩) ⟨hf, hs', rfl⟩ hms')
  exact this hzb haz

/-- A closed run from a starting state relates its event to itself by
words of the automaton in sequence. -/
theorem toPlus {s a ms f} (h : Walk N M s a ms f a) (hs : s ∈ N.start)
    (hf : N.isAccepting f = true) : Rel.Plus (N.denote (Label.denote M)) a a := by
  obtain ⟨w, c, hw, hr, hc⟩ := toStar h hf
  exact ⟨c, ⟨s, hs, w, hw, hr⟩, hc⟩

/-- A run between events other than `e`, as one of the letters on them. -/
theorem lift {e : E} {q a ms q' b} (h : Walk N M q a ms q' b) (ha : a ≠ e)
    (hy : ∀ m ∈ ms, m.y ≠ e) :
    ∃ (hb : b ≠ e) (ms' : List (Move {a : E // a ≠ e})),
      Walk N (M.without e) q ⟨a, ha⟩ ms' q' ⟨b, hb⟩ ∧ ms'.map Move.isWrap = ms.map Move.isWrap := by
  induction h with
  | nil q a => exact ⟨ha, [], .nil _ _, rfl⟩
  | @cons m ms₀ q₀ b₀ hv h' ih =>
    have hmy : m.y ≠ e := hy m (List.mem_cons_self ..)
    obtain ⟨hb, ms', hw', hmap⟩ := ih hmy fun m' hm' => hy m' (List.mem_cons_of_mem _ hm')
    let m' : Move {a : E // a ≠ e} := ⟨m.src, m.lab, m.dst, ⟨m.x, ha⟩, ⟨m.y, hmy⟩⟩
    refine ⟨hb, m' :: ms', Walk.cons (m := m') ?_ hw', ?_⟩
    · exact Move.valid_lift hv
    · simp only [List.map_cons, hmap]
      rfl

end Walk

/-! ## The search for the exits -/

section Search

variable {θ : Theory} {loc : Rel E} {N : NFA Label} {M : Interp E}

theorem lt_of_mem_trans {X : NFA Label} {p : Nat} {t : Label × Nat} (h : t ∈ X.trans p) :
    p < X.size := by
  unfold NFA.trans at h
  unfold NFA.size
  rcases Nat.lt_or_ge p X.outs.size with hp | hp
  · exact hp
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)] at h
    simp at h

theorem unsat_false (hθ : θ.Sound M loc) {ps : List Predicate} {a : E} (h : Checks M ps a) :
    θ.unsat ps = false := by
  cases hu : θ.unsat ps
  · rfl
  · exact absurd h (hθ.unsat ps hu a)

theorem checks_union_iff {ps qs : List Predicate} {a : E} :
    Checks M (Guarded.union ps qs) a ↔ Checks M ps a ∧ Checks M qs a := by
  constructor
  · intro h
    have hps : ∀ p ∈ ps, p ∈ Guarded.union ps qs := by
      intro p hp
      unfold Guarded.union
      have : ∀ (l : List Predicate) (acc : List Predicate), p ∈ acc →
          p ∈ l.foldl (fun acc q => Guarded.insertPred q acc) acc := by
        intro l
        induction l with
        | nil => intro acc h; exact h
        | cons q l ih =>
          intro acc h
          apply ih
          exact mem_insertPred_of_mem h
      exact this qs ps hp
    have hqs : ∀ q ∈ qs, q ∈ Guarded.union ps qs := by
      intro q hq
      unfold Guarded.union
      have : ∀ (l : List Predicate) (acc : List Predicate), q ∈ l →
          q ∈ l.foldl (fun acc q => Guarded.insertPred q acc) acc := by
        intro l
        induction l with
        | nil => intro _ h; simp at h
        | cons q' l ih =>
          intro acc h
          simp only [List.foldl_cons]
          rcases List.mem_cons.mp h with rfl | h
          · have : ∀ (l : List Predicate) (acc : List Predicate), q ∈ acc →
                q ∈ l.foldl (fun acc q => Guarded.insertPred q acc) acc := by
              intro l
              induction l with
              | nil => intro acc h; exact h
              | cons q'' l ih' =>
                intro acc h
                exact ih' _ (mem_insertPred_of_mem h)
            exact this l _ mem_insertPred_self
          · exact ih _ h
      exact this qs ps hq
    exact ⟨fun p hp => h p (hps p hp), fun q hq => h q (hqs q hq)⟩
  · rintro ⟨hp, hq⟩
    exact Guarded.checks_union hp hq
where
  mem_insertPred_of_mem {p q : Predicate} {acc : List Predicate} (h : p ∈ acc) :
      p ∈ Guarded.insertPred q acc := by
    induction acc with
    | nil => simp at h
    | cons r rs ih =>
      unfold Guarded.insertPred
      split
      · exact h
      · split
        · exact List.mem_cons_of_mem _ h
        · rcases List.mem_cons.mp h with rfl | h
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (ih h)
  mem_insertPred_self {q : Predicate} {acc : List Predicate} : q ∈ Guarded.insertPred q acc := by
    induction acc with
    | nil => simp [Guarded.insertPred]
    | cons r rs ih =>
      unfold Guarded.insertPred
      split
      · rename_i h
        rw [eq_of_beq h]
        exact List.mem_cons_self ..
      · split
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ ih

/-- **The search covers the runs at the event**: a run of predicates' letters
and ends of words from a configuration of a closed set, at an event whose
predicates the configuration read hold, ends at a configuration of the set
whose predicates hold too, which went on into the next word if the run
did. -/
theorem cover (hθ : θ.Sound M loc) {S : List Conf} (hS : closed θ N S = true) :
    ∀ {q a seg q' b}, Walk N M q a seg q' b → (∀ m ∈ seg, m.isStep = false) →
      ∀ {K : List Predicate} {w : Bool}, (q, K, w) ∈ S → Checks M K a →
        ∃ K', (q', K', w || seg.any Move.isWrap) ∈ S ∧ Checks M K' a := by
  intro q a seg q' b h
  induction h with
  | nil q a =>
    intro _ K w hc hK
    exact ⟨K, by simpa using hc, hK⟩
  | @cons m ms q₀ b₀ hv h' ih =>
    intro hs K w hc hK
    have hst := hs m (List.mem_cons_self ..)
    have hxy := Move.stay hv hst
    have hrest : ∀ m' ∈ ms, m'.isStep = false := fun m' hm' => hs m' (List.mem_cons_of_mem _ hm')
    simp only [closed, List.all_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hS
    -- the configuration the move leads to, and the one of `S` that covers it
    unfold Move.Valid at hv
    split at hv
    · rename_i l hl
      have hr : l.rel = none := by
        unfold Move.isStep at hst
        rw [hl] at hst
        cases h : l.rel with
        | none => rfl
        | some _ => simp [h] at hst
      have hpre : Checks M l.pre m.x := by
        have := hv.2
        simp only [Label.denote, hr] at this
        exact this.2
      have hU : Checks M (Guarded.union K l.pre) m.x := Guarded.checks_union hK hpre
      have hmv : (m.dst, Guarded.union K l.pre, w) ∈ moves θ N (m.src, K, w) := by
        unfold moves
        apply List.mem_append_left
        rw [List.mem_filterMap]
        refine ⟨(l, m.dst), hv.1, ?_⟩
        simp [hr, unsat_false hθ hU]
      obtain ⟨c'', hc'', ⟨hq'', hw''⟩, hsub⟩ := hS _ hc _ hmv
      obtain ⟨K', hK', hchk⟩ := ih hrest (K := c''.2.1) (w := w)
        (by
          rcases c'' with ⟨q1, K1, w1⟩
          simp only at hq'' hw'' ⊢
          rw [← hq'', ← hw'']
          exact hc'')
        (by rw [← hxy]; exact Guarded.checks_of_subTests hsub hU)
      refine ⟨K', ?_, by rw [hxy]; exact hchk⟩
      have : (m :: ms).any Move.isWrap = ms.any Move.isWrap := by
        simp [List.any_cons, Move.isWrap, hl]
      rw [this]
      exact hK'
    · rename_i hl
      obtain ⟨hacc, hstart, -⟩ := hv
      have hmv : (m.dst, K, true) ∈ moves θ N (m.src, K, w) := by
        unfold moves
        apply List.mem_append_right
        simp only [hacc, ite_true, List.mem_map]
        exact ⟨m.dst, hstart, rfl⟩
      obtain ⟨c'', hc'', ⟨hq'', hw''⟩, hsub⟩ := hS _ hc _ hmv
      obtain ⟨K', hK', hchk⟩ := ih hrest (K := c''.2.1) (w := true)
        (by
          rcases c'' with ⟨q1, K1, w1⟩
          simp only at hq'' hw'' ⊢
          rw [← hq'', ← hw'']
          exact hc'')
        (by rw [← hxy]; exact Guarded.checks_of_subTests hsub hK)
      refine ⟨K', ?_, by rw [hxy]; exact hchk⟩
      have : (w || (m :: ms).any Move.isWrap) = (true || ms.any Move.isWrap) := by
        simp [List.any_cons, Move.isWrap, hl]
      rw [this]
      exact hK'

theorem mem_exitsOf {S : List Conf} {q : Nat} {K : List Predicate} {w : Bool} (hc : (q, K, w) ∈ S)
    {l : Label} {d : Nat} (ht : (l, d) ∈ N.trans q) (hl : l.rel.isSome = true) :
    ⟨K, l, d, w⟩ ∈ exitsOf N S := by
  unfold exitsOf
  rw [List.mem_flatMap]
  refine ⟨(q, K, w), hc, ?_⟩
  rw [List.mem_filterMap]
  exact ⟨(l, d), ht, by simp [hl]⟩

theorem mem_entries {src s : Nat} {l : Label} (ht : (l, s) ∈ N.trans src) (hl : l.rel.isSome = true) :
    (src, l) ∈ entries N s := by
  unfold entries
  rw [List.mem_flatMap]
  refine ⟨src, List.mem_range.mpr (lt_of_mem_trans ht), ?_⟩
  rw [List.mem_filterMap]
  exact ⟨(l, s), ht, by simp [hl]⟩

/-- A letter of a relation within `rf`, `mo` or `fr` steps by one of them. -/
theorem isEco_sound (hθ : θ.Sound M loc) {l : Label} (h : isEco θ l = true) {a b : E}
    (hab : l.denote M a b) :
    M.rel Builtin.Rel.rf.id a b ∨ M.rel Builtin.Rel.mo.id a b ∨ M.rel Builtin.Rel.fr.id a b := by
  unfold isEco at h
  split at h
  · rename_i r hr
    simp only [Label.denote, hr] at hab
    have hrel := hab.2.1
    simp only [Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · exact .inl (by simpa [Relation.denote] using hθ.relIncl _ _ h a b hrel)
    · exact .inr (.inl (by simpa [Relation.denote] using hθ.relIncl _ _ h a b hrel))
    · exact .inr (.inr (by simpa [Relation.denote] using hθ.relIncl _ _ h a b hrel))
  · simp at h

/-- A letter within a builtin relation, without checks, steps by it. -/
theorem within_sound (hθ : θ.Sound M loc) {l : Label} {r : Builtin.Rel} (h : within θ l r = true)
    {a b : E} (hab : l.denote M a b) : M.rel r.id a b := by
  unfold within at h
  split at h
  · rename_i rel hr
    simp only [Label.denote, hr] at hab
    simp only [Bool.and_eq_true] at h
    simpa [Relation.denote] using hθ.relIncl _ _ h.2 a b hab.2.1
  · simp at h

theorem bare_denote {r : Int} {a b : E} :
    (Exp.bareLabel r).denote M a b ↔ M.rel r a b := by
  simp [Exp.bareLabel, Label.denote, Relation.denote, Checks]

/-- **A skippable visit**: a run that enters the event by `entry`, from
`src`, and leaves it by the exit, which `canSkip` accepts, has a letter of
`N` from `src`, to where the exit leads, that relates the events before and
after the event. -/
theorem canSkip_sound (hθ : θ.Sound M loc) (hpo : ∀ a b c, M.rel Builtin.Rel.po.id a b →
      M.rel Builtin.Rel.po.id b c → M.rel Builtin.Rel.po.id a c)
    (hpl : ∀ a b c, M.rel Builtin.Rel.po_loc.id a b → M.rel Builtin.Rel.po_loc.id b c →
      M.rel Builtin.Rel.po_loc.id a c)
    {src : Nat} {entry : Label} {ex : Exit} (h : canSkip θ N src entry ex = true)
    {a e b : E} (h₁ : entry.denote M a e) (h₂ : ex.label.denote M e b) :
    ex.wraps = false ∧ ∃ l, (l, ex.dest) ∈ N.trans src ∧ l.denote M a b := by
  unfold canSkip at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hw, hpe⟩, hpx⟩, ⟨l, d⟩, ht, hd, hincl⟩ := h
  refine ⟨hw, l, hd ▸ ht, ?_⟩
  apply hθ.labelIncl hincl a b
  split
  · rename_i hloc
    exact bare_denote.mpr (hpl _ _ _ (within_sound hθ hloc.1 h₁) (within_sound hθ hloc.2 h₂))
  · exact bare_denote.mpr (hpo _ _ _ (within_sound hθ hpe h₁) (within_sound hθ hpx h₂))

/-! ## The words -/

theorem mem_words_trans {exits : List Exit} {p : Nat} {l : Label} {q : Nat}
    (hp : p < N.size + 1 + exits.length) :
    (l, q) ∈ (words N exits).trans p ↔
      (p, l, q) ∈ (((List.range N.size).flatMap fun q => (N.trans q).map fun t => (q, t.1, t.2)) ++
        ((List.range exits.length).map fun i =>
          (N.size, (⟨none, Guarded.union exits[i]!.preds addable, []⟩ : Label), N.size + 1 + i)) ++
        ((List.range exits.length).map fun i => (N.size + 1 + i, exits[i]!.label, exits[i]!.dest))) :=
  NFA.mem_trans_ofList hp

/-- The words automaton reads what `N` does from its states. -/
theorem accepts_words (hN : closedStates N = true) {exits : List Exit} :
    ∀ {q w}, N.Accepts q w → (words N exits).Accepts q w := by
  intro q w h
  simp only [closedStates, Bool.and_eq_true, beq_iff_eq] at hN
  induction h with
  | @nil q hq =>
    have hq' : q < N.size := by
      unfold NFA.isAccepting at hq
      rw [← hN.1.1]
      rcases Nat.lt_or_ge q N.accepting.size with hn | hn
      · exact hn
      · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)] at hq
        simp at hq
    apply NFA.Accepts.nil
    rw [words, NFA.isAccepting_ofList (by omega)]
    simp [hq', hq]
  | @cons q l q' w ht _ ih =>
    have hq : q < N.size := lt_of_mem_trans ht
    refine .cons ((mem_words_trans (by omega)).mpr ?_) ih
    apply List.mem_append_left
    apply List.mem_append_left
    rw [List.mem_flatMap]
    exact ⟨q, List.mem_range.mpr hq, List.mem_map.mpr ⟨(l, q'), ht, rfl⟩⟩

/-- **What the words automaton reads**: from an event whose exit's checks
hold, with `addable`, the exit's letter, and then a word `N` accepts from
where it leads. -/
theorem words_denote (hN : closedStates N = true) {exits : List Exit} {ex : Exit}
    (hex : ex ∈ exits) {a b c : E} (hK : Checks M (Guarded.union ex.preds addable) a)
    (hl : ex.label.denote M a b) {w : List Label} (hw : N.Accepts ex.dest w)
    (hr : wordRel (Label.denote M) w b c) :
    (words N exits).denote (Label.denote M) a c := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hex
  have hget : exits[i]! = exits[i] := by simp [hi]
  refine ⟨N.size, by simp [words, NFA.ofList],
    ⟨none, Guarded.union exits[i].preds addable, []⟩ :: exits[i].label :: w, ?_, ?_⟩
  · exact .cons (a := ⟨none, Guarded.union exits[i].preds addable, []⟩) (q' := N.size + 1 + i)
      ((mem_words_trans (exits := exits) (p := N.size) (by omega)).mpr (by
        apply List.mem_append_left
        apply List.mem_append_right
        rw [List.mem_map]
        exact ⟨i, List.mem_range.mpr hi, by rw [hget]⟩))
      (.cons (a := exits[i].label) (q' := exits[i].dest)
        ((mem_words_trans (exits := exits) (p := N.size + 1 + i) (by omega)).mpr (by
          apply List.mem_append_right
          rw [List.mem_map]
          exact ⟨i, List.mem_range.mpr hi, by rw [hget]⟩))
        (accepts_words hN hw))
  · exact ⟨a, ⟨rfl, hK⟩, b, hl, hr⟩

/-! ## The predicates' words -/

/-- An automaton `noPredWords` accepts reads a relation's letter in each
word it accepts: a run from a starting state that ends a word, or at an
accepting state, has a step. -/
theorem noPred_step (hpw : noPredWords N = true) {s a ms f b} (hw : Walk N M s a ms f b)
    (hs : s ∈ N.start) (hf : N.isAccepting f = true) : ∃ m ∈ ms, m.isStep = true := by
  simp only [noPredWords, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
    Bool.or_eq_true, List.contains_iff_mem] at hpw
  obtain ⟨hstart, hR⟩ := hpw
  apply Classical.byContradiction
  intro hno
  simp only [not_exists, not_and, Bool.not_eq_true] at hno
  have : ∀ {q a ms f b}, Walk N M q a ms f b → q ∈ predReach N → (∀ m ∈ ms, m.isStep = false) →
      N.isAccepting f = true → False := by
    intro q a ms f b h
    induction h with
    | nil q a =>
      intro hq _ hf
      rw [(hR q hq).1] at hf
      simp at hf
    | @cons m ms₀ q₀ b₀ hv h' ih =>
      intro hq hns hf
      have hst := hns m (List.mem_cons_self ..)
      unfold Move.Valid at hv
      split at hv
      · rename_i l hl
        have hr : l.rel.isSome = false := by
          unfold Move.isStep at hst
          rw [hl] at hst
          exact hst
        have := (hR m.src hq).2 (l, m.dst) hv.1
        simp only [hr, Bool.false_eq_true, false_or] at this
        exact ih this (fun m' hm' => hns m' (List.mem_cons_of_mem _ hm')) hf
      · rw [(hR m.src hq).1] at hv
        simp at hv
  exact this hw (hstart s hs) hno hf

/-! ## Without `lin` -/

theorem trans_dropLin {p : Nat} :
    (dropLin θ N).trans p = (N.trans p).filter fun t => match t.1.rel with
      | some r => !θ.relIncl r ⟨Builtin.Rel.lin.id, false⟩
      | none => true := by
  simp only [NFA.trans, dropLin, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases N.outs[p]? <;> rfl

/-- **Without `lin`**: where the letters within `lin` relate nothing, an
automaton denotes no more than it does without them. -/
theorem dropLin_sub (hθ : θ.Sound M loc) (hlin : ∀ a b, ¬ M.rel Builtin.Rel.lin.id a b) :
    Rel.Sub (N.denote (Label.denote M)) ((dropLin θ N).denote (Label.denote M)) := by
  rintro a b ⟨q, hq, w, hw, hr⟩
  refine ⟨q, hq, w, ?_, hr⟩
  clear hq
  induction hw generalizing a with
  | nil hq => exact .nil hq
  | @cons q l q' w ht _ ih =>
    obtain ⟨c, hl, hr'⟩ := hr
    refine .cons ?_ (ih (a := c) hr')
    rw [trans_dropLin, List.mem_filter]
    refine ⟨ht, ?_⟩
    cases hrl : l.rel with
    | none => rfl
    | some r =>
      cases hi : θ.relIncl r ⟨Builtin.Rel.lin.id, false⟩
      · simp [hi]
      · simp only [Label.denote, hrl] at hl
        exact absurd (by simpa [Relation.denote] using hθ.relIncl _ _ hi a c hl.2.1) (hlin a c)

theorem lt_of_closedStates (hN : closedStates N = true) {q : Nat} {t : Label × Nat}
    (ht : t ∈ N.trans q) : t.2 < N.size := by
  simp only [closedStates, Bool.and_eq_true, List.all_eq_true, Array.all_eq_true,
    decide_eq_true_eq] at hN
  have hq := lt_of_mem_trans ht
  unfold NFA.trans at ht
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hq] at ht
  exact hN.2 q hq t ht

end Search

/-! ## The visits of the event -/

section Visits

variable {N : NFA Label} {M : Interp E}

/-- The first step of a list of moves that has one. -/
theorem split_first : ∀ {ms : List (Move E)}, (∃ m ∈ ms, m.isStep = true) →
    ∃ C t R, ms = C ++ t :: R ∧ (∀ m ∈ C, m.isStep = false) ∧ t.isStep = true
  | [], ⟨_, hm, _⟩ => by simp at hm
  | m :: ms, h => by
    cases hs : m.isStep
    · obtain ⟨m', hm', hs'⟩ := h
      rcases List.mem_cons.mp hm' with rfl | hm'
      · rw [hs] at hs'
        exact absurd hs' (by simp)
      · obtain ⟨C, t, R, rfl, hC, ht⟩ := split_first ⟨m', hm', hs'⟩
        refine ⟨m :: C, t, R, rfl, fun x hx => ?_, ht⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hs
        · exact hC x hx
    · exact ⟨[], m, ms, rfl, by simp, hs⟩

/-- The last step of a list of moves that has one. -/
theorem split_last : ∀ {ms : List (Move E)}, (∃ m ∈ ms, m.isStep = true) →
    ∃ A t R, ms = A ++ t :: R ∧ (∀ m ∈ R, m.isStep = false) ∧ t.isStep = true
  | [], ⟨_, hm, _⟩ => by simp at hm
  | m :: ms, h => by
    by_cases h' : ∃ m' ∈ ms, m'.isStep = true
    · obtain ⟨A, t, R, rfl, hR, ht⟩ := split_last h'
      exact ⟨m :: A, t, R, rfl, hR, ht⟩
    · have hm : m.isStep = true := by
        obtain ⟨m', hm', hs'⟩ := h
        rcases List.mem_cons.mp hm' with rfl | hm'
        · exact hs'
        · exact absurd ⟨m', hm', hs'⟩ h'
      refine ⟨[], m, ms, rfl, fun x hx => ?_, hm⟩
      cases hxs : x.isStep
      · rfl
      · exact absurd ⟨x, hx, hxs⟩ h'

/-- **The first arrival** at `e` of a run from and to other events is by a
relation's letter, after which the run reads predicates of `e`, and ends
words, until a relation's letter leaves it. -/
theorem first_arrival {e : E} : ∀ {q a ms q' b}, Walk N M q a ms q' b → a ≠ e → b ≠ e →
    (∃ m ∈ ms, m.y = e) →
    ∃ A entry mid t B, ms = A ++ entry :: (mid ++ t :: B) ∧ entry.isStep = true ∧ entry.y = e ∧
      (∀ m ∈ mid, m.isStep = false) ∧ t.isStep = true := by
  intro q a ms q' b h
  induction h with
  | nil => intro _ _ ⟨m, hm, _⟩; simp at hm
  | @cons m ms₀ q₀ b₀ hv h' ih =>
    intro ha hb hex
    by_cases hmy : m.y = e
    · have hstep : m.isStep = true := by
        cases hs : m.isStep
        · exact absurd ((Move.stay hv hs).trans hmy) ha
        · rfl
      have : ∃ m' ∈ ms₀, m'.isStep = true := by
        apply Classical.byContradiction
        intro hno
        simp only [not_exists, not_and, Bool.not_eq_true] at hno
        exact hb ((Walk.stays h' hno).symm.trans hmy)
      obtain ⟨C, t, R, rfl, hC, ht⟩ := split_first this
      exact ⟨[], m, C, t, R, rfl, hstep, hmy, hC, ht⟩
    · obtain ⟨m', hm', hm'y⟩ := hex
      rcases List.mem_cons.mp hm' with rfl | hm'
      · exact absurd hm'y hmy
      · obtain ⟨A, entry, mid, t, B, rfl, h1, h2, h3, h4⟩ := ih hmy hb ⟨m', hm', hm'y⟩
        exact ⟨m :: A, entry, mid, t, B, rfl, h1, h2, h3, h4⟩

variable {θ : Theory} {loc : Rel E}

/-- What the argument takes of the meaning `M` of the letters, of the
automaton `N` of the constraint, of the `exits` the words are built of,
and of the event `e` GenMC adds: the theory is sound, `po` and `po-loc`
are transitive; `N`'s states are those of its arrays, it accepts no word of
predicates alone, and `exits` has each exit the check asks about; `e` has
no step within `rf`, `mo` or `fr` out of it and is `addable`; and the words
relate it to nothing (for coherence, `single`: the words of the exits
within their word relate it to nothing, those of the exits into the next
word do not relate it to itself). -/
structure Visit (θ : Theory) (loc : Rel E) (N : NFA Label) (M : Interp E) (exits : List Exit)
    (single : Bool) (e : E) : Prop where
  sound : θ.Sound M loc
  po : ∀ a b c, M.rel Builtin.Rel.po.id a b → M.rel Builtin.Rel.po.id b c →
    M.rel Builtin.Rel.po.id a c
  poLoc : ∀ a b c, M.rel Builtin.Rel.po_loc.id a b → M.rel Builtin.Rel.po_loc.id b c →
    M.rel Builtin.Rel.po_loc.id a c
  states : closedStates N = true
  noPred : noPredWords N = true
  complete : ∀ s < N.size, ∃ S, closed θ N S = true ∧ (s, [], false) ∈ S ∧
    ∀ ex ∈ toCheck θ N s S, ex ∈ exits
  noEco : ∀ b, ¬ M.rel Builtin.Rel.rf.id e b ∧ ¬ M.rel Builtin.Rel.mo.id e b ∧
    ¬ M.rel Builtin.Rel.fr.id e b
  addable : Checks M addable e
  inWord : ∀ c, ¬ (words N (if single then exits.filter (!·.wraps) else exits)).denote
    (Label.denote M) e c
  atStart : single = true → ¬ (words N (exits.filter (·.wraps))).denote (Label.denote M) e e

/-- **A visit of `e`**: a run that enters `e` by a relation's letter, reads
predicates of `e` and ends words, and leaves `e` by a relation's letter,
leaves it by an exit the check asks about, or by one it can skip after the
letter it entered `e` by. -/
theorem visit {exits : List Exit} {single : Bool} {e : E} (hV : Visit θ loc N M exits single e)
    {entry t : Move E} {seg : List (Move E)} (hen : entry.Valid N M)
    (hes : entry.isStep = true) (hseg : Walk N M entry.dst e seg t.src e)
    (hsegs : ∀ m ∈ seg, m.isStep = false) (htv : t.Valid N M) (hts : t.isStep = true)
    (htx : t.x = e) :
    ∃ le lt K, entry.lab = some le ∧ t.lab = some lt ∧ Checks M (Guarded.union K addable) e ∧
      (Exit.mk K lt t.dst (seg.any Move.isWrap) ∈ exits ∨
        canSkip θ N entry.src le ⟨K, lt, t.dst, seg.any Move.isWrap⟩ = true) := by
  have hθ := hV.sound
  -- the letters of the two steps
  have hlab : ∀ {m : Move E}, m.isStep = true → ∃ l, m.lab = some l ∧ l.rel.isSome = true := by
    intro m hm
    unfold Move.isStep at hm
    split at hm
    · rename_i l hl
      exact ⟨l, hl, hm⟩
    · simp at hm
  obtain ⟨le, hle, hler⟩ := hlab hes
  obtain ⟨lt, hlt, hltr⟩ := hlab hts
  have hen' : (le, entry.dst) ∈ N.trans entry.src ∧ le.denote M entry.x entry.y := by
    unfold Move.Valid at hen
    rw [hle] at hen
    exact hen
  have htv' : (lt, t.dst) ∈ N.trans t.src ∧ lt.denote M t.x t.y := by
    unfold Move.Valid at htv
    rw [hlt] at htv
    exact htv
  -- the configurations of the state `e` is entered at cover the visit
  obtain ⟨S, hS, hS0, hSex⟩ := hV.complete entry.dst (lt_of_closedStates hV.states hen'.1)
  obtain ⟨K, hK, hKe⟩ := cover hθ hS hseg hsegs hS0 (fun _ h => by simp at h)
  simp only [Bool.false_or] at hK
  have hex : Exit.mk K lt t.dst (seg.any Move.isWrap) ∈ exitsOf N S :=
    mem_exitsOf hK htv'.1 hltr
  have hKadd : Checks M (Guarded.union K addable) e := Guarded.checks_union hKe hV.addable
  refine ⟨le, lt, K, hle, hlt, hKadd, ?_⟩
  -- not an `eco` step, which `e` has none of, nor one `addable` rules out
  have heco : isEco θ lt = false := by
    cases h : isEco θ lt
    · rfl
    · have := isEco_sound hθ h (htx ▸ htv'.2)
      obtain ⟨h₁, h₂, h₃⟩ := hV.noEco t.y
      rcases this with h | h | h
      · exact absurd h h₁
      · exact absurd h h₂
      · exact absurd h h₃
  have hunsat := unsat_false hθ hKadd
  by_cases hall : (entries N entry.dst).all fun e => canSkip θ N e.1 e.2 ⟨K, lt, t.dst, seg.any Move.isWrap⟩
  · right
    simp only [List.all_eq_true] at hall
    exact hall _ (mem_entries hen'.1 hler)
  · left
    apply hSex
    unfold toCheck
    rw [List.mem_filter]
    refine ⟨hex, ?_⟩
    simp only [heco, hunsat, Bool.not_false, Bool.true_and]
    simpa using hall

/-- **The shortening**: a closed run of `N` that visits `e` has a shorter
one, for what `Visit` assumes rules out the exits the check asks about. -/
theorem shorten {exits : List Exit} {single : Bool} {e : E} (hV : Visit θ loc N M exits single e)
    {s a ms f} (hs : s ∈ N.start) (hf : N.isAccepting f = true) (hw : Walk N M s a ms f a)
    (hsw : single = true → ∀ m ∈ ms, m.isWrap = false) (hv : a = e ∨ ∃ m ∈ ms, m.y = e) :
    ∃ s' a' ms' f', s' ∈ N.start ∧ N.isAccepting f' = true ∧ Walk N M s' a' ms' f' a' ∧
      (single = true → ∀ m ∈ ms', m.isWrap = false) ∧ ms'.length < ms.length := by
  have hθ := hV.sound
  have hstep := noPred_step hV.noPred hw hs hf
  -- the words of an exit the check asks about relate `e` to something
  have hwords : ∀ {ex : Exit}, ex ∈ exits → Checks M (Guarded.union ex.preds addable) e →
      ∀ {b}, ex.label.denote M e b → ∀ {R q c}, Walk N M ex.dest b R q c →
        N.isAccepting q = true → (single = true → ∀ m ∈ R, m.isWrap = false) →
        (single = true → ex.wraps = true → c = e) → False := by
    intro ex hex hK b hl R q c hR hq hRw hc
    cases hsingle : single
    · obtain ⟨w, d, hw', hr⟩ := Walk.rest hR hq
      apply hV.inWord d
      simp only [hsingle, Bool.false_eq_true, ite_false]
      exact words_denote hV.states hex hK hl hw' hr
    · obtain ⟨w, hw', hr⟩ := Walk.toAccepts hR hq (hRw hsingle)
      cases hwr : ex.wraps
      · apply hV.inWord c
        simp only [hsingle, ite_true]
        have hmem : ex ∈ exits.filter (!·.wraps) :=
          List.mem_filter.mpr ⟨hex, by show (!ex.wraps) = true; rw [hwr]; rfl⟩
        exact words_denote hV.states hmem hK hl hw' hr
      · apply hV.atStart hsingle
        have := words_denote hV.states (List.mem_filter.mpr ⟨hex, hwr⟩) hK hl hw' hr
        rwa [hc hsingle hwr] at this
  rcases Classical.em (a = e) with ha | ha
  · -- the visit at the end of the run's last word: its exit begins the next
    obtain ⟨A, entry, mid, hms₁, hmid, hent⟩ := split_last hstep
    obtain ⟨C, t, R, hms₂, hC, htst⟩ := split_first hstep
    rw [hms₁] at hw
    obtain ⟨q₁, b₁, -, hw₁⟩ := Walk.split hw
    obtain ⟨-, -, hev, hwmid⟩ := Walk.cons_inv hw₁
    have hey : entry.y = a := Walk.stays hwmid hmid
    rw [← hms₁, hms₂] at hw
    obtain ⟨q₂, b₂, hwC, hw₂⟩ := Walk.split hw
    have hb₂ : a = b₂ := Walk.stays hwC hC
    obtain ⟨hq₂, htx, htv, hwR⟩ := Walk.cons_inv hw₂
    let wrap : Move E := ⟨f, none, s, a, a⟩
    have hseg : Walk N M entry.dst e (mid ++ wrap :: C) t.src e := by
      rw [← ha, ← hey]
      refine hwmid.append (Walk.cons (m := wrap) ⟨hf, hs, rfl⟩ ?_)
      rw [hq₂] at hwC
      rw [hey, hb₂]
      rw [← hb₂] at hwC ⊢
      exact hwC
    have hsegs : ∀ m ∈ mid ++ wrap :: C, m.isStep = false := by
      intro m hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hmid m hm
      · rcases List.mem_cons.mp hm with rfl | hm
        · rfl
        · exact hC m hm
    have hwrap : (mid ++ wrap :: C).any Move.isWrap = true := by
      simp only [List.any_append, List.any_cons, Bool.or_eq_true]
      exact .inr (.inl rfl)
    obtain ⟨le, lt, K, hle, hlt, hK, hor⟩ :=
      visit hV hev hent hseg hsegs htv htst (htx.symm.trans (hb₂.symm.trans ha))
    rw [hwrap] at hor
    rcases hor with hex | hskip
    · exfalso
      have htv' : lt.denote M e t.y := by
        unfold Move.Valid at htv
        rw [hlt] at htv
        rw [← ha, hb₂, htx]
        exact htv.2
      refine hwords hex hK htv' hwR hf ?_ (fun _ _ => ha)
      intro hsingle m hm
      exact hsw hsingle m (by rw [hms₂]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hm))
    · exfalso
      simp [canSkip] at hskip
  · -- the first arrival at `e`
    have hv' : ∃ m ∈ ms, m.y = e := hv.resolve_left ha
    obtain ⟨A, entry, mid, t, B, hms, hent, hey, hmid, htst⟩ := first_arrival hw ha ha hv'
    rw [hms] at hw
    obtain ⟨q₁, b₁, hwA, hw₁⟩ := Walk.split hw
    obtain ⟨hq₁, hb₁, hev, hw₂⟩ := Walk.cons_inv hw₁
    obtain ⟨q₃, b₃, hwmid, hw₃⟩ := Walk.split hw₂
    have hb₃ : entry.y = b₃ := Walk.stays hwmid hmid
    obtain ⟨hq₃, htx, htv, hwB⟩ := Walk.cons_inv hw₃
    have hseg : Walk N M entry.dst e mid t.src e := by
      rw [← hey, ← hq₃]
      rw [← hb₃] at hwmid
      exact hwmid
    have htxe : t.x = e := by rw [← htx, ← hb₃, hey]
    obtain ⟨le, lt, K, hle, hlt, hK, hor⟩ := visit hV hev hent hseg hmid htv htst htxe
    have hlt' : lt.denote M e t.y := by
      unfold Move.Valid at htv
      rw [hlt] at htv
      rw [← htxe]
      exact htv.2
    have hBw : single = true → ∀ m ∈ B, m.isWrap = false := by
      intro hsingle m hm
      exact hsw hsingle m (by
        rw [hms]
        exact List.mem_append_right _ (List.mem_cons_of_mem _
          (List.mem_append_right _ (List.mem_cons_of_mem _ hm))))
    rcases hor with hex | hskip
    · exfalso
      refine hwords hex hK hlt' hwB hf hBw ?_
      intro hsingle hwr
      exfalso
      have : mid.any Move.isWrap = false := by
        rw [Bool.eq_false_iff]
        intro h
        simp only [List.any_eq_true] at h
        obtain ⟨m, hm, hmw⟩ := h
        have := hsw hsingle m (by
          rw [hms]
          exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ hm)))
        rw [hmw] at this
        exact absurd this (by simp)
      simp only at hwr
      rw [this] at hwr
      exact absurd hwr (by simp)
    · -- skip `e`: one letter of `N` from before the entry to after the exit
      have hle' : le.denote M entry.x e := by
        unfold Move.Valid at hev
        rw [hle] at hev
        rw [← hey]
        exact hev.2
      obtain ⟨-, l', hl', hl'den⟩ := canSkip_sound hθ hV.po hV.poLoc hskip hle' hlt'
      let m' : Move E := ⟨entry.src, some l', t.dst, entry.x, t.y⟩
      refine ⟨s, a, A ++ m' :: B, f, hs, hf, ?_, ?_, ?_⟩
      · rw [hq₁, hb₁] at hwA
        exact hwA.append (Walk.cons (m := m') ⟨hl', hl'den⟩ hwB)
      · intro hsingle m hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hsw hsingle m (by rw [hms]; exact List.mem_append_left _ hm)
        · rcases List.mem_cons.mp hm with rfl | hm
          · rfl
          · exact hBw hsingle m hm
      · rw [hms]
        simp only [List.length_append, List.length_cons]
        omega

/-- **A shortest cycle avoids `e`**: a closed run of `N` has one that does
not visit `e`. -/
theorem avoid {exits : List Exit} {single : Bool} {e : E} (hV : Visit θ loc N M exits single e) :
    ∀ (n : Nat) {s a ms f}, ms.length ≤ n → s ∈ N.start → N.isAccepting f = true →
      Walk N M s a ms f a → (single = true → ∀ m ∈ ms, m.isWrap = false) →
      ∃ s' a' ms' f', s' ∈ N.start ∧ N.isAccepting f' = true ∧ Walk N M s' a' ms' f' a' ∧
        (single = true → ∀ m ∈ ms', m.isWrap = false) ∧ a' ≠ e ∧ ∀ m ∈ ms', m.y ≠ e
  | n, s, a, ms, f, hn, hs, hf, hw, hsw => by
    by_cases hv : a = e ∨ ∃ m ∈ ms, m.y = e
    · obtain ⟨s', a', ms', f', hs', hf', hw', hsw', hlt⟩ := shorten hV hs hf hw hsw hv
      match n with
      | 0 => omega
      | n + 1 => exact avoid hV n (by omega) hs' hf' hw' hsw'
    · simp only [not_or, not_exists, not_and] at hv
      exact ⟨s, a, ms, f, hs, hf, hw, hsw, hv.1, fun m hm => hv.2 m hm⟩

/-- **The cycles of the constraint's automaton**: under what `Visit`
assumes, if `N` has a cycle (of one word, for `single`), it has one that
does not visit `e`: one of the events other than `e`. -/
theorem cycles_sound {exits : List Exit} {single : Bool} {e : E}
    (hV : Visit θ loc N M exits single e) {a : E}
    (hc : if single then N.denote (Label.denote M) a a
      else Rel.Plus (N.denote (Label.denote M)) a a) :
    ∃ a' : {a : E // a ≠ e}, if single then N.denote (Label.denote (M.without e)) a' a'
      else Rel.Plus (N.denote (Label.denote (M.without e))) a' a' := by
  cases hsingle : single
  · simp only [hsingle, Bool.false_eq_true, ite_false] at hc ⊢
    obtain ⟨s, hs, ms, f, hw, hf⟩ := Walk.ofPlus hc
    obtain ⟨s', a', ms', f', hs', hf', hw', -, ha', hy⟩ :=
      avoid hV ms.length (Nat.le_refl _) hs hf hw (by simp [hsingle])
    obtain ⟨hb, ms'', hw'', -⟩ := Walk.lift hw' ha' hy
    exact ⟨⟨a', ha'⟩, Walk.toPlus hw'' hs' hf'⟩
  · simp only [hsingle, ite_true] at hc ⊢
    obtain ⟨s, hs, ms, f, hw, hf, hnw⟩ := Walk.ofDenote hc
    obtain ⟨s', a', ms', f', hs', hf', hw', hnw', ha', hy⟩ :=
      avoid hV ms.length (Nat.le_refl _) hs hf hw (fun _ => hnw)
    obtain ⟨hb, ms'', hw'', hmap⟩ := Walk.lift hw' ha' hy
    obtain ⟨w, hw₁, hr⟩ := Walk.toAccepts hw'' hf' (by
      intro m hm
      have : m.isWrap ∈ ms''.map Move.isWrap := List.mem_map_of_mem hm
      rw [hmap] at this
      obtain ⟨m₀, hm₀, heq⟩ := List.mem_map.mp this
      rw [← heq]
      exact hnw' hsingle m₀ hm₀)
    exact ⟨⟨a', ha'⟩, s', hs', w, hw₁, hr⟩

end Visits

/-! ## The check -/

section Check

variable {F : Type} {θ : Theory} {loc : Rel F} {M : Interp F}

theorem mapM_some {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → ∀ a ∈ l, ∃ b, f a = some b ∧ b ∈ r
  | [], _, _, _, ha => by simp at ha
  | a :: l, r, h, a', ha' => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, r', hr', rfl⟩ := h
    rcases List.mem_cons.mp ha' with rfl | ha'
    · exact ⟨b, hb, List.mem_cons_self ..⟩
    · obtain ⟨b', hb', hmem⟩ := mapM_some hr' a' ha'
      exact ⟨b', hb', List.mem_cons_of_mem _ hmem⟩

/-- The exits Lean computes have each exit the check asks about. -/
theorem allExits_complete {N : NFA Label} {exits : List Exit} (h : allExits θ N = some exits) :
    ∀ s < N.size, ∃ S, closed θ N S = true ∧ (s, [], false) ∈ S ∧
      ∀ ex ∈ toCheck θ N s S, ex ∈ exits := by
  intro s hs
  unfold allExits at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨r, hr, rfl⟩ := h
  obtain ⟨b, hb, hmem⟩ := mapM_some hr s (List.mem_range.mpr hs)
  unfold stateExits at hb
  dsimp only at hb
  split at hb
  · rename_i hok
    simp only [Bool.and_eq_true, List.contains_iff_mem] at hok
    simp only [Option.some.injEq] at hb
    subst hb
    exact ⟨_, hok.1, hok.2, fun ex hex => List.mem_flatten.mpr ⟨_, hmem, hex⟩⟩
  · simp at hb

/-- The cycles of the constraint, without `lin`, are those of its automaton. -/
theorem cycle_of_check {x : Extensibility} (hθ : θ.Sound M loc)
    (hlin : ∀ a b, ¬ M.rel Builtin.Rel.lin.id a b) (hwf : x.re.wellFormed = true)
    (hT : Guarded.prove θ (dropLin θ (Thompson.nfa x.re)) x.cycles false = true) {a b : F}
    (h : x.re.denote M a b) : x.cycles.denote (Label.denote M) a b :=
  Guarded.prove_sound hθ hT a b (dropLin_sub hθ hlin a b (Thompson.nfa_complete M x.re hwf h))

/-- **The extensibility check is sound**, for one meaning of the letters:
if Lean accepts the evidence of an extensibility check (`checkInclusions`
and `checkCycles`), then wherever the module's theory is sound, `po` and
`po-loc` are transitive, `any` relates every two events, the module's
assumptions hold and `lin` relates nothing, a cycle of the constraint (of
one word, for coherence) is a cycle of its automaton on the events other
than `e`, if `e` has no step within `rf`, `mo` or `fr` out of it, is
`addable`, and has no `pporf` successor, and for coherence `po+ ; (rf | mo
| fr)+` does not relate it to itself. -/
theorem check_sound {x : Extensibility} (hinc : checkInclusions x = .ok ())
    (hcyc : checkCycles x = .ok ()) (hθ : (Theory.ofDecls x.module.decls).Sound M loc)
    (hF : Facts M)
    (hpl : ∀ a b c, M.rel Builtin.Rel.po_loc.id a b → M.rel Builtin.Rel.po_loc.id b c →
      M.rel Builtin.Rel.po_loc.id a c)
    (hh : Whole.HypsHold M x.module.assumptions) (hlin : ∀ a b, ¬ M.rel Builtin.Rel.lin.id a b)
    {e : F} (heco : ∀ b, ¬ M.rel Builtin.Rel.rf.id e b ∧ ¬ M.rel Builtin.Rel.mo.id e b ∧
      ¬ M.rel Builtin.Rel.fr.id e b)
    (hadd : Checks M addable e) (hpporf : ∀ b, ¬ x.pporf.denote M e b)
    (hback : x.single = true → ¬ backToEvent.denote M e e) {a : F}
    (hc : if x.single then x.re.denote M a a else Rel.Plus (x.re.denote M) a a) :
    ∃ a' : {a : F // a ≠ e}, if x.single then x.cycles.denote (Label.denote (M.without e)) a' a'
      else Rel.Plus (x.cycles.denote (Label.denote (M.without e))) a' a' := by
  have hwords := checkInclusions_sound hinc hθ hF hh
  have hshape : shapeOk x.single x.words = true := by
    unfold checkInclusions at hinc
    split at hinc
    · simp at hinc
    · split at hinc
      · simp at hinc
      · rename_i hs
        split at hinc
        · simp at hinc
        · rename_i hs'
          simpa using hs'
  unfold checkCycles at hcyc
  simp only at hcyc
  split at hcyc
  · simp at hcyc
  rename_i hwf
  split at hcyc
  · simp at hcyc
  rename_i hst
  split at hcyc
  · simp at hcyc
  split at hcyc
  · simp at hcyc
  rename_i hT
  split at hcyc
  · simp at hcyc
  split at hcyc
  · simp at hcyc
  rename_i hpw
  split at hcyc
  · simp at hcyc
  rename_i exits hexits
  split at hcyc
  · rename_i hok
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hwf hst hT hpw
    -- the words of the pporf ; any* inclusions relate `e` to nothing
    have hnone : ∀ {X : NFA Label} (w : WordsInclusion), w ∈ x.words → w.backToEvent = false →
        Guarded.prove (Theory.ofDecls x.module.decls) X w.words.nfa false (some w.words.origins) = true →
        ∀ c, ¬ X.denote (Label.denote M) e c := by
      intro X w hw hb hX c hXc
      have := hwords w hw e c (Guarded.prove_sound hθ hX e c hXc)
      rw [hb] at this
      simp only [rhsOf, Bool.false_eq_true, ite_false, Exp.denote, Rel.comp] at this
      obtain ⟨d, hd, -⟩ := this
      exact hpporf d hd
    have hcyc' : if x.single then x.cycles.denote (Label.denote M) a a
        else Rel.Plus (x.cycles.denote (Label.denote M)) a a := by
      split
      · rename_i hs
        simp only [hs, ite_true] at hc
        exact cycle_of_check hθ hlin hwf hT hc
      · rename_i hs
        simp only [hs, Bool.false_eq_true, ite_false] at hc
        obtain ⟨z, h₁, h₂⟩ := hc
        exact ⟨z, cycle_of_check hθ hlin hwf hT h₁,
          Rel.Star.mono (fun _ _ => cycle_of_check hθ hlin hwf hT) _ _ h₂⟩
    refine cycles_sound (exits := exits) ⟨hθ, hF.po_trans, hpl, hst, hpw,
      allExits_complete hexits, heco, hadd, ?_, ?_⟩ hcyc'
    · -- the words of the exits within their word, or of all exits
      unfold wordsOk at hok
      split at hok
      · rename_i w hws
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
        simp only [hok.1, Bool.false_eq_true, ite_false]
        have hb : w.backToEvent = false := by
          rw [hws] at hshape
          unfold shapeOk at hshape
          split at hshape <;> simp_all
        exact hnone w (by rw [hws]; exact List.mem_singleton_self _) hb hok.2
      · rename_i w₁ w₂ hws
        simp only [Bool.and_eq_true] at hok
        simp only [hok.1.1, ite_true]
        have hb : w₁.backToEvent = false := by
          rw [hws] at hshape
          unfold shapeOk at hshape
          split at hshape <;> simp_all
        exact hnone w₁ (by rw [hws]; exact List.mem_cons_self ..) hb hok.1.2
      · simp at hok
    · -- the words of the exits into the next word do not relate `e` to itself
      intro hsingle hXe
      unfold wordsOk at hok
      split at hok
      · simp [hsingle] at hok
      · rename_i w₁ w₂ hws
        simp only [Bool.and_eq_true] at hok
        have hb : w₂.backToEvent = true := by
          rw [hws] at hshape
          unfold shapeOk at hshape
          split at hshape <;> simp_all
        have := hwords w₂ (by rw [hws]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
          e e (Guarded.prove_sound hθ hok.2 e e hXe)
        rw [hb] at this
        simp only [rhsOf, ite_true, Exp.denote, Rel.union, Rel.comp] at this
        rcases this with ⟨d, hd, -⟩ | h
        · exact hpporf d hd
        · exact hback hsingle h
      · simp at hok
  · simp at hcyc

/-- What an accepted check says of the constraint's automaton beyond the
cycles: its letters are stable, and it denotes no more than the
constraint. -/
theorem checkCycles_automaton {x : Extensibility} (h : checkCycles x = .ok ()) :
    x.cycles.outs.all (·.all fun t => stableLabel t.1) = true ∧
      Guarded.prove (Theory.ofDecls x.module.decls) x.cycles (Thompson.nfa x.re) false = true := by
  unfold checkCycles at h
  simp only at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i hst
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i hNT
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hst hNT
  exact ⟨hst, hNT⟩

end Check

end Extensible

end KaterCert
