import KaterCert.Saturation
import KaterCert.Path
import KaterCert.Soundness

/-!
# Soundness of the check of a saturation's evidence

If `Evidence.check` accepts the evidence of a saturation from `N` to `M`,
its hypothesis holds and its letter inclusions hold, then `M` denotes no
more than `N`, with letters read as the oracle reads them.

The proof gives each role the relation it bounds (`bound`), shows that
lifting a role only widens its bound, that each step the check allows keeps
the bounds, that the starting states' bounds hold the identity and the
accepting states' are within what `N` denotes; then every word of `M` to a
state relates no more than the state's role bounds, by induction over the
word (`NFA.past_bound`).
-/

namespace KaterCert

universe u

variable {E : Type u}

theorem checks_append {Mi : Interp E} {ps qs : List Predicate} {x : E}
    (hp : Checks Mi ps x) (hq : Checks Mi qs x) : Checks Mi (ps ++ qs) x := by
  intro p hmem
  rcases List.mem_append.mp hmem with h | h
  · exact hp p h
  · exact hq p h

theorem knows_checks {Mi : Interp E} {known ps : List Predicate} (h : knows known ps = true)
    {x : E} (hx : Checks Mi known x) : Checks Mi ps x := by
  intro p hp
  simp only [knows, List.all_eq_true] at h
  exact hx p (List.contains_iff_mem.mp (h p hp))

/-- A predicate letter relates an event to itself, if its checks hold. -/
theorem denote_pred {Mi : Interp E} {ps : List Predicate} {x : E} (h : Checks Mi ps x) :
    Label.denote Mi ⟨none, ps, []⟩ x x :=
  ⟨rfl, h⟩

/-- If `path` reads `word`, the word relates no more than the path, from an
event where what is `known` holds. -/
theorem reads_sound {Mi : Interp E} {incl : Label → Label → Bool}
    (hincl : ∀ a b, incl a b = true → Rel.Sub (a.denote Mi) (b.denote Mi)) :
    ∀ known w path, reads incl known w path = true →
      ∀ x y, Checks Mi known x → wordRel (Label.denote Mi) w x y →
        wordRel (Label.denote Mi) (path.map Step.letter) x y := by
  intro known w path
  induction known, w, path using reads.induct with
  | case1 known a w path ha ih =>
    intro h x y hx hw
    rw [reads.eq_def] at h
    simp only [ite_eq_left ha] at h
    obtain ⟨z, haz, hwz⟩ := hw
    have hnone : a.rel = none := Option.isNone_iff_eq_none.mp ha
    simp only [Label.denote, hnone] at haz
    obtain ⟨rfl, hpre⟩ := haz
    exact ih h x y (checks_append hx hpre) hwz
  | case2 known a w ha s path' hs ih =>
    intro h x y hx hw
    rw [reads.eq_1, ite_eq_right ha, ite_eq_left hs] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hknows, hinc⟩, hrest⟩ := h
    refine ⟨x, hincl _ _ hinc x x (denote_pred (knows_checks hknows hx)), ?_⟩
    exact ih hrest x y hx hw
  | case3 known a w ha s path' hs ih =>
    intro h x y hx hw
    rw [reads.eq_1, ite_eq_right ha, ite_eq_right hs] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨_, _⟩, hknows⟩, hinc⟩, hrest⟩ := h
    obtain ⟨z, haz, hwz⟩ := hw
    obtain ⟨r, hr⟩ : ∃ r, a.rel = some r := by
      cases hrel : a.rel with
      | none => exact absurd (by simp [hrel]) ha
      | some r => exact ⟨r, rfl⟩
    simp only [Label.denote, hr] at haz
    obtain ⟨_, hrxz, _⟩ := haz
    have hlet : Label.denote Mi ⟨a.rel, s.known, []⟩ x z := by
      simp only [Label.denote, hr]
      exact ⟨knows_checks hknows hx, hrxz, fun _ h => absurd h List.not_mem_nil⟩
    refine ⟨z, hincl _ _ hinc x z hlet, ?_⟩
    exact ih hrest z y (fun _ h => absurd h List.not_mem_nil) hwz
  | case4 known a w ha =>
    intro h
    rw [reads.eq_2, ite_eq_right ha] at h
    exact absurd h (by simp)
  | case5 known s path' ih =>
    intro h x y hx hw
    rw [reads.eq_3] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨_, hknows⟩, hinc⟩, hrest⟩ := h
    refine ⟨x, hincl _ _ hinc x x (denote_pred (knows_checks hknows hx)), ?_⟩
    exact ih hrest x y hx hw
  | case6 known =>
    intro _ x y _ hw
    exact hw

namespace NFA

theorem lt_of_isAccepting {L : Type} {A : NFA L} {q : Nat} (h : A.isAccepting q = true) :
    q < A.accepting.size := by
  unfold isAccepting Array.getD at h
  split at h
  · assumption
  · exact absurd h (by simp)

theorem lt_of_mem_trans {L : Type} {A : NFA L} {q : Nat} {t : L × Nat} (h : t ∈ A.trans q) :
    q < A.size := by
  unfold trans Array.getD at h
  split at h
  · assumption
  · exact absurd h List.not_mem_nil

theorem hasStep_mem {A : NFA Label} {q : Nat} {a : Label} {q' : Nat} (h : A.hasStep q a q' = true) :
    (a, q') ∈ A.trans q := by
  simp only [hasStep, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨b, d⟩, hmem, rfl, rfl⟩ := h
  exact hmem

/-- Walking a path leads from a state's past into its end's. -/
theorem walk_sound {Mi : Interp E} {A : NFA Label} :
    ∀ {q q' : Nat} {path : List Step}, A.walk q path = some q' →
      Rel.Sub (Rel.comp (A.past (Label.denote Mi) q)
        (wordRel (Label.denote Mi) (path.map Step.letter))) (A.past (Label.denote Mi) q')
  | q, q', [], h => by
    simp only [walk, Option.some.injEq] at h
    subst h
    intro x z ⟨y, hxy, hyz⟩
    cases hyz
    exact hxy
  | q, q', s :: path, h => by
    simp only [walk] at h
    split at h
    · rename_i hstep
      intro x z ⟨y, hxy, y', hs, hrest⟩
      exact walk_sound h x z ⟨y', A.past_step (hasStep_mem hstep) x y' ⟨y, hxy, hs⟩, hrest⟩
    · exact absurd h (by simp)

end NFA

namespace Evidence

variable {ev : Evidence} {N M : NFA Label} {Mi : Interp E}

/-- Where the words reaching the start of copy `g` come from: those reaching
its `src`, or, for an empty hypothesis, anywhere. -/
def anchor (ev : Evidence) (N : NFA Label) (Mi : Interp E) (g : Nat) : Rel E :=
  if ev.hypothesis = .empty then fun _ _ => True else N.past (Label.denote Mi) (ev.copy g).src

/-- What a role bounds: the most the words reaching a state with that role
relate. -/
def bound (ev : Evidence) (N : NFA Label) (Mi : Interp E) : Role → Rel E
  | .state n => N.past (Label.denote Mi) n
  | .after n => fun x z => ∃ p, (ev.letter, n) ∈ N.trans p ∧
      Rel.comp (N.past (Label.denote Mi) p) (ev.letter.denote Mi) x z
  | .copy j g => Rel.comp (ev.anchor N Mi g) (ev.automaton.past (Label.denote Mi) j)

/-- What the hypothesis says, with letters read through `Mi`. -/
def Holds (ev : Evidence) (Mi : Interp E) : Prop :=
  match ev.hypothesis with
  | .transitive =>
    Rel.Sub (Rel.comp (ev.letter.denote Mi) (ev.letter.denote Mi)) (ev.letter.denote Mi)
  | .within =>
    Rel.Sub (ev.automaton.denote (Label.denote Mi)) (wordRel (Label.denote Mi) ev.word)
  | .empty => ∀ x y, ¬ ev.automaton.denote (Label.denote Mi) x y

/-- That the evidence's letter inclusions hold, with letters read through
`Mi`. -/
def InclusionsHold (ev : Evidence) (Mi : Interp E) : Prop :=
  ∀ a b, (a, b) ∈ ev.inclusions → Rel.Sub (a.denote Mi) (b.denote Mi)

theorem includes_sound (hinc : ev.InclusionsHold Mi) {a b : Label}
    (h : ev.includes a b = true) : Rel.Sub (a.denote Mi) (b.denote Mi) := by
  simp only [includes, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · exact Rel.Sub.refl _
  · exact hinc a b (List.contains_iff_mem.mp h)

/-- Leaving copy `g` from an accepting state of the hypothesis' automaton
lands within what reaches the copy's end. -/
theorem exit_sound (hw : ev.hypothesis = .within) (hyp : ev.Holds Mi) (hinc : ev.InclusionsHold Mi)
    {j g : Nat} (hj : ev.automaton.isAccepting j = true) (hg : ev.exits N g = true) :
    Rel.Sub (ev.bound N Mi (.copy j g)) (N.past (Label.denote Mi) (ev.copy g).dst) := by
  simp only [exits, Bool.and_eq_true, beq_iff_eq] at hg
  obtain ⟨hwalk, hreads⟩ := hg
  have hhyp : Rel.Sub (ev.automaton.denote (Label.denote Mi)) (wordRel (Label.denote Mi) ev.word) := by
    simp only [Holds, hw] at hyp
    exact hyp
  intro x z ⟨y, hxy, hyz⟩
  simp only [anchor, hw, reduceCtorEq, ite_false] at hxy
  have hword := hhyp y z (ev.automaton.past_accepting hj y z hyz)
  have hpath := reads_sound (fun a b h => includes_sound hinc h) [] ev.word (ev.copy g).path
    hreads y z (fun _ h => absurd h List.not_mem_nil) hword
  exact NFA.walk_sound hwalk x z ⟨y, hxy, hpath⟩

theorem liftsState_sound {n : Nat} {s : Role} (hs : s ∈ ev.liftsState n) :
    Rel.Sub (N.past (Label.denote Mi) n) (ev.bound N Mi s) := by
  simp only [liftsState] at hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact Rel.Sub.refl _
  · split at hs
    · rename_i hw
      simp only [List.mem_flatMap, List.mem_range] at hs
      obtain ⟨g, _, hg⟩ := hs
      split at hg
      · rename_i hsrc
        simp only [List.mem_map] at hg
        obtain ⟨i, hi, rfl⟩ := hg
        have hsrc : (ev.copy g).src = n := beq_iff_eq.mp hsrc
        intro x y hxy
        simp only [bound, anchor, hw, reduceCtorEq, ite_false, hsrc]
        exact ⟨y, hxy, ev.automaton.past_start hi y y rfl⟩
      · exact absurd hg List.not_mem_nil
    · exact absurd hs List.not_mem_nil

/-- A role's bound is within the bound of each role it lifts to. -/
theorem lifts_sound (hyp : ev.Holds Mi) (hinc : ev.InclusionsHold Mi) {r s : Role}
    (hs : s ∈ ev.lifts N r) : Rel.Sub (ev.bound N Mi r) (ev.bound N Mi s) := by
  cases r with
  | state n => exact liftsState_sound hs
  | after n =>
    rcases List.mem_cons.mp hs with rfl | hs
    · exact Rel.Sub.refl _
    · refine Rel.Sub.trans ?_ (liftsState_sound hs)
      intro x z ⟨p, hp, hpz⟩
      exact N.past_step hp x z hpz
  | copy j g =>
    simp only [lifts] at hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact Rel.Sub.refl _
    · split at hs
      · rename_i hcond
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        obtain ⟨⟨hw, hj⟩, hg⟩ := hcond
        exact Rel.Sub.trans (exit_sound hw hyp hinc hj hg) (liftsState_sound hs)
      · exact absurd hs List.not_mem_nil

/-- What an empty hypothesis' accepting states bound is nothing. -/
theorem bound_empty_accepting (he : ev.hypothesis = .empty) (hyp : ev.Holds Mi) {j g : Nat}
    (hj : ev.automaton.isAccepting j = true) {x z : E} (h : ev.bound N Mi (.copy j g) x z) :
    False := by
  obtain ⟨y, _, hyz⟩ := h
  simp only [Holds, he] at hyp
  exact hyp y z (ev.automaton.past_accepting hj y z hyz)

/-- Each step the check allows keeps the bounds. -/
theorem steps_sound (hyp : ev.Holds Mi) {s t : Role} {l : Label}
    (h : ev.steps N s l t = true) :
    Rel.Sub (Rel.comp (ev.bound N Mi s) (l.denote Mi)) (ev.bound N Mi t) := by
  unfold steps at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hp, rfl⟩ := h
    intro x z ⟨y, hxy, hyz⟩
    have hid := Label.denote_sub_id Mi (Option.isNone_iff_eq_none.mp hp) y z hyz
    cases hid
    exact hxy
  · cases s with
    | state n =>
      cases t with
      | state n' =>
        exact N.past_step (NFA.hasStep_mem h)
      | after n' =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨_, rfl⟩, hstep⟩ := h
        intro x z hxz
        exact ⟨n, NFA.hasStep_mem hstep, hxz⟩
      | copy _ _ => exact absurd h (by simp)
    | after n =>
      cases t with
      | after n' =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨rfl, ht⟩, rfl⟩ := h
        have htrans : Rel.Sub (Rel.comp (ev.letter.denote Mi) (ev.letter.denote Mi))
            (ev.letter.denote Mi) := by
          simp only [Holds, ht] at hyp
          exact hyp
        intro x z ⟨y, ⟨p, hp, w, hxw, hwy⟩, hyz⟩
        exact ⟨p, hp, w, hxw, htrans w z ⟨y, hwy, hyz⟩⟩
      | state _ => exact absurd h (by simp)
      | copy _ _ => exact absurd h (by simp)
    | copy j g =>
      rcases Bool.or_eq_true_iff.mp h with h | h
      · simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨he, hj⟩ := h
        intro x z ⟨y, hxy, _⟩
        exact absurd (bound_empty_accepting he hyp hj hxy) id
      · cases t with
        | copy j' g' =>
          rcases Bool.or_eq_true_iff.mp h with h | h
          · simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at h
            obtain ⟨⟨he, _⟩, hj'⟩ := h
            intro x z _
            simp only [bound, anchor, he, ite_true]
            exact ⟨z, trivial, ev.automaton.past_start hj' z z rfl⟩
          · simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
            obtain ⟨hg, hstep⟩ := h
            have hanchor : ev.anchor N Mi g = ev.anchor N Mi g' := by
              rcases hg with he | rfl
              · simp only [anchor, he, ite_true]
              · rfl
            intro x z ⟨y, ⟨w, hxw, hwy⟩, hyz⟩
            simp only [bound]
            exact ⟨w, hanchor ▸ hxw, ev.automaton.past_step (NFA.hasStep_mem hstep) w z ⟨y, hwy, hyz⟩⟩
        | state _ => exact absurd h (by simp)
        | after _ => exact absurd h (by simp)

/-- The role of a starting state of a copy bounds the identity, if the
identity reaches the copy's start, or the copy starts anywhere. -/
theorem startable_copy {j g : Nat} (hj : j ∈ ev.automaton.start)
    (hsrc : ev.hypothesis = .empty ∨ Rel.Sub Rel.id (N.past (Label.denote Mi) (ev.copy g).src)) :
    Rel.Sub Rel.id (ev.bound N Mi (.copy j g)) := by
  intro x y hxy
  cases hxy
  refine ⟨x, ?_, ev.automaton.past_start hj x x rfl⟩
  simp only [anchor]
  split
  · trivial
  · rename_i hne
    rcases hsrc with he | hsrc
    · exact absurd he hne
    · exact hsrc x x rfl

theorem foldl_invariant {α β : Type} (P : β → Prop) (f : β → β) (hf : ∀ b, P b → P (f b)) :
    ∀ (l : List α) (b : β), P b → P (l.foldl (fun b _ => f b) b)
  | [], _, h => h
  | _ :: l, b, h => foldl_invariant P f hf l (f b) (hf b h)

/-- The identity reaches the states `byIdentity` gives. -/
theorem byIdentity_sound (hyp : ev.Holds Mi) (hinc : ev.InclusionsHold Mi) :
    ∀ n ∈ ev.byIdentity N, Rel.Sub Rel.id (N.past (Label.denote Mi) n) := by
  unfold byIdentity
  split
  · rename_i hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    obtain ⟨hw, hre⟩ := hcond
    simp only [readsEmpty, List.any_eq_true] at hre
    obtain ⟨i, hi, hiacc⟩ := hre
    refine foldl_invariant (fun Z => ∀ n ∈ Z, Rel.Sub Rel.id (N.past (Label.denote Mi) n))
      (ev.identityStep N) ?_ _ _ (fun n hn => N.past_start hn)
    intro Z hZ n hn
    simp only [identityStep, List.mem_append, List.mem_filterMap, List.mem_range] at hn
    rcases hn with hn | ⟨g, _, hg⟩
    · exact hZ n hn
    · split at hg
      · rename_i hcopy
        simp only [Bool.and_eq_true, List.contains_iff_mem] at hcopy
        obtain ⟨hsrc, hexit⟩ := hcopy
        cases hg
        exact Rel.Sub.trans (startable_copy (g := g) hi (.inr (hZ _ hsrc)))
          (exit_sound hw hyp hinc hiacc hexit)
      · exact absurd hg (by simp)
  · exact fun n hn => N.past_start hn

/-- A starting state's role bounds the identity, if the identity reaches the
states of `Z`. -/
theorem startable_sound {Z : List Nat}
    (hZ : ∀ n ∈ Z, Rel.Sub Rel.id (N.past (Label.denote Mi) n)) {r : Role}
    (h : ev.startable Z r = true) : Rel.Sub Rel.id (ev.bound N Mi r) := by
  cases r with
  | state n =>
    simp only [startable, List.contains_iff_mem] at h
    exact hZ n h
  | after n => exact absurd h (by simp [startable])
  | copy j g =>
    simp only [startable, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      List.contains_iff_mem] at h
    exact startable_copy h.1 (h.2.imp id (hZ _))

/-- An accepting state's role bounds no more than `N` denotes. -/
theorem acceptable_sound (hyp : ev.Holds Mi) (hinc : ev.InclusionsHold Mi) {r : Role}
    (h : ev.acceptable N r = true) :
    Rel.Sub (ev.bound N Mi r) (N.denote (Label.denote Mi)) := by
  simp only [acceptable, List.any_eq_true] at h
  obtain ⟨s, hs, hacc⟩ := h
  refine Rel.Sub.trans (lifts_sound hyp hinc hs) ?_
  cases s with
  | state n => exact N.past_accepting hacc
  | after n => exact absurd hacc (by simp)
  | copy j g =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hacc
    obtain ⟨he, hj⟩ := hacc
    intro x z hxz
    exact absurd (bound_empty_accepting he hyp hj hxz) id

/-- What an accepted check establishes about the saturated automaton. -/
theorem check_spec (h : ev.check N M = none) :
    (∀ m ∈ M.start, ev.startable (ev.byIdentity N) (ev.role m) = true) ∧
      (∀ m, M.isAccepting m = true → ev.acceptable N (ev.role m) = true) ∧
      ∀ m a m', (a, m') ∈ M.trans m →
        ∃ s ∈ ev.lifts N (ev.role m), ev.steps N s a (ev.role m') = true := by
  unfold check at h
  split at h
  · exact absurd h (by simp)
  simp only [Certificate.orElse_eq_none] at h
  obtain ⟨-, -, hstart, hstates⟩ := h
  rw [List.findSome?_eq_none_iff] at hstart hstates
  refine ⟨fun m hm => ?_, fun m hacc => ?_, fun m a m' ht => ?_⟩
  · have := hstart m hm
    split at this
    · assumption
    · exact absurd this (by simp)
  · have hm : m < max M.size M.accepting.size := by
      have := NFA.lt_of_isAccepting hacc
      omega
    have := hstates m (List.mem_range.mpr hm)
    split at this
    · exact absurd this (by simp)
    · rename_i hcond
      simpa [hacc] using hcond
  · have hm : m < max M.size M.accepting.size := by
      have := NFA.lt_of_mem_trans ht
      omega
    have := hstates m (List.mem_range.mpr hm)
    split at this
    · exact absurd this (by simp)
    · rw [List.findSome?_eq_none_iff] at this
      have := this (a, m') ht
      split at this
      · rename_i hany
        simpa only [List.any_eq_true] using hany
      · exact absurd this (by simp)

/-- **Soundness.** If `check` accepts the evidence of a saturation from `N`
to `M`, the hypothesis holds and the evidence's letter inclusions hold, with
letters read through `Mi`, then `M` denotes no more than `N`. -/
theorem check_sound (h : ev.check N M = none) (hyp : ev.Holds Mi)
    (hinc : ev.InclusionsHold Mi) :
    Rel.Sub (M.denote (Label.denote Mi)) (N.denote (Label.denote Mi)) := by
  obtain ⟨hstart, hacc, hsteps⟩ := check_spec h
  have hpast := M.past_bound (I := Label.denote Mi) (fun m => ev.bound N Mi (ev.role m))
    (fun m hm => startable_sound (byIdentity_sound hyp hinc) (hstart m hm))
    (fun m a m' ht => by
      obtain ⟨s, hs, hstep⟩ := hsteps m a m' ht
      exact Rel.Sub.trans (Rel.comp_mono (lifts_sound hyp hinc hs) (Rel.Sub.refl _))
        (steps_sound hyp hstep))
  intro x y hxy
  obtain ⟨m, hm, hp⟩ := M.denote_past hxy
  exact acceptable_sound hyp hinc (hacc m hm) x y (hpast m x y hp)

end Evidence

end KaterCert

/-! The proof rests on Lean's standard axioms and nothing else: `lake build`
fails if a `sorry` or a new axiom creeps in. -/

/--
info: 'KaterCert.Evidence.check_sound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms KaterCert.Evidence.check_sound
