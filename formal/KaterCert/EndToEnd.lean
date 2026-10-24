import KaterCert.Whole
import KaterCert.ModelSound

/-!
# End to end

If Lean accepts the evidence of an assertion, the assertion holds on every
graph of the model that satisfies the module's declarations and assumptions.

`check` accepts the evidence if `Whole.checkAssertion` does and the
assumptions it marks as builtin are Kater's builtin ones
(`Model.builtinAssumptions`), which hold on every graph. The theory the chain
rests on is sound on every such graph (`Model.theory_sound`): its builtin
facts by the model, its module facts because the declarations and the
assumptions they come from hold (`incorporate_hold`). `rf` is `rfe | rfi`,
`po` is transitive and `any` relates every two events on every graph
(`Model.rf_split`, `facts`).
-/

namespace KaterCert

open ReadChain Whole

namespace EndToEnd

variable {E : Type}

/-- Whether Lean accepts the evidence of an assertion: the chain checks, and
the assumptions marked builtin are Kater's builtin ones. -/
def check (ev : ReadChain.Evidence) : Except String Unit :=
  match checkAssertion ev with
  | .error e => .error e
  | .ok () =>
    if ev.assumptions.all fun a => !a.builtin || match a.constraint with
        | .ok c => Model.builtinAssumptions.contains c
        | .error _ => true then .ok ()
    else .error "an assumption marked builtin is not one of Kater's builtin assumptions"

/-! ## Sequences -/

/-- The relation of a list of expressions in sequence. -/
def seqRel (M : Interp E) : List Exp → Rel E
  | [] => Rel.id
  | e :: es => Rel.comp (e.denote M) (seqRel M es)

theorem seqRel_append (M : Interp E) :
    ∀ (u v : List Exp) {x y : E}, seqRel M (u ++ v) x y ↔ Rel.comp (seqRel M u) (seqRel M v) x y
  | [], _, _, _ => Rel.id_comp.symm
  | a :: u, v, x, y => by
    simp only [List.cons_append, seqRel]
    constructor
    · rintro ⟨z, ha, hw⟩
      obtain ⟨z', hu, hv⟩ := (seqRel_append M u v).mp hw
      exact ⟨z', ⟨z, ha, hu⟩, hv⟩
    · rintro ⟨z', ⟨z, ha, hu⟩, hv⟩
      exact ⟨z, ha, (seqRel_append M u v).mpr ⟨z', hu, hv⟩⟩

theorem seqList_denote (M : Interp E) : ∀ (e : Exp) {x y : E},
    e.denote M x y ↔ seqRel M e.seqList x y
  | .seq a b, x, y => by
    simp only [Exp.seqList, Exp.denote]
    rw [seqRel_append]
    constructor
    · rintro ⟨z, ha, hb⟩
      exact ⟨z, (seqList_denote M a).mp ha, (seqList_denote M b).mp hb⟩
    · rintro ⟨z, ha, hb⟩
      exact ⟨z, (seqList_denote M a).mpr ha, (seqList_denote M b).mpr hb⟩
  | .label l, x, y => by simp only [Exp.seqList, seqRel, Rel.comp_id]
  | .zero, x, y => by simp only [Exp.seqList, seqRel, Rel.comp_id]
  | .alt a b, x, y => by simp only [Exp.seqList, seqRel, Rel.comp_id]
  | .star a, x, y => by simp only [Exp.seqList, seqRel, Rel.comp_id]
  | .plus a, x, y => by simp only [Exp.seqList, seqRel, Rel.comp_id]
  | .opt a, x, y => by simp only [Exp.seqList, seqRel, Rel.comp_id]
  | .ref _, x, y => by simp only [Exp.seqList, seqRel, Rel.comp_id]
  | .fix _ _, x, y => by simp only [Exp.seqList, seqRel, Rel.comp_id]

/-- Letters that are all predicates relate an event to itself, with their
checks. -/
theorem predChecks_rel {M : Interp E} : ∀ {es : List Exp} {ps : List Predicate},
    predChecks es = some ps → ∀ {x y : E}, seqRel M es x y → x = y ∧ Checks M ps x
  | [], ps, h, x, y, hr => by
    simp only [predChecks, Option.some.injEq] at h
    subst h
    exact ⟨hr, fun p hp => by simp at hp⟩
  | .label l :: es, ps, h, x, y, hr => by
    simp only [predChecks] at h
    split at h
    · rename_i hl
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨qs, hqs, rfl⟩ := h
      obtain ⟨z, hz, hrest⟩ := hr
      have hl' : l.rel = none := by simpa using hl
      simp only [Exp.denote, Label.denote, hl'] at hz
      obtain ⟨rfl, hpre⟩ := hz
      obtain ⟨rfl, hq⟩ := predChecks_rel hqs hrest
      exact ⟨rfl, fun p hp => by
        simp only [List.mem_append] at hp
        rcases hp with hp | hp
        · exact hpre p hp
        · exact hq p hp⟩
    · simp at h
  | .zero :: _, _, h, _, _, _ => by simp [predChecks] at h
  | .alt _ _ :: _, _, h, _, _, _ => by simp [predChecks] at h
  | .seq _ _ :: _, _, h, _, _, _ => by simp [predChecks] at h
  | .star _ :: _, _, h, _, _, _ => by simp [predChecks] at h
  | .plus _ :: _, _, h, _, _, _ => by simp [predChecks] at h
  | .opt _ :: _, _, h, _, _, _ => by simp [predChecks] at h
  | .ref _ :: _, _, h, _, _, _ => by simp [predChecks] at h
  | .fix _ _ :: _, _, h, _, _, _ => by simp [predChecks] at h

/-! ## What the theory takes in holds -/

variable {M : Interp E}

/-- The relation of a bare letter. -/
theorem bare_denote {r : Relation} {l : Label} (hl : l.rel = some r) (hpre : l.pre = [])
    (hpost : l.post = []) {x y : E} : l.denote M x y ↔ r.denote M x y := by
  simp [Label.denote, hl, hpre, hpost, Checks]

/-- What the right-hand side of a domain assumption says of the steps of
`r`, from the sequence `[A];r;[B]` it reads it off. -/
theorem domainOfSeq_sound {r : Relation} {parts : List Exp} {pb pa : List Predicate}
    (h : domainOfSeq r parts = some (pb, pa)) {x y : E} (hr : r.denote M x y)
    (hrhs : seqRel M parts x y → Checks M pb x ∧ Checks M pa y →
      Checks M pb x ∧ Checks M pa y)
    (hs : seqRel M parts x y) : Checks M pb x ∧ Checks M pa y := by
  unfold domainOfSeq at h
  split at h
  · simp at h
  · rename_i i hi
    split at h
    · rename_i m qb qa hpi hqb hqa
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hlt : i < parts.length := by
          rcases Nat.lt_or_ge i parts.length with h' | h'
          · exact h'
          · simp [List.getElem?_eq_none h'] at hpi
        have hget : parts[i] = Exp.label m := by
          rw [List.getElem?_eq_getElem hlt] at hpi
          simpa using hpi
        have hsplit : parts = parts.take i ++ Exp.label m :: parts.drop (i + 1) := by
          conv => lhs; rw [← List.take_append_drop i parts]
          rw [List.drop_eq_getElem_cons hlt, hget]
        rw [hsplit, seqRel_append] at hs
        obtain ⟨z, hb, hz⟩ := hs
        obtain ⟨w, -, ha⟩ := hz
        obtain ⟨rfl, hpb'⟩ := predChecks_rel hqb hb
        obtain ⟨rfl, hpa'⟩ := predChecks_rel hqa ha
        exact ⟨hpb', hpa'⟩
      · simp at h
    · simp at h

/-- The domain `domainOf` reads off an inclusion holds. -/
theorem domainOf_sound {r : Relation} {rhs : Exp} {dom codom : List Predicate}
    (h : domainOf r rhs = some (dom, codom))
    (hsub : ∀ x y, r.denote M x y → rhs.denote M x y) :
    ∀ x y, M.rel r.id x y → Checks M dom x ∧ Checks M codom y := by
  unfold domainOf at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨⟨pb, pa⟩, hp, horient⟩ := h
  -- what the right-hand side says of a step of `r`, in the direction of `r`
  have hr : ∀ x y, r.denote M x y → Checks M pb x ∧ Checks M pa y := by
    intro x y hxy
    split at hp
    · rename_i m
      split at hp
      · rename_i hm
        have hm' : m.rel = some r := by simpa using hm
        simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        have := hsub x y hxy
        simp only [Exp.denote, Label.denote, hm'] at this
        exact ⟨this.1, this.2.2⟩
      · simp at hp
    · exact domainOfSeq_sound hp hxy (fun _ h => h) ((seqList_denote M rhs).mp (hsub x y hxy))
  intro x y hxy
  unfold orient at horient
  cases hinv : r.inverse
  · simp only [hinv, Bool.false_eq_true, ite_false, Prod.mk.injEq] at horient
    obtain ⟨rfl, rfl⟩ := horient
    exact hr x y (by simp [Relation.denote, hinv, hxy])
  · simp only [hinv, ite_true, Prod.mk.injEq] at horient
    obtain ⟨rfl, rfl⟩ := horient
    have := hr y x (by simp [Relation.denote, hinv, hxy])
    exact ⟨this.2, this.1⟩

theorem onePred_spec {e : Exp} {p : Predicate} (h : onePred e = some p) :
    ∃ l, e = .label l ∧ l.rel = none ∧ l.pre = [p] ∧ p.complement = false := by
  cases e with
  | label l =>
    rcases l with ⟨rel, pre, post⟩
    cases rel with
    | some r => simp [onePred] at h
    | none =>
      match pre with
      | [] => simp [onePred] at h
      | [q] =>
        cases hq : q.complement
        · simp only [onePred, Option.isNone_none, ite_true, hq, Bool.false_eq_true, ite_false,
            Option.some.injEq] at h
          subst h
          exact ⟨_, rfl, rfl, rfl, hq⟩
        · simp [onePred, hq] at h
      | _ :: _ :: _ => simp [onePred] at h
  | _ => simp [onePred] at h

/-- Letters that each check one plain predicate relate an event to itself
exactly when the predicates hold of it. -/
theorem onePred_rel {es : List Exp} {ps : List Predicate} (h : es.mapM onePred = some ps)
    {x : E} (hx : ∀ p ∈ ps, M.pred p.id x) : seqRel M es x x := by
  induction es generalizing ps with
  | nil => exact rfl
  | cons e es ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨p, hp, qs, hqs, rfl⟩ := h
    obtain ⟨l, rfl, hl, hpre, hc⟩ := onePred_spec hp
    refine ⟨x, ?_, ih hqs fun q hq => hx q (List.mem_cons_of_mem _ hq)⟩
    simp only [Exp.denote, Label.denote, hl, true_and]
    intro p' hp'
    rw [hpre, List.mem_singleton] at hp'
    subst hp'
    simp only [Predicate.Holds, hc, Bool.false_eq_true, ite_false]
    exact hx _ (List.mem_cons_self ..)

/-- What a domain assumption `r <= [A];r;[B]` takes in holds. -/
theorem domain_hold {d : Decls} (hd : d.Hold M) {l : Label} {rhs : Exp}
    (hsub : ∀ x y, l.denote M x y → rhs.denote M x y) :
    (match l.rel with
      | some r =>
        if l.pre.isEmpty && l.post.isEmpty then
          match domainOf r rhs with
          | some (dom, codom) => { d with domains := d.domains ++ [(r.id, dom, codom)] }
          | none => d
        else d
      | none => d).Hold M := by
  obtain ⟨hdisj, hinv, hdom⟩ := hd
  split
  · rename_i r hr
    split
    · rename_i hbare
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hbare
      split
      · rename_i dom codom hdc
        refine ⟨hdisj, hinv, fun t ht => ?_⟩
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with ht | rfl
        · exact hdom t ht
        · exact domainOf_sound hdc fun x y h =>
            hsub x y ((bare_denote hr hbare.1 hbare.2).mpr h)
      · exact ⟨hdisj, hinv, hdom⟩
    · exact ⟨hdisj, hinv, hdom⟩
  · exact ⟨hdisj, hinv, hdom⟩

theorem mem_pair {l : List Int} (hl : l.length = 2) {a b c : Int} (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) (hc : c ∈ l) : c = a ∨ c = b := by
  match l, hl with
  | [x, y], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb hc
    omega

/-- What an incompatibility `[A;B;...] <= 0` takes in holds. -/
theorem incompat_hold {d : Decls} (hd : d.Hold M) {lhs : Exp}
    (hnone : ∀ x, ¬ lhs.denote M x x) :
    (let parts := lhs.seqList
     if parts.length < 2 then d else
     match parts.mapM onePred with
     | some ps =>
       let ids := (ps.map (·.id)).eraseDups
       if ids.length == 2 then { d with disjoint := d.disjoint ++ [ids] }
       else { d with invalid := d.invalid ++ [ids] }
     | none => d).Hold M := by
  obtain ⟨hdisj, hinv, hdom⟩ := hd
  simp only []
  split
  · exact ⟨hdisj, hinv, hdom⟩
  · split
    · rename_i ps hps
      have hall : ∀ x, ¬ ∀ p ∈ ps, M.pred p.id x := fun x hx =>
        hnone x ((seqList_denote M lhs).mpr (onePred_rel hps hx))
      have hmem : ∀ {s : Predicate}, s ∈ ps → s.id ∈ (ps.map (·.id)).eraseDups := fun hs =>
        List.mem_eraseDups.mpr (List.mem_map_of_mem hs)
      split
      · rename_i hlen
        refine ⟨fun D hD => ?_, hinv, hdom⟩
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hD
        rcases hD with hD | rfl
        · exact hdisj D hD
        · intro a ha b hb hab e' ⟨h₁, h₂⟩
          apply hall e'
          intro s hs
          have hlen' : ((ps.map (·.id)).eraseDups).length = 2 := by simpa using hlen
          rcases mem_pair hlen' ha hb hab (hmem hs) with h | h
          · rw [h]; exact h₁
          · rw [h]; exact h₂
      · refine ⟨hdisj, fun I hI => ?_, hdom⟩
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hI
        rcases hI with hI | rfl
        · exact hinv I hI
        · intro e' he'
          exact hall e' fun s hs => he' s.id (hmem hs)
    · exact ⟨hdisj, hinv, hdom⟩

/-- What Lean's reading of an assumption takes into the theory holds if the
assumption does. -/
theorem incorporate_hold {d : Decls} (hd : d.Hold M) {c : Constraint} (hc : c.Holds M) :
    (incorporate d c).Hold M := by
  cases c with
  | subset lhs rhs e r =>
    have hnone : rhs = .zero → ∀ x, ¬ lhs.denote M x x := by
      intro hz x hx
      subst hz
      simp only [Constraint.Holds, Constraint.SubsetHolds] at hc
      split at hc
      · obtain ⟨y, hy⟩ := hc ⟨x, hx⟩
        exact hy
      · split at hc
        · exact hc x hx
        · exact hc x x hx
    cases lhs <;> cases rhs <;> cases e <;> cases r <;>
      first
      | exact domain_hold hd fun x y hxy => hc x y hxy
      | exact incompat_hold hd (hnone rfl)
      | exact hd
  | equal lhs rhs e r =>
    cases lhs <;> cases e <;> cases r <;>
      first
      | exact domain_hold hd fun x y hxy => hc.1 x y hxy
      | exact hd
  | total _ => exact hd

/-- What the theory takes in of a module holds where its declarations and
the assumptions the theory took in hold. -/
theorem declsOf_hold {ev : ReadChain.Evidence}
    (hdisj : ∀ D ∈ ev.disjoint, ∀ p ∈ D, ∀ q ∈ D, p ≠ q → ∀ e, ¬ (M.pred p e ∧ M.pred q e))
    (hh : HypsHold M ev.assumptions) : (declsOf ev).Hold M := by
  unfold declsOf
  have : ∀ (l : List Assumption) (d : Decls), d.Hold M →
      (∀ a ∈ l, ∀ c, a.constraint = .ok c → c.Holds M) →
      (l.foldl (fun d a => match a.constraint with
        | .ok c => if a.saturated then d else incorporate d c
        | .error _ => d) d).Hold M := by
    intro l
    induction l with
    | nil => intro d hd _; exact hd
    | cons a l ih =>
      intro d hd hl
      simp only [List.foldl_cons]
      apply ih _ _ fun a' ha' => hl a' (List.mem_cons_of_mem _ ha')
      split
      · rename_i c hc
        split
        · exact hd
        · exact incorporate_hold hd (hl a (List.mem_cons_self ..) c hc)
      · exact hd
  rw [← Array.foldl_toList]
  apply this
  · exact ⟨hdisj, fun I hI => by simp at hI, fun t ht => by simp at ht⟩
  · intro a ha c hc
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
    exact hh i a c (by rw [← Array.getElem?_toList]; exact hi) hc

theorem declsOf_perLoc (ev : ReadChain.Evidence) : (declsOf ev).perLoc = ev.perLoc := by
  unfold declsOf
  have : ∀ (l : List Assumption) (d : Decls),
      (l.foldl (fun d a => match a.constraint with
        | .ok c => if a.saturated then d else incorporate d c
        | .error _ => d) d).perLoc = d.perLoc := by
    intro l
    induction l with
    | nil => intro d; rfl
    | cons a l ih =>
      intro d
      simp only [List.foldl_cons]
      rw [ih]
      split
      · split
        · rfl
        · rename_i c _ _
          unfold incorporate
          cases c with
          | subset lhs rhs e r =>
            cases lhs <;> cases rhs <;> cases e <;> cases r <;> simp only [] <;>
              (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl
          | equal lhs rhs e r =>
            cases lhs <;> cases e <;> cases r <;> simp only [] <;>
              (try split) <;> (try split) <;> (try split) <;> rfl
          | total _ => rfl
      · rfl
  rw [← Array.foldl_toList]
  exact this _ _

end EndToEnd

namespace EndToEnd

open Model

/-- `po` is transitive and `any` relates every two events, on every graph. -/
theorem facts {G : Graph} (hG : G.WF) (U : Graph.User G.E) (perLoc : List (Int × Int)) :
    Facts (G.interp U perLoc) where
  po_trans x y z h₁ h₂ := by
    simp only [interp_rel, Graph.rel] at h₁ h₂ ⊢
    exact hG.po_trans _ _ _ h₁ h₂
  any_univ x y := by simp [interp_rel, Graph.rel]

/-- **End to end.** If Lean accepts the evidence of an assertion, the
assertion holds on every graph of the model where the module's `disjoint`
declarations and its assumptions hold, whatever its own predicates and
relations mean. -/
theorem sound {ev : ReadChain.Evidence} (h : check ev = .ok ())
    (G : Graph) (hG : G.WF) (U : Graph.User G.E)
    (hdisj : ∀ D ∈ ev.disjoint, ∀ p ∈ D, ∀ q ∈ D, p ≠ q →
      ∀ e, ¬ ((G.interp U ev.perLoc).pred p e ∧ (G.interp U ev.perLoc).pred q e))
    (hyps : ∀ a ∈ ev.assumptions, a.builtin = false → ∀ c, a.constraint = .ok c →
      c.Holds (G.interp U ev.perLoc)) :
    ev.constraint.Holds (G.interp U ev.perLoc) := by
  unfold check at h
  split at h
  · simp at h
  · rename_i hchain
    split at h
    · rename_i hbuiltin
      have hh : HypsHold (G.interp U ev.perLoc) ev.assumptions := by
        intro i a c hi hc
        have ha : a ∈ ev.assumptions := Array.mem_of_getElem? hi
        cases hb : a.builtin
        · exact hyps a ha hb c hc
        · simp only [Array.all_eq_true] at hbuiltin
          obtain ⟨hj, hji⟩ := Array.getElem?_eq_some_iff.mp hi
          have := hbuiltin i hj
          rw [hji] at this
          simp only [hb, Bool.not_true, Bool.false_or, hc] at this
          exact builtinAssumptions_hold hG U ev.perLoc c (List.contains_iff_mem.mp this)
      have hwf : (declsOf ev).wf = true := by
        unfold checkAssertion at hchain
        split at hchain
        · simp at hchain
        · rename_i hwf
          simpa using hwf
      have hd := declsOf_hold hdisj hh
      have hθ := theory_sound hG U (declsOf ev) hwf (by rw [declsOf_perLoc]; exact hd)
      rw [declsOf_perLoc] at hθ
      exact checkAssertion_sound hchain hθ (rf_split U ev.perLoc) (facts hG U ev.perLoc) hh
    · simp at h

end EndToEnd

end KaterCert

/-! The proofs rest on Lean's standard axioms and nothing else: `lake build`
fails if a `sorry` or a new axiom creeps in. -/

/--
info: 'KaterCert.EndToEnd.sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms KaterCert.EndToEnd.sound
