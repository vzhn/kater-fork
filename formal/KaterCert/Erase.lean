import KaterCert.ModelSound
import KaterCert.Cycles

/-!
# A graph without one of its events

GenMC adds an event `e` to a graph `G₀` it has built; the graph with `e` is
`G`, and `G₀` is `G` without `e` (`Graph.erase`): its other events, with all
`G` says of them. A cycle of `G` that does not pass `e` is one of `G₀` if
each letter it reads relates two events other than `e` in `G₀` as it does in
`G`, or more. That holds of every builtin, if nothing reads from `e`
(`rel_erase`, `pred_erase`), but of the hazard pointers' predicates, `HEAP`
and `unprotected`, which depend on the protections, allocations and retires
around an event (`Extensible.stableLabel` leaves them out): the positional
relations (`po-imm`, `mo-imm`, `fr-imm`, `last_*`, ...) only gain pairs
when `e` goes. A module's own relations and predicates in `G₀` are those of
`G` on the other events (`User.erase`).
-/

namespace KaterCert

namespace Model

namespace Graph

variable (G : Graph) (e : G.E)

/-- The graph without the event `e`. -/
def erase : Graph where
  E := {a : G.E // a ≠ e}
  kind a := G.kind a.1
  order a := G.order a.1
  excl a := G.excl a.1
  loc a := G.loc a.1
  thread a := G.thread a.1
  po a b := G.po a.1 b.1
  rf a b := G.rf a.1 b.1
  mo a b := G.mo a.1 b.1
  ctrl a b := G.ctrl a.1 b.1
  addr a b := G.addr a.1 b.1
  data a b := G.data a.1 b.1
  pctrl a b := G.pctrl a.1 b.1
  tc a b := G.tc a.1 b.1
  tj a b := G.tj a.1 b.1
  lin a b := G.lin a.1 b.1
  hp a := G.hp a.1
  added a b := G.added a.1 b.1
  hb a b := G.hb a.1 b.1
  durable a := G.durable a.1
  recovery a := G.recovery a.1
  abstractLock a := G.abstractLock a.1
  dependableOther a := G.dependableOther a.1
  si a b := G.si a.1 b.1
  locOverlap a b := G.locOverlap a.1 b.1
  lk a := G.lk a.1
  ul a := G.ul a.1

/-- The module's own predicates and relations, on the other events. -/
def User.erase {G : Graph} (U : User G.E) (e : G.E) : User (G.erase e).E where
  pred i a := U.pred i a.1
  rel i a b := U.rel i a.1 b.1

variable {G e}

/-! ## What the graph without `e` says of its events -/

theorem erase_ext {a b : (G.erase e).E} : a = b ↔ a.1 = b.1 := Subtype.ext_iff

theorem erase_sameLoc {a b : (G.erase e).E} : (G.erase e).sameLoc a b ↔ G.sameLoc a.1 b.1 := by
  unfold sameLoc
  rw [erase_ext]
  rfl

theorem erase_sameBlock {a b : (G.erase e).E} :
    (G.erase e).sameBlock a b ↔ G.sameBlock a.1 b.1 := by
  unfold sameBlock
  rw [ne_eq, ne_eq, erase_ext]
  rfl

theorem erase_sameThread {a b : (G.erase e).E} :
    (G.erase e).sameThread a b ↔ G.sameThread a.1 b.1 := Iff.rfl

theorem erase_poLoc {a b : (G.erase e).E} : (G.erase e).poLoc a b ↔ G.poLoc a.1 b.1 := by
  simp only [poLoc, erase_sameLoc]
  rfl

/-- What reads from `e` reads from no event of the graph without it: if
nothing does, the reads of the initial value are the same. -/
theorem erase_readsInit (hrf : ∀ b, ¬ G.rf e b) {a : (G.erase e).E} :
    (G.erase e).readsInit a ↔ G.readsInit a.1 := by
  simp only [readsInit, erase]
  constructor
  · rintro h ⟨w, hw⟩
    by_cases hwe : w = e
    · subst hwe
      exact hrf _ hw
    · exact h ⟨⟨w, hwe⟩, hw⟩
  · rintro h ⟨w, hw⟩
    exact h ⟨w.1, hw⟩

theorem erase_fr (hrf : ∀ b, ¬ G.rf e b) {a b : (G.erase e).E} :
    (G.erase e).fr a b ↔ G.fr a.1 b.1 := by
  unfold fr
  rw [erase_readsInit hrf, erase_sameLoc, ne_eq, ne_eq, erase_ext]
  show (¬a.1 = b.1 ∧ G.kind a.1 = .R ∧ G.kind b.1 = .W ∧ G.sameLoc a.1 b.1 ∧
      (G.readsInit a.1 ∨ ∃ s : (G.erase e).E, G.rf s.1 a.1 ∧ G.mo s.1 b.1)) ↔ _
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄, h₅ | ⟨s, hs₁, hs₂⟩⟩
    · exact ⟨h₁, h₂, h₃, h₄, .inl h₅⟩
    · exact ⟨h₁, h₂, h₃, h₄, .inr ⟨s.1, hs₁, hs₂⟩⟩
  · rintro ⟨h₁, h₂, h₃, h₄, h₅ | ⟨s, hs₁, hs₂⟩⟩
    · exact ⟨h₁, h₂, h₃, h₄, .inl h₅⟩
    · by_cases hse : s = e
      · subst hse
        exact absurd hs₁ (hrf _)
      · exact ⟨h₁, h₂, h₃, h₄, .inr ⟨⟨s, hse⟩, hs₁, hs₂⟩⟩

theorem erase_wf (hG : G.WF) (hrf : ∀ b, ¬ G.rf e b) : (G.erase e).WF where
  order_rel a := hG.order_rel a.1
  order_acq a := hG.order_acq a.1
  po_trans a b c := hG.po_trans a.1 b.1 c.1
  po_total a b h hne := hG.po_total a.1 b.1 h fun h' => hne (Subtype.ext h')
  rf_kinds a b := hG.rf_kinds a.1 b.1
  rf_unique a b c h₁ h₂ := Subtype.ext (hG.rf_unique a.1 b.1 c.1 h₁ h₂)
  mo_kinds a b := hG.mo_kinds a.1 b.1
  mo_irrefl a := hG.mo_irrefl a.1
  mo_trans a b c := hG.mo_trans a.1 b.1 c.1
  rf_po a b := hG.rf_po a.1 b.1
  mo_po a b := hG.mo_po a.1 b.1
  fr_po a b h := hG.fr_po a.1 b.1 ((erase_fr hrf).mp h)
  ctrl_po a b := hG.ctrl_po a.1 b.1
  addr_po a b := hG.addr_po a.1 b.1
  data_po a b := hG.data_po a.1 b.1
  pctrl_po a b := hG.pctrl_po a.1 b.1
  dependableOther_kind a := hG.dependableOther_kind a.1
  tc_kinds a b := hG.tc_kinds a.1 b.1
  tj_kinds a b := hG.tj_kinds a.1 b.1
  lin_kinds a b := hG.lin_kinds a.1 b.1

/-- The predicates whose meaning at an event depends on other events. -/
def unstablePred : Builtin.Pred → Bool
  | .HPPROT | .NOTHPPROT | .HEAP => true
  | _ => false

/-- **The predicates** but the unstable ones mean of an event what they do
in the graph with `e`. -/
theorem pred_erase {p : Builtin.Pred} (hp : unstablePred p = false) {a : (G.erase e).E} :
    (G.erase e).pred p a ↔ G.pred p a.1 := by
  cases p <;> first | exact absurd hp (by decide) | exact Iff.rfl

/-- The positional relations only gain pairs when an event goes. -/
theorem positional_erase {P Q : G.E → Prop} {byHb : Bool} {a b : (G.erase e).E}
    (h : G.positional P Q byHb a.1 b.1) :
    (G.erase e).positional (fun z => P z.1) (fun z => Q z.1) byHb a b := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  refine ⟨fun h => h₁ (congrArg Subtype.val h), h₂, h₃, erase_sameBlock.mpr h₄, h₅, ?_⟩
  rintro ⟨z, hz₁, hz₂, hz₃, hz₄, hz₅, hz₆, hz₇⟩
  exact h₆ ⟨z.1, fun h => hz₁ (Subtype.ext h), fun h => hz₂ (Subtype.ext h), hz₃,
    erase_sameBlock.mp hz₄, hz₅, hz₆, hz₇⟩

theorem lastFreeing_erase {a b : (G.erase e).E} (h : G.lastFreeing a.1 b.1) :
    (G.erase e).lastFreeing a b := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  refine ⟨fun h => h₁ (congrArg Subtype.val h), h₂, h₃, erase_sameBlock.mpr h₄, h₅, ?_⟩
  rintro ⟨g, hg₁, hg₂, hg₃, hg₄, hg₅, hg₆⟩
  exact h₆ ⟨g.1, fun h => hg₁ (Subtype.ext h), fun h => hg₂ (Subtype.ext h), hg₃,
    erase_sameBlock.mp hg₄, hg₅, hg₆⟩

/-- **The relations** but `unprotected` relate two events at least as they
do in the graph with `e`, if nothing reads from `e`. -/
theorem rel_erase (hrf : ∀ b, ¬ G.rf e b) {r : Builtin.Rel} (hr : r ≠ .unprotected)
    {a b : (G.erase e).E} (h : G.rel r a.1 b.1) : (G.erase e).rel r a b := by
  cases r
  case unprotected => exact absurd rfl hr
  case last_na_reads | last_na_writes | last_at_reads | last_at_writes =>
    simp only [rel] at h ⊢
    exact positional_erase h
  case alloc =>
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h
    exact ⟨fun h => h₁ (congrArg Subtype.val h), h₂, h₃, erase_sameBlock.mpr h₄⟩
  case free | retire =>
    exact ⟨lastFreeing_erase h.1, h.2⟩
  case mo_imm =>
    exact ⟨h.1, fun ⟨z, hz₁, hz₂⟩ => h.2 ⟨z.1, hz₁, hz₂⟩⟩
  case fr =>
    exact (erase_fr hrf).mpr h
  case fr_imm =>
    refine ⟨(erase_fr hrf).mpr h.1, fun ⟨z, hz₁, hz₂⟩ => h.2 ⟨z.1, (erase_fr hrf).mp hz₁, hz₂⟩⟩
  case rfe | moe =>
    exact h
  case fre =>
    exact ⟨(erase_fr hrf).mpr h.1, h.2⟩
  case fri =>
    exact ⟨(erase_fr hrf).mpr h.1, h.2⟩
  case detour =>
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h
    exact ⟨h₁, h₂, erase_poLoc.mpr h₃, h₄⟩
  case rmw =>
    obtain ⟨⟨h₀, h₀'⟩, h₁, h₂, h₃, h₄, h₅⟩ := h
    exact ⟨⟨h₀, fun ⟨z, hz₁, hz₂⟩ => h₀' ⟨z.1, hz₁, hz₂⟩⟩, h₁, h₂, h₃, h₄,
      erase_sameLoc.mpr h₅⟩
  case po_loc_imm =>
    obtain ⟨h₁, h₂⟩ := h
    exact ⟨erase_poLoc.mpr h₁, fun ⟨z, hz₁, hz₂, hz₃⟩ => h₂ ⟨z.1, hz₁, hz₂, erase_sameLoc.mp hz₃⟩⟩
  case po_loc =>
    exact erase_poLoc.mpr h
  case po_imm =>
    exact ⟨h.1, fun ⟨z, hz₁, hz₂⟩ => h.2 ⟨z.1, hz₁, hz₂⟩⟩
  all_goals exact h

/-! ## What the letters mean -/

section Interp

variable {U : User G.E} {perLoc : List (Int × Int)}

theorem erase_interp_pred {i : Int}
    (hi : ∀ p, Builtin.Pred.ofId i = some p → unstablePred p = false) {a : (G.erase e).E} :
    ((G.erase e).interp (U.erase e) perLoc).pred i a ↔ (G.interp U perLoc).pred i a.1 := by
  simp only [interp]
  cases hp : Builtin.Pred.ofId i with
  | some p => exact pred_erase (hi p hp)
  | none =>
    simp only
    split
    · exact Iff.rfl
    · exact Iff.rfl

theorem erase_interp_rel (hrf : ∀ b, ¬ G.rf e b) {i : Int}
    (hi : i ≠ Builtin.Rel.unprotected.id) {a b : (G.erase e).E}
    (h : (G.interp U perLoc).rel i a.1 b.1) : ((G.erase e).interp (U.erase e) perLoc).rel i a b := by
  simp only [interp] at h ⊢
  cases hr : Builtin.Rel.ofId i with
  | some r =>
    rw [hr] at h
    have : r ≠ .unprotected := by
      rintro rfl
      exact hi (rel_ofId_eq_some hr).symm
    exact rel_erase hrf this h
  | none =>
    rw [hr] at h
    simp only at h ⊢
    split
    · rename_i hneg
      simp only [hneg, ite_true] at h
      cases hf : List.find? (fun x => x.snd == i) perLoc with
      | some p =>
        rw [hf] at h
        rcases p with ⟨b', v⟩
        exact ⟨h.1, erase_sameLoc.mpr h.2⟩
      | none =>
        rw [hf] at h
        exact h
    · rename_i hneg
      simp only [hneg, ite_false] at h

theorem pred_ofId_eq_some {i : Int} {p : Builtin.Pred} (h : Builtin.Pred.ofId i = some p) :
    p.id = i := by
  have := List.find?_some h
  simpa using this

/-- The predicates of a stable letter mean what they did. -/
theorem checks_erase {ps : List Predicate}
    (hps : ps.all (fun p => !Extensible.unstablePreds.contains p.id) = true) {a : (G.erase e).E} :
    Checks ((G.erase e).interp (U.erase e) perLoc) ps a ↔ Checks (G.interp U perLoc) ps a.1 := by
  simp only [List.all_eq_true, Bool.not_eq_true'] at hps
  have hp : ∀ p ∈ ps, (p.Holds ((G.erase e).interp (U.erase e) perLoc) a ↔
      p.Holds (G.interp U perLoc) a.1) := by
    intro p hp
    have hi : ∀ q, Builtin.Pred.ofId p.id = some q → unstablePred q = false := by
      intro q hq
      have hq' := pred_ofId_eq_some hq
      have hn := hps p hp
      simp only [Extensible.unstablePreds, List.contains_cons, List.contains_nil, Bool.or_false,
        Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hn
      rw [← hq'] at hn
      cases q <;> first | rfl | (exfalso; simp [Builtin.Pred.id] at hn)
    unfold Predicate.Holds
    rw [erase_interp_pred hi]
  exact ⟨fun h p hm => (hp p hm).mp (h p hm), fun h p hm => (hp p hm).mpr (h p hm)⟩

/-- **A stable letter** relates two events other than `e` without `e` as it
does with it, or more, if nothing reads from `e`. -/
theorem label_erase (hrf : ∀ b, ¬ G.rf e b) {l : Label} (hl : Extensible.stableLabel l = true)
    {a b : (G.erase e).E} (h : l.denote ((G.interp U perLoc).without e) a b) :
    l.denote ((G.erase e).interp (U.erase e) perLoc) a b := by
  have h : l.denote (G.interp U perLoc) a.1 b.1 := (Label.denote_without l).mp h
  unfold Extensible.stableLabel at hl
  simp only [Bool.and_eq_true, List.all_append] at hl
  obtain ⟨⟨hpre, hpost⟩, hrel⟩ := hl
  rcases l with ⟨_ | r, pre, post⟩
  · simp only [Label.denote] at h ⊢
    exact ⟨Subtype.ext h.1, (checks_erase hpre).mpr h.2⟩
  · simp only [Label.denote] at h ⊢
    simp only [bne_iff_ne, ne_eq] at hrel
    refine ⟨(checks_erase hpre).mpr h.1, ?_, (checks_erase hpost).mpr h.2.2⟩
    have h₂ := h.2.1
    unfold Relation.denote at h₂ ⊢
    cases hinv : r.inverse <;> simp only [hinv, Bool.false_eq_true, ↓reduceIte] at h₂ ⊢ <;>
      exact erase_interp_rel hrf hrel h₂

/-- **An automaton of stable letters** relates two events other than `e`
without `e` as it does with it, or more, if nothing reads from `e`. -/
theorem nfa_erase (hrf : ∀ b, ¬ G.rf e b) {N : NFA Label}
    (hN : N.outs.all (·.all fun t => Extensible.stableLabel t.1) = true) :
    Rel.Sub (N.denote (Label.denote ((G.interp U perLoc).without e)))
      (N.denote (Label.denote ((G.erase e).interp (U.erase e) perLoc))) := by
  rintro a b ⟨q, hq, w, hw, hr⟩
  refine ⟨q, hq, w, hw, ?_⟩
  clear hq
  induction hw generalizing a with
  | nil => exact hr
  | @cons q l q' w ht _ ih =>
    obtain ⟨c, hl, hr'⟩ := hr
    have hstable : Extensible.stableLabel l = true := by
      have hq := Extensible.lt_of_mem_trans ht
      unfold NFA.trans at ht
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hq] at ht
      simp only [Array.all_eq_true, List.all_eq_true] at hN
      exact hN q hq _ ht
    exact ⟨c, label_erase hrf hstable hl, ih (a := c) hr'⟩

end Interp

end Graph

end Model

end KaterCert
