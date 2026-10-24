import KaterCert.Model

/-!
# The theory holds in the model

Lean's theory of a module (`Theory.ofDecls`) is sound in every graph of the
model whose module declarations hold (`theory_sound`); the builtin
assumptions hold in every graph (`builtinAssumptions_hold`); and `rf` is
`rfe | rfi` (`rf_split`). These are what the facts the checkers ask of the
theory, and the assumptions Kater always makes, rest on: they stop being
hypotheses.
-/

namespace KaterCert

namespace Model

open Builtin

/-- A letter of a bare relation. -/
def bare (r : Builtin.Rel) : Exp := .label { rel := some { id := r.id, inverse := false }, pre := [], post := [] }

/-- Kater's builtin assumptions (`registerBuiltins`): `fr;mo <= fr`,
`po;po <= po`, `mo;mo <= mo`, `rf;fr <= mo`. -/
def builtinAssumptions : List Constraint :=
  [.subset (.seq (bare .fr) (bare .mo)) (bare .fr) false false,
   .subset (.seq (bare .po) (bare .po)) (bare .po) false false,
   .subset (.seq (bare .mo) (bare .mo)) (bare .mo) false false,
   .subset (.seq (bare .rf) (bare .fr)) (bare .mo) false false]

variable {G : Graph}

theorem sameLoc_refl (x : G.E) : G.sameLoc x x := Or.inl rfl

theorem sameLoc_symm {x y : G.E} (h : G.sameLoc x y) : G.sameLoc y x := by
  rcases h with rfl | ⟨hx, hy, hl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hy, hx, hl.symm⟩

theorem sameLoc_trans {x y z : G.E} (h₁ : G.sameLoc x y) (h₂ : G.sameLoc y z) :
    G.sameLoc x z := by
  rcases h₁ with rfl | ⟨hx, hy, hl₁⟩
  · exact h₂
  · rcases h₂ with rfl | ⟨_, hz, hl₂⟩
    · exact Or.inr ⟨hx, hy, hl₁⟩
    · exact Or.inr ⟨hx, hz, hl₁.trans hl₂⟩

/-! ## Ids -/

theorem pred_ofId_id (p : Builtin.Pred) : Pred.ofId p.id = some p := by
  cases p <;> rfl

theorem rel_ofId_id (r : Builtin.Rel) : Builtin.Rel.ofId r.id = some r := by
  cases r <;> rfl

theorem rel_id_nonneg (r : Builtin.Rel) : 0 ≤ r.id := by
  cases r <;> decide

theorem rel_ofId_eq_some {i : Int} {r : Builtin.Rel} (h : Builtin.Rel.ofId i = some r) :
    r.id = i := by
  simpa using List.find?_some h

/-- The ids of the module's relations are no builtin's. -/
theorem rel_ofId_neg {i : Int} (h : i < 0) : Builtin.Rel.ofId i = none := by
  cases h' : Builtin.Rel.ofId i with
  | none => rfl
  | some r =>
    have := rel_ofId_eq_some h'
    have := rel_id_nonneg r
    omega

/-! ## Lists -/

theorem length_eraseDups_le {α : Type} [BEq α] : ∀ (l : List α), l.eraseDups.length ≤ l.length
  | [] => by simp
  | a :: as => by
    rw [List.eraseDups_cons, List.length_cons, List.length_cons]
    have := length_eraseDups_le (as.filter fun b => !b == a)
    have := List.length_filter_le (fun b => !b == a) as
    omega
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  have := List.length_filter_le (fun b => !b == a) as
  omega

/-- A list `eraseDups` keeps whole has no duplicates. -/
theorem nodup_of_length_eraseDups {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List α), l.eraseDups.length = l.length → l.Nodup
  | [] => fun _ => List.nodup_nil
  | a :: as => fun h => by
    rw [List.eraseDups_cons, List.length_cons, List.length_cons] at h
    have h₁ := length_eraseDups_le (as.filter fun b => !b == a)
    have h₂ := List.length_filter_le (fun b => !b == a) as
    have hf : (as.filter fun b => !b == a).length = as.length := by omega
    have hall := List.length_filter_eq_length_iff.mp hf
    have hfe : as.filter (fun b => !b == a) = as := List.filter_eq_self.mpr hall
    rw [List.nodup_cons]
    constructor
    · intro ha
      have := hall a ha
      simp at this
    · have := nodup_of_length_eraseDups (as.filter fun b => !b == a) (by omega)
      rwa [hfe] at this
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  have := List.length_filter_le (fun b => !b == a) as
  omega

theorem eq_of_nodup_map {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | c :: l, h, a, b, ha, hb, hab => by
    rw [List.map_cons, List.nodup_cons] at h
    rw [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd (hab ▸ List.mem_map_of_mem hb) h.1
    · exact absurd (hab ▸ List.mem_map_of_mem ha) h.1
    · exact eq_of_nodup_map h.2 ha hb hab

/-! ## The module's per-location variants -/

/-- What `Decls.wf` says of the per-location variants: they and their
relations are the module's, each variant is of one relation, and no variant
has one. -/
theorem wf_perLoc {d : Decls} (hwf : d.wf = true) :
    (∀ p ∈ d.perLoc, p.1 < 0 ∧ p.2 < 0) ∧
    (d.perLoc.map (·.2)).Nodup ∧
    (∀ p ∈ d.perLoc, ∀ q ∈ d.perLoc, q.1 ≠ p.2) := by
  simp only [Decls.wf, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hwf
  obtain ⟨⟨⟨h₁, _⟩, h₃⟩, h₄⟩ := hwf
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    have := h₁ p hp
    simp only [decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2⟩
  · apply nodup_of_length_eraseDups
    rw [h₃, List.length_map]
  · intro p hp q hq heq
    have := h₄ p hp
    simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at this
    exact this q hq heq

/-- A variant is found as the variant of its relation. -/
theorem find_variant {d : Decls} (hwf : d.wf = true) {b v : Int} (hmem : (b, v) ∈ d.perLoc) :
    d.perLoc.find? (·.2 == v) = some (b, v) := by
  obtain ⟨_, hnd, _⟩ := wf_perLoc hwf
  cases hf : d.perLoc.find? (·.2 == v) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact (hf _ hmem (by simp)).elim
  | some pr =>
    have h₁ := List.mem_of_find?_eq_some hf
    have h₂ : pr.2 = v := by simpa using List.find?_some hf
    rw [eq_of_nodup_map hnd h₁ hmem h₂]

/-- A relation with a variant is no variant. -/
theorem find_base {d : Decls} (hwf : d.wf = true) {b v : Int} (hmem : (b, v) ∈ d.perLoc) :
    d.perLoc.find? (·.2 == b) = none := by
  obtain ⟨_, _, hnb⟩ := wf_perLoc hwf
  rw [List.find?_eq_none]
  intro pr hpr heq
  have : pr.2 = b := by simpa using heq
  exact hnb pr hpr (b, v) hmem this.symm

/-! ## Builtin facts -/

theorem subPred_sound (hG : G.WF) {a b : Builtin.Pred} (h : subPred a b = true) {e : G.E}
    (ha : G.pred a e) : G.pred b e := by
  have hrel := hG.order_rel e
  have hacq := hG.order_acq e
  cases a <;> cases b <;> (try exact absurd h (by decide)) <;>
    simp only [Graph.pred, Graph.atLeastAcq, Graph.atLeastRel, Graph.isKind, Graph.dependable,
      Graph.hasLocation, Graph.located] at ha ⊢ <;>
    first
    | (simp [ha]; done)
    | (rcases ha with h | h | h <;> simp [h])
    | (simp [ha] at hrel hacq; simp [hrel, hacq])

/-- Kater's disjoint sets of builtin predicates are pairwise disjoint. -/
theorem disjoint_builtin (hG : G.WF) {D : List Builtin.Pred} (hD : D ∈ disjointSets)
    {a b : Builtin.Pred} (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b) (e : G.E) :
    ¬ (G.pred a e ∧ G.pred b e) := by
  intro ⟨h₁, h₂⟩
  have h₃ := hG.dependableOther_kind e
  have h₄ := hG.order_acq e
  have h₅ := hG.order_rel e
  simp only [disjointSets, List.mem_cons, List.not_mem_nil, or_false] at hD
  rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb <;>
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact hab rfl
    | simp_all [Graph.pred, Graph.atLeastAcq, Graph.atLeastRel, Graph.isKind, Graph.dependable,
        Graph.hasLocation, Graph.located]

theorem rf_sameLoc (hG : G.WF) {x y : G.E} (h : G.rf x y) : G.sameLoc x y :=
  have ⟨hx, hy, hl⟩ := hG.rf_kinds x y h
  Or.inr ⟨Or.inr hx, Or.inl hy, hl⟩

theorem mo_sameLoc (hG : G.WF) {x y : G.E} (h : G.mo x y) : G.sameLoc x y :=
  have ⟨hx, hy, hl⟩ := hG.mo_kinds x y h
  Or.inr ⟨Or.inr hx, Or.inr hy, hl⟩

theorem fr_sameLoc {x y : G.E} (h : G.fr x y) : G.sameLoc x y := h.2.2.2.1

/-- The builtin relations within a thread are within `po`. -/
theorem withinPo_po (hG : G.WF) {a : Builtin.Rel} (h : withinPo a = true) {x y : G.E}
    (hxy : G.rel a x y) : G.po x y := by
  cases a <;> (try exact absurd h (by decide)) <;> simp only [Graph.rel] at hxy
  case ctrl => exact (hG.ctrl_po x y hxy).1
  case addr => exact (hG.addr_po x y hxy).1
  case data => exact (hG.data_po x y hxy).1
  case pctrl => exact (hG.pctrl_po x y hxy).1
  case rfi =>
    obtain ⟨hrf, hth⟩ := hxy
    have ⟨hw, hr, _⟩ := hG.rf_kinds x y hrf
    have hne : x ≠ y := by
      intro h; subst h; rw [hw] at hr; cases hr
    exact (hG.po_total x y hth hne).resolve_right (hG.rf_po x y hrf)
  case moi =>
    obtain ⟨hmo, hth⟩ := hxy
    have hne : x ≠ y := by
      intro h; subst h; exact hG.mo_irrefl x hmo
    exact (hG.po_total x y hth hne).resolve_right (hG.mo_po x y hmo)
  case fri =>
    obtain ⟨hfr, hth⟩ := hxy
    exact (hG.po_total x y hth hfr.1).resolve_right (hG.fr_po x y hfr)
  case detour => exact hxy.2.2.1.1
  case rmw => exact hxy.1.1
  case po_loc_imm => exact hxy.1.1
  case po_loc => exact hxy.1
  case po_imm => exact hxy.1

/-- Those that keep the location are within `po_loc`. -/
theorem withinPo_poLoc (hG : G.WF) {a : Builtin.Rel} (h : withinPo a = true)
    (hk : keepsLocInfo a = true) {x y : G.E} (hxy : G.rel a x y) : G.poLoc x y := by
  refine ⟨withinPo_po hG h hxy, ?_⟩
  cases a <;> (try exact absurd h (by decide)) <;> (try exact absurd hk (by decide)) <;>
    simp only [Graph.rel] at hxy
  case rfi => exact rf_sameLoc hG hxy.1
  case moi => exact mo_sameLoc hG hxy.1
  case fri => exact fr_sameLoc hxy.1
  case detour => exact hxy.2.2.1.2
  case rmw => exact hxy.2.2.2.2.2
  case po_loc_imm => exact hxy.1.2
  case po_loc => exact hxy.2

theorem isEco_sameLoc (hG : G.WF) {a : Builtin.Rel} (h : isEco a = true) {x y : G.E}
    (hxy : G.rel a x y) : G.sameLoc x y := by
  cases a <;> (try exact absurd h (by decide)) <;> simp only [Graph.rel] at hxy
  case rf => exact rf_sameLoc hG hxy
  case mo_imm => exact mo_sameLoc hG hxy.1
  case mo => exact mo_sameLoc hG hxy
  case fr_imm => exact fr_sameLoc hxy.1
  case fr => exact fr_sameLoc hxy
  case rfe => exact rf_sameLoc hG hxy.1
  case moe => exact mo_sameLoc hG hxy.1
  case fre => exact fr_sameLoc hxy.1
  case rfi => exact rf_sameLoc hG hxy.1
  case moi => exact mo_sameLoc hG hxy.1
  case fri => exact fr_sameLoc hxy.1

theorem builtin_perLoc {b v : Builtin.Rel} (h : Builtin.perLoc b = some v) {x y : G.E}
    (hxy : G.rel b x y) (hl : G.sameLoc x y) : G.rel v x y := by
  cases b <;> simp only [Builtin.perLoc, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
    simp only [Graph.rel] at hxy ⊢
  case po_imm => exact ⟨⟨hxy.1, hl⟩, fun ⟨z, h₁, h₂, _⟩ => hxy.2 ⟨z, h₁, h₂⟩⟩
  case po => exact ⟨hxy, hl⟩

/-- The inclusions between builtin relations `Theory.ofDecls` states. -/
theorem builtin_relIncl (hG : G.WF) {a b : Builtin.Rel}
    (h : ((Builtin.perLoc b == some a && b != .po_imm) || Builtin.relIncl a b) = true)
    {x y : G.E} (hxy : G.rel a x y) : G.rel b x y := by
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    Builtin.relIncl] at h
  rcases h with ⟨hp, hne⟩ | ((((((rfl | rfl) | ⟨rfl, rfl | rfl⟩) | ⟨rfl, (rfl | rfl) | rfl⟩) |
    ⟨rfl, (rfl | rfl) | rfl⟩) | ⟨rfl, hw⟩) | ⟨⟨rfl, hw⟩, hk⟩)
  · cases b <;> simp only [Builtin.perLoc, reduceCtorEq, Option.some.injEq] at hp
    · exact absurd rfl hne
    · subst hp; exact hxy.1
  · exact hxy
  · trivial
  · exact hxy.1
  · exact hxy.1
  · exact hxy.1
  · exact hxy.1
  · exact hxy.1
  · exact hxy.1
  · exact hxy.1
  · exact hxy.1
  · exact withinPo_po hG hw hxy
  · exact withinPo_poLoc hG hw hk hxy

theorem builtin_dom (hG : G.WF) {b : Builtin.Rel} {q : Builtin.Pred} (hq : q ∈ (domains b).1)
    {x y : G.E} (hxy : G.rel b x y) : G.pred q x := by
  cases b <;> simp only [domains, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
    simp only [Graph.rel] at hxy
  case rmw =>
    rcases hq with rfl | rfl
    · exact hxy.2.1
    · exact hxy.2.2.1
  case ctrl => subst hq; exact (hG.ctrl_po x y hxy).2
  case addr => subst hq; exact (hG.addr_po x y hxy).2
  case data => subst hq; exact (hG.data_po x y hxy).2
  case pctrl => subst hq; exact (hG.pctrl_po x y hxy).2
  case alloc => subst hq; exact hxy.2.1
  case free => subst hq; exact hxy.2
  case retire => subst hq; exact hxy.2
  case tc => subst hq; exact (hG.tc_kinds x y hxy).1
  case tj => subst hq; exact (hG.tj_kinds x y hxy).1
  case lin => subst hq; exact (hG.lin_kinds x y hxy).1
  case rf => subst hq; exact (hG.rf_kinds x y hxy).1
  case mo_imm => subst hq; exact (hG.mo_kinds x y hxy.1).1
  case mo => subst hq; exact (hG.mo_kinds x y hxy).1
  case fr_imm => subst hq; exact hxy.1.2.1
  case fr => subst hq; exact hxy.2.1
  case rfe => subst hq; exact (hG.rf_kinds x y hxy.1).1
  case moe => subst hq; exact (hG.mo_kinds x y hxy.1).1
  case fre => subst hq; exact hxy.1.2.1
  case rfi => subst hq; exact (hG.rf_kinds x y hxy.1).1
  case moi => subst hq; exact (hG.mo_kinds x y hxy.1).1
  case fri => subst hq; exact hxy.1.2.1
  case detour => subst hq; exact hxy.1

theorem builtin_codom (hG : G.WF) {b : Builtin.Rel} {q : Builtin.Pred} (hq : q ∈ (domains b).2)
    {x y : G.E} (hxy : G.rel b x y) : G.pred q y := by
  cases b <;> simp only [domains, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
    simp only [Graph.rel] at hxy
  case rmw =>
    rcases hq with rfl | rfl
    · exact hxy.2.2.2.1
    · exact hxy.2.2.2.2.1
  case tc => subst hq; exact (hG.tc_kinds x y hxy).2
  case tj => subst hq; exact (hG.tj_kinds x y hxy).2
  case lin => subst hq; exact (hG.lin_kinds x y hxy).2
  case rf => subst hq; exact (hG.rf_kinds x y hxy).2.1
  case mo_imm => subst hq; exact (hG.mo_kinds x y hxy.1).2.1
  case mo => subst hq; exact (hG.mo_kinds x y hxy).2.1
  case fr_imm => subst hq; exact hxy.1.2.2.1
  case fr => subst hq; exact hxy.2.2.1
  case rfe => subst hq; exact (hG.rf_kinds x y hxy.1).2.1
  case moe => subst hq; exact (hG.mo_kinds x y hxy.1).2.1
  case fre => subst hq; exact hxy.1.2.2.1
  case rfi => subst hq; exact (hG.rf_kinds x y hxy.1).2.1
  case moi => subst hq; exact (hG.mo_kinds x y hxy.1).2.1
  case fri => subst hq; exact hxy.1.2.2.1
  case detour => subst hq; exact hxy.2.1

/-! ## Inverses -/

theorem denote_cases {E : Type} {M : Interp E} {r : Relation} {x y : E} (h : r.denote M x y) :
    (r.inverse = false ∧ M.rel r.id x y) ∨ (r.inverse = true ∧ M.rel r.id y x) := by
  unfold Relation.denote at h
  cases hi : r.inverse <;> simp only [hi, Bool.false_eq_true, ↓reduceIte] at h <;> simp [h]

theorem denote_of {E : Type} {M : Interp E} {r : Relation} {x y : E}
    (h : (r.inverse = false ∧ M.rel r.id x y) ∨ (r.inverse = true ∧ M.rel r.id y x)) :
    r.denote M x y := by
  unfold Relation.denote
  rcases h with ⟨hi, h⟩ | ⟨hi, h⟩ <;> simp only [hi, Bool.false_eq_true, ↓reduceIte] <;> exact h

theorem denote_sub {E : Type} {M : Interp E} {r s : Relation} (hinv : r.inverse = s.inverse)
    (h : ∀ x y, M.rel r.id x y → M.rel s.id x y) : Rel.Sub (r.denote M) (s.denote M) := by
  intro x y hxy
  apply denote_of
  rw [← hinv]
  rcases denote_cases hxy with ⟨hi, hxy⟩ | ⟨hi, hxy⟩
  · exact Or.inl ⟨hi, h _ _ hxy⟩
  · exact Or.inr ⟨hi, h _ _ hxy⟩

/-! ## What the ids mean -/

section Interp

variable {U : Graph.User G.E} {perLoc : List (Int × Int)}

theorem interp_pred_of {i : Int} {p : Builtin.Pred} (h : Pred.ofId i = some p) :
    (G.interp U perLoc).pred i = G.pred p := by
  simp only [Graph.interp, h]

theorem interp_rel_of {i : Int} {r : Builtin.Rel} (h : Builtin.Rel.ofId i = some r) :
    (G.interp U perLoc).rel i = G.rel r := by
  simp only [Graph.interp, h]

theorem interp_pred (p : Builtin.Pred) : (G.interp U perLoc).pred p.id = G.pred p :=
  interp_pred_of (pred_ofId_id p)

theorem interp_rel (r : Builtin.Rel) : (G.interp U perLoc).rel r.id = G.rel r :=
  interp_rel_of (rel_ofId_id r)

theorem bare_denote (r : Builtin.Rel) {x y : G.E} :
    (bare r).denote (G.interp U perLoc) x y ↔ G.rel r x y := by
  simp [bare, Exp.denote, Label.denote, Checks, Relation.denote, interp_rel]

/-- A variant is its relation on the same location. -/
theorem interp_variant {d : Decls} (hwf : d.wf = true) {b v : Int} (hmem : (b, v) ∈ d.perLoc) :
    (G.interp U d.perLoc).rel v = fun x y => U.rel b x y ∧ G.sameLoc x y := by
  have hv : v < 0 := ((wf_perLoc hwf).1 _ hmem).2
  simp only [Graph.interp, rel_ofId_neg hv, hv, find_variant hwf hmem, ↓reduceIte]

/-- A relation with a variant is the module's relation. -/
theorem interp_base {d : Decls} (hwf : d.wf = true) {b v : Int} (hmem : (b, v) ∈ d.perLoc) :
    (G.interp U d.perLoc).rel b = U.rel b := by
  have hb : b < 0 := ((wf_perLoc hwf).1 _ hmem).1
  simp only [Graph.interp, rel_ofId_neg hb, hb, find_base hwf hmem, ↓reduceIte]

/-! ## The facts of the theory, one by one -/

theorem subPredId_sound (hG : G.WF) {p q : Int} (h : Theory.subPredId p q = true) {e : G.E}
    (hp : (G.interp U perLoc).pred p e) : (G.interp U perLoc).pred q e := by
  unfold Theory.subPredId at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · exact hp
  · cases hpa : Pred.ofId p with
    | none => simp [hpa] at h
    | some a =>
      cases hqb : Pred.ofId q with
      | none => simp [hpa, hqb] at h
      | some b =>
        simp only [hpa, hqb] at h
        rw [interp_pred_of hpa] at hp
        rw [interp_pred_of hqb]
        exact subPred_sound hG h hp

theorem predIncl_sound (hG : G.WF) (d : Decls) (p q : Predicate)
    (h : (Theory.ofDecls d).predIncl p q = true) (e : G.E)
    (hp : p.Holds (G.interp U perLoc) e) : q.Holds (G.interp U perLoc) e := by
  simp only [Theory.ofDecls, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at h
  rcases h with (rfl | ⟨⟨hpc, hqc⟩, hs⟩) | ⟨⟨hpc, hqc⟩, hs⟩
  · exact hp
  · simp only [Predicate.Holds, hpc, hqc, Bool.false_eq_true, ↓reduceIte] at hp ⊢
    exact subPredId_sound hG hs hp
  · simp only [Predicate.Holds, hpc, hqc, ↓reduceIte] at hp ⊢
    exact fun hq => hp (subPredId_sound hG hs hq)

theorem unsat_sound (hG : G.WF) (d : Decls) (hd : d.Hold (G.interp U perLoc))
    (ps : List Predicate) (h : (Theory.ofDecls d).unsat ps = true) (e : G.E) :
    ¬ Checks (G.interp U perLoc) ps e := by
  intro hc
  simp only [Theory.ofDecls, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true,
    List.all_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true', List.mem_append,
    List.mem_map] at h
  rcases h with (⟨p, hp, q, hq, hid, hcomp⟩ |
      ⟨D, hD, p, hp, q, hq, ⟨⟨hpc, hqc⟩, _⟩, a, ha, b, hb, ⟨hab, hpa⟩, hqb⟩) | ⟨I, hI, hall⟩
  · -- a predicate and its complement
    have h₁ := hc p hp
    have h₂ := hc q hq
    simp only [Predicate.Holds] at h₁ h₂
    rw [hid] at h₁
    cases hpc : p.complement <;> cases hqc : q.complement <;> simp_all
  · -- two predicates below two of a disjoint set
    have h₁ := hc p hp
    have h₂ := hc q hq
    simp only [Predicate.Holds, hpc, hqc, Bool.false_eq_true, ↓reduceIte] at h₁ h₂
    have ha' := subPredId_sound hG hpa h₁
    have hb' := subPredId_sound hG hqb h₂
    rcases hD with hD | ⟨D', hD', rfl⟩
    · exact hd.1 D hD a ha b hb hab e ⟨ha', hb'⟩
    · obtain ⟨a', ha'', rfl⟩ := List.mem_map.mp ha
      obtain ⟨b', hb'', rfl⟩ := List.mem_map.mp hb
      rw [interp_pred] at ha' hb'
      exact disjoint_builtin hG hD' ha'' hb'' (fun h => hab (h ▸ rfl)) e ⟨ha', hb'⟩
  · -- an invalid set
    apply hd.2.1 I hI e
    intro i hi
    obtain ⟨p, hp, hpc, rfl⟩ := hall i hi
    have := hc p hp
    simpa [Predicate.Holds, hpc] using this

theorem relIncl_sound (hG : G.WF) (d : Decls) (hwf : d.wf = true) (r s : Relation)
    (h : (Theory.ofDecls d).relIncl r s = true) :
    Rel.Sub (r.denote (G.interp U d.perLoc)) (s.denote (G.interp U d.perLoc)) := by
  simp only [Theory.ofDecls, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    List.any_eq_true] at h
  rcases h with (rfl | hany) | ⟨hinv, ⟨⟨b, v⟩, hmem, hb, hv⟩ | hbi⟩
  · exact Rel.Sub.refl _
  · -- `any`
    intro x y _
    cases hs : Builtin.Rel.ofId s.id with
    | none => simp [hs] at hany
    | some c =>
      cases c <;> simp only [hs, Bool.false_eq_true] at hany
      unfold Relation.denote
      rw [interp_rel_of hs]
      split <;> trivial
  · -- a variant of the module's in its relation
    simp only at hb hv
    subst hb hv
    apply denote_sub hinv
    intro x y hxy
    rw [interp_variant hwf hmem] at hxy
    rw [interp_base hwf hmem]
    exact hxy.1
  · -- builtins
    cases ha : Builtin.Rel.ofId r.id with
    | none => simp [ha] at hbi
    | some a =>
      cases hb : Builtin.Rel.ofId s.id with
      | none => simp [ha, hb] at hbi
      | some b =>
        simp only [ha, hb] at hbi
        apply denote_sub hinv
        intro x y hxy
        rw [interp_rel_of ha] at hxy
        rw [interp_rel_of hb]
        exact builtin_relIncl hG hbi hxy

theorem dom_sound (hG : G.WF) (d : Decls) (hd : d.Hold (G.interp U perLoc)) (r : Relation)
    (p : Predicate) (hp : p ∈ (Theory.ofDecls d).dom r) (x y : G.E)
    (hxy : r.denote (G.interp U perLoc) x y) : p.Holds (G.interp U perLoc) x := by
  simp only [Theory.ofDecls] at hp
  cases hr : Builtin.Rel.ofId r.id with
  | some b =>
    simp only [hr] at hp
    rcases denote_cases hxy with ⟨hi, hxy⟩ | ⟨hi, hxy⟩ <;>
      simp only [hi, Bool.false_eq_true, ↓reduceIte, List.mem_map] at hp <;>
      obtain ⟨q, hq, rfl⟩ := hp <;>
      rw [interp_rel_of hr] at hxy <;>
      simp only [Theory.plain, Predicate.Holds, Bool.false_eq_true, ↓reduceIte, interp_pred]
    · exact builtin_dom hG hq hxy
    · exact builtin_codom hG hq hxy
  | none =>
    simp only [hr] at hp
    rcases denote_cases hxy with ⟨hi, hxy⟩ | ⟨hi, hxy⟩ <;>
      simp only [hi, Bool.false_eq_true, ↓reduceIte, List.mem_flatten, List.mem_filterMap,
        beq_iff_eq, Option.ite_none_right_eq_some, Option.some.injEq] at hp <;>
      obtain ⟨l, ⟨t, ht, hti, rfl⟩, hpl⟩ := hp
    · exact (hd.2.2 t ht x y (by rw [hti]; exact hxy)).1 p hpl
    · exact (hd.2.2 t ht y x (by rw [hti]; exact hxy)).2 p hpl

theorem codom_sound (hG : G.WF) (d : Decls) (hd : d.Hold (G.interp U perLoc)) (r : Relation)
    (p : Predicate) (hp : p ∈ (Theory.ofDecls d).codom r) (x y : G.E)
    (hxy : r.denote (G.interp U perLoc) x y) : p.Holds (G.interp U perLoc) y := by
  simp only [Theory.ofDecls] at hp
  cases hr : Builtin.Rel.ofId r.id with
  | some b =>
    simp only [hr] at hp
    rcases denote_cases hxy with ⟨hi, hxy⟩ | ⟨hi, hxy⟩ <;>
      simp only [hi, Bool.false_eq_true, ↓reduceIte, List.mem_map] at hp <;>
      obtain ⟨q, hq, rfl⟩ := hp <;>
      rw [interp_rel_of hr] at hxy <;>
      simp only [Theory.plain, Predicate.Holds, Bool.false_eq_true, ↓reduceIte, interp_pred]
    · exact builtin_codom hG hq hxy
    · exact builtin_dom hG hq hxy
  | none =>
    simp only [hr] at hp
    rcases denote_cases hxy with ⟨hi, hxy⟩ | ⟨hi, hxy⟩ <;>
      simp only [hi, Bool.false_eq_true, ↓reduceIte, List.mem_flatten, List.mem_filterMap,
        beq_iff_eq, Option.ite_none_right_eq_some, Option.some.injEq] at hp <;>
      obtain ⟨l, ⟨t, ht, hti, rfl⟩, hpl⟩ := hp
    · exact (hd.2.2 t ht x y (by rw [hti]; exact hxy)).2 p hpl
    · exact (hd.2.2 t ht y x (by rw [hti]; exact hxy)).1 p hpl

theorem perLoc_sound (d : Decls) (hwf : d.wf = true) (r r' : Relation)
    (h : (Theory.ofDecls d).perLoc r = some r') (x y : G.E)
    (hxy : r.denote (G.interp U d.perLoc) x y) (hl : G.sameLoc x y) :
    r'.denote (G.interp U d.perLoc) x y := by
  simp only [Theory.ofDecls] at h
  cases hr : Builtin.Rel.ofId r.id with
  | some b =>
    simp only [hr] at h
    cases hb : Builtin.perLoc b with
    | none => simp [hb] at h
    | some v =>
      simp only [hb, Option.map_some, Option.some.injEq] at h
      subst h
      apply denote_of
      rcases denote_cases hxy with ⟨hi, hxy⟩ | ⟨hi, hxy⟩ <;> rw [interp_rel_of hr] at hxy <;>
        simp only [interp_rel]
      · exact Or.inl ⟨hi, builtin_perLoc hb hxy hl⟩
      · exact Or.inr ⟨hi, builtin_perLoc hb hxy (sameLoc_symm hl)⟩
  | none =>
    simp only [hr] at h
    cases hf : d.perLoc.find? (·.1 == r.id) with
    | none => simp [hf] at h
    | some pr =>
      obtain ⟨b, v⟩ := pr
      simp only [hf, Option.map_some, Option.some.injEq] at h
      subst h
      have hmem := List.mem_of_find?_eq_some hf
      have hb : b = r.id := by simpa using List.find?_some hf
      subst hb
      apply denote_of
      rcases denote_cases hxy with ⟨hi, hxy⟩ | ⟨hi, hxy⟩ <;> rw [interp_base hwf hmem] at hxy <;>
        simp only [interp_variant hwf hmem]
      · exact Or.inl ⟨hi, hxy, hl⟩
      · exact Or.inr ⟨hi, hxy, sameLoc_symm hl⟩

theorem keepsLoc_sound (hG : G.WF) (d : Decls) (r : Relation)
    (h : (Theory.ofDecls d).keepsLoc r = true) (x y : G.E)
    (hxy : r.denote (G.interp U perLoc) x y) : G.sameLoc x y := by
  simp only [Theory.ofDecls] at h
  cases hr : Builtin.Rel.ofId r.id with
  | none => simp [hr] at h
  | some b =>
    simp only [hr] at h
    rcases denote_cases hxy with ⟨_, hxy⟩ | ⟨_, hxy⟩ <;> rw [interp_rel_of hr] at hxy
    · exact isEco_sameLoc hG h hxy
    · exact sameLoc_symm (isEco_sameLoc hG h hxy)

theorem reflexive_sound (d : Decls) (r : Relation)
    (h : (Theory.ofDecls d).reflexive r = true) (x : G.E) :
    r.denote (G.interp U perLoc) x x := by
  simp only [Theory.ofDecls] at h
  cases hr : Builtin.Rel.ofId r.id with
  | none => simp [hr] at h
  | some b =>
    cases b <;> simp only [hr, Bool.false_eq_true] at h
    unfold Relation.denote
    rw [interp_rel_of hr]
    split <;> trivial

end Interp

/-- **The theory is sound** in every graph whose module declarations hold. -/
theorem theory_sound (hG : G.WF) (U : Graph.User G.E) (d : Decls) (hwf : d.wf = true)
    (hd : d.Hold (G.interp U d.perLoc)) :
    (Theory.ofDecls d).Sound (G.interp U d.perLoc) G.sameLoc where
  predIncl := predIncl_sound hG d
  unsat := unsat_sound hG d hd
  relIncl := relIncl_sound hG d hwf
  dom := dom_sound hG d hd
  codom := codom_sound hG d hd
  loc_refl := sameLoc_refl
  loc_symm := fun _ _ => sameLoc_symm
  loc_trans := fun _ _ _ => sameLoc_trans
  perLoc := perLoc_sound d hwf
  keepsLoc := keepsLoc_sound hG d
  reflexive := reflexive_sound d

/-- The builtin assumptions hold in every graph. -/
theorem builtinAssumptions_hold (hG : G.WF) (U : Graph.User G.E) (perLoc : List (Int × Int)) :
    ∀ c ∈ builtinAssumptions, c.Holds (G.interp U perLoc) := by
  intro c hc
  simp only [builtinAssumptions, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;>
    simp only [Constraint.Holds, Constraint.SubsetHolds, Bool.false_eq_true, ↓reduceIte] <;>
    intro x z ⟨y, h₁, h₂⟩ <;>
    rw [bare_denote] at h₁ h₂ ⊢ <;> simp only [Graph.rel] at h₁ h₂ ⊢
  · -- `fr;mo <= fr`
    obtain ⟨hne, hr, _, hloc, hsrc⟩ := h₁
    obtain ⟨_, hz, hl⟩ := hG.mo_kinds y z h₂
    refine ⟨?_, hr, hz, ?_, ?_⟩
    · intro h; subst h; rw [hr] at hz; cases hz
    · rcases hloc with rfl | ⟨hlx, _, hl'⟩
      · exact absurd rfl hne
      · exact Or.inr ⟨hlx, Or.inr hz, hl'.trans hl⟩
    · rcases hsrc with hi | ⟨s, hs, hm⟩
      · exact Or.inl hi
      · exact Or.inr ⟨s, hs, hG.mo_trans _ _ _ hm h₂⟩
  · -- `po;po <= po`
    exact hG.po_trans _ _ _ h₁ h₂
  · -- `mo;mo <= mo`
    exact hG.mo_trans _ _ _ h₁ h₂
  · -- `rf;fr <= mo`
    obtain ⟨_, _, _, _, hsrc⟩ := h₂
    rcases hsrc with hi | ⟨s, hs, hm⟩
    · exact absurd ⟨x, h₁⟩ hi
    · rw [hG.rf_unique _ _ _ h₁ hs]; exact hm

/-- `rf` is `rfe | rfi`. -/
theorem rf_split (U : Graph.User G.E) (perLoc : List (Int × Int)) (x y : G.E) :
    (G.interp U perLoc).rel Builtin.Rel.rf.id x y ↔
      (G.interp U perLoc).rel Builtin.Rel.rfe.id x y ∨
        (G.interp U perLoc).rel Builtin.Rel.rfi.id x y := by
  simp only [interp_rel, Graph.rel, Graph.external, Graph.internal]
  by_cases h : G.sameThread x y <;> simp [h]

end Model

end KaterCert

/--
info: 'KaterCert.Model.theory_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms KaterCert.Model.theory_sound

/--
info: 'KaterCert.Model.builtinAssumptions_hold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms KaterCert.Model.builtinAssumptions_hold

/--
info: 'KaterCert.Model.rf_split' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms KaterCert.Model.rf_split
