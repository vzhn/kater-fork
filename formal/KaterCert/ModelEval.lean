import KaterCert.Model

/-!
# The model on finite graphs

A finite graph of the model, its events `Fin n` and its attributes data
(`Finite`), and its builtins and axioms decided on it: the differential test
against the oracle (`kater-model-check`, `ModelMain.lean`) compares the
oracle's meaning of each builtin with `Finite.pred` and `Finite.rel` on the
graphs it enumerates, and checks `Finite.wf` of each.

The decisions are the model's definitions themselves, made decidable, so
`pred_iff`, `rel_iff` and `interp_pred` / `interp_rel` say they mean what
`Model.lean` does, and `wf_sound` that a graph `Finite.wf` accepts satisfies
`Graph.WF`.

`po` is not data: events are numbered thread by thread in program order, as
the oracle numbers them, so it is forward in a thread. `si`, `loc-overlap`,
`LK` and `UL`, which the oracle gives no meaning, hold of nothing.
-/

namespace KaterCert

namespace Model

/-- A finite execution graph, as the oracle writes one. -/
structure Finite where
  n : Nat
  kind : Fin n → Kind
  order : Fin n → Order
  excl : Fin n → Bool
  loc : Fin n → Nat
  thread : Fin n → Nat
  hp : Fin n → Nat
  rf : Fin n → Fin n → Bool
  mo : Fin n → Fin n → Bool
  ctrl : Fin n → Fin n → Bool
  addr : Fin n → Fin n → Bool
  data : Fin n → Fin n → Bool
  pctrl : Fin n → Fin n → Bool
  tc : Fin n → Fin n → Bool
  tj : Fin n → Fin n → Bool
  lin : Fin n → Fin n → Bool
  added : Fin n → Fin n → Bool
  hb : Fin n → Fin n → Bool
  durable : Fin n → Bool
  recovery : Fin n → Bool
  abstractLock : Fin n → Bool
  dependableOther : Fin n → Bool

namespace Finite

/-- The graph of the model it is. -/
@[reducible] def graph (g : Finite) : Graph where
  E := Fin g.n
  kind := g.kind
  order := g.order
  excl e := g.excl e = true
  loc := g.loc
  thread := g.thread
  po x y := x < y ∧ g.thread x = g.thread y
  rf x y := g.rf x y = true
  mo x y := g.mo x y = true
  ctrl x y := g.ctrl x y = true
  addr x y := g.addr x y = true
  data x y := g.data x y = true
  pctrl x y := g.pctrl x y = true
  tc x y := g.tc x y = true
  tj x y := g.tj x y = true
  lin x y := g.lin x y = true
  hp := g.hp
  added x y := g.added x y = true
  hb x y := g.hb x y = true
  durable e := g.durable e = true
  recovery e := g.recovery e = true
  abstractLock e := g.abstractLock e = true
  dependableOther e := g.dependableOther e = true
  si _ _ := False
  locOverlap _ _ := False
  lk _ := False
  ul _ := False

variable (g : Finite)

/-! The events are `Fin g.n`, under the graph's name for them. -/
instance : DecidableEq g.graph.E := inferInstanceAs (DecidableEq (Fin g.n))

instance decExists (P : g.graph.E → Prop) [DecidablePred P] : Decidable (∃ x, P x) :=
  inferInstanceAs (Decidable (∃ x : Fin g.n, P x))

instance decForall (P : g.graph.E → Prop) [DecidablePred P] : Decidable (∀ x, P x) :=
  inferInstanceAs (Decidable (∀ x : Fin g.n, P x))

section
open Graph

/-! Each definition of the model decided, from the decisions of those it uses. -/
instance : DecidablePred g.graph.located := fun _ => by dsimp only [located]; exact inferInstance
instance : DecidablePred g.graph.hasLocation := fun _ => by
  dsimp only [hasLocation]; exact inferInstance
instance : DecidableRel g.graph.sameLoc := fun _ _ => by dsimp only [sameLoc]; exact inferInstance
instance : DecidableRel g.graph.sameBlock := fun _ _ => by
  dsimp only [sameBlock]; exact inferInstance
instance : DecidableRel g.graph.sameThread := fun _ _ => by
  dsimp only [sameThread]; exact inferInstance
instance : DecidablePred g.graph.dependable := fun _ => by
  dsimp only [dependable]; exact inferInstance
instance : DecidablePred g.graph.atLeastAcq := fun _ => by
  dsimp only [atLeastAcq]; exact inferInstance
instance : DecidablePred g.graph.atLeastRel := fun _ => by
  dsimp only [atLeastRel]; exact inferInstance
instance : DecidableRel g.graph.poImm := fun _ _ => by dsimp only [poImm]; exact inferInstance
instance : DecidableRel g.graph.poLoc := fun _ _ => by dsimp only [poLoc]; exact inferInstance
instance : DecidableRel g.graph.poLocImm := fun _ _ => by
  dsimp only [poLocImm]; exact inferInstance
instance : DecidablePred g.graph.readsInit := fun _ => by
  dsimp only [readsInit]; exact inferInstance
instance : DecidableRel g.graph.fr := fun _ _ => by dsimp only [fr]; exact inferInstance
instance : DecidableRel g.graph.moImm := fun _ _ => by dsimp only [moImm]; exact inferInstance
instance : DecidableRel g.graph.frImm := fun _ _ => by dsimp only [frImm]; exact inferInstance
instance : DecidableRel g.graph.rmw := fun _ _ => by dsimp only [rmw]; exact inferInstance
instance : DecidableRel g.graph.detour := fun _ _ => by dsimp only [detour]; exact inferInstance
instance (r : g.graph.E → g.graph.E → Prop) [DecidableRel r] :
    DecidableRel (g.graph.external r) := fun _ _ => by
  dsimp only [external]; exact inferInstance
instance (r : g.graph.E → g.graph.E → Prop) [DecidableRel r] :
    DecidableRel (g.graph.internal r) := fun _ _ => by
  dsimp only [internal]; exact inferInstance
instance : DecidablePred g.graph.heap := fun _ => by dsimp only [heap]; exact inferInstance
instance : DecidablePred g.graph.memLabel := fun _ => by
  dsimp only [memLabel]; exact inferInstance
instance : DecidableRel g.graph.sameHp := fun _ _ => by dsimp only [sameHp]; exact inferInstance
instance : DecidablePred g.graph.hpProtected := fun _ => by
  dsimp only [hpProtected]; exact inferInstance
instance : DecidablePred g.graph.freeing := fun _ => by dsimp only [freeing]; exact inferInstance
instance : DecidableRel g.graph.lastFreeing := fun _ _ => by
  dsimp only [lastFreeing]; exact inferInstance
instance : DecidableRel g.graph.allocRel := fun _ _ => by
  dsimp only [allocRel]; exact inferInstance
instance : DecidableRel g.graph.freeRel := fun _ _ => by dsimp only [freeRel]; exact inferInstance
instance : DecidableRel g.graph.retireRel := fun _ _ => by
  dsimp only [retireRel]; exact inferInstance
instance : DecidablePred g.graph.protectedWhenAdded := fun _ => by
  dsimp only [protectedWhenAdded]; exact inferInstance
instance : DecidablePred g.graph.access := fun _ => by dsimp only [access]; exact inferInstance
instance : DecidablePred g.graph.lifecycle := fun _ => by
  dsimp only [lifecycle]; exact inferInstance
instance (recorded asks : g.graph.E → Prop) [DecidablePred recorded] [DecidablePred asks]
    (byHb : Bool) : DecidableRel (g.graph.positional recorded asks byHb) := fun _ _ => by
  dsimp only [positional]; exact inferInstance

instance decPred (p : Builtin.Pred) : DecidablePred (g.graph.pred p) := fun _ => by
  cases p <;> dsimp only [Graph.pred, isKind] <;> exact inferInstance

instance decRel (r : Builtin.Rel) : DecidableRel (g.graph.rel r) := fun _ _ => by
  cases r <;> dsimp only [Graph.rel] <;> exact inferInstance

end

/-- Whether builtin predicate `p` holds at event `e`. -/
def pred (p : Builtin.Pred) (e : Fin g.n) : Bool := decide (g.graph.pred p e)

/-- Whether builtin relation `r` relates `x` to `y`. -/
def rel (r : Builtin.Rel) (x y : Fin g.n) : Bool := decide (g.graph.rel r x y)

theorem pred_iff (p : Builtin.Pred) (e : Fin g.n) : g.pred p e = true ↔ g.graph.pred p e :=
  decide_eq_true_iff

theorem rel_iff (r : Builtin.Rel) (x y : Fin g.n) : g.rel r x y = true ↔ g.graph.rel r x y :=
  decide_eq_true_iff

theorem Pred.ofId_id (p : Builtin.Pred) : Builtin.Pred.ofId p.id = some p := by
  cases p <;> rfl

theorem Rel.ofId_id (r : Builtin.Rel) : Builtin.Rel.ofId r.id = some r := by
  cases r <;> rfl

/-- The id of a builtin means the builtin, whatever the module's own
predicates and relations: the meaning `Graph.interp` gives letters. -/
theorem interp_pred (U : Graph.User g.graph.E) (perLoc : List (Int × Int))
    (p : Builtin.Pred) (e : Fin g.n) :
    g.pred p e = true ↔ (g.graph.interp U perLoc).pred p.id e := by
  simp only [Graph.interp, Pred.ofId_id, pred_iff]

theorem interp_rel (U : Graph.User g.graph.E) (perLoc : List (Int × Int))
    (r : Builtin.Rel) (x y : Fin g.n) :
    g.rel r x y = true ↔ (g.graph.interp U perLoc).rel r.id x y := by
  simp only [Graph.interp, Rel.ofId_id, rel_iff]

/-! ## The axioms -/

section
open Graph
variable {g}

/-- The axioms of `Graph.WF`, one by one, decided: each with its name. -/
def wfChecks (g : Finite) : List (String × Bool) :=
  let G := g.graph
  [("order_rel", decide (∀ e : G.E, G.kind e = .TC ∨ G.kind e = .TE ∨ G.kind e = .HPPROTECT →
      G.order e = .REL)),
   ("order_acq", decide (∀ e : G.E, G.kind e = .TB ∨ G.kind e = .TJ → G.order e = .ACQ)),
   ("po_trans", decide (∀ x y z : G.E, G.po x y → G.po y z → G.po x z)),
   ("po_total", decide (∀ x y : G.E, G.thread x = G.thread y → x ≠ y → G.po x y ∨ G.po y x)),
   ("rf_kinds", decide (∀ w r : G.E, G.rf w r →
      G.kind w = .W ∧ G.kind r = .R ∧ G.loc w = G.loc r)),
   ("rf_unique", decide (∀ w w' r : G.E, G.rf w r → G.rf w' r → w = w')),
   ("mo_kinds", decide (∀ x y : G.E, G.mo x y →
      G.kind x = .W ∧ G.kind y = .W ∧ G.loc x = G.loc y)),
   ("mo_irrefl", decide (∀ x : G.E, ¬ G.mo x x)),
   ("mo_trans", decide (∀ x y z : G.E, G.mo x y → G.mo y z → G.mo x z)),
   ("rf_po", decide (∀ x y : G.E, G.rf x y → ¬ G.po y x)),
   ("mo_po", decide (∀ x y : G.E, G.mo x y → ¬ G.po y x)),
   ("fr_po", decide (∀ x y : G.E, g.rel .fr x y = true → ¬ G.po y x)),
   ("ctrl_po", decide (∀ x y : G.E, G.ctrl x y → G.po x y ∧ g.pred .DEP x = true)),
   ("addr_po", decide (∀ x y : G.E, G.addr x y → G.po x y ∧ g.pred .DEP x = true)),
   ("data_po", decide (∀ x y : G.E, G.data x y → G.po x y ∧ g.pred .DEP x = true)),
   ("pctrl_po", decide (∀ x y : G.E, G.pctrl x y → G.po x y ∧ g.pred .DEP x = true)),
   ("dependableOther_kind", decide (∀ e : G.E, G.dependableOther e → G.kind e = .OTHER)),
   ("tc_kinds", decide (∀ x y : G.E, G.tc x y → G.kind x = .TC ∧ G.kind y = .TB)),
   ("tj_kinds", decide (∀ x y : G.E, G.tj x y → G.kind x = .TE ∧ G.kind y = .TJ)),
   ("lin_kinds", decide (∀ x y : G.E, G.lin x y → G.kind x = .ME ∧ G.kind y = .MB))]

/-- Whether the graph satisfies `Graph.WF`. -/
def wf (g : Finite) : Bool := (wfChecks g).all (·.2)

theorem wf_sound (h : g.wf = true) : g.graph.WF := by
  simp only [wf, wfChecks, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20⟩ := h
  exact
    { order_rel := h1, order_acq := h2, po_trans := h3, po_total := h4, rf_kinds := h5
      rf_unique := h6, mo_kinds := h7, mo_irrefl := h8, mo_trans := h9, rf_po := h10
      mo_po := h11
      fr_po := fun x y hxy => h12 x y ((rel_iff g .fr x y).2 hxy)
      ctrl_po := fun x y hxy => (h13 x y hxy).imp_right (pred_iff g .DEP x).1
      addr_po := fun x y hxy => (h14 x y hxy).imp_right (pred_iff g .DEP x).1
      data_po := fun x y hxy => (h15 x y hxy).imp_right (pred_iff g .DEP x).1
      pctrl_po := fun x y hxy => (h16 x y hxy).imp_right (pred_iff g .DEP x).1
      dependableOther_kind := h17, tc_kinds := h18, tj_kinds := h19, lin_kinds := h20 }

end

end Finite

end Model

end KaterCert

/-! The build checks that the evaluation rests on Lean's standard axioms only. -/

/--
info: 'KaterCert.Model.Finite.wf_sound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms KaterCert.Model.Finite.wf_sound

/--
info: 'KaterCert.Model.Finite.interp_pred' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms KaterCert.Model.Finite.interp_pred

/--
info: 'KaterCert.Model.Finite.interp_rel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms KaterCert.Model.Finite.interp_rel
