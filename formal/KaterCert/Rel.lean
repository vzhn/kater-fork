/-!
# Relations

Binary relations on a type of events: what Kater's expressions and automata
denote.
-/

namespace KaterCert

universe u

/-- A binary relation on events. -/
abbrev Rel (E : Type u) := E → E → Prop

namespace Rel

variable {E : Type u}

/-- The identity relation. -/
def id : Rel E := fun x y => x = y

/-- The empty relation. -/
def empty : Rel E := fun _ _ => False

/-- Union, `r | s`. -/
def union (r s : Rel E) : Rel E := fun x y => r x y ∨ s x y

/-- Sequential composition, `r ; s`. -/
def comp (r s : Rel E) : Rel E := fun x z => ∃ y, r x y ∧ s y z

/-- The inverse, `r^-1`. -/
def inv (r : Rel E) : Rel E := fun x y => r y x

/-- Inclusion, `r ⊆ s`. -/
def Sub (r s : Rel E) : Prop := ∀ x y, r x y → s x y

/-- The reflexive-transitive closure, `r*`. -/
inductive Star (r : Rel E) : Rel E
  | refl (x : E) : Star r x x
  | step {x y z : E} : r x y → Star r y z → Star r x z

/-- The transitive closure, `r+`. -/
def Plus (r : Rel E) : Rel E := comp r (Star r)

/-- The reflexive closure, `r?`. -/
def Opt (r : Rel E) : Rel E := union id r

theorem Sub.refl (r : Rel E) : Sub r r := fun _ _ h => h

theorem Sub.trans {r s t : Rel E} (h₁ : Sub r s) (h₂ : Sub s t) : Sub r t :=
  fun x y h => h₂ x y (h₁ x y h)

theorem comp_mono {r r' s s' : Rel E} (hr : Sub r r') (hs : Sub s s') :
    Sub (comp r s) (comp r' s') :=
  fun _ _ ⟨y, h₁, h₂⟩ => ⟨y, hr _ _ h₁, hs _ _ h₂⟩

theorem id_comp {r : Rel E} {x y : E} : comp id r x y ↔ r x y :=
  ⟨fun ⟨_, h₁, h₂⟩ => h₁ ▸ h₂, fun h => ⟨x, rfl, h⟩⟩

theorem comp_id {r : Rel E} {x y : E} : comp r id x y ↔ r x y :=
  ⟨fun ⟨_, h₁, h₂⟩ => h₂ ▸ h₁, fun h => ⟨y, h, rfl⟩⟩

theorem comp_assoc {r s t : Rel E} {x y : E} :
    comp (comp r s) t x y ↔ comp r (comp s t) x y :=
  ⟨fun ⟨_, ⟨b, h₁, h₂⟩, h₃⟩ => ⟨b, h₁, _, h₂, h₃⟩,
   fun ⟨_, h₁, ⟨c, h₂, h₃⟩⟩ => ⟨c, ⟨_, h₁, h₂⟩, h₃⟩⟩

theorem Star.single {r : Rel E} {x y : E} (h : r x y) : Star r x y := .step h (.refl y)

theorem Star.trans {r : Rel E} {x y z : E} (h₁ : Star r x y) (h₂ : Star r y z) : Star r x z := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

theorem Star.mono {r s : Rel E} (h : Sub r s) : Sub (Star r) (Star s) := by
  intro x y hxy
  induction hxy with
  | refl => exact .refl _
  | step hr _ ih => exact .step (h _ _ hr) ih

end Rel

end KaterCert
