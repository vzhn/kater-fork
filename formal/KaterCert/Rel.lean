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

/-- Sequential composition, `r ; s`. -/
def comp (r s : Rel E) : Rel E := fun x z => ∃ y, r x y ∧ s y z

/-- Inclusion, `r ⊆ s`. -/
def Sub (r s : Rel E) : Prop := ∀ x y, r x y → s x y

theorem Sub.refl (r : Rel E) : Sub r r := fun _ _ h => h

theorem Sub.trans {r s t : Rel E} (h₁ : Sub r s) (h₂ : Sub s t) : Sub r t :=
  fun x y h => h₂ x y (h₁ x y h)

theorem comp_mono {r r' s s' : Rel E} (hr : Sub r r') (hs : Sub s s') :
    Sub (comp r s) (comp r' s') :=
  fun _ _ ⟨y, h₁, h₂⟩ => ⟨y, hr _ _ h₁, hs _ _ h₂⟩

end Rel

end KaterCert
