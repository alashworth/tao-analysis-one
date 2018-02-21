--------------------------------------------------------------------------------
-- Chapter 3 - Set theory
-- Section 3 - Functions
-- Analysis 1, Third Edition, Tao
--------------------------------------------------------------------------------

import data.set.function data.equiv
open function set 

universes u v w z
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Type z}

-- Exercise 3.3.1. Show that the definition of function equality is reflexive,
-- symmetric, and transitive.
section

variables (f g : α → β).

example : f = g ↔ ∀ x, f x = g x := 
⟨congr_fun, funext⟩.

example : ∀ x, f x = f x := λ x, rfl.

example : ∀ x, f x = g x ↔ g x = f x := 
λ x, ⟨λ h₁, eq.symm h₁, λ h₂, eq.symm h₂⟩.

example (h : α → β) : ∀ x, f x = g x → g x = h x → f x = h x := 
λ x h₁ h₂, eq.trans h₁ h₂. 

end

-- Exercise 3.3.2. Let f : X → Y and g : Y → Z be functions. Show that if f
-- and g are both injective, then so is g ◦ f; similarly, show that if f and g -- are both surjective, then so is g ◦ f.
section 
variables (f : α → β) (g : β → γ)

example (h₁ : injective f) (h₂ : injective g) : injective (g ∘ f) := 
λ x₁ x₂ h₃, h₁ $ h₂ h₃ 

example (h₁ : surjective f) (h₂ : surjective g) : surjective (g ∘ f) := 
λ z, let ⟨y, h₃⟩ := h₂ z, ⟨x, h₄⟩ := h₁ y in 
⟨x, show (g ∘ f) x = z, by rw [←h₃, ←h₄]⟩ 

end

-- Exercise 3.3.3. When is the empty function injective? surjective? bijective?
section 
variable (f : (∅ : set α) → set α)

-- The empty function is injective vacuously.
example : injective f := λ x₁ _, false.elim x₁.2

-- The empty function is a surjection iff the set is empty
example : ∀ X, set.surj_on f ∅ X ↔ X = ∅ :=
λ X, iff.intro 
    (λ h₁, ext $ λ Y, iff.intro 
        (λ h₂, 
            begin
                unfold surj_on at *,
                unfold image at *,
                simp at h₁, 
                let h₃ := mem_of_subset_of_mem h₁ h₂,
                exact h₃ 
            end) 
        (λ h₂, false.elim h₂)) 
    (λ h₁ Y h₂, 
        have h₃ : Y ∈ ∅, by rw ←h₁; exact h₂, 
        false.elim h₃)
end
-- Therefore it follows that it is bijective only between two empty sets.


-- Exercise 3.3.4.  In this section we give some cancellation laws for 
-- composition. Let f₁ : X → Y, f₂ : X → Y, g₁ : Y → Z, and g₂ : Y → Z be 
-- functions. Show that if g ◦ f = g ◦ f₂ and g is injective, then f₁ = f₂. 
-- Show that if g ◦ f = g₂ ◦ f and f is surjective, then g₁ = g₂.
section
variables (f₁ f₂ : α → β) (g₁ g₂ : β → γ)

example (h₁ : injective g₁) (h₂ : g₁ ∘ f₁ = g₁ ∘ f₂) : f₁ = f₂ := 
funext (λ x, let h₂ := congr_fun h₂ x in h₁ h₂) 

example (h₁ : surjective f₁) (h₂ : g₁ ∘ f₁ = g₂ ∘ f₁) : g₁ = g₂ := 
funext $ λ y, let ⟨x, h₃⟩ := h₁ y, h₄ := congr_fun h₂ x in by rw ←h₃; exact h₄

end

-- Exercise 3.3.5
section 
variables (f : α → β) (g : β → γ)

example (h₁ : injective (g ∘ f)) : injective f := 
λ x₁ x₂ h₂, h₁ (show g (f x₁) = g (f x₂), by rw [←h₂])

example (h₁ : surjective (g ∘ f)) : surjective g := 
λ x, let ⟨a, h₃⟩ := h₁ x in ⟨f a, h₃⟩

end

/- Exercise 3.3.6 Let f : X → Y be a bijective function, and let f⁻¹ : Y → X
be its inverse. Verify the cancellation laws f⁻¹ (f(x)) = x for all x ∈ X and
f(f⁻¹(y)) = y for all y ∈ Y . Conclude that f⁻¹ is also invertible, and has f
as its inverse (thus (f⁻¹ )⁻¹ = f -/


section 

variables (f : α → β) (g : β → α) (h₁ : bijective f) (h₂ : left_inverse g f)
    (h₃ : right_inverse f g)

example : g ∘ f = id := funext h₂

example : f ∘ g = id := funext $ (let ⟨h₄, h₅⟩ := h₁ in 
    have h₆ : left_inverse f g, 
        from left_inverse_of_surjective_of_right_inverse h₅ h₃, 
    λ x, h₆ x)



end

-- Exercise 3.3.7
section 
variables (f : α → β) (g : β → γ) 

example : bijective f → bijective g → bijective (g ∘ f) := 
λ ⟨h₁, h₂⟩ ⟨h₃, h₄⟩, and.intro 
    (λ x₁ x₂ h₅, h₁ (h₃ h₅)) 
    (λ x, 
        exists.elim (h₄ x) (λ y h₅, 
        exists.elim (h₂ y) (λ z h₆, ⟨z, by rw [←h₅, ←h₆]⟩))) 
 
end

-- Exercise 3.3.8 
section 

variables {X Y Z : set α}

def inclusion_map (XsubY : X ⊆ Y) : X → Y
| ⟨x, h⟩ := ⟨x, XsubY h⟩

lemma inclusion_trans 
  (XsubY : X ⊆ Y) (YsubZ : Y ⊆ Z) (XsubZ : X ⊆ Z) :
  (inclusion_map YsubZ) ∘ (inclusion_map XsubY) = inclusion_map (XsubZ) :=
funext (λ ⟨x, h⟩, rfl).

lemma inclusion_comp_right :
    ∀ f : X → Y, f = f ∘ (inclusion_map $ subset.refl X) := 
λ f, funext (λ ⟨x, h⟩, rfl)

lemma inclusion_comp_left (f : X → Y) :
  f = (inclusion_map $ subset.refl Y) ∘ f := 
funext (λ x, match f x : ∀ y, y = inclusion_map (subset.refl Y) y
  with ⟨y, h⟩ := rfl end)

end