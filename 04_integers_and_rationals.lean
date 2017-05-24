-- Let the integers be represented as an ordered pair of natural numbers.
def ℤ₀ := ℕ × ℕ 

-- An equivalence relation is defined on the integers.
def eqv : ℤ₀ → ℤ₀ → Prop
| (a, b) (c, d) := a + d = c + b

infix ` ∽ `:50 := eqv

private theorem eqv.refl : ∀ (a : ℤ₀), a ∽ a 
| (a, b) := rfl

private theorem eqv.symm : ∀ (a b : ℤ₀), a ∽ b → b ∽ a
| (a, b) (c, d) := λ h₁, eq.symm h₁

private theorem eqv.trans : ∀ (a b c : ℤ₀), a ∽ b → b ∽ c → a ∽ c
| (a, b) (c, d) (e, f) := 
λ (h₁ : a + d = c + b) 
  (h₂ : c + f = e + d), 
show (a + f = e + b), from 
  have h₃ : a + d + c + f = c + b + e + d, from 
    calc
      a + d + c + f = a + d + e + d : by simp [add_assoc, h₂^.symm]
                ... = c + b + e + d : by simp [add_assoc, h₁^.symm], 
  have h₄ : c + d + a + f = c + d + b + e, from 
    calc
      c + d + a + f = a + d + c + f : by simp [add_comm]
                ... = c + b + e + d : h₃
                ... = c + d + b + e : by simp [add_comm],
  have h₅ : a + f = b + e, 
    from @add_left_cancel ℕ _ (c + d) _ _ (by simp; simp at h₃; assumption), 
  h₅^.symm ▸ (add_comm b e ▸ rfl)

private theorem is_equivalence : equivalence eqv := 
mk_equivalence (_) (eqv.refl) (eqv.symm) (eqv.trans)

instance Z.setoid : setoid ℤ₀ := setoid.mk eqv is_equivalence

-- A characteristic property of eqv

-- Now define the integers as a quotient of the ordered pair of naturals.
def Z : Type := quotient (Z.setoid)

namespace Z

-- Definition 4.1.2.
def add_Z₀ : ℤ₀ → ℤ₀ → ℤ₀
| (a, b) (c, d) := (a + c, b + d) 

-- Lemma 4.1.3 (Addition and multiplication are well-defined).



end Z
