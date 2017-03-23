namespace integers

def eqv : ℕ × ℕ → ℕ × ℕ → Prop
| (a, b) (c, d) := a + d = c + b

infix ` ∽ `:50 := eqv

theorem eqv.refl : ∀ (a : ℕ × ℕ), a ∽ a 
| (a, b) := rfl

theorem eqv.symm : ∀ (a b : ℕ × ℕ), a ∽ b → b ∽ a
| (a, b) (c, d) := λ h₁, eq.symm h₁

theorem eqv.trans : ∀ (a b c : ℕ × ℕ), a ∽ b → b ∽ c → a ∽ c
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

end integers
