namespace integers

-- the whole numbers, defined as a cartesian product
section pre_integers

local notation `whl` := ℕ × ℕ.

def eqv : whl → whl → Prop
| (a, b) (c, d) := a + d = c + b → (a, b) = (c, d)

infix ` ∽ `:50 := eqv

theorem eqv.refl : ∀ (a : whl), a ∽ a 
| (a, b) := λ h, rfl.

theorem eqv.symm : ∀ (a b : whl), a ∽ b → b ∽ a
| (a, b) (c, d) := 
  assume 
    (h₁ : a + d = c + b → (a, b) = (c, d))
    (h₂ : c + b = a + d), 
  eq.symm (h₁ (eq.symm h₂)).

theorem eqv.trans : ∀ (a b c : whl), a ∽ b → b ∽ c → a ∽ c
| (a, b) (c, d) (e, f) := 
  assume
    (h₁ : a + d = c + b → (a, b) = (c, d))
    (h₂ : c + f = e + d → (c, d) = (e, f))
    (h₃ : a + f = e + b), 
  _

end pre_integers

end integers
