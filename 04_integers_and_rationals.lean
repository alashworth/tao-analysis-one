-- Definition 4.1.1 (Integers). An integer is an expression of the form 
-- a--b, where a and b are natural numbers. Two integers are considered to be
-- equal, a--b = c--d, iff a + d = c + b. We let Z denote the set of all 
-- integers.

-- An equivalence relation is defined on the integers.
private def eqv : ℕ × ℕ → ℕ × ℕ → Prop
| (a, b) (c, d) := a + d = c + b

infix ` ∽ `:50 := eqv

private theorem eqv.refl : ∀ (a : ℕ × ℕ), a ∽ a 
| (a, b) := rfl

private theorem eqv.symm : ∀ (a b : ℕ × ℕ), a ∽ b → b ∽ a
| (a, b) (c, d) := λ h₁, eq.symm h₁

private theorem eqv.trans : ∀ (a b c : ℕ × ℕ), a ∽ b → b ∽ c → a ∽ c
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

instance Z.setoid : setoid (ℕ × ℕ) := setoid.mk eqv is_equivalence

def Z : Type := quotient (Z.setoid)

private def mk (a b : ℕ) : Z := ⟦(a, b)⟧

local notation a`—`b := mk a b

-- Definition 4.1.2.
private def add_Z' : ℕ × ℕ → ℕ × ℕ → Z 
| (a, b) (c, d) := ⟦(a + c, b + d)⟧ 

-- Lemma 4.1.3 (Addition and multiplication are well-defined).
private lemma add_well_defined 
  (a b a' b' c d : ℕ) 
  (h₁ : (a—b) = (a'—b'))
  : add_Z' (a—b) (c—d) = add_Z' (a'—b') (c—d) := _

def add (x y : Z) : Z :=
(quotient.lift_on₂ x y 
  (λ a b, add_Z' a b) 
  (λ n₁ n₂ n₃ n₄ h₁ h₂, add_well_defined n₁ n₂ n₃ n₄ h₁ h₂))

instance Z.has_zero : has_zero Z := ⟨⟦(0, 0)⟧⟩
instance Z.has_one : has_one Z := ⟨⟦(1, 0)⟧⟩
