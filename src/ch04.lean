--------------------------------------------------------------------------------
--  Chapter 4 - Integers and rationals                 
--  Analysis 1, Third Edition, Tao                                            
--------------------------------------------------------------------------------

import tactic.interactive data.quot

private def eqv : (ℕ × ℕ) → (ℕ × ℕ) → Prop 
| ⟨a, b⟩  ⟨c, d⟩ := a + d = c + b

local infix ` ~ ` := eqv

-- Exercise 4.1.1.
private theorem eqv.refl : ∀ p : ℕ × ℕ, p ~ p
| ⟨a, b⟩ := rfl

private theorem eqv.symm : ∀ p₁ p₂ : ℕ × ℕ, p₁ ~ p₂ → p₂ ~ p₁
| (a, b) (c, d) (h₁ : a + d = c + b) := 
show c + b = a + d, by rw ←h₁

private theorem eqv.trans : ∀ p₁ p₂ p₃ : ℕ × ℕ, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃ 
| (a, b) (c, d) (e, f) (h₁ : a + d = c + b) := 
λ h₂ : c + f = e + d, 
show a + f = e + b, from 
    have h₃ : a + d + c + f = c + b + d + e, by simp [h₂, h₁], 
    have h₄ : a + f = b + e, from 
        @nat.add_left_cancel (c + d) (a + f) (b + e) (by simpa using h₃),
    by rw [h₄, add_comm b e] 

private theorem is_eqv : equivalence eqv := ⟨eqv.refl, eqv.symm, eqv.trans⟩ 

instance xint.setoid : setoid (ℕ × ℕ) := ⟨eqv, is_eqv⟩

def xint : Type := quotient (xint.setoid)

local notation `Z` := xint

namespace xint 

def mk (a b : ℕ) : xint :=  ⟦(a, b)⟧

instance : has_coe ℕ xint := has_coe.mk (λ n, mk n 0)    
instance xint_has_zero : has_zero xint := ⟨mk 0 0⟩
instance xint_has_one : has_one xint := ⟨mk 1 0⟩ 


def padd : ℕ × ℕ → ℕ × ℕ → xint
| (a, b) (c, d) := ⟦(a + c, b + d)⟧

@[simp] theorem eq_iff_equiv {p₁ p₂ : ℕ × ℕ} : ⟦p₁⟧ = ⟦p₂⟧ ↔ p₁ ~ p₂ := quotient.eq 

lemma padd_wd₁ : 
    ∀ (p₁ p₂ p₃ : ℕ × ℕ), p₁ ≈ p₂ → padd p₁ p₃ = padd p₂ p₃
| (a, b) (a', b') (c, d) (h₁ : a + b' = a' + b) := 
begin 
    unfold padd; simp; unfold eqv,
    have h₂ : a + b' + (c + d) = a' + b + (c + d), by rw h₁,
    simpa using h₂
end 

lemma padd_wd₂ : 
    ∀ (p₁ p₂ p₃ : ℕ × ℕ), p₂ ≈ p₃ → padd p₁ p₂ = padd p₁ p₃ 
| (a, b) (c, d) (c', d') (h₁ : c + d' = c' + d) := 
begin 
    unfold padd; simp; unfold eqv,
    have h₂ : (a + b) + (c + d') = (a + b) + (c' + d), by rw h₁,
    simpa using h₂ 
end

lemma padd_wd (a₁ a₂ b₁ b₂ : ℕ × ℕ) (h₁ : a₁ ≈ b₁) (h₂ : a₂ ≈ b₂) :
    padd a₁ a₂ = padd b₁ b₂ :=
let h₃ := (padd_wd₁ _ _ a₂) h₁,
    h₄ := (padd_wd₂ b₁ _ _) h₂ in 
by rw [h₃, h₄]

def add (a b : xint) : xint := 
quotient.lift_on₂ a b padd padd_wd

instance xint_has_add : has_add xint := ⟨add⟩

def pmul : ℕ × ℕ → ℕ × ℕ → xint
| (a, b) (c, d) := ⟦⟨a * c + b * d, a * d + b * c⟩⟧ 

lemma pmul_wd₁ : ∀ p₁ p₂ p₃ : ℕ × ℕ, p₁ ≈ p₂ → pmul p₁ p₃ = pmul p₂ p₃
| (a, b) (a', b') (c, d) (h₁ : a + b' = a' + b) := 
begin
    unfold pmul; simp; unfold eqv,
    have h₂ : a * c + b * d + (a' * d + b' * c)  = c * (a + b') + d * (a' + b), 
        by simp [mul_add, mul_comm],
    have h₃ : a' * c + b' * d + (a * d + b * c) = c * (a' + b) + d * (a + b'),
        by simp [mul_add, mul_comm],
    rw [h₂, h₃, h₁]
end 

lemma pmul_comm : ∀ p₁ p₂ : ℕ × ℕ, pmul p₁ p₂ = pmul p₂ p₁ 
| (a, b) (c, d) := by unfold pmul; simp; unfold eqv; simp [mul_add, mul_comm]

lemma pmul_wd (a₁ a₂ b₁ b₂ : ℕ × ℕ) (h₁ : a₁ ≈ b₁) (h₂ : a₂ ≈ b₂): 
    pmul a₁ a₂ = pmul b₁ b₂ := 
let h₃ := pmul_wd₁ _ _ a₂ h₁,
    h₄ := pmul_wd₁ _ _ b₁ h₂ in 
by rw [h₃, pmul_comm b₁ b₂, pmul_comm b₁ a₂, h₄].

def mul (a b : xint) : xint :=
quotient.lift_on₂ a b pmul pmul_wd.

instance xint_has_mul : has_mul xint := ⟨mul⟩ 

def pneg : ℕ × ℕ → Z | (a, b) := ⟦(b, a)⟧  

-- Exercise 4.1.2
def pneg_wd : ∀ (a b : ℕ × ℕ), a ≈ b → pneg a = pneg b 
| (a, b) (c, d) (h₁ : a + d = c + b) := 
begin
    unfold pneg, simp, unfold eqv,
    rw [add_comm d a, h₁, add_comm b c] 
end 

def neg (a : Z) : Z := quotient.lift_on a pneg pneg_wd

instance xint_has_neg : has_neg Z := ⟨neg⟩ 

-- Exercise 4.1.3
lemma one_mul (a : Z) : mul (⟦(1, 0)⟧) a = a :=
quotient.induction_on a (λ ⟨b, c⟩, quotient.sound (by simp))

theorem neg_one_mul : ∀ a : Z, mul (neg 1:Z) a = neg a := 
λ b, quotient.induction_on b $ λ ⟨c, d⟩, quot.sound $ (by simp : _ = _)

-- Exercise 4.1.4
section 
variables x y z : Z

theorem xint_comm : x + y = y + x :=
quotient.induction_on₂ x y $ λ ⟨a, b⟩ ⟨c, d⟩, quot.sound (by simp : _ = _)

theorem xint_assoc : (x + y) + z = x + (y + z) := 
quotient.induction_on₃ x y z $ λ ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩, 
quot.sound (by simp : _ = _)

theorem add_zero : x + 0 = x := 
quotient.induction_on x $ λ ⟨a, b⟩, quot.sound (by simp : _ = _) 

theorem zero_add : 0 + x = x :=
quotient.induction_on x $ λ ⟨a, b⟩, quot.sound (by simp : _ = _) 

theorem neg_cancel₁ : x + (-x) = 0 := 
quotient.induction_on x $ λ ⟨a, b⟩, quot.sound (by simp : _ = _)  

theorem neg_cancel₂ : (-x) + x = 0 := 
quotient.induction_on x $ λ ⟨a, b⟩, quot.sound (by simp : _ = _)   

theorem mul_comm : x * y = y * x := 
quotient.induction_on₂ x y $ λ ⟨a, b⟩ ⟨c, d⟩, 
quot.sound (by simp [add_mul, mul_comm] : _ = _) 

theorem mul_assoc : (x * y) * z = x * (y * z) := 
quotient.induction_on₃ x y z $ λ ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩, 
quot.sound 
(by simp [mul_add, add_mul, mul_comm, mul_assoc, mul_left_comm]  : _ = _) 

theorem mul_one : x * 1 = x := 
quotient.induction_on x $ λ ⟨a, b⟩, quot.sound (by simp : _ = _) 

theorem mul_add : x * (y + z) = x * y + x * z := 
quotient.induction_on₃ x y z $ λ ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩, 
quot.sound 
(by simp [mul_add, mul_assoc]  : _ = _)

theorem add_mul : ∀ (a b c : Z), (a + b) * c = a * c + b * c := 
λ a b c,
quotient.induction_on₃ a b c $ λ ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩, 
quot.sound (by simp [add_mul] : _ = _)  

end 

instance : comm_ring xint :=
{ add            := add,
  add_assoc      := xint_assoc,
  zero           := 0,
  zero_add       := zero_add,
  add_zero       := add_zero,
  neg            := xint.neg,
  add_left_neg   := neg_cancel₂,
  add_comm       := xint_comm,
  mul            := xint.mul,
  mul_assoc      := mul_assoc,
  one            := 1,
  one_mul        := one_mul,
  mul_one        := mul_one,
  left_distrib   := mul_add,
  right_distrib  := add_mul,
  mul_comm       := mul_comm}

instance : has_sub xint            := by apply_instance
instance : add_comm_monoid xint    := by apply_instance
instance : add_monoid xint         := by apply_instance
instance : monoid xint             := by apply_instance
instance : comm_monoid xint        := by apply_instance
instance : comm_semigroup xint     := by apply_instance
instance : semigroup xint          := by apply_instance
instance : add_comm_semigroup xint := by apply_instance
instance : add_semigroup xint      := by apply_instance
instance : comm_semiring xint      := by apply_instance
instance : semiring xint           := by apply_instance
instance : ring xint               := by apply_instance
instance : distrib xint            := by apply_instance

end xint

-- Exercise 4.1.5.
    