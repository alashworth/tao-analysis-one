prelude

import init.data.nat init.data.nat.lemmas

-- The integers are defined as a pair of natural numbers.
local notation `ℤ` := ℕ × ℕ

namespace int

-- An equivalence relation is defined on the integers.
def eqv : ℤ → ℤ → Prop
| (a, b) (c, d) := a + d = c + b

infix ` ∽ `:50 := eqv

theorem eqv.refl : ∀ (a : ℤ), a ∽ a 
| (a, b) := rfl

theorem eqv.symm : ∀ (a b : ℤ), a ∽ b → b ∽ a
| (a, b) (c, d) := λ h₁, eq.symm h₁

theorem eqv.trans : ∀ (a b c : ℤ), a ∽ b → b ∽ c → a ∽ c
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

def add : ℤ → ℤ → ℤ 
| (a, b) (c, d) := ((a + c), (b + d))

def mul : ℤ → ℤ → ℤ 
| (a, b) (c, d) := ((a * c + b * d), (a * d + b * c))

def neg : ℤ → ℤ 
| (a, b) := (b, a)

-- the natural numbers are isomorphic with the integers of form (a, 0)
def nat.to_int (n : ℕ) : ℤ := (n, 0)

instance nat_to_int_coe : has_coe (ℕ) (ℤ) := ⟨nat.to_int⟩ 

-- trichotomy of integers as inductive proposition
inductive trichot (x : ℤ) : Prop 
| zero : x = nat.zero → trichot
| pos : (∃ (n : ℕ), x = nat.succ n) → trichot
| neg : (∃ (n : ℕ), x = neg (nat.succ n)) → trichot 

theorem trichotomy_of_integers : ∀ (x : ℤ), trichot x 
| (a, b) := 
have h₁ : a < b ∨ a = b ∨ b < a, from nat.lt_trichotomy a b,
or.elim h₁ 
  (assume h₂ : a < b, 
    trichot.neg (exists.intro (b) 
        (suffices (a, b) = (nat.succ b, 0), from _, _))) 
        -- (a, b) = (nat.succ b, 0)
  (_)

end int
