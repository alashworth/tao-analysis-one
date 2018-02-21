/- Multiplication -/

import algebra.ring

-- Lemma 2.3.2 (Multiplication is commutative).
example := nat.mul_comm 

-- Lemma 2.3.3 (Positive natural numbers have no zero divisors).
example := @mul_eq_zero_iff_eq_zero_or_eq_zero

-- Proposition 2.3.4 (Distributive law). 
example := @mul_add

-- Proposition 2.3.5 (Multiplication is associative). 
example := @mul_assoc

-- Proposition 2.3.6 (Multiplication preserves order).
example := @mul_lt_mul_of_pos_right

-- Corollary 2.3.7 (Cancellation law). 
example := @eq_of_mul_eq_mul_right

-- Proposition 2.3.9 (Euclidean algorithm).
-- Exercise 2.3.5. Prove Proposition 2.3.9.
section
open nat
variables (n q : ℕ) (h₁ : q > 0)
include h₁

example : ∃ (m r : ℕ), 0 ≤ r ∧ r < q ∧ n = m * q + r := 
nat.rec_on n
    (exists.intro 0 (exists.intro 0 
    (and.intro 
        (show 0 ≤ 0, from le_refl 0) 
        (and.intro 
            (show q > 0, from h₁) 
            (show 0 = 0 * q + 0, by rw zero_mul)))))
    (λ n ih, 
    let ⟨m, r, h₁, h₂, h₃⟩ := ih in 
    have h₄ : succ r ≤ q , from h₂,
    let h₅ := lt_or_eq_of_le h₄ in 
    or.elim h₅ 
        (λ h₆, begin 
            existsi [m, succ r],
            split,
                exact zero_le _,
                split,
                    exact h₆, 
                    rw [add_succ, h₃],
        end) 
        (λ h₆, begin
            existsi [succ m, 0],
            split,
                exact zero_le _,
                split,
                    assumption,
                    rw add_zero,
                    rw [h₃, ←add_succ, succ_mul, h₆]
        end))
end
