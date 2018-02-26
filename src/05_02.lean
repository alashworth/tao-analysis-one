/- Equivalent Cauchy Sequences -/

import analysis.real tactic.ring
open real is_absolute_value is_cau_seq

variables 
  (a : ℕ → ℚ)
  (b : ℕ → ℚ)

-- Exercise 5.2.1.
lemma third_pos {n : ℚ} (h : 0 < n) : 0 < (n / 3) := div_pos h (dec_trivial) 

lemma add_thirds (n : ℚ) : (n / 3) + (n / 3) + (n / 3) = n := by ring

set_option eqn_compiler.zeta true
example (eqv : ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (a n - b n) < ε) : 
  is_cau_seq abs a → is_cau_seq abs b := 
λ acau ε εgt0, 
  let ⟨N₀, h₀⟩ := (eqv (ε / 3) (third_pos εgt0)) in
  let ⟨N₁, h₁⟩ := (cauchy₂ acau (third_pos εgt0)) in
  let N := max N₀ N₁ in 
  exists.intro N (λ m h₂,
  let ⟨_, _⟩ := (max_le_iff.1 h₂) in 
  let h₃ := (h₀ m) ‹N₀ ≤ m› in
  let h₄ := (h₀ N) (le_max_left N₀ N₁) in  
  let h₅ := (h₁ m N) ‹_› (le_max_right _ _) in
    calc
      abs (b m - b N) = abs ((b m - a m) + (a m - a N) + (a N - b N)) : 
        by simp [add_comm, add_assoc]
      ... ≤ abs (b m - a m) + abs (a m - a N) + abs (a N - b N) : 
        abs_add_three (b m - a m) (a m - a N) (a N - b N)
      ... < (ε / 3) + (ε / 3) + (ε / 3) : 
        add_lt_add (add_lt_add (by rwa abs_sub at h₃) h₅) h₄
      ... = ε : add_thirds ε)