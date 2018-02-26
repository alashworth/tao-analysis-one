/- Cauchy sequences -/

import analysis.real
open cau_seq

variables 
  (α : Type) [discrete_linear_ordered_field α] 
  (β : Type) [ring β] 
  (abv : β → α) [is_absolute_value abv]
  (f : cau_seq β abv)

-- Lemma 5.1.15 (Cauchy sequences are bounded). 
example : ∃ r, ∀ i, abv (f i) < r :=
let ⟨i, h⟩ := cauchy f zero_lt_one in 
let R := (finset.range (i+1)).sum (λ j, abv (f j)) in 
have h₁ : ∀ j ≤ i, abv (f j) ≤ R, from
  λ j ij, show (λ j, abv (f j)) j ≤ R, from 
  finset.single_le_sum 
    (λ k hk, is_absolute_value.abv_nonneg abv (f k)) 
    (by rwa [finset.mem_range, nat.lt_succ_iff]),
exists.intro (R + 1) (λ j, or.elim (lt_or_le j i) 
  (λ h₂, 
    let h₃ := le_of_lt h₂ in 
    lt_of_le_of_lt (h₁ j h₃) (lt_add_one R)) 
  (λ ij, 
    let h₃ := lt_of_le_of_lt (is_absolute_value.abv_add abv _ _)
      (add_lt_add_of_le_of_lt (h₁ _ (le_refl i)) (h j ij)) in 
    by rw [add_sub, add_comm] at h₃; simpa using h₃))
