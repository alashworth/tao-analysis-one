--------------------------------------------------------------------------------
--  Chapter 4 - Integers and rationals      
--  Section 4 - Gaps in the rational numbers   
--  Analysis 1, Third Edition, Tao                                            
--------------------------------------------------------------------------------

import data.rat

local infix ` ^ ` := monoid.pow

-- Exercise 4.4.3. 
def even (n : ℕ) := ∃ k, n = 2 * k

def odd (n : ℕ) := ∃ k, n = 2 * k + 1

lemma even_or_odd (n : ℕ) : even n ∨ odd n := 
nat.rec_on n 
    (or.inl $ exists.intro 0 (mul_zero 2)) 
    (λ k ih, or.elim ih 
        (λ ⟨m, h₁⟩, or.inr (exists.intro m (h₁ ▸ rfl))) 
        (λ ⟨m, h₁⟩, or.inl (exists.intro (m + 1) 
            (by rw [h₁, mul_add, mul_one])))) 

lemma even_of_even_add_even (n m : ℕ) : even n → even m → even (n + m) :=
λ ⟨a, (h₁ : n = 2 * a)⟩ ⟨b, (h₂ : m = 2 * b)⟩, 
    have h₃ : n + m = 2 * (a + b), from calc
        n + m = 2 * a + 2 * b : by rw [h₁, h₂]
            ... = 2 * (a + b) : by rw mul_add,
    exists.intro (a + b) h₃

lemma odd_of_even_add_odd (n m : ℕ) : even n → odd m → odd (n + m) :=
λ ⟨a, h₁⟩ ⟨b, h₂⟩, 
    have h₃ : n + m = 2 * (a + b) + 1, from calc 
        n + m = 2 * a + 2 * b + 1 : by rw [h₁, h₂, add_assoc]
            ... = 2 * (a + b) + 1 : by rw mul_add,
    exists.intro (a + b) h₃

lemma even_of_odd_add_odd (n m : ℕ) : odd n → odd m → even (n + m) := 
λ ⟨a, h₁⟩ ⟨b, h₂⟩, 
    have h₃ : n + m = 2 * (a + b + 1), from calc 
        n + m = 2 * a + 1 + (2 * b + 1) : by rw [h₁, h₂] 
            ... = 2 * a + 2 * b + 1 + 1 : by simp
            ... = 2 * a + 2 * b + (1 + 1) : by rw [add_assoc _ _ (1 + 1)]
            ... = 2 * a + 2 * b + 2 : by simpa using (1 + 1 = 2) 
            ... = 2 * (a + b + 1) : by simp [mul_add],
    exists.intro (a + b + 1) h₃

lemma odd_succ_of_even {n : ℕ} : even n → odd (nat.succ n) := 
λ ⟨a, h₁⟩, exists.intro a (by simp [h₁, nat.one_add])

lemma even_succ_of_odd {n : ℕ} : odd n → even (nat.succ n) := 
λ ⟨a, h₁⟩, exists.intro (nat.succ a) 
    (show nat.succ n = 2 * nat.succ a, from calc
        nat.succ n = nat.succ (2 * a + 1) : h₁ ▸ rfl
            ... = 2 * a + 2 : rfl
            ... = 2 * (a + 1) : by simp [mul_add]
            ... = 2 * nat.succ a : rfl)

lemma even_iff_odd_succ {n : ℕ} : even n ↔ odd (nat.succ n) :=
iff.intro (odd_succ_of_even) 
    (λ ⟨a, h₁⟩, exists.intro a 
        (have h₂ : nat.succ n = nat.succ (2 * a), from h₁, 
            nat.succ.inj h₂))

lemma odd_of_even_succ (n : ℕ) : even (nat.succ n) → odd n := 
λ h₁, exists.elim h₁ (λ a, nat.cases_on a (λ h₂, nat.no_confusion h₂) 
    (λ b h₂, exists.intro b 
        begin 
            rw [two_mul, nat.succ_add, nat.add_succ] at h₂,
            let h₃ := nat.succ.inj h₂,
            rw [h₃, nat.add_one, two_mul],
        end))

lemma odd_iff_even_succ {n : ℕ} : odd n ↔ even (nat.succ n) := 
iff.intro (even_succ_of_odd) (odd_of_even_succ n)

lemma not_even_and_odd (n : ℕ) : even n → odd n → false := 
nat.rec_on n 
    (λ ⟨a, h₁⟩ ⟨b, h₂⟩, nat.no_confusion h₂) 
    (λ k ih h₁ h₂, ih 
        (even_iff_odd_succ.mpr h₂) 
        (odd_iff_even_succ.mpr h₁))

lemma even_xor_odd (n : ℕ) : xor (even n) (odd n) :=
or.elim (even_or_odd n)
    (λ h₁, or.inl $ and.intro h₁ $ λ h₂, not_even_and_odd n h₁ h₂)
    (λ h₂, or.inr $ and.intro h₂ $ λ h₁, not_even_and_odd n h₁ h₂)

lemma even_iff_mod_two_eq_zero (n : ℕ) : even n ↔ n % 2 = 0 :=
iff.intro
    (λ ⟨k, h⟩, show n % 2 = 0, from calc
        n % 2 = (0 + n) % 2 : congr_arg (λ m, m % 2) (zero_add n).symm
            ... = (0 + 2 * k) % 2 : congr_arg (λ m, (0 + m) % 2) h
            ... = 0 : nat.add_mul_mod_self_left 0 2 k )
    (λ h, exists.intro (n / 2)
        (show n = 2 * (n / 2), from calc
            n = n % 2 + 2 * (n / 2) : (nat.mod_add_div n 2).symm
                ... = 0 + 2 * (n / 2) : congr_arg (λ m, m + 2 * (n / 2)) h
                ... = 2 * (n / 2) : zero_add (2 * (n / 2)) ) )

lemma odd_iff_mod_two_eq_one (n : ℕ) : odd n ↔ n % 2 = 1 :=
iff.intro
    (λ ⟨k, h⟩, show n % 2 = 1, from calc
        n % 2 = (2 * k + 1) % 2 : congr_arg (λ m, m % 2) h
            ... = (1 + 2 * k) % 2 : congr_arg (λ m, m % 2) (add_comm (2 * k) 1)
            ... = 1 : nat.add_mul_mod_self_left 1 2 k )
    (λ h, exists.intro (n / 2)
        (show n = 2 * (n / 2) + 1, from calc
            n = n % 2 + 2 * (n / 2) : (nat.mod_add_div n 2).symm
                ... = 1 + 2 * (n / 2) : congr_arg (λ m, m + 2 * (n / 2)) h
                ... = 2 * (n / 2) + 1 : add_comm 1 (2 * (n / 2)) ) )

lemma odd_of_odd_mul_odd (n m : ℕ) : odd n → odd m → odd (n * m) := 
λ ⟨a, h₁⟩ ⟨b, h₂⟩, exists.intro (2 * a * b + a + b) 
(by simp [h₁, h₂, mul_add, add_mul, two_mul])



