--------------------------------------------------------------------------------
--  Chapter 2 - Starting at the beginning: the natural numbers                 
--  Analysis 1, Third Edition, Tao                                            
--------------------------------------------------------------------------------

open nat

-- Exercise 2.2.1. Prove Proposition 2.2.5.
example : ∀ a b c : ℕ, (a + b) + c = a + (b + c) := 
λ a b c, 
nat.rec_on c 
    (show a + b + 0 = a + (b + 0), from rfl)
    (λ c ih, 
    show a + b + succ c = a + (b + succ c), from calc
        a + b + succ c = succ (a + b + c) : by rw add_succ
            ... = succ (a + (b + c)) : by rw ih
            ... = a + (b + succ c) : by rw add_succ)

-- Exercise 2.2.2. Prove Lemma 2.2.10.
def positive (n : ℕ) := n ≠ 0

example (a : ℕ) (h₁ : positive a) : ∃! b, succ b = a := begin
cases a with a,
    {unfold positive at h₁; contradiction},
    {existsi a,
    split,
        {simp},
        {intros b h₂; exact nat.no_confusion h₂ id}}
end

-- Exercise 2.2.3. Prove Proposition 2.2.12.
section
variables {a b c : ℕ}

example : a ≤ a := le.intro (add_zero a)

example (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := 
let ⟨m, h₃⟩ := le.dest h₁, ⟨n, h₄⟩ := le.dest h₂ in 
have h₅ : a + (m + n) = c, by rw [←add_assoc, h₃, h₄],
le.intro h₅

example (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := 
let ⟨m, h₃⟩ := le.dest h₁, ⟨n, h₄⟩ := le.dest h₂ in 
have h₅ : a + (m + n) = a + 0, by rw [←add_assoc, h₃, h₄, add_zero], 
have h₆ : m + n = 0, from add_left_cancel h₅, 
let ⟨h₇, h₈⟩ := eq_zero_of_add_eq_zero h₆ in 
by rw [←h₃, h₇, add_zero]

example : a ≤ b ↔ a + c ≤ b + c := 
iff.intro 
    (λ h₁, 
    let ⟨d, h₂⟩ := le.dest h₁ in 
    suffices ∃ k, a + c + k = b + c, from 
        exists.elim this (λ k h₃, le.intro h₃), 
    exists.intro d (by rw [←h₂, add_assoc a d c, add_comm d c, add_assoc]))
    (λ h₁, 
    let ⟨d, h₂⟩ := le.dest h₁ in 
    have h₃ : a + d = b, from 
        have h₃ : c + (a + d) = c + b, by 
            rw [add_comm c b, add_comm c (a + d)];
            rw [add_assoc, add_comm d c, ←add_assoc, h₂],
        add_left_cancel h₃,
    le.intro h₃)

-- Tao's definition 2.2.11 for less-than as a theorem
theorem lt_iff_le_and_ne : a < b ↔ a ≤ b ∧ a ≠ b :=
iff.intro 
    (λ h₁,
    and.intro 
        (less_than_or_equal.rec_on h₁ 
            (less_than_or_equal.step (less_than_or_equal.refl a))
            (λ b' (ih₁ : succ a ≤ b') ih₂, 
            less_than_or_equal.step ih₂)) 
        (λ h₂, 
        let ⟨k, h₃⟩ := le.dest h₁ in 
        have h₄ : k = 0, begin
            rw [succ_add, ←add_succ] at h₃,
            clear _let_match,
            subst h₂,
            exact absurd h₁ (lt_irrefl a)
        end,
        begin
            subst h₄,
            rw [add_zero, ←h₂] at h₃,
            have h₄ : (succ a) ≠ a, 
                exact succ_ne_self a,
            contradiction 
        end)) 
    (λ ⟨h₁, h₂⟩, 
    let h₃ := lt_or_eq_of_le h₁ in 
    or.elim h₃ id (λ h₄, absurd h₄ h₂))

example : a < b ↔ succ a ≤ b :=
iff.intro 
    (λ h₁, 
    let ⟨h₂, h₃⟩ := (iff.mp lt_iff_le_and_ne) h₁ in 
    let h₄ := le.dest h₂ in 
    exists.elim h₄ (λ k, 
    nat.cases_on k 
        (λ h₅ : a = b, absurd h₅ h₃) 
        (λ k' h₅, 
        have h₆ : succ a + k' = b, by rw [succ_add, ←add_succ, h₅], 
        le.intro h₆)))
    (λ h₁, 
    iff.mpr lt_iff_le_and_ne (and.intro 
        (let ⟨k, h₂⟩ := le.dest h₁ in 
        have h₃ : a + succ k = b, by rw [add_succ, ←succ_add, h₂], 
        le.intro h₃) 
        (let ⟨k, h₂⟩ := le.dest h₁ in 
        λ h₃, 
        have h₄ : succ a ≤ a, by rw ←h₃ at h₁; exact h₁, 
        let h₅ := not_succ_le_self a in absurd h₄ h₅)))
        
example : a < b ↔ ∃ d, (positive d ∧ b = a + d) := 
iff.intro
    (λ h₁, 
    let ⟨h₂, h₃⟩ := lt_iff_le_and_ne.mp h₁ in 
    let h₄ := le.dest h₂ in 
    exists.elim h₄ (λ k, nat.cases_on k 
        (λ h₅ : a = b, absurd h₅ h₃) 
        (λ c h₅, exists.intro (succ c) $ and.intro 
            (λ h₆, nat.no_confusion h₆) 
            (eq.symm h₅))))
    (λ h₁, 
    let ⟨c, ⟨h₂, h₃⟩⟩ := h₁ in begin
        cases c with c',
            {unfold positive at h₂,
            contradiction},
            have h₄ : b = succ a + c',
                rw [succ_add, ←add_succ, h₃],
            fapply le.intro,
            exact c',
            exact (eq.symm h₄)
    end)
end

-- Exercise 2.2.4. Justify the three statements marked (why?) in the proof of
-- Proposition 2.2.13.
example (b : ℕ) : 0 ≤ b :=
nat.rec_on b 
    (less_than_or_equal.refl 0)
    (λ a h₁, less_than_or_equal.step h₁)

example (a b : ℕ) (h₁ : a > b) : succ a > b := 
less_than_or_equal.step h₁ 

example (a b : ℕ) (h₁ : a = b) : succ a > b := h₁ ▸ (lt_succ_self _)

-- Exercise 2.2.5. Prove Proposition 2.2.14.
section
parameters (m₀ : ℕ) (P : ℕ → Prop)

example : 
    (∀ m, m₀ ≤ m) → 
    (∀ m' m, ((m₀ ≤ m' → m' < m) → P m') → P m) →
    (∀ m, m₀ ≤ m → P m) :=
λ h₁ h₂ m, 
nat.rec_on m 
    (λ h₃, h₂ 0 0 (λ h₄, false.elim (not_lt_zero 0 (h₄ h₃))))
    (λ n ih h₃, 
    h₂ (succ n) (succ n) (λ h₄, false.elim (not_succ_le_self (succ n) (h₄ h₃))))
end

-- Exercise 2.2.6. Let n be a natural number, and let P(m) be a property per-
-- taining to the natural numbers such that whenever P(m++) is true, then P(m)
-- is true. Suppose that P(n) is also true. Prove that P(m) is true for all
-- natural numbers m ≤ n; this is known as the principle of backwards induction.
example   
  (m n : ℕ) (P : ℕ → Prop) (h1 : ∀ {m}, P (succ m) → P m) :
  P n → (m ≤ n → P m) :=
nat.rec_on n
  (λ h2 h3, 
    have h4 : m = 0, from eq_zero_of_le_zero h3, 
    h4.symm ▸ h2)
  (λ n' h2 h3 h4, 
    have h5 : P n', from h1 h3, 
    have h6 : m < succ n' ∨ m = succ n', from lt_or_eq_of_le h4, 
    or.elim h6 
      (assume h7, 
        have h8 : m ≤ n', from le_of_lt_succ h7, 
        h2 h5 h8) 
      (assume h7 : m = succ n', h7.symm ▸ h3))

-- Exercise 2.3.1. Prove Lemma 2.3.2.
example : ∀ n : ℕ, 0 * n = 0 := begin
intro n, 
induction n with n ih,
    {trivial},
    {rw [mul_succ, zero_mul]}
end  

example (n m : ℕ) : n * m = m * n := 
nat.rec_on n 
    (show 0 * m = m * 0, by rw [zero_mul, mul_zero]) 
    (λ n ih, calc
        succ n * m = n * m + m  : by rw [succ_mul, ih]
            ... = m * succ n : by rw [mul_succ, ih])

-- Exercise 2.3.2. Prove Lemma 2.3.3.
example (n m : ℕ) : n * m = 0 ↔ n = 0 ∨ m = 0 := begin
apply iff.intro,
    {intro h₁,
    cases m,
        right; trivial,
        rw mul_succ at h₁,
        have h₂ := eq_zero_of_add_eq_zero_left h₁,
        left; assumption},
    {intro h₁, 
    cases h₁ with h₂ h₂, 
        rw [h₂, zero_mul],
        rw [h₂, mul_zero]}
end

-- Exercise 2.3.3. Prove Proposition 2.3.5.
example (a b c : ℕ) : (a * b) * c = a * (b * c) := begin
induction a with a ih,
    {repeat {rw zero_mul}},
    {rw [succ_mul, succ_mul],
    rw [add_mul, ih]}
end

-- Exercise 2.3.4. Prove the identity (a + b)^2 = a^2 + 2ab + b^2
lemma twice_of_add_self {n : ℕ} : n + n = 2 * n := by rw [succ_mul, one_mul] 
lemma sq_of_mul_self {n : ℕ} : n * n = n^2 := by unfold pow; rw one_mul

example (a b : ℕ) : (a + b)^2 = a^2 + 2*a*b + b^2 := calc
(a + b)^2 = (a + b) * (a + b) : by unfold pow; rw [one_mul]
    ... = (a + b) * a + (a + b) * b : by rw [mul_add]
    ... = (a * a + b * a) + (a * b + b * b) : by repeat {rw add_mul}
    ... = (a^2 + b * a) + (a * b + b^2) : by rw [sq_of_mul_self, sq_of_mul_self]
    ... = a^2 + (b * a + b * a) + b^2 : 
        by rw [mul_comm b a, ←add_assoc, add_assoc (a^2) _ _]  
    ... = a^2 + 2*a*b + b^2 : by rw [twice_of_add_self, mul_comm b a, mul_assoc]

-- Exercise 2.3.5. Prove Proposition 2.3.9.
section
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

