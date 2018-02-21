/- Addition -/

import data.nat.basic

-- Lemma 2.2.2. For any natural number n, n + 0 = n.
example (n : ℕ) : n + 0 = n := nat.add_zero n 

-- Lemma 2.2.3. For any natural numbers n and m, n + (succ m) = succ (n + m)
example (m n : ℕ) : n + (nat.succ m) = nat.succ (n + m) := nat.add_succ n m

-- Lemma 2.2.4 (Addition is commutative). 
-- For any natural numbers n and m, n + m = m + n
example (m n : ℕ) : n + m = m + n := nat.add_comm n m

-- Proposition 2.2.5 (Addition is associative).
example (a b c : ℕ) : a + b + c = a + (b + c) := nat.add_assoc a b c

-- Proposition 2.2.6 (Cancellation law). 
example (a b c : ℕ) : a + b = a + c → b = c := nat.add_left_cancel

-- Proposition 2.2.8. 
example (a b : ℕ) : a > 0 → a + b > 0 := 
begin 
  intro h,
  cases b with b',
    { assumption },
    { rw nat.add_succ,
      apply nat.zero_lt_succ }
end

-- Proposition 2.2.9 
example (a b : ℕ) : a + b = 0 → a = 0 ∧ b = 0 := nat.eq_zero_of_add_eq_zero

-- Lemma 2.2.10.
example (a : ℕ) (ha : a > 0) : ∃! b, nat.succ b = a := 
begin 
  cases a with a',
    { have : ¬ 0 < 0, from nat.not_lt_zero 0,
      contradiction },
    { refine (exists_unique.intro a' rfl _),
      intros c h,
      injection h }
end

-- Proposition 2.2.12
section prop_2_2_12
open nat
variables a b c : ℕ

example : a ≥ a := nat.less_than_or_equal.refl a

example : a ≥ b → b ≥ c → a ≥ c := ge_trans

example : a ≥ b → b ≥ a → b = a := @le_antisymm ℕ _ b a 

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

example : a < b ↔ succ a ≤ b := 
iff.intro (λ (h : nat.succ a ≤ b), h) (λ (h : a < b), h)

@[reducible] def positive (n : ℕ) := n ≠ 0

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
end prop_2_2_12

-- Proposition 2.2.13 (Trichotomy of order for natural numbers)
example := nat.lt_trichotomy

-- Proposition 2.2.14 (Strong principle of induction).
section
open nat
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

