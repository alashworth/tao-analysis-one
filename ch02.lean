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
            rw [add_comm c b, add_comm c (a + d), add_assoc, add_comm d c, ←add_assoc, h₂],
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
            (_))))
    (_)

end
-- Exercise 2.2.4. Justify the three statements marked (why?) in the proof of
-- Proposition 2.2.13.

-- Exercise 2.2.5. Prove Proposition 2.2.14.

-- Exercise 2.2.6. Let n be a natural number, and let P(m) be a property per-
-- taining to the natural numbers such that whenever P(m++) is true, then P(m)
-- is true. Suppose that P(n) is also true. Prove that P(m) is true for all
-- natural numbers m ≤ n; this is known as the principle of backwards induction.

/-
 For any natural numbers
a,b,c, we have (a + b) + c = a + (b + c).
-/