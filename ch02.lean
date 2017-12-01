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
variables a b c : ℕ

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
    let ⟨k, h₂⟩ := le.dest h₁ in 
        _)
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