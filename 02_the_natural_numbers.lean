---------------------------------------------------------------------------------
--  Chapter 2 - Starting at the beginning: the natural numbers                 --
--  Analysis 1, Third Edition, Tao                                             --
---------------------------------------------------------------------------------

open nat

-- Remark: some theorems in Analysis 1 are already proven in Lean. In that case,
-- the proof will be referred from the standard library.

-- Tao's successor notation.
local postfix `++` := succ

-- Axiom 2.1. 0 is a natural number.
example : ℕ := 0

-- Axiom 2.2. If n is a natural number, then n++ is also a natural number.
example (n : ℕ) : ℕ := n++

-- Proposition 2.1.4. 3 is a natural number.
example : ℕ := 3

-- Axiom 2.3. 0 is not the successor of any natural number; i.e.; we have 
-- n++ ≠ 0 for every natural number n.
example : ∀ n : ℕ, n++ ≠ 0 := succ_ne_zero

-- Proposition 2.1.6. 4 is not equal to 0.
example : 4 ≠ 0 := succ_ne_zero 3 

-- Axiom 2.4. Different natural numbers must have different successors.
example (n m : ℕ) (h : n ≠ m) : (n++) ≠ (m++) := 
λ h₂, nat.no_confusion h₂ (λ h₃, absurd h₃ h)

-- Equivalently, if n++ = m++, then we must have n = m.
example (n m : ℕ) (h : n++ = m++) : n = m := nat.no_confusion h id

-- Proposition 2.1.8. 6 is not equal to 2.
example : 6 ≠ 2 := 
suffices 5++ ≠ 1++, from this, 
λ h, nat.no_confusion h 
  (λ h₂, 
    have h₃ : 4++ = 0++, from h₂, 
    have h₄ : 4 = 0, from nat.no_confusion h₃ id, 
    have h₅ : 4 ≠ 0, from succ_ne_zero _, 
    absurd h₄ h₅)

-- Axiom 2.5. Principle of mathematical induction.
-- Let P(n) be any property pertaining to a natural number n. Suppose that
-- P(0) is true, and suppose that whenever P(n) is true, P(n++) is also true.
-- Then P(n) is true for every natural number n.
example (P : ℕ → Prop) (h : P 0) (ih : ∀ n, P n → P (n++)) : ∀ n, P n :=
λ n, @nat.rec_on P n h ih

-- Proposition 2.1.16 (Recursive definitions). Suppose for each natural number n,
-- we have some function f(n) : ℕ → ℕ from the natural numbers to the natural
-- numbers. Let c be a natural number. Then we can assign a unique natural
-- number a(n) to each natural number n, such that a(0) = c and
-- a(n++) = f(n) a(n) for each natural number n.

-- TODO
-- 1) How should this be expressed using dependent types?

-- Lemma 2.2.2. For any natural number n, n + 0 = n.
example : ∀ n, n + 0 = n := add_zero

-- Lemma 2.2.3. For any natural numbers n and m, n + (m++) = (n + m)++
example : ∀ n m, n + (m++) = (n + m)++ := add_succ

-- Proposition 2.2.4 (Addition is commutative)
example : ∀ n m : ℕ, n + m = m + n := add_comm

-- Proposition 2.2.5 (Addition is associative)
example : ∀ a b c : ℕ, (a + b) + c = a + (b + c) := add_assoc

-- Proposition 2.2.6 (Cancellation law). Let a, b, c be natural numbers such that
-- a + b = a + c. Then we have b = c.
example (a b c : ℕ) : a + b = a + c → b = c := add_left_cancel 

-- Definition 2.2.7 (Positive natural numbers). A natural number n is said
-- to be positive iff it is not equal to 0.
def positive : ℕ → Prop
| zero := false
| (n++) := true

lemma pos_of_succ : ∀ {n}, n ≠ 0 → positive n := 
λ n, nat.rec_on n (λ h, absurd (eq.refl 0) h) (λ n' ih h, by trivial)

lemma not_pos_of_zero : ∀ {n}, n = 0 → ¬ positive n := 
λ n, nat.rec_on n (λ h h₂, h₂) (λ n' ih h₂ h₃, absurd h₂ (succ_ne_zero _))

-- Proposition 2.2.8. If a is positive and b is a natural number, then a + b 
-- is positive (and hence b + a is also, by Proposition 2.2.4).
theorem pos_of_pos_add {a b : ℕ} (h : positive a) : positive (a + b) := 
nat.rec_on b 
  (by simp [positive]; exact h)
  (λ a' ih, by rw add_succ; unfold positive; trivial)

theorem pos_of_add_pos {a b : ℕ} (h : positive b) : positive (a + b) := 
nat.rec_on a
  (by rw [zero_add]; exact h)
  (λ b' ih, by rw [succ_add]; unfold positive; trivial)

-- Corollary 2.2.9. If a and b are natural numbers such that a + b = 0, then
-- a = 0 and b = 0.

-- Remark: this statement will be proved formally in Chapter 3
axiom demorgan {p q : Prop} (h : ¬(p ∧ q)) : ¬p ∨ ¬q

example (a b : ℕ) (h : a + b = 0) : a = 0 ∧ b = 0 :=
classical.by_contradiction (λ h₂, 
  have h₃ : a ≠ 0 ∨ b ≠ 0, from demorgan h₂, 
  or.elim h₃ 
    (λ h₄, 
      have h₅ : positive a, from pos_of_succ h₄, 
      have h₆ : positive (a + b), from pos_of_pos_add h₅, 
      absurd h₆ (not_pos_of_zero h)) 
    (λ h₄, 
      have h₅ : positive b, from pos_of_succ h₄,
      have h₆ : positive (a + b), from pos_of_add_pos h₅, 
      absurd h₆ (not_pos_of_zero h)))

-- Lemma 2.2.10. Let a be a positive number. Then there exists exactly one
-- natural number b such that b++ = a.
example (a b : ℕ) : a = 0 ∨ ∃! b, nat.succ b = a :=
nat.cases_on a
  (or.inl (eq.refl nat.zero))
  (take a : ℕ,
    suffices ∃! b, nat.succ b = nat.succ a, from or.inr this,
    exists.intro a (and.intro (rfl) 
      (take b : ℕ,
        assume h : nat.succ b = nat.succ a,
        succ.inj h))).

-- Proposition 2.2.12
section ordering

variables (a b c : ℕ)

-- order is reflexive
example : a ≥ a := le_refl _

-- order is transitive
example : a ≥ b → b ≥ c → a ≥ c := ge_trans

-- order is antisymmetric
example : a ≥ b → b ≥ a → a = b := 
λ h₁ h₂, le_antisymm h₂ h₁ 

-- addition preserves order
example (a b c : ℕ) : a ≤ b ↔ a + c ≤ b + c :=
iff.intro
  (assume h : a ≤ b,
    nat.less_than_or_equal.rec_on h 
      (nat.less_than_or_equal.refl (a + c))
      (take b',
        assume h : a ≤ b',
        assume ih : a + c ≤ b' + c,
        have h2 : a + c ≤ nat.succ (b' + c), 
          from nat.less_than_or_equal.step ih,
        have h3 : a + c ≤ nat.succ b' + c, 
          begin rw -nat.succ_add at h2, exact h2 end, 
        h3))
  (assume h : a + c ≤ b + c,
    have h2 : ∃ d, a + c + d = b + c, from nat.le.dest h,
    exists.elim h2 (take d, assume h3 : a + c + d = b + c,
      have h4 : c + (a + d) = c + b, from
        calc
          c + (a + d) = a + d + c : add_comm c (a + d)
                  ... = a + c + d : by simp [add_comm d c]
                  ... = b + c     : h3
                  ... = c + b     : add_comm b c,
      have h5 : a + d = b, from add_left_cancel h4,
      nat.le.intro h5)).

example (a b : ℕ) : a < b ↔ a++ ≤ b :=
iff.intro
  (assume h : a < b, h)
  (assume h : a++ ≤ b, h)

example (a b : ℕ) : a < b ↔ ∃ c, b = a + c ∧ c ≠ 0 :=
iff.intro
  (assume h : a < b,
    have h2 : nat.succ a ≤ b, from h,
    have h3 : ∃ d, nat.succ a + d = b, from nat.le.dest h2,
    exists.elim h3 (take d, assume h4 : nat.succ a + d = b, 
      exists.intro (nat.succ d) 
        (and.intro 
          (show b = a + nat.succ d, from 
             calc
               b = nat.succ a + d   : eq.symm h4
             ... = nat.succ (a + d) : nat.succ_add a d
             ... = a + nat.succ d   : eq.symm (nat.add_succ a d))
          (show nat.succ d ≠ 0, from nat.succ_ne_zero d)))) 
  (assume h : ∃ c, b = a + c ∧ c ≠ 0,
    exists.elim h (take c, 
      nat.cases_on c 
        (assume h, 
          have h2 : 0 ≠ 0, from and.right h,
          absurd (rfl) h2) 
        (take c',
          assume h : b = a + nat.succ c' ∧ nat.succ c' ≠ 0,
          have h2 : b = a + nat.succ c', from and.left h, 
          have h3 : b = nat.succ a + c', from 
            calc
              b = a + nat.succ c'   : h2
            ... = nat.succ (a + c') : nat.add_succ a c'
            ... = nat.succ a + c'   : eq.symm (nat.succ_add a c'),
          suffices nat.succ a ≤ b, from this,
          suffices nat.succ a ≤ nat.succ a + c', begin rw h3, exact this end, 
          nat.le_add_right (nat.succ a) c'))).

-- Proposition 2.2.13 (Trichotomy of order for natural numbers).
-- (the full proof is in the text, these are the three (Why?s))
example (a b : ℕ) : 0 ≤ b :=
nat.rec_on b
  (nat.le_refl 0)
  (take a',
     assume h,
     nat.less_than_or_equal.step h)

example (a b : ℕ) : a > b → nat.succ a > b := 
nat.rec_on a 
  (assume h : 0 > b, 
     have h1 : b < 0, from h, 
     have h2 : false, from iff.mp (nat.lt_zero_iff_false b) h1,
     false.elim h2)
  (take a', 
     assume ih h,
     have h2 : b < nat.succ a', from h,
     nat.lt.step h2)

example (a b : ℕ) : a = b → nat.succ a > b :=
nat.rec_on a
 (assume h,
   have h1 : 0 < 1, from nat.succ_pos 0,
   eq.rec h1 h)
 (take a',
   assume ih h,
   have h2 : nat.succ (nat.succ a') ≤ nat.succ (nat.succ a'), 
     from le_refl (nat.succ (nat.succ a')),
   have h3 : nat.succ a' < nat.succ (nat.succ a'), from h2,
   have h4 : b < nat.succ (nat.succ a'), begin rw -h, exact h3 end,
   h4)

end ordering

section strong_induction

lemma le_or_eq_of_le_succ 
  {m n : ℕ} (h1 : m ≤ nat.succ n) : m ≤ n ∨ m = nat.succ n :=
begin
  cases h1 with k h2,
  right, exact (eq.refl (nat.succ n)),
  left, assumption 
end

lemma le_zero_iff_eq_zero {n : ℕ} : n ≤ 0 ↔ n = 0 :=
begin
  apply iff.intro, 
    {intro h, 
      cases h, 
      reflexivity},
    {intro h,
      rw h}, 
end

lemma stronger_induction :
  (∀ P : ℕ → Prop, P 0 → 
  (∀ n, (∀ m, m ≤ n → P m) → P (nat.succ n)) → 
  (∀ j, (∀ k, ((k ≤ j) → P k)))) :=
begin
  intros P h1 h2 j,
  induction j with j' ih,
    intros k h3,
    assert h4 : k = 0, begin exact iff.mp le_zero_iff_eq_zero h3 end,
    rw h4,
    exact h1,
    intros k h3,
    assert h4 : k ≤ j' ∨ k = nat.succ j', 
      begin exact le_or_eq_of_le_succ h3 end,
    cases h4 with h4l h4r,
      apply ih, exact h4l,
      rw h4r,
      apply h2, exact ih
end

lemma weaken :
  (∀ P : ℕ → Prop, 
  (∀ n, (∀ m, ((m ≤ n) → P m))) → 
  (∀ n, P n)) :=
begin
  intros P h n,
  apply (h n n),
  exact le_refl n
end

theorem strong_induction :
  (∀ P : ℕ → Prop, P 0 → 
  (∀ n, (∀ m, m ≤ n → P m) → P (nat.succ n)) → 
  (∀ k, P k)) :=
begin
  intros P h1 h2,
  apply weaken,
  apply stronger_induction,
    exact h1,
    exact h2
end

end strong_induction

-- Exercise 2.2.6. Let n be a natural number, and let P(m) be a property
-- pertaining to the natural numbers such that whenever P(m++) is true, then P(m)
-- is true. Suppose that P(n) is also true. Prove that P(m) is true for all
-- natural numbers m ≤ n; this is known as the principle of backwards induction.

theorem backwards_induction  
  (m n : ℕ) (P : ℕ → Prop) (h1 : ∀ {m}, P (succ m) → P m) :
  P n → (m ≤ n → P m) :=
nat.rec_on n
  (assume h2 h3, 
    have h4 : m = 0, from eq_zero_of_le_zero h3, h4^.symm ▸ h2)
  (assume n' h2 h3 h4, 
    have h5 : P n', from h1 h3, 
    have h6 : m < succ n' ∨ m = succ n', from lt_or_eq_of_le h4, 
    or.elim h6 
      (assume h7, 
        have h8 : m ≤ n', from le_of_lt_succ h7, 
        h2 h5 h8) 
      (assume h7 : m = succ n', h7^.symm ▸ h3))


-- Exercise 2.3.1. Prove Lemma 2.3.2.
example (n m : ℕ) : n * m = m * n :=
nat.rec_on m
  (show n * 0 = 0 * n, from 
    calc
      n * 0 = 0     : rfl
        ... = 0 * n : eq.symm (zero_mul n))
  (take k,
    assume ih : n * k = k * n,  
    show n * succ k = succ k * n, from
      calc
        n * succ k = n * k + n  : mul_succ n k
               ... = n + n * k  : add_comm (n * k) n
               ... = n + k * n  : by rw [ih]
               ... = k * n + n  : by simp [add_comm]
               ... = succ k * n : by simp [succ_mul])

-- Exercise 2.3.2. Prove Lemma 2.3.3. (Hint: prove the second statement first)
-- TODO
lemma aux232 (n m : ℕ) : n * m + m = 0 → m = 0 :=
begin
  induction m with k ih,
    {simp},
    {intro h, rw add_succ at h, 
      assert h2 : false, {apply succ_ne_zero (n * succ k + k) h},
      apply false.elim h2}   
end 

example (n m : ℕ) : n * m = 0 ↔ n = 0 ∨ m = 0 := 
begin
  apply iff.intro,
    {cases n with n',
      {intro h, left, exact eq.refl 0},
      {intro h, right, rw (succ_mul n' m) at h, apply aux232 n', exact h}},
    {intro h,
      cases h with h1 h2,
        {rw h1, exact zero_mul m},
        {rw h2, exact mul_zero n}}
end

-- Exercise 2.3.3. Prove Proposition 2.3.5. (Hint: modify the proof of Proposition
-- 2.2.5 and use the distributive law).

example (a b c : ℕ) : (a * b) * c = a * (b * c) :=
begin
  induction c with k ih,
    {trivial},
    {rw [mul_succ, mul_succ, mul_add, ih]}
end

-- Exercise 2.3.4. Prove the identity (a + b)^2 = a^2 + 2ab + b^2 for all 
-- natural numbers a and b
section 

def pow (a : ℕ) : ℕ → ℕ
| 0 := 1
| (n++) := a * pow n

infix `^` := pow

theorem pow_zero (a : ℕ) : a^0 = 1 := rfl
theorem pow_succ (a : ℕ) (n : ℕ) : a^(n++) = a * a^n := by unfold pow; simp

theorem n_sq : ∀ {n : ℕ}, n * n = n^2 :=
begin intros, unfold pow, simp, rw [pow_zero, mul_one] end

theorem n_plus_n_eq_2n : ∀ {n : ℕ}, n + n = 2 * n :=
begin 
  intros, 
  assert h : 2 = succ 1, begin trivial end,
  rw h,
  rw succ_mul,
  rw one_mul
end

example (a b : ℕ) : (a + b)^2 = a^2 + 2*a*b + b^2 := 
calc
  (a + b)^2 = (a + b) * (a + b) : 
     begin unfold pow, simp, rw [pow_zero, mul_one] end
        ... = (a + b) * a + (a + b) * b       : by rw mul_add
        ... = a * a + b * a + (a * b + b * b) : by rw [add_mul, add_mul]
        ... = a^2 + b * a + (a * b + b^2)     : by rw [n_sq, n_sq]
        ... = a^2 + (a * b + a * b) + b^2     : by simp [mul_comm]
        ... = a^2 + 2*(a*b) + b^2             : by rw (@n_plus_n_eq_2n (a * b))
        ... = a^2 + 2*a*b + b^2               : by rw -(mul_assoc 2 a b).

end

-- Exercise 2.3.5. Prove Proposition 2.3.9. 
example (n q : ℕ) (h1 : q > 0) : ∃ m r, 0 ≤ r ∧ r < q ∧ n = m * q + r :=
begin
  -- the first insight - induct on n
  induction n with n ih,
    existsi 0, existsi 0, simp, split, exact h1, exact le_refl 0,
    cases ih with m ih, 
    cases ih with r ih, 
    cases ih with h2 ih, 
    cases ih with h3 h4,
    assert h5 : succ n = m * q + (succ r), begin exact congr_arg succ h4 end,
    assert h6 : succ r ≤ q, exact h3,
    -- the second insight - case analysis on h7
    assert h7 : succ r < q ∨ succ r = q, exact lt_or_eq_of_le h6,
    cases h7 with h7 h7,
      existsi m, existsi (succ r), split, 
      exact zero_le (succ r), split, 
      exact h7, 
      exact h5,
      existsi (succ m), existsi 0, split, 
      apply zero_le, split,
      apply h1, simp, rw mul_succ, rw -h7, rw -h7 at h5, rw h5, simp     
end
