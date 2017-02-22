open nat

---------------------------------------------------------------------------------
--  Chapter 2 - Starting at the beginning: the natural numbers                 --
--  Analysis 1, Third Edition, Tao                                             --
---------------------------------------------------------------------------------

-- Exercise 2.2.1. Prove Proposition 2.2.5.
proposition prop225 (a b c : ℕ) : (a + b) + c = a + (b + c) :=
nat.induction_on c
  (show a + b + 0 = a + (b + 0), by repeat {rw [add_zero]})
  (take c,
    assume ih : a + b + c = a + (b + c),
    show a + b + succ c = a + (b + succ c), from
      calc
        a + b + succ c = succ (a + b + c)   : add_succ (a + b) c
                   ... = succ (a + (b + c)) : congr_arg succ ih
                   ... = a + (b + succ c)   : add_succ a (b + c)).

-- Exercise 2.2.2. Prove Lemma 2.2.10.
def is_pos (n : ℕ) := n ≠ 0

lemma lem2210 (a b : ℕ) : is_pos a → ∃! b, succ b = a :=
nat.induction_on a
  (assume h : is_pos 0,
    show ∃! b, succ b = 0, from absurd (eq.refl 0) h)
  (take a',
    assume ih : is_pos a' → (∃! (b : ℕ), succ b = a'),
    assume h1 : is_pos (succ a'),
    exists.intro a' 
      (and.intro 
        (show succ a' = succ a', from eq.refl (succ a'))
        (take k,
          assume h : succ k = succ a', 
          show k = a', from nat.no_confusion h (λ h, h)))).

-- Exercise 2.2.3. Prove Proposition 2.2.12.

-- order is reflexive
proposition prop2212a (a : ℕ) : a ≤ a :=
  have h : a + nat.zero = a, from rfl,
  nat.le.intro h.

-- order is transitive
proposition prop2212b (a b c : ℕ) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
nat.less_than_or_equal.induction_on h2
  (h1)
  (take c' : ℕ,
    assume h3,
    assume ih : a ≤ c',
    nat.less_than_or_equal.step ih).

-- order is antisymmetric 
proposition prop2212c (a b : ℕ) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := 
  have h3 : ∃ c, a + c = b, from nat.le.dest h1,
  have h4 : ∃ d, b + d = a, from nat.le.dest h2,
  exists.elim h3 (take c, assume h5 : a + c = b,
  exists.elim h4 (take d, assume h6 : b + d = a,
  have h7 : a + (c + d) = a + 0, from 
    calc
      a + (c + d) = a + c + d : eq.symm (add_assoc a c d) 
              ... = a         : eq.symm h5 ▸ h6
              ... = a + 0     : add_zero a,
  have h8 : c + d = 0, from add_left_cancel h7,
  have h9 : c = 0, from nat.eq_zero_of_add_eq_zero_right h8,
  have h10 : a + 0 = b, from h9 ▸ h5,
  show a = b, from h10)).

-- addition preserves order
proposition prop2212d (a b c : ℕ) : a ≤ b ↔ a + c ≤ b + c :=
iff.intro
  (assume h : a ≤ b,
    nat.less_than_or_equal.induction_on h 
      (nat.less_than_or_equal.refl (a + c))
      (take b',
        assume h : a ≤ b',
        assume ih : a + c ≤ b' + c,
        have h2 : a + c ≤ succ (b' + c), 
          from nat.less_than_or_equal.step ih,
        have h3 : a + c ≤ succ b' + c, 
          begin rw -succ_add at h2, exact h2 end, 
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

proposition prop2212e (a b : ℕ) : a < b ↔ succ a ≤ b :=
iff.intro
  (assume h : a < b, h)
  (assume h : succ a ≤ b, h)

proposition prop2212f (a b : ℕ) : a < b ↔ ∃ d, b = a + d ∧ is_pos d :=
iff.intro
  (assume h : a < b,
    have h2 : succ a ≤ b, from h,
    have h3 : ∃ d, succ a + d = b, from nat.le.dest h2,
    exists.elim h3 (take d, assume h4 : succ a + d = b, 
      exists.intro (succ d) 
        (and.intro 
          (show b = a + succ d, from 
             calc
               b = succ a + d   : eq.symm h4
             ... = succ (a + d) : succ_add a d
             ... = a + succ d   : eq.symm (nat.add_succ a d))
          (show succ d ≠ 0, from succ_ne_zero d)))) 
  (assume h : ∃ c, b = a + c ∧ c ≠ 0,
    exists.elim h (take c, 
      nat.cases_on c 
        (assume h, 
          have h2 : 0 ≠ 0, from and.right h,
          absurd (rfl) h2) 
        (take c',
          assume h : b = a + succ c' ∧ succ c' ≠ 0,
          have h2 : b = a + succ c', from and.left h, 
          have h3 : b = succ a + c', from 
            calc
              b = a + succ c'   : h2
            ... = succ (a + c') : nat.add_succ a c'
            ... = succ a + c'   : eq.symm (succ_add a c'),
          suffices succ a ≤ b, from this,
          suffices succ a ≤ succ a + c', begin rw h3, exact this end, 
          nat.le_add_right (succ a) c'))).

-- Exercise 2.2.13. Justify the three statements marked (why?) in the proof of
-- Proposition 2.2.13.

example (b : ℕ) : 0 ≤ b := 
nat.induction_on b
  (show 0 ≤ 0, from le_refl 0)
  (show ∀ b', 0 ≤ b' → 0 ≤ succ b', from
    take b', 
    assume h1 : 0 ≤ b',
    have h2 : b' ≤ succ b', from le_succ b', 
    le_trans h1 h2)

example (a b : ℕ) (h1 : a > b) : succ a > b := lt.step h1

example (a b : ℕ) (h1 : a = b) : succ a > b := 
have h2 : a < succ a, from lt_succ_self a, 
h1 ▸ h2

-- Exercise 2.2.5. Prove Proposition 2.2.14. 

section

parameters (m₀ : ℕ) (P : ℕ → Prop)

theorem strong_induction {P : ℕ → Prop} {m₀ : ℕ} 
(h1 : ∀ m n, (m₀ ≤ m → m < n → P m) → P n) : ∀ k, P k :=
assume (k : ℕ), 
have h1 : (m₀ ≤ k → k < k → P k) → P k, from h1 k k, 
suffices (m₀ ≤ k → k < k → P k), from h1 this, 
assume (h2 : m₀ ≤ k) (h3 : k < k), 
absurd h3 (iff.mp (lt_self_iff_false k))

-- Exercise 2.2.6. Let n be a natural number, and let P(m) be a property
-- pertaining to the natural numbers such that whenever P(m++) is true, then P(m)
-- is true. Suppose that P(n) is also true. Prove that P(m) is true for all
-- natural numbers m ≤ n; this is known as the principle of backwards induction.

lemma eq_zero_of_le_zero {n : ℕ} (h : n ≤ 0) : n = 0 :=
have h1 : n < 0 ∨ n = 0, from lt_or_eq_of_le h, 
or.elim h1 (λ h2, absurd h2 (not_lt_zero _)) (id)

theorem backwards_induction  
  (m n : ℕ) (P : ℕ → Prop) (h1 : ∀ {m}, P (succ m) → P m) :
  P n → (m ≤ n → P m) :=
nat.induction_on n
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
nat.induction_on m
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

universe variable u
variable {α : Type u}
variable [monoid α]

def pow (a : α) : ℕ → α
| 0 := 1
| (n + 1) := a * pow n

infix `^` := pow

theorem pow_zero (a : α) : a^0 = 1 := rfl

theorem pow_succ (a : α) (n : ℕ) : a^(succ n) = a * a^n := rfl

theorem n_sq : ∀ {n : ℕ}, n * n = n^2 :=
  begin intros, unfold pow, simp end

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
  (a + b)^2 = (a + b) * (a + b)               : begin unfold pow, simp end
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
