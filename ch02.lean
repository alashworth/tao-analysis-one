open nat

/-------------------------------------------------------------------------------\
  Chapter 2 - Starting at the beginning: the natural numbers
  Analysis 1, Third Edition, Tao                                             
\-------------------------------------------------------------------------------/

-- For brevity, we do not restate axioms or definitions unless they do not 
-- exist in Lean's base proof library, such as the book's definition of the 
-- positive numbers or the power operator.

proposition prop214 : ℕ := 3.

proposition prop216 : 4 ≠ 0 := succ_ne_zero 3 .

proposition prop218 : 6 ≠ 2 :=
ne.intro   
  (assume h1 : 6 = 2,
    have h2 : succ 5 = succ 1, from h1,
    have h3 : 5 = 1, from nat.no_confusion h2 (λ h, h),
    have h4 : succ 4 = succ 0, from h3,
    have h5 : 4 = 0, from nat.no_confusion h3 (λ h, h),
    show false, from absurd h5 prop216).

lemma lem222 (n : ℕ) : n + 0 = n := 
nat.induction_on n
  (show 0 + 0 = 0, by rw zero_add)
  (take n',
    assume ih : n' + 0 = n', 
    show succ n' + 0 = succ n', by rw add_zero).

lemma lem223 (n m : ℕ) : n + (succ m) = succ (n + m) :=
nat.induction_on n
  (show 0 + succ m = succ (0 + m), by repeat {rw zero_add})
  (take n', 
    assume ih : n' + succ m = succ (n' + m), 
    show succ n' + succ m = succ (succ n' + m), from 
      calc
        succ n' + succ m 
          = succ (n' + succ m)   : succ_add n' (succ m)
      ... = succ (succ (n' + m)) : congr_arg succ ih
      ... = succ (succ n' + m)   : congr_arg succ (eq.symm (succ_add n' m))).

proposition prop224 (n m : ℕ) : n + m = m + n :=
nat.induction_on n
  (show 0 + m = m + 0, by rw [zero_add, add_zero])
  (take n',
    assume ih : n' + m = m + n',
    show succ n' + m = m + succ n', from
      calc
        succ n' + m = succ (n' + m) : succ_add n' m
                ... = succ (m + n') : congr_arg succ ih
                ... = m + succ n'   : eq.symm (add_succ m n')).

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

proposition prop226 (a b c : ℕ) : a + b = a + c →  b = c :=
nat.induction_on a
  (assume h1 : 0 + b = 0 + c, 
    show b = c, by rw [-zero_add b, -zero_add c, h1])
  (take a',
    assume ih : a' + b = a' + c → b = c,
    assume h1 : succ a' + b = succ a' + c,
    have h2 : succ (a' + b) = succ (a' + c), by rw [-succ_add, -succ_add, h1],
    have h3 : a' + b = a' + c, from nat.no_confusion h2 (λ h, h),
    show b = c, from ih h3).

-- definition 2.2.7 
def is_pos (n : ℕ) := n ≠ 0

proposition prop228 {a b : ℕ} (h1 : is_pos a) : is_pos (a + b) :=
nat.induction_on b
  (show is_pos (a + 0), begin rw [add_zero], exact h1 end)
  (take b',
    assume ih : is_pos (a + b'),
    have h1 : a + succ b' = succ (a + b'), from add_succ a b',
    have h2 : is_pos (succ (a + b')), from succ_ne_zero (a + b'),
    show is_pos (a + succ b'), begin rw add_succ, exact h2 end)

-- corollary 2.2.9's book proof requires de Morgan's 1st law
lemma demorgan1 {p q : Prop} :  ¬(p ∧ q) ↔ ¬p ∨ ¬q :=
iff.intro
  (assume h1 : ¬(p ∧ q),
    or.elim (classical.em p) 
      (assume hp : p, 
        or.elim (classical.em q) 
          (assume hq : q, have hpq : p ∧ q, from and.intro hp hq, 
            show ¬p ∨ ¬q, from absurd hpq h1) 
          (assume hnq : ¬q, 
            show ¬p ∨ ¬q, from or.inr hnq)) 
      (assume hnp : ¬p, 
        show ¬p ∨ ¬q, from or.inl hnp))
  (assume h1 : ¬p ∨ ¬q, 
    or.cases_on h1
      (assume (hnp : ¬p) (h2 : p ∧ q), 
        show false, from absurd h2^.left hnp)
      (assume hnq h2,
        show false, from absurd h2^.right hnq)).

corollary cor229 (a b : ℕ) (h1 : a + b = 0) : a = 0 ∧ b = 0 :=
classical.by_contradiction 
  (assume h2: ¬(a = 0 ∧ b = 0),
    have h3 : ¬a = 0 ∨ ¬b = 0, from (iff.mp demorgan1) h2,
    or.cases_on h3
      (assume h4 : ¬a = 0,
        have h5 : is_pos a, from h4,
        have h6 : is_pos (a + b), from prop228 h5, 
        show false, from absurd h1 h6)
      (assume h4 : ¬b = 0,
        have h5 : is_pos b, from h4,
        have h6 : is_pos (b + a), from prop228 h5,
        have h7 : b + a = 0, by rw [add_comm, h1], 
        show false, from absurd h7 h6)).

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

-- trichotomy of order
proposition prop2213 (a b : ℕ) : a < b ∨ a = b ∨ a > b := 
nat.induction_on a
  (have h1 : 0 ≤ b, from zero_le b,
    have h2 : _, from lt_or_eq_of_le h1,
    or.cases_on h2 
      (assume h3, or.inl h3)
      (assume h3, or.inr (or.inl h3)))
  (take a',
    assume ih,
    or.cases_on ih
      (assume h1, 
        have h2 : succ a' ≤ b, from succ_le_of_lt h1, 
        have h3 : _, from lt_or_eq_of_le h2, 
        or.cases_on h3 
          (assume h4, or.inl h4)
          (assume h4, or.inr (or.inl h4)))
      (assume ih2,
        or.cases_on ih2
          (assume h1,
            have h2 : succ a' > a', from lt_succ_self a', 
            or.inr (or.inr (h1 ▸ h2)))
          (assume h1,
            have h2 : succ a' > b, from lt.step h1,
            or.inr (or.inr h2))))


-- exercise 2.2.5: prove proposition 2.2.14
-- principle of strong induction

lemma le_or_eq_of_le_succ  {m n : ℕ} (h1 : m ≤ succ n) : m ≤ n ∨ m = succ n:= 
have h2 : _, from lt_or_eq_of_le h1, 
or.cases_on h2
  (assume h3, have h4 : m ≤ n, from le_of_lt_succ h3, or.inl h4)
  (assume h3, or.inr h3)

lemma le_zero_iff_eq_zero {n : ℕ} : n ≤ 0 ↔ n = 0 :=
iff.intro
  (assume h1, 
    have h2 : _, from lt_or_eq_of_le h1,
    or.cases_on h2
      (assume h3, 
        have h4 : _, from iff.mp (lt_zero_iff_false n),
        have h5 : _, from h4 h3, false.elim h5)
      (λ h3, h3))
  (assume h1, le_of_eq h1)

lemma stronger_induction :
  (∀ P : ℕ → Prop, P 0 → 
  (∀ n, (∀ m, m ≤ n → P m) → P (succ n)) → 
  (∀ j, (∀ k, ((k ≤ j) → P k)))) :=
begin
  intros P h1 h2 j,
  induction j with j' ih,
    intros k h3,
    assert h4 : k = 0, begin exact iff.mp le_zero_iff_eq_zero h3 end,
    rw h4,
    exact h1,
    intros k h3,
    assert h4 : k ≤ j' ∨ k = succ j', 
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

proposition strong_induction :
  (∀ P : ℕ → Prop, P 0 → 
  (∀ n, (∀ m, m ≤ n → P m) → P (succ n)) → 
  (∀ k, P k)) :=
begin
  intros P h1 h2,
  apply weaken,
  apply stronger_induction,
    exact h1,
    exact h2
end

-- exercise 2.2.6
-- principle of backwards induction

proposition backwards_induction :
  (∀ P : ℕ → Prop, ∀ n : ℕ, P n →
  (∀ m : ℕ, P (succ m) → P m) → 
  (∀ k, k ≤ n → P k)) :=
begin
  intros P n,
  induction n with n' ih,
    {intros h0 m k h1,
      assert h2 : k = 0, {exact iff.mp le_zero_iff_eq_zero h1},
      show P k, {rw h2, exact h0}},
    {intros h0 h1 k h2,
      assert h3 : k ≤ n' ∨ k = succ n', {exact le_or_eq_of_le_succ h2},
      cases h3 with h4 h5,
        {apply ih, 
          apply h1,
          exact h0, exact h1, exact h4},
        {rw h5, 
          exact h0}}  
end.

-- exercise 2.3.1
-- multiplication is commutative

example (n : ℕ) : n * 0 = 0 := rfl

example (n : ℕ) : 0 * n = 0 :=
nat.induction_on n
  (rfl)
  (take n',
    assume ih : 0 * n' = 0,
    show 0 * succ n' = 0, from
      calc
        0 * succ n' = 0 * n' + 0 : mul_succ 0 n'
                ... = 0 + 0      : ih
                ... = 0          : rfl).

example (m n : ℕ) : m * succ n = m * n + m := rfl

example (m n : ℕ) : succ m * n = m * n + n := 
nat.induction_on n
  (show succ m * 0 = m * 0 + 0, from 
    calc
      succ m * 0 = 0         : succ_mul m 0
             ... = m * 0     : eq.symm (mul_zero m)
             ... = m * 0 + 0 : add_zero (m * 0))
  (take k,
    assume ih : succ m * k = m * k + k,
    show succ m * succ k = m * succ k + succ k, from
      calc
        succ m * succ k = succ m * k + succ m  : rfl
                    ... = succ m + succ m * k  : add_comm (succ m * k) (succ m)
                    ... = succ m + m * k + k   : by simp [ih]
                    ... = m * k + succ m + k   : by simp [add_comm]
                    ... = m * k + (succ m + k) : by simp [add_assoc]
                    ... = m * k + succ (m + k) : by simp [add_succ]
                    ... = m * k + (m + succ k) : by rw -(add_succ m k)
                    ... = m * succ k + succ k  : by simp [mul_succ]). 


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

-- exercise 2.3.2
-- positive natural numbers have no zero divisors

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

-- exercise 2.3.3
-- multiplication is associative
example (a b c : ℕ) : (a * b) * c = a * (b * c) :=
begin
  induction c with k ih,
    {trivial},
    {rw [mul_succ, mul_succ, mul_add, ih]}
end

-- exercise 2.3.4
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

-- exercise 2.3.5 
-- prove the Euclidean algorithm

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
