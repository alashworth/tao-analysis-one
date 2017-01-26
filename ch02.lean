open nat

/-------------------------------------------------------------------------------\
  solutions for chapter two: the natural numbers                                  
  analysis 1, third edition, tao                                             
\-------------------------------------------------------------------------------/

theorem succ.inj {a b : ℕ} (h : succ a = succ b) : a = b :=
nat.no_confusion h (λ e : a = b, e)

-- exercise 2.2.1: prove proposition 2.2.5
-- addition is associative
example (a b c : ℕ) : a + b + c = a + (b + c) :=
nat.induction_on c
  (rfl)
  (take c,
    assume ih : a + b + c = a + (b + c),
    calc
      a + b + succ c = succ (a + b + c)   : nat.add_succ (a + b) c
                     ... = succ (a + (b + c)) : congr_arg succ ih
                     ... = a + (b + succ c)   : nat.add_succ a (b + c)).

-- exercise 2.2.2: prove lemma 2.2.10
example (a b : ℕ) : a = 0 ∨ ∃! b, succ b = a :=
nat.cases_on a
  (or.inl (eq.refl nat.zero))
  (take a : ℕ,
    suffices ∃! b, succ b = succ a, from or.inr this,
    exists.intro a (and.intro (rfl) 
      (take b : ℕ,
        assume h : succ b = succ a,
        succ.inj h))).

-- exercise 2.2.3: prove proposition 2.2.12
-- order is reflexive
example (a : ℕ) : a ≤ a :=
  have h : a + nat.zero = a, from rfl,
  nat.le.intro h.

-- order is transitive
example (a b c : ℕ) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
nat.less_than_or_equal.induction_on h2
  (h1)
  (take c' : ℕ,
    assume h3,
    assume ih : a ≤ c',
    nat.less_than_or_equal.step ih).

-- order is antisymmetric 
example (a b : ℕ) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := 
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
example (a b c : ℕ) : a ≤ b ↔ a + c ≤ b + c :=
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

example (a b : ℕ) : a < b ↔ succ a ≤ b :=
iff.intro
  (assume h : a < b, h)
  (assume h : succ a ≤ b, h)

example (a b : ℕ) : a < b ↔ ∃ c, b = a + c ∧ c ≠ 0 :=
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

-- exercise 2.2.4: complete the proof of proposition 2.2.13
-- trichotomy of order
example (a b : ℕ) : 0 ≤ b :=
nat.induction_on b
  (nat.le_refl 0)
  (take a',
     assume h,
     nat.less_than_or_equal.step h)

example (a b : ℕ) : a > b → succ a > b := 
nat.induction_on a 
  (assume h : 0 > b, 
     have h1 : b < 0, from h, 
     have h2 : false, from iff.mp (nat.lt_zero_iff_false b) h1,
     false.elim h2)
  (take a', 
     assume ih h,
     have h2 : b < succ a', from h,
     nat.lt.step h2)

example (a b : ℕ) : a = b → succ a > b :=
nat.induction_on a
 (assume h,
   have h1 : 0 < 1, from succ_pos 0,
   eq.rec h1 h)
 (take a',
   assume ih h,
   have h2 : succ (succ a') ≤ succ (succ a'), 
     from le_refl (succ (succ a')),
   have h3 : succ a' < succ (succ a'), from h2,
   have h4 : b < succ (succ a'), begin rw -h, exact h3 end,
   h4)

-- exercise 2.2.5: prove proposition 2.2.14
-- principle of strong induction

lemma le_or_eq_of_le_succ 
  {m n : ℕ} (h1 : m ≤ succ n) : m ≤ n ∨ m = succ n :=
begin
  cases h1 with k h2,
  right, exact (eq.refl (succ n)),
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
    cases ih with m ih, cases ih with r ih, cases ih with h2 ih, cases ih with h3 h4,
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
