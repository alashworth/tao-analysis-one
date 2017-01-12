/-------------------------------------------------------------------------------\
  solutions for chapter two: the natural numbers                                  
  analysis 1, third edition, tao                                             
\-------------------------------------------------------------------------------/

theorem succ.inj {a b : ℕ} (h : nat.succ a = nat.succ b) : a = b :=
nat.no_confusion h (λ e : a = b, e)

example (a b c : ℕ) : a + b + c = a + (b + c) :=
nat.induction_on c
  (rfl)
  (take c,
    assume ih : a + b + c = a + (b + c),
    calc
      a + b + nat.succ c = nat.succ (a + b + c)   : nat.add_succ (a + b) c
                     ... = nat.succ (a + (b + c)) : congr_arg nat.succ ih
                     ... = a + (b + nat.succ c)   : nat.add_succ a (b + c)).

example (a b : ℕ) : a = 0 ∨ ∃! b, nat.succ b = a :=
nat.cases_on a
  (or.inl (eq.refl nat.zero))
  (take a : ℕ,
    suffices ∃! b, nat.succ b = nat.succ a, from or.inr this,
    exists.intro a (and.intro (rfl) 
      (take b : ℕ,
        assume h : nat.succ b = nat.succ a,
        succ.inj h))).

example (a : ℕ) : a ≤ a :=
  have h : a + nat.zero = a, from rfl,
  nat.le.intro h.

example (a b c : ℕ) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
nat.less_than.induction_on h2
  (h1)
  (take c' : ℕ,
    assume h3,
    assume ih : a ≤ c',
    nat.less_than.step ih).

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

example (a b c : ℕ) : a ≤ b ↔ a + c ≤ b + c :=
iff.intro
  (assume h : a ≤ b,
    nat.less_than.induction_on h 
      (nat.less_than.refl (a + c))
      (take b',
        assume h : a ≤ b',
        assume ih : a + c ≤ b' + c,
        have h2 : a + c ≤ nat.succ (b' + c), from nat.less_than.step ih,
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

example (a b : ℕ) : a < b ↔ nat.succ a ≤ b :=
iff.intro
  (assume h : a < b, h)
  (assume h : nat.succ a ≤ b, h)

theorem nat.le.dest.iff (n m : ℕ) : n ≤ m ↔ ∃ k, n + k = m :=
iff.intro
  (assume h, nat.le.dest h)
  (assume h2 : ∃ k, n + k = m,
   exists.elim h2 (take k, assume h3 : n + k = m, nat.le.intro h3))

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
    exists.elim h (take c, assume h2 : b = a + c ∧ c ≠ 0, 
      have h3 : b = a + c, from and.left h2,
      have h4 : c ≠ 0, from and.right h2,
      have h5 : a ≤ b, from nat.le.intro (eq.symm h3),
      suffices nat.succ a ≤ b, from this, 
      suffices nat.succ a ≤ a + c, begin rw h3, exact this end, 
      begin
        induction c with c ih,
          { apply absurd (eq.refl 0) h4 },
          { rw [nat.add_succ, -nat.succ_add],
            exact nat.le_add_right (nat.succ a) c},
      end))
