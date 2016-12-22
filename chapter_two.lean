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
(begin
  intro h,
  apply nat.less_than.induction_on h,
  reflexivity,
  intros d h1 ih,
  rewrite nat.succ_add,
  apply nat.less_than.step,
  exact ih,
end)
(assume h,
  have h1 : ∃ d, a + c + d = b + c, from nat.le.dest h,
  exists.elim h1 (take d, assume h2 : a + c + d = b + c, 
  have h3 : a + d + c = b + c, from
    calc
      a + d + c = a + (d + c) : nat.add_assoc a d c
            ... = a + (c + d) : by rw {_ + _}nat.add_comm
            ... = a + c + d   : by rw nat.add_assoc
            ... = b + c       : h2,
_))

