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
                     ... = nat.succ (a + (b + c)) : by rewrite ih
                     ... = a + (b + nat.succ c)   : nat.add_succ a (b + c)).

example (a b : ℕ) : a = 0 ∨ ∃! b, nat.succ b = a :=
nat.cases_on a
  (or.inl (eq.refl nat.zero))
  (take a : ℕ,
    suffices ∃! b, nat.succ b = nat.succ a, from or.inr this,
    exists.intro a
      (and.intro 
        (rfl) 
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

check @add_left_cancel

example (a b : ℕ) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := 
have h3 : ∃ c, a + c = b, from nat.le.dest h1,
have h4 : ∃ d, b + d = a, from nat.le.dest h2,
exists.elim h3 (take c, assume h5,
exists.elim h4 (take d, assume h6,
have h7 : a + c + d = a, from h5^.symm ▸ h6,
have h8 : c + d = 0, from add_left_cancel h7 ,
_))
