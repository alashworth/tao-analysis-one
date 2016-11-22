/-------------------------------------------------------------------------------\
  Solutions for chapter two: the natural numbers                                  
  Analysis 1, Third Edition, Tao                                             
\-------------------------------------------------------------------------------/

import data.nat
open eq.ops nat

namespace ch2
local abbreviation S := nat.succ
local abbreviation induction_on := @nat.induction_on

-- axiom 2.1 - zero is a natural number
example : ℕ := 0

-- axiom 2.2 - if n is a natural number, so is S(n)
example (n : ℕ) : ℕ := S n 

-- axiom 2.3 - zero is not the successor of any natural number
lemma zero_not_succ (n : ℕ) : S n = 0 → false :=
(assume h : S n = 0, show false, from nat.no_confusion h)

-- axiom 2.4 - the successor function is injective
theorem succ_inj {a b : ℕ} (h : S a = S b) : a = b := 
  nat.no_confusion h (λ e : a = b, e)

-- auxiliary lemmas
lemma add_n_0 {n : ℕ} : n + 0 = n := rfl

lemma add_n_Sm {n m : ℕ} : n + S m = S (n + m) := rfl

-- lemma 2.2.2, reversed
lemma add_0_n {n : ℕ} : 0 + n = n :=
induction_on n
  (show 0 + 0 = 0, from add_n_0)
  (take n, 
    assume ih : 0 + n = n,
    show 0 + S n = S n, from 
      calc
        0 + S n = S (0 + n) : add_n_Sm
            ... = S n       : ih)

-- lemma 2.2.3, reversed
lemma add_Sn_m {n m : ℕ} : S n + m = S (n + m) :=
induction_on m
  (show S n + 0 = S (n + 0), from 
    calc
      S n + 0 = S n       : add_n_0
          ... = S (n + 0) : add_n_0)
  (take m,
    assume ih : S n + m = S (n + m),
    show S n + S m = S (n + S m), from
      calc
        S n + S m = S (S n + m)   : add_n_Sm
              ... = S (S (n + m)) : ih
              ... = S (n + S m)   : add_n_Sm)

-- proposition 2.2.4 
proposition add_comm {n m : ℕ} : n + m = m + n :=
induction_on n
  (show 0 + m = m + 0, from
    calc
      0 + m = m     : add_0_n
        ... = m + 0 : add_n_0)
  (take n,
    assume ih : n + m = m + n,
    show S n + m = m + S n, from 
      calc
        S n + m = S (n + m) : add_Sn_m
            ... = S (m + n) : ih
            ... = m + S n   : add_n_Sm)

-- proposition 2.2.5
proposition add_assoc {a b c : ℕ} : (a + b) + c = a + (b + c) :=
induction_on c
  (show (a + b) + 0 = a + (b + 0), from
    calc
      (a + b) + 0 = a + b       : add_n_0
              ... = a + (b + 0) : add_n_0)
  (take c,
    assume ih : a + b + c = a + (b + c),
    show a + b + S c = a + (b + S c), from
      calc
        a + b + S c = S (a + b + c)   : add_n_Sm 
                ... = S (a + (b + c)) : ih)

-- proposition 2.2.6
proposition add_cancel {a b c : ℕ} :  a + b = a + c → b = c :=
induction_on a
  (assume h : 0 + b = 0 + c,
    show b = c, from
      calc
        b = 0 + b : add_0_n
      ... = 0 + c : h
      ... = c     : add_0_n)
  (take a,
    assume ih : a + b = a + c → b = c,
    assume h0 : S a + b = S a + c,
    show b = c, from 
    proof
      have h1 :   S a + c = S (a + c) , from add_Sn_m,
      have h2 :   S a + b = S (a + b) , from add_Sn_m,
      have h3 : S (a + b) = S (a + c) , from h2⁻¹ ⬝ h0  ⬝ h1,
      have h4 :     a + b = a + c     , from succ_inj h3,
      ih h4
    qed)
 
-- def 2.2.7, prop 2.2.8 skipped

-- corollary 2.2.9
example (a b : ℕ) : (a + b = 0) → a = 0 ∧ b = 0 :=
nat.cases_on a
  (assume h : 0 + b = 0,
    show (0 = 0 ∧ b = 0), from 
      and.intro 
        (show (0 = 0), from rfl) 
        (show (b = 0), from h ▸ add_0_n⁻¹))
  (take a,
    assume h : (S a + b = 0),
    show (S a = 0 ∧ b = 0), from proof
      have S (a + b) = 0, from add_Sn_m ▸ h,
      have false, from nat.no_confusion `S (a + b) = 0`,
      false.elim this
    qed)

-- lemma 2.2.10 
example (a b : ℕ) : a = 0 ∨ ∃!b, S b = a :=
nat.cases_on a
  (show (0 = 0 ∨ ∃! b, S b = 0), from or.inl (eq.refl 0))
  (take a,
    suffices ∃!b, S b = S a, from or.inr this,
    exists.intro a 
      (and.intro 
        (show (S a = S a), from rfl)
        (take b, 
          show (S b = S a → b = a), from succ_inj)))

-- proposition 2.2.12 (≥ replaced with ≤ in order to match internal definitions)
section ordering

variables a b c : ℕ

-- order is reflexive
example : a ≤ a := 
  suffices a + 0 = a, from le.intro this,
  show (a + 0 = a), from add_n_0

-- order is transitive
example (h0 : a ≤ b) : b ≤ c → a ≤ c :=
le.rec h0
  (take c,
    assume h0 : (b ≤ c),
    show (a ≤ c → a ≤ S c), from le.step)
  
-- order is antisymmetric
example (h0 : a ≤ b) (h1 : b ≤ a) : a = b := sorry

end ordering

end ch2
