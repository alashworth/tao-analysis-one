---------------------------------------------------------------------------------
--  Chapter 2 - Starting at the beginning: the natural numbers                 --
--  Analysis 1, Third Edition, Tao                                             --
---------------------------------------------------------------------------------

-- Tao gives an axiomatic construction of the natural numbers. We instead 
-- construct them, and prove the Peano axioms hold. To follow precisely his 
-- formulations would require a rigorous formalization of set theory, which
-- is in the next chapter.

inductive N : Type 
| Z : N      -- Axiom 2.1. 0 is a natural number             
| S : N → N  -- Axiom 2.2. If n is a natural number, then n++ is also.

namespace N
open N (rec_on)

-- Necessary to use 0 as notation for Z; similarly for 1
instance N_has_zero : has_zero N := has_zero.mk Z
instance N_has_one : has_one N := has_one.mk (S Z)

-- Axiom 2.3. 0 is not the successor of any natural number.
theorem zero_ne_succ (n : N) (h : 0 = S n) : false := 
N.no_confusion h 

-- Axiom 2.4. Different natural numbers must have different successors.
theorem S.injective (n m : N) (h : S n = S m) : n = m := 
N.no_confusion h id

theorem S.injective₂ (n m : N) (h : n ≠ m) : S n ≠ S m :=
λ h₂, N.no_confusion h₂ (λ h₃, absurd h₃ h)

-- Axiom 2.5. Principle of mathematical induction.
theorem N.induction 
  (n : N) 
  (P : N → Prop) 
  (P₀ : P 0)
  (ih : ∀n, P n → P (S n))
  : P n :=
N.rec_on n (P₀) (ih)

-- Proposition 2.1.16. Recursive definitions.
-- This proposition requires the notion of indexed sets of functions, 
-- and so is postponed until the next chapter.

-- Definition 2.2.1 Addition of natural numbers.
def nat_add : N → N → N 
| 0 m := m
| (S n) m := S (nat_add n m)

instance N_has_add : has_add N := has_add.mk nat_add

theorem zero_add (n : N) : n = 0 + n := rfl
theorem succ_add (m n : N) : S (m + n) = (S m) + n := rfl   

-- Lemma 2.2.2. For any natural number n, n + 0 = n.
lemma add_zero : ∀n, n = n + Z 
| Z := rfl
| (S n) := congr_arg S (add_zero n)

-- Lemma 2.2.3. For any natural numbers m and n, n + (S m) = S (n + m)
lemma add_succ : ∀ m n, S (n + m) = n + (S m)
| m 0 := rfl
| m (S n) := congr_arg S (add_succ m n) 

-- Corollary : For all n, S n = n + 1
lemma succ_of_add_one : ∀(n : N), S n = n + 1 
| Z := rfl
| (S n) := congr_arg S (succ_of_add_one n)



end N
