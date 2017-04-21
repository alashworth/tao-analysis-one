---------------------------------------------------------------------------------
--  Chapter 2 - Starting at the beginning: the natural numbers                 --
--  Analysis 1, Third Edition, Tao                                             --
---------------------------------------------------------------------------------

-- Tao gives an axiomatic construction of the natural numbers. We instead 
-- construct them, and prove the Peano axioms hold.

inductive N : Type 
| Z : N      -- Axiom 2.1. 0 is a natural number             
| S : N → N  -- Axiom 2.2. If n is a natural number, then n++ is also.

namespace N
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
-- TODO

-- Definition 2.2.1 Addition of natural numbers.
def N_add : N → N → N 
| 0 m := m
| (S n) m := S (N_add n m)

instance N_has_add : has_add N := has_add.mk N_add

theorem zero_add (n : N) : Z + n = n := rfl
theorem succ_add (m n : N) : (S m) + n = S (m + n) := rfl   

-- Lemma 2.2.2. For any natural number n, n + 0 = n.
lemma add_zero : ∀n, n + Z = n 
| Z := rfl
| (S n) := congr_arg S (add_zero n)

-- Lemma 2.2.3. For any natural numbers m and n, n + (S m) = S (n + m)
lemma add_succ : ∀ m n, n + (S m) = S (n + m)
| m 0 := rfl
| m (S n) := congr_arg S (add_succ m n) 

-- Corollary : For all n, S n = n + 1
lemma succ_of_add_one : ∀(n : N), n + 1 = S n 
| Z := rfl
| (S n) := congr_arg S (succ_of_add_one n)

-- Proposition 2.2.4. Addition is commutative
theorem add_comm : ∀ n m : N, n + m = m + n
| n Z := by rw add_zero; reflexivity
| n (S m) := by rw add_succ; exact (congr_arg S (add_comm n m)) 

-- Proposition 2.2.5. Addition is associative
theorem add_assoc : ∀ a b c : N, (a + b) + c = a + (b + c)
| a b Z := by rw [add_zero, add_zero]
| a b (S c) := by repeat {rw [add_succ]}; exact (congr_arg S (add_assoc a b c))

-- Proposition 2.2.6. Cancellation law.
theorem add_left_cancel : ∀ a b c : N, a + b = a + c → b = c
| Z b c := id
| (S a) b c :=
  begin
    rw [succ_add, succ_add],
    intro h,
    apply add_left_cancel a b c,
    apply S.injective _ _ h
  end

-- Definition 2.2.7. Positive natural numbers.
inductive pos (n : N) : Prop
| mk : n ≠ Z → pos

-- Proposition 2.2.8.
theorem pos_of_add_pos : ∀ a b : N, pos a → pos (a + b)
| a Z := by rw [add_zero]; exact id
| a (S b) := λ h, by rw add_succ; exact ⟨λ h, N.no_confusion h⟩  

-- Corollary 2.2.9.
theorem zero_of_eq_zero : ∀ a b : N, a + b = 0 → a = 0 ∧ b = 0
| a Z := by rw add_zero; intro h; exact ⟨h, rfl⟩  
| a (S b) := by rw [add_succ]; intro h; exact (N.no_confusion h)

-- Lemma 2.2.10.
lemma pos_surjective : ∀ a : N, pos a → ∃! b, S b = a 
| Z := λ h, pos.cases_on h (λ h₂, absurd (eq.refl Z) h₂) 
| (S a) := λ h, ⟨a, ⟨rfl, λ b h₂, N.no_confusion h₂ id⟩⟩ 

end N
