/-------------------------------------------------------------------------------\
  Solutions for chapter two: the natural numbers                                  
  Analysis 1, Third Edition, Tao                                             
\-------------------------------------------------------------------------------/

import logic data.nat
open classical nat

namespace ch2
local abbreviation S := nat.succ
local abbreviation induction_on := @nat.induction_on

-- axiom 2.1 - zero is a natural number
example : ℕ := 0


-- axiom 2.2 - if n is a natural number, so is S(n)
example (n : ℕ) : ℕ := S n 


-- axiom 2.3 - zero is not the successor of any natural number
lemma zero_not_succ (n : ℕ) : S n = 0 ↔ false :=
begin
  split, exact nat.no_confusion, intro h; exfalso; assumption
end

-- axiom 2.4 - the successor function is injective
theorem succ_inj (a b : ℕ) : S a = S b ↔ a = b := 
begin
  split,
    intro h, injection h, assumption,
    intro h; rewrite h
end


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
      have h3 : S (a + b) = S (a + c) , by rewrite [-h2, -h1, h0],
      have h4 :     a + b = a + c     , by rewrite [-succ_inj, h3],
      ih h4
    qed)

-- definition 2.2.7
definition is_positive :  ℕ → Prop
| (nat.zero  ) := false
| (nat.succ _) := true

-- proposition 2.2.8
proposition pos_nat_num (a b : ℕ) (h : is_positive a) : is_positive (a + b) :=
induction_on b
  (show is_positive (a + 0), by rewrite [add_n_0]; assumption)
  (take b,
    assume ih : is_positive (a + b),
    show is_positive (a + S b), by rewrite [add_n_Sm, ↑is_positive]; trivial)


-- corollary 2.2.9
/- suppose that a neq 0, or b neq zero. if a neq 0, then a is positive, and then 
a + b = 0 is positive by pos_nat_num, a contradiction. a similar argument follows for b -/
example (a b : ℕ) (h : a + b = 0) : a = 0 ∧ b = 0 :=
begin
  apply by_contradiction,
  rewrite not_and_iff_not_or_not,
  intro h, cases h with [ha, hb],
    -- showing false from ¬a = 0
    -- if a neq 0 (premise), then is_positive a
    have hapos : is_positive a, begin
      cases a, 
        unfold not at ha, 
        have htriv : (nat.zero = nat.zero), from rfl,
        have hfalse : false, from ha htriv,
        unfold is_positive, assumption, 

        rewrite add_Sn_m at h, apply nat.no_confusion h
    end,
    -- if is_positive a, then is_positive (a + b)
    have habpos : is_positive (a + b), begin
      apply pos_nat_num a b hapos
    end,

    -- contradiction! 
    rewrite [h at habpos, ↑is_positive at habpos]; assumption,

    -- showing false from ¬b = 0
    have hb_pos : is_positive b, begin
      cases b with b,
        have (nat.zero = nat.zero), from rfl,
        apply not.elim hb this,

        rewrite add_n_Sm at h, apply nat.no_confusion h
    end,

    -- if is_positive b, then is_positive (a + b)
    have h_abpos : is_positive (a + b), begin
      rewrite add.comm,  apply pos_nat_num b a hb_pos
    end,

    -- contradiction!
    rewrite h at h_abpos, unfold is_positive at h_abpos, assumption 
end


-- corollary 2.2.9
example (a b : ℕ) : (a + b = 0) → a = 0 ∧ b = 0 :=
begin
  cases a,
  intro h, split, trivial, rewrite [-h, add_0_n],
  intro h, rewrite [add_Sn_m at h], apply nat.no_confusion h
end

-- lemma 2.2.10 
/-
example : ∀(a : ℕ), is_positive a → ∃!(b : ℕ), S b = a :=
begin
  intros a h,
  induction a with a ih,
      unfold is_positive at h, exfalso, assumption,
    repeat split,
      clear h, intro y h0, rewrite [-succ_inj, h0] 
end
-/
-- definition 2.2.11

end ch2
