import data.nat
open nat

-- lean doesn't have any examples of their well founded recursion syntax
lemma add_n_0 : ∀(n : ℕ), n + 0 = n :=
nat.induction_on n
  (show 0 + 0 = 0, from add)
  (take (n : ℕ) (IH : n + 0 = n) (H : succ n + 0 = succ n),
    show H, from calc
      n + 0 = n : IH
      succ (n + 0) = succ (n) : add_inj
      succ n + 0 = succ n : add)
