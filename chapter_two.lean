namespace ch2

-- in order to avoid conflicts with lean's built-in nat type,
-- we define the whole numbers

inductive whole : Type :=
| zero : whole
| succ : whole → whole

notation 0 := whole.zero

definition plus : whole → whole → whole
| plus 0 m     := m
| plus (whole.succ n) m := whole.succ (plus n m)

infix ` + ` := plus

section addition

variables m n : whole

lemma plus_0_n : 0 + n = n := rfl
lemma plus_Sn_m : whole.succ n + m = whole.succ(n + m) := rfl

lemma plus_n_0 : n + 0 = n := 
whole.induction_on n 
 (show 0 + 0 = 0, from plus_0_n 0)
  (take n, assume ih : n + 0 = n, 
  show whole.succ n + 0 = whole.succ n, from calc
      whole.succ n + 0 = whole.succ (n + 0) : plus_Sn_m
                   ... = whole.succ n : ih)

lemma plus_n_Sm : n + whole.succ m = whole.succ (n + m) :=
begin
  induction n with n m,
  rewrite plus_0_n,

  rewrite plus_Sn_m,
  rewrite m_1
end

lemma plus_n_Sm : n + whole.succ m = whole.succ (n + m) :=
whole.induction_on n
  (show 0 + whole.succ m = whole.succ (0 + m), from calc
    0 + whole.succ m = whole.succ m : plus_0_n
                 ... = whole.succ (0 + m) : plus_0_n)
  (take n, take m, assume ih : n + whole.succ m = whole.succ (n + m),
  show whole.succ n + whole.succ m = whole.succ ((whole.succ n) + m), from
    calc
      whole.succ n + whole.succ m = whole.succ (whole.succ (n + m)) : plus_Sn_m
      whole.succ n + whole.succ m = whole.succ (whole.succ (n + m)) : plus_Sn_m
      whole.succ n + whole.succ m = whole.succ ((whole.succ n) + m) : ih)
--whole.induction_on n
  --(show 0 + whole.succ m = whole.succ (0 + m), from calc
    --0 + whole.succ m = whole.succ m : plus_0_n
    --... = whole.succ (0 + m) : plus_0_n)
  --(take n m, assume ih : n + whole.succ m = whole.succ (n + m),
   -- show whole.succ n + whole.succ m = whole.succ (whole.succ n + m), from calc
     -- whole.succ n + whole.succ m = whole.succ ((whole.succ n) + m) : plus_Sn_m)


end addition

end ch2
