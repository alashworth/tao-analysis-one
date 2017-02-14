import data.set
open set

-- ch. 3 - set theory ----------------------------------------------------------
section 

universe variables u
variable {α : Type u}

-- definition 3.1.4 (equality of sets)
def def314 {a b : set α} : a = b ↔ ∀ x, x ∈ a ↔ x ∈ b :=
iff.intro
  (assume h1,
    take x,
    iff.intro 
      (assume h2, h1 ▸ h2)
      (assume h2, (eq.symm h1) ▸ h2))
  (assume h1,
    funext (take x, propext (h1 x))).

-- lemma 3.1.6 (single choice)
lemma lem316a (A : set α) (h1 : ¬∃ x, x ∈ A) : ∀ x, x ∉ A := 
take x,
  have h2 : (∃ x, x ∈ A) → false, begin unfold not at h1, exact h1 end, 
  assume h3, h2 (exists.intro x h3).

lemma lem316 (A : set α) (h1 : A ≠ ∅) : ∃ x, x ∈ A :=
classical.by_contradiction 
  (assume h2, 
    have h3 : _, from lem316a A h2, 
    have h4 : _, from eq_empty_of_forall_not_mem h3,
    absurd h4 h1)

-- lemma 3.1.12 (union is commutative)
lemma lem3112a (a b : set α) : a ∪ b = b ∪ a := 
ext (take x, or.comm)

-- lemma 3.1.12.b (union is associative)
lemma lem3112b (a b c : set α) : a ∪ b ∪ c = a ∪ (b ∪ c) := 
ext (take x, or.assoc)

-- proposition 3.1.17 (sets are partially ordered by set inclusion)
proposition prop3117 (a b c : set α) : a ⊆ b ∧ b ⊆ c → a ⊆ c :=
assume ⟨h1, h2⟩, take x, assume h3, h2 (h1 h3)

-- proposition 3.1.27 (sets form a boolean algebra)
-- these were actually implicitly used in lemma 3.1.12a and 3.1.12b
proposition prop3127a (a : set α) : a ∪ ∅ = a ∧ a ∩ ∅ = ∅ :=
and.intro 
  (ext (take x, iff.intro 
    (assume h, begin rw [union_empty] at h, exact h end) 
    (assume h, begin rw [union_empty], exact h end)))
  (ext (take x, and_false (x ∈ a)))

proposition prop3127b (A X : set α) (h1 : A ⊆ X) : A ∪ X = X ∧ A ∩ X = A :=
and.intro
  (ext (take x, iff.intro
    (assume h2,
      have h3 : x ∈ A → x ∈ X, from mem_of_subset_of_mem h1, 
      have h4 : x ∈ A ∨ x ∈ X, from h2, 
      or.elim h4 (h3) (λ h, h))
    (assume h2,or.inr h2)))
  (ext (take x, iff.intro
    (assume h2, have h3 : x ∈ A ∧ x ∈ X, from h2, h3^.left)
    (assume h2, have h3 : x ∈ A → x ∈ X, from mem_of_subset_of_mem h1,
      and.intro h2 (h3 h2))))

end
