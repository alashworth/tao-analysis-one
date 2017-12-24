--------------------------------------------------------------------------------
-- Chapter 3 - Set theory
-- Section 1 - Fundamentals
-- Analysis 1, Third Edition, Tao
--------------------------------------------------------------------------------

import data.set.basic

open set

variable {α : Type}

-- Exercise 3.1.1. Show that the definition of set equality is reflexive,
-- symmetric, and transitive.
example (A : set α) : ∀ x, x ∈ A ↔ x ∈ A := 
λ x, iff_of_eq rfl

example (A B : set α) : ∀ x, (x ∈ A ↔ x ∈ B) → (x ∈ B ↔ x ∈ A) := 
λ x ⟨h₁, h₂⟩, ⟨h₂, h₁⟩  

example (A B C : set α) : 
  ∀ x, (x ∈ A ↔ x ∈ B) → (x ∈ B ↔ x ∈ C) → (x ∈ A ↔ x ∈ C) := 
λ x ⟨h₁, h₂⟩ ⟨h₃, h₄⟩, ⟨λ h₅, h₃ $ h₁ h₅, λ h₅, h₂ $ h₄ h₅⟩

-- Exercise 3.1.2. Skipped. Type inequality is trivial in type theory.

-- Exercise 3.1.3. Prove the remaining claims in Lemma 3.1.13.
lemma eq_or_eq_of_mem_pair {a b y : α} : y ∈ ({a, b}:set α) → y = a ∨ y = b := 
by finish  -- Tao axiom 3.3  

lemma mem_pair_of_eq_or_eq {a b y : α} : y = a ∨ y = b → y ∈ ({a, b}:set α) := 
by finish  -- Tao axiom 3.3

example (a b : α) : ({a, b} : set α) = ({a} ∪ {b}) := 
ext (λ x, iff.intro 
  (λ h₁, or.elim (eq_or_eq_of_mem_pair h₁) 
    (λ h₂, mem_union_left {b} $ mem_singleton_of_eq h₂) 
    (λ h₂, mem_union_right {a} $ mem_singleton_of_eq h₂))
  (λ h₁, or.elim (mem_or_mem_of_mem_union h₁) 
    (λ h₂, mem_pair_of_eq_or_eq $ or.inl $ eq_of_mem_singleton h₂) 
    (λ h₂, mem_pair_of_eq_or_eq $ or.inr $ eq_of_mem_singleton h₂)))

example (A B C : set α) : A ∪ B = B ∪ A := ext (λ x, or.comm)

example (A : set α) : A ∪ A = A ∪ ∅ ∧ A ∪ ∅ = ∅ ∪ A ∧ ∅ ∪ A = A := 
and.intro 
  (ext (λ x, iff.intro 
    (λ h₁, mem_union_left ∅ $ union_self A ▸ h₁)
    (λ h₁, or.elim (mem_or_mem_of_mem_union h₁) 
      (λ h₂, or.inl h₂) 
      (λ h₂, absurd h₂ $ not_mem_empty x)))) 
  (and.intro 
    (union_comm _ _) 
    (ext (λ x, false_or _)))

-- Exercise 3.1.4. Prove the remaining claims in Proposition 3.1.18.
example (A B C : set α) : A ⊆ B → B ⊆ A → A = B := 
λ (h₁ : ∀ x, x ∈ A → x ∈ B) (h₂ : ∀ x, x ∈ B → x ∈ A), 
ext (λ x, {mp := h₁ x, mpr := h₂ x})

example (A B C : set α) : A ⊂ B → B ⊂ C → A ⊂ C := 
λ ⟨h₁, h₂⟩ ⟨h₃, h₄⟩, and.intro 
  (subset.trans h₁ h₃) 
  (λ h₅, h₂ $ subset.antisymm h₁ $ h₅.symm ▸ h₃)

-- Exercise 3.1.5. Let A, B be sets. Show that the three statements 
-- A ⊆ B, A ∪ B = B, and A ∩ B = A are logically equivalent. 
example (A B : set α) : 
  (A ⊆ B ↔ A ∪ B = B) ∧
  (A ∪ B = B ↔ A ∩ B = A) :=
and.intro 
  (iff.intro 
    (λ h₁ : ∀ x, x ∈ A → x ∈ B, ext $ λ x, iff.intro 
      (λ h₂, or.elim h₂ (λ h₃, h₁ x h₃) id) 
      (λ h₂, or.inr h₂)) 
    (λ h₁ x h₂, 
      let ⟨h₃, h₄⟩ := set_eq_def (A ∪ B) B, 
        h₅ := h₃ h₁ x in
      h₅.mp $ or.inl h₂)) 
  (iff.intro 
    (λ h₁, ext (λ x, iff.intro 
      (λ ⟨h₂, _⟩, h₂) 
      (λ h₂, and.intro (h₂) 
        (let ⟨h₃, h₄⟩ := set_eq_def (A ∪ B) B,
          h₅ := h₃ h₁ x in 
        h₅.mp $ or.inl h₂))))  
    (λ h₁, ext (λ x, iff.intro 
      (λ h₂, or.elim h₂ 
        (λ h₃, 
          let ⟨h₄, h₅⟩ := set_eq_def (A ∩ B) A, 
            ⟨h₆, h₇⟩ := h₄ h₁ x,
            ⟨h₈, h₉⟩ := h₇ h₃ in 
          h₉) 
        (id)) 
      (λ h₂, or.inr h₂)))) 

-- Exercise 3.1.6. Prove Proposition 3.1.28.
section
variables A B C X : set α
variables (AsubX : A ⊆ X) 

example : A ∪ ∅ = A := ext $ λ x, iff.intro 
(λ h₁, or.elim h₁ id 
  (λ h₂, absurd h₂ (not_mem_empty x))) 
(λ h₁, or.inl h₁)

example : A ∩ ∅ = ∅ := ext $ λ x, iff.intro 
(λ ⟨h₁, h₂⟩, h₂) 
(λ h₁, and.intro (absurd h₁ (not_mem_empty x)) h₁)

example : A ∪ X = X := ext $ λ x, iff.intro
(λ h₁, or.elim h₁ (λ h₂, AsubX h₂) id) 
(λ h₁, or.inr h₁)

example : A ∩ X = A := ext $ λ x, iff.intro 
(λ ⟨h₁, h₂⟩, h₁) (λ h₁, and.intro h₁ (AsubX h₁))

example : A ∩ A = A := ext $ λ x, iff.intro 
(λ ⟨h₁, h₂⟩, h₁) (λ h₁, and.intro h₁ h₁)

example : A ∪ A = A := ext $ λ x, iff.intro 
(λ h₁, or.elim h₁ id id) (λ h₁, or.inl h₁)

example : A ∪ B = B ∪ A := ext $ λ x, iff.intro 
(λ h₁, or.elim h₁ (λ h₂, or.inr h₂) (λ h₂, or.inl h₂)) 
(λ h₁, or.elim h₁ (λ h₂, or.inr h₂) (λ h₂, or.inl h₂))

example : A ∩ B = B ∩ A := ext $ λ x, iff.intro 
(λ ⟨h₁, h₂⟩, and.intro h₂ h₁) (λ ⟨h₁, h₂⟩, and.intro h₂ h₁)

example : (A ∪ B) ∪ C = A ∪ (B ∪ C) := ext $ λ x, iff.intro 
(λ h₁, or.elim h₁ (λ h₂, or.elim h₂ 
  (λ h₃, or.inl h₃) 
  (λ h₃, or.inr $ or.inl h₃)) 
  (λ h₃, or.inr $ or.inr h₃)) 
(λ h₁, or.elim h₁ 
  (λ h₂, or.inl $ or.inl h₂) 
  (λ h₂, or.elim h₂ 
    (λ h₃, or.inl $ or.inr h₃) 
    (λ h₃, or.inr h₃)))

example : (A ∩ B) ∩ C = A ∩ (B ∩ C) := ext $ λ x, iff.intro 
(λ ⟨⟨h₁, h₂⟩, h₃⟩, ⟨h₁, h₂, h₃⟩) 
(λ ⟨h₁, ⟨h₂, h₃⟩⟩, ⟨⟨h₁, h₂⟩, h₃⟩)

example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := ext $ λ x, iff.intro 
(λ ⟨h₁, h₂⟩, or.elim h₂ (λ h₃, or.inl ⟨h₁, h₃⟩) (λ h₃, or.inr ⟨h₁, h₃⟩)) 
(λ h₁, or.elim h₁ (λ ⟨h₂, h₃⟩, ⟨h₂, or.inl h₃⟩) (λ ⟨h₂, h₃⟩, ⟨h₂, or.inr h₃⟩))

example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := ext $ λ x, iff.intro 
(λ h₁, or.elim h₁ 
  (λ h₂, ⟨or.inl h₂, or.inl h₂⟩) 
  (λ ⟨h₂, h₃⟩, ⟨or.inr h₂, or.inr h₃⟩)) 
(λ ⟨h₁, h₂⟩, or.elim h₁ 
  (λ h₃, or.inl h₃) 
  (λ h₃, or.elim h₂ (λ h₄, or.inl h₄) (λ h₄, or.inr ⟨h₃, h₄⟩))) 

example : A ∪ (X \ A) = X := ext $ λ x, iff.intro 
(λ h₁, or.elim h₁ (λ h₂, AsubX h₂) (λ ⟨h₂, h₃⟩, h₂)) 
(λ h₁, or.elim (classical.em (x ∈ A)) (λ h₂, or.inl h₂) (λ h₂, or.inr ⟨h₁, h₂⟩))

example : A ∩ (X \ A) = ∅ := ext $ λ x, iff.intro 
(λ ⟨h₁, ⟨h₂, h₃⟩⟩, absurd h₁ h₃)
(λ h₁, absurd h₁ (not_mem_empty x))

example : X \ (A ∪ B) = (X \ A) ∩ (X \ B) := ext $ λ x, iff.intro 
(λ ⟨h₁, h₂⟩, ⟨⟨h₁, λ h₃, h₂ $ or.inl h₃⟩, ⟨h₁, λ h₃, h₂ $ or.inr h₃⟩⟩) 
(λ ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩, ⟨h₁, λ h₅, or.elim h₅ 
  (λ h₆, absurd h₆ h₂) 
  (λ h₆, absurd h₆ h₄)⟩)

example : X \ (A ∩ B) = (X \ A) ∪ (X \ B) := ext $ λ x, iff.intro 
(λ ⟨h₁, (h₂ : x ∈ A ∧ x ∈ B → false)⟩, 
  or.elim (classical.em (x ∈ A)) 
    (or.elim (classical.em (x ∈ B)) 
      (λ h₃ h₄, or.inl ⟨h₁, λ h₅, h₂ ⟨h₄, h₃⟩⟩) 
      (λ h₃ h₄, or.inr ⟨h₁, h₃⟩)) 
    (λ h₃, or.inl ⟨h₁, h₃⟩)) 
(λ h₁, or.elim h₁ 
  (λ ⟨h₂, h₃⟩, ⟨h₂, λ ⟨h₄, h₅⟩, h₃ h₄⟩) 
  (λ ⟨h₂, h₃⟩, ⟨h₂, λ ⟨h₄, h₅⟩, h₃ h₅⟩))

end

-- Exercise 3.1.7. Let A, B, and C be sets. Show that A ∩ B ⊆ A and A ∩ B ⊆ B. 
-- Furthermore, show that C ⊆ A and C ⊆ B if and only if C ⊆ A ∩ B. In a similar
-- spirit, show that A ⊆ A ∪ B and B ⊆ A ∪ B, and furthermore that A ⊆ C and 
-- B ⊆ C if and only if A ∪ B ⊆ C.
section
variables (A B C : set α)

example : A ∩ B ⊆ A := λ x (h₁ : x ∈ A ∧ x ∈ B), h₁.left 
example : A ∩ B ⊆ B := λ x (h₁ : x ∈ A ∧ x ∈ B), h₁.right

example : C ⊆ A ∧ C ⊆ B ↔ C ⊆ (A ∩ B) := iff.intro 
(λ ⟨h₁, h₂⟩ x h₃, (mem_inter_iff x A B).mpr $ and.intro 
  (subset.trans h₁ (subset.refl A) h₃) 
  (subset.trans h₂ (subset.refl B) h₃))
(λ h₁, and.intro 
  (by simp at h₁; exact h₁.left)
  (by simp at h₁; exact h₁.right))

example : A ⊆ A ∪ B := λ x h, or.inl h
example : B ⊆ A ∪ B := λ x h, or.inr h

example : A ⊆ C ∧ B ⊆ C ↔ A ∪ B ⊆ C :=
iff.intro
  (λ ⟨h1, h2⟩, λ x h3, or.elim h3 (λ h4, h1 h4) (λ h4, h2 h4))
  (λ h1 : ∀ {x}, x ∈ (A ∪ B) → x ∈ C, and.intro 
    (λ x h2, h1 (or.inl h2)) 
    (λ x h2, h1 (or.inr h2)))
end

-- Exercise 3.1.8. Let A and B bet sets. Prove the absorption laws
--  A ∩ (A ∪ B) = A and A ∪ (A ∩ B) = A.
section
variables {A B : set α}

example : A ∩ (A ∪ B) = A := ext $ λ x, 
iff.intro (λ ⟨h₁, h₂⟩, h₁) (λ h₁, and.intro h₁ (or.inl h₁))

example : A ∪ (A ∩ B) = A := 
ext $ λ x, iff.intro 
  (λ h₁, 
    let h₂ := mem_or_mem_of_mem_union h₁ in 
    or.elim h₂ id 
      (λ ⟨h₂, h₃⟩, h₂))
  (λ h₁, mem_union_left _ h₁)

-- Exercise 3.1.9. Let A, B, and X be sets such that A ∪ B = X and A ∩ B = ∅. 
-- Show that A = X ∖ B and B = X ∖ A.
example (A B X : set α) (h₁ : A ∪ B = X) (h₂ : A ∩ B = ∅) : A = X \ B := 
ext $ λ x, iff.intro 
  (λ h₃, mem_diff 
    (let h₄ := iff.mp (((set_eq_def (A ∪ B) X).mp $ h₁) x) in h₄ $ or.inl h₃) 
    (λ h₄, 
      let h₅ := (iff.mp (set_eq_def (A ∩ B) ∅) h₂ x).mp in 
      h₅ $ and.intro h₃ h₄))
  (λ ⟨h₃, h₄⟩, 
    let h₅ := ((set_eq_def (A ∪ B) X).mp h₁ x).mpr h₃ in 
    or.elim h₅ id 
      (λ h₆, absurd h₆ h₄))

example (A B X : set α) (h₁ : A ∪ B = X) (h₃ : A ∩ B = ∅) : B = X \ A := 
ext $ λ x, 
  have h₄ : x ∈ A ∨ x ∈ B ↔ x ∈ X, by finish,
  have h₅ : x ∈ A ∧ x ∈ B ↔ x ∈ (∅ : set α), from 
    iff.mp ((set_eq_def (A ∩ B) ∅)) h₃ x,
  iff.intro 
    (λ h₆, ⟨h₄.mp $ or.inr h₆, λ h₇, h₅.mp $ ⟨h₇, h₆⟩⟩) 
    (λ ⟨h₅, h₆⟩, or.elim (h₄.mpr h₅) 
      (λ h₇, absurd h₇ h₆) id)

-- Exercise 3.1.10. Let A and B be sets. Show that the three sets A \ B, A ∩ B 
-- and B \ A are disjoint, and that their union is A ∪ B.

example (A B : set α) : (A \ B) ∩ (A ∩ B) = ∅ := ext $ λ x, iff.intro 
(λ ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩, h₂ h₄) 
(λ h₁, absurd h₁ (not_mem_empty x))

example (A B : set α) : (A ∩ B) ∩ (B \ A) = ∅ := ext $ λ x, iff.intro 
(λ ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩, h₄ h₁)
(λ h₁, absurd h₁ (not_mem_empty x))

example (A B : set α) : (A \ B) ∩ (B \ A) = ∅ := ext $ λ x, iff.intro
(λ ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩, h₂ h₃) 
(λ h₁, absurd h₁ (not_mem_empty x))

-- Exercise 3.1.11. Show that the axiom of replacement implies the axiom of
-- specification. Skipped since we don't have set-theory axioms in type theory.

end