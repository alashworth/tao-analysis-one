---------------------------------------------------------------------------------
--  Chapter 3 - Set theory                                                     --
--  Analysis 1, Third Edition, Tao                                             --
---------------------------------------------------------------------------------

import data.set .logic

-- Remark: As in other chapters, existing theorems in Lean's proof library are 
-- used if they duplicate theorems described in the chapter.
section
universe u
variable {α : Type u}
-- Remark: consider α to be the "objects" described in chapter 3

-- Axiom 3.1 (Sets are objects). If A is a set, then A is also an object. In 
-- particular, given two sets A and B, it is meaningful to ask whether A is
-- also and element of B.
example (A : set α) (B : set (set α)) : Prop := A ∈ B

-- Definition 3.1.4 (Equality of sets). Two sets A and B are equal, A = B, iff
-- every element of A is an element of B and vice versa.
example (A B : set α) : (∀ x : α, x ∈ A ↔ x ∈ B) → A = B := set.ext  
-- To put it another way, A = B iff every element x of A belongs also to B, and 
-- every element y of B belongs also to A.
theorem ext.elim {A B : set α} (h : A = B) : ∀ x, x ∈ A ↔ x ∈ B := 
λ x, iff.intro (λ h₂, h ▸ h₂) (λ h₂, h.symm ▸ h₂)

-- Axiom 3.2 (Empty set). There exists a set ∅, known as the empty set, which 
-- contains no elements, i.e., for every object x we have x ∉ ∅.
example (A : set α) : (∀ (x : α), x ∉ A) → A = ∅ := 
set.eq_empty_of_forall_not_mem

-- Lemma 3.1.6 (Single choice). Let A be a non-empty set. Then there exists an
-- object x such that x ∈ A.
lemma single_choice {A : set α} (h : A ≠ ∅) : ∃ x, x ∈ A :=
classical.by_contradiction
  (suppose ¬ ∃ x, x ∈ A, 
    have h₂ : ∀ x, x ∉ A, from forall_not_of_not_exists this, 
    show false, from h (set.eq_empty_of_forall_not_mem h₂)) 

-- Axiom 3.3 (Singleton sets and pair sets). If a is an object, then there exists
-- a set {a} whose only element is a, i.e., for every object y, y ∈ {a} iff y = a
-- we refer to {a} as the singleton set whose element is a. Furthermore, if a 
-- and b are objects, then there exists a set {a,b} whose only elements are a 
-- and b; i.e., for every object y, y ∈ {a,b} iff y = a or y = b; we refer to 
-- this set as the pair set formed by a and b.
theorem mem_singleton_iff (a b : α) : a ∈ ({b} : set α) ↔ a = b :=
iff.intro
  (assume ainb,
    or.elim (ainb : a = b ∨ false) (λ aeqb, aeqb) (λ f, false.elim f))
  (assume aeqb, or.inl aeqb)

-- Axiom 3.4 (Pairwise union). Given any two sets A, B, there exists a set A ∪ B,
-- called the union A ∪ B of A and B, whose elements consist of all the elements
-- which belong to A or B or both. 
example (A B : set α): ∀ x : α, x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B :=
λ x, iff.intro id id

-- Lemma 3.1.12. If a and b are objects, then {a,b} = {a} ∪ {b}. If A, B, C
-- are sets, then the union operation is commutative and associative. Also,
-- A ∪ A = A ∪ ∅ = ∅ ∪ A = A.
section set_union
  variables (A B C : set α)
  -- Set union is associative
  example : A ∪ B ∪ C = A ∪ (B ∪ C) := set.union_assoc _ _ _ 
  -- Set union is commutative
  example : A ∪ B = B ∪ A := set.union_comm _ _
  -- Set union identity
  example : A ∪ A = A := set.union_self _
  -- Union of the empty set is an identity relationship
  example : A ∪ ∅ = A := set.union_empty _
end set_union

-- Definition 3.1.14 (Subsets). Let A, B be sets. We say that A is a subset of B,
-- denoted A ⊆ B, iff every element of A is also an element of B.
example (A B : set α) : A ⊆ B ↔ ∀ x : α, x ∈ A → x ∈ B :=
iff.intro (λ h x, set.mem_of_subset_of_mem h) id 
-- We say that A is a proper subset of B, denoted A ⊂ B, if A ⊆ B and A ≠ B
def strict_subset (a b : set α) := a ⊆ b ∧ a ≠ b
instance : has_ssubset (set α) := ⟨strict_subset⟩

-- Proposition 3.1.17 (Sets are partially ordered by set inclusion). Let A, B, C
-- be sets. If A ⊆ B and B ⊆ C, then A ⊆ C. If instead A ⊆ B and B ⊆ A, then 
-- A = B. Finally, if A ⊂ B and B ⊂ C then A ⊂ C. 
section ordering_set_inclusion
  variables {A B C : set α}
  
  -- Set subset is transitive
  example : A ⊆ B → B ⊆ C → A ⊆ C := set.subset.trans
  
  -- Set subset can show equality
  example : A ⊆ B → B ⊆ A → A = B := set.subset.antisymm
  
  lemma subset_of_eq_left (h : A = B) : A ⊆ B := 
  λ x, have h₂ : _, from (ext.elim h) x, iff.mp h₂ 
  
  lemma subset_of_eq_right (h : A = B) : B ⊆ A :=
  λ x, have h₂ : _, from (ext.elim h) x, iff.mpr h₂
  
  -- Proper subsets are transitive
  theorem ssubset.trans : A ⊂ B → B ⊂ C → A ⊂ C := 
  λ ⟨h₁, h₂⟩ ⟨h₃, h₄⟩, 
    and.intro 
      (set.subset.trans h₁ h₃) 
      (show A ≠ C, from λ h₅, 
        have h₇ : _, from subset_of_eq_right h₅,
        have h₈ : _, from set.subset.trans h₃ h₇, 
        have h₉ : A = B, from set.subset.antisymm h₁ h₈, 
        absurd h₉ h₂)
end ordering_set_inclusion

-- Axiom 3.5 (Axiom of specification). Let A be a set, and for each x ∈ A,
-- let P(x) be a property pertaining to x (i.e., P(x) is either a true statement
-- or a false statement). Then there exists a set, called {x ∈ A : P(x) is true}
-- {or simply {x∈A:P(x)} for short}, whose elements are precisely the elements
-- x in A for which P(x) is true. 
example (A : set α) (P : α → Prop) : set α := {x : α | x ∈ A ∧ P x}  

-- Proposition 3.1.27 (Sets form a boolean algebra). Let A, B, C be sets, 
-- and let X be a set containing A,B,C as subsets.
section boolean_algebra
  variables {A B C X : set α} (AinX : A ⊆ X)
  
  -- Minimal element
  example : A ∪ ∅ = A := set.union_empty _
  example : A ∩ ∅ = ∅ := set.inter_empty _
  
  -- Maximal element 
  lemma subset_union_left : A ⊆ A ∪ B := λ x h, or.inl h
  lemma subset_union_right : B ⊆ A ∪ B := λ x h, or.inr h
  
  lemma union_subset (ax : A ⊆ X) (bx : B ⊆ X) : A ∪ B ⊆ X :=
  λ x xab, or.elim xab (λ xa, ax xa) (λ xb, bx xb)

  example : A ∪ X = X := 
    set.subset.antisymm 
      (union_subset AinX (set.subset.refl _)) 
      subset_union_right
  
  lemma inter_subset_left : A ∩ B ⊆ A := λ x h, and.left h
  lemma inter_subset_right : A ∩ B ⊆ B := λ x h, and.right h

  lemma subset_inter (ax : A ⊆ X) (ab : A ⊆ B) : A ⊆ X ∩ B :=
  λ x xa, and.intro (ax xa) (ab xa)
  
  example : A ∩ X = A := 
  set.subset.antisymm 
    inter_subset_left 
    (subset_inter (set.subset.refl _) AinX)

  -- Identity
  example : A ∩ A = A := set.inter_self _
  example : A ∪ A = A := set.union_self _

  -- Commutativity
  example : A ∪ B = B ∪ A := set.union_comm _ _
  example : A ∩ B = B ∩ A := set.inter_comm _ _

  -- Associativity
  example : (A ∪ B) ∪ C = A ∪ (B ∪ C) := set.union_assoc _ _ _
  example : (A ∩ B) ∩ C = A ∩ (B ∩ C) := set.inter_assoc _ _ _

  -- Distributivity
  theorem inter_distrib_left : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := 
  set.ext (λ x, and_distrib _ _ _)

  theorem union_distrib_left : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := 
  set.ext (λ x, or_distrib _ _ _)

  -- Partition
  theorem union_diff_cancel : A ∪ (X \ A) = X := 
  set.ext (λ x, iff.intro 
    (λ h, or.elim h (@AinX x) (λ ⟨h₂, h₃⟩, h₂)) 
    (λ h, or.elim (classical.em (x ∈ A)) 
      (λ h₂, or.inl h₂) 
      (λ h₂, or.inr (and.intro h h₂))))

  example : A ∩ (X \ A) = ∅ := 
  set.ext (λ x, iff.intro 
    (λ ⟨h₁, h₂, h₃⟩, absurd h₁ h₃) 
    (λ h, absurd h (set.not_mem_empty _)))

  -- De Morgan laws
  example : X \ (A ∪ B) = (X \ A) ∩ (X \ B) := 
  set.ext (take x, iff.intro 
    (assume ⟨(h4 : x ∈ X), (h5 : ¬(x ∈ A ∨ x ∈ B))⟩, 
      and.intro 
        (and.intro (h4) (assume h6, h5 (or.inl h6))) 
        (and.intro (h4) (assume h6, h5 (or.inr h6))))
    (assume ⟨⟨h4, h5⟩, h6, h7⟩, 
      and.intro (h6) (assume h8 : x ∈ A ∨ x ∈ B, or.elim h8 
        (assume h9, absurd h9 h5) 
        (assume h9, absurd h9 h7))))

  example : X \ (A ∩ B) = (X \ A) ∪ (X \ B) := 
  set.ext (take x, iff.intro
    (assume ⟨h4, (h5 : ¬(x ∈ A ∧ x ∈ B))⟩, 
      (or.elim (classical.em (x ∈ A)) 
        (or.elim (classical.em (x ∈ B)) 
          (assume h6 h7, or.inl (and.intro h4 (assume h8, h5 ⟨h7, h6⟩))) 
          (assume h6 h7, or.inr (and.intro h4 h6))) 
        (assume h6, or.inl (and.intro h4 h6)))) 
    (assume h4, or.elim h4 
      (assume ⟨h5, h6⟩, and.intro h5 
        (assume ⟨h7, h8⟩, absurd h7 h6)) 
      (assume ⟨h5, h6⟩, and.intro h5 
        (assume ⟨h7, h8⟩, absurd h8 h6)))) 
end boolean_algebra

-- Axiom 3.6 (Replacement)
-- TODO (This is the set theory version of a functor.)

-- Axiom 3.7 (Infinity) 
-- TODO

-- Exercise 3.1.1. Show that the definition of set equality is reflexive,
-- symmetric, and transitive.
theorem ext.refl (A : set α) : A = A :=
set.ext (take x, show x ∈ A ↔ x ∈ A, from iff.intro id id)

theorem ext.symm (A B : set α) : A = B → B = A := 
assume h1, have h2 : _, from ext.elim h1, set.ext (take x, iff.symm (h2 _))

theorem ext.trans (A B C : set α) : A = B → B = C → A = C :=
assume h1 h2, 
  have h3 : _, from ext.elim h1,
  have h4 : _, from ext.elim h2,
  set.ext (take x,
    have h5 : _, from h3 x,
    have h6 : _, from h4 x,
    iff.trans h5 h6)

-- Exercise 3.1.2. Using only definition 3.1.4, axiom 3.2, and axiom 3.3, prove
-- that the sets ∅, {∅}, and {{∅}}, and {∅,{∅}} are all distinct
theorem mem_insert (x : α) (s : set α) : x ∈ insert x s := or.inl rfl

theorem insert_ne_empty (a : α) (s : set α) : insert a s ≠ ∅ :=
λ h, absurd (mem_insert a s) begin rw h, apply set.not_mem_empty end

theorem mem_singleton (a : α) : a ∈ ({a} : set α) := or.inl rfl

theorem singleton_ne_empty (a : α) : ({a} : set α) ≠ ∅ := insert_ne_empty _ _

example : (∅ : set (set α)) ≠ {∅} :=
assume h : ∅ = {∅},
have ∅ ∈ ({∅} : set (set α)), from mem_singleton _,
have ∅ ∈ (∅ : set (set α)), from eq.rec_on h^.symm this,
absurd this (set.not_mem_empty _).

-- TODO: other five cases (figure out a way to use the simplifier to prove them!)

-- Exercise 3.1.5. Let A, B be sets. Show that the three statements 
-- A ⊆ B, A ∪ B = B, and A ∩ B = A are logically equivalent. 
section exercise_315
  variables {A B C : set α}
  open set

  example : A ⊆ B → A ∪ B = B :=
  assume h1 : ∀ x, x ∈ A → x ∈ B,
  ext (take x, iff.intro 
    (assume  h2 : x ∈ A ∨ x ∈ B, 
      or.elim h2 
        (h1 x)  
        (id)) 
  (assume h2 : x ∈ B, or.inr h2))

  example : A ⊆ B → A ∩ B = A :=
  assume h1 : ∀ x, x ∈ A → x ∈ B,
  suffices ∀ (x : α), x ∈ A ∩ B ↔ x ∈ A, from ext this, 
  take x, iff.intro
    (assume h2 : x ∈ A ∧ x ∈ B, h2^.left)
    (assume h2 : x ∈ A, 
      and.intro (h2) (h1 x h2))

  example : A ∪ B = B → A ⊆ B :=
  assume h1 :  A ∪ B = B,
  have h2 : ∀ x, x ∈ A ∨ x ∈ B ↔ x ∈ B, from ext.elim h1, 
  take x, assume h3 : x ∈ A,
  iff.mp (h2 x) (or.inl h3)

  example : A ∪ B = B → A ∩ B = A :=
  assume h1, ext (take x,
    (iff.intro 
      (assume h2, h2^.left) 
      (have h2 : x ∈ A ∨ x ∈ B ↔ x ∈ B, from ext.elim h1 x, 
          assume h3 : x ∈ A, and.intro (h3) (iff.mp h2 (or.inl h3)))))

  example : A ∩ B = A → A ⊆ B :=
  assume h1,
  take x, 
  have h2 : x ∈ A ∧ x ∈ B ↔ x ∈ A, from ext.elim h1 x,
  have h3 : x ∈ A → x ∈ A ∧ x ∈ B, from iff.mpr h2,
  assume h4, have h5 : x ∈ A ∧ x ∈ B, from h3 h4, h5^.right

  example : A ∩ B = A → A ⊆ B :=
  assume h1, take x, assume h2,
  have h3 : x ∈ A ∧ x ∈ B ↔ x ∈ A, from ext.elim h1 x, 
  have x ∈ A → x ∈ A ∧ x ∈ B, from iff.mpr h3,
  have x ∈ A ∧ x ∈ B, from this h2, this^.right
end exercise_315

-- Exercise 3.1.7. Let A, B, and C be sets. Show that A ∩ B ⊆ A and A ∩ B ⊆ B. 
-- Furthermore, show that C ⊆ A and C ⊆ B if and only if C ⊆ A ∩ B. In a similar
-- spirit, show that A ⊆ A ∪ B and B ⊆ A ∪ B, and furthermore that A ⊆ C and 
-- B ⊆ C if and only if A ∪ B ⊆ C.
section
variables {A B C : set α}

example : A ∩ B ⊆ A := take x, assume h1 : x ∈ A ∧ x ∈ B, h1^.left
example : A ∩ B ⊆ B := take x, assume h1 : x ∈ A ∧ x ∈ B, h1^.right

example : C ⊆ A ∧ C ⊆ B ↔ C ⊆ (A ∩ B) := 
iff.intro 
  (assume ⟨h1, h2⟩, take x, assume h3, and.intro (h1 h3) (h2 h3)) 
  (assume h1 : ∀ {x}, x ∈ C → x ∈ (A ∩ B), and.intro 
    (take x, assume h2, have h3 : x ∈ A ∧ x ∈ B, from h1 h2, h3^.left) 
    (take x, assume h2, have h3 : x ∈ A ∧ x ∈ B, from h1 h2, h3^.right))

example : A ⊆ A ∪ B := λ x h, or.inl h
example : B ⊆ A ∪ B := λ x h, or.inr h

example : A ⊆ C ∧ B ⊆ C ↔ A ∪ B ⊆ C :=
iff.intro
  (assume ⟨h1, h2⟩, λ x h3, or.elim h3 (λ h4, h1 h4) (λ h4, h2 h4))
  (assume h1 : ∀ {x}, x ∈ (A ∪ B) → x ∈ C, and.intro 
    (λ x h2, h1 (or.inl h2)) 
    (λ x h2, h1 (or.inr h2)))
end

-- Exercise 3.1.8. Let A and B bet sets. Prove the absorption laws
--  A ∩ (A ∪ B) = A and A ∪ (A ∩ B) = A.
section
variables {A B : set α}

example : A ∩ (A ∪ B) = A := set.ext (take x, 
iff.intro 
  (λ ⟨h1, h2⟩, h1) 
  (λ h1, and.intro h1 (or.inl h1)))

example : A ∪ (A ∩ B) = A := set.ext (take x,
iff.intro
  (λ h1, or.elim h1 id (λ ⟨h2, h3⟩, h2))
  (λ h1, or.inl h1))
end

-- Exercise 3.1.9. Let A, B, and X be sets such that A ∪ B = X and A ∩ B = ∅. 
-- Show that A = X ∖ B and B = X ∖ A.
example (A B X : set α) (h1 : A ∪ B = X) (h2 : A ∩ B = ∅) 
  : A = X \ B ∧ B = X \ A :=
and.intro 
  (set.ext (take x, iff.intro 
    (assume h3 : x ∈ A, and.intro 
      (have h4 : _, from ext.elim h1 x, 
        have h5 : x ∈ A ∨ x ∈ B, from or.inl h3, iff.mp h4 h5) 
      (assume h4, 
        have h5 : _, from ext.elim h2 x, 
        have h6 : x ∈ ∅, from iff.mp h5 ⟨h3, h4⟩, 
        absurd h6 (set.not_mem_empty _))) 
    (assume ⟨h3, h4⟩, 
      have h5 : _, from iff.mpr (ext.elim h1 x) h3, or.elim h5 (id) 
        (assume h6, absurd h6 h4))))
  (set.ext (take x, iff.intro 
    (assume h3, and.intro 
      (have h4 : _, from iff.mp (ext.elim h1 x), h4 (or.inr h3)) 
      (assume h4, have h5 : _, from iff.mp (ext.elim h2 x), h5 ⟨h4, h3⟩))
    (assume ⟨h3, h4⟩, have h5 : _, from iff.mpr (ext.elim h1 x) h3, 
      or.elim h5 (assume h6, absurd h6 h4) (id))))

-- Exercise 3.1.10. Let A and B be sets. Show that the three sets A ∖ B, A ∩ B 
-- and B ∖ A are disjoint, and that their union is A ∪ B.
example (A B : set α) : (A \ B) ∩ (A ∩ B) = ∅ := 
set.ext (take x, iff.intro 
  (assume ⟨⟨h1, h2⟩, h3, h4⟩, absurd h4 h2) 
  (assume h1, have h2 : _, from set.not_mem_empty x, absurd h1 h2)) 

example (A B : set α) : (A ∩ B) ∩ (B \ A) = ∅ := 
set.ext (take x, iff.intro
  (assume ⟨⟨h1, h2⟩, _, h3⟩, absurd h1 h3)
  (assume h1, absurd h1 (set.not_mem_empty x)))

example (A B : set α) : (A \ B) ∩ (B \ A) = ∅ := 
set.ext (take x, iff.intro 
  (assume ⟨⟨h1, h2⟩, h3, h4⟩, absurd h1 h4)
  (assume h1, absurd h1 (set.not_mem_empty x)))

example (A B : set α) : (A \ B) ∪ (A ∩ B) ∪ (B \ A) = A ∪ B := 
set.ext (take x, iff.intro 
  (λ h1, or.elim h1 
    (λ h2, or.elim h2 
      (λ ⟨h3, h4⟩, or.inl h3) 
      (λ ⟨h3, h4⟩, or.inl h3)) 
    (λ h2, or.inr h2^.left))
  (λ h1, or.elim h1
    (λ h2, or.elim (classical.em (x ∈ B)) 
      (λ h3, or.inl (or.inr ⟨h2, h3⟩)) 
      (λ h3, or.inl (or.inl ⟨h2, h3⟩)))
    (λ h2, or.elim (classical.em (x ∈ A)) 
      (λ h3, or.inl (or.inr ⟨h3, h2⟩)) 
      (λ h3, or.inr (⟨h2, h3⟩)))))
end

-- Exercise 3.1.11. Show that the axiom of replacement implies the axiom
-- of specification. TODO

-- Axiom 3.9 (Regularity). TODO
-- Rest of Russell's Paradox chapter - TODO

section functions
open function
variables {W X Y Z : Type}

-- Lemma 3.3.12 (Composition is associative). Let f : X → Y, g : Y → Z,
-- and h : Z → W be functions. Then f ∘ (g ∘ h) = (f ∘ g) ∘ h.
example (f : Z → W) (g : Y → Z) (h : X → Y) : f ∘ (g ∘ h) = (f ∘ g) ∘ h := rfl

-- Exercise 3.3.1. Show that the definition of function equality is reflexive,
-- symmetric, and transitive.
section ex331
  local infix ` ~ `:60 := function.equiv
  -- Reflexivity
  example (f : X → Y) : f ~ f := function.equiv.refl _
  -- Symmetry
  example (f g : X → Y) : f ~ g = g ~ f := 
  propext (iff.intro (λ h x, eq.symm (h x)) (λ h x, eq.symm (h x))) 
  -- Transivitiy
  example (f g h : X → Y) : f ~ g → g ~ h → f ~ h := 
  λ p₁ p₂, function.equiv.trans p₁ p₂ 
end ex331

-- Exercise 3.3.2.
section ex332
  variables (f : X → Y) (g : Y → Z)
  
  example (injf : injective f) (injg : injective g) : injective (g ∘ f) :=
  injective_comp injg injf
  
  example : surjective f → surjective g → surjective (g ∘ f) := 
  λ h₁ h₂, surjective_comp h₂ h₁ 
end ex332

-- Exercise 3.3.3. 
-- TODO

-- Exercise 3.3.4.
example (f₁ f₂ : X → Y) (g₁ g₂ : Y → Z) (h₁ : g₁ ∘ f₁ = g₁ ∘ f₂) 
  (hg : injective g₁) : f₁ = f₂ := 
funext (take x, 
  have h₂ : g₁ (f₁ x) = g₁ (f₂ x) → f₁ x = f₂ x, from @hg (f₁ x) (f₂ x), 
  have h₃ : _, from congr_fun h₁ x,
  h₂ (congr_fun h₁ x))

example (f : X → Y) (g₁ g₂ : Y → Z) (hf : surjective f) (h₁ : g₁ ∘ f = g₂ ∘ f) 
  : g₁ = g₂ :=
funext (λ y, let ⟨x, h₂⟩ := hf y, h₃ := congr_fun h₁ x in by rw -h₂; exact h₃)

-- Exercise 3.3.5
example (f : X → Y) (g : Y → Z) (h₁ : injective (g ∘ f)) : injective f :=
begin
  intros x₁ x₂ h₂,
  apply h₁,
  unfold function.comp,
  rw h₂,
end

example (f : X → Y) (g : Y → Z) (h₁ : surjective (g ∘ f)) : surjective g :=
λ z,
  have h₂ : ∃ x : X, g (f x) = z, from h₁ z,
  exists.elim h₂ (
    λ x (h₃ : g (f x) = z), 
      exists.intro (f x) h₃)

-- Exercise 3.3.6
example (f : X → Y) (h₁ : bijective f) (g : Y → X) (h₂ : left_inverse g f) 
  : ∀ x, g (f x) = x := λ x, h₂ _

example (f : X → Y) (h₁ : bijective f) (g : Y → X) (h₂ : left_inverse g f) 
  : ∀ y : Y, f (g y) = y := 
λ y, 
  let ⟨h₃, h₄⟩ := h₁ in 
  have h₅ : ∃ x, f x = y, from h₄ y, 
  exists.elim h₅ (λ x h₆, 
    suffices f (g y) = f x, by rw [this, h₆], 
    suffices g y = x, by rw [this], 
    suffices g (f x) = x, by rw [-h₆, this], 
    h₂ _)

example (f : X → Y) (h₁ : bijective f) (g : Y → X) (h₂ : left_inverse g f)
  : left_inverse f g :=
left_inverse_of_surjective_of_right_inverse
  (let ⟨(h₃ : injective f), (h₄ : surjective f)⟩ := h₁ in h₄)
  (h₂)

-- Exercise 3.3.7
section ex337
  variables 
    (f : X → Y) 
    (g : Y → Z) 
    (h₁ : injective f) 
    (h₂ : surjective f)
    (h₃ : injective g)
    (h₄ : surjective g)
  
  example : bijective (g ∘ f) := 
  bijective_comp (and.intro h₃ h₄) (and.intro h₁ h₂)

  example : false := sorry
  
  -- TODO : (g ∘ f)⁻¹ = f⁻¹ ∘ g⁻¹ 
end ex337

-- Exercise 3.3.8
-- TODO

end functions
