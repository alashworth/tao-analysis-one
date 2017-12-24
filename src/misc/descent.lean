lemma noetherian : 
    ∀ P : ℕ → Prop, (∀ x, (∀ y, y < x → P y) → P x) → (∀ x, P x) := 
λ P h₁ x, well_founded.fix nat.lt_wf h₁ x


