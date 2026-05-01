theorem piext {α : Type _} {β γ : α → Type _} (p : ∀ x, β x = γ x) : (∀ x, β x) = (∀ x, γ x) := by
  have h : β = γ := by
    funext x
    apply p
  rw [h]
