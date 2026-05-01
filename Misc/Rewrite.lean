import Mathlib.Tactic.TypeStar
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Limits.HasLimits

open CategoryTheory (eqToHom)

@[simp]
theorem rw_rw_is_id {α β : Type _} (x : α) (p : α = β) (q : β = α) : q ▸ p ▸ x = x := by
  induction p
  rfl

@[simp]
theorem cast_app_eq_app {α : Type*} {β : α → Type*} (f : (a : α) → β a) {x y : α} (p : β y = β x) (q : y = x)
           : cast p (f y) = f x := by
  induction q
  simp

@[simp]
theorem eqToHom_simp {α β : Type _} (p : α = β) (q : β = α)
                 : eqToHom (C := Type _) p ∘ eqToHom (C := Type _) q = id := by
  induction p
  rfl
