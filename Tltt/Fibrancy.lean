import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Misc
import Finite
import Tltt.Hott
import Tltt.DirectCategories

import Tltt.Fibrancy.FibrantType
import Tltt.Fibrancy.FibrantLift
import Tltt.Fibrancy.Fibration
import Tltt.Fibrancy.PiFibrancy
import Tltt.Fibrancy.SigmaFibrancy

open CategoryTheory
open Limits (limit)

noncomputable section
namespace Tltt.Fibrancy
open Hott

def fibrant_of_eqv_fibrant {α β : Type*} (α_is_fib : IsFibrantWeak α) (α_eqv_β : α ≃ β)
                           : IsFibrantWeak β := by
  exists α_is_fib.obj_type
  calc
    _ ≃ α := α_is_fib.fibrancy
    _ ≃ _ := α_eqv_β

def prod_is_fibrant {α₁ α₂ : Type*} (α₁_is_fib : IsFibrantWeak α₁) (α₂_is_fib : IsFibrantWeak α₂)
                    : IsFibrantWeak (α₁ × α₂) := by
  apply fibrant_of_eqv_fibrant (α := Σ _ : α₁, α₂)
  · apply sigma_fibrant
    · assumption
    · intro
      assumption
  · apply Equiv.symm
    apply prod_eqv_sigma

def fintype_is_cofibrant {α : Type*} [Finite α] [DecidableEq α]
                         {β : α → Type*} {β_is_fib : ∀ x, IsFibrantWeak (β x)}
                         : IsFibrantWeak <| ∀ a : α, β a := by
  generalize h : |α| = n
  induction n generalizing α with
  | zero =>
    apply fibrant_of_eqv_fibrant
    · exact unit_is_fibrant.{0}
    · apply Equiv.symm
      apply Finite.from_card_zero_eqv_unit (α := α)
      assumption
  | succ n ih =>
    have z : α := Finite.el_of_card_succ <| by
      rw [h]
      simp
    let previous := { x : α // x ≠ z }
    apply fibrant_of_eqv_fibrant (α := (∀ x : previous, β ↑x) × (β z))
    · apply prod_is_fibrant
      · apply ih
        · intro x
          apply β_is_fib
        rw [Finite.card_of_remove_one, h]
        simp
      · apply β_is_fib
    · apply Equiv.symm
      apply Finite.pi_eqv_pi_prod

end Tltt.Fibrancy
end
