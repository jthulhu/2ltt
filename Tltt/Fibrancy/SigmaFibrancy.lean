import Tltt.Fibrancy.Fibration
import Misc

namespace Tltt.Fibrancy

def sigma_preserves_fibrancy {α : Type*} {α_is_fib : IsFibrantWeak α} {β : α → Type*}
                             {β_is_fib : ∀ x, IsFibrantWeak (β x)}
                             : (Σ x, β x) ≃ Σₒ x : unlift_weak α, unlift_weak (β ↗ʷx) := calc
  _ ≃ Σ x : α, unlift_weak (β x) := by
    apply sigma_eqv_of_eqv_post
    intro a
    apply Equiv.symm
    apply IsFibrantWeak.unlift_eqv
  _ ≃ Σ x : unlift_weak α, unlift_weak (β ↗ʷx) := by apply sigma_eqv_of_eqv_pre
  _ ≃ _ := by apply Hott.Sigmaₒ.sigma_eqv_obj_sigma

def sigma_fibrant {α : Type*} {β : α → Type*} (α_is_fib : IsFibrantWeak α)
                  (β_is_fib : ∀ x, IsFibrantWeak (β x))
                  : IsFibrantWeak <| Σ x, β x := by
  exists Σₒ x : unlift_weak α, unlift_weak (β ↗ʷx)
  apply Equiv.symm
  apply sigma_preserves_fibrancy
end Tltt.Fibrancy
