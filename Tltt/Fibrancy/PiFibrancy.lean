import Tltt.Fibrancy.Fibration
import Misc

namespace Tltt.Fibrancy
def pi_preserves_fibrancy {α : Type*} {α_is_fib : IsFibrantWeak α} {β : α → Type*}
                          {β_is_fib : ∀ x, IsFibrantWeak (β x)}
                          : (∀ x, β x) ≃ Πₒ x : unlift_weak α, unlift_weak (β ↗ʷx) := calc
  _ ≃ ∀ x : α, unlift_weak (β x) := by
    apply pi_eqv_of_eqv_post
    intro a
    apply Equiv.symm
    apply IsFibrantWeak.unlift_eqv
  _ ≃ ∀ x : unlift_weak α, unlift_weak (β ↗ʷx) := by apply pi_eqv_of_eqv_pre
  _ ≃ Πₒ x : unlift_weak α, unlift_weak (β ↗ʷx) := by apply Hott.Pi.pi_eqv_obj_pi

def pi_fibrant {α : Type*} {β : α → Type*} (α_is_fib : IsFibrantWeak α)
               (β_is_fib : ∀ x, IsFibrantWeak <| β x)
               : IsFibrantWeak <| ∀ x, β x := by
  exists Πₒ x : unlift_weak α, unlift_weak (β ↗ʷx)
  apply Equiv.symm
  apply pi_preserves_fibrancy
end Tltt.Fibrancy
