import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Limits.HasLimits
import Tltt.Fibrancy.FibrantLift

namespace Tltt.Fibrancy
open Hott
open CategoryTheory

def is_fibration_weak {α β : Type*} (f : α → β) : Type _ :=
  ∀ y : β, IsFibrantWeak { x : α // f x = y }

abbrev tot {α : Type*} (β : α → U) : Σ γ : Type _, γ → α :=
  ⟨Σ a, β a, Sigma.fst⟩

def is_fibration_strict {α β : Type _} (f : α → β) : Type _ :=
  { x // tot x = ⟨α, f⟩ }

def fibration_stable_identity.{u} {α β γ δ : Type u} (p : α = β) (f : β → γ) (q : γ = δ)
                              (fib : is_fibration_strict f)
                              : is_fibration_strict (eqToHom q ∘ f ∘ eqToHom p) := by
  induction p
  induction q
  simp
  assumption

end Tltt.Fibrancy
