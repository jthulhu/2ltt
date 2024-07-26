import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Tltt.Finite
import Misc

open CategoryTheory
open Limits (limit getLimitCone Cone LimitCone)
open Limits.IsLimit (conePointUniqueUpToIso)
open Limits.Types (terminalLimitCone)

noncomputable section
namespace Tltt

class DirectCategory (C : Type*) extends Category C where
  rank : @Functor C _ Nat (Preorder.smallCategory _)
  reflect_identity : ∀ x y : C, ∀ f : x ⟶ y, rank.obj x = rank.obj y →
                     (Sigma.mk (β := fun y => x ⟶ y) y f) = ⟨x, 𝟙 x⟩
export DirectCategory (rank)

abbrev rk {C : Type*} [DirectCategory C] (x : C) : Nat :=
  rank.obj x

abbrev leq_of_map {C : Type*} [DirectCategory C] {x y : C} (f : x ⟶ y) : rk x ≤ rk y :=
  rank.map f |>.down |>.down

abbrev eq_of_map_of_rk_eq_rk {C : Type*} [DirectCategory C] {x y : C} (f : x ⟶ y)
                             (p : rk x = rk y) : x = y := by
  have := DirectCategory.reflect_identity x y f p
  apply congrArg (·.fst) this.symm

@[simp]
theorem eq_id {C : Type*} [DirectCategory C] {x : C} (f : x ⟶ x) : f = 𝟙 x := by
  have := DirectCategory.reflect_identity x x f rfl
  simp at this
  assumption

end Tltt
end
