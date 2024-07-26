import Tltt.DirectCategories
import Misc.Category
import Tltt.Fibrancy

namespace Tltt.ReedyFibrancy
open CategoryTheory
open Fibrancy

universe u₁ u₂
variable {D : Type u₁} [DirectCategory.{u₁, max u₁ u₂} D]

def is_reedy_at (i : D) (psh : Psh (Below D (rk i + 1))) :=
  is_fibration_strict <| MatchingObject.canonical i psh

def is_reedy_up_to (n : Nat) (psh : Psh (Below D n)) :=
  ∀ i : Below D n, is_reedy_at i.point (restrict₂ i psh)

end Tltt.ReedyFibrancy
