import Mathlib.CategoryTheory.Category.Basic
import Tltt.Hott

noncomputable section
namespace Tltt.Fibrancy
open Hott

class IsFibrantWeak (α : Type*) : Type _ where
  obj_type : U
  fibrancy : obj_type ≃ α

class IsFibrantStrict (α : Type*) : Type _ where
  obj_type : U
  fibrancy : obj_type = α

abbrev IsFibrantWeak.unlift {α : Type*} (self : IsFibrantWeak α) : U :=
  self.obj_type

abbrev unlift_weak (α : Type*) [IsFibrantWeak α] : U :=
  IsFibrantWeak.obj_type α

abbrev IsFibrantStrict.unlift {α : Type*} (self : IsFibrantStrict α) : U :=
  self.obj_type

abbrev unlift_strict (α : Type*) [IsFibrantStrict α] : U :=
  IsFibrantStrict.obj_type α

instance unit_is_fibrant : IsFibrantWeak PUnit where
  obj_type := Unitₒ
  fibrancy := {
    toFun := fun _ => PUnit.unit
    invFun := fun _ => ()ₒ
    left_inv := by
      intro _
      rfl
    right_inv := by
      intro _
      rfl
  }

instance fibrant_weakening {α : Type*} {ι : IsFibrantStrict α} : IsFibrantWeak α where
  obj_type := ι.obj_type
  fibrancy :=
    have h : ι.obj_type = α := ι.fibrancy
    have l {α β : Type _} (x : α) (p : α = β) (q : β = α) : q ▸ p ▸ x = x := by
      induction p
      rfl
    { toFun := fun x => h ▸ x
      invFun := fun x => h.symm ▸ x
      left_inv := by
        intro x
        simp
        apply l
      right_inv := by
        intro x
        simp
        apply l
    }

end Tltt.Fibrancy
end
