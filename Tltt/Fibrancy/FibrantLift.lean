import Tltt.Fibrancy.FibrantType
import Misc.Rewrite

namespace Tltt.Fibrancy
open Hott

instance lift_is_fibrant (α : Typeₒ) : IsFibrantStrict α where
  obj_type := α
  fibrancy := rfl

@[simp]
def IsFibrantStrict.unlift_eq {α : Type*} (self : IsFibrantStrict α) : self.unlift = α :=
  self.fibrancy

def IsFibrantWeak.unlift_eqv {α : Type*} (self : IsFibrantWeak α) : self.unlift ≃ α :=
  self.fibrancy

abbrev up_strict {α : Type*} [ι : IsFibrantStrict α] (x : ι.unlift) : α :=
  ι.unlift_eq ▸ x

abbrev up_weak {α : Type*} [ι : IsFibrantWeak α] (x : ι.unlift) : α :=
  ι.fibrancy x

prefix:max "↗ˢ" => up_strict
prefix:max "↗ʷ" => up_weak

abbrev down_strict {α : Type*} [ι : IsFibrantStrict α] (x : α) : ι.unlift :=
  ι.unlift_eq.symm ▸ x

abbrev down_weak {α : Type*} [ι : IsFibrantWeak α] (x : α) : ι.unlift :=
  ι.unlift_eqv.symm x

prefix:max "↘ˢ" => down_strict
prefix:max "↘ʷ" => down_weak

@[simp]
theorem up_down_id_strict {α : Type*} [IsFibrantStrict α] (x : α) : ↗ˢ↘ˢx = x := by
  apply rw_rw_is_id

@[simp]
theorem up_down_id_weak {α : Type*} [ι : IsFibrantWeak α] (x : α) : ↗ʷ↘ʷx = x := by
  apply ι.unlift_eqv.right_inv

@[simp]
theorem down_up_id_strict {α : Type*} [ι : IsFibrantStrict α] (x : ι.unlift) : ↘ˢ↗ˢx = x := by
  apply rw_rw_is_id

@[simp]
theorem down_up_id_weak {α : Type*} [ι : IsFibrantWeak α] (x : ι.unlift) : ↘ʷ↗ʷx = x := by
  apply ι.unlift_eqv.left_inv
end Tltt.Fibrancy
