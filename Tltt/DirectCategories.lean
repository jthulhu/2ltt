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

@[ext]
structure OfRank (C : Type*) [DirectCategory C] (n : Nat) where
  point : C
  rank_is : rk point = n

namespace OfRank
  variable {C : Type*} [DirectCategory C]

  def in_own_layer (i : C) : OfRank C (rk i) where
    point := i
    rank_is := by rfl

  instance (i : C) : CoeDep C i (OfRank C (rk i)) where
    coe := OfRank.in_own_layer i

  @[simp]
  def in_own_layer_point (i : C) : (in_own_layer i).point = i := by
    rfl

  instance [DecidableEq C] (n : Nat) : DecidableEq (OfRank C n) := by
    intro x y
    if h : x.point = y.point then
      apply Decidable.isTrue
      ext
      assumption
    else
      apply Decidable.isFalse
      intro
      apply h
      congr

end OfRank

@[ext]
structure Below (C : Type _) [DirectCategory C] (n : Nat) where
  point : C
  rank_is_lt : rk point < n

namespace Below
  variable {C : Type*} [DirectCategory C]

  instance (n : Nat) : Category (Below C n) where
    Hom a b := a.point ⟶ b.point
    id a := 𝟙 a.point
    comp {a b c} f g := f ≫ g
    id_comp := by
      intro a b f
      simp
    comp_id := by
      intro a b f
      simp
    assoc := by
      intro a b c d f g h
      simp

  def forget {n : Nat} : Below C n ⥤ C where
    obj x := x.point
    map {a b} f := f
    map_id := by
      intro
      rfl
    map_comp := by
      intros
      rfl

  @[simp]
  theorem forget.beta_obj {n : Nat} (x : Below C n) : forget.obj x = x.point := by
    rfl

  instance (C : Type _) [DirectCategory C] (n : Nat) : DirectCategory (Below C n) where
    rank := forget ⋙ rank
    reflect_identity := by
      intro x y f p
      simp at p
      have q := DirectCategory.reflect_identity _ _ f p
      simp at q ⊢
      have ⟨q₁, q₂⟩ := q
      apply And.intro
      · ext
        exact q₁
      · exact q₂

  abbrev transport_fwd {n : Nat} (i : OfRank C n) : Below C n ⥤ Below C (rk i.point) := by
    induction i with | mk point rank_is =>
    induction rank_is
    apply Functor.id

  abbrev transport_bwd {n : Nat} (i : OfRank C n) : Below C (rk i.point) ⥤ Below C n := by
    induction i with | mk point rank_is =>
    induction rank_is
    apply Functor.id

  -- abbrev transport' {n : Nat} (i : OfRank C n) : Below C (rk i.point + 1) ⥤ Below C (n+1) := by
  --   induction i with | mk i rank_is =>
  --   induction rank_is
  --   apply Functor.id

  def not_below_zero (x : Below C 0) : False := by
    apply Nat.not_lt_zero
    apply x.rank_is_lt

  def generic {n : Nat} : Below C n ≃ { point : C // rk point < n } where
    toFun := by
      intro ⟨point, rank_is_lt⟩
      exact ⟨point, rank_is_lt⟩
    invFun := by
      intro ⟨point, rank_is_lt⟩
      exact ⟨point, rank_is_lt⟩
    left_inv := by
      intro
      rfl
    right_inv := by
      intro
      rfl

  def up {n : ℕ} (i : Below C n) : Below C (n+1) where
    point := i.point
    rank_is_lt := by
      trans n
      apply i.rank_is_lt
      constructor

  def in_own_layer (i : C) : Below C (rk i + 1) where
    point := i
    rank_is_lt := by simp

  instance (i : C) : CoeDep C i (Below C (rk i + 1)) where
    coe := Below.in_own_layer i

  instance of_below (n : Nat) : Coe (Below C n) (Below C (n+1)) where
    coe := by
      intro ⟨x, _⟩
      exists x
      apply Nat.lt_succ_of_lt
      assumption

  instance of_rank {n : Nat} : Coe (OfRank C n) (Below C (n+1)) where
    coe := by
      intro ⟨x, _⟩
      exists x
      simp [*]

  def inclusion (C : Type*) [DirectCategory C] (n : Nat) : Below C n ⥤ Below C (n+1) where
    obj x := ↑x
    map {_ _} f := f
    map_id := by
      intros
      rfl
    map_comp := by
      intros
      rfl

  @[simp]
  theorem inclusion_obj {n : Nat} (x : Below C n) : (inclusion C n |>.obj x) = ↑x := by
    rfl

  @[simp]
  theorem inclusion_map {n : Nat} {x y : Below C n} (f : x ⟶ y) : (inclusion C n |>.map f) = f := by
    rfl

  def eqv_empty_of_zero : Below C 0 ≃ Empty where
    toFun x := by
      exfalso
      apply x.not_below_zero
    invFun x :=
      x.elim
    left_inv x := by
      exfalso
      apply x.not_below_zero
    right_inv x :=
      x.elim

  def forget' {n : Nat} {i : Below C n} : Below C (rk i + 1) ⥤ Below C n where
    obj x := .mk x.point <| calc
      rk x ≤ rk i := by
        apply Nat.le_of_lt_succ
        apply rank_is_lt
      rk i < n := by apply rank_is_lt
    map {x y} f := f
    map_id := by
      intro
      rfl
    map_comp := by
      intros
      rfl

  @[simp]
  theorem rk_of_forget' {n : Nat} {i : Below C n} (j : Below C (rk i + 1)) : rk (forget'.obj j) = rk j := by
    rfl

  def of_succ_of_rk_ne {n : Nat} (x : Below C (n+1)) (p : rk x ≠ n) : Below C n :=
    .mk x.point <| by
      apply Nat.lt_of_le_of_ne
      · apply Nat.le_of_lt_succ
        exact x.rank_is_lt
      · assumption

  @[simp]
  theorem of_succ_of_rk_ne.beta_point {n : Nat} (x : Below C (n+1)) (p : rk x ≠ n)
                                      : (of_succ_of_rk_ne x p).point = x.point := by
    rfl

end Below


def OfRank.as_below {C : Type*} [DirectCategory C] {n : Nat} (i : OfRank C n) : Below C (n+1) where
  point := i.point
  rank_is_lt := by simp [i.rank_is]
end Tltt
end
