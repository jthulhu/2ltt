import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.IsConnected
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.CategoryTheory.PEmpty

noncomputable section
namespace CategoryTheory
open Limits (Cone IsLimit getLimitCone LimitCone)
open Limits.IsLimit (conePointUniqueUpToIso)
open Limits.Types (constPUnitFunctor)

def op_eqv {C : Type*} [Category C] : Cᵒᵖ ≃ C where
  toFun x := x.unop
  invFun x := .op x
  left_inv := by
    intro x
    rfl
  right_inv := by
    intro x
    rfl

def unit_cone_of_presheaf_over_empty {J : Type*} [Category J] [IsEmpty J] (F : J ⥤ Type _)
                                     : Cone F where
  pt := PUnit
  π := {
    app := fun X => IsEmpty.false X |>.elim
    naturality := fun {X} => IsEmpty.false X |>.elim
  }

def unit_cone_is_limit {J : Type*} [Category J] [IsEmpty J] {F : J ⥤ Type _}
                       : IsLimit (unit_cone_of_presheaf_over_empty F) where
  lift _ _ := .unit
  fac _ j := IsEmpty.false j |>.elim
  uniq := by
    intros
    funext
    rfl

def lim {J : Type*} [Category J] (F : J ⥤ Type _) : Type _ :=
  getLimitCone F |>.cone |>.pt

instance {C : Type*} [Category C] {P : C → Prop} : Category { x : C // P x } where
  Hom x y := x.val ⟶ y.val
  id x := 𝟙 x.val
  comp {x y z} f g := f ≫ g
  id_comp := by
    intros
    simp
  comp_id := by
    intros
    simp
  assoc := by
    intros
    simp

def lim_eqv_unit_of_empty_shape {J : Type*} [Category J] [IsEmpty J] (F : J ⥤ Type _)
                                : lim F ≃ PUnit := by
  apply Iso.toEquiv
  apply conePointUniqueUpToIso (t := unit_cone_of_presheaf_over_empty _)
  · apply LimitCone.isLimit
  · apply unit_cone_is_limit

abbrev Psh (J : Type*) [Category J] :=
  Jᵒᵖ ⥤ Type*

def cone_of_nat_unit {J : Type*} [Category J] (X : Psh J) : Cone X where
  pt := NatTrans (constPUnitFunctor _) X
  π := {
    app := by
      simp
      intro i u
      apply u.app
      exact .unit
    naturality := by
      intro j i f
      funext u
      dsimp at u ⊢
      apply congrFun <| u.naturality _
  }

def cone_of_nat_unit_is_lim {J : Type*} [Category J] (X : Psh J) : IsLimit (cone_of_nat_unit X) where
  lift ψ x := {
    -- X ≡ ψ.pt
    app :=
      fun j _ => ψ.π.app j x
    naturality := by
      intro j i f
      funext
      simp
      have := ψ.π.naturality (X := j) (Y := i) f
      apply congrFun this
  }
  uniq ψ := by
    intro m e
    funext x
    simp
    apply NatTrans.ext
    funext
    apply congrFun <| e _
  fac ψ := by
    intro j
    funext x
    rfl

def limit {J : Type*} [Category J] (X : Psh J) : Type _ :=
  cone_of_nat_unit X |>.pt

abbrev weighted_shape {J : Type*} [Category J] (A X : Psh J) : (Functor.Elements A) ⥤ Type _ where
  obj x := X.obj x.fst
  map {x y} f := X.map f.val

abbrev cone_of_nat {J : Type*} [Category J] (A X : Psh J) : Cone (weighted_shape A X) where
  pt := NatTrans A X
  π := {
    app := by
      simp
      intro ⟨j, a⟩ u
      simp at u ⊢
      apply u.app
      exact a
    naturality := by
      intro ⟨j, aj⟩ ⟨i, ai⟩ ⟨f, h⟩
      simp at h ⊢
      funext u
      simp
      rw [← h]
      apply congrFun <| u.naturality _
  }

def lim_of_weight_shape {J : Type*} [Category J] (A F : Psh J) : IsLimit (cone_of_nat A F) where
  lift ψ x := {
    -- X ≡ ψ.pt
    app :=
      fun j aj => ψ.π.app ⟨j, aj⟩ x
    naturality := by
      intro j i f
      funext aj
      simp
      have := ψ.π.naturality (X := ⟨j, aj⟩) (Y := ⟨i, A.map f aj⟩) ⟨f, by rfl⟩
      apply congrFun this
  }
  uniq ψ := by
    intro m e
    funext x
    simp
    ext
    rename_i j aj
    simp
    apply congrFun <| e ⟨j, aj⟩
  fac ψ := by
    intro ⟨j, aj⟩
    funext x
    simp

macro " 𝐲" j:term : term => ``(yoneda.obj $j)

@[simp]
theorem id_is_id {α : Type*} : 𝟙 α = id := by
  rfl

def comp_op_is_app_op {α β γ : Type*} [Category α] [Category β] [Category γ] (F : α ⥤ β)
                      (G : βᵒᵖ ⥤ γ) (x : α) : (F.op ⋙ G).obj (.op x) = G.obj (.op <| F.obj x) := by
  simp

@[simp]
def comp_id {α β : Type*} [Category α] [Category β] (F : α ⥤ β) : Functor.id _ ⋙ F = F := by
  rfl

@[simp]
def id_op {α : Type*} [Category α] : (Functor.id α).op = Functor.id αᵒᵖ := by
  rfl

instance {C : Type*} [Category C] (P : C → Prop) : Category { x : C // P x } where
  Hom a b := a.val ⟶ b.val
  comp {a b c} f g := f ≫ g
  id a := 𝟙 a.val
  comp_id := by
    intros
    apply Category.comp_id
  id_comp := by
    intros
    apply Category.id_comp
  assoc := by
    intros
    apply Category.assoc

def eqvl_of_empty (C : Type*) [Category C] [IsEmpty C] : C ≌ Discrete Empty :=
  equivalenceOfIsEmpty C (Discrete Empty)

@[simp]
theorem eq_of_empty_shape {C₁ C₂ : Type*} [Category C₁] [Category C₂] (p : C₁ ≃ Empty) (F : C₁ ⥤ C₂)
                     (G : C₁ ⥤ C₂) : F = G := by
  apply CategoryTheory.Functor.ext
  · intro x
    apply Empty.elim
    apply p.toFun
    assumption
  · intro x
    apply Empty.elim
    apply p.toFun
    assumption

end CategoryTheory
end
