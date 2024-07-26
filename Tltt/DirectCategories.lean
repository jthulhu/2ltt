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

def empty.functor (D : Type _) [DirectCategory D] : Psh (Below D 0) where
  obj x := by
    exfalso
    apply x.unop.not_below_zero
  map {x _} _ _ := by
    exfalso
    exact x.unop.not_below_zero
  map_id := by
    intro ⟨x⟩
    exfalso
    exact x.not_below_zero
  map_comp := by
    intro ⟨x⟩
    exfalso
    exact x.not_below_zero

def OfRank.as_below {C : Type*} [DirectCategory C] {n : Nat} (i : OfRank C n) : Below C (n+1) where
  point := i.point
  rank_is_lt := by simp [i.rank_is]

instance {C : Type*} [DirectCategory C] {P : C → Prop} : DirectCategory { x : C // P x } where
  rank := {
    obj := (rank.obj <| Subtype.val ·)
    map := rank.map
    map_comp := by
      intros
      simp
      apply rank.map_comp
    map_id := by
      intros
      simp
  }
  reflect_identity := by
    intro x y f e
    have := DirectCategory.reflect_identity x.val y.val f e
    simp
    simp at this
    cases this
    constructor
    apply Subtype.coe_eq_of_eq_mk
    repeat assumption


@[simp]
def cast_cast_eq {D : Type*} [DirectCategory D] {n : Nat} (x : Below D (n+1)) (p : rk x ≠ n)
                 : ↑(x.of_succ_of_rk_ne p) = x := by
  rfl

def under {C : Type _} [Category C] (x : C) :=
  Σ y : C, { _f : y ⟶ x // x ≠ y }

instance under_is_category {C : Type _} [ι : Category C] (x : C) : Category (under x) where
  Hom a b := { f : a.1 ⟶ b.1 // f ≫ b.2.1 = a.2.1 }
  id a := ⟨𝟙 a.1, by apply ι.id_comp⟩
  comp {a b c} f g := ⟨f.1 ≫ g.1, by rw [ι.assoc, g.2, f.2]⟩
  id_comp := by
    intro a b f
    simp
  comp_id := by
    intro a b f
    simp
  assoc := by
    intros
    simp

def under.inclusion (C : Type _) [DirectCategory C] (x : C) : under x ⥤ (Below C (rk x)) where
  obj y := .mk y.fst <| by
    apply Nat.lt_of_le_of_ne
    · apply leq_of_map
      apply y.snd.val
    · intro rk_y_eq_rk_x
      apply y.snd.prop
      have := DirectCategory.reflect_identity _ _ y.snd.val rk_y_eq_rk_x
      apply congrArg (·.fst) this
  map {_ _} f := f.val
  map_id := by
    intros
    rfl
  map_comp := by
    intros
    rfl

abbrev MatchingObject.functor {D : Type*} [DirectCategory D] (i : D)
                              (X : Psh (Below D (rk i))) : Psh (under i) :=
  (under.inclusion D i).op ⋙ X

def MatchingObject.limit_cone {D : Type*} [DirectCategory D] (i : D)
                                  (X : Psh (Below D (rk i))) : LimitCone (functor i X) :=
  getLimitCone <| MatchingObject.functor i X

def MatchingObject {D : Type*} [DirectCategory D] (i : D) (X : Psh (Below D (rk i))) : Type _ :=
  MatchingObject.limit_cone i X |>.cone |>.pt

section Restrictions
variable {D : Type*} [DirectCategory D] {n : ℕ}

-- @[simp]
def restrict₁ (F : Psh (Below D (n+1))) : Psh (Below D n) :=
  (Below.inclusion _ _).op ⋙ F

@[simp]
theorem restrict₁.obj_beta (F : Psh (Below D (n+1))) (i : Below D n)
                           : (restrict₁ F).obj (.op i) = F.obj (.op i) := by
  rfl

-- @[simp]
def restrict₂ (i : Below D n) (F : Psh (Below D n)) : Psh (Below D (rk i + 1)) :=
  Below.forget'.op ⋙ F

-- @[simp]
def restrict₃ (F : Psh D) : Psh (Below D n) :=
  Below.forget.op ⋙ F

@[simp]
theorem restrict₃.obj_beta (F : Psh D) (i : Below D n)
                           : (restrict₃ F).obj (.op i) = F.obj (.op i.point) := by
  rfl

@[simp]
def restrict₃.beta (F : Psh D) (x : Below D n) : (restrict₃ F).obj (.op x) = F.obj (.op x.point) := by
  rfl

-- @[simp]
def restrict₄ (i : OfRank D n) (F : Psh (Below D (n+1))) : Psh (Below D (rk i.point + 1)) :=
  (Below.forget' (i := i.as_below)).op ⋙ F

def func_of_rk_eq (i : D) (p : rk i = n) : Below D (rk i) ⥤ Below D n := by
  induction p
  apply Functor.id

@[simp]
theorem func_of_rk_eq_refl (i : D) (p : rk i = rk i) : func_of_rk_eq i p = Functor.id _ := by
  rfl

def restrict₅ (i : OfRank D n) (F : Psh (Below D n)) : Psh (Below D (rk i.point)) :=
  (func_of_rk_eq i.point i.rank_is).op ⋙ F

@[simp]
theorem restrict₅.refl_beta (i : D) (F : Psh (Below D (rk i))) (p : rk i = rk i) : restrict₅ ⟨i, p⟩ F = F := by
  rfl

def restrict₆ (F G : Psh D) (η : NatTrans F G) : NatTrans (restrict₃ (n := n) F) (restrict₃ G) where
  app := by
    intro ⟨x⟩
    simp
    apply η.app
  naturality := by
    intros
    simp
    apply η.naturality
end Restrictions

namespace MatchingObject
  variable {D : Type*} [DirectCategory D] (i : D)

  namespace Canonical
    variable (X : Psh (Below D (rk i + 1)))
    def canonical_cone : Cone <| functor i (restrict₁ X) where
      pt := X.obj <| .op i
      π := {
        app := fun j => by
          simp
          let ⟨⟨_, f, _⟩⟩ := j
          unfold under.inclusion
          simp
          exact X.map f.op
        naturality := by
          intro a b f
          let ⟨⟨x, xm, x_neq_i⟩⟩ := a
          let ⟨⟨y, ym, y_neq_i⟩⟩ := b
          simp
          unfold under.inclusion
          simp
          have h := f.unop.property
          simp at h
          show _ ∘ _ = _
          dsimp
          conv =>
            lhs
            erw [← h]
          simp
          conv =>
            rhs
            erw [← X.map_comp]
          rfl
      }

    def canonical : X.obj (.op i) → MatchingObject i (restrict₁ X) :=
      limit_cone i (restrict₁ X) |>.isLimit |>.lift <| canonical_cone i X

    section uniqueness
    variable (f : X.obj (.op i) → MatchingObject i (restrict₁ X))

    def is_unique (q : ∀ j, (limit_cone i (restrict₁ X)).cone.π.app j ∘ f = (canonical_cone i X).π.app j)
                : f = canonical i X := by
      unfold canonical
      apply limit_cone i (restrict₁ X) |>.isLimit |>.uniq (s := canonical_cone i X)
      assumption
    end uniqueness
  end Canonical
  export Canonical (canonical)

  def eqv_unit_of_card_zero [d : DirectCategory D] (i : D) {ι : Finite (Below D (rank.obj i))}
                            (X : (Below D (rank.obj i))ᵒᵖ ⥤ Type _) (p : |Below D (rank.obj i)| = 0)
                            : MatchingObject i X ≃ PUnit := by
    apply Iso.toEquiv
    have : IsEmpty (under i)ᵒᵖ := by
      constructor
      intro j
      apply Nat.not_lt_zero
      apply Fin.isLt
      rw [← p]
      apply ι.equiv.toFun
      constructor
      rotate_left
      · exact j.unop.fst
      · apply Nat.lt_of_le_of_ne
        · apply PLift.down
          apply ULift.down
          apply rank.map
          apply j.unop.snd.val
        · intro rank_j_eq_rank_i
          apply j.unop.snd.prop
          apply congrArg Sigma.fst
            <| d.reflect_identity j.unop.fst i j.unop.snd.val rank_j_eq_rank_i
    apply conePointUniqueUpToIso (t := unit_cone_of_presheaf_over_empty _)
    · apply LimitCone.isLimit
    · apply unit_cone_is_limit

end MatchingObject

end Tltt
end
