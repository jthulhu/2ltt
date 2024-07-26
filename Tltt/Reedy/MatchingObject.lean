import Mathlib.Tactic.TypeStar
import Tltt.DirectCategories
import Tltt.Fibrancy
import Tltt.Reedy.ReedyPresheaf
import Misc

namespace Tltt.ReedyFibrancy
open CategoryTheory
open Limits (Cone IsLimit)
open Iso (toEquiv)
open Limits.Types (constPUnitFunctor)
open Limits.IsLimit (conePointUniqueUpToIso)
open Fibrancy

variable {J : Type*} [DirectCategory J]

def border (j : J) : Psh J where
  obj i := { f : i.unop ⟶ j // i.unop ≠ j }

  map := by
    intro ⟨l⟩ ⟨i⟩ f ⟨g, l_neq_j⟩
    have f := f.unop
    dsimp only at f g l_neq_j ⊢
    exists f ≫ g
    intro i_eq_j
    apply Nat.lt_irrefl <| rank.obj i
    calc
      _ ≤ rank.obj l := by
        apply PLift.down
        apply ULift.down
        apply rank.map
        assumption
      _ < rank.obj j := by
        apply Nat.lt_of_le_of_ne
        · apply PLift.down
          apply ULift.down
          apply rank.map
          assumption
        · intro rk_l_eq_rk_j
          apply l_neq_j
          apply Eq.symm
          exact congrArg Sigma.fst <| DirectCategory.reflect_identity _ _ g rk_l_eq_rk_j
      _ = rank.obj i := by rw [i_eq_j]

  map_id := by
    intro ⟨i⟩
    dsimp only
    funext ⟨f, i_neq_j⟩
    simp

  map_comp := by
    intro ⟨i⟩ ⟨k⟩ ⟨l⟩ f g
    have f := f.unop
    have g := g.unop
    funext ⟨h, i_neq_j⟩
    dsimp only at f g h i_neq_j
    simp

macro " ∂" j:term : term => ``(border $j)

def border_inc_yoneda (j : J) : NatTrans (∂j) (𝐲j) where
  app := by
    intro ⟨i⟩ ⟨f, _⟩
    exact f
  naturality := by
    intro ⟨k⟩ ⟨l⟩ f
    have f := f.unop
    unfold border yoneda
    funext ⟨g, k_neq_j⟩
    dsimp only at f g k_neq_j
    simp

def MatchObj (j : J) (F : Psh (Below J (rk j))) : Type _ :=
  NatTrans (restrict₃ (∂j)) F

def MatchObj.canonical (F : Psh J) (j : J) : F.obj (.op j) → MatchObj j (restrict₃ F) := by
  intro fj
  have yj_to_F : (𝐲j) ⟶ F := yonedaEquiv.symm fj
  have bj_to_yj : (∂j) ⟶ (𝐲j) := border_inc_yoneda j
  apply restrict₆
  exact bj_to_yj ≫ yj_to_F

def match_obj_eqv (i : J) (F : Psh (Below J (rk i)))
                  : MatchObj i F ≃ MatchingObject i F := by
  -- Lemma 4.5 of the article "Two-level type theory and applications"
  sorry

section
  variable {n : Nat} (X : ReedyPresheaf J n)

  def nat_trans_fibrant (A : Psh (Below J n)) : IsFibrantWeak (NatTrans A X.presheaf) := by
    -- this is a not so easy theorem
    sorry

  def limit_is_fibrant (C : Cone X.presheaf) (p : IsLimit C) : IsFibrantWeak C.pt := by
    apply fibrant_of_eqv_fibrant (α := NatTrans (constPUnitFunctor _) X.presheaf)
    · apply nat_trans_fibrant
    · apply toEquiv
      apply conePointUniqueUpToIso (s := cone_of_nat_unit _)
      apply cone_of_nat_unit_is_lim
      assumption
end

section
  variable (i : J) (X : ReedyPresheaf J (rk i))
  
  def match_obj_fibrant : IsFibrantWeak (MatchObj i X.presheaf) := by
    apply nat_trans_fibrant

  def matching_object_fibrant : IsFibrantWeak (MatchingObject i X.presheaf) := by
    apply fibrant_of_eqv_fibrant (α := MatchObj i X.presheaf)
    · apply match_obj_fibrant
    · apply match_obj_eqv
end

end Tltt.ReedyFibrancy
