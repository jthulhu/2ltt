import Mathlib.Tactic.TypeStar
import Tltt.DirectCategories
import Tltt.Reedy.ReedyPresheaf
import Tltt.Fibrancy
import Misc

namespace Tltt.ReedyFibrancy
open CategoryTheory
open Fibrancy

variable {D : Type*} [DirectCategory D]

def Sk (n : Nat) (A : Psh D) : Psh D where
  obj d :=
    if rk d.unop < n then A.obj d else Empty

  map {j i} f := by
    dsimp only
    if h : rk j.unop < n then
      have rk_i_lt_n : rk i.unop < n := calc
        rk i.unop ≤ rk j.unop := leq_of_map f.unop
        rk j.unop < n := h
      have h₁ : (if rk j.unop < n then A.obj j else Empty) = A.obj j := by
        simp
        intro
        exfalso
        apply Nat.not_lt_of_le <;> assumption
      have h₂ : (if rk i.unop < n then A.obj i else Empty) = A.obj i := by
        simp
        intro
        exfalso
        apply Nat.not_lt_of_le <;> assumption
      exact eqToHom h₂.symm ∘ A.map f ∘ eqToHom h₁
    else
      have h₁ : (if rk j.unop < n then A.obj j else Empty) = Empty := by
        simp
        intro
        contradiction
      refine ?map ∘ eqToHom h₁
      intro
      contradiction

  map_id := by
    intro j
    simp
    intro h
    funext a
    have : (if rk j.unop < n then A.obj j else Empty) = Empty := by
      simp
      intro
      exfalso
      apply Nat.not_lt_of_le
      exact h
      assumption
    rw [this] at a
    contradiction

  map_comp := by
    intro ⟨j⟩ ⟨i⟩ ⟨k⟩ f g
    simp
    split_ifs <;> rename_i h
    · generalize_proofs pf₁ pf₂ pf₃ pf₄ pf₅ pf₆ pf₇
      conv =>
        rhs
        erw [apply_dite (CategoryStruct.comp (obj := Type _) (eqToHom pf₃ ∘ A.map f ∘ eqToHom pf₂) ·)]
      erw [apply_dite (eqToHom pf₁ ∘ (A.map f ≫ A.map g) ∘ eqToHom pf₂ = ·)]
      split_ifs <;> rename_i h'
      · generalize_proofs pf₈
        show _ ∘ A.map g ∘ A.map f ∘ _ = _ ∘ _ ∘ _ ∘ _
        show _ ∘ _ ∘ _ ∘ _ = eqToHom pf₁ ∘ A.map g ∘ (eqToHom pf₈ ∘ eqToHom pf₃) ∘ _
        simp
      · exfalso
        apply Nat.lt_irrefl n
        calc
          n ≤ rk i := Nat.le_of_not_lt h'
          rk i ≤ rk j := leq_of_map f.unop
          rk j < n := h
    · funext x
      simp [h] at x
      contradiction

variable {n : Nat} (X : ReedyPresheaf D n) in
def nat_trans_fibrant (A : Psh (Below D n)) : IsFibrantWeak (NatTrans A X.presheaf) := by
  -- Skeletal functors are useful for this proof.
  sorry

end Tltt.ReedyFibrancy
