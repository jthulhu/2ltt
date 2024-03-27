import Tltt.ObjLang

-- This module gives basic definitions, lemmas and axioms of Hott. Since we cannot "cheat" in
-- this module by peeking inside the definition of object languages, we must "speak" in the
-- object language.

namespace Hott
open Hott

namespace Id
  def subst {α : U} {P : ↑α → U} {a b : ↑α} (h₁ : ↑(a =∘ b)) : ↑(P a) → ↑(P b) := by
    apply Pi.app
    apply Id.elim (P := fun x y _ => ↑(P x →∘ P y))
    intro x
    apply Pi.lam
    exact id
    exact h₁
  
  @[simp]
  theorem refl_refl_is_refl {α : U} (x : ↑α) : (refl x ⬝ refl x) = refl x := by
    rfl
  
  theorem concat_refl {α : U} (x y : ↑α) (p : ↑(x =∘ y)) : ↑(p ⬝ refl y =∘ p) := by
    apply elim (P := fun x y p => p ⬝ refl y =∘ p)
    intro x
    simp
    apply refl

  theorem refl_concat {α : U} (x y : ↑α) (p : ↑(x =∘ y)) : ↑(refl x ⬝ p =∘ p) := by
    apply elim (P := fun x y p => refl x ⬝ p =∘ p)
    intro x
    simp
    apply refl

  @[simp]
  theorem inv_refl_concat {α : U} (x : ↑α) : ((refl x)⁻¹ ⬝ refl x) = refl x := by
    rfl

  theorem inv_concat {α : U} (x y : ↑α) (p : ↑(x =∘ y)) : ↑(p⁻¹ ⬝ p =∘ refl y) := by
    apply elim (P := fun x y p => p⁻¹ ⬝ p =∘ refl y)
    intro x
    simp
    apply refl

  @[simp]
  theorem concat_refl_inv {α : U} (x : ↑α) : (refl x ⬝ (refl x)⁻¹) = refl x := by
    rfl

  theorem concat_inv {α : U} (x y : ↑α) (p : ↑(x =∘ y)) : ↑(p ⬝ p⁻¹ =∘ refl x) := by
    apply elim (P := fun x y p => p ⬝ p⁻¹ =∘ refl x)
    intro x
    simp
    apply refl

  @[simp]
  theorem inv_refl {α : U} (x : ↑α) : (refl x)⁻¹ = refl x := by
    rfl

  theorem inv_inv {α : U} (x y : ↑α) (p : ↑(x =∘ y)) : ↑((p⁻¹)⁻¹ =∘ p) := by
    apply elim (P := fun x y p => (p⁻¹)⁻¹ =∘ p)
    intro x
    simp
    apply refl

  theorem concat_assoc {α : U} (x y z w : ↑α) (p : ↑(x =∘ y)) (q : ↑(y =∘ z)) (r : ↑(z =∘ w))
    : ↑(p ⬝ (q ⬝ r) =∘ (p ⬝ q) ⬝ r) :=
    let P := fun x y p =>
      Π∘ z : α, Π∘ w : α, Π∘ q : y =∘ z, Π∘ r : z =∘ w, p ⬝ (q ⬝ r) =∘ (p ⬝ q) ⬝ r
    let h (x : ↑α) : ↑(P x x (refl x)) := Λ z => Λ w => Λ q => Λ r => by
      have h₁ : ↑(q ⬝ r =∘ refl x ⬝ (q ⬝ r)) := refl_concat _ _ _ |> symm _ _
      apply subst (P := fun qr => qr =∘ (refl x ⬝ q) ⬝ r) h₁
      have h₂ : ↑(q =∘ refl x ⬝ q) := refl_concat _ _ _ |> symm _ _
      apply subst (P := fun q' => q ⬝ r =∘ q' ⬝ r) h₂
      apply refl
    elim (P := P) h x y p @∘ z @∘ w @∘ q @∘ r
end Id

-- Homotopies

def Homotopy.{u, v} {α : U.{u}} {P : ↑α → U.{v}} (f g : ↑(Pi α P)) : U.{max u v} :=
  Π∘ x : α, f $∘ x =∘ g $∘ x

infix:30 " ~ " => Homotopy

namespace Homotopy
  theorem refl {α : U} {P : ↑α → U} (f : ↑(Pi α P)) : ↑(f ~ f) :=
    Λ x => Id.refl (f $∘ x)

  theorem symm {α : U} {P : ↑α → U} (f g : ↑(Pi α P)) (h : ↑(f ~ g)) : ↑(g ~ f) :=
    Λ x => Id.symm (f $∘ x) (g $∘ x) (h $∘ x)

  theorem trans.{u, v} {α : U.{u}} {P : ↑α → U.{v}} (f g h : ↑(Pi α P)) (h₁ : ↑(f ~ g)) (h₂ : ↑(g ~ h))
    : ↑(f ~ h) :=
    Λ x => Id.trans (f $∘ x) (g $∘ x) (h $∘ x) (h₁ $∘ x) (h₂ $∘ x)
end Homotopy

-----

def Arrow.fiber {α : U} {β : U} (f : ↑(α →∘ β)) (y : ↑β) : U :=
  Σ∘ x : α, f $∘ x =∘ y


-- Note: if this function is defined in the current namespace rather than in `U`, then the
-- `Arrow.is_contractible` one doesn't compile anymore (assuming the `is_contractible` function
-- is still pointing to this one.
def U.is_contractible (α : U) : U :=
  Σ∘ a : α, Π∘ x : α, a =∘ x

def Arrow.is_contractible {α β : U} (f : ↑(α →∘ β)) : U :=
  Π∘ y : β, Arrow.fiber f y |>.is_contractible

-- def Arrow.qinv {α : U} {β : U} (f : ↑(Arrow α β)) :=
--   Pi (Arrow β α) (fun g => 

def U.equiv (α : U) (β : U) : U :=
  Σ∘ f : α →∘ β, Arrow.is_contractible f

infix:20 " ≈∘ " => U.equiv

axiom U.univalence {α β : U} : ↑((α ≈∘ β) ≈∘ (α =∘ β))

end Hott

