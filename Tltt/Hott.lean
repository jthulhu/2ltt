import Tltt.ObjLang
import Tltt.Tactics

set_option autoImplicit false

noncomputable section

-- This module gives basic definitions, lemmas and axioms of Hott. Since we cannot "cheat" in
-- this module by peeking inside the definition of object languages, we must "speak" in the
-- object language.

namespace Hott
open Hott

@[reducible]
def Funₒ.id {α : U} : α →ₒ α :=
  Λ x => x

@[simp]
def Funₒ.id_is_id {α : U} {x : α} : (id $ₒ x) = x := by
  rfl

namespace Id

  section
    variable {α : U}
    
    @[simp]
    theorem refl_refl_is_refl (x : α) : (refl x ⬝ refl x) = refl x := by
      rfl

    theorem concat_refl (x y : α) (p : x =ₒ y) : p ⬝ refl y =ₒ p := by
      path_inductionₒ p
      rflₒ

    theorem refl_concat (x y : α) (p : x =ₒ y) : refl x ⬝ p =ₒ p := by
      path_inductionₒ p
      rflₒ

    @[simp]
    theorem inv_refl_concat (x : α) : ((refl x)⁻¹ ⬝ refl x) = refl x := by
      rfl

    theorem inv_concat (x y : α) (p : x =ₒ y) : p⁻¹ ⬝ p =ₒ refl y := by
      path_inductionₒ p
      rflₒ

    @[simp]
    theorem concat_refl_inv (x : α) : (refl x ⬝ (refl x)⁻¹) = refl x := by
      rfl

    theorem concat_inv (x y : α) (p : x =ₒ y) : p ⬝ p⁻¹ =ₒ refl x := by
      path_inductionₒ p
      rflₒ

    @[simp]
    theorem inv_refl (x : α) : (refl x)⁻¹ = refl x := by
      rfl

    theorem inv_inv (x y : α) (p : x =ₒ y) : (p⁻¹)⁻¹ =ₒ p := by
      path_inductionₒ p
      rflₒ

    def concat_assoc (x y z w : α) (p : x =ₒ y) (q : y =ₒ z) (r : z =ₒ w)
                     : p ⬝ (q ⬝ r) =ₒ (p ⬝ q) ⬝ r := by
      path_inductionₒ p
      introₒ q
      path_inductionₒ q
      introₒ r
      path_inductionₒ r
      rflₒ
  end
  
  section
    variable {α β γ : U}
    -- variable (f : α → β) (g : β → γ)
    -- variable (x y z : α)
    -- variable (p : x =ₒ y) (q : y =ₒ z)

    -- Lemma 2.2.1
    def ap (f : α → β) {x y : α} (p : x =ₒ y) : f x =ₒ f y := by
      path_inductionₒ p
      rflₒ

    @[simp]
    theorem ap_refl (f : α → β) (x : α) : ap f (refl x) = refl (f x) := by
      rfl

    -- Lemma 2.2.2
    theorem ap_concat (f : α → β) (x y z : α) (p : x =ₒ y) (q : y =ₒ z)
                      : ap f (p ⬝ q) =ₒ ap f p ⬝ ap f q := by
      path_inductionₒ p
      introₒ q
      rwₒ [refl_concat _ _ _, refl_concat _ _ _]

    theorem ap_inv (f : α → β) (x y : α) (p : x =ₒ y) : ap f p⁻¹ =ₒ (ap f p)⁻¹ := by
      path_inductionₒ p
      rflₒ

    theorem ap_id (x y : α) (p : x =ₒ y) : ap Funₒ.id p =ₒ p := by
      path_inductionₒ p
      rflₒ
  end
end Id

-- Composition

namespace Funₒ
  @[reducible]
  def after {α β γ : U} (f : α →ₒ β) (g : β →ₒ γ) : α →ₒ γ :=
    Λ x => g $ₒ f x

  @[reducible]
  def compose {α β γ : U} (f : β →ₒ γ) (g : α →ₒ β) : α →ₒ γ :=
    Λ x => f $ₒ g x
end Funₒ

infixr:90 " ∘ₒ " => Funₒ.compose

-- Homotopies

abbrev Homotopy.{u, v} {α : U.{u}} {P : α → U.{v}} (f g : (x : α) →ₒ P x) : U.{max u v} :=
  Πₒ x : α, f x =ₒ g x

infix:30 " ~ " => Homotopy

namespace Homotopy
  section
    variable {α : U} {P : α → U}
    variable (f g h : Pi α P)
    variable (h₁ : f ~ g) (h₂ : g ~ h)

    @[match_pattern]
    theorem refl : f ~ f := by
      introₒ x
      rflₒ

    theorem symm : g ~ f := by
      introₒ x
      apply Id.symm
      exact h₁ x

    theorem trans : f ~ h := by
      introₒ x
      apply Id.trans
      · exact h₁ x
      · exact h₂ x
  end

  section Lemma_2_4_3
    variable {α β : U}
    variable (f g : α →ₒ β)
    variable (H : f ~ g)
    variable (x y : α)
    variable (p : x =ₒ y)

    theorem homotopy_transport_commute : H x ⬝ Id.ap g p =ₒ Id.ap f p ⬝ H y := by
      path_inductionₒ p
      rwₒ [Id.refl_concat _ _ _, Id.concat_refl _ _ _]
  end Lemma_2_4_3

  section Corollary_2_4_4
    variable {α : U}
    variable (f : α →ₒ α)
    variable (H : f ~ Funₒ.id)
    variable (x : α)

    theorem homm_ap_commute : H (f x) =ₒ Id.ap f (H x) := by
      have h₁ := homotopy_transport_commute f Funₒ.id H (f x) x (H x)
      rewriteₒ [Id.ap_id _ _ _] at h₁
      have h₂ := Id.ap (· ⬝ (H x)⁻¹) h₁
      simp at h₂
      rewriteₒ [
        ← Id.concat_assoc _ _ _ _ _ _ _,
        ← Id.concat_assoc _ _ _ _ _ _ _,
        Id.concat_inv _ _ _,
        Id.concat_refl _ _ _,
        Id.concat_refl _ _ _,
      ] at h₂
      exact h₂
  end Corollary_2_4_4

  section
    variable {α β γ ρ : U}
    variable (f g : α →ₒ β) (h : ρ →ₒ α) (h' : β →ₒ γ)
    variable (H : f ~ g)
    theorem comp_homm : f ∘ₒ h ~ g ∘ₒ h := by
      introₒ w
      exact H (h w)

    theorem homm_comp : h' ∘ₒ f ~ h' ∘ₒ g := by
      introₒ x
      simp
      rwₒ [H x]
  end
end Homotopy

-- Equivalences

def Funₒ.fiber {α : U} {β : U} (f : α →ₒ β) (y : β) : U :=
  Σₒ x : α, f x =ₒ y

-- Note: if this function is defined in the current namespace rather than in `U`, then the
-- `Funₒ.is_contractible` one doesn't compile anymore (assuming the `is_contractible` function
-- is still pointing to this one.
abbrev U.is_contractible (α : U) : U :=
  Σₒ a : α, Πₒ x : α, a =ₒ x

namespace Funₒ
  section
  variable {α β : U}
  variable (f : α →ₒ β)
  
  abbrev is_contractible : U :=
    Πₒ y : β, Funₒ.fiber f y |> U.is_contractible

  @[simp]
  theorem id_simp (x : α) : id x = x := by
    rfl

  def qinv : U :=
    Σₒ g : β →ₒ α, (f ∘ₒ g ~ id) ×ₒ (g ∘ₒ f ~ id)

  def linv : U :=
    Σₒ g : β →ₒ α, g ∘ₒ f ~ id

  def rinv : U :=
    Σₒ g : β →ₒ α, f ∘ₒ g ~ id

  def biinv : U :=
    linv f ×ₒ rinv f

  def ishae : U :=
    Σₒ g : β →ₒ α, Σₒ η : g ∘ₒ f ~ id, Σₒ ε : f ∘ₒ g ~ id, Πₒ x : α, Id.ap f (η x) =ₒ ε (f x)

  theorem ishae_to_qinv (i : ishae f) : qinv f :=
    let ⟪g, η, ε, _⟫ := i
    ⟪g, ε, η⟫

  -- Theorem 4.2.3
  theorem qinv_to_ishae (q : qinv f) : ishae f :=
    let ⟪g, ε, η⟫ := q
    let ε' :=
      Λ b => (ε (f (g b)))⁻¹ ⬝ ((Id.ap f (η (g b))) ⬝ (ε b))
    let τ :=
      sorry
    ⟪g, η, ε', τ⟫

  theorem qinv_to_biinv (q : qinv f) : biinv f :=
    let ⟪g, h₁, h₂⟫ := q
    let left : linv f := ⟪g, h₂⟫
    let right : rinv f := ⟪g, h₁⟫
    ⟪left, right⟫

  theorem biinv_to_qinv (b : biinv f) : qinv f :=
    let ⟪⟪g, h₁⟫, ⟪h, h₂⟫⟫ := b
    let γ : g ~ h :=
      let p₁ : g ~ g ∘ₒ f ∘ₒ h := Λ z => by
        simp
        rewriteₒ [h₂ z]
        simp
        rflₒ
      let p₂ : g ∘ₒ f ∘ₒ h ~ h := Λ z => by
        apply h₁ (h z)
      Homotopy.trans _ _ _ p₁ p₂
    let H : f ∘ₒ g ~ id := by
      apply Homotopy.trans _ (f ∘ₒ h) _
      apply Homotopy.homm_comp
      apply γ
      apply h₂
    ⟪g, H, h₁⟫

  theorem contr_to_qinv (c : is_contractible f) : qinv f :=
    let g : β →ₒ α := λₒ x => Sigma.pr₁ (Sigma.pr₁ (c x))
    let h₁ : f ∘ₒ g ~ id := by
      introₒ x
      let path := Sigma.pr₂ (Sigma.pr₁ (c x))
      simp at *
      assumption
    let h₂ : g ∘ₒ f ~ id := by
      introₒ x
      let is_unique := Sigma.pr₂ (c (f x))
      let f_x_in_fiber_f_x : fiber f (f x) := ⟪x, by rflₒ⟫
      let path := is_unique f_x_in_fiber_f_x
      let h := Id.ap Sigma.pr₁ path
      simp at h
      exact h
    ⟪g, h₁, h₂⟫

  theorem qinv_to_contr (q : qinv f) : is_contractible f :=
    let ⟪g, h₁, h₂⟫ := q
    Λ y =>
      let x := g y
      let is_in_fiber := h₁ y
      let is_connected := Λ z => sorry
      ⟪⟪x, is_in_fiber⟫, is_connected⟫
  end

-- theorem id_is_contractible {α : U} : Arrow.is_contractible (@Arrow.id α) :=
--   Λ y => ⟪⟪y, Arrow.id y =ₒ y⟫, Λ fib' => _⟫

def U.equiv (α : U) (β : U) : U :=
  Σₒ f : α →ₒ β, Arrow.is_contractible f

infix:20 " ≃ₒ " => U.equiv
end Funₒ

-- def Id.idtoeqv {α β : U} (p : α =ₒ β) : (α ≃∘ β) :=
--   -- let idObj {γ : U} : γ →ₒ γ := Λ z => z
--   elim (P := fun α β _ => α ≃∘ β) (λ γ => Sigma.mk ⟨@Arrow.id γ, id_is_contractible⟩) α β p
infix:20 " ≃ₒ " => Funₒ.equiv

axiom U.univalence {α β : U} : (α ≃ₒ β) ≃ₒ (α =ₒ β)

end Hott
end
