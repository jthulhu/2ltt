import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.DefEqTransformations
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Misc.Rewrite

def sigma_eqv_of_eqv_post {α : Type*} {β γ : α → Type _} (u : ∀ a, β a ≃ γ a)
                          : (Σ a, β a) ≃ (Σ a, γ a) where
  toFun a :=
    let ⟨x, y⟩ := a
    ⟨x, u x y⟩
  invFun a :=
    let ⟨x, z⟩ := a
    ⟨x, u x |>.symm z⟩
  left_inv := by
    intro ⟨x, y⟩
    simp
  right_inv := by
    intro ⟨x, z⟩
    simp

def sigma_eqv_of_eqv_pre {α α' : Type*} {β : α → Type*} (u : α' ≃ α)
                         : (Σ a, β a) ≃ (Σ a, β (u a)) :=
  let β' x := β (u x)
  calc
    _ = Σ a, β' (u.symm a) := by
      have : β = β' ∘ u.symm := by
        funext
        unfold_let β'
        simp
      rw [this]
      rfl
    _ ≃ Σ a, β' a := {
      toFun := by
        intro ⟨x, y⟩
        exact ⟨u.symm x, y⟩
      invFun := by
        intro ⟨x, z⟩
        constructor
        case fst =>
          exact u x
        case snd =>
          show β' (u.invFun (u.toFun x))
          rw [u.left_inv x]
          exact z
      left_inv := by
        intro ⟨x, y⟩
        simp
      right_inv := by
        intro ⟨x, z⟩
        simp
    }

def sigma_eqv_of_eqv {α α' : Type*} {β : α → Type*} {β' : α' → Type*} (u : α' ≃ α)
                     (v : ∀ a, β' a ≃ β (u a)) : (Σ a, β a) ≃ (Σ a, β' a) :=
  calc
    _ ≃ Σ a, β (u a) := sigma_eqv_of_eqv_pre u
    _ ≃ Σ a, β' a := by
      apply sigma_eqv_of_eqv_post
      intro a
      apply Equiv.symm
      apply v

def pi_eqv_of_eqv_post {α : Type*} {β γ : α → Type _} (p : ∀ a, β a ≃ γ a)
                       : (∀ a, β a) ≃ (∀ a, γ a) where
  toFun f a :=
    (p a).toFun <| f a
  invFun g a :=
    (p a).invFun <| g a
  left_inv := by
    intro f
    simp
  right_inv := by
    intro g
    simp

def pi_eqv_of_eqv_pre {α α' : Type*} {β : α → Type*} (u : α' ≃ α)
                      : (∀ a, β a) ≃ (∀ a, β (u a)) :=
  let β' (x : α') := β (u x)
  calc
    _ = ∀ a : α, β' (u.symm a) := by
      have : β = β' ∘ u.symm := by
        funext
        unfold_let β'
        simp
      rw [this]
      rfl
    _ ≃ _ := {
      toFun := by
        intro f a
        rw [← u.left_inv a]
        apply f
      invFun := by
        intro f a
        apply f
      left_inv := by
        intro f
        funext a
        dsimp only
        apply cast_app_eq_app
        simp
      right_inv := by
        intro f
        funext a
        dsimp only
        apply cast_app_eq_app
        simp
    }

def pi_eqv_of_eqv {α α' : Type*} {β : α → Type*} {β' : α' → Type*} (u : α' ≃ α)
                 (v : ∀ a : α', β' a ≃ β (u a)) : (∀ a, β a) ≃ (∀ a, β' a) :=
  calc
    _ ≃ ∀ a, β (u a) := pi_eqv_of_eqv_pre u
    _ ≃ ∀ a, β' a := by
      apply pi_eqv_of_eqv_post
      intro a
      apply Equiv.symm
      apply v

def prod_eqv_sigma {α₁ α₂ : Type*} : α₁ × α₂ ≃ Σ _ : α₁, α₂ where
  toFun a :=
    let (x, y) := a
    ⟨x, y⟩
  invFun a :=
    let ⟨x, y⟩ := a
    (x, y)
  left_inv := by
    intro a
    rfl
  right_inv := by
    intro a
    rfl

def from_empty_eqv_unit {α : Empty → Type*} : (∀ x : Empty, α x) ≃ PUnit where
  toFun _ :=
    .unit
  invFun _ x :=
    x.elim
  left_inv := by
    intro f
    funext x
    apply x.elim
  right_inv := by
    intro x
    rfl
