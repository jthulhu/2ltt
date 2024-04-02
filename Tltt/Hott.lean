import Tltt.ObjLang

-- This module gives basic definitions, lemmas and axioms of Hott. Since we cannot "cheat" in
-- this module by peeking inside the definition of object languages, we must "speak" in the
-- object language.

namespace Hott
open Hott

namespace Id
  def subst {α : U} {P : α → U} {a b : α} (h₁ : a =∘ b) : P a → P b := by
    apply Pi.app
    apply Id.elim (P := fun x y _ => P x →∘ P y)
    intro x
    apply Pi.lam
    exact id
    exact h₁

  postfix:max "ₒ" => subst

  section
    variable {α : U}
    variable (x y z w : α)
    variable (p : x =∘ y) (q : y =∘ z) (r : z =∘ w)
    
    @[simp]
    theorem refl_refl_is_refl : (refl x ⬝ refl x) = refl x := by
      rfl

    theorem concat_refl : p ⬝ refl y =∘ p := by
      apply elim (P := fun x y p => p ⬝ refl y =∘ p)
      intro x
      simp
      apply refl

    theorem refl_concat : refl x ⬝ p =∘ p := by
      apply elim (P := fun x y p => refl x ⬝ p =∘ p)
      intro x
      simp
      apply refl

    @[simp]
    theorem inv_refl_concat : ((refl x)⁻¹ ⬝ refl x) = refl x := by
      rfl

    theorem inv_concat : p⁻¹ ⬝ p =∘ refl y := by
      apply elim (P := fun x y p => p⁻¹ ⬝ p =∘ refl y)
      intro x
      simp
      apply refl

    @[simp]
    theorem concat_refl_inv : (refl x ⬝ (refl x)⁻¹) = refl x := by
      rfl

    theorem concat_inv : p ⬝ p⁻¹ =∘ refl x := by
      apply elim (P := fun x y p => p ⬝ p⁻¹ =∘ refl x)
      intro x
      simp
      apply refl

    @[simp]
    theorem inv_refl : (refl x)⁻¹ = refl x := by
      rfl

    theorem inv_inv : (p⁻¹)⁻¹ =∘ p := by
      apply elim (P := fun x y p => (p⁻¹)⁻¹ =∘ p)
      intro x
      simp
      apply refl

    theorem concat_assoc : p ⬝ (q ⬝ r) =∘ (p ⬝ q) ⬝ r :=
      let P := fun x y p =>
        Π∘ z : α, Π∘ w : α, Π∘ q : y =∘ z, Π∘ r : z =∘ w, p ⬝ (q ⬝ r) =∘ (p ⬝ q) ⬝ r
      let h (x : α) : P x x (refl x) := Λ z => Λ w => Λ q => Λ r => by
        have h₁ : q ⬝ r =∘ refl x ⬝ (q ⬝ r) := refl_concat _ _ _ |> symm _ _
        apply subst (P := fun qr => qr =∘ (refl x ⬝ q) ⬝ r) h₁
        have h₂ : q =∘ refl x ⬝ q := refl_concat _ _ _ |> symm _ _
        apply subst (P := fun q' => q ⬝ r =∘ q' ⬝ r) h₂
        apply refl
      elim (P := P) h x y p z w q r
  end
  
  section
    variable {α β γ : U}
    variable (f : α → β) (g : β → γ)
    variable (x y z : α)
    variable (p : x =∘ y) (q : y =∘ z)

    -- Lemma 2.2.1
    def ap {x y : α} (p : x =∘ y) : f x =∘ f y :=
      elim (P := fun x y _ => f x =∘ f y) (fun x => refl (f x)) x y p

    @[simp]
    theorem ap_refl : ap f (refl x) = refl (f x) := by
      rfl

    -- Lemma 2.2.2
    theorem ap_concat : ap f (p ⬝ q) =∘ ap f p ⬝ ap f q :=
      let P := fun x y p => Π∘ z : α, Π∘ q : y =∘ z, ap f (p ⬝ q) =∘ ap f p ⬝ ap f q
      let h x := Λ z => Λ q => by
        have h₁ : q =∘ refl x ⬝ q := refl_concat _ _ _ |> symm _ _
        apply subst (P := fun q' => ap f q' =∘ _) h₁
        simp
        apply symm
        apply refl_concat
      elim (P := P) h _ _ _ @∘ z @∘ q

    theorem ap_inv : ap f p⁻¹ =∘ (ap f p)⁻¹ :=
      let P := fun x y p => ap f p⁻¹ =∘ (ap f p)⁻¹
      let h x : ap f (refl x)⁻¹ =∘ (ap f (refl x))⁻¹ := by
        simp
        apply refl
      elim (P := P) h _ _ _

    -- instance : CoeFun (α →∘ β) (fun f => x =∘ y → f x =∘ f y) where
    --   coe f p := ap (Pi.app f) p
  end
end Id

-- Composition

namespace Arrow
  def after {α β γ : U} (f : α →∘ β) (g : β →∘ γ) : α →∘ γ :=
    Λ x => g $∘ f x

  def compose {α β γ : U} (f : β →∘ γ) (g : α →∘ β) : α →∘ γ :=
    Λ x => f $∘ g x
end Arrow

infixr:90 " ∘∘ " => Arrow.compose

-- Homotopies

abbrev Homotopy.{u, v} {α : U.{u}} {P : α → U.{v}} (f g : (x : α) →∘ P x) : U.{max u v} :=
  Π∘ x : α, f x =∘ g x

infix:30 " ~ " => Homotopy

namespace Homotopy
  section
    variable {α : U} {P : α → U}
    variable (f g h : Pi α P)
    variable (h₁ : f ~ g) (h₂ : g ~ h)

    theorem refl : f ~ f :=
      Λ x => Id.refl (f x)

    theorem symm : g ~ f :=
      Λ x => Id.symm (f x) (g x) (h₁ x)

    theorem trans : f ~ h :=
      Λ x => Id.trans (f x) (g x) (h x) (h₁ x) (h₂ x)
  end

  section                       -- Lemma 2.4.3
    variable {α β : U}
    variable (f g : α →∘ β)
    variable (H : f ~ g)
    variable (x y : α)
    variable (p : x =∘ y)
    
    theorem homotopy_transport_commute : H x ⬝ Id.ap g p =∘ Id.ap f p ⬝ H y :=
      let P x y p := H x ⬝ Id.ap g p =∘ Id.ap f p ⬝ H y
      let h x := by
        simp
        apply Id.subst
        apply Id.symm
        apply Id.refl_concat
        apply Id.concat_refl
      Id.elim (P := P) h x y p
  end

  section
    variable {α β γ ρ : U}
    variable (f g : α →∘ β) (h : ρ →∘ α) (h' : β →∘ γ)
    variable (H : f ~ g)
    theorem comp_homm : f ∘∘ h ~ g ∘∘ h :=
      Λ w => H (h w)

    theorem homm_comp : h' ∘∘ f ~ h' ∘∘ g :=
      Λ x => Id.subst (P := fun c => h' ∘∘ f $∘ x =∘ h' $∘ c) (H x) (Id.refl _)
  end
end Homotopy

-- Equivalences

def Arrow.fiber {α : U} {β : U} (f : α →∘ β) (y : β) : U :=
  Σ∘ x : α, f x =∘ y

-- Note: if this function is defined in the current namespace rather than in `U`, then the
-- `Arrow.is_contractible` one doesn't compile anymore (assuming the `is_contractible` function
-- is still pointing to this one.
def U.is_contractible (α : U) : U :=
  Σ∘ a : α, Π∘ x : α, a =∘ x

namespace Arrow
  section
  variable {α β : U}
  variable (f : α →∘ β)
  
  def is_contractible : U :=
    Π∘ y : β, Arrow.fiber f y |>.is_contractible

  def id : α →∘ α :=
    Λ x => x

  @[simp]
  theorem id_simp (x : α) : id x = x := by
    rfl

  def qinv : U :=
    Σ∘ g : β →∘ α, (f ∘∘ g ~ id) ×∘ (g ∘∘ f ~ id)

  def linv : U :=
    Σ∘ g : β →∘ α, g ∘∘ f ~ id

  def rinv : U :=
    Σ∘ g : β →∘ α, f ∘∘ g ~ id

  def biinv : U :=
    linv f ×∘ rinv f

  def qinv_to_biinv (q : qinv f) : biinv f :=
    let g := Sigma.pr₁ q
    let (h₁, h₂) :=
      let r := Sigma.pr₂ q
      (Sigma.pr₁ r, Sigma.pr₂ r)
    let left : linv f := ⟪g, h₂⟫
    let right : rinv f := ⟪g, h₁⟫
    ⟪left, right⟫

  def biinv_to_qinv (b : biinv f) : qinv f :=
    let g := Sigma.pr₁ <| Sigma.pr₁ b
    let h₁ := Sigma.pr₂ <| Sigma.pr₁ b
    let h := Sigma.pr₁ <| Sigma.pr₂ b
    let h₂ := Sigma.pr₂ <| Sigma.pr₂ b
    let γ : g ~ h :=
      let p₁ : g ~ g ∘∘ f ∘∘ h := Λ z => by
        apply Id.subst (P := fun c => g z =∘ g c) (h₂ z)⁻¹
        simp
        apply Id.refl
      let p₂ : g ∘∘ f ∘∘ h ~ h := Λ z => by
        apply h₁ (h z)
      Homotopy.trans _ _ _ p₁ p₂
    let H : f ∘∘ g ~ id := by
      apply Homotopy.trans _ (f ∘∘ h) _
      apply Homotopy.homm_comp
      apply γ
      apply h₂
    ⟪g, ⟪H, h₁⟫⟫
  end
end Arrow

-- theorem id_is_contractible {α : U} : Arrow.is_contractible (@Arrow.id α) :=
--   Λ y => ⟪⟪y, Arrow.id y =∘ y⟫, Λ fib' => _⟫

def U.equiv (α : U) (β : U) : U :=
  Σ∘ f : α →∘ β, Arrow.is_contractible f

infix:20 " ≃∘ " => U.equiv

-- def Id.idtoeqv {α β : U} (p : α =∘ β) : (α ≃∘ β) :=
--   -- let idObj {γ : U} : γ →∘ γ := Λ z => z
--   elim (P := fun α β _ => α ≃∘ β) (λ γ => Sigma.mk ⟨@Arrow.id γ, id_is_contractible⟩) α β p

axiom U.univalence {α β : U} : (α ≃∘ β) ≃∘ (α =∘ β)

-- namespace Tactics
--   open Lean.Parser.Tactic
--   open Lean.Elab Tactic
--   open Lean.Meta
  
--   syntax (name := objRewriteSeq) "rewrite∘" rwRuleSeq (location)? : tactic

--   def objRewrite (mvarId : MVarId) (e : Expr) (heq : Expr) (symm : Bool := false)
--                  (occs : Occurrences := Occurrences.all) : MetaM RewriteResult :=
--     mvarId.withContext do
--       sorry

--   def objRewriteTarget (stx : Syntax) (symm : Bool) : TacticM Unit := do
--     Term.withSynthesize <| withMainContext do
--       let e ← elabTerm stx none true
--       let r ← objRewrite (← getMainGoal) (← getMainTarget) e symm

--   def objRewriteLocalDecl (stx : Syntax) (symm : Bool) (fvarId : FVarId) : TacticM Unit := do
--     sorry

--   def withObjRWRulesSeq (token : Syntax) (rwObjRulesSeqStx : Syntax)
--     (x : (symm : Bool) → (term : Syntax) → TacticM Unit) : TacticM Unit := do
--     sorry

--   @[tactic objRewriteSeq]
--   def evalObjRewriteSeq : Tactic := fun stx => do
--     let loc := expandOptLocation stx[2]
--     withObjRWRulesSeq stx[0] stx[1] fun symm term => do
--       withLocation loc
--         (objRewriteLocalDecl term symm ·)
--         (objRewriteTarget term symm)
--         (throwTacticEx `rewriteObj · "did not find instance of the pattern in the current goal")
-- end Tactics

end Hott
