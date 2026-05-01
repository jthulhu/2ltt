import Tltt.ObjLang

noncomputable section

-- This module gives basic definitions, lemmas and axioms of Hott. Since we cannot "cheat" in
-- this module by peeking inside the definition of object languages, we must "speak" in the
-- object language.

namespace Hott
open Hott

@[reducible]
def Arrow.id {α : U} : α →ₒ α :=
  Λ x => x

@[simp]
def Arrow.id_is_id {α : U} {x : α} : (id $ₒ x) = x := by
  rfl

namespace Id
  def subst {α : U} {P : α → U} {a b : α} (h₁ : a =ₒ b) : P a → P b := by
    apply Pi.app
    apply Id.elim (P := fun x y _ => P x →ₒ P y)
    intro x
    apply Pi.lam
    exact id
    exact h₁

  def mp {α β : U} (h : α =ₒ β) (a : α) : β :=
    subst (P := fun x => x) h a

  def mpr {α β : U} (h : α =ₒ β) (b : β) : α :=
    mp (symm α β h) b

  section
    variable {α : U}
    variable (x y z w : α)
    variable (p : x =ₒ y) (q : y =ₒ z) (r : z =ₒ w)
    
    @[simp]
    theorem refl_refl_is_refl : (refl x ⬝ refl x) = refl x := by
      rfl

    theorem concat_refl : p ⬝ refl y =ₒ p := by
      apply elim (P := fun x y p => p ⬝ refl y =ₒ p)
      intro x
      simp
      apply refl

    theorem refl_concat : refl x ⬝ p =ₒ p := by
      apply elim (P := fun x y p => refl x ⬝ p =ₒ p)
      intro x
      simp
      apply refl

    @[simp]
    theorem inv_refl_concat : ((refl x)⁻¹ ⬝ refl x) = refl x := by
      rfl

    theorem inv_concat : p⁻¹ ⬝ p =ₒ refl y := by
      apply elim (P := fun x y p => p⁻¹ ⬝ p =ₒ refl y)
      intro x
      simp
      apply refl

    @[simp]
    theorem concat_refl_inv : (refl x ⬝ (refl x)⁻¹) = refl x := by
      rfl

    theorem concat_inv : p ⬝ p⁻¹ =ₒ refl x := by
      apply elim (P := fun x y p => p ⬝ p⁻¹ =ₒ refl x)
      intro x
      simp
      apply refl

    @[simp]
    theorem inv_refl : (refl x)⁻¹ = refl x := by
      rfl

    theorem inv_inv : (p⁻¹)⁻¹ =ₒ p := by
      apply elim (P := fun x y p => (p⁻¹)⁻¹ =ₒ p)
      intro x
      simp
      apply refl

    theorem concat_assoc : p ⬝ (q ⬝ r) =ₒ (p ⬝ q) ⬝ r :=
      let P := fun x y p =>
        Πₒ z : α, Πₒ w : α, Πₒ q : y =ₒ z, Πₒ r : z =ₒ w, p ⬝ (q ⬝ r) =ₒ (p ⬝ q) ⬝ r
      let h (x : α) : P x x (refl x) := Λ z => Λ w => Λ q => Λ r => by
        have h₁ : q ⬝ r =ₒ refl x ⬝ (q ⬝ r) := refl_concat _ _ _ |> symm _ _
        apply subst (P := fun qr => qr =ₒ (refl x ⬝ q) ⬝ r) h₁
        have h₂ : q =ₒ refl x ⬝ q := refl_concat _ _ _ |> symm _ _
        apply subst (P := fun q' => q ⬝ r =ₒ q' ⬝ r) h₂
        apply refl
      elim (P := P) h x y p z w q r
  end
  
  section
    variable {α β γ : U}
    variable (f : α → β) (g : β → γ)
    variable (x y z : α)
    variable (p : x =ₒ y) (q : y =ₒ z)

    -- Lemma 2.2.1
    def ap {x y : α} (p : x =ₒ y) : f x =ₒ f y :=
      elim (P := fun x y _ => f x =ₒ f y) (fun x => refl (f x)) x y p

    @[simp]
    theorem ap_refl : ap f (refl x) = refl (f x) := by
      rfl

    -- Lemma 2.2.2
    theorem ap_concat : ap f (p ⬝ q) =ₒ ap f p ⬝ ap f q :=
      let P := fun x y p => Πₒ z : α, Πₒ q : y =ₒ z, ap f (p ⬝ q) =ₒ ap f p ⬝ ap f q
      let h x := Λ z => Λ q => by
        have h₁ : q =ₒ refl x ⬝ q := refl_concat _ _ _ |> symm _ _
        apply subst (P := fun q' => ap f q' =ₒ _) h₁
        simp
        apply symm
        apply refl_concat
      elim (P := P) h _ _ _ z q

    theorem ap_inv : ap f p⁻¹ =ₒ (ap f p)⁻¹ :=
      let P := fun x y p => ap f p⁻¹ =ₒ (ap f p)⁻¹
      let h x : ap f (refl x)⁻¹ =ₒ (ap f (refl x))⁻¹ := by
        simp
        apply refl
      elim (P := P) h _ _ _

    theorem ap_id : ap Arrow.id p =ₒ p := by
      apply elim (P := fun x y p => ap Arrow.id p =ₒ p)
      intro x
      simp
      apply refl
  end
end Id

-- Composition

namespace Arrow
  @[reducible]
  def after {α β γ : U} (f : α →ₒ β) (g : β →ₒ γ) : α →ₒ γ :=
    Λ x => g $ₒ f x

  @[reducible]
  def compose {α β γ : U} (f : β →ₒ γ) (g : α →ₒ β) : α →ₒ γ :=
    Λ x => f $ₒ g x
end Arrow

infixr:90 " ∘ₒ " => Arrow.compose

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
      apply Id.refl (f x)

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

    theorem homotopy_transport_commute : H x ⬝ Id.ap g p =ₒ Id.ap f p ⬝ H y :=
      let P x y p := H x ⬝ Id.ap g p =ₒ Id.ap f p ⬝ H y
      let h x := by
        simp
        apply Id.subst
        apply Id.symm
        apply Id.refl_concat
        apply Id.concat_refl
      Id.elim (P := P) h x y p
  end Lemma_2_4_3

  section Corollary_2_4_4
    variable {α : U}
    variable (f : α →ₒ α)
    variable (H : f ~ Arrow.id)
    variable (x : α)

    theorem homm_ap_commute : H (f x) =ₒ Id.ap f (H x) :=
      let h₁ : _ =ₒ _ := homotopy_transport_commute f Arrow.id H (f x) x (H x)      
      sorry
  end Corollary_2_4_4

  section
    variable {α β γ ρ : U}
    variable (f g : α →ₒ β) (h : ρ →ₒ α) (h' : β →ₒ γ)
    variable (H : f ~ g)
    theorem comp_homm : f ∘ₒ h ~ g ∘ₒ h :=
      Λ w => H (h w)

    theorem homm_comp : h' ∘ₒ f ~ h' ∘ₒ g :=
      Λ x => Id.subst (P := fun c => h' ∘ₒ f $ₒ x =ₒ h' $ₒ c) (H x) (Id.refl _)
  end
end Homotopy

-- Equivalences

def Arrow.fiber {α : U} {β : U} (f : α →ₒ β) (y : β) : U :=
  Σₒ x : α, f x =ₒ y

-- Note: if this function is defined in the current namespace rather than in `U`, then the
-- `Arrow.is_contractible` one doesn't compile anymore (assuming the `is_contractible` function
-- is still pointing to this one.
abbrev U.is_contractible (α : U) : U :=
  Σₒ a : α, Πₒ x : α, a =ₒ x

namespace Arrow
  section
  variable {α β : U}
  variable (f : α →ₒ β)
  
  abbrev is_contractible : U :=
    Πₒ y : β, Arrow.fiber f y |> U.is_contractible

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
    let ⟪g, ⟪h₁, h₂⟫⟫ := q
    let left : linv f := ⟪g, h₂⟫
    let right : rinv f := ⟪g, h₁⟫
    ⟪left, right⟫

  theorem biinv_to_qinv (b : biinv f) : qinv f :=
    let ⟪⟪g, h₁⟫, ⟪h, h₂⟫⟫ := b
    let γ : g ~ h :=
      let p₁ : g ~ g ∘ₒ f ∘ₒ h := Λ z => by
        apply Id.subst (P := fun c => g z =ₒ g c) (h₂ z)⁻¹
        simp
        apply Id.refl
      let p₂ : g ∘ₒ f ∘ₒ h ~ h := Λ z => by
        apply h₁ (h z)
      Homotopy.trans _ _ _ p₁ p₂
    let H : f ∘ₒ g ~ id := by
      apply Homotopy.trans _ (f ∘ₒ h) _
      apply Homotopy.homm_comp
      apply γ
      apply h₂
    ⟪g, ⟪H, h₁⟫⟫

  theorem contr_to_qinv (c : is_contractible f) : qinv f :=
    let g : β →ₒ α := Λ x =>
      let ⟪⟪center, _⟫, _⟫ := c x
      center
    let h₁ : f ∘ₒ g ~ id := by
      introₒ x
      let path := Sigma.pr₂ (Sigma.pr₁ (c x))
      simp at *
      assumption
    let h₂ : g ∘ₒ f ~ id := by
      introₒ x
      let hello := Sigma.pr₁ (c (f x))
      -- let center := Sigma.pr₁ (Sigma.pr₁ (c (f x)))
      let path := Sigma.pr₂ (c (f x)) hello
      let h := Id.ap Sigma.pr₁ path
      simp at *
      admit
    ⟪g, ⟪h₁, h₂⟫⟫

  theorem qinv_to_contr (q : qinv f) : is_contractible f :=
    let ⟪g, h₁, h₂⟫ := q
    Λ y =>
      let x := g y
      let is_in_fiber := h₁ y
      let is_connected := Λ z => sorry
      ⟪⟪x, is_in_fiber⟫, is_connected⟫
  end
end Arrow

-- theorem id_is_contractible {α : U} : Arrow.is_contractible (@Arrow.id α) :=
--   Λ y => ⟪⟪y, Arrow.id y =ₒ y⟫, Λ fib' => _⟫

def U.equiv (α : U) (β : U) : U :=
  Σₒ f : α →ₒ β, Arrow.is_contractible f

infix:20 " ≃ₒ " => U.equiv

-- def Id.idtoeqv {α β : U} (p : α =ₒ β) : (α ≃∘ β) :=
--   -- let idObj {γ : U} : γ →ₒ γ := Λ z => z
--   elim (P := fun α β _ => α ≃∘ β) (λ γ => Sigma.mk ⟨@Arrow.id γ, id_is_contractible⟩) α β p

axiom U.univalence {α β : U} : (α ≃ₒ β) ≃ₒ (α =ₒ β)

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
end
