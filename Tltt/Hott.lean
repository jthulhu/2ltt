import Tltt.ObjLang
import Tltt.Tactics

set_option autoImplicit false

noncomputable section

-- This module gives basic definitions, lemmas and axioms of Hott. Since we cannot "cheat" in
-- this module by peeking inside the definition of object languages, we must "speak" in the
-- object language.

namespace Hott
open Hott

-- Composition

namespace Funₒ
  @[reducible]
  def id {α : U} : α →ₒ α :=
    Λ x => x

  @[simp]
  def id_is_id {α : U} {x : α} : (id $ₒ x) = x := by
    rfl

  @[reducible]
  def after {α β γ : U} (f : α →ₒ β) (g : β →ₒ γ) : α →ₒ γ :=
    Λ x => g $ₒ f x

  @[reducible]
  def compose {α β γ : U} (f : β →ₒ γ) (g : α →ₒ β) : α →ₒ γ :=
    Λ x => f $ₒ g x
end Funₒ

infixr:90 " ∘ₒ " => Funₒ.compose

namespace Id
  theorem based_path_induction {α : U} (a : α) {motive : (x : α) → a =ₒ x → U}
                               (c : motive a (refl a)) (x : α) (p : a =ₒ x) : motive x p := by
    let D := λₒ x : α => λₒ y : α => λₒ p : x =ₒ y =>
      Πₒ C : ((z : α) →ₒ x =ₒ z →ₒ U), Πₒ _x : C x (refl x), C y p
    have f : ∀ x y : α, ∀ p : x =ₒ y, D x y p := by
      intro x y p
      path_inductionₒ p
      introₒ C
      introₒ c
      exact c
    exact f a x p @ₒ (funₒ z => funₒ p => motive z p) @ₒ c
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
      path_inductionₒ q
      path_inductionₒ r
      rflₒ
  end
  
  section
    variable {α β γ : U}
    -- variable (f : α → β) (g : β → γ)
    -- variable (x y z : α)
    -- variable (p : x =ₒ y) (q : y =ₒ z)

    -- Lemma 2.2.1
    def ap (f : α →ₒ β) {x y : α} (p : x =ₒ y) : f x =ₒ f y := by
      path_inductionₒ p
      rflₒ

    @[simp]
    theorem ap_refl (f : α →ₒ β) (x : α) : ap f (refl x) = refl (f x) := by
      rfl

    -- Lemma 2.2.2
    theorem ap_concat (f : α →ₒ β) (x y z : α) (p : x =ₒ y) (q : y =ₒ z)
                      : ap f (p ⬝ q) =ₒ ap f p ⬝ ap f q := by
      path_inductionₒ p
      rwₒ [refl_concat _ _ _, refl_concat _ _ _]

    theorem ap_inv (f : α →ₒ β) (x y : α) (p : x =ₒ y) : ap f p⁻¹ =ₒ (ap f p)⁻¹ := by
      path_inductionₒ p
      rflₒ

    theorem ap_id (x y : α) (p : x =ₒ y) : ap Funₒ.id p =ₒ p := by
      path_inductionₒ p
      rflₒ

    theorem ap_comp (f : α →ₒ β) (g : β →ₒ γ) {x y : α} (p : x =ₒ y)
                    : ap g (ap f p) =ₒ ap (g ∘ₒ f) p := by
      path_inductionₒ p
      rflₒ
  end
end Id

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
      have h₂ := Id.ap (λₒ p => p ⬝ (H x)⁻¹) h₁
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

def U.Singleton {α : U} (x : α) : U :=
  Σₒ x' : α, x =ₒ x'

def U.Singleton.is_contr {α : U} {a : α} : is_contractible (Singleton a) := by
  exhibitₒ ⟪a, Id.refl a⟫
  introₒ o
  let ⟪a', p⟫ := o
  simp at p
  apply @Id.based_path_induction α a (fun x p'' => ⟪a, Id.refl a⟫ =ₒ ⟪x, p''⟫) (Id.refl _) a' p

namespace Funₒ
  namespace Retraction
    def is_retraction {α β : U} (f : α →ₒ β) : U :=
      Σₒ g : β →ₒ α, f ∘ₒ g ~ id

    def Retraction (α β : U) : U :=
      Σₒ f : α →ₒ β, is_retraction f

    /--
    `is_retract β α` means that β is a retract of α, that is, there is a retraction from α to β.
    -/
    def is_retract (β α : U) : U :=
      Retraction α β

    def Retracts (α : U) : U :=
      Σₒ β : U, is_retract β α

    theorem retract_elim {α β : U} (rp : is_retract β α) {motive : β → U}
                         (H : Πₒ x : α, motive (pr₁ rp x)) (y : β) : motive y := by
      let ⟪r, s, p⟫ := rp
      have h := H (s y)
      rewriteₒ [p y] at h
      exact h

    theorem retract_of_retract {α β γ : U} (r₁ : is_retract α β) (r₂ : is_retract β γ)
                               : is_retract α γ := by
      let ⟪f, finv, f_hom⟫ := r₁
      let ⟪g, ginv, g_hom⟫ := r₂
      exhibitₒ f ∘ₒ g
      exhibitₒ ginv ∘ₒ finv
      introₒ x
      simp
      rewriteₒ [g_hom _]
      simp
      rewriteₒ [f_hom _]
      simp
      rflₒ
  end Retraction

  section
  variable {α β : U}
  variable (f : α →ₒ β)

  abbrev is_contractible : U :=
    Πₒ y : β, Funₒ.fiber f y |> U.is_contractible

  theorem retract_preseve_contractible (α β : U) (h : Retraction.is_retract β α)
                                       (c : U.is_contractible α) : U.is_contractible β := by
    let ⟪a₀, Ha⟫ := c
    simp at Ha
    let ⟪r, s, p⟫ := h
    simp at p
    exhibitₒ r a₀
    introₒ b
    have h := Id.ap r (Ha (s b))
    rewriteₒ [p _] at h
    exact h

  @[simp]
  theorem id_simp (x : α) : id x = x := by
    rfl

  def qinv : U :=
    Σₒ g : β →ₒ α, (f ∘ₒ g ~ id) ×ₒ (g ∘ₒ f ~ id)

  def linv : U :=
    Σₒ g : β →ₒ α, g ∘ₒ f ~ id

  def rinv : U :=
    Σₒ g : β →ₒ α, f ∘ₒ g ~ id

  theorem rinv_is_retraction {α β : U} (f : α →ₒ β) (frinv : rinv f)
                             : Retraction.is_retraction f := by
    exact frinv

  def biinv : U :=
    linv f ×ₒ rinv f

  theorem ap_section_is_section {α β : U} (f : α →ₒ β) (rp : linv f) {x y : α}
                                : linv (Pi.lam <| Id.ap f (x := x) (y := y)) := by
    let ⟪g, h⟫ := rp
    simp at h
    exhibitₒ by
      introₒ p
      let p' := Id.ap g p
      rewriteₒ [h x, h y] at p'
      exact p'
    introₒ p
    simp
    path_inductionₒ p
    generalize h x = p
    simp at p
    have h : Πₒ z : α, Πₒ q : z =ₒ x,
             Id.mp (Id.subst (P := fun hole => (x =ₒ z) =ₒ (x =ₒ hole)) q (Id.refl (x =ₒ z)))
                   (Id.mp (Id.subst (P := fun hole => (z =ₒ z) =ₒ (hole =ₒ z)) q
                                    (Id.refl (z =ₒ z)))
                          (Id.refl z))
             =ₒ Id.refl x := by
      introₒ z
      introₒ q
      path_inductionₒ q
      simp
      rflₒ
    exact h _ _

  theorem linv.induction {α β : U} (f : α →ₒ β) (flinv : linv f) {x y : α} (p : f x =ₒ f y)
                         : x =ₒ y := by
    let ⟪apinv, _⟫ := ap_section_is_section f flinv (x := x) (y := y)
    exact apinv p

  theorem lemma_a {α β γ : U} (f : α →ₒ β) (g : β →ₒ γ) (h : α →ₒ γ) (H : g ∘ₒ f ~ h)
                  (glinv : linv g) (hrinv : rinv h) : rinv f := by
    let ⟪hinv, hinv_proof⟫ := hrinv
    exhibitₒ hinv ∘ₒ g
    introₒ x
    apply linv.induction g glinv
    simp
    rewriteₒ [H _, hinv_proof _]
    dsimp
    rflₒ

  abbrev id_endpoint_id {α : U} {x y x' y' : α} (p : x =ₒ x') (q : y =ₒ y')
                        : Funₒ (x =ₒ y) (x' =ₒ y') := by
    introₒ l
    exact (p⁻¹ ⬝ l) ⬝ q

  def id_endpoint_id.qinv {α : U} {x y x' y' : α} (p : x =ₒ x') (q : y =ₒ y')
                          : qinv (id_endpoint_id p q) := by
    let g := by
      introₒ l
      exact (p ⬝ l) ⬝ q⁻¹
    exhibitₒ g
    exhibitₒ by
      introₒ l
      simp
      path_inductionₒ p
      path_inductionₒ q
      simp
      rwₒ [
        Id.refl_concat _ _ _,
        Id.refl_concat _ _ _,
        Id.concat_refl _ _ _,
        Id.concat_refl _ _ _
      ]
    introₒ l
    simp
    path_inductionₒ p
    path_inductionₒ q
    simp
    rwₒ [
      Id.refl_concat _ _ _,
      Id.refl_concat _ _ _,
      Id.concat_refl _ _ _,
      Id.concat_refl _ _ _
    ]
  def id_endpoint_id.beta {α : U} {x x' : α} (p : x =ₒ x')
      : id_endpoint_id p p (Id.refl _) =ₒ Id.refl _ := by
    simp
    rwₒ [Id.concat_refl _ _ _, Id.inv_concat _ _ _]

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
    let τ := by
      introₒ a
      have h₁ := Homotopy.homm_ap_commute (g ∘ₒ f) η a
      have h₂ := Homotopy.homotopy_transport_commute (f ∘ₒ g ∘ₒ f) f (by introₒ z; exact ε (f z))
                                                     (g (f a)) a (η a)
      rewriteₒ [← Id.ap_comp (g ∘ₒ f) f (η a), ← h₁] at h₂
      have h₃ := Id.ap (λₒ p => (ε (f (g (f a))))⁻¹ ⬝ p) h₂
      simp at h₃
      rewriteₒ [Id.concat_assoc _ _ _ _ _ _ _, Id.inv_concat _ _ _, Id.refl_concat _ _ _] at h₃
      assumption
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
    let g : β →ₒ α := λₒ x => pr₁ (pr₁ (c x))
    let h₁ : f ∘ₒ g ~ id := by
      introₒ x
      let path := pr₂ (pr₁ (c x))
      simp at *
      assumption
    let h₂ : g ∘ₒ f ~ id := by
      introₒ x
      let is_unique := pr₂ (c (f x))
      let f_x_in_fiber_f_x : fiber f (f x) := ⟪x, by rflₒ⟫
      let path := is_unique f_x_in_fiber_f_x
      let h := Id.ap (Pi.lam pr₁) path
      simp at h
      exact h
    ⟪g, h₁, h₂⟫

  theorem sigma_closed_under_retract {α : U} {β β' : α → U}
                                     (r : (x : α) →ₒ Retraction.is_retract (β x) (β' x))
                                     : Retraction.is_retract (Σₒ x : α, β x) (Σₒ x : α, β' x)
                                     := by
    exhibitₒ by
      introₒ ptn
      let ⟪x, y⟫ := ptn
      let ⟪f, _⟫ := r x
      exact ⟪x, f y⟫
    exhibitₒ by
      introₒ ptn
      let ⟪x, y⟫ := ptn
      let ⟪_, g, _⟫ := r x
      exact ⟪x, g y⟫
    introₒ ptn
    let ⟪x, y⟫ := ptn
    simp
    rewrite [← Sigmaₒ.eta (r x), ← Sigmaₒ.eta (pr₂ (r x))]
    let h := pr₂ (pr₂ (r x))
    simp
    rewrite [← Sigmaₒ.eta (r x)]
    simp
    rwₒ [h y]
    rflₒ

  theorem linv_cancellation {α β : U} (g : α →ₒ β) (li : linv g) (x y : α) (p : g x =ₒ g y)
                            : x =ₒ y := by
    let ⟪ap_inv, _⟫ := ap_section_is_section g li (x := x) (y := y)
    applyₒ ap_inv
    assumption

  theorem qinv_to_contr (q : qinv f) : is_contractible f := by
    let ⟪g, h₁, h₂⟫ := q
    introₒ y
    apply Funₒ.Retraction.retract_elim (α := α)
      (motive := fun y => U.is_contractible (Σₒ x' : α, f x' =ₒ y))
    case rp => exact ⟪f, g, h₁⟫
    introₒ x
    simp
    apply Funₒ.retract_preseve_contractible (Σₒ x' : α, x =ₒ x') _
    · apply sigma_closed_under_retract
      introₒ y
      apply Funₒ.Retraction.retract_of_retract <| by
        exhibitₒ funₒ p => p⁻¹
        exhibitₒ funₒ p => p⁻¹
        introₒ x
        simp
        exact Id.inv_inv _ _ _
      exhibitₒ Pi.lam <| Id.ap f
      apply rinv_is_retraction
      refine lemma_a (Pi.lam <| Id.ap f) (Pi.lam <| Id.ap g) (funₒ p => Id.ap (g ∘ₒ f) p) ?homm
                     ?apg_linv ?aggf_rinv
      · introₒ p
        exact Id.ap_comp _ _ _
      · apply ap_section_is_section _
        exhibitₒ f
        exact h₁
      · let ⟪einv, erinv_proof, elinv_proof⟫ := id_endpoint_id.qinv (h₂ x) (h₂ y)
        let e := id_endpoint_id (h₂ x) (h₂ y)
        exhibitₒ e
        introₒ r
        simp
        apply @Retraction.retract_elim (x =ₒ y) (g (f x) =ₒ g (f y)) ⟪einv, e, elinv_proof⟫
                                       (fun r => Id.ap (g ∘ₒ f) (e r) =ₒ r)
        introₒ r'
        rewriteₒ [erinv_proof _]
        simp
        path_inductionₒ r'
        simp
        rewriteₒ [← id_endpoint_id.beta (x' := x) (h₂ x), elinv_proof _]
        simp
        rflₒ
    · exact U.Singleton.is_contr
  end

  abbrev is_equiv {α β : U} (f : α →ₒ β) : U :=
    ishae f

  def equiv (α β : U) : U :=
    Σₒ f : α →ₒ β, is_equiv f

  theorem id_is_equiv {α : U} : is_equiv (@id α) := by
    apply qinv_to_ishae
    exact ⟪id, Homotopy.refl id, Homotopy.refl id⟫
end Funₒ

infix:50 " ≃ₒ " => Funₒ.equiv

namespace Equivalence
  def refl (α : U) : α ≃ₒ α :=
    ⟪Funₒ.id, Funₒ.id_is_equiv⟫
end Equivalence

namespace Univalence
  def canonical (α β : U) : α =ₒ β →ₒ α ≃ₒ β := by
    introₒ p
    path_inductionₒ p
    exact ⟪Funₒ.id, Funₒ.id_is_equiv⟫

  example : Natₒ ≃ₒ Natₒ := canonical Natₒ Natₒ (by rflₒ)

  axiom univalence {α β : U} : Funₒ.is_equiv (canonical α β)

  def eqv_to_id {α β : U} : α ≃ₒ β → α =ₒ β :=
    pr₁ <| univalence
end Univalence

section Lemma_4_8_1
  universe u
  variable {α : U.{u}} {β : α → U.{u}} {a : α}
  theorem fiber_pr₁_eqv_beta : @Funₒ.fiber (Sigmaₒ α β) _ (Pi.lam pr₁) a ≃ₒ β a := by
    exhibitₒ by
      introₒ fib
      let ⟪⟪x, y⟫, h⟫ := fib
      apply Id.subst h y
    apply Funₒ.qinv_to_ishae
    exhibitₒ by
      introₒ y
      exhibitₒ ⟪a, y⟫
      rflₒ
    exhibitₒ by
      introₒ fib
      simp
      rflₒ
    introₒ ⟪⟪x, y⟫, h⟫
    dsimp at h
    simp
    -- set_option trace.Meta.check true in
    -- set_option pp.all true in
    -- rewrite [pr₁.beta]
    -- path_inductionₒ h
    sorry
end Lemma_4_8_1

namespace Extensionality
  -- def weak_extensionality {α : U} {P : α → U} (f : (x : α) →ₒ U.is_contractible (P x))
  --                         : U.is_contractible (Πₒ x : α, P x) := by
  --   let p := Univalence.eqv_to_id
  section Lemma_4_9_2
    universe u₁ u₂
    variable {α β : U.{u₁}} {γ : U.{u₂}}
    variable (e : α ≃ₒ β)
    theorem lift_equiv_fun : (γ →ₒ α) ≃ₒ (γ →ₒ β) := by
      have p := Univalence.eqv_to_id e
      path_inductionₒ p
      applyₒ Univalence.canonical _ _
      rflₒ
  end Lemma_4_9_2

  section Corollary_4_9_3
    universe u
    variable {α : U.{u}} {β : α → U.{u}} (p : Πₒ x : α, U.is_contractible (β x))

    theorem pr₁_eqv : @pr₁ α β |> Pi.lam |> Funₒ.is_equiv := by
      apply Funₒ.qinv_to_ishae
      apply Funₒ.contr_to_qinv
      introₒ x
      rewriteₒ [Univalence.eqv_to_id fiber_pr₁_eqv_beta]
      exact p x
  end Corollary_4_9_3
end Extensionality

end Hott
end
