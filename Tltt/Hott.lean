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
  def id_is_id {α : U} {x : α} : id x = x :=
    rfl

  @[reducible]
  def after {α β γ : U} (f : α →ₒ β) (g : β →ₒ γ) : α →ₒ γ :=
    Λ x => g $ₒ f x

  @[reducible]
  def compose {α β γ : U} (f : β →ₒ γ) (g : α →ₒ β) : α →ₒ γ :=
    Λ x => f $ₒ g x

  infixr:90 " ∘ₒ " => compose

  @[simp]
  theorem compose.beta {α β γ : U} (f : β →ₒ γ) (g : α →ₒ β) (x : α) : (f ∘ₒ g) x = f (g x) := rfl

  @[simp]
  theorem id_comp {α β : U} (f : α →ₒ β) : id ∘ₒ f = f := rfl

  @[simp]
  theorem comp_id {α β : U} (f : α →ₒ β) : f ∘ₒ id = f := rfl
end Funₒ

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

def Singleton {α : U} (x : α) : U :=
  Σₒ x' : α, x =ₒ x'

namespace Singleton
  -- Lemma 3.11.8
  -- Note: in the book, this is prooved using the characterization of paths in Σₒ-types
  theorem is_contr {α : U} {a : α} : U.is_contractible (Singleton a) := by
    exhibitₒ ⟪a, Id.refl a⟫
    introₒ o
    let ⟪a', p⟫ := o
    simp at p
    apply @Id.based_path_induction α a (fun x p'' => ⟪a, Id.refl a⟫ =ₒ ⟪x, p''⟫) (Id.refl _) a' p
end Singleton

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

  def happly {α : U} {β : α → U} {f g : Pi α β} (p : f =ₒ g) : f ~ g := by
    path_inductionₒ p
    exact Homotopy.refl _

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
    · exact Singleton.is_contr
  end

  abbrev is_equiv {α β : U} (f : α →ₒ β) : U :=
    ishae f

  def qinv_to_equiv {α β : U} {f : α →ₒ β} : qinv f → is_equiv f :=
    qinv_to_ishae f

  def equiv (α β : U) : U :=
    Σₒ f : α →ₒ β, is_equiv f

  def equiv_to_qinv {α β : U} (e : equiv α β) : Σₒ f : α →ₒ β, qinv f :=
    let ⟪f, hae⟫ := e
    ⟪f, ishae_to_qinv f hae⟫

  theorem id_is_equiv {α : U} : is_equiv (@id α) := by
    apply qinv_to_ishae
    exact ⟪id, Homotopy.refl id, Homotopy.refl id⟫
end Funₒ

infix:50 " ≃ₒ " => Funₒ.equiv

def Equivalence.refl (α : U) : α ≃ₒ α :=
  ⟪Funₒ.id, Funₒ.id_is_equiv⟫

@[simp]
theorem Equivalence.refl.beta {α : U} : pr₁ (refl α) = Funₒ.id := by rfl

namespace Funₒ
  @[simp]
  def equiv_to_qinv.beta {α : U} : equiv_to_qinv (Equivalence.refl α)
                                   = ⟪Funₒ.id, Funₒ.id, funₒ x => by rflₒ, funₒ x => by rflₒ⟫ := by
    rfl'

  @[simp]
  def ishae_to_qinv.beta {α : U} : ishae_to_qinv id id_is_equiv
                                   = ⟪Funₒ.id, funₒ x : α => by rflₒ, funₒ x => by rflₒ⟫ := by
    rfl'
end Funₒ

namespace Unitₒ
  theorem eq_unit (x : Unitₒ) : x =ₒ ()ₒ := by
    apply Unitₒ.elim (motive := fun x => x =ₒ ()ₒ) (Id.refl ()ₒ)

  theorem id_is_unit (x y : Unitₒ) : (x =ₒ y) ≃ₒ Unitₒ := by
    exhibitₒ by
      introₒ _p
      exact ()ₒ
    apply Funₒ.qinv_to_equiv
    exhibitₒ by
      introₒ ()ₒ
      refine Unitₒ.elim (motive := fun x => x =ₒ y) ?_ x
      refine Unitₒ.elim (motive := fun y => ()ₒ =ₒ y) ?_ y
      rflₒ
    exhibitₒ by
      introₒ z
      simp
      rewriteₒ [eq_unit z]
      rflₒ
    introₒ p
    simp
    refine Unitₒ.elim (motive := fun y => (Unitₒ.elim (motive := fun x => x =ₒ y) (Unitₒ.elim (motive := fun y => ()ₒ =ₒ y) (Id.refl ()ₒ) y) x) =ₒ p) ?_ y
    simp
    refine Unitₒ.elim (motive := fun x => (Unitₒ.elim (Id.refl ()ₒ) x) =ₒ p) ?_ x
    simp
    path_inductionₒ p
    rflₒ

  theorem loop_is_refl {x : Unitₒ} (p : x =ₒ x) : p =ₒ Id.refl x := by
    let ⟪f, g, gf_id, _⟫ := id_is_unit x x
    have fp_is_frefl : f p =ₒ f (Id.refl x) := by
      rwₒ [eq_unit (f p), eq_unit (f (Id.refl x))]
    have gfp_is_gfrefl := Id.ap g fp_is_frefl
    rewriteₒ [gf_id _, gf_id _] at gfp_is_gfrefl
    assumption
end Unitₒ

namespace U.is_contractible
  theorem contr_eqv_unit {α : U} (cntrl : is_contractible α) : α ≃ₒ Unitₒ := by
    exhibitₒ by
      introₒ _x
      exact ()ₒ
    apply Funₒ.qinv_to_equiv
    exhibitₒ by
      introₒ ()ₒ
      exact pr₁ cntrl
    exhibitₒ by
      introₒ ()ₒ
      rflₒ
    introₒ x
    exact pr₂ cntrl x

  theorem singleton_eqv_unit {α : U} : Singleton α ≃ₒ Unitₒ := by
    apply contr_eqv_unit
    apply Singleton.is_contr
end U.is_contractible

namespace Sigmaₒ
  section Theorem_2_7_2
    variable {α : U} {β : α → U} {w w' : Σₒ x : α, β x}

    theorem eq_constructor : (w =ₒ w') ≃ₒ Σₒ p : pr₁ w =ₒ pr₁ w', Id.subst p (pr₂ w) =ₒ pr₂ w' := by
      exhibitₒ by
        introₒ p
        path_inductionₒ p
        exhibitₒ Id.refl _
        rflₒ
      apply Funₒ.qinv_to_ishae
      let ⟪w₁, w₂⟫ := w
      let ⟪w₁', w₂'⟫ := w'
      exhibitₒ by
        introₒ ptn
        let ptn : Σₒ p : w₁ =ₒ w₁', Id.subst p w₂ =ₒ w₂' := ptn
        let ⟪p, q⟫ := ptn
        path_inductionₒ p
        dsimp at q
        rwₒ [q]
      exhibitₒ by
        introₒ ⟪p, q⟫
        simp
        replace pr₁ ⟪w₁, w₂⟫ with w₁ at p q
        sorry
        -- path_inductionₒ p
  end Theorem_2_7_2
end Sigmaₒ

namespace Equivalence
  theorem trans {α β γ : U} (e : α ≃ₒ β) (e' : β ≃ₒ γ) : α ≃ₒ γ := by
    let ⟪f, g, fg_id, gf_id⟫ := Funₒ.equiv_to_qinv e
    let ⟪f', g', f'g'_id, g'f'_id⟫ := Funₒ.equiv_to_qinv e'
    exhibitₒ f' ∘ₒ f
    apply Funₒ.qinv_to_ishae _
    exhibitₒ g ∘ₒ g'
    exhibitₒ by
      introₒ x
      simp
      rwₒ [fg_id _, f'g'_id _]
      rflₒ
    introₒ x
    simp
    rwₒ [g'f'_id _, gf_id _]
    rflₒ

  theorem symm {α β : U} (e : α ≃ₒ β) : β ≃ₒ α := by
    let ⟪f, f_is_hae⟫ := e
    let ⟪g, fg_id, gf_id⟫ := Funₒ.ishae_to_qinv f f_is_hae
    exhibitₒ g
    apply Funₒ.qinv_to_ishae
    exact ⟪f, gf_id, fg_id⟫

  section Exercise_2_10
    variable {α : U} {β : α → U} {γ : (Σₒ x : α, β x) → U}
    theorem sigma_assoc : (Σₒ x : α, Σₒ y : β x, γ ⟪x, y⟫) ≃ₒ Σₒ p : (Σₒ x : α, β x), γ p := by
      exhibitₒ by
        introₒ ⟪x, y, z⟫
        exhibitₒ ⟪x, y⟫
        exact z
      apply Funₒ.qinv_to_ishae
      exhibitₒ by
        introₒ ⟪⟪x, y⟫, z⟫
        exhibitₒ x
        exhibitₒ y
        exact z
      exhibitₒ by
        introₒ ⟪⟪x, y⟫, z⟫
        rflₒ
      introₒ ⟪x, y, z⟫
      rflₒ
  end Exercise_2_10

  -- Definition 4.7.5
  def total {α : U} {β β' : α → U} (f : (x : α) →ₒ (β x →ₒ β' x))
            : Funₒ (Σₒ x : α, β x) (Σₒ x : α, β' x) :=
    funₒ ptn => let ⟪x, y⟫ := ptn; ⟪x, f x y⟫

  section
    variable {α : U} {β β' : α → U} (f : (x : α) →ₒ (β x →ₒ β' x))

    -- Theorem 4.7.6
    theorem fiber_total_is_fiber (x : α) (v : β' x): Funₒ.fiber (total f) ⟪x, v⟫ ≃ₒ Funₒ.fiber (f x) v := by
      apply Equivalence.trans (β := Σₒ a : α, Σₒ u : β a, ⟪a, f a u⟫ =ₒ ⟪x, v⟫)
      · apply symm
        apply @sigma_assoc α β (fun ⟪a, u⟫ => ⟪a, f a u⟫ =ₒ ⟪x, v⟫)
      apply Equivalence.trans (β := Σₒ a : α, Σₒ u : β a, Σₒ p : a =ₒ x, Id.subst p (f a u) =ₒ v)
      · sorry
      apply Equivalence.trans (β := Σₒ a : α, Σₒ p : a =ₒ x, Σₒ u : β a, Id.subst p (f a u) =ₒ v)
      · sorry
      apply Equivalence.trans (β := Σₒ u : β x, f x u =ₒ v)
      · sorry
      exact Equivalence.refl _

    -- Theorem 4.7.7
    theorem total_equiv_if_equiv (f_eqv : Πₒ x : α, Funₒ.is_equiv (f x)) : Funₒ.is_equiv (total f) := by
      apply Funₒ.qinv_to_equiv
      apply Funₒ.contr_to_qinv
      introₒ ⟪x, v⟫
      apply Funₒ.retract_preseve_contractible (Funₒ.fiber (f x) v)
      · let ⟪s, r, rs_id, _⟫ := fiber_total_is_fiber f x v
        exhibitₒ r
        exhibitₒ s
        exact rs_id
      · refine Funₒ.qinv_to_contr _ ?_ _
        apply Funₒ.ishae_to_qinv
        exact f_eqv x

    theorem equiv_if_total_equiv (total_f_eqv : Funₒ.is_equiv (total f)) (x : α) : Funₒ.is_equiv (f x) := by
      apply Funₒ.qinv_to_equiv
      apply Funₒ.contr_to_qinv
      introₒ v
      apply Funₒ.retract_preseve_contractible (Funₒ.fiber (total f) ⟪x, v⟫)
      · let ⟪r, s, _, rs_id, _⟫ := fiber_total_is_fiber f x v
        exhibitₒ r
        exhibitₒ s
        exact rs_id
      · refine Funₒ.qinv_to_contr _ ?_ _
        apply Funₒ.ishae_to_qinv
        exact total_f_eqv
  end
end Equivalence

namespace Univalence
  def canonical (α β : U) : α =ₒ β →ₒ α ≃ₒ β := by
    introₒ p
    path_inductionₒ p
    exact ⟪Funₒ.id, Funₒ.id_is_equiv⟫

  @[simp]
  def canonical.beta {α : U} : canonical α α (Id.refl α) = Equivalence.refl α := by
    rfl

  example : Natₒ ≃ₒ Natₒ := canonical Natₒ Natₒ (by rflₒ)

  axiom univalence {α β : U} : Funₒ.is_equiv (canonical α β)

  theorem univalence.beta {α : U} : pr₁ (@univalence α α) (Equivalence.refl α) =ₒ Id.refl α := by
    let ⟪canon_inv, rinv, _⟫ := univalence
    simp
    rewrite [← canonical.beta]
    rewriteₒ [rinv _]
    rflₒ

  def eqv_to_id {α β : U} : α ≃ₒ β → α =ₒ β :=
    pr₁ <| univalence

  @[simp]
  def eqv_to_id.beta {α : U} : eqv_to_id (Equivalence.refl α) =ₒ Id.refl α := by
    exact univalence.beta

  theorem canonical_eqv_to_id {α β : U} : canonical α β ∘ₒ (Pi.lam eqv_to_id) ~ Funₒ.id :=
    univalence |> pr₂ |> pr₂ |> pr₁

  theorem eqv_to_id_canonical {α β : U} : (Pi.lam eqv_to_id) ∘ₒ canonical α β ~ Funₒ.id :=
    univalence |> pr₂ |> pr₁
end Univalence

theorem U.is_contractible.path_is_refl {α : U} {x : α} (ctr : is_contractible α) (p : x =ₒ x)
                                       : p =ₒ Id.refl x := by
  let ⟪f, g, gf_id, _⟫ := contr_eqv_unit ctr
  apply Funₒ.linv_cancellation (Id.ap f |> Pi.lam)
  · apply Funₒ.ap_section_is_section
    exact ⟪g, gf_id⟫
  · apply Unitₒ.loop_is_refl

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
      have underlying (p : α =ₒ β) : (γ →ₒ α) ≃ₒ (γ →ₒ β) := by
        path_inductionₒ p
        exact Equivalence.refl _
      have p := Univalence.eqv_to_id e
      exact underlying p

    theorem lift_equiv_fun.beta {α γ : U} : lift_equiv_fun (Equivalence.refl α)
                                            =ₒ Equivalence.refl (γ →ₒ α) := by
      unfold lift_equiv_fun
      simp
      rewriteₒ [@Univalence.eqv_to_id.beta α]
      rflₒ

    @[simp]
    theorem lift_equiv_fun.pr₁.beta (f : γ →ₒ α) : pr₁ (lift_equiv_fun e) f =ₒ (pr₁ e) ∘ₒ f := by
      have underlying (p : α =ₒ β)
                     : pr₁ (lift_equiv_fun (Univalence.canonical _ _ p)) f
                       =ₒ (pr₁ (Univalence.canonical _ _ p)) ∘ₒ f := by
        path_inductionₒ p
        simp
        rwₒ [lift_equiv_fun.beta]
        rflₒ
      have h := underlying (Univalence.eqv_to_id e)
      rewriteₒ [Univalence.canonical_eqv_to_id _] at h
      exact h
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

    theorem into_sum_of_contractible_is_into_base : (α →ₒ Σₒ x : α, β x) ≃ₒ (α →ₒ α) := by
      apply lift_equiv_fun
      exhibitₒ Pi.lam pr₁
      exact pr₁_eqv p
  end Corollary_4_9_3
end Extensionality

namespace Singleton
  section Lemma_3_11_9
    universe u
    variable {α : U.{u}} {β : α → U.{u}}
    theorem sum_is_base_if_contr (p : Πₒ x : α, U.is_contractible (β x)) : (Σₒ x : α, β x) ≃ₒ α := by
      exhibitₒ Pi.lam pr₁
      apply Extensionality.pr₁_eqv
      assumption

    theorem contract_sum (α_ctrbl : U.is_contractible α) : (Σₒ x : α, β x) ≃ₒ (β (pr₁ α_ctrbl)) := by
      let a := pr₁ α_ctrbl
      let a_is_center := pr₂ α_ctrbl
      exhibitₒ by
        introₒ ⟪x, y⟫
        dsimp at y
        exact Id.subst (a_is_center x)⁻¹ y
      apply Funₒ.qinv_to_ishae
      exhibitₒ by
        introₒ z
        exhibitₒ a
        exact z
      exhibitₒ by
        introₒ h
        simp
        rewriteₒ [U.is_contractible.path_is_refl α_ctrbl <| pr₂ α_ctrbl (pr₁ α_ctrbl)]
        rflₒ
      introₒ ⟪x, y⟫
      revertₒ y
      simp
      rewriteₒ [← a_is_center x, U.is_contractible.path_is_refl α_ctrbl <| a_is_center _]
      introₒ y
      rflₒ
  end Lemma_3_11_9
end Singleton

namespace U.is_contractible
  theorem map_is_eqv {α β : U} (α_contr : is_contractible α) (β_contr : is_contractible β) (f : α →ₒ β)
                     : Funₒ.is_equiv f := by
    apply Funₒ.qinv_to_ishae
    exhibitₒ by
      introₒ _y
      exact pr₁ α_contr
    exhibitₒ by
      introₒ y
      apply Id.trans _ (pr₁ β_contr) _
      · exact (pr₂ β_contr _)⁻¹
      · exact pr₂ β_contr _
    introₒ x
    exact pr₂ α_contr _

end U.is_contractible

namespace WeakChoice
  variable {α : U} {β : α → U} {γ : (x : α) → β x → U}

  -- Function 2.15.6
  def choice (ex : Πₒ x : α, Σₒ a : β x, γ x a) : Πₒ x : α, β x := by
    introₒ x
    exact ex x |> pr₁

  theorem choice.is_correct (ex : Πₒ x : α, Σₒ a : β x, γ x a) : Πₒ x : α, γ x (choice ex x) := by
    introₒ x
    exact ex x |> pr₂

  def choice.map : Funₒ (Πₒ x : α, Σₒ a : β x, γ x a) (Σₒ g : (Πₒ x : α, β x), Πₒ x : α, γ x (g x)) :=
    funₒ ex => ⟪choice ex, choice.is_correct ex⟫

  -- Half of Theorem 2.15.7
  theorem choice_is_retract : Funₒ.rinv (@choice.map α β γ) := by
    exhibitₒ by
      introₒ ⟪g, h⟫
      introₒ x
      exact ⟪g x, h x⟫
    introₒ ⟪g, h⟫
    simp
    unfold choice.map choice choice.is_correct
    rflₒ
end WeakChoice

namespace Extensionality
  section Theorem_4_9_4
    universe u
    variable {α : U.{u}} {β : α → U.{u}} (p : Πₒ x : α, U.is_contractible (β x))

    theorem weak_fun_ext : U.is_contractible (Πₒ x : α, β x) := by
      let f := pr₁ <| into_sum_of_contractible_is_into_base (α := α) (β := β) p
      let f_is_equiv := pr₂ <| into_sum_of_contractible_is_into_base (α := α) (β := β) p
      apply Funₒ.retract_preseve_contractible (Funₒ.fiber (pr₁ <| into_sum_of_contractible_is_into_base p) Funₒ.id)
      · exhibitₒ by
          introₒ ⟪g, q⟫
          introₒ x
          unfold into_sum_of_contractible_is_into_base at q
          simp at q
          rewriteₒ [lift_equiv_fun.pr₁.beta _ _] at q
          simp at q
          let y := pr₂ (g x)
          exact Id.subst (Funₒ.happly q x) y
        exhibitₒ by
          introₒ g
          exhibitₒ funₒ x => ⟪x, g x⟫
          unfold into_sum_of_contractible_is_into_base
          unfold lift_equiv_fun
          simp
          sorry
        introₒ g
        simp
        sorry
      · refine Funₒ.qinv_to_contr f ?_ Funₒ.id
        apply Funₒ.ishae_to_qinv
        exact f_is_equiv
  end Theorem_4_9_4

  section Theorem_4_9_5
    universe u
    variable {α : U.{u}} {β : α → U.{u}} {f g : Pi α β}

    theorem happly_is_equiv : Funₒ.is_equiv (Pi.lam <| Funₒ.happly (f := f) (g := g)) := by
      apply Equivalence.equiv_if_total_equiv (funₒ g => Pi.lam <| Funₒ.happly (f := f) (g := g))
      apply U.is_contractible.map_is_eqv
      · exact Singleton.is_contr
      · apply Funₒ.retract_preseve_contractible (Πₒ x : α, Σₒ u : β x, f x =ₒ u)
        · exhibitₒ WeakChoice.choice.map
          apply WeakChoice.choice_is_retract
        · apply weak_fun_ext
          introₒ x
          apply Singleton.is_contr

    theorem fun_ext (H : f ~ g) : f =ₒ g :=
      pr₁ happly_is_equiv <| H
  end Theorem_4_9_5
end Extensionality

end Hott
end
