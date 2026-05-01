import Tltt.Reedy.ReedyFibrancy
import Misc.Category

noncomputable section
namespace Tltt.ReedyFibrancy
open CategoryTheory
open Fibrancy
open Hott

@[ext]
structure ReedyPresheaf (D : Type _) [DirectCategory D] (n : Nat) : Type _ where
  presheaf : Psh (Below D n)
  is_reedy : is_reedy_up_to n presheaf

namespace ReedyPresheaf
  def ext' {D : Type*} [DirectCategory D] {n : Nat} (F G : ReedyPresheaf D n)
           (p : F.presheaf = G.presheaf)
           (q : ∀ i, F.is_reedy i = eqToHom (C := Type _) (by rw [p]) (G.is_reedy i))
           : F = G := by
    induction F with | mk pshF is_reedy_F =>
    induction G with | mk pshG is_reedy_G =>
    dsimp only at p q
    induction p
    simp
    funext
    apply q
    
  def empty (D : Type _) [DirectCategory D] : ReedyPresheaf D 0 where
    presheaf := empty.functor D
    is_reedy := by
      intro i
      exfalso
      apply Nat.not_lt_zero
      exact i.rank_is_lt

  def psh_below_zero_eqv_unit {D : Type*} [DirectCategory D] : ReedyPresheaf D 0 ≃ PUnit where
    toFun _ :=
      .unit
    invFun _ :=
      empty D
    left_inv := by
      intro X
      simp
      ext
      · apply eq_of_empty_shape
        calc
          _ ≃ Below D 0 := op_eqv
          _ ≃ _ := Below.eqv_empty_of_zero
      · apply heq_of_cast_eq
        · funext x
          exfalso
          apply Nat.not_lt_zero
          apply x.rank_is_lt
        · apply piext
          intro x
          exfalso
          apply Nat.not_lt_zero
          apply x.rank_is_lt
    right_inv := by
      intro
      ext

end ReedyPresheaf

def fib_below_zero {D : Type*} [DirectCategory D] : IsFibrantWeak (ReedyPresheaf D 0) := by
  apply fibrant_of_eqv_fibrant (α := Unit)
  · apply unit_is_fibrant
  · apply Equiv.symm
    apply ReedyPresheaf.psh_below_zero_eqv_unit

universe u₁ u₂ in
@[ext]
structure LayeredReedyPresheaf (D : Type u₁) [DirectCategory.{u₁, max u₁ u₂} D] (n : Nat)
          extends Presheaf.LayeredPresheaf D n where
  is_reedy : is_reedy_up_to.{u₁, u₂} n X
  is_fibrant (i : OfRank D n) : is_reedy_at.{u₁, max u₁ u₂} i.point (restrict₄ i toLayeredPresheaf.to_psh)

namespace LayeredReedyPresheaf
  universe u₁ u₂
  variable {D : Type u₁} [DirectCategory.{u₁, max u₁ u₂} D] {n : Nat}
  
  section ToPsh
  variable (self : LayeredReedyPresheaf D n)

  variable (i : Below D (n+1))

  def to_rd_psh : ReedyPresheaf D (n+1) where
    presheaf := self.toLayeredPresheaf.to_psh
    is_reedy (i : Below D (n+1)) :=
      if h : rk i = n then
        let i' : OfRank D n := ⟨i.point, h⟩
        self.is_fibrant i'
      else by
        let i' : Below D n := i.of_succ_of_rk_ne h
        suffices h : restrict₂ i self.to_psh = restrict₂ i' self.X
        rw [h]
        apply self.is_reedy i'
        refine CategoryTheory.Functor.ext ?object ?map
        · intro j
          simp [restrict₂]
          apply Presheaf.LayeredPresheaf.ToPsh.obj_rk_lt_n
          apply Nat.ne_of_lt
          simp
          calc
            _ ≤ rk i := by
              apply Nat.le_of_lt_succ
              apply Below.rank_is_lt
            _ = rk i' := rfl
            _ < n := i'.rank_is_lt
        · intro j k f
          apply Presheaf.LayeredPresheaf.ToPsh.map_rk_lt_n <;> simp <;> {
            apply Nat.ne_of_lt
            calc
            _ ≤ rk i := by
              apply Nat.le_of_lt_succ
              apply Below.rank_is_lt
            _ = rk i' := rfl
            _ < n := by apply Below.rank_is_lt
          }
  end ToPsh

  section OfPsh
  variable (F : ReedyPresheaf D (n+1))

  @[simp]
  def of_rd_psh : LayeredReedyPresheaf D n where
    toLayeredPresheaf := Presheaf.LayeredPresheaf.of_psh F.presheaf
    is_fibrant := by
      intro i
      let i' : Below D (n+1) := i.as_below
      rw [Presheaf.LayeredPresheaf.left_inv]
      suffices h : restrict₄ i F.presheaf = restrict₂ i' F.presheaf
      rw [h]
      apply F.is_reedy i'
      rfl
    is_reedy := by
      intro i
      let i' : Below D (n+1) := i.up
      simp [Presheaf.LayeredPresheaf.of_psh]
      suffices h : restrict₂ i (restrict₁ F.presheaf) = restrict₂ i' F.presheaf
      rw [h]
      apply F.is_reedy i'
      rfl
  end OfPsh

  @[simp]
  def left_inv : Function.LeftInverse (to_rd_psh (D := D) (n := n)) of_rd_psh := by
    intro ⟨psh, psh_is_reedy⟩
    dsimp
    apply ReedyPresheaf.ext'
    · dsimp only
      intro i
      sorry
    · dsimp only
      apply Presheaf.LayeredPresheaf.left_inv
      

  def right_inv : Function.RightInverse (to_rd_psh (D := D) (n := n)) of_rd_psh := by
    intro l
    unfold of_rd_psh to_rd_psh
    ext <;> dsimp only
    repeat sorry

  def eqv_of_layer_below : ReedyPresheaf D (n+1) ≃ LayeredReedyPresheaf D n where
    toFun := of_rd_psh
    invFun := to_rd_psh
    left_inv := left_inv
    right_inv := right_inv
end LayeredReedyPresheaf

universe u₁ u₂ in
structure CompactLRP (D : Type u₁) [DirectCategory.{u₁, max u₁ u₂} D] (n : Nat) where
  X : ReedyPresheaf D n
  glueing : ∀ i : OfRank D n,
            MatchingObject i.point (restrict₅ i X.presheaf)
            → Typeₒ.{max u₁ u₂}

universe u₁ u₂ in
abbrev SigmaCompactLRP (D : Type u₁) [DirectCategory.{u₁, max u₁ u₂} D] (n : Nat) :=
  Σ X : ReedyPresheaf D n,
  ∀ i : OfRank D n,
  MatchingObject i.point (restrict₅ i X.presheaf) → Typeₒ.{max u₁ u₂}

namespace CompactLRP
  universe u₁ u₂
  variable {D : Type u₁} [DirectCategory.{u₁, max u₁ u₂} D] {n : Nat}

  namespace ToLRP
  variable (self : CompactLRP.{u₁, u₂} D n)

  abbrev X : Psh (Below D n) :=
    self.X.presheaf

  abbrev Y (i : OfRank D n) : Type _ :=
    Σ z, self.glueing i z

  abbrev u {i : OfRank D n} {j : Below D n} (f : j.point ⟶ i.point) : Y self i → (X self).obj (.op j) := by
    intro y
    induction y with | mk z a =>
    let cone := MatchingObject.limit_cone i.point (restrict₅ i self.X.presheaf) |>.cone
    have : i.point ≠ j.point := by
      intro i_eq_j
      apply Nat.lt_irrefl n
      conv =>
        lhs
        rw [← i.rank_is, i_eq_j]
      apply j.rank_is_lt
    induction i with | mk i rk_i_eq_n =>
    induction rk_i_eq_n
    have := cone.π.app ⟨j.point, f, this⟩
    dsimp [restrict₅, under.inclusion] at this
    apply this
    show MatchingObject _ _
    dsimp only at z ⊢
    exact z

  abbrev is_reedy : is_reedy_up_to n (X self) :=
    self.X.is_reedy

  abbrev coh : ∀ {i : OfRank D n} {j k : Below D n} (f : j.point ⟶ i.point) (g : k ⟶ j),
               (X self).map g.op ∘ u self f = u self (g ≫ f) := by
    intro ⟨i, rk_i_eq_n⟩ j k f g
    induction rk_i_eq_n
    dsimp
    funext ⟨z, hello⟩
    simp
    generalize_proofs pf₁ pf₂
    let cone := (MatchingObject.limit_cone i self.X.presheaf).cone
    let j' : under i := by
      exists j.point, f
      intro i_eq_j
      apply Nat.lt_irrefl (rk i)
      conv =>
        lhs
        rw [i_eq_j]
      apply Below.rank_is_lt
    let k' : under i := by
      exists k.point, g ≫ f
      intro k_eq_j
      apply Nat.lt_irrefl (rk i)
      conv =>
        lhs
        rw [k_eq_j]
      apply Below.rank_is_lt
    let g' : k' ⟶ j' := by exists g
    apply Eq.symm
    apply congrFun <| cone.π.naturality (.op g')

  abbrev layered_presheaf : Presheaf.LayeredPresheaf D n where
    X := X self
    Y := Y self
    u := u self
    coh := coh self

  theorem restrict_lp_to_psh : (restrict₁ (layered_presheaf self).to_psh) = self.X.presheaf := by
    refine CategoryTheory.Functor.ext ?object ?map
    · intro ⟨i⟩
      unfold Presheaf.LayeredPresheaf.to_psh
      simp
      rw [Presheaf.LayeredPresheaf.ToPsh.obj_rk_lt_n]
      · simp [X]
        rfl
      · simp
        intro h
        apply Nat.lt_irrefl n
        conv => lhs; rw [← h]
        apply Below.rank_is_lt
    · intro ⟨i⟩ ⟨j⟩ f
      simp [restrict₁, layered_presheaf, Presheaf.LayeredPresheaf.to_psh]
      rw [Presheaf.LayeredPresheaf.ToPsh.map_rk_lt_n]
      · rfl
      repeat {
        intro h
        apply Nat.lt_irrefl n
        conv => lhs; rw [← h]
        apply Below.rank_is_lt
      }

  abbrev is_fibrant : ∀ (i : OfRank D n),
                      is_reedy_at i.point (restrict₄ i (layered_presheaf self).to_psh) := by
    intro ⟨i, rk_i_eq_n⟩
    induction rk_i_eq_n
    dsimp
    unfold is_reedy_at
    unfold is_fibration_strict
    exists ?map
    case map =>
      have : MatchingObject i (restrict₁ (layered_presheaf self).to_psh)
             = MatchingObject i self.X.presheaf := by
        rw [restrict_lp_to_psh]
      refine ?_ ∘ eqToHom this
      exact self.glueing i
    simp
    constructor
    · sorry
    · sorry

  def to_lrp : LayeredReedyPresheaf.{u₁, u₂} D n where
    X := X self
    Y := Y self
    u := u self
    coh := coh self
    is_reedy := is_reedy self
    is_fibrant := is_fibrant self
  end ToLRP
  export ToLRP (to_lrp)

  section OfLRP
  variable (l : LayeredReedyPresheaf.{u₁, u₂} D n)

  def of_lrp : CompactLRP.{u₁, u₂} D n where
    X := {
      presheaf := l.X
      is_reedy := l.is_reedy
    }
    glueing i z := by
      dsimp only at z
      induction i with | mk i rk_i_eq_n =>
      induction rk_i_eq_n
      simp at z
      have := l.is_fibrant (OfRank.in_own_layer i)
      simp at this
      cases this with | mk can hello =>
      apply can
      suffices h : restrict₁ (restrict₄ i l.to_psh) = l.X
      · erw [h]
        exact z
      · refine CategoryTheory.Functor.ext ?object ?map
        · intro ⟨x⟩
          simp [restrict₄]
          apply Presheaf.LayeredPresheaf.ToPsh.obj_rk_lt_n
          simp
          intro rk_x_eq_rk_i
          apply Nat.lt_irrefl (rk i)
          conv => lhs; rw [← rk_x_eq_rk_i]
          apply x.rank_is_lt
        · intro ⟨x⟩ ⟨y⟩ f
          simp [restrict₁, restrict₄]
          apply Presheaf.LayeredPresheaf.ToPsh.map_rk_lt_n <;> {
            simp
            intro h
            apply Nat.lt_irrefl (rk i)
            conv =>
              lhs
              rw [← h]
            apply Below.rank_is_lt
          }
          
  end OfLRP

  def left_inv : Function.LeftInverse (to_lrp (D := D) (n := n)) of_lrp := by
    sorry

  def right_inv : Function.RightInverse (to_lrp (D := D) (n := n)) of_lrp := by
    sorry

  def compact_eqv_layered : LayeredReedyPresheaf D n ≃ CompactLRP D n where
    toFun := of_lrp
    invFun := to_lrp
    left_inv := left_inv
    right_inv := right_inv

  def compact_eqv_sigma : CompactLRP D n ≃ SigmaCompactLRP D n where
    toFun x :=
      let ⟨X, glueing⟩ := x
      ⟨X, glueing⟩
    invFun x :=
      let ⟨X, glueing⟩ := x
      ⟨X, glueing⟩
    left_inv := by
      intro
      rfl
    right_inv := by
      intro
      rfl

end CompactLRP

variable {D : Type*} [DirectCategory D] {n : Nat} in
def rdpsh_eqv_compact : ReedyPresheaf D (n+1) ≃ SigmaCompactLRP D n := by
  calc
    _ ≃ _ := by apply LayeredReedyPresheaf.eqv_of_layer_below
    _ ≃ _ := by apply CompactLRP.compact_eqv_layered
    _ ≃ _ := by apply CompactLRP.compact_eqv_sigma

end Tltt.ReedyFibrancy



namespace Fibrancy
def hello {α β : Type _} (p : α = β) (x : α) : (show α → α by rw [p]; exact id) x = x := by
  induction p
  rfl

end Fibrancy

end
