import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic
import Misc

namespace Tltt
class Finite (α : Type _) where
  card : Nat
  equiv : α ≃ Fin card

export Finite (card)

macro " |" e:term "| " : term =>
  `(card $e)

namespace Finite
instance (n : Nat) : Finite (Fin n) where
  card := n
  equiv := {
    toFun := id
    invFun := id
    left_inv := by
      intro x
      rfl
    right_inv := by
      intro x
      rfl
  }

instance finite_decidable_eq {α : Type*} [ι : Finite α] : DecidableEq α := by
  intro x y
  if h : ι.equiv x = ι.equiv y then
    right
    apply ι.equiv.injective
    assumption
  else
    left
    intro x_eq_y
    apply h
    congr

def el_of_card_succ {α : Type*} [Finite α] (p : |α| > 0) : α := by
  apply Finite.equiv.invFun
  apply Fin.mk 0
  exact p

instance finite_inhabited {α : Type*} [Finite α] (p : |α| > 0) : Inhabited α where
  default := el_of_card_succ p

def arg_max {α : Type _} [ι : Finite α] (f : α → Nat) (x : α) : α :=
  aux 0 x
where
  aux (i : Nat) (acc : α) : α :=
    if h : i < |α| then
      let current := ι.equiv.invFun ⟨i, h⟩
      aux (i+1) <| if f current ≤ f acc then acc else current
    else
      acc
  termination_by |α|-i

def arg_max.is_max {α : Type _} [ι : Finite α] (f : α → Nat) (x : α)
                   : ∀ y : α, f y ≤ f (arg_max f x) := by
  intro y
  unfold arg_max
  have : ∀ (i : Nat) (acc : α), f acc ≤ f (aux f i acc) := by
    apply aux.induct f
    · intro i acc h current ih
      split at ih <;> rename_i h' <;> unfold aux
      · simp [h, h']
        split <;> rename_i h'' <;> first | assumption | contradiction
      · simp [h]
        split <;> rename_i h'' <;> try contradiction
        trans f current
        · omega
        · exact ih
    · intro i acc p
      unfold aux
      simp [p]
  have : ∀ (i : Nat) (acc : α) (j : Nat) (p : j < |α|) (_ : i ≤ j),
         f (ι.equiv.invFun ⟨j, p⟩) ≤ f (aux f i acc) := by
    apply aux.induct f
    · intro i acc h current ih j p q
      unfold aux
      simp [h]
      if i_eq_j : i = j then
        simp [h, ← i_eq_j]
        split 
        · calc
            _ ≤ f acc := by assumption
            _ ≤ _ := by apply this
        · rename_i f_curr_gt_f_acc
          split at ih <;> try contradiction
          apply this
      else
        apply ih
        apply Nat.succ_le_of_lt
        apply Nat.lt_of_le_of_ne <;> assumption
    · intro i acc i_geq_card j p q
      exfalso
      apply Nat.not_succ_le_self
      apply Nat.succ_le_of_lt
      calc j
        _ < ι.card := p
        _ ≤ i := by
          apply Nat.le_of_not_lt
          assumption
        _ ≤ _ := q
  rw [← ι.equiv.left_inv y]
  apply this
  simp

def max {α : Type*} [ι : Finite α] (f : α → ℕ) : ℕ :=
  if h : |α| = 0 then
    0
  else
    let z := arg_max f <| @default _ <| finite_inhabited <| by
      apply Nat.zero_lt_of_ne_zero
      assumption
    f z

def max.is_max {α : Type*} [ι : Finite α] (f : α → ℕ) (x : α) : f x ≤ max f := by
  unfold max
  split <;> rename_i h
  · exfalso
    apply Nat.not_lt_zero
    apply Fin.isLt
    rw [← h]
    apply ι.equiv.toFun
    assumption
  · apply arg_max.is_max

instance finite_of_remove_one {α : Type*} [ι : Finite α] (x : α) : Finite { y : α // y ≠ x } where
  card := |α| - 1
  equiv :=
    let x_idx := Finite.equiv x
    have idx_inj (y : α) (p : ι.equiv y = x_idx) : y = x := by
      apply ι.equiv.left_inv.injective
      assumption
    { toFun := fun y =>
        let y_idx := Finite.equiv y.val
        if h : y_idx ≤ x_idx then
          Fin.mk y_idx <| by
            have : y_idx < x_idx := by
              apply Nat.lt_of_le_of_ne
              assumption
              intro y_idx_eq_x_ird
              apply y.prop
              apply ι.equiv.left_inv.injective
              ext
              assumption
            apply Nat.lt_of_succ_le
            apply Nat.le_pred_of_lt
            simp
            calc
              _ ≤ x_idx.val := by
                apply Nat.succ_le_of_lt
                assumption
              _ < |α| := by apply Fin.isLt
        else
          Fin.mk (y_idx-1) <| by
            apply Nat.pred_lt_pred
            · apply Nat.not_eq_zero_of_lt
              simp
              apply Nat.lt_of_not_le
              exact h
            · simp
      invFun := fun i =>
        if h : i.val < x_idx.val then
          let y := ι.equiv.symm <| .mk i.val <| by
            trans |α|-1
            · exact i.isLt
            · apply Nat.pred_lt
              apply Nat.not_eq_zero_of_lt
              simp
              calc
                _ < |α|-1 := i.isLt
                _ ≤ |α| := by simp
          .mk y <| by
            intro y_eq_x
            have : x_idx.val = i.val := calc x_idx.val
              _ = ι.equiv x := rfl
              _ = ι.equiv y := by rw [y_eq_x]
              _ = i.val := by unfold_let y; simp
            apply lt_irrefl (α := Nat)
            rewrite [this] at h
            assumption
        else
          let y := ι.equiv.symm <| .mk (i.val+1) <| by omega
          .mk y <| by
            intro y_eq_x
            have : x_idx.val = i.val+1 := calc x_idx.val
              _ = ι.equiv x := rfl
              _ = ι.equiv y := by rw [y_eq_x]
              _ = i.val+1 := by unfold_let y; simp
            apply lt_irrefl (α := Nat)
            calc x_idx.val
              _ ≤ i := by apply Nat.le_of_not_lt; exact h
              _ < i+1 := by simp
              _ = x_idx := by rw [this]
      left_inv := by
        intro y
        generalize_proofs
        simp
        split <;> rename_i h₁ <;> split <;> rename_i h₂
        · simp
        · exfalso
          apply y.prop
          apply idx_inj
          apply Fin.ext
          apply Nat.le_antisymm
          · exact h₁
          · apply Nat.le_of_not_lt
            exact h₂
        · simp at h₁ h₂
          exfalso
          rename_i h₃
          apply h₃
          apply Nat.le_of_pred_lt
          assumption
        · simp
          have (n : Nat) (p : n > 0) : n - 1 + 1 = n := by omega
          ext
          simp
          conv =>
            rhs
            rewrite [← ι.equiv.left_inv y]
          show _ = ι.equiv.symm (equiv y)
          congr
          rw [this]
          rfl
          calc
            0 ≤ x_idx.val := by simp
            _ < _ := by
              apply Nat.lt_of_not_le
              exact h₁
      right_inv := by
        intro y
        generalize_proofs
        simp
        split <;> rename_i h₁ <;> split <;> rename_i h₂
        · simp
        · simp at h₂
          exfalso
          apply LT.lt.not_lt (α := Nat)
          exact h₁
          exact h₂
        · simp
          simp at h₂
          exfalso
          apply h₁
          apply Nat.lt_of_succ_le
          exact h₂
        · simp
    }

def finite_of_add_one {α : Type*} [DecidableEq α] {x : α} (ι : Finite { y : α // y ≠ x }) : Finite α where
  card := |{ y : α // y ≠ x}| + 1
  equiv := {
    toFun := fun y =>
      if h : y = x then
        |{ y // y ≠ x}|
      else
        ι.equiv ⟨y, h⟩
    invFun := fun i =>
      if h : i = |{ y // y ≠ x}| then
        x
      else
        ι.equiv.invFun <| .mk i <| by
          apply Nat.lt_of_le_of_ne
          · apply Nat.le_of_lt_succ
            simp
          · intro e
            apply h
            apply Fin.eq_of_val_eq
            simp
            assumption
    left_inv := by
      intro y
      simp [-dite_eq_left_iff]
      split <;> rename_i h <;> simp
      · apply h.symm
      · intro y_is_last
        exfalso
        generalize_proofs at y_is_last
        apply lt_irrefl (α := Nat) |{ y // y ≠ x }|
        calc |{ y // y ≠ x }|
          _ = ι.equiv ⟨y, h⟩ := by
            show (Fin.last _).val = _
            rewrite [← y_is_last]
            rfl
          _ < _ := by apply Fin.isLt
    right_inv := by
      intro i
      simp [-dite_eq_left_iff]
      split <;> rename_i h <;> simp
      · exact h.symm
      · intro i_is_x_idx
        generalize_proofs i_lt_card at i_is_x_idx
        exfalso
        apply equiv.symm ⟨i, i_lt_card⟩ |>.prop
        assumption
  }

def unique_card {α : Type*} (ι₁ : Finite α) (ι₂ : Finite α) : ι₁.card = ι₂.card := by
  rw [← Fin.equiv_iff_eq]
  apply Nonempty.intro
  calc
    _ ≃ _ := ι₁.equiv.symm
    _ ≃ _ := ι₂.equiv

def card_of_remove_one {α : Type*} [Finite α] (x : α) : |{ y : α // y ≠ x }| = |α|-1 := by
  rfl

instance is_finite_of_card_zero {α : Type*} [Finite α] (p : |α| = 0) : IsEmpty α where
  false := by
    intro a
    apply Nat.not_lt_zero
    apply Fin.isLt
    rw [← p]
    apply Finite.equiv.toFun
    exact a

def finite_of_eqv_finite {α β : Type*} [Finite α] (p : α ≃ β) : Finite β where
  card := |α|
  equiv := by
    calc
      _ ≃ α := p.symm
      _ ≃ Fin |α| := Finite.equiv

def empty_subtype {α : Type*} [Finite α] {P : α → Prop} (p : |α| = 0) : α ≃ { x : α // P x } where
  toFun x := by
    exfalso
    apply Nat.not_lt_zero
    apply Fin.isLt
    rw [← p]
    apply Finite.equiv.toFun
    assumption
  invFun x := by
    exfalso
    apply Nat.not_lt_zero
    apply Fin.isLt
    rw [← p]
    apply Finite.equiv.toFun
    apply Subtype.val
    assumption
  left_inv := by
    intro x
    exfalso
    apply Nat.not_lt_zero
    apply Fin.isLt
    rw [← p]
    apply Finite.equiv.toFun
    assumption
  right_inv := by
    intro x
    exfalso
    apply Nat.not_lt_zero
    apply Fin.isLt
    rw [← p]
    apply Finite.equiv.toFun
    apply Subtype.val
    assumption

def _root_.Subtype.eqv_inter_comm {α : Type*} {P Q : α → Prop}
                                  : { x // P x ∧ Q x } ≃ { x // Q x ∧ P x } where
  toFun x := .mk x <| by
    cases x.prop
    constructor <;> assumption
  invFun x := .mk x <| by
    cases x.prop
    constructor <;> assumption
  left_inv := by
    intro x
    simp
  right_inv := by
    intro x
    simp

def _root_.Subtype.eqv_inter_forget {α : Type*} {P : α → Prop} (x : α) (h : P x)
                                    : { y : { y // P y } // y ≠ ⟨x, h⟩ } ≃ { y : { y // P y} // ↑y ≠ x } where
  toFun y := .mk y <| by
    intro
    apply y.prop
    apply Subtype.coe_eq_of_eq_mk
    assumption
  invFun y := .mk y <| by
    intro y_eq_x_h
    apply y.prop
    rw [y_eq_x_h]
  left_inv := by
    intro y
    simp
  right_inv := by
    intro y
    simp

def subtype_is_finite {α : Type*} [ι : Finite α] [DecidableEq α] (P : α → Prop) {d : DecidablePred P}
                      : Finite { x : α // P x } := by
  generalize p : |α| = n
  induction n generalizing α with
  | zero =>
    apply finite_of_eqv_finite (α := α)
    apply empty_subtype
    assumption
  | succ n ih =>
    let x := ι.equiv.invFun ⟨n, by rw [p]; simp⟩
    let α' := { y : α // y ≠ x }
    have ih_α' : Finite { y // P _ } := @ih α' (finite_of_remove_one x) _ (fun y => P y) (fun y => d y) <| by
      have : n = n + 1 - 1 := rfl
      rw [this, ← p]
      apply card_of_remove_one
    if h : P x then
      apply finite_of_add_one (x := ⟨x, h⟩)
      refine @finite_of_eqv_finite (α := { y : { z // z ≠ x } // P ↑y }) _ ?finite ?eqv
      · assumption
      · calc
          _ ≃ _ := by apply Equiv.subtypeSubtypeEquivSubtypeInter
          _ ≃ _ := by
            apply Subtype.eqv_inter_comm
          _ ≃ _ := by
            apply Equiv.symm
            apply Equiv.subtypeSubtypeEquivSubtypeInter
          _ ≃ _ := by
            apply Equiv.symm
            apply Subtype.eqv_inter_forget
    else
      apply @Finite.finite_of_eqv_finite _ _ ih_α'
      apply Equiv.subtypeSubtypeEquivSubtype
      intro y Py y_eq_x
      apply h
      rewrite [← y_eq_x]
      assumption

def elim_empty {α : Type*} {β : Sort*} [ι : Finite α] (p : |α| = 0) (x : α) : β := by
  exfalso
  apply Nat.not_lt_zero
  apply Fin.isLt
  rw [← p]
  apply ι.equiv.toFun
  exact x

def eqv_empty_of_card_eq_zero {α : Type*} [ι : Finite α] (p : |α| = 0) : α ≃ Empty where
  toFun x := elim_empty p x
  invFun x := by induction x
  left_inv x := elim_empty p x
  right_inv x := by induction x

def from_card_zero_eqv_unit {α : Type*} {β : α → Type*} [Finite α] (p : |α| = 0)
                            : (∀ x, β x) ≃ PUnit :=
  let α' := Empty
  let u : α' ≃ α := by
    apply Equiv.symm
    apply Finite.eqv_empty_of_card_eq_zero
    assumption
  let β' (x : α') := β (u x)
  calc
    _ ≃ (∀ x, β' x) := by
      apply pi_eqv_of_eqv
      intro a
      rfl
    _ ≃ PUnit := from_empty_eqv_unit

end Finite
end Tltt
