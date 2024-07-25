import Tltt.ObjLang
import Tltt.Tactics.Matching

open Lean (
  MVarId
  indentExpr
)
open Lean.Elab.Tactic (
  Tactic
  liftMetaTactic
)
open Lean.Meta (
  MetaM
  throwTacticEx
  isDefEq
)

namespace Tltt.Hott.Tactic.Rfl
  def _root_.Lean.MVarId.refl_obj (mvarId : MVarId) : MetaM Unit := do
    mvarId.withContext do
      mvarId.checkNotAssigned `rflₒ
      let τ ← mvarId.getType
      let τₒ ← τ.objType!
      let some (u, α, a, b) ← τₒ.id?
        | throwTacticEx `rflₒ mvarId m!"object equality expected, got{indentExpr τ}"
      unless ← isDefEq a b do
        throwTacticEx `rflₒ mvarId
          m!"equality lhs{indentExpr a}\nis not definitionally equal to rhs{indentExpr b}"
      mvarId.assign <| Lean.mkApp2 (.const ``Id.refl [u]) α a

  /-- `rflₒ` closes a goal of the forw `x =ₒ x` with object-level reflexivity. -/
  syntax (name := obj_refl) "rflₒ " : tactic

  @[tactic obj_refl]
  def obj_refl_impl : Tactic := fun _ =>
    liftMetaTactic fun mvarId => do
      mvarId.refl_obj
      pure []
end Tltt.Hott.Tactic.Rfl
