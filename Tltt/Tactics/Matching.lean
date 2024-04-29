import Tltt.ObjLang
import Tltt.Tactics.Base

open Lean.Meta (
  isDefEq
  mkFreshExprMVar
  mkFreshLevelMVar
)

set_option autoImplicit false

namespace Lean.Expr
  /-- Given `Id.{u} {α} x y`, return `(u, α, x, y)`. -/
  def id? (e : Expr) : MetaM (Option (Level × Expr × Expr × Expr)) := do
    let u ← mkFreshLevelMVar
    let α ← mkFreshExprMVar (Expr.const ``Tltt.Hott.liftedU [u])
    let x ← mkFreshExprMVar (α.liftWith u)
    let y ← mkFreshExprMVar (α.liftWith u)
    let pattern := mkApp3 (.const ``Tltt.Hott.Id [u]) α x y
    if ← isDefEq e pattern then
      return some (u, α, x, y)
    else
      return none

  /-- Given `Pi.{u₁, u₂} α β`, return `(u₁, u₂, α, β)`. -/
  def pi? (e : Expr) : MetaM (Option (Level × Level × Expr × Expr)) := do
    let u₁ ← mkFreshLevelMVar
    let u₂ ← mkFreshLevelMVar
    let α ← mkFreshExprMVar (Expr.const ``Tltt.Hott.liftedU [u₁])
    let β ← mkFreshExprMVar (Expr.forallE `_ (α.liftWith u₁) (.const ``Tltt.Hott.liftedU [u₂]) .default)
    let pattern := mkApp2 (.const ``Tltt.Hott.Pi [u₁, u₂]) α β
    if ← isDefEq e pattern then
      return some (u₁, u₂, α, β)
    else
      return none

  def sigma? (e : Expr) : MetaM (Option (Level × Level × Expr × Expr)) := do
    let u₁ ← mkFreshLevelMVar
    let u₂ ← mkFreshLevelMVar
    let α ← mkFreshExprMVar (Expr.const ``Tltt.Hott.liftedU [u₁])
    let β ← mkFreshExprMVar (Expr.forallE `_ (α.liftWith u₁) (.const ``Tltt.Hott.liftedU [u₂]) .default)
    let pattern := mkApp2 (.const ``Tltt.Hott.Sigmaₒ [u₁, u₂]) α β
    if ← isDefEq e pattern then
      return some (u₁, u₂, α, β)
    else
      return none
end Lean.Expr
