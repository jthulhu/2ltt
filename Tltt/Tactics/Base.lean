import Tltt.ObjLang

open Lean (
  Expr
  Level
  indentExpr
)
open Lean.Meta (
  MetaM
  inferType
  isDefEq
  mkFreshExprMVar
  mkFreshLevelMVar
)

set_option autoImplicit false

namespace Lean.Expr
  /-- If given `lift.{u} α`, return `(u, α)`. -/
  def lift? (e : Expr) : MetaM (Option (Level × Expr)) := do
    let u ← mkFreshLevelMVar
    let type ← mkFreshExprMVar (Expr.const ``Tltt.Hott.liftedU [u])
    let lifted := .app (.const ``Tltt.Hott.lift [u]) type
    if ← isDefEq e lifted then
      return some (u, type)
    else
      return none

  /-- If given `lift.{u} α`, return `(u, α)`, otherwise throw error. See `lift?`. -/
  def lift! (e : Expr) : MetaM (Level × Expr) := do
    let some (u, t) ← e.lift? | throwError "expected object-level type, got{indentExpr e}"
    return (u, t)

  /-- If given `lift.{u} α`, return `u`, otherwise throw error. -/
  def levelAsObjType! (e : Expr) : MetaM Level := do
    let (u, _) ← e.lift!
    return u

  /-- Given `^α`, returns `α`. -/
  def objType? (e : Expr) : MetaM (Option Expr) := do
    let t ← e.lift?
    return t >>= (·.2)

  /-- Given `^α`, returns `α`, throw error otherwise. See `objType?` -/
  def objType! (e : Expr) : MetaM Expr := do
    let some t ← e.objType?
      | throwError "expected object-level type, got{indentExpr e}"
    return t

  /-- Given `α` such that `α : ^U.{u}`, return `u`. Throw error otherwise. -/
  def objLevel! (e : Expr) : MetaM Level := do
    let t ← inferType e
    let u ← mkFreshLevelMVar
    let pattern := .const ``Tltt.Hott.liftedU [u]
    if ← isDefEq t pattern then
      return u
    else
      throwError "expression{indentExpr e}\nhas type{indentExpr t}\nwhich is not an object-level type"

  /-- Lifts `α` into `^α` -/
  def liftWith (e : Expr) (u : Level) : Expr :=
    .app (.const ``Tltt.Hott.lift [u]) e

  /-- Lifts `α` into `^α`, inferring the universe level in which `α` lives. See `liftWith`. -/
  def lift (e : Expr) : MetaM Expr := do
    let u ← e.objLevel!
    return e.liftWith u

  /-- Given `e` such that `e : lift.{u} α`, return `(u, α)`. -/
  def inferObjType? (e : Expr) : MetaM (Option (Level × Expr)) := do
    let t ← inferType e
    t.lift?

  /-- Given `e` such that `e : lift.{u} α`, return `(u, α)`, throw error otherise. -/
  def inferObjType! (e : Expr) : MetaM (Level × Expr) := do
    let some t ← e.inferObjType?
      | throwError "expression{indentExpr e}\nis not an object-level term"
    return t
end Lean.Expr
