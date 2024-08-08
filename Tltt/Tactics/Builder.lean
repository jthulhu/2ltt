import Tltt.ObjLang
import Tltt.Tactics.Base
import Tltt.Tactics.Matching

open Lean (
  Expr
  Level
  indentExpr
  mkApp2
  mkApp3
  mkApp4
  mkAppN
)
open Lean.Meta (
  MetaM
  inferType
  mkFreshLevelMVar
  isDefEq
  whnfD
)

namespace Tltt.Hott.Tactic

/-- Given `h : a =ₒ b`, return a proof of `b =ₒ a`. -/
def mkIdSymm (h : Expr) : MetaM Expr := do
  if h.isAppOf ``Id.refl then
    return h
  else
    let (_, τ) ← h.inferObjType!
    match ← τ.id? with
    | some (u, α, a, b) =>
      return mkApp4 (.const ``Id.symm [u]) α a b h
    | none =>
      throwError "builder for {``Id.symm}, object equality proof expected, but{indentExpr h}\nhas type{indentExpr τ}"

/-- Build the type `a =ₒ b`, unlifted! -/
def mkId (u : Level) (α a b : Expr) : MetaM Expr := do
  return mkApp3 (.const ``Id [u]) α a b

/-- Build a proof of `a =ₒ a`. -/
def mkIdRefl (a : Expr) : MetaM Expr := do
  let (u, α) ← a.inferObjType!
  return mkApp2 (.const ``Id.refl [u]) α a

def mkIdSubst (motive h idh : Expr) : MetaM Expr := do
  if (← whnfD idh).isAppOf ``Id.refl then
    return h
  let (_, idhObjType) ← idh.inferObjType!
  match ← idhObjType.id? with
  | none => throwError "AppBuilder for '{``Id.subst}, object equality proof expected{indentExpr idh}\nhas type{indentExpr idhObjType}"
  | some (u₁, α, lhs, rhs) =>
    let motiveType ← whnfD (← inferType motive)
    match motiveType with
    | .forallE _ _ motiveTargetType _ =>
      let some (_, U) ← motiveTargetType.lift?
        | throwError "Motive target type{indentExpr motiveTargetType}\nis not a object-level universe type"
      let u₂ ← mkFreshLevelMVar
      let pattern := .const ``«Typeₒ» [u₂]
      if !(← isDefEq U pattern) then
        throwError "Motive target type{indentExpr motiveTargetType}\nis not a object-level universe type"
      return mkAppN (.const ``Id.subst [u₁, u₂]) #[α, motive, lhs, rhs, idh, h]
    | _ => throwError "AppBuilder for '{``Id.subst}, invalid motive{indentExpr motive}"

def mkExpectedObjTypeHint (e : Expr) (expectedObjType : Expr) : MetaM Expr := do
  let u ← expectedObjType.objLevel!
  return mkAppN (.const ``id [.succ u]) #[expectedObjType.liftWith u, e]

end Tltt.Hott.Tactic
