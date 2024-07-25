import Tltt.ObjLang
import Tltt.Tactics.Matching

open Lean (
  Expr
  MVarId
  Name
  Syntax
  indentExpr
  mkAppN
)
open Lean.Elab (throwUnsupportedSyntax)
open Lean.Elab.Tactic (
  Tactic
  TacticM
  elabTermEnsuringType
  getMainGoal
  replaceMainGoal
)
open Lean.Meta (
  mkFreshExprSyntheticOpaqueMVar
  throwTacticEx
  whnfI
  withLetDecl
)

namespace Tltt.Hott.Tactic.Exhibit
  /-- `exhibitₒ e` will reduce a goal of the form `Σₒ x, P` to a goal `P[x ← e]` -/
  syntax (name := exhibit_obj) "exhibitₒ " term (" as " ident)? : tactic

  def exhibit (mvarId : MVarId) (witness : Syntax) (name : Option Name) : TacticM Unit := do
    mvarId.withContext do
      let goal_type ← mvarId.getType
      let some (u₁, u₂, α, β) ← (← goal_type.objType!).sigma?
        | throwTacticEx `exhibitₒ mvarId m!"goal is expected to have object-level sigma type, found{indentExpr goal_type}"
      let witness_type := α.liftWith u₁
      let w ← elabTermEnsuringType witness witness_type
      match name with
      | some name =>
        withLetDecl name witness_type w fun _ => do
          let proof_validity_type ← Expr.app β w |> whnfI
          let new_goal ← mkFreshExprSyntheticOpaqueMVar (proof_validity_type.liftWith u₂)
          new_goal.mvarId!.withContext do
            mvarId.assign (mkAppN (.const ``Sigmaₒ.mk [u₁, u₂]) #[α, β, w, new_goal])
            replaceMainGoal [new_goal.mvarId!]
      | none =>
        let proof_validity_type ← Expr.app β w |> whnfI
        let new_goal ← mkFreshExprSyntheticOpaqueMVar (proof_validity_type.liftWith u₂)
        new_goal.mvarId!.withContext do
          mvarId.assign (mkAppN (.const ``Sigmaₒ.mk [u₁, u₂]) #[α, β, w, new_goal])
          replaceMainGoal [new_goal.mvarId!]

  @[tactic exhibit_obj]
  def exhibit_impl : Tactic
    | `(tactic| exhibitₒ $w as $x) => do
      let .ident _ _ name _ := x.raw
        | throwTacticEx `exhibitₒ (← getMainGoal) m!"expected variable, got {x}"
      exhibit (← getMainGoal) w name
    | `(tactic| exhibitₒ $w) => do
      exhibit (← getMainGoal) w none
    | _ => throwUnsupportedSyntax
end Tltt.Hott.Tactic.Exhibit
