import Tltt.ObjLang
import Tltt.Tactics.Matching

open Lean.Meta (
  throwTacticEx
  withLocalDecl
  mkFreshExprSyntheticOpaqueMVar
  mkLambdaFVars
)

def Lean.MVarId.introₒ (goal : MVarId) : List Name → MetaM (MVarId × List FVarId)
  | [] => return (goal, [])
  | var_name::rest => do
    goal.checkNotAssigned `introₒ
    -- we have
    --   goal : ^((var : α) →ₒ (β var))
    -- we want to produce
    --   goal' : ^β
    -- with goal ≡ Pi.lam (λ var. goal')
    let goal_typeₒ ← (← goal.getType).objType!
    let some (u₁, u₂, α, β) ← goal_typeₒ.pi?
      | throwTacticEx `introₒ goal
                      "could not introduce a variable, goal has type{indentExpr goal_typeₒ}\nwhich is not a universal quantifier"
    withLocalDecl var_name .default (α.liftWith u₁) fun var => do
      let goal' ← mkFreshExprSyntheticOpaqueMVar (Expr.app β var |>.liftWith u₂)
      let (goal'', fvars) ← goal'.mvarId!.introₒ rest
      let lam ← mkLambdaFVars #[var] goal'
      goal.assign <| mkAppN (.const ``Tltt.Hott.Pi.lam [u₁, u₂]) #[α, β, lam]
      return (goal'', var.fvarId!::fvars)
