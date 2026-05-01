import Tltt.ObjLang
import Tltt.Tactics.Matching
import Tltt.Tactics.Intro

open Lean (
  FVarId
  Name
  Expr
  indentExpr
  instantiateMVars
  mkApp2
  mkApp3
  mkAppN
)
open Lean.Elab (
  throwUnsupportedSyntax
)
open Lean.Elab.Tactic (
  Tactic
  TacticM
  getMainGoal
  getFVarId
  replaceMainGoal
)
open Lean.Meta (
  throwTacticEx
  forallBoundedTelescope
  forallTelescopeReducing
  mkForallFVars
  mkFreshExprSyntheticOpaqueMVar
  mkLambdaFVars
  mkAppM
  withLocalDecl
)

namespace Tltt.Hott.Tactics.PathInduction
  syntax (name := path_induction_obj) "path_inductionₒ " term (" with refl " term)? : tactic

  def path_induction (path : FVarId) (name : Name) : TacticM Unit := do
    let mvarId ← getMainGoal
    mvarId.withContext do
      let id_type ← path.getType
      let path_expr ← id_type.objType!
      let some (u, α, x, y) ← path_expr.id?
        | throwTacticEx `path_inductionₒ mvarId
                        m!"the variable {Expr.fvar path} has type{indentExpr id_type}\nwhile\n  ^(? =ₒ ?)\nwas expected"
      let .fvar x_var ← instantiateMVars x
        | throwTacticEx `path_inductionₒ mvarId m!"variable expected to induct on, got{indentExpr x}"
      let .fvar y_var ← instantiateMVars y
        | throwTacticEx `path_inductionₒ mvarId m!"variable expected to induct on, got{indentExpr y}"
      -- we revert here, and intro later, because there might be other local hypothesis which
      -- depend on `x_var`, `y_var` and `path`, which need to be reverted but not introed.
      let (_, forall_form) ← mvarId.revert #[x_var, y_var, path] (preserveOrder := true)
      forall_form.withContext do
        -- forall_form : (x y : ^α) → (p : ^(x =ₒ y)) → inner_type
        --   where inner_type = ∀ ..xs, ^e
        -- should be turned into
        -- forall_formₒ : (x y : ^α) → (p : ^(x =ₒ y)) → inner_typeₒ
        --   where inner_typeₒ = ^(∀ₒ ..xs, e)
        -- forall_form =?= λ x y p. λ ..xs. forall_formₒ x y p ..($ₒ xs)
        let (forall_formₒ_type, motive, motive_level) ← forallBoundedTelescope (← forall_form.getType) (some 3)
                                                                               fun xyp inner_type => do
          let inner_typeₒ ← forallTelescopeReducing inner_type fun xs e => do
            let mut result := e
            for var in xs.reverse do
              -- var : ^α
              -- result = ^resultₒ
              -- ⊢ result ← ^((var : α) →ₒ resultₒ)
              let (res_level, resultₒ) ← result.lift!
              let (arg_level, α) ← var.inferObjType!
              let β ← mkLambdaFVars #[var] resultₒ
              result ← mkApp2 (.const ``Pi [arg_level, res_level]) α β |>.lift
            pure result
          let motive ← mkLambdaFVars xyp (← inner_typeₒ.objType!)
          let forall_formₒ_type ← mkForallFVars xyp inner_typeₒ
          let motive_level ← inner_typeₒ.levelAsObjType!
          return (forall_formₒ_type, motive, motive_level)
        let forall_formₒ ← mkFreshExprSyntheticOpaqueMVar forall_formₒ_type
        let var_names ← forallBoundedTelescope (← forall_form.getType) (some 3) fun xyp inner_type => do
          -- body = λ ..xs. forall_formₒ x y p ..($ₒ xs)
          let #[x, y, p] := xyp | throwTacticEx `path_inductionₒ forall_form "this should not happen"
          let (body, var_names) ← forallTelescopeReducing inner_type fun xs _ => do
            let mut body := mkApp3 forall_formₒ x y p
            for arg in xs do
              body ← mkAppM ``Pi.app #[body, arg]
            let lam_body ← mkLambdaFVars xs body
            return (lam_body, ← xs.toList.mapM fun v => v.fvarId!.getUserName)
          forall_form.assign <| ← mkLambdaFVars xyp body
          return var_names
        let forall_formₒ := forall_formₒ.mvarId!
        let refl_case_motive_type ← withLocalDecl name .default (← α.lift) fun newx => do
          let motiveBody :=
            mkAppN motive #[newx, newx, mkApp2 (.const ``Id.refl [u]) α newx] |>.headBeta
          let liftedMotiveBody := motiveBody.liftWith motive_level
          mkForallFVars #[newx] liftedMotiveBody
        let refl_case_goal ← mkFreshExprSyntheticOpaqueMVar refl_case_motive_type
        let (_, refl_case_goal_with_x) ← refl_case_goal.mvarId!.intro name
        refl_case_goal_with_x.withContext do
          let elimProof := mkAppN (.const ``Id.elim [u, motive_level]) #[α, motive, refl_case_goal]
          forall_formₒ.assign elimProof
          let (refl_case_with_subst_goal, _) ← refl_case_goal_with_x.introₒ var_names
          refl_case_with_subst_goal.withContext do
            replaceMainGoal [refl_case_with_subst_goal]

  @[tactic path_induction_obj]
  def path_induction_obj_impl : Tactic
    | `(tactic| path_inductionₒ $p with refl $x) => do
      let .ident _ _ name _ := x.raw
        | throwTacticEx `path_inductionₒ (← getMainGoal) m!"expected variable, got {x}"
      path_induction (← getFVarId p.raw) name
    | `(tactic| path_inductionₒ $p) => do
      path_induction (← getFVarId p.raw) `x
    | _ => throwUnsupportedSyntax
end Tltt.Hott.Tactics.PathInduction
