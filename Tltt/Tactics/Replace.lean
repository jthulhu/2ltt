import Tltt.ObjLang
import Tltt.Tactics.Matching

open Lean (
  Expr
  FVarId
  indentExpr
)
open Lean.Elab.Tactic (
  Tactic
  TacticM
  elabTerm
  expandOptLocation
  getMainGoal
  replaceMainGoal
  withLocation
  withMainContext
)
open Lean.Elab.Term (
  withSynthesize
)
open Lean.Meta (
  getLocalInstances
  isDefEq
  kabstract
  mkFreshExprSyntheticOpaqueMVar
  throwTacticEx
  withLCtx
)
open Lean.MonadLCtx (getLCtx)
open Lean.Parser.Tactic (location)

namespace Tltt.Hott.Tactic.Replace
  /-- `replace a with b at l` replaces `a` with `b` if they are definitionally equal, in `l`,
      which can be either a local hypothesis or `⊢` to signify the goal. -/
  syntax (name := replace) "replace " term " with " term (location)? : tactic

  def replaceLocalDecl (pattern : Expr) (replacement : Expr) (fvarId : FVarId) : TacticM Unit := do
    withSynthesize <| withMainContext do
      let mvarId ← getMainGoal
      let localDecl ← fvarId.getDecl
      let target_type := localDecl.type
      let target_type_hole ← kabstract target_type pattern
      -- check that we found an occurrence of the pattern in the target type
      unless target_type_hole.hasLooseBVars do
        throwTacticEx `replace mvarId
          m!"did not find instance of pattern{indentExpr pattern}\nin the type of the local hypothesis {← fvarId.getUserName}{indentExpr target_type}"
      let new_target_type := target_type_hole.instantiate1 replacement
      -- check that the new type does not depend on "future" local hypothesis
      new_target_type.forEach' fun e => do
        if e.isFVar then
          let localDecl' ← e.fvarId!.getDecl
          unless localDecl'.index < localDecl.index do
            throwTacticEx `replace mvarId m!"the replacement contains a reference to the local hypothesis {localDecl'.userName}, which is defined after the local hypothesis we are replacing into"
          return false
        else
          return e.hasFVar
      let lctx := (← getLCtx).modifyLocalDecl fvarId fun
        | .ldecl index fvarId name _ value non_dep kind =>
          .ldecl index fvarId name new_target_type value non_dep kind
        | .cdecl index fvarId name _ bi kind =>
          .cdecl index fvarId name new_target_type bi kind
      withLCtx lctx (← getLocalInstances) do
        let new_goal ← mkFreshExprSyntheticOpaqueMVar (← mvarId.getType)
        mvarId.assign new_goal
        replaceMainGoal [new_goal.mvarId!]

  def replaceTarget (pattern : Expr) (replacement : Expr) : TacticM Unit := do
    withSynthesize <| withMainContext do
      let mvarId ← getMainGoal
      let goal_type ← mvarId.getType
      let goal_type_hole ← kabstract pattern goal_type
      unless goal_type_hole.hasLooseBVars do
        throwTacticEx `replace mvarId
          m!"did not find instance of the pattern{indentExpr pattern}\nin the target expression{indentExpr goal_type}"
      let new_goal_type := goal_type_hole.instantiate1 replacement
      let new_goal ← mkFreshExprSyntheticOpaqueMVar new_goal_type
      mvarId.assign new_goal
      replaceMainGoal [new_goal.mvarId!]

  @[tactic replace]
  def replace_impl : Tactic := fun stx => do
    let loc := expandOptLocation stx[4]
    withMainContext do
      let pattern ← elabTerm stx[1] none
      let replacement ← elabTerm stx[3] none
      unless ← isDefEq pattern replacement do
        throwTacticEx `replace (← getMainGoal)
          "the term to be replaced and its replacements must be definitionally equal"
      withLocation loc
        (replaceLocalDecl pattern replacement ·)
        (replaceTarget pattern replacement)
        (throwTacticEx `replace · "did not find instance of the pattern in the current goal")
end Tltt.Hott.Tactic.Replace
