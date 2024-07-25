import Tltt.Tactics.Base
import Tltt.Tactics.Matching
import Tltt.Tactics.Builder
import Tltt.Tactics.Rfl

open Lean (
  BinderInfo
  Expr
  FVarId
  LocalDecl
  MVarId
  Syntax
  indentExpr
  instantiateMVars
  mkAppN
)
open Lean.Elab.Tactic (
  Tactic
  TacticM
  expandOptLocation
  getMainGoal
  getMainTarget
  replaceMainGoal
  elabTerm
  withLocation
  withMainContext
  withRWRulesSeq
)
open Lean.Elab.Term (withSynthesize)
open Lean.Meta (
  AssertAfterResult
  MetaM
  Occurrences
  RewriteResult
  forallMetaTelescopeReducing
  getMVarsNoDelayed
  inferType
  isTypeCorrect
  kabstract
  mkFreshExprSyntheticOpaqueMVar
  postprocessAppMVars
  throwTacticEx
)
open Lean.Parser.Tactic (rwRuleSeq location)

namespace Tltt.Hott.Tactic.Rewrite
  ---  Object-level rewrite: rewriteₒ
  def rewriteObj (mvarId : MVarId) (e : Expr) (heq : Expr) (symm : Bool := false)
                 (occs : Occurrences := .all) : MetaM RewriteResult :=
    mvarId.withContext do
      mvarId.checkNotAssigned `rewriteₒ
      let heqType ← inferType heq
      let heqObjType ← heqType.objType!
      let (newMVars, binderInfos, heqType) ← forallMetaTelescopeReducing heqType
      let heq := mkAppN heq newMVars
      match ← heqObjType.id? with
      | none => throwTacticEx `rewriteₒ mvarId m!"object equality expected {indentExpr heqType}"
      | some (u, α, lhs, rhs) => do
        let (heq, heqType, lhs, rhs) ← do
          if symm then
            let heq ← mkIdSymm heq
            let heqType ← mkId u α rhs lhs
            pure (heq, heqType, rhs, lhs)
          else
            pure (heq, heqType, lhs, rhs)
        let lhs ← instantiateMVars lhs
        let rhs ← instantiateMVars rhs
        if lhs.getAppFn.isMVar then
          throwTacticEx `rewriteₒ mvarId m!"pattern is a metavariable{indentExpr lhs}\nfrom equation{indentExpr heqType}"
        let e ← instantiateMVars e
        let some (e_level, e_obj) ← e.lift?
          | throwTacticEx `rewriteₒ mvarId m!"the goal is not an object-level type"
        let e_abstₒ ← kabstract e_obj lhs occs
        unless e_abstₒ.hasLooseBVars do
          throwTacticEx `rewriteₒ mvarId m!"did not find instance of the pattern in the target expresion{indentExpr lhs}"
        let eNewₒ := e_abstₒ.instantiate1 rhs
        let eNewₒ ← instantiateMVars eNewₒ
        let e_objeq_eabst ← mkId (.succ e_level) (.const ``U [e_level]) e_obj e_abstₒ
        let liftedα ← α.lift
        let motive := Expr.lam `_a liftedα e_objeq_eabst BinderInfo.default
        unless ← isTypeCorrect motive do
          throwTacticEx `rewriteₒ mvarId "motive is not type correct..."
        let eqRefl ← mkIdRefl e_obj
        let eqPrf ← mkIdSubst motive eqRefl heq
        postprocessAppMVars `rewriteₒ mvarId newMVars binderInfos
        let newMVarIds ← newMVars.map Expr.mvarId! |>.filterM (not <$> ·.isAssigned)
        let otherMVarIds ← getMVarsNoDelayed eqPrf
        let otherMVarIds := otherMVarIds.filter (!newMVarIds.contains ·)
        let newMVarIds := newMVarIds ++ otherMVarIds
        pure { eNew := ← eNewₒ.lift, eqProof := eqPrf, mvarIds := newMVarIds.toList }

  def replaceLocalDeclObj (mvarId : MVarId) (fvarId : FVarId) (typeNew : Expr)
                          (eqProof : Expr) : MetaM AssertAfterResult :=
    mvarId.withContext do
      let localDecl ← fvarId.getDecl
      let target ← fvarId.getType
      let some (u, targetₒ) ← target.lift?
        | throwTacticEx `rewriteₒ mvarId m!"target {indentExpr target}\nis not an object-level type"
      let targetNewₒ ← typeNew.objType!
      let typeNewPr := mkAppN (.const ``Id.mp [u]) #[targetₒ, targetNewₒ, eqProof, .fvar fvarId]
      let (_, localDecl') ← findMaxFVar typeNew |>.run localDecl
      let result ← mvarId.assertAfter localDecl'.fvarId localDecl.userName typeNew typeNewPr
      (do let mvarIdNew ← result.mvarId.clear fvarId
          pure { result with mvarId := mvarIdNew })
      <|> pure result
  where
    findMaxFVar (e : Expr) : StateRefT LocalDecl MetaM Unit :=
      e.forEach' fun e => do
        if e.isFVar then
          let localDecl' ← e.fvarId!.getDecl
          modify fun localDecl => if localDecl'.index > localDecl.index then localDecl' else localDecl
          return false
        else
          return e.hasFVar

  def replaceTargetId (mvarId : MVarId) (targetNew : Expr) (eqProof : Expr) : MetaM MVarId :=
    mvarId.withContext do
      mvarId.checkNotAssigned `replaceTarget
      let tag ← mvarId.getTag
      let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew tag
      let target ← mvarId.getType
      let some (u, targetₒ) ← target.lift?
        | throwTacticEx `rewriteₒ mvarId m!"target {indentExpr target}\nis not an object-level type"
      let targetNewₒ ← targetNew.objType!
      let eq ← mkId (.succ u) (.const ``U [u]) targetₒ targetNewₒ
      let newProof ← mkExpectedObjTypeHint eqProof eq
      let val := mkAppN (.const ``Id.mpr [u]) #[targetₒ, targetNewₒ, newProof, mvarNew]
      mvarId.assign val
      return mvarNew.mvarId!

  def rewriteTarget (stx : Syntax) (symm : Bool) : TacticM Unit := do
    withSynthesize <| withMainContext do
      let e ← elabTerm stx none true
      let r ← rewriteObj (← getMainGoal) (← getMainTarget) e symm
      let mvarId' ← replaceTargetId (← getMainGoal) r.eNew r.eqProof
      replaceMainGoal (mvarId' :: r.mvarIds)

  def rewriteLocalDecl (stx : Syntax) (symm : Bool) (fvarId : FVarId) : TacticM Unit := do
    withSynthesize <| withMainContext do
      let e ← elabTerm stx none true
      let localDecl ← fvarId.getDecl
      let rwResult ← rewriteObj (← getMainGoal) localDecl.type e symm
      let replaceResult ← replaceLocalDeclObj (← getMainGoal) fvarId rwResult.eNew rwResult.eqProof
      replaceMainGoal (replaceResult.mvarId :: rwResult.mvarIds)

  syntax (name := rewriteSeqObj) "rewriteₒ" rwRuleSeq (location)? : tactic

  @[tactic rewriteSeqObj]
  def rewriteSeqObjImpl : Tactic := fun stx => do
    let loc := expandOptLocation stx[2]
    withRWRulesSeq stx[0] stx[1] fun symm term => do
      withLocation loc
        (rewriteLocalDecl term symm ·)
        (rewriteTarget term symm)
        (throwTacticEx `rewriteₒ · "did not find instance of the pattern in the current goal")

  macro "rwₒ " s:rwRuleSeq l:(location)? : tactic =>
    `(tactic| (rewriteₒ $s $(l)?; try (with_reducible rflₒ)))
end Tltt.Hott.Tactic.Rewrite
