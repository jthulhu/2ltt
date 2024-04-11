import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Location
import Lean.Elab.Tactic.Rewrite

import Tltt.ObjLang

open Lean.Parser.Tactic (rwRuleSeq location)
open Lean.Elab.Term (withSynthesize)
open Lean.Elab.Tactic (
  Tactic
  TacticM
  elabTerm
  expandOptLocation
  getFVarId
  getGoals
  getMainGoal
  getMainTarget
  replaceMainGoal
  withLocation
  withMainContext
  withRWRulesSeq
)
open Lean.Elab (throwUnsupportedSyntax)
open Lean.Meta (
  AssertAfterResult
  MetaM
  RewriteResult
  forallBoundedTelescope
  forallMetaTelescopeReducing
  forallTelescopeReducing
  getLevel
  getMVarsNoDelayed
  inferType
  isDefEq
  isTypeCorrect
  kabstract
  matchHelper?
  mkAppM
  mkForallFVars
  mkFreshExprMVar
  mkFreshExprSyntheticOpaqueMVar
  mkFreshLevelMVar
  mkLambdaFVars
  postprocessAppMVars
  throwTacticEx
  whnfD
  whnfI
  withLocalDecl
)
open Lean (
  BinderInfo
  Expr
  FVarId
  Level
  LocalDecl
  MVarId
  Name
  Occurrences
  Syntax
  indentExpr
  instantiateMVars
  mkApp2
  mkApp3
  mkApp4
  mkAppN
  mkFreshFVarId
  mkFreshMVarId
)

open Hott

set_option autoImplicit false

namespace Hott.Tactic

/-- If given `lift.{u} α`, returns `(u, α)`. -/
def _root_.Lean.Expr.lift? (e : Expr) : MetaM (Option (Level × Expr)) := do
  let u ← mkFreshLevelMVar
  let type ← mkFreshExprMVar (Expr.const ``Hott.liftedU [u])
  let lifted := Expr.app (.const ``Hott.lift [u]) type
  if ← isDefEq e lifted then
    return some (u, type)
  else
    return none

def _root_.Lean.Expr.lift! (e : Expr) : MetaM (Level × Expr) := do
  let some (u, t) ← e.lift? | throwError "{indentExpr e} is not an object-level type"
  return (u, t)

/-- Lifts `α` into `^α`. -/
@[inline]
def _root_.Lean.Expr.liftWith (e : Expr) (u : Level) : Expr :=
  .app (.const ``Hott.lift [u]) e

/-- If `e` is a lifted type `^α`, returns `α`. -/
@[inline]
def _root_.Lean.Expr.objType? (e : Expr) : Option Expr :=
  e.app1? ``Hott.lift

/-- Given `^α`, returns `α`. -/
@[inline]
def _root_.Lean.Expr.objType! (e : Expr) : MetaM Expr := do
  let some (_, t) ← e.lift? | throwError "{indentExpr e} is not an object-level type"
  return t


/-- Given `x : lift.{u} α`, returns (u, α). -/
@[inline]
def inferObjType (e : Expr) : MetaM (Level × Expr) := do
  let t ← inferType e
  let some result ← t.lift?
    | throwError "expression{indentExpr e}\nhas type{indentExpr t}\nwhich is not an object-level type"
  return result

/-- Given `Id.{u} {α} x y`, returns `(u, α, x, y)`. -/
@[inline]
def _root_.Lean.Expr.id? (e : Expr) : MetaM (Option (Level × Expr × Expr × Expr)) := do
  let u ← mkFreshLevelMVar
  let α ← mkFreshExprMVar (Expr.const ``liftedU [u])
  let x ← mkFreshExprMVar (α.liftWith u)
  let y ← mkFreshExprMVar (α.liftWith u)
  let pattern := mkAppN (.const ``Hott.Id [u]) #[α, x, y]
  if ← isDefEq e pattern then
    return some (u, α, x, y)
  else
    return none

/-- Given `x : ^α` where `α : ^U.{u}`, returns `u` -/
def getObjLevel (e : Expr) : MetaM Level := do
  let t ← inferType e
  let u ← mkFreshLevelMVar
  let pattern := .const ``liftedU [u]
  if ← isDefEq t pattern then
    return u
  else
    throwError "expression{indentExpr e}\nhas type{indentExpr t}\nwhich is not an object-level type"
    

/-- Lift `α` into `^α`. -/
@[inline]
def _root_.Lean.Expr.lift (e : Expr) : MetaM Expr := do
  let u ← getObjLevel e
  return e.liftWith u

/-- Given `h : ^(a =ₒ b)`, returns a proof of `b =ₒ a`. -/
def mkIdSymm (h : Expr) : MetaM Expr := do
  if h.isAppOf ``Id.refl then
    return h
  else
    let hType ← inferType h
    let hTypeₒ ← hType.objType!
    match ← hTypeₒ.id? with
      | some (u, α, a, b) =>
        return mkApp4 (.const ``Id.symm [u]) α a b h
      | none =>
        throwError "AppBuilder for '{``Id.symm}, object equality proof expected{indentExpr h}\nhas type{indentExpr hType}"

/-- Returns `a =ₒ b`. -/
def mkId (u : Level) (α a b : Expr) : MetaM Expr := do
  return mkApp3 (.const ``Id [u]) α a b

/-- Returns a proof of `a =ₒ a` if `a` is an object-level term. -/
def mkIdRefl (a : Expr) : MetaM Expr := do
  let (u, aObjType) ← inferObjType a
  let result := mkApp2 (.const ``Id.refl [u]) aObjType a
  return result

def mkIdSubst (motive h idh : Expr) : MetaM Expr := do
  if (← whnfD idh).isAppOf ``Id.refl then
    return h
  let (_, idhObjType) ← inferObjType idh
  match ← idhObjType.id? with
  | none => throwError "AppBuilder for '{``Id.subst}, object equality proof expected{indentExpr idh}\nhas type{indentExpr idhObjType}"
  | some (u₁, α, lhs, rhs) =>
    let motiveType ← whnfD (← inferType motive)
    match motiveType with
    | .forallE _ _ motiveTargetType _ =>
      let some (_, U) ← motiveTargetType.lift?
        | throwError "Motive target type{indentExpr motiveTargetType}\nis not a object-level universe type"
      let u₂ ← mkFreshLevelMVar
      let pattern := .const ``U [u₂]
      if !(← isDefEq U pattern) then
        throwError "Motive target type{indentExpr motiveTargetType}\nis not a object-level universe type"
      return mkAppN (.const ``Id.subst [u₁, u₂]) #[α, motive, lhs, rhs, idh, h]
    | _ => throwError "AppBuilder for '{``Id.subst}, invalid motive{indentExpr motive}"
    
---  Object-level rewrite: rewriteₒ
def rewriteObj (mvarId : MVarId) (e : Expr) (heq : Expr) (symm : Bool := false)
               (occs : Occurrences := .all) : MetaM RewriteResult :=
  mvarId.withContext do
    mvarId.checkNotAssigned `rewriteₒ
    let heqType ← instantiateMVars (← inferType heq)
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

def mkExpectedObjTypeHint (e : Expr) (expectedObjType : Expr) : MetaM Expr := do
  let u ← getObjLevel expectedObjType
  return mkAppN (.const ``id [.succ u]) #[expectedObjType.liftWith u, e]

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

namespace PathInduction
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
      let (_, newGoal) ← mvarId.revert #[x_var, y_var, path] (preserveOrder := true)
      newGoal.withContext do
        let (motive, goal_level, newGoal) ← forallBoundedTelescope (← newGoal.getType) (some 3) fun args e => do
          -- turn goals of the form (x : ^α) → ^β into ^((x : α) →ₒ β)
          let (e, goal) ← forallTelescopeReducing e fun args e => do
            let mut result := e
            let mut goal := newGoal
            for arg in args.reverse do
              -- result =?= ^β
              -- arg : ^α
              -- goal : (arg : ^α) → result
              let (u₂, β) ← result.lift!
              let body ← mkLambdaFVars #[arg] β
              let (u₁, α) ← inferObjType arg
              result ← mkAppN (.const ``Pi [u₁, u₂]) #[α, body] |>.lift
              -- goal' : ^((arg : α) →ₒ β)
              let goal' ← mkFreshExprSyntheticOpaqueMVar result
              goal.assign (mkAppN (.const ``Pi.app [u₁, u₂]) #[α, body, goal'])
              goal := goal'.mvarId!
            pure (result, goal)
          let some (goal_level, motiveBody) ← e.lift?
            | throwTacticEx `path_inductionₒ newGoal m!"the goal{indentExpr e}\nis not an object-level type"
          return (← mkLambdaFVars args motiveBody, goal_level, goal)
        let (goal, switcharoo) ← withLocalDecl name .default (← α.lift) fun newx => do
          let motiveBody ←
            whnfI (mkAppN motive #[newx, newx, mkApp2 (.const ``Id.refl [u]) α newx])
          let liftedMotiveBody := motiveBody.liftWith goal_level
          let body ← mkFreshExprSyntheticOpaqueMVar liftedMotiveBody
          return (body, ← mkLambdaFVars #[newx] body)
        let elimProof := mkAppN (.const ``Id.elim [u, goal_level]) #[α, motive, switcharoo]
        replaceMainGoal [goal.mvarId!]
        newGoal.assign elimProof

  @[tactic path_induction_obj]
  def path_induction_obj_impl : Tactic
    | `(tactic| path_inductionₒ $p with refl $x) => do
      let .ident _ _ name _ := x.raw
        | throwTacticEx `path_inductionₒ (← getMainGoal) m!"expected variable, got {x}"
      path_induction (← getFVarId p.raw) name
    | `(tactic| path_inductionₒ $p) => do
      path_induction (← getFVarId p.raw) `x
    | _ => throwUnsupportedSyntax
end PathInduction

macro "rflₒ" : tactic => `(tactic| apply Id.refl)

macro "rwₒ" s:rwRuleSeq l:(location)? : tactic =>
  `(tactic| (rewriteₒ $s $(l)?; try (with_reducible rflₒ)))

example {α β : U} (h : β =ₒ α) (x : α) : β := by
  rewriteₒ [h]
  assumption

example (x y z : Natₒ) (h₁ : x =ₒ y) (h₂ : y =ₒ z) : x =ₒ z := by
  rewriteₒ [h₁]
  assumption

example (x y z : Natₒ) (h₁ : x =ₒ y) (h₂ : y =ₒ z) : x =ₒ z := by
  rewriteₒ [h₂] at h₁
  assumption

example (x y z : Natₒ) (h₁ : x =ₒ y) (h₂ : y =ₒ z) : x =ₒ z := by
  rewriteₒ [h₁, h₂]
  rflₒ

example (x y z : Natₒ) (h₁ : x =ₒ y) (h₂ : y =ₒ z) : x =ₒ z := by
  rwₒ [h₁, h₂]

example (x y : Natₒ) (p : x =ₒ y) : y =ₒ x := by
  path_inductionₒ p
  rflₒ

example {α β : U} (h : α =ₒ β) (x : α) : β := by
  rewriteₒ [← h]
  assumption

end Hott.Tactic
