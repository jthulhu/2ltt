import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Location
import Lean.Elab.Tactic.Rewrite

import Tltt.ObjLang
import Tltt.Hott

open Lean.Parser.Tactic (rwRuleSeq location)
open Lean.Elab.Term (withSynthesize)
open Lean.Elab.Tactic (
  Tactic
  TacticM
  elabTerm
  expandOptLocation
  getMainGoal
  getMainTarget
  replaceMainGoal
  withLocation
  withMainContext
  withRWRulesSeq
)
open Lean.Meta (
  AssertAfterResult
  MetaM
  RewriteResult
  forallMetaTelescopeReducing
  getLevel
  getMVarsNoDelayed
  inferType
  isDefEq
  isTypeCorrect
  kabstract
  matchHelper?
  mkFreshLevelMVar
  mkFreshExprMVar
  postprocessAppMVars
  throwTacticEx
  whnfD
)
open Lean (
  BinderInfo
  Expr
  FVarId
  Level
  MVarId
  Occurrences
  Syntax
  indentExpr
  instantiateMVars
  mkApp
  mkApp2
  mkApp3
  mkApp4
  mkAppN
  mkConst
  mkFreshMVarId
)

open Hott

set_option autoImplicit false

namespace Hott.Tactic

/-- If given `lift.{u} α`, returns `(u, α)` -/
def _root_.Lean.Expr.lift? (e : Expr) : MetaM (Option (Level × Expr)) := do
  let type ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkConstWithFreshMVarLevels ``Hott.liftedU)
  let u ← Lean.Meta.mkFreshLevelMVar
  let lifted := Expr.app (.const ``Hott.lift [u]) type
  if ← isDefEq e lifted then
    return some (u, type)
  else
    return none


/--
Lift `α` into `^α`.
-/
@[inline]
def _root_.Lean.Expr.liftWith (e : Expr) (u : Level) : Expr :=
  .app (.const ``Hott.lift [u]) e

/--
If `e` is a lifted type `^α`, returns `α`.
-/
@[inline]
def _root_.Lean.Expr.objType? (e : Expr) : Option Expr :=
  e.app1? ``Hott.lift

@[inline]
def _root_.Lean.Expr.objType (e : Expr) : MetaM Expr := do
  let some t := e.objType? | throwError "{indentExpr e} is not an object-level type"
  return t

    
@[inline]
def inferObjType (e : Expr) : MetaM (Level × Expr) := do
  let t ← inferType e
  match ← t.lift? with
  | some x => return x
  | none => throwError "expression{indentExpr e}\nhas type{indentExpr t}\nwhich is not an object-level type"

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

def getObjLevel (e : Expr) : MetaM Level := do
  let t ← inferType e
  let u ← mkFreshLevelMVar
  let pattern := .const ``liftedU [u]
  if ← isDefEq t pattern then
    return u
  else
    throwError "expression{indentExpr e}\nhas type{indentExpr t}\nwhich is not an object-level type"
    

/--
Lift `α` into `^α`.
-/
@[inline]
def _root_.Lean.Expr.lift (e : Expr) : MetaM Expr := do
  let u ← getObjLevel e
  return .app (.const ``Hott.lift [u]) e

universe u in
example : lift.{u+1} U.{u} = liftedU.{u} := by rfl

---  Object-level rewrite: rewriteₒ
def replaceLocalDeclObjCore (mvarId : MVarId) (fvarId : FVarId) (typeNew : Expr)
                            (eqProof : Expr) : MetaM AssertAfterResult :=
  -- mvarId.withContext do
  --   let localDecl ← fvarId.getDecl
  --   let typeNewPr ← mkIdMp eqProof (mkFVar fvarId)
  --   let (_, localDecl') ← findMaxFVar typeNew |>.run localDecl
  --   let result ← mvarId.assertAfter localDecl'.fvarId localDecl.userName typeNew typeNewPr
  --   (do let mvarIdNew ← result.mvarId.clear fvarId
  --       pure { result with mvarId := mvarIdNew })
  --   <|> pure result
  sorry

def replaceLocalDeclObj (mvarId : MVarId) (fvarId : FVarId) (typeNew : Expr) (eqProof : Expr)
                        : MetaM AssertAfterResult :=
  replaceLocalDeclObjCore mvarId fvarId typeNew eqProof

/-- Given `h : ^(a =ₒ b)`, returns a proof of `b =ₒ a`. -/
def mkIdSymm (h : Expr) : MetaM Expr := do
  if h.isAppOf ``Id.refl then
    return h
  else
    let hType ← whnfD (← inferType h)
    match ← hType.id? with
      | some (u, α, a, b) =>
        return mkApp4 (mkConst ``Id.symm [u]) α a b h
      | none =>
        throwError "AppBuilder for '{``Id.symm}, object equality proof expected{indentExpr h}\nhas type{indentExpr hType}"

def mkId (u : Level) (α a b : Expr) : MetaM Expr := do
  return mkApp3 (mkConst ``Id [u]) α a b

/-- Returns a proof of `a =ₒ a` if `a` is an object-level term. -/
def mkIdRefl (a : Expr) : MetaM Expr := do
  let (u, aObjType) ← inferObjType a
  return mkApp2 (mkConst ``Id.refl [u]) aObjType a

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
      let some (u₂, _) ← motiveTargetType.lift?
        | throwError "Motive target type{indentExpr motiveTargetType}\nis not an object-level type"
      return mkAppN (mkConst ``Id.subst [u₁, u₂]) #[α, motive, lhs, rhs, idh, h]
    | _ => throwError "AppBuilder for '{``Id.subst}, invalid motive{indentExpr motive}"

def rewriteObj (mvarId : MVarId) (e : Expr) (heq : Expr) (symm : Bool := false)
               (occs : Occurrences := .all) : MetaM RewriteResult :=
  mvarId.withContext do
    mvarId.checkNotAssigned `rewriteₒ
    let heqType ← instantiateMVars (← inferType heq)
    let heqObjType ← heqType.objType
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
      let eAbst ← kabstract e lhs occs
      unless eAbst.hasLooseBVars do
        throwTacticEx `rewriteₒ mvarId m!"did not find instance of the pattern in the target expresion{indentExpr lhs}"
      let eNew := eAbst.instantiate1 rhs
      let eNew ← instantiateMVars eNew
      let some (e_level, e_obj) ← e.lift?
        | throwTacticEx `rewriteₒ mvarId m!"the goal is not an object-level type{indentExpr e}"
      let some e_abst_obj := eAbst.objType?
        | throwTacticEx `rewriteₒ mvarId m!"the inferred context is not an object-level type"
      let e_objeq_eabst ← mkId (.succ e_level) (.const ``U [e_level]) e_obj e_abst_obj
      let liftedα ← α.lift
      let motive := Expr.lam `_a liftedα e_objeq_eabst BinderInfo.default
      Lean.Meta.check motive
      unless ← isTypeCorrect motive do
        throwTacticEx `rewriteₒ mvarId "motive is not type correct..."
      let eqRefl ← mkIdRefl e_obj
      let eqPrf ← mkIdSubst motive eqRefl heq
      postprocessAppMVars `rewriteₒ mvarId newMVars binderInfos
      let newMVarIds ← newMVars.map Expr.mvarId! |>.filterM (not <$> ·.isAssigned)
      let otherMVarIds ← getMVarsNoDelayed eqPrf
      let otherMVarIds := otherMVarIds.filter (!newMVarIds.contains ·)
      let newMVarIds := newMVarIds ++ otherMVarIds
      pure { eNew := eNew, eqProof := eqPrf, mvarIds := newMVarIds.toList }

def mkExpectedObjTypeHint (e : Expr) (expectedObjType : Expr) : MetaM Expr := do
  let u ← getObjLevel expectedObjType
  return mkAppN (.const ``Arrow.id [u]) #[expectedObjType, e]

def replaceTargetId (mvarId : MVarId) (targetNew : Expr) (eqProof : Expr) : MetaM MVarId :=
  mvarId.withContext do
    mvarId.checkNotAssigned `replaceTarget
    let tag ← mvarId.getTag
    let mvarNew ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar targetNew tag
    let target ← mvarId.getType
    let some (u, targetObjType) ← target.lift?
      | throwTacticEx `rewriteₒ mvarId m!"target {indentExpr target}\nis not an object-level type"
    let eq ← mkId u targetObjType target targetNew
    let newProof ← mkExpectedObjTypeHint eqProof eq
    let val := mkAppN (Lean.mkConst ``Id.mpr [u]) #[target, targetNew, newProof, mvarNew]
    mvarId.assign val
    return mvarNew.mvarId!

def rewriteTarget (stx : Syntax) (symm : Bool) : TacticM Unit := do
  withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let r ← rewriteObj (← getMainGoal) (← getMainTarget) e symm
    let mvarId' ← replaceTargetId (← getMainGoal) r.eNew r.eqProof
    replaceMainGoal (mvarId' :: r.mvarIds)

def rewriteLocalDecl (stx : Syntax) (symm : Bool) (fvarId : FVarId) : TacticM Unit := do
  -- withSynthesize <| withMainContext do
  --   let e ← elabTerm stx none true
  --   let localDecl ← fvarId.getDecl
  --   let rwResult ← rewriteObj (← getMainGoal) localDecl.type e symm
  --   let replaceResult ← replaceLocalDeclObj (← getMainGoal) fvarId rwResult.eNew rwResult.eqProof
  --   replaceMainGoal (replaceResult.mvarId :: rwResult.mvarIds)
  pure ()

syntax (name := rewriteSeqObj) "rewriteₒ" rwRuleSeq (location)? : tactic

@[tactic rewriteSeqObj]
def rewriteSeqObjImpl : Tactic := fun stx => do
  let loc := expandOptLocation stx[2]
  withRWRulesSeq stx[0] stx[1] fun symm term => do
    withLocation loc
      (rewriteLocalDecl term symm ·)
      (rewriteTarget term symm)
      (throwTacticEx `rewriteₒ · "did not find instance of the pattern in the current goal")



syntax (name := checkObj) "checkₒ" term : tactic

@[tactic checkObj]
def checkImpl : Tactic := fun stx => do
  let e ← elabTerm stx[1] none true
  let eType ← instantiateMVars (← inferType e)
  match eType.objType? with
  | none =>
    let mvarId ← getMainGoal
    throwTacticEx `checkₒ mvarId "This term is not an object-level term"
  | some t =>
    Lean.logInfo s!"Term has object-level type {t}."
    
-- set_option pp.universes true in
-- set_option trace.Meta.isDefEq true in
example {α β : U.{0}} (h : β =ₒ α) (x : α) : β := by
  rewriteₒ [h]
  assumption
  -- exact x

end Hott.Tactic
