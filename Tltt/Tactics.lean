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
def inferObjType (e : Expr) : MetaM Expr := do
  let t ← inferType e
  let ot ← t.objType
  return ot

/-- If given `lift.{u} α`, returns `(u, α)` -/
def _root_.Lean.Expr.lift? (e : Expr) : MetaM (Option (Level × Expr)) := do
  Lean.Meta.withNewMCtxDepth do
    let type ← Lean.Meta.mkFreshExprMVar none
    let u ← Lean.Meta.mkFreshLevelMVar
    let lifted := Expr.app (.const ``Hott.lift [u]) type
    if ← isDefEq e lifted then
      return some (u, type)
    else
      return none
      
#eval (Expr.const ``Hott.liftedU [Level.zero]).lift?

@[inline]
def _root_.Lean.Expr.id? (e : Expr) : Option (Expr × Expr × Expr) :=
  e.app3? ``Id

def getObjLevel (e : Expr) : MetaM Level := do
  let t ← inferType e
  Lean.logInfo s!"getObjLevel of {e} : {t}"
  match ← t.lift? with
  | some (u, _) =>
    Lean.logInfo "gotcha!"
    return u
  | none => throwError "expression{indentExpr e}\nhas type{indentExpr t}\nwhich is not an object-level type"

/--
Lift `α` into `^α`.
-/
@[inline]
def _root_.Lean.Expr.lift (e : Expr) : MetaM Expr := do
  let u ← getObjLevel e
  return .app (.const ``Hott.lift [u]) e


---  Object-level rewrite: rewriteₒ
def replaceLocalDeclObjCore (mvarId : MVarId) (fvarId : FVarId) (typeNew : Expr)
                            (eqProof : Expr) : MetaM AssertAfterResult :=
  mvarId.withContext do
    let localDecl ← fvarId.getDecl
    let typeNewPr ← mkIdMp eqProof (mkFVar fvarId)
    let (_, localDecl') ← findMaxFVar typeNew |>.run localDecl
    let result ← mvarId.assertAfter localDecl'.fvarId localDecl.userName typeNew typeNewPr
    (do let mvarIdNew ← result.mvarId.clear fvarId
        pure { result with mvarId := mvarIdNew })
    <|> pure result

def replaceLocalDeclObj (mvarId : MVarId) (fvarId : FVarId) (typeNew : Expr) (eqProof : Expr)
                        : MetaM AssertAfterResult :=
  replaceLocalDeclObjCore mvarId fvarId typeNew eqProof

/-- Matches `e` with `lhs =ₒ rhs : ^α` and returns `(α, lhs, rhs)` -/
def matchId? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) :=
  matchHelper? e fun e => return e.app3? ``Id

/-- Given `h : ^(a =ₒ b)`, returns a proof of `b =ₒ a`. -/
def mkIdSymm (h : Expr) : MetaM Expr := do
  if h.isAppOf ``Id.refl then
    return h
  else
    let hType ← whnfD (← inferType h)
    match hType.id? with
      | some (α, a, b) =>
        let u ← getObjLevel α
        return mkApp4 (mkConst ``Id.symm [u]) α a b h
      | none =>
        throwError "AppBuilder for '{``Id.symm}, object equality proof expected{indentExpr h}\nhas type{indentExpr hType}"

def mkId (α a b : Expr) : MetaM Expr := do
  let u ← getObjLevel α
  return mkApp3 (mkConst ``Id [u]) α a b

/-- Returns a proof of `a =ₒ a` if `a` is an object-level term. -/
def mkIdRefl (a : Expr) : MetaM Expr := do
  let aObjType ← inferObjType a
  let u ← getObjLevel aObjType
  return mkApp2 (mkConst ``Id.refl [u]) aObjType a

def mkIdSubst (motive h idh : Expr) : MetaM Expr := do
  Lean.logInfo m!"motive = {motive}\nh = {h}\nidh = {idh}\nidh ≡ {← whnfD idh}"
  if (← whnfD idh).isAppOf ``Id.refl then
    return h
  let idhType ← whnfD (← inferType idh)
  Lean.logInfo m!"idhType = {idhType}"
  match (← idhType.objType).id? with
  | none => throwError "AppBuilder for '{``Id.subst}, object equality proof expected{indentExpr idh}\nhas type{indentExpr idhType}"
  | some (α, lhs, rhs) =>
    let u₁ ← getLevel α
    let motiveType ← whnfD (← inferType motive)
    match motiveType with
    | .forallE _ _ (.sort u₂) _ =>
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
    match ← matchId? heqObjType with
    | none => throwTacticEx `rewriteₒ mvarId m!"object equality expected {indentExpr heqType}"
    | some (α, lhs, rhs) => do
      let (heq, heqType, lhs, rhs) ← do
        if symm then
          let heq ← mkIdSymm heq
          let heqType ← mkId α rhs lhs
          pure (heq, heqType, rhs, lhs)
        else
          pure (heq, heqType, lhs, rhs)
      if lhs.getAppFn.isMVar then
        throwTacticEx `rewriteₒ mvarId m!"pattern is a metavariable{indentExpr lhs}\nfrom equation{indentExpr heqType}"
      let e ← instantiateMVars e
      let eAbst ← kabstract e lhs occs
      unless eAbst.hasLooseBVars do
        throwTacticEx `rewriteₒ mvarId m!"did not find instance of the pattern in the target expresion{indentExpr lhs}"
      let eNew := eAbst.instantiate1 rhs
      let eNew ← instantiateMVars eNew
      Lean.logInfo "bonjour"
      let some e_obj := e.objType?
        | throwTacticEx `rewriteₒ mvarId m!"the goal is not an object-level type{indentExpr e}"
      let some e_abst_obj := eAbst.objType?
        | throwTacticEx `rewriteₒ mvarId m!"the inferred context is not an object-level type"
      let e_objeq_eabst ← do
        let level ← getObjLevel e_obj
        mkId (.const ``U [level]) e_obj e_abst_obj
      let motive := Lean.mkLambda `_a BinderInfo.default (← α.lift) e_objeq_eabst
      unless ← isTypeCorrect motive do
        throwTacticEx `rewriteₒ mvarId "motive is not type correct..."
      Lean.logInfo "CHECKPOINT 2"
      let eqRefl ← mkIdRefl e_obj
      Lean.logInfo "CHECKPOINT 2.5"
      let eqPrf ← mkIdSubst motive eqRefl heq
      Lean.logInfo "CHECKPOINT 3"
      postprocessAppMVars `rewriteₒ mvarId newMVars binderInfos
      let newMVarIds ← newMVars.map Expr.mvarId! |>.filterM (not <$> ·.isAssigned)
      let otherMVarIds ← getMVarsNoDelayed eqPrf
      let otherMVarIds := otherMVarIds.filter (!newMVarIds.contains ·)
      let newMVarIds := newMVarIds ++ otherMVarIds
      pure { eNew := eNew, eqProof := eqPrf, mvarIds := newMVarIds.toList }

def replaceTargetId (mvarId : MVarId) (targetNew : Expr) (eqProof : Expr) : MetaM MVarId :=
  mvarId.withContext do
    mvarId.checkNotAssigned `replaceTarget
    let tag ← mvarId.getTag
    let mvarNew ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar targetNew tag
    let target ← mvarId.getType
    let u ← getLevel target
    let targetType ← inferType target
    let some targetObjType := targetType.objType?
      | throwTacticEx `rewriteₒ mvarId m!"Expression{indentExpr target}does not have an object-level type{indentExpr targetType}"
    let eq ← mkId targetObjType target targetNew
    let newProof ← Lean.Meta.mkExpectedTypeHint eqProof eq
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

example {α β : U} (h : β =ₒ α) (x : α) : β := by
  -- checkₒ h
  rewriteₒ [h]

end Hott.Tactic
