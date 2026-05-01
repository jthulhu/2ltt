import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Location
import Lean.Elab.Tactic.Rewrite

import Tltt.ObjLang
import Tltt.Tactics.Base
import Tltt.Tactics.Builder
import Tltt.Tactics.Check
import Tltt.Tactics.Exhibit
import Tltt.Tactics.Intro
import Tltt.Tactics.Matching
import Tltt.Tactics.PathInduction
import Tltt.Tactics.Replace
import Tltt.Tactics.Rewrite
import Tltt.Tactics.Rfl

open Lean.Parser.Tactic (rwRuleSeq location)
open Lean.Elab.Term (withSynthesize)
open Lean.Elab.Tactic (
  Tactic
  TacticM
  elabTerm
  elabTermEnsuringType
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
  Occurrences
  RewriteResult
  forallBoundedTelescope
  forallMetaTelescopeReducing
  forallTelescopeReducing
  getLevel
  getLocalInstances
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
  withLCtx
  withLetDecl
  withLocalDecl
)
open Lean.MonadLCtx (getLCtx)
open Lean (
  BinderInfo
  Expr
  FVarId
  Level
  LocalDecl
  MVarId
  Name
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

namespace Tltt.Hott.Tactic

namespace DotExpansion
  syntax:max term "₊" ident : term

  elab_rules : term
    | `($e:term₊$fn:ident) => do
      let e_term ← Lean.Elab.Term.elabTerm e none
      let some (_, e_type) ← e_term.inferObjType?
        | throwError "{indentExpr e_term}\nis not an object-level term"
      let rec extract_type (l : Expr) := do
        match l with
        | .const name _ => return name
        | .mdata _ head
        | .app head _ => extract_type head
        | _ =>
          throwError "the type should have the form `C ...` where `C` is a constant, but it's{indentExpr l}"
      let type_name ← extract_type (← instantiateMVars e_type)
      let .ident info rawVal name preresolved := fn.raw
        | throwError "it doesn't work this way, billy...?"
      let actual_ident := ⟨.ident info rawVal (type_name ++ name) preresolved⟩
      let new_stx ← `($actual_ident $e)
      Lean.Elab.Term.elabTerm new_stx none
end DotExpansion

namespace Intro
  syntax "introₒ " notFollowedBy("|") (ppSpace colGt term:max)* : tactic
  macro_rules
    | `(tactic| introₒ $first $[$pat]*) => `(tactic| apply Pi.lam; intro $first $[$pat]*)
end Intro

namespace Apply
  macro "applyₒ " h:term : tactic =>
    `(tactic| apply Pi.app $h)
end Apply

namespace Revert
  syntax "revertₒ " ident : tactic
  macro_rules
    | `(tactic| revertₒ $x) => `(tactic| revert $x; apply Pi.app)
end Revert

noncomputable section
example {α β : Typeₒ} (h : β =ₒ α) (x : α) : β := by
  rewriteₒ [h]
  assumption

example {α β : Typeₒ} (h : α =ₒ β) (x : α) : β := by
  rewriteₒ [← h]
  assumption
end

end Tltt.Hott.Tactic
