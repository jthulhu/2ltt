import Tltt.ObjLang

open Lean.Elab (throwUnsupportedSyntax)
open Lean.Elab.Tactic (
  Tactic
  getMainGoal
  getFVarId
)

namespace Tltt.Hott.Tactic.Check
  /-- `check` is a debugging tactic. It will not affect the state of the proof whatsoever.
      `check ⊢` checks that the current goal is type-correct.
      `check h` checks that the local hypothesis `h` is type-correct. -/
  syntax (name := check) "check " ("⊢" <|> ident) : tactic

  @[tactic check]
  def check_impl : Tactic
    | `(tactic| check ⊢) => do
      let goal ← getMainGoal
      goal.withContext do
        let goal_type ← goal.getType
        Lean.Meta.check goal_type
    | `(tactic| check $p:ident) => do
      let goal ← getMainGoal
      goal.withContext do
        let lh ← getFVarId p.raw
        Lean.Meta.check <| ← lh.getType
    | _ => throwUnsupportedSyntax
end Tltt.Hott.Tactic.Check
