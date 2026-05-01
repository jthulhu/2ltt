import Lean

open Lean (
  registerTraceClass
)

set_option autoImplicit false

initialize registerTraceClass `Tltt.inductiveₒ
initialize registerTraceClass `Tltt.inductiveₒ.names (inherited := true)
initialize registerTraceClass `Tltt.inductiveₒ.universes (inherited := true)

syntax "todo!" : term

elab_rules : term
| `(todo!) => do
  Lean.logWarning "TODO"
  let throw_stx ← `(throwError "not implemented yet")
  Lean.Elab.Term.elabTerm throw_stx none
