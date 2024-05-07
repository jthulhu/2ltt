import Lean

open Lean (
  registerTraceClass
  HashMap
  Name
  Syntax
)
open Lean.Elab (Modifiers)

set_option autoImplicit false

namespace Tltt.Hott.InductiveDecl
instance : Repr Modifiers where
  reprPrec _ _ := .text "<mods>"

instance : Repr Syntax where
  reprPrec _ _ := .text "<stx>"

/-- A constructor branch of an inductive type. -/
structure ConstructorView where
  /-- A syntax reference corresponding to the whole view. -/
  ref : Syntax
  /-- Flags, attributes and documentation of the constructor. -/
  modifiers : Modifiers
  /-- Fully qualified name, ie. `foo.bar.List.nil`. -/
  name : Name
  /-- Name of the constructor, ie. `nil`. See `name`. -/
  short_name : Name
  /-- Syntactic explicitly named arguments of the constructor. -/
  binders : Syntax
  /-- Syntactic type annotation, ie. everything after `:`. -/
  type? : Option Syntax
  deriving Inhabited, Repr

structure ObjInductiveView where
  /-- A syntax reference to the original declaration of the inductive type. -/
  ref : Syntax
  /-- The syntax object grouping the name and the explicit universes of the declaraiton. -/
  declId : Syntax
  /-- Flags, attributes and documentation of the declaration. -/
  modifiers : Modifiers
  /-- Fully-qualified name, ie. `foo.bar.MyInductiveType`. -/
  full_name : Name
  /-- Name of the declaration in the local namespace, ie. `MyInductiveType`. See `name`. -/
  short_name : Name
  /-- All the explicit universe variables introduced at this declaration, taking into account
      `universe`-introduced variables. -/
  levelNames : List Name
  /-- Syntactic parameters of the declaration. -/
  binders : Syntax
  /-- Syntactic type declaration, ie everything after the `:`. -/
  type? : Option Syntax
  /-- The constructors of the inductive type. -/
  constructors : Array ConstructorView
  deriving Inhabited, Repr

initialize registerTraceClass `Tltt.inductiveₒ
initialize registerTraceClass `Tltt.inductiveₒ.names (inherited := true)
initialize registerTraceClass `Tltt.inductiveₒ.universes (inherited := true)

abbrev InductiveTypeMap := HashMap Name ObjInductiveView
initialize obj_inductive_types : IO.Ref InductiveTypeMap ← IO.mkRef {}

syntax "todo!" : term

elab_rules : term
| `(todo!) => do
  Lean.logWarning "TODO"
  let throw_stx ← `(throwError "not implemented yet")
  Lean.Elab.Term.elabTerm throw_stx none
end Tltt.Hott.InductiveDecl
