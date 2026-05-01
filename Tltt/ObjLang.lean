import Lean
import Lean.Data.Options
import Lean.Elab.SyntheticMVars
import Tltt.Initialize

open Lean.PrettyPrinter (Unexpander)
open Lean.PrettyPrinter.Delaborator (Delab delab whenNotPPOption)
open Lean.PrettyPrinter.Delaborator.SubExpr (getExpr withAppArg)
open Lean.MonadOptions (getOptions)

noncomputable section
namespace Tltt.Hott

-- Universe setup
--
-- The object language universe hierarchy is `U.{i}`. If `α : ^U.{i}`, `^α : Type i`, where `^` is
-- the lifting operator.
--
-- `MetaU`, `Ty` and `El` are implementation details required to bootstrap this. For coherency
-- concerns, none outside this module should be able to access the private definitions given
-- here, because they provide an isomorphism that should not exist in the actual 2ltt.
--
-- In this module should only be present the definitions which require access to these private
-- defintions. Otherwise, define them in the Hott module.

structure MetaU.{i} : Type (i+1) where
  private mk ::
  private intoType : Type i

def Ty.{i} : MetaU.{i+1} :=
  MetaU.mk MetaU.{i}

@[pp_using_anonymous_constructor]
structure El (α : MetaU) where
  private mk ::
  private intoU : α.intoType

abbrev liftedU.{i} : Type (i+1) := El.{i+1} Ty.{i}
def U : liftedU := El.mk Ty

example : U.intoU = Ty := by rfl

private def U.fromType.{i} (α : Type i) : liftedU.{i} :=
  El.mk (MetaU.mk α)

-- Tm
def lift.{i} (α : liftedU.{i}) : Type i := El α.intoU

register_option pp.lift : Bool := {
  defValue := false
  group := "pp"
  descr := "(pretty printing) display lift from object-level types to Lean types"
}

prefix:max "^" => lift

@[app_unexpander lift]
def unexpand_lift : Unexpander
  | `($_ $α) => `($α)
  | _ => throw ()

-- @[delab app.lift]
-- def delab_lift : Delab := do
--   -- `(lift oui)
--   whenNotPPOption (·.get pp.lift.name pp.lift.defValue) do
--     let e ← getExpr
--     guard <| e.isAppOfArity' ``lift 1
--     let arg ← withAppArg delab
--     `($arg)

section
universe u
instance : CoeSort liftedU.{u} (Type u) where
  coe α := ^α

-- ^  ≡ Tm
-- U.{i} ≡ Ty

-- Tm (Ty i) ⇒ Set i

instance : CoeSort ^U.{u} (Type u) where
  coe α := ^α
end

example : ^U = liftedU := by rfl

-- Boolean type

def Boolₒ : U :=
  U.fromType Bool

namespace Boolₒ
  def trueₒ : Boolₒ :=
    El.mk true

  def falseₒ : Boolₒ :=
    El.mk false

  protected def elim {P : Boolₒ → U} (b : Boolₒ) (t : P trueₒ) (f : P falseₒ) : P b :=
    match b with
    | ⟨true⟩ => t
    | ⟨false⟩ => f
end Boolₒ
export Boolₒ (trueₒ falseₒ)

-- Pi types

def Pi (α : U) (β : α → U) : U :=
  U.fromType ((a : α) → β a)

namespace Pi
  variable {α : U} {β : α → U}

  def lam (f : (a : α) → β a) : Pi α β :=
    El.mk f

  def app (f : Pi α β) (a : α) : β a :=
    f.intoU a

  infixl:50 " @ₒ " => app
  infixr:50 " $ₒ " => app

  @[app_unexpander app]
  def unexpand_app : Unexpander
    | `($_ $f $a) => `($f $a)
    | _ => throw ()

  syntax obj_fun_binder := "Λ " <|> "λₒ " <|> "funₒ "
  syntax (priority := high) obj_fun_binder ident (" : " term)? " => " term : term
  macro_rules
    | `($_:obj_fun_binder $var $[: $type]? => $body) => `(Pi.lam fun $var $[: $type]? => $body)

  @[app_unexpander lam]
  def unexpand_lam : Unexpander
    | `($_ fun $x:ident $[: $t]? => $b) => `(funₒ $x $[: $t]? => $b)
    | _ => throw ()

  instance : CoeFun (Pi α β) (fun _ => (x : α) → β x) where
    coe := app

  def funext (f g : Pi α β) (p : ∀ x : α, f x = g x) : f = g := by
    induction f
    induction g
    congr
    funext
    apply p
end Pi

syntax "Πₒ " ident " : " term ", " term : term
macro_rules
  | `(Πₒ $x : $α, $P) => `(Pi $α (fun $x : $α => $P))

macro "(" x:ident " : " α:term ") →ₒ " P:term : term => `(Pi $α (fun $x => $P))

@[app_unexpander Pi]
def unexpand_pi : Unexpander
  | `($_ $α fun $x:ident => $β) => `(Πₒ $x : $α, $β)
  | _ => throw ()


namespace Pi
  section
  variable {α : U} {β : α → U}
  variable (f : (a : α) → β a) (g : (a : α) →ₒ β a)

  @[simp]
  theorem app_lam : app (lam f) = f := by rfl
  
  @[simp]
  theorem lam_app : lam (app g) = g := by rfl
  end

  def eta {α : U} {β : α → U} (f : Pi α β) : (funₒ x => f x) = f := by
    rfl
end Pi

-- Arrow type
def Funₒ (α : U) (β : U) : U :=
  Pi α (fun _ => β)

infixr:25 " →ₒ " => Funₒ

instance {α β : U} : CoeFun (α →ₒ β) (fun _ => α → β) where
  coe := Pi.app

instance {α β : U} : Coe (α →ₒ β) (α → β) where
  coe := Pi.app

instance {α β : U} : Coe (α → β) (α →ₒ β) where
  coe := Pi.lam

-- Sigma types
def Sigmaₒ (α : U) (β : α → U) : U :=
  U.fromType (Σ a : α, β a)

namespace Sigmaₒ
  @[match_pattern, inline]
  def mk {α : U} {β : α → U} (x : α) (y : β x) : Sigmaₒ α β :=
    El.mk (Sigma.mk x y)

  @[match_pattern, inline]
  def pr₁ {α : U} {β : α → U} (x : Sigmaₒ α β) : α :=
    x.intoU.1

  postfix:max "₊1" => pr₁

  @[match_pattern, inline]
  def pr₂ {α : U} {β : α → U} (x : Sigmaₒ α β) : β (pr₁ x) :=
    x.intoU.2

  postfix:max "₊2" => pr₂

  @[simp]
  def pr₁.beta {α : U} {β : α → U} (x : α) (y : β x) : (mk x y)₊1 = x := by rfl

  @[simp]
  def pr₂.beta {α : U} {β : α → U} (x : α) (y : β x) : (mk x y)₊2 = y := by rfl

  -- @[simp]
  def eta {α : U} {β : α → U} (x : Sigmaₒ α β) : mk x₊1 x₊2 = x := by rfl
end Sigmaₒ
export Sigmaₒ (pr₁ pr₂)

syntax "Σₒ " ident " : " term ", " term : term
macro_rules
  | `(Σₒ $x : $α, $P) => `(Sigmaₒ $α (fun $x : $α => $P))

@[app_unexpander Sigmaₒ]
def unexpand_sigma : Unexpander
  | `($_ $α fun $x:ident => $β) => ``(Σₒ $x : $α, $β)
  | _ => throw ()

syntax "⟪" term ", " term,+ "⟫" : term
macro_rules
  | `(⟪$left, $right⟫) => `(Sigmaₒ.mk $left $right)
  | `(⟪$x, $y, $tl,*⟫) => `(⟪$x, ⟪$y, $tl,*⟫⟫)

@[app_unexpander Sigmaₒ.mk]
def unexpand_sigma_mk : Unexpander
  | `($_ $x $y) => ``(⟪$x, $y⟫)
  | _ => throw ()

-- Coproduct

def Sumₒ (α : U) (β : U) : U :=
  U.fromType (α ⊕ β)
  
infixr:30 " ⊕ₒ " => Sumₒ

@[app_unexpander Sumₒ]
def unexpand_plus : Unexpander
  | `($_ $α $β) => ``($α ⊕ₒ $β)
  | _ => throw ()

namespace Sumₒ
  @[match_pattern]
  def inlₒ {α : U} {β : U} (a : α) : α ⊕ₒ β :=
    El.mk (Sum.inl a)

  @[match_pattern]
  def inrₒ {α : U} {β : U} (b : β) : α ⊕ₒ β :=
    El.mk (Sum.inr b)

  protected def elim {α : U} {β : U} {P : α ⊕ₒ β → U} (l : (a : α) → P (inlₒ a)) (r : (b : β) → P (inrₒ b))
    (x : α ⊕ₒ β) : P x :=
    match x with
    | ⟨.inl a⟩ => l a
    | ⟨.inr b⟩ => r b
end Sumₒ
export Sumₒ (inlₒ inrₒ)

-- Product

def Prodₒ (α : U) (β : U) : U :=
  Sigmaₒ α (fun _ => β)

infixr:35 " ×ₒ " => Prodₒ

@[app_unexpander Prodₒ]
def unexpand_times : Unexpander
  | `($_ $α $β) => ``($α ×ₒ $β)
  | _ => throw ()

-- Identity type

private inductive Id.Inner.{i} {α : Type i} : α → α → Type i where
  | refl (x : α) : Inner x x

private def Id.Inner.elim.{u₁, u₂} {α : Type u₁} {P : (x : α) → (y : α) → Inner x y → Type u₂}
                                   (h : (x : α) → P x x (refl x)) (x : α) (y : α) (p : Inner x y)
                                   : (P x y p) :=
  @Inner.rec α x (P x) (h x) y p

private def Id.Inner.trans.{i} {α : Type i} (x y z : α) : Inner x y → Inner y z → Inner x z
  | refl _, refl _ => refl _

def Id.{i} {α : U.{i}} (x y : α) : U.{i} :=
  U.fromType.{i} (Id.Inner x.intoU y.intoU)

infix:50 " =ₒ " => Id

@[app_unexpander Id]
def unexpand_id : Unexpander
  | `($_ $x $y) => ``($x =ₒ $y)
  | _ => throw ()

namespace Id
  @[match_pattern]
  def refl {α : U} (x : α) : x =ₒ x :=
    ⟨Inner.refl x.intoU⟩

  protected def elim {α : U} {P : (x : α) → (y : α) → x =ₒ y → U} (h : (x : α) → P x x (refl x)) (x : α)
           (y : α) (p : x =ₒ y) : P x y p := by
    apply El.mk
    apply Inner.elim (P := fun a b q => (P (El.mk a) (El.mk b) (El.mk q)).intoU.intoType)
    intro x
    apply El.intoU
    apply h

  @[simp]
  def elim.beta {α : U} {P : (x : α) → (y : α) → x =ₒ y → U} (h : (x : α) → P x x (refl x))
                (x : α) : Id.elim h x x (refl x) = h x := by
    rfl

  def symm {α : U} (x y : α) (p : x =ₒ y) : y =ₒ x :=
    Id.elim (P := fun x y _ => y =ₒ x) refl x y p

  @[simp]
  theorem symm.beta {α : U} (a : α) : symm a a (refl a) = refl a := by rfl

  def inv {α : U} {x y : α} (p : x =ₒ y): y =ₒ x :=
    symm x y p

  postfix:max "⁻¹ " => Id.inv

  @[app_unexpander Id.inv]
  def unexpand_inv : Unexpander
    | `($_ $x) => ``($x⁻¹)
    | _ => throw ()

  def trans {α : U} (x y z : α) (p₁ : x =ₒ y) (p₂ : y =ₒ z) : x =ₒ z := by
    apply El.mk
    apply Inner.trans <;> apply El.intoU <;> assumption

  @[match_pattern]
  def concat {α : U} {x y z : α} (p₁ : x =ₒ y) (p₂ : y =ₒ z) : x =ₒ z :=
    trans x y z p₁ p₂

  infixr:60 " ⬝ " => concat

  @[app_unexpander concat]
  def unexpand_concat : Unexpander
    | `($_ $p₁ $p₂) => ``($p₁ ⬝ $p₂)
    | _ => throw ()

  def subst {α : U} {P : α → U} {a b : α} (h : a =ₒ b) : P a → P b := by
    apply Pi.app
    apply Id.elim (P := fun x y _ => P x →ₒ P y)
    intro x
    apply Pi.lam
    exact id
    exact h

  @[simp]
  theorem subst.beta {α : U} {motive : α → U} {a : α} : @subst α motive a a (refl _) = id :=
    rfl

  def mp {α β : U} (h : α =ₒ β) (a : α) : β :=
    subst (P := fun x => x) h a

  @[simp]
  theorem mp.beta {α : U} : mp (refl α) = id := by rfl

  def mpr {α β : U} (h : α =ₒ β) (b : β) : α :=
    mp (symm α β h) b

  @[simp]
  theorem mpr.beta {α : U} : mpr (refl α) = id := by rfl
end Id

namespace InductiveDecl
  open Lean (
    BinderInfo
    Constructor
    Declaration
    DeclarationRanges
    Expr
    HashMap
    indentD
    InductiveType
    LMVarId
    Level
    LocalContext
    LocalInstances
    MVarId
    MacroM
    MonadRef
    MonadError
    Name
    Syntax
    TransformStep
    addDecl
    addDeclarationRanges
    assignLevelMVar
    collectLevelParams
    getMaxHeight
    indentExpr
    instantiateLevelMVars
    instantiateMVars
    logErrorAt
    mkApp2
    mkAppN
    mkFreshId
    mkIdentFrom
    mkLevelParam
    privateHeader
    withRef
  )
  open Lean.MonadEnv (getEnv)
  open Lean.Parser (
    atomic
    many
    optional
    ppGroup
    ppIndent
    ppSpace
    rawIdent
  )
  open Lean.Parser.Command (
    declModifiers
    docComment
  )
  open Lean.Parser.Term (
    binderIdent
    bracketedBinder
    optType
  )
  open Lean.Elab (
    Modifiers
    applyVisibility
    elabModifiers
    expandOptDeclSig
    getDeclarationRange
    getDeclarationSelectionRef
    liftMacroM
    sortDeclLevelParams
    throwAbortTerm
  )
  open Lean.Elab.Command (
    CommandElab
    CommandElabM
    accLevel
    checkResultingUniverse
    expandDeclId
    mkResultUniverse
    runTermElabM
    shouldInferResultUniverse
  )
  open Lean.Elab.Term (
    TermElabM
    addAutoBoundImplicits
    addAutoBoundImplicits'
    addLocalVarInfo
    applyAttributes
    collectUnassignedMVars
    elabBinders
    elabTerm
    elabType
    ensureNoUnassignedMVars
    getLevelNames
    synthesizeSyntheticMVars
    synthesizeSyntheticMVarsNoPostponing
    withAutoBoundImplicit
    withAutoBoundImplicitForbiddenPred
    withLevelNames
    withoutSavingRecAppSyntax
  )
  open Lean.Meta (
    MetaM
    forallBoundedTelescope
    forallTelescopeReducing
    getFVarLocalDecl
    getLevel
    getLocalInstances
    inferType
    instantiateForall
    isDefEq
    isType
    mkAppM
    mkForallFVars
    mkLambdaFVars
    mkFreshLevelMVar
    transform
    whnf
    whnfD
    whnfI
    whnfR
    withAtLeastTransparency
    withLCtx
    withLocalDecl
    withLocalDecls
    withLocalDeclD
    withNewBinderInfos
    withTransparency
  )
  open Lean.MonadLCtx (
    getLCtx
  )

  def optDeclSig := leading_parser
    many (ppSpace >> (binderIdent <|> bracketedBinder)) >> optType

  def ctor := leading_parser
    atomic (Lean.Parser.optional docComment >> "\n| ")
    >> ppGroup (declModifiers true >> rawIdent >> optDeclSig)

  def modifiers := declModifiers false
  def sig := ppIndent optDeclSig

  /--
    Object-level inductive declaration. They are similar to meta-level inductive declarations,
    but produce object-level types.

    Here are the rules that govern these declarations:
    - object-level inductive types are `noncomputable`, due to a (supposedly temporary)
      limitation of the Lean compiler
    - recursive inductive types must only occur in strictly positive positions
    - parameters can be from any level (this includes variables defined in a `variable`
      statement)
    - indices must be object-level (this includes fixed indices that are lifted as parameters)
    - the resulting type is, of course, an object-level type
    - constructor arguments must be object-level
    - `unsafe` declarations are not supported
    - `mutual` declarations are not supported
  -/
  syntax (name := obj_inductive_decl) modifiers "inductiveₒ " declId sig (" :=" <|> " where")?
                                      ctor* : command

  structure ObjConstructor where
    /-- Fully qualified name of the constructor, ie. `foo.bar.List.nil`. -/
    full_name : Name
    /-- Name of the constructor, ie. `nil`. See `full_name` for the fully qualified version. -/
    short_name : Name
    /--
      Name of the inner counterpart of the constructor, that is, the corresponding constructor
      of the private, underlying inductive type.
    -/
    inner_name : Name
    /-- Type of the constructor, ie. `nil : {α : U.{u}} → List.{u} α` -/
    type : Expr
  deriving Inhabited, Repr

  namespace ObjConstructor
    def type_instanciated_with_parameters (self : ObjConstructor) (params : Array Expr)
                                          : MetaM Expr := do
      let lambda_form ← forallBoundedTelescope self.type params.size fun args goal =>
        mkLambdaFVars args goal
      let substitued := mkAppN lambda_form params
      whnfI substitued

    /--
      For a constructor like `cons : {α : U} → (hd : α) → (tl : Hello α) → Hello α`, given `α`,
      `hd` and `tl`, return the arguments to be passed to `Hello`, ie `#[α]` here. Indices may
      depend on the constructor arguments.
    -/
    def target_inner_type (self : ObjConstructor) (arguments : Array Expr) : MetaM (Array Expr) := do
      let lambda_form ← forallTelescopeReducing self.type fun args target =>
        mkLambdaFVars args target
      let substitued ← whnfI <| mkAppN lambda_form arguments
      let .app (.const ``lift [_]) substitued := substitued
        | throwError m!"constructor has to produce an object-level type, got{indentExpr substitued}"
      return substitued.getAppArgs
  end ObjConstructor
  
  structure PartialObjInductiveType where
    /-- Fully qualified name of the inductive type family, ie. `foo.bar.List`. -/
    full_name : Name
    /-- Name of the inductive type family, ie. `List`. See `full_name`. -/
    short_name : Name
    /-- Name of the underlying, private inductive type. -/
    inner_name : Name
    /-- The constructors of the inductive type. -/
    constructors : List ObjConstructor
    /-- The type of the family of inductive types, ie `List.{u} : U.{u} → U.{u}`. -/
    type : Expr
  deriving Inhabited, Repr

  structure ObjInductiveType extends PartialObjInductiveType where
    /-- All the explicit universe variables introduced at this declaration. -/
    level_names : List Name
    /--
      Number of parameters. This is *not* the same as the arity, which is the number of
      parameters plus the number of indices.
    -/
    number_parameters : Nat
  deriving Inhabited, Repr

  namespace ObjInductiveType
    def level_vars (self : ObjInductiveType) : List Level :=
      self.level_names.map Level.param
  end ObjInductiveType

  def ObjConstructor.make_inner_decl (constructor : ObjConstructor) (ind_type : ObjInductiveType)
                                     : MetaM Constructor := do
    let type := constructor.type.replace fun
      | .app (.const ``lift [_]) e => do
        let fn := e.getAppFn
        let args := e.getAppArgs
        let .const name levels := fn | none
        if name == ind_type.full_name then
          return mkAppN (.const ind_type.inner_name levels) args
        else
          none
      | _ => none
    return {
      name := constructor.inner_name
      type
    }

  def liftedU? : Expr → Option Level
    | .app (.const ``lift [_]) (.const ``U [u])
    | .app (.const ``El [.succ _])
           (.app (.app (.const ``El.intoU [.succ (.succ _)])
                       (.const ``Ty [.succ _]))
                 (.const ``U [u])) => some u
    | _ => none

  def ObjInductiveType.make_inner_decl (ind_type : ObjInductiveType) : MetaM InductiveType := do
    let type ← forallTelescopeReducing ind_type.type fun params goal => do
      -- let u ← mkFreshLevelMVar
      -- let pattern := .const ``liftedU [u]
      let some u := liftedU? goal
        | throwError "object-level inductive definition should produce a type that lives in the object-level universe, not{indentExpr goal}"
      mkForallFVars params <| .sort (.succ u)
    return {
      name := ind_type.inner_name
      type
      ctors := ← ind_type.constructors.mapM (·.make_inner_decl ind_type)
      : InductiveType
    }

  structure ElabHeaderResult where
    view : ObjInductiveView
    lctx : LocalContext
    localInsts : LocalInstances
    params : Array Expr
    type : Expr
    deriving Inhabited


  def mk_obj_private (n : Name) : Name :=
    -- TODO: replace with `Tltt.ObjLang.Empty to avoid name clashes with things actually defined
    --       in this module. This is currently like this to debug: any "private" declaration
    --       actually ends up here, so we can inspect it.
    .num (privateHeader ++ `Tltt.ObjLang) 0 ++ (n.appendAfter "_priv")

  def register_inductive_type (name : Name) (view : ObjInductiveView) : IO Unit :=
    obj_inductive_types.modify fun map => map.insert name view

  def get_inductive_type? (name : Name) : IO (Option ObjInductiveView) := do
    let map ← obj_inductive_types.get
    return map.find? name

  def check_obj_inductive_modifiers {m : Type → Type} [Monad m] [MonadError m]
                                    (modifiers : Modifiers) : m Unit := do
    if modifiers.isNoncomputable then
      throwError "invalid use of 'noncomputable' in object inductive declaration"
    if modifiers.isPartial then
      throwError "invalid use of 'partial' in inductive declaration"
    if modifiers.isUnsafe then
      throwError "'unsafe' is unsupported for object types"

  def check_obj_ctor_modifiers {m : Type → Type} [Monad m] [MonadError m] (modifiers : Modifiers)
                               : m Unit := do
    if modifiers.isNoncomputable then
      throwError "invalid use of 'noncomputable' in constructor declaration"
    if modifiers.isPartial then
      throwError "invalid use of 'partial' in constructor declaration"
    if modifiers.isUnsafe then
      throwError "invalid use of 'unsafe' in constructor declaration"
    if modifiers.attrs.size != 0 then
      throwError "invalid use of attributes in constructor declaration"

  def obj_ind_stx_to_view (modifiers : Modifiers) (decl : Syntax) (declRange : DeclarationRanges)
                          (declId : Syntax) (declSig : Syntax) (declCtrs : Syntax)
                          : CommandElabM ObjInductiveView := do
    check_obj_inductive_modifiers modifiers
    let (binders, type?) := expandOptDeclSig declSig
    let ⟨short_name, name, levelNames⟩ ← expandDeclId declId modifiers
    trace[Tltt.inductiveₒ.names] "name = {name}, short_name = {short_name}, levelNames = {levelNames}"
    addDeclarationRanges name declRange
    let constructors ← declCtrs.getArgs.mapM fun ctor => withRef ctor do
      -- `ctor` syntax is
      -- (docComment)? "\n| " modifiers rawIdent optDeclSig
      let mut ctor_modifiers ← elabModifiers ctor[2]
      if let some leadingDocComment := ctor[0].getOptional? then
        if ctor_modifiers.docString?.isSome then
          logErrorAt leadingDocComment "duplicate doc string"
        ctor_modifiers := { ctor_modifiers with docString? := Lean.TSyntax.getDocString ⟨leadingDocComment⟩ }
      -- ensure that constructors can be used in pattern matching
      ctor_modifiers := { ctor_modifiers with attrs := ctor_modifiers.attrs.push { name := `match_pattern } }
      let short_ctor_name := ctor.getIdAt 3
      trace[Tltt.inductiveₒ.names] "ctor_name = {short_ctor_name}"
      let ctor_name := name ++ short_ctor_name
      let ctor_name ← withRef ctor[3] <| applyVisibility ctor_modifiers.visibility ctor_name
      let (binders, type?) := expandOptDeclSig ctor[4]
      Lean.addDocString' ctor_name ctor_modifiers.docString?
      Lean.Elab.addAuxDeclarationRanges ctor_name ctor ctor[3]
      return {
        ref := ctor
        modifiers := ctor_modifiers
        name := ctor_name
        short_name := short_ctor_name
        binders := binders
        type? := type?
        : ConstructorView
      }
    return {
      ref := decl
      full_name := name
      short_name
      declId
      modifiers
      levelNames
      binders
      type?
      constructors
    }

  /-- Lifts `e` if it's an object-level type, raises an exception otherwise. -/
  def ensure_obj_type (e : Expr) : TermElabM Expr := do
    let u ← mkFreshLevelMVar
    let pattern := Expr.const ``liftedU [u]
    let e_type ← inferType e
    withAtLeastTransparency .default do
      if ← isDefEq e_type pattern then
        return .app (.const ``lift [u]) e
      else if (← instantiateMVars e).hasSyntheticSorry then
        throwAbortTerm
      else
        throwError "object-level type expected, got\n  {← instantiateMVars e} : {← instantiateMVars e_type}"

  def elab_obj_type (stx : Syntax) : TermElabM Expr := do
    let u ← mkFreshLevelMVar
    let type ← elabTerm stx (Expr.const ``liftedU [u])
    withRef stx <| ensure_obj_type type

  /-- Check that the type is of the form α₁ → α₂ → ⋯ → αₙ → U, where every has to be an
      object-level type. -/
  partial def is_obj_type_former (type : Expr) : MetaM Bool := do
    match ← whnfD type with
    | .forallE var_name var_type body bi =>
      let type_of_var_type ← inferType var_type
      if liftedU? type_of_var_type |>.isSome then
        withLocalDecl var_name bi var_type fun x => is_obj_type_former (body.instantiate1 x)
      else if let .app (.const ``lift _) _ := var_type then
        return true
      else
        return false
    | _ =>
      trace[Tltt.inductiveₒ] "{repr type}"
      return liftedU? type |>.isSome

  /-- Elaborate the header of the declaration, checking for the following properties:
      - all indices must be object-level types (lifted object-level types **not** accepted)
      - parameters can be any-level types
      - the type of an element of the inductive family must be an object-level type, ie. in U -/
  def elab_header (view : ObjInductiveView) : TermElabM ElabHeaderResult := do
    -- do not attempt to add auto-bound implicits for occurrences of the inductive type in its
    -- header declaration, ie. if an inductive type `Header` uses `Header` in its parameters or
    -- in its type, it's an error.
    withAutoBoundImplicitForbiddenPred (fun n => view.short_name == n) do
      withAutoBoundImplicit <| elabBinders view.binders.getArgs fun params => do
        match view.type? with
        | none =>
          let u ← mkFreshLevelMVar
          let type := Expr.const ``liftedU [u]
          synthesizeSyntheticMVarsNoPostponing
          -- this transforms every metavariable that has not been unified yet into an implicit
          -- parameter, adding it to `params` and modifying `type` to swap out the metavariable
          -- for a free variable referencing that implicit parameter
          addAutoBoundImplicits' params type fun params type => do
            trace[Tltt.inductiveₒ] "header params: {params}, type: {type}"
            return {
              lctx := ← getLCtx
              localInsts := ← getLocalInstances
              params
              type
              view
            }
        | some type_stx =>
          let type ← withAutoBoundImplicit do
            let type ← elabType type_stx
            unless ← is_obj_type_former type do
              throwErrorAt type_stx "invalid object-inductive type, resultant type is not U"
            synthesizeSyntheticMVarsNoPostponing
            let indices ← addAutoBoundImplicits #[]
            mkForallFVars indices type
          addAutoBoundImplicits' params type fun params type => do
            trace[Tltt.inductiveₒ] "header params: {params}, type: {type}"
            return {
              lctx := ← getLCtx
              localInsts := ← getLocalInstances
              params
              type
              view
            }

  def mk_type_for (header : ElabHeaderResult) : TermElabM Expr := do
    withLCtx header.lctx header.localInsts do
      mkForallFVars header.params header.type

  def with_obj_ind_local_decl {α : Type _} (header : ElabHeaderResult)
                              (x : Array Expr → Expr → TermElabM α) : TermElabM α := do
    let type ← mk_type_for header
    withLCtx header.lctx header.localInsts <| withRef header.view.ref do
      Lean.Elab.Term.withAuxDecl header.view.short_name type header.view.full_name fun indFVar =>
        forallTelescopeReducing type fun params _ => do
          x params indFVar

  /-- Execute `k` with updated binder information for `xs`. Any `x` that is explicit becomes
      implicit. -/
  def withExplicitToImplicit {α : Type _} (xs : Array Expr) (k : TermElabM α)
                                     : TermElabM α := do
    let mut toImplicit := #[]
    for x in xs do
      if (← getFVarLocalDecl x).binderInfo.isExplicit then
        toImplicit := toImplicit.push (x.fvarId!, BinderInfo.implicit)
    withNewBinderInfos toImplicit k

  def is_inductive_family (num_params : Nat) (indFVar : Expr) : TermElabM Bool := do
    let indFVarType ← inferType indFVar
    forallTelescopeReducing indFVarType fun xs _ =>
      return xs.size > num_params

  def elab_constructor (indFVar : Expr) (params : Array Expr) (nb_params : Nat)
                       (header : ElabHeaderResult) : TermElabM (List ObjConstructor) :=
    withRef header.view.ref do
    let indFamily ← is_inductive_family params.size indFVar
    header.view.constructors.toList.mapM fun ctor_view =>
      withAutoBoundImplicit <| elabBinders ctor_view.binders.getArgs fun ctorParams =>
        withRef ctor_view.ref do
          let rec elabCtorType (k : Expr → TermElabM ObjConstructor)
                               : TermElabM ObjConstructor := do
            match ctor_view.type? with
            | none =>
              if indFamily then
                throwError "constructor resulting type must be specified in inductive family declaration"
              k <| mkAppN indFVar params
            | some ctorType =>
              let type ← elab_obj_type ctorType
              trace[Tltt.inductiveₒ] "elabType {ctor_view.name}: {type}"
              synthesizeSyntheticMVars (postpone := .yes)
              let type ← instantiateMVars type
              let type ← checkParamOccs type
              forallTelescopeReducing type fun _ resultingType => do
                let .app (.const ``lift [_]) resultingType := resultingType
                  | throwError "unepexceted constructor resulting type, expected lifted type{indentExpr resultingType}"
                unless resultingType.getAppFn == indFVar do
                  throwError "unexpected constructor resulting type{indentExpr resultingType}"
                -- unless ← isType resultingType do
                  -- throwError "unexpected constructor resulting type, type expected{indentExpr resultingType}"
              k type
          elabCtorType fun type => do
            synthesizeSyntheticMVarsNoPostponing
            let ctorParams ← addAutoBoundImplicits ctorParams
            let except (mvarId : MVarId) := ctorParams.any fun ctorParam =>
              ctorParam.isMVar && ctorParam.mvarId! == mvarId
            let extraCtorParams ← collectUnassignedMVars (← instantiateMVars type) #[] except
            trace[Tltt.inductiveₒ] "extraCtorParams: {extraCtorParams}"
            let type ← mkForallFVars (extraCtorParams ++ ctorParams) type
            -- let type ← reorderCtorArgs type
            let type ← mkForallFVars params[:nb_params] type
            trace[Tltt.inductiveₒ] "{ctor_view.name}: {type}"
            return {
              full_name := ctor_view.name
              short_name := ctor_view.short_name
              inner_name := mk_obj_private ctor_view.name
              type
            }
  where
    checkParamOccs (ctorType : Expr) : MetaM Expr := do
      let visit (e : Expr) : MetaM TransformStep := do
        let f := e.getAppFn
        if indFVar == f then
          let mut args := e.getAppArgs
          unless args.size ≥ params.size do
            throwError "unexpected inductive type occurrence{indentExpr e}"
          for i in [:nb_params] do
            let param := params[i]!
            let arg := args[i]!
            unless ← isDefEq param arg do
              throwError "inductive type parameter mismatch{indentExpr arg}\nexpected{indentExpr param}"
            args := args.set! i param
          return .done (mkAppN f args)
        else
          return .continue
      transform ctorType (pre := visit)

  /--
    Retrieve the object-level universe in which the inductive type lives. Concretely, if we
    define a value with type `α₁ → α₂ → ⋯ → αₙ → U.{u}`, return `u`.
  -/
  def get_obj_resulting_universe (ind_type : PartialObjInductiveType) : MetaM Level :=
  forallTelescopeReducing ind_type.type fun _ r => do
    let some u := liftedU? r
      | throwError "unexpected inductive type resulting type{indentExpr r}"
    return u

  
  def ObjInductiveType.as_const (self : ObjInductiveType) : Expr :=
    .const self.full_name (self.level_names.map Level.param)

  def ObjInductiveType.as_expr_type (self : ObjInductiveType) (params : Array Expr) : MetaM Expr := do
    let u ← get_obj_resulting_universe self.toPartialObjInductiveType
    let cst := self.as_const
    return .app (.const ``lift [u]) <| mkAppN cst params
  /--
    Retrieve the Lean-level universe in which the definition lives. Concretely, if we define
    a value with type `α₁ → α₂ → ⋯ → αₙ → U.{u}`, return `u+1`.
  -/
  def get_resulting_universe_as_sort (ind_type : PartialObjInductiveType) : TermElabM Level := do
    let u ← get_obj_resulting_universe ind_type
    return .succ u

  def collectUsed (ind_type : PartialObjInductiveType) : StateRefT Lean.CollectFVars.State MetaM Unit := do
    ind_type.type.collectFVars
    ind_type.constructors.forM fun ctor =>
      ctor.type.collectFVars

  def removeUnused (vars : Array Expr) (ind_type : PartialObjInductiveType)
                   : TermElabM (LocalContext × LocalInstances × Array Expr) := do
    let (_, used) ← collectUsed ind_type |>.run {}
    Lean.Meta.removeUnused vars used

  def withUsed {α} (vars : Array Expr) (ind_type : PartialObjInductiveType) (k : Array Expr → TermElabM α)
               : TermElabM α := do
    let (lctx, local_insts, vars) ← removeUnused vars ind_type
    withLCtx lctx local_insts <| k vars

  def update_params (vars : Array Expr) (ind_type : PartialObjInductiveType)
                    : TermElabM PartialObjInductiveType := do
    let type ← mkForallFVars vars ind_type.type
    let ctors ← ind_type.constructors.mapM fun ctor => do
      let ctorType ← withExplicitToImplicit vars (mkForallFVars vars ctor.type)
      return { ctor with type := ctorType }
    return { ind_type with type, constructors := ctors }

  def levelMVarToParam (ind_type : PartialObjInductiveType) (univToInfer? : Option LMVarId)
                       : TermElabM PartialObjInductiveType := do
    let type ← levelMVarToParam' ind_type.type
    let ctors ← ind_type.constructors.mapM fun ctor => do
      let ctorType ← levelMVarToParam' ctor.type
      return { ctor with type := ctorType }
    return { ind_type with constructors := ctors, type }
  where
    levelMVarToParam' (type : Expr) : TermElabM Expr := do
      Lean.Elab.Term.levelMVarToParam type (except := fun mvarId => univToInfer? == some mvarId)

  /-- Execute `k` using the syntactic reference to the constructor branch. -/
  def with_ctor_ref {m α} [Monad m] [MonadRef m] (view : ObjInductiveView) (ctor_name : Name)
                    (k : m α) : m α := do
    for ctor_view in view.constructors do
      if ctor_view.name == ctor_name then
        return ← withRef ctor_view.ref k
    k

  /--
    Auxiliary function for `updateResultingUniverse`
    `acc_level_at_ctor ctor ctorParam r rOffset` add `u` (`ctorParam`'s universe) to state if it is not already there and
    it is different from the resulting universe level `r+rOffset`.

    See `accLevel`.
  -/
  def acc_level_at_ctor (ctor : ObjConstructor) (ctorParam : Expr) (r : Level) (rOffset : Nat) : StateRefT (Array Level) TermElabM Unit := do
    let type ← inferType ctorParam
    let u ← instantiateLevelMVars (← getLevel type)
    match (← modifyGet fun s => accLevel u r rOffset |>.run |>.run s) with
    | some _ => pure ()
    | none =>
      let typeType ← inferType type
      let mut msg := m!"failed to compute resulting universe level of inductive datatype, constructor '{ctor.short_name}' has type{indentExpr ctor.type}\nparameter"
      let localDecl ← getFVarLocalDecl ctorParam
      unless localDecl.userName.hasMacroScopes do
        msg := msg ++ m!" '{ctorParam}'"
      msg := msg ++ m!" has type{indentD m!"{type} : {typeType}"}\ninductive type resulting type{indentExpr (.sort (r.addOffset rOffset))}"
      if r.isMVar then
        msg := msg ++ "\nrecall that Lean only infers the resulting universe level automatically when there is a unique solution for the universe level constraints, consider explicitly providing the inductive type resulting universe level"
      throwError msg


  /--
    Collect all the universes in which the inductive type might live, ie. those declared for each
    constructor.
  -/
  def collectUniverses (view : ObjInductiveView) (u : Level) (u_offset : Nat) (numParams : Nat)
                       (ind_type : PartialObjInductiveType) : TermElabM (Array Level) := do
    let (_, us) ← go |>.run #[]
    return us
  where
    go : StateRefT (Array Level) TermElabM Unit :=
      ind_type.constructors.forM fun ctor =>
        with_ctor_ref view ctor.full_name do
          forallTelescopeReducing ctor.type fun ctorParams _ =>
            for ctorParam in ctorParams[numParams:] do
              acc_level_at_ctor ctor ctorParam u u_offset

  def check_resulting_universes (view : ObjInductiveView) (numParams : Nat)
                                (ind_type : PartialObjInductiveType) : TermElabM Unit := do
    let u := (← instantiateLevelMVars (← get_resulting_universe_as_sort ind_type)).normalize
    -- `u` must be of the form `?u+1`
    checkResultingUniverse u
    for ctor in ind_type.constructors do
      forallTelescopeReducing ctor.type fun ctorArgs _ => do
        for ctorArg in ctorArgs[numParams:] do
          let type ← inferType ctorArg
          let v := (← instantiateLevelMVars (← getLevel type)).normalize
          let rec check (v' : Level) (u' : Level) : TermElabM Unit := match v', u' with
            | .succ v', .succ u' => check v' u'
            | .mvar id, Level.param .. =>
              assignLevelMVar id u'
            | .mvar id, .zero => assignLevelMVar id u'
            | _, _ =>
              unless u.geq v do
                let mut msg := m!"invalid universe level in constructor '{ctor.short_name}', parameter"
                let local_decl ← getFVarLocalDecl ctorArg
                unless local_decl.userName.hasMacroScopes do
                  msg := msg ++ m!" '{ctorArg}"
                msg := msg ++ m!" has type{indentExpr type}\n"
                msg := msg ++ m!"at universe level{indentD v}\n"
                msg := msg ++ m!"it must be smaller than or equal to the inductive datatype universe level{indentD u}"
                with_ctor_ref view ctor.full_name <| throwError msg
          check v u

  /--
    Resolve the metavariables in the universe level of the universe in which the inductive type
    will eventually live in.
  -/
  def update_resulting_universe (view : ObjInductiveView) (numParams : Nat)
                                (ind_type : PartialObjInductiveType) : TermElabM PartialObjInductiveType := do
    let u ← get_resulting_universe_as_sort ind_type
    let u_offset : Nat := u.getOffset
    let u : Level := u.getLevelOffset
    unless u.isMVar do
      -- we only handle the case where `u =?= ?u + u_offset`
      throwError "failed to compute resulting universe level of inductive datatype, provide universe explicitely: {u}"
    let us ← collectUniverses view u u_offset numParams ind_type
    trace[Tltt.inductiveₒ] "update_resulting_universe us: {us}, u: {u}, u_offset: {u_offset}"
    let u_new := mkResultUniverse us u_offset
    assignLevelMVar u.mvarId! u_new
    let type ← instantiateMVars ind_type.type
    let ctors ← ind_type.constructors.mapM fun ctor =>
      return { ctor with type := ← instantiateMVars ctor.type }
    return { ind_type with type, constructors := ctors }

  def collect_level_params_in_inductive (ind_type : PartialObjInductiveType) : Array Name := Id.run do
    let mut used_params := collectLevelParams {} ind_type.type
    for ctor in ind_type.constructors do
      used_params := collectLevelParams used_params ctor.type
    return used_params.params

  def replace_ind_fvars_with_consts (ind_fvar : Expr) (level_names : List Name)
                                    (num_vars : Nat) (num_params : Nat)
                                    (ind_type : PartialObjInductiveType)
                                    : TermElabM PartialObjInductiveType := do
    let ctors ← ind_type.constructors.mapM fun ctor => do
      let type ← forallBoundedTelescope ctor.type num_params fun params type => do
        let type := type.replace fun e =>
          if !e.isFVar then
            none
          else if e != ind_fvar then
            none
          else
            let level_params := level_names.map Level.param
            let c := Expr.const ind_type.full_name level_params
            mkAppN c (params.extract 0 num_vars)
        instantiateMVars (← mkForallFVars params type)
      return { ctor with type }
    return { ind_type with constructors := ctors }

  /--
    For an inductive declaration `ind_type` that produces a value of type `α₁ → α₂ → ⋯ → αₙ → U`,
    return `n`.

    This corresponds to the number of parameters plus the number of indices of the inductive
    family defined.
  -/
  def get_arity (ind_type : PartialObjInductiveType) : MetaM Nat :=
    forallTelescopeReducing ind_type.type fun xs _ => pure xs.size

  /--
    Compute a bit-mask that masks indices that are fixed, ie. they are always instantiate with
    the same value for all constructors, for the inductive type `ind_type`. The first
    `num_params` are `false`, since they alreay are paremeters.
    For `i ∈ [num_params, arity)`, we have `result[i]` is `true` if the `i`-th index of the
    inductive family is fixed.
  -/
  def compute_fixed_index_bitmask (num_params : Nat) (ind_type : PartialObjInductiveType) (ind_fvar : Expr)
                                  : MetaM (Array Bool) := do
      let arity ← get_arity ind_type
      let num_indices := arity - num_params
      if arity ≤ num_params then
        -- This is copied from `Inductive.lean`. From my understanding, `arity ≥ num_params`, as
        -- the `arity` is the number of parameters `num_params` plus the number of indices. If
        -- both are equal, then there are no indices, so the bitmask is all `false`.
        return mkArray arity false
      let mask_ref ← IO.mkRef (mkArray num_params false ++ mkArray num_indices true)
      for ctor in ind_type.constructors do
        forallTelescopeReducing ctor.type fun xs type => do
          let type_args := type.getAppArgs
          for i in [num_params:arity] do
            unless i < xs.size && xs[i]! == type_args[i]! do
              mask_ref.modify fun mask => mask.set! i false
          for x in xs[num_params:] do
            let x_type ← inferType x
            let cond (e : Expr) := e.getAppFn == ind_fvar && e.getAppNumArgs > num_params
            x_type.forEachWhere cond fun e => do
              let e_args := e.getAppArgs
              for i in [num_params:e_args.size] do
                if i >= type_args.size then
                  mask_ref.modify (reset_mask_at · i)
                else
                  unless e_args[i]! == type_args[i]! do
                    mask_ref.modify (reset_mask_at · i)
      mask_ref.get
  where
    reset_mask_at (mask : Array Bool) (i : Nat) : Array Bool :=
      if h : i < mask.size then
        mask.set ⟨i, h⟩ false
      else
        mask

  def isDomainDefEq (arrow_type : Expr) (type : Expr) : MetaM Bool := do
    if !arrow_type.isForall then
      return false
    else
      isDefEq arrow_type.bindingDomain! type

  /--
    Computes the largest prefix of indices that can be converted to parameters, and return the
    new number of parameters, which is `num_params` plus the number of such indices.
  -/
  partial def fixed_indices_to_params (num_params : Nat) (ind_type : PartialObjInductiveType)
                                      (ind_fvar : Expr) : MetaM Nat := do
    let mask ← compute_fixed_index_bitmask num_params ind_type ind_fvar
    if !mask.contains true then
      return num_params
    forallBoundedTelescope ind_type.type num_params fun params type => do
      -- otherTypes ≡ #[]
      let ctor_types ← ind_type.constructors.mapM fun ctor => do
        whnfD (← instantiateForall ctor.type params)
      let rec go (i : Nat) (type : Expr) (types_to_check : List Expr) : MetaM Nat := do
        if h : i < mask.size then
          if !mask[i] then
            return i
          if !type.isForall then
            return i
          let param_type := type.bindingDomain!
          if !(← types_to_check.allM fun type => isDomainDefEq type param_type) then
            trace[Tltt.inductiveₒ] "domain not def eq: {i}, {type} =?= {param_type}"
            return i
          withLocalDeclD `a param_type fun param_new => do
            let types_to_check ← types_to_check.mapM fun type =>
              whnfD (type.bindingBody!.instantiate1 param_new)
            go (i+1) (type.bindingBody!.instantiate1 param_new) types_to_check
        else
          return i
      go num_params type ctor_types

  def make_constructor_decl (ind_type : ObjInductiveType) (constructor : ObjConstructor)
                            (params : Array Expr) : TermElabM Unit := do
    let u ← get_obj_resulting_universe ind_type.toPartialObjInductiveType
    let constr_val ← forallTelescopeReducing constructor.type fun constr_params _ => do
      -- `actual_params` is the same as constructor params, except that the arguments
      -- which are of the type of the inductive type we are defining are unwraped
      let actual_params ← constr_params.mapM fun param => do
        let param_type ← inferType param
        -- By strict positiivty, the only place were the inductive type we are defining
        -- can appear is as `param_target`.
        forallTelescopeReducing param_type fun param_args param_target => do
          let Expr.app (.const ``lift [u_param]) lifted := param_target | return param
          let Expr.const name level_args := lifted.getAppFn | return param
          let inner_metau :=
            Expr.app (.const ``MetaU.mk [u_param])
            <| mkAppN (.const ind_type.inner_name level_args) lifted.getAppArgs
          if name == ind_type.full_name then
            mkAppN param param_args
            |> mkApp2 (.const ``El.intoU [u_param]) inner_metau
            |> mkLambdaFVars param_args
          else
            return param
      let inner_metau :=
        .app (.const ``MetaU.mk [u])
        <| mkAppN (.const ind_type.inner_name ind_type.level_vars)
        <| ← constructor.target_inner_type constr_params
      actual_params
      |> mkAppN (.const constructor.inner_name ind_type.level_vars)
      |> mkApp2 (.const ``El.mk [u]) inner_metau
      |> mkLambdaFVars constr_params
    let constr_val ← instantiateMVars constr_val
    let constr_def_val := {
      value := constr_val
      name := constructor.full_name
      levelParams := ind_type.level_names
      type := constructor.type
      safety := .safe
      hints := .regular <| getMaxHeight (← getEnv) constr_val + 1
    }
    trace[Tltt.inductiveₒ.constr] m!"{constructor.short_name} : {constructor.type} := {indentExpr constr_val}"
    let constr_decl := Declaration.defnDecl constr_def_val
    ensureNoUnassignedMVars constr_decl
    addDecl constr_decl

  def mkElMk (e : Expr) : MetaM Expr := do
    let e_type ← inferType e
    let e_type_type ← inferType e_type
    let .sort (.succ u) := e_type_type
      | throwError "type's type should be `Type u`{indentExpr e_type}\nnot{indentExpr e_type_type}"
    let metau := .app (.const ``MetaU.mk [u]) e_type
    return mkApp2 (.const ``El.mk [u]) metau e

  def with_dewraped_arguments {α} [Inhabited α] (actual_arguments : Array Expr)
                              (ind_type : ObjInductiveType) (f : Array Expr → TermElabM α)
                              : TermElabM α := do
    let mut rewrap_maps : Array (Expr → MetaM Expr) := Array.mkEmpty actual_arguments.size
    let mut dewraped_argument_decls : Array (_ × BinderInfo × _) := Array.mkEmpty actual_arguments.size
    for i in [:actual_arguments.size] do
      let arg := actual_arguments[i]!
      let arg_type ← inferType arg
      let name := ← arg.fvarId!.getUserName
      let no_recursive_case := (
        pure,
        (name, .default, fun _ : Array _ => pure arg_type)
      )
      let (arg_map, decl) ← forallTelescopeReducing arg_type fun _ arg_goal => do
        -- check whether the argument is of the form
        --   `∀ ..arg_args, ^(cons ..cons_args)`
        let .app (.const ``lift [_]) arg_goal_ul := arg_goal | return no_recursive_case
        let .const arg_goal_ul_fn arg_goal_levels := arg_goal_ul.getAppFn
          | return no_recursive_case
        unless arg_goal_ul_fn == ind_type.full_name do
          return no_recursive_case
        let dewraped_type (previous_constrs : Array Expr) :=
          forallTelescopeReducing arg_type fun arg_args arg_goal => do
            -- We must substitue occurrences of previous arguments of the constructor
            -- with the newly-created arguments. For instance, if we had a constructor
            --   cons_case : (x : Hello) → (y : f x) → motive (cons x y)
            -- it must turn into
            --   cons'_case : (x' : Hello) → (y' : f (El.mk x')) → motive <| El.mk (cons x' y')
            --                                        ^^^^^^^^ =: rewrap_map x'
            let .app (.const ``lift [_]) arg_goal_ul := arg_goal | throwError "impossible?"
            whnfI
            <| (mkAppN · <| ← previous_constrs.zip rewrap_maps
                            |>.mapM fun (constr, map) => map constr)
            <| ← mkLambdaFVars actual_arguments[:i].toArray
            <| ← mkForallFVars arg_args
            <| mkAppN (.const ind_type.inner_name arg_goal_levels)
            <| arg_goal_ul.getAppArgs
        -- `rewrap_map` takes a free variable bound to the unwrap constructor, and
        -- rewraps it. The goal is to use substitute the rewraped version for
        -- occurrences of the plain argument with expressions that only depend on its
        -- unwraped counterpart. See the above example for when this map would be
        -- used.
        let rewrap_map cons' := do
          let type ← inferType cons'
          forallTelescopeReducing type fun a g => do
            mkForallFVars a
            <| ← mkElMk
            <| mkAppN g a
        return (rewrap_map, (name, .default, dewraped_type))
      rewrap_maps := rewrap_maps.push arg_map
      dewraped_argument_decls := dewraped_argument_decls.push decl
    withLocalDecls dewraped_argument_decls f

  def mkElIntoU (e : Expr) : MetaM Expr := do
    let e_type ← inferType e
    let .app (.const ``El [u]) α := e_type
      | throwError "type mismatch, expected type `El α`, got{indentExpr e_type}\nfor `El.intoU e` where `e` is{indentExpr e}"
    return mkApp2 (.const ``El.intoU [u]) α e

  def make_recursor (ind_type : ObjInductiveType) (params : Array Expr) : TermElabM Unit := do
    -- The type of the recursor is
    --   ∀ ..parameters, ∀ motive, ∀ ..constructors, ∀ ..indices, ∀ x, motive indices x
    -- where the type of motive is
    --   ∀ ..indices, ∀ x, U
    let indices := params[ind_type.number_parameters:]
    let parameters := params[:ind_type.number_parameters]
    let motive_level_name ← mkFreshId
    let motive_level := Level.param motive_level_name
    let level_names := motive_level_name :: ind_type.level_names
    let level_vars_for_inner := (.succ motive_level) :: ind_type.level_names.map Level.param
    let motive_type ←
      mkForallFVars indices
      <| .forallE `x (← ind_type.as_expr_type params) (.const ``liftedU [motive_level]) .default
    let x_level ← get_obj_resulting_universe ind_type.toPartialObjInductiveType
    withLocalDecl `motive BinderInfo.implicit motive_type fun motive => do
      withLocalDecl `x BinderInfo.default (← ind_type.as_expr_type params) fun x => do
        let cons_decls ← ind_type.constructors.toArray.mapM fun constructor => do
          let constr_type ←
            constructor.type_instanciated_with_parameters parameters
          forallTelescopeReducing constr_type fun constr_args target => do
            let .app (.const ``lift [_]) target := target
              | throwError "the constructor should produce an object-level type, not{indentExpr target}"
            let target_args := target.getAppArgs
            let target_indices := target_args[ind_type.number_parameters:]
            let partial_constr_value :=
              mkAppN (.const constructor.full_name (ind_type.level_names.map Level.param))
                     parameters
            let constr_value := mkAppN partial_constr_value constr_args
            -- We add, for each recursive argument of the constructor, an additional induction
            -- hypothesis.
            let ih_bounds ← constr_args.filterMapM fun arg => do
              let arg_type ← inferType arg
              forallTelescopeReducing arg_type fun args arg_goal => do
                let .app (.const ``lift [_]) arg_goal_ul := arg_goal | return none
                let .const type_former _ := arg_goal_ul.getAppFn | return none
                let indices_args := arg_goal_ul.getAppArgs[ind_type.number_parameters:]
                if type_former == ind_type.full_name then
                  let ih_type :=
                    ← mkForallFVars args
                    <| .app (.const ``lift [motive_level])
                    <| .app (mkAppN motive indices_args) (mkAppN arg args)
                  return some (
                    (← arg.fvarId!.getUserName).appendAfter "_ih",
                    BinderInfo.default,
                    fun _ : Array _=> pure ih_type
                  )
                else
                  return none
            -- The motive is quantified over constructor arguments which are not parameters.
            -- However, in our expression, the arguments `target_args` might refer free variables
            -- that appear in the constructor arguments as parameters. Hence, we must quantify
            -- universally over every argument *except* parameters, then substitute the remaining
            -- arguments with the actual parameters.
            let constr_case_type ← withLocalDecls ih_bounds fun ih_vars => do
              mkForallFVars constr_args
              <| ← mkForallFVars ih_vars
              <| .app (.const ``lift [motive_level])
              <| .app (mkAppN motive target_indices) constr_value
            let constr_case_type ←
              mkLambdaFVars parameters constr_case_type
            let constr_case_type ← whnfI <| mkAppN constr_case_type parameters
            return (constructor.short_name, BinderInfo.default, fun _ : Array _ => pure constr_case_type)
        withLocalDecls cons_decls fun constructors => do
          trace[Tltt.inductiveₒ.recₒ] m!"constructors = {constructors}"
          -- build goal type
          let mut goal_type := Expr.app (mkAppN motive indices) x
          goal_type := .app (.const ``lift [motive_level]) goal_type
          goal_type ← mkForallFVars #[x] goal_type
          goal_type ← mkForallFVars indices goal_type
          goal_type ← mkForallFVars constructors goal_type
          goal_type ← mkForallFVars #[motive] goal_type
          goal_type ← mkForallFVars parameters goal_type
          let rec_type ← instantiateMVars goal_type
          trace[Tltt.inductiveₒ.recₒ] m!"rec_type.{level_names} = {rec_type}"
          -- build goal value
          let mut goal_value := Expr.const (ind_type.inner_name ++ `rec) level_vars_for_inner
          goal_value := mkAppN goal_value parameters
          goal_value := .app goal_value <| ← forallTelescopeReducing motive_type fun args _ => do
            let truncated_args := args.pop
            let inner_x_type :=
              mkAppN (.const ind_type.inner_name <| ind_type.level_names.map Level.param)
                     (parameters ++ truncated_args)
            let metau := Expr.app (.const ``MetaU.mk [x_level]) inner_x_type
            withLocalDecl `x .default inner_x_type fun x => do
              let unlifted_x := mkApp2 (.const ``El.mk [x_level]) metau x
              let lifted_motive := Expr.app (.const ``lift [motive_level])
                                   <| .app (mkAppN motive truncated_args) unlifted_x
              mkLambdaFVars (truncated_args ++ #[x]) lifted_motive
          let mut constr_by_name : HashMap Name ObjConstructor := {}
          for constructor in ind_type.constructors do
            constr_by_name := constr_by_name.insert constructor.short_name constructor
          trace[Tltt.inductiveₒ.recₒ] m!"goal_value = {goal_value}"
          goal_value := mkAppN goal_value <| ← constructors.mapM fun constructor_case => do
            let constructor := constr_by_name.find! (← constructor_case.fvarId!.getUserName)
            -- `constructor_case` might be an `fvar` `cons` that looks like
            --   cons : (hd : α) → (tl : Hello α) → ^(motive tl) → ^(motive (Hello.cons hd tl))
            -- we must produce a `cons'` whose type is
            --   cons' : (hd' : α) → (tl' : Hello_priv α) → ^(motive (El.mk tl'))
            --                     → ^(motive (El.mk <| Hello_priv.cons hd' tl'))
            -- we have three things to do:
            --  1. dewrap the `tl` argument into, say, `tl'`
            --  2. rewrap it before passing it into its induction hypothesis, ie. `motive tl`
            --     should become `motive (El.mk tl')`
            --  3. change the constructor in the target of the constructor to the underlying,
            --     private counterpart
            -- In the end, we will have the following:
            --   cons : (hd' : α) → (tl' : Hello_priv α) → motive (El.mk tl')
            --                    → motive (El.mk <| Hello_priv.cons hd' tl')
            -- We start by introducing the "dewraped" version of every argument, ie. `hd'` and
            -- `tl'`. Then, we modify the target. Finally, we substitue every remaining
            -- occurrence of `hd` and `tl` in the induction hypothesis + target type by the
            -- dewraped counterpart.
            -- In the grand scheme of things, `arity` is the number of arguments of the
            -- constructor case which are not inductive, that is, it accounts for `hd` and `tl`
            -- in our previous example.
            let arity ← forallTelescopeReducing constructor.type fun pars _ => do
              return pars.size - ind_type.number_parameters
            let constr_type ← constructor_case.fvarId!.getType
            forallTelescopeReducing constr_type fun constr_args _ => do
              let actual_arguments := constr_args[:arity]
              let induction_hypothesis := constr_args[arity:]
              with_dewraped_arguments actual_arguments ind_type fun dewraped_arguments => do
                trace[Tltt.inductiveₒ.recₒ] m!"{← (dewraped_arguments.mapM fun x => inferType x)}"
                let rewraped_arguments ← dewraped_arguments.mapM fun arg => do
                  let type ← inferType arg
                  forallTelescopeReducing type fun arg_args arg_goal => do
                    let .const name _ := arg_goal.getAppFn | return arg
                    unless name == ind_type.inner_name do
                      return arg
                    mkLambdaFVars arg_args
                    <| ← mkElMk
                    <| mkAppN arg arg_args
                let actual_goal :=
                  mkAppN constructor_case
                  <| actual_arguments ++ induction_hypothesis
                let with_ih ←
                  whnfI
                  <| (mkAppN · rewraped_arguments)
                  <| ← mkLambdaFVars actual_arguments
                  <| ← mkLambdaFVars induction_hypothesis actual_goal
                mkLambdaFVars dewraped_arguments with_ih
          goal_value := mkAppN goal_value indices
          goal_value :=
            let metau :=
              .app (.const ``MetaU.mk [x_level])
              <| mkAppN (.const ind_type.inner_name <| ind_type.level_names.map Level.param)
                        params
            .app goal_value <| mkApp2 (.const ``El.intoU [x_level]) metau x
          goal_value ← mkLambdaFVars #[x] goal_value
          goal_value ← mkLambdaFVars indices goal_value
          goal_value ← mkLambdaFVars constructors goal_value
          goal_value ← mkLambdaFVars #[motive] goal_value
          goal_value ← mkLambdaFVars parameters goal_value
          let rec_value ← instantiateMVars goal_value
          trace[Tltt.inductiveₒ.recₒ] m!"rec_value = {rec_value}"
          Lean.Meta.check rec_type
          Lean.Meta.check rec_value
          let def_decl := {
            value := rec_value
            name := ind_type.full_name ++ `recₒ
            levelParams := level_names
            type := rec_type
            hints := .regular <| getMaxHeight (← getEnv) rec_value + 1
            safety := .safe
          }
          let rec_decl := Declaration.defnDecl def_decl
          ensureNoUnassignedMVars rec_decl
          addDecl rec_decl

  def mk_obj_inductive_decl (vars : Array Expr) (view : ObjInductiveView) : TermElabM Unit :=
    withoutSavingRecAppSyntax do
      -- this is just used for sorting universe variables
      let scope_level_names ← getLevelNames
      -- this is the actual list of *all* the explicit universe variables available in the
      -- current scope, ie those declared with `universe`-style declarations, and those declared
      -- using the `.{...}` syntax.
      let all_user_level_names := view.levelNames
      trace[Tltt.inductiveₒ.universes] "scope_level_names = {scope_level_names}, all_user_level_names = {all_user_level_names}"
      -- We make the current syntax reference the current declaration, so that errors are
      -- reported
      withRef view.ref <| withLevelNames all_user_level_names do
        let header ← elab_header view
        with_obj_ind_local_decl header fun params ind_fvar => do
          trace[Tltt.inductiveₒ] "ind_fvar: {ind_fvar}"
          addLocalVarInfo view.declId ind_fvar
          let nb_params ← forallTelescopeReducing header.type fun indices _ =>
            return params.size - indices.size
          let type ← forallTelescopeReducing header.type fun type_indices type_goal => do
            mkForallFVars params
            <| ← whnfI
            <| (mkAppN · params[nb_params:])
            <| ← mkLambdaFVars type_indices type_goal

          let ctors ← withExplicitToImplicit params (elab_constructor ind_fvar params nb_params header)
          let ind_type : PartialObjInductiveType := {
            full_name := header.view.full_name
            short_name := header.view.short_name
            inner_name := mk_obj_private header.view.full_name
            type
            constructors := ctors
          }
          synthesizeSyntheticMVarsNoPostponing
          -- `numExplicitParams` is the number of parameters after having promoted indices to
          -- parameters.
          let numExplicitParams ← fixed_indices_to_params nb_params ind_type ind_fvar
          trace[Tltt.inductiveₒ] "numExplicitParams: {numExplicitParams}"
          let u ← get_resulting_universe_as_sort ind_type
          let univToInfer? ← shouldInferResultUniverse u
          -- we collect additional variables that have been used, but never declared as
          -- parameters (I guess this is some kind of auto-implicit feature?), and add them as
          -- parameters.
          withUsed vars ind_type fun vars => do
            let num_vars := vars.size
            let num_params := num_vars + numExplicitParams
            let ind_type ← update_params vars ind_type
            let ind_type ← if let some univ_to_infer := univToInfer? then
              -- if the universe contains some metavariables, resolve those...
              update_resulting_universe view num_params (← levelMVarToParam ind_type univ_to_infer)
            else
              -- ...otherwise, check that the current definition is universe-coherent
              check_resulting_universes view num_params ind_type
              levelMVarToParam ind_type none
            let used_level_names := collect_level_params_in_inductive ind_type
            let level_params ←
              match sortDeclLevelParams scope_level_names all_user_level_names used_level_names with
              | .error msg => throwError msg
              | .ok level_params => pure level_params
            let params ← params.mapM instantiateMVars
            let ind_type ← replace_ind_fvars_with_consts ind_fvar level_params num_vars
                           num_params ind_type
            let ind_type := {
              ind_type with
              level_names := level_params
              number_parameters := num_params
              : ObjInductiveType
            }
            let inner_ind_type ← ind_type.make_inner_decl
            let inner_decl := Declaration.inductDecl level_params num_params [inner_ind_type] false
            ensureNoUnassignedMVars inner_decl
            addDecl inner_decl
            let u ← get_obj_resulting_universe ind_type.toPartialObjInductiveType
            let ind_type_value ←
              mkAppN (.const ind_type.inner_name <| ind_type.level_names.map Level.param) params
              |> Expr.app (.const ``U.fromType [u])
              |> mkLambdaFVars params
            let ind_type_value ← instantiateMVars ind_type_value
            let definition_val := {
              value := ind_type_value
              name := ind_type.full_name
              levelParams := ind_type.level_names
              type := ← instantiateMVars <| ← mkForallFVars params (.const ``liftedU [u])
              hints := .regular <| getMaxHeight (← getEnv) ind_type_value + 1
              safety := .safe
            }
            let obj_decl := Declaration.defnDecl definition_val
            ensureNoUnassignedMVars obj_decl
            addDecl obj_decl
            for constructor in ind_type.constructors do
              make_constructor_decl ind_type constructor params
            make_recursor ind_type params
            -- mkAuxConstructions view
        -- todo!

  def elab_obj_inductive_view (view : ObjInductiveView) : CommandElabM Unit := do
    let ref := view.ref
    runTermElabM fun vars => Lean.Elab.Term.withDeclName view.full_name do withRef ref do
      applyAttributes view.full_name view.modifiers.attrs
      for constructor_view in view.constructors do
        applyAttributes constructor_view.name constructor_view.modifiers.attrs
      mk_obj_inductive_decl vars view
    register_inductive_type view.full_name view
  
  @[command_elab obj_inductive_decl]
  def elab_obj_inductive_decl : CommandElab := fun stx => do
    let modifiers ← elabModifiers stx[0]
    let declId := stx[2]
    let declSig := stx[3]
    let ctrs := stx[5]
    let range := {
      range := ← getDeclarationRange stx
      selectionRange := ← getDeclarationRange <| getDeclarationSelectionRef stx
    }
    let view ← obj_ind_stx_to_view modifiers stx range declId declSig ctrs
    trace[Tltt.inductiveₒ] "{reprPrec view 0}"
    elab_obj_inductive_view view
end InductiveDecl

end Tltt.Hott

-- namespace examples
-- open Tltt.Hott

-- section
-- inductiveₒ MyList (α : U) : U where
--   | nil : MyList α
--   | cons (hd : α) (tl : MyList α) : MyList α

-- inductiveₒ MyId {α : U} : α → α → U where
--   | refl (x : α) : MyId x x

-- inductiveₒ Natₒ : U where
--   | zero : Natₒ
--   | succ (n : Natₒ) : Natₒ

-- def Natₒ.plus (n m : Natₒ) : Natₒ :=
--   Natₒ.recₒ n (fun _ n_p_m' => succ n_p_m') m

-- inductiveₒ Vecₒ (α : U) : Natₒ → U where
--   | nil : Vecₒ α Natₒ.zero
--   | cons (n : Natₒ) (v : Vecₒ α n) : Vecₒ α (Natₒ.succ n)

-- /-- `BTree n` is a binary tree with `n` nodes. -/
-- inductiveₒ BTree : Natₒ → U where
--   | leaf : BTree Natₒ.zero
--   | node (n m : Natₒ) (left : BTree n) (right : BTree m) : BTree (Natₒ.plus (Natₒ.plus n m) (Natₒ.succ Natₒ.zero))

-- inductiveₒ InfTree : U where
--   | nil : InfTree
--   | node (children : Natₒ → InfTree) : InfTree
-- end

-- -- inductive ListS.{u} (α : Type u) : Nat → Type u where
-- --   | nil : ListS α 0
-- --   | cons {n : Nat} (hd : α) (tl : ListS α n) : ListS α (n+1)

-- -- inductive BTree : Nat → Type _ where
-- --   | nil : BTree 1
-- --   | node {n m : Nat} (left : BTree n) (right : BTree m) : BTree (n+m+1)

-- /-
-- inductive_obj Seq (α : U) : U.{u} where
--                             ^^^^^ this must be replaced by `Type u`
--   | nil : Seq α
--           ^^^ this must be replaced by `Inner`
--   | cons (hd : α) (tl : Seq α) : Seq α
--                         ^^^      ^^^
--                         these must be replaced by `Inner`
-- -/

-- private inductive Seq.Inner (α : U) : Type _ where
--   | nil : Inner α
--   | cons (hd : α) (tl : Inner α) : Inner α

-- def Seq.{u₁} (α : U.{u₁}) : U.{u₁} :=
--   U.fromType <| Seq.Inner α

-- namespace Seq
--   @[match_pattern]
--   def nil.{u} {α : U.{u}} : Seq.{u} α :=
--     El.mk.{u} Inner.nil.{u}

--   @[match_pattern]
--   def cons.{u} {α : U.{u}} (hd : α) (tl : Seq.{u} α) : Seq.{u} α :=
--     El.mk.{u} <| Inner.cons.{u} hd (El.intoU.{u} tl)

--   protected def recₒ.{u, u₁} {α : U.{u₁}} {motive : Seq.{u₁} α → U.{u}} (nil_case : motive nil)
--                      (cons_case : (hd : α) → (tl : Seq.{u₁} α) → motive tl → motive (cons hd tl)) (x : Seq.{u₁} α)
--                      : motive x :=
--     @Inner.rec.{u+1, u₁} α (fun x : Inner α => motive (El.mk x)) nil_case (fun hd tl tl_ih => cons_case hd (El.mk tl) tl_ih) x.intoU

--   @[simp]
--   protected def recₒ.beta.nil.{u, u₁} {α : U.{u₁}} {motive : Seq.{u₁} α → U.{u}} (nil_case : motive nil)
--                              (const_case : (hd : α) → (tl : Seq.{u₁} α) → motive tl → motive (cons hd tl))
--                              : @Seq.recₒ.{u, u₁} α motive nil_case const_case nil = nil_case :=
--     rfl

--   @[simp]
--   protected def recₒ.beta.cons.{u, u₁} {α : U.{u₁}} {motive : Seq.{u₁} α → U.{u}} (nil_case : motive nil)
--                               (const_case : (hd : α) → (tl : Seq.{u₁} α) → motive tl → motive (cons hd tl))
--                               (hd : α) (tl : Seq.{u₁} α)
--                               : @Seq.recₒ.{u, u₁} α motive nil_case const_case (cons hd tl)
--                                 = const_case hd tl (Seq.recₒ (motive := motive) nil_case const_case tl) :=
--     rfl

--   protected def casesOnₒ.{u, u₁} {α : U.{u₁}} {motive : Seq.{u₁} α → U.{u}} (nil_case : motive nil)
--                                   (cons_case : (hd : α) → (tl : Seq.{u₁} α) → motive (cons hd tl))
--                                   (x : Seq.{u₁} α) : motive x :=
--     @Seq.recₒ α motive nil_case (fun hd tl _ => cons_case hd tl) x

--   @[simp]
--   protected def casesOnₒ.beta.nil.{u, u₁} {α : U.{u₁}} {motive : Seq.{u₁} α → U.{u}}
--                                            (nil_case : motive nil)
--                                            (cons_case : (hd : α) → (tl : Seq.{u₁} α) → motive (cons hd tl))
--                                            : @Seq.casesOnₒ.{u, u₁} α motive nil_case cons_case nil
--                                              = nil_case :=
--     rfl

--   @[simp]
--   protected def casesOnₒ.beta.cons.{u, u₁} {α : U.{u₁}} {motive : Seq.{u₁} α → U.{u}}
--                                             (nil_case : motive nil)
--                                             (cons_case : (hd : α) → (tl : Seq.{u₁} α) → motive (cons hd tl))
--                                             (hd : α) (tl : Seq.{u₁} α)
--                                             : @Seq.casesOnₒ.{u, u₁} α motive nil_case cons_case (cons hd tl)
--                                               = cons_case hd tl :=
--     rfl
-- end Seq

-- end examples
end
