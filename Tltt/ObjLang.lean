import Lean
import Lean.Data.Options

open Lean.PrettyPrinter (Unexpander)
open Lean.PrettyPrinter.Delaborator (Delab delab whenNotPPOption)
open Lean.PrettyPrinter.Delaborator.SubExpr (getExpr withAppArg)
open Lean.MonadOptions (getOptions)

section
set_option autoImplicit false
namespace Hott

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

-- prefix:max " ↑ " => lift
prefix:max "^" => lift

-- @[delab app.lift]
-- def delab_lift : Delab := do
--   `(lift oui)
  -- whenNotPPOption (·.get pp.lift.name pp.lift.defValue) do
  --   let e ← getExpr
  --   guard <| e.isAppOfArity' ``lift 1
  --   let arg ← withAppArg delab
  --   `($arg)

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

def B : U :=
  U.fromType Bool

namespace B
  @[match_pattern]
  def true' : B :=
    El.mk true

  @[match_pattern]
  def false' : B :=
    El.mk false

  def elim {P : B → U} (b : B) (t : P true') (f : P false') : P b :=
    match b with
    | ⟨true⟩ => t
    | ⟨false⟩ => f
end B


-- Pi types

def Pi (α : U) (β : α → U) : U :=
  U.fromType ((a : α) → β a)

namespace Pi
  section
  variable {α : U} {β : α → U}
  def lam (f : (a : α) → β a) : Pi α β :=
    El.mk f

  def app (f : Pi α β) (a : α) : β a :=
    f.intoU a

  infixl:50 " @ₒ " => app
  infixr:50 " $ₒ " => app

  instance : CoeFun (Pi α β) (fun _ => (x : α) → β x) where
    coe := app
  end
end Pi

syntax obj_fun_binder := "Λ" <|> "λₒ" <|> "funₒ"
syntax (priority := high) obj_fun_binder ident (":" term)? "=>" term : term
macro_rules
  | `($_:obj_fun_binder $var $[: $type]? => $body) => `(Pi.lam fun $var $[: $type]? => $body)

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
end Pi

-- Arrow type
def Funₒ (α : U) (β : U) : U :=
  Pi α (fun _ => β)

infixr:20 " →ₒ " => Funₒ

instance {α β : U} : CoeFun (α →ₒ β) (fun _ => α → β) where
  coe := Pi.app

-- Sigma types
def Sigma (α : U) (β : α → U) : U :=
  U.fromType (Σ a : α, β a)

namespace Sigma
  @[match_pattern, inline]
  def mk {α : U} {β : α → U} (x : Σ a : α, β a) : Sigma α β :=
    El.mk x

  @[match_pattern, inline]
  def pr₁ {α : U} {β : α → U} (x : Sigma α β) : α :=
    x.intoU.1

  @[match_pattern, inline]
  def pr₂ {α : U} {β : α → U} (x : Sigma α β) : β (pr₁ x) :=
    x.intoU.2

  @[simp]
  def beta_pr₁ {α : U} {β : α → U} (x : α) (y : β x) : pr₁ (mk ⟨x, y⟩) = x := by rfl

  @[simp]
  def beta_pr₂ {α : U} {β : α → U} (x : α) (y : β x) : pr₂ (mk ⟨x, y⟩) = y := by rfl

  @[simp]
  def eta {α : U} {β : α → U} (x : Sigma α β) : mk ⟨pr₁ x, pr₂ x⟩ = x := by rfl
end Sigma

syntax "Σₒ" ident ":" term ", " term : term
macro_rules
  | `(Σₒ $x : $α, $P) => `(Sigma $α (fun $x : $α => $P))

@[app_unexpander Sigma]
def unexpand_sigma : Unexpander
  | `($_ $α fun $x:ident => $β) => ``(Σₒ $x : $α, $β)
  | _ => throw ()

syntax "⟪" term ", " term,+ "⟫" : term
macro_rules
  | `(⟪$left, $right⟫) => `(Sigma.mk ⟨$left, $right⟩)
  | `(⟪$x, $y, $tl,*⟫) => `(⟪$x, ⟪$y, $tl,*⟫⟫)

@[app_unexpander Sigma.mk]
def unexpand_sigma_mk : Unexpander
  | `($_ ⟨$x, $y⟩) => ``(⟪$x, $y⟫)
  | _ => throw ()

-- Coproduct

def Plus (α : U) (β : U) : U :=
  U.fromType (α ⊕ β)
  
infixr:30 " ⊕ₒ " => Plus

@[app_unexpander Plus]
def unexpand_plus : Unexpander
  | `($_ $α $β) => ``($α ⊕ₒ $β)
  | _ => throw ()

namespace Plus
  @[match_pattern]
  def inl {α : U} {β : U} (a : α) : α ⊕ₒ β :=
    El.mk (Sum.inl a)

  @[match_pattern]
  def inr {α : U} {β : U} (b : β) : α ⊕ₒ β :=
    El.mk (Sum.inr b)

  def elim {α : U} {β : U} {P : α ⊕ₒ β → U} (l : (a : α) → P (inl a)) (r : (b : β) → P (inr b))
    (x : α ⊕ₒ β) : P x :=
    match x with
    | ⟨.inl a⟩ => l a
    | ⟨.inr b⟩ => r b
end Plus

-- Product

def Times (α : U) (β : U) : U :=
  Sigma α (fun _ => β)

infixr:35 " ×ₒ " => Times

@[app_unexpander Times]
def unexpand_times : Unexpander
  | `($_ $α $β) => ``($α ×ₒ $β)
  | _ => throw ()

-- Unit

def Unitₒ : U :=
  U.fromType Unit

namespace Unitₒ
  @[match_pattern]
  def point : Unitₒ := ⟨()⟩
end Unitₒ

notation "()ₒ" => Unitₒ.point

@[app_unexpander Unitₒ.point]
def unexpand_unit_point : Unexpander
  | `($_) => ``(()ₒ)

-- Counit

def Emptyₒ : U :=
  U.fromType Empty

namespace Emptyₒ
  def elim {α : U} (x : Emptyₒ) : α :=
    x.intoU.rec
end Emptyₒ

-- Natural numbers

def Natₒ : U :=
  U.fromType Nat
  
namespace Natₒ
  @[match_pattern]
  def zero : Natₒ := ⟨.zero⟩

  @[match_pattern]
  def succ (n : Natₒ) : Natₒ :=
    let m : Nat := n.intoU
    ⟨m + 1⟩

  def elim {P : Natₒ → U} (c₀ : P zero) (cₙ : (n : Natₒ) → P n → P (succ n))
    (n : Natₒ) : P n :=
    let rec natElim {P' : Nat → Type}
      (c₀' : P' 0) (cₙ' : (n' : Nat) → P' n' → P' (n'+1)) (n' : Nat) : P' n' :=
      match n' with
      | 0 => c₀'
      | m'+1 => natElim c₀' cₙ' m' |> cₙ' m'
    natElim c₀ (fun n' p => cₙ (El.mk n') p) n.intoU
end Natₒ


-- Identity type

-- private inductive InnerId {α : Type} (x : α) : α → Type where
--   | refl : InnerId x x

private inductive InnerId.{i} {α : Type i} : α → α → Type i where
  | refl (x : α) : InnerId x x

namespace InnerId
  def elim.{u₁, u₂} {α : Type u₁} {P : (x : α) → (y : α) → InnerId x y → Type u₂}
    (h : (x : α) → P x x (refl x)) (x : α) (y : α) (p : InnerId x y)
    : (P x y p) :=
    match p with
    | .refl _ => h x

  def symm.{i} {α : Type i} (x y : α) (p : InnerId x y) : InnerId y x :=
    match p with
    | .refl _ => .refl _

  def trans.{i} {α : Type i} (x y z : α) (p₁ : InnerId x y) (p₂ : InnerId y z) : InnerId x z :=
    match p₁, p₂ with
    | .refl _, .refl _ => .refl _
end InnerId

def Id.{i} {α : U.{i}} (x y : α) : U.{i} :=
  U.fromType.{i} (InnerId x.intoU y.intoU)

infix:40 " =ₒ " => Id

@[app_unexpander Id]
def unexpand_id : Unexpander
  | `($_ $x $y) => ``($x =ₒ $y)
  | _ => throw ()

namespace Id
  @[match_pattern]
  def refl {α : U} (x : α) : x =ₒ x :=
    ⟨InnerId.refl x.intoU⟩

  def symm {α : U} (x y : α) (p : x =ₒ y) : y =ₒ x := by
    apply El.mk
    apply InnerId.symm
    exact p.intoU

  def inv {α : U} {x y : α} (p : x =ₒ y): y =ₒ x :=
    symm x y p

  postfix:max "⁻¹ " => Id.inv

  @[app_unexpander Id.inv]
  def unexpand_inv : Unexpander
    | `($_ $x) => ``($x⁻¹)
    | _ => throw ()

  def trans {α : U} (x y z : α) (p₁ : x =ₒ y) (p₂ : y =ₒ z) : x =ₒ z := by
    apply El.mk
    apply InnerId.trans <;> apply El.intoU <;> assumption

  @[match_pattern]
  def concat {α : U} {x y z : α} (p₁ : x =ₒ y) (p₂ : y =ₒ z) : x =ₒ z :=
    trans x y z p₁ p₂

  infix:45 " ⬝ " => concat

  @[app_unexpander concat]
  def unexpand_concat : Unexpander
    | `($_ $p₁ $p₂) => ``($p₁ ⬝ $p₂)
    | _ => throw ()

  def elim {α : U} {P : (x : α) → (y : α) → x =ₒ y → U}
           (h : (x : α) → P x x (refl x)) (x : α) (y : α) (p : x =ₒ y) : P x y p := by
    apply El.mk
    apply InnerId.elim (P := fun a b q =>  (P (El.mk a) (El.mk b) (El.mk q)).intoU.intoType)
    intro x
    apply El.intoU
    apply h

  def subst {α : U} {P : α → U} {a b : α} (h₁ : a =ₒ b) : P a → P b := by
    apply Pi.app
    apply Id.elim (P := fun x y _ => P x →ₒ P y)
    intro x
    apply Pi.lam
    exact id
    exact h₁

  def mp {α β : U} (h : α =ₒ β) (a : α) : β :=
    subst (P := fun x => x) h a

  def mpr {α β : U} (h : α =ₒ β) (b : β) : α :=
    mp (symm α β h) b
end Id

end Hott

end
