namespace Hott

-- Universe setup
--
-- The object language universe hierarchy is `U.{i}`. If `α : U.{i}`, `↑α : Type i`, where `↑` is
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
  
abbrev U.{i} : Type (i+1) := El Ty.{i}

private def U.fromType.{i} (α : Type i) : U.{i} :=
  El.mk (MetaU.mk α)

def lift.{i} (α : U.{i}) : Type i := El α.intoU

-- prefix:max " ↑ " => lift
prefix:max "^" => lift

instance : CoeSort U.{i} (Type i) where
  coe α := ^α

-- Boolean type

def B : U :=
  U.fromType Bool

namespace B
  def true' : B :=
    El.mk true

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

  infixl:50 " @∘ " => app
  infixr:50 " $∘ " => app

  instance : CoeFun (Pi α β) (fun _ => (x : α) → β x) where
    coe := app
  end
end Pi

syntax (priority := high) "Λ" ident "=>" term : term
syntax (priority := high) "Λ" ident ":" term "=>" term : term
macro_rules
  | `(Λ $x => $b) => `(Pi.lam fun $x => $b)
  | `(Λ $x : $t => $b) => `(Pi.lam fun $x : $t => $b)

syntax "Π∘" ident " : " term ", " term : term
macro_rules
  | `(Π∘ $x : $α, $P) => `(Pi $α (fun $x : $α => $P))

macro "(" x:ident " : " α:term ") →∘ " P:term : term => `(Pi $α (fun $x => $P))

-- Arrow type
def Arrow (α : U) (β : U) : U :=
  Pi α (fun _ => β)

infixr:20 " →∘ " => Arrow

instance : CoeFun (α →∘ β) (fun _ => α → β) where
  coe := Pi.app

-- Sigma types
def Sigma (α : U) (β : α → U) : U :=
  U.fromType (Σ a : α, β a)

namespace Sigma
  def mk {α : U} {β : α → U} (x : Σ a : α, β a) : Sigma α β :=
    El.mk x

  def pr₁ {α : U} {β : α → U} (x : Sigma α β) : α :=
    x.intoU.1

  def pr₂ {α : U} {β : α → U} (x : Sigma α β) : β (pr₁ x) :=
    x.intoU.2
end Sigma

syntax "Σ∘" ident ":" term ", " term : term
macro_rules
  | `(Σ∘ $x : $α, $P) => `(Sigma $α (fun $x : $α => $P))

-- Coproduct

def Plus (α : U) (β : U) : U :=
  U.fromType (α ⊕ β)
  
infixr:30 " ⊕∘ " => Plus

namespace Plus
  def inl {α : U} {β : U} (a : α) : α ⊕∘ β :=
    El.mk (Sum.inl a)

  def inr {α : U} {β : U} (b : β) : α ⊕∘ β :=
    El.mk (Sum.inr b)

  def elim {α : U} {β : U} {P : α ⊕∘ β → U}
    (l : (a : α) → P (inl a)) (r : (b : β) → P (inr b))
    (x : α ⊕∘ β) : P x :=
    match x with
    | ⟨.inl a⟩ => l a
    | ⟨.inr b⟩ => r b
end Plus

-- Unit

def One : U :=
  U.fromType Unit

namespace One
  def point : One := ⟨()⟩
end One

-- Counit

def Zero : U :=
  U.fromType Empty

namespace Zero
  def elim {α : U} (x : Zero) : α :=
    x.intoU.rec
end Zero

-- Natural numbers

def N : U :=
  U.fromType Nat
  
namespace N
  def zero : N := ⟨.zero⟩

  def succ (n : N) : N :=
    let m : Nat := n.intoU
    ⟨m + 1⟩

  def elim {P : N → U} (c₀ : P zero) (cₙ : (n : N) → P n → P (succ n))
    (n : N) : P n :=
    let rec natElim {P' : Nat → Type}
      (c₀' : P' 0) (cₙ' : (n' : Nat) → P' n' → P' (n'+1)) (n' : Nat) : P' n' :=
      match n' with
      | 0 => c₀'
      | m'+1 => natElim c₀' cₙ' m' |> cₙ' m'
    natElim c₀ (fun n' p => cₙ (El.mk n') p) n.intoU
end N

-- instance : OfNat ↑N n where
--   ofNat := ⟨n⟩

-- Identity type

-- private inductive InnerId {α : Type} (x : α) : α → Type where
--   | refl : InnerId x x

private inductive InnerId.{i} {α : Type i} : α → α → Type i where
  | refl (x : α) : InnerId x x

namespace InnerId
  def elim.{i} {α : Type i} {P : (x : α) → (y : α) → InnerId x y → Type i}
    (h : (x : α) → P x x (refl x)) (x : α) (y : α) (p : InnerId x y)
    : (P x y p) :=
    match p with
    | .refl _ => h _

  def symm.{i} {α : Type i} (x y : α) (p : InnerId x y) : InnerId y x :=
    match p with
    | .refl _ => .refl _

  def trans.{i} {α : Type i} (x y z : α) (p₁ : InnerId x y) (p₂ : InnerId y z) : InnerId x z :=
    match p₁, p₂ with
    | .refl _, .refl _ => .refl _
end InnerId

def Id.{i} {α : U.{i}} (x y : α) : U.{i} :=
  U.fromType.{i} (InnerId x.intoU y.intoU)

infix:40 " =∘ " => Id

namespace Id
  def refl {α : U} (x : α) : x =∘ x :=
    ⟨InnerId.refl x.intoU⟩

  def symm {α : U} (x y : α) (p : x =∘ y) : y =∘ x := by
    apply El.mk
    apply InnerId.symm
    exact p.intoU

  def inv {α : U} {x y : α} (p : x =∘ y): y =∘ x :=
    symm x y p

  def trans {α : U} (x y z : α) (p₁ : x =∘ y) (p₂ : y =∘ z) : x =∘ z := by
    apply El.mk
    apply InnerId.trans <;> apply El.intoU <;> assumption

  def concat {α : U} {x y z : α} (p₁ : x =∘ y) (p₂ : y =∘ z) : x =∘ z :=
    trans x y z p₁ p₂

  infix:45 " ⬝ " => concat

  def elim {α : U} {P : (x : α) → (y : α) → x =∘ y → U}
    (h : (x : α) → P x x (refl x)) (x : α) (y : α) (p : x =∘ y)
    : P x y p := by
    apply El.mk
    apply InnerId.elim (P := fun a b q =>  (P (El.mk a) (El.mk b) (El.mk q)).intoU.intoType)
    intro x
    apply El.intoU
    apply h
end Id

postfix:max " ⁻¹ " => Id.inv

end Hott
