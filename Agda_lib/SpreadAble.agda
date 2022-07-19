-- Elements that can be spread for a certain TT F to LNDT F

module SpreadAble where

open import Dependencies.Imports

-- Type Transformers

TT : Set₁
TT = Set → Set

-- MapAble type constructors

Map : TT → Set₁
Map F = {A B : Set} → (A → B) → F A → F B

-- Properties of MapAbles : congruence and composition

MapCongruence : ∀ {F : TT} → Map F → Set₁
MapCongruence map = ∀ {A B : Set} (f g : A → B) x →
  (∀ x → f x ≡ g x) → map f x ≡ map g x

MapComposition : ∀ {F : TT} → Map F → Set₁
MapComposition map = ∀ {A B C : Set} (f : A → B) (g : B → C) x
  → map (g ∘ f) x ≡ (map g ∘ map f) x

record MapAble (F : TT) : Set₁ where
  constructor M⟨_,_,_⟩
  field
    map      : Map F
    map-cong : MapCongruence map
    map-comp : MapComposition map

open MapAble public

-- FoldAble type constructors

Fold : TT → Set₁
Fold F = ∀ {A : Set}{T : Set → Set} → {{ _ : Applicative T }} → F (T A) → T (F A)

-- A transformation of predicate over a type constructor (used later for Any and All)

TransPred : TT → Setω
TransPred F = ∀ {b}{A : Set} → Pred A b → Pred (F A) b

-- The preservation of decidability through TransPred

TransDec : ∀ {F : TT} → TransPred F → Setω
TransDec TransPF = ∀ {b} {A : Set} {P : Pred A b} → Decidableₚ P → Decidableₚ (TransPF P)

record AnyAllAble (F : TT) : Setω where
  constructor A⟨_,_,_,_⟩
  field
    any     : TransPred F
    dec-any : TransDec  any
    all     : TransPred F
    dec-all : TransDec  all
    
  _∈_ : ∀ {A : Set} → REL A (F A) _
  _∈_ x = any (x ≡_)

  empty : {A : Set} → Pred (F A) _
  empty l = ∀ {x} → ¬ x ∈ l

  dec-∈ :{A : Set} → Decidable {A = A} _≡_ → Decidable _∈_
  dec-∈ dec-≡ = dec-any ∘ dec-≡

open AnyAllAble public

-- Type constructors that preserve decidability of equality

DecEq : TT → Set₁
DecEq F = ∀ {A : Set} → Decidable {A = A} _≡_ → Decidable {A = F A} _≡_

record EqAble (F : TT) : Set₁ where
  constructor E⟨_⟩
  field
    dec-eq : DecEq F

open EqAble public

-- All spread-able properties in a single record

record SpreadAble (F : TT) : Setω where
  constructor ⟨_,_,_,_⟩
  field
    fold-able    : Fold       F
    map-able     : MapAble    F
    any-all-able : AnyAllAble F
    eq-able      : EqAble     F
    
open SpreadAble public


