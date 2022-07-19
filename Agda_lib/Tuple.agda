-- The type constructors of homogeneous tuples

module Tuple where

open import Dependencies.Imports
open import SpreadAble

-- The tuple type constructors family

Tuple : ℕ → TT
Tuple zero      = id
Tuple (suc n) A = A × Tuple n A

-- Tuple n is spread-able for any n

tuple-map : ∀ n → Map (Tuple n)
tuple-map zero              = id
tuple-map (suc n) f (a , t) = f a , tuple-map n f t

tuple-cmp-map : ∀ n → MapComposition (tuple-map n)
tuple-cmp-map zero    _ _ _       = refl
tuple-cmp-map (suc n) f g (a , t) = cong (g (f a) ,_) (tuple-cmp-map n f g t)

tuple-cng-map : ∀ n → MapCongruence (tuple-map n)
tuple-cng-map zero _ _                          = _|>_
tuple-cng-map (suc n) f g (a , t) p rewrite p a = cong (g a ,_) (tuple-cng-map n f g t p)

tuple-foldr : ∀ n → Fold (Tuple n)
tuple-foldr zero                 = id
tuple-foldr (suc n) f b₀ (a , t) = f (tuple-foldr n f b₀ t) a

tuple-foldl : ∀ n → Fold (Tuple n)
tuple-foldl zero                 = id
tuple-foldl (suc n) f b₀ (a , t) = tuple-foldl n f (f b₀ a) t

tuple-any : ∀ n → TransPred (Tuple n)
tuple-any zero              = id
tuple-any (suc n) P (a , t) = P a ⊎ tuple-any n P t

tuple-dec-any : ∀ n → TransDec (tuple-any n)
tuple-dec-any zero = id
tuple-dec-any (suc n) decP (a , t) with decP a | tuple-dec-any n decP t
... | yes p  | _      = yes (inj₁ p)
... | no  ¬p | yes q  = yes (inj₂ q)
... | no  ¬p | no  ¬q = no (λ {(inj₁ p) → ¬p p ; (inj₂ q) → ¬q q})

tuple-all : ∀ n → TransPred (Tuple n)
tuple-all zero = id
tuple-all (suc n) P (a , t) = P a × tuple-all n P t

tuple-dec-all : ∀ n → TransDec (tuple-all n)
tuple-dec-all zero = id
tuple-dec-all (suc n) decP (a , t) with decP a | tuple-dec-all n decP t
... | yes p  | yes q  = yes (p , q)
... | yes _  | no  ¬q = no  (¬q ∘ proj₂)
... | no  ¬p | _      = no  (¬p ∘ proj₁)

tuple-dec-eq : ∀ n → DecEq (Tuple n)
tuple-dec-eq zero = id
tuple-dec-eq (suc n) _≟_ (a , t) (a₁ , t₁) with a ≟ a₁ | tuple-dec-eq n _≟_ t t₁
... | yes refl | yes refl = yes refl
... | yes refl | no ¬q = no (λ {refl → ¬q refl})
... | no ¬p | _ = no (λ {refl → ¬p refl})

tuple-spread-able : ∀ n → SpreadAble (Tuple n)
tuple-spread-able n = ⟨
  F⟨ tuple-foldl n , tuple-foldr n ⟩ ,
  M⟨ tuple-map n , tuple-cng-map n , tuple-cmp-map n ⟩ ,
  A⟨ tuple-any n , tuple-dec-any n , tuple-all n , tuple-dec-all n ⟩ ,
  E⟨ tuple-dec-eq n ⟩ ⟩

tuple-size : ∀ {A : Set} {n} → Tuple n A → ℕ
tuple-size {n = n} = size (fold-able (tuple-spread-able n))

tuple-size-prop : ∀ {A : Set} {n} → (e : Tuple n A) → tuple-size {n = n} e ≡ suc n
tuple-size-prop {n = zero} _ = refl
tuple-size-prop {n = suc _} = (cong suc) ∘ tuple-size-prop ∘ proj₂

tuple-flatten : ∀ {A : Set} {n} → Tuple n A → Listₗ A
tuple-flatten {n = n} = flatten (fold-able (tuple-spread-able n))

tuple-show : ∀ {A : Set} {n} → (A → String) → Tuple n A → String
tuple-show {n = n} = show (fold-able (tuple-spread-able n))

tuple-∈ : ∀ {A : Set} {n} → A → Tuple n A → Set
tuple-∈ {n = n} = _∈_ (any-all-able (tuple-spread-able n))

tuple-empty : ∀ {A : Set} {n} → Tuple n A → Set
tuple-empty {n = n} = empty (any-all-able (tuple-spread-able n))
