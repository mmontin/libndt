module LNDT where

open import Dependencies.Imports
open import GNDT
open import SpreadAble

-- The specification for linked lndt data types

Σ-LNDT : ∀ {a} → Sig a
Σ-LNDT = `⊤ `⊎ (`A `× `X)

LNDT : ∀ {a} (F : TT)(A : Set a) → Set a
LNDT F A = GNDT Σ-LNDT F A

nil : ∀ {a} {F : TT}{A : Set a} → LNDT F A
nil = ctor (inj₁ (lift tt))

cons : ∀ {a} {F : TT}{A : Set a} → A → LNDT F (F A) → LNDT F A
cons a xs = ctor (inj₂ (a , xs))

pattern [] = ctor (inj₁ (lift tt))
pattern _∷_ a xs = ctor (inj₂ (a , xs))

infixr 3 _∷_

-- Induction principle over lndt data types

lndt-ind : ∀
  {F   : TT} {b}
  (P   : ∀ {a} {A : Set a} → LNDT F A → Set b)
  (P[] : ∀ {a} {A : Set a} → P {A = A} [])
  (f   : ∀ {a} {A : Set a} (x : A) {l} → P l → P (x ∷ l))
  {a} {A : Set a} (x : LNDT F A) → P x
lndt-ind {F} P P[] f x = gndt-ind {Σ = Σ-LNDT} P (λ { (inj₁ (lift tt)) (lift tt) → P[]
                                                    ; (inj₂ (a , x)) (lift tt , px) → f a px }) x

-- The depth of an instance of LNDT
depth : ∀ {a} {F : TT} {A : Set a} → LNDT F A → ℕ
depth = lndt-ind _ 0 (λ _ → suc)

-- All spread-able elements can indeed be spread from F to LNDT F

-- Map function and properties

lndt-map : ∀ {F : TT} → Map F → Map (LNDT F)
lndt-map _   _ []      = []
lndt-map map f (x ∷ v) = f x ∷ lndt-map map (map f) v

lndt-map-cong : ∀ {F : TT} {map : Map F} → MapCongruence map → MapCongruence (lndt-map map)
lndt-map-cong _     _ _ []      _ = refl
lndt-map-cong cgMap f g (x ∷ v) p
  rewrite p x | lndt-map-cong cgMap _ _ v (flip (cgMap f g) p) = refl

lndt-map-comp : ∀ {F : TT} {map : Map F} → MapCongruence map → MapComposition map → MapComposition (lndt-map map)
lndt-map-comp _     _     _ _ []      = refl
lndt-map-comp cgMap cpMap f g (x ∷ s)
  rewrite trans (lndt-map-cong cgMap _ _ s (cpMap f g)) (lndt-map-comp cgMap cpMap _ _ s) = refl

lndt-map-able : ∀ {F : ∀ {a} → Set a → Set a} → MapAble F → MapAble (LNDT F)
lndt-map-able mp = M⟨
    lndt-map (map mp) ,
    lndt-map-cong (map-cong mp) ,
    lndt-map-comp (map-cong mp) (map-comp mp) ⟩

-- Fold functions

lndt-foldr : ∀ {F : TT} → Fold F → Fold (LNDT F)
lndt-foldr _     _ b₀ []      = b₀
lndt-foldr foldr f b₀ (x ∷ v) = f (lndt-foldr foldr (foldr f) b₀ v) x

lndt-foldl : ∀ {F : TT} → Fold F → Fold (LNDT F)
lndt-foldl _     _ b₀ []      = b₀
lndt-foldl foldl f b₀ (x ∷ v) = lndt-foldl foldl (foldl f) (f b₀ x) v

lndt-fold-able : ∀ {F : TT} → FoldAble F → FoldAble (LNDT F)
lndt-fold-able fp = F⟨
    lndt-foldl (foldl fp) ,
    lndt-foldr (foldr fp) ⟩

-- Any predicate transformer

data lndt-any {F : TT} (T : TransPred F) {a b} {A : Set a} (P : Pred A b) : Pred (LNDT F A) b where
  here : ∀ {a x} → P a → lndt-any T P (a ∷ x)
  there : ∀ {a x} → lndt-any T (T P) x → lndt-any T P (a ∷ x)

lndt-dec-any : ∀ {F : TT} {T : TransPred F} → TransDec T → TransDec (lndt-any T)
lndt-dec-any _ _ [] = no (λ ())
lndt-dec-any tdec decP (x ∷ v) with decP x | lndt-dec-any tdec (tdec decP) v
... | yes p  | _      = yes (here p)
... | no  _  | yes q  = yes (there q)
... | no  ¬p | no  ¬q = no (λ {(here p) → ¬p p ; (there q) → ¬q q})

-- All predicate transformer

data lndt-all {F : TT} (T : TransPred F) {a b} {A : Set a} (P : Pred A b) : Pred (LNDT F A) b where
  all[] : lndt-all T P []
  all∷ : ∀ {a x} → P a → lndt-all T (T P) x → lndt-all T P (a ∷ x)

lndt-dec-all : ∀ {F : TT} {T : TransPred F} → TransDec T → TransDec (lndt-all T)
lndt-dec-all _ _ [] = yes all[]
lndt-dec-all tdec decP (x ∷ v) with decP x | lndt-dec-all tdec (tdec decP) v
... | no  ¬p | _      = no λ {(all∷ p _) → ¬p p}
... | yes _  | no  ¬q = no λ {(all∷ _ q) → ¬q q}
... | yes p  | yes q  = yes (all∷ p q)

lndt-any-all-able : ∀ {F : TT} → AnyAllAble F → AnyAllAble (LNDT F)
lndt-any-all-able aa = A⟨
    lndt-any (any aa) ,
    lndt-dec-any (dec-any aa) ,
    lndt-all (all aa) ,
    lndt-dec-all (dec-all aa) ⟩

-- Decidability of equality

lndt-dec-eq : ∀ {F : TT} → DecEq F → DecEq (LNDT F)
lndt-dec-eq _      _   []      []        = yes refl
lndt-dec-eq _      _   []      (_ ∷ _)   = no (λ ())
lndt-dec-eq _      _   (_ ∷ _) []        = no (λ ())
lndt-dec-eq decEqF _≟_ (x ∷ y) (x₁ ∷ y₁) with x ≟ x₁ | lndt-dec-eq decEqF (decEqF _≟_) y y₁
... | yes refl | yes refl = yes refl
... | yes refl | no  ¬q   = no λ {refl → ¬q refl}
... | no  ¬p   | _        = no λ {refl → ¬p refl}

lndt-eq-able : ∀ {F : TT} → EqAble F → EqAble (LNDT F)
lndt-eq-able eq = E⟨ lndt-dec-eq (dec-eq eq) ⟩

lndt-spread-able : ∀ {F : TT} → SpreadAble F → SpreadAble (LNDT F)
lndt-spread-able sp = ⟨
  lndt-fold-able (fold-able sp) ,
  lndt-map-able (map-able sp) ,
  lndt-any-all-able (any-all-able sp) ,
  lndt-eq-able (eq-able sp) ⟩
