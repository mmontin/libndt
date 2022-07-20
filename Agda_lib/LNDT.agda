module LNDT where

open import Dependencies.Imports
open import SpreadAble

-- The specification for linked lndt data types

rec : ∀ {a} (F : TT) (A : Set a) → ℕ → Set a
rec F A zero = Lift _ ⊤
rec F A (suc n) = A × rec F (F A) n

-- XXX: `rec` very obviously inherit whatever structure that `F` has
-- which is also true for ‵⊤` and which is preserved by product `×`.
-- THIS IS WHAT SpreadAble IS!

record LNDT {a} (F : TT) (A : Set a) : Set a where
  constructor [_]#_
  field
    -- The depth of an instance of LNDT
    depth : ℕ
    values : rec F A depth

open LNDT public

nil : ∀ {a}{F : TT}{A : Set a} → LNDT F A
nil = [ 0 ]# (lift tt)

cons : ∀ {a}{F : TT}{A : Set a} → A → LNDT F (F A) → LNDT F A
cons a xs = [ suc (depth xs) ]# (a , values xs)

pattern [] = [ 0 ]# (lift tt)
pattern _∷_ a xs = [ suc _ ]# (a , xs)

infixr 3 _∷_

-- Induction principle over lndt data types

lndt-ind : ∀
  {F   : TT} {b}
  (P   : ∀ {a} {A : Set a} → LNDT F A → Set b)
  (P[] : ∀ {a} {A : Set a} → P {A = A} [])
  (f   : ∀ {a} {A : Set a} (x : A) {l} → P l → P (cons x l))
  {a} {A : Set a} (x : LNDT F A) → P x
lndt-ind P P[] f [] = P[]
lndt-ind P P[] f (a ∷ vs) = f a (lndt-ind P P[] f ([ _ ]# vs))

-- All spread-able elements can indeed be spread from F to LNDT F

-- Map function and properties
lndt-map : ∀ {F : TT} → Map F → Map (LNDT F)
lndt-map map f [] = []
lndt-map map f (x ∷ v) = cons (f x) (lndt-map map (map f) ([ _ ]# v))

{-# TERMINATING #-}
-- This TERMINATING could be avoided through a helper function explicitly defined by induction over `depth`
lndt-map-cong : ∀ {F : TT} {map : Map F} → MapCongruence map → MapCongruence (lndt-map map)
lndt-map-cong _     _ _ []      _ = refl
lndt-map-cong cgMap f g (x ∷ v) p
  rewrite p x | lndt-map-cong cgMap _ _ ([ _ ]# v) (flip (cgMap f g) p) = refl

lndt-map-comp : ∀ {F : TT} {map : Map F} → MapCongruence map → MapComposition map → MapComposition (lndt-map map)
lndt-map-comp _     _     _ _ []      = refl
lndt-map-comp cgMap cpMap f g (x ∷ s)
  rewrite trans (lndt-map-cong cgMap _ _ ([ _ ]# s) (cpMap f g)) (lndt-map-comp cgMap cpMap _ _ ([ _ ]# s)) = refl

lndt-map-able : ∀ {F : ∀ {a} → Set a → Set a} → MapAble F → MapAble (LNDT F)
lndt-map-able mp = M⟨
    lndt-map (map mp) ,
    lndt-map-cong (map-cong mp) ,
    lndt-map-comp (map-cong mp) (map-comp mp) ⟩

-- Fold functions

lndt-foldr : ∀ {F : TT} → Fold F → Fold (LNDT F)
lndt-foldr _     _ b₀ []      = b₀
lndt-foldr foldr f b₀ (x ∷ v) = f (lndt-foldr foldr (foldr f) b₀ ([ _ ]# v)) x

lndt-foldl : ∀ {F : TT} → Fold F → Fold (LNDT F)
lndt-foldl _     _ b₀ []      = b₀
lndt-foldl foldl f b₀ (x ∷ v) = lndt-foldl foldl (foldl f) (f b₀ x) ([ _ ]# v)

lndt-fold-able : ∀ {F : TT} → FoldAble F → FoldAble (LNDT F)
lndt-fold-able fp = F⟨
    lndt-foldl (foldl fp) ,
    lndt-foldr (foldr fp) ⟩

-- XXX: dropped the others: same general idea applies
