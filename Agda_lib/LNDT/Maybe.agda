-- Maybe seen as an instance of LNDT

open import Dependencies.Imports
open import SpreadAble
open import LNDT
open import Null

module LNDT.Maybe where

Maybe : TT
Maybe = LNDT Null

pattern nothing = []
pattern just a = a ∷ []

maybe-complete : ∀ {A : Set} → (x : Maybe A) → x ≡ nothing ⊎ ∃ λ v → x ≡ just v
maybe-complete nothing = inj₁ refl
maybe-complete (just x) = inj₂ (x , refl)

maybe-spread-able : SpreadAble Maybe
maybe-spread-able = lndt-spread-able (null-spread-able)

maybe-map      = map      (map-able     maybe-spread-able)
maybe-map-cong = map-cong (map-able     maybe-spread-able)
maybe-map-comp = map-comp (map-able     maybe-spread-able)
maybe-foldr    = foldr    (fold-able    maybe-spread-able)
maybe-foldl    = foldl    (fold-able    maybe-spread-able)
maybe-size     = size     (fold-able    maybe-spread-able)
maybe-flatten  = flatten  (fold-able    maybe-spread-able)
maybe-show     = show     (fold-able    maybe-spread-able)
maybe-any      = any      (any-all-able maybe-spread-able)
maybe-dec-any  = dec-any  (any-all-able maybe-spread-able)
maybe-all      = all      (any-all-able maybe-spread-able)
maybe-dec-all  = dec-all  (any-all-able maybe-spread-able)
maybe-∈        = _∈_      (any-all-able maybe-spread-able)
maybe-empty    = empty    (any-all-able maybe-spread-able)
maybe-dec-∈    = dec-∈    (any-all-able maybe-spread-able)
maybe-dec-eq   = dec-eq   (eq-able      maybe-spread-able)
