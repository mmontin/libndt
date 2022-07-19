-- The Null type constructor

module Null where

open import SpreadAble
open import Dependencies.Imports
open import Data.Empty

-- The Null type constructor

Null : TT
Null _ = ⊥

-- Null is spread-able

null-spread-able : SpreadAble Null
null-spread-able = ⟨
  F⟨ (λ _ _ ()) , (λ _ _ ()) ⟩ ,
  M⟨ (λ _ ()) , (λ _ _ ()) , (λ _ _ ()) ⟩ ,
  A⟨ (λ _ ()) , (λ _ ()) , (λ _ ()) , (λ _ ()) ⟩ ,
  E⟨ (λ _ _ ()) ⟩ ⟩
