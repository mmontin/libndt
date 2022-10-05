-- A module consisting of all the dependencies to the standard library used
-- in the project, reexported using "public"

module Dependencies.Imports where

open import Data.Nat public
  using
    (ℕ ; _+_ ; z≤n ; s≤s ; _≥_ ; zero ; suc ; _>_ ; _<_ ; _≤_ ; _∸_ ; _*_)

open import Data.Nat.Show public
  using
    ()
  renaming
    (show to showₙ)

open import Relation.Binary.PropositionalEquality public
  using
    (_≡_ ; refl ; cong ; sym ; trans)
  
open import Function public
  using
    (_∘_ ; id ; const ; constᵣ ; flip ; _|>_ ; case_of_ ; _∘₂_ ; ∣_⟩-_)

open import Data.Unit public
  using
    (⊤ ; tt)

open import Data.Product public
  using
    (Σ-syntax ; _,_ ; ∃ ; _×_ ; proj₁ ; proj₂)

open import Data.Sum public
  using
    (inj₁ ; inj₂ ; _⊎_) public

open import Relation.Nullary public
  using
    (¬_ ; yes ; no)

open import Relation.Unary public
  using
    (Pred ; _⇒_)
  renaming
    (Decidable to Decidableₚ)
    
open import Agda.Primitive public
  using

    (Setω ; lsuc ; _⊔_)

open import Level public
  using
    (Lift ; lift)

open import Relation.Binary public
  using
    (Decidable ; REL)

open import Data.List public
  using
    ()
  renaming
    (List to Listₗ ; [] to []ₗ ; _∷_  to _∷ₗ_)

open import Data.String public
  using
    (String ; _++_ ; fromChar)

open import Data.Char public
  using
    (Char ; toℕ ; fromℕ)
