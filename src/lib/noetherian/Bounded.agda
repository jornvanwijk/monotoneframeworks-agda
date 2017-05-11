


module Bounded where

open import Data.Product hiding (map)
open import Data.List
open import Utilities
open import Data.Nat


Bounded : Set → Set
Bounded X = Σ[ n ∈ ℕ ] ((xs : List X) → n ≤ length xs → Dup xs)
