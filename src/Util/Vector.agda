module Util.Vector where

open import Data.Fin
open import Function
open import Data.Vec
open import Relation.Binary.PropositionalEquality

{-
these are copied from the standard library; reason: not really sure why, but using op; op-pure; op-⊛ on lookup-morphism does not have the same effect regarding implicit parameters as the code below even though they are defined as such.
-}
lookup-replicate : ∀ {a n} {A : Set a} (i : Fin n) → lookup i ∘ replicate {A = A} ≗ id {A = A}
lookup-replicate zero    = λ _ → refl
lookup-replicate (suc i) = lookup-replicate i

lookup-⊛ : ∀ {a b n} {A : Set a} {B : Set b} i (fs : Vec (A → B) n) (xs : Vec A n) → lookup i (fs ⊛ xs) ≡ (lookup i fs $ lookup i xs)
lookup-⊛ zero    (f ∷ fs) (x ∷ xs) = refl
lookup-⊛ (suc i) (f ∷ fs) (x ∷ xs) = lookup-⊛ i fs xs


