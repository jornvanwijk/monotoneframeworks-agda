

module Noetherian where

open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.List
open import Utilities


data NoethAcc' (X : Set) (xs : List X) : Set where
  stop : Dup xs → NoethAcc' X xs
  ask  : (∀ x → NoethAcc' X (x ∷ xs)) → NoethAcc' X xs

NoethAcc : Set → Set
NoethAcc X = NoethAcc' X []


data NoethAccS' (X : Set) (acc : List X) : Set where
  ask : (∀ x → ¬ x ∈ acc → NoethAccS' X (x ∷ acc)) → NoethAccS' X acc

NoethAccS : Set → Set
NoethAccS X = NoethAccS' X []


_⧹_ : (X : Set) → X → Set
X ⧹ x = Σ[ x' ∈ X ] ¬ x ≡ x'

data NoethSet (X : Set) : Set where
  ask :  (∀ (x : X) → NoethSet (X ⧹ x)) → NoethSet X

data NoethSet' (X : Set)(P : X → Set) : Set where
  ask :  ((x : X) → P x → NoethSet' X (λ y → P y × ¬ x ≡ y)) → NoethSet' X P

data NoethGame' (X : Set) (acc : List X) : Set where
  tell : (x : X) → NoethGame' X (x ∷ acc) → NoethGame' X acc
  ask  : (∀ x → ¬ x ∈ acc → NoethGame' X (x ∷ acc)) → NoethGame' X acc

NoethGame : Set → Set
NoethGame X = NoethGame' X []


data NoethExpose' (X : Set) (acc : List X) : Set where
  stop :  (∀ x → x ∈ acc) → NoethExpose' X acc
  tell :  (x : X) → NoethExpose' X (x ∷ acc) → NoethExpose' X acc
  ask  :  (∀ x → NoethExpose' X (x ∷ acc)) → NoethExpose' X acc

NoethExpose : Set → Set
NoethExpose X = NoethExpose' X []
