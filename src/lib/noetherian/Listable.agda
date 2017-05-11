
module Listable where

open import Data.Product hiding (map)
open import Data.List
open import Utilities
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Nat
open import Function

{- set X is lisable if there is a list containing all elements of X -}
Listable : Set → Set
Listable X = Σ[ xs ∈ List X ] ((x : X) → x ∈ xs)

length∈ : {X : Set}{xs : List X}{x : X} → x ∈ xs → ℕ
length∈ (here refl) = zero
length∈ (there p) = suc (length∈ p)

suc≡ : {n m : ℕ} → suc n ≡ suc m → n ≡ m
suc≡ refl = refl

length∈≡ : {X : Set}{xs : List X}{x y : X}(p : x ∈ xs)(q : y ∈ xs) →
           length∈ p ≡ length∈ q → x ≡ y
length∈≡ (here refl) (here refl) r = refl
length∈≡ (here refl) (there q) ()
length∈≡ (there p) (here refl) ()
length∈≡ (there p) (there q) r = length∈≡ p q (suc≡ r)

{- listability implies decidable equality -}
Listable→Dec≡ : {X : Set} → Listable X → DecEq X
Listable→Dec≡ (l , p) x y with length∈ (p x) ≟ length∈ (p y)
Listable→Dec≡ (l , p) x y | yes q = yes (length∈≡ (p x) (p y) q)
Listable→Dec≡ (l , p) x y | no ¬q = no (λ r → ¬q (cong (length∈ ∘ p) r))


