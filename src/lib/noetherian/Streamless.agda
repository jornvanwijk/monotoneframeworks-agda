

module Streamless where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.List
open import Data.Colist renaming (_∈_ to _∈c_)
open import Utilities
open import Coinduction




data Stream (X : Set) : Set where
  _∷_ : (x : X)(xs : ∞ (Stream X)) → Stream X

data _∼_ {X : Set} : Stream X → Stream X → Set where
  ∷∼ : ∀{x xs ys} → ∞ (♭ xs ∼ ♭ ys) → (x ∷ xs) ∼ (x ∷ ys)

refl∼ : ∀{X}{xs : Stream X} → xs ∼ xs
refl∼ {xs = x ∷ xs} = ∷∼ (♯ refl∼)

trans∼ : ∀{X}{xs ys zs : Stream X} → xs ∼ ys → ys ∼ zs → xs ∼ zs
trans∼ (∷∼ p) (∷∼ q) = ∷∼ (♯ trans∼ (♭ p) (♭ q))

_S++_ : {X : Set} → List X → Stream X → Stream X
[] S++ xs = xs
(x ∷ ys) S++ xs = ys S++  (x ∷ ♯ xs)

S++∼ : {X : Set} (acc : List X){xs ys : Stream X} → xs ∼ ys →
       (acc S++ xs) ∼ (acc S++ ys)
S++∼ [] (∷∼ p) = ∷∼ p
S++∼ (x ∷ acc) (∷∼ p) = S++∼ acc (∷∼ (♯ ∷∼ p))

infix 4 _∈S_

data  _∈S_ {X : Set} (x : X) : Stream X → Set where
  here  : ∀ {xs} → x ∈S x ∷ xs
  there : ∀ {y xs} → x ∈S ♭ xs → x ∈S y ∷ xs

data DupS {X : Set} : Stream X → Set where
  duphere  : ∀ {x xs} → x ∈S (♭ xs) → DupS (x ∷ xs)
  dupthere : ∀ {x xs} → DupS (♭ xs) → DupS (x ∷ xs)

Streamless : (X : Set) → Set
Streamless X = (xs : Stream X) → DupS xs



data DupC {X : Set} : Colist X → Set where
  duphere  : ∀ {x xs} → x ∈c (♭ xs) → DupC (x ∷ xs)
  dupthere : ∀ {x xs} → DupC (♭ xs) → DupC (x ∷ xs)


StreamlessS : Set → Set
StreamlessS X = (xs : Colist X) → ¬ DupC xs → Finite xs

