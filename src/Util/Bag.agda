open import Data.List renaming (_∷_ to _∷L_ ; [] to []L)
open import Util.List
open import Data.Product
open import Data.List.Any
open import Relation.Binary.PropositionalEquality
open import Relation.Binary

module Util.Bag where
  open Membership-≡
  
  -- definition from FiniteSubset library (but using std-lib definition for ∈)
  infixr 5 _:::_
  data NoDupInd {a} {A : Set a} : List A → Set a where
    end : NoDupInd []L
    _:::_ : {xs : List A} → {x : A} → (x ∉ xs) → NoDupInd xs → NoDupInd (x ∷L xs)

  Bag : ∀{a} → Set a → Set a
  Bag A = Σ[ zs ∈ List A ] NoDupInd zs

  [] : ∀{a} → {A : Set a} → Bag A
  [] = ([]L , end)
  
  toList : ∀{a} → {A : Set a} → Bag A → List A
  toList x = proj₁ x

  open import Relation.Nullary.Decidable
  module Auto {a} {A : Set a} ⦃ _≟_ : Decidable (_≡_ {A = A}) ⦄ where
    infixr 5 _::_
    _::_ : (x : A) → {xs : List A} → (nodup : NoDupInd xs) → {p : False (x ∈?[ _≟_ ] xs) } → NoDupInd (x ∷L xs)
    _::_ x {xs} nodup {p} = toWitnessFalse p ::: nodup

    infixr 5 _∷_
    _∷_ : (x : A) → (b : Bag A) → {p : False (x ∈?[ _≟_ ] toList b) } → Bag A 
    _∷_ x (xs , nodup) {p} = x ∷L xs , (_::_ x nodup {p})
