

module Examples.Prover where


open import Relation.Binary.PropositionalEquality 
  hiding (inspect)
open import Relation.Binary
open import Relation.Nullary

open import Data.List
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Bool
open import Data.Nat hiding (_⊔_)
open import Data.Fin
open import Data.Fin.Dec

open import Utilities.ListProperties 
open import Utilities.Logic

open import Finiteness
open import Prover

open import Examples.Pauli

{- We have seen in ExamplePauli.agda that proving commutativity of _⋅_
   directly is not sensible as the proof is large and also very
   dependent on the names of the elemnents of Pauli.

  Another idea is to use the the module Data.Fin.Dec after
  establishing the surjection from Fin 4 to Pauli and its inverse 

  (f2p : Fin 4 → Pauli, p2f : Pauli → Fin 4).

  First, we prove the commutativity translated to the Fins: -}
⋅-commDec : Dec ((f₁ f₂ : Fin 4) 
                → f2p f₁ ⋅ f2p f₂ ≡ f2p f₂ ⋅ f2p f₁)
⋅-commDec = all? (λ f₁ → 
        all? (λ f₂ → 
             (f2p f₁ ⋅ f2p f₂) =? (f2p f₂ ⋅ f2p f₁)))
  where
    _=?_ : (p1 p2 : Pauli) → Dec (p1 ≡ p2)
    _=?_ p1 p2 with p1 == p2 
    p1 =? p2 | inj₁ x = yes x
    p1 =? p2 | inj₂ y = no y


{- Then, we can establish the property itself by using the proof that
   inverse of f2p -}
⋅-comm' : ∀ p₁ p₂ → p₁ ⋅ p₂ ≡ p₂ ⋅ p₁
⋅-comm' p1 p2 with ∥-∥-yes ⋅-commDec (p2f p1) (p2f p2) 
... | prf  rewrite fp-inv p1  | fp-inv p2  = prf



{-
 Instead of translating the property to Fins and back we can now 
 use the implemented combinators and prove it directly: -}

PauliLstbl : Listable Pauli
PauliLstbl = listPauli , allPauli

_?=_ : DecEq Pauli
_?=_ = lstblEq PauliLstbl

-- The property is proved by translating its formula in different
-- sytax (Π for ∀, ∃ for Σ)
⋅-comm2 : (p₁ p₂ : Pauli) → p₁ ⋅ p₂ ≡ p₂ ⋅ p₁
⋅-comm2 
  = ∥-∥-yes (Π p₁ ∈ PauliLstbl ∙ (Π p₂ ∈ PauliLstbl ∙ ((p₁ ⋅ p₂) ?= (p₂ ⋅ p₁))))


-- Another example: every element of Pauli has inverse
⋅-id : (p : Pauli) → Σ[ q ∈ Pauli ] p ⋅ q ≡ I
⋅-id 
  = ∥-∥-yes (Π p ∈ PauliLstbl ∙ (∃ q ∈ PauliLstbl ∙ ((p ⋅ q) ?= I)))


{- In some cases, the module Data.Fin.Dec can not be used. 
   If the elements of finite subset defined by some predicate do not have the
   decidable equality then there is no hope to provide a surjection from Fins to
   the elments of a subset (the latter would equality) -}

_=?_ : DecEq Bool
_=?_ = Data.Bool._≟_

BoolLstbl : Listable Bool
BoolLstbl = (true ∷ false ∷ []) , (λ { true → here 
                                     ; false → there here })

{- Let us start by defining a list of functions from Bool to Bool  -}
listB2B : List (Bool → Bool)
listB2B = f1 ∷ f2 ∷ f3 ∷ []
  where
    f1 : Bool → Bool
    f1 _ = true

    f2 : Bool → Bool
    f2 b = if b ∧ b then b else true

    f3 : Bool → Bool
    f3 b = if b then true else true

{- The predicate B2B defines a listable finite subset -}
B2B : (Bool → Bool) → Set
B2B f = f ∈ listB2B 

listableB2B : ListableSubset (Bool → Bool) B2B
listableB2B = listB2B , (λ x i → i) , (λ x i → i)

{- For example, the property we could try to decide automatically if
all elements of the set defined by B2B evaluate always to true. As
previously, we need only to translate the formula into a different
syntax -}
constB2B : (f : Bool → Bool) → {_ : B2B f} → (b : Bool) → f b ≡ true
constB2B 
  = ∥-∥-yes (Π' f ∈ listableB2B ∙ (Π b ∈ BoolLstbl ∙ (f b =? true)))
