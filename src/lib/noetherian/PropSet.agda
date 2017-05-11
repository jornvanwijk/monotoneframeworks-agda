

module PropSet where

open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (map)
open import Relation.Binary
open import Relation.Nullary
open import Data.List
open import Utilities
open import Coinduction
open import Data.Nat renaming (_+_ to _+N_)
open import Data.Sum renaming (_⊎_ to _+_) hiding (map)
open import Data.Empty
open import Function
open import Data.Bool
open import Data.Unit hiding (_≤_)
open import Noetherian
open import NoethRels
open import Listable
open import Bounded


NoethExposeProp : (X : Set) → isProp X → NoethExpose X
NoethExposeProp X p  = ask (λ x → stop (λ x' → here (p {x'} {x}) ))


ListableProp→LEM : ((X : Set) → isProp X → Listable X)
  → (X : Set) → isProp X → X + ¬ X
ListableProp→LEM d X p with d X p 
ListableProp→LEM d X p | [] , proj₂ = inj₂ (λ x → h (proj₂ x))
  where
    h : {X : Set} → {x : X} → x ∈ [] → ⊥ 
    h ()
ListableProp→LEM d X p | x ∷ proj₁ , proj₂ = inj₁ x


  
  
