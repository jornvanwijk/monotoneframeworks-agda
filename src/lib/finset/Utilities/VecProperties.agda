

module Utilities.VecProperties where

open import Relation.Binary 
open import Relation.Binary.PropositionalEquality 
  hiding (inspect)
open import Relation.Binary.Core 
open import Relation.Nullary

open import Data.Bool hiding (_≟_)
open import Data.Sum  hiding (map)
open import Data.Product hiding (map)
open import Data.Maybe hiding (map ; All)
open import Data.List
open import Data.Fin 
  hiding ( _≤_ ; _<_) 
  renaming (suc to fsuc ; zero to fzero ; pred to fpred)
open import Data.Empty 
open import Data.Nat
open import Data.Unit hiding (_≤_ ; _≟_)
open import Data.Vec 
  renaming (map to vmap ; _∈_ to _∈v_ ; _++_ to _++v_ ; _∷_ to _::_) 
  hiding (drop ; take ; foldl ; foldr)  

open import Level hiding (suc ; zero)

open import Data.Vec.Properties hiding (map-cong)

open import Utilities.FinProperties
open import Utilities.BoolProperties
open import Utilities.ListProperties
open import Utilities.ListsAddition
open import Utilities.Logic




∈∈v : {X : Set} → {n : ℕ} → ∀ x → (v : Vec X n)  → x ∈ toList v → x ∈v v
∈∈v x [] ()
∈∈v x (.x :: v) here = here
∈∈v x (x₁ :: v) (there pr) = there (∈∈v x v pr)


∈∈v2 : {X : Set} → {n : ℕ} → ∀ x → (v : Vec X n)  →  x ∈v v → Σ[ i ∈ Fin n ] lookup i v ≡ x
∈∈v2 x [] ()
∈∈v2 x (.x :: v) here = fzero , refl
∈∈v2 x (x₁ :: v) (there inp) with ∈∈v2 x v inp 
... | o1 , o2  = fsuc o1 , o2
