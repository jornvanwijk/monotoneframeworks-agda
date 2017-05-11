

module Utilities.FinProperties where





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
open import Utilities.BoolProperties
open import Utilities.ListProperties
open import Utilities.ListsAddition
open import Utilities.Logic



allFinList : ∀ n → List (Fin n)
allFinList n = toList (allFin n)

toListC : {X : Set} → {n : ℕ} → (i : X) → (v : Vec X n) 
  → i ∈v v → i ∈ toList v
toListC i ._ here = here
toListC i ._ (there iv) = there (toListC i _ iv)

allFinListComplete : ∀ n → (i : Fin n) → i ∈ allFinList n
allFinListComplete n i = toListC i (allFin n) (∈-allFin i)


convf : {X : Set} → (xs : List X) → Σ[ x ∈ X ] x ∈ xs → Fin (length xs)
convf ._ (proj₁ , here) = fzero 
convf ._ (x , there proj₂) = fsuc (convf _ (x , proj₂))

convb : {X : Set} → (xs : List X) → Fin (length xs) → Σ[ x ∈ X ] x ∈ xs
convb [] ()
convb (x ∷ xs) fzero = x , here
convb (x ∷ xs) (fsuc f) = proj₁ (convb xs f) , there (proj₂ (convb xs f))

convfb : {X : Set} → (xs : List X) → (f : Fin (length xs)) → convf xs (convb xs f) ≡ f
convfb [] ()
convfb (x ∷ xs) fzero = refl
convfb (x ∷ xs) (fsuc f) = cong fsuc (convfb  xs f)

convbf : {X : Set} → (xs : List X) → (xi : Σ[ x ∈ X ] x ∈ xs) → convb xs (convf xs xi) ≡ xi
convbf [] (proj₁ , ())
convbf (x ∷ xs) (.x , here) = refl
convbf (x ∷ xs) (x₁ , there proj₂) with convbf xs (x₁ , proj₂) 
... | o rewrite o = refl

