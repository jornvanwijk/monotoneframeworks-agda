module Util.List.All.Properties where 
  open import Data.Nat as ℕ hiding (_≟_)
  open import Data.Product
  open import Data.List as 𝕃
  open import Data.Fin
  open import Data.Fin.Properties
  open import Function
  import Data.Vec as 𝕍
  open 𝕍 hiding (_∈_) 
  open import Relation.Nullary.Decidable
  open import Data.List.Any
  open import Data.List.Any.Properties
  open import Data.Unit renaming (_≟_ to _≟⊤_)
  import Data.List.Any.Membership as Any-Properties
  open Any-Properties
  open import Relation.Binary.PropositionalEquality
  open Membership-≡
  open import Relation.Nullary
  open import Relation.Nullary.Negation
  open import Data.Bool renaming (_≟_ to _≟𝔹_)
  open import Function.Inverse using (Inverse)
  open import Function.Equality using (_⟨$⟩_)
  open import Data.List.All
  open import Relation.Unary using (Decidable)
  open import Util.Product
  open import Data.Bool.Properties
  open import Function.Equivalence using (Equivalence)
  
  All-filter : ∀ {a p} {A : Set a} {P : A → Set p} (f : Decidable {a} {p} {A} P) (xs : List A) → All {a} {p} P (filter (⌊_⌋ ∘ f) xs)
  All-filter _ [] = []
  All-filter f (x ∷ xs) with f x 
  All-filter f (x ∷ xs) | yes p₁ = p₁ ∷ All-filter f xs 
  All-filter f (x ∷ xs) | no ¬p = All-filter f xs

  ∀-elim : ∀ {a p} → {A : Set a} → (P : A → Set p) → (xs : List A) → All P xs → (x : A) → x ∈ xs → P x
  ∀-elim P .[] [] x₁ ()
  ∀-elim P .(x₂ ∷ _) (px ∷ x₁) x₂ (here refl) = px
  ∀-elim P .(_ ∷ _) (px ∷ x₁) x₂ (there x₃) = ∀-elim P _ x₁ x₂ x₃
