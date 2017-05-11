module Util.List.Any.Properties where 
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


  filter-∈′ : ∀ {a} {A : Set a} (p : A → Bool) (xs : List A) {x} → x ∈ filter p xs → x ∈ xs × p x ≡ true
  filter-∈′ p [] {x} ()
  filter-∈′ p (x ∷ xs) {x₁} x₂ with p x | inspect p x 
  filter-∈′ p (x ∷ xs) {x₁} x₂ | false | Reveal_·_is_.[ eq ] with filter-∈′ p xs x₂
  filter-∈′ p (x ∷ xs) {x₁} x₂ | false | Reveal_·_is_.[ eq ] | proj₁ , proj₂ = (there proj₁) , proj₂
  filter-∈′ p (x ∷ xs) {.x} (here refl) | true | Reveal_·_is_.[ eq ] = (here refl) , eq
  filter-∈′ p (x ∷ xs) {x₁} (there x₂) | true | _ with filter-∈′ p xs x₂
  filter-∈′ p (x₁ ∷ xs) {x} (there x₂) | true | _ | proj₁ , proj₂ = (there proj₁) , proj₂

  filter-∈? : ∀ {a p} {A : Set a} {P : A → Set p} (f : Decidable {a} {p} {A} P) (xs : List A) {x} → x ∈ filter (⌊_⌋ ∘ f) xs → x ∈ xs × P x
  filter-∈? f [] {x} ()
  filter-∈? f (x ∷ xs) {x₁} x₂ with f x
  filter-∈? f (x ∷ xs) {.x} (here refl) | yes p₁ = (here refl) , p₁
  filter-∈? f (x ∷ xs) {x₁} (there x₂) | yes p₁ with filter-∈? f xs x₂
  filter-∈? f (x₁ ∷ xs) {x} (there x₂) | yes p₁ | proj₁ , proj₂ = (there proj₁) , proj₂
  filter-∈? f (x ∷ xs) {x₁} x₂ | no ¬p with filter-∈? f xs x₂
  filter-∈? f (x ∷ xs) {x₁} x₂ | no ¬p | proj₁ , proj₂ = (there proj₁) , proj₂
