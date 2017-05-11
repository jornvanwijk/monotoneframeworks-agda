open import Data.List
open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties
open import Data.Product
open import Function.Inverse
open import Data.Fin
open import Algebra
open import Relation.Binary.PropositionalEquality
open CommutativeSemiring commutativeSemiring
open import Algebra.Operations semiring
open import Function.Equality using (_⟨$⟩_)  
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Binary


module Util.BoundedList where

  data BoundedList' {a} (A : Set a) (k : ℕ) : ℕ → Set a where
    nil : BoundedList' A k ℕ.zero
    cons' : {i : ℕ} → A → BoundedList' A k i → .(suc i Data.Nat.≤ k) → BoundedList' A k (suc i)

  BoundedList : ∀{a} → (A : Set a) → (k : ℕ) → Set a
  BoundedList A k = Σ[ n ∈ ℕ ] BoundedList' A k n

  dropLast' : ∀{a} → {A : Set a} → {k n : ℕ} → BoundedList' A k (suc n) → BoundedList' A k n
  dropLast' {n = ℕ.zero} (cons' x x₁ x₂) = nil
  dropLast' {n = suc n} (cons' x x₁ x₂) = cons' x (dropLast' x₁) (≤⇒pred≤ (suc (suc n)) _ x₂)

  dropLast :  ∀{a} → {A : Set a} → {k : ℕ} → BoundedList A k → BoundedList A k
  dropLast (zero , proj₂) = ℕ.zero , proj₂
  dropLast (suc n , proj₂) = n , dropLast' proj₂

  cons :  ∀{a} → {A : Set a} → {k : ℕ} → A → BoundedList A k → BoundedList A k
  cons {k = k} a (n , xs) with suc n Data.Nat.≤? k
  cons {k = k} a (n , xs) | yes p = (suc n) , (cons' a xs p)
  cons {k = k} a (zero , nil) | no ¬p = (ℕ.zero , nil)
  cons {k = k} a (suc n , cons' x xs x₁) | no ¬p = (suc n , cons' a (dropLast' (cons' x xs x₁)) x₁)

  open import Relation.Binary.List.Pointwise renaming (decidable-≡ to decidable-≡-pointwise)


  decidable-≡' : ∀{a k n} {A : Set a} → Decidable {A = A} _≡_ → Decidable {A = BoundedList' A k n} _≡_
  decidable-≡' _≟_ nil nil = yes _≡_.refl
  decidable-≡' _≟_ (cons' x xs xp) (cons' y ys yp) with x ≟ y
  decidable-≡' _≟_ (cons' x xs xp) (cons' .x ys yp) | yes _≡_.refl with decidable-≡' _≟_ xs ys
  decidable-≡' _≟_ (cons' x xs xp) (cons' .x .xs yp) | yes _≡_.refl | yes _≡_.refl = yes _≡_.refl
  decidable-≡' _≟_ (cons' x xs xp) (cons' .x ys yp) | yes _≡_.refl | no ¬p = no (λ{ _≡_.refl → ¬p _≡_.refl})
  decidable-≡' _≟_ (cons' x xs xp) (cons' y ys yp) | no ¬p = no (λ{ _≡_.refl → ¬p _≡_.refl})


  decidable-≡ : ∀{a k} {A : Set a} → Decidable {A = A} _≡_ → Decidable {A = BoundedList A k} _≡_
  decidable-≡ _≟_ (i , xs) (j , ys) with i ≟ℕ j
  decidable-≡ _≟_ (i , xs) (.i , ys) | yes _≡_.refl with decidable-≡' _≟_ xs ys
  decidable-≡ _≟_ (i , xs) (.i , .xs) | yes _≡_.refl | yes _≡_.refl = yes _≡_.refl
  decidable-≡ _≟_ (i , xs) (.i , ys) | yes _≡_.refl | no ¬p = no (λ{ _≡_.refl → ¬p _≡_.refl})
  decidable-≡ _≟_ (i , xs) (j , ys) | no ¬p = no (λ{ _≡_.refl → ¬p _≡_.refl})

  syntax decidable-≡ _≟_ a b = a ≟⟨ _≟_ ⟩ b


  open import Data.String
  showBL′ : ∀{a k n} {A : Set a} → (showA : A → String) → BoundedList' A k n → String
  showBL′ showA nil = ""
  showBL′ showA (cons' x x₁ x₂) = showA x Data.String.++ ", " Data.String.++ showBL′ showA x₁

  showBL : ∀{a k} {A : Set a} → (showA : A → String) → BoundedList A k → String
  showBL f (n , bl) = showBL′ f bl
  
  open import Data.Vec
  allBoundedLists' : ∀{a k n} → {A : Set a} → Σ[ n ∈ ℕ ] A ↔ Fin n → List (BoundedList' A k n)
  allBoundedLists' {a} {k} {ℕ.zero} (m , A↔) = Data.List.[ nil ]
  allBoundedLists' {a} {k} {suc n} (m , A↔) with suc n Data.Nat.≤? k
  allBoundedLists' {a} {k} {suc n} (m , A↔) | yes p = Data.List.concat (Data.List.map (λ x → Data.List.map (λ xs → cons' (Inverse.from A↔ ⟨$⟩ x) xs p) (allBoundedLists' {a} {k} {n} (m , A↔))) (Data.Vec.toList (allFin m)))
  allBoundedLists' {a} {k} {suc n} (m , A↔) | no ¬p = []

  

  allBoundedLists : ∀{a k} → {A : Set a} → Σ[ n ∈ ℕ ] A ↔ Fin n → List (BoundedList A k)
  allBoundedLists {a} {k} (m , A↔) = Data.List.concat (Data.List.map (λ x → Data.List.map (λ xs → (toℕ x , xs)) (allBoundedLists' {a} {k} {toℕ x} (m , A↔))) (Data.Vec.toList (allFin (suc k))))
  
  example : List (BoundedList (Fin 2) 2)
  example = allBoundedLists (2 , Function.Inverse.id)

  postulate
    isBijectiveToFin : ∀{a k} → {A : Set a} → Σ[ n ∈ ℕ ] A ↔ Fin n → Σ[ r ∈ ℕ ] BoundedList A k ↔ Fin r
