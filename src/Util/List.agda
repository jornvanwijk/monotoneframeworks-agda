module Util.List where

open import Data.List 
open import Relation.Binary.PropositionalEquality
open import Function.Inverse using (Inverse ; _↔_ ; _InverseOf_)
open import Function.Equality using (_⟨$⟩_ ; Π)
open import Data.Product
open import Data.Nat
open import Data.Fin
open import Function
open import Data.List.Any
open import Relation.Binary



module _ where
  -- open import Data.List.Any.Membership
  open Membership-≡
  ∈?' : ∀ {a} {A : Set a} → Decidable (_≡_ {A = A}) → Decidable (_∈_ {A = A})
  ∈?' _≟_ x xs = Data.List.Any.any (_≟_ x) xs

  syntax ∈?' _≟_ x xs = x ∈?[ _≟_ ] xs

open import Data.Vec as 𝕍 hiding (_∈_)
lemma : ∀{α} → {A : Set α} → (xs : List A) → (x : Fin (length xs)) → Any (λ section → section ≡ lookup x (fromList xs)) xs
lemma [] ()
lemma (x ∷ xs) zero = here refl
lemma (x ∷ xs) (suc i) = there (lemma xs i)

module ListIndex↔Fin  where
  open Membership-≡ 
  to : ∀ {α} → {A : Set α} → {xs : List A} → Σ[ x ∈ A ] x ∈ xs → Fin (length xs)
  to (x , x∈xs) = index x∈xs

  from : ∀ {α} → {A : Set α} → {xs : List A} → Fin (length xs) → Σ[ x ∈ A ] x ∈ xs
  from {xs = []} ()
  from {xs = x ∷ xs} zero = x , (here refl)
  from {xs = x ∷ xs} (suc i) = let a = from {xs = xs} i in proj₁ a , there (proj₂ a)

  left-inverse' : ∀ {α} → {A : Set α} → {xs : List A} → (z : Σ[ x ∈ A ] x ∈ xs) → from (to z) ≡ z
  left-inverse' {xs = []} (proj₃ , ())
  left-inverse' {xs = x ∷ xs} (.x , here refl) = refl
  left-inverse' {xs = x ∷ xs} (proj₃ , there {y} {ys} proj₄) = cong (λ{ (a , b) → (a , there b)}) (left-inverse' {_} {_} {ys} (proj₃ , proj₄))
  

  right-inverse' : ∀{α} → {A : Set α} → {xs : List A} →  (z : Fin (length xs)) → to {α} {A} {xs} (from {α} {A} {xs} z) ≡ z
  right-inverse' {xs = []} ()
  right-inverse' {xs = x ∷ xs} zero = refl
  right-inverse' {xs = x ∷ xs} (suc p) = cong suc (right-inverse' {xs = xs} p)
  
  ListIndex↔Fin : ∀ {α} → {A : Set α} → {xs : List A} → (Σ[ x ∈ A ] x ∈ xs) ↔ Fin (length xs)
  Inverse.to ListIndex↔Fin = →-to-⟶  to
  Inverse.from ListIndex↔Fin = →-to-⟶ from
  _InverseOf_.left-inverse-of (Inverse.inverse-of ListIndex↔Fin) = left-inverse'
  _InverseOf_.right-inverse-of (Inverse.inverse-of (ListIndex↔Fin {α} {A} {xs})) = right-inverse' {α} {A} {xs}
open ListIndex↔Fin using (ListIndex↔Fin) public

