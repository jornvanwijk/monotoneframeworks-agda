{-
contents of this file are from the paper of Denis Firsov et al. Slightly modified to allow universe polymorphism and using membership from Data.List.Any
-}
module Util.Listable where

open import Data.Product hiding (map)
open import Data.List hiding (all)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Nat as ℕ
open import Function
import Level
open import Data.List.Any hiding (index)
open import Relation.Binary
{- set X is lisable if there is a list containing all elements of X -}
open Membership-≡ 
record Listable {α} (A : Set α) : Set α where
  field
    all : List A
    complete : (a : A) → a ∈ all
open import Function.Inverse hiding (_∘_)
open import Data.Sum
open import Util.Product

index : ∀{α} {A : Set α}{as : List A}{a : A} → a ∈ as → ℕ
index (here px) = zero
index (there x₁) = suc (index x₁)


suc≡ : {n m : ℕ} → suc n ≡ suc m → n ≡ m
suc≡ refl = refl 



index≡ : ∀{α} {A : Set α} {as : List A} {a b : A} (p : a ∈ as) (q : b ∈ as) → index p ≡ index q → a ≡ b
index≡ (here refl) (here refl) _ = refl
index≡ (here refl) (there q) ()
index≡ (there p) (here refl) ()
index≡ (there p) (there q) x₁ = index≡ p q (suc≡ x₁)

{- listability implies decidable equality -}
open Listable
Listability→Dec≡ : ∀{α} → {A : Set α} → Listable A → Decidable (_≡_ {A = A})
Listability→Dec≡ ls a b with index (complete ls a) ≟ index (complete ls b)
Listability→Dec≡ ls a b | yes p = yes (index≡ (complete ls a) (complete ls b) p)
Listability→Dec≡ ls a b | no ¬p = no (λ x → ¬p (cong (index ∘ complete ls) x))




open import Data.Vec.Properties
open import Data.Fin using (Fin ; suc ; zero)
open import Data.Bool hiding (_≟_)
open import Data.Vec as 𝕍 hiding (_∈_ ; lookup)
open import Data.Fin.Subset    hiding (_∈_)
open import Data.List.Any
open import Relation.Binary.PropositionalEquality


fin-listable : ∀{n} → Listable (Fin n)
Listable.all fin-listable = 𝕍.toList (allFin _)
Listable.complete fin-listable a = ∈⇒List-∈ (∈-allFin a)
                                                     
--  open import Data.List.Any.Membership
bool-listable : Listable Bool
Listable.all bool-listable = false ∷ true ∷ []
Listable.complete bool-listable false = here refl
Listable.complete bool-listable true = there (here refl)


open import Data.List.Any.Properties 
open import Data.List.Any.Membership as Any-Membership-Properties 
open import Function.Inverse hiding (sym ; _∘_)
open import Function.Equality hiding (Π ; cong ; _∘_ ; flip)
open import Relation.Binary.PropositionalEquality

vec-listable : ∀{a} → {A : Set a} → (n : ℕ) → Listable A → Listable (Vec A n)
vec-listable zero x = record { all = [] ∷ [] ; complete = λ{ [] → here refl} }
all (vec-listable (suc n) x) = Data.List.concatMap (λ a → Data.List.map (a ∷_) (Listable.all (vec-listable n x))) (Listable.all x)
complete (vec-listable {a} (suc n) x) (y ∷ ys) = _⟨$⟩_ {a} {a} {a} {a} (Inverse.to >>=-∈↔) (y , ((Listable.complete x y) , (Inverse.to map-∈↔ ⟨$⟩ (ys , ((Listable.complete (vec-listable n x) ys) , refl)))))

subset-listable : ∀{m} → Listable (Subset m)
subset-listable = vec-listable _ bool-listable


indexF : ∀{α} {A : Set α}{as : List A}{a : A} → a ∈ as → Fin (length as)
indexF (here px) = zero
indexF (there x₁) = suc (indexF x₁)


lookup-listable : ∀{α} {A : Set α} (as : List A) → Fin (length as) → A
lookup-listable [] ()
lookup-listable (x ∷ as) zero = x
lookup-listable (x ∷ as) (suc x₁) = lookup-listable as x₁





open import Util.List
-- hier eerst nog een bag van maken voordat het een inverse vormt.
{-
listable-fin↔ : ∀{a} → {A : Set a} → Listable A → Σ[ n ∈ ℕ ] A ↔ Fin n
listable-fin↔ {a} {A} ls = (length (Listable.all ls)) , (ListIndex↔Fin {xs = Listable.all ls}) Function.Inverse.∘ A↔∈ A ls
-}
