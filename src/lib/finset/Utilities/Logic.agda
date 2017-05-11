

module Utilities.Logic where

open import Data.Nat
open import Data.List
open import Data.Empty

open import Relation.Binary.PropositionalEquality hiding ([_] ; inspect)

open import Relation.Binary.Core 
open import Relation.Nullary
open import Data.Empty
open import Data.Unit
open import Data.Bool



DecEq : ∀ X → Set
DecEq X = Decidable (_≡_ {A = X})


DecEqRest : {X : Set} → (P : X → Set) → Set
DecEqRest P = ∀ x1 x2 → P x1 → P x2 → Dec (x1 ≡ x2)


∥_∥ : ∀ {p} → {S : Set p} → Dec S → Set
∥ yes _ ∥  = ⊤
∥ no  _ ∥  = ⊥

∥-∥-prop3 : {S : Set} → (d : Dec S) → ∥ d ∥ → S
∥-∥-prop3 (yes p) tt = p
∥-∥-prop3 (no p) ()

∥-∥-yes : {S : Set} → (d : Dec S) → {d : ∥ d ∥} → S
∥-∥-yes (yes p) {tt} = p
∥-∥-yes (no p) {()}

∥-∥-prop2 : {S : Set} → S → (d : Dec S) → ∥ d ∥ 
∥-∥-prop2 s (yes p) = tt
∥-∥-prop2 s (no ¬p) = ¬p s

p2p3 : {X : Set} → (d : Dec X) → (x : ∥ d ∥) → ∥-∥-prop2 (∥-∥-prop3 d x) d ≡ x
p2p3 (yes p) tt = refl
p2p3 (no ¬p) ()

{-
p3p2 : {X : Set} → (d : Dec X) → (x : X) →  ∥-∥-prop3 d (∥-∥-prop2 x d) ≡ x
p3p2 (yes p) x = {!!}
p3p2 (no ¬p) x = {!!}
-}

∥-∥-prop : {S : Set} → (d : Dec S) → (s₁ s₂ : ∥ d ∥) → s₁ ≡ s₂
∥-∥-prop (yes p) tt tt = refl
∥-∥-prop (no ¬p) () s2


dec2bool : ∀ {p} → {S : Set p} → Dec S → Bool
dec2bool (yes _) = true
dec2bool (no _)  = false



open import Data.Product
open import Data.Sum

prod-eq : {A B : Set} → Decidable (_≡_ {A = A}) → Decidable (_≡_ {A = B}) → Decidable (_≡_ {A = A × B})
prod-eq da db (proj₁ , proj₂) (proj₃ , proj₄) with da proj₁ proj₃ | db proj₂ proj₄ 
prod-eq da db (proj₁ , proj₂) (.proj₁ , .proj₂) | yes refl | yes refl = yes refl
prod-eq da db (proj₁ , proj2) (.proj₁ , proj₄) | yes refl | no ¬p = no (λ pr → ¬p (cong proj₂ pr))
prod-eq da db (proj1 , proj2) (proj₃ , .proj2) | no ¬p | yes refl = no (λ pr → ¬p (cong proj₁ pr))
prod-eq da db (proj₁ , proj2) (proj₃ , proj₄) | no ¬p | no ¬p₁ = no (λ pr → ¬p₁ (cong proj₂ pr))


dsum-eq : {A B : Set} → Decidable (_≡_ {A = A}) → Decidable (_≡_ {A = B}) → Decidable (_≡_ {A = A ⊎ B})
dsum-eq da db (inj₁ x) (inj₁ x₁) with da x x₁ 
dsum-eq da db (inj₁ x) (inj₁ .x) | yes refl = yes refl
dsum-eq da db (inj₁ x) (inj₁ x₁) | no ¬p = no (λ pr → ¬p (cong (λ { (inj₁ z) → z ; (inj₂ _) → x }) pr))
dsum-eq da db (inj₁ x) (inj₂ y) = no (λ { () })
dsum-eq da db (inj₂ y) (inj₁ x) = no (λ { () })
dsum-eq da db (inj₂ y) (inj₂ y₁) with db y y₁ 
dsum-eq da db (inj₂ y) (inj₂ .y) | yes refl = yes refl
dsum-eq da db (inj₂ y) (inj₂ y₁) | no ¬p = no (λ pr → ¬p (cong (λ { (inj₂ z) → z ; (inj₁ _) → y }) pr))


data Inspect {a}{A : Set a}(x : A) : Set a where
  it : (y : A) → x ≡ y → Inspect x

open import Level
inspect : {a : Level}{A : Set a}(x : A) → Inspect x
inspect x = it x refl

data Inspect1 {A : Set₁}(x : A) : Set₁ where
  it : (y : A) → x ≡ y → Inspect1 x

inspect1 : {A : Set₁}(x : A) → Inspect1 x
inspect1 x = it x refl


ex-falso-quodlibet : {p : Set}(x : ⊥) → p
ex-falso-quodlibet ()

Rel' : Set → Set₁
Rel' A = A → A → Set


open import Relation.Binary.HeterogeneousEquality.Core

∥-∥-eq : {A B : Set} → (P₁ : Dec A) → (P₂ : Dec B) → (p₁ : ∥ P₁ ∥) → (p₂ : ∥ P₂ ∥) → p₁ ≅ p₂
∥-∥-eq (yes p) (yes p₁) tt tt = refl
∥-∥-eq (yes p) (no ¬p) p1 ()
∥-∥-eq (no ¬p) d2 () p2
