module Util.Product where

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Product.Pointwise
open import Function.Inverse using (Inverse)
open import Function.Equality using (_⟨$⟩_ ; Π)
≡-on-× : ∀{a b} → {A : Set a} → {B : Set b} → {x z : A} → {y w : B} -> (x , y) ≡ (z , w) → (x ≡ z) × (y ≡ w)
≡-on-× refl = refl , refl


≡×⇒≡ : ∀{a b} → {A : Set a} → {B : Set b} → {x z : A} → {y w : B} -> (x ≡ z) × (y ≡ w) → (x , y) ≡ (z , w)
≡×⇒≡ q = Π.cong (Inverse.to ×-Rel↔≡) q


open import Data.Sum
open import Data.Empty
open import Data.Unit
open import Relation.Nullary
open import Relation.Binary
open import Relation.Nullary.Negation
≠-proj : ∀{a b} → {A : Set a} → {B : Set b} → {x z : A} → {y w : B} → Decidable (_≡_ {A = A}) → Decidable (_≡_ {A = B}) → ¬ (x , y) ≡ (z , w) → (x ≡ z × ¬ (y ≡ w)) ⊎ (¬ x ≡ z × y ≡ w) ⊎ (¬ x ≡ z × ¬ y ≡ w)
≠-proj {_} {_} {A} {B} {x} {z} {y} {w} _≟A_ _≟B_ x₁ with x ≟A z | y ≟B w
≠-proj {a} {b} {A} {B} {x} {z} {y} {w} _≟A_ _≟B_ x₁ | yes p | (yes p₁) = contradiction (≡×⇒≡ (p , p₁)) x₁
≠-proj {a} {b} {A} {B} {x} {z} {y} {w} _≟A_ _≟B_ x₁ | yes p | (no ¬p) = inj₁ (p , ¬p)
≠-proj {a} {b} {A} {B} {x} {z} {y} {w} _≟A_ _≟B_ x₁ | no ¬p | (yes p) = inj₂ (inj₁ (¬p , p))
≠-proj {a} {b} {A} {B} {x} {z} {y} {w} _≟A_ _≟B_ x₁ | no ¬p | (no ¬p₁) = inj₂ (inj₂ (¬p , ¬p₁))

≠-proj′ : ∀{a b} → {A : Set a} → {B : Set b} → {x z : A} → {y w : B} → Decidable (_≡_ {A = A}) → Decidable (_≡_ {A = B}) → ¬ (x , y) ≡ (z , w) → (¬ x ≡ z) ⊎ ¬ (y ≡ w)
≠-proj′ {_} {_} {A} {B} {x} {z} {y} {w} _≟A_ _≟B_ x₁ with x ≟A z | y ≟B w
≠-proj′ {a} {b} {A} {B} {x} {z} {y} {w} _≟A_ _≟B_ x₁ | yes p | (yes p₁) = contradiction (≡×⇒≡ (p , p₁)) x₁
≠-proj′ {a} {b} {A} {B} {x} {z} {y} {w} _≟A_ _≟B_ x₁ | yes p | (no ¬p) = inj₂ ¬p
≠-proj′ {a} {b} {A} {B} {x} {z} {y} {w} _≟A_ _≟B_ x₁ | no ¬p | r = inj₁ ¬p
