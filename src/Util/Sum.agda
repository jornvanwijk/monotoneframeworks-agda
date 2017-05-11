
open import Data.Sum
open import Data.Empty
open import Relation.Nullary

module Util.Sum where

⊎-elim-left : ∀{a b} → {A : Set a} → {B : Set b} → A ⊎ B → ¬ A → B
⊎-elim-left (inj₁ x) x₁ = ⊥-elim (x₁ x)
⊎-elim-left (inj₂ y) x₁ = y

⊎-elim-right : ∀{a b} → {A : Set a} → {B : Set b} → A ⊎ B → ¬ B → A
⊎-elim-right (inj₁ x) x₁ = x
⊎-elim-right (inj₂ y) x₁ = ⊥-elim (x₁ y)
