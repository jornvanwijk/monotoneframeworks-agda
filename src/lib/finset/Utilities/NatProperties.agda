

module Utilities.NatProperties where

open import Data.Nat

open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Relation.Binary.Core 
open import Relation.Nullary


+-com : ∀ a b → a + b ≡ b + a
+-com zero zero = refl
+-com zero (suc b) = cong suc (+-com zero b)
+-com (suc a) zero = cong suc (+-com a zero)
+-com (suc a) (suc b) rewrite +-com a (suc b) | +-com b a 
 = cong suc (+-com (suc a) b)

open import Data.Sum
≤-pr : ∀ a b → ¬ (a ≡ b) → a ≤ b ⊎ b ≤ a
≤-pr zero b pr = inj₁ z≤n
≤-pr (suc a) zero pr = inj₂ z≤n
≤-pr (suc a) (suc b) pr with ≤-pr a b (λ pr2 → pr (cong suc pr2)) 
≤-pr (suc a) (suc b) pr | inj₁ x = inj₁ (s≤s x)
≤-pr (suc a) (suc b) pr | inj₂ y = inj₂ (s≤s y)



≤-pr' : ∀ a b → a ≤ b ⊎ b ≤ a
≤-pr' zero b  = inj₁ z≤n
≤-pr' (suc a) zero  = inj₂ z≤n
≤-pr' (suc a) (suc b) with ≤-pr' a b  
≤-pr' (suc a) (suc b) | inj₁ x = inj₁ (s≤s x)
≤-pr' (suc a) (suc b) | inj₂ y = inj₂ (s≤s y)
