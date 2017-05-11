module Util.Decidable where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Algebra.FunctionProperties


{-
--Decidable : ∀ {a b ℓ} {A : Set a} {B : Set b} → REL A B ℓ →
cong-dec : ∀ {a b ℓ} → {A : Set a} → {B : Set b} → {_op_ : Rel A ℓ } → Decidable _op_ → (f : A → B) → Decidable (λ x y → f x op f y)
cong-dec = ?
-}
