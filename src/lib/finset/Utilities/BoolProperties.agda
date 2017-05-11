

module Utilities.BoolProperties where

open import Data.Bool
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Relation.Binary.Core 
open import Relation.Nullary

postulate ∨-comm : (a b : Bool) → a ∨ b ≡ b ∨ a 


not-inv : ∀ b → not b ≡ true → b ≡ false
not-inv true ()
not-inv false pr = refl

not-inv2 : ∀ b → b ≡ false → not b ≡ true
not-inv2 true ()
not-inv2 false _ = refl


∧-comm : (a b : Bool) → a ∧ b ≡ b ∧ a 
∧-comm true true = refl
∧-comm true false = refl
∧-comm false true = refl
∧-comm false false = refl

∧-assoc : (a b c : Bool) → a ∧ b ∧ c ≡ (a ∧ b) ∧ c
∧-assoc true b c = refl
∧-assoc false b c = refl
