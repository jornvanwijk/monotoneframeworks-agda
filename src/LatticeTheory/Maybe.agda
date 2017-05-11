import Level

module LatticeTheory.Maybe {a b : Level.Level} where

open import Algebra.Structures
open import LatticeTheory.Core
open import Function
open import Induction.WellFounded
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Data.Unit hiding (_≟_)
open import Util.Function
open import Data.Product
open import Data.Empty renaming (⊥ to Empty-⊥)
import Algebra.FunctionProperties
open import Data.Maybe

Maybeᴸ : BoundedSemiLattice a → BoundedSemiLattice a
Maybeᴸ L = completeLattice ℂ _⊔_ _≟_ ⊥ ⊥-isMinimal ⊔-idem ⊔-comm ⊔-cong ⊔-assoc ⊐-isWellFounded
 where
  module L where
    open BoundedSemiLattice L public
  ℂ : Set a    
  ℂ = Maybe L.ℂ
  open Algebra.FunctionProperties {A = ℂ} _≡_ 
  _⊔_ : Op₂ ℂ
  just x ⊔ just y = just (x L.⊔ y)
  just x ⊔ nothing = just x
  nothing ⊔ y = y
  _≟_ : Decidable {A = ℂ} _≡_
  just x ≟ just y with x L.≟ y
  just x ≟ just y | yes p = yes (cong just p)
  just x ≟ just y | no ¬p = no (λ{ refl → ¬p refl})
  just x ≟ nothing = no (λ{()})
  nothing ≟ just x = no (λ{()})
  nothing ≟ nothing = yes refl
  ⊥ : ℂ 
  ⊥ = nothing
  open Operators ℂ ⊥ _⊔_ _≟_
  ⊥-isMinimal : (c : ℂ) -> ⊥ ⊑ c
  ⊥-isMinimal (just x) = refl
  ⊥-isMinimal nothing = refl
  ⊔-idem : Idempotent _⊔_
  ⊔-idem (just x) = cong just (L.⊔-idem x)
  ⊔-idem nothing = refl
  ⊔-comm : Commutative _⊔_
  ⊔-comm (just x) (just x₁) = cong just (L.⊔-comm x x₁)
  ⊔-comm (just x) nothing = refl
  ⊔-comm nothing (just x) = refl
  ⊔-comm nothing nothing = refl
  ⊔-cong : _⊔_ Preserves₂ _≡_ ⟶ _≡_ ⟶ _≡_
  ⊔-cong refl refl = refl
  ⊔-assoc : Associative _⊔_
  ⊔-assoc (just x) (just x₁) (just x₂) = cong just (L.⊔-assoc x x₁ x₂)
  ⊔-assoc nothing (just x₁) (just x₂) = refl
  ⊔-assoc (just x) nothing (just x₁) = refl
  ⊔-assoc nothing nothing (just x₁) = refl
  ⊔-assoc (just x) (just x₁) nothing = refl
  ⊔-assoc (just x) nothing nothing = refl
  ⊔-assoc nothing y nothing = refl

  ≡-just : {a b : L.ℂ} → _≡_ {A = ℂ} (just a) (just b) → a ≡ b
  ≡-just {a₁} {.a₁} refl = refl

  -- everything greater than i is accessible because
  acc-just : {i : L.ℂ} →  Acc L._⊐_ i → Acc _⊐_ (just i)
  acc-just {i} (acc rs) = acc (λ{ (just x) (a , b) → acc-just (rs x (≡-just a , (λ x₁ → b (cong just x₁))))
                                ; nothing (a , b) → ⊥-elim (b a)})

  -- everything greater than bot is accessible because
  acc-bot : Acc _⊐_ nothing
  acc-bot = acc (λ{ (just x) x₁ → acc-just (L.⊐-isWellFounded x)
                   ; nothing (a , b) → ⊥-elim (b a)}) 

  ⊐-isWellFounded : Well-founded _⊐_
  ⊐-isWellFounded (just x) = acc-just (L.⊐-isWellFounded x)
  ⊐-isWellFounded nothing = acc-bot
                                  

