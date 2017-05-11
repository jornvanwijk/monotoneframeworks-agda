import Level

module LatticeTheory.Sum where

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
open import Data.Sum
open import Relation.Nullary.Sum
{-


either combinator that assumes that values of the left domain are always smaller than the right domain.
i.e. given domains A and B,     (  x : A ⊎ B →   if x ∈ A then it is smaller than all  y : A ⊎ B  where y ∈ B)
-}
_⊎ᴸ<_ : ∀{a₁ a₂} → BoundedSemiLattice a₁ → BoundedSemiLattice a₂ → BoundedSemiLattice (a₁ Level.⊔ a₂)
L ⊎ᴸ< R = completeLattice ℂ _⊔_ _≟_ ⊥ ⊥-isMinimal ⊔-idem ⊔-comm ⊔-cong ⊔-assoc ⊐-isWellFounded
 where
  module L where
    open BoundedSemiLattice L public
  module R where
    open BoundedSemiLattice R public
  
  ℂ : Set _    
  ℂ = L.ℂ ⊎ R.ℂ
  open Algebra.FunctionProperties {A = ℂ} _≡_ 
  _⊔_ : Op₂ ℂ
  inj₁ x ⊔ inj₁ y = inj₁ (x L.⊔ y)
  inj₁ x ⊔ inj₂ y = inj₂ y
  inj₂ x ⊔ inj₁ y = inj₂ x
  inj₂ x ⊔ inj₂ y = inj₂ (x R.⊔ y)
  _≟_ : Decidable {A = ℂ} _≡_
  inj₁ x ≟ inj₁ y with x L.≟ y
  inj₁ x ≟ inj₁ y | yes p = yes (cong inj₁ p)
  inj₁ x ≟ inj₁ y | no ¬p = no (λ{refl → ¬p refl})
  inj₁ x ≟ inj₂ y = no (λ{()})
  inj₂ x ≟ inj₁ y = no (λ{()})
  inj₂ x ≟ inj₂ y with x R.≟ y
  inj₂ x ≟ inj₂ y | yes p = yes (cong inj₂ p)
  inj₂ x ≟ inj₂ y | no ¬p = no (λ{refl → ¬p refl})
  ⊥ : ℂ 
  ⊥ = inj₁ L.⊥
  open Operators ℂ ⊥ _⊔_ _≟_
  ⊥-isMinimal : (c : ℂ) -> ⊥ ⊑ c
  ⊥-isMinimal (inj₁ x) = cong inj₁ (L.⊥-isMinimal x)
  ⊥-isMinimal (inj₂ y) = refl
  ⊔-idem : Idempotent _⊔_
  ⊔-idem (inj₁ x) = cong inj₁ (L.⊔-idem x)
  ⊔-idem (inj₂ y) = cong inj₂ (R.⊔-idem y)
  ⊔-comm : Commutative _⊔_
  ⊔-comm (inj₁ x) (inj₁ x₁) = cong inj₁ (L.⊔-comm x x₁)
  ⊔-comm (inj₁ x) (inj₂ y) = refl
  ⊔-comm (inj₂ y) (inj₁ x) = refl
  ⊔-comm (inj₂ y) (inj₂ y₁) = cong inj₂ (R.⊔-comm y y₁)
  ⊔-cong : _⊔_ Preserves₂ _≡_ ⟶ _≡_ ⟶ _≡_
  ⊔-cong refl refl = refl
  ⊔-assoc : Associative _⊔_
  ⊔-assoc (inj₁ x) (inj₁ x₁) (inj₁ x₂) = cong inj₁ (L.⊔-assoc x x₁ x₂)
  ⊔-assoc (inj₁ x) (inj₂ y) (inj₁ x₁) = refl
  ⊔-assoc (inj₂ y) (inj₁ x) (inj₁ x₁) = refl
  ⊔-assoc (inj₂ y) (inj₂ y₁) (inj₁ x₁) = refl
  ⊔-assoc (inj₁ x) (inj₁ x₁) (inj₂ y₁) = refl
  ⊔-assoc (inj₁ x) (inj₂ y) (inj₂ y₁) = refl
  ⊔-assoc (inj₂ y) (inj₁ x) (inj₂ y₂) = refl
  ⊔-assoc (inj₂ y) (inj₂ y₁) (inj₂ y₂) = cong inj₂ (R.⊔-assoc y y₁ y₂)
  drop-inj₁ : {a b : L.ℂ} → _≡_ {A = ℂ} (inj₁ a) (inj₁ b) → a ≡ b
  drop-inj₁ refl = refl 
  drop-inj₂ : {a b : R.ℂ} → _≡_ {A = ℂ} (inj₂ a) (inj₂ b) → a ≡ b
  drop-inj₂ refl = refl
  lemma-inj₂ : (x : R.ℂ) → Acc R._⊐_ x → Acc _⊐_ (inj₂ x)
  lemma-inj₂ x (acc rs) = acc (λ{ (inj₁ x₁) (a , b) → ⊥-elim (b a)
                                  ; (inj₂ y) (a , b) → lemma-inj₂ y (rs y (drop-inj₂ a , (λ x₁ → b (cong inj₂ x₁))))})                                  
  lemma-inj₁ : (x : L.ℂ) → Acc L._⊐_ x → Acc _⊐_ (inj₁ x)
  lemma-inj₁ x (acc rs) = acc (λ{ (inj₁ x₁) (a , b) → lemma-inj₁ x₁ (rs x₁ (drop-inj₁ a , (λ x₂ → b (cong inj₁ x₂))))
                                ; (inj₂ y) x₂ → lemma-inj₂ y (R.⊐-isWellFounded y)})
  ⊐-isWellFounded : Well-founded _⊐_
  ⊐-isWellFounded (inj₁ x) = lemma-inj₁ x (L.⊐-isWellFounded x)
  ⊐-isWellFounded (inj₂ y) = lemma-inj₂ y (R.⊐-isWellFounded y)


_⊎ᴸ>_ : ∀{a₁ a₂} → BoundedSemiLattice a₁ → BoundedSemiLattice a₂ → BoundedSemiLattice (a₁ Level.⊔ a₂)
L ⊎ᴸ> R = R ⊎ᴸ< L
