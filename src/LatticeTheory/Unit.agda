import Level

module LatticeTheory.Unit {a : Level.Level} where

import Algebra.FunctionProperties
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


Unitᴸ  : BoundedSemiLattice a
Unitᴸ  = completeLattice ℂ _⊔_ _≟_ ⊥ ⊥-isMinimal ⊔-idem ⊔-comm ⊔-cong₂ ⊔-assoc ⊐-isWellFounded
 where
  ℂ : Set a    
  ℂ = Level.Lift ⊤
  open Algebra.FunctionProperties {A = ℂ} _≡_ 
  _⊔_ : Op₂ ℂ
  x ⊔ y = Level.lift tt
  _≟_ : Decidable {A = ℂ} _≡_
  x ≟ y = yes refl
  ⊥ : ℂ 
  ⊥ = Level.lift tt
  open Operators ℂ ⊥ _⊔_ _≟_
  ⊥-isMinimal : (c : ℂ) -> ⊥ ⊑ c
  ⊥-isMinimal c = refl
  ⊔-idem : Idempotent _⊔_
  ⊔-idem = const refl 
  ⊔-comm : Commutative _⊔_
  ⊔-comm = const₂ refl
  ⊔-cong₂ : _⊔_ Preserves₂ _≡_ ⟶ _≡_ ⟶ _≡_
  ⊔-cong₂ = const₂ refl
  ⊔-assoc : Associative _⊔_
  ⊔-assoc = const₃ refl
  ⊐-isWellFounded : Well-founded _⊐_
  ⊐-isWellFounded (Level.lift tt) = acc (λ{ (Level.lift tt) (a , b) → ⊥-elim (b a) })


    

