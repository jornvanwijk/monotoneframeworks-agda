import Level

module LatticeTheory.OneOrMore {a : Level.Level} where

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

data OneOrMore (A : Set a) : Set a where
 one : A → OneOrMore A
 more : OneOrMore A


{-
this is a join semi lattice, but not bounded.

   ⊤                        = more
 / | \ .... \  
a₁ a₂ aᵢ     aₙ              = one

but: there is no minimal element.
-}

OneOrMoreᴸ : BoundedSemiLattice a
OneOrMoreᴸ = completeLattice ℂ _⊔_ _≟_ ⊥ ⊥-isMinimal ⊔-idem ⊔-comm ⊔-cong ⊔-assoc ⊐-isWellFounded
 where
  ℂ : Set a    
  ℂ = {!!}
  open Algebra.FunctionProperties {A = ℂ} _≡_ 
  _⊔_ : Op₂ ℂ
  x ⊔ y = {!!}
  _≟_ : Decidable {A = ℂ} _≡_
  x ≟ y = {!!}
  ⊥ : ℂ 
  ⊥ = {!!}
  open Operators ℂ ⊥ _⊔_ _≟_
  ⊥-isMinimal : (c : ℂ) -> ⊥ ⊑ c
  ⊥-isMinimal = {!!}
  ⊔-idem : Idempotent _⊔_
  ⊔-idem = {!!}
  ⊔-comm : Commutative _⊔_
  ⊔-comm = {!!}
  ⊔-cong : _⊔_ Preserves₂ _≡_ ⟶ _≡_ ⟶ _≡_
  ⊔-cong = {!!}
  ⊔-assoc : Associative _⊔_
  ⊔-assoc = {!!}
  ⊐-isWellFounded : Well-founded _⊐_
  ⊐-isWellFounded x = {!!}
