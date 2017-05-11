import Level

module LatticeTheory.ByGraph {a : Level.Level} where

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


open import Data.Graph.Acyclic
open import Data.Nat hiding (_⊔_ ; _≟_)


myBoundedSemiLattice : {ℂ : Set} → (n : ℕ) → (Graph ℂ ⊤ n) → BoundedSemiLattice Level.zero
myBoundedSemiLattice {ℂ} n x = completeLattice ℂ _⊔_ _≟_ ⊥ ⊥-isMinimal ⊔-idem ⊔-comm ⊔-cong ⊔-assoc ⊐-isWellFounded
 where
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
