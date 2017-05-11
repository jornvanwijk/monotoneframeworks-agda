import Level

module LatticeTheory.Bool where

open import Algebra
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
open import Data.Bool renaming (_∨_ to _⊔_ ; _∧_ to _⊓_)
open import Data.Bool.Properties
open IsBooleanAlgebra isBooleanAlgebra using (isLattice)
open IsLattice isLattice using () renaming (∨-comm to ⊔-comm ; ∨-cong to ⊔-cong ; ∨-assoc to ⊔-assoc; ∧-comm to ⊓-comm ; ∧-cong to ⊓-cong ; ∧-assoc to ⊓-assoc)
import Algebra.Properties.Lattice
open BooleanAlgebra using (lattice)
open Algebra.Properties.Lattice (lattice booleanAlgebra) renaming (∨-idempotent to ⊔-idem ; ∧-idempotent to ⊓-idem)


Boolᴸ : BoundedSemiLattice Level.zero
Boolᴸ = completeLattice ℂ _⊔_ _≟_ ⊥ ⊥-isMinimal ⊔-idem ⊔-comm ⊔-cong ⊔-assoc ⊐-isWellFounded
 where
  ℂ : Set Level.zero
  ℂ = Bool
  ⊥ : ℂ 
  ⊥ = false
  open Operators ℂ ⊥ _⊔_ _≟_
  ⊥-isMinimal : (c : ℂ) -> ⊥ ⊑ c
  ⊥-isMinimal false = refl
  ⊥-isMinimal true = refl
  ⊐-isWellFounded : Well-founded _⊐_
  ⊐-isWellFounded false = acc (λ{ false (a , b) → ⊥-elim (b a) ; true x → acc (λ{ false (a , b) → ⊥-elim (b a) ; true (a , b) → ⊥-elim (b a) }) })
  ⊐-isWellFounded true = acc (λ{ false (a , b) → ⊥-elim (b a) ; true (a , b) → ⊥-elim (b a) })

Mayᴸ : BoundedSemiLattice Level.zero
Mayᴸ = Boolᴸ

Mustᴸ : BoundedSemiLattice Level.zero
Mustᴸ = completeLattice ℂ _⊓_ _≟_ ⊥ ⊥-isMinimal ⊓-idem ⊓-comm ⊓-cong ⊓-assoc ⊐-isWellFounded
 where
  ℂ : Set Level.zero
  ℂ = Bool
  ⊥ : ℂ 
  ⊥ = true
  open Operators ℂ ⊥ _⊓_ _≟_
  ⊥-isMinimal : (c : ℂ) -> ⊥ ⊑ c
  ⊥-isMinimal false = refl
  ⊥-isMinimal true = refl
  ⊐-isWellFounded : Well-founded _⊐_
  ⊐-isWellFounded true = acc (λ{ false (refl , b) → acc (λ{ false (a , b) → ⊥-elim (b a) ; true (a , b) → ⊥-elim (b a)}) ; true (a , b) → ⊥-elim (b a)})
  ⊐-isWellFounded false = acc (λ{ false (a , b) → ⊥-elim (b a) ; true (a , b) → ⊥-elim (b a)})

