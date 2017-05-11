import Level

module LatticeTheory.Dual {a : Level.Level} where

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


{- denk dat deze vereist zijn:
    ⊤         : ℂ           -- Least element
    ⊤-isMaximal : (c : ℂ) -> ⊤ ⊒ c    -- Proof that ⊥ is the least element
    ⊏-isWellFounded : Well-founded _⊏_ -- Ascending chain condition
-}

Dualᴸ : (L : BoundedSemiLattice a) → (open BoundedSemiLattice L) → (⊤ : ℂ) → (⊤-isMaximal : (c : ℂ) → ⊤ ⊒ c) → (⊏-isWellFounded : Well-founded _⊏_) → BoundedSemiLattice a
Dualᴸ L ⊤ ⊤-isMaximal ⊏-isWellFounded = completeLattice L.ℂ _⊓_ L._≟_ ⊤ {!⊤-isMaximal!} {!!} {!!} {!!} {!!} {!⊏-isWellFounded!} -- completeLattice L.ℂ _⊓_ L._≟_ ⊤ {!⊤-isMaximal!} ⊓-comm ⊓-cong ⊓-assoc {!!}
 where
  module L where
    open BoundedSemiLattice L public
  _≟_ : Decidable {A = L.ℂ} _≡_
  _≟_ = L._≟_
  open Algebra.FunctionProperties {A = L.ℂ} _≡_

  postulate
    ⊔-idem : Idempotent L._⊔_

  _⊓_ : Op₂ L.ℂ
  x ⊓ x₁ = L.⨆ {!!}

  open Operators L.ℂ ⊤ _⊓_ L._≟_

  ⊓-comm : Commutative _⊓_
  ⊓-comm = {!!}
  ⊓-cong : _⊓_ Preserves₂ _≡_ ⟶ _≡_ ⟶ _≡_
  ⊓-cong = {!!}
  ⊓-assoc : Associative _⊓_
  ⊓-assoc = {!!}
  
{-
  _⊔'_ : (x : ℂ) → (y : ℂ) -> (a : ℂ) → Acc L._⊐_ a → ℂ  -- Altijd: α ⊐ x ∨ α ⊐ y     ..
  (x ⊔' y) α (acc rs) with α L.⊔ y L.≟ α | α L.≟ x L.⊔ α
  (x ⊔' y) α (acc rs) | yes p | q with α L.⊔ x L.≟ x
  (x ⊔' y) α (acc rs) | yes p₁ | q | yes p = α
  (x ⊔' y) α (acc rs) | yes p | q | no ¬p = {!!}  -- dit kan niet?
  (x ⊔' y) α (acc rs) | no ¬p | yes p with α L.⊔ y L.≟ y
  (x ⊔' y) α (acc rs) | no ¬p | yes p₁ | yes p = α
  (x ⊔' y) α (acc rs) | no ¬p₁ | yes p | no ¬p = {!!} -- dit kan ook niet.
  (x ⊔' y) α (acc rs) | no ¬p | no ¬p₁ = ((x L.⊔ (α L.⊔ y)) ⊔' x) {!!} {!!}

--  (x ⊔' y) α (acc rs) | no ¬p | no ¬p₁ = (x ⊔' y) (x L.⊔ α) (rs (x L.⊔ α) ({!!} , ¬p₁)) L.⊔ (x ⊔' y) (y L.⊔ α) (rs (y L.⊔ α) ({!!} , {!!})) 
{-(x ⊔' y) (acc rs) with x L.⊐? y
  (x ⊔' y) (acc rs) | yes p = y
  (x ⊔' y) (acc rs) | no ¬p with y L.⊐? x
  (x ⊔' y) (acc rs) | no ¬p | yes p = x
  (x ⊔' y) (acc rs) | no ¬p₁ | no ¬p = ({!!} ⊔' {!!}) (rs {!!} {!!})-}
{-(x ⊔' y) (acc rs) (acc rs₁) with x L.⊐? (x L.⊔ y) | y L.⊐? (x L.⊔ y)
  (x ⊔' y) (acc rs) (acc rs₁) | yes (proj₁ , proj₂) = ((y L.⊔ x) ⊔' y) (rs (y L.⊔ x) ({!!} , {!!})) (acc rs₁)
  (x ⊔' y) (acc rs) (acc rs₁) | no ¬p = {!!}
  -}
  _⊔_ : Op₂ ℂ
  x ⊔ y = _⊔'_ x y L.⊥ (L.⊐-isWellFounded L.⊥)


  open Operators ℂ _⊔_ _≟_

  fff : (x : ℂ) → Acc L._⊐_ x → ℂ
  fff x (acc rs) = fff {!!} {!!}

  ⊥ : ℂ 
  ⊥ = fff L.⊥ (L.⊐-isWellFounded L.⊥)
  ⊥-isMinimal : (c : ℂ) -> ⊥ ⊑ c
  ⊥-isMinimal = {!!}
  ⊔-comm : Commutative _⊔_
  ⊔-comm = {!!}
  ⊔-cong : _⊔_ Preserves₂ _≡_ ⟶ _≡_ ⟶ _≡_
  ⊔-cong = {!!}
  ⊔-assoc : Associative _⊔_
  ⊔-assoc = {!!}
  isWellFounded : Well-founded _⊐_
  isWellFounded x = {!!}
  -}
