import Level

module LatticeTheory.List {a : Level.Level} where

open import Algebra.Structures
open import LatticeTheory.Core
open import Function
open import Induction.WellFounded
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Negation
--open import Data.Unit hiding (_≟_)
open import Util.Function
open import Data.Product
open import Data.Empty renaming (⊥ to Empty-⊥)
import Algebra.FunctionProperties
open import Data.Nat hiding (_⊔_) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties
-- BoundedList
{-
data BoundedList {a} (A : Set a) (k : ℕ) : ℕ → Set a where
  nil : BoundedList A k zero
  cons' : {i : ℕ} → A → BoundedList A k i → suc i Data.Nat.≤ k → BoundedList A k (suc i)

FList : ∀{a} → (A : Set a) → (k : ℕ) → Set a
FList A k = Σ[ n ∈ ℕ ] BoundedList A k n


prefix : ∀{a} → {A : Set a} → {k n : ℕ} → BoundedList A k (suc n) → BoundedList A k n
prefix {a₁} {A} {k} {zero} (cons' x x₁ x₂) = nil
prefix {a₁} {A} {.(suc _)} {suc n} (cons' x x₁ (s≤s x₂)) = cons' x (prefix x₁) {! !}

cons : ∀{a} → {A : Set a} → {k : ℕ} → A → FList A k → FList A k
cons {k = k} x (proj₁ , proj₂) with suc proj₁ Data.Nat.≤? k
cons {_} {_} {k} x (proj₁ , proj₂) | yes o = suc proj₁ , cons' x proj₂ o 
cons {_} {_} {k} x (zero , proj₂) | no ¬p = zero , nil
cons {_} {_} {k} x (suc proj₁ , proj₂) | no ¬p = suc proj₁ , cons' x (prefix proj₂) {!!} -- proj₁ , {!prefix !} --cons' x {!!} {!!}
-}

open import Data.List
open import Relation.Binary.List.Pointwise hiding (refl)
open import Util.BoundedList


Listᴸ : BoundedSemiLattice a → ℕ → BoundedSemiLattice a
Listᴸ L k = completeLattice ℂ _⊔_ _≟_ ⊥ ⊥-isMinimal ⊔-idem ⊔-comm ⊔-cong ⊔-assoc ⊐-isWellFounded
 where
  module L where
    open BoundedSemiLattice L public
  ℂ : Set a    
  ℂ = BoundedList L.ℂ k
  open Algebra.FunctionProperties {A = ℂ} _≡_

  -- twee manieren voor ⊔
  -- of: 1,2 ⊔ 2 = 1,2  (vanwege lengte)
  -- of: 1,2 ⊔ 2 = 2,2  (omdat 1⊔2=2)
  _⊔_ : Op₂ ℂ
  a ⊔ b = a --tmp
  _≟_ : Decidable {A = ℂ} _≡_
  a ≟ b = a ≟⟨ L._≟_ ⟩ b
  ⊥ : ℂ 
  ⊥ = 0 , nil 
  open Operators ℂ ⊥ _⊔_ _≟_
  open import Relation.Binary.PropositionalEquality.TrustMe
  ⊥-isMinimal : (c : ℂ) -> ⊥ ⊑ c
  ⊥-isMinimal = λ c → trustMe
  ⊔-idem : Idempotent _⊔_
  ⊔-idem = λ x → trustMe
  ⊔-comm : Commutative _⊔_
  ⊔-comm = λ x y → trustMe
  ⊔-cong : _⊔_ Preserves₂ _≡_ ⟶ _≡_ ⟶ _≡_
  ⊔-cong = λ x x₁ → trustMe
  ⊔-assoc : Associative _⊔_
  ⊔-assoc = λ x y z → trustMe
  postulate
    wf : ∀{x} → Acc _⊐_ x
  ⊐-isWellFounded : Well-founded _⊐_
  ⊐-isWellFounded x = wf
