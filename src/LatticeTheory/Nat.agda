import Level

module LatticeTheory.Nat where

open import Algebra.Structures
open import LatticeTheory.Core
open import Function
open import Induction.WellFounded
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Negation

open import Util.Function
open import Data.Product
open import Data.Empty renaming (⊥ to Empty-⊥)
import Algebra.FunctionProperties
open import Data.Nat renaming (_⊔_ to _ℕ⊔_ ; _⊓_ to _ℕ⊓_ ; _≟_ to _ℕ≟_)
open import Data.Nat.Properties
open import Induction.Nat renaming (<-well-founded to <′-well-founded)
open import Algebra

data ℕ∞ : Set where
  inf : ℕ∞ 
  nat : (n : ℕ) → ℕ∞

mapNat : (f : ℕ → ℕ) → ℕ∞ → ℕ∞
mapNat f inf = inf
mapNat f (nat n) = nat (f n)

-- is actually a MeetSemiLattice
ℕ∞ᴸ : BoundedSemiLattice _
ℕ∞ᴸ = completeLattice ℂ _⊓_ _≟_ ⊤ ⊤-isMaximal ⊓-idem ⊓-comm ⊓-cong ⊓-assoc ⊐-isWellFounded
 where
  ℂ : Set
  ℂ = ℕ∞
  open Algebra.FunctionProperties {A = ℂ} _≡_ 
  _⊓_ : Op₂ ℂ
  inf ⊓ y = y
  x ⊓ inf = x
  nat n ⊓ nat n₁ = nat (n ℕ⊓ n₁)
  _≟_ : Decidable {A = ℂ} _≡_
  nat n ≟ inf = no (λ{()})
  nat n ≟ nat n₁ with n ℕ≟ n₁
  nat n ≟ nat .n | yes refl = yes refl
  nat n ≟ nat n₁ | no ¬p = no (λ{ refl → ¬p refl})
  inf ≟ nat n = no (λ{()})
  inf ≟ inf = yes refl
  ⊤ : ℂ 
  ⊤ = inf
  open Operators ℂ ⊤ _⊓_ _≟_
  ⊤-isMaximal : (c : ℂ) -> ⊤ ⊑ c
  ⊤-isMaximal inf = refl
  ⊤-isMaximal (nat n) = refl
  open DistributiveLattice distributiveLattice hiding (refl)

  ℕ⊓-idem : Algebra.FunctionProperties.Idempotent {A = ℕ} _≡_ _ℕ⊓_
  ℕ⊓-idem zero = refl
  ℕ⊓-idem (suc x) = cong suc (ℕ⊓-idem x)
  
  ⊓-idem : Idempotent _⊓_
  ⊓-idem inf = refl
  ⊓-idem (nat n) = cong nat (ℕ⊓-idem n)
  ⊓-comm : Commutative _⊓_
  ⊓-comm inf inf = refl
  ⊓-comm inf (nat n) = refl 
  ⊓-comm (nat n) inf = refl
  ⊓-comm (nat n) (nat n₁) = cong nat (∨-comm n n₁)
  ⊓-cong : _⊓_ Preserves₂ _≡_ ⟶ _≡_ ⟶ _≡_
  ⊓-cong refl refl = refl
  ⊓-assoc : Associative _⊓_
  ⊓-assoc inf y z = refl
  ⊓-assoc (nat n) inf z = refl
  ⊓-assoc (nat n) (nat n₁) inf = refl
  ⊓-assoc (nat n) (nat n₁) (nat n₂) = cong nat (∨-assoc n n₁ n₂)

  open Properties ⊤-isMaximal ⊓-idem ⊓-comm ⊓-cong ⊓-assoc
  lemma₁ : (x y : ℕ) → nat x ⊐ nat y → x < y
  lemma₁ zero zero (a , b) = ⊥-elim (b a)
  lemma₁ zero (suc y) (refl , b) = s≤s z≤n
  lemma₁ (suc x) zero (a , b) = ⊥-elim (b a)
  lemma₁ (suc x) (suc y) (a , b) = s≤s (lemma₁ x y (cong (mapNat pred) a , (λ x₁ → b (cong (mapNat suc) x₁))))

  <-well-founded : Well-founded _<_
  <-well-founded = Subrelation.well-founded ≤⇒≤′ <′-well-founded

  -- kan dit ook met subrelation?  <⇒⊐ ?
  <-acc⇒⊐-acc : (n : ℕ) → Acc _<_ n → Acc _⊐_ (nat n)
  <-acc⇒⊐-acc n (acc rs) = acc (λ{ inf (a , b) → ⊥-elim (b a) ; (nat n₁) x → <-acc⇒⊐-acc n₁ (rs n₁ (lemma₁ n₁ n x))})

  ⊐-well-founded' : (n : ℕ∞) → WfRec _⊐_ (Acc _⊐_) n
  ⊐-well-founded' inf inf (a , b) = ⊥-elim (b a)
  ⊐-well-founded' inf (nat n) (refl , b) = <-acc⇒⊐-acc n (<-well-founded n)
  ⊐-well-founded' (nat n) inf (a , b) = ⊥-elim (b a)
  ⊐-well-founded' (nat x) (nat y) (a , b) = <-acc⇒⊐-acc y (<-well-founded y)

  ⊐-isWellFounded : Well-founded _⊐_
  ⊐-isWellFounded n = acc (⊐-well-founded' n)
    
