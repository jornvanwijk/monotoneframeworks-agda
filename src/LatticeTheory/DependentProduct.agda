module LatticeTheory.DependentProduct where

open import LatticeTheory.Core
open import Relation.Binary
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Induction.WellFounded
open import Relation.Binary.PropositionalEquality
open import Data.Empty renaming (⊥ to Empty-⊥)
import Level
open import Data.Sum
import Algebra.FunctionProperties
open import Util.Product
open import Data.Nat using (ℕ)

infixr 5 _×ᴸ_
open import Function
open import LatticeTheory.TotalFunctionSpace

{- the lattice is not dependent
   But the second value depends on the first. -}

-- We need a lattice with a constraint that the carrier of the lattice is of the form     A → B   where A is the carrier of L.
---   /-  suc a₂ ?
_×ᴸ_ : ∀{a₁ a₂} → (L : BoundedSemiLattice a₁) → (f : BoundedSemiLattice.ℂ L → BoundedSemiLattice a₂) → BoundedSemiLattice (a₁ Level.⊔ a₂)
_×ᴸ_ {a₁} {a₂} L f = {!!} --completeLattice ℂ _⊔_ _≟_ ⊥ ⊥-isMinimal ⊔-idem ⊔-comm ⊔-cong₂ ⊔-assoc ⊐-isWellFounded
 where
  module L where
    open BoundedSemiLattice L public
  {-
  module R where
    open BoundedSemiLattice R public -}

  ℂ : Set (a₂ Level.⊔ a₁) -- (a₁ Level.⊔ a₂)
  ℂ = Σ[ x ∈ L.ℂ ] BoundedSemiLattice.ℂ (f x) 
  {-
  ℂ : Set (a₁ Level.⊔ a₂)
  ℂ = Σ (BoundedSemiLattice.ℂ L) (λ x → BoundedSemiLattice.ℂ (R x)) --(λ x → BoundedSemiLattice.ℂ (R x)) --  (BoundedSemiLattice.ℂ ∘ R)
  -}
  open Algebra.FunctionProperties {A = ℂ} _≡_

  _≟_ : Decidable {A = ℂ} _≡_
  _≟_ = {!!} {-
  (x , y) ≟ (w , z) with x L.≟ w
  (x , y) ≟ (.x , z) | yes refl with y x R.≟ z x
  (x , y) ≟ (.x , z) | yes refl | yes p = {!fun-ext {_} {_} {L.ℂ} !}
  (x , y) ≟ (.x , z) | yes refl | no ¬p = {!!}
  (x , y) ≟ (w , z) | no ¬p = {!!} -}
  {-
  (proj₁ , proj₂) ≟ (proj₃ , proj₄) with proj₁ L.≟ proj₃
  (proj₁ , proj₂) ≟ (.proj₁ , proj₄) | yes refl with BoundedSemiLattice._≟_ (R proj₁) proj₂ proj₄
  (proj₁ , proj₂) ≟ (.proj₁ , .proj₂) | yes refl | yes refl = yes refl
  (proj₁ , proj₂) ≟ (.proj₁ , proj₄) | yes refl | no ¬p = no (λ{ refl → ¬p refl})
  (proj₁ , proj₂) ≟ (proj₃ , proj₄) | no ¬p = no (λ{ refl → ¬p refl})
  
  _⊔_ : Op₂ ℂ
  (proj₁ , proj₂) ⊔ (proj₃ , proj₄) = (proj₁ L.⊔ proj₃) , {!!}  
  
  _⊔_ : Op₂ ℂ
  (x₁ , x₂) ⊔ (y₁ , y₂) = x₁ L.⊔ y₁ , x₂ R.⊔ y₂
  _≟_ : Decidable {A = ℂ} _≡_
  _≟_ (a , b) (c , d) with a L.≟ c | b R.≟ d
  _≟_ (a , b) (c , d) | yes p | yes p₁ = yes (cong₂ _,_ p p₁)
  _≟_ (a , b) (c , d) | yes p | no ¬p = no (λ x → ¬p (proj₂ (≡-on-× x)))
  _≟_ (a , b) (c , d) | no ¬p | p = no (λ x → ¬p (proj₁ (≡-on-× x)))
  ⊥ : ℂ 
  ⊥ = L.⊥ , R.⊥
  open Operators ℂ ⊥ _⊔_ _≟_
  ⊥-isMinimal : (c : ℂ) -> ⊥ ⊑ c
  ⊥-isMinimal (a , b) = cong₂ _,_ (L.⊥-isMinimal a) (R.⊥-isMinimal b) 
  ⊔-idem : Idempotent _⊔_
  ⊔-idem (a , b) = cong₂ _,_ (L.⊔-idem a) (R.⊔-idem b)
  ⊔-comm : Commutative _⊔_
  ⊔-comm (a , b) (c , d) = cong₂ _,_ (L.⊔-comm a c) (R.⊔-comm b d) 
  ⊔-cong₂ : _⊔_ Preserves₂ _≡_ ⟶ _≡_ ⟶ _≡_
  ⊔-cong₂ refl refl = cong₂ _,_ (L.⊔-cong₂ refl refl) (R.⊔-cong₂ refl refl)
  ⊔-assoc : Associative _⊔_
  ⊔-assoc (a , b) (c , d) (e , f) = cong₂ _,_ (L.⊔-assoc a c e) (R.⊔-assoc b d f)


  lemma-wf : ∀{x y} -> Acc L._⊐_ x -> Acc R._⊐_ y -> Acc _⊐_ (x , y)
  lemma-wf {x} {y} (acc rs) (acc rs₁) = acc l
    where l : WfRec _⊐_ (Acc _⊐_) (x , y)
          l (w , z) b with (w L.⊐? x) | (z R.⊐? y)
          l (w , z) (xz≠wz , xz⊐wz) | yes (p₁ , p₂) | yes (q₁ , q₂) = lemma-wf (rs w (p₁ , p₂)) (rs₁ z (q₁ , q₂))
          l (w , z) (xz≠wz , xz⊐wz) | no ¬p         | yes (q₁ , q₂) with x L.≟ w
          l (w , z) (xz≠wz , xz⊐wz) | no ¬p         | yes (q₁ , q₂) | yes r rewrite sym r = lemma-wf (acc rs) (rs₁ z (q₁ , q₂))
          l (w , z) (xz≠wz , xz⊐wz) | no ¬p         | yes (q₁ , q₂) | no r = ⊥-elim (¬p ((proj₁ (≡-on-× xz≠wz)) , r))
          l (w , z) (xz≠wz , xz⊐wz) | yes (p₁ , p₂) | no ¬q         with y R.≟ z
          l (w , z) (xz≠wz , xz⊐wz) | yes (p₁ , p₂) | no ¬q         | yes r rewrite sym r = lemma-wf (rs w (p₁ , p₂)) (acc rs₁) 
          l (w , z) (xz≠wz , xz⊐wz) | yes (p₁ , p₂) | no ¬q         | no r = ⊥-elim (¬q ((proj₂ (≡-on-× xz≠wz)) , r)) 
          l (w , z) (xz≠wz , xz⊐wz) | no ¬p         | no ¬q         = ⊥-elim (¬p ((proj₁ (≡-on-× xz≠wz)) , (λ x₁ → ¬q ((proj₂ (≡-on-× xz≠wz)) , (λ x₂ → xz⊐wz (cong₂ _,_ x₁ x₂))))))
          
  ⊐-isWellFounded : Well-founded _⊐_
  ⊐-isWellFounded (x , y) = lemma-wf (L.⊐-isWellFounded x) (R.⊐-isWellFounded y)
-}
