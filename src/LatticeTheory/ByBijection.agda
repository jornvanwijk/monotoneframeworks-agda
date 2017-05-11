import Level

module LatticeTheory.ByBijection {a b : Level.Level} where

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
open import Function.Inverse using (Inverse ; _↔_)
open import Function.Equality using (_⟨$⟩_; Π)

--⊔-bij : (A : Set a) → (L : BoundedSemiLattice b) → (open BoundedSemiLattice L) → (inv : A ↔ ℂ) → (x y : ℂ) →  (BoundedSemiLattice._⊔_ (fromBijectionᴸ A L inv) a b ≡ a ⊔ b



fromBijectionᴸ : (A : Set a) → (L : BoundedSemiLattice b) → (open BoundedSemiLattice L) → A ↔ ℂ → BoundedSemiLattice a
fromBijectionᴸ A L inv = completeLattice ℂ _⊔_ _≟_ ⊥ ⊥-isMinimal ⊔-idem ⊔-comm ⊔-cong ⊔-assoc ⊐-isWellFounded
 where
  module L where
    open BoundedSemiLattice L public
  from : L.ℂ → A
  from = _⟨$⟩_ (Inverse.from inv) 
  to : A → L.ℂ
  to = _⟨$⟩_ (Inverse.to inv)
  
  {-# DISPLAY from x = x #-}
  {-# DISPLAY to x = x #-}
  left-inverse-of : (x : A) → from (to x) ≡ x
  left-inverse-of = Inverse.left-inverse-of inv
  
  right-inverse-of : (x : L.ℂ) → to (from x) ≡ x
  right-inverse-of = Inverse.right-inverse-of inv

  ℂ : Set a    
  ℂ = A
  open Algebra.FunctionProperties {A = ℂ} _≡_ 
  _⊔_ : Op₂ ℂ
  x ⊔ y = from ((to x) L.⊔ (to y))
  _≟_ : Decidable {A = ℂ} _≡_
  x ≟ y with to x L.≟ to y
  x ≟ y | yes p = yes (sym (left-inverse-of _) ⟨ trans ⟩ cong from p ⟨ trans ⟩ left-inverse-of _ )
  x ≟ y | no ¬p = no (λ p → contradiction (cong to p) ¬p)
  ⊥ : ℂ 
  ⊥ = from L.⊥
  open Operators ℂ ⊥ _⊔_ _≟_
  ⊥-isMinimal : (c : ℂ) -> ⊥ ⊑ c
  ⊥-isMinimal c = subst (λ i → from (i L.⊔ to c) ≡ c) (sym (right-inverse-of L.⊥)) (cong from (L.⊥-isMinimal (to c)) ⟨ trans ⟩ left-inverse-of c)
  ⊔-idem : Idempotent _⊔_
  ⊔-idem x = cong from (L.⊔-idem (to x)) ⟨ trans ⟩ (left-inverse-of x)
  ⊔-comm : Commutative _⊔_
  ⊔-comm x y = cong from (L.⊔-comm (to x) (to y))
  ⊔-cong : _⊔_ Preserves₂ _≡_ ⟶ _≡_ ⟶ _≡_
  ⊔-cong x y = cong from (L.⊔-cong₂ (cong to x) (cong to y))
  ⊔-assoc : Associative _⊔_
  ⊔-assoc x y z = cong from (cong (λ x → x L.⊔ (to z)) (right-inverse-of ((to x) L.⊔ (to y))) ⟨ trans ⟩ (L.⊔-assoc (to x) (to y) (to z) ⟨ trans ⟩ cong (L._⊔_ (to x)) (sym (right-inverse-of _))))

  lemma-wf : (x : ℂ) → Acc L._⊐_ (to x) → Acc _⊐_ x
  lemma-wf x (acc rs) = acc l
    where l : WfRec _⊐_ (Acc _⊐_) x
          l y x₁ with (to y) L.⊐? (to x)
          l y _ | yes p = lemma-wf y (rs (to y) p)
          l y (a , b) | no ¬p = ⊥-elim (¬p (trans (sym (right-inverse-of _)) (cong to a) , (λ x₁ → b (trans (trans (sym (left-inverse-of x)) (cong from x₁)) (left-inverse-of y)))))  
  ⊐-isWellFounded : Well-founded _⊐_
  ⊐-isWellFounded x = lemma-wf x (L.⊐-isWellFounded (to x))


module Properties (A : Set a) (L : BoundedSemiLattice b) (open BoundedSemiLattice L) (inv : A ↔ ℂ) where
  module B where
    open BoundedSemiLattice (fromBijectionᴸ A L inv) public
  open ≡-Reasoning
  from : ℂ → A
  from = _⟨$⟩_ (Inverse.from inv) 
  to : A → ℂ
  to = _⟨$⟩_ (Inverse.to inv)

  left-inverse-of : (x : A) → from (to x) ≡ x
  left-inverse-of = Inverse.left-inverse-of inv
  
  right-inverse-of : (x : ℂ) → to (from x) ≡ x
  right-inverse-of = Inverse.right-inverse-of inv

  right-inverse-⊔ : (x y : A) → from (to x ⊔ to y) ≡ x B.⊔ y
  right-inverse-⊔ x y = refl
  
  left-inverse-⊔ :  (x y : ℂ) → to (from x B.⊔ from y) ≡ x ⊔ y
  left-inverse-⊔ x y = 
    begin
    to (from x B.⊔ from y) ≡⟨ sym (cong to (right-inverse-⊔ (from x) (from y))) ⟩
    to (from (to (from x) ⊔ to (from y))) ≡⟨ right-inverse-of _ ⟩
    to (from x) ⊔ to (from y) ≡⟨ ⊔-cong₂ (right-inverse-of _) (right-inverse-of _) ⟩
    x ⊔ y
    ∎

  {-# DISPLAY from x = x #-}
  {-# DISPLAY to x = x #-}
  

{-
from ((to (from x)) ⊔ (to (from y))) ≡
from x B.⊔ from y


from x B.⊔ from y ≡ from (x ⊔ y)


-}
