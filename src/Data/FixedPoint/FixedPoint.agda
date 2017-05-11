open import Relation.Binary.PropositionalEquality
open import LatticeTheory.Core
open import Data.Product

module Data.FixedPoint.FixedPoint {a} (completeLattice : BoundedSemiLattice a) (open BoundedSemiLattice completeLattice) (f : ℂ -> ℂ) where

  IsFixedPoint : (c : ℂ) -> Set a
  IsFixedPoint c = c ≡ f c
  
  IsExtensivePoint : ℂ -> Set a
  IsExtensivePoint c = c ⊑ f c

  IsReductivePoint : ℂ -> Set a
  IsReductivePoint c = f c ⊑ c

  fixed⇒reductive : {c : ℂ} -> IsFixedPoint c -> IsReductivePoint c
  fixed⇒reductive {c} p = trans (cong (λ y → y ⊔ c) (sym p)) (⊔-idem c)

  fixed⇒extensive : {c : ℂ} → IsFixedPoint c → IsExtensivePoint c
  fixed⇒extensive {c} p = trans (cong (λ w → _⊔_ w (f c)) p) (⊔-idem (f c))

  record FixedPoint : Set a where
    constructor fp
    field
      element : ℂ
      isFixedPoint : IsFixedPoint element
  IsLeastFixedPoint : (c : ℂ) -> Set a
  IsLeastFixedPoint c = IsFixedPoint c × ((e : FixedPoint) -> c ⊑ FixedPoint.element e)

  record LeastFixedPoint : Set a where
    constructor lfp
    field
      element : ℂ
      isLeastFixedPoint : IsLeastFixedPoint element
