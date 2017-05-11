open import MonotoneFramework
open import LatticeTheory
open import Data.Vec
open import Function
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Util.Product
open import Data.Fin

module Algorithms.Equivalence {a} (mf : MonotoneFramework a) where
open MonotoneFramework.MonotoneFramework mf
open import Data.Graph n
open BoundedSemiLattice L 
private 
  module V where
    open BoundedSemiLattice (Vecᴸ L n) public
  module V× where
    open BoundedSemiLattice (Vecᴸ L n ×ᴸ Vecᴸ L n) public
    open BoundedSemiLattice.Reasoning (Vecᴸ L n ×ᴸ Vecᴸ L n) public
    
open import Algorithms.Parallel mf
open import TarskiWellFounded (Vecᴸ L n ×ᴸ Vecᴸ L n) transfer-parallel transfer-parallel-isMonotone renaming (IsFixedPoint to IsFixedPointT)
open import Algorithms.MFP mf
open ProvenWithTermination
open import Data.FixedPoint.VectorFixedPoint mf
  

to : (x : V.ℂ) → IsFixedPoint x → IsFixedPointT (x , (tabulate 𝓕 ⊛ x ))
to [] x₁ = refl
to (x ∷ []) x₂ = ≡×⇒≡ (cong (_∷ []) {!!} , {!x₂ (# 0)!}) --  ≡×⇒≡ ({!x₂ (# 0)!} , (cong (λ x → x ∷ []) (cong {!!} {!!})))
 where open MonotoneFramework.MonotoneFramework mf
to (x ∷ x₁ ∷ x₂) x₃ = {!!}



  {-
  open import TarskiWellFounded (ParallelTotalFunctionSpace mf) (parallel-tfs mf) (parallel-tfs-isMonotone mf) renaming (IsFixedPoint to IsFixedPointT)
  to : (x : V.ℂ mf) → IsFixedPoint mf x → IsFixedPointT (λ x₁ → lookup x₁ x) --(x : V.ℂ ? ?) → IsFixedPoint x 
  to [] x₁ = {!!} -- fun-ext (λ x → case x₁ x of (λ{ x₂ → {!!}}))
  to (x ∷ x₁) x₂ = {!!}

  from : (f : P.ℂ mf) → IsFixedPointT f → IsFixedPoint mf (tabulate f)
  from f x ℓ′ = {!!}

  -}


{-
parallel-tfs  x
=
ιE x ⊔ ⨆ (𝕃.map (λ ℓ → 𝓕 ℓ ((λ x₃ → lookup x₃ []) ℓ)) (predecessors F x))


parallel-tfs : P.ℂ → P.ℂ
parallel-tfs σ ℓ′ = ιE ℓ′ ⊔ ⨆ (𝕃.map (λ ℓ → 𝓕 ℓ (σ ℓ)) (predecessors F ℓ′))


-}
