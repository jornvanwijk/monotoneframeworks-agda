import Level
open import MonotoneFramework
open import Monotonicity
open import LatticeTheory
open import Data.Vec as 𝕍 hiding (_∈_)
open import Data.List as 𝕃
open import Data.Fin
open import Data.Product
open import Function

module Algorithms.Parallel {a} (mf : MonotoneFramework a) where
open MonotoneFramework.MonotoneFramework mf
open import Data.Graph n
open LatticeTheory.BoundedSemiLattice L 
private 
  module V where
    open LatticeTheory.BoundedSemiLattice (Vecᴸ L n) public
  module V× where
    open LatticeTheory.BoundedSemiLattice (Vecᴸ L n ×ᴸ Vecᴸ L n) public
    open BoundedSemiLattice.Reasoning (Vecᴸ L n ×ᴸ Vecᴸ L n) public
open import Data.List.Any
open import Data.Bool
open import Relation.Nullary.Decidable
open import Data.Fin.Properties as FinP
open import Data.List.NonEmpty as 𝕃⁺

transfer-parallel : V×.ℂ → V×.ℂ
transfer-parallel (entry , exit) = let entry' = 𝕍.map (λ ℓ′ → ιE ℓ′ ⊔ ⨆ (𝕃.map (flip lookup exit) (predecessors F ℓ′))) (allFin n)
                                   in (entry' , (tabulate 𝓕 𝕍.⊛ entry'))
        
postulate
  transfer-parallel-isMonotone : Monotone V×._⊑_ transfer-parallel
    
open import TarskiWellFounded (Vecᴸ L n ×ᴸ Vecᴸ L n) transfer-parallel transfer-parallel-isMonotone


parallel-lfp : LeastFixedPoint 
parallel-lfp = l₀-lfp

parallel-result : V×.ℂ
parallel-result = solveLeastFixedPoint

parallel○ : V.ℂ
parallel○ = proj₁ parallel-result

parallel● : V.ℂ
parallel● = proj₂ parallel-result
    
