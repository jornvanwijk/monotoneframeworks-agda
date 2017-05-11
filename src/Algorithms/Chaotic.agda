import Level
open import MonotoneFramework
open import Monotonicity
open import LatticeTheory
open import Data.Vec as 𝕍 hiding (_∈_)
open import Data.List as 𝕃
open import Data.Fin
open import Data.Product
open import Function

module Algorithms.Chaotic {a} (mf : MonotoneFramework a) where
open MonotoneFramework.MonotoneFramework mf
open import Data.Graph n
open LatticeTheory.BoundedSemiLattice L
open import Data.List.Any
open import Data.Bool
open import Relation.Nullary.Decidable
open import Data.Fin.Properties as FinP
open import Data.List.NonEmpty as 𝕃⁺
private
  module V where
    open LatticeTheory.BoundedSemiLattice (Vecᴸ L n) public
  module V× where
    open LatticeTheory.BoundedSemiLattice (Vecᴸ L n ×ᴸ Vecᴸ L n) public

-- applies the transfer function in foldr fashion reusing earlier applied transfer function updates.
transfer-chaotic : Vec ℂ n × Vec ℂ n → Vec ℂ n × Vec ℂ n            
transfer-chaotic x = 𝕍.foldr (λ x₁ → _) (λ{ ℓ′ (entry , exit) → (let entry' = ιE ℓ′ ⊔ ⨆ (𝕃.map (flip lookup exit) (predecessors F ℓ′))
                                                                 in (entry [ ℓ′ ]≔ entry' , exit [ ℓ′ ]≔ 𝓕 ℓ′ entry'))}) x (allFin n)


postulate
  transfer-chaotic-isMonotone : Monotone V×._⊑_ transfer-chaotic

open import TarskiWellFounded (Vecᴸ L n ×ᴸ Vecᴸ L n) transfer-chaotic transfer-chaotic-isMonotone
  
-- chaotic iteration solves the fixed point equation by reusing results from the current iteration.
chaotic-lfp : LeastFixedPoint 
chaotic-lfp = l₀-lfp 

chaotic-result : V×.ℂ
chaotic-result = solveLeastFixedPoint

chaotic○ : V.ℂ
chaotic○ = proj₁ chaotic-result

chaotic● : V.ℂ
chaotic● = proj₂ chaotic-result
  
