import Level
open import MonotoneFramework
open import Monotonicity
open import LatticeTheory
open import Data.Vec as 𝕍 hiding (_∈_)
open import Data.List as 𝕃
open import Data.Fin
open import Data.Product
open import Function

module Algorithms.Parallel-TFS {a} (mf : MonotoneFramework a) where
open MonotoneFramework.MonotoneFramework mf
open import Data.Graph n
open import LatticeTheory.TotalFunctionSpace
open import Function.Inverse using (id)

open LatticeTheory.BoundedSemiLattice L 

ParallelTotalFunctionSpace : BoundedSemiLattice a
ParallelTotalFunctionSpace = Label -[ n , Function.Inverse.id ]→ L

module P where
  open LatticeTheory.BoundedSemiLattice ParallelTotalFunctionSpace public
  open BoundedSemiLattice.Reasoning ParallelTotalFunctionSpace public
module V where
  open BoundedSemiLattice (Vecᴸ L n) public
module V× where
  open BoundedSemiLattice (Vecᴸ L n ×ᴸ Vecᴸ L n) public

parallel-tfs' : P.ℂ → P.ℂ
parallel-tfs' σ ℓ′ = 𝓕 ℓ′ (⨆ (𝕃.map σ (predecessors F ℓ′)))

parallel-tfs : P.ℂ → P.ℂ
parallel-tfs σ ℓ′ = ιE ℓ′ ⊔ ⨆ (𝕃.map (λ ℓ → 𝓕 ℓ (σ ℓ)) (predecessors F ℓ′))

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
import Function.Equality
import Function.Inverse
open import LatticeTheory.ByBijection
open LatticeTheory.ByBijection.Properties
open import Relation.Binary.List.Pointwise hiding (refl)


parallel-tfs-isMonotone : Monotone P._⊑_ parallel-tfs
parallel-tfs-isMonotone {x} {y} p = P.begin
               parallel-tfs x P.≡⟨⟩
               (λ ℓ′ → ιE ℓ′ ⊔ ⨆ (𝕃.map (λ ℓ → 𝓕 ℓ (x ℓ)) (predecessors F ℓ′)))
               P.⊑⟨ fun-ext (λ ℓ′ → 
                 begin
                  ((λ ℓ′₁ → ιE ℓ′₁ ⊔ ⨆ (𝕃.map (λ ℓ → 𝓕 ℓ (x ℓ)) (predecessors F ℓ′₁)))
                  P.⊔
                  (λ z → ιE z ⊔ ⨆ (𝕃.map (λ ℓ → 𝓕 ℓ (y ℓ)) (predecessors F z)))
                 ) ℓ′
                 ≡⟨ $-⊔ Label (n , Function.Inverse.id) L _ _ ℓ′ ⟩
                 (ιE ℓ′ ⊔ ⨆ (𝕃.map (λ ℓ → 𝓕 ℓ (x ℓ)) (predecessors F ℓ′))) ⊔
                 (ιE ℓ′ ⊔ ⨆ (𝕃.map (λ ℓ → 𝓕 ℓ (y ℓ)) (predecessors F ℓ′)))
                 ≡⟨ ⊔-over-⊔  ⟩
                 (ιE ℓ′ ⊔ ιE ℓ′) ⊔
                 (⨆ (𝕃.map (λ ℓ → 𝓕 ℓ (x ℓ)) (predecessors F ℓ′)) ⊔ ⨆ (𝕃.map (λ ℓ → 𝓕 ℓ (y ℓ)) (predecessors F ℓ′)))
                 ≡⟨ ⊔-cong₂ (⊔-idem _) (⨆⊑⨆-pointwise (𝕃.map (λ ℓ → 𝓕 ℓ (x ℓ)) (predecessors F ℓ′)) (𝕃.map (λ ℓ → 𝓕 ℓ (y ℓ)) (predecessors F ℓ′)) (rec (λ {v} {v₁} v₂ → Rel _⊑_ (𝕃.map (λ ℓ → 𝓕 ℓ (x ℓ)) v) (𝕃.map (λ ℓ → 𝓕 ℓ (y ℓ)) v₁)) (λ{ {a} {b} {xs} {ys} {xs⊑ys} x⊑y p → f {a} {b} {xs} {ys} {xs⊑ys} x⊑y p}) [] (≡⇒Rel≡ (refl {_} {_} {predecessors F ℓ′} )))) ⟩
                 ιE ℓ′ ⊔ ⨆ (𝕃.map (λ ℓ → 𝓕 ℓ (y ℓ)) (predecessors F ℓ′))
                 ∎) ⟩
               (λ ℓ′ → ιE ℓ′ ⊔ ⨆ (𝕃.map (λ ℓ → 𝓕 ℓ (y ℓ)) (predecessors F ℓ′)))
               P.∎
             where f : {a : Label} {b : Label} {xs ys : List Label} {xs∼ys : Rel _≡_ xs ys} (x∼y : a ≡ b) →
                       Rel _⊑_ (𝕃.map (λ ℓ → 𝓕 ℓ (x ℓ)) xs) (𝕃.map (λ ℓ → 𝓕 ℓ (y ℓ)) ys) →
                       Rel _⊑_ (𝓕 a (x a) ∷ 𝕃.map (λ ℓ → 𝓕 ℓ (x ℓ)) xs) (𝓕 b (y b) ∷ 𝕃.map (λ ℓ → 𝓕 ℓ (y ℓ)) ys)
                   f {a} {.a} refl g = 𝓕-isMonotone a ($-⊑ Label ( n , Function.Inverse.id) L x y a p) ∷ g
 
open import TarskiWellFounded ParallelTotalFunctionSpace parallel-tfs parallel-tfs-isMonotone
open import Data.Vec

parallel-tfs-lfp : LeastFixedPoint
parallel-tfs-lfp = l₀-lfp

parallel-tfs○ : V.ℂ
parallel-tfs○ = tabulate solveLeastFixedPoint

parallel-tfs● : V.ℂ
parallel-tfs● = tabulate 𝓕 ⊛ parallel-tfs○

parallel-tfs-result : V.ℂ × V.ℂ
parallel-tfs-result = (parallel-tfs○ , parallel-tfs●)
   
