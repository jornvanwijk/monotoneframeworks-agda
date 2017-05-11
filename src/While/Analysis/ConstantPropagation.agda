open import Data.Fin hiding (_-_)
open import Data.Product
open import Data.Graph 6
open import MonotoneFramework as MF
import Data.List.NonEmpty
open import Data.Fin.Subset
import Level
open import LatticeTheory
--open import Data.Vec hiding (init)
open import Data.Nat hiding (_≟_)
open import Data.Fin.Properties as FinP
open import Relation.Nullary
open import Algorithms
open import Function
--open import Data.Vec
open import Data.List
open import Monotonicity
open import LatticeTheory.Z-Top
open import While.Language

module While.Analysis.ConstantPropagation (program : Labeled.WhileProgram) where
  open Labeled
  open WhileProgram program
  open Extra program
  open import LatticeTheory.TotalFunctionSpace
  open import Function.Inverse as Inverse
  L : BoundedSemiLattice Level.zero
  L = Fin m -[ m , Inverse.id ]→ ℤ⊤⊥ᴸ

  open BoundedSemiLattice L

  𝑨CP : AExpr → (Fin m → BoundedSemiLattice.ℂ ℤ⊤⊥ᴸ) →  BoundedSemiLattice.ℂ ℤ⊤⊥ᴸ
  𝑨CP (var x) σ̂ = σ̂ x
  𝑨CP (lit n) σ̂ = in-ℤ n
  𝑨CP (x plus y) σ̂ = 𝑨CP x σ̂ plusℤ 𝑨CP y σ̂
  𝑨CP (x min y) σ̂ = 𝑨CP x σ̂ minℤ 𝑨CP y σ̂
  𝑨CP (x mul y) σ̂ = 𝑨CP x σ̂ mulℤ 𝑨CP y σ̂

  open import Data.Vec hiding (init)
  transfer-functions : Lab → ℂ → ℂ
  transfer-functions l x = case lookup l blocks of (λ
                           { (Labeled.skip l₁) → x 
                           ; ((x₁ Labeled.:= a) l₁) → λ m' → case m' FinP.≟ x₁ of (λ
                                                             { (yes p) → 𝑨CP a x
                                                             ; (no ¬p) → x m'
                                                             })
                           ; (Labeled.bExpr c l₁) → x
                           }) 

  postulate
    transfer-monotone : (ℓ : Fin n) → Monotone _⊑_ (transfer-functions ℓ)
  
  constant-propagation : MonotoneFramework _ 
  constant-propagation = record
      { L = L
      ; 𝓕 = transfer-functions
      ; F = flow labelledProgram
      ; E = Data.List.[ init labelledProgram ]
      ; ι = λ x → top
      ; 𝓕-isMonotone = transfer-monotone
      }

  open import Data.String
  showCP : ℂ → String
  showCP f = Data.String.fromList (Data.List.concat (intersperse (Data.String.toList ", ") (Data.Vec.toList (Data.Vec.map (λ v → Data.String.toList (showℤ⊤⊥ (f v))) (allFin _)))))

--unlines (Data.Vec.toList (Data.Vec.map  x)) --Data.Vec.map (λ f → Data.Vec.map f (allFin 3)) x
