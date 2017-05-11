open import Data.Fin hiding (_-_)
open import Data.Product
open import Data.Graph 6
open import MonotoneFramework as MF
import Data.List.NonEmpty
open import Data.Fin.Subset
import Level
open import LatticeTheory
open import Data.Nat hiding (_≟_)
open import Data.Fin.Properties as FinP
open import Relation.Nullary
open import Algorithms
open import Function
open import Data.List
open import Monotonicity
open import LatticeTheory.Z-Top
open import While-Fun.Language
open import Data.Vec hiding (init)
open import EmbellishedFramework


module While-Fun.Analysis.ConstantPropagation (program : Labeled.WhileProgram) where
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
  
  embellishedType : Fin n → EmbellishedBlock n
  embellishedType l with lookup l blocks
  embellishedType l | call cℓ name rℓ args retvar = call
  embellishedType l | return cℓ name rℓ args retvar = return cℓ
  embellishedType l | _ = other

-- (c : Lab) → (name : Fun) → (r : Lab) → (a : List (Common.AExpr Var)) → (r : Var)
  transfer-function : (ℓ : Fin n) → arityToType (arity embellishedType ℓ) ℂ
  transfer-function ℓ with lookup ℓ blocks
  transfer-function ℓ | skip l = Function.id
  transfer-function ℓ | (x₁ := a) l = λ x m' → case m' FinP.≟ x₁ of (λ
                                                     { (yes p) → 𝑨CP a x
                                                     ; (no ¬p) → x m'
                                                     })                 
  transfer-function ℓ | bExpr c l = Function.id
  transfer-function ℓ | call c name r a r₁ = Function.id
  transfer-function ℓ | return  cℓ name rℓ args retvar = λ beforeCall afterCall v → (case v FinP.≟ retvar of
                                                    (λ{ (yes p) → afterCall
                                                      ; (no ¬p) → beforeCall})) v
  transfer-function ℓ | entry name arguments result ln body lx = Function.id
  transfer-function ℓ | exit name arguments result ln body lx = Function.id

  postulate
    isMonotone : (ℓ : Fin n) → EmbellishedFrameworkMonotonicity.Monotonicity n L (arity embellishedType) transfer-function ℓ

  constant-propagation-embellished : EmbellishedMonotoneFramework _
  constant-propagation-embellished = record
    { n = n
    ; L = L
    ; k = 2
    ; labelType = embellishedType
    ; 𝓕 = transfer-function
    ; E = Data.List.[ init⋆ labelledProgram ]
    ; ι = λ x → top
    ; 𝓕-isMonotone = isMonotone
    }

  constant-propagation : MonotoneFramework _
  constant-propagation = EmbellishedMonotoneFramework.asMonotoneFramework constant-propagation-embellished (flow⋆ labelledProgram) 
  open EmbellishedMonotoneFramework constant-propagation-embellished                       
  open import Data.String

  showCP : ℂ → String
  showCP f = Data.String.fromList (Data.List.concat (intersperse (Data.String.toList ", ") (Data.Vec.toList (Data.Vec.map (λ v → Data.String.toList (showℤ⊤⊥ (f v))) (allFin _)))))
  showCP-emb : BoundedSemiLattice.ℂ L̂ → String
  showCP-emb f = showEmb showCP f

