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

module While.Analysis.ConstantPropagation (n : ℕ) (m : ℕ) where
  open import While.Language n m
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


  
  module _ (program : Stmt) where


    transfer-function : Block → Lab → ℂ → ℂ
    transfer-function b l₁ x with (getLab b) FinP.≟ l₁
    transfer-function (skip l) l₁ x | yes p = x
    transfer-function ((x := a) l) l₁ x₁ | yes p = λ m' → case m' FinP.≟ x of
                                                           (λ{ (yes p₁) → 𝑨CP a x₁
                                                            ;  (no ¬p) → x₁ m'})
    transfer-function (bExpr c l) l₁ x | yes p = x --(x - (kill b)) ∪ gen b
    transfer-function b l₁ x | no ¬p = x -- x
  
    -- very inefficient; reason @ WhileLanguage.Blocks
    transfer-functions : Lab → ℂ → ℂ
    transfer-functions l x = Data.List.foldr (flip transfer-function l) x (blocks program)

    postulate
      transfer-monotone : (ℓ : Fin n) → Monotone _⊑_ (transfer-functions ℓ)
  

    constant-propagation : MonotoneFramework _ _
    constant-propagation = record
      { L = L
      ; 𝓕 = transfer-functions
      ; F = flow program
      ; E = Data.List.NonEmpty.[ init program ]
      ; ι = λ x → top
      ; 𝓕-isMonotone = transfer-monotone
      }
