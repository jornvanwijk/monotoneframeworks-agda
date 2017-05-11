open import Data.Fin hiding (_-_)
open import Data.Product
open import Data.Graph 6
open import MonotoneFramework as MF
import Data.List.NonEmpty
open import Data.Fin.Subset
import Level
open import LatticeTheory
open import Data.Vec hiding (init)
open import Data.Nat hiding (_≟_)
open import Data.Fin.Properties
open import Relation.Nullary
open import Algorithms
open import Function
open import Data.Vec
open import Data.List
open import Monotonicity
module While.Analysis.LiveVariables (n : ℕ) (m : ℕ) where
  open import While.Language n m
  
  kill : Block → Subset m
  kill (skip l) = ⊥
  kill ((x := a) l) = ⁅ x ⁆
  kill (bExpr c l) = ⊥

  free-variables : AExpr → Subset m
  free-variables (var x) = ⁅ x ⁆
  free-variables (lit x) = ⊥
  free-variables (a plus a₁) = free-variables a ∪ free-variables a₁
  free-variables (a min a₁) = free-variables a ∪ free-variables a₁
  free-variables (a mul a₁) = free-variables a ∪ free-variables a₁

  free-variables-BExpr : BExpr → Subset m
  free-variables-BExpr true = ⊥
  free-variables-BExpr false = ⊥
  free-variables-BExpr (not b) = free-variables-BExpr b
  free-variables-BExpr (b and b₁) = free-variables-BExpr b ∪ free-variables-BExpr b₁
  free-variables-BExpr (b or b₁) =  free-variables-BExpr b ∪ free-variables-BExpr b₁
  free-variables-BExpr (x gt x₁) = free-variables x ∪ free-variables x₁

  gen : Block → Subset m
  gen (skip l) = ⊥
  gen ((x := a) l) = free-variables a
  gen (bExpr c l) = free-variables-BExpr c

  _-_ : ∀{n} → Subset n → Subset n → Subset n
  x - y = x ∩ (∁ y)

  transfer-function : Block → Lab → Subset m → Subset m
  transfer-function b l₁ x with (getLab b) ≟ l₁
  transfer-function b l₁ x | yes p = (x - (kill b)) ∪ gen b
  transfer-function b l₁ x | no ¬p = x
  
  -- very inefficient; reason @ WhileLanguage.Blocks
  transfer-functions : Stmt → Lab → Subset m → Subset m
  transfer-functions p l x = Data.List.foldr (flip transfer-function l) x (blocks p)

  postulate
    transfer-functions-monotone : (s : Stmt) → (l : Fin n) → Monotone (BoundedSemiLattice._⊑_ 𝓟ᴸ) (transfer-functions s l)

  
  live-variables : Stmt → MonotoneFramework _ _
  live-variables p = record
         { L = 𝓟ᴸ {m}
         ; 𝓕 = transfer-functions p
         ; F = flowᴿ p
         ; E = final p
         ; ι = ⊥
         ; 𝓕-isMonotone = transfer-functions-monotone p
         }
