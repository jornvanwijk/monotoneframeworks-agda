import Data.List.NonEmpty
import Level
open import Algorithms
open import LatticeTheory
open import Data.Bool
open import Data.Fin hiding (_-_)
open import Data.Fin.Dec
open import Data.Fin.Properties
open import Data.Fin.Subset
open import Data.List
open import Data.List.Any renaming (module Membership-≡ to L)
open import Data.Nat hiding (_≟_)
open import Data.Product
open import Data.Vec hiding (init)
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse using (Inverse)
open import MonotoneFramework as MF
open import Monotonicity
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Util.Bag hiding ([])
open import Util.List
open import While.Language
open import Util.Subset

module While.Analysis.AvailableExpressions (program : Labeled.WhileProgram) where
  open Labeled
  open WhileProgram program
  open Extra program



  ASubExpr : Set
  ASubExpr = Bag AExpr


  subExpressions-AExpr : AExpr → ASubExpr → ASubExpr
  subExpressions-AExpr (Labeled.var x) (xs , nodup) = (xs , nodup)
  subExpressions-AExpr (Labeled.lit x) (xs , nodup) = (xs , nodup)
  subExpressions-AExpr (x Labeled.plus x₁) (xs , nodup) with x Labeled.plus x₁ ∈?[ _≟A_ ] xs
  subExpressions-AExpr (x Labeled.plus x₁) (xs , nodup) | yes p = subExpressions-AExpr x₁ (subExpressions-AExpr x (xs , nodup))
  subExpressions-AExpr (x Labeled.plus x₁) (xs , nodup) | no ¬p = subExpressions-AExpr x₁ (subExpressions-AExpr x (x Labeled.plus x₁ ∷ xs , ¬p ::: nodup))
  subExpressions-AExpr (x Labeled.min x₁) (xs , nodup)  with x Labeled.min x₁ ∈?[ _≟A_ ] xs
  subExpressions-AExpr (x Labeled.min x₁) (xs , nodup) | yes p = subExpressions-AExpr x₁ (subExpressions-AExpr x (xs , nodup))
  subExpressions-AExpr (x Labeled.min x₁) (xs , nodup) | no ¬p = subExpressions-AExpr x₁ (subExpressions-AExpr x (x Labeled.min x₁ ∷ xs , ¬p ::: nodup))
  subExpressions-AExpr (x Labeled.mul x₁) (xs , nodup)  with x Labeled.mul x₁ ∈?[ _≟A_ ] xs
  subExpressions-AExpr (x Labeled.mul x₁) (xs , nodup) | yes p = subExpressions-AExpr x₁ (subExpressions-AExpr x (xs , nodup))
  subExpressions-AExpr (x Labeled.mul x₁) (xs , nodup) | no ¬p = subExpressions-AExpr x₁ (subExpressions-AExpr x (x Labeled.mul x₁ ∷ xs , ¬p ::: nodup))


  subExpressions-BExpr : BExpr → ASubExpr → ASubExpr
  subExpressions-BExpr Labeled.true (xs , nodup) = (xs , nodup)
  subExpressions-BExpr Labeled.false (xs , nodup) = (xs , nodup)
  subExpressions-BExpr (Labeled.not e) (xs , nodup) = subExpressions-BExpr e (xs , nodup)
  subExpressions-BExpr (e Labeled.and e₁) (xs , nodup) = subExpressions-BExpr e₁ (subExpressions-BExpr e (xs , nodup)) 
  subExpressions-BExpr (e Labeled.or e₁) (xs , nodup) = subExpressions-BExpr e₁ (subExpressions-BExpr e (xs , nodup)) 
  subExpressions-BExpr (x Labeled.gt x₁) (xs , nodup) = subExpressions-AExpr x₁ (subExpressions-AExpr x (xs , nodup))


  subExpressions-Stmt : Stmt → ASubExpr → ASubExpr
  subExpressions-Stmt ((v Labeled.:= e) l) xs = subExpressions-AExpr e xs
  subExpressions-Stmt (Labeled.skip l) xs = xs
  subExpressions-Stmt (s Labeled.seq s₁) xs = subExpressions-Stmt s₁ (subExpressions-Stmt s xs)
  subExpressions-Stmt (Labeled.if (x , l) then s else s₁) xs = subExpressions-Stmt s₁ (subExpressions-Stmt s (subExpressions-BExpr x xs))
  subExpressions-Stmt (Labeled.while (x , l) do s) xs = subExpressions-Stmt s (subExpressions-BExpr x xs)

  free-variables : AExpr → Subset m
  free-variables (var x) = ⁅ x ⁆
  free-variables (lit x) = ⊥
  free-variables (a plus a₁) = free-variables a ∪ free-variables a₁
  free-variables (a min a₁) = free-variables a ∪ free-variables a₁
  free-variables (a mul a₁) = free-variables a ∪ free-variables a₁


  AExpr⋆ : List AExpr
  AExpr⋆ = proj₁ (subExpressions-Stmt labelledProgram ([] , end))
    
  
  to : (a : AExpr) → a L.∈ AExpr⋆ → Fin (length AExpr⋆)
  to a pv = Inverse.to (ListIndex↔Fin {_} {AExpr} {AExpr⋆} ) ⟨$⟩ (a , pv) 
  from : Fin (length AExpr⋆) → AExpr
  from = proj₁ ∘ (_⟨$⟩_ (Inverse.from (ListIndex↔Fin {_} {AExpr} {AExpr⋆})))
  
  
  kill : Block → Subset (length  AExpr⋆)
  kill (skip l) = ⊥
  kill ((x := a) l) = tabulate (λ i → ⌊ x ∈? free-variables (from i) {- from i -} ⌋)
  kill (bExpr c l) = ⊥
  gen : Block → Subset (length AExpr⋆)
  gen (skip l) = ⊥
  gen ((x := a) l) = tabulate (λ i →  ⌊ Data.List.Any.any (_≟A (from i)) (proj₁ (subExpressions-AExpr a ([] , end))) ⌋ ∧ Data.Bool.not ⌊ x ∈? free-variables (from i) ⌋)
  gen (bExpr c l) = tabulate (λ i → ⌊ Data.List.Any.any (_≟A (from i)) (proj₁ (subExpressions-BExpr c ([] , end))) ⌋)
                                                                                                
                
  transfer-functions : Lab → Subset (length AExpr⋆) → Subset (length AExpr⋆)
  transfer-functions l x = (x - kill (lookup l blocks)) ∪ gen (lookup l blocks)

  postulate
    transfer-monotone : (ℓ : Fin n) → Monotone (BoundedSemiLattice._⊑_ (𝓟ᴸ-by-exclusion (length AExpr⋆))) (transfer-functions ℓ)
                                                                                                                      
  open import Data.List.NonEmpty hiding (length)
  available-expressions : MonotoneFramework _
  available-expressions = record
    { L = 𝓟ᴸ-by-exclusion (length AExpr⋆)
    ; 𝓕 = transfer-functions
    ; F = flow labelledProgram
    ; E = Data.List.[ init labelledProgram ]
    ; ι = ⊥
    ; 𝓕-isMonotone = transfer-monotone
    }

  open import Data.Fin.Dec
  open import Data.Bool
  open import Data.String
  showAE : Subset (length  AExpr⋆) → String
  showAE xs with nonempty? xs
  showAE xs | yes p = Data.Vec.foldr (λ x → String) (λ x x₁ → Data.Bool.if ⌊ x ∈? xs ⌋ 
                                                     then show-AExpr (lookup x (Data.Vec.fromList AExpr⋆)) Data.String.++ ", " Data.String.++ x₁
                                                     else x₁) "" (allFin _)
  showAE xs | no ¬p = "∅"

