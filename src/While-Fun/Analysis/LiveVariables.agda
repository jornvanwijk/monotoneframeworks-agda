open import Data.Fin hiding (_-_)
open import Data.Product
open import Data.Graph 6
open import MonotoneFramework as MF
import Data.List.NonEmpty
open import Data.Fin.Subset
import Level
open import LatticeTheory
open import Data.Vec hiding (init)
open import Data.Nat hiding (_≟_ ; _⊔_)
open import Data.Fin.Properties
open import Relation.Nullary
open import Algorithms
open import Function
open import Data.Vec
open import Data.List
open import Monotonicity
open import Data.Fin.Dec
open import Data.String
open import Data.Bool
open import Relation.Nullary.Decidable
open import While.Language
module While.Analysis.LiveVariables (program : Labeled.WhileProgram) where
  open Labeled
  open WhileProgram program
  open Extra program

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


  transfer-functions : Lab → Subset m → Subset m
  transfer-functions l x = (x - (kill (lookup l blocks))) ∪ gen (lookup l blocks)

{-
--  open BoundedSemiLattice.Reasoning (𝓟ᴸ {m})
  open import Relation.Binary.PropositionalEquality
  open ≡-Reasoning
  open import Algebra.Structures
  open import Algebra
  open import LatticeTheory.ByBijection
  open BoundedSemiLattice.ByBijection.Properties (Vec (BoundedSemiLattice.ℂ Boolᴸ) n) (N-ary-×ᴸ Boolᴸ n) Vecᴸ↔N-ary-×ᴸ
  --fromBijectionᴸ (Vec (BoundedSemiLattice.ℂ L) n) (N-ary-×ᴸ L n) Vecᴸ↔N-ary-×ᴸ

  --Properties (A : Set a) (L : BoundedSemiLattice b) (open BoundedSemiLattice L) (inv : A ↔ ℂ)
  open BoundedSemiLattice (𝓟ᴸ {m}) using (_⊔_ ; ℂ ; _⊑_ ; ⊔-cong₂)
  g : {a : ℂ} → Monotone _⊑_ (_∪ a)    --a ⊔ b ≡ b → f (a ⊔ b) ≡ f b 
  g {a} {x} {y} x⊑y = begin
        (x ∪ a) ⊔ (y ∪ a)
        ≡⟨ {!left-inverse-⊔ !} ⟩
        y ∪ a
        ∎ --IsLattice.∨-cong (BooleanAlgebra.isLattice (booleanAlgebra _))     x ⊔ y ≡ y
  -}
  postulate
    transfer-functions-monotone : (l : Fin n) → Monotone (BoundedSemiLattice._⊑_ (𝓟ᴸ {m})) (transfer-functions l)

{-
  open BoundedSemiLattice.Reasoning (𝓟ᴸ {m})
  transfer-functions-monotone' : (l : Fin n) → Monotone (BoundedSemiLattice._⊑_ 𝓟ᴸ) (transfer-functions l)
  transfer-functions-monotone' l {x} {y} x₁ = begin
    transfer-functions l x
    ≡⟨⟩
    (x - (kill (lookup l blocks))) ∪ gen (lookup l blocks)
    ⊑⟨ {!!} ⟩
    (y - (kill (lookup l blocks))) ∪ gen (lookup l blocks)
    ≡⟨⟩
    transfer-functions l y
    ∎ 
-}
{-
given: x ⊑ y
goal: transfer l x ⊑ transfer l y

transfer l x
≡
(x - (kill (lookup l blocks))) ∪ gen (lookup l blocks)

⊑

(y - (kill (lookup l blocks))) ∪ gen (lookup l blocks)
≡
transfer l y


a ⊑ b   →   a ⊔ X ⊑ b ⊔ X 

-}  
  live-variables : MonotoneFramework _ _
  live-variables = record
         { L = 𝓟ᴸ {m}
         ; 𝓕 = transfer-functions
         ; F = flowᴿ labelledProgram
         ; E = final labelledProgram
         ; ι = ⊥
         ; 𝓕-isMonotone = transfer-functions-monotone
         }
         
  showLV : Subset m → String
  showLV s with nonempty? s
  showLV s | yes p = Data.Vec.foldr (λ x → String) (λ x x₁ → Data.Bool.if ⌊ x ∈? s ⌋ 
                                                     then lookup x (Data.Vec.fromList (proj₁ Var*)) Data.String.++ x₁
                                                     else x₁
                                           ) "" (allFin _)
  showLV s | no ¬p = "∅"


