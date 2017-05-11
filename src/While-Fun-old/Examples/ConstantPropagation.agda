open import Data.Product
open import Data.Fin.Subset
open import Data.Vec
open import While.Analysis.ConstantPropagation as CP
open import Algorithms
open import Data.List
module While.Examples.ConstantPropagation where

open import While.Programs.Factorial
open import Data.Fin
open import LatticeTheory.Z-Top
open import IO
open import Function
open import While.Examples.Common constant-propagation

open import Data.String
show' : Vec (Fin 3 → ℤ⊤⊥) 5 → String
show' x = unlines (Data.Vec.toList (Data.Vec.map (λ f → Data.String.fromList (Data.List.concat (intersperse (Data.String.toList ", ") (Data.Vec.toList (Data.Vec.map (λ v → Data.String.toList (showℤ⊤⊥ (f v))) (allFin 3)))))) x)) --Data.Vec.map (λ f → Data.Vec.map f (allFin 3)) x

result : String -- Vec (Vec ℤ⊤⊥ 3) 6 × Vec (Vec ℤ⊤⊥ 3) 6
result = "Analysis○: " Data.String.++ show' (proj₁ bogus₃-mfp) Data.String.++ "\n\nAnalysis●:\n" Data.String.++ show' (proj₂ bogus₃-mfp) --Data.Product.map show' show' fac-mfp

main =  run ∘ putStrLn $ result




{-

  𝑨CP : AExpr → (Fin m → BoundedSemiLattice.ℂ ℤ⊤⊥ᴸ) →  BoundedSemiLattice.ℂ ℤ⊤⊥ᴸ
  transfer-function : Block → Lab → ℂ → ℂ
stmt-0 : Block
stmt-0 = (x := (var a plus var b)) (# 0)
stmt-1 : Block
stmt-1 = (y := (var a mul var b)) (# 1)
stmt-2 : Block
stmt-2 = bExpr (var y gt (var a plus var b)) (# 2)
stmt-3 : Block
stmt-3 = (a := (var a plus lit (+ 1))) (# 3)
stmt-4 : Block
stmt-4 = (x := (var a plus var b)  ) (# 4)
-}
